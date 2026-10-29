import V3Wire.Verification.Codec
import V3Wire.Verification.Path

/-!
Refinement of the production v3 protocol core (`initialize_config`,
`authenticate_config`, `seal_record`, `open_record`,
`authorize_agent_request`) against the independent protocol specification
`Transcrypt.V3Policy`.

The core is generic in its cryptographic primitives (`V3Primitives`). The
production adapter instantiates it with RustCrypto AES-SIV and SHA-256. Here
the instance is arbitrary, constrained only by `Realizes`, the explicit
contract that it computes the abstract `Suite`'s deterministic SIV function
with the spec's domain strings and associated-data order, and the truncated
digest. `Realizes` is assumption A5 of `docs/verification/V3-ASSUMPTIONS.md`;
it is tested, not proved: `rust/crates/transcrypt-rs/tests/v3_differential.rs`
checks the production `Keyed` against OpenSSL AES-SIV and `hashlib` SHA-256
(`tests/v3/reference/differential.py`; argon2-cffi only derives the corpus
keys, and Argon2id is not part of `Realizes`), and
`keyed_satisfies_the_realizes_contract` tests its clauses directly.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

/-- The cryptographic contract on a `V3Primitives` instance under one key,
    relative to an abstract suite `s`. Outputs written through `&mut` slices
    keep their length, as Rust guarantees for any `&mut [u8]`. A primitive
    may report failure (`false`), but never claims success wrongly. -/
structure Realizes {P : Type} (inst : V3Primitives P) (prims : P) (s : Suite) : Prop where
  seal_config : ∀ pre tag, WP.spec (inst.seal_config prims pre tag) (fun r =>
    r.1 = true → wireBytes r.2 = s.siv [configDomain, wireBytes pre] [])
  open_config : ∀ pre tag, WP.spec (inst.open_config prims pre tag) (fun b =>
    b = true ↔ s.siv [configDomain, wireBytes pre] [] = wireBytes tag)
  seal_file : ∀ cfg path pt out, WP.spec (inst.seal_file prims cfg path pt out) (fun r =>
    r.2.length = out.length ∧
    (r.1 = true → sliceBytes r.2 = s.siv [fileDomain, wireBytes cfg, sliceBytes path] (sliceBytes pt)))
  /-- Soundness (success only for a genuine sealing of the output) and
      completeness (a genuine sealing of a right-sized plaintext opens). -/
  open_file : ∀ cfg path sealed out, WP.spec (inst.open_file prims cfg path sealed out) (fun r =>
    r.2.length = out.length ∧
    (r.1 = true → s.siv [fileDomain, wireBytes cfg, sliceBytes path] (sliceBytes r.2) = sliceBytes sealed) ∧
    ((∃ pt : List Nat, pt.length = out.length ∧
        s.siv [fileDomain, wireBytes cfg, sliceBytes path] pt = sliceBytes sealed) → r.1 = true))
  config_id : ∀ cfg, WP.spec (inst.config_id prims cfg) (fun id =>
    wireBytes id = s.digest16 (wireBytes cfg))

variable {P : Type} {inst : V3Primitives P} {prims : P} {σ : Suite}

/-- A freshly initialized configuration authenticates and has the exact
    55-byte layout of the spec. -/
@[step]
theorem initialize_config_spec (h : Realizes inst prims σ) (salt : Std.Array U8 32#usize) :
    initialize_config inst prims salt ⦃ r => match r with
      | core.result.Result.Ok cfg =>
          ConfigAuthentic σ (wireBytes cfg) ∧
          wireBytes cfg = Transcrypt.V3Wire.encodeConfig (wireBytes salt)
            (σ.siv [configDomain, Transcrypt.V3Wire.configMagic ++ wireBytes salt] [])
      | core.result.Result.Err e => e = Refusal.Primitive ⦄ := by
  unfold initialize_config
  step with encode_config_prefix_bytes as ⟨ pre, hpre ⟩
  have hsc := h.seal_config pre (Std.Array.repeat 16#usize 0#u8)
  step with hsc as ⟨ b, tag, htag ⟩
  split
  · rename_i hb
    step with encode_config_refines as ⟨ cfg, hcfg ⟩
    have hpre' : wireBytes pre = Transcrypt.V3Wire.configMagic ++ wireBytes salt := by
      simp only [wireBytes, hpre, List.map_append]
      rw [← extracted_config_magic_matches_spec]; rfl
    have ht : wireBytes tag = σ.siv [configDomain, Transcrypt.V3Wire.configMagic ++ wireBytes salt] [] := by
      rw [htag hb, hpre']
    refine ⟨⟨wireBytes salt, wireBytes tag, ?_, ?_⟩, ?_⟩
    · rw [hcfg]
      exact Transcrypt.V3Wire.decode_config_encode _ _ (by simp [wireBytes]) (by simp [wireBytes])
    · simpa using ht.symm
    · simpa [ht] using hcfg
  · simp

theorem configAuthentic_iff {cfg : Std.Array U8 55#usize} {salt : Std.Array U8 32#usize}
    {tag : Std.Array U8 16#usize} (h : cfg.val = CONFIG_MAGIC.val ++ salt.val ++ tag.val) :
    ConfigAuthentic σ (wireBytes cfg) ↔
      σ.siv [configDomain, Transcrypt.V3Wire.configMagic ++ wireBytes salt] [] = wireBytes tag := by
  have hshape := config_shape_of_eq salt tag h
  constructor
  · rintro ⟨salt', tag', hs, ht⟩
    have : (wireBytes salt, wireBytes tag) = (salt', tag') := by
      rw [← Option.some.injEq]; rw [← hshape]; exact hs
    simp only [Prod.mk.injEq] at this
    rw [this.1, this.2]; exact ht
  · intro ht
    exact ⟨wireBytes salt, wireBytes tag, hshape, ht⟩

/-- `authenticate_config` accepts exactly the authentic configurations:
    `Ok` iff the 55 bytes parse and the tag verifies under the held key. -/
@[step]
theorem authenticate_config_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize) :
    authenticate_config inst prims config ⦃ r => match r with
      | core.result.Result.Ok c =>
          ConfigAuthentic σ (wireBytes config) ∧ config.val = CONFIG_MAGIC.val ++ c.salt.val ++ c.tag.val
      | core.result.Result.Err Refusal.Config =>
          Transcrypt.V3Wire.decodeConfigShape (wireBytes config) = none
      | core.result.Result.Err Refusal.ConfigAuthentication => ¬ ConfigAuthentic σ (wireBytes config)
      | core.result.Result.Err _ => False ⦄ := by
  unfold authenticate_config
  step with decode_config_exact_spec as ⟨ r, hr ⟩
  rcases r with c | e
  · simp only at hr ⊢
    step with encode_config_prefix_bytes as ⟨ pre, hpre ⟩
    have hpre' : wireBytes pre = Transcrypt.V3Wire.configMagic ++ wireBytes c.salt := by
      simp only [wireBytes, hpre, List.map_append]
      rw [← extracted_config_magic_matches_spec]; rfl
    step with h.open_config pre c.tag as ⟨ b, hb ⟩
    rw [hpre'] at hb
    split
    · rename_i hbt
      exact ⟨(configAuthentic_iff hr).2 (hb.1 hbt), hr⟩
    · rename_i hbf
      intro hauth
      exact hbf (hb.2 ((configAuthentic_iff hr).1 hauth))
  · simp only at hr ⊢
    cases e
    · exact hr.elim
    · exact config_shape_none_of_take hr

/-! ## Record sealing and opening -/

theorem setSlice!_tail {l ss : List U8} {i : Nat} (h : ss.length = l.length - i) (hi : i ≤ l.length) :
    l.setSlice! i ss = l.take i ++ ss := by
  have hm : min ss.length (l.length - i) = ss.length := by omega
  have hd : List.drop (i + ss.length) l = [] := List.drop_of_length_le (by omega)
  simp only [List.setSlice!, hm, List.take_length, hd, List.append_nil]

/-- `&mut out[22..]`: the view is the tail, and writing back a same-length
    tail replaces exactly that tail. -/
theorem index_mut_from_spec (out : Slice U8) (h : 22 ≤ out.length) :
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      out { start := FILE_HEADER_LEN } ⦃ r =>
        r.1.val = out.val.drop 22 ∧
        ∀ ss : Slice U8, ss.length = out.length - 22 → (r.2 ss).val = out.val.take 22 ++ ss.val ⦄ := by
  unfold core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
  simp only [core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_slice_mut, rust_primitives.slice.slice_length]
  have hlen : out.len.val = out.length := by simp
  step*
  · simp only [FILE_HEADER_LEN_val, hlen]; omega
  · refine ⟨?_, fun ss hss => ?_⟩
    · rw [sub_post1, Slice.slice, List.slice, hlen, FILE_HEADER_LEN_val]
      exact List.take_of_length_le (by simp)
    · simp only [FILE_HEADER_LEN_val]
      exact setSlice!_tail (by simpa using hss) (by simpa using h)

/-- `record[22..]` (shared borrow) is the tail of the record. -/
theorem index_from_spec (record : Slice U8) (h : 22 ≤ record.length) :
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      record { start := FILE_HEADER_LEN } ⦃ r => r.val = record.val.drop 22 ⦄ := by
  unfold core.Slice.Insts.CoreOpsIndexIndex.index
  simp only [core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_slice, rust_primitives.slice.slice_length]
  have hlen : record.len.val = record.length := by simp
  have hle : FILE_HEADER_LEN ≤ record.len := by
    rw [UScalar.le_equiv, FILE_HEADER_LEN_val, hlen]; exact h
  simp only [bind_tc_ok]
  rw [if_pos hle]
  step*
  rw [r_post1, Slice.slice, List.slice, hlen, FILE_HEADER_LEN_val]
  exact List.take_of_length_le (by simp)

theorem seal_record_loop_spec (base out : Slice U8) (header : Std.Array U8 22#usize) (i : Usize)
    (hlen : 22 ≤ out.length) (hi : i.val ≤ 22) (h : Copied out.val base.val header.val 0 0 i.val) :
    seal_record_loop out header i ⦃ r => Copied r.val base.val header.val 0 0 22 ⦄ := by
  unfold seal_record_loop
  apply copy_loop (val := fun o : Slice U8 => o.val) (bound := 22) _ _ _ _ _ _ _ _ hi h
  intro o j hj hc
  unfold seal_record_loop.body
  have hhl : header.length = 22 := by simp
  have hol : o.length = out.length := by
    have := hc.1; have h2 := h.1; simp only [Slice.length] at *; omega
  have hF := FILE_HEADER_LEN_val
  step*
  refine ⟨i2_post, by omega, ?_⟩
  rw [s_post2, i1_post2, i2_post]
  have := hc.step (by simp; omega)
  rw [Nat.zero_add, getElem!_pos header.val j.val (by simp; omega)] at this
  exact this

/-- The clean direction. Success means every precondition of the spec's
    `MaySeal` holds and the output is exactly the spec's `sealedRecord`;
    each refusal names a violated precondition (or a primitive failure). -/
@[step]
theorem seal_record_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (path plaintext out : Slice U8) :
    seal_record inst prims config path plaintext out ⦃ r => match r.1 with
      | core.result.Result.Ok _ =>
          MaySeal σ (wireBytes config) (sliceBytes path) (sliceBytes plaintext) ∧
          sliceBytes r.2 = sealedRecord σ (wireBytes config) (sliceBytes path) (sliceBytes plaintext)
      | core.result.Result.Err Refusal.Size =>
          ¬ (plaintext.length ≤ maxFile ∧ out.length = plaintext.length + 38)
      | core.result.Result.Err Refusal.Path => ¬ CanonicalProtectedPath (sliceBytes path)
      | core.result.Result.Err Refusal.Config => ¬ ConfigAuthentic σ (wireBytes config)
      | core.result.Result.Err Refusal.ConfigAuthentication => ¬ ConfigAuthentic σ (wireBytes config)
      | core.result.Result.Err Refusal.DoubleEncryption =>
          Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes plaintext) ≠ none
      | core.result.Result.Err Refusal.Primitive => True
      | core.result.Result.Err _ => False ⦄ := by
  unfold seal_record
  have hptl : plaintext.len.val = plaintext.length := by simp
  have houtl : out.len.val = out.length := by simp
  simp_len
  have := usize_max_ge
  step*
  · have hn := ‹¬plaintext.len > i1›
    simp only [gt_iff_lt, UScalar.lt_equiv, not_lt, i1_post, maxFile] at hn
    omega
  · -- Success path: identifier, header, header copy, tail view, seal.
    have hn := ‹¬plaintext.len > i1›
    simp only [gt_iff_lt, UScalar.lt_equiv, not_lt, i1_post] at hn
    have hol := ‹¬(out.len != i4) = true›
    simp_bne at hol
    have holv : out.length = plaintext.length + 38 := by
      rw [← houtl, hol, i4_post, i3_post, hptl]
    have hauth : ConfigAuthentic σ (wireBytes config) := by
      have := ‹r = core.result.Result.Ok _›; subst this; exact r_post.1
    have hnotrec : Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes plaintext) = none := by
      have hb1 := ‹¬b1 = true›
      rw [b1_post] at hb1
      cases r1 with
      | Ok x => exact absurd ⟨x, rfl⟩ hb1
      | Err e =>
        cases e with
        | Magic => exact r1_post.2
        | Length => exact Transcrypt.V3Wire.file_truncated _ (by rw [sliceBytes_length]; exact r1_post)
    have hcanon : CanonicalProtectedPath (sliceBytes path) := b_post.1 ‹b = true›
    step with h.config_id config as ⟨ cid, hcid ⟩
    step with encode_file_header_bytes as ⟨ header, hheader ⟩
    step with seal_record_loop_spec out out header 0#usize (by omega) (by simp) (Copied.zero _ _ _ _) as ⟨ out1, hout1 ⟩
    have hout1l : out1.length = out.length := by have := hout1.1; simpa using this
    step with index_mut_from_spec out1 (by omega) as ⟨ sub, back, hsub, hback ⟩
    step with h.seal_file config path plaintext sub as ⟨ b2, s1, hs1l, hs1 ⟩
    split
    · rename_i hb2
      refine ⟨⟨hcanon, hauth, by rw [sliceBytes_length, ← hptl]; omega, hnotrec⟩, ?_⟩
      have hs1l' : s1.length = out1.length - 22 := by
        rw [hs1l]; simp [Slice.length, hsub]
      have htake : out1.val.take 22 = header.val := by
        have hl1 : out1.val.length = out1.length := rfl
        have hge : 22 ≤ out1.val.length := by omega
        apply list_eq_of_getElem! (by simp; omega)
        intro k hk
        have hk22 : k < 22 := by simp at hk; omega
        rw [getElem!_pos (out1.val.take 22) k (by simp; omega), List.getElem_take,
          ← getElem!_pos out1.val k (by omega), hout1.get_in (by omega) (by omega) (by omega)]
        simp
      simp only [sliceBytes, hback s1 hs1l', htake, hheader, List.map_append]
      have := hs1 hb2
      simp only [sliceBytes] at this
      rw [this, sealedRecord, Transcrypt.V3Wire.encodeFile, ← hcid, ← extracted_file_magic_matches_spec]
      simp [wireBytes]
    · trivial
  · have hr := ‹r = core.result.Result.Err refusal›
    subst hr
    cases refusal <;> simp only at r_post ⊢
    · intro ⟨salt, tag, hs, _⟩; rw [r_post] at hs; cases hs
    · exact r_post

/-- The zeroing loop run when authentication fails. -/
theorem open_record_loop_spec (base out : Slice U8) (i : Usize)
    (_hl : out.length = base.length) (hi : i.val ≤ base.length)
    (h : Copied out.val base.val (List.replicate base.length 0#u8) 0 0 i.val) :
    open_record_loop out i ⦃ r =>
      Copied r.val base.val (List.replicate base.length 0#u8) 0 0 base.length ⦄ := by
  unfold open_record_loop
  apply copy_loop (val := fun o : Slice U8 => o.val) (bound := base.length) _ _ _ _ _ _ _ _ hi h
  intro o j hj hc
  unfold open_record_loop.body
  have hol : o.length = base.length := by have := hc.1; simpa using this
  simp_len
  step*
  refine ⟨i2_post, by omega, ?_⟩
  rw [s_post2, i2_post]
  have hlt : j.val < o.val.length := s_post1
  have := hc.step (by simpa using hlt)
  have hj : j.val < base.length := by omega
  simp only [Nat.zero_add] at this
  rw [getElem!_pos (List.replicate base.length 0#u8) j.val (by simpa using hj),
    List.getElem_replicate] at this
  simpa [Slice.set, Slice.setAtNat] using this

/-- The smudge/verify direction: plaintext is released only if the record
    authentically opens to it at exactly this config and path (the spec's
    `OpensTo`). On authentication failure the buffer is zeroed; on every
    other refusal it is untouched. -/
@[step]
theorem open_record_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (path record out : Slice U8) :
    open_record inst prims config path record out ⦃ r => match r.1 with
      | core.result.Result.Ok _ =>
          OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes record) (sliceBytes r.2)
      | core.result.Result.Err Refusal.Authentication =>
          r.2.length = out.length ∧ (∀ b ∈ sliceBytes r.2, b = 0) ∧
          ¬ ∃ pt, pt.length = out.length ∧
            sliceBytes record = sealedRecord σ (wireBytes config) (sliceBytes path) pt
      | core.result.Result.Err Refusal.Size =>
          r.2 = out ∧ (maxRecord < record.length ∨ out.length + 38 ≠ record.length)
      | core.result.Result.Err Refusal.Path => r.2 = out ∧ ¬ CanonicalProtectedPath (sliceBytes path)
      | core.result.Result.Err Refusal.Config => r.2 = out ∧ ¬ ConfigAuthentic σ (wireBytes config)
      | core.result.Result.Err Refusal.ConfigAuthentication =>
          r.2 = out ∧ ¬ ConfigAuthentic σ (wireBytes config)
      | core.result.Result.Err Refusal.Envelope =>
          r.2 = out ∧ Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes record) = none
      | core.result.Result.Err Refusal.ConfigMismatch =>
          r.2 = out ∧ ∃ id, Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes record) = some id ∧
            id ≠ σ.digest16 (wireBytes config)
      | core.result.Result.Err _ => False ⦄ := by
  unfold open_record
  have hrl : record.len.val = record.length := by simp
  have houtl : out.len.val = out.length := by simp
  simp_len
  have := usize_max_ge
  step*
  · have hr1 := ‹r1 = core.result.Result.Ok id›
    subst hr1
    have := (Transcrypt.V3Wire.record_of_shape r1_post).2.1
    rw [sliceBytes_length] at this
    rw [i2_post, hrl]; exact this
  · have hr1 := ‹r1 = core.result.Result.Ok id›
    subst hr1
    obtain ⟨hshape, hlen38, -⟩ := Transcrypt.V3Wire.record_of_shape r1_post
    rw [sliceBytes_length] at hlen38
    have hauth : ConfigAuthentic σ (wireBytes config) := by
      have := ‹r = core.result.Result.Ok _›; subst this; exact r_post.1
    have hcanon : CanonicalProtectedPath (sliceBytes path) := b_post.1 ‹b = true›
    have hmax : record.length ≤ maxRecord := by
      have hn := ‹¬record.len > i1›
      simp only [gt_iff_lt, UScalar.lt_equiv, not_lt, i1_post, hrl] at hn
      exact hn
    have hol : out.length + 38 = record.length := by
      have hne := ‹¬(i3 != out.len) = true›
      simp_bne at hne
      have := congrArg (fun x : Usize => x.val) hne
      simp only [i3_post1, i2_post, hrl, houtl] at this
      omega
    step with h.config_id config as ⟨ cid, hcid ⟩
    step as ⟨ s1, hs1 ⟩
    step with bytes_eq_spec as ⟨ b1, hb1 ⟩
    have hid_iff : b1 = true ↔ wireBytes id = σ.digest16 (wireBytes config) := by
      rw [hb1, ← hcid, s_post, hs1, wireBytes_inj]; rfl
    split
    · rename_i hb1t
      step with index_from_spec record (by omega) as ⟨ s2, hs2 ⟩
      step with h.open_file config path s2 out as ⟨ b2, out1, hol1, hopen, hcomplete ⟩
      split
      · rename_i hb2
        refine ⟨hcanon, hauth, by rw [sliceBytes_length]; exact hmax, ?_⟩
        have hdrop : List.drop 22 (sliceBytes record) =
            σ.siv [fileDomain, wireBytes config, sliceBytes path] (sliceBytes out1) := by
          rw [hopen hb2]; simp [sliceBytes, hs2, List.map_drop]
        rw [hshape, hdrop, sealedRecord, Transcrypt.V3Wire.encodeFile, ← hid_iff.1 hb1t]
      · step with open_record_loop_spec out1 out1 0#usize rfl (by simp) (Copied.zero _ _ _ _) as ⟨ out2, hout2 ⟩
        have hl2 : out2.val.length = out1.val.length := by have := hout2.1; simpa using this
        rename_i hb2f
        refine ⟨by simp only [Slice.length] at hol1 ⊢; omega, ?_, ?_⟩
        rotate_left
        · rintro ⟨pt, hptl, hpt⟩
          apply hb2f
          apply hcomplete pt hptl
          have : List.drop 22 (sliceBytes record) =
              σ.siv [fileDomain, wireBytes config, sliceBytes path] pt := by
            rw [hpt]; simp [sealedRecord, Transcrypt.V3Wire.encodeFile, Transcrypt.V3Wire.fileMagic,
              σ.digest16_length]
          rw [← this]; simp [sliceBytes, hs2, List.map_drop]
        intro b hb
        simp only [sliceBytes, List.mem_map] at hb
        obtain ⟨x, hx, rfl⟩ := hb
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        have := hout2.get_in hk (by omega) (by have := hout2.1; simp at this ⊢; omega)
        rw [getElem!_pos out2.val k hk] at this
        rw [this, Nat.zero_add, Nat.sub_zero, getElem!_pos _ k (by have := hout2.1; simp at this ⊢; omega),
          List.getElem_replicate]
        rfl
    · rename_i hb1f
      refine ⟨rfl, wireBytes id, r1_post, fun heq => hb1f (hid_iff.2 heq)⟩
  · have hr1 := ‹r1 = core.result.Result.Err _›
    subst hr1
    rename_i e _
    cases e with
    | Magic => exact r1_post.2
    | Length => exact Transcrypt.V3Wire.file_truncated _ (by rw [sliceBytes_length]; exact r1_post)
  · have hr := ‹r = core.result.Result.Err refusal›
    subst hr
    cases refusal <;> simp only at r_post ⊢
    · intro ⟨salt, tag, hs, _⟩; rw [r_post] at hs; cases hs
    · exact r_post

/-! ## Credential agent authorization -/

def agentOpSpec : transcrypt_v3_core.AgentOp → Transcrypt.V3Policy.AgentOp
  | .Ping => .ping
  | .Encrypt => .encrypt
  | .Decrypt => .decrypt
  | .Stop => .stop

/-- The agent performs exactly the operations the spec authorizes. -/
@[step]
theorem authorize_agent_request_spec (opcode : U8) (supplied active : Std.Array U8 55#usize)
    (path : Slice U8) (body_len : Usize) :
    authorize_agent_request opcode supplied active path body_len ⦃ r => match r with
      | core.result.Result.Ok op =>
          authorizeSpec opcode.val (wireBytes supplied) (wireBytes active) (sliceBytes path) body_len.val =
            some (agentOpSpec op)
      | core.result.Result.Err _ =>
          authorizeSpec opcode.val (wireBytes supplied) (wireBytes active) (sliceBytes path) body_len.val =
            none ⦄ := by
  unfold authorize_agent_request
  have hpl : path.len.val = path.length := by simp
  simp_len
  have := usize_max_ge
  have hwb := wireBytes_inj supplied active
  have hsl : (sliceBytes path).length = path.length := sliceBytes_length path
  have hnil : sliceBytes path = [] ↔ path.length = 0 := by
    rw [← List.length_eq_zero_iff, hsl]
  step*
  all_goals
    simp only [gt_iff_lt, UScalar.lt_equiv, not_lt, hpl, MAX_PATH_val, bne_iff_ne, ne_eq,
      Decidable.not_not, UScalar.eq_equiv] at *
    unfold authorizeSpec
    simp_all [agentOpSpec]

/-! ## Completeness: genuine records open -/

/-- A genuine record of the right size always opens, to exactly its plaintext. -/
theorem open_record_complete (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (path record out : Slice U8) (pt : List Nat)
    (hop : OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes record) pt)
    (hl : out.length = pt.length) :
    open_record inst prims config path record out ⦃ r =>
      r.1 = core.result.Result.Ok () ∧ sliceBytes r.2 = pt ⦄ := by
  obtain ⟨hcanon, hauth, hmax, hrec⟩ := hop
  have hreclen : record.length = pt.length + 38 := by
    rw [← sliceBytes_length record, hrec, sealed_length]
  have hshape := sealed_shape σ (wireBytes config) (sliceBytes path) pt
  rw [← hrec] at hshape
  apply WP.spec_mono (open_record_spec h config path record out)
  rintro ⟨res, buf⟩ hpost
  rcases res with u | e
  · exact ⟨rfl, opensTo_unique σ hpost ⟨hcanon, hauth, hmax, hrec⟩⟩
  · exfalso
    cases e <;> simp only at hpost
    · exact hpost.2 hcanon
    · rcases hpost.2 with h1 | h1
      · rw [sliceBytes_length] at hmax; omega
      · omega
    · exact hpost.2 hauth
    · exact hpost.2 hauth
    · rw [hshape] at hpost; cases hpost.2
    · obtain ⟨id, hid, hne⟩ := hpost.2
      rw [hshape] at hid; cases hid; exact hne rfl
    · exact hpost.2.2 ⟨pt, hl.symm, hrec⟩

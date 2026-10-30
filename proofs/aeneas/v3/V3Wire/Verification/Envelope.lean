import V3Wire.Verification.Codec

/-!
Functional refinement of two keyless production checks used by the Git
adapter: `is_object_id` accepts exactly the Git object names of
`Transcrypt.V3Policy.ObjectId` (40 or 64 lowercase hexadecimal digits), and
`record_envelope_ok` accepts exactly the records satisfying
`Transcrypt.V3Policy.EnvelopeOk` (size bound plus a v3 file header naming the
given configuration id). As `WP.spec` triples they also exclude panics and
divergence. `record_envelope_prefix_ok` refuses a declared size outside the
record bounds or shorter than its prefix, so its answer holds for any
caller; `record_envelope_prefix_ok_record` shows the envelope of a real
record needs only its size and its first `FILE_MIN_LEN` bytes.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core

/-- The digits examined so far are all lowercase hexadecimal. -/
def EnvHexUpTo (l : List Nat) (i : Nat) : Prop := ∀ k < i, Transcrypt.V3Policy.HexDigit l[k]!

/-- Invariant of the object-name scan: `ok` records exactly whether the length
    is admissible and every examined digit is hexadecimal. -/
def EnvOidInv (oid : Slice U8) (lenOk : Prop) (s : Bool × Usize) : Prop :=
  s.2.val ≤ oid.length ∧ (s.1 = true ↔ lenOk ∧ EnvHexUpTo (sliceBytes oid) s.2.val)

/-- The per-digit test of `is_object_id` decides `HexDigit`. The program is
    restated from the body of `is_object_id_loop` in
    `V3Wire/Extraction/Funs.lean` and must match it: `env_oid_body_spec`
    applies this lemma with `step with`, which fails if the extraction
    changes. -/
theorem env_hex_spec (c : U8) :
    (if c ≥ 48#u8 then if c ≤ 57#u8 then ok true else if c ≥ 97#u8 then ok (decide (c ≤ 102#u8)) else ok false
      else if c ≥ 97#u8 then ok (decide (c ≤ 102#u8)) else ok false : RustM Bool) ⦃ b =>
      b = true ↔ Transcrypt.V3Policy.HexDigit c.val ⦄ := by
  unfold Transcrypt.V3Policy.HexDigit
  split_ifs <;> simp_all

theorem env_oid_body_spec (oid : Slice U8) (n : Usize) (hn : n.val = oid.length) (lenOk : Prop)
    (ok : Bool) (i : Usize) (hinv : EnvOidInv oid lenOk (ok, i)) :
    is_object_id_loop.body oid n ok i ⦃ cf => match cf with
      | .cont s' => EnvOidInv oid lenOk s' ∧ n.val - s'.2.val < n.val - i.val
      | .done r => r = true ↔ lenOk ∧ EnvHexUpTo (sliceBytes oid) oid.length ⦄ := by
  obtain ⟨hi, hiff⟩ := hinv
  simp only at hi hiff
  have hrl : oid.length = oid.val.length := rfl
  unfold is_object_id_loop.body
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok, false_iff]
    simp only [Bool.false_eq_true, false_iff] at hiff
    rintro ⟨hl, hh⟩
    exact hiff ⟨hl, fun k hk => hh k (by omega)⟩
  · simp only [true_iff, ↓reduceIte] at hiff ⊢
    have := usize_max_ge
    step*
    step with env_hex_spec as ⟨ ok2, hok2 ⟩
    step*
    rw [c_post2] at hok2
    have hb := sliceBytes_getElem! oid i.val (by omega)
    refine ⟨⟨by dsimp only; omega, ?_⟩, by omega⟩
    dsimp only
    rw [hok2, i1_post, ← hb]
    constructor
    · intro hx
      refine ⟨hiff.1, fun k hk => ?_⟩
      rcases Nat.lt_or_ge k i.val with h | h
      · exact hiff.2 k h
      · have : k = i.val := by omega
        subst this; exact hx
    · intro ⟨_, hh⟩
      exact hh i.val (by omega)

theorem env_oid_loop_spec (oid : Slice U8) (n : Usize) (hn : n.val = oid.length) (lenOk : Prop)
    (ok : Bool) (hok : ok = true ↔ lenOk) :
    is_object_id_loop oid n ok 0#usize ⦃ r =>
      r = true ↔ lenOk ∧ EnvHexUpTo (sliceBytes oid) oid.length ⦄ := by
  unfold is_object_id_loop
  apply loop.spec_decr_nat (fun s => n.val - s.2.val) (EnvOidInv oid lenOk)
  · rintro ⟨r, k⟩ hinv
    apply WP.spec_mono (env_oid_body_spec oid n hn lenOk r k hinv)
    rintro (⟨_, _⟩ | _) <;> exact id
  · refine ⟨by simp, ?_⟩
    have h0 : (0#usize).val = 0 := by simp
    simp only [hok, h0]
    exact ⟨fun h => ⟨h, fun k hk => absurd hk (by omega)⟩, fun h => h.1⟩

theorem env_objectId_iff (l : List Nat) :
    Transcrypt.V3Policy.ObjectId l ↔
      (l.length = Transcrypt.V3Policy.sha1OidLen ∨ l.length = Transcrypt.V3Policy.sha256OidLen) ∧
        EnvHexUpTo l l.length := by
  unfold Transcrypt.V3Policy.ObjectId EnvHexUpTo
  refine and_congr Iff.rfl ⟨fun h k hk => ?_, fun h c hc => ?_⟩
  · rw [getElem!_pos l k hk]; exact h _ (List.getElem_mem hk)
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have := h k hk
    rwa [getElem!_pos l k hk] at this

/-- `is_object_id` accepts exactly the Git object names of the spec. -/
@[step]
theorem is_object_id_spec (oid : Slice U8) :
    is_object_id oid ⦃ r => r = true ↔ Transcrypt.V3Policy.ObjectId (sliceBytes oid) ⦄ := by
  unfold is_object_id
  simp_len
  rw [env_objectId_iff, sliceBytes_length]
  have key := env_oid_loop_spec oid oid.len (by simp)
    (oid.length = Transcrypt.V3Policy.sha1OidLen ∨ oid.length = Transcrypt.V3Policy.sha256OidLen)
  -- The length test `(n == SHA1_OID_LEN) | (n == SHA256_OID_LEN)` computes the admissible-length flag.
  apply key
  simp [UScalar.eq_equiv]

/-- `record_envelope_prefix_ok` decides the keyless envelope from a declared
    size and leading bytes, meaningfully for any caller: the declared size
    lies in `fileMinLen ..= maxRecord`, `prefix` is no longer than it, and
    `prefix` has the v3 file header naming configuration id `id`. -/
@[step]
theorem record_envelope_prefix_ok_spec (size : Usize) («prefix» : Slice U8) (id : Std.Array U8 16#usize) :
    record_envelope_prefix_ok size «prefix» id ⦃ r => r = true ↔
      Transcrypt.V3Wire.fileMinLen ≤ size.val ∧ size.val ≤ Transcrypt.V3Policy.maxRecord ∧
        «prefix».length ≤ size.val ∧
        Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes «prefix») = some (wireBytes id) ⦄ := by
  unfold record_envelope_prefix_ok
  simp_len
  have hbl := sliceBytes_length «prefix»
  have hfm : Transcrypt.V3Wire.fileMinLen = 38 := rfl
  have := usize_max_ge
  step with FILE_MIN_LEN_spec as ⟨ i0, i0_post ⟩
  split
  · rename_i hlt
    simp only [UScalar.lt_equiv, i0_post] at hlt
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
    intro h; omega
  · rename_i hlt
    have hmin : Transcrypt.V3Wire.fileMinLen ≤ size.val := by
      simp only [UScalar.lt_equiv, not_lt, i0_post] at hlt; omega
    step with MAX_RECORD_spec as ⟨ i1, i1_post ⟩
    split
    · rename_i hgt
      simp only [gt_iff_lt, UScalar.lt_equiv, i1_post] at hgt
      simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
      intro _ h; omega
    · rename_i hgt
      have hmax : size.val ≤ Transcrypt.V3Policy.maxRecord := by
        simp only [gt_iff_lt, UScalar.lt_equiv, not_lt, i1_post] at hgt
        exact hgt
      split
      · rename_i hlong
        simp only [gt_iff_lt, UScalar.lt_equiv] at hlong
        simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
        have hpv : «prefix».length = «prefix».val.length := rfl
        intro _ _ h; simp at hlong; omega
      · rename_i hlong
        have hle : «prefix».length ≤ size.val := by
          have hpv : «prefix».length = «prefix».val.length := rfl
          simp only [gt_iff_lt, UScalar.lt_equiv, not_lt] at hlong; simp at hlong; omega
        step with parse_file_header_spec as ⟨ r, hr ⟩
        cases r with
        | Ok found =>
          simp only at hr ⊢
          step*
          rw [r_post, s_post, s1_post, hr, Option.some_inj]
          simp only [hmin, hmax, hle, true_and, Array.to_slice]
          exact (wireBytes_inj found id).symm
        | Err e =>
          simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
          intro _ _ _
          cases e with
          | Magic =>
            simp only at hr
            rw [hr.2]; simp
          | Length =>
            simp only at hr
            rw [Transcrypt.V3Wire.file_truncated _ (by rw [hbl]; exact hr)]
            simp

/-- A decoded file header implies the bytes are at least `fileMinLen` long. -/
theorem decodeFileHeaderShape_length {l id : List Nat}
    (h : Transcrypt.V3Wire.decodeFileHeaderShape l = some id) :
    Transcrypt.V3Wire.fileMinLen ≤ l.length := by
  unfold Transcrypt.V3Wire.decodeFileHeaderShape at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- `record_envelope_ok` accepts exactly the records whose keyless envelope
    is valid for configuration id `id`. -/
@[step]
theorem record_envelope_ok_spec (record : Slice U8) (id : Std.Array U8 16#usize) :
    record_envelope_ok record id ⦃ r => r = true ↔
      Transcrypt.V3Policy.EnvelopeOk (sliceBytes record) (wireBytes id) ⦄ := by
  unfold record_envelope_ok Transcrypt.V3Policy.EnvelopeOk
  simp_len
  simp only [bind_tc_ok]
  have hrl : record.len.val = record.length := by simp
  apply WP.spec_mono (record_envelope_prefix_ok_spec record.len record id)
  intro r hr
  rw [hr, hrl, sliceBytes_length]
  constructor
  · exact fun ⟨_, hmax, _, hd⟩ => ⟨hmax, hd⟩
  · intro ⟨hmax, hd⟩
    have := decodeFileHeaderShape_length hd
    rw [sliceBytes_length] at this
    exact ⟨this, hmax, le_refl _, hd⟩

/-- The file header decision reads only the first `fileMinLen` bytes. -/
theorem decodeFileHeaderShape_take (l : List Nat) :
    Transcrypt.V3Wire.decodeFileHeaderShape (l.take Transcrypt.V3Wire.fileMinLen) =
      Transcrypt.V3Wire.decodeFileHeaderShape l := by
  unfold Transcrypt.V3Wire.decodeFileHeaderShape
  by_cases h : Transcrypt.V3Wire.fileMinLen ≤ l.length
  · have ht : Transcrypt.V3Wire.fileMinLen ≤ (l.take Transcrypt.V3Wire.fileMinLen).length := by
      rw [List.length_take]; omega
    rw [if_pos ht, if_pos h, List.take_take, List.drop_take, List.take_take]
    rfl
  · have ht : ¬ Transcrypt.V3Wire.fileMinLen ≤ (l.take Transcrypt.V3Wire.fileMinLen).length := by
      rw [List.length_take]; omega
    rw [if_neg ht, if_neg h]

/-- Two never-failing Boolean programs deciding the same proposition are
    the same program. -/
theorem bool_spec_unique {m m' : RustM Bool} {Q : Prop}
    (h : m ⦃ r => r = true ↔ Q ⦄) (h' : m' ⦃ r => r = true ↔ Q ⦄) : m = m' := by
  cases m <;> cases m' <;> simp only [WP.spec_ok, WP.spec_fail, WP.spec_div] at h h' ⊢
  rename_i r r'
  cases r <;> cases r' <;> simp_all

/-- The keyless envelope of a record is decided by its size and its first
    `ENVELOPE_PREFIX_LEN` (`FILE_MIN_LEN`) bytes: given only those, as a
    reader that skips the rest of the blob has them,
    `record_envelope_prefix_ok` is the very program `record_envelope_ok`
    of the whole record. -/
theorem record_envelope_prefix_ok_record (record «prefix» : Slice U8) (id : Std.Array U8 16#usize)
    (hprefix : sliceBytes «prefix» = (sliceBytes record).take Transcrypt.V3Wire.fileMinLen) :
    record_envelope_prefix_ok record.len «prefix» id = record_envelope_ok record id := by
  apply bool_spec_unique _ (record_envelope_ok_spec record id)
  apply WP.spec_mono (record_envelope_prefix_ok_spec record.len «prefix» id)
  intro r hr
  rw [hr, hprefix, decodeFileHeaderShape_take]
  unfold Transcrypt.V3Policy.EnvelopeOk
  have hrl : record.len.val = record.length := by simp
  have hpl : «prefix».length ≤ record.length := by
    rw [← sliceBytes_length «prefix», hprefix, List.length_take, sliceBytes_length]; omega
  rw [hrl, sliceBytes_length]
  constructor
  · exact fun ⟨_, hmax, _, hd⟩ => ⟨hmax, hd⟩
  · intro ⟨hmax, hd⟩
    have := decodeFileHeaderShape_length hd
    rw [sliceBytes_length] at this
    exact ⟨this, hmax, hpl, hd⟩

/-! ## Smudge decision -/

/-- Rust encoding of the specification's smudge decision. -/
def smudgeResult : Transcrypt.V3Policy.SmudgeAction → SmudgeAction
  | .open_ => .Open
  | .keep => .Keep

/-- `smudge_action` makes exactly the spec's smudge decision: `Ok` with the
    spec's action when `smudgeSpec` decides one, and a refusal exactly when
    `smudgeSpec` refuses (`Size` for an oversized blob, `Foreign` for bytes
    without the v3 file envelope). -/
@[step]
theorem smudge_action_spec (blob : Slice U8) (id : Std.Array U8 16#usize) (unlocked : Bool) :
    smudge_action blob id unlocked ⦃ r => match r with
      | core.result.Result.Ok a => ∃ s, Transcrypt.V3Policy.smudgeSpec (sliceBytes blob)
          (wireBytes id) unlocked = some s ∧ a = smudgeResult s
      | core.result.Result.Err e =>
          Transcrypt.V3Policy.smudgeSpec (sliceBytes blob) (wireBytes id) unlocked = none ∧
          (e = Refusal.Size ∧ Transcrypt.V3Policy.maxRecord < blob.length ∨
           e = Refusal.Foreign ∧ blob.length ≤ Transcrypt.V3Policy.maxRecord ∧
             Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes blob) = none) ⦄ := by
  unfold smudge_action Transcrypt.V3Policy.smudgeSpec
  simp_len
  have hrl : blob.len.val = blob.length := by simp
  have hbl := sliceBytes_length blob
  have := usize_max_ge
  step with MAX_RECORD_spec as ⟨ i1, i1_post ⟩
  split
  · rename_i hgt
    have hgt' : Transcrypt.V3Policy.maxRecord < blob.length := by
      simp only [gt_iff_lt, UScalar.lt_equiv, i1_post, hrl] at hgt; exact hgt
    simp only [WP.spec_ok, hbl, gt_iff_lt, hgt', if_true, true_and]
    simp
  · rename_i hgt
    have hle : blob.length ≤ Transcrypt.V3Policy.maxRecord := by
      simp only [gt_iff_lt, UScalar.lt_equiv, not_lt, i1_post, hrl] at hgt; exact hgt
    have hng : ¬ (sliceBytes blob).length > Transcrypt.V3Policy.maxRecord := by omega
    rw [if_neg hng]
    step with parse_file_header_spec as ⟨ r, hr ⟩
    cases r with
    | Ok found =>
      simp only at hr ⊢
      rw [hr]
      simp only
      split
      · rename_i hu
        step*
        all_goals
          have hiff : b = true ↔ wireBytes found = wireBytes id := by
            rw [b_post, s_post, s1_post, wireBytes_inj]; rfl
        · rename_i hb
          exact ⟨_, by rw [if_pos ⟨hu, hiff.mp hb⟩], rfl⟩
        · rename_i hb
          exact ⟨_, by rw [if_neg (fun h => hb (hiff.mpr h.2))], rfl⟩
      · rename_i hu
        simp only [WP.spec_ok]
        exact ⟨_, by rw [if_neg (fun h => hu h.1)], rfl⟩
    | Err e =>
      have hnone : Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes blob) = none := by
        cases e with
        | Magic => exact hr.2
        | Length => exact Transcrypt.V3Wire.file_truncated _ (by rw [hbl]; exact hr)
      simp [WP.spec_ok, hnone, hle]

end Transcrypt.V3Verification

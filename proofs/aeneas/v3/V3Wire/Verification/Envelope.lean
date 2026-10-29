import V3Wire.Verification.Codec

/-!
Functional refinement of two keyless production checks used by the Git
adapter: `is_object_id` accepts exactly the Git object names of
`Transcrypt.V3Policy.ObjectId` (40 or 64 lowercase hexadecimal digits), and
`record_envelope_ok` accepts exactly the records satisfying
`Transcrypt.V3Policy.EnvelopeOk` (size bound plus a v3 file header naming the
given configuration id). As `WP.spec` triples they also exclude panics and
divergence.
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
      (l.length = 40 ∨ l.length = 64) ∧ EnvHexUpTo l l.length := by
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
  have key := env_oid_loop_spec oid oid.len (by simp) (oid.length = 40 ∨ oid.length = 64)
  -- The length test `(n == 40) | (n == 64)` computes the admissible-length flag.
  apply key
  simp [UScalar.eq_equiv]

/-- `record_envelope_ok` accepts exactly the records whose keyless envelope
    is valid for configuration id `id`. -/
@[step]
theorem record_envelope_ok_spec (record : Slice U8) (id : Std.Array U8 16#usize) :
    record_envelope_ok record id ⦃ r => r = true ↔
      Transcrypt.V3Policy.EnvelopeOk (sliceBytes record) (wireBytes id) ⦄ := by
  unfold record_envelope_ok Transcrypt.V3Policy.EnvelopeOk
  simp_len
  have hrl : record.len.val = record.length := by simp
  have hbl := sliceBytes_length record
  have := usize_max_ge
  step with MAX_RECORD_spec as ⟨ i1, i1_post ⟩
  split
  · rename_i hgt
    simp only [gt_iff_lt, UScalar.lt_equiv, i1_post, hrl] at hgt
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and, hbl]
    intro h; omega
  · rename_i hgt
    have hmax : record.length ≤ Transcrypt.V3Policy.maxRecord := by
      simp only [gt_iff_lt, UScalar.lt_equiv, not_lt, i1_post, hrl] at hgt
      exact hgt
    step with parse_file_header_spec as ⟨ r, hr ⟩
    cases r with
    | Ok found =>
      simp only at hr ⊢
      step*
      rw [r_post, s_post, s1_post, hr, hbl, Option.some_inj]
      simp only [hmax, true_and, Array.to_slice]
      exact (wireBytes_inj found id).symm
    | Err e =>
      simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
      intro _
      cases e with
      | Magic =>
        simp only at hr
        rw [hr.2]; simp
      | Length =>
        simp only at hr
        rw [Transcrypt.V3Wire.file_truncated _ (by omega)]
        simp

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

import V3Wire.Verification.Protocol
import Transcrypt.V3Policy
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
namespace Transcrypt.V3Verification
open transcrypt_v3_core

/-!
Functional refinement of two keyless production checks used by the Git
adapter: `is_object_id` accepts exactly the Git object names of
`Transcrypt.V3Policy.ObjectId` (40 or 64 lowercase hexadecimal digits), and
`record_envelope_ok` accepts exactly the records satisfying
`Transcrypt.V3Policy.EnvelopeOk` (size bound plus a v3 file header naming the
given configuration id). As `WP.spec` triples they also exclude panics and
divergence.
-/

theorem env_sliceBytes_length (s : Slice U8) : (sliceBytes s).length = s.length := by
  simp [sliceBytes]

theorem env_sliceBytes_getElem! (p : Slice U8) (i : Nat) (h : i < p.val.length) :
    (sliceBytes p)[i]! = (p.val[i]).val := by
  rw [getElem!_pos (sliceBytes p) i (by simp [sliceBytes]; omega)]
  simp [sliceBytes]

/-- The digits examined so far are all lowercase hexadecimal. -/
def EnvHexUpTo (l : List Nat) (i : Nat) : Prop := ∀ k < i, Transcrypt.V3Policy.HexDigit l[k]!

/-- Invariant of the object-name scan: `ok` records exactly whether the length
    is admissible and every examined digit is hexadecimal. -/
def EnvOidInv (oid : Slice U8) (lenOk : Prop) (s : Bool × Usize) : Prop :=
  s.2.val ≤ oid.length ∧ (s.1 = true ↔ lenOk ∧ EnvHexUpTo (sliceBytes oid) s.2.val)

/-- The per-digit test of `is_object_id` decides `HexDigit`. -/
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
    have hb := env_sliceBytes_getElem! oid i.val (by omega)
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
    rintro (⟨r', k'⟩ | r)
    · exact id
    · exact id
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
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  rw [env_objectId_iff, env_sliceBytes_length]
  have key := env_oid_loop_spec oid oid.len (by simp) (oid.length = 40 ∨ oid.length = 64)
  simp only [bind_tc_ok]
  -- The length test `n == 40 || n == 64` computes the admissible-length flag.
  split_ifs <;> simp only [bind_tc_ok] <;> apply key <;> simp_all [UScalar.eq_equiv]

/-- `record_envelope_ok` accepts exactly the records whose keyless envelope
    is valid for configuration id `id`. -/
@[step]
theorem record_envelope_ok_spec (record : Slice U8) (id : Std.Array U8 16#usize) :
    record_envelope_ok record id ⦃ r => r = true ↔
      Transcrypt.V3Policy.EnvelopeOk (sliceBytes record) (wireBytes id) ⦄ := by
  unfold record_envelope_ok Transcrypt.V3Policy.EnvelopeOk
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hrl : record.len.val = record.length := by simp
  have hbl := env_sliceBytes_length record
  have := usize_max_ge
  step with FILE_MIN_LEN_spec as ⟨ i1, i1_post ⟩
  split
  · rename_i hlt
    have : record.length < 38 := by
      simp only [UScalar.lt_equiv, hrl, i1_post] at hlt; exact hlt
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
    intro _
    rw [Transcrypt.V3Wire.file_truncated _ (by omega)]
    simp
  · rename_i hge
    simp only [UScalar.lt_equiv, hrl, i1_post, not_lt] at hge
    step with MAX_RECORD_spec as ⟨ i2, i2_post ⟩
    split
    · rename_i hgt
      simp only [gt_iff_lt, UScalar.lt_equiv, i2_post, hrl] at hgt
      simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and, hbl]
      intro h; omega
    · rename_i hgt
      have hmax : record.length ≤ Transcrypt.V3Policy.maxRecord := by
        simp only [gt_iff_lt, UScalar.lt_equiv, not_lt, i2_post, hrl] at hgt
        exact hgt
      step with parse_file_header_spec as ⟨ r, hr ⟩
      cases r with
      | Ok found =>
        simp only at hr ⊢
        step*
        rw [r_post, s_post, s1_post, hr, hbl, Option.some_inj]
        simp only [hmax, true_and, Array.to_slice]
        constructor
        · intro h; simp only [wireBytes]; rw [h]
        · intro h; exact map_val_injective h
      | Err e =>
        simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
        intro _
        cases e with
        | Magic =>
          simp only at hr
          rw [hr.2]; simp
        | Length =>
          simp only at hr
          omega

end Transcrypt.V3Verification

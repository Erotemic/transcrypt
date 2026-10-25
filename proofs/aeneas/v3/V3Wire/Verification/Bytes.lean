import V3Wire.Verification.Copy
import Transcrypt.V3Policy
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
namespace Transcrypt.V3Verification
open transcrypt_v3_core

/-!
Functional refinement of the production v3 byte-comparison decisions: byte
equality and the hydrate/lock lifecycle decisions. Each theorem names the Aeneas-generated translation and
relates its complete result to the independent specification in
`Transcrypt.V3Policy`; as `WP.spec` triples they also exclude panics and
divergence.
-/

theorem bytes_eq_loop_spec (a b : Slice U8) (hlen : a.length = b.length) (i : Usize)
    (hi : i.val ≤ a.length) (h : MatchesUpTo a.val b.val 0 i.val) :
    bytes_eq_loop a b i ⦃ r => r = true ↔ a.val = b.val ⦄ := by
  unfold bytes_eq_loop
  apply compare_loop _ (fun n => MatchesUpTo a.val b.val 0 n) a.length _ _ i hi h
  intro j hj hc
  unfold bytes_eq_loop.body
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  step*
  · refine ⟨i4_post, by omega, ?_⟩
    rw [i4_post]
    apply hc.step
    have hne := ‹¬(_ != _) = true›
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    rw [Nat.zero_add, getElem!_pos a.val j.val i2, getElem!_pos b.val j.val i3, ← i2_post2, ← i3_post2, hne]
  · rename_i hge
    have hj' : a.length ≤ j.val := by scalar_tac
    simp only [true_iff]
    apply List.ext_getElem (by simpa using hlen)
    intro k h1 h2
    have := hc k (by have : a.length = a.val.length := rfl; omega)
    rwa [Nat.zero_add, getElem!_pos a.val k h1, getElem!_pos b.val k h2] at this

@[step]
theorem bytes_eq_spec (a b : Slice U8) :
    bytes_eq a b ⦃ r => r = true ↔ a.val = b.val ⦄ := by
  unfold bytes_eq
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  step*
  rename_i hne
  have hlen : a.length = b.length := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    scalar_tac
  exact bytes_eq_loop_spec a b hlen 0#usize (by simp) (MatchesUpTo.zero _ _ _)

theorem sliceBytes_inj (a b : Slice U8) : sliceBytes a = sliceBytes b ↔ a.val = b.val := by
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun x y hxy => UScalar.eq_of_val_eq hxy) h
  · intro h
    simp [sliceBytes, h]

theorem map_prefix_drop_iff (l p : List U8) (j : Nat) (hj : j ≤ l.length) :
    p.map (·.val) <+: (l.map (·.val)).drop j ↔
      j + p.length ≤ l.length ∧ MatchesUpTo l p j p.length := by
  rw [List.prefix_iff_eq_take]
  simp only [List.length_map]
  constructor
  · intro h
    have hlen := congrArg List.length h
    simp only [List.length_map, List.length_take, List.length_drop] at hlen
    refine ⟨by omega, fun k hk => ?_⟩
    have h2 := List.getElem_of_eq h (i := k) (by simpa using hk)
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop] at h2
    rw [getElem!_pos l (j + k) (by omega), getElem!_pos p k hk]
    exact UScalar.eq_of_val_eq h2.symm
  · rintro ⟨hlen, hm⟩
    apply List.ext_getElem (by simp; omega)
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    have := hm k (by simpa using h1)
    rw [getElem!_pos l (j + k) (by simp at h1; omega), getElem!_pos p k (by simpa using h1)] at this
    rw [this]

theorem sliceBytes_length (s : Slice U8) : (sliceBytes s).length = s.length := by
  simp [sliceBytes]

theorem sliceBytes_getElem (s : Slice U8) (k : Nat) (h : k < s.length) :
    (sliceBytes s)[k]'(by rw [sliceBytes_length]; exact h) = (s.val[k]'h).val := by
  simp [sliceBytes]

/-! ## Lifecycle decisions -/

/-- Rust encoding of the specification's hydrate decision. -/
def hydrateResult : Option Transcrypt.V3Policy.HydrateAction →
    core.result.Result HydrateAction Refusal
  | some .publish => .Ok .Publish
  | some .keep => .Ok .Keep
  | none => .Err .UnexpectedWorktree

/-- Rust encoding of the specification's lock decision. -/
def lockResult : Option Transcrypt.V3Policy.LockAction →
    core.result.Result LockAction Refusal
  | some .keep => .Ok .Keep
  | some .flush => .Ok .Flush
  | none => .Err .UnexpectedWorktree

theorem hydrateResult_injective : Function.Injective hydrateResult := by
  intro a b h
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> first | rfl | cases h

theorem lockResult_injective : Function.Injective lockResult := by
  intro a b h
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> first | rfl | cases h

@[step]
theorem hydrate_action_spec (w r p : Slice U8) :
    hydrate_action w r p ⦃ res =>
      res = hydrateResult
        (Transcrypt.V3Policy.hydrateSpec (sliceBytes w) (sliceBytes r) (sliceBytes p)) ⦄ := by
  unfold hydrate_action
  step*
  all_goals simp_all [Transcrypt.V3Policy.hydrateSpec, hydrateResult, sliceBytes_inj]

@[step]
theorem lock_action_spec (w r s : Slice U8) :
    lock_action w r s ⦃ res =>
      res = lockResult
        (Transcrypt.V3Policy.lockSpec (sliceBytes w) (sliceBytes r) (sliceBytes s)) ⦄ := by
  unfold lock_action
  step*
  all_goals simp_all [Transcrypt.V3Policy.lockSpec, lockResult, sliceBytes_inj]

end Transcrypt.V3Verification

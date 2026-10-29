import V3Wire.Verification.Bytes

/-!
Functional refinement of the production Git index-record parser
`parse_index_entry`: it accepts exactly the records described by
`Transcrypt.V3Policy.IndexRecord`, returning the regular-mode flag and the
offset of the path (everything after the first TAB). The TAB is found with
`find_byte` and the mode compared with `matches_at`, both proved in `Bytes`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core

/-- `matches_at entry 0 M` for a six-byte mode `M` (the post of
    `matches_at_spec`) says exactly whether the entry starts with `M`. -/
theorem matches_mode_iff (entry : Slice U8) (M : Std.Array U8 6#usize) (m : List Nat)
    (hM : sliceBytes M.to_slice = m) :
    (0 ≤ entry.length ∧ sliceBytes M.to_slice <+: (sliceBytes entry).drop 0) ↔
      (sliceBytes entry).take 6 = m := by
  have hm : m.length = 6 := by rw [← hM, sliceBytes_length]; simp
  rw [hM, List.drop_zero, List.prefix_iff_eq_take, hm]
  exact ⟨fun h => h.2.symm, fun h => ⟨Nat.zero_le _, h.symm⟩⟩

theorem drop_three (l : List Nat) (j : Nat) (hj : j + 2 < l.length) :
    l.drop j = [l[j]!, l[j+1]!, l[j+2]!] ++ l.drop (j + 3) := by
  rw [List.drop_eq_getElem_cons (by omega : j < l.length),
    List.drop_eq_getElem_cons (by omega : j + 1 < l.length),
    List.drop_eq_getElem_cons (by omega : j + 1 + 1 < l.length),
    getElem!_pos l j (by omega), getElem!_pos l (j+1) (by omega), getElem!_pos l (j+2) (by omega)]
  rfl

theorem index_sound (l : List Nat) (t : Nat) (reg : Bool) (h10 : 10 ≤ t)
    (hn : t + 1 < l.length) (h9 : l[t]! = 9) (hno : ∀ k < t, l[k]! ≠ 9)
    (h6 : l[6]! = 32) (h2 : l[t-2]! = 32) (h1 : l[t-1]! = 48)
    (hreg : reg = true ↔ l.take 6 = Transcrypt.V3Policy.regularMode ∨
      l.take 6 = Transcrypt.V3Policy.executableMode) :
    Transcrypt.V3Policy.IndexRecord l reg (l.drop (t+1)) := by
  have hsplit : l = l.take 6 ++ [32] ++ (l.drop 7).take (t - 9) ++ [32, 48, 9] ++ l.drop (t+1) := by
    have e3 := drop_three l (t - 2) (by omega)
    have ht3 : t - 2 + 3 = t + 1 := by omega
    have ht1 : t - 2 + 1 = t - 1 := by omega
    have ht2 : t - 2 + 2 = t := by omega
    rw [ht3, ht1, ht2, h2, h1, h9] at e3
    have e6 := List.drop_eq_getElem_cons (by omega : 6 < l.length)
    rw [← getElem!_pos l 6 (by omega), h6] at e6
    have e7 : l.drop 7 = (l.drop 7).take (t - 9) ++ l.drop (t - 2) := by
      conv_lhs => rw [← List.take_append_drop (t - 9) (l.drop 7)]
      rw [List.drop_drop]
      congr 2
      omega
    conv_lhs => rw [← List.take_append_drop 6 l, e6, e7, e3]
    simp
  refine ⟨l.take 6, (l.drop 7).take (t - 9), hsplit, by simp; omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg List.length h; simp at this; omega
  · intro hm
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
    simp only [List.getElem_take, List.length_take] at he hi
    exact hno i (by omega) (by rw [getElem!_pos l i (by omega), he])
  · intro hm
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
    simp only [List.getElem_take, List.getElem_drop, List.length_take, List.length_drop] at he hi
    exact hno (7 + i) (by omega) (by rw [getElem!_pos l (7 + i) (by omega), he])
  · intro h; have := congrArg List.length h; simp at this; omega
  · exact hreg

theorem index_complete (l : List Nat) (reg : Bool) (path : List Nat)
    (h : Transcrypt.V3Policy.IndexRecord l reg path) :
    ∃ t, 10 ≤ t ∧ t + 1 < l.length ∧ l[t]! = 9 ∧ (∀ k < t, l[k]! ≠ 9) ∧
      l[6]! = 32 ∧ l[t-2]! = 32 ∧ l[t-1]! = 48 ∧ path = l.drop (t+1) ∧
      (reg = true ↔ l.take 6 = Transcrypt.V3Policy.regularMode ∨
        l.take 6 = Transcrypt.V3Policy.executableMode) := by
  obtain ⟨mode, oid, rfl, hm, ho, h9m, h9o, hp, hreg⟩ := h
  unfold_v3_bytes
  have hol : 0 < oid.length := List.length_pos_iff.mpr ho
  have hpl : 0 < path.length := List.length_pos_iff.mpr hp
  let A := mode ++ [32] ++ oid ++ [32, 48]
  have hA : A.length = 9 + oid.length := by simp [A, hm]; omega
  have hl : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = A ++ (9 :: path) := by simp [A]
  have h9A : 9 ∉ A := by simp [A, h9m, h9o]
  refine ⟨9 + oid.length, by omega, by simp [hm]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl, ← hA]; exact getElem!_append_length_add A (9 :: path) 0
  · intro k hk h9
    rw [hl, List.getElem!_append_left A _ k (by omega), getElem!_pos A k (by omega)] at h9
    exact h9A (h9 ▸ List.getElem_mem (by omega))
  · have : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = mode ++ (32 :: (oid ++ [32, 48, 9] ++ path)) := by simp
    rw [this, show 6 = mode.length + 0 by omega, getElem!_append_length_add]; rfl
  · have : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = (mode ++ [32] ++ oid) ++ (32 :: 48 :: 9 :: path) := by simp
    rw [this, show 9 + oid.length - 2 = (mode ++ [32] ++ oid).length + 0 by simp [hm]; omega,
      getElem!_append_length_add]; rfl
  · have : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = (mode ++ [32] ++ oid) ++ (32 :: 48 :: 9 :: path) := by simp
    rw [this, show 9 + oid.length - 1 = (mode ++ [32] ++ oid).length + 1 by simp [hm]; omega,
      getElem!_append_length_add]; rfl
  · rw [hl, show 9 + oid.length + 1 = (A ++ [9]).length by simp [hA]]
    simp
  · rw [hreg]
    have : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = mode ++ ([32] ++ oid ++ [32, 48, 9] ++ path) := by simp
    rw [this, List.take_left' hm]

@[step]
theorem parse_index_entry_spec (entry : Slice U8) :
    parse_index_entry entry ⦃ r => match r with
      | core.result.Result.Ok e =>
          Transcrypt.V3Policy.IndexRecord (sliceBytes entry) e.regular ((sliceBytes entry).drop e.path_start.val)
      | core.result.Result.Err _ =>
          ∀ reg path, ¬ Transcrypt.V3Policy.IndexRecord (sliceBytes entry) reg path ⦄ := by
  unfold parse_index_entry
  simp_len
  have hl := sliceBytes_length entry
  have hmax := usize_max_ge
  have hrl : entry.length = entry.val.length := rfl
  step with find_byte_spec entry 0#usize 9#u8 as ⟨ t, hscan, ht9 ⟩
  obtain ⟨-, htn, hno⟩ := hscan
  have htle : t.val ≤ entry.length := by rcases htn with h | h <;> simp_all
  have hno' : ∀ k < t.val, (sliceBytes entry)[k]! ≠ 9 := fun k hk => hno k (Nat.zero_le _) hk
  -- Every record's first TAB is at `t`.
  have key : ∀ reg path, Transcrypt.V3Policy.IndexRecord (sliceBytes entry) reg path →
      10 ≤ t.val ∧ t.val + 1 < (sliceBytes entry).length ∧ (sliceBytes entry)[6]! = 32 ∧
      (sliceBytes entry)[t.val-2]! = 32 ∧ (sliceBytes entry)[t.val-1]! = 48 := by
    intro reg path h
    obtain ⟨t0, h10, hn0, h90, hno0, h6, h2, h1, _⟩ := index_complete _ _ _ h
    have : t0 = t.val := by
      rcases Nat.lt_trichotomy t0 t.val with hlt | heq | hgt
      · exact absurd h90 (hno' t0 hlt)
      · exact heq
      · exact absurd (ht9 (by omega)) (hno0 t.val hgt)
    subst this
    exact ⟨h10, hn0, h6, h2, h1⟩
  have hbyte : ∀ (k : Nat) (hk : k < entry.val.length) (b : U8), b = entry.val[k] →
      ∀ c : U8, ¬(b != c) = true → (sliceBytes entry)[k]! = c.val := by
    intro k hk b hb c hne
    simp_bne at hne
    rw [sliceBytes_getElem! entry k hk, ← hb, hne]
  step*
  have h6 : (sliceBytes entry)[6]! = 32 := hbyte 6 (by omega) _ i1_post2 32#u8 ‹_›
  have h2 : (sliceBytes entry)[t.val - 2]! = 32 := by
    rw [← i2_post1]; exact hbyte i2.val (by omega) _ i3_post2 32#u8 ‹_›
  have h1 : (sliceBytes entry)[t.val - 1]! = 48 := by
    rw [← i4_post1]; exact hbyte i4.val (by omega) _ i5_post2 48#u8 ‹_›
  have hsound := index_sound (sliceBytes entry) t.val (h10 := by scalar_tac)
    (hn := by scalar_tac) (h9 := ht9 (by scalar_tac)) (hno := hno') (h6 := h6) (h2 := h2) (h1 := h1)
  rw [s_post, matches_mode_iff entry _ _ REGULAR_MODE_bytes] at b_post
  split
  · step*
    scalar_tac
  · step as ⟨ s1, s1_post ⟩
    step with matches_at_spec as ⟨ b1, hb1 ⟩
    rw [s1_post, matches_mode_iff entry _ _ EXECUTABLE_MODE_bytes] at hb1
    step*
    scalar_tac

end Transcrypt.V3Verification

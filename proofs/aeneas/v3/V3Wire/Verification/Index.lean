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

/-- `matches_at entry 0 M` for a mode `M` (the post of `matches_at_spec`)
    says exactly whether the entry starts with `M`. -/
theorem matches_mode_iff (entry : Slice U8) (M : Std.Array U8 6#usize) (m : List Nat)
    (hM : sliceBytes M.to_slice = m) :
    (0 ≤ entry.length ∧ sliceBytes M.to_slice <+: (sliceBytes entry).drop 0) ↔
      (sliceBytes entry).take Transcrypt.V3Policy.modeLen = m := by
  have hm : m.length = Transcrypt.V3Policy.modeLen := by rw [← hM, sliceBytes_length]; simp
  rw [hM, List.drop_zero, List.prefix_iff_eq_take, hm]
  exact ⟨fun h => h.2.symm, fun h => ⟨Nat.zero_le _, h.symm⟩⟩

theorem drop_three (l : List Nat) (j : Nat) (hj : j + 2 < l.length) :
    l.drop j = [l[j]!, l[j+1]!, l[j+2]!] ++ l.drop (j + 3) := by
  rw [List.drop_eq_getElem_cons (by omega : j < l.length),
    List.drop_eq_getElem_cons (by omega : j + 1 < l.length),
    List.drop_eq_getElem_cons (by omega : j + 1 + 1 < l.length),
    getElem!_pos l j (by omega), getElem!_pos l (j+1) (by omega), getElem!_pos l (j+2) (by omega)]
  rfl

open Transcrypt.V3Policy (tab space digitZero modeLen oidEndLen entryFixedLen) in
/-- The offsets are those of the extracted parser: the mode is the first
    `modeLen` bytes, the object id starts at `oidStart`, the first TAB `t` is
    at least `entryFixedLen`, and `SP 0 TAB` ends at it. -/
theorem index_sound (l : List Nat) (t : Nat) (reg : Bool) (h10 : entryFixedLen ≤ t)
    (hn : t + 1 < l.length) (hno : ∀ k < t, l[k]! ≠ tab)
    (h6 : l[modeLen]! = space) (hend : [space, digitZero, tab] <+: l.drop (t + 1 - oidEndLen))
    (hreg : reg = true ↔ l.take modeLen = Transcrypt.V3Policy.regularMode ∨
      l.take modeLen = Transcrypt.V3Policy.executableMode) :
    Transcrypt.V3Policy.IndexRecord l reg (l.drop (t+1)) := by
  unfold_v3_bytes
  have hsplit : l = l.take 6 ++ [32] ++ (l.drop 7).take (t - 9) ++ [32, 48, 9] ++ l.drop (t+1) := by
    have e3 : l.drop (t - 2) = [32, 48, 9] ++ l.drop (t + 1) := by
      rw [show t + 1 - 3 = t - 2 by omega] at hend
      obtain ⟨u, hu⟩ := hend
      have hu' : u = l.drop (t + 1) := by
        have := congrArg (List.drop 3) hu
        rw [List.drop_drop, show t - 2 + 3 = t + 1 by omega] at this
        simpa using this
      rw [← hu, hu']
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

open Transcrypt.V3Policy (tab space digitZero modeLen oidEndLen entryFixedLen) in
theorem index_complete (l : List Nat) (reg : Bool) (path : List Nat)
    (h : Transcrypt.V3Policy.IndexRecord l reg path) :
    ∃ t, entryFixedLen ≤ t ∧ t + 1 < l.length ∧ l[t]! = tab ∧ (∀ k < t, l[k]! ≠ tab) ∧
      l[modeLen]! = space ∧ [space, digitZero, tab] <+: l.drop (t + 1 - oidEndLen) ∧
      path = l.drop (t+1) ∧
      (reg = true ↔ l.take modeLen = Transcrypt.V3Policy.regularMode ∨
        l.take modeLen = Transcrypt.V3Policy.executableMode) := by
  obtain ⟨mode, oid, rfl, hm, ho, h9m, h9o, hp, hreg⟩ := h
  unfold_v3_bytes
  have hol : 0 < oid.length := List.length_pos_iff.mpr ho
  have hpl : 0 < path.length := List.length_pos_iff.mpr hp
  let A := mode ++ [32] ++ oid ++ [32, 48]
  have hA : A.length = 9 + oid.length := by simp [A, hm]; omega
  have hl : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = A ++ (9 :: path) := by simp [A]
  have h9A : 9 ∉ A := by simp [A, h9m, h9o]
  refine ⟨9 + oid.length, by omega, by simp [hm]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl, ← hA]; exact getElem!_append_length_add A (9 :: path) 0
  · intro k hk h9
    rw [hl, List.getElem!_append_left A _ k (by omega), getElem!_pos A k (by omega)] at h9
    exact h9A (h9 ▸ List.getElem_mem (by omega))
  · have : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = mode ++ (32 :: (oid ++ [32, 48, 9] ++ path)) := by simp
    rw [this, show 6 = mode.length + 0 by omega, getElem!_append_length_add]; rfl
  · have : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = (mode ++ [32] ++ oid) ++ ([32, 48, 9] ++ path) := by simp
    rw [this, show 9 + oid.length + 1 - 3 = (mode ++ [32] ++ oid).length by simp [hm]; omega, List.drop_left]
    exact List.prefix_append _ _
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
      Transcrypt.V3Policy.entryFixedLen ≤ t.val ∧ t.val + 1 < (sliceBytes entry).length ∧
      (sliceBytes entry)[Transcrypt.V3Policy.modeLen]! = 32 ∧
      [32, 48, 9] <+: (sliceBytes entry).drop (t.val + 1 - Transcrypt.V3Policy.oidEndLen) := by
    intro reg path h
    obtain ⟨t0, h10, hn0, h90, hno0, h6, hend, _⟩ := index_complete _ _ _ h
    have : t0 = t.val := by
      rcases Nat.lt_trichotomy t0 t.val with hlt | heq | hgt
      · exact absurd h90 (hno' t0 hlt)
      · exact heq
      · exact absurd (ht9 (by omega)) (hno0 t.val hgt)
    subst this
    exact ⟨h10, hn0, h6, hend⟩
  have hbyte : ∀ (k : Nat) (hk : k < entry.val.length) (b : U8), b = entry.val[k] →
      ∀ c : U8, ¬(b != c) = true → (sliceBytes entry)[k]! = c.val := by
    intro k hk b hb c hne
    simp_bne at hne
    rw [sliceBytes_getElem! entry k hk, ← hb, hne]
  step*
  all_goals
    have h6 : (sliceBytes entry)[Transcrypt.V3Policy.modeLen]! = 32 := by
      have := hbyte MODE_LEN.val (by scalar_tac) _ i_post2 32#u8 ‹_›
      rwa [ MODE_LEN_val] at this
    have hi1 : i1.val = t.val + 1 - Transcrypt.V3Policy.oidEndLen := by
      rw [i1_post1, path_start_post, OID_END_LEN_val]
    rw [s_post, OID_END_bytes, hi1] at b_post
    have h10 : Transcrypt.V3Policy.entryFixedLen ≤ t.val := by scalar_tac
    have hn : t.val + 1 < (sliceBytes entry).length := by scalar_tac
  · rw [path_start_post]
    apply index_sound _ _ _ h10 hn hno' h6 (b_post.mp ‹b = true›).2
    rw [s1_post, matches_mode_iff entry _ _ REGULAR_MODE_bytes] at b1_post
    simp only [true_iff]; exact Or.inl (b1_post.mp ‹_›)
  · rw [path_start_post]
    apply index_sound _ _ _ h10 hn hno' h6 (b_post.mp ‹b = true›).2
    rw [s1_post, matches_mode_iff entry _ _ REGULAR_MODE_bytes] at b1_post
    rw [s2_post, matches_mode_iff entry _ _ EXECUTABLE_MODE_bytes] at regular_post
    rw [regular_post]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · exact absurd (b1_post.mpr h) ‹¬b1 = true›
      · exact h
  · intro reg path h
    obtain ⟨-, -, -, hend⟩ := key reg path h
    exact ‹¬b = true› (b_post.mpr ⟨by scalar_tac, hend⟩)

end Transcrypt.V3Verification

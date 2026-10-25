import V3Wire.Verification.Copy
import Transcrypt.V3Policy
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
namespace Transcrypt.V3Verification
open transcrypt_v3_core

/-!
Functional refinement of the production Git index-record parser
`parse_index_entry`: it accepts exactly the records described by
`Transcrypt.V3Policy.IndexRecord`, returning the regular-mode flag and the
offset of the path (everything after the first TAB). The first loop finds the
least TAB; the second compares the mode field with `REGULAR_MODE` and
`EXECUTABLE_MODE` at once.
-/

theorem idx_sliceBytes_length (s : Slice U8) : (sliceBytes s).length = s.length := by
  simp [sliceBytes]

theorem idx_sliceBytes_getElem! (p : Slice U8) (i : Nat) (h : i < p.val.length) :
    (sliceBytes p)[i]! = (p.val[i]).val := by
  rw [getElem!_pos (sliceBytes p) i (by simp [sliceBytes]; omega)]
  simp [sliceBytes]

/-- Invariant of the TAB scan. -/
def TabInv (l : List Nat) (t : Nat) (found : Bool) : Prop :=
  t ≤ l.length ∧ (∀ k < t, l[k]! ≠ 9) ∧ (found = true → t < l.length ∧ l[t]! = 9)

def TabPost (l : List Nat) (r : Usize × Bool) : Prop :=
  (r.2 = true → r.1.val < l.length ∧ l[r.1.val]! = 9 ∧ ∀ k < r.1.val, l[k]! ≠ 9) ∧
  (r.2 = false → ∀ k < l.length, l[k]! ≠ 9)

theorem tab_body_spec (entry : Slice U8) (n : Usize) (hn : n.val = entry.length)
    (t : Usize) (found : Bool) (hinv : TabInv (sliceBytes entry) t.val found) :
    parse_index_entry_loop0.body entry n t found ⦃ cf => match cf with
      | .cont (t', f') => TabInv (sliceBytes entry) t'.val f' ∧
          2 * (n.val - t'.val) + (if f' then 0 else 1) < 2 * (n.val - t.val) + (if found then 0 else 1)
      | .done r => TabPost (sliceBytes entry) r ⦄ := by
  have hl := idx_sliceBytes_length entry
  obtain ⟨hle, hno, hf⟩ := hinv
  unfold parse_index_entry_loop0.body
  cases found
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step*
    · have hi := i
      have hb : (sliceBytes entry)[t.val]! = 9 := by
        rw [idx_sliceBytes_getElem! entry t.val hi, ← i_post2]; have h9 : _ = 9#u8 := ‹_›; rw [h9]; rfl
      refine ⟨⟨hle, hno, fun _ => ⟨by rw [hl]; exact hi, hb⟩⟩, by simp⟩
    · have hi := i
      have hb : (sliceBytes entry)[t.val]! ≠ 9 := by
        rw [idx_sliceBytes_getElem! entry t.val hi, ← i_post2]
        intro h; exact ‹¬_ = 9#u8› (UScalar.eq_of_val_eq h)
      refine ⟨⟨by omega, fun k hk => ?_, by simp⟩, by simp; omega⟩
      rcases Nat.lt_or_ge k t.val with h | h
      · exact hno k h
      · have : k = t.val := by omega
        subst this; exact hb
    · rename_i hge
      have : entry.length ≤ t.val := by scalar_tac
      exact ⟨by simp, fun _ k hk => hno k (by omega)⟩
  · simp only [↓reduceIte]
    step*
    obtain ⟨h1, h2⟩ := hf rfl
    exact ⟨fun _ => ⟨h1, h2, hno⟩, by simp⟩

theorem tab_loop_spec (entry : Slice U8) (n : Usize) (hn : n.val = entry.length) :
    parse_index_entry_loop0 entry n 0#usize false ⦃ r => TabPost (sliceBytes entry) r ⦄ := by
  unfold parse_index_entry_loop0
  apply loop.spec_decr_nat (fun s => 2 * (n.val - s.1.val) + (if s.2 then 0 else 1))
    (fun s => TabInv (sliceBytes entry) s.1.val s.2)
  · rintro ⟨t, f⟩ hinv
    apply WP.spec_mono (tab_body_spec entry n hn t f hinv)
    rintro (⟨t', f'⟩ | r)
    · exact id
    · exact id
  · exact ⟨by simp, fun k hk => absurd hk (by simp), by simp⟩

theorem REGULAR_MODE_matches_spec :
    REGULAR_MODE.val.map (·.val) = Transcrypt.V3Policy.regularMode := by
  unfold REGULAR_MODE Transcrypt.V3Policy.regularMode Transcrypt.V3Policy.ascii
  decide

@[simp] theorem REGULAR_MODE_length : REGULAR_MODE.length = 6 := by simp

theorem EXECUTABLE_MODE_matches_spec :
    EXECUTABLE_MODE.val.map (·.val) = Transcrypt.V3Policy.executableMode := by
  unfold EXECUTABLE_MODE Transcrypt.V3Policy.executableMode Transcrypt.V3Policy.ascii
  decide

@[simp] theorem EXECUTABLE_MODE_length : EXECUTABLE_MODE.length = 6 := by simp

/-- Invariant of the mode comparison loop: each flag records whether the
    mode field agrees so far with the respective mode constant. -/
def RegInv (entry : Slice U8) (s : Bool × Bool × Usize) : Prop :=
  s.2.2.val ≤ 6 ∧ (s.1 = true ↔ MatchesUpTo entry.val REGULAR_MODE.val 0 s.2.2.val) ∧
    (s.2.1 = true ↔ MatchesUpTo entry.val EXECUTABLE_MODE.val 0 s.2.2.val)

theorem idx_ite_ok {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then (ok a : RustM α) else ok b) = ok (if c then a else b) := by
  split <;> rfl

theorem matches_flag_step (entry mode : List U8) (k : Nat) (hk : k < entry.length)
    (hm : k < mode.length) (flag : Bool) (x y : U8) (hx : x = entry[k]) (hy : y = mode[k])
    (hiff : flag = true ↔ MatchesUpTo entry mode 0 k) :
    (if (x != y) = true then false else flag) = true ↔ MatchesUpTo entry mode 0 (k + 1) := by
  subst hx hy
  by_cases hne : (entry[k] != mode[k]) = true
  · rw [if_pos hne]
    simp only [bne_iff_ne, ne_eq] at hne
    simp only [Bool.false_eq_true, false_iff]
    intro hm'
    apply hne
    have := hm' k (by omega)
    rwa [Nat.zero_add, getElem!_pos entry k hk, getElem!_pos mode k hm] at this
  · rw [if_neg hne, hiff]
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    constructor
    · intro h
      apply h.step
      rw [Nat.zero_add, getElem!_pos entry k hk, getElem!_pos mode k hm, hne]
    · intro h j hj
      exact h j (by omega)

theorem reg_body_spec (entry : Slice U8) (h6 : 6 ≤ entry.length) (plain executable : Bool)
    (k : Usize) (hinv : RegInv entry (plain, executable, k)) :
    parse_index_entry_loop1.body entry plain executable k ⦃ cf => match cf with
      | .cont s' => RegInv entry s' ∧ 6 - s'.2.2.val < 6 - k.val
      | .done r => (r.1 = true ↔ MatchesUpTo entry.val REGULAR_MODE.val 0 6) ∧
          (r.2 = true ↔ MatchesUpTo entry.val EXECUTABLE_MODE.val 0 6) ⦄ := by
  obtain ⟨hk, hp, he⟩ := hinv
  unfold parse_index_entry_loop1.body
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hF := REGULAR_MODE_length
  have hE := EXECUTABLE_MODE_length
  have hrl : entry.length = entry.val.length := rfl
  simp only at hk hp he
  simp only [idx_ite_ok]
  step*
  have hk' : k.val < entry.val.length := by omega
  simp only [RegInv]
  refine ⟨⟨by omega, ?_, ?_⟩, by omega⟩
  · rw [k1_post]
    exact matches_flag_step _ _ _ hk' (by simp; omega) _ _ _ i1_post2 i2_post2 hp
  · rw [k1_post]
    exact matches_flag_step _ _ _ hk' (by simp; omega) _ _ _ i1_post2 i3_post2 he

theorem reg_loop_spec (entry : Slice U8) (h6 : 6 ≤ entry.length) :
    parse_index_entry_loop1 entry true true 0#usize ⦃ r =>
      (r.1 = true ↔ MatchesUpTo entry.val REGULAR_MODE.val 0 6) ∧
      (r.2 = true ↔ MatchesUpTo entry.val EXECUTABLE_MODE.val 0 6) ⦄ := by
  unfold parse_index_entry_loop1
  apply loop.spec_decr_nat (fun s => 6 - s.2.2.val) (RegInv entry)
  · rintro ⟨p, e, k⟩ hinv
    apply WP.spec_mono (reg_body_spec entry h6 p e k hinv)
    rintro (⟨p', e', k'⟩ | r)
    · exact id
    · exact id
  · exact ⟨by simp, by simp [MatchesUpTo.zero], by simp [MatchesUpTo.zero]⟩

theorem idx_map_val_inj {a b : List U8} : a.map (·.val) = b.map (·.val) ↔ a = b := by
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun x y hxy => by
      simpa using (UScalar.eq_equiv x y).mpr hxy) h
  · rintro rfl; rfl

theorem matches_mode_iff (entry : Slice U8) (h6 : 6 ≤ entry.length) (mode : List U8)
    (hR : mode.length = 6) :
    MatchesUpTo entry.val mode 0 6 ↔
      (sliceBytes entry).take 6 = mode.map (·.val) := by
  rw [sliceBytes, ← List.map_take, idx_map_val_inj]
  have he : entry.length = entry.val.length := rfl
  constructor
  · intro h
    apply List.ext_getElem (by simp; omega)
    intro k h1 h2
    have := h k (by simp at h1; omega)
    rw [Nat.zero_add, getElem!_pos entry.val k (by simp at h1; omega),
      getElem!_pos mode k h2] at this
    simpa using this
  · intro h k hk
    rw [← h, Nat.zero_add, getElem!_pos entry.val k (by omega),
      getElem!_pos (entry.val.take 6) k (by simp; omega)]
    simp

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

theorem idx_getElem!_append_right (P S : List Nat) (j : Nat) : (P ++ S)[P.length + j]! = S[j]! := by
  simp only [getElem!_def, List.getElem?_append_right (by omega : P.length ≤ P.length + j),
    Nat.add_sub_cancel_left]

theorem idx_getElem!_append_left (P S : List Nat) (j : Nat) (h : j < P.length) :
    (P ++ S)[j]! = P[j]! := by
  simp only [getElem!_def, List.getElem?_append_left h]

theorem index_complete (l : List Nat) (reg : Bool) (path : List Nat)
    (h : Transcrypt.V3Policy.IndexRecord l reg path) :
    ∃ t, 10 ≤ t ∧ t + 1 < l.length ∧ l[t]! = 9 ∧ (∀ k < t, l[k]! ≠ 9) ∧
      l[6]! = 32 ∧ l[t-2]! = 32 ∧ l[t-1]! = 48 ∧ path = l.drop (t+1) ∧
      (reg = true ↔ l.take 6 = Transcrypt.V3Policy.regularMode ∨
        l.take 6 = Transcrypt.V3Policy.executableMode) := by
  obtain ⟨mode, oid, rfl, hm, ho, h9m, h9o, hp, hreg⟩ := h
  have hol : 0 < oid.length := List.length_pos_iff.mpr ho
  have hpl : 0 < path.length := List.length_pos_iff.mpr hp
  let A := mode ++ [32] ++ oid ++ [32, 48]
  have hA : A.length = 9 + oid.length := by simp [A, hm]; omega
  have hl : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = A ++ (9 :: path) := by simp [A]
  have h9A : 9 ∉ A := by simp [A, h9m, h9o]
  refine ⟨9 + oid.length, by omega, by simp [hm]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl, ← hA]; exact idx_getElem!_append_right A (9 :: path) 0
  · intro k hk h9
    rw [hl, idx_getElem!_append_left A _ k (by omega), getElem!_pos A k (by omega)] at h9
    exact h9A (h9 ▸ List.getElem_mem (by omega))
  · have : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = mode ++ (32 :: (oid ++ [32, 48, 9] ++ path)) := by simp
    rw [this, show 6 = mode.length + 0 by omega, idx_getElem!_append_right]; rfl
  · have : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = (mode ++ [32] ++ oid) ++ (32 :: 48 :: 9 :: path) := by simp
    rw [this, show 9 + oid.length - 2 = (mode ++ [32] ++ oid).length + 0 by simp [hm]; omega,
      idx_getElem!_append_right]; rfl
  · have : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = (mode ++ [32] ++ oid) ++ (32 :: 48 :: 9 :: path) := by simp
    rw [this, show 9 + oid.length - 1 = (mode ++ [32] ++ oid).length + 1 by simp [hm]; omega,
      idx_getElem!_append_right]; rfl
  · rw [hl, show 9 + oid.length + 1 = (A ++ [9]).length by simp [hA]]
    simp
  · rw [hreg]
    have : mode ++ [32] ++ oid ++ [32, 48, 9] ++ path = mode ++ ([32] ++ oid ++ [32, 48, 9] ++ path) := by simp
    rw [this, List.take_left' hm]

theorem idx_usize_max_ge : 4294967295 ≤ Usize.max := by
  simp only [Usize.max, Usize.numBits]
  cases System.Platform.numBits_eq <;> simp [*]

@[step]
theorem parse_index_entry_spec (entry : Slice U8) :
    parse_index_entry entry ⦃ r => match r with
      | core.result.Result.Ok e =>
          Transcrypt.V3Policy.IndexRecord (sliceBytes entry) e.regular ((sliceBytes entry).drop e.path_start.val)
      | core.result.Result.Err _ =>
          ∀ reg path, ¬ Transcrypt.V3Policy.IndexRecord (sliceBytes entry) reg path ⦄ := by
  unfold parse_index_entry
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hl := idx_sliceBytes_length entry
  have hmax := idx_usize_max_ge
  have hrl : entry.length = entry.val.length := rfl
  step with tab_loop_spec entry entry.len (by simp) as ⟨ t, found, hr ⟩
  obtain ⟨hT, hF⟩ := hr
  simp only at hT hF
  cases found
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    intro reg path h
    obtain ⟨t0, _, hn0, h9, _⟩ := index_complete _ _ _ h
    exact hF rfl t0 (by omega) h9
  · obtain ⟨htn, ht9, hno⟩ := hT rfl
    simp only [↓reduceIte]
    have key : ∀ reg path, Transcrypt.V3Policy.IndexRecord (sliceBytes entry) reg path →
        10 ≤ t.val ∧ t.val + 1 < (sliceBytes entry).length ∧ (sliceBytes entry)[6]! = 32 ∧
        (sliceBytes entry)[t.val-2]! = 32 ∧ (sliceBytes entry)[t.val-1]! = 48 := by
      intro reg path h
      obtain ⟨t0, h10, hn0, h90, hno0, h6, h2, h1, _⟩ := index_complete _ _ _ h
      have : t0 = t.val := by
        rcases Nat.lt_trichotomy t0 t.val with hlt | heq | hgt
        · exact absurd h90 (hno t0 hlt)
        · exact heq
        · exact absurd ht9 (hno0 t.val hgt)
      subst this
      exact ⟨h10, hn0, h6, h2, h1⟩
    have hbyte : ∀ (k : Nat) (hk : k < entry.val.length) (b : U8), b = entry.val[k] →
        (sliceBytes entry)[k]! = b.val := by
      intro k hk b hb
      rw [idx_sliceBytes_getElem! entry k hk, hb]
    step*
    step with reg_loop_spec entry (by omega) as ⟨ plain, executable, hplain, hexec ⟩
    have hbyte' : ∀ (k : Nat) (hk : k < entry.val.length) (b : U8), b = entry.val[k] →
        ∀ c : U8, ¬(b != c) = true → (sliceBytes entry)[k]! = c.val := by
      intro k hk b hb c hne
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
      rw [hbyte k hk b hb, hne]
    have h6 : (sliceBytes entry)[6]! = 32 := hbyte' 6 (by omega) _ i1_post2 32#u8 ‹_›
    have h2 : (sliceBytes entry)[t.val - 2]! = 32 := by
      rw [← i2_post1]; exact hbyte' i2.val (by omega) _ i3_post2 32#u8 ‹_›
    have h1 : (sliceBytes entry)[t.val - 1]! = 48 := by
      rw [← i4_post1]; exact hbyte' i4.val (by omega) _ i5_post2 48#u8 ‹_›
    simp only [idx_ite_ok]
    step*
    case h_fail => scalar_tac
    rw [i6_post]
    apply index_sound _ t.val _ (by scalar_tac) (by scalar_tac) ht9 hno h6 h2 h1
    have hR := REGULAR_MODE_matches_spec
    have hE := EXECUTABLE_MODE_matches_spec
    rw [← hR, ← hE, ← matches_mode_iff entry (by omega) _ (by simp),
      ← matches_mode_iff entry (by omega) _ (by simp), ← hplain, ← hexec]
    cases plain <;> cases executable <;> simp

end Transcrypt.V3Verification

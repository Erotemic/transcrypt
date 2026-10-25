import V3Wire.Verification.Copy
import Transcrypt.V3Policy
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
namespace Transcrypt.V3Verification
open transcrypt_v3_core

theorem protected_suffix_matches_spec :
    PROTECTED_SUFFIX.val.map (·.val) = Transcrypt.V3Policy.protectedSuffix := by
  unfold PROTECTED_SUFFIX Transcrypt.V3Policy.protectedSuffix Transcrypt.V3Policy.ascii
  decide

theorem is_protected_path_loop_body_spec (path : Slice U8) (start k : Usize)
    (hs : start.val + 7 = path.length) (hk : k.val ≤ 7)
    (hm : MatchesUpTo path.val PROTECTED_SUFFIX.val start.val k.val) :
    is_protected_path_loop.body path start k ⦃ cf => match cf with
        | .cont k' => k'.val = k.val + 1 ∧ k'.val ≤ 7 ∧ MatchesUpTo path.val PROTECTED_SUFFIX.val start.val k'.val
        | .done r => r = true ↔ MatchesUpTo path.val PROTECTED_SUFFIX.val start.val 7 ⦄ := by
  unfold is_protected_path_loop.body
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hlen : PROTECTED_SUFFIX.length = 7 := by simp
  step*
  · rename_i hne
    simp only [Bool.false_eq_true, false_iff]
    intro hm7
    have := hm7 k.val (by omega)
    rw [← i1_post, getElem!_pos path.val i1.val i2, getElem!_pos PROTECTED_SUFFIX.val k.val (by simp; omega)] at this
    simp [i2_post2, i3_post2, this] at hne
  · rename_i hne
    refine ⟨k1_post, by omega, ?_⟩
    rw [k1_post]
    apply hm.step
    rw [← i1_post, getElem!_pos path.val i1.val i2, getElem!_pos PROTECTED_SUFFIX.val k.val (by simp; omega)]
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    rw [← i2_post2, ← i3_post2, hne]

theorem matchesUpTo_iff_drop (a b : List U8) (off m : Nat) (hb : b.length = m)
    (ha : a.length = off + m) : MatchesUpTo a b off m ↔ a.drop off = b := by
  constructor
  · intro h
    apply List.ext_getElem (by simp; omega)
    intro k h1 h2
    have := h k (by omega)
    rw [getElem!_pos a (off + k) (by omega), getElem!_pos b k h2] at this
    simpa using this
  · intro h k hk
    subst h
    rw [getElem!_pos a (off + k) (by omega), getElem!_pos (a.drop off) k (by simp; omega)]
    simp

theorem map_val_inj {a b : List U8} : a.map (·.val) = b.map (·.val) ↔ a = b := by
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun x y hxy => by
      simpa using (UScalar.eq_equiv x y).mpr hxy) h
  · rintro rfl; rfl

theorem protected_iff (path : Slice U8) (hn : 7 ≤ path.length) :
    Transcrypt.V3Policy.Protected (sliceBytes path) ↔
      MatchesUpTo path.val PROTECTED_SUFFIX.val (path.length - 7) 7 := by
  rw [matchesUpTo_iff_drop _ _ _ _ (by simp) (by simp at hn ⊢; omega)]
  unfold Transcrypt.V3Policy.Protected sliceBytes
  rw [List.suffix_iff_eq_drop, ← protected_suffix_matches_spec, eq_comm]
  simp only [List.length_map, ← List.map_drop]
  have : PROTECTED_SUFFIX.val.length = 7 := by simp
  rw [this, map_val_inj]

theorem not_protected_of_short (path : Slice U8) (hn : path.length < 7) :
    ¬ Transcrypt.V3Policy.Protected (sliceBytes path) := by
  intro h
  have := h.length_le
  rw [← protected_suffix_matches_spec] at this
  simp [sliceBytes] at this hn
  omega

@[step]
theorem is_protected_path_spec (p : Slice U8) :
    is_protected_path p ⦃ r => r = true ↔ Transcrypt.V3Policy.Protected (sliceBytes p) ⦄ := by
  unfold is_protected_path is_protected_path_loop
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hlen : PROTECTED_SUFFIX.length = 7 := by simp
  step*
  · rename_i hlt
    simp only [UScalar.lt_equiv, Slice.len_val, s_post] at hlt
    simp only [Bool.false_eq_true, false_iff]
    exact not_protected_of_short p (by simp at hlt ⊢; omega)
  · simp only [Slice.len_val, s1_post] at start_post1 start_post2
    have h7 : 7 ≤ p.length := by simp at start_post2 ⊢; omega
    have hst : start.val = p.length - 7 := by simp at start_post1 ⊢; omega
    rw [protected_iff p h7, ← hst]
    apply compare_loop _ (fun k => MatchesUpTo p.val PROTECTED_SUFFIX.val start.val k) 7
    · intro k hk hm
      apply WP.spec_mono (is_protected_path_loop_body_spec p start k (by omega) hk hm)
      rintro (k' | r) <;> exact id
    · simp
    · exact MatchesUpTo.zero _ _ _

theorem componentOk_iff (c : List Nat) :
    Transcrypt.V3Policy.ComponentOk c ↔
      c.length ≠ 0 ∧ ¬ (c.length = 1 ∧ c[0]! = 46) ∧
        ¬ (c.length = 2 ∧ c[0]! = 46 ∧ c[1]! = 46) := by
  unfold Transcrypt.V3Policy.ComponentOk Transcrypt.V3Policy.dot
  match c with
  | [] => simp
  | [a] => simp
  | [a, b] => simp
  | a :: b :: d :: e => simp

theorem extract_getElem! (p : Slice U8) (start end_ k : Nat) (hk : start + k < end_)
    (h2 : end_ ≤ p.length) :
    ((sliceBytes p).extract start end_)[k]! = (p.val[start + k]!).val := by
  have hl : ((sliceBytes p).extract start end_).length = end_ - start := by
    simp [sliceBytes] at h2 ⊢; omega
  rw [getElem!_pos ((sliceBytes p).extract start end_) k (by omega),
    getElem!_pos p.val (start + k) (by simp at h2; omega)]
  simp [sliceBytes]

@[step]
theorem component_ok_spec (p : Slice U8) (start end_ : Usize) (h : start.val ≤ end_.val)
    (h2 : end_.val ≤ p.length) :
    component_ok p start end_ ⦃ r => r = true ↔
      Transcrypt.V3Policy.ComponentOk ((sliceBytes p).extract start.val end_.val) ⦄ := by
  unfold component_ok
  have hlen : ((sliceBytes p).extract start.val end_.val).length = end_.val - start.val := by
    simp [sliceBytes] at h2 ⊢; omega
  have h0 : ∀ hs : start.val < p.val.length, start.val < end_.val →
      ((sliceBytes p).extract start.val end_.val)[0]! = (p.val[start.val]'hs).val := by
    intro hs he
    rw [extract_getElem! p start.val end_.val 0 (by omega) h2, getElem!_pos p.val _ (by omega)]
    simp
  have h1 : ∀ hs : start.val + 1 < p.val.length, start.val + 1 < end_.val →
      ((sliceBytes p).extract start.val end_.val)[1]! = (p.val[start.val + 1]'hs).val := by
    intro hs he
    rw [extract_getElem! p start.val end_.val 1 (by omega) h2, getElem!_pos p.val _ (by omega)]
  rw [componentOk_iff, hlen]
  generalize ((sliceBytes p).extract start.val end_.val)[0]! = a0 at *
  generalize ((sliceBytes p).extract start.val end_.val)[1]! = a1 at *
  clear hlen
  step*
  all_goals try (split <;> step*)
  all_goals try (split <;> step*)

/-! ## Pure characterization of the component scan -/

/-- Every `/`-separated component is acceptable and there is no NUL. -/
def PathGood (m : List Nat) : Prop :=
  (∀ c ∈ m.splitOn 47, Transcrypt.V3Policy.ComponentOk c) ∧ 0 ∉ m

theorem pathGood_of_no_sep {m : List Nat} (h : 47 ∉ m) :
    PathGood m ↔ Transcrypt.V3Policy.ComponentOk m ∧ 0 ∉ m := by
  unfold PathGood
  rw [List.splitOn_eq_singleton h]
  simp

theorem pathGood_sep (l : List Nat) (s i : Nat) (hs : s ≤ i) (hi : i < l.length)
    (h47 : l[i]! = 47) (hno : 47 ∉ l.extract s i) :
    PathGood (l.drop s) ↔
      (Transcrypt.V3Policy.ComponentOk (l.extract s i) ∧ 0 ∉ l.extract s i) ∧
        PathGood (l.drop (i + 1)) := by
  have hsplit : l.drop s = l.extract s i ++ 47 :: l.drop (i + 1) := by
    rw [getElem!_pos l i hi] at h47
    rw [← h47, List.extract_eq_take_drop]
    rw [← List.drop_eq_getElem_cons hi]
    have : i = s + (i - s) := by omega
    conv => lhs; rw [← List.take_append_drop (i - s) (l.drop s)]
    rw [List.drop_drop]
    congr 2
    omega
  unfold PathGood
  rw [hsplit, List.splitOn_append_cons_self_of_not_mem hno]
  simp only [List.mem_cons, forall_eq_or_imp, List.mem_append, not_or]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    exact ⟨⟨h1, h3⟩, h2, h5⟩
  · rintro ⟨⟨h1, h3⟩, h2, h5⟩
    exact ⟨⟨h1, h2⟩, h3, by decide, h5⟩

theorem extract_succ (l : List Nat) (s i : Nat) (hs : s ≤ i) (hi : i < l.length) :
    l.extract s (i + 1) = l.extract s i ++ [l[i]!] := by
  rw [getElem!_pos l i hi]
  simp only [List.extract_eq_take_drop]
  have : i + 1 - s = (i - s) + 1 := by omega
  rw [this, List.take_add_one]
  congr
  rw [List.getElem?_drop, List.getElem?_eq_getElem (by omega)]
  simp only [Option.toList_some, List.cons.injEq, and_true]
  congr 1
  omega

theorem extract_all (l : List Nat) (s : Nat) : l.extract s l.length = l.drop s := by
  simp

theorem sliceBytes_getElem! (p : Slice U8) (i : Nat) (h : i < p.val.length) :
    (sliceBytes p)[i]! = (p.val[i]).val := by
  rw [getElem!_pos (sliceBytes p) i (by simp [sliceBytes]; omega)]
  simp [sliceBytes]

/-! ## The canonical-path scan loop -/

/-- Loop invariant of the scan in `is_canonical_protected_path`, for state
    `(ok, start, i)` over the bytes `l`. While `i ≤ n`: `start ≤ i`; if `ok`,
    the current component `l[start..i)` has no separator and no NUL and the
    whole path is good iff its suffix from `start` is; if not `ok`, the path is
    not good. After the final step (`i = n + 1`), `ok` is the verdict. -/
def ScanInv (l : List Nat) (ok : Bool) (s i : Nat) : Prop :=
  i ≤ l.length + 1 ∧
  (i ≤ l.length → s ≤ i ∧
    (ok = true → 47 ∉ l.extract s i ∧ 0 ∉ l.extract s i ∧ (PathGood l ↔ PathGood (l.drop s))) ∧
    (ok = false → ¬ PathGood l)) ∧
  (i = l.length + 1 → (ok = true ↔ PathGood l))

theorem scan_body_spec (path : Slice U8) (n : Usize) (hn : n.val = path.length)
    (hmax : n.val ≤ 4096) (ok : Bool) (s i : Usize)
    (hinv : ScanInv (sliceBytes path) ok s.val i.val) :
    is_canonical_protected_path_loop.body path n ok s i ⦃ cf => match cf with
      | .cont (ok', s', i') => ScanInv (sliceBytes path) ok' s'.val i'.val ∧
          n.val + 1 - i'.val < n.val + 1 - i.val
      | .done r => r = true ↔ PathGood (sliceBytes path) ⦄ := by
  have hl : (sliceBytes path).length = n.val := by simp [sliceBytes, hn]
  unfold ScanInv at hinv
  rw [hl] at hinv
  obtain ⟨hi, hlo, hhi⟩ := hinv
  unfold is_canonical_protected_path_loop.body
  step*
  split
  · step*
    rename_i hok _ hin ok3 _ hok3 _
    have hin' : i.val = n.val := by rw [hin]
    obtain ⟨_, hT, _⟩ := hlo (by omega)
    obtain ⟨hno47, hno0, hiff⟩ := hT hok
    refine ⟨⟨by simp [hl]; omega, fun h => by simp [hl] at h; omega, fun _ => ?_⟩, by omega⟩
    rw [hok3, hiff]
    rw [hin', ← hl, extract_all] at hno47 hno0
    rw [hin', ← hl, extract_all, pathGood_of_no_sep hno47]
    simp [hno0]
  · step*
    rename_i hok _ hin b
    have hin' : i.val < n.val := by
      have : i.val ≠ n.val := fun h => hin (by scalar_tac)
      scalar_tac
    have hb : (sliceBytes path)[i.val]! = b.val := by
      rw [sliceBytes_getElem! path i.val (by simpa using x), x_post2]
    obtain ⟨hsi, hT, _⟩ := hlo (by omega)
    obtain ⟨hno47, hno0, hiff⟩ := hT hok
    split
    · step*
      rename_i h47 ok3 _ hok3 _
      have h47' : (sliceBytes path)[i.val]! = 47 := by
        rw [hb, h47]; rfl
      have hsep := pathGood_sep (sliceBytes path) s.val i.val hsi (by omega) h47' hno47
      rw [x_post, i1_post]
      refine ⟨⟨by simp [hl]; omega, fun _ => ⟨le_refl _, fun h3 => ?_, fun h3 => ?_⟩,
        fun h => by simp [hl] at h; omega⟩, by omega⟩
      · simp only [List.extract_eq_take_drop, Nat.sub_self, List.take_zero, List.not_mem_nil,
          not_false_eq_true, true_and]
        rw [hiff, hsep]
        have := hok3.mp h3
        simp [this, hno0]
      · intro hg
        rw [hiff, hsep] at hg
        have := hok3.mpr hg.1.1
        rw [h3] at this
        exact absurd this (by decide)
    · split <;> step*
      · rename_i h0
        have hbad : ¬ PathGood (sliceBytes path) := by
          intro hg
          apply hg.2
          have hm := List.getElem_mem (l := sliceBytes path) (n := i.val) (by omega)
          rw [← getElem!_pos (sliceBytes path) i.val (by omega), hb, h0] at hm
          exact hm
        rw [i1_post]
        refine ⟨⟨by omega, fun _ => ⟨by omega, fun h => absurd h (by decide), fun _ => hbad⟩,
          fun h => by omega⟩, by omega⟩
      · rename_i hn47 hn0
        have hext := extract_succ (sliceBytes path) s.val i.val hsi (by omega)
        rw [hb] at hext
        have h47v : b.val ≠ 47 := fun h => hn47 (by scalar_tac)
        have h0v : b.val ≠ 0 := fun h => hn0 (by scalar_tac)
        rw [i1_post]
        refine ⟨⟨by omega, fun _ => ⟨by omega, fun _ => ⟨?_, ?_, hiff⟩, fun h => absurd h (by decide)⟩,
          fun h => by omega⟩, by omega⟩
        · rw [hext]; simp [hno47, Ne.symm h47v]
        · rw [hext]; simp [hno0, Ne.symm h0v]

theorem scanInv_init (l : List Nat) : ScanInv l true 0 0 := by
  refine ⟨by omega, fun _ => ⟨le_refl _, fun _ => ?_, fun h => absurd h (by decide)⟩,
    fun h => by omega⟩
  simp

theorem scan_loop_spec (path : Slice U8) (n : Usize) (hn : n.val = path.length)
    (hmax : n.val ≤ 4096) (ok : Bool) (s i : Usize)
    (hinv : ScanInv (sliceBytes path) ok s.val i.val) :
    is_canonical_protected_path_loop path n ok s i ⦃ r =>
      r = true ↔ PathGood (sliceBytes path) ⦄ := by
  unfold is_canonical_protected_path_loop
  apply loop.spec_decr_nat (fun st => n.val + 1 - st.2.2.val)
    (fun st => ScanInv (sliceBytes path) st.1 st.2.1.val st.2.2.val)
  · rintro ⟨ok', s', i'⟩ hinv'
    apply WP.spec_mono (scan_body_spec path n hn hmax ok' s' i' hinv')
    rintro (⟨ok'', s'', i''⟩ | r)
    · exact id
    · exact id
  · exact hinv

theorem canonical_iff (l : List Nat) :
    Transcrypt.V3Policy.CanonicalProtectedPath l ↔
      l ≠ [] ∧ l.length ≤ 4096 ∧ PathGood l ∧ Transcrypt.V3Policy.Protected l := by
  unfold Transcrypt.V3Policy.CanonicalProtectedPath PathGood Transcrypt.V3Policy.maxPath
    Transcrypt.V3Policy.slash
  tauto

@[step]
theorem is_canonical_protected_path_spec (p : Slice U8) :
    is_canonical_protected_path p ⦃ r =>
      r = true ↔ Transcrypt.V3Policy.CanonicalProtectedPath (sliceBytes p) ⦄ := by
  unfold is_canonical_protected_path
  have hmp : MAX_PATH.val = 4096 := by unfold MAX_PATH; rfl
  have hlen : (sliceBytes p).length = p.length := by simp [sliceBytes]
  rw [canonical_iff]
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  step*
  · rename_i h0
    have : p.length = 0 := by have := congrArg UScalar.val h0; simpa using this
    have hnil : sliceBytes p = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hnil]
  · rename_i h0 hgt
    have hn0 : p.length ≠ 0 := fun h => h0 (by scalar_tac)
    have hle : p.length ≤ 4096 := by
      have : ¬ p.len.val > MAX_PATH.val := hgt
      simp at this ⊢; omega
    step with scan_loop_spec p p.len (by simp) (by simpa using hle) true 0#usize 0#usize
      (scanInv_init _) as ⟨ ok1, hok1 ⟩
    have hne : sliceBytes p ≠ [] := fun h => hn0 (by rw [← hlen, h]; rfl)
    split
    · rename_i htrue
      step with is_protected_path_spec as ⟨ r, hr ⟩
      rw [hr]
      have := hok1.mp htrue
      simp only [hne, ne_eq, not_false_eq_true, hlen, hle, this, true_and]
    · rename_i hfalse
      simp only [Bool.not_eq_true] at hfalse
      simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
      intro _ _ hg
      exact absurd (hok1.mpr hg) (by simp [hfalse])

end Transcrypt.V3Verification
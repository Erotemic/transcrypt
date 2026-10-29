import V3Wire.Verification.Bytes

/-!
Functional refinement of the production path policy: the suffix test
`ends_with` (over `matches_at`, proved in `Bytes`), the reserved-metadata test
`is_reserved_path`, `component_ok` and the canonical-path scan
`is_canonical_protected_path`, each against `Transcrypt.V3Policy`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core
open Transcrypt.V3Policy (slash dot maxPath)

/-! ## `ends_with` -/

/-- `ends_with bytes suffix` holds iff `suffix` is a suffix of `bytes`. -/
@[step]
theorem ends_with_spec (bytes suffix : Slice U8) :
    ends_with bytes suffix ⦃ r => r = true ↔ sliceBytes suffix <:+ sliceBytes bytes ⦄ := by
  unfold ends_with
  simp_len
  have hbl := sliceBytes_length bytes
  have hsl := sliceBytes_length suffix
  step*
  · have hi2 : i2.val = bytes.length - suffix.length := by simp at i2_post1; exact i2_post1
    rw [r_post, List.suffix_iff_eq_drop, hbl, hsl, ← hi2]
    constructor
    · rintro ⟨_, hp⟩
      exact hp.eq_of_length (by simp only [List.length_drop, hbl, hsl]; scalar_tac)
    · intro h
      refine ⟨by omega, ?_⟩
      rw [h]
  · simp only [Bool.false_eq_true, false_iff]
    intro hs
    have := hs.length_le
    rw [hbl, hsl] at this
    scalar_tac

/-! ## Reserved metadata paths -/

/-- `is_reserved_path` decides exactly the spec's `Reserved`. -/
@[step]
theorem is_reserved_path_spec (p : Slice U8) :
    is_reserved_path p ⦃ r => r = true ↔ Transcrypt.V3Policy.Reserved (sliceBytes p) ⦄ := by
  unfold is_reserved_path Transcrypt.V3Policy.Reserved
  step*
  all_goals
    subst_vars
    simp only [METADATA_DIR_bytes, ATTRIBUTES_NAME_bytes, ATTRIBUTES_SUFFIX_bytes,
      MODULES_NAME_bytes, List.drop_zero, Nat.zero_le, true_and, ← sliceBytes_inj] at *
    tauto

theorem componentOk_iff (c : List Nat) :
    Transcrypt.V3Policy.ComponentOk c ↔
      c.length ≠ 0 ∧ ¬ (c.length = 1 ∧ c[0]! = dot) ∧
        ¬ (c.length = 2 ∧ c[0]! = dot ∧ c[1]! = dot) := by
  unfold Transcrypt.V3Policy.ComponentOk
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
  rw [componentOk_iff, hlen, show dot = 46 from rfl]
  generalize ((sliceBytes p).extract start.val end_.val)[0]! = a0 at *
  generalize ((sliceBytes p).extract start.val end_.val)[1]! = a1 at *
  clear hlen
  step*
  all_goals try (split <;> step*)
  all_goals try (split <;> step*)

/-! ## Pure characterization of the component scan -/

/-- Every `/`-separated component is acceptable and there is no NUL. -/
def PathGood (m : List Nat) : Prop :=
  (∀ c ∈ m.splitOn slash, Transcrypt.V3Policy.ComponentOk c) ∧ 0 ∉ m

theorem pathGood_of_no_sep {m : List Nat} (h : slash ∉ m) :
    PathGood m ↔ Transcrypt.V3Policy.ComponentOk m ∧ 0 ∉ m := by
  unfold PathGood
  rw [List.splitOn_eq_singleton h]
  simp

theorem pathGood_sep (l : List Nat) (s i : Nat) (hs : s ≤ i) (hi : i < l.length)
    (h47 : l[i]! = slash) (hno : slash ∉ l.extract s i) :
    PathGood (l.drop s) ↔
      (Transcrypt.V3Policy.ComponentOk (l.extract s i) ∧ 0 ∉ l.extract s i) ∧
        PathGood (l.drop (i + 1)) := by
  have hsplit : l.drop s = l.extract s i ++ slash :: l.drop (i + 1) := by
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

theorem extract_all (l : List Nat) (s : Nat) : l.extract s l.length = l.drop s := by
  simp

/-! ## The canonical-path scan loop -/

/-- Loop invariant of the scan in `is_canonical_protected_path`, for state
    `(ok, start, i)` over the bytes `l`. While `i ≤ n`: `start ≤ i`; if `ok`,
    the current component `l[start..i)` has no separator and no NUL and the
    whole path is good iff its suffix from `start` is; if not `ok`, the path is
    not good. After the final step (`i = n + 1`), `ok` is the verdict. -/
def ScanInv (l : List Nat) (ok : Bool) (s i : Nat) : Prop :=
  i ≤ l.length + 1 ∧
  (i ≤ l.length → s ≤ i ∧
    (ok = true → slash ∉ l.extract s i ∧ 0 ∉ l.extract s i ∧ (PathGood l ↔ PathGood (l.drop s))) ∧
    (ok = false → ¬ PathGood l)) ∧
  (i = l.length + 1 → (ok = true ↔ PathGood l))

theorem scan_body_spec (path : Slice U8) (n : Usize) (hn : n.val = path.length)
    (hmax : n.val ≤ maxPath) (ok : Bool) (s i : Usize)
    (hinv : ScanInv (sliceBytes path) ok s.val i.val) :
    is_canonical_protected_path_loop.body path n ok s i ⦃ cf => match cf with
      | .cont (ok', s', i') => ScanInv (sliceBytes path) ok' s'.val i'.val ∧
          n.val + 1 - i'.val < n.val + 1 - i.val
      | .done r => r = true ↔ PathGood (sliceBytes path) ⦄ := by
  have hl : (sliceBytes path).length = n.val := by simp [sliceBytes, hn]
  simp only [maxPath] at hmax
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
      have h47' : (sliceBytes path)[i.val]! = slash := by
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
        have hext := extract_snoc (sliceBytes path) hsi (by omega)
        rw [hb] at hext
        have h47v : b.val ≠ slash := fun h => hn47 (by simp only [slash] at h; scalar_tac)
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
    (hmax : n.val ≤ maxPath) (ok : Bool) (s i : Usize)
    (hinv : ScanInv (sliceBytes path) ok s.val i.val) :
    is_canonical_protected_path_loop path n ok s i ⦃ r =>
      r = true ↔ PathGood (sliceBytes path) ⦄ := by
  unfold is_canonical_protected_path_loop
  apply loop.spec_decr_nat (fun st => n.val + 1 - st.2.2.val)
    (fun st => ScanInv (sliceBytes path) st.1 st.2.1.val st.2.2.val)
  · rintro ⟨ok', s', i'⟩ h
    apply WP.spec_mono (scan_body_spec path n hn hmax ok' s' i' h)
    rintro (⟨_, _, _⟩ | _) <;> exact id
  · exact hinv

theorem canonical_iff (l : List Nat) :
    Transcrypt.V3Policy.CanonicalProtectedPath l ↔
      l ≠ [] ∧ l.length ≤ maxPath ∧ PathGood l ∧ ¬ Transcrypt.V3Policy.Reserved l := by
  unfold Transcrypt.V3Policy.CanonicalProtectedPath PathGood
  tauto

@[step]
theorem is_canonical_protected_path_spec (p : Slice U8) :
    is_canonical_protected_path p ⦃ r =>
      r = true ↔ Transcrypt.V3Policy.CanonicalProtectedPath (sliceBytes p) ⦄ := by
  unfold is_canonical_protected_path
  have hmp : MAX_PATH.val = 4096 := MAX_PATH_val
  have hlen : (sliceBytes p).length = p.length := by simp [sliceBytes]
  rw [canonical_iff, maxPath]
  simp_len
  step*
  · rename_i h0
    have : p.length = 0 := by have := congrArg UScalar.val h0; simpa using this
    have hnil : sliceBytes p = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hnil]
  · rename_i h0 hgt
    have hn0 : p.length ≠ 0 := fun h => h0 (by scalar_tac)
    have hle : p.length ≤ 4096 := by
      have : ¬ p.len.val > MAX_PATH.val := hgt
      simp [maxPath] at this ⊢; omega
    step with scan_loop_spec p p.len (by simp) (by simpa [maxPath] using hle) true 0#usize 0#usize
      (scanInv_init _) as ⟨ ok1, hok1 ⟩
    have hne : sliceBytes p ≠ [] := fun h => hn0 (by rw [← hlen, h]; rfl)
    split
    · rename_i htrue
      step with is_reserved_path_spec as ⟨ r, hr ⟩
      have := hok1.mp htrue
      simp only [decide_eq_true_eq, hr, ne_eq, hne, not_false_eq_true, hlen, hle, this, true_and]
    · rename_i hfalse
      simp only [Bool.not_eq_true] at hfalse
      simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
      intro _ _ hg
      exact absurd (hok1.mpr hg) (by simp [hfalse])

end Transcrypt.V3Verification
import V3Wire.Extraction

/-!
Shared definitions, lemmas and tactics for the refinement proofs.

* Byte projections: `wireBytes` (arrays) and `sliceBytes` (slices) map
  Aeneas's bitvector-backed bytes to the specification's natural numbers.
* General list facts used by several modules (`getElem!` after `set`,
  `extract` one past the end, first occurrences, pigeonhole).
* `WP.spec` helpers: `spec_result`, `result_is_ok_spec`, `index_range_spec`.
* Loop reasoning. Every copy loop of `transcrypt_v3_core` has the shape

      while i < bound { out[dst + i] = src[srcOff + i]; i += 1 }

  and is described by the pointwise invariant `Copied`; every comparison
  loop has the shape

      while i < bound { if a[off + i] != b[i] { return false } i += 1 }

  and is described by `MatchesUpTo`. `copy_loop` and `compare_loop` turn a
  one-iteration specification of an extracted loop body into one of the
  extracted `loop` (via `loop.spec_decr_nat`).
* Tactics `simp_len` (the extracted slice length is `Slice.len`) and
  `simp_bne` (normalize `!=` tests from the extraction).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

/-! ## Tactics -/

/-- Rewrite the extracted `s.len` (via `slice_length`) to `Slice.len`, plus
    optional extra simp lemmas. -/
macro "simp_len" : tactic =>
  `(tactic| simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length])
macro "simp_len" " [" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let args : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic| simp only [CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, $args,*])

/-- Turn the extraction's `(a != b) = true` into `a ≠ b` (and its negation
    into `a = b`). -/
macro "simp_bne" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [bne_iff_ne, ne_eq, Decidable.not_not] $[$loc]?)

/-! ## Byte projections -/

/-- Project Aeneas's fixed array of bitvector-backed bytes into the
    independent wire specification's natural-number byte representation. -/
def wireBytes {n : Usize} (xs : Std.Array U8 n) : List Nat :=
  xs.val.map (fun byte => byte.val)

/-- Project an Aeneas byte slice to the specification's natural-number bytes. -/
def sliceBytes (s : Slice U8) : List Nat := s.val.map (fun b => b.val)

theorem sliceBytes_length (s : Slice U8) : (sliceBytes s).length = s.length := by
  simp [sliceBytes]

theorem sliceBytes_getElem (s : Slice U8) (k : Nat) (h : k < s.length) :
    (sliceBytes s)[k]'(by rw [sliceBytes_length]; exact h) = (s.val[k]'h).val := by
  simp [sliceBytes]

theorem sliceBytes_getElem! (p : Slice U8) (i : Nat) (h : i < p.val.length) :
    (sliceBytes p)[i]! = (p.val[i]).val := by
  rw [getElem!_pos (sliceBytes p) i (by simp [sliceBytes]; omega)]
  simp [sliceBytes]

theorem map_val_injective : Function.Injective (List.map (fun b : U8 => b.val)) :=
  List.map_injective_iff.2 (fun a b h => (UScalar.eq_equiv a b).2 h)

theorem sliceBytes_inj (a b : Slice U8) : sliceBytes a = sliceBytes b ↔ a.val = b.val :=
  ⟨fun h => map_val_injective h, fun h => by simp [sliceBytes, h]⟩

theorem wireBytes_inj {n m : Usize} (a : Std.Array U8 n) (b : Std.Array U8 m) :
    wireBytes a = wireBytes b ↔ a.val = b.val :=
  ⟨fun h => map_val_injective h, fun h => by simp [wireBytes, h]⟩

theorem wireBytes_injective {n : Usize} {a b : Std.Array U8 n}
    (h : wireBytes a = wireBytes b) : a = b :=
  Subtype.ext (map_val_injective h)

/-- `usize` is at least 32 bits wide on every supported platform. -/
theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  simp only [Usize.max, Usize.numBits]
  cases System.Platform.numBits_eq <;> simp [*]

/-! ## Lists -/

/-- List equality from pointwise `getElem!` agreement. -/
theorem list_eq_of_getElem! {α : Type} [Inhabited α] {l₁ l₂ : List α} (hl : l₁.length = l₂.length)
    (h : ∀ k, k < l₁.length → l₁[k]! = l₂[k]!) : l₁ = l₂ := by
  apply List.ext_getElem hl
  intro k h₁ h₂
  have := h k h₁
  rwa [getElem!_pos l₁ k h₁, getElem!_pos l₂ k h₂] at this

/-- `List.getElem!_append_right` at an offset written past the prefix. -/
theorem getElem!_append_length_add {α : Type} [Inhabited α] (P S : List α) (j : Nat) :
    (P ++ S)[P.length + j]! = S[j]! := by
  rw [List.getElem!_append_right _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem getElem?_eq_some_iff' {α : Type} [Inhabited α] (l : List α) (k : Nat) (x : α) :
    l[k]? = some x ↔ k < l.length ∧ l[k]! = x := by
  constructor
  · intro h
    obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp h
    exact ⟨hk, by rw [getElem!_pos l k hk, he]⟩
  · rintro ⟨hk, he⟩
    rw [List.getElem?_eq_getElem hk, ← getElem!_pos l k hk, he]

theorem getElem!_set_ne' {α : Type} [Inhabited α] (l : List α) {i k : Nat} (v : α) (h : k ≠ i) :
    (l.set i v)[k]! = l[k]! := by
  simp only [getElem!_def, List.getElem?_set_ne (Ne.symm h)]

theorem getElem!_set_self' {α : Type} [Inhabited α] (l : List α) {i : Nat} (v : α) (h : i < l.length) :
    (l.set i v)[i]! = v := by
  simp only [getElem!_def, List.getElem?_set_self h]

theorem take_set_succ {α : Type} (l : List α) (i : Nat) (b : α) (hi : i < l.length) :
    (l.set i b).take (i + 1) = l.take i ++ [b] := by
  rw [List.take_add_one, List.getElem?_set_self hi, List.take_set_of_le (by omega)]
  rfl

theorem prefix_append_iff {α : Type} (a b l : List α) :
    a ++ b <+: l ↔ a <+: l ∧ b <+: l.drop a.length := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨b ++ t, by simp⟩, ⟨t, by simp⟩⟩
  · rintro ⟨⟨u, rfl⟩, ⟨t, ht⟩⟩
    simp only [List.drop_left] at ht
    exact ⟨t, by rw [← ht]; simp⟩

/-- Extending an `extract` by one element. -/
theorem extract_snoc {α : Type} [Inhabited α] (L : List α) {a i : Nat} (hai : a ≤ i)
    (hi : i < L.length) : L.extract a (i + 1) = L.extract a i ++ [L[i]!] := by
  rw [List.extract_eq_take_drop, List.extract_eq_take_drop, show i + 1 - a = (i - a) + 1 by omega,
    List.take_add_one, List.getElem?_drop, show a + (i - a) = i by omega, List.getElem?_eq_getElem hi,
    getElem!_pos L i hi]
  rfl

/-- An `extract` split at an inner position. -/
theorem extract_split {α : Type} [Inhabited α] (L : List α) {a i b : Nat} (hai : a ≤ i) (hib : i < b)
    (hb : b ≤ L.length) : L.extract a b = L.extract a i ++ [L[i]!] ++ L.extract (i + 1) b := by
  rw [← extract_snoc L hai (by omega)]
  simp only [List.extract_eq_take_drop]
  rw [show b - a = (i + 1 - a) + (b - (i + 1)) by omega, List.take_add, List.drop_drop,
    show a + (i + 1 - a) = i + 1 by omega]

/-- The first position satisfying a property is unique. -/
theorem eq_of_first {P : Nat → Prop} {a b : Nat} (ha : P a) (hna : ∀ k < a, ¬ P k)
    (hb : P b) (hnb : ∀ k < b, ¬ P k) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd ha (hnb a h)
  · exact h
  · exact absurd hb (hna b h)

/-- A transitive relation holds pairwise if it holds between neighbors. -/
theorem pairwise_of_adjacent {α : Type} {R : α → α → Prop} (htr : ∀ a b c, R a b → R b c → R a c) :
    ∀ (l : List α), (∀ k (h : k + 1 < l.length), R l[k] l[k + 1]) → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    refine List.Pairwise.cons ?_ (pairwise_of_adjacent htr xs (fun k hk => h (k + 1) (by simp; omega)))
    have hall : ∀ m (hm : m < xs.length), R x xs[m] := by
      intro m
      induction m with
      | zero => exact fun hm => h 0 (by simp; omega)
      | succ m ih => exact fun hm => htr _ _ _ (ih (by omega)) (h (m + 1) (by simp; omega))
    intro y hy
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hy
    exact hall m hm

/-- Pigeonhole: `n` distinct numbers below `n` are all of them. -/
theorem mem_of_nodup_lt {L : List Nat} {n : Nat} (hd : L.Nodup) (hl : L.length = n) (hlt : ∀ x ∈ L, x < n)
    {j : Nat} (hj : j < n) : j ∈ L := by
  have hsub : L.toFinset ⊆ Finset.range n := by
    intro x hx; simp only [List.mem_toFinset] at hx; simpa using hlt x hx
  have hcard : (Finset.range n).card ≤ L.toFinset.card := by
    rw [List.toFinset_card_of_nodup hd, hl, Finset.card_range]
  have := Finset.eq_of_subset_of_card_le hsub hcard
  have hj' : j ∈ Finset.range n := Finset.mem_range.mpr hj
  rw [← this] at hj'
  exact List.mem_toFinset.mp hj'

/-! ## `WP.spec` helpers -/

/-- A verified function's specification applies to the result the adapter
    observed. -/
theorem spec_result {α : Type} {m : RustM α} {P : α → Prop} {r : α} (h : m ⦃ x => P x ⦄)
    (hm : m = ok r) : P r := by
  obtain ⟨y, hy, hP⟩ := WP.spec_imp_exists h
  rw [hm] at hy
  cases hy
  exact hP

@[step] theorem result_is_ok_spec {T E : Type} (r : core.result.Result T E) :
    core.result.Result.is_ok r ⦃ b => b = true ↔ ∃ x, r = core.result.Result.Ok x ⦄ :=
  match r with
  | .Ok _ => by simp [core.result.Result.is_ok]
  | .Err _ => by simp [core.result.Result.is_ok]

/-- `&s[a..b]` is the `extract` of the bytes. -/
theorem index_range_spec (s : Slice U8) (a b : Usize) (hab : a.val ≤ b.val) (hb : b.val ≤ s.length) :
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      s { start := a, «end» := b } ⦃ r => sliceBytes r = (sliceBytes s).extract a.val b.val ⦄ := by
  unfold core.Slice.Insts.CoreOpsIndexIndex.index
  simp only [core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_slice, rust_primitives.slice.slice_length]
  have h1 : a ≤ b := by scalar_tac
  have h2 : b ≤ s.len := by scalar_tac
  simp only [h1, h2, if_true, Slice.subslice, bind_tc_ok]
  rw [if_pos ⟨hab, hb⟩]
  simp [sliceBytes, List.slice, List.map_take, List.map_drop]

/-! ## Copy loops -/

/-- `out` agrees with `src[srcOff + (k - dst)]` on `[dst, dst + n)` and with
    `base` everywhere else. -/
def Copied (out base src : List U8) (dst srcOff n : Nat) : Prop :=
  out.length = base.length ∧
  ∀ k, k < out.length →
    out[k]! = if dst ≤ k ∧ k < dst + n then src[srcOff + (k - dst)]! else base[k]!

theorem Copied.zero (base src : List U8) (dst srcOff : Nat) :
    Copied base base src dst srcOff 0 := by
  refine ⟨rfl, fun k _ => ?_⟩
  simp

theorem Copied.step {out base src : List U8} {dst srcOff n : Nat}
    (h : Copied out base src dst srcOff n) (_hlt : dst + n < out.length) :
    Copied (out.set (dst + n) src[srcOff + n]!) base src dst srcOff (n + 1) := by
  obtain ⟨hlen, hk⟩ := h
  refine ⟨by simp [hlen], fun k hk' => ?_⟩
  rw [List.length_set] at hk'
  by_cases heq : k = dst + n
  · subst heq
    rw [getElem!_pos (out.set (dst + n) src[srcOff + n]!) (dst + n) (by simp; omega),
      List.getElem_set_self]
    simp
  · rw [getElem!_pos (out.set (dst + n) src[srcOff + n]!) k (by simp; omega),
      List.getElem_set_ne (by omega), ← getElem!_pos out k hk', hk k hk']
    by_cases hr : dst ≤ k ∧ k < dst + n
    · rw [if_pos hr, if_pos (by omega)]
    · rw [if_neg hr, if_neg (by omega)]

/-- One iteration of a copy loop writing into an Aeneas array. -/
theorem Copied.array_step {N : Usize} {o : Std.Array U8 N} {base src : List U8}
    {dst srcOff k : Nat} {p : Usize} {x : U8}
    (hc : Copied o.val base src dst srcOff k) (hp : p.val = dst + k)
    (hx : x = src[srcOff + k]!) (hlt : dst + k < o.val.length) :
    Copied (o.set p x).val base src dst srcOff (k + 1) := by
  have := hc.step hlt
  subst hx
  simpa [Std.Array.set, hp] using this

/-- Read back a byte of a completed copy. -/
theorem Copied.get_in {out base src : List U8} {dst srcOff n k : Nat}
    (h : Copied out base src dst srcOff n) (hk : k < out.length)
    (hlo : dst ≤ k) (hhi : k < dst + n) :
    out[k]! = src[srcOff + (k - dst)]! := by
  rw [h.2 k hk, if_pos ⟨hlo, hhi⟩]

theorem Copied.get_out {out base src : List U8} {dst srcOff n k : Nat}
    (h : Copied out base src dst srcOff n) (hk : k < out.length)
    (hr : ¬ (dst ≤ k ∧ k < dst + n)) :
    out[k]! = base[k]! := by
  rw [h.2 k hk, if_neg hr]

/-- A copy of all of `src` from offset 0 into a fresh buffer of length `n`
    is the first `n` bytes of `src`. -/
theorem copied_full {out base src : List U8} {n : Nat} (h : Copied out base src 0 0 n)
    (hl : out.length = n) (hn : n ≤ src.length) : out = src.take n := by
  apply list_eq_of_getElem! (by simp; omega)
  intro k hk
  rw [h.get_in hk (by omega) (by omega), getElem!_pos (src.take n) k (by simp; omega),
    List.getElem_take, ← getElem!_pos src k (by omega)]
  simp

/-- Two consecutive copies, `A` to `[0, n)` and then `B` to `[n, n + m)` of
    an `n + m`-byte buffer, produce exactly `A ++ B`. -/
theorem copied_concat {out mid base A B : List U8} {n m : Nat}
    (h0 : Copied mid base A 0 0 n) (h1 : Copied out mid B n 0 m)
    (hA : A.length = n) (hB : B.length = m) (hl : out.length = n + m) : out = A ++ B := by
  apply list_eq_of_getElem! (by simp; omega)
  intro k hk
  by_cases hlt : k < n
  · rw [h1.get_out hk (by omega), List.getElem!_append_left _ _ _ (by omega),
      h0.get_in (by have := h1.1; omega) (by omega) (by omega)]
    simp
  · rw [h1.get_in hk (by omega) (by omega), List.getElem!_append_right _ _ _ (by omega)]
    simp [hA]

/-- Whole-loop rule for an extracted copy loop. `hstep` is the specification
    of one iteration of the extracted loop body. -/
theorem copy_loop {α : Type} (body : α × Usize → RustM (ControlFlow (α × Usize) α))
    (val : α → List U8) (base src : List U8) (dst srcOff bound : Nat)
    (hstep : ∀ o (i : Usize), i.val ≤ bound → Copied (val o) base src dst srcOff i.val →
      body (o, i) ⦃ cf => match cf with
        | .cont (o', i') => i'.val = i.val + 1 ∧ i'.val ≤ bound ∧
            Copied (val o') base src dst srcOff i'.val
        | .done o' => Copied (val o') base src dst srcOff bound ⦄)
    (o : α) (i : Usize) (hi : i.val ≤ bound)
    (h : Copied (val o) base src dst srcOff i.val) :
    loop body (o, i) ⦃ r => Copied (val r) base src dst srcOff bound ⦄ := by
  apply loop.spec_decr_nat (fun s => bound - s.2.val)
    (fun s => s.2.val ≤ bound ∧ Copied (val s.1) base src dst srcOff s.2.val)
  · rintro ⟨o', j⟩ ⟨hj, hc⟩
    apply WP.spec_mono (hstep o' j hj hc)
    rintro (⟨o'', k⟩ | o'')
    · rintro ⟨hk, hkb, hc'⟩
      exact ⟨⟨hkb, hc'⟩, by simp only; omega⟩
    · exact id
  · exact ⟨hi, h⟩

/-! ## Comparison loops -/

/-- `a[off + k] = b[k]` for every `k < n`. -/
def MatchesUpTo (a b : List U8) (off n : Nat) : Prop :=
  ∀ k, k < n → a[off + k]! = b[k]!

theorem MatchesUpTo.zero (a b : List U8) (off : Nat) : MatchesUpTo a b off 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem MatchesUpTo.step {a b : List U8} {off n : Nat}
    (h : MatchesUpTo a b off n) (hn : a[off + n]! = b[n]!) :
    MatchesUpTo a b off (n + 1) := by
  intro k hk
  by_cases heq : k = n
  · subst heq; exact hn
  · exact h k (by omega)

/-- Whole-loop rule for an extracted comparison loop with early exit. The
    caller's `post` describes both the mismatch exit and the completed exit. -/
theorem compare_loop {β : Type} (body : Usize → RustM (ControlFlow Usize β))
    (inv : Nat → Prop) (bound : Nat) (post : β → Prop)
    (hstep : ∀ (i : Usize), i.val ≤ bound → inv i.val →
      body i ⦃ cf => match cf with
        | .cont i' => i'.val = i.val + 1 ∧ i'.val ≤ bound ∧ inv i'.val
        | .done r => post r ⦄)
    (i : Usize) (hi : i.val ≤ bound) (h : inv i.val) :
    loop body i ⦃ r => post r ⦄ := by
  apply loop.spec_decr_nat (fun s => bound - s.val) (fun s => s.val ≤ bound ∧ inv s.val)
  · rintro j ⟨hj, hc⟩
    apply WP.spec_mono (hstep j hj hc)
    rintro (k | r)
    · rintro ⟨hk, hkb, hc'⟩
      exact ⟨⟨hkb, hc'⟩, by omega⟩
    · exact id
  · exact ⟨hi, h⟩

end Transcrypt.V3Verification

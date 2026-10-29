import V3Wire.Verification.Refinement

/-!
Functional refinement of the production pkt-line length decoder
`decode_pkt_len`: it returns `Ok n` exactly for the headers satisfying
`Transcrypt.V3Policy.PktLenAccepted` (with `n` the decoded length), and
`Err Refusal.Request` for every other header. As a `WP.spec` triple it also
excludes panics, overflow and divergence.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core

open Transcrypt.V3Policy (hexValue)

/-- Big-endian value of the first `k` digits of `l`, or `none` as soon as one
    of them is not a lowercase hexadecimal digit. -/
def pktAcc (l : List Nat) : Nat → Option Nat
  | 0 => some 0
  | k + 1 => (pktAcc l k).bind fun v => (hexValue l[k]!).map fun d => v * 16 + d

theorem pkt_hexValue_lt {c d : Nat} (h : hexValue c = some d) : d < 16 := by
  unfold hexValue at h
  split_ifs at h <;> simp at h <;> omega

theorem pktAcc_lt (l : List Nat) : ∀ k v, pktAcc l k = some v → v < 16 ^ k
  | 0, v, h => by simp [pktAcc] at h; subst h; simp
  | k + 1, v, h => by
    simp only [pktAcc, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, d, hd, rfl⟩ := h
    have h1 := pktAcc_lt l k w hw
    have h2 := pkt_hexValue_lt hd
    rw [Nat.pow_succ]
    have : w * 16 + d < (w + 1) * 16 := by omega
    have : (w + 1) * 16 ≤ 16 ^ k * 16 := Nat.mul_le_mul_right _ h1
    omega

theorem pktAcc_none_mono (l : List Nat) (i : Nat) (h : pktAcc l i = none) :
    ∀ j, i ≤ j → pktAcc l j = none
  | j, hj => by
    induction j with
    | zero => have : i = 0 := by omega
              subst this; simp [pktAcc] at h
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hl | hl
      · simp [pktAcc, ih (by omega)]
      · have : i = j + 1 := by omega
        subst this; exact h

theorem pkt_hex_dec {c : Nat} (h1 : 48 ≤ c) (h2 : c ≤ 57) : hexValue c = some (c - 48) := by
  unfold hexValue; rw [if_pos ⟨h1, h2⟩]

theorem pkt_hex_low {c : Nat} (h1 : 97 ≤ c) (h2 : c ≤ 102) : hexValue c = some (c - 87) := by
  unfold hexValue; rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

theorem pkt_hex_none {c : Nat} (h1 : ¬(48 ≤ c ∧ c ≤ 57)) (h2 : ¬(97 ≤ c ∧ c ≤ 102)) :
    hexValue c = none := by
  unfold hexValue; rw [if_neg h1, if_neg h2]

/-- Invariant of the digit scan: `i` stays within the header and `ok` with
    `value` record exactly the decoded value of the first `i` digits. -/
def PktInv (l : List Nat) (s : Usize × Bool × Usize) : Prop :=
  s.2.2.val ≤ 4 ∧ pktAcc l s.2.2.val = if s.2.1 then some s.1.val else none

/-- One digit step of `decode_pkt_len`. The program is restated from the
    body of `decode_pkt_len_loop` in `V3Wire/Extraction/Funs.lean` and must
    match it: `pkt_body_spec` applies this lemma with `step with`, which
    fails if the extraction changes. -/
theorem pkt_digit_spec (c : U8) (value : Usize) (hv : value.val < 16 ^ 3) :
    (if c >= 48#u8 then
        if c <= 57#u8 then
          do
          let i1 ← value * 16#usize
          let i2 ← c - 48#u8
          let i3 ← lift (UScalar.cast .Usize i2)
          let value2 ← i1 + i3
          ok (value2, true)
        else
          if c >= 97#u8 then
            if c <= 102#u8 then
              do
              let i1 ← value * 16#usize
              let i2 ← c - 97#u8
              let i3 ← i2 + 10#u8
              let i4 ← lift (UScalar.cast .Usize i3)
              let value2 ← i1 + i4
              ok (value2, true)
            else ok (value, false)
          else ok (value, false)
      else
        if c >= 97#u8 then
          if c <= 102#u8 then
            do
            let i1 ← value * 16#usize
            let i2 ← c - 97#u8
            let i3 ← i2 + 10#u8
            let i4 ← lift (UScalar.cast .Usize i3)
            let value2 ← i1 + i4
            ok (value2, true)
          else ok (value, false)
        else ok (value, false) : RustM (Usize × Bool)) ⦃ p =>
      (hexValue c.val).map (fun d => value.val * 16 + d) =
        if p.2 then some p.1.val else none ⦄ := by
  have := usize_max_ge
  have hc := c.hBounds
  split_ifs with h1 h2 h3 h4 h3 h4 <;> simp only [ge_iff_le, UScalar.le_equiv] at *
  · step*
    all_goals
      rw [pkt_hex_dec (by scalar_tac) (by scalar_tac)]
      simp only [Option.map_some, if_true]
      scalar_tac
  · step*
    all_goals
      rw [pkt_hex_low (by scalar_tac) (by scalar_tac)]
      simp only [Option.map_some, if_true, Option.some.injEq]
      have h4' : i4.val = i3.val := by rw [i4_post]; scalar_tac
      scalar_tac
  · simp only [WP.spec_ok, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff]
    exact pkt_hex_none (by scalar_tac) (by scalar_tac)
  · simp only [WP.spec_ok, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff]
    exact pkt_hex_none (by scalar_tac) (by scalar_tac)
  · step*
  · simp only [WP.spec_ok, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff]
    exact pkt_hex_none (by scalar_tac) (by scalar_tac)
  · simp only [WP.spec_ok, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff]
    exact pkt_hex_none (by scalar_tac) (by scalar_tac)

/-- The loop body preserves `PktInv` and, on exit, has decoded all four digits. -/
theorem pkt_body_spec (header : Std.Array U8 4#usize) (value : Usize) (ok1 : Bool) (i : Usize)
    (hinv : PktInv (wireBytes header) (value, ok1, i)) :
    decode_pkt_len_loop.body header value ok1 i ⦃ cf => match cf with
      | .cont s' => PktInv (wireBytes header) s' ∧ 4 - s'.2.2.val < 4 - i.val
      | .done r => pktAcc (wireBytes header) 4 = if r.2 then some r.1.val else none ⦄ := by
  obtain ⟨hi, hacc⟩ := hinv
  simp only at hi hacc
  unfold decode_pkt_len_loop.body
  cases ok1
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok] at hacc ⊢
    exact pktAcc_none_mono _ _ hacc 4 hi
  · simp only [↓reduceIte] at hacc ⊢
    have := usize_max_ge
    have hlen : header.length = 4 := by simp
    split
    · rename_i hlt
      have hlt' : i.val < 4 := by simpa [UScalar.lt_equiv] using hlt
      have hv : value.val < 16 ^ 3 := by
        have := pktAcc_lt _ _ _ hacc
        have : 16 ^ i.val ≤ 16 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      step as ⟨ _, c, c_post ⟩
      step with pkt_digit_spec c value hv as ⟨ v1, o2, hp ⟩
      step*
      unfold PktInv
      refine ⟨⟨show i1.val ≤ 4 by omega, ?_⟩, show 4 - i1.val < 4 - i.val by omega⟩
      rw [i1_post, pktAcc, hacc, ← hp]
      have hb : (wireBytes header)[i.val]! = c.val := by
        rw [c_post]
        rw [getElem!_pos (wireBytes header) i.val (by simp [wireBytes]; omega)]
        simp [wireBytes]
      simp [hb]
    · rename_i hge
      have : i.val = 4 := by simp [UScalar.lt_equiv] at hge; omega
      simp only [WP.spec_ok, ↓reduceIte]
      rw [this] at hacc; exact hacc

theorem pkt_loop_spec (header : Std.Array U8 4#usize) :
    decode_pkt_len_loop header 0#usize true 0#usize ⦃ r =>
      pktAcc (wireBytes header) 4 = if r.2 then some r.1.val else none ⦄ := by
  unfold decode_pkt_len_loop
  apply loop.spec_decr_nat (fun s => 4 - s.2.2.val) (PktInv (wireBytes header))
  · rintro ⟨v, o, k⟩ hinv
    apply WP.spec_mono (pkt_body_spec header v o k hinv)
    rintro (⟨_, _, _⟩ | _) <;> exact id
  · simp [PktInv, pktAcc]

/-- The spec's `PktLen` is exactly the four-digit decoded value. -/
theorem pktLen_iff (header : Std.Array U8 4#usize) (n : Nat) :
    Transcrypt.V3Policy.PktLen (wireBytes header) n ↔ pktAcc (wireBytes header) 4 = some n := by
  have hlen : (wireBytes header).length = 4 := by simp [wireBytes]
  generalize wireBytes header = l at hlen ⊢
  match l, hlen with
  | [a, b, c, d], _ =>
    unfold Transcrypt.V3Policy.PktLen
    cases ha : hexValue a <;> cases hb : hexValue b <;> cases hc : hexValue c <;>
      cases hd : hexValue d <;> simp [pktAcc, ha, hb, hc, hd]
    exact eq_comm

/-- `decode_pkt_len` accepts exactly the pkt-line headers of the spec and
    returns their decoded length; every other header is refused with
    `Refusal.Request`. -/
@[step]
theorem decode_pkt_len_spec (header : Std.Array U8 4#usize) :
    decode_pkt_len header ⦃ r => match r with
      | core.result.Result.Ok n => Transcrypt.V3Policy.PktLenAccepted (wireBytes header) n.val
      | core.result.Result.Err e => e = Refusal.Request ∧
          ∀ n, ¬ Transcrypt.V3Policy.PktLenAccepted (wireBytes header) n ⦄ := by
  unfold decode_pkt_len Transcrypt.V3Policy.PktLenAccepted
  step with pkt_loop_spec header as ⟨ value, ok1, hr ⟩
  have hmax : MAX_PKT_LEN.val = 65520 := MAX_PKT_LEN_val
  unfold Transcrypt.V3Policy.maxPktLen
  cases ok1
  · simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
    simp only [WP.spec_ok, true_and]
    rintro n ⟨hn, _⟩
    rw [pktLen_iff, hr] at hn
    cases hn
  · simp only [↓reduceIte] at hr ⊢
    have hu : ∀ n, Transcrypt.V3Policy.PktLen (wireBytes header) n ↔ n = value.val := by
      intro n; rw [pktLen_iff, hr, Option.some.injEq, eq_comm]
    simp only [hu]
    clear hr hu
    split_ifs with h1 h2 h3 h3 <;>
      simp only [WP.spec_ok, true_and, not_and] <;>
      simp only [bne_iff_ne, ne_eq, UScalar.le_equiv, gt_iff_lt, UScalar.lt_equiv, hmax] at * <;>
      first
      | (rintro n rfl; scalar_tac)
      | scalar_tac

end Transcrypt.V3Verification

import Std.Tactic.BVDecide

/-
  Independent, fixed-width Base64 bit-manipulation specification.

  This deliberately does not import Aeneas-generated Rust functions.
  The obligations below state the mathematical laws corresponding to
  `rust-legacy/crates/transcrypt-protocol/src/base64_bits.rs`.

  The Z3 solver has discharged all these *bit-vector* obligations locally;
  this Lean target additionally asks Lean's `bv_decide` to produce and
  check proof certificates. An end-to-end proof of the actual Rust source
  still requires Charon/Aeneas generation and refinement proofs.
-/

namespace Transcrypt.LegacyBase64

private def s0 (a : BitVec 8) : BitVec 8 := a >>> 2
private def s1 (a b : BitVec 8) : BitVec 8 :=
  ((a &&& 3) <<< 4) ||| (b >>> 4)
private def s2 (b c : BitVec 8) : BitVec 8 :=
  ((b &&& 15) <<< 2) ||| (c >>> 6)
private def s3 (c : BitVec 8) : BitVec 8 := c &&& 63

private def d0 (u v : BitVec 8) : BitVec 8 := (u <<< 2) ||| (v >>> 4)
private def d1 (v w : BitVec 8) : BitVec 8 := (v <<< 4) ||| (w >>> 2)
private def d2 (w x : BitVec 8) : BitVec 8 := (w <<< 6) ||| x

/-- Every three-byte block roundtrips through the four six-bit values. -/
theorem full_block_roundtrip (a b c : BitVec 8) :
    d0 (s0 a) (s1 a b) = a ∧
    d1 (s1 a b) (s2 b c) = b ∧
    d2 (s2 b c) (s3 c) = c := by
  unfold d0 d1 d2 s0 s1 s2 s3
  bv_decide

/-- The output symbols always fit in six bits. -/
theorem sextets_are_six_bits (a b c : BitVec 8) :
    (s0 a &&& 192) = 0 ∧
    (s1 a b &&& 192) = 0 ∧
    (s2 b c &&& 192) = 0 ∧
    (s3 c &&& 192) = 0 := by
  unfold s0 s1 s2 s3
  bv_decide

/-- A single-byte tail always has canonical (zero) spare bits. -/
theorem one_byte_tail (a : BitVec 8) :
    d0 (s0 a) (s1 a 0) = a ∧ (s1 a 0 &&& 15) = 0 := by
  unfold d0 s0 s1
  bv_decide

/-- A two-byte tail always has canonical (zero) spare bits. -/
theorem two_byte_tail (a b : BitVec 8) :
    d0 (s0 a) (s1 a b) = a ∧
    d1 (s1 a b) (s2 b 0) = b ∧
    (s2 b 0 &&& 3) = 0 := by
  unfold d0 d1 s0 s1 s2
  bv_decide

end Transcrypt.LegacyBase64

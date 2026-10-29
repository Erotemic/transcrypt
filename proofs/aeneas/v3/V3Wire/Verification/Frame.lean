import V3Wire.Verification.Codec

/-!
Credential-agent request framing: the production encoder and decoder of the
60-byte request header refine `Transcrypt.V3Policy.frameHeader`, and decoding
inverts encoding. Local IPC only; not part of the committed wire format.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

@[step]
theorem encode_be_u32_spec (x : U32) :
    encode_be_u32 x ⦃ out => wireBytes out = be32 x.val ⦄ := by
  unfold encode_be_u32
  step*
  simp only [wireBytes, Std.Array.make, List.map, i1_post, i3_post, i5_post, i6_post,
    UScalar.cast_val_eq, be32, i_post1, i2_post1, i4_post1, Nat.shiftRight_eq_div_pow]
  simp [UScalarTy.numBits]

theorem be32_bv (c0 c1 c2 c3 : BitVec 8) :
    let r := ((c0.setWidth 32 <<< 24 ||| c1.setWidth 32 <<< 16) ||| c2.setWidth 32 <<< 8) |||
      c3.setWidth 32
    (r >>> 24).setWidth 8 = c0 ∧ (r >>> 16).setWidth 8 = c1 ∧ (r >>> 8).setWidth 8 = c2 ∧
      r.setWidth 8 = c3 := by
  intro r
  -- Bit by bit, without `bv_decide` (whose native evaluation adds axioms).
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext i hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals first | (simp [r]; done) | omega

theorem bv_byte (r : BitVec 32) (k : Nat) : ((r >>> k).setWidth 8).toNat = r.toNat / 2^k % 256 := by
  simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[step]
theorem decode_be_u32_spec (b : Std.Array U8 4#usize) :
    decode_be_u32 b ⦃ r => be32 r.val = wireBytes b ⦄ := by
  unfold decode_be_u32
  have hl : b.length = 4 := by simp
  step*
  have hcast : ∀ y : U8, U32.bv (UScalar.cast UScalarTy.U32 y) = y.bv.setWidth 32 := fun _ => rfl
  have hcast2 : ∀ y : U8, (UScalar.cast UScalarTy.U32 y).bv = y.bv.setWidth 32 := fun _ => rfl
  have hr : (i10 ||| i12).bv = ((b.val[0].bv.setWidth 32 <<< 24 ||| b.val[1].bv.setWidth 32 <<< 16) |||
      b.val[2].bv.setWidth 32 <<< 8) ||| b.val[3].bv.setWidth 32 := by
    rw [UScalar.bv_or, i10_post2, i6_post2, i2_post2, i5_post2, i9_post2, i12_post, i1_post,
      i4_post, i8_post]
    simp only [hcast]
    rw [← i_post2, ← i3_post2, ← i7_post2, ← i11_post2]
  obtain ⟨h0, h1, h2, h3⟩ := be32_bv b.val[0].bv b.val[1].bv b.val[2].bv b.val[3].bv
  have hv : (i10 ||| i12).val = (i10 ||| i12).bv.toNat := rfl
  have hb : b.val = [b.val[0], b.val[1], b.val[2], b.val[3]] := by
    apply List.ext_getElem (by simp)
    intro k h1 _
    have : k < 4 := by simpa using h1
    rcases k with _ | _ | _ | _ | k
    · rfl
    · rfl
    · rfl
    · rfl
    · omega
  rw [wireBytes, hb, be32, hv, hr]
  simp only [List.map_cons, List.map_nil]
  rw [← bv_byte, ← bv_byte, ← bv_byte, h0, h1, h2]
  have : (((b.val[0].bv.setWidth 32 <<< 24 ||| b.val[1].bv.setWidth 32 <<< 16) |||
      b.val[2].bv.setWidth 32 <<< 8) ||| b.val[3].bv.setWidth 32).toNat % 256 = b.val[3].bv.toNat := by
    have := congrArg BitVec.toNat h3
    rw [BitVec.toNat_setWidth] at this
    exact this
  rw [this]; rfl

theorem encode_frame_header_loop0_spec (base out : Std.Array U8 60#usize)
    (config : Std.Array U8 55#usize) (i : Usize) (hi : i.val ≤ 55)
    (h : Copied out.val base.val config.val 1 0 i.val) :
    encode_frame_header_loop0 config out i ⦃ r => Copied r.val base.val config.val 1 0 55 ⦄ := by
  unfold encode_frame_header_loop0
  apply copy_loop (val := fun o : Std.Array U8 60#usize => o.val) (bound := 55) _ _ _ _ _ _ _ _ hi h
  intro o j hj hc
  unfold encode_frame_header_loop0.body
  have hsrc : config.length = 55 := by simp
  have hC := CONFIG_LEN_val
  step*
  refine ⟨i3_post, by omega, ?_⟩
  rw [a_post, i3_post]
  apply Copied.array_step hc (by rw [i2_post])
  · simp_all [getElem!_pos]
  · simp; omega

theorem encode_frame_header_loop1_spec (base out : Std.Array U8 60#usize)
    (len : Std.Array U8 4#usize) (k : Usize) (hk : k.val ≤ 4)
    (h : Copied out.val base.val len.val 56 0 k.val) :
    encode_frame_header_loop1 out len k ⦃ r => Copied r.val base.val len.val 56 0 4 ⦄ := by
  unfold encode_frame_header_loop1
  apply copy_loop (val := fun o : Std.Array U8 60#usize => o.val) (bound := 4) _ _ _ _ _ _ _ _ hk h
  intro o j hj hc
  unfold encode_frame_header_loop1.body
  have hsrc : len.length = 4 := by simp
  have hC := CONFIG_LEN_val
  step*
  refine ⟨k1_post, by omega, ?_⟩
  rw [a_post, k1_post]
  apply Copied.array_step hc (by rw [i2_post, i1_post, hC])
  · simp_all [getElem!_pos]
  · simp; omega

/-- The production encoder emits exactly the spec's request header. -/
@[step]
theorem encode_frame_header_spec (opcode : U8) (config : Std.Array U8 55#usize) (path_len : U32) :
    encode_frame_header opcode config path_len ⦃ out =>
      wireBytes out = frameHeader opcode.val (wireBytes config) path_len.val ⦄ := by
  unfold encode_frame_header
  step*
  step with encode_frame_header_loop0_spec a a config 0#usize (by simp) (Copied.zero _ _ _ _) as ⟨ o1, h1 ⟩
  step with encode_be_u32_spec as ⟨ len, hlen ⟩
  step with encode_frame_header_loop1_spec o1 o1 len 0#usize (by simp) (Copied.zero _ _ _ _) as ⟨ o2, h2 ⟩
  have hval : o2.val = [opcode] ++ config.val ++ len.val := by
    apply list_eq_of_getElem! (by simp)
    intro k hk
    have hk60 : k < 60 := by simpa using hk
    have ho1 : o1.val.length = 60 := by simp
    have ha : a.val.length = 60 := by simp
    by_cases hlo : k < 56
    · rw [h2.get_out hk (by omega)]
      by_cases hz : k = 0
      · subst hz
        rw [h1.get_out (by omega) (by omega), a_post]
        simp [Std.Array.set]
      · rw [h1.get_in (by omega) (by omega) (by omega),
          List.getElem!_append_left _ _ _ (by simp; omega)]
        rw [show k = 1 + (k - 1) by omega, List.getElem!_append_right _ _ _ (by simp)]
        simp
    · rw [h2.get_in hk (by omega) (by omega), List.getElem!_append_right _ _ _ (by simp; omega)]
      simp
  simp only [wireBytes, hval, List.map_append, frameHeader]
  rw [← hlen]
  rfl

theorem decode_frame_header_loop_spec (input : Std.Array U8 60#usize) (base cfg : Std.Array U8 55#usize)
    (i : Usize) (hi : i.val ≤ 55) (h : Copied cfg.val base.val input.val 0 1 i.val) :
    decode_frame_header_loop input cfg i ⦃ r => Copied r.val base.val input.val 0 1 55 ⦄ := by
  unfold decode_frame_header_loop
  apply copy_loop (val := fun o : Std.Array U8 55#usize => o.val) (bound := 55) _ _ _ _ _ _ _ _ hi h
  intro o j hj hc
  unfold decode_frame_header_loop.body
  have hsrc : input.length = 60 := by simp
  have hol : o.length = 55 := by simp
  have hC := CONFIG_LEN_val
  step*
  have hj55 : j.val < 55 := by
    have := ‹j < CONFIG_LEN›; simp only [UScalar.lt_equiv, hC] at this; exact this
  refine ⟨i3_post, by omega, ?_⟩
  rw [a_post, i3_post]
  apply Copied.array_step hc (by simp)
  · rw [i2_post2, getElem!_pos input.val (1 + j.val) (by simp; omega)]
    simp only [i1_post]
  · simp; omega

/-- The production decoder reads the opcode, the 55 config bytes and the
    big-endian path length exactly as laid out by `frameHeader`. -/
@[step]
theorem decode_frame_header_spec (input : Std.Array U8 60#usize) :
    decode_frame_header input ⦃ r =>
      r.opcode.val :: wireBytes r.config ++ be32 r.path_len.val = wireBytes input ⦄ := by
  unfold decode_frame_header
  have hsrc : input.length = 60 := by simp
  have hC := CONFIG_LEN_val
  step with decode_frame_header_loop_spec input _ _ 0#usize (by simp) (Copied.zero _ _ _ _) as ⟨ cfg, hcfg ⟩
  step*
  subst i1_post2 i3_post2 i5_post2 i7_post2 i8_post2
  rw [i9_post]
  rw [hC] at i_post i2_post i4_post i6_post
  have hcl : cfg.val.length = 55 := by simp
  have hil : input.val.length = 60 := by simp
  have hval : input.val = input.val[0] :: cfg.val ++
      [input.val[i.val], input.val[i2.val], input.val[i4.val], input.val[i6.val]] := by
    apply list_eq_of_getElem! (by simp)
    intro k hk
    have hk60 : k < 60 := by simpa using hk
    rcases Nat.lt_or_ge k 56 with hlo | hhi
    · rcases Nat.eq_zero_or_pos k with hz | hpos
      · subst hz; simp
      · rw [show k = (k - 1) + 1 by omega, List.cons_append, List.getElem!_cons_succ,
          List.getElem!_append_left _ _ _ (by omega), hcfg.get_in (by omega) (by omega) (by omega)]
        congr 1; omega
    · rw [List.cons_append, show k = (k - 1) + 1 by omega, List.getElem!_cons_succ,
        List.getElem!_append_right _ _ _ (by omega), hcl]
      have : k - 1 - 55 < 4 := by omega
      rcases (show k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 by omega) with rfl | rfl | rfl | rfl <;>
        simp [i_post, i2_post, i4_post, i6_post, getElem!_pos, hil]
  conv => rhs; rw [wireBytes, hval]
  simp [wireBytes, Std.Array.make]

/-- Decoding an encoded request header returns exactly its fields. -/
theorem decode_frame_header_encode (opcode : U8) (config : Std.Array U8 55#usize) (path_len : U32) :
    (do let h ← encode_frame_header opcode config path_len; decode_frame_header h) ⦃ r =>
      r = { opcode, config, path_len } ⦄ := by
  step with encode_frame_header_spec as ⟨ h, hh ⟩
  step with decode_frame_header_spec as ⟨ r, hr ⟩
  rw [hh, frameHeader, List.singleton_append] at hr
  have hlen : (r.opcode.val :: wireBytes r.config).length = (opcode.val :: wireBytes config).length := by
    simp [wireBytes]
  obtain ⟨hhead, hpl⟩ := List.append_inj hr hlen
  obtain ⟨hop, hcfg⟩ := List.cons.inj hhead
  have hlt : ∀ x : U32, x.val < 2^32 := fun x => by have := x.hBounds; simpa using this
  cases r with
  | mk op c l =>
    simp only at hop hcfg hpl ⊢
    have h1 : op = opcode := (UScalar.eq_equiv _ _).2 hop
    have h2 : c = config := wireBytes_injective hcfg
    have h3 : l = path_len := (UScalar.eq_equiv _ _).2 (be32_injective (hlt l) (hlt path_len) hpl)
    rw [h1, h2, h3]

end Transcrypt.V3Verification

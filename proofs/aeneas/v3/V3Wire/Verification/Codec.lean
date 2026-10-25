import V3Wire.Verification.Copy
import V3Wire.Verification.Refinement
import Transcrypt.V3WireCodec

/-!
Full functional refinement of the production v3 wire codec. Every theorem
names the Aeneas-generated translation of the production Rust function
(`transcrypt_v3_core.*`) and relates its *complete* result — every byte, and
every success/error outcome — to the independently written specification in
`Transcrypt.V3Wire` / `Transcrypt.V3WireCodec`. The postconditions are
`WP.spec` triples, so they also rule out panics (index/overflow failures) and
divergence.

No cryptographic property is asserted: a structurally valid record is not an
authenticated one.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core

/-! ## Constant facts -/

@[simp] theorem FILE_MAGIC_length : FILE_MAGIC.length = 6 := by simp
@[simp] theorem CONFIG_MAGIC_length : CONFIG_MAGIC.length = 7 := by simp
@[simp] theorem FILE_MAGIC_slice_len : FILE_MAGIC.to_slice.len.val = 6 := by simp
@[simp] theorem CONFIG_MAGIC_slice_len : CONFIG_MAGIC.to_slice.len.val = 7 := by simp
@[simp] theorem ID_LEN_val : ID_LEN.val = 16 := by simp [ID_LEN]
@[simp] theorem SALT_LEN_val : SALT_LEN.val = 32 := by simp [SALT_LEN]
@[simp] theorem TAG_LEN_val : TAG_LEN.val = 16 := by simp [TAG_LEN]
@[simp] theorem CONFIG_PREFIX_LEN_val : CONFIG_PREFIX_LEN.val = 39 := by simp [CONFIG_PREFIX_LEN]
@[simp] theorem CONFIG_LEN_val : CONFIG_LEN.val = 55 := by simp [CONFIG_LEN]
@[simp] theorem FILE_HEADER_LEN_val : FILE_HEADER_LEN.val = 22 := by simp [FILE_HEADER_LEN]

/-! ## File header encoder -/

theorem encode_file_header_loop0_spec (base out : Std.Array U8 22#usize) (i : Usize)
    (hi : i.val ≤ 6) (h : Copied out.val base.val FILE_MAGIC.val 0 0 i.val) :
    encode_file_header_loop0 out i ⦃ r => Copied r.val base.val FILE_MAGIC.val 0 0 6 ⦄ := by
  unfold encode_file_header_loop0
  apply copy_loop (val := fun o : Std.Array U8 22#usize => o.val) (bound := 6) _ _ _ _ _ _ _ _ hi h
  intro o j hj hc
  unfold encode_file_header_loop0.body
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  step*
  have := FILE_MAGIC_length
  refine ⟨i3_post, by omega, ?_⟩
  rw [a_post, i2_post2, i3_post]
  have := hc.step (by simp; omega)
  simpa [getElem!_pos FILE_MAGIC.val j.val (by simpa using i2)] using this

theorem encode_file_header_loop1_spec (base out : Std.Array U8 22#usize) (src : Std.Array U8 16#usize)
    (j : Usize) (hj : j.val ≤ 16) (h : Copied out.val base.val src.val 6 0 j.val) :
    encode_file_header_loop1 src out j ⦃ r => Copied r.val base.val src.val 6 0 16 ⦄ := by
  unfold encode_file_header_loop1
  apply copy_loop (val := fun o : Std.Array U8 22#usize => o.val) (bound := 16) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold encode_file_header_loop1.body
  have hsrc : src.length = 16 := by simp
  have ho : o.length = 22 := by simp
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hID := ID_LEN_val
  step*
  refine ⟨j1_post, by omega, ?_⟩
  have hpos : i2.val = 6 + k.val := by rw [i2_post, s_post]; simp
  rw [a_post, i_post2, j1_post]
  have := hc.step (by simp; omega)
  simp only [Std.Array.set, hpos]
  rw [Nat.zero_add, getElem!_pos src.val k.val (by simp; omega)] at this
  exact this

/-- List equality from pointwise `getElem!` agreement. -/
theorem list_eq_of_getElem! {l₁ l₂ : List U8} (hl : l₁.length = l₂.length)
    (h : ∀ k, k < l₁.length → l₁[k]! = l₂[k]!) : l₁ = l₂ := by
  apply List.ext_getElem hl
  intro k h₁ h₂
  have := h k h₁
  rwa [getElem!_pos l₁ k h₁, getElem!_pos l₂ k h₂] at this

theorem getElem!_append_left' {l₁ l₂ : List U8} {k : Nat} (hk : k < l₁.length) :
    (l₁ ++ l₂)[k]! = l₁[k]! := by
  rw [getElem!_pos (l₁ ++ l₂) k (by simp; omega), getElem!_pos l₁ k hk, List.getElem_append_left]

theorem getElem!_append_right' {l₁ l₂ : List U8} {k : Nat} (hk : l₁.length ≤ k)
    (hk2 : k < l₁.length + l₂.length) :
    (l₁ ++ l₂)[k]! = l₂[k - l₁.length]! := by
  rw [getElem!_pos (l₁ ++ l₂) k (by simp; omega), getElem!_pos l₂ (k - l₁.length) (by omega),
    List.getElem_append_right hk]

/-- The production file-header encoder emits exactly the magic followed by
    the arbitrary 16-byte configuration identifier. -/
@[step]
theorem encode_file_header_bytes (id : Std.Array U8 16#usize) :
    encode_file_header id ⦃ out => out.val = FILE_MAGIC.val ++ id.val ⦄ := by
  unfold encode_file_header
  step with encode_file_header_loop0_spec (Array.repeat 22#usize 0#u8) as ⟨ o0, h0 ⟩
  · exact Copied.zero _ _ _ _
  step with encode_file_header_loop1_spec o0 o0 id as ⟨ o1, h1 ⟩
  · exact Copied.zero _ _ _ _
  apply list_eq_of_getElem! (by simp)
  intro k hk
  have hk22 : k < 22 := by simpa using hk
  by_cases hlt : k < 6
  · rw [h1.get_out hk (by omega), getElem!_append_left' (by simp; omega),
      h0.get_in (by simp; omega) (by omega) (by omega)]
    simp
  · rw [h1.get_in hk (by omega) (by omega), getElem!_append_right' (by simp; omega) (by simp; omega)]
    simp

/-! ## Config encoder -/

/-- One iteration of a copy loop writing into an Aeneas array. -/
theorem Copied.array_step {N : Usize} {o : Std.Array U8 N} {base src : List U8}
    {dst srcOff k : Nat} {p : Usize} {x : U8}
    (hc : Copied o.val base src dst srcOff k) (hp : p.val = dst + k)
    (hx : x = src[srcOff + k]!) (hlt : dst + k < o.val.length) :
    Copied (o.set p x).val base src dst srcOff (k + 1) := by
  have := hc.step hlt
  subst hx
  simpa [Std.Array.set, hp] using this

theorem encode_config_prefix_loop0_spec (base out : Std.Array U8 39#usize) (i : Usize)
    (hi : i.val ≤ 7) (h : Copied out.val base.val CONFIG_MAGIC.val 0 0 i.val) :
    encode_config_prefix_loop0 out i ⦃ r => Copied r.val base.val CONFIG_MAGIC.val 0 0 7 ⦄ := by
  unfold encode_config_prefix_loop0
  apply copy_loop (val := fun o : Std.Array U8 39#usize => o.val) (bound := 7) _ _ _ _ _ _ _ _ hi h
  intro o j hj hc
  unfold encode_config_prefix_loop0.body
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  step*
  have := CONFIG_MAGIC_length
  refine ⟨i3_post, by omega, ?_⟩
  rw [a_post, i2_post2, i3_post]
  have := hc.step (by simp; omega)
  simpa [getElem!_pos CONFIG_MAGIC.val j.val (by simpa using i2)] using this

theorem encode_config_prefix_loop1_spec (base out : Std.Array U8 39#usize) (src : Std.Array U8 32#usize)
    (j : Usize) (hj : j.val ≤ 32) (h : Copied out.val base.val src.val 7 0 j.val) :
    encode_config_prefix_loop1 src out j ⦃ r => Copied r.val base.val src.val 7 0 32 ⦄ := by
  unfold encode_config_prefix_loop1
  apply copy_loop (val := fun o : Std.Array U8 39#usize => o.val) (bound := 32) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold encode_config_prefix_loop1.body
  have hsrc : src.length = 32 := by simp
  have ho : o.length = 39 := by simp
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hID := SALT_LEN_val
  step*
  refine ⟨j1_post, by omega, ?_⟩
  have hpos : i2.val = 7 + k.val := by rw [i2_post, s_post]; simp
  rw [a_post, i_post2, j1_post]
  have := hc.step (by simp; omega)
  simp only [Std.Array.set, hpos]
  rw [Nat.zero_add, getElem!_pos src.val k.val (by simp; omega)] at this
  exact this

theorem encode_config_loop0_spec (base out : Std.Array U8 55#usize) (src : Std.Array U8 39#usize)
    (i : Usize) (hi : i.val ≤ 39) (h : Copied out.val base.val src.val 0 0 i.val) :
    encode_config_loop0 out src i ⦃ r => Copied r.val base.val src.val 0 0 39 ⦄ := by
  unfold encode_config_loop0
  apply copy_loop (val := fun o : Std.Array U8 55#usize => o.val) (bound := 39) _ _ _ _ _ _ _ _ hi h
  intro o k hk hc
  unfold encode_config_loop0.body
  have hsrc : src.length = 39 := by simp
  have ho : o.length = 55 := by simp
  have hID := CONFIG_PREFIX_LEN_val
  step*
  refine ⟨i2_post, by omega, ?_⟩
  rw [a_post, i2_post]
  apply Copied.array_step hc (by simp)
  · simp_all [getElem!_pos]
  · simp; omega

theorem encode_config_loop1_spec (base out : Std.Array U8 55#usize) (src : Std.Array U8 16#usize)
    (j : Usize) (hj : j.val ≤ 16) (h : Copied out.val base.val src.val 39 0 j.val) :
    encode_config_loop1 src out j ⦃ r => Copied r.val base.val src.val 39 0 16 ⦄ := by
  unfold encode_config_loop1
  apply copy_loop (val := fun o : Std.Array U8 55#usize => o.val) (bound := 16) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold encode_config_loop1.body
  have hsrc : src.length = 16 := by simp
  have ho : o.length = 55 := by simp
  have hID := TAG_LEN_val
  have hP := CONFIG_PREFIX_LEN_val
  step*
  refine ⟨j1_post, by omega, ?_⟩
  rw [a1_post, j1_post]
  apply Copied.array_step hc (by omega)
  · simp_all [getElem!_pos]
  · simp; omega

/-- The production config-prefix encoder emits the magic followed by the salt. -/
@[step]
theorem encode_config_prefix_bytes (salt : Std.Array U8 32#usize) :
    encode_config_prefix salt ⦃ out => out.val = CONFIG_MAGIC.val ++ salt.val ⦄ := by
  unfold encode_config_prefix
  step with encode_config_prefix_loop0_spec (Array.repeat 39#usize 0#u8) as ⟨ o0, h0 ⟩
  · exact Copied.zero _ _ _ _
  step with encode_config_prefix_loop1_spec o0 o0 salt as ⟨ o1, h1 ⟩
  · exact Copied.zero _ _ _ _
  apply list_eq_of_getElem! (by simp)
  intro k hk
  have hk39 : k < 39 := by simpa using hk
  by_cases hlt : k < 7
  · rw [h1.get_out hk (by omega), getElem!_append_left' (by simp; omega),
      h0.get_in (by simp; omega) (by omega) (by omega)]
    simp
  · rw [h1.get_in hk (by omega) (by omega), getElem!_append_right' (by simp; omega) (by simp; omega)]
    simp

/-- The production config encoder emits magic, salt and verifier tag. -/
@[step]
theorem encode_config_bytes (c : Config) :
    encode_config c ⦃ out => out.val = CONFIG_MAGIC.val ++ c.salt.val ++ c.tag.val ⦄ := by
  unfold encode_config
  step with encode_config_prefix_bytes c.salt as ⟨ p, hp ⟩
  step with encode_config_loop0_spec (Array.repeat 55#usize 0#u8) (Array.repeat 55#usize 0#u8) p as ⟨ o0, h0 ⟩
  · exact Copied.zero _ _ _ _
  step with encode_config_loop1_spec o0 o0 c.tag as ⟨ o1, h1 ⟩
  · exact Copied.zero _ _ _ _
  rw [← hp]
  apply list_eq_of_getElem! (by simp)
  intro k hk
  have hk55 : k < 55 := by simpa using hk
  by_cases hlt : k < 39
  · rw [h1.get_out hk (by omega), getElem!_append_left' (by simp; omega),
      h0.get_in (by simp; omega) (by omega) (by omega)]
    simp
  · rw [h1.get_in hk (by omega) (by omega), getElem!_append_right' (by simp; omega) (by simp; omega)]
    simp

/-! ## Decoders -/

theorem decode_file_header_exact_loop0_loop0_spec (input : Std.Array U8 22#usize)
    (base id : Std.Array U8 16#usize) (j : Usize) (hj : j.val ≤ 16)
    (h : Copied id.val base.val input.val 0 6 j.val) :
    decode_file_header_exact_loop0_loop0 input id j ⦃ r => Copied r.val base.val input.val 0 6 16 ⦄ := by
  unfold decode_file_header_exact_loop0_loop0
  apply copy_loop (val := fun o : Std.Array U8 16#usize => o.val) (bound := 16) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold decode_file_header_exact_loop0_loop0.body
  have hsrc : input.length = 22 := by simp
  have ho : o.length = 16 := by simp
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hID := ID_LEN_val
  step*
  have hs : s.len.val = 6 := by simp [s_post]
  refine ⟨j1_post, by omega, ?_⟩
  rw [a_post, j1_post]
  apply Copied.array_step hc (by simp)
  · rw [i2_post2, getElem!_pos input.val (6 + k.val) (by simp; omega)]
    simp only [i1_post, hs]
  · simp; omega

theorem decode_config_exact_loop0_loop0_spec (input : Std.Array U8 55#usize)
    (base salt : Std.Array U8 32#usize) (j : Usize) (hj : j.val ≤ 32)
    (h : Copied salt.val base.val input.val 0 7 j.val) :
    decode_config_exact_loop0_loop0 input salt j ⦃ r => Copied r.val base.val input.val 0 7 32 ⦄ := by
  unfold decode_config_exact_loop0_loop0
  apply copy_loop (val := fun o : Std.Array U8 32#usize => o.val) (bound := 32) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold decode_config_exact_loop0_loop0.body
  have hsrc : input.length = 55 := by simp
  have ho : o.length = 32 := by simp
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hID := SALT_LEN_val
  step*
  have hs : s.len.val = 7 := by simp [s_post]
  have hk32 : k.val < 32 := by scalar_tac
  refine ⟨j1_post, by omega, ?_⟩
  rw [a_post, j1_post]
  apply Copied.array_step hc (by simp)
  · rw [i2_post2, getElem!_pos input.val (7 + k.val) (by simp; omega)]
    simp only [i1_post, hs]
  · simp; omega

theorem decode_config_exact_loop0_loop1_spec (input : Std.Array U8 55#usize)
    (base tag : Std.Array U8 16#usize) (j : Usize) (hj : j.val ≤ 16)
    (h : Copied tag.val base.val input.val 0 39 j.val) :
    decode_config_exact_loop0_loop1 input tag j ⦃ r => Copied r.val base.val input.val 0 39 16 ⦄ := by
  unfold decode_config_exact_loop0_loop1
  apply copy_loop (val := fun o : Std.Array U8 16#usize => o.val) (bound := 16) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold decode_config_exact_loop0_loop1.body
  have hsrc : input.length = 55 := by simp
  have ho : o.length = 16 := by simp
  have hID := TAG_LEN_val
  have hP := CONFIG_PREFIX_LEN_val
  step*
  refine ⟨k1_post, by omega, ?_⟩
  rw [a_post, k1_post]
  apply Copied.array_step hc (by simp)
  · rw [i1_post2, getElem!_pos input.val (39 + k.val) (by simp; omega)]
    simp only [i_post, hP]
  · simp; omega

theorem take_ne_of_getElem!_ne {l M : List U8} {n i : Nat} (hi : i < n) (hn : n ≤ l.length)
    (h : l[i]! ≠ M[i]!) : l.take n ≠ M := by
  intro heq
  apply h
  rw [← heq, getElem!_pos (l.take n) i (by simp; omega), getElem!_pos l i (by omega),
    List.getElem_take]

theorem eq_append_of_matches_copied {inp M id base : List U8}
    (hlen : inp.length = M.length + id.length)
    (hm : MatchesUpTo inp M 0 M.length)
    (hc : Copied id base inp 0 M.length id.length) : inp = M ++ id := by
  apply list_eq_of_getElem! (by simp [hlen])
  intro k hk
  by_cases hlt : k < M.length
  · rw [getElem!_append_left' hlt]
    simpa using hm k hlt
  · rw [getElem!_append_right' (by omega) (by omega),
      hc.get_in (by omega) (by omega) (by omega)]
    congr 1
    omega

theorem decode_file_header_exact_loop0_spec (input : Std.Array U8 22#usize) (i : Usize)
    (hi : i.val ≤ 6) (h : MatchesUpTo input.val FILE_MAGIC.val 0 i.val) :
    decode_file_header_exact_loop0 input i ⦃ r => match r with
      | core.result.Result.Ok id => input.val = FILE_MAGIC.val ++ id.val
      | core.result.Result.Err FormatError.Magic => input.val.take 6 ≠ FILE_MAGIC.val
      | core.result.Result.Err FormatError.Length => False ⦄ := by
  unfold decode_file_header_exact_loop0
  apply compare_loop _ (fun n => MatchesUpTo input.val FILE_MAGIC.val 0 n) 6 _ _ i hi h
  intro j hj hm
  unfold decode_file_header_exact_loop0.body
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hsrc : input.length = 22 := by simp
  have hM := FILE_MAGIC_length
  simp only [lift, bind_tc_ok]
  split
  · step*
    · have hne := ‹(_ != _) = true›
      rw [i2_post2, i3_post2] at hne
      have hne' : input.val[j.val] ≠ FILE_MAGIC.val[j.val] := by simpa using hne
      apply take_ne_of_getElem!_ne (i := j.val) (by omega) (by simp)
      rw [getElem!_pos input.val j.val i2, getElem!_pos FILE_MAGIC.val j.val i3]
      exact hne'
    · have hne := ‹¬(_ != _) = true›
      rw [i2_post2, i3_post2] at hne
      have hne' : input.val[j.val] = FILE_MAGIC.val[j.val] :=
        (UScalar.eq_equiv _ _).2 (by simpa using hne)
      refine ⟨i4_post, by omega, ?_⟩
      rw [i4_post]
      apply hm.step
      rw [Nat.zero_add, getElem!_pos input.val j.val i2, getElem!_pos FILE_MAGIC.val j.val i3]
      exact hne'
  · rename_i hge
    have hj6 : j.val = 6 := by
      have : ¬ j.val < 6 := by simpa using hge
      omega
    step with decode_file_header_exact_loop0_loop0_spec input (Array.repeat 16#usize 0#u8) as ⟨ id1, h1 ⟩
    · exact Copied.zero _ _ _ _
    rw [hj6] at hm
    exact eq_append_of_matches_copied (by simp) (by simpa using hm) (by simpa using h1)

theorem eq_append3_of_matches_copied {inp M s t bs bt : List U8}
    (hlen : inp.length = M.length + s.length + t.length)
    (hm : MatchesUpTo inp M 0 M.length)
    (hs : Copied s bs inp 0 M.length s.length)
    (ht : Copied t bt inp 0 (M.length + s.length) t.length) : inp = M ++ s ++ t := by
  apply list_eq_of_getElem! (by simp [hlen]; omega)
  intro k hk
  by_cases hlt : k < M.length + s.length
  · rw [getElem!_append_left' (by simp; omega)]
    by_cases hlt' : k < M.length
    · rw [getElem!_append_left' hlt']
      simpa using hm k hlt'
    · rw [getElem!_append_right' (by omega) (by omega),
        hs.get_in (by omega) (by omega) (by omega)]
      congr 1
      omega
  · rw [getElem!_append_right' (by simp; omega) (by simp; omega),
      ht.get_in (by simp; omega) (by omega) (by simp; omega)]
    congr 1
    simp
    omega

theorem decode_config_exact_loop0_spec (input : Std.Array U8 55#usize) (i : Usize)
    (hi : i.val ≤ 7) (h : MatchesUpTo input.val CONFIG_MAGIC.val 0 i.val) :
    decode_config_exact_loop0 input i ⦃ r => match r with
      | core.result.Result.Ok c => input.val = CONFIG_MAGIC.val ++ c.salt.val ++ c.tag.val
      | core.result.Result.Err FormatError.Magic => input.val.take 7 ≠ CONFIG_MAGIC.val
      | core.result.Result.Err FormatError.Length => False ⦄ := by
  unfold decode_config_exact_loop0
  apply compare_loop _ (fun n => MatchesUpTo input.val CONFIG_MAGIC.val 0 n) 7 _ _ i hi h
  intro j hj hm
  unfold decode_config_exact_loop0.body
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hsrc : input.length = 55 := by simp
  have hM := CONFIG_MAGIC_length
  simp only [lift, bind_tc_ok]
  split
  · step*
    · have hne := ‹(_ != _) = true›
      rw [i2_post2, i3_post2] at hne
      have hne' : input.val[j.val] ≠ CONFIG_MAGIC.val[j.val] := by simpa using hne
      apply take_ne_of_getElem!_ne (i := j.val) (by omega) (by simp)
      rw [getElem!_pos input.val j.val i2, getElem!_pos CONFIG_MAGIC.val j.val i3]
      exact hne'
    · have hne := ‹¬(_ != _) = true›
      rw [i2_post2, i3_post2] at hne
      have hne' : input.val[j.val] = CONFIG_MAGIC.val[j.val] :=
        (UScalar.eq_equiv _ _).2 (by simpa using hne)
      refine ⟨i4_post, by omega, ?_⟩
      rw [i4_post]
      apply hm.step
      rw [Nat.zero_add, getElem!_pos input.val j.val i2, getElem!_pos CONFIG_MAGIC.val j.val i3]
      exact hne'
  · rename_i hge
    have hj7 : j.val = 7 := by
      have : ¬ j.val < 7 := by simpa using hge
      omega
    step with decode_config_exact_loop0_loop0_spec input (Array.repeat 32#usize 0#u8) as ⟨ s1, h1 ⟩
    · exact Copied.zero _ _ _ _
    step with decode_config_exact_loop0_loop1_spec input (Array.repeat 16#usize 0#u8) as ⟨ t1, h2 ⟩
    · exact Copied.zero _ _ _ _
    rw [hj7] at hm
    exact eq_append3_of_matches_copied (by simp) (by simpa using hm) (by simpa using h1)
      (by simpa using h2)

/-- The production exact file-header decoder accepts exactly the magic
    followed by an arbitrary identifier, and returns that identifier. -/
@[step]
theorem decode_file_header_exact_spec (input : Std.Array U8 22#usize) :
    decode_file_header_exact input ⦃ r => match r with
      | core.result.Result.Ok id => input.val = FILE_MAGIC.val ++ id.val
      | core.result.Result.Err FormatError.Magic => input.val.take 6 ≠ FILE_MAGIC.val
      | core.result.Result.Err FormatError.Length => False ⦄ :=
  decode_file_header_exact_loop0_spec input 0#usize (by simp) (MatchesUpTo.zero _ _ _)

/-- The production exact config decoder accepts exactly the magic followed by
    an arbitrary salt and tag, and returns them. -/
@[step]
theorem decode_config_exact_spec (input : Std.Array U8 55#usize) :
    decode_config_exact input ⦃ r => match r with
      | core.result.Result.Ok c => input.val = CONFIG_MAGIC.val ++ c.salt.val ++ c.tag.val
      | core.result.Result.Err FormatError.Magic => input.val.take 7 ≠ CONFIG_MAGIC.val
      | core.result.Result.Err FormatError.Length => False ⦄ :=
  decode_config_exact_loop0_spec input 0#usize (by simp) (MatchesUpTo.zero _ _ _)

/-! ## Slice-boundary parsers -/

theorem parse_config_loop_spec (input : Slice U8) (hlen : input.length = 55)
    (base record : Std.Array U8 55#usize) (i : Usize) (hi : i.val ≤ 55)
    (h : Copied record.val base.val input.val 0 0 i.val) :
    parse_config_loop input record i ⦃ r => Copied r.val base.val input.val 0 0 55 ⦄ := by
  unfold parse_config_loop
  apply copy_loop (val := fun o : Std.Array U8 55#usize => o.val) (bound := 55) _ _ _ _ _ _ _ _ hi h
  intro o k hk hc
  unfold parse_config_loop.body
  have ho : o.length = 55 := by simp
  have hID := CONFIG_LEN_val
  step*
  have hkb : k.val < 55 := by scalar_tac
  refine ⟨i2_post, by omega, ?_⟩
  rw [a_post, i2_post]
  apply Copied.array_step hc (by simp)
  · rw [i1_post2, Nat.zero_add, getElem!_pos input.val k.val i1]
  · simp; omega

theorem parse_file_header_loop_spec (input : Slice U8) (hlen : 22 ≤ input.length)
    (base header : Std.Array U8 22#usize) (i : Usize) (hi : i.val ≤ 22)
    (h : Copied header.val base.val input.val 0 0 i.val) :
    parse_file_header_loop input header i ⦃ r => Copied r.val base.val input.val 0 0 22 ⦄ := by
  unfold parse_file_header_loop
  apply copy_loop (val := fun o : Std.Array U8 22#usize => o.val) (bound := 22) _ _ _ _ _ _ _ _ hi h
  intro o k hk hc
  unfold parse_file_header_loop.body
  have ho : o.length = 22 := by simp
  have hID := FILE_HEADER_LEN_val
  step*
  have hkb : k.val < 22 := by scalar_tac
  refine ⟨i2_post, by omega, ?_⟩
  rw [a_post, i2_post]
  apply Copied.array_step hc (by simp)
  · rw [i1_post2, Nat.zero_add, getElem!_pos input.val k.val i1]
  · simp; omega

theorem map_val_injective : Function.Injective (List.map (fun b : U8 => b.val)) :=
  List.map_injective_iff.2 (fun a b h => (UScalar.eq_equiv a b).2 h)

theorem copied_full {out base src : List U8} {n : Nat} (h : Copied out base src 0 0 n)
    (hl : out.length = n) (hn : n ≤ src.length) : out = src.take n := by
  apply list_eq_of_getElem! (by simp; omega)
  intro k hk
  rw [h.get_in hk (by omega) (by omega), getElem!_pos (src.take n) k (by simp; omega),
    List.getElem_take, ← getElem!_pos src k (by omega)]
  simp

theorem config_shape_of_eq {l : List U8} (salt : Std.Array U8 32#usize)
    (tag : Std.Array U8 16#usize) (h : l = CONFIG_MAGIC.val ++ salt.val ++ tag.val) :
    Transcrypt.V3Wire.decodeConfigShape (l.map (fun b => b.val)) =
      some (wireBytes salt, wireBytes tag) := by
  have hm : l.map (fun b => b.val) =
      Transcrypt.V3Wire.encodeConfig (wireBytes salt) (wireBytes tag) := by
    rw [h, Transcrypt.V3Wire.encodeConfig, ← extracted_config_magic_matches_spec]
    simp [wireBytes]
  rw [hm]
  exact Transcrypt.V3Wire.decode_config_encode _ _ (by simp [wireBytes]) (by simp [wireBytes])

theorem config_shape_none_of_take {l : List U8} (h : l.take 7 ≠ CONFIG_MAGIC.val) :
    Transcrypt.V3Wire.decodeConfigShape (l.map (fun b => b.val)) = none := by
  apply Transcrypt.V3Wire.config_wrong_magic
  intro heq
  apply h
  apply map_val_injective
  rw [List.map_take, heq, ← extracted_config_magic_matches_spec]
  rfl

@[step]
theorem parse_config_spec (input : Slice U8) :
    parse_config input ⦃ r => match r with
      | core.result.Result.Ok c => Transcrypt.V3Wire.decodeConfigShape (sliceBytes input) =
          some (wireBytes c.salt, wireBytes c.tag)
      | core.result.Result.Err FormatError.Magic => input.length = 55 ∧
          Transcrypt.V3Wire.decodeConfigShape (sliceBytes input) = none
      | core.result.Result.Err FormatError.Length => input.length ≠ 55 ⦄ := by
  unfold parse_config
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  split
  · rename_i hne
    have h1 : input.len ≠ CONFIG_LEN := by simpa using hne
    have h2 : input.len.val ≠ 55 := by
      intro h3; apply h1; rw [UScalar.eq_equiv, h3, CONFIG_LEN_val]
    simp only [WP.spec_ok]
    simpa using h2
  rename_i hne
  have h55 : input.length = 55 := by simpa using hne
  step with parse_config_loop_spec input h55 (Array.repeat 55#usize 0#u8) as ⟨ rec, hrec ⟩
  · exact Copied.zero _ _ _ _
  step with decode_config_exact_spec rec as ⟨ r, hr ⟩
  have hrin : rec.val = input.val := by
    rw [copied_full hrec (by simp) (by simp [h55])]
    exact List.take_of_length_le (by simp [h55])
  unfold sliceBytes
  rw [← hrin]
  match r with
  | core.result.Result.Ok c => exact config_shape_of_eq c.salt c.tag hr
  | core.result.Result.Err FormatError.Magic => exact ⟨h55, config_shape_none_of_take hr⟩
  | core.result.Result.Err FormatError.Length => exact hr.elim

theorem file_shape_of_take {l : List U8} (id : Std.Array U8 16#usize) (hlen : 38 ≤ l.length)
    (h : l.take 22 = FILE_MAGIC.val ++ id.val) :
    Transcrypt.V3Wire.decodeFileHeaderShape (l.map (fun b => b.val)) = some (wireBytes id) := by
  have h6 : l.take 6 = FILE_MAGIC.val := by
    have : (l.take 22).take 6 = l.take 6 := by simp [List.take_take]
    rw [← this, h, List.take_append_of_le_length (by simp)]
    simp
  have h16 : (l.drop 6).take 16 = id.val := by
    have : (l.take 22).drop 6 = (l.drop 6).take 16 := by simp [List.drop_take]
    rw [← this, h]
    simp
  unfold Transcrypt.V3Wire.decodeFileHeaderShape
  have hM : FILE_MAGIC.val.map (fun b => b.val) = Transcrypt.V3Wire.fileMagic :=
    extracted_file_magic_matches_spec
  rw [if_pos (by simpa using hlen), ← List.map_take, h6, hM, if_pos rfl, ← List.map_drop,
    ← List.map_take, h16]
  rfl

theorem file_shape_none_of_take {l : List U8} (h : l.take 6 ≠ FILE_MAGIC.val) :
    Transcrypt.V3Wire.decodeFileHeaderShape (l.map (fun b => b.val)) = none := by
  apply Transcrypt.V3Wire.file_wrong_magic
  intro heq
  apply h
  apply map_val_injective
  rw [List.map_take, heq, ← extracted_file_magic_matches_spec]
  rfl

@[step]
theorem parse_file_header_spec (input : Slice U8) :
    parse_file_header input ⦃ r => match r with
      | core.result.Result.Ok id => Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes input) =
          some (wireBytes id)
      | core.result.Result.Err FormatError.Magic => 38 ≤ input.length ∧
          Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes input) = none
      | core.result.Result.Err FormatError.Length => input.length < 38 ⦄ := by
  unfold parse_file_header FILE_MIN_LEN
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  have h1 := FILE_HEADER_LEN_val
  have h2 := TAG_LEN_val
  step*
  · rename_i hge
    have h38 : 38 ≤ input.length := by
      have : ¬ input.len.val < i1.val := hge
      simp only [Slice.len_val] at this
      omega
    step with parse_file_header_loop_spec input (by omega) (Array.repeat 22#usize 0#u8) as ⟨ hd, hhd ⟩
    · exact Copied.zero _ _ _ _
    step with decode_file_header_exact_spec hd as ⟨ r, hr ⟩
    have hrin : hd.val = input.val.take 22 := copied_full hhd (by simp) (by have : 38 ≤ input.val.length := h38; omega)
    unfold sliceBytes
    rw [hrin] at hr
    match r with
    | core.result.Result.Ok id => exact file_shape_of_take id (by simpa using h38) hr
    | core.result.Result.Err FormatError.Magic =>
      refine ⟨h38, file_shape_none_of_take ?_⟩
      rwa [List.take_take, Nat.min_eq_left (by omega)] at hr
    | core.result.Result.Err FormatError.Length => exact hr.elim

/-! ## Spec-facing corollaries -/

/-- The production file-header encoder refines the independent `encodeFile`
    (header part, i.e. with an empty authenticated payload). -/
theorem encode_file_header_refines (id : Std.Array U8 16#usize) :
    encode_file_header id ⦃ out =>
      wireBytes out = Transcrypt.V3Wire.encodeFile (wireBytes id) [] ⦄ := by
  apply WP.spec_mono (encode_file_header_bytes id)
  intro out h
  rw [Transcrypt.V3Wire.encodeFile, ← extracted_file_magic_matches_spec]
  simp [wireBytes, h]

/-- The production config encoder refines the independent `encodeConfig`. -/
theorem encode_config_refines (c : Config) :
    encode_config c ⦃ out =>
      wireBytes out = Transcrypt.V3Wire.encodeConfig (wireBytes c.salt) (wireBytes c.tag) ⦄ := by
  apply WP.spec_mono (encode_config_bytes c)
  intro out h
  rw [Transcrypt.V3Wire.encodeConfig, ← extracted_config_magic_matches_spec]
  simp [wireBytes, h]

/-- Production roundtrip: decoding an encoded config yields the same config. -/
theorem decode_config_exact_encode_config (c : Config) :
    (do let out ← encode_config c; decode_config_exact out) ⦃ r =>
      r = core.result.Result.Ok c ⦄ := by
  step with encode_config_bytes c as ⟨ out, hout ⟩
  step with decode_config_exact_spec out as ⟨ r, hr ⟩
  rcases r with c' | e
  · simp only [hout, List.append_assoc] at hr
    have h2 := List.append_cancel_left hr
    obtain ⟨hs, ht⟩ := List.append_inj h2 (by simp)
    obtain ⟨cs, ct⟩ := c
    obtain ⟨cs', ct'⟩ := c'
    simp only at hs ht
    have : cs = cs' := Subtype.ext hs
    have : ct = ct' := Subtype.ext ht
    subst_vars
    rfl
  · cases e
    · exact hr.elim
    · exact absurd (by rw [hout, List.append_assoc]; simp) hr

/-- Production roundtrip: decoding an encoded file header yields the same id. -/
theorem decode_file_header_exact_encode_file_header (id : Std.Array U8 16#usize) :
    (do let out ← encode_file_header id; decode_file_header_exact out) ⦃ r =>
      r = core.result.Result.Ok id ⦄ := by
  step with encode_file_header_bytes id as ⟨ out, hout ⟩
  step with decode_file_header_exact_spec out as ⟨ r, hr ⟩
  rcases r with id' | e
  · simp only [hout] at hr
    have : id = id' := Subtype.ext (List.append_cancel_left hr)
    subst this
    rfl
  · cases e
    · exact hr.elim
    · exact absurd (by rw [hout]; simp) hr

theorem wireBytes_injective {n : Usize} {a b : Std.Array U8 n}
    (h : wireBytes a = wireBytes b) : a = b :=
  Subtype.ext (map_val_injective h)

/-- Public slice-boundary roundtrip for configs: the production parser
    recovers exactly the config the production encoder serialized. -/
theorem parse_config_encode_config (c : Config) :
    (do let out ← encode_config c; parse_config out.to_slice) ⦃ r =>
      r = core.result.Result.Ok c ⦄ := by
  step with encode_config_refines c as ⟨ out, hout ⟩
  step with parse_config_spec out.to_slice as ⟨ r, hr ⟩
  have hsb : sliceBytes out.to_slice = wireBytes out := rfl
  have hdec := Transcrypt.V3Wire.decode_config_encode (wireBytes c.salt) (wireBytes c.tag)
    (by simp [wireBytes]) (by simp [wireBytes])
  rw [hsb, hout, hdec] at hr
  rcases r with c' | e
  · simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨hs, ht⟩ := hr
    obtain ⟨cs, ct⟩ := c
    obtain ⟨cs', ct'⟩ := c'
    simp only at hs ht
    rw [wireBytes_injective hs, wireBytes_injective ht]
  · cases e
    · simp at hr
    · simp at hr

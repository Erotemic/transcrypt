import V3Wire.Verification.Bytes

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
open Transcrypt.V3Wire (fileMagicLen idLen configMagicLen saltLen tagLen configLen fileHeaderLen fileMinLen)

/-! ## File header encoder -/

theorem encode_file_header_loop0_spec (base out : Std.Array U8 22#usize) (i : Usize)
    (hi : i.val ≤ fileMagicLen) (h : Copied out.val base.val FILE_MAGIC.val 0 0 i.val) :
    encode_file_header_loop0 out i ⦃ r => Copied r.val base.val FILE_MAGIC.val 0 0 fileMagicLen ⦄ := by
  unfold encode_file_header_loop0
  apply copy_loop (val := fun o : Std.Array U8 22#usize => o.val) (bound := fileMagicLen) _ _ _ _ _ _ _ _ hi h
  intro o j hj hc
  unfold_v3_bytes
  unfold encode_file_header_loop0.body
  simp_len
  step*
  have := FILE_MAGIC_length
  refine ⟨i3_post, by omega, ?_⟩
  rw [a_post, i3_post]
  apply Copied.array_step hc (by simp)
  · simp_all [getElem!_pos]
  · simp; omega

theorem encode_file_header_loop1_spec (base out : Std.Array U8 22#usize) (src : Std.Array U8 16#usize)
    (j : Usize) (hj : j.val ≤ idLen) (h : Copied out.val base.val src.val fileMagicLen 0 j.val) :
    encode_file_header_loop1 src out j ⦃ r => Copied r.val base.val src.val fileMagicLen 0 idLen ⦄ := by
  unfold encode_file_header_loop1
  apply copy_loop (val := fun o : Std.Array U8 22#usize => o.val) (bound := idLen) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold_v3_bytes
  unfold encode_file_header_loop1.body
  have hsrc : src.length = 16 := by simp
  have ho : o.length = 22 := by simp
  simp_len
  have hID := ID_LEN_val
  step*
  refine ⟨j1_post, by omega, ?_⟩
  rw [a_post, j1_post]
  apply Copied.array_step hc (by rw [i2_post, s_post]; simp)
  · simp_all [getElem!_pos]
  · simp; omega

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
  exact copied_concat h0 h1 (by simp) (by simp) (by simp; rfl)

/-! ## Config encoder -/

theorem encode_config_prefix_loop0_spec (base out : Std.Array U8 39#usize) (i : Usize)
    (hi : i.val ≤ configMagicLen) (h : Copied out.val base.val CONFIG_MAGIC.val 0 0 i.val) :
    encode_config_prefix_loop0 out i ⦃ r => Copied r.val base.val CONFIG_MAGIC.val 0 0 configMagicLen ⦄ := by
  unfold encode_config_prefix_loop0
  apply copy_loop (val := fun o : Std.Array U8 39#usize => o.val) (bound := configMagicLen) _ _ _ _ _ _ _ _ hi h
  intro o j hj hc
  unfold_v3_bytes
  unfold encode_config_prefix_loop0.body
  simp_len
  step*
  have := CONFIG_MAGIC_length
  refine ⟨i3_post, by omega, ?_⟩
  rw [a_post, i3_post]
  apply Copied.array_step hc (by simp)
  · simp_all [getElem!_pos]
  · simp; omega

theorem encode_config_prefix_loop1_spec (base out : Std.Array U8 39#usize) (src : Std.Array U8 32#usize)
    (j : Usize) (hj : j.val ≤ saltLen) (h : Copied out.val base.val src.val configMagicLen 0 j.val) :
    encode_config_prefix_loop1 src out j ⦃ r => Copied r.val base.val src.val configMagicLen 0 saltLen ⦄ := by
  unfold encode_config_prefix_loop1
  apply copy_loop (val := fun o : Std.Array U8 39#usize => o.val) (bound := saltLen) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold_v3_bytes
  unfold encode_config_prefix_loop1.body
  have hsrc : src.length = 32 := by simp
  have ho : o.length = 39 := by simp
  simp_len
  have hID := SALT_LEN_val
  step*
  refine ⟨j1_post, by omega, ?_⟩
  rw [a_post, j1_post]
  apply Copied.array_step hc (by rw [i2_post, s_post]; simp)
  · simp_all [getElem!_pos]
  · simp; omega

theorem encode_config_loop0_spec (base out : Std.Array U8 55#usize) (src : Std.Array U8 39#usize)
    (i : Usize) (hi : i.val ≤ configMagicLen + saltLen) (h : Copied out.val base.val src.val 0 0 i.val) :
    encode_config_loop0 out src i ⦃ r => Copied r.val base.val src.val 0 0 (configMagicLen + saltLen) ⦄ := by
  unfold encode_config_loop0
  apply copy_loop (val := fun o : Std.Array U8 55#usize => o.val) (bound := configMagicLen + saltLen) _ _ _ _ _ _ _ _ hi h
  intro o k hk hc
  unfold_v3_bytes
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
    (j : Usize) (hj : j.val ≤ tagLen) (h : Copied out.val base.val src.val (configMagicLen + saltLen) 0 j.val) :
    encode_config_loop1 src out j ⦃ r => Copied r.val base.val src.val (configMagicLen + saltLen) 0 tagLen ⦄ := by
  unfold encode_config_loop1
  apply copy_loop (val := fun o : Std.Array U8 55#usize => o.val) (bound := tagLen) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold_v3_bytes
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
  exact copied_concat h0 h1 (by simp) (by simp) (by simp; rfl)

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
  exact copied_concat h0 h1 (by simp; rfl) (by simp) (by simp; rfl)

/-! ## Decoders -/

theorem decode_file_header_exact_loop_spec (input : Std.Array U8 22#usize)
    (base id : Std.Array U8 16#usize) (j : Usize) (hj : j.val ≤ idLen)
    (h : Copied id.val base.val input.val 0 fileMagicLen j.val) :
    decode_file_header_exact_loop input id j ⦃ r => Copied r.val base.val input.val 0 fileMagicLen idLen ⦄ := by
  unfold decode_file_header_exact_loop
  apply copy_loop (val := fun o : Std.Array U8 16#usize => o.val) (bound := idLen) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold_v3_bytes
  unfold decode_file_header_exact_loop.body
  have hsrc : input.length = 22 := by simp
  have ho : o.length = 16 := by simp
  simp_len
  have hID := ID_LEN_val
  step*
  have hs : s.len.val = 6 := by simp [s_post]
  refine ⟨j1_post, by omega, ?_⟩
  rw [a_post, j1_post]
  apply Copied.array_step hc (by simp)
  · rw [i2_post2, getElem!_pos input.val (6 + k.val) (by simp; omega)]
    simp only [i1_post, hs]
  · simp; omega

theorem decode_config_exact_loop0_spec (input : Std.Array U8 55#usize)
    (base salt : Std.Array U8 32#usize) (j : Usize) (hj : j.val ≤ saltLen)
    (h : Copied salt.val base.val input.val 0 configMagicLen j.val) :
    decode_config_exact_loop0 input salt j ⦃ r => Copied r.val base.val input.val 0 configMagicLen saltLen ⦄ := by
  unfold decode_config_exact_loop0
  apply copy_loop (val := fun o : Std.Array U8 32#usize => o.val) (bound := saltLen) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold_v3_bytes
  unfold decode_config_exact_loop0.body
  have hsrc : input.length = 55 := by simp
  have ho : o.length = 32 := by simp
  simp_len
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

theorem decode_config_exact_loop1_spec (input : Std.Array U8 55#usize)
    (base tag : Std.Array U8 16#usize) (j : Usize) (hj : j.val ≤ tagLen)
    (h : Copied tag.val base.val input.val 0 (configMagicLen + saltLen) j.val) :
    decode_config_exact_loop1 input tag j ⦃ r => Copied r.val base.val input.val 0 (configMagicLen + saltLen) tagLen ⦄ := by
  unfold decode_config_exact_loop1
  apply copy_loop (val := fun o : Std.Array U8 16#usize => o.val) (bound := tagLen) _ _ _ _ _ _ _ _ hj h
  intro o k hk hc
  unfold_v3_bytes
  unfold decode_config_exact_loop1.body
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

/-- `matches_at input 0 magic`, for an input at least as long as the magic,
    says exactly whether the input starts with the magic. -/
theorem matches_magic_iff (input M : List U8) (h : M.length ≤ input.length) :
    (0 ≤ input.length ∧ M.map (·.val) <+: (input.map (·.val)).drop 0) ↔
      MatchesUpTo input M 0 M.length := by
  rw [map_prefix_drop_iff _ _ _ (Nat.zero_le _)]
  exact ⟨fun h' => h'.2.2, fun hm => ⟨Nat.zero_le _, by omega, hm⟩⟩

theorem take_ne_of_not_matches {l M : List U8} (h : ¬ MatchesUpTo l M 0 M.length) :
    l.take M.length ≠ M := by
  intro heq
  apply h
  intro k hk
  have hl : k < l.length := by
    have := congrArg List.length heq
    simp at this
    omega
  rw [Nat.zero_add, ← heq, getElem!_pos l k hl, getElem!_pos (l.take M.length) k (by simp; omega),
    List.getElem_take]

theorem eq_append_of_matches_copied {inp M id base : List U8}
    (hlen : inp.length = M.length + id.length)
    (hm : MatchesUpTo inp M 0 M.length)
    (hc : Copied id base inp 0 M.length id.length) : inp = M ++ id := by
  apply list_eq_of_getElem! (by simp [hlen])
  intro k hk
  by_cases hlt : k < M.length
  · rw [List.getElem!_append_left _ _ _ hlt]
    simpa using hm k hlt
  · rw [List.getElem!_append_right _ _ _ (by omega),
      hc.get_in (by omega) (by omega) (by omega)]
    congr 1
    omega

theorem eq_append3_of_matches_copied {inp M s t bs bt : List U8}
    (hlen : inp.length = M.length + s.length + t.length)
    (hm : MatchesUpTo inp M 0 M.length)
    (hs : Copied s bs inp 0 M.length s.length)
    (ht : Copied t bt inp 0 (M.length + s.length) t.length) : inp = M ++ s ++ t := by
  apply list_eq_of_getElem! (by simp [hlen]; omega)
  intro k hk
  by_cases hlt : k < M.length + s.length
  · rw [List.getElem!_append_left _ _ _ (by simp; omega)]
    by_cases hlt' : k < M.length
    · rw [List.getElem!_append_left _ _ _ hlt']
      simpa using hm k hlt'
    · rw [List.getElem!_append_right _ _ _ (by omega),
        hs.get_in (by omega) (by omega) (by omega)]
      congr 1
      omega
  · rw [List.getElem!_append_right _ _ _ (by simp; omega),
      ht.get_in (by simp; omega) (by omega) (by simp; omega)]
    congr 1
    simp
    omega

/-- The production exact file-header decoder accepts exactly the magic
    followed by an arbitrary identifier, and returns that identifier. -/
@[step]
theorem decode_file_header_exact_spec (input : Std.Array U8 22#usize) :
    decode_file_header_exact input ⦃ r => match r with
      | core.result.Result.Ok id => input.val = FILE_MAGIC.val ++ id.val
      | core.result.Result.Err FormatError.Magic => input.val.take Transcrypt.V3Wire.fileMagicLen ≠ FILE_MAGIC.val
      | core.result.Result.Err FormatError.Length => False ⦄ := by
  unfold decode_file_header_exact
  unfold_v3_bytes
  simp only [lift, bind_tc_ok]
  step with matches_at_spec as ⟨ b, hb ⟩
  have hm := matches_magic_iff input.val FILE_MAGIC.val (by simp)
  simp only [sliceBytes, Array.to_slice, Slice.length] at hb hm
  split
  · step with decode_file_header_exact_loop_spec input (Array.repeat 16#usize 0#u8) as ⟨ id1, h1 ⟩
    · exact Copied.zero _ _ _ _
    exact eq_append_of_matches_copied (by simp) (by simpa using hm.1 (hb.1 ‹_›))
      (by simpa using h1)
  · simpa using take_ne_of_not_matches (fun h => ‹¬b = true› (hb.2 (hm.2 h)))

/-- The production exact config decoder accepts exactly the magic followed by
    an arbitrary salt and tag, and returns them. -/
@[step]
theorem decode_config_exact_spec (input : Std.Array U8 55#usize) :
    decode_config_exact input ⦃ r => match r with
      | core.result.Result.Ok c => input.val = CONFIG_MAGIC.val ++ c.salt.val ++ c.tag.val
      | core.result.Result.Err FormatError.Magic => input.val.take Transcrypt.V3Wire.configMagicLen ≠ CONFIG_MAGIC.val
      | core.result.Result.Err FormatError.Length => False ⦄ := by
  unfold decode_config_exact
  unfold_v3_bytes
  simp only [lift, bind_tc_ok]
  step with matches_at_spec as ⟨ b, hb ⟩
  have hm := matches_magic_iff input.val CONFIG_MAGIC.val (by simp)
  simp only [sliceBytes, Array.to_slice, Slice.length] at hb hm
  split
  · step with decode_config_exact_loop0_spec input (Array.repeat 32#usize 0#u8) as ⟨ s1, h1 ⟩
    · exact Copied.zero _ _ _ _
    step with decode_config_exact_loop1_spec input (Array.repeat 16#usize 0#u8) as ⟨ t1, h2 ⟩
    · exact Copied.zero _ _ _ _
    exact eq_append3_of_matches_copied (by simp) (by simpa using hm.1 (hb.1 ‹_›))
      (by simpa using h1) (by unfold_v3_bytes; simpa using h2)
  · simpa using take_ne_of_not_matches (fun h => ‹¬b = true› (hb.2 (hm.2 h)))

/-! ## Slice-boundary parsers -/

theorem parse_config_loop_spec (input : Slice U8) (hlen : input.length = configLen)
    (base record : Std.Array U8 55#usize) (i : Usize) (hi : i.val ≤ configLen)
    (h : Copied record.val base.val input.val 0 0 i.val) :
    parse_config_loop input record i ⦃ r => Copied r.val base.val input.val 0 0 configLen ⦄ := by
  unfold parse_config_loop
  apply copy_loop (val := fun o : Std.Array U8 55#usize => o.val) (bound := configLen) _ _ _ _ _ _ _ _ hi h
  intro o k hk hc
  unfold_v3_bytes
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

theorem parse_file_header_loop_spec (input : Slice U8) (hlen : fileHeaderLen ≤ input.length)
    (base header : Std.Array U8 22#usize) (i : Usize) (hi : i.val ≤ fileHeaderLen)
    (h : Copied header.val base.val input.val 0 0 i.val) :
    parse_file_header_loop input header i ⦃ r => Copied r.val base.val input.val 0 0 fileHeaderLen ⦄ := by
  unfold parse_file_header_loop
  apply copy_loop (val := fun o : Std.Array U8 22#usize => o.val) (bound := fileHeaderLen) _ _ _ _ _ _ _ _ hi h
  intro o k hk hc
  unfold_v3_bytes
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

theorem config_shape_none_of_take {l : List U8} (h : l.take configMagicLen ≠ CONFIG_MAGIC.val) :
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
      | core.result.Result.Err FormatError.Magic => input.length = Transcrypt.V3Wire.configLen ∧
          Transcrypt.V3Wire.decodeConfigShape (sliceBytes input) = none
      | core.result.Result.Err FormatError.Length => input.length ≠ Transcrypt.V3Wire.configLen ⦄ := by
  unfold parse_config
  unfold_v3_bytes
  simp_len [bind_tc_ok]
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
    rw [copied_full hrec (by unfold_v3_bytes; simp) (by unfold_v3_bytes; simp [h55])]
    exact List.take_of_length_le (by unfold_v3_bytes; simp [h55])
  unfold sliceBytes
  rw [← hrin]
  match r with
  | core.result.Result.Ok c => exact config_shape_of_eq c.salt c.tag hr
  | core.result.Result.Err FormatError.Magic => exact ⟨h55, config_shape_none_of_take hr⟩
  | core.result.Result.Err FormatError.Length => exact hr.elim

theorem file_shape_of_take {l : List U8} (id : Std.Array U8 16#usize) (hlen : fileMinLen ≤ l.length)
    (h : l.take fileHeaderLen = FILE_MAGIC.val ++ id.val) :
    Transcrypt.V3Wire.decodeFileHeaderShape (l.map (fun b => b.val)) = some (wireBytes id) := by
  unfold_v3_bytes
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
  rw [if_pos (by rw [List.length_map]; exact hlen), ← List.map_take, h6, hM, if_pos rfl, ← List.map_drop,
    ← List.map_take, h16]
  rfl

theorem file_shape_none_of_take {l : List U8} (h : l.take fileMagicLen ≠ FILE_MAGIC.val) :
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
      | core.result.Result.Err FormatError.Magic => Transcrypt.V3Wire.fileMinLen ≤ input.length ∧
          Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes input) = none
      | core.result.Result.Err FormatError.Length => input.length < Transcrypt.V3Wire.fileMinLen ⦄ := by
  unfold parse_file_header FILE_MIN_LEN
  unfold_v3_bytes
  simp_len [bind_tc_ok]
  have h1 := FILE_HEADER_LEN_val
  have h2 := TAG_LEN_val
  step*
  · rename_i hge
    have h38 : 38 ≤ input.length := by
      have : ¬ input.len.val < i1.val := hge
      simp only [Slice.len_val] at this
      omega
    step with parse_file_header_loop_spec input (by unfold_v3_bytes; omega) (Array.repeat 22#usize 0#u8) as ⟨ hd, hhd ⟩
    · exact Copied.zero _ _ _ _
    step with decode_file_header_exact_spec hd as ⟨ r, hr ⟩
    have hrin : hd.val = input.val.take 22 := copied_full hhd (by simp) (by have : 38 ≤ input.val.length := h38; omega)
    unfold sliceBytes
    rw [hrin] at hr
    match r with
    | core.result.Result.Ok id => exact file_shape_of_take id (by unfold_v3_bytes; simpa using h38) hr
    | core.result.Result.Err FormatError.Magic =>
      refine ⟨h38, file_shape_none_of_take ?_⟩
      rwa [List.take_take, Nat.min_eq_left (by decide)] at hr
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
    · simp at hr; exact absurd rfl hr
    · simp at hr

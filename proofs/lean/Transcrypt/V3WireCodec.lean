import Transcrypt.V3Wire

/-!
Independent executable *shape* decoder for the v3 committed wire protocol.
It is not an Aeneas translation. The production slice parsers are proved to
compute exactly `decodeConfigShape` / `decodeFileHeaderShape`
(`parse_config_spec`, `parse_file_header_spec` in
`proofs/aeneas/v3/V3Wire/Verification/Codec.lean`). Ciphertext
authentication remains outside the shape decoder.
-/

namespace Transcrypt.V3Wire

/-- Strict configuration decoder: no extra bytes, the exact family marker,
    and a profile byte that names a profile; returns the profile, salt and
    tag. -/
def decodeConfigShape (bytes : List Nat) : Option (Profile × List Nat × List Nat) :=
  if bytes.length = configLen then
    if bytes.take configFamilyLen = configFamily then
      match profileOfByte (bytes.getD configFamilyLen 0) with
      | some p => some (p, (bytes.drop configMagicLen).take saltLen, (bytes.drop configMagicLen).drop saltLen)
      | none => none
    else none
  else none

/-- A file header is valid only with room for the full SIV tag. -/
def decodeFileHeaderShape (bytes : List Nat) : Option (List Nat) :=
  if fileMinLen ≤ bytes.length then
    if bytes.take fileMagicLen = fileMagic then
      some ((bytes.drop fileMagicLen).take idLen)
    else none
  else none

/-- Exact configuration serialization is recovered by its independent
    parser, profile included. -/
theorem decode_config_encode (p : Profile) (salt tag : List Nat)
    (hs : salt.length = saltLen) (ht : tag.length = tagLen) :
    decodeConfigShape (encodeConfig p salt tag) = some (p, salt, tag) := by
  have hlen : (encodeConfig p salt tag).length = configLen := config_length p salt tag hs ht
  have hfam : (encodeConfig p salt tag).take configFamilyLen = configFamily := by
    simp [encodeConfig, configMagic, configFamily]
  have hbyte : (encodeConfig p salt tag).getD configFamilyLen 0 = profileByte p := by
    simp [encodeConfig, configMagic, configFamily]
  have hd : (encodeConfig p salt tag).drop configMagicLen = salt ++ tag := by
    change (configMagic p ++ (salt ++ tag)).drop (configMagic p).length = salt ++ tag
    exact List.drop_append_length
  have htaken : (salt ++ tag).take saltLen = salt := by
    simpa only [hs] using (List.take_append_length (l₁ := salt) (l₂ := tag))
  have hdropped : (salt ++ tag).drop saltLen = tag := by
    simpa only [hs] using (List.drop_append_length (l₁ := salt) (l₂ := tag))
  simp only [decodeConfigShape, hlen, hfam, hbyte, profileOfByte_profileByte, hd, htaken, hdropped, if_true]

/-- An accepted configuration is exactly the encoding of what it decodes to. -/
theorem encode_of_decodeConfigShape {bytes salt tag : List Nat} {p : Profile}
    (h : decodeConfigShape bytes = some (p, salt, tag)) :
    bytes = encodeConfig p salt tag ∧ salt.length = saltLen ∧ tag.length = tagLen := by
  unfold decodeConfigShape at h
  split at h
  · rename_i hlen
    split at h
    · rename_i hfam
      split at h
      · rename_i q hq
        cases h
        have hb := profileByte_of_profileOfByte hq
        have hmagic : bytes.take configMagicLen = configMagic p := by
          have h7 : bytes.take configMagicLen = bytes.take configFamilyLen ++ [bytes.getD configFamilyLen 0] := by
            rw [show configMagicLen = configFamilyLen + 1 from rfl, List.take_add_one]
            have : configFamilyLen < bytes.length := by
              simp only [configLen, configMagicLen, saltLen, tagLen, configFamilyLen] at hlen ⊢; omega
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
          rw [h7, hfam, ← hb]; rfl
        refine ⟨?_, ?_, ?_⟩
        · conv => lhs; rw [← List.take_append_drop configMagicLen bytes]
          rw [hmagic, encodeConfig, List.append_assoc, List.take_append_drop]
        · simp only [configLen, configMagicLen, saltLen, tagLen] at hlen
          simp [hlen, configMagicLen, saltLen]
        · simp only [configLen, configMagicLen, saltLen, tagLen] at hlen
          simp [hlen, configMagicLen, saltLen, tagLen]
      · cases h
    · cases h
  · cases h

/-- Missing or additional configuration bytes are never accepted. -/
theorem config_wrong_length (bytes : List Nat) (h : bytes.length ≠ configLen) :
    decodeConfigShape bytes = none := by
  simp [decodeConfigShape, h]

/-- A wrong family marker is rejected, regardless of the salt or verifier. -/
theorem config_wrong_magic (bytes : List Nat) (h : bytes.take configFamilyLen ≠ configFamily) :
    decodeConfigShape bytes = none := by
  simp [decodeConfigShape, h]

/-- A profile byte that names no profile is rejected: no operation runs
    under an unknown profile, and none falls back to another. -/
theorem config_unknown_profile (bytes : List Nat) (h : profileOfByte (bytes.getD configFamilyLen 0) = none) :
    decodeConfigShape bytes = none := by
  unfold decodeConfigShape
  split
  · split
    · rw [h]
    · rfl
  · rfl

/-- A valid file header is reconstructed exactly, including an empty file
    represented by the mandatory authenticated tag. -/
theorem decode_file_header_encode (id encrypted : List Nat)
    (hi : id.length = idLen) (hbody : tagLen ≤ encrypted.length) :
    decodeFileHeaderShape (encodeFile id encrypted) = some id := by
  have hlen : fileMinLen ≤ (encodeFile id encrypted).length := by
    rw [file_length id encrypted hi]
    simp only [fileMinLen] at hbody ⊢
    omega
  have hp : (encodeFile id encrypted).take fileMagicLen = fileMagic := file_magic_prefix id encrypted
  have hd : (encodeFile id encrypted).drop fileMagicLen = id ++ encrypted := by
    change (fileMagic ++ (id ++ encrypted)).drop fileMagic.length = id ++ encrypted
    exact List.drop_append_length
  have htaken : (id ++ encrypted).take idLen = id := by
    simpa only [hi] using (List.take_append_length (l₁ := id) (l₂ := encrypted))
  simp [decodeFileHeaderShape, hlen, hp, hd, htaken]

/-- A file shorter than its authenticated minimum is rejected. -/
theorem file_truncated (bytes : List Nat) (h : bytes.length < fileMinLen) :
    decodeFileHeaderShape bytes = none := by
  have hn : ¬ fileMinLen ≤ bytes.length := Nat.not_le.mpr h
  simp [decodeFileHeaderShape, hn]

/-- No file record with an incorrect version header parses successfully. -/
theorem file_wrong_magic (bytes : List Nat) (h : bytes.take fileMagicLen ≠ fileMagic) :
    decodeFileHeaderShape bytes = none := by
  simp [decodeFileHeaderShape, h]

/-- An accepted file header is the magic and the id it returns, followed
    by the rest of the record (at least the tag). -/
theorem record_of_shape {l id : List Nat} (h : decodeFileHeaderShape l = some id) :
    l = fileMagic ++ id ++ l.drop fileHeaderLen ∧ fileMinLen ≤ l.length ∧ id.length = idLen := by
  unfold decodeFileHeaderShape at h
  split at h
  · split at h
    · rename_i hlen hmag
      cases h
      refine ⟨?_, hlen, by simp only [fileMinLen, fileHeaderLen] at hlen; simp; omega⟩
      conv => lhs; rw [← List.take_append_drop fileMagicLen l]
      rw [hmag, List.append_assoc]
      congr 1
      conv => lhs; rw [← List.take_append_drop idLen (l.drop fileMagicLen)]
      simp [List.drop_drop]
    · cases h
  · cases h

end Transcrypt.V3Wire

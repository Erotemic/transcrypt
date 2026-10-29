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

/-- Strict configuration decoder: no extra bytes, exact version and magic. -/
def decodeConfigShape (bytes : List Nat) : Option (List Nat × List Nat) :=
  if bytes.length = configLen then
    if bytes.take configMagicLen = configMagic then
      some ((bytes.drop configMagicLen).take saltLen, (bytes.drop configMagicLen).drop saltLen)
    else none
  else none

/-- A file header is valid only with room for the full SIV tag. -/
def decodeFileHeaderShape (bytes : List Nat) : Option (List Nat) :=
  if fileMinLen ≤ bytes.length then
    if bytes.take fileMagicLen = fileMagic then
      some ((bytes.drop fileMagicLen).take idLen)
    else none
  else none

/-- Exact configuration serialization is recovered by its independent parser. -/
theorem decode_config_encode (salt tag : List Nat)
    (hs : salt.length = saltLen) (ht : tag.length = tagLen) :
    decodeConfigShape (encodeConfig salt tag) = some (salt, tag) := by
  have hlen : (encodeConfig salt tag).length = configLen := config_length salt tag hs ht
  have hp : (encodeConfig salt tag).take configMagicLen = configMagic := config_magic_prefix salt tag
  have hd : (encodeConfig salt tag).drop configMagicLen = salt ++ tag := by
    change (configMagic ++ (salt ++ tag)).drop configMagic.length = salt ++ tag
    exact List.drop_append_length
  have htaken : (salt ++ tag).take saltLen = salt := by
    simpa only [hs] using (List.take_append_length (l₁ := salt) (l₂ := tag))
  have hdropped : (salt ++ tag).drop saltLen = tag := by
    simpa only [hs] using (List.drop_append_length (l₁ := salt) (l₂ := tag))
  simp [decodeConfigShape, hlen, hp, hd, htaken, hdropped]

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

/-- Missing or additional configuration bytes are never accepted. -/
theorem config_wrong_length (bytes : List Nat) (h : bytes.length ≠ configLen) :
    decodeConfigShape bytes = none := by
  simp [decodeConfigShape, h]

/-- Magic-version mismatch is rejected, regardless of the salt or verifier. -/
theorem config_wrong_magic (bytes : List Nat) (h : bytes.take configMagicLen ≠ configMagic) :
    decodeConfigShape bytes = none := by
  simp [decodeConfigShape, h]

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

import Transcrypt.V3Wire

/-
Independent executable *shape* decoder for the v3 committed wire protocol.
It is not an Aeneas translation. Its theorems specify the behaviors that
must subsequently be proved for Aeneas-generated Rust functions.
Ciphertext authentication remains outside the shape decoder.
-/

namespace Transcrypt.V3Wire

/-- Strict configuration decoder: no extra bytes, exact version and magic. -/
def decodeConfigShape (bytes : List Nat) : Option (List Nat × List Nat) :=
  if bytes.length = 55 then
    if bytes.take 7 = configMagic then
      some ((bytes.drop 7).take 32, (bytes.drop 7).drop 32)
    else none
  else none

/-- A file header is valid only with room for the full 16-byte SIV tag. -/
def decodeFileHeaderShape (bytes : List Nat) : Option (List Nat) :=
  if 38 ≤ bytes.length then
    if bytes.take 6 = fileMagic then
      some ((bytes.drop 6).take 16)
    else none
  else none

/-- Exact configuration serialization is recovered by its independent parser. -/
theorem decode_config_encode (salt tag : List Nat)
    (hs : salt.length = 32) (ht : tag.length = 16) :
    decodeConfigShape (encodeConfig salt tag) = some (salt, tag) := by
  have hlen : (encodeConfig salt tag).length = 55 := config_length salt tag hs ht
  have hp : (encodeConfig salt tag).take 7 = configMagic := config_magic_prefix salt tag
  have hd : (encodeConfig salt tag).drop 7 = salt ++ tag := by
    change (configMagic ++ (salt ++ tag)).drop configMagic.length = salt ++ tag
    exact List.drop_append_length
  have htaken : (salt ++ tag).take 32 = salt := by
    simpa only [hs] using (List.take_append_length (l₁ := salt) (l₂ := tag))
  have hdropped : (salt ++ tag).drop 32 = tag := by
    simpa only [hs] using (List.drop_append_length (l₁ := salt) (l₂ := tag))
  simp [decodeConfigShape, hlen, hp, hd, htaken, hdropped]

/-- A valid file header is reconstructed exactly, including an empty file
    represented by the mandatory 16-byte authenticated tag. -/
theorem decode_file_header_encode (id encrypted : List Nat)
    (hi : id.length = 16) (hbody : 16 ≤ encrypted.length) :
    decodeFileHeaderShape (encodeFile id encrypted) = some id := by
  have hlen : 38 ≤ (encodeFile id encrypted).length := by
    rw [file_length id encrypted hi]
    omega
  have hp : (encodeFile id encrypted).take 6 = fileMagic := file_magic_prefix id encrypted
  have hd : (encodeFile id encrypted).drop 6 = id ++ encrypted := by
    change (fileMagic ++ (id ++ encrypted)).drop fileMagic.length = id ++ encrypted
    exact List.drop_append_length
  have htaken : (id ++ encrypted).take 16 = id := by
    simpa only [hi] using (List.take_append_length (l₁ := id) (l₂ := encrypted))
  simp [decodeFileHeaderShape, hlen, hp, hd, htaken]

/-- Missing or additional configuration bytes are never accepted. -/
theorem config_wrong_length (bytes : List Nat) (h : bytes.length ≠ 55) :
    decodeConfigShape bytes = none := by
  simp [decodeConfigShape, h]

/-- Magic-version mismatch is rejected, regardless of the salt or verifier. -/
theorem config_wrong_magic (bytes : List Nat) (h : bytes.take 7 ≠ configMagic) :
    decodeConfigShape bytes = none := by
  simp [decodeConfigShape, h]

/-- A file shorter than its authenticated 38-byte minimum is rejected. -/
theorem file_truncated (bytes : List Nat) (h : bytes.length < 38) :
    decodeFileHeaderShape bytes = none := by
  have hn : ¬ 38 ≤ bytes.length := by omega
  simp [decodeFileHeaderShape, hn]

/-- No file record with an incorrect version header parses successfully. -/
theorem file_wrong_magic (bytes : List Nat) (h : bytes.take 6 ≠ fileMagic) :
    decodeFileHeaderShape bytes = none := by
  simp [decodeFileHeaderShape, h]

end Transcrypt.V3Wire

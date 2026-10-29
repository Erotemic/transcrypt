import Std

/-!
Independent abstract byte-wire specification of v3: the committed config
(`encodeConfig`) and record (`encodeFile`) layouts. Written from the protocol
spec, not from the Rust source. The refinement of the production encoders
and decoders to these definitions is proved in
`proofs/aeneas/v3/V3Wire/Verification/Codec.lean` (see
`proofs/aeneas/v3/PROOF-STATUS.md`).
-/

namespace Transcrypt.V3Wire

-- Rust adapters use UInt8; this abstract specification uses byte values as
-- natural numbers in [0,255], with framing constants all in this range.
def configMagic : List Nat := [84, 67, 70, 71, 51, 0, 1]
def fileMagic : List Nat := [84, 86, 51, 70, 0, 1]

/-! Field lengths, in bytes. They are reducible (definitional unfolding and
`decide`); `simp only [..]` or `unfold` exposes the numbers to `omega`. -/

/-- The config magic `TCFG3\0\x01` and the record magic `TV3F\0\x01`. -/
abbrev configMagicLen : Nat := 7
abbrev fileMagicLen : Nat := 6
/-- The Argon2id salt, the AES-SIV tag and the config identifier. -/
abbrev saltLen : Nat := 32
abbrev tagLen : Nat := 16
abbrev idLen : Nat := 16
/-- A config: magic, salt and tag. -/
abbrev configLen : Nat := configMagicLen + saltLen + tagLen
/-- A record header (magic and config id), and the shortest record (a
    header and the tag of an empty plaintext). -/
abbrev fileHeaderLen : Nat := fileMagicLen + idLen
abbrev fileMinLen : Nat := fileHeaderLen + tagLen

/-- Unfold the field lengths to their numbers everywhere, for `omega` (which
    treats a named constant as an unknown) and for matching against the
    production constants' numeric `_val` facts. -/
macro "unfold_v3_lengths" : tactic =>
  `(tactic| try simp only [Transcrypt.V3Wire.configMagicLen, Transcrypt.V3Wire.fileMagicLen,
    Transcrypt.V3Wire.saltLen, Transcrypt.V3Wire.tagLen, Transcrypt.V3Wire.idLen,
    Transcrypt.V3Wire.configLen, Transcrypt.V3Wire.fileHeaderLen, Transcrypt.V3Wire.fileMinLen] at *)

theorem configMagic_length : configMagic.length = configMagicLen := rfl
theorem fileMagic_length : fileMagic.length = fileMagicLen := rfl

def encodeConfig (salt tag : List Nat) : List Nat :=
  configMagic ++ salt ++ tag

def encodeFile (id authenticatedCiphertext : List Nat) : List Nat :=
  fileMagic ++ id ++ authenticatedCiphertext

-- Grammar predicates: authentication itself is intentionally an opaque
-- external cryptographic assumption, not a result of magic-byte checking.
def ValidConfigShape (bytes : List Nat) : Prop :=
  bytes.length = configLen ∧ bytes.take configMagicLen = configMagic

def ValidFileShape (bytes : List Nat) : Prop :=
  fileMinLen ≤ bytes.length ∧ bytes.take fileMagicLen = fileMagic

/-- Config and file records have disjoint leading magic bytes. -/
theorem magic_disjoint : configMagic ≠ fileMagic := by
  decide

/-- Serialized config has the required fixed length. -/
theorem config_length (salt tag : List Nat)
    (hs : salt.length = saltLen) (ht : tag.length = tagLen) :
    (encodeConfig salt tag).length = configLen := by
  simp only [encodeConfig, List.length_append, configMagic_length, hs, ht]

/-- Serialized record length is exactly its fixed overhead plus ciphertext. -/
theorem file_length (id encrypted : List Nat)
    (hi : id.length = idLen) :
    (encodeFile id encrypted).length = fileHeaderLen + encrypted.length := by
  simp only [encodeFile, List.length_append, fileMagic_length, hi]

/-- Construction places the config magic at the beginning, regardless of salt. -/
theorem config_magic_prefix (salt tag : List Nat) :
    (encodeConfig salt tag).take configMagicLen = configMagic := by
  simp [encodeConfig, configMagic]

/-- Construction places the file magic at the beginning, regardless of key or body. -/
theorem file_magic_prefix (id encrypted : List Nat) :
    (encodeFile id encrypted).take fileMagicLen = fileMagic := by
  simp [encodeFile, fileMagic]

end Transcrypt.V3Wire

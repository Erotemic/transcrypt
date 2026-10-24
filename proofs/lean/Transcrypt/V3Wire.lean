import Std

/-
Independent abstract byte-wire specification of the v3 proof-of-concept.
This file does NOT claim that Aeneas-translated Rust functions refine it.
The proof targets for the real Rust core are tracked in the v3 spec.
-/

namespace Transcrypt.V3Wire

-- Rust adapters use UInt8; this abstract specification uses byte values as
-- natural numbers in [0,255], with framing constants all in this range.
def configMagic : List Nat := [84, 67, 70, 71, 51, 0, 1]
def fileMagic : List Nat := [84, 86, 51, 70, 0, 1]

def encodeConfig (salt tag : List Nat) : List Nat :=
  configMagic ++ salt ++ tag

def encodeFile (id authenticatedCiphertext : List Nat) : List Nat :=
  fileMagic ++ id ++ authenticatedCiphertext

-- Grammar predicates: authentication itself is intentionally an opaque
-- external cryptographic assumption, not a result of magic-byte checking.
def ValidConfigShape (bytes : List Nat) : Prop :=
  bytes.length = 55 ∧ bytes.take 7 = configMagic

def ValidFileShape (bytes : List Nat) : Prop :=
  38 ≤ bytes.length ∧ bytes.take 6 = fileMagic

/-- Config and file records have disjoint leading magic bytes. -/
theorem magic_disjoint : configMagic ≠ fileMagic := by
  decide

/-- Serialized config has the required fixed length. -/
theorem config_length (salt tag : List Nat)
    (hs : salt.length = 32) (ht : tag.length = 16) :
    (encodeConfig salt tag).length = 55 := by
  simp [encodeConfig, configMagic, hs, ht]

/-- Serialized record length is exactly its fixed overhead plus ciphertext. -/
theorem file_length (id encrypted : List Nat)
    (hi : id.length = 16) :
    (encodeFile id encrypted).length = 22 + encrypted.length := by
  simp [encodeFile, fileMagic, hi]
  omega

/-- Construction places the config magic at the beginning, regardless of salt. -/
theorem config_magic_prefix (salt tag : List Nat) :
    (encodeConfig salt tag).take 7 = configMagic := by
  simp [encodeConfig, configMagic]

/-- Construction places the file magic at the beginning, regardless of key or body. -/
theorem file_magic_prefix (id encrypted : List Nat) :
    (encodeFile id encrypted).take 6 = fileMagic := by
  simp [encodeFile, fileMagic]

end Transcrypt.V3Wire

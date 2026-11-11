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

/-- A configuration profile: the key-derivation function (with fixed
    parameters, `Transcrypt.V3Profiles.profileKdf`) that turns the
    passphrase and salt into the AES-SIV key. Records are the same for
    every profile. -/
inductive Profile where
  | argon2id
  | scrypt
  | pbkdf2
  deriving DecidableEq, Repr

/-- The byte after the configuration family marker. -/
def profileByte : Profile → Nat
  | .argon2id => 1
  | .scrypt => 2
  | .pbkdf2 => 3

/-- The profile a byte names, if any. -/
def profileOfByte (b : Nat) : Option Profile :=
  if b = 1 then some .argon2id
  else if b = 2 then some .scrypt
  else if b = 3 then some .pbkdf2
  else none

theorem profileOfByte_profileByte (p : Profile) : profileOfByte (profileByte p) = some p := by
  cases p <;> rfl

theorem profileByte_of_profileOfByte {b : Nat} {p : Profile} (h : profileOfByte b = some p) :
    profileByte p = b := by
  unfold profileOfByte at h
  split at h
  · cases h; simp_all [profileByte]
  · split at h
    · cases h; simp_all [profileByte]
    · split at h
      · cases h; simp_all [profileByte]
      · cases h

theorem profileByte_injective : Function.Injective profileByte := by
  intro p q h
  have := profileOfByte_profileByte p
  rw [h, profileOfByte_profileByte] at this
  exact (Option.some.inj this).symm

/-- The family marker `TCFG3\0` shared by every configuration. -/
def configFamily : List Nat := [84, 67, 70, 71, 51, 0]
/-- A profile's configuration magic: the family marker and its profile
    byte. Profile 1's is the original `TCFG3\0\x01`. -/
def configMagic (p : Profile) : List Nat := configFamily ++ [profileByte p]
def fileMagic : List Nat := [84, 86, 51, 70, 0, 1]

theorem configMagic_argon2id : configMagic .argon2id = [84, 67, 70, 71, 51, 0, 1] := rfl

/-! Field lengths, in bytes. They are reducible (definitional unfolding and
`decide`); `simp only [..]` or `unfold` exposes the numbers to `omega`.
The refinement proofs' tactic for that, `unfold_v3_bytes`, lives in the
verification layer (`V3Wire/Verification/Tactics.lean`), not here. -/

/-- The config family `TCFG3\0`, the config magic (family and profile
    byte) and the record magic `TV3F\0\x01`. -/
abbrev configFamilyLen : Nat := 6
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

theorem configFamily_length : configFamily.length = configFamilyLen := rfl
theorem configMagic_length (p : Profile) : (configMagic p).length = configMagicLen := rfl
theorem fileMagic_length : fileMagic.length = fileMagicLen := rfl

def encodeConfig (p : Profile) (salt tag : List Nat) : List Nat :=
  configMagic p ++ salt ++ tag

def encodeFile (id authenticatedCiphertext : List Nat) : List Nat :=
  fileMagic ++ id ++ authenticatedCiphertext

-- Grammar predicates: authentication itself is intentionally an opaque
-- external cryptographic assumption, not a result of magic-byte checking.
def ValidConfigShape (bytes : List Nat) : Prop :=
  bytes.length = configLen ∧ ∃ p, bytes.take configMagicLen = configMagic p

def ValidFileShape (bytes : List Nat) : Prop :=
  fileMinLen ≤ bytes.length ∧ bytes.take fileMagicLen = fileMagic

/-- Config and file records have disjoint leading magic bytes. -/
theorem magic_disjoint (p : Profile) : configMagic p ≠ fileMagic := by
  cases p <;> decide

/-- Distinct profiles have distinct configuration magic. -/
theorem configMagic_injective : Function.Injective configMagic := by
  intro p q h
  apply profileByte_injective
  have := congrArg (fun l => l.getD configFamilyLen 0) h
  simpa [configMagic, configFamily] using this

/-- Serialized config has the required fixed length. -/
theorem config_length (p : Profile) (salt tag : List Nat)
    (hs : salt.length = saltLen) (ht : tag.length = tagLen) :
    (encodeConfig p salt tag).length = configLen := by
  simp only [encodeConfig, List.length_append, configMagic_length, hs, ht]

/-- Serialized record length is exactly its fixed overhead plus ciphertext. -/
theorem file_length (id encrypted : List Nat)
    (hi : id.length = idLen) :
    (encodeFile id encrypted).length = fileHeaderLen + encrypted.length := by
  simp only [encodeFile, List.length_append, fileMagic_length, hi]

/-- Construction places the profile's config magic at the beginning,
    regardless of salt. -/
theorem config_magic_prefix (p : Profile) (salt tag : List Nat) :
    (encodeConfig p salt tag).take configMagicLen = configMagic p := by
  simp [encodeConfig, configMagic, configFamily]

/-- Construction places the file magic at the beginning, regardless of key or body. -/
theorem file_magic_prefix (id encrypted : List Nat) :
    (encodeFile id encrypted).take fileMagicLen = fileMagic := by
  simp [encodeFile, fileMagic]

end Transcrypt.V3Wire

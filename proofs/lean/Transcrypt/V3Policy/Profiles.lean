import Transcrypt.V3Policy.Authentication

/-!
# Profiles: the key derivation a configuration selects

Written from `docs/verification/specs/V3-PORTABLE-PROFILES.md`. A
configuration's profile byte names one key-derivation function with fixed
parameters (`profileKdf`); records are the same AES-SIV records for every
profile. Key derivation itself is abstract (`KeyDerivation`): its output for
a function, passphrase and salt. That a passphrase-derived key resists
guessing is the cryptographic assumption on the named function (A-KDF), not
a theorem.

The facts proved here are about *selection*: the committed configuration
alone determines which function and parameters are used, unknown profiles
are refused before any derivation, and an authenticated configuration binds
its profile byte (relabelling it requires an AES-SIV collision).
-/

namespace Transcrypt.V3Policy

open Transcrypt.V3Wire

/-- A key-derivation function with all of its parameters. Every function
    outputs a 64-byte key from the passphrase and the 32-byte salt. -/
inductive Kdf where
  /-- Argon2id version 0x13, memory in KiB. -/
  | argon2id (memoryKiB passes lanes : Nat)
  /-- scrypt with N = 2^logN. -/
  | scrypt (logN r p : Nat)
  /-- PBKDF2 with HMAC-SHA256. -/
  | pbkdf2Sha256 (rounds : Nat)
  deriving DecidableEq, Repr

/-- The profile table: profile 1 is Argon2id (m = 64 MiB, t = 3, p = 1),
    profile 2 scrypt (N = 2^15, r = 8, p = 1), profile 3 PBKDF2-HMAC-SHA256
    with 600 000 iterations. -/
def profileKdf : Profile → Kdf
  | .argon2id => .argon2id 65536 3 1
  | .scrypt => .scrypt 15 8 1
  | .pbkdf2 => .pbkdf2Sha256 600000

/-- Each profile has its own function: no two profiles share a derivation. -/
theorem profileKdf_injective : Function.Injective profileKdf := by
  intro p q h
  cases p <;> cases q <;> simp_all [profileKdf]

/-- scrypt's working memory, `128 r N` bytes: 32 MiB for profile 2. -/
def scryptMemory (logN r : Nat) : Nat := 128 * r * 2 ^ logN

theorem scrypt_profile_memory : scryptMemory 15 8 = 32 * 1024 * 1024 := by decide

/-- The longest passphrase any profile accepts. -/
def maxPassphrase : Nat := 4096

/-- Whether profile `p` accepts passphrase `pw`: one to `maxPassphrase`
    bytes, and for the portable profiles no NUL byte (a shell cannot carry
    one). Profile 1 keeps its original rule. -/
def passphraseOk (p : Profile) (pw : List Nat) : Bool :=
  decide (0 < pw.length) && decide (pw.length ≤ maxPassphrase) &&
    (match p with
     | .argon2id => true
     | .scrypt | .pbkdf2 => !pw.contains 0)

/-- The abstract key-derivation functions: `derive kdf pw salt` is the key
    `kdf` gives for passphrase `pw` and salt `salt`. -/
structure KeyDerivation where
  derive : Kdf → List Nat → List Nat → List Nat

/-- The key a passphrase gives under profile `p` and salt `salt`: the
    profile's own function, nothing else. -/
def profileKey (D : KeyDerivation) (p : Profile) (pw salt : List Nat) : List Nat :=
  D.derive (profileKdf p) pw salt

/-- The derivation a passphrase gets for a committed configuration: decided
    by the configuration's own profile byte and salt; `none` for a
    configuration that does not decode (in particular one of an unknown
    profile) or a passphrase the profile refuses. -/
def configKey (D : KeyDerivation) (config pw : List Nat) : Option (Profile × List Nat) :=
  match decodeConfigShape config with
  | some (p, salt, _) => if passphraseOk p pw then some (p, profileKey D p pw salt) else none
  | none => none

/-- The derivation of a configuration is exactly its profile's function,
    applied to its own salt: whatever profile a configuration names, no other
    function, parameter set or salt is used. -/
theorem configKey_uses_its_profile {D : KeyDerivation} {config pw key : List Nat} {p : Profile}
    (h : configKey D config pw = some (p, key)) :
    ∃ salt tag, config = encodeConfig p salt tag ∧ salt.length = saltLen ∧
      key = D.derive (profileKdf p) pw salt ∧ passphraseOk p pw = true := by
  unfold configKey at h
  split at h
  · rename_i q salt tag hd
    split at h
    · rename_i hok
      cases h
      obtain ⟨he, hs, _⟩ := encode_of_decodeConfigShape hd
      exact ⟨salt, tag, he, hs, rfl, hok⟩
    · cases h
  · cases h

/-- A configuration of an unknown profile gets no derivation at all. -/
theorem configKey_unknown_profile (D : KeyDerivation) (config pw : List Nat)
    (h : profileOfByte (config.getD configFamilyLen 0) = none) :
    configKey D config pw = none := by
  simp [configKey, config_unknown_profile config h]

/-- Two colliding AES-SIV tags of the empty plaintext under different
    associated data: what forging a relabelled configuration requires. -/
def ConfigTagCollision (s : Suite) : Prop :=
  ∃ ad ad', ad ≠ ad' ∧ s.siv ad [] = s.siv ad' []

/-- An authenticated configuration binds its profile byte: if the same salt
    and tag authenticated under two different profiles with one key, the
    key's AES-SIV would map two distinct associated-data lists to one tag.
    Under AES-SIV's pseudorandomness (A10) this happens with negligible
    probability, so relabelling a configuration's profile is detected, and
    with it any attempt to make a passphrase run under a weaker derivation. -/
theorem config_profile_bound {s : Suite} {p q : Profile} {salt tag : List Nat}
    (hs : salt.length = saltLen) (ht : tag.length = tagLen)
    (hp : ConfigAuthentic s (encodeConfig p salt tag))
    (hq : ConfigAuthentic s (encodeConfig q salt tag)) (hne : p ≠ q) :
    ConfigTagCollision s := by
  obtain ⟨p', salt₁, tag₁, hd₁, h₁⟩ := hp
  obtain ⟨q', salt₂, tag₂, hd₂, h₂⟩ := hq
  rw [decode_config_encode p salt tag hs ht] at hd₁
  rw [decode_config_encode q salt tag hs ht] at hd₂
  cases hd₁; cases hd₂
  refine ⟨[configDomain, configMagic p ++ salt], [configDomain, configMagic q ++ salt], ?_, ?_⟩
  · intro h
    apply hne
    have h' := List.cons.inj h |>.2
    have hm : configMagic p ++ salt = configMagic q ++ salt := List.cons.inj h' |>.1
    exact configMagic_injective (List.append_cancel_right hm)
  · rw [h₁, h₂]

end Transcrypt.V3Policy

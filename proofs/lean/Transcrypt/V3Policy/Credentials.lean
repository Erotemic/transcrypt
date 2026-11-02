import Transcrypt.V3Policy.Authentication

/-!
# Credentials: the agent's requests and the stored key

Which credential-agent requests are authorized, the agent's request framing
(local IPC), and when a stored key is used.
-/

namespace Transcrypt.V3Policy

open Transcrypt.V3Wire

/-! ## Credential agent requests -/

inductive AgentOp | ping | encrypt | decrypt | stop
  deriving DecidableEq

open Classical in
/-- Opcode bytes `P`, `E`, `D`, `X`. -/
noncomputable def authorizeSpec (opcode : Nat) (supplied active path : List Nat) (bodyLen : Nat) :
    Option AgentOp :=
  if path.length > maxPath ∨ bodyLen > maxRecord ∨ supplied ≠ active then none
  else if opcode = opEncrypt ∨ opcode = opDecrypt then
    if CanonicalProtectedPath path then some (if opcode = opEncrypt then .encrypt else .decrypt)
    else none
  else if path ≠ [] ∨ bodyLen ≠ 0 then none
  else if opcode = opPing then some .ping
  else if opcode = opStop then some .stop
  else none

/-! ## Credential-agent framing (local IPC) -/

/-- Big-endian 4-byte encoding of a natural number below 2^32. -/
def be32 (n : Nat) : List Nat := [n / 2^24 % 256, n / 2^16 % 256, n / 2^8 % 256, n % 256]

/-- Request header: opcode, the 55-byte public config, path length. -/
def frameHeader (opcode : Nat) (config : List Nat) (pathLen : Nat) : List Nat :=
  [opcode] ++ config ++ be32 pathLen

theorem be32_length (n : Nat) : (be32 n).length = be32Len := rfl

/-- Decoding big-endian bytes inverts `be32` below 2^32. -/
theorem be32_decode (n : Nat) (h : n < 2^32) :
    (n / 2^24 % 256) * 2^24 + (n / 2^16 % 256) * 2^16 + (n / 2^8 % 256) * 2^8 + n % 256 = n := by
  omega

/-- `be32` is injective below 2^32. -/
theorem be32_injective {m n : Nat} (hm : m < 2^32) (hn : n < 2^32) (h : be32 m = be32 n) : m = n := by
  simp only [be32, List.cons.injEq, and_true] at h
  obtain ⟨h24, h16, h8, h0⟩ := h
  rw [← be32_decode m hm, ← be32_decode n hn, h24, h16, h8, h0]

/-! ## The stored key -/

inductive StoredKey | absent | damaged | stale | unlocked
  deriving DecidableEq

/-- The associated-data path and the plaintext of a stored key's check
    value. The path is reserved metadata, so no record is ever sealed or
    opened at it (`keyCheckPath_reserved`). -/
def keyCheckPath : List Nat := ascii ".transcrypt/key-check"
def keyCheckPlaintext : List Nat := ascii "transcrypt/v3/key-check"

/-- The check value of the key of suite `s`, stored with `config`: the
    sealing of `keyCheckPlaintext` at `keyCheckPath` under `config`. Unlike
    the configuration tag (the encryption of the empty plaintext) its
    plaintext is not empty, so with AES-SIV it involves both halves of the
    key; that a different key gives a different value is the cipher's
    property (A10), not this specification's. -/
def keyCheckValue (s : Suite) (config : List Nat) : List Nat :=
  s.siv [fileDomain, config, keyCheckPath] keyCheckPlaintext

/-- The key bytes and the check value of a stored key file, after its
    `configLen`-byte configuration. -/
def storedKeyBytes (file : List Nat) : List Nat := (file.drop configLen).take keyLen
def storedKeyCheck (file : List Nat) : List Nat := file.drop keyCheckStart

/-- A stored key file is authentic for suite `s` (that of its key bytes)
    when its configuration authenticates under `s` and its check value is
    the one `s` gives that configuration. This is what `storedKeySpec`'s
    `authentic` means. -/
def StoredKeyAuthentic (s : Suite) (file : List Nat) : Prop :=
  ConfigAuthentic s (file.take configLen) ∧ storedKeyCheck file = keyCheckValue s (file.take configLen)

theorem keyCheckPlaintext_length : keyCheckPlaintext.length = keyCheckPlaintextLen := by decide

theorem keyCheckValue_length (s : Suite) (config : List Nat) :
    (keyCheckValue s config).length = keyCheckLen := by
  rw [keyCheckValue, s.siv_length, keyCheckPlaintext_length, keyCheckLen, Nat.add_comm]

/-- The check value's path is reserved, so it is no protected path: no
    record is sealed or opened with the check value's associated data. -/
theorem keyCheckPath_reserved : Reserved keyCheckPath ∧ ¬ CanonicalProtectedPath keyCheckPath :=
  have h : Reserved keyCheckPath := Or.inl ⟨ascii "key-check", by decide⟩
  ⟨h, fun hc => hc.2.2.2.2 h⟩

/-- The stored key file of an unlocked checkout holds the public
    configuration it was unlocked for, the key, and the key's check value
    (`keyFileLen` bytes). A key-sized file (the key alone, from an earlier
    version) or no file at all means no stored key; any other length is
    damaged, including the earlier layout without a check value
    (`keyCheckStart` bytes). A key is used only for exactly the
    configuration stored with it, and only if it authenticates that
    configuration and its check value (`authentic`, which is
    `StoredKeyAuthentic` of the key's suite); otherwise it is stale. -/
def storedKeySpec (present : Bool) (file current : List Nat) (authentic : Bool) : StoredKey :=
  if present = false ∨ file.length = keyLen then .absent
  else if file.length ≠ keyFileLen then .damaged
  else if file.take configLen = current ∧ authentic = true then .unlocked
  else .stale

/-- A stored key is used only for the configuration it was stored with,
    and only after it authenticates it. -/
theorem storedKeySpec_unlocked {present : Bool} {file current : List Nat} {authentic : Bool}
    (h : storedKeySpec present file current authentic = .unlocked) :
    present = true ∧ file.length = keyFileLen ∧ file.take configLen = current ∧ authentic = true := by
  unfold storedKeySpec at h
  -- No file or a bare key is `.absent`, another length `.damaged`; of a
  -- file of the right length only the matching, authentic one is unlocked.
  by_cases habsent : present = false ∨ file.length = keyLen
  · rw [if_pos habsent] at h; cases h
  rw [if_neg habsent] at h
  by_cases hdamaged : file.length ≠ keyFileLen
  · rw [if_pos hdamaged] at h; cases h
  rw [if_neg hdamaged] at h
  by_cases hmatch : file.take configLen = current ∧ authentic = true
  · have hpresent : present = true := by
      cases present
      · exact absurd (Or.inl rfl) habsent
      · rfl
    exact ⟨hpresent, Decidable.of_not_not hdamaged, hmatch.1, hmatch.2⟩
  · rw [if_neg hmatch] at h; cases h

end Transcrypt.V3Policy

import Transcrypt.V3Policy.Paths

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

/-- The stored key file of an unlocked checkout holds the public
    configuration it was unlocked for, then the key. A key-sized file
    (the key alone, from an earlier version) or no file at all means no
    stored key; any other length is damaged. A key is used only for exactly
    the configuration stored with it, and only if it authenticates that
    configuration (`authentic`); otherwise it is stale. -/
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

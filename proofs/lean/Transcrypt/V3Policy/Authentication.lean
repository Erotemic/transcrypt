import Transcrypt.V3Policy.Paths

/-!
# Authentication: the abstract suite, sealing and opening records

The abstract cryptographic `Suite`, when a config authenticates, the record
`clean` produces (`sealedRecord`), when a record opens to a plaintext
(`OpensTo`), and the keyless envelope check (`EnvelopeOk`).
-/

namespace Transcrypt.V3Policy

open Transcrypt.V3Wire

def configDomain : List Nat := ascii "transcrypt/v3/config"
def fileDomain : List Nat := ascii "transcrypt/v3/file"

/-! ## Abstract cryptographic suite -/

structure Suite where
  /-- Deterministic AES-SIV(K) output (tag ++ ciphertext) for ordered AD. -/
  siv : List (List Nat) → List Nat → List Nat
  /-- SHA-256(x)[0:16]. -/
  digest16 : List Nat → List Nat
  siv_length : ∀ ad pt, (siv ad pt).length = pt.length + tagLen
  /-- Decryption is a function of the ciphertext: SIV is injective per AD. -/
  siv_injective : ∀ ad pt pt', siv ad pt = siv ad pt' → pt = pt'
  digest16_length : ∀ x, (digest16 x).length = idLen

/-- The committed config authenticates under the suite's key: its tag is the
    AES-SIV encryption of the empty plaintext under `[configDomain, prefix]`. -/
def ConfigAuthentic (s : Suite) (config : List Nat) : Prop :=
  ∃ salt tag, decodeConfigShape config = some (salt, tag) ∧
    s.siv [configDomain, configMagic ++ salt] [] = tag

/-- The record that `clean` must produce. -/
def sealedRecord (s : Suite) (config path pt : List Nat) : List Nat :=
  encodeFile (s.digest16 config) (s.siv [fileDomain, config, path] pt)

/-- Preconditions under which `clean` may seal: canonical path, authentic
    config, size bound, and the input is not itself a v3 record. -/
def MaySeal (s : Suite) (config path pt : List Nat) : Prop :=
  CanonicalProtectedPath path ∧ ConfigAuthentic s config ∧ pt.length ≤ maxFile ∧
    decodeFileHeaderShape pt = none

/-- `record` authentically opens to `pt` at `path` under `config`. -/
def OpensTo (s : Suite) (config path record pt : List Nat) : Prop :=
  CanonicalProtectedPath path ∧ ConfigAuthentic s config ∧ record.length ≤ maxRecord ∧
    record = sealedRecord s config path pt

/-- At most one plaintext is released for a given record, config and path. -/
theorem opensTo_unique (s : Suite) {config path record pt pt' : List Nat}
    (h : OpensTo s config path record pt) (h' : OpensTo s config path record pt') :
    pt = pt' := by
  obtain ⟨-, -, -, hrec⟩ := h
  obtain ⟨-, -, -, hrec'⟩ := h'
  have heq : sealedRecord s config path pt = sealedRecord s config path pt' := by
    rw [← hrec, ← hrec']
  simp only [sealedRecord, encodeFile, List.append_assoc, List.append_cancel_left_eq] at heq
  exact s.siv_injective _ _ _ heq

/-- A sealed record is its plaintext plus the fixed overhead. -/
theorem sealed_length (s : Suite) (config path pt : List Nat) :
    (sealedRecord s config path pt).length = pt.length + fileMinLen := by
  simp only [sealedRecord, encodeFile, List.length_append, fileMagic_length, s.digest16_length,
    s.siv_length, fileMinLen, fileHeaderLen]
  omega

/-- A sealed record has the file header naming its configuration's id. -/
theorem sealed_shape (s : Suite) (config path pt : List Nat) :
    decodeFileHeaderShape (sealedRecord s config path pt) = some (s.digest16 config) :=
  decode_file_header_encode _ _ (s.digest16_length _) (by rw [s.siv_length]; omega)

/-- Sealing then opening at the same config and path releases the plaintext. -/
theorem seal_opens (s : Suite) {config path pt : List Nat}
    (h : MaySeal s config path pt) :
    OpensTo s config path (sealedRecord s config path pt) pt := by
  obtain ⟨hpath, hconfig, hsize, -⟩ := h
  refine ⟨hpath, hconfig, ?_, rfl⟩
  rw [sealed_length]
  simp only [maxRecord]
  omega

/-- The keyless check of a committed record: within the size bound, with the
    v3 file header naming configuration id `id`. It cannot establish
    authenticity, which needs the key. -/
def EnvelopeOk (record id : List Nat) : Prop :=
  record.length ≤ maxRecord ∧ decodeFileHeaderShape record = some id

/-- Every genuine record passes the keyless check for its configuration,
    so the check never rejects legitimate history. -/
theorem opensTo_envelopeOk (s : Suite) {config path record pt : List Nat}
    (h : OpensTo s config path record pt) : EnvelopeOk record (s.digest16 config) := by
  obtain ⟨_, _, hlen, rfl⟩ := h
  exact ⟨hlen, sealed_shape s _ _ _⟩

end Transcrypt.V3Policy

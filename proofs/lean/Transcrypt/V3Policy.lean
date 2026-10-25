import Transcrypt.V3WireCodec

/-
Independent specification of the v3 protocol *decisions* (path policy, Git
attribute check, record sealing/opening, lifecycle actions, agent requests).
Written from `docs/verification/specs/V3-AUTHENTICATED-P0.md`, not from the
Rust source. Aeneas refinement theorems in `proofs/aeneas/v3` relate the
production Rust core to these definitions.

Cryptography is abstract. `Suite` models one derived key: `siv ad pt` is the
deterministic AES-SIV output (16-byte tag then ciphertext) for the ordered
associated-data list `ad`, and `digest16` is SHA-256 truncated to 16 bytes.
The only algebraic facts assumed are functional ones that hold for every
deterministic SIV construction (length and injectivity for fixed `ad`).
Unforgeability -- that only a key holder can produce `siv ad pt` -- is the
*computational* assumption under which the theorems below have security
meaning; it is not, and cannot be, a Lean theorem here.
-/

namespace Transcrypt.V3Policy

open Transcrypt.V3Wire

def ascii (s : String) : List Nat := s.toList.map Char.toNat

/-! ## Constants -/

def maxFile : Nat := 16 * 1024 * 1024
def maxPath : Nat := 4096
def maxRecord : Nat := maxFile + 38
def slash : Nat := 47
def dot : Nat := 46
def protectedSuffix : List Nat := ascii ".secret"
def configDomain : List Nat := ascii "transcrypt/v3/config"
def fileDomain : List Nat := ascii "transcrypt/v3/file"
/-- What Git's `check-attr -z` prints after a path whose `filter` is ours. -/
def filterAttrSuffix : List Nat := [0] ++ ascii "filter" ++ [0] ++ ascii "transcrypt-v3" ++ [0]

/-! ## Path policy -/

/-- Protected Git paths are those whose name ends in `.secret`. -/
def Protected (path : List Nat) : Prop := protectedSuffix <:+ path

/-- A component is acceptable iff nonempty and neither `.` nor `..`. -/
def ComponentOk (c : List Nat) : Prop := c ≠ [] ∧ c ≠ [dot] ∧ c ≠ [dot, dot]

/-- The canonical authenticated-path policy of the v3 spec: nonempty, at most
    4096 bytes, no NUL, every `/`-separated component acceptable (which
    excludes absolute paths and empty, `.` and `..` components), protected. -/
def CanonicalProtectedPath (path : List Nat) : Prop :=
  path ≠ [] ∧ path.length ≤ maxPath ∧ 0 ∉ path ∧
  (∀ c ∈ path.splitOn slash, ComponentOk c) ∧ Protected path

/-! ## Effective Git filter attribute -/

/-- The exact `check-attr -z` response expected for a request: every NUL
    terminating a requested path becomes `NUL filter NUL transcrypt-v3 NUL`. -/
def expectedAttrResponse (request : List Nat) : List Nat :=
  request.flatMap (fun b => if b = 0 then filterAttrSuffix else [b])

/-- The request the adapter sends for a list of NUL-free paths. -/
def attrRequest (paths : List (List Nat)) : List Nat := paths.flatMap (· ++ [0])

theorem expand_nul_free (p : List Nat) (hp : 0 ∉ p) :
    p.flatMap (fun b => if b = 0 then filterAttrSuffix else [b]) = p := by
  induction p with
  | nil => rfl
  | cons b bs ih =>
    have hb : b ≠ 0 := fun hb => hp (hb ▸ List.mem_cons_self ..)
    have hbs : 0 ∉ bs := fun hm => hp (List.mem_cons_of_mem _ hm)
    simp [hb, ih hbs]

/-- For NUL-free paths the expected response reports, for every path in
    order, `path NUL filter NUL transcrypt-v3 NUL` and nothing else. -/
theorem expectedAttrResponse_paths (paths : List (List Nat))
    (h : ∀ p ∈ paths, 0 ∉ p) :
    expectedAttrResponse (attrRequest paths) = paths.flatMap (· ++ filterAttrSuffix) := by
  induction paths with
  | nil => rfl
  | cons p ps ih =>
    have hp : 0 ∉ p := h p (List.mem_cons_self ..)
    have hps : ∀ q ∈ ps, 0 ∉ q := fun q hq => h q (List.mem_cons_of_mem _ hq)
    have ih' := ih hps
    simp only [expectedAttrResponse, attrRequest] at ih' ⊢
    simp only [List.flatMap_cons, List.flatMap_append, expand_nul_free p hp, ih']
    simp

/-! ## Abstract cryptographic suite -/

structure Suite where
  /-- Deterministic AES-SIV(K) output (tag ++ ciphertext) for ordered AD. -/
  siv : List (List Nat) → List Nat → List Nat
  /-- SHA-256(x)[0:16]. -/
  digest16 : List Nat → List Nat
  siv_length : ∀ ad pt, (siv ad pt).length = pt.length + 16
  /-- Decryption is a function of the ciphertext: SIV is injective per AD. -/
  siv_injective : ∀ ad pt pt', siv ad pt = siv ad pt' → pt = pt'
  digest16_length : ∀ x, (digest16 x).length = 16

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
  have heq : sealedRecord s config path pt = sealedRecord s config path pt' := by
    rw [← h.2.2.2, ← h'.2.2.2]
  simp only [sealedRecord, encodeFile, List.append_assoc, List.append_cancel_left_eq] at heq
  exact s.siv_injective _ _ _ heq

/-- Sealing then opening at the same config and path releases the plaintext. -/
theorem seal_opens (s : Suite) {config path pt : List Nat}
    (h : MaySeal s config path pt) :
    OpensTo s config path (sealedRecord s config path pt) pt := by
  refine ⟨h.1, h.2.1, ?_, rfl⟩
  have := file_length (s.digest16 config) (s.siv [fileDomain, config, path] pt)
    (s.digest16_length _)
  simp only [sealedRecord, this, s.siv_length]
  have := h.2.2.1
  simp only [maxRecord]
  omega

/-! ## Lifecycle decisions -/

inductive HydrateAction | publish | keep
  deriving DecidableEq

/-- Hydration may replace the worktree only when it is exactly the staged
    record; it leaves exactly-authenticated plaintext alone; anything else is
    possibly the user's only copy of new data and is refused. -/
def hydrateSpec (worktree record plaintext : List Nat) : Option HydrateAction :=
  if worktree = record then some .publish
  else if worktree = plaintext then some .keep
  else none

inductive LockAction | keep | flush
  deriving DecidableEq

/-- Lock may replace the worktree by the staged record only when the
    worktree already is that record, or reseals to exactly that record. -/
def lockSpec (worktree record resealed : List Nat) : Option LockAction :=
  if worktree = record then some .keep
  else if resealed = record then some .flush
  else none

/-- Lock never loses data: if it flushes, the worktree plaintext is exactly
    what the staged record authentically opens to. -/
theorem lock_flush_recoverable (s : Suite) {config path worktree record : List Nat}
    (hseal : MaySeal s config path worktree)
    (hflush : lockSpec worktree record (sealedRecord s config path worktree) = some .flush) :
    OpensTo s config path record worktree := by
  unfold lockSpec at hflush
  split at hflush
  · cases hflush
  · split at hflush
    · rename_i h
      rw [← h]
      exact seal_opens s hseal
    · cases hflush

/-! ## Credential agent requests -/

inductive AgentOp | ping | encrypt | decrypt | stop
  deriving DecidableEq

open Classical in
/-- Opcode bytes `P`, `E`, `D`, `X`. -/
noncomputable def authorizeSpec (opcode : Nat) (supplied active path : List Nat) (bodyLen : Nat) :
    Option AgentOp :=
  if path.length > maxPath ∨ bodyLen > maxRecord ∨ supplied ≠ active then none
  else if opcode = 69 ∨ opcode = 68 then
    if CanonicalProtectedPath path then some (if opcode = 69 then .encrypt else .decrypt)
    else none
  else if path ≠ [] ∨ bodyLen ≠ 0 then none
  else if opcode = 80 then some .ping
  else if opcode = 88 then some .stop
  else none

end Transcrypt.V3Policy

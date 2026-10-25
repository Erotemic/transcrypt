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

/-! ## Git index records -/

/-- Git mode of a regular, non-executable file. -/
def regularMode : List Nat := ascii "100644"

/-- A stage-0 `git ls-files --stage -z` record `mode SP oid SP 0 TAB path`.
    Modes and object ids never contain TAB, so the path (which becomes
    AES-SIV associated data) is exactly what follows the first TAB; paths
    themselves may contain TAB. -/
def IndexRecord (entry : List Nat) (regular : Bool) (path : List Nat) : Prop :=
  ∃ mode oid, entry = mode ++ [32] ++ oid ++ [32, 48, 9] ++ path ∧
    mode.length = 6 ∧ oid ≠ [] ∧ 9 ∉ mode ∧ 9 ∉ oid ∧ path ≠ [] ∧
    (regular = true ↔ mode = regularMode)

/-- The adapter takes the object id of an accepted record as the bytes from
    offset 7 up to 3 bytes before the path, i.e. `entry[7..path_start-3]`.
    For every record of the spec's shape that is exactly its object id. -/
theorem indexRecord_oid {entry : List Nat} {regular : Bool} {path : List Nat}
    (h : IndexRecord entry regular path) :
    ∃ mode oid, entry = mode ++ [32] ++ oid ++ [32, 48, 9] ++ path ∧
      ((entry.take (entry.length - path.length - 3)).drop 7) = oid := by
  obtain ⟨mode, oid, rfl, hm, _⟩ := h
  refine ⟨mode, oid, rfl, ?_⟩
  have hlen : (mode ++ [32] ++ oid ++ [32, 48, 9] ++ path).length - path.length - 3 =
      (mode ++ [32] ++ oid).length := by simp; omega
  rw [hlen, show mode ++ [32] ++ oid ++ [32, 48, 9] ++ path =
      (mode ++ [32] ++ oid) ++ ([32, 48, 9] ++ path) by simp, List.take_left]
  rw [show mode ++ [32] ++ oid = (mode ++ [32]) ++ oid by simp]
  exact List.drop_left' (by simp [hm])

/-! ## Credential-agent framing (local IPC) -/

/-- Big-endian 4-byte encoding of a natural number below 2^32. -/
def be32 (n : Nat) : List Nat := [n / 2^24 % 256, n / 2^16 % 256, n / 2^8 % 256, n % 256]

/-- Request header: opcode, the 55-byte public config, path length. -/
def frameHeader (opcode : Nat) (config : List Nat) (pathLen : Nat) : List Nat :=
  [opcode] ++ config ++ be32 pathLen

theorem be32_length (n : Nat) : (be32 n).length = 4 := rfl

/-- Decoding big-endian bytes inverts `be32` below 2^32. -/
theorem be32_decode (n : Nat) (h : n < 2^32) :
    (n / 2^24 % 256) * 2^24 + (n / 2^16 % 256) * 2^16 + (n / 2^8 % 256) * 2^8 + n % 256 = n := by
  omega

/-! ## Git object names and keyless record envelopes -/

/-- A lowercase hexadecimal digit. -/
def HexDigit (c : Nat) : Prop := (48 ≤ c ∧ c ≤ 57) ∨ (97 ≤ c ∧ c ≤ 102)

/-- A Git object name as `ls-files --stage` and `ls-tree` print it: 40
    (SHA-1) or 64 (SHA-256) lowercase hexadecimal digits. The adapter reads
    Git content only through such names. -/
def ObjectId (oid : List Nat) : Prop :=
  (oid.length = 40 ∨ oid.length = 64) ∧ ∀ c ∈ oid, HexDigit c

/-- An object name is neither revision syntax (no `:`, `^`, `~`, `@`, `{`)
    nor an option (it does not start with `-`). -/
theorem objectId_plain {oid : List Nat} (h : ObjectId oid) :
    ∀ c ∈ oid, c ∉ [58, 94, 126, 64, 123, 45] := by
  intro c hc hbad
  rcases h.2 c hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp at hbad <;> omega

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
  refine ⟨hlen, ?_⟩
  exact decode_file_header_encode _ _ (s.digest16_length config) (by simp [s.siv_length])

/-! ## Git long-running filter protocol framing (local IPC with Git) -/

/-- The value of a lowercase hexadecimal digit. -/
def hexValue (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else none

/-- The largest pkt-line: 4 length digits and 65516 data bytes. -/
def maxPktLen : Nat := 65520

/-- A pkt-line header: four lowercase hexadecimal digits giving the total
    packet length, big-endian. -/
def PktLen (header : List Nat) (n : Nat) : Prop :=
  ∃ d0 d1 d2 d3, header.map hexValue = [some d0, some d1, some d2, some d3] ∧
    n = ((d0 * 16 + d1) * 16 + d2) * 16 + d3

/-- The headers the filter protocol uses: a flush packet (`0000`) or a data
    packet with at least one data byte and at most `maxPktLen` in total. -/
def PktLenAccepted (header : List Nat) (n : Nat) : Prop :=
  PktLen header n ∧ (n = 0 ∨ (5 ≤ n ∧ n ≤ maxPktLen))

end Transcrypt.V3Policy

import Transcrypt.V3WireCodec

/-!
Independent specification of the v3 protocol *decisions* (path policy, Git
attribute records, record sealing/opening, smudge, lifecycle actions, agent
requests).
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
def maxRecord : Nat := maxFile + fileMinLen
def slash : Nat := 47
def dot : Nat := 46

/-! ASCII bytes of the Git and agent formats. They are reducible, so `decide`,
`simp` and definitional unfolding see the numbers. -/

abbrev tab : Nat := 9
abbrev lf : Nat := 10
abbrev space : Nat := 32
/-- `0` and `9`, `a` and `f`: the ends of the decimal and hexadecimal digit
    ranges; `a` is the hexadecimal digit worth `hexLetterValue`. -/
abbrev digitZero : Nat := 48
abbrev digitNine : Nat := 57
abbrev lowerA : Nat := 97
abbrev lowerF : Nat := 102
abbrev hexLetterValue : Nat := 10
/-- The radixes of decimal sizes and hexadecimal pkt-line lengths. -/
abbrev decimalRadix : Nat := 10
abbrev hexRadix : Nat := 16
/-- The credential agent's opcodes `P`, `E`, `D` and `X`. -/
abbrev opPing : Nat := 80
abbrev opEncrypt : Nat := 69
abbrev opDecrypt : Nat := 68
abbrev opStop : Nat := 88
/-- The derived key's length, and the stored key file: the config it was
    unlocked for, then the key. -/
abbrev keyLen : Nat := 64
abbrev keyFileLen : Nat := configLen + keyLen
/-- Git object names: SHA-1 or SHA-256, in hexadecimal digits. -/
abbrev sha1OidLen : Nat := 40
abbrev sha256OidLen : Nat := 64
/-- The most decimal digits of a blob size Git's reply may have. -/
abbrev maxSizeDigits : Nat := 19
/-- A pkt-line header: its length in four hexadecimal digits. -/
abbrev pktHeaderLen : Nat := 4
/-- A Git file mode, such as `100644`. -/
abbrev modeLen : Nat := 6

/-- Unfold these bytes and lengths (and the wire lengths) to their numbers
    everywhere, for `omega`, which treats a named constant as an unknown. -/
macro "unfold_v3_bytes" : tactic =>
  `(tactic| try simp only [Transcrypt.V3Wire.configMagicLen, Transcrypt.V3Wire.fileMagicLen,
    Transcrypt.V3Wire.saltLen, Transcrypt.V3Wire.tagLen, Transcrypt.V3Wire.idLen,
    Transcrypt.V3Wire.configLen, Transcrypt.V3Wire.fileHeaderLen, Transcrypt.V3Wire.fileMinLen,
    Transcrypt.V3Policy.tab, Transcrypt.V3Policy.lf,
    Transcrypt.V3Policy.space, Transcrypt.V3Policy.digitZero, Transcrypt.V3Policy.digitNine,
    Transcrypt.V3Policy.lowerA, Transcrypt.V3Policy.lowerF, Transcrypt.V3Policy.hexLetterValue,
    Transcrypt.V3Policy.decimalRadix, Transcrypt.V3Policy.hexRadix, Transcrypt.V3Policy.opPing,
    Transcrypt.V3Policy.opEncrypt, Transcrypt.V3Policy.opDecrypt, Transcrypt.V3Policy.opStop,
    Transcrypt.V3Policy.keyLen, Transcrypt.V3Policy.keyFileLen, Transcrypt.V3Policy.sha1OidLen,
    Transcrypt.V3Policy.sha256OidLen, Transcrypt.V3Policy.maxSizeDigits,
    Transcrypt.V3Policy.pktHeaderLen, Transcrypt.V3Policy.modeLen] at *)

def configDomain : List Nat := ascii "transcrypt/v3/config"
def fileDomain : List Nat := ascii "transcrypt/v3/file"
/-- The Git attribute selecting protected files, and the value that does. -/
def filterAttr : List Nat := ascii "filter"
def filterDriver : List Nat := ascii "transcrypt-v3"
def metadataDir : List Nat := ascii ".transcrypt/"
def attributesName : List Nat := ascii ".gitattributes"
def modulesName : List Nat := ascii ".gitmodules"

/-! ## Path policy -/

/-- Repository metadata that must stay readable without the key, whatever
    the attributes select: the committed configuration directory, every
    `.gitattributes` (Git reads it to decide what is protected) and the
    top-level `.gitmodules`. -/
def Reserved (path : List Nat) : Prop :=
  metadataDir <+: path ∨ path = attributesName ∨ (slash :: attributesName) <:+ path ∨
    path = modulesName

/-- A component is acceptable iff nonempty and neither `.` nor `..`. -/
def ComponentOk (c : List Nat) : Prop := c ≠ [] ∧ c ≠ [dot] ∧ c ≠ [dot, dot]

/-- The canonical authenticated-path policy of the v3 spec: nonempty, at most
    4096 bytes, no NUL, every `/`-separated component acceptable (which
    excludes absolute paths and empty, `.` and `..` components), and not
    reserved. *Which* of these paths are protected is the user's choice,
    expressed in Git attributes (below), not a property of the name. -/
def CanonicalProtectedPath (path : List Nat) : Prop :=
  path ≠ [] ∧ path.length ≤ maxPath ∧ 0 ∉ path ∧
  (∀ c ∈ path.splitOn slash, ComponentOk c) ∧ ¬ Reserved path

/-! ## Protected-file selection: Git's `filter` attribute -/

/-- One record of `git check-attr -z --stdin filter` output: the path as
    requested, the attribute name and its value, each NUL-terminated. -/
def attrRecord (path value : List Nat) : List Nat :=
  path ++ [0] ++ filterAttr ++ [0] ++ value ++ [0]

/-- A path is protected iff Git reports `filter` = `transcrypt-v3` for it. -/
def Selected (value : List Nat) : Prop := value = filterDriver

instance (value : List Nat) : Decidable (Selected value) :=
  inferInstanceAs (Decidable (value = filterDriver))

/-- `response` holds, at offset `start`, the record for `path` with the
    NUL-free value `value`; the next record starts at `next`. -/
def AttrRecordAt (response : List Nat) (start : Nat) (path value : List Nat) (next : Nat) : Prop :=
  0 ∉ value ∧ attrRecord path value <+: response.drop start ∧
    next = start + (attrRecord path value).length

/-- Git's complete answer to a request for the listed paths, in order. -/
def attrResponse (records : List (List Nat × List Nat)) : List Nat :=
  records.flatMap (fun r => attrRecord r.1 r.2)

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
  have heq : sealedRecord s config path pt = sealedRecord s config path pt' := by
    rw [← h.2.2.2, ← h'.2.2.2]
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
  refine ⟨h.1, h.2.1, ?_, rfl⟩
  have := h.2.2.1
  rw [sealed_length]
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
  have h : sealedRecord s config path worktree = record := by
    unfold lockSpec at hflush
    split at hflush <;> (try split at hflush) <;> first | assumption | cases hflush
  exact h ▸ seal_opens s hseal

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

/-! ## Git index records -/

/-- Git modes of a regular file, non-executable and executable: the only
    modes whose content Git passes through filters (a symlink stores its
    target unfiltered; a submodule stores a commit id). -/
def regularMode : List Nat := ascii "100644"
def executableMode : List Nat := ascii "100755"

/-- A stage-0 `git ls-files --stage -z` record `mode SP oid SP 0 TAB path`.
    Modes and object ids never contain TAB, so the path (which becomes
    AES-SIV associated data) is exactly what follows the first TAB; paths
    themselves may contain TAB. -/
def IndexRecord (entry : List Nat) (regular : Bool) (path : List Nat) : Prop :=
  ∃ mode oid, entry = mode ++ [space] ++ oid ++ [space, digitZero, tab] ++ path ∧
    mode.length = modeLen ∧ oid ≠ [] ∧ tab ∉ mode ∧ tab ∉ oid ∧ path ≠ [] ∧
    (regular = true ↔ mode = regularMode ∨ mode = executableMode)

/-- The adapter takes the object id of an accepted record as the bytes from
    offset 7 up to 3 bytes before the path, i.e. `entry[7..path_start-3]`.
    For every record of the spec's shape that is exactly its object id. -/
theorem indexRecord_oid {entry : List Nat} {regular : Bool} {path : List Nat}
    (h : IndexRecord entry regular path) :
    ∃ mode oid, entry = mode ++ [space] ++ oid ++ [space, digitZero, tab] ++ path ∧
      ((entry.take (entry.length - path.length - [space, digitZero, tab].length)).drop
        (modeLen + [space].length)) = oid := by
  obtain ⟨mode, oid, rfl, hm, _⟩ := h
  refine ⟨mode, oid, rfl, ?_⟩
  have hlen : (mode ++ [space] ++ oid ++ [space, digitZero, tab] ++ path).length - path.length -
      [space, digitZero, tab].length = (mode ++ [space] ++ oid).length := by simp; omega
  rw [hlen, show mode ++ [space] ++ oid ++ [space, digitZero, tab] ++ path =
      (mode ++ [space] ++ oid) ++ ([space, digitZero, tab] ++ path) by simp, List.take_left]
  rw [show mode ++ [space] ++ oid = (mode ++ [space]) ++ oid by simp]
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

/-- `be32` is injective below 2^32. -/
theorem be32_injective {m n : Nat} (hm : m < 2^32) (hn : n < 2^32) (h : be32 m = be32 n) : m = n := by
  simp only [be32, List.cons.injEq, and_true] at h
  rw [← be32_decode m hm, ← be32_decode n hn, h.1, h.2.1, h.2.2.1, h.2.2.2]

/-! ## Git object names and keyless record envelopes -/

/-- A lowercase hexadecimal digit. -/
def HexDigit (c : Nat) : Prop := (digitZero ≤ c ∧ c ≤ digitNine) ∨ (lowerA ≤ c ∧ c ≤ lowerF)

/-- A Git object name as `ls-files --stage` and `ls-tree` print it: 40
    (SHA-1) or 64 (SHA-256) lowercase hexadecimal digits. The adapter reads
    Git content only through such names. -/
def ObjectId (oid : List Nat) : Prop :=
  (oid.length = sha1OidLen ∨ oid.length = sha256OidLen) ∧ ∀ c ∈ oid, HexDigit c

/-- An object name is neither revision syntax (no `:`, `^`, `~`, `@`, `{`)
    nor an option (it does not start with `-`). -/
theorem objectId_plain {oid : List Nat} (h : ObjectId oid) :
    ∀ c ∈ oid, c ∉ ascii ":^~@{-" := by
  intro c hc hbad
  rcases h.2 c hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [ascii] at hbad <;> unfold_v3_bytes <;> omega

/-- An object name has no byte below `0`: in particular no NUL or TAB. -/
theorem ObjectId.not_mem_of_lt {oid : List Nat} (h : ObjectId oid) {c : Nat} (hc : c < digitZero) :
    c ∉ oid := fun hm => by
  rcases h.2 c hm with ⟨_, _⟩ | ⟨_, _⟩ <;> unfold_v3_bytes <;> omega

theorem objectId_no_tab {oid : List Nat} (h : ObjectId oid) : tab ∉ oid :=
  h.not_mem_of_lt (by decide)

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

/-! ## Smudge -/

inductive SmudgeAction | open_ | keep
  deriving DecidableEq

/-- The smudge decision for a committed blob at a protected path, for the
    configuration with identifier `id`. Bytes that are no v3 record (for
    example plaintext that bypassed the clean filter) are refused, so they are
    never presented as a protected file; a record of this configuration is
    opened (authenticated or refused) when the key is available; any other
    record (locked, or another configuration such as history before a
    rekey) stays encrypted. -/
def smudgeSpec (blob id : List Nat) (unlocked : Bool) : Option SmudgeAction :=
  if blob.length > maxRecord then none
  else match decodeFileHeaderShape blob with
    | none => none
    | some found => if unlocked = true ∧ found = id then some .open_ else some .keep

/-- Smudge only ever keeps a blob that has the v3 file envelope. -/
theorem smudgeSpec_keep_envelope {blob id : List Nat} {unlocked : Bool}
    (h : smudgeSpec blob id unlocked = some .keep) :
    ∃ found, decodeFileHeaderShape blob = some found ∧ blob.length ≤ maxRecord := by
  unfold smudgeSpec at h
  cases hd : decodeFileHeaderShape blob <;> simp_all

/-! ## Pre-commit repair -/

inductive SealAction | keep | seal | rebind | leave
  deriving DecidableEq

/-- The pre-commit decision for one staged protected entry. `opens`: the
    staged blob opens at its own path. `isLocal`: the user staged it (not
    content of a commit being merged, picked or already committed).
    `envelope`: it has the v3 file header. `moved`: it opens at a path the
    user moved it from. Only local content that does not already open is
    repaired: plaintext is sealed, a moved record is re-sealed. -/
def sealSpec (opens isLocal envelope moved : Bool) : SealAction :=
  if opens then .keep
  else if !isLocal then .leave
  else if !envelope then .seal
  else if moved then .rebind
  else .leave

/-- Content from a commit is never re-encrypted (no laundering of a hostile
    move), and neither is a record that already opens at its path. -/
theorem sealSpec_repairs_only_local {o l e m : Bool}
    (h : sealSpec o l e m = .seal ∨ sealSpec o l e m = .rebind) : l = true ∧ o = false := by
  cases o <;> cases l <;> cases e <;> cases m <;> simp_all [sealSpec]

/-- Only plaintext (no envelope) is sealed; only a moved record is re-sealed. -/
theorem sealSpec_seal_plain {o l e m : Bool} (h : sealSpec o l e m = .seal) : e = false := by
  cases o <;> cases l <;> cases e <;> cases m <;> simp_all [sealSpec]

theorem sealSpec_rebind_moved {o l e m : Bool} (h : sealSpec o l e m = .rebind) :
    e = true ∧ m = true := by
  cases o <;> cases l <;> cases e <;> cases m <;> simp_all [sealSpec]

/-! ## Git long-running filter protocol framing (local IPC with Git) -/

/-- The value of a lowercase hexadecimal digit. -/
def hexValue (c : Nat) : Option Nat :=
  if digitZero ≤ c ∧ c ≤ digitNine then some (c - digitZero)
  else if lowerA ≤ c ∧ c ≤ lowerF then some (c - (lowerA - hexLetterValue))
  else none

/-- The largest pkt-line: the header and 65516 data bytes. -/
def maxPktLen : Nat := 65520

/-- A pkt-line header: four lowercase hexadecimal digits giving the total
    packet length, big-endian. -/
def PktLen (header : List Nat) (n : Nat) : Prop :=
  ∃ d0 d1 d2 d3, header.map hexValue = [some d0, some d1, some d2, some d3] ∧
    n = ((d0 * hexRadix + d1) * hexRadix + d2) * hexRadix + d3

/-- The headers the filter protocol uses: a flush packet (`0000`) or a data
    packet with at least one data byte and at most `maxPktLen` in total. -/
def PktLenAccepted (header : List Nat) (n : Nat) : Prop :=
  PktLen header n ∧ (n = 0 ∨ (pktHeaderLen < n ∧ n ≤ maxPktLen))

/-! ## Git snapshots

What Git reports about an index or a commit, as data: the entries of
`git ls-files --stage -z` (or of `git ls-tree -r -z`), in order. The
pre-commit decisions are specified over these lists. -/

/-- One stage-0 entry: mode, object name and path. -/
structure Entry where
  mode : List Nat
  oid : List Nat
  path : List Nat

/-- Its record, `mode SP oid SP 0 TAB path`. -/
def entryRecord (e : Entry) : List Nat := e.mode ++ [space] ++ e.oid ++ [space, digitZero, tab] ++ e.path

/-- An entry as Git prints it: a six-digit mode, an object name and a
    nonempty path. NUL ends records, so no field contains one; the mode
    contains no TAB. -/
def EntryOk (e : Entry) : Prop :=
  e.mode.length = modeLen ∧ tab ∉ e.mode ∧ 0 ∉ e.mode ∧ ObjectId e.oid ∧ e.path ≠ [] ∧ 0 ∉ e.path

/-- A regular file (non-executable or executable): the only kind of entry
    whose content Git passes through filters. -/
def Entry.Regular (e : Entry) : Prop := e.mode = regularMode ∨ e.mode = executableMode

instance (e : Entry) : Decidable e.Regular :=
  inferInstanceAs (Decidable (e.mode = regularMode ∨ e.mode = executableMode))

/-- The exact listing of a snapshot: each record followed by NUL. -/
def listingBytes (es : List Entry) : List Nat := es.flatMap (fun e => entryRecord e ++ [0])

/-- The snapshot has the blob `oid` at `path` (modes do not matter). -/
def Holds (es : List Entry) (oid path : List Nat) : Prop := ∃ e ∈ es, e.oid = oid ∧ e.path = path

/-- Byte order, Git's order of paths in the index and in `ls-tree -r`: at
    the first position where two byte strings differ the smaller byte comes
    first, and a proper prefix comes before its extensions. -/
def BytesLt : List Nat → List Nat → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs => a < b ∨ (a = b ∧ BytesLt as bs)

theorem bytesLt_irrefl : ∀ (a : List Nat), ¬ BytesLt a a
  | [] => fun h => h
  | _ :: xs => fun h => by
    rcases h with h | ⟨_, h⟩
    · exact Nat.lt_irrefl _ h
    · exact bytesLt_irrefl xs h

theorem bytesLt_trans {a b c : List Nat} (h1 : BytesLt a b) (h2 : BytesLt b c) : BytesLt a c := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil => exact h1.elim
    | cons y ys =>
      cases c with
      | nil => exact h2.elim
      | cons z zs => exact trivial
  | cons x xs ih =>
    cases b with
    | nil => exact h1.elim
    | cons y ys =>
      cases c with
      | nil => exact h2.elim
      | cons z zs =>
        rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
        · exact Or.inl (Nat.lt_trans h1 h2)
        · exact Or.inl h1
        · exact Or.inl h2
        · exact Or.inr ⟨rfl, ih h1 h2⟩

theorem bytesLt_total : ∀ (a b : List Nat), BytesLt a b ∨ a = b ∨ BytesLt b a
  | [], [] => Or.inr (Or.inl rfl)
  | [], _ :: _ => Or.inl trivial
  | _ :: _, [] => Or.inr (Or.inr trivial)
  | x :: xs, y :: ys => by
    rcases Nat.lt_trichotomy x y with h | rfl | h
    · exact Or.inl (Or.inl h)
    · rcases bytesLt_total xs ys with h | rfl | h
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
    · exact Or.inr (Or.inr (Or.inl h))

theorem bytesLt_append_left (p a b : List Nat) : BytesLt (p ++ a) (p ++ b) ↔ BytesLt a b := by
  induction p with
  | nil => exact Iff.rfl
  | cons x p ih => simp only [List.cons_append, BytesLt, Nat.lt_irrefl, false_or, true_and, ih]

/-- Byte strings with a common prefix compare as their rests. -/
theorem bytesLt_drop {A B : List Nat} {j : Nat} (h : A.take j = B.take j) :
    BytesLt A B ↔ BytesLt (A.drop j) (B.drop j) := by
  conv => lhs; rw [← List.take_append_drop j A, ← List.take_append_drop j B, h]
  exact bytesLt_append_left _ _ _

/-- A snapshot as Git lists it (the index, or one tree): paths strictly
    increase in byte order, so each path occurs once. A tree that lists a
    path twice or out of order (`git mktree` accepts one, `git fsck` does
    not) is not a snapshot. -/
def Sorted (es : List Entry) : Prop := es.Pairwise (fun a b => BytesLt a.path b.path)

/-- Paths never decrease in byte order: the entries of several trees, merged
    by path (a path may repeat). -/
def PathOrdered (es : List Entry) : Prop :=
  es.Pairwise (fun a b => BytesLt a.path b.path ∨ a.path = b.path)

theorem Sorted.pathOrdered {es : List Entry} (h : Sorted es) : PathOrdered es :=
  h.imp Or.inl

/-- In a sorted snapshot an entry is determined by its path. -/
theorem Sorted.eq_of_path {es : List Entry} (h : Sorted es) {a b : Entry} (ha : a ∈ es) (hb : b ∈ es)
    (hp : a.path = b.path) : a = b := by
  induction es with
  | nil => cases ha
  | cons x xs ih =>
    rw [Sorted, List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with hax | ha'
    · rcases List.mem_cons.1 hb with hbx | hb'
      · rw [hax, hbx]
      · have := h.1 b hb'
        rw [← hax, hp] at this
        exact absurd this (bytesLt_irrefl _)
    · rcases List.mem_cons.1 hb with hbx | hb'
      · have := h.1 a ha'
        rw [← hbx, ← hp] at this
        exact absurd this (bytesLt_irrefl _)
      · exact ih h.2 ha' hb'

/-- So in a sorted snapshot, `Holds` names *the* entry at the path: every
    entry at that path has that blob. -/
theorem Sorted.holds_oid {es : List Entry} (h : Sorted es) {oid path : List Nat} (hh : Holds es oid path)
    {e : Entry} (he : e ∈ es) (hp : e.path = path) : e.oid = oid := by
  obtain ⟨x, hx, ho, hxp⟩ := hh
  rw [h.eq_of_path he hx (hp.trans hxp.symm), ho]

/-- Distinct entries of a sorted snapshot have distinct paths. -/
theorem Sorted.path_ne {es : List Entry} (hS : Sorted es) {a b : Nat} (ha : a < es.length)
    (hb : b < es.length) (hab : a ≠ b) : es[a].path ≠ es[b].path := by
  intro heq
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · have := List.pairwise_iff_getElem.mp hS a b ha hb h
    rw [heq] at this; exact bytesLt_irrefl _ this
  · have := List.pairwise_iff_getElem.mp hS b a hb ha h
    rw [heq] at this; exact bytesLt_irrefl _ this

/-- In a listing in path order, paths before `P` come first. -/
theorem PathOrdered.lt_of_le {es : List Entry} (hO : PathOrdered es) {P : List Nat} {k m : Nat}
    (hkm : k ≤ m) (hm : m < es.length) (h : BytesLt es[m].path P) : BytesLt es[k].path P := by
  rcases Nat.lt_or_ge k m with hlt | hge
  · rcases List.pairwise_iff_getElem.mp hO k m (by omega) hm hlt with h' | h'
    · exact bytesLt_trans h' h
    · rw [h']; exact h
  · have : k = m := by omega
    subst this; exact h

/-- After a path that comes after `P`, no path is `P`. -/
theorem PathOrdered.ne_of_gt {es : List Entry} (hO : PathOrdered es) {P : List Nat} {j k : Nat}
    (hjk : j ≤ k) (hk : k < es.length) (hj : BytesLt P es[j].path) : es[k].path ≠ P := by
  intro hkp
  rcases Nat.lt_or_ge j k with hlt | hge
  · rcases List.pairwise_iff_getElem.mp hO j k (by omega) hk hlt with h' | h'
    · rw [hkp] at h'; exact bytesLt_irrefl _ (bytesLt_trans hj h')
    · rw [h', hkp] at hj; exact bytesLt_irrefl _ hj
  · have : j = k := by omega
    subst this; rw [hkp] at hj; exact bytesLt_irrefl _ hj

/-- A selected entry can be protected: a regular file, not reserved
    metadata. -/
def Selectable (e : Entry) : Prop := e.Regular ∧ ¬ Reserved e.path

/-- The `isLocal` input of `sealSpec` for the staged entry `s`: the user
    staged it, i.e. `HEAD` does not hold its blob at its path and the
    commits being merged, picked, reverted or rebased (`incoming`) are known
    and do not hold it either (`none`: a rebase or `am` without a known
    commit, where nothing counts as local); or `protect` selected it
    (`forced`) and it is plaintext (no `envelope`). -/
def LocalChange (head : List Entry) (incoming : Option (List Entry)) (forced envelope : Bool)
    (s : Entry) : Prop :=
  (¬ Holds head s.oid s.path ∧ ∃ m, incoming = some m ∧ ¬ Holds m s.oid s.path) ∨
    (forced = true ∧ envelope = false)

/-- `h`, an entry of `HEAD`, is where the staged entry `s` may have been
    moved from: the same blob at another path, whose own entry has left the
    index (removed, or replaced by other content). -/
def MoveSource (index : List Entry) (s h : Entry) : Prop :=
  h.oid = s.oid ∧ h.path ≠ s.path ∧ ¬ Holds index h.oid h.path

/-- Unchanged since `HEAD` and since its first parent: already in history
    (the parent counts because `--amend` makes it the commit's parent). -/
def Settled (head parent : List Entry) (s : Entry) : Prop :=
  Holds head s.oid s.path ∧ Holds parent s.oid s.path

/-- The blob of `s` is at another path of one of the snapshots: a record
    moved or copied there, which would not open at `s`'s path. -/
def BlobElsewhere (snapshots : List (List Entry)) (s : Entry) : Prop :=
  ∃ l ∈ snapshots, ∃ e ∈ l, e.oid = s.oid ∧ e.path ≠ s.path

/-- Every record of a well-formed snapshot is an `IndexRecord`, with the
    regular flag of its mode and its path. -/
theorem entryOk_indexRecord {e : Entry} (h : EntryOk e) :
    IndexRecord (entryRecord e) (decide e.Regular) e.path := by
  obtain ⟨hm, h9, _, hoid, hp, _⟩ := h
  refine ⟨e.mode, e.oid, rfl, hm, ?_, h9, objectId_no_tab hoid, hp, decide_eq_true_iff⟩
  intro h0; have := h0 ▸ hoid.1; simp at this

/-- Content held by `HEAD` at its path is never a local change unless
    `protect` forces sealing its plaintext. -/
theorem localChange_held {head : List Entry} {incoming : Option (List Entry)} {forced envelope : Bool}
    {s : Entry} (h : Holds head s.oid s.path) :
    LocalChange head incoming forced envelope s ↔ forced = true ∧ envelope = false := by
  unfold LocalChange
  constructor
  · rintro (⟨hn, _⟩ | hf)
    · exact absurd h hn
    · exact hf
  · exact Or.inr

/-- Without known incoming commits (a rebase without a stopped commit),
    only forced plaintext is local. -/
theorem localChange_unknown {head : List Entry} {forced envelope : Bool} {s : Entry} :
    LocalChange head none forced envelope s ↔ forced = true ∧ envelope = false := by
  unfold LocalChange
  constructor
  · rintro (⟨_, m, hm, _⟩ | hf)
    · cases hm
    · exact hf
  · exact Or.inr

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
  split at h <;> (try split at h) <;> (try split at h) <;> simp_all

/-! ## Git object replies (`git cat-file --batch`) -/

/-- The type field of a blob reply. -/
def blobField : List Nat := ascii " blob "

def DecimalDigit (c : Nat) : Prop := digitZero ≤ c ∧ c ≤ digitNine

/-- The value of decimal digits, most significant first. -/
def decimalValue (ds : List Nat) : Nat := ds.foldl (fun v c => v * decimalRadix + (c - digitZero)) 0

/-- Canonical decimal: at least one digit, digits only, and no leading zero
    except in `0` itself. -/
def CanonicalDecimal (ds : List Nat) : Prop :=
  ds ≠ [] ∧ (∀ c ∈ ds, DecimalDigit c) ∧ (ds.head? = some digitZero → ds = [digitZero])

/-- Git's reply header for the blob `oid` of `size` bytes:
    `<oid> SP blob SP <size> LF`, with the size in canonical decimal of at
    most `maxSizeDigits` digits (any blob smaller than 10^19 bytes). -/
def BatchHeader (header oid : List Nat) (size : Nat) : Prop :=
  ∃ ds, header = oid ++ blobField ++ ds ++ [lf] ∧ CanonicalDecimal ds ∧ ds.length ≤ maxSizeDigits ∧
    size = decimalValue ds

/-- A reply header names one size: the reply for an object id cannot be
    read as two different sizes. -/
theorem batchHeader_unique {header oid : List Nat} {n n' : Nat}
    (h : BatchHeader header oid n) (h' : BatchHeader header oid n') : n = n' := by
  obtain ⟨ds, rfl, _, _, rfl⟩ := h
  obtain ⟨ds', he, _, _, rfl⟩ := h'
  simp only [List.append_assoc, List.append_cancel_left_eq, List.append_cancel_right_eq] at he
  rw [he]

inductive BlobRead | read | skip | tooLarge
  deriving DecidableEq

/-- Only a blob within the record bound is ever loaded; a larger one is
    skipped unread where the caller allows it, else refused. -/
def blobReadSpec (size : Nat) (skipLarge : Bool) : BlobRead :=
  if size ≤ maxRecord then .read else if skipLarge then .skip else .tooLarge

end Transcrypt.V3Policy

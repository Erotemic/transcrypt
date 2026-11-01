import Transcrypt.V3Policy.Paths
import Transcrypt.V3Policy.Lifecycle

/-!
# What Git reports, as data

Index and tree records, object names, snapshots (`Entry`, `Sorted`) and the
pre-commit facts about them (`ProvenanceIs`, `LocalChange`, `Settled`, ...), the pkt-line
framing of Git's long-running filter protocol, and `git cat-file --batch`
replies.
-/

namespace Transcrypt.V3Policy

open Transcrypt.V3Wire

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
    offset `oidStart` up to `oidEndLen` bytes before the path, i.e.
    `entry[OID_START..path_start - OID_END_LEN]`.
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

/-! ## Git object names and keyless record envelopes -/

/-- A lowercase hexadecimal digit. -/
def HexDigit (c : Nat) : Prop := (digitZero ≤ c ∧ c ≤ digitNine) ∨ (lowerA ≤ c ∧ c ≤ lowerF)

/-- A Git object name as `ls-files --stage` and `ls-tree` print it: 40
    (SHA-1) or 64 (SHA-256) lowercase hexadecimal digits. The adapter reads
    Git content only through such names. -/
def ObjectId (oid : List Nat) : Prop :=
  (oid.length = sha1OidLen ∨ oid.length = sha256OidLen) ∧ ∀ c ∈ oid, HexDigit c

/-- The two digit ranges as numbers: `0`-`9` are bytes 48-57, `a`-`f` are
    97-102. -/
theorem hexDigit_iff {c : Nat} : HexDigit c ↔ (48 ≤ c ∧ c ≤ 57) ∨ (97 ≤ c ∧ c ≤ 102) := Iff.rfl

/-- An object name is neither revision syntax (no `:`, `^`, `~`, `@`, `{`)
    nor an option (it does not start with `-`): those bytes (58, 94, 126,
    64, 123, 45) are not hexadecimal digits. -/
theorem objectId_plain {oid : List Nat} (h : ObjectId oid) :
    ∀ c ∈ oid, c ∉ ascii ":^~@{-" := by
  intro c hc hbad
  simp [ascii] at hbad
  rcases hexDigit_iff.mp (h.2 c hc) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

/-- An object name has no byte below `0`: in particular no NUL or TAB. -/
theorem ObjectId.not_mem_of_lt {oid : List Nat} (h : ObjectId oid) {c : Nat} (hc : c < digitZero) :
    c ∉ oid := fun hm => by
  have hc48 : c < 48 := hc
  rcases hexDigit_iff.mp (h.2 c hm) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

theorem objectId_no_tab {oid : List Nat} (h : ObjectId oid) : tab ∉ oid :=
  h.not_mem_of_lt (by decide)

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
structure EntryOk (e : Entry) : Prop where
  mode_len : e.mode.length = modeLen
  mode_no_tab : tab ∉ e.mode
  mode_no_nul : 0 ∉ e.mode
  oid_ok : ObjectId e.oid
  path_ne : e.path ≠ []
  path_no_nul : 0 ∉ e.path

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

/-- The user staged `s`: `HEAD` does not hold its blob at its path, and the
    commits being merged, picked, reverted or rebased (`incoming`) are known
    and do not hold it either (`none`: a rebase or `am` without a known
    commit, where nothing counts as the user's). -/
def UserStaged (head : List Entry) (incoming : Option (List Entry)) (s : Entry) : Prop :=
  ¬ Holds head s.oid s.path ∧ ∃ m, incoming = some m ∧ ¬ Holds m s.oid s.path

/-- `p` is where the content of the staged entry `s` came from: the user
    staged it (`local_`); otherwise `protect` selected it (`forced`);
    otherwise `HEAD` does not hold it and the commits being brought in are
    not known (`unknown`); otherwise `HEAD` or one of those commits holds
    its blob at its path (`committed`). -/
def ProvenanceIs (head : List Entry) (incoming : Option (List Entry)) (forced : Bool) (s : Entry) :
    Provenance → Prop
  | .local_ => UserStaged head incoming s
  | .forced => ¬ UserStaged head incoming s ∧ forced = true
  | .unknown => forced = false ∧ ¬ Holds head s.oid s.path ∧ incoming = none
  | .committed => forced = false ∧
      (Holds head s.oid s.path ∨ ∃ m, incoming = some m ∧ Holds m s.oid s.path)

/-- The user's change is not content of a commit. -/
theorem UserStaged.not_committed {head : List Entry} {incoming : Option (List Entry)} {s : Entry}
    (h : UserStaged head incoming s) :
    ¬ (Holds head s.oid s.path ∨ ∃ m, incoming = some m ∧ Holds m s.oid s.path) := by
  obtain ⟨hh, m, rfl, hmh⟩ := h
  rintro (h | ⟨m', hm', h'⟩)
  · exact hh h
  · cases hm'; exact hmh h'

/-- An entry has one provenance. -/
theorem provenanceIs_unique {head : List Entry} {incoming : Option (List Entry)} {forced : Bool} {s : Entry}
    {p q : Provenance} (hp : ProvenanceIs head incoming forced s p) (hq : ProvenanceIs head incoming forced s q) :
    p = q := by
  cases p <;> cases q <;> simp only [ProvenanceIs] at hp hq <;> first | rfl | exfalso
  all_goals first
    | exact hp.not_committed hq.2
    | exact hq.not_committed hp.2
    | exact hp.1 hq
    | exact hq.1 hp
    | simp_all [UserStaged]

/-- Content `HEAD` holds at its path has the same provenance whatever the
    commits being brought in are: the hook need not list them. -/
theorem provenanceIs_held {head : List Entry} {incoming incoming' : Option (List Entry)} {forced : Bool}
    {s : Entry} {p : Provenance} (h : Holds head s.oid s.path) :
    ProvenanceIs head incoming forced s p ↔ ProvenanceIs head incoming' forced s p := by
  have hu : ∀ inc, ¬ UserStaged head inc s := fun _ hu => hu.1 h
  cases p <;> simp only [ProvenanceIs, h, not_true_eq_false, false_and, and_false, true_or, and_true]
  · exact ⟨fun hl => absurd hl (hu _), fun hl => absurd hl (hu _)⟩
  · simp [hu]

/-- The local-change test: the user staged `s`, or `protect` selected it
    (`forced`) and it is plaintext (no `envelope`). -/
def LocalChange (head : List Entry) (incoming : Option (List Entry)) (forced envelope : Bool)
    (s : Entry) : Prop :=
  UserStaged head incoming s ∨ (forced = true ∧ envelope = false)

/-- A local change is content of `local_` provenance, or `forced`
    plaintext: what `repairSpec` may repair. -/
theorem localChange_iff_provenance {head : List Entry} {incoming : Option (List Entry)} {forced : Bool}
    {s : Entry} {p : Provenance} (hp : ProvenanceIs head incoming forced s p) (envelope : Bool) :
    LocalChange head incoming forced envelope s ↔ p = .local_ ∨ (p = .forced ∧ envelope = false) := by
  unfold LocalChange
  cases p <;> simp only [ProvenanceIs] at hp <;> simp
  · obtain ⟨hf, hh⟩ := hp
    exact ⟨fun hu => hu.not_committed hh, fun h => by rw [hf] at h; cases h⟩
  · exact Or.inl hp
  · obtain ⟨hn, rfl⟩ := hp
    simp [hn]
  · obtain ⟨rfl, -, hi⟩ := hp
    simp [UserStaged, hi]

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

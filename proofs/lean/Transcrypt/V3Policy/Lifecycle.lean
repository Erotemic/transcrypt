import Transcrypt.V3Policy.Authentication

/-!
# Lifecycle decisions

What `hydrate`, `lock`, the smudge filter and the pre-commit repair do with
one protected file.
-/

namespace Transcrypt.V3Policy

open Transcrypt.V3Wire

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
  -- `.flush` is returned only when the worktree is not already the record
  -- and resealing it gives exactly the record.
  have h : sealedRecord s config path worktree = record := by
    unfold lockSpec at hflush
    by_cases hkeep : worktree = record
    · rw [if_pos hkeep] at hflush; cases hflush
    · rw [if_neg hkeep] at hflush
      by_cases hreseal : sealedRecord s config path worktree = record
      · exact hreseal
      · rw [if_neg hreseal] at hflush; cases hflush
  exact h ▸ seal_opens s hseal

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
  -- An oversized blob and bytes without the header are refused (`none`).
  by_cases hbig : blob.length > maxRecord
  · rw [if_pos hbig] at h; cases h
  rw [if_neg hbig] at h
  cases hd : decodeFileHeaderShape blob with
  | none => rw [hd] at h; cases h
  | some found => exact ⟨found, rfl, Nat.le_of_not_gt hbig⟩

/-! ## Pre-commit repair

The pre-commit hook may re-encrypt a staged protected entry before checking
the index. Two independent facts decide it: where the content came from
(`Provenance`, defined from Git's snapshots by `ProvenanceIs` in `Git`) and
what its blob is (`RecordClass`). The policy: a blob that already opens is
kept, and only the user's own content is repaired. Content that came from a
commit is checked, never re-encrypted, so a hostile commit's moved or
plaintext content cannot be laundered into a genuine record. -/

/-- Where the content of a staged protected entry came from: a commit
    (`HEAD` or a commit being brought in), the user (`local_`), `protect`
    selecting it (`forced`), or not known (the commits being brought in are
    not known). -/
inductive Provenance | committed | local_ | forced | unknown
  deriving DecidableEq

/-- What a staged protected blob is: it opens at the entry's own path; it
    has no v3 file header (`plaintext`); it is a record that does not open
    there but opens at the path of record `source` of `HEAD`, a place it was
    moved from; or a record that opens at neither (`unusable`). -/
inductive RecordClass | opensHere | plaintext | movedFrom (source : Nat) | unusable
  deriving DecidableEq

/-- Why an entry is left to verification: not the user's change, or the
    user's record that opens nowhere it could be re-encrypted from. -/
inductive LeaveReason | notLocal | opensNowhere
  deriving DecidableEq

/-- The repair of one entry: keep it, seal its plaintext, re-seal the
    plaintext of a record moved from `HEAD` record `source`, or leave it to
    verification. -/
inductive RepairPlan | keep | seal | rebind (source : Nat) | leave (reason : LeaveReason)
  deriving DecidableEq

/-- Content the hook may change: the user's own, or plaintext `protect`
    selected. -/
def Repairable (p : Provenance) : Prop := p = .local_ ∨ p = .forced

instance : DecidablePred Repairable := fun p => inferInstanceAs (Decidable (p = .local_ ∨ p = .forced))

/-- The pre-commit decision. Plaintext is sealed when the user staged it or
    `protect` forced it; a record is re-sealed only when the user moved it
    (`protect` never re-encrypts a record); anything else that does not open
    is left to verification. -/
def repairSpec (p : Provenance) (c : RecordClass) : RepairPlan :=
  match c with
  | .opensHere => .keep
  | .plaintext => if Repairable p then .seal else .leave .notLocal
  | .movedFrom source => if p = .local_ then .rebind source else .leave .notLocal
  | .unusable => if p = .local_ then .leave .opensNowhere else .leave .notLocal

/-- Whether the decision depends on the blob at all: only for content the
    hook may change. -/
def needsRecordSpec (p : Provenance) : Bool := decide (Repairable p)

/-- Only plaintext is sealed, and only the user's or forced content. -/
theorem repairSpec_seal {p : Provenance} {c : RecordClass} :
    repairSpec p c = .seal ↔ c = .plaintext ∧ Repairable p := by
  cases p <;> cases c <;> simp [repairSpec, Repairable]

/-- Only a record the user moved is re-sealed, from where it was moved. -/
theorem repairSpec_rebind {p : Provenance} {c : RecordClass} {source : Nat} :
    repairSpec p c = .rebind source ↔ c = .movedFrom source ∧ p = .local_ := by
  cases p <;> cases c <;> simp [repairSpec, Repairable, eq_comm]

/-- A blob is kept exactly when it opens at its own path. -/
theorem repairSpec_keep {p : Provenance} {c : RecordClass} :
    repairSpec p c = .keep ↔ c = .opensHere := by
  cases p <;> cases c <;> simp [repairSpec, Repairable]

/-- **No laundering.** Every repair is of the user's own content, or of
    plaintext `protect` selected; never of a blob that already opens. -/
theorem repairSpec_repairs_only_local {p : Provenance} {c : RecordClass}
    (h : repairSpec p c = .seal ∨ ∃ source, repairSpec p c = .rebind source) :
    (p = .local_ ∨ (p = .forced ∧ c = .plaintext)) ∧ c ≠ .opensHere := by
  rcases h with h | ⟨source, h⟩
  · obtain ⟨rfl, hp⟩ := repairSpec_seal.mp h
    rcases hp with rfl | rfl <;> simp
  · obtain ⟨rfl, rfl⟩ := repairSpec_rebind.mp h
    simp

/-- An entry whose blob the hook does not read is never repaired, whatever
    its blob is. -/
theorem repairSpec_unread {p : Provenance} (h : needsRecordSpec p = false) (c : RecordClass) :
    repairSpec p c = .keep ∨ ∃ reason, repairSpec p c = .leave reason := by
  have hp : p = .committed ∨ p = .unknown := by
    cases p <;> simp_all [needsRecordSpec, Repairable]
  rcases hp with rfl | rfl <;> cases c <;> simp [repairSpec, Repairable]

end Transcrypt.V3Policy

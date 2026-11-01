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
  have h : sealedRecord s config path worktree = record := by
    unfold lockSpec at hflush
    split at hflush <;> (try split at hflush) <;> first | assumption | cases hflush
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

end Transcrypt.V3Policy

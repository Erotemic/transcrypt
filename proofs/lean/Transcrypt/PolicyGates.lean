/-!
  **Legacy (pre-v3).** Abstract preflight decision gates. The properties hold for all Boolean
  evidence inputs; *correct production of the evidence* is a separate
  external Git/crypto adapter obligation. These definitions intentionally
  do not assert that Transcrypt v2 currently uses these gates.

  Future Charon/Aeneas refinement must relate the real Rust implementations
  to this independent specification rather than replacing these definitions.
-/

namespace Transcrypt.PolicyGates

def secureStageAllowed (stagedProtected localProtected stagedRegular
    completeConfig metadataBound authenticated : Bool) : Bool :=
  (stagedProtected || localProtected) && stagedRegular &&
    completeConfig && metadataBound && authenticated

def unlockWritesAllowed (authenticated configValid destinationSafe stable : Bool) : Bool :=
  authenticated && configValid && destinationSafe && stable

def migrationPublishAllowed (sourceAuthenticated contextsComplete targetAuthenticated
    targetConfigComplete stable rollbackAvailable : Bool) : Bool :=
  sourceAuthenticated && contextsComplete && targetAuthenticated &&
    targetConfigComplete && stable && rollbackAvailable

/-- No protected ciphertext is accepted without explicit authentication
    and matching staged metadata. The or-ed protection predicate prevents
    a local attribute override from hiding the staged protection policy. -/
theorem secure_stage_sound (p l r c m a : Bool) :
    secureStageAllowed p l r c m a = true →
      (p = true ∨ l = true) ∧ r = true ∧ c = true ∧ m = true ∧ a = true := by
  revert p l r c m a; decide

/-- A wrong password, absent verifier, or failed preflight cannot authorize
    persistent writes (conditional on correctly classified evidence). -/
theorem unlock_no_writes_on_failed_preflight (a c d s : Bool) :
    unlockWritesAllowed a c d s = true →
      a = true ∧ c = true ∧ d = true ∧ s = true := by
  revert a c d s; decide

/-- Migration publication is withheld unless source and target evidence,
    snapshot stability and a rollback path have all been established. -/
theorem migration_publish_requires_complete_evidence
    (a b c d e f : Bool) :
    migrationPublishAllowed a b c d e f = true →
      a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true ∧ f = true := by
  revert a b c d e f; decide

end Transcrypt.PolicyGates

import V3Wire.Verification.Bytes

/-!
# Interrupted commands and the pre-push verdict: the production decisions

Functional refinement of the core functions behind the setup record, the
rekey journal's recovery and the pre-push verdict: each production function
makes exactly the decision of the independent specification
(`Transcrypt.V3Policy.Interruption`), with no panic or divergence. The
models there (`interrupted_setup_completes_with_its_policy`,
`interrupted_rekey_abort_restores`, ...) are stated over these
specification decisions, so they hold of the adapter's runs whose
decisions these functions make (`journal.rs`, `rekey.rs`, `audit.rs`), under
the adapter contracts the models name (A28, A29).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core

/-! ## The setup record -/

def setupKindSpecOf : SetupKind → Transcrypt.V3Policy.SetupKind
  | .Init => .init
  | .Migrate => .migrate

def recordUseSpecOf : RecordUse → Transcrypt.V3Policy.RecordUse
  | .Fresh => .fresh
  | .Merge => .merge
  | .OtherSetup => .otherSetup
  | .Unrecorded => .unrecorded

theorem recordUseSpecOf_injective {a b : RecordUse} (h : recordUseSpecOf a = recordUseSpecOf b) : a = b := by
  cases a <;> cases b <;> simp_all [recordUseSpecOf]

/-- `setup_record_use` is `recordUseSpec`; the record is passed as
    `recorded` (it exists), its command and whether it finished. -/
@[step]
theorem setup_record_use_spec (kind : SetupKind) (resuming recorded : Bool) (recordedKind : SetupKind)
    (complete named : Bool) :
    setup_record_use kind resuming recorded recordedKind complete named ⦃ u =>
      recordUseSpecOf u = Transcrypt.V3Policy.recordUseSpec (setupKindSpecOf kind) resuming
        (if recorded then some (setupKindSpecOf recordedKind, complete) else none) named ⦄ := by
  rcases kind with _ | _ <;> rcases recordedKind with _ | _ <;> rcases resuming with _ | _ <;>
    rcases recorded with _ | _ <;> rcases complete with _ | _ <;> rcases named with _ | _ <;>
    simp [setup_record_use, same_setup_kind, setupKindSpecOf, recordUseSpecOf,
      Transcrypt.V3Policy.recordUseSpec]

/-- **An unfinished record is never ignored, in production terms**: with a
    record that did not finish, `setup_record_use` answers `Merge` for its
    own command and `OtherSetup` for the other. -/
theorem setup_record_use_unfinished (kind recordedKind : SetupKind) (resuming named : Bool) :
    setup_record_use kind resuming true recordedKind false named ⦃ u =>
      u = (if setupKindSpecOf recordedKind = setupKindSpecOf kind then .Merge else .OtherSetup) ⦄ := by
  rcases kind with _ | _ <;> rcases recordedKind with _ | _ <;> rcases resuming with _ | _ <;>
    rcases named with _ | _ <;>
    simp [setup_record_use, same_setup_kind, setupKindSpecOf]

/-! ## The rekey journal's recovery -/

def entryRecoverySpecOf : EntryRecovery → Transcrypt.V3Policy.EntryRecovery
  | .Done => .done
  | .Todo => .todo
  | .Changed => .changed

def configRecoverySpecOf : ConfigRecovery → Transcrypt.V3Policy.ConfigRecovery
  | .Done => .done
  | .Write => .write
  | .Changed => .changed

def fileRecoverySpecOf : FileRecovery → Transcrypt.V3Policy.FileRecovery
  | .Relock => .relock
  | .Keep => .keep
  | .Check => .check

theorem entryRecoverySpecOf_injective {a b : EntryRecovery} (h : entryRecoverySpecOf a = entryRecoverySpecOf b) :
    a = b := by
  cases a <;> cases b <;> simp_all [entryRecoverySpecOf]

theorem configRecoverySpecOf_injective {a b : ConfigRecovery}
    (h : configRecoverySpecOf a = configRecoverySpecOf b) : a = b := by
  cases a <;> cases b <;> simp_all [configRecoverySpecOf]

theorem fileRecoverySpecOf_injective {a b : FileRecovery} (h : fileRecoverySpecOf a = fileRecoverySpecOf b) :
    a = b := by
  cases a <;> cases b <;> simp_all [fileRecoverySpecOf]

/-- `entry_recovery` is `entryRecoverySpec` on the bytes of the object ids. -/
@[step]
theorem entry_recovery_spec (staged : Bool) (oid want other : Slice U8) :
    entry_recovery staged oid want other ⦃ r =>
      entryRecoverySpecOf r = Transcrypt.V3Policy.entryRecoverySpec staged (sliceBytes oid) (sliceBytes want)
        (sliceBytes other) ⦄ := by
  unfold entry_recovery
  rcases staged with _ | _
  · simp [entryRecoverySpecOf, Transcrypt.V3Policy.entryRecoverySpec]
  · step*
    all_goals simp_all [entryRecoverySpecOf, Transcrypt.V3Policy.entryRecoverySpec, sliceBytes_inj]

/-- `config_recovery` is `configRecoverySpec` on the config bytes. -/
@[step]
theorem config_recovery_spec (present : Bool) (worktree want other : Slice U8) :
    config_recovery present worktree want other ⦃ r =>
      configRecoverySpecOf r = Transcrypt.V3Policy.configRecoverySpec present (sliceBytes worktree)
        (sliceBytes want) (sliceBytes other) ⦄ := by
  unfold config_recovery
  rcases present with _ | _
  · simp [configRecoverySpecOf, Transcrypt.V3Policy.configRecoverySpec]
  · step*
    all_goals simp_all [configRecoverySpecOf, Transcrypt.V3Policy.configRecoverySpec, sliceBytes_inj]

/-- `file_recovery` is `fileRecoverySpec` on the file and record bytes. -/
@[step]
theorem file_recovery_spec (worktree want other : Slice U8) :
    file_recovery worktree want other ⦃ r =>
      fileRecoverySpecOf r = Transcrypt.V3Policy.fileRecoverySpec (sliceBytes worktree) (sliceBytes want)
        (sliceBytes other) ⦄ := by
  unfold file_recovery
  step*
  all_goals simp_all [fileRecoverySpecOf, Transcrypt.V3Policy.fileRecoverySpec, sliceBytes_inj]

/-- **A recovery writes a worktree file only when it is exactly the record
    being replaced**, in production terms: `file_recovery` answers `Relock`
    exactly then. -/
theorem file_recovery_relock (worktree want other : Slice U8) :
    file_recovery worktree want other ⦃ r => r = .Relock ↔ sliceBytes worktree = sliceBytes other ⦄ := by
  apply WP.spec_mono (file_recovery_spec worktree want other)
  intro r hr
  rw [← (Transcrypt.V3Policy.fileRecoverySpec_relock (worktree := sliceBytes worktree) (want := sliceBytes want)
    (other := sliceBytes other)), ← hr]
  constructor
  · rintro rfl; rfl
  · intro h
    exact fileRecoverySpecOf_injective (a := r) (b := .Relock) h

/-! ## The pre-push verdict -/

def pushAdmissionSpecOf : PushAdmission → Transcrypt.V3Policy.PushAdmission
  | .Admit => .allow
  | .Warn => .warn
  | .Refuse => .refuse

/-- `push_admission` is `pushAdmissionSpec`. -/
@[step]
theorem push_admission_spec (authenticated required : Bool) :
    push_admission authenticated required ⦃ r =>
      pushAdmissionSpecOf r = Transcrypt.V3Policy.pushAdmissionSpec authenticated required ⦄ := by
  rcases authenticated with _ | _ <;> rcases required with _ | _ <;>
    simp [push_admission, pushAdmissionSpecOf, Transcrypt.V3Policy.pushAdmissionSpec]

/-- **A push that requires authentication proceeds only authenticated**:
    with `required`, `push_admission` refuses unless the audit
    authenticated every protected file. -/
theorem push_admission_required (authenticated : Bool) :
    push_admission authenticated true ⦃ r => r ≠ .Refuse → authenticated = true ⦄ := by
  rcases authenticated with _ | _ <;> simp [push_admission]

end Transcrypt.V3Verification

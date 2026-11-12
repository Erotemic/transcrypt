/-!
# Interrupted commands

What `init`, `migrate` and `rekey` leave when they are interrupted, and what
resuming them does. Two records in the Git directory carry an interrupted
command's intent across processes (`docs/verification/specs/V3-AUTHENTICATED-P0.md`,
"Interrupted commands"):

* the **setup record** (`transcrypt-v3-setup`): what `init` or `migrate`
  was asked to protect, saved before the command changes anything;
* the **rekey journal** (`transcrypt-v3-rekey`): every index entry `rekey`
  replaces, as it was and as it becomes, saved before the index changes.

Each section has the decisions the verified core makes (`recordUseSpec`,
`entryRecoverySpec`, `configRecoverySpec`, `fileRecoverySpec`; the Aeneas
refinement theorems relate the production functions to them) and a model of
the command's durable transitions, in which the theorems hold whatever
point the command is interrupted at.

* **Setup** (`interrupted_setup_completes_with_its_policy`,
  `interrupted_init_completes_with_its_patterns`): once a setup has saved
  its record, every later run that completes, however many runs were
  interrupted, failed and rolled back, or ran meanwhile, protects at least
  what the record holds; for `migrate`, less only a recorded path a later
  run found removed from the index. Only the operator's start over, which
  removes the record and is no transition of the model, releases it.
* **Rekey** (`interrupted_rekey_recovers`, `interrupted_rekey_abort_restores`):
  from any state an interrupted `rekey`, interrupted recoveries in either
  direction and the user's changes to other paths can leave, `--continue`
  and `--abort` are both possible; `--abort` puts back exactly what `rekey`
  found at every journaled path, the worktree config and the key, and
  leaves every other index entry and worktree file as the user left it,
  including changes that exist only in the index. Without such changes it
  restores the state `rekey` started from exactly
  (`interrupted_rekey_abort_restores_exactly`). A change to a journaled
  entry makes both refuse, before any write (`admissible_iff`).
-/

namespace Transcrypt.V3Policy

/-! ## The setup record: the decision -/

/-- The command a setup record is for. -/
inductive SetupKind | init | migrate
  deriving DecidableEq

/-- What a run of `init` or `migrate` does with the setup record. -/
inductive RecordUse | fresh | merge | otherSetup | unrecorded
  deriving DecidableEq

/-- The decision. `record`: the record's command and whether it finished,
    if there is one; `resuming`: `.transcrypt` exists and `HEAD` has no
    config; `named`: the run was asked to protect something. A record binds
    unless it finished and its setup is no longer in the checkout; the same
    command merges a binding record, any other is refused; resuming with no
    record and nothing named is refused. -/
def recordUseSpec (kind : SetupKind) (resuming : Bool) (record : Option (SetupKind × Bool)) (named : Bool) :
    RecordUse :=
  match record with
  | none => if resuming = true ∧ named = false then .unrecorded else .fresh
  | some (recorded, complete) =>
    if resuming = false ∧ complete = true then .fresh
    else if recorded = kind then .merge else .otherSetup

/-- An unfinished record is never ignored: its own command merges it, any
    other command is refused. -/
theorem recordUseSpec_unfinished (kind recorded : SetupKind) (resuming named : Bool) :
    recordUseSpec kind resuming (some (recorded, false)) named =
      if recorded = kind then .merge else .otherSetup := by
  simp [recordUseSpec]

/-- A record of a setup still in the checkout binds, finished or not. -/
theorem recordUseSpec_resuming (kind recorded : SetupKind) (complete named : Bool) :
    recordUseSpec kind true (some (recorded, complete)) named =
      if recorded = kind then .merge else .otherSetup := by
  simp [recordUseSpec]

/-- Resuming a setup that left no record, asked to protect nothing, is
    refused: what it was to protect is unknown. -/
theorem recordUseSpec_unrecorded (kind : SetupKind) :
    recordUseSpec kind true none false = .unrecorded := by
  simp [recordUseSpec]

/-! ## The setup record: the model

`Item` is a pattern (`init`) or a path (`migrate`). The state is what
persists across processes: the record, whether `.transcrypt` exists in the
worktree (`config`), whether `HEAD` has a config (`committed`), what the
attributes protect, and the run in progress if any (one process at a time,
A28). A run's durable transitions are its steps; an interruption is
`crash`, at any point; a failure of a run that found no config rolls back
(`rollback*`, each step separately, so a crash can stop it anywhere); the
user may change the worktree config, the attributes and `HEAD` at any
time. The operator's start over (removing the record) is deliberately no
step: it is the authorization to drop what a setup was asked to protect. -/

/-- A setup record. -/
structure SetupRecord (Item : Type) where
  kind : SetupKind
  complete : Bool
  items : List Item

/-- The part of a record the decision reads. -/
def SetupRecord.shape {Item : Type} (r : SetupRecord Item) : SetupKind × Bool := (r.kind, r.complete)

/-- A run in progress: its command, its plan (what it protects), the
    record it found, whether it found no config (so a failure rolls it
    back), and whether it has saved its record. -/
structure SetupRun (Item : Type) where
  kind : SetupKind
  plan : List Item
  before : Option (SetupRecord Item)
  fresh : Bool
  saved : Bool

/-- What persists. -/
structure SetupState (Item : Type) where
  record : Option (SetupRecord Item)
  config : Bool
  committed : Bool
  protects : List Item
  run : Option (SetupRun Item)

variable {Item : Type}

/-- The record's items, none without a record. -/
def recordedItems : Option (SetupRecord Item) → List Item
  | none => []
  | some r => r.items

/-- The decision a run of `kind`, asked to protect `named`, makes in `s`. -/
def SetupState.use (s : SetupState Item) (kind : SetupKind) (named : List Item) : RecordUse :=
  recordUseSpec kind s.config (s.record.map SetupRecord.shape) (!named.isEmpty)

/-- A run's plan: what it was asked to protect and, when it merges, the
    recorded items it keeps (`keep`: `migrate` keeps the recorded paths
    still in the index; `init` keeps every pattern). -/
def setupPlan (use : RecordUse) (named recorded : List Item) (keep : Item → Bool) : List Item :=
  if use = .merge then named ++ recorded.filter keep else named

/-- One durable transition (or interruption) other than a run's
    completion, labelled with what it keeps of a merged record (everything,
    except for `migrate`'s start). -/
inductive SetupStep : (Item → Bool) → SetupState Item → SetupState Item → Prop
  /-- A run starts: refused (no transition) unless the decision is `fresh`
      or `merge`, and only while `HEAD` has no config. Nothing persists
      yet: the passphrase is read and checked before the record is saved. -/
  | start (s : SetupState Item) (kind : SetupKind) (named : List Item) (keep : Item → Bool)
      (hidle : s.run = none) (hhead : s.committed = false)
      (huse : s.use kind named = .fresh ∨ s.use kind named = .merge)
      (hkeep : kind = .init → ∀ i, keep i = true) :
      SetupStep keep s { s with run := some ⟨kind, setupPlan (s.use kind named) named (recordedItems s.record) keep,
        s.record, !s.config, false⟩ }
  /-- The run saves its record (atomically: a rename). -/
  | save (s : SetupState Item) (r : SetupRun Item) (hrun : s.run = some r) :
      SetupStep (fun _ => true) s
        { s with record := some ⟨r.kind, false, r.plan⟩, run := some { r with saved := true } }
  /-- The run writes `.transcrypt/config`. -/
  | writeConfig (s : SetupState Item) (r : SetupRun Item) (hrun : s.run = some r) (hsaved : r.saved = true) :
      SetupStep (fun _ => true) s { s with config := true }
  /-- The run protects one item of its plan. -/
  | protect (s : SetupState Item) (r : SetupRun Item) (i : Item) (hrun : s.run = some r) (hsaved : r.saved = true)
      (hi : i ∈ r.plan) :
      SetupStep (fun _ => true) s { s with protects := i :: s.protects }
  /-- The process stops, at any point. -/
  | crash (s : SetupState Item) (r : SetupRun Item) (hrun : s.run = some r) :
      SetupStep (fun _ => true) s { s with run := none }
  /-- A failed run that found no config removes the config. -/
  | rollbackConfig (s : SetupState Item) (r : SetupRun Item) (hrun : s.run = some r) (hfresh : r.fresh = true)
      (hsaved : r.saved = true) :
      SetupStep (fun _ => true) s { s with config := false }
  /-- ... restores the attributes (to anything: what it saved). -/
  | rollbackAttributes (s : SetupState Item) (r : SetupRun Item) (ps : List Item) (hrun : s.run = some r)
      (hfresh : r.fresh = true) (hsaved : r.saved = true) :
      SetupStep (fun _ => true) s { s with protects := ps }
  /-- ... and last puts back the record it found, or removes its own once
      the config is gone, and stops. -/
  | rollbackRecord (s : SetupState Item) (r : SetupRun Item) (hrun : s.run = some r) (hfresh : r.fresh = true)
      (hsaved : r.saved = true) :
      SetupStep (fun _ => true) s
        { s with record := (match r.before with
                            | some b => some b
                            | none => if s.config then s.record else none),
                 run := none }
  /-- The user changes the worktree config. -/
  | userConfig (s : SetupState Item) (b : Bool) : SetupStep (fun _ => true) s { s with config := b }
  /-- The user changes the attributes. -/
  | userAttributes (s : SetupState Item) (ps : List Item) : SetupStep (fun _ => true) s { s with protects := ps }
  /-- The user moves `HEAD`. -/
  | userHead (s : SetupState Item) (b : Bool) : SetupStep (fun _ => true) s { s with committed := b }

/-- A run completes: once everything it planned is protected, its record
    is marked complete (`init`: after `protect` of every pattern
    succeeded; `migrate`: after the conversion checked every selected path
    protected). -/
inductive SetupComplete : SetupState Item → SetupState Item → Prop
  | complete (s : SetupState Item) (r : SetupRun Item) (hrun : s.run = some r) (hsaved : r.saved = true)
      (hdone : ∀ i ∈ r.plan, i ∈ s.protects) :
      SetupComplete s { s with record := some ⟨r.kind, true, r.plan⟩, run := none }

/-- Any number of steps; `keep` is what all of them keep. -/
inductive SetupSteps : (Item → Bool) → SetupState Item → SetupState Item → Prop
  | refl (s : SetupState Item) : SetupSteps (fun _ => true) s s
  | step {keep keep' : Item → Bool} {s t u : SetupState Item} :
      SetupStep keep s t → SetupSteps keep' t u → SetupSteps (fun i => keep i && keep' i) s u

/-- **What is owed** to an unfinished record of `kind` holding at least
    `F`: the record stays unfinished, of `kind`, with at least `F`, and a
    run in progress is of `kind`, plans at least `F` and found such a
    record. -/
def Owes (kind : SetupKind) (F : List Item) (s : SetupState Item) : Prop :=
  (∃ items, s.record = some ⟨kind, false, items⟩ ∧ ∀ i ∈ F, i ∈ items) ∧
  ∀ r, s.run = some r → r.kind = kind ∧ (∀ i ∈ F, i ∈ r.plan) ∧
    ∃ items, r.before = some ⟨kind, false, items⟩ ∧ ∀ i ∈ F, i ∈ items

theorem owes_mono {kind : SetupKind} {F G : List Item} {s : SetupState Item} (h : Owes kind F s)
    (hsub : ∀ i ∈ G, i ∈ F) : Owes kind G s := by
  obtain ⟨⟨items, hr, hF⟩, hrun⟩ := h
  refine ⟨⟨items, hr, fun i hi => hF i (hsub i hi)⟩, fun r hr' => ?_⟩
  obtain ⟨hk, hp, b, hb, hbF⟩ := hrun r hr'
  exact ⟨hk, fun i hi => hp i (hsub i hi), b, hb, fun i hi => hbF i (hsub i hi)⟩

/-- A run started while an unfinished record of `kind` exists is of `kind`
    and merges it. -/
theorem start_merges {kind k : SetupKind} {F : List Item} {s : SetupState Item} {named : List Item}
    (h : Owes kind F s) (huse : s.use k named = .fresh ∨ s.use k named = .merge) :
    k = kind ∧ s.use k named = .merge := by
  obtain ⟨⟨items, hr, _⟩, _⟩ := h
  have hu : s.use k named = if kind = k then .merge else .otherSetup := by
    simp only [SetupState.use, hr, Option.map, SetupRecord.shape]
    exact recordUseSpec_unfinished k kind _ _
  by_cases hk : kind = k
  · exact ⟨hk.symm, by rw [hu, if_pos hk]⟩
  · rw [hu, if_neg hk] at huse
    rcases huse with h | h <;> cases h

/-- **Every step keeps what is owed**, less what a `migrate` start no
    longer finds in the index. -/
theorem owes_step {kind : SetupKind} {F : List Item} {keep : Item → Bool} {s t : SetupState Item}
    (h : Owes kind F s) (hstep : SetupStep keep s t) : Owes kind (F.filter keep) t := by
  have hfilt : ∀ i ∈ F.filter keep, i ∈ F := fun i hi => (List.mem_filter.mp hi).1
  cases hstep with
  | start s k named keep hidle hhead huse hkeep =>
    obtain ⟨hk, hmerge⟩ := start_merges h huse
    obtain ⟨⟨items, hr, hF⟩, _⟩ := h
    refine ⟨⟨items, hr, fun i hi => hF i (hfilt i hi)⟩, fun r hr' => ?_⟩
    simp only [Option.some.injEq] at hr'
    subst hr'
    refine ⟨hk, fun i hi => ?_, items, hr, fun i hi => hF i (hfilt i hi)⟩
    have ⟨hiF, hik⟩ := List.mem_filter.mp hi
    simp only [setupPlan, hmerge, recordedItems, hr]
    exact List.mem_append_right _ (List.mem_filter.mpr ⟨hF i hiF, hik⟩)
  | save s r hrun =>
    obtain ⟨_, hrunF⟩ := h
    obtain ⟨hk, hp, b, hb, hbF⟩ := hrunF r hrun
    refine ⟨⟨r.plan, by simp [hk], fun i hi => hp i (hfilt i hi)⟩, fun r' hr' => ?_⟩
    simp only [Option.some.injEq] at hr'
    subst hr'
    exact ⟨hk, fun i hi => hp i (hfilt i hi), b, hb, fun i hi => hbF i (hfilt i hi)⟩
  | writeConfig s r hrun hsaved => exact owes_mono h hfilt
  | protect s r i hrun hsaved hi => exact owes_mono h hfilt
  | crash s r hrun =>
    obtain ⟨hrec, _⟩ := owes_mono h hfilt
    exact ⟨hrec, fun r' hr' => by cases hr'⟩
  | rollbackConfig s r hrun hfresh hsaved => exact owes_mono h hfilt
  | rollbackAttributes s r ps hrun hfresh hsaved => exact owes_mono h hfilt
  | rollbackRecord s r hrun hfresh hsaved =>
    obtain ⟨_, hrunF⟩ := h
    obtain ⟨_, _, b, hb, hbF⟩ := hrunF r hrun
    refine ⟨⟨b, by simp [hb], fun i hi => hbF i (hfilt i hi)⟩, fun r' hr' => by cases hr'⟩
  | userConfig s b => exact owes_mono h hfilt
  | userAttributes s ps => exact owes_mono h hfilt
  | userHead s b => exact owes_mono h hfilt

/-- While an unfinished `init` record is owed, every step keeps every
    pattern: only `init` can start, and it merges the whole record. -/
theorem owes_init_keeps_all {F : List Item} {keep : Item → Bool} {s t : SetupState Item}
    (h : Owes .init F s) (hstep : SetupStep keep s t) : ∀ i, keep i = true := by
  cases hstep with
  | start s k named keep hidle hhead huse hkeep => exact hkeep (start_merges h huse).1
  | _ => intro _; rfl

/-- A completion while something is owed protects it, under a finished
    record of the same command that still lists it. -/
theorem owes_complete {kind : SetupKind} {F : List Item} {s t : SetupState Item}
    (h : Owes kind F s) (hdone : SetupComplete s t) :
    ∀ i ∈ F, i ∈ t.protects ∧ ∃ plan, t.record = some ⟨kind, true, plan⟩ ∧ i ∈ plan := by
  cases hdone with
  | complete r hrun hsaved hall =>
    obtain ⟨hk, hp, _⟩ := h.2 r hrun
    intro i hi
    exact ⟨hall i (hp i hi), r.plan, by simp [hk], hp i hi⟩

/-- Any number of steps keep what is owed, less what they did not keep. -/
theorem owes_steps {kind : SetupKind} {keep : Item → Bool} {s t : SetupState Item} (hsteps : SetupSteps keep s t) :
    ∀ F, Owes kind F s → Owes kind (F.filter keep) t := by
  induction hsteps with
  | refl s =>
    intro F h
    exact owes_mono h fun i hi => (List.mem_filter.mp hi).1
  | step hstep _ ih =>
    intro F h
    refine owes_mono (ih _ (owes_step h hstep)) fun i hi => ?_
    have ⟨hi', hk⟩ := List.mem_filter.mp hi
    simp only [Bool.and_eq_true] at hk
    exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hi', hk.1⟩, hk.2⟩

/-- While an unfinished `init` record is owed, any number of steps keep
    every pattern. -/
theorem owes_init_steps_keep_all {keep : Item → Bool} {s t : SetupState Item} (hsteps : SetupSteps keep s t) :
    ∀ F, Owes .init F s → ∀ i, keep i = true := by
  induction hsteps with
  | refl s => intro _ _ _; rfl
  | step hstep _ ih =>
    intro F h i
    simp only [Bool.and_eq_true]
    exact ⟨owes_init_keeps_all h hstep i, ih _ (owes_step h hstep) i⟩

/-- **Policy persistence.** Take a state in which a setup of `kind` saved
    its record with items `F` and is not finished (it was interrupted, at
    any point after saving it). Whatever happens next (runs started,
    interrupted at any transition, failed and rolled back; the user
    changing the config, the attributes or `HEAD`), the first run to
    complete protects every item of `F` that every run since kept, and
    records it. Only start over, which is no step, can release it. -/
theorem interrupted_setup_completes_with_its_policy {kind : SetupKind} {F : List Item}
    {keep : Item → Bool} {s t u : SetupState Item}
    (hrec : ∃ items, s.record = some ⟨kind, false, items⟩ ∧ ∀ i ∈ F, i ∈ items) (hrun : s.run = none)
    (hsteps : SetupSteps keep s t) (hdone : SetupComplete t u) :
    ∀ i ∈ F, keep i = true → i ∈ u.protects ∧ ∃ plan, u.record = some ⟨kind, true, plan⟩ ∧ i ∈ plan := by
  have howes : Owes kind F s := ⟨hrec, fun r hr => by rw [hrun] at hr; cases hr⟩
  intro i hi hk
  exact owes_complete (owes_steps hsteps F howes) hdone i (List.mem_filter.mpr ⟨hi, hk⟩)

/-- **Policy persistence for `init`.** An `init` interrupted after saving
    its record with patterns `F`: the first run to complete afterwards
    protects every pattern of `F`, whatever the reruns named. -/
theorem interrupted_init_completes_with_its_patterns {F : List Item} {keep : Item → Bool}
    {s t u : SetupState Item}
    (hrec : s.record = some ⟨.init, false, F⟩) (hrun : s.run = none)
    (hsteps : SetupSteps keep s t) (hdone : SetupComplete t u) :
    ∀ i ∈ F, i ∈ u.protects := by
  have howes : Owes .init F s := ⟨⟨F, hrec, fun _ h => h⟩, fun r hr => by rw [hrun] at hr; cases hr⟩
  intro i hi
  exact (interrupted_setup_completes_with_its_policy ⟨F, hrec, fun _ h => h⟩ hrun hsteps hdone i hi
    (owes_init_steps_keep_all hsteps F howes i)).1

/-- The record a run saves holds everything it was asked to protect. -/
theorem setupPlan_named (use : RecordUse) (named recorded : List Item) (keep : Item → Bool) :
    ∀ i ∈ named, i ∈ setupPlan use named recorded keep := by
  intro i hi
  unfold setupPlan
  split
  · exact List.mem_append_left _ hi
  · exact hi

/-- Resuming with no record and nothing named starts no run. -/
theorem no_start_unrecorded (s : SetupState Item) (kind : SetupKind)
    (hconfig : s.config = true) (hrec : s.record = none) :
    s.use kind [] ≠ .fresh ∧ s.use kind [] ≠ .merge := by
  simp [SetupState.use, hconfig, hrec, recordUseSpec]

/-! ## The rekey journal: the decisions -/

/-- Where a journaled index entry stands for a recovery. -/
inductive EntryRecovery | done | todo | changed
  deriving DecidableEq

/-- `staged`: the index holds a stage-0 entry at the journaled path with
    the journaled mode, with object id `oid`; the recovery ends at `want`
    from `other`. -/
def entryRecoverySpec {α : Type} [DecidableEq α] (staged : Bool) (oid want other : α) : EntryRecovery :=
  if staged = false then .changed
  else if oid = want then .done
  else if oid = other then .todo
  else .changed

/-- Where the worktree config stands. -/
inductive ConfigRecovery | done | write | changed
  deriving DecidableEq

def configRecoverySpec {α : Type} [DecidableEq α] (present : Bool) (worktree want other : α) : ConfigRecovery :=
  if present = false then .write
  else if worktree = want then .done
  else if worktree = other then .write
  else .changed

/-- What happens to a journaled worktree file. -/
inductive FileRecovery | relock | keep | check
  deriving DecidableEq

def fileRecoverySpec {α : Type} [DecidableEq α] (worktree want other : α) : FileRecovery :=
  if worktree = other then .relock
  else if worktree = want then .keep
  else .check

theorem entryRecoverySpec_ne_changed {α : Type} [DecidableEq α] {staged : Bool} {oid want other : α} :
    entryRecoverySpec staged oid want other ≠ .changed ↔ staged = true ∧ (oid = want ∨ oid = other) := by
  unfold entryRecoverySpec
  cases staged with
  | false => simp
  | true =>
    rw [if_neg (by simp)]
    by_cases h1 : oid = want
    · rw [if_pos h1]; simp [h1]
    · by_cases h2 : oid = other
      · rw [if_neg h1, if_pos h2]; simp [h2]
      · rw [if_neg h1, if_neg h2]; simp [h1, h2]

theorem entryRecoverySpec_todo {α : Type} [DecidableEq α] {staged : Bool} {oid want other : α} :
    entryRecoverySpec staged oid want other = .todo ↔ staged = true ∧ oid ≠ want ∧ oid = other := by
  unfold entryRecoverySpec
  cases staged with
  | false => simp
  | true =>
    rw [if_neg (by simp)]
    by_cases h1 : oid = want
    · rw [if_pos h1]; simp [h1]
    · by_cases h2 : oid = other
      · rw [if_neg h1, if_pos h2]; exact ⟨fun _ => ⟨rfl, h1, h2⟩, fun _ => rfl⟩
      · rw [if_neg h1, if_neg h2]; simp [h1, h2]

theorem configRecoverySpec_ne_changed {α : Type} [DecidableEq α] {worktree want other : α} :
    configRecoverySpec true worktree want other ≠ .changed ↔ (worktree = want ∨ worktree = other) := by
  unfold configRecoverySpec
  rw [if_neg (by simp)]
  by_cases h1 : worktree = want
  · rw [if_pos h1]; simp [h1]
  · by_cases h2 : worktree = other
    · rw [if_neg h1, if_pos h2]; simp [h2]
    · rw [if_neg h1, if_neg h2]; simp [h1, h2]

theorem fileRecoverySpec_relock {α : Type} [DecidableEq α] {worktree want other : α} :
    fileRecoverySpec worktree want other = .relock ↔ worktree = other := by
  unfold fileRecoverySpec
  by_cases h1 : worktree = other
  · rw [if_pos h1]; simp [h1]
  · rw [if_neg h1]
    by_cases h2 : worktree = want
    · rw [if_pos h2]; simp [h1]
    · rw [if_neg h2]; simp [h1]

/-! ## The rekey journal: the model

`Path`, `Mode` and `Oid` are Git's: a worktree file is named by the object
id of its content (Git's hash, A11). The index maps a path to its stage-0
entry (`none`: absent, or unmerged); the worktree config, the stored key
(by the config it is for) and the journal are separate. Every transition
is a function of the state; the theorems allow them in any order and any
number, so they cover an interruption between any two of them and reruns
of either direction. -/

/-- Which way a recovery goes: `--continue` or `--abort`. -/
inductive Direction | forward | backward
  deriving DecidableEq

/-- A journaled index entry: its mode, its object before and after. -/
structure JournalEntry (Mode Oid : Type) where
  mode : Mode
  old : Oid
  new : Oid

/-- The object a recovery in direction `d` ends at, and the one it replaces. -/
def JournalEntry.want {Mode Oid : Type} : Direction → JournalEntry Mode Oid → Oid
  | .forward, e => e.new
  | .backward, e => e.old

def JournalEntry.other {Mode Oid : Type} : Direction → JournalEntry Mode Oid → Oid
  | .forward, e => e.old
  | .backward, e => e.new

/-- The journal: the old and new worktree configs, and the entry at each
    journaled path (the file's distinct paths, read as a function). -/
structure Journal (Path Mode Oid : Type) where
  oldConfig : Oid
  newConfig : Oid
  entry : Path → Option (JournalEntry Mode Oid)

def Journal.wantConfig {Path Mode Oid : Type} (J : Journal Path Mode Oid) : Direction → Oid
  | .forward => J.newConfig
  | .backward => J.oldConfig

def Journal.otherConfig {Path Mode Oid : Type} (J : Journal Path Mode Oid) : Direction → Oid
  | .forward => J.oldConfig
  | .backward => J.newConfig

/-- What persists. -/
structure RekeyState (Path Mode Oid : Type) where
  index : Path → Option (Mode × Oid)
  worktree : Path → Option Oid
  config : Option Oid
  key : Option Oid
  journal : Option (Journal Path Mode Oid)

theorem RekeyState.ext' {Path Mode Oid : Type} {a b : RekeyState Path Mode Oid}
    (h1 : a.index = b.index) (h2 : a.worktree = b.worktree) (h3 : a.config = b.config) (h4 : a.key = b.key)
    (h5 : a.journal = b.journal) : a = b := by
  cases a; cases b; simp_all

variable {Path Mode Oid : Type} [DecidableEq Path] [DecidableEq Mode] [DecidableEq Oid]

/-- The decision for the entry `e` journaled at `p`, as the adapter calls
    it: staged with the journaled mode, and its object id. -/
def stagedState (s : RekeyState Path Mode Oid) (d : Direction) (p : Path) (e : JournalEntry Mode Oid) :
    EntryRecovery :=
  match s.index p with
  | none => .changed
  | some (m, o) => entryRecoverySpec (decide (m = e.mode)) o (e.want d) (e.other d)

/-- The decision for the worktree config. -/
def configState (J : Journal Path Mode Oid) (d : Direction) (s : RekeyState Path Mode Oid) : ConfigRecovery :=
  match s.config with
  | none => .write
  | some c => configRecoverySpec true c (J.wantConfig d) (J.otherConfig d)

/-- **The recovery's check**, made before any write: no journaled entry and
    not the worktree config changed. Refused otherwise, and then nothing is
    written. -/
def Admissible (J : Journal Path Mode Oid) (d : Direction) (s : RekeyState Path Mode Oid) : Prop :=
  (∀ p e, J.entry p = some e → stagedState s d p e ≠ .changed) ∧ configState J d s ≠ .changed

/-- Every journaled entry is staged as it was or as it becomes, and the
    worktree config is missing or one of the two. -/
def InJournal (J : Journal Path Mode Oid) (s : RekeyState Path Mode Oid) : Prop :=
  (∀ p e, J.entry p = some e → s.index p = some (e.mode, e.old) ∨ s.index p = some (e.mode, e.new)) ∧
  (s.config = none ∨ s.config = some J.oldConfig ∨ s.config = some J.newConfig)

omit [DecidableEq Path] in
/-- **The check does not depend on the direction**: both refuse exactly
    when a journaled entry or the worktree config is neither what `rekey`
    found nor what it wrote. -/
theorem admissible_iff (J : Journal Path Mode Oid) (d : Direction) (s : RekeyState Path Mode Oid) :
    Admissible J d s ↔ InJournal J s := by
  constructor
  · rintro ⟨hentries, hconfig⟩
    refine ⟨fun p e he => ?_, ?_⟩
    · have h := hentries p e he
      unfold stagedState at h
      cases hi : s.index p with
      | none => rw [hi] at h; exact absurd rfl h
      | some x =>
        obtain ⟨m, o⟩ := x
        rw [hi] at h
        obtain ⟨hm, ho⟩ := entryRecoverySpec_ne_changed.mp h
        have hm' : m = e.mode := of_decide_eq_true hm
        subst hm'
        cases d <;> simp only [JournalEntry.want, JournalEntry.other] at ho <;> rcases ho with rfl | rfl <;> simp
    · unfold configState at hconfig
      cases hc : s.config with
      | none => exact Or.inl rfl
      | some c =>
        rw [hc] at hconfig
        have h := configRecoverySpec_ne_changed.mp hconfig
        cases d <;> simp only [Journal.wantConfig, Journal.otherConfig] at h <;> rcases h with rfl | rfl <;> simp
  · rintro ⟨hentries, hconfig⟩
    refine ⟨fun p e he => ?_, ?_⟩
    · unfold stagedState
      rcases hentries p e he with h | h <;> rw [h] <;> apply entryRecoverySpec_ne_changed.mpr <;>
        cases d <;> simp [JournalEntry.want, JournalEntry.other]
    · unfold configState
      rcases hconfig with h | h | h <;> rw [h]
      · simp
      all_goals
        apply configRecoverySpec_ne_changed.mpr
        cases d <;> simp [Journal.wantConfig, Journal.otherConfig]

/-! ### The transitions -/

/-- The stored key becomes the one for the config the recovery ends with
    (the stored one reused, or derived from that config's passphrase and
    authenticated, before anything is written). -/
def storeKey (J : Journal Path Mode Oid) (d : Direction) (s : RekeyState Path Mode Oid) : RekeyState Path Mode Oid :=
  { s with key := some (J.wantConfig d) }

/-- The worktree config is written (atomically) when the decision says so. -/
def writeConfig (J : Journal Path Mode Oid) (d : Direction) (s : RekeyState Path Mode Oid) :
    RekeyState Path Mode Oid :=
  if configState J d s = .write then { s with config := some (J.wantConfig d) } else s

/-- One index update (`update-index --index-info`, atomic by Git's
    `index.lock`, A29) stages exactly the entries still to do. -/
def stageAll (J : Journal Path Mode Oid) (d : Direction) (s : RekeyState Path Mode Oid) :
    RekeyState Path Mode Oid :=
  { s with index := fun p =>
      match J.entry p with
      | some e => if stagedState s d p e = .todo then some (e.mode, e.want d) else s.index p
      | none => s.index p }

/-- The worktree file at `p` after the recovery: the record being replaced
    becomes the other one; anything else stays. Never the worktree config
    (`cfgPath`), which `writeConfig` handles. -/
def relocked (cfgPath : Path) (J : Journal Path Mode Oid) (d : Direction) (s : RekeyState Path Mode Oid)
    (p : Path) : Option Oid :=
  match J.entry p, s.worktree p with
  | some e, some w => if p ≠ cfgPath ∧ fileRecoverySpec w (e.want d) (e.other d) = .relock then some (e.want d)
                      else some w
  | _, w => w

/-- The files selected by `sel` are relocked (each by its own atomic
    replacement, in any order). -/
def relockSome (cfgPath : Path) (J : Journal Path Mode Oid) (d : Direction) (sel : Path → Bool)
    (s : RekeyState Path Mode Oid) : RekeyState Path Mode Oid :=
  { s with worktree := fun p => if sel p then relocked cfgPath J d s p else s.worktree p }

/-- The journal is removed, last. -/
def finish (s : RekeyState Path Mode Oid) : RekeyState Path Mode Oid := { s with journal := none }

/-- A complete recovery, in the adapter's order. -/
def recoverAll (cfgPath : Path) (J : Journal Path Mode Oid) (d : Direction) (s : RekeyState Path Mode Oid) :
    RekeyState Path Mode Oid :=
  finish (relockSome cfgPath J d (fun _ => true) (stageAll J d (writeConfig J d (storeKey J d s))))

/-! ### What a recovery does -/

omit [DecidableEq Path] [DecidableEq Mode] [DecidableEq Oid] in
theorem storeKey_index (J : Journal Path Mode Oid) (d : Direction) (s : RekeyState Path Mode Oid) :
    (storeKey J d s).index = s.index ∧ (storeKey J d s).worktree = s.worktree ∧
      (storeKey J d s).config = s.config := ⟨rfl, rfl, rfl⟩

omit [DecidableEq Path] [DecidableEq Mode] in
theorem writeConfig_fields (J : Journal Path Mode Oid) (d : Direction) (s : RekeyState Path Mode Oid) :
    (writeConfig J d s).index = s.index ∧ (writeConfig J d s).worktree = s.worktree ∧
      (writeConfig J d s).key = s.key ∧ (writeConfig J d s).journal = s.journal := by
  unfold writeConfig; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

omit [DecidableEq Path] in
/-- An admissible state's journaled entry is either done or to do. -/
theorem stagedState_of_admissible {J : Journal Path Mode Oid} {d : Direction} {s : RekeyState Path Mode Oid}
    (h : Admissible J d s) {p : Path} {e : JournalEntry Mode Oid} (he : J.entry p = some e) :
    (stagedState s d p e = .todo ∧ s.index p = some (e.mode, e.other d)) ∨
    (stagedState s d p e ≠ .todo ∧ s.index p = some (e.mode, e.want d)) := by
  have hne := h.1 p e he
  unfold stagedState at hne ⊢
  cases hi : s.index p with
  | none => rw [hi] at hne; exact absurd rfl hne
  | some x =>
    obtain ⟨m, o⟩ := x
    rw [hi] at hne
    obtain ⟨hm, ho⟩ := entryRecoverySpec_ne_changed.mp hne
    have hm' : m = e.mode := of_decide_eq_true hm
    subst hm'
    by_cases hw : o = e.want d
    · right
      subst hw
      exact ⟨by simp [entryRecoverySpec], rfl⟩
    · left
      have hoo : o = e.other d := ho.resolve_left hw
      subst hoo
      exact ⟨by simp [entryRecoverySpec, hw], rfl⟩

omit [DecidableEq Path] in
/-- After a recovery's index update, every journaled entry is staged as the
    recovery ends it, and every other entry is untouched. -/
theorem stageAll_index {J : Journal Path Mode Oid} {d : Direction} {s : RekeyState Path Mode Oid}
    (h : Admissible J d s) (p : Path) :
    (stageAll J d s).index p = match J.entry p with
      | some e => some (e.mode, e.want d)
      | none => s.index p := by
  simp only [stageAll]
  cases he : J.entry p with
  | none => rfl
  | some e =>
    rcases stagedState_of_admissible h he with ⟨ht, _⟩ | ⟨ht, hi⟩
    · simp [ht]
    · simp [ht, hi]

omit [DecidableEq Path] in
/-- The worktree config after `writeConfig`, from an admissible state. -/
theorem writeConfig_config {J : Journal Path Mode Oid} {d : Direction} {s : RekeyState Path Mode Oid}
    (h : Admissible J d s) : (writeConfig J d s).config = some (J.wantConfig d) := by
  have hc := h.2
  unfold writeConfig
  by_cases hw : configState J d s = .write
  · rw [if_pos hw]
  · rw [if_neg hw]
    unfold configState at hc hw
    cases hs : s.config with
    | none => rw [hs] at hw; exact absurd rfl hw
    | some c =>
      by_cases h1 : c = J.wantConfig d
      · rw [h1]
      · exfalso
        by_cases h2 : c = J.otherConfig d <;> simp_all [configRecoverySpec]

omit [DecidableEq Path] in
theorem admissible_storeKey {J : Journal Path Mode Oid} {d d' : Direction} {s : RekeyState Path Mode Oid}
    (h : Admissible J d s) : Admissible J d (storeKey J d' s) := h

omit [DecidableEq Path] in
theorem admissible_writeConfig {J : Journal Path Mode Oid} {d d' : Direction} {s : RekeyState Path Mode Oid}
    (h : Admissible J d s) : Admissible J d (writeConfig J d' s) := by
  rw [admissible_iff] at h ⊢
  refine ⟨fun p e he => (writeConfig_fields J d' s).1 ▸ h.1 p e he, ?_⟩
  have hc : (writeConfig J d' s).config = some (J.wantConfig d') :=
    writeConfig_config ((admissible_iff J d' s).mpr h)
  rw [hc]
  cases d' <;> simp [Journal.wantConfig]

omit [DecidableEq Path] in
theorem admissible_stageAll {J : Journal Path Mode Oid} {d d' : Direction} {s : RekeyState Path Mode Oid}
    (h : Admissible J d s) : Admissible J d (stageAll J d' s) := by
  have h' : Admissible J d' s := (admissible_iff J d' s).mpr ((admissible_iff J d s).mp h)
  rw [admissible_iff] at h ⊢
  refine ⟨fun p e he => ?_, h.2⟩
  rw [stageAll_index h' p, he]
  cases d' <;> simp [JournalEntry.want]

theorem admissible_relockSome {J : Journal Path Mode Oid} {d d' : Direction} {cfgPath : Path} {sel : Path → Bool}
    {s : RekeyState Path Mode Oid} (h : Admissible J d s) : Admissible J d (relockSome cfgPath J d' sel s) := h

omit [DecidableEq Mode] in
/-- **Relocking commutes with any later recovery.** Relocking first in
    direction `d` and then fully in `d'` relocks each file exactly as `d'`
    alone would: a file `d` turned into its `want` is turned back by `d'`
    when the directions differ. -/
theorem relocked_relocked (cfgPath : Path) (J : Journal Path Mode Oid) (d d' : Direction) (sel : Path → Bool)
    (s : RekeyState Path Mode Oid) (p : Path) :
    relocked cfgPath J d' (relockSome cfgPath J d sel s) p = relocked cfgPath J d' s p := by
  by_cases hs : sel p = false
  · simp [relocked, relockSome, hs]
  have hs' : sel p = true := by cases h : sel p <;> simp_all
  unfold relocked
  simp only [relockSome, hs', if_true]
  cases he : J.entry p with
  | none => simp [relocked, he]
  | some e =>
    cases hw : s.worktree p with
    | none => simp [relocked, he, hw]
    | some w =>
      by_cases hc : p = cfgPath
      · subst hc; simp [relocked, he, hw]
      have key : ∀ a b : Direction, e.want b = e.other a ∨ a = b ∨ e.old = e.new := by
        intro a b; cases a <;> cases b <;> simp [JournalEntry.want, JournalEntry.other]
      cases d <;> cases d' <;>
        by_cases h1 : w = e.old <;> by_cases h2 : w = e.new <;> by_cases h3 : e.old = e.new <;>
        simp_all [relocked, fileRecoverySpec, JournalEntry.want, JournalEntry.other]

/-- **A complete recovery, characterized.** From any state the check
    admits, a recovery in direction `d` stages every journaled entry as `d`
    ends it and leaves every other index entry as it was; writes the
    worktree config and keeps the key of the config `d` ends with; relocks
    exactly the files holding the record being replaced and leaves every
    other worktree file as it was; and removes the journal. -/
theorem recoverAll_spec {cfgPath : Path} {J : Journal Path Mode Oid} {d : Direction} {s : RekeyState Path Mode Oid}
    (h : Admissible J d s) :
    let t := recoverAll cfgPath J d s
    (∀ p, t.index p = match J.entry p with
      | some e => some (e.mode, e.want d)
      | none => s.index p) ∧
    (∀ p, t.worktree p = relocked cfgPath J d s p) ∧
    t.config = some (J.wantConfig d) ∧ t.key = some (J.wantConfig d) ∧ t.journal = none := by
  have h1 : Admissible J d (storeKey J d s) := admissible_storeKey h
  have h2 : Admissible J d (writeConfig J d (storeKey J d s)) := admissible_writeConfig h1
  refine ⟨fun p => ?_, fun p => ?_, ?_, ?_, rfl⟩
  · show (stageAll J d (writeConfig J d (storeKey J d s))).index p = _
    rw [stageAll_index h2 p]
    cases J.entry p <;> simp [(writeConfig_fields J d _).1, storeKey]
  · show relocked cfgPath J d (stageAll J d (writeConfig J d (storeKey J d s))) p = _
    have hw : (stageAll J d (writeConfig J d (storeKey J d s))).worktree = s.worktree := by
      simp [stageAll, (writeConfig_fields J d _).2.1, storeKey]
    simp only [relocked, hw]
  · show (stageAll J d (writeConfig J d (storeKey J d s))).config = _
    simp only [stageAll]
    exact writeConfig_config h1
  · show (writeConfig J d (storeKey J d s)).key = _
    rw [(writeConfig_fields J d _).2.2.1]; rfl

/-- The result of a complete recovery depends only on the journaled index
    entries and worktree files it starts from, and the other entries and
    files. -/
theorem recoverAll_congr {cfgPath : Path} {J : Journal Path Mode Oid} {d : Direction} {s s' : RekeyState Path Mode Oid}
    (h : Admissible J d s) (h' : Admissible J d s')
    (hindex : ∀ p, J.entry p = none → s'.index p = s.index p)
    (hworktree : ∀ p, relocked cfgPath J d s' p = relocked cfgPath J d s p) :
    recoverAll cfgPath J d s' = recoverAll cfgPath J d s := by
  obtain ⟨i1, w1, c1, k1, j1⟩ := recoverAll_spec (cfgPath := cfgPath) h
  obtain ⟨i2, w2, c2, k2, j2⟩ := recoverAll_spec (cfgPath := cfgPath) h'
  apply RekeyState.ext'
  · funext p
    rw [i1, i2]
    cases he : J.entry p
    · exact hindex p he
    · rfl
  · funext p; rw [w1, w2, hworktree]
  · rw [c1, c2]
  · rw [k1, k2]
  · rw [j1, j2]

/-- **Every transition, in either direction, leaves what any later
    complete recovery does unchanged.** So a recovery (or `rekey`)
    interrupted after any of its writes, and then completed in either
    direction, ends exactly as that direction would have from before those
    writes. -/
theorem recoverAll_transition {cfgPath : Path} {J : Journal Path Mode Oid} {d d' : Direction}
    {s : RekeyState Path Mode Oid} (h : Admissible J d s) (sel : Path → Bool) :
    recoverAll cfgPath J d' (storeKey J d s) = recoverAll cfgPath J d' s ∧
    recoverAll cfgPath J d' (writeConfig J d s) = recoverAll cfgPath J d' s ∧
    recoverAll cfgPath J d' (stageAll J d s) = recoverAll cfgPath J d' s ∧
    recoverAll cfgPath J d' (relockSome cfgPath J d sel s) = recoverAll cfgPath J d' s := by
  have h' : Admissible J d' s := (admissible_iff J d' s).mpr ((admissible_iff J d s).mp h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact recoverAll_congr h' (admissible_storeKey h') (fun _ _ => rfl) (fun _ => rfl)
  · exact recoverAll_congr h' (admissible_writeConfig h')
      (fun p _ => by rw [(writeConfig_fields J d s).1])
      (fun p => by simp only [relocked, (writeConfig_fields J d s).2.1])
  · refine recoverAll_congr h' (admissible_stageAll h') (fun p he => ?_) (fun p => ?_)
    · rw [stageAll_index h p, he]
    · simp only [relocked, stageAll]
  · exact recoverAll_congr h' (admissible_relockSome h') (fun _ _ => rfl)
      (fun p => relocked_relocked cfgPath J d d' sel s p)

/-! ### An interrupted `rekey` -/

/-- `rekey` writes its journal first, from the state it starts in (after
    its new records are written as Git objects: content-addressed, they
    change nothing here). -/
def startJournal (J : Journal Path Mode Oid) (s : RekeyState Path Mode Oid) : RekeyState Path Mode Oid :=
  { s with journal := some J }

/-- A change the user makes meanwhile to anything but the journaled entries
    and files, the worktree config, the key and the journal: other index
    entries (including changes only in the index) and other worktree files. -/
def UnrelatedChange (J : Journal Path Mode Oid) (s s' : RekeyState Path Mode Oid) : Prop :=
  (∀ p, J.entry p ≠ none → s'.index p = s.index p ∧ s'.worktree p = s.worktree p) ∧
  s'.config = s.config ∧ s'.key = s.key ∧ s'.journal = s.journal

/-- **The states an interrupted `rekey` can lead to.** `rekey`'s own writes
    (journal; index; worktree config; key; in that order, each one atomic,
    and any of them the last before an interruption) are the forward
    transitions; any number of `--continue` and `--abort` runs, each
    interrupted after any of its writes (all of them made only after its
    check admitted the state), add transitions in either direction; and the
    user may change other paths at any time (`quiet := false`). -/
inductive Interrupted (cfgPath : Path) (J : Journal Path Mode Oid) (s0 : RekeyState Path Mode Oid) :
    Bool → RekeyState Path Mode Oid → Prop
  | start : Interrupted cfgPath J s0 true (startJournal J s0)
  | storeKey {quiet : Bool} {s : RekeyState Path Mode Oid} (d : Direction) :
      Interrupted cfgPath J s0 quiet s → Admissible J d s → Interrupted cfgPath J s0 quiet (storeKey J d s)
  | writeConfig {quiet : Bool} {s : RekeyState Path Mode Oid} (d : Direction) :
      Interrupted cfgPath J s0 quiet s → Admissible J d s → Interrupted cfgPath J s0 quiet (writeConfig J d s)
  | stageAll {quiet : Bool} {s : RekeyState Path Mode Oid} (d : Direction) :
      Interrupted cfgPath J s0 quiet s → Admissible J d s → Interrupted cfgPath J s0 quiet (stageAll J d s)
  | relock {quiet : Bool} {s : RekeyState Path Mode Oid} (d : Direction) (sel : Path → Bool) :
      Interrupted cfgPath J s0 quiet s → Admissible J d s →
      Interrupted cfgPath J s0 quiet (relockSome cfgPath J d sel s)
  | user {quiet : Bool} {s s' : RekeyState Path Mode Oid} :
      Interrupted cfgPath J s0 quiet s → UnrelatedChange J s s' → Interrupted cfgPath J s0 false s'

/-- What `rekey` found: each journaled entry staged as it was, its worktree
    config the journal's old one (A29: the journal is written from the
    index it replaces), and no journal yet. -/
def RekeyStart (J : Journal Path Mode Oid) (s0 : RekeyState Path Mode Oid) : Prop :=
  (∀ p e, J.entry p = some e → s0.index p = some (e.mode, e.old)) ∧ s0.config = some J.oldConfig

omit [DecidableEq Path] in
theorem admissible_start {J : Journal Path Mode Oid} {s0 : RekeyState Path Mode Oid} (h : RekeyStart J s0)
    (d : Direction) : Admissible J d (startJournal J s0) := by
  rw [admissible_iff]
  exact ⟨fun p e he => Or.inl (h.1 p e he), Or.inr (Or.inl h.2)⟩

/-- **An interrupted `rekey` can always be finished or undone.** In every
    state an interruption can lead to, both directions' checks pass, the
    journal is still there, and a complete recovery in either direction
    does at every journaled path, the worktree config and the key exactly
    what it would have done right after `rekey` wrote its journal, and
    leaves every other index entry and worktree file as the state has
    them. Without the user's changes meanwhile (`quiet`) the result is that
    of the recovery from right after the journal, exactly. -/
theorem interrupted_rekey_recovers {cfgPath : Path} {J : Journal Path Mode Oid} {s0 s : RekeyState Path Mode Oid}
    {quiet : Bool} (hstart : RekeyStart J s0) (h : Interrupted cfgPath J s0 quiet s) (d : Direction) :
    Admissible J d s ∧ s.journal = some J ∧
    (∀ p, J.entry p ≠ none →
      (recoverAll cfgPath J d s).index p = (recoverAll cfgPath J d (startJournal J s0)).index p ∧
      (recoverAll cfgPath J d s).worktree p = (recoverAll cfgPath J d (startJournal J s0)).worktree p) ∧
    (∀ p, J.entry p = none → (recoverAll cfgPath J d s).index p = s.index p ∧
      (recoverAll cfgPath J d s).worktree p = s.worktree p) ∧
    (recoverAll cfgPath J d s).config = some (J.wantConfig d) ∧
    (recoverAll cfgPath J d s).key = some (J.wantConfig d) ∧ (recoverAll cfgPath J d s).journal = none ∧
    (quiet = true → recoverAll cfgPath J d s = recoverAll cfgPath J d (startJournal J s0)) := by
  -- The invariant: admitted, journal present, and every complete recovery
  -- agrees at the journaled paths with the one from the start (equal when quiet).
  have inv : ∀ {q : Bool} {s : RekeyState Path Mode Oid}, Interrupted cfgPath J s0 q s →
      Admissible J d s ∧ s.journal = some J ∧
      (∀ d', ∀ p, J.entry p ≠ none →
        (recoverAll cfgPath J d' s).index p = (recoverAll cfgPath J d' (startJournal J s0)).index p ∧
        (recoverAll cfgPath J d' s).worktree p = (recoverAll cfgPath J d' (startJournal J s0)).worktree p) ∧
      (q = true → ∀ d', recoverAll cfgPath J d' s = recoverAll cfgPath J d' (startJournal J s0)) := by
    intro q s hs
    induction hs with
    | start =>
      exact ⟨admissible_start hstart d, rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩
    | storeKey d1 _ had ih =>
      obtain ⟨ha, hj, hagree, hq⟩ := ih
      have e := fun d' => (recoverAll_transition (cfgPath := cfgPath) (d' := d') had (fun _ => true)).1
      exact ⟨admissible_storeKey ha, hj, fun d' p hp => by rw [e d']; exact hagree d' p hp,
        fun hqq d' => by rw [e d']; exact hq hqq d'⟩
    | writeConfig d1 _ had ih =>
      obtain ⟨ha, hj, hagree, hq⟩ := ih
      have e := fun d' => (recoverAll_transition (cfgPath := cfgPath) (d' := d') had (fun _ => true)).2.1
      exact ⟨admissible_writeConfig ha, by rw [(writeConfig_fields J d1 _).2.2.2]; exact hj,
        fun d' p hp => by rw [e d']; exact hagree d' p hp, fun hqq d' => by rw [e d']; exact hq hqq d'⟩
    | stageAll d1 _ had ih =>
      obtain ⟨ha, hj, hagree, hq⟩ := ih
      have e := fun d' => (recoverAll_transition (cfgPath := cfgPath) (d' := d') had (fun _ => true)).2.2.1
      exact ⟨admissible_stageAll ha, hj, fun d' p hp => by rw [e d']; exact hagree d' p hp,
        fun hqq d' => by rw [e d']; exact hq hqq d'⟩
    | relock d1 sel _ had ih =>
      obtain ⟨ha, hj, hagree, hq⟩ := ih
      have e := fun d' => (recoverAll_transition (cfgPath := cfgPath) (d' := d') had sel).2.2.2
      exact ⟨admissible_relockSome ha, hj, fun d' p hp => by rw [e d']; exact hagree d' p hp,
        fun hqq d' => by rw [e d']; exact hq hqq d'⟩
    | user _ hchange ih =>
      rename_i q1 s1 s2 _
      obtain ⟨ha, hj, hagree, _⟩ := ih
      obtain ⟨hpaths, hc, hk, hjj⟩ := hchange
      have ha2 : Admissible J d s2 := by
        rw [admissible_iff] at ha ⊢
        refine ⟨fun p e he => ?_, by rw [hc]; exact ha.2⟩
        rw [(hpaths p (by rw [he]; simp)).1]
        exact ha.1 p e he
      refine ⟨ha2, by rw [hjj]; exact hj, fun d' p hp => ?_, fun hf => by cases hf⟩
      have had1 : Admissible J d' s1 := (admissible_iff J d' s1).mpr ((admissible_iff J d s1).mp ha)
      have had2 : Admissible J d' s2 := (admissible_iff J d' s2).mpr ((admissible_iff J d s2).mp ha2)
      obtain ⟨i1, w1, _⟩ := recoverAll_spec (cfgPath := cfgPath) had1
      obtain ⟨i2, w2, _⟩ := recoverAll_spec (cfgPath := cfgPath) had2
      obtain ⟨hi, hw⟩ := hpaths p hp
      refine ⟨?_, ?_⟩
      · rw [i2, ← (hagree d' p hp).1, i1]
        cases he : J.entry p with
        | none => exact absurd he hp
        | some e => rfl
      · rw [w2, ← (hagree d' p hp).2, w1]
        simp only [relocked, hw]
  obtain ⟨ha, hj, hagree, hq⟩ := inv h
  obtain ⟨i, w, c, k, j⟩ := recoverAll_spec (cfgPath := cfgPath) ha
  refine ⟨ha, hj, hagree d, fun p hp => ⟨?_, ?_⟩, c, k, j, fun hqq => hq hqq d⟩
  · rw [i, hp]
  · rw [w]; simp [relocked, hp]

/-- What `rekey` started from, for `--abort` to put back: besides
    `RekeyStart`, the key of the old config is stored, and no worktree file
    at a journaled path holds a new record (they are fresh: a new salt and
    key; `rekey` decrypts every protected file before it starts). -/
def RekeyFound (J : Journal Path Mode Oid) (s0 : RekeyState Path Mode Oid) : Prop :=
  RekeyStart J s0 ∧ s0.key = some J.oldConfig ∧ s0.journal = none ∧
  ∀ p e, J.entry p = some e → s0.worktree p ≠ some e.new

/-- `--abort` right after the journal was written gives back exactly the
    state `rekey` started from. -/
theorem abort_start {cfgPath : Path} {J : Journal Path Mode Oid} {s0 : RekeyState Path Mode Oid}
    (h : RekeyFound J s0) : recoverAll cfgPath J .backward (startJournal J s0) = s0 := by
  obtain ⟨hstart, hkey, hjournal, hfresh⟩ := h
  obtain ⟨i, w, c, k, j⟩ := recoverAll_spec (cfgPath := cfgPath) (admissible_start hstart .backward)
  apply RekeyState.ext'
  · funext p
    rw [i]
    cases he : J.entry p with
    | none => rfl
    | some e => rw [hstart.1 p e he]; rfl
  · funext p
    rw [w]
    unfold relocked
    cases he : J.entry p with
    | none => rfl
    | some e =>
      simp only [startJournal]
      cases hw : s0.worktree p with
      | none => rfl
      | some x =>
        have hx : x ≠ e.new := fun hxe => hfresh p e he (by rw [hw, hxe])
        by_cases h1 : x = e.old <;> simp [fileRecoverySpec, JournalEntry.want, JournalEntry.other, hx, h1]
  · rw [c, hstart.2]; rfl
  · rw [k, hkey]; rfl
  · rw [j, hjournal]

/-- **`rekey --abort` is lossless.** After `rekey` was interrupted at any
    point, and any number of `--continue` and `--abort` runs were
    interrupted after any of their writes, a complete `--abort` puts back
    exactly what `rekey` found at every journaled index entry and worktree
    file, the worktree config and the key, removes the journal, and leaves
    every other index entry (including changes only in the index) and
    worktree file exactly as the user left them. -/
theorem interrupted_rekey_abort_restores {cfgPath : Path} {J : Journal Path Mode Oid}
    {s0 s : RekeyState Path Mode Oid} {quiet : Bool} (hfound : RekeyFound J s0)
    (h : Interrupted cfgPath J s0 quiet s) :
    let t := recoverAll cfgPath J .backward s
    (∀ p, J.entry p ≠ none → t.index p = s0.index p ∧ t.worktree p = s0.worktree p) ∧
    (∀ p, J.entry p = none → t.index p = s.index p ∧ t.worktree p = s.worktree p) ∧
    t.config = s0.config ∧ t.key = s0.key ∧ t.journal = s0.journal := by
  obtain ⟨_, _, hagree, hother, hc, hk, hj, _⟩ := interrupted_rekey_recovers hfound.1 h .backward
  have hs0 := abort_start (cfgPath := cfgPath) hfound
  refine ⟨fun p hp => ?_, hother, ?_, ?_, ?_⟩
  · rw [(hagree p hp).1, (hagree p hp).2, hs0]; exact ⟨rfl, rfl⟩
  · rw [hc, hfound.1.2]; rfl
  · rw [hk, hfound.2.1]; rfl
  · rw [hj, hfound.2.2.1]

/-- **Without the user's changes, `--abort` restores the state `rekey`
    started from, exactly.** -/
theorem interrupted_rekey_abort_restores_exactly {cfgPath : Path} {J : Journal Path Mode Oid}
    {s0 s : RekeyState Path Mode Oid} (hfound : RekeyFound J s0) (h : Interrupted cfgPath J s0 true s) :
    recoverAll cfgPath J .backward s = s0 := by
  obtain ⟨_, _, _, _, _, _, _, hq⟩ := interrupted_rekey_recovers hfound.1 h .backward
  rw [hq rfl, abort_start hfound]

/-- **`rekey --continue` finishes what `rekey` would have done.** From any
    state an interruption leads to without the user's changes, a complete
    `--continue` ends exactly as `rekey` itself would have: every journaled
    entry staged as new, the new config written and its key stored, the
    journal removed (and, `rekey` having decrypted every protected file, no
    worktree file relocked). -/
theorem interrupted_rekey_continue_finishes {cfgPath : Path} {J : Journal Path Mode Oid}
    {s0 s : RekeyState Path Mode Oid} (hfound : RekeyFound J s0) (h : Interrupted cfgPath J s0 true s)
    (hplain : ∀ p e, J.entry p = some e → s0.worktree p ≠ some e.old) :
    recoverAll cfgPath J .forward s =
      finish (storeKey J .forward (writeConfig J .forward (stageAll J .forward (startJournal J s0)))) := by
  obtain ⟨_, _, _, _, _, _, _, hq⟩ := interrupted_rekey_recovers hfound.1 h .forward
  rw [hq rfl]
  have ha := admissible_start hfound.1 .forward
  obtain ⟨i, w, c, k, j⟩ := recoverAll_spec (cfgPath := cfgPath) ha
  have ha1 : Admissible J .forward (stageAll J .forward (startJournal J s0)) := admissible_stageAll ha
  apply RekeyState.ext'
  · funext p
    rw [i]
    have hx : (finish (storeKey J .forward (writeConfig J .forward (stageAll J .forward (startJournal J s0))))).index =
        (stageAll J .forward (startJournal J s0)).index := (writeConfig_fields J .forward _).1
    rw [hx, stageAll_index ha p]
  · funext p
    rw [w]
    have hx : (finish (storeKey J .forward (writeConfig J .forward (stageAll J .forward (startJournal J s0))))).worktree =
        (startJournal J s0).worktree := (writeConfig_fields J .forward _).2.1
    rw [hx]
    unfold relocked
    cases he : J.entry p with
    | none => rfl
    | some e =>
      simp only [startJournal]
      cases hw : s0.worktree p with
      | none => rfl
      | some x =>
        have hx : x ≠ e.old := fun hxe => hplain p e he (by rw [hw, hxe])
        by_cases h1 : x = e.new <;> simp [fileRecoverySpec, JournalEntry.want, JournalEntry.other, hx, h1]
  · rw [c]
    show _ = (writeConfig J .forward (stageAll J .forward (startJournal J s0))).config
    rw [writeConfig_config ha1]
  · rw [k]; rfl
  · rw [j]; rfl

/-! ## The pre-push verdict -/

/-- What the pre-push hook does after the audit accepted every pushed
    commit. -/
inductive PushAdmission | allow | warn | refuse
  deriving DecidableEq

/-- `authenticated`: every protected file of the pushed commits was
    authenticated (or none needed the key); `required`:
    `transcrypt.requireAuthenticatedPush` is set. -/
def pushAdmissionSpec (authenticated required : Bool) : PushAdmission :=
  if authenticated = true then .allow else if required = true then .refuse else .warn

/-- A push that requires authentication is admitted only when every
    protected file was authenticated. -/
theorem pushAdmissionSpec_required {authenticated : Bool} (h : pushAdmissionSpec authenticated true ≠ .refuse) :
    authenticated = true := by
  cases authenticated <;> simp_all [pushAdmissionSpec]

/-- `transcrypt.requireAuthenticatedPush` as the hook reads it: not set in
    any scope, set to a value Git reads as false, or set to anything else
    (a misspelt value included). -/
inductive PushSetting | unset | disabled | enabled
  deriving DecidableEq

/-- **Authenticated pushes are the default.** Only an explicit false
    setting lets the hook accept records it could not authenticate. -/
def authenticatedPushRequiredSpec : PushSetting → Bool
  | .disabled => false
  | .unset | .enabled => true

theorem authenticatedPushRequiredSpec_false {s : PushSetting} :
    authenticatedPushRequiredSpec s = false ↔ s = .disabled := by
  cases s <;> simp [authenticatedPushRequiredSpec]

/-- **Unless explicitly disabled, an admitted push authenticated every new
    or changed record**: with any setting but `disabled`, the verdict is
    not `refuse` only when the audit authenticated. -/
theorem pushAdmissionSpec_default {authenticated : Bool} {s : PushSetting} (hs : s ≠ .disabled)
    (h : pushAdmissionSpec authenticated (authenticatedPushRequiredSpec s) ≠ .refuse) : authenticated = true := by
  cases s <;> first | exact absurd rfl hs | exact pushAdmissionSpec_required h

/-- **The committed policy's protection, for publication checks**:
    `committed` is what the committed (or staged) `.gitattributes` files
    alone select, `effective` what Git selects with every local attribute
    source applied. -/
def admissionSelectedSpec (committed effective : Bool) : Bool :=
  committed || effective

/-- **No local attribute source unprotects a committed path**: whatever
    the local sources make of it. -/
theorem admissionSelectedSpec_committed {effective : Bool} : admissionSelectedSpec true effective = true := by
  simp [admissionSelectedSpec]

/-- Local sources may add protection. -/
theorem admissionSelectedSpec_effective {committed : Bool} : admissionSelectedSpec committed true = true := by
  simp [admissionSelectedSpec]

end Transcrypt.V3Policy

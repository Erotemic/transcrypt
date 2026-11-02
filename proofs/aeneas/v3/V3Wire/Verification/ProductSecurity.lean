import V3Wire.Verification.EndToEnd

/-!
# Product security: the public theorems

The product promise of the [charter](../../../../../docs/verification/V3-PRODUCT-CHARTER.md)
is that *user-selected files are authenticated ciphertext in public Git
history*. This file states that promise, and the guarantees around it, as a
handful of theorems over named domain predicates. The mechanics (the parsed
snapshots, offsets and per-entry checks of `HookEvidence`, the core's
`Result`s) stay in `EndToEnd.lean`, `Lifecycle.lean` and `Filters.lean`;
each theorem below composes the guarantees proved there. Every external
contract is a visible hypothesis: `Realizes` (A5), `HookContracts` (A11,
A19, A20, A21), `HookAnswers` (A4, A21: the adapter's answers to the
verified check), `ConfigCommitted` (the adapter's check, A4),
`RepairContracts` (A4, A20, A23), and, for history, `CommitStep` (A11, A22)
and the start of the history (A24).

* **A. Authenticated publication** (`keyed_publication_authenticates`): when
  a keyed pre-commit check accepts, every path the committed attributes
  select is a regular, non-reserved file whose blob authenticates at exactly
  that path under the committed configuration. A full check needs nothing
  about history; an incremental one needs `HeadAuthentic` (A24).
* **The three check modes** (`pre_commit_check_modes`): full keyed,
  incremental keyed and keyless acceptance, stated separately.
* **The record invariant** (`keyed_check_records_authentic`): a keyed check
  that accepted makes every regular, non-reserved index entry whose blob has
  this configuration's envelope authenticate at its own path
  (`RecordsAuthentic`), trusting `HEAD`'s records only when it was
  incremental with the guard `true`. The invariant says nothing about
  selection, so no attribute source, committed or local, can turn a forged
  record of history into an accepted protected file.
* **The history** (`keyed_history_authenticated_by_guard`): in a history of
  keyed commits, each made from the index checked before it, every commit's
  records and selected paths authenticate, given only that the first commit's
  `HEAD` records authenticate if its check trusted `HEAD`. The guard keeps
  the configuration (`config_unchanged_of_guard`); no assumption about how
  Git selects paths is needed (A19 is not a hypothesis).
* **B. Authenticated recovery** (`checkout_releases_only_authenticated_plaintext`,
  `checkout_opens_genuine_records`): a checkout either keeps the stored
  record unchanged or releases exactly the plaintext it authenticates to at
  its path; when the decision was to open, a record that does not
  authenticate is refused, never presented; a genuine record of this
  configuration opens to its plaintext.
* **C. No laundering** (`repair_never_launders`): the hook seals only the
  user's change or plaintext `protect` forced, rebinds only the user's
  record that authenticates at the path it was moved from, never repairs
  content imported from a commit unless `protect` forced it (and then only
  seals plaintext), and never skips the user's change.
* **D. Configuration-bound key use** (`stored_key_binds_file_operations`): a
  stored key is used only when its file holds exactly the current
  configuration, which the key authenticates; every record it opens or seals
  is bound to that configuration and the exact path.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

variable {P : Type} {inst : V3Primitives P} {prims : P} {σ : Suite}

/-! ## Check modes -/

/-- How much of the index a keyed pre-commit check authenticated. -/
inductive CheckMode
  /-- Nothing was trusted from `HEAD`. -/
  | full
  /-- An entry `HEAD` holds exactly may have been trusted from history
      (A24): a settled protected entry checked by its envelope only, an
      unprotected file not read at all. -/
  | incremental
  deriving DecidableEq

/-- The run trusted nothing from `HEAD`: it was not incremental
    (`verify-index`, `lock`, `rekey`), or its guard returned `false` (an
    attribute file or the configuration differs from `HEAD` or `HEAD^1`). -/
def FullCheck {E : Type} {g : GitState} (incremental : Bool) (run : HookEvidence g E) : Prop :=
  incremental = false ∨ run.samePolicy = false

/-- The runs a mode describes: `full` only a `FullCheck`, `incremental` any. -/
def CheckMode.Permits {E : Type} {g : GitState} : CheckMode → Bool → HookEvidence g E → Prop
  | .full, inc, run => FullCheck inc run
  | .incremental, _, _ => True

/-- **An accepted keyed check.** The hook's final check of `run` (`hookPlan`
    of the verified `staged_check` and `staged_verdict`) accepted with the
    key, under the configuration whose bytes are `config` and whose id is
    the suite's digest of them (A5), in a run of the given mode. The
    adapter's answers are as `HookAnswers` states (A4): a contract on the
    adapter, carried here with the configuration it is about, not something
    the run checked. -/
def KeyedCheckAccepted {E : Type} (ans : StagedEvidence E) (inst : V3Primitives P) (prims : P) (σ : Suite)
    {g : GitState} (run : HookEvidence g E) (config : List Nat) (mode : CheckMode) : Prop :=
  ∃ (cfg : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (incremental : Bool),
    wireBytes cfg = config ∧ wireBytes id = σ.digest16 config ∧ HookAnswers ans inst prims cfg id g run ∧
    hookPlan ans id true incremental run.inputs run.entries = ok true ∧
    mode.Permits incremental run

/-! ## A24, part 1: a full check needs no history -/

/-- **Full-check bootstrap.** A keyed check that trusted nothing from `HEAD`
    (`FullCheck`) and accepted gives an `AuthenticatedIndex` and the record
    invariant of the index (`RecordsAuthentic`) with no hypothesis about
    history, and without `ConfigCommitted`. -/
theorem hook_full_check_authenticates {E : Type} (g : GitState) (run : HookEvidence g E)
    (ans : StagedEvidence E) (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (incremental : Bool)
    (hR : Realizes inst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hgit : HookContracts g run)
    (hans : HookAnswers ans inst prims config id g run)
    (hcheck : hookPlan ans id true incremental run.inputs run.entries = ok true)
    (hfull : FullCheck incremental run) :
    AuthenticatedIndex σ (wireBytes config) g ∧ RecordsAuthentic σ (wireBytes config) g g.index := by
  have hrec := hook_records_authentic g run ans inst prims config id incremental hR hid hgit hans hcheck
    (fun hi hg => by
      rcases hfull with h | h
      · rw [h] at hi; cases hi
      · rw [h] at hg; cases hg)
  exact ⟨hook_authenticated_of_records g run ans inst prims config id incremental hR hid hgit hans hcheck hrec,
    hrec⟩

/-- **The three modes of the pre-commit check**, under the hook's contracts:

    * **full keyed** (`incremental = false`): every selected entry
      authenticates (`AuthenticatedIndex`), and so does every record of the
      index (`RecordsAuthentic`), with no assumption about history;
    * **incremental keyed**: every selected entry authenticates or is settled
      with this configuration's envelope (`AcceptedIndex`); every one
      authenticates if `HEAD`'s selected entries do (`HeadAuthentic`, A24),
      and the index's records and selected entries authenticate if `HEAD`'s
      records do whenever the guard returned `true` (`RecordsAuthentic`, A24);
    * **keyless**: every selected entry is a regular, non-reserved file with
      this configuration's envelope, settled or not a blob moved from another
      path (`KeylessEnvelopeOk`); authenticity is not established (A14). -/
theorem pre_commit_check_modes {E : Type} (g : GitState) (run : HookEvidence g E)
    (ans : StagedEvidence E) (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hR : Realizes inst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hgit : HookContracts g run)
    (hans : HookAnswers ans inst prims config id g run)
    (hcfg : ConfigCommitted g (wireBytes config)) :
    (hookPlan ans id true false run.inputs run.entries = ok true →
      AuthenticatedIndex σ (wireBytes config) g ∧ RecordsAuthentic σ (wireBytes config) g g.index) ∧
    (hookPlan ans id true true run.inputs run.entries = ok true →
      AcceptedIndex σ (wireBytes config) true true g ∧
      (HeadAuthentic σ (wireBytes config) g → AuthenticatedIndex σ (wireBytes config) g) ∧
      ((run.samePolicy = true → RecordsAuthentic σ (wireBytes config) g g.head) →
        AuthenticatedIndex σ (wireBytes config) g ∧ RecordsAuthentic σ (wireBytes config) g g.index)) ∧
    (∀ incremental, hookPlan ans id false incremental run.inputs run.entries = ok true →
      ∀ x ∈ g.index, Selected (g.filter x.path) →
        Selectable x ∧ ∃ content, g.blob x.oid = some content ∧
          KeylessEnvelopeOk σ (wireBytes config) g x content) := by
  refine ⟨fun hc => hook_full_check_authenticates g run ans config id false hR hid hgit hans hc (Or.inl rfl),
    fun hc => ⟨(hook_accepts_only_authenticated_ciphertext g run ans inst prims config id true true hR hid hgit
        hans hcfg hc).2.2,
      fun hh => hook_accepts_only_authenticated_ciphertext_given_history g run ans inst prims config id true hR
        hid hgit hans hcfg hc hh,
      fun hh => ?_⟩, ?_⟩
  · have hrec := hook_records_authentic g run ans inst prims config id true hR hid hgit hans hc
      (fun _ hg => hh hg)
    exact ⟨hook_authenticated_of_records g run ans inst prims config id true hR hid hgit hans hc hrec, hrec⟩
  · intro incremental hc x hx hsx
    obtain ⟨hsel, content, hcont, -, hkl⟩ :=
      (hook_accepts_only_authenticated_ciphertext g run ans inst prims config id false incremental hR hid hgit
        hans hcfg hc).2.2 x hx hsx
    exact ⟨hsel, content, hcont, hkl rfl⟩

/-! ## A. Authenticated publication -/

/-- **Authenticated publication.** Assume the hook's adapter contracts (Git's
    listings, attribute answers and objects, `HookContracts`), primitives that
    realize the suite (`Realizes`), and that `config` is the committed
    `.transcrypt/config` (`ConfigCommitted`). If a keyed check accepted
    (`KeyedCheckAccepted`), and, for an incremental check only, `HEAD`'s
    selected entries authenticate (`HeadAuthentic`, A24), then every path the
    committed attributes select is a regular, non-reserved file whose blob
    authenticates at exactly that path under the committed configuration
    (`AuthenticatedIndex`). -/
theorem keyed_publication_authenticates {E : Type} (g : GitState) (run : HookEvidence g E)
    (ans : StagedEvidence E) (config : List Nat) (mode : CheckMode)
    (hR : Realizes inst prims σ)
    (hgit : HookContracts g run)
    (hcfg : ConfigCommitted g config)
    (hacc : KeyedCheckAccepted ans inst prims σ run config mode)
    (hhist : mode = .incremental → HeadAuthentic σ config g) :
    ConfigCommitted g config ∧ AuthenticatedIndex σ config g := by
  obtain ⟨cfg, id, incremental, rfl, hid, hans, hcheck, hmode⟩ := hacc
  refine ⟨hcfg, ?_⟩
  cases mode with
  | full => exact (hook_full_check_authenticates g run ans cfg id incremental hR hid hgit hans hcheck hmode).1
  | incremental =>
    exact hook_accepts_only_authenticated_ciphertext_given_history g run ans inst prims cfg id incremental hR hid
      hgit hans hcfg hcheck (hhist rfl)

/-- **The record invariant of an accepted keyed check.** A keyed check that
    accepted makes every regular, non-reserved index entry whose blob has
    this configuration's envelope authenticate at its own path
    (`RecordsAuthentic`), and so every selected entry
    (`AuthenticatedIndex`), given `HEAD`'s records only if the check trusted
    `HEAD` (incremental, with the guard `true`). Nothing here depends on how
    Git selects paths: a local attribute file that selects a path, or stops
    selecting it, cannot make a forged record pass. -/
theorem keyed_check_records_authentic {E : Type} (g : GitState) (run : HookEvidence g E)
    (ans : StagedEvidence E) (config : List Nat) (mode : CheckMode)
    (hR : Realizes inst prims σ)
    (hgit : HookContracts g run)
    (hacc : KeyedCheckAccepted ans inst prims σ run config mode)
    (hhist : run.samePolicy = true → mode = .incremental → RecordsAuthentic σ config g g.head) :
    RecordsAuthentic σ config g g.index ∧ AuthenticatedIndex σ config g := by
  obtain ⟨cfg, id, incremental, rfl, hid, hans, hcheck, hmode⟩ := hacc
  have hrec := hook_records_authentic g run ans inst prims cfg id incremental hR hid hgit hans hcheck
    (fun hi hg => hhist hg (by
      cases mode with
      | full =>
        rcases hmode with h | h
        · rw [h] at hi; cases hi
        · rw [h] at hg; cases hg
      | incremental => rfl))
  exact ⟨hrec, hook_authenticated_of_records g run ans inst prims cfg id incremental hR hid hgit hans hcheck hrec⟩

/-! ## A24, part 2: one history transition

The next commit's `HEAD` is the commit Git made from the checked index. -/

/-- **The next commit was made from the checked index.** Every entry of the
    next `HEAD` is an entry of the index that was checked (A22: Git commits
    the index the hook checked last; equality in practice), and objects keep
    their content (A11: an object id names one content). -/
structure CommitStep (g g' : GitState) : Prop where
  head : ∀ y ∈ g'.head, y ∈ g.index
  objects : ∀ oid content, g.blob oid = some content → g'.blob oid = some content

/-- **The checked index's records are the next `HEAD`'s.** If the records of
    the checked index authenticate under `config` and the next commit's
    `HEAD` was made from it (`CommitStep`), the next check may trust
    `HEAD`'s records under the same configuration. -/
theorem records_authentic_of_checked_commit {g g' : GitState} {config config' : List Nat}
    (hrec : RecordsAuthentic σ config g g.index) (hstep : CommitStep g g') (hcfg : config' = config) :
    RecordsAuthentic σ config' g' g'.head := by
  intro y hy hsel
  obtain ⟨content, hc, hra⟩ := hrec y (hstep.head y hy) hsel
  subst hcfg
  exact ⟨content, hstep.objects _ _ hc, hra⟩

/-! ## A24, part 3: a history of keyed commits -/

/-- One commit of a history: Git's state when its hook ran, the run, the
    configuration it was checked under, and the mode of the check. -/
structure CheckedCommit (E : Type) where
  g : GitState
  run : HookEvidence g E
  config : List Nat
  mode : CheckMode

/-- The commit was accepted by a keyed check, with the contracts of its run. -/
structure KeyedCommit {E : Type} (ans : StagedEvidence E) (inst : V3Primitives P) (prims : P) (σ : Suite)
    (c : CheckedCommit E) : Prop where
  contracts : HookContracts c.g c.run
  config : ConfigCommitted c.g c.config
  accepted : KeyedCheckAccepted ans inst prims σ c.run c.config c.mode

/-- `c'` is the next commit after `c`, as Git makes it: from `c`'s checked
    index (`CommitStep`), so that its `HEAD` has that index's policy entries
    (A22). Nothing is said about the policy, the selection or the mode of
    `c'`'s check. -/
structure GuardedHistoryStep {E : Type} (c c' : CheckedCommit E) : Prop where
  commit : CommitStep c.g c'.g
  policy : policyEntries c'.g.head = policyEntries c.g.index

/-- **The guard keeps the configuration.** Let `g'` be the next run's state,
    made from the checked index of `g` (`CommitStep`) whose policy entries its
    `HEAD` has (A22). If the next run's verified `policy_unchanged` returned
    `true`, the configuration it commits is the one `g` committed. -/
theorem config_unchanged_of_guard {E : Type} {g g' : GitState} {run' : HookEvidence g' E}
    {config config' : List Nat}
    (hgit' : HookContracts g' run') (hguard : run'.samePolicy = true)
    (hstep : CommitStep g g') (hhead : policyEntries g'.head = policyEntries g.index)
    (hsorted : Sorted g.index) (hcfg : ConfigCommitted g config) (hcfg' : ConfigCommitted g' config') :
    config' = config := by
  have hpe : policyEntries g'.index = policyEntries g.index :=
    (hook_policy_guard hgit' hguard).1.trans hhead
  obtain ⟨c', hc'm, hc'p, -, hc'b⟩ := hcfg'
  obtain ⟨c, hcm, hcp, -, hcb⟩ := hcfg
  have hc' : c' ∈ policyEntries g.index := hpe ▸ mem_policyEntries.mpr ⟨hc'm, Or.inr hc'p⟩
  have heq := hsorted.eq_of_path (mem_policyEntries.mp hc').1 hcm (hc'p.trans hcp.symm)
  subst heq
  rw [hstep.objects _ _ hcb, Option.some.injEq] at hc'b
  exact hc'b.symm

/-- **A history of keyed commits stays authenticated.** Take commits
    `h 0, …, h n`, each accepted by a keyed check under one key
    (`KeyedCommit`, whose run records its guard), each made from the index
    checked before it (`GuardedHistoryStep`), and the first commit's `HEAD`
    records authentic if its check trusted `HEAD` (incremental, guard
    `true`). Then every commit's records authenticate (`RecordsAuthentic`)
    and so do its selected paths (`AuthenticatedIndex`), at their paths
    under its committed configuration. No step assumes anything about the
    policy or how Git selects paths: a check whose guard returned `true`
    keeps the configuration (`config_unchanged_of_guard`) and trusts only
    records `HEAD` holds exactly, and one whose guard returned `false`
    trusted nothing. -/
theorem keyed_history_authenticated_by_guard {E : Type} (ans : StagedEvidence E) (hR : Realizes inst prims σ)
    (h : Nat → CheckedCommit E) (n : Nat)
    (hcommits : ∀ i ≤ n, KeyedCommit ans inst prims σ (h i))
    (hsteps : ∀ i < n, GuardedHistoryStep (h i) (h (i + 1)))
    (hstart : (h 0).run.samePolicy = true → (h 0).mode = .incremental →
      RecordsAuthentic σ (h 0).config (h 0).g (h 0).g.head) :
    ∀ i ≤ n, RecordsAuthentic σ (h i).config (h i).g (h i).g.index ∧ AuthenticatedIndex σ (h i).config (h i).g := by
  intro i hi
  induction i with
  | zero =>
    have hc := hcommits 0 hi
    exact keyed_check_records_authentic _ _ ans _ _ hR hc.contracts hc.accepted hstart
  | succ k ih =>
    have hk := ih (by omega)
    have hs := hsteps k (by omega)
    have hc0 := hcommits k (by omega)
    have hc := hcommits (k + 1) hi
    exact keyed_check_records_authentic _ _ ans _ _ hR hc.contracts hc.accepted
      (fun hg _ => records_authentic_of_checked_commit hk.1 hs.commit
        (config_unchanged_of_guard hc.contracts hg hs.commit hs.policy (hook_snapshots_sorted hc0.contracts).1
          hc0.config hc.config))

/-! ## B. Authenticated recovery -/

/-- A released plaintext is never the record itself: a record is its
    plaintext plus the fixed overhead. -/
theorem opensTo_ne_record {config path record pt : List Nat} (hop : OpensTo σ config path record pt) :
    pt ≠ record := by
  intro heq
  have hl := congrArg List.length hop.2.2.2
  rw [sealed_length, ← heq] at hl
  simp [Transcrypt.V3Wire.fileMinLen, Transcrypt.V3Wire.fileHeaderLen] at hl

/-- **Authenticated recovery.** What the smudge filter writes for a
    protected path, given the stored `record`, is either

    * **released plaintext** (it differs from the record): exactly the
      plaintext the record authenticates to at this path under this
      configuration; or
    * **the kept record** (it is the record, unchanged): a v3 record within
      the size bound. This is a locked checkout, a record of another
      configuration, or the private mode's kept record; nothing is claimed
      to be decrypted.

    When the decision was to open (unlocked, this configuration's record), a
    record that does not authenticate is refused: an authentication failure
    is never presented as either outcome. -/
theorem checkout_releases_only_authenticated_plaintext (hR : Realizes inst prims σ)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (unlocked keepRecord : Bool)
    (path record buf : Slice U8) :
    smudgeModel inst prims config id unlocked keepRecord path record buf ⦃ r =>
      (∀ out, r = some out →
        (sliceBytes out ≠ sliceBytes record →
          OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes record) (sliceBytes out)) ∧
        (sliceBytes out = sliceBytes record →
          ∃ found, Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes record) = some found ∧
            record.length ≤ maxRecord)) ∧
      (smudgeSpec (sliceBytes record) (wireBytes id) unlocked = some .open_ →
        (¬ ∃ pt, OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes record) pt) → r = none) ⦄ := by
  apply WP.spec_mono (smudgeModel_spec hR config id unlocked keepRecord path record buf)
  intro r hr
  refine ⟨fun out hout => ?_, fun hopen hno => ?_⟩
  · rcases hr out hout with ⟨rfl, henv, -⟩ | hop
    · exact ⟨fun hne => absurd rfl hne, fun _ => henv⟩
    · exact ⟨fun _ => hop, fun heq => absurd heq (opensTo_ne_record hop)⟩
  · rcases r with _ | out
    · rfl
    · exfalso
      rcases hr out rfl with ⟨-, -, hpt⟩ | hop
      · exact hno (hpt hopen)
      · exact hno ⟨_, hop⟩

/-- **Genuine records open.** With the key, a record that authenticates at
    its path under this configuration (whose id the checkout holds) is
    opened by the smudge filter, to exactly its plaintext. -/
theorem checkout_opens_genuine_records (hR : Realizes inst prims σ)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (path record buf : Slice U8) (pt : List Nat)
    (hop : OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes record) pt)
    (hl : buf.length = pt.length) :
    smudgeModel inst prims config id true false path record buf ⦃ r =>
      ∃ out, r = some out ∧ sliceBytes out = pt ⦄ := by
  have hdec : smudgeSpec (sliceBytes record) (wireBytes id) true = some .open_ := by
    obtain ⟨hlen, hshape⟩ := opensTo_envelopeOk σ hop
    unfold smudgeSpec
    rw [if_neg (by omega), hshape, hid]
    simp
  unfold smudgeModel
  step with smudge_action_spec record id true as ⟨ a, ha ⟩
  rcases a with (_ | _) | e
  · simp only
    step with open_record_complete hR config path record buf pt hop hl as ⟨ r, out, hr, hout ⟩
    rw [hr]
    simp [hout]
  · obtain ⟨s, hs, ha'⟩ := ha
    rw [hdec] at hs
    cases hs
    simp [smudgeResult] at ha'
  · exact absurd ha.1 (by rw [hdec]; simp)

/-! ## C. No laundering -/

/-- Content imported from a commit: `HEAD`, or a commit being brought in,
    holds the entry's blob at its path. -/
def ImportedContent (g : GitState) (x : Entry) : Prop :=
  Holds g.head x.oid x.path ∨ ∃ m, g.incoming = some m ∧ Holds m x.oid x.path

/-- **No laundering.** For a protected index entry `x` whose repair the hook
    decided (`RepairContracts`: Git's listings A20, the sequencing state A23,
    the adapter's evidence about the blob and the verified decisions, A4):

    * a **seal** is of the user's change or of plaintext `protect` forced,
      and only of a blob without the v3 header;
    * a **rebind** is of the user's change: a record that authenticates at
      the path of a `HEAD` record it was moved from (`MoveSource`);
    * **imported content** (`HEAD` or an incoming commit holds it) is never
      rebound, and is sealed only when `protect` forced it: a record from
      another commit is never turned into a record of this path, and
      committed plaintext is encrypted only on the user's explicit request;
    * the **user's change, or a forced entry, is never skipped**: the hook
      reads its blob (`needs_record`). -/
theorem repair_never_launders (g : GitState) (run : RepairInputs)
    (hR : Realizes inst prims σ) (hc : RepairContracts inst prims g run) :
    (run.plan = transcrypt_v3_core.RepairPlan.Seal →
      (UserStaged g.head g.incoming (g.index[run.i.val]'hc.entry) ∨ run.forced = true) ∧
        NoHeader run.record) ∧
    (∀ j, run.plan = transcrypt_v3_core.RepairPlan.Rebind j →
      UserStaged g.head g.incoming (g.index[run.i.val]'hc.entry) ∧
        ∃ h, g.head[j.val]? = some h ∧ MoveSource g.index (g.index[run.i.val]'hc.entry) h ∧
          ∃ pt, OpensTo σ (wireBytes run.config) h.path (sliceBytes run.record) pt) ∧
    (ImportedContent g (g.index[run.i.val]'hc.entry) →
      (∀ j, run.plan ≠ transcrypt_v3_core.RepairPlan.Rebind j) ∧
      (run.forced = false → run.plan ≠ transcrypt_v3_core.RepairPlan.Seal)) ∧
    (UserStaged g.head g.incoming (g.index[run.i.val]'hc.entry) ∨ run.forced = true →
      needs_record run.prov = ok true) := by
  have hwho : run.plan = transcrypt_v3_core.RepairPlan.Seal →
      UserStaged g.head g.incoming (g.index[run.i.val]'hc.entry) ∨
        (run.forced = true ∧ run.plan = transcrypt_v3_core.RepairPlan.Seal) := fun hs =>
    (hook_repairs_only_local_changes g run hR hc (Or.inl hs)).2.1
  have hrebind := fun j (hj : run.plan = transcrypt_v3_core.RepairPlan.Rebind j) =>
    (hook_repairs_only_local_changes g run hR hc (Or.inr ⟨j, hj⟩)).2.2.2.2.2 j hj
  have hdec := repair_plan_repairs_only_local hc.decision
  refine ⟨fun hs => ⟨?_, ?_⟩, fun j hj => ?_, fun himp => ⟨fun j hj => ?_, fun hf hs => ?_⟩, fun hl => ?_⟩
  · rcases hwho hs with hu | ⟨hf, -⟩
    · exact Or.inl hu
    · exact Or.inr hf
  · have hrec := hc.record
    rw [(hdec.1 hs).1] at hrec
    exact hrec.2
  · obtain ⟨hu, -, hmove⟩ := hrebind j hj
    exact ⟨hu, hmove⟩
  · exact (hrebind j hj).1.not_committed himp
  · rcases hwho hs with hu | ⟨hf', -⟩
    · exact hu.not_committed himp
    · rw [hf] at hf'; cases hf'
  · obtain ⟨b, hb, -⟩ := WP.spec_imp_exists (needs_record_spec run.prov)
    cases b
    · obtain ⟨hns, hnf⟩ := hook_skips_only_unrepairable g run hc.toProvenanceContracts hb
      rcases hl with hu | hf
      · exact absurd hu hns
      · rw [hf] at hnf; cases hnf
    · exact hb

/-! ## D. Configuration-bound key use -/

/-- **Configuration-bound key use.** When `Key::load` uses the stored key
    (the verified `stored_key_state` says `Unlocked`, with `authentic` from
    `authenticate_config` under the primitives built from the stored key,
    A17), the key file holds exactly the current configuration, the key
    authenticates it, and every file operation under it is bound to that
    configuration and the exact path: a record `open_record` accepts opens
    there to exactly the released bytes, and a record `seal_record` writes is
    the spec's sealing, which opens there to the plaintext. Nothing here is
    about how the key was derived (Argon2id, A10) or where it came from. -/
theorem stored_key_binds_file_operations (hR : Realizes inst prims σ)
    (present : Bool) (file current : Slice U8) (config : Std.Array U8 55#usize)
    (hcur : sliceBytes current = wireBytes config) (authentic : Bool)
    (hauth : authentic = true → ∃ c, authenticate_config inst prims config = ok (core.result.Result.Ok c))
    (hstate : stored_key_state present file current authentic = ok transcrypt_v3_core.StoredKey.Unlocked) :
    (sliceBytes file).take Transcrypt.V3Wire.configLen = wireBytes config ∧
    ConfigAuthentic σ (wireBytes config) ∧
    (∀ path record out buf : Slice U8,
      open_record inst prims config path record out = ok (core.result.Result.Ok (), buf) →
        OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes record) (sliceBytes buf)) ∧
    (∀ path plaintext out sealed : Slice U8,
      seal_record inst prims config path plaintext out = ok (core.result.Result.Ok (), sealed) →
        sliceBytes sealed = sealedRecord σ (wireBytes config) (sliceBytes path) (sliceBytes plaintext) ∧
        OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes sealed) (sliceBytes plaintext)) := by
  obtain ⟨-, -, htake, hca⟩ :=
    stored_key_authenticates_current_config hR present file current config hcur authentic hauth hstate
  refine ⟨htake, hca, fun path record out buf ho => ?_, fun path plaintext out sealed hs => ?_⟩
  · have h := open_record_spec hR config path record out
    rw [ho] at h
    simpa using h
  · have h := seal_record_spec hR config path plaintext out
    rw [hs] at h
    obtain ⟨hmay, hsealed⟩ := (by simpa using h :
      MaySeal σ (wireBytes config) (sliceBytes path) (sliceBytes plaintext) ∧
        sliceBytes sealed = sealedRecord σ (wireBytes config) (sliceBytes path) (sliceBytes plaintext))
    exact ⟨hsealed, hsealed ▸ seal_opens σ hmay⟩

end Transcrypt.V3Verification

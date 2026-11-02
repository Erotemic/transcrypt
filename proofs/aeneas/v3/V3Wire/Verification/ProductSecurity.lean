import V3Wire.Verification.EndToEnd
import V3Wire.Verification.KeyUse

/-!
# Product security: the public theorems

The product promise of the [charter](../../../../../docs/verification/V3-PRODUCT-CHARTER.md)
is that *user-selected files are authenticated ciphertext in public Git
history*. This file states that promise, and the guarantees around it, as a
handful of theorems over named domain predicates. The mechanics (the parsed
snapshots, offsets and per-entry checks of `HookEvidence`, the core's
`Result`s) stay in `EndToEnd.lean`, `Lifecycle.lean` and `Filters.lean`;
each theorem below composes the guarantees proved there. Every external
contract is a visible hypothesis: `Realizes` (A5), `KeyScheduleRealizes`
(A5, A17), `HookContracts` (A11,
A19, A20, A21), `ConfigCommitted` (the adapter's check, A4), `RepairContracts`
(A4, A20, A23), and, for history, `HeadAuthentic`, `CommitStep` (A11, A22) and
`PolicyUnchanged` (A19 and the hook's policy guard).

* **A. Authenticated publication** (`keyed_publication_authenticates`): when
  a keyed pre-commit check accepts, every path the committed attributes
  select is a regular, non-reserved file whose blob authenticates at exactly
  that path under the committed configuration. A full check needs nothing
  about history; an incremental one needs `HeadAuthentic` (A24).
* **The three check modes** (`pre_commit_check_modes`): full keyed,
  incremental keyed and keyless acceptance, stated separately.
* **The history** (`head_authentic_of_checked_commit`,
  `keyed_history_stays_authenticated`): an authenticated index gives
  `HeadAuthentic` for the next commit when that commit is the checked index
  and the protected-path policy and configuration are unchanged; so in a
  history of keyed commits that starts with a full check and checks in full
  whenever the policy changes, every commit authenticates. This is the part
  of A24 that is mathematics; what remains assumed is named in
  `docs/verification/V3-ASSUMPTIONS.md` (A24).
* **The history from the guard** (`keyed_history_authenticated_by_guard`):
  the same with no policy hypothesis on any step. Each run records the
  verified guard (`HookGuard`); a `true` guard gives `PolicyUnchanged`
  (`policy_unchanged_of_guard`) under A19 stated as the contract
  `SelectionByPolicy`, and a `false` guard settled nothing
  (`unguarded_check_is_full`).
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
  configuration, which the key authenticates; the primitives used are those
  `unlock_stored_key` built from the file's own key bytes (`KeyUse.lean`;
  the key schedule is the contract `KeyScheduleRealizes`, A5/A17); every
  record they open or seal is bound to that configuration and the exact path.
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
  /-- Every protected entry was authenticated with the key. -/
  | full
  /-- An entry unchanged since `HEAD` and `HEAD^1` (*settled*) may have been
      checked by its envelope only, trusting history (A24). -/
  | incremental
  deriving DecidableEq

/-- The run authenticated every protected entry: it was not incremental
    (`verify-index`, a full hook run), or no entry counted as settled (what
    the incremental hook does when the protected-path policy changed). -/
def FullCheck (incremental : Bool) (entries : List HookEntry) : Prop :=
  incremental = false ∨ ∀ e ∈ entries, e.settled = false

/-- The runs a mode describes: `full` only a `FullCheck`, `incremental` any. -/
def CheckMode.Permits : CheckMode → Bool → List HookEntry → Prop
  | .full, inc, es => FullCheck inc es
  | .incremental, _, _ => True

/-- **An accepted keyed check.** The hook's final check of `run` (the
    model `hookPlan` of `check_staged`, A4) accepted with the key, under the
    configuration whose bytes are `config` and whose id is the suite's digest
    of them (A5), in a run of the given mode. -/
def KeyedCheckAccepted (inst : V3Primitives P) (prims : P) (σ : Suite) {g : GitState}
    (run : HookEvidence g) (config : List Nat) (mode : CheckMode) : Prop :=
  ∃ (cfg : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (incremental : Bool),
    wireBytes cfg = config ∧ wireBytes id = σ.digest16 config ∧
    hookPlan inst prims cfg id true incremental run.entries = ok true ∧
    mode.Permits incremental run.entries

/-! ## A24, part 1: a full check needs no history -/

/-- **Full-check bootstrap.** A keyed check that authenticated every
    protected entry (`FullCheck`) and accepted gives an `AuthenticatedIndex`
    with no hypothesis about history (no `HeadAuthentic`), and without
    `ConfigCommitted`: every selected entry authenticates under `config`. -/
theorem hook_full_check_authenticates (g : GitState) (run : HookEvidence g)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (incremental : Bool)
    (hR : Realizes inst prims σ)
    (hgit : HookContracts g run)
    (hcheck : hookPlan inst prims config id true incremental run.entries = ok true)
    (hfull : FullCheck incremental run.entries) :
    AuthenticatedIndex σ (wireBytes config) g := by
  have hplan := spec_result (hookPlan_spec hR config id true incremental run.entries) hcheck rfl
  intro x hx hsx
  obtain ⟨e, he, hce⟩ := hook_checks_selected hgit hx hsx
  have hk : true = true ∧ ¬ (incremental = true ∧ e.settled = true) := by
    refine ⟨rfl, ?_⟩
    rintro ⟨hi, hs⟩
    rcases hfull with hf | hf
    · rw [hf] at hi; cases hi
    · rw [hf e he] at hs; cases hs
  obtain ⟨pt, hpt⟩ := (hplan e he).1 hk
  rw [hce.path] at hpt
  exact ⟨hook_selectable hgit hx hsx, _, hce.blob, pt, hpt⟩

/-- **The three modes of the pre-commit check**, under the hook's contracts:

    * **full keyed** (`incremental = false`): every selected entry
      authenticates (`AuthenticatedIndex`), with no assumption about history;
    * **incremental keyed**: every selected entry authenticates or is settled
      with this configuration's envelope (`AcceptedIndex`), and every one
      authenticates if `HEAD`'s selected entries do (`HeadAuthentic`, A24);
    * **keyless**: every selected entry is a regular, non-reserved file with
      this configuration's envelope, settled or not a blob moved from another
      path (`KeylessEnvelopeOk`); authenticity is not established (A14). -/
theorem pre_commit_check_modes (g : GitState) (run : HookEvidence g)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hR : Realizes inst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hgit : HookContracts g run)
    (hcfg : ConfigCommitted g (wireBytes config)) :
    (hookPlan inst prims config id true false run.entries = ok true →
      AuthenticatedIndex σ (wireBytes config) g) ∧
    (hookPlan inst prims config id true true run.entries = ok true →
      AcceptedIndex σ (wireBytes config) true true g ∧
      (HeadAuthentic σ (wireBytes config) g → AuthenticatedIndex σ (wireBytes config) g)) ∧
    (∀ incremental, hookPlan inst prims config id false incremental run.entries = ok true →
      ∀ x ∈ g.index, Selected (g.filter x.path) →
        Selectable x ∧ ∃ content, g.blob x.oid = some content ∧
          KeylessEnvelopeOk σ (wireBytes config) g x content) := by
  refine ⟨fun hc => hook_full_check_authenticates g run config id false hR hgit hc (Or.inl rfl),
    fun hc => ⟨(hook_accepts_only_authenticated_ciphertext g run config id true true hR hid hgit hcfg hc).2.2,
      fun hh => hook_accepts_only_authenticated_ciphertext_given_history g run config id true hR hid hgit
        hcfg hc hh⟩, ?_⟩
  intro incremental hc x hx hsx
  obtain ⟨hsel, content, hcont, -, hkl⟩ :=
    (hook_accepts_only_authenticated_ciphertext g run config id false incremental hR hid hgit hcfg hc).2.2
      x hx hsx
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
theorem keyed_publication_authenticates (g : GitState) (run : HookEvidence g) (config : List Nat)
    (mode : CheckMode)
    (hR : Realizes inst prims σ)
    (hgit : HookContracts g run)
    (hcfg : ConfigCommitted g config)
    (hacc : KeyedCheckAccepted inst prims σ run config mode)
    (hhist : mode = .incremental → HeadAuthentic σ config g) :
    ConfigCommitted g config ∧ AuthenticatedIndex σ config g := by
  obtain ⟨cfg, id, incremental, rfl, hid, hcheck, hmode⟩ := hacc
  refine ⟨hcfg, ?_⟩
  cases mode with
  | full => exact hook_full_check_authenticates g run cfg id incremental hR hgit hcheck hmode
  | incremental =>
    exact hook_accepts_only_authenticated_ciphertext_given_history g run cfg id incremental hR hid hgit
      hcfg hcheck (hhist rfl)

/-! ## A24, part 2: one history transition

The next commit's `HEAD` is the commit Git made from the checked index. -/

/-- **The next commit was made from the checked index.** Every entry of the
    next `HEAD` is an entry of the index that was checked (A22: Git commits
    the index the hook checked last; equality in practice), and objects keep
    their content (A11: an object id names one content). -/
structure CommitStep (g g' : GitState) : Prop where
  head : ∀ y ∈ g'.head, y ∈ g.index
  objects : ∀ oid content, g.blob oid = some content → g'.blob oid = some content

/-- **The protected-path policy did not change.** Every path the attributes
    being committed now select was selected by the attributes of the checked
    commit, and the committed configuration is the one the records were
    checked under. The hook's policy guard (the committed attribute files and
    `.transcrypt/config` are those of `HEAD` and `HEAD^1`) establishes it
    through A19 (Git evaluates `filter` from the committed attribute files);
    this is the hypothesis that guard plugs into. -/
structure PolicyUnchanged (g g' : GitState) (config config' : List Nat) : Prop where
  selection : ∀ p, Selected (g'.filter p) → Selected (g.filter p)
  config : config' = config

/-- **An authenticated index makes the next `HEAD` authentic.** If the
    checked index authenticates under `config`, the next commit's `HEAD` was
    made from it (`CommitStep`) and the policy is unchanged
    (`PolicyUnchanged`), then the next check may trust `HEAD`
    (`HeadAuthentic`). -/
theorem head_authentic_of_checked_commit {g g' : GitState} {config config' : List Nat}
    (hauth : AuthenticatedIndex σ config g) (hstep : CommitStep g g')
    (hpol : PolicyUnchanged g g' config config') :
    HeadAuthentic σ config' g' := by
  intro y hy hsy
  obtain ⟨-, content, hc, hat⟩ := hauth y (hstep.head y hy) (hpol.selection _ hsy)
  rw [hpol.config]
  exact ⟨content, hstep.objects _ _ hc, hat⟩

/-! ## A24, part 3: a history of keyed commits -/

/-- One commit of a history: Git's state when its hook ran, the run, the
    configuration it was checked under, and the mode of the check. -/
structure CheckedCommit where
  g : GitState
  run : HookEvidence g
  config : List Nat
  mode : CheckMode

/-- The commit was accepted by a keyed check, with the contracts of its run. -/
structure KeyedCommit (inst : V3Primitives P) (prims : P) (σ : Suite) (c : CheckedCommit) : Prop where
  contracts : HookContracts c.g c.run
  config : ConfigCommitted c.g c.config
  accepted : KeyedCheckAccepted inst prims σ c.run c.config c.mode

/-- `c'` is the next commit after `c`: made from `c`'s checked index, and
    checked incrementally only if the policy is unchanged (otherwise in full:
    a selection or configuration change needs full revalidation). -/
structure HistoryStep (c c' : CheckedCommit) : Prop where
  commit : CommitStep c.g c'.g
  policy : c'.mode = .incremental → PolicyUnchanged c.g c'.g c.config c'.config

/-- **A history of keyed commits stays authenticated.** Take commits
    `h 0, …, h n`, each accepted by a keyed check under one key
    (`KeyedCommit`), each made from the index checked before it
    (`HistoryStep`), and the first checked in full or after an authentic
    `HEAD`. Then every commit's selected paths authenticate at their paths
    under its committed configuration. -/
theorem keyed_history_stays_authenticated (hR : Realizes inst prims σ)
    (h : Nat → CheckedCommit) (n : Nat)
    (hcommits : ∀ i ≤ n, KeyedCommit inst prims σ (h i))
    (hsteps : ∀ i < n, HistoryStep (h i) (h (i + 1)))
    (hstart : (h 0).mode = .incremental → HeadAuthentic σ (h 0).config (h 0).g) :
    ∀ i ≤ n, AuthenticatedIndex σ (h i).config (h i).g := by
  intro i hi
  induction i with
  | zero =>
    have hc := hcommits 0 hi
    exact (keyed_publication_authenticates _ _ _ _ hR hc.contracts hc.config hc.accepted hstart).2
  | succ k ih =>
    have hk := ih (by omega)
    have hs := hsteps k (by omega)
    have hc := hcommits (k + 1) hi
    exact (keyed_publication_authenticates _ _ _ _ hR hc.contracts hc.config hc.accepted
      (fun hm => head_authentic_of_checked_commit hk hs.commit (hs.policy hm))).2

/-! ## A24, part 4: the hook's guard in place of `PolicyUnchanged`

`HistoryStep` takes `PolicyUnchanged` as a hypothesis of each incremental
step. Here it is derived instead: from the guard the next check computed
(`run.samePolicy`, the verified `policy_unchanged`, `HookGuard`), the commit
step, and A19 stated as a contract (`SelectionByPolicy`). A check whose guard
returned `false` settled nothing, so it is a `FullCheck` and needs no
history at all. -/

/-- **A19, the selection rule, as a contract.** Git's effective `filter` of
    every path is one fixed function `attrs` of the policy entries of the
    index being committed: its attribute files, by object id (which names
    their content, A11), and its configuration entry. `attrs` stands for
    everything else Git's answer depends on, notably the local attribute
    sources that are not committed (`.git/info/attributes`,
    `core.attributesFile`): taking one `attrs` for every commit of a history
    assumes those do not change during it. This is the stated exclusion. The
    contract says how Git selects paths; it says nothing about records. -/
def SelectionByPolicy (attrs : List Entry → List Nat → List Nat) (g : GitState) : Prop :=
  ∀ p, g.filter p = attrs (policyEntries g.index) p

/-- A run whose guard returned `false` settled nothing: it is a
    `FullCheck`, whatever its mode. -/
theorem unguarded_check_is_full {g : GitState} (run : HookEvidence g) (incremental : Bool)
    (h : run.samePolicy = false) : FullCheck incremental run.entries :=
  Or.inr (hook_unguarded_settles_nothing run h)

/-- **The guard gives `PolicyUnchanged`.** Let `g'` be the next run's state,
    made from the checked index of `g` (`CommitStep`) whose policy entries its
    `HEAD` has (A22: Git commits the index the hook checked), with Git's
    selection given by the policy entries in both (`SelectionByPolicy`, A19,
    one `attrs`). If the next run's verified `policy_unchanged` returned
    `true`, no path is newly selected, and the configuration it commits is the
    one `g` committed. -/
theorem policy_unchanged_of_guard {g g' : GitState} {run' : HookEvidence g'} {config config' : List Nat}
    {attrs : List Entry → List Nat → List Nat}
    (hgit' : HookContracts g' run') (hguard : run'.samePolicy = true)
    (hsel : SelectionByPolicy attrs g) (hsel' : SelectionByPolicy attrs g')
    (hstep : CommitStep g g') (hhead : policyEntries g'.head = policyEntries g.index)
    (hsorted : Sorted g.index) (hcfg : ConfigCommitted g config) (hcfg' : ConfigCommitted g' config') :
    PolicyUnchanged g g' config config' := by
  have hpe : policyEntries g'.index = policyEntries g.index :=
    (hook_policy_guard hgit' hguard).1.trans hhead
  refine ⟨fun p hp => ?_, ?_⟩
  · rw [hsel' p, hpe, ← hsel p] at hp
    exact hp
  · obtain ⟨c', hc'm, hc'p, -, hc'b⟩ := hcfg'
    obtain ⟨c, hcm, hcp, -, hcb⟩ := hcfg
    have hc' : c' ∈ policyEntries g.index := hpe ▸ mem_policyEntries.mpr ⟨hc'm, Or.inr hc'p⟩
    have heq := hsorted.eq_of_path (mem_policyEntries.mp hc').1 hcm (hc'p.trans hcp.symm)
    subst heq
    rw [hstep.objects _ _ hcb, Option.some.injEq] at hc'b
    exact hc'b.symm

/-- **An accepted keyed check authenticates, trusting `HEAD` only under the
    guard.** A keyed check that accepted gives an `AuthenticatedIndex` when
    `HEAD`'s selected entries authenticate, which is needed only if the run
    was incremental *and* its guard returned `true`: otherwise nothing was
    settled. -/
theorem keyed_check_authenticates_given_guard (g : GitState) (run : HookEvidence g) (config : List Nat)
    (mode : CheckMode)
    (hR : Realizes inst prims σ)
    (hgit : HookContracts g run)
    (hcfg : ConfigCommitted g config)
    (hacc : KeyedCheckAccepted inst prims σ run config mode)
    (hhist : run.samePolicy = true → mode = .incremental → HeadAuthentic σ config g) :
    AuthenticatedIndex σ config g := by
  cases hp : run.samePolicy
  · obtain ⟨cfg, id, incremental, rfl, -, hcheck, -⟩ := hacc
    exact hook_full_check_authenticates g run cfg id incremental hR hgit hcheck
      (unguarded_check_is_full run incremental hp)
  · exact (keyed_publication_authenticates g run config mode hR hgit hcfg hacc (hhist hp)).2

/-- `c'` is the next commit after `c`, as Git makes it: from `c`'s checked
    index (`CommitStep`), so that its `HEAD` has that index's policy entries
    (A22). Nothing is said about the policy or the mode of `c'`'s check. -/
structure GuardedHistoryStep (c c' : CheckedCommit) : Prop where
  commit : CommitStep c.g c'.g
  policy : policyEntries c'.g.head = policyEntries c.g.index

/-- **A history of keyed commits stays authenticated, with the hook's guard.**
    Take commits `h 0, …, h n`, each accepted by a keyed check under one key
    (`KeyedCommit`, whose run records its guard), each made from the index
    checked before it (`GuardedHistoryStep`), with Git selecting paths by the
    committed policy under one rule (`SelectionByPolicy attrs`, A19, local
    attribute sources fixed), and the first commit's `HEAD` authentic if its
    check was incremental with the guard `true`. Then every commit's
    selected paths authenticate at their paths under its committed
    configuration. No step assumes `PolicyUnchanged`: a check whose guard
    returned `true` derives it (`policy_unchanged_of_guard`), and one whose
    guard returned `false` settled nothing (`unguarded_check_is_full`). -/
theorem keyed_history_authenticated_by_guard (hR : Realizes inst prims σ)
    (attrs : List Entry → List Nat → List Nat)
    (h : Nat → CheckedCommit) (n : Nat)
    (hcommits : ∀ i ≤ n, KeyedCommit inst prims σ (h i))
    (hselection : ∀ i ≤ n, SelectionByPolicy attrs (h i).g)
    (hsteps : ∀ i < n, GuardedHistoryStep (h i) (h (i + 1)))
    (hstart : (h 0).run.samePolicy = true → (h 0).mode = .incremental →
      HeadAuthentic σ (h 0).config (h 0).g) :
    ∀ i ≤ n, AuthenticatedIndex σ (h i).config (h i).g := by
  intro i hi
  induction i with
  | zero =>
    have hc := hcommits 0 hi
    exact keyed_check_authenticates_given_guard _ _ _ _ hR hc.contracts hc.config hc.accepted hstart
  | succ k ih =>
    have hk := ih (by omega)
    have hs := hsteps k (by omega)
    have hc0 := hcommits k (by omega)
    have hc := hcommits (k + 1) hi
    exact keyed_check_authenticates_given_guard _ _ _ _ hR hc.contracts hc.config hc.accepted
      (fun hg _ => head_authentic_of_checked_commit hk hs.commit
        (policy_unchanged_of_guard hc.contracts hg (hselection k (by omega)) (hselection (k + 1) hi)
          hs.commit hs.policy (hook_snapshots_sorted hc0.contracts).1 hc0.config hc.config))

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

/-- **Configuration-bound key use.** When `Key::load` uses the stored key,
    the primitives and configuration it holds (`ValidatedKey::from_stored`)
    are exactly what the verified `unlock_stored_key` returned for the key
    file's bytes and the current configuration. Then the file holds exactly
    that configuration followed by the key bytes `storedKeyBytes file`; the
    primitives realize the suite of those bytes (given only the key-schedule
    contract `KeyScheduleRealizes`, A5/A17), and the configuration
    authenticates under them; and every file operation under them is bound
    to that configuration and the exact path: a record `open_record` accepts
    opens there to exactly the released bytes, and a record `seal_record`
    writes is the spec's sealing, which opens there to the plaintext.
    Nothing here is about how the key was derived (Argon2id, A10) or which
    `unlock` wrote the file. -/
theorem stored_key_binds_file_operations {sched : V3KeySchedule P} {σk : List Nat → Suite}
    (hK : KeyScheduleRealizes inst sched σk)
    (present : Bool) (file current : Slice U8) (keyed : P) (config : Std.Array U8 55#usize)
    (hunlock : unlock_stored_key inst sched present file current =
      ok (core.result.Result.Ok (keyed, config))) :
    wireBytes config = sliceBytes current ∧
    (sliceBytes file).take Transcrypt.V3Wire.configLen = wireBytes config ∧
    ConfigAuthentic (σk (storedKeyBytes (sliceBytes file))) (wireBytes config) ∧
    (∀ path record out buf : Slice U8,
      open_record inst keyed config path record out = ok (core.result.Result.Ok (), buf) →
        OpensTo (σk (storedKeyBytes (sliceBytes file))) (wireBytes config) (sliceBytes path)
          (sliceBytes record) (sliceBytes buf)) ∧
    (∀ path plaintext out sealed : Slice U8,
      seal_record inst keyed config path plaintext out = ok (core.result.Result.Ok (), sealed) →
        sliceBytes sealed = sealedRecord (σk (storedKeyBytes (sliceBytes file))) (wireBytes config)
          (sliceBytes path) (sliceBytes plaintext) ∧
        OpensTo (σk (storedKeyBytes (sliceBytes file))) (wireBytes config) (sliceBytes path)
          (sliceBytes sealed) (sliceBytes plaintext)) := by
  obtain ⟨-, -, htake, hcfg, hR, hca⟩ :=
    spec_result (unlock_stored_key_spec hK present file current) hunlock
  refine ⟨hcfg, htake.trans hcfg.symm, hca, fun path record out buf ho => ?_, fun path plaintext out sealed hs => ?_⟩
  · have h := open_record_spec hR config path record out
    rw [ho] at h
    simpa using h
  · have h := seal_record_spec hR config path plaintext out
    rw [hs] at h
    obtain ⟨hmay, hsealed⟩ := (by simpa using h :
      MaySeal (σk (storedKeyBytes (sliceBytes file))) (wireBytes config) (sliceBytes path) (sliceBytes plaintext) ∧
        sliceBytes sealed = sealedRecord (σk (storedKeyBytes (sliceBytes file))) (wireBytes config)
          (sliceBytes path) (sliceBytes plaintext))
    exact ⟨hsealed, hsealed ▸ seal_opens _ hmay⟩

end Transcrypt.V3Verification

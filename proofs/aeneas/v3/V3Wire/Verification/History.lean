import V3Wire.Verification.ProductAssurance

/-!
# History: merges, branches and rekeys

`keyed_audit_chain_authenticated` and `transcrypt_product_assurance` describe
one linear chain of commits under one key. Real histories are graphs, and
`rekey` starts a new configuration with its own key. This file composes the
single-commit theorems over both, without re-proving them.

* **The audited range as a graph.** `audit` walks the commits
  `git rev-list --reverse --parents` prints and audits each one against its
  **first** parent only (`AuditedRange.firstParent`). Every other parent of a
  merge plays no part: the merge's entries are examined as changes relative
  to the first parent, and a second parent is itself audited if it lies in
  the range, and trusted by nothing otherwise. The order of the walk does not
  matter either: the induction is over the first-parent relation, which is
  acyclic (`FirstParentAcyclic`, a property of Git's commit graph: a commit
  names its parents by object id, A11), so a parent printed after its child
  (commit-date skew) is covered.
* **Epochs.** Each configuration has its own key or none
  (`EpochKeys`: what `Key::load(repo, config)` finds, per committed config).
  The record invariant is per configuration (`RecordsAuthentic σ config`), and
  the audit trusts a first parent only while the configuration is unchanged
  (`AuditStep.config`), so a configuration change (a rekey) restarts from
  the whole tree (`AuditBase.Tree`) and no key ever vouches for another
  epoch's records.
* **What is concluded.** `keyed_dag_audit_authenticated`: every audited
  commit whose configuration has a key keeps both invariants under that key
  (`AuditedCommitAuthentic`), given only the trusted boundary (A13: a first
  parent outside the range). `keyless_dag_audit_enveloped`: every audited
  commit whose configuration has no key in this checkout has the envelope of
  its configuration at every selected path (`SelectionEnveloped`); nothing
  is authenticated there (A14).
* **The hook across a rekey.** `rekey_guard_false`: a commit whose
  configuration differs from the previous one is checked with the guard
  `false`, so `rekey_commit_starts_epoch` establishes the new epoch's
  invariant with no hypothesis about the old one; `epoch_history_authenticated`
  is `keyed_history_authenticated_by_guard` with a key per epoch.
* **Top level.** `transcrypt_product_assurance_dag`.

Each accepted run of the verified core enters only through its bundle
(`KeyedAudit`, `KeylessAudit`, `KeyedCommit`); `keyed_audit_run_authenticated`
and `keyless_audit_run_enveloped` are the only proofs that open an audit
bundle.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

variable {P : Type} {inst : V3Primitives P}

/-! ## Keys per configuration -/

/-- The validated key of one configuration epoch: its primitives and the
    suite they realize. -/
structure EpochKey (P : Type) where
  prims : P
  suite : Suite

/-- The key this checkout has for each configuration (by its bytes), or
    none: the audit asks `Key::load(repo, config)` once per committed
    configuration, and a configuration without a key is audited keyless. -/
abbrev EpochKeys (P : Type) := List Nat → Option (EpochKey P)

/-- Every key's primitives realize its suite (A5). -/
def KeysRealize (inst : V3Primitives P) (keys : EpochKeys P) : Prop :=
  ∀ config k, keys config = some k → Realizes inst k.prims k.suite

/-! ## One audited commit, as a bundle -/

/-- The commit's audit without the key accepted, with its contracts and
    answers (the shape of `KeyedAudit`, for `audit_check` with `keyed =
    false`). The primitives are never used; `σ₀` gives only the
    configuration's id (A5: `config_id`). -/
structure KeylessAudit {A : Type} (ans : StagedEvidence A) (pinst : V3Primitives P) (σ₀ : Suite)
    (g : GitState) (r : AuditRun A) : Prop where
  id : wireBytes r.id = σ₀.digest16 (wireBytes r.config)
  contracts : AuditContracts g r.commit r.base r.entries
  answers : ∃ prims : P, AuditAnswers ans pinst prims r.config r.id g r.entries
  accepted : auditPlan ans r.id false r.base r.entries = ok true

/-- **An audited commit authenticates**: its records (`RecordsAuthentic`)
    and every entry its own attributes select (`SelectionAuthentic`). -/
def AuditedCommitAuthentic (σ : Suite) (config : List Nat) (g : GitState) (c : AuditedCommit) : Prop :=
  RecordsAuthentic σ config g c.tree ∧ SelectionAuthentic σ config g c.filter c.tree

/-- **The selection has the envelope.** Every entry of `es` that `filter`
    selects, unless it is repository metadata, is a regular file whose blob
    has the envelope of the configuration with id `id`. -/
def SelectionEnveloped (id : List Nat) (g : GitState) (filter : List Nat → List Nat) (es : List Entry) : Prop :=
  ∀ x ∈ es, Selected (filter x.path) → ¬ Reserved x.path →
    x.Regular ∧ ∃ content, g.blob x.oid = some content ∧ EnvelopeOk content id

/-- **One keyed audit run.** `keyed_audit_authenticates_commit` for an
    accepted `KeyedAudit`: given the first parent's invariants (under the
    parent's selection `pfilter`) when the audit trusted the parent. -/
theorem keyed_audit_run_authenticated {A : Type} {aans : StagedEvidence A} {prims : P} {σ : Suite}
    {g : GitState} {r : AuditRun A}
    (ha : KeyedAudit aans inst prims σ g r) (hR : Realizes inst prims σ)
    (pfilter : List Nat → List Nat)
    (hparent : r.base = .Parent → RecordsAuthentic σ (wireBytes r.config) g r.commit.parent ∧
      SelectionAuthentic σ (wireBytes r.config) g pfilter r.commit.parent)
    (hagree : AuditSelectionAgrees r.commit r.entries pfilter) :
    AuditedCommitAuthentic σ (wireBytes r.config) g r.commit :=
  keyed_audit_authenticates_commit g _ _ _ aans inst prims _ _ hR ha.id ha.contracts ha.answers ha.accepted
    (fun hb => (hparent hb).1) pfilter (fun hb => (hparent hb).2) hagree

/-- **One keyless audit run.** Every entry the commit's attributes select,
    unless it is metadata, has the envelope: an examined one by
    `keyless_audit_checks_envelopes`, any other because the audit trusted the
    parent, which holds it exactly and selects it alike
    (`AuditSelectionAgrees`). -/
theorem keyless_audit_run_enveloped {A : Type} {aans : StagedEvidence A} {σ₀ : Suite}
    {g : GitState} {r : AuditRun A}
    (ha : KeylessAudit aans inst σ₀ g r) (pfilter : List Nat → List Nat)
    (hparent : r.base = .Parent → SelectionEnveloped (σ₀.digest16 (wireBytes r.config)) g pfilter r.commit.parent)
    (hagree : AuditSelectionAgrees r.commit r.entries pfilter) :
    SelectionEnveloped (σ₀.digest16 (wireBytes r.config)) g r.commit.filter r.commit.tree := by
  obtain ⟨prims, hans⟩ := ha.answers
  intro x hx hs hnr
  by_cases hex : ∃ e ∈ r.entries, e.entry = x
  · obtain ⟨e, he, rfl⟩ := hex
    obtain ⟨hreg, content, hc, henv, -⟩ := keyless_audit_checks_envelopes (σ := σ₀) g r.commit r.base r.entries
      aans inst prims r.config r.id ha.id ha.contracts hans ha.accepted e he hs hnr
    exact ⟨hreg, content, hc, henv⟩
  · rcases ha.contracts.covers x hx hnr with hex' | ⟨hb, hxp⟩
    · exact absurd hex' hex
    · exact hparent hb x hxp (hagree x hx hnr hex ▸ hs) hnr

/-! ## The audited range as a commit graph -/

/-- The commits one `audit` run walked: those `git rev-list --reverse
    --parents` printed (`commits`, in any order), each commit's parents in
    Git's order, and each commit's audit run (`audit_commit`, against its
    first parent). -/
structure AuditedRange (C A : Type) where
  commits : List C
  parents : C → List C
  run : C → AuditRun A

/-- The first parent, the only one the audit compares with (`ids.get(1)`). -/
def AuditedRange.firstParent {C A : Type} (d : AuditedRange C A) (c : C) : Option C :=
  (d.parents c).head?

/-- The configuration bytes a commit was audited under. -/
abbrev AuditedRange.config {C A : Type} (d : AuditedRange C A) (c : C) : List Nat :=
  wireBytes (d.run c).config

/-- **Git's commit graph is acyclic** along the first parents within the
    range: some rank (Git's generation number) decreases from a commit to
    its first parent. A commit names its parents by object id (A11), so
    none is its own ancestor. Nothing is assumed about the order of the
    walk. -/
def FirstParentAcyclic {C A : Type} (d : AuditedRange C A) : Prop :=
  ∃ gen : C → Nat, ∀ c ∈ d.commits, ∀ p ∈ d.commits, d.firstParent c = some p → gen p < gen c

/-- **The audit's view of the graph** (A11, A20): the first-parent relation
    is acyclic; a root commit is audited against the empty tree; and a
    commit whose first parent is in the range is that parent's child in the
    sense of `AuditStep` (its parent tree is the parent's tree, a trusted
    parent has its configuration, and an unexamined entry's selection is
    the parent's). -/
structure FirstParentEdges {C A : Type} (d : AuditedRange C A) : Prop where
  acyclic : FirstParentAcyclic d
  root : ∀ c ∈ d.commits, d.firstParent c = none → (d.run c).commit.parent = []
  step : ∀ c ∈ d.commits, ∀ p ∈ d.commits, d.firstParent c = some p → AuditStep (d.run p) (d.run c)

/-- **Induction along first parents.** A property of every commit of the
    range follows from its first parent's, whatever the walk's order. -/
theorem first_parent_induction {C A : Type} (d : AuditedRange C A) (hacyclic : FirstParentAcyclic d)
    (Inv : C → Prop)
    (hstep : ∀ c ∈ d.commits, (∀ p ∈ d.commits, d.firstParent c = some p → Inv p) → Inv c) :
    ∀ c ∈ d.commits, Inv c := by
  obtain ⟨gen, hgen⟩ := hacyclic
  suffices h : ∀ n, ∀ c ∈ d.commits, gen c < n → Inv c from fun c hc => h _ c hc (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro c _ hlt; omega
  | succ n ih =>
    intro c hc hlt
    exact hstep c hc fun p hp hfp => ih p hp (by have := hgen c hc p hp hfp; omega)

/-- **A13: the trusted boundary, with the key.** A commit of the range whose
    first parent lies outside it and that the audit trusted from that parent
    has, under its own configuration's key, a parent whose records and
    selection (under the commit's attributes) authenticate: the parent was
    audited when it was published, or is deliberately excluded. -/
def KeyedBoundaryTrusted {C A : Type} (keys : EpochKeys P) (g : GitState) (d : AuditedRange C A) : Prop :=
  ∀ c ∈ d.commits, ∀ p, d.firstParent c = some p → p ∉ d.commits → (d.run c).base = .Parent →
    ∀ k, keys (d.config c) = some k →
      RecordsAuthentic k.suite (d.config c) g (d.run c).commit.parent ∧
      SelectionAuthentic k.suite (d.config c) g (d.run c).commit.filter (d.run c).commit.parent

/-- **A13: the trusted boundary, without the key.** Likewise for a commit
    whose configuration has no key: its trusted parent's selection has the
    envelope. -/
def KeylessBoundaryTrusted {C A : Type} (keys : EpochKeys P) (σ₀ : Suite) (g : GitState) (d : AuditedRange C A) :
    Prop :=
  ∀ c ∈ d.commits, ∀ p, d.firstParent c = some p → p ∉ d.commits → (d.run c).base = .Parent →
    keys (d.config c) = none →
      SelectionEnveloped (σ₀.digest16 (d.config c)) g (d.run c).commit.filter (d.run c).commit.parent

/-- **The keyed audit of a commit graph.** Take the commits an audit run
    walked (`AuditedRange`), in any order, each audited against its first
    parent (`FirstParentEdges`: an acyclic graph, A11, A20); every commit
    whose configuration has a key (`EpochKeys`, each realizing its suite,
    A5) accepted by the keyed audit with that key (`KeyedAudit`); and the
    trusted boundary (`KeyedBoundaryTrusted`, A13). Then every such commit
    keeps both invariants under its own configuration's key
    (`AuditedCommitAuthentic`). The invariant flows along first parents
    only: a merge is examined as its changes relative to its first parent,
    so nothing about a second parent is used; a configuration change
    (`AuditBase.Tree`) uses nothing from its parent, so no epoch's key
    vouches for another's records. -/
theorem keyed_dag_audit_authenticated {C A : Type} (aans : StagedEvidence A)
    (keys : EpochKeys P) (hkeys : KeysRealize inst keys)
    (g : GitState) (d : AuditedRange C A) (hedges : FirstParentEdges d)
    (haudits : ∀ c ∈ d.commits, ∀ k, keys (d.config c) = some k → KeyedAudit aans inst k.prims k.suite g (d.run c))
    (hboundary : KeyedBoundaryTrusted keys g d) :
    ∀ c ∈ d.commits, ∀ k, keys (d.config c) = some k →
      AuditedCommitAuthentic k.suite (d.config c) g (d.run c).commit := by
  refine first_parent_induction d hedges.acyclic _ fun c hc ih k hk => ?_
  have ha := haudits c hc k hk
  have hR := hkeys _ _ hk
  cases hfp : d.firstParent c with
  | none =>
    -- A root commit: its parent is the empty tree.
    have hroot := hedges.root c hc hfp
    exact keyed_audit_run_authenticated ha hR _
      (fun _ => ⟨(fun x hx => by rw [hroot] at hx; cases hx), (fun x hx => by rw [hroot] at hx; cases hx)⟩)
      (fun _ _ _ _ => rfl)
  | some p =>
    by_cases hp : p ∈ d.commits
    · -- The first parent is audited: the same configuration when trusted, so the same key.
      have hs := hedges.step c hc p hp hfp
      exact keyed_audit_run_authenticated ha hR (d.run p).commit.filter (fun hb => by
          have hcfg : (d.run c).config = (d.run p).config := hs.config hb
          rw [hs.parent, hcfg]
          exact ih p hp hfp k (by simpa [AuditedRange.config, hcfg] using hk))
        hs.selection
    · -- The first parent lies outside the range: trusted (A13).
      exact keyed_audit_run_authenticated ha hR _ (fun hb => hboundary c hc p hfp hp hb k hk)
        (fun _ _ _ _ => rfl)

/-- **The keyless audit of a commit graph.** Under the same graph, every
    commit whose configuration has no key in this checkout, accepted by the
    keyless audit (`KeylessAudit`), with the keyless boundary
    (`KeylessBoundaryTrusted`, A13): every entry its attributes select,
    unless it is metadata, is a regular file with its configuration's
    envelope (`SelectionEnveloped`). Nothing is authenticated: a forged
    envelope passes (A14). -/
theorem keyless_dag_audit_enveloped {C A : Type} (aans : StagedEvidence A) (keys : EpochKeys P) (σ₀ : Suite)
    (g : GitState) (d : AuditedRange C A) (hedges : FirstParentEdges d)
    (haudits : ∀ c ∈ d.commits, keys (d.config c) = none → KeylessAudit aans inst σ₀ g (d.run c))
    (hboundary : KeylessBoundaryTrusted keys σ₀ g d) :
    ∀ c ∈ d.commits, keys (d.config c) = none →
      SelectionEnveloped (σ₀.digest16 (d.config c)) g (d.run c).commit.filter (d.run c).commit.tree := by
  refine first_parent_induction d hedges.acyclic _ fun c hc ih hk => ?_
  have ha := haudits c hc hk
  cases hfp : d.firstParent c with
  | none =>
    have hroot := hedges.root c hc hfp
    exact keyless_audit_run_enveloped ha _ (fun _ x hx => by rw [hroot] at hx; cases hx) (fun _ _ _ _ => rfl)
  | some p =>
    by_cases hp : p ∈ d.commits
    · have hs := hedges.step c hc p hp hfp
      exact keyless_audit_run_enveloped ha (d.run p).commit.filter (fun hb => by
          have hcfg : (d.run c).config = (d.run p).config := hs.config hb
          rw [hs.parent, hcfg]
          exact ih p hp hfp (by simpa [AuditedRange.config, hcfg] using hk))
        hs.selection
    · exact keyless_audit_run_enveloped ha _ (fun hb => hboundary c hc p hfp hp hb hk) (fun _ _ _ _ => rfl)

/-! ## The pre-commit history across a rekey -/

/-- The commit was accepted by a keyed check with its own configuration's
    key. -/
def EpochKeyedCommit {E : Type} (ans : StagedEvidence E) (inst : V3Primitives P) (keys : EpochKeys P)
    (c : CheckedCommit E) : Prop :=
  ∃ k, keys c.config = some k ∧ KeyedCommit ans inst k.prims k.suite c

/-- **A rekey turns the guard off.** If the next commit, made from the
    checked index (`GuardedHistoryStep`), commits another configuration, the
    verified `policy_unchanged` of its check returned `false`: the check
    trusted nothing from `HEAD`. -/
theorem rekey_guard_false {E : Type} {c c' : CheckedCommit E}
    (hgit : HookContracts c.g c.run) (hcfg : ConfigCommitted c.g c.config)
    (hgit' : HookContracts c'.g c'.run) (hcfg' : ConfigCommitted c'.g c'.config)
    (hstep : GuardedHistoryStep c c') (hrekey : c'.config ≠ c.config) :
    c'.run.samePolicy = false := by
  cases hg : c'.run.samePolicy with
  | false => rfl
  | true =>
    exact absurd (config_unchanged_of_guard hgit' hg hstep.commit hstep.policy (hook_snapshots_sorted hgit).1
      hcfg hcfg') hrekey

/-- **A rekey commit starts its epoch.** A commit after one with another
    configuration (a rekey), accepted by a keyed check with the new key,
    keeps the record invariant and authenticates every selected path under
    the new configuration, with no hypothesis about the earlier commit's
    records or key: only its Git run (to know that its configuration
    differs). -/
theorem rekey_commit_starts_epoch {E : Type} (ans : StagedEvidence E) {prims : P} {σ : Suite}
    (hR : Realizes inst prims σ) {c c' : CheckedCommit E}
    (hgit : HookContracts c.g c.run) (hcfg : ConfigCommitted c.g c.config)
    (hc' : KeyedCommit ans inst prims σ c') (hstep : GuardedHistoryStep c c') (hrekey : c'.config ≠ c.config) :
    RecordsAuthentic σ c'.config c'.g c'.g.index ∧ AuthenticatedIndex σ c'.config c'.g := by
  have hoff := rekey_guard_false hgit hcfg hc'.contracts hc'.config hstep hrekey
  exact keyed_check_records_authentic _ _ ans _ _ hR hc'.contracts hc'.accepted
    (fun hg _ => by rw [hoff] at hg; cases hg)

/-- **A history of keyed commits across rekeys.** Take commits
    `h 0, …, h n`, each accepted by a keyed check with the key of its own
    configuration (`EpochKeyedCommit`), each made from the index checked
    before it (`GuardedHistoryStep`), and the first commit's `HEAD` records
    authentic under its key if its check trusted `HEAD`. Then every commit's
    records and selected paths authenticate under its own configuration's
    key. Within an epoch this is `keyed_history_authenticated_by_guard`; at
    a rekey the guard is `false` (`rekey_guard_false`), so the new epoch
    starts from nothing (`rekey_commit_starts_epoch`). -/
theorem epoch_history_authenticated {E : Type} (ans : StagedEvidence E) (keys : EpochKeys P)
    (hkeys : KeysRealize inst keys) (h : Nat → CheckedCommit E) (n : Nat)
    (hcommits : ∀ i ≤ n, EpochKeyedCommit ans inst keys (h i))
    (hsteps : ∀ i < n, GuardedHistoryStep (h i) (h (i + 1)))
    (hstart : (h 0).run.samePolicy = true → (h 0).mode = .incremental →
      ∀ k, keys (h 0).config = some k → RecordsAuthentic k.suite (h 0).config (h 0).g (h 0).g.head) :
    ∀ i ≤ n, ∀ k, keys (h i).config = some k →
      RecordsAuthentic k.suite (h i).config (h i).g (h i).g.index ∧ AuthenticatedIndex k.suite (h i).config (h i).g := by
  intro i hi
  induction i with
  | zero =>
    intro k hk
    obtain ⟨k', hk', hc⟩ := hcommits 0 hi
    rw [hk, Option.some.injEq] at hk'
    subst hk'
    exact keyed_check_records_authentic _ _ ans _ _ (hkeys _ _ hk) hc.contracts hc.accepted
      (fun hg hm => hstart hg hm k hk)
  | succ m ih =>
    intro k hk
    obtain ⟨k', hk', hc⟩ := hcommits (m + 1) hi
    rw [hk, Option.some.injEq] at hk'
    subst hk'
    obtain ⟨_, -, hc0⟩ := hcommits m (by omega)
    have hs := hsteps m (by omega)
    exact keyed_check_records_authentic _ _ ans _ _ (hkeys _ _ hk) hc.contracts hc.accepted (fun hg _ => by
      -- A true guard keeps the configuration, and so the key.
      have hcfg := config_unchanged_of_guard hc.contracts hg hs.commit hs.policy
        (hook_snapshots_sorted hc0.contracts).1 hc0.config hc.config
      rw [hcfg] at hk ⊢
      exact records_authentic_of_checked_commit (ih (by omega) k hk).1 hs.commit rfl)

/-! ## The top-level statement -/

/-- The epoch keys of stored-key decisions, one per configuration: the
    primitives each returned and the suite of its file's own key bytes. -/
def storedEpochKeys (σk : List Nat → Suite) (ks : List Nat → Option (StoredKeyRun P)) : EpochKeys P :=
  fun config => (ks config).map fun k => ⟨k.keyed, k.suite σk⟩

/-- **Every epoch's stored key unlocked**: each configuration's stored-key
    decision (`ks config`, when this checkout has a key for it) returned the
    primitives and that very configuration (`StoredKeyUnlocked`). -/
def StoredKeysUnlocked (inst : V3Primitives P) (sched : V3KeySchedule P) (σk : List Nat → Suite)
    (ks : List Nat → Option (StoredKeyRun P)) : Prop :=
  ∀ config k, ks config = some k → StoredKeyUnlocked inst sched σk k ∧ wireBytes k.config = config

/-- **The audit run of a commit graph with epochs.** The commits one audit
    walked, in any order, each against its first parent (`FirstParentEdges`,
    A11, A20); each commit whose configuration has a stored key accepted by
    the keyed audit with it, each other one by the keyless audit (with
    `AuditContracts` and `AuditAnswers` inside, A4, A19–A21); and the trusted
    boundary of both kinds (A13). -/
structure EpochAuditedRange {C A : Type} (aans : StagedEvidence A) (inst : V3Primitives P) (σk : List Nat → Suite)
    (σ₀ : Suite) (ks : List Nat → Option (StoredKeyRun P)) (g : GitState) (d : AuditedRange C A) : Prop where
  edges : FirstParentEdges d
  keyed : ∀ c ∈ d.commits, ∀ k, ks (d.config c) = some k → KeyedAudit aans inst k.keyed (k.suite σk) g (d.run c)
  keyless : ∀ c ∈ d.commits, ks (d.config c) = none → KeylessAudit aans inst σ₀ g (d.run c)
  keyed_boundary : KeyedBoundaryTrusted (storedEpochKeys σk ks) g d
  keyless_boundary : KeylessBoundaryTrusted (storedEpochKeys σk ks) σ₀ g d

/-- A keyed publication with the stored key of its own configuration. -/
def EpochPublication {E : Type} (ans : StagedEvidence E) (inst : V3Primitives P) (σk : List Nat → Suite)
    (ks : List Nat → Option (StoredKeyRun P)) (c : CheckedCommit E) : Prop :=
  ∃ k, ks c.config = some k ∧ ValidCheckedPublication ans inst σk k c

/-- **How the history starts**: a check that trusted nothing from `HEAD`,
    or a `HEAD` that is a commit of the audited range (Git lists the same
    tree, A20, objects keep their content, A11), whose tree commits the
    configuration it was audited under (`CommitConfig`: the adapter's
    `config_blob`, A20, A11). -/
inductive EpochHistoryStart {C A E : Type} (g : GitState) (d : AuditedRange C A) (c : CheckedCommit E) : Prop
  | full (hmode : c.mode = .full)
  | audited (x : C) (hx : x ∈ d.commits) (hconfig : CommitConfig g (d.run x).commit.tree (d.config x))
      (hhead : c.g.head = (d.run x).commit.tree)
      (hobjects : ∀ oid content, g.blob oid = some content → c.g.blob oid = some content)

/-- **What each epoch's key guarantees** (as in `transcrypt_product_assurance`):
    it is validated for its configuration (`ValidatedCryptoContext`),
    checkout with it releases only authenticated plaintext
    (`AuthenticatedRecovery`), and every repair decided with it launders
    nothing (`NoLaunderingRepair`). -/
structure EpochKeyGuarantees (inst : V3Primitives P) (σk : List Nat → Suite) (k : StoredKeyRun P) : Prop where
  context : ValidatedCryptoContext inst (k.suite σk) (sliceBytes k.file) (sliceBytes k.current) k.keyed k.config
  recovery : AuthenticatedRecovery inst k.keyed (k.suite σk) k.config k.id
  repair : ∀ g run (hc : RepairContracts inst k.keyed g run), run.config = k.config →
    NoLaunderingRepair (k.suite σk) g run (g.index[run.i.val]'hc.entry)

theorem storedEpochKeys_some {σk : List Nat → Suite} {ks : List Nat → Option (StoredKeyRun P)} {config : List Nat}
    {e : EpochKey P} (he : storedEpochKeys σk ks config = some e) :
    ∃ k, ks config = some k ∧ e = ⟨k.keyed, k.suite σk⟩ := by
  cases hk : ks config with
  | none => simp [storedEpochKeys, hk] at he
  | some k =>
    simp only [storedEpochKeys, hk, Option.map_some, Option.some.injEq] at he
    exact ⟨k, rfl, he.symm⟩

theorem storedEpochKeys_none {σk : List Nat → Suite} {ks : List Nat → Option (StoredKeyRun P)} {config : List Nat}
    (he : ks config = none) : storedEpochKeys σk ks config = none := by
  simp [storedEpochKeys, he]

/-- **Transcrypt's product assurance over merges, branches and rekeys.**
    Let each configuration this checkout has a key for have its stored-key
    decision unlocked (`StoredKeysUnlocked`, with `KeyScheduleRealizes`, A5,
    A17). Take one audit run over a commit graph (`EpochAuditedRange`: the
    commits it walked in any order, each against its first parent, the
    first-parent relation acyclic, A11, A20; each commit accepted by the
    keyed audit with its configuration's key or, without one, by the keyless
    audit; the parents outside the range trusted, A13), and a history of
    keyed publications `h 0, …, h n`, each with the key of its own
    configuration (`EpochPublication`), each made by Git from the index
    checked before it (`GuardedHistoryStep`, A22, A11), starting at a check
    that trusted nothing or at a commit of the audited range
    (`EpochHistoryStart`). Then

    * **every epoch's key** (`EpochKeyGuarantees`) is validated for its
      configuration, recovers only authenticated plaintext and repairs
      without laundering;
    * **every audited commit** keeps both invariants under its own
      configuration's key when it has one (`AuditedCommitAuthentic`), and
      otherwise has its configuration's envelope at every selected path
      (`SelectionEnveloped`, no authenticity: A14);
    * **every checked state** of the history is authenticated under its own
      configuration's key (`AuthenticatedRepositoryState`), across rekeys.

    Merges are covered as the audit treats them: compared with the first
    parent only. Not covered: a second parent outside the range (audited by
    nothing), commits outside the range (trusted, A13), the authenticity of
    an epoch whose key this checkout lacks, and everything
    `transcrypt_product_assurance` excludes. -/
theorem transcrypt_product_assurance_dag {C A E : Type} {sched : V3KeySchedule P} {σk : List Nat → Suite}
    (hK : KeyScheduleRealizes inst sched σk)
    (ks : List Nat → Option (StoredKeyRun P)) (hks : StoredKeysUnlocked inst sched σk ks)
    (aans : StagedEvidence A) (σ₀ : Suite) (g : GitState) (d : AuditedRange C A)
    (hrange : EpochAuditedRange aans inst σk σ₀ ks g d)
    (ans : StagedEvidence E) (h : Nat → CheckedCommit E) (n : Nat)
    (hcommits : ∀ i ≤ n, EpochPublication ans inst σk ks (h i))
    (hsteps : ∀ i < n, GuardedHistoryStep (h i) (h (i + 1)))
    (hstart : EpochHistoryStart g d (h 0)) :
    (∀ config k, ks config = some k → EpochKeyGuarantees inst σk k) ∧
    (∀ c ∈ d.commits,
      (∀ k, ks (d.config c) = some k → AuditedCommitAuthentic (k.suite σk) (d.config c) g (d.run c).commit) ∧
      (ks (d.config c) = none →
        SelectionEnveloped (σ₀.digest16 (d.config c)) g (d.run c).commit.filter (d.run c).commit.tree)) ∧
    (∀ i ≤ n, ∀ k, ks (h i).config = some k →
      AuthenticatedRepositoryState (k.suite σk) (h i).config (h i).g) := by
  -- Each epoch's key is a validated context.
  have hctx : ∀ config k, ks config = some k →
      ValidatedCryptoContext inst (k.suite σk) (sliceBytes k.file) (sliceBytes k.current) k.keyed k.config :=
    fun config k hk => stored_key_binds_file_operations hK k.present k.file k.current k.keyed k.config
      (hks config k hk).1.unlock
  have hkeys : KeysRealize inst (storedEpochKeys σk ks) := fun config e he => by
    obtain ⟨k, hk, rfl⟩ := storedEpochKeys_some he
    exact (hctx config k hk).realizes
  -- The audited graph, with keys and without.
  have hdag := keyed_dag_audit_authenticated aans (storedEpochKeys σk ks) hkeys g d hrange.edges
    (fun c hc e he => by
      obtain ⟨k, hk, rfl⟩ := storedEpochKeys_some he
      exact hrange.keyed c hc k hk)
    hrange.keyed_boundary
  have hkeyed : ∀ c ∈ d.commits, ∀ k, ks (d.config c) = some k →
      AuditedCommitAuthentic (k.suite σk) (d.config c) g (d.run c).commit := fun c hc k hk =>
    hdag c hc ⟨k.keyed, k.suite σk⟩ (by simp [storedEpochKeys, hk])
  have hkeyless := keyless_dag_audit_enveloped aans (storedEpochKeys σk ks) σ₀ g d hrange.edges
    (fun c hc he => hrange.keyless c hc (by cases hk : ks (d.config c) <;> simp_all [storedEpochKeys]))
    hrange.keyless_boundary
  -- The history, across epochs.
  have hhist := epoch_history_authenticated ans (storedEpochKeys σk ks) hkeys h n
    (fun i hi => by
      obtain ⟨k, hk, hpub⟩ := hcommits i hi
      exact ⟨⟨k.keyed, k.suite σk⟩, by simp [storedEpochKeys, hk], hpub.toKeyedCommit⟩)
    hsteps
    (fun hg hinc e he => by
      cases hstart with
      | full hmode => rw [hmode] at hinc; cases hinc
      | audited x hx hconfig hhead hobjects =>
        obtain ⟨k, hk, rfl⟩ := storedEpochKeys_some he
        obtain ⟨_, -, hpub⟩ := hcommits 0 (Nat.zero_le n)
        -- A true guard commits `HEAD`'s configuration: the audited commit's, so its key.
        obtain ⟨y, hy, hyp, hyr, hyb⟩ := hconfig
        have hcfg : (h 0).config = d.config x :=
          config_of_guard_head hpub.contracts hg ⟨y, hhead ▸ hy, hyp, hyr, hobjects _ _ hyb⟩ hpub.config
        rw [hcfg] at hk ⊢
        rw [hhead]
        intro z hz hsel
        obtain ⟨content, hc, hra⟩ := (hkeyed x hx k hk).1 z hz hsel
        exact ⟨content, hobjects _ _ hc, hra⟩)
  refine ⟨fun config k hk => ⟨hctx config k hk, ?_, ?_⟩, fun c hc => ⟨hkeyed c hc, fun hk =>
      hkeyless c hc (storedEpochKeys_none hk)⟩, fun i hi k hk => ?_⟩
  · have hR := (hctx config k hk).realizes
    exact ⟨fun unlocked keepRecord path record buf =>
        checkout_releases_only_authenticated_plaintext hR k.config k.id unlocked keepRecord path record buf,
      fun path record buf pt hop hl =>
        checkout_opens_genuine_records hR k.config k.id (hks config k hk).1.id path record buf pt hop hl⟩
  · exact fun g run hc _ => repair_never_launders g run (hctx config k hk).realizes hc
  · obtain ⟨hrec, hsel⟩ := hhist i hi ⟨k.keyed, k.suite σk⟩ (by simp [storedEpochKeys, hk])
    exact ⟨hrec, hsel⟩

end Transcrypt.V3Verification

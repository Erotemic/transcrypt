import V3Wire.Verification.History
import V3Wire.Verification.Recovery

/-!
# Publication: what `git push` sends once the pre-push hook admitted it

`History.lean` proves what an audit run establishes about the commits it
walked, given a trusted boundary: the first parents outside the range
(A13). This file closes the gap between that audit and the push it guards:
which commits the hook audits, which commits Git then sends, where the
boundary lies, which paths count as protected, and what the hook's verdict
requires.

* **The hook's range** (`HookRange`): `pre_push` (`audit.rs`; Bash
  `tc_cmd_pre_push`) runs `git rev-list` on every pushed commit, excluding
  only commits the remote itself reports: its current commit of each
  updated ref (Git's input to the hook) and every commit `git ls-remote` on
  the push URL lists, when this repository has them (`remoteTips`). No
  local ref bounds the range: a remote-tracking ref is a local ref that
  anyone can point at an unaudited commit, and stale after the remote's URL
  changes (H-98). A pushed tip that is no commit (a tag of a tree or blob)
  is refused before the audit (H-97).
* **Git's push contract** (`PushContract`, A30): Git sends only commits
  reachable from a pushed commit and from no ref the remote advertised that
  this repository has; the remote commits the hook learns (its input, and
  `ls-remote`) are ones the remote advertised.
* **Every sent commit was audited** (`sent_audited`), and **every boundary
  parent is the remote's own history** (`boundary_outside`,
  `knownRemote_advertised`): pure graph facts.
* **The committed policy** (`admissionFilter`, H-99): a path counts as
  protected when the commit's own `.gitattributes` alone select it
  (`committed`: Git's answer in an isolated directory, A31) or Git's
  effective attributes do (`effective`: every local source applied). The
  adapter combines Git's two flags with the verified `admission_selected`
  (`admissionFilter_flag`), so no local source unprotects a committed
  path (`selected_admissionFilter`), whatever it says.
* **Authenticated by default** (`push_publishes_authenticated`,
  `push_sends_no_protected_plaintext`, H-100): with
  `transcrypt.requireAuthenticatedPush` anything but an explicit false
  (unset included), an admitted push had an audit that authenticated every
  record it could not trust from the remote (`pushAdmissionSpec_default`;
  in production `push_dispatch`). Then every path a sent commit's
  committed policy (or a local source) protects is a regular file whose
  blob **authenticates at that path** under its configuration's key: this
  checkout's when it has one, the configuration's genuine key otherwise
  (`epochSuite`). An envelope alone (plaintext appended to a record keeps
  it) is not enough. The trusted boundary is the remote's own history
  (`RemoteAuthentic`, A13).
* **The explicit opt-out** (`push_publishes_enveloped`,
  `push_sends_only_records`): with the setting false, an admitted push
  only guarantees that every protected path of a sent commit holds a record
  with its configuration's envelope, which a record with plaintext appended
  also has.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

variable {P : Type} {inst : V3Primitives P}

/-! ## The commit graph -/

/-- `c` reaches `q` along parent links (Git's ancestry, reflexive). -/
inductive Reaches {C : Type} (parents : C → List C) : C → C → Prop
  | refl (c : C) : Reaches parents c c
  | parent {c p q : C} : p ∈ parents c → Reaches parents p q → Reaches parents c q

theorem Reaches.trans {C : Type} {parents : C → List C} {a b c : C} (h1 : Reaches parents a b)
    (h2 : Reaches parents b c) : Reaches parents a c := by
  induction h1 with
  | refl => exact h2
  | parent hp _ ih => exact .parent hp (ih h2)

theorem Reaches.tail {C : Type} {parents : C → List C} {a b p : C} (h : Reaches parents a b)
    (hp : p ∈ parents b) : Reaches parents a p :=
  h.trans (.parent hp (.refl p))

/-- Some commit of `tips` reaches `c`. -/
def ReachedFrom {C : Type} (parents : C → List C) (tips : List C) (c : C) : Prop :=
  ∃ t ∈ tips, Reaches parents t c

/-! ## The hook's range -/

/-- One line of the hook's input as the adapter reads it: the pushed commit
    (`none`: a deletion, which pushes nothing), and the remote's current
    commit of the ref when it is not zero and this repository has it. -/
structure PushUpdate (C : Type) where
  pushed : Option C
  remote : Option C

/-- The remote's commits the hook learns: each updated ref's current commit
    and every commit `ls-remote` listed (`listed`), when this repository has
    them. -/
def remoteTips {C : Type} (ups : List (PushUpdate C)) (listed : List C) : List C :=
  ups.filterMap (·.remote) ++ listed

/-- `c` is reachable from a pushed commit. -/
def Pushed {C : Type} (parents : C → List C) (ups : List (PushUpdate C)) (c : C) : Prop :=
  ∃ u ∈ ups, ∃ l, u.pushed = some l ∧ Reaches parents l c

/-- `c` is reachable from a remote commit the hook learned. -/
def KnownRemote {C : Type} (parents : C → List C) (ups : List (PushUpdate C)) (listed : List C) (c : C) : Prop :=
  ReachedFrom parents (remoteTips ups listed) c

/-- **What the hook audits**: `git rev-list <pushed>... ^<remote>...`, the
    remote commits being those it learned from the remote. No local ref
    (no remote-tracking ref) is excluded. -/
def HookRange {C : Type} (parents : C → List C) (ups : List (PushUpdate C)) (listed : List C) (c : C) : Prop :=
  Pushed parents ups c ∧ ¬ KnownRemote parents ups listed c

/-- **A30: Git's push contract.** After the pre-push hook succeeded, Git
    sends only commits reachable from a pushed commit and from no ref the
    remote advertised that this repository has (`advertised`); the remote
    commit the hook is told for each updated ref, and each commit
    `ls-remote` lists, is one the remote advertised (the remote answers the
    hook's `ls-remote` as it answered the push). -/
structure PushContract {C : Type} (parents : C → List C) (ups : List (PushUpdate C)) (listed : List C)
    (advertised : List C) (sent : C → Prop) : Prop where
  sends : ∀ c, sent c → Pushed parents ups c ∧ ¬ ReachedFrom parents advertised c
  told : ∀ u ∈ ups, ∀ r, u.remote = some r → r ∈ advertised
  listed_advertised : ∀ r ∈ listed, r ∈ advertised

theorem remoteTips_advertised {C : Type} {parents : C → List C} {ups : List (PushUpdate C)} {listed : List C}
    {advertised : List C} {sent : C → Prop} (h : PushContract parents ups listed advertised sent) {r : C}
    (hr : r ∈ remoteTips ups listed) : r ∈ advertised := by
  unfold remoteTips at hr
  rcases List.mem_append.mp hr with h1 | h1
  · obtain ⟨u, hu, hur⟩ := List.mem_filterMap.mp h1
    exact h.told u hu r hur
  · exact h.listed_advertised r h1

/-- **A commit reachable from a remote commit the hook learned is
    reachable from a commit the remote advertised**: it is the remote's own
    history, which Git does not send. -/
theorem knownRemote_advertised {C : Type} {parents : C → List C} {ups : List (PushUpdate C)} {listed : List C}
    {advertised : List C} {sent : C → Prop} (h : PushContract parents ups listed advertised sent) {p : C}
    (hp : KnownRemote parents ups listed p) : ReachedFrom parents advertised p ∧ ¬ sent p := by
  obtain ⟨r, hr, hreach⟩ := hp
  have hadv : ReachedFrom parents advertised p := ⟨r, remoteTips_advertised h hr, hreach⟩
  exact ⟨hadv, fun hs => (h.sends p hs).2 hadv⟩

/-- **Every commit Git sends was audited by the hook.** -/
theorem sent_audited {C : Type} {parents : C → List C} {ups : List (PushUpdate C)} {listed : List C}
    {advertised : List C} {sent : C → Prop} (h : PushContract parents ups listed advertised sent) {c : C}
    (hc : sent c) : HookRange parents ups listed c :=
  ⟨(h.sends c hc).1, fun hk => (knownRemote_advertised h hk).2 hc⟩

/-- **The audit's boundary is the remote's.** A parent of an audited commit
    that the hook did not audit is reachable from a remote commit it
    learned. -/
theorem boundary_outside {C : Type} {parents : C → List C} {ups : List (PushUpdate C)} {listed : List C}
    {c p : C} (hc : HookRange parents ups listed c) (hp : p ∈ parents c)
    (hout : ¬ HookRange parents ups listed p) : KnownRemote parents ups listed p := by
  obtain ⟨⟨u, hu, l, hl, hreach⟩, _⟩ := hc
  have hpushed : Pushed parents ups p := ⟨u, hu, l, hl, hreach.tail hp⟩
  by_cases hk : KnownRemote parents ups listed p
  · exact hk
  · exact absurd ⟨hpushed, hk⟩ hout

/-! ## The committed policy and local attribute sources -/

/-- **The selection publication checks use** (H-99): the committed
    policy's `filter` value where it selects the path, Git's effective
    value (every local attribute source applied) otherwise. -/
def admissionFilter (committed effective : List Nat → List Nat) (path : List Nat) : List Nat :=
  if Selected (committed path) then committed path else effective path

/-- **No local attribute source unprotects a committed path**: the
    admission selection selects exactly what the committed policy or the
    local sources select. -/
theorem selected_admissionFilter {committed effective : List Nat → List Nat} {path : List Nat} :
    Selected (admissionFilter committed effective path) ↔ Selected (committed path) ∨ Selected (effective path) := by
  unfold admissionFilter
  by_cases h : Selected (committed path) <;> simp [h]

/-- **The adapter's flag is the model's selection**: the verified
    `admission_selected` (`admission_selected_spec`) of Git's committed and
    effective flags for a path is whether the admission selection selects
    it. -/
theorem admissionFilter_flag (committed effective : List Nat → List Nat) (path : List Nat) :
    decide (Selected (admissionFilter committed effective path)) =
      admissionSelectedSpec (decide (Selected (committed path))) (decide (Selected (effective path))) := by
  unfold admissionSelectedSpec
  by_cases h1 : Selected (committed path) <;> by_cases h2 : Selected (effective path) <;>
    simp [admissionFilter, h1, h2]

/-! ## The hook's audit run -/

/-- **A20, A19: the hook's audit is of the hook's range.** The audit run
    walked exactly the commits `rev-list` printed for the range
    (`commits`), with Git's parents (`--parents`); it audited each commit's
    own tree and attributes under its own configuration; and a commit it
    compared with a first parent outside the range compared with that
    parent's tree, under the same configuration and the same selection
    when it trusted the parent (no attribute file or config changed). -/
structure HookAudit {C A : Type} (parents : C → List C) (ups : List (PushUpdate C)) (listed : List C)
    (tree : C → List Entry) (filter : C → List Nat → List Nat) (config : C → List Nat) (d : AuditedRange C A) :
    Prop where
  commits_iff : ∀ c, c ∈ d.commits ↔ HookRange parents ups listed c
  parents_eq : d.parents = parents
  tree_eq : ∀ c ∈ d.commits, (d.run c).commit.tree = tree c
  filter_eq : ∀ c ∈ d.commits, (d.run c).commit.filter = filter c
  config_eq : ∀ c ∈ d.commits, d.config c = config c
  boundary_tree : ∀ c ∈ d.commits, ∀ p, d.firstParent c = some p → p ∉ d.commits →
    (d.run c).commit.parent = tree p
  boundary_config : ∀ c ∈ d.commits, ∀ p, d.firstParent c = some p → p ∉ d.commits →
    (d.run c).base = .Parent → config c = config p
  boundary_selection : ∀ c ∈ d.commits, ∀ p, d.firstParent c = some p → p ∉ d.commits →
    (d.run c).base = .Parent → ∀ x ∈ tree p, filter c x.path = filter p x.path

/-! ## What a published commit keeps -/

/-- With the key of its configuration, a commit's records and selection
    authenticate. -/
def CommitKeyed {C : Type} (keys : EpochKeys P) (g : GitState) (tree : C → List Entry)
    (filter : C → List Nat → List Nat) (config : C → List Nat) (c : C) : Prop :=
  ∀ k, keys (config c) = some k →
    RecordsAuthentic k.suite (config c) g (tree c) ∧ SelectionAuthentic k.suite (config c) g (filter c) (tree c)

/-- Without it, its records and selection authenticate under `real` of its
    configuration: the suite of that configuration's genuine key. -/
def CommitAuthenticUnder {C : Type} (keys : EpochKeys P) (real : List Nat → Suite) (g : GitState)
    (tree : C → List Entry) (filter : C → List Nat → List Nat) (config : C → List Nat) (c : C) : Prop :=
  keys (config c) = none →
    RecordsAuthentic (real (config c)) (config c) g (tree c) ∧
      SelectionAuthentic (real (config c)) (config c) g (filter c) (tree c)

/-- Without it, its selection has the configuration's envelope. -/
def CommitEnveloped {C : Type} (keys : EpochKeys P) (σ₀ : Suite) (g : GitState) (tree : C → List Entry)
    (filter : C → List Nat → List Nat) (config : C → List Nat) (c : C) : Prop :=
  keys (config c) = none → SelectionEnveloped (σ₀.digest16 (config c)) g (filter c) (tree c)

/-- The suite a configuration's records authenticate under: this
    checkout's key's when it has one, `real` (the genuine key's)
    otherwise. -/
def epochSuite (keys : EpochKeys P) (real : List Nat → Suite) (config : List Nat) : Suite :=
  match keys config with
  | some k => k.suite
  | none => real config

/-- **A13, for a push: the remote's own history was admitted
    authenticated.** Every commit reachable from a remote commit the hook
    learned (which the remote advertised: `knownRemote_advertised`)
    authenticates under its configuration's key: it is already on the
    remote, admitted when it was pushed there (by this default) or by the
    remote's own audit. Nothing is assumed of any local ref. -/
def RemoteAuthentic {C : Type} (keys : EpochKeys P) (real : List Nat → Suite) (g : GitState)
    (parents : C → List C) (ups : List (PushUpdate C)) (listed : List C) (tree : C → List Entry)
    (filter : C → List Nat → List Nat) (config : C → List Nat) : Prop :=
  ∀ p, KnownRemote parents ups listed p →
    CommitKeyed keys g tree filter config p ∧ CommitAuthenticUnder keys real g tree filter config p

/-- **A13, for the opt-out: the remote's own history was admitted.** As
    `RemoteAuthentic`, with only the envelope where this checkout has no
    key. -/
def RemoteAdmitted {C : Type} (keys : EpochKeys P) (σ₀ : Suite) (g : GitState) (parents : C → List C)
    (ups : List (PushUpdate C)) (listed : List C) (tree : C → List Entry) (filter : C → List Nat → List Nat)
    (config : C → List Nat) : Prop :=
  ∀ p, KnownRemote parents ups listed p →
    CommitKeyed keys g tree filter config p ∧ CommitEnveloped keys σ₀ g tree filter config p

theorem firstParent_mem {C A : Type} {d : AuditedRange C A} {c p : C} (h : d.firstParent c = some p) :
    p ∈ d.parents c := by
  unfold AuditedRange.firstParent at h
  cases hp : d.parents c with
  | nil => rw [hp] at h; cases h
  | cons q qs =>
    rw [hp] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact List.mem_cons_self

/-- A parent the hook did not audit is the remote's. -/
theorem boundary_published {C A : Type} {parents : C → List C} {ups : List (PushUpdate C)} {listed : List C}
    {tree : C → List Entry} {filter : C → List Nat → List Nat} {config : C → List Nat} {d : AuditedRange C A}
    (haudit : HookAudit parents ups listed tree filter config d) {c p : C} (hc : c ∈ d.commits)
    (hfp : d.firstParent c = some p) (hp : p ∉ d.commits) : KnownRemote parents ups listed p := by
  have hmem : p ∈ parents c := haudit.parents_eq ▸ firstParent_mem hfp
  exact boundary_outside ((haudit.commits_iff c).mp hc) hmem (fun h => hp ((haudit.commits_iff p).mpr h))

/-- **The keyed boundary of the hook's audit is trusted** when the remote's
    history authenticates with the key. -/
theorem keyed_boundary_of_published {C A : Type} {keys : EpochKeys P} {g : GitState}
    {parents : C → List C} {ups : List (PushUpdate C)} {listed : List C} {tree : C → List Entry}
    {filter : C → List Nat → List Nat} {config : C → List Nat} {d : AuditedRange C A}
    (haudit : HookAudit parents ups listed tree filter config d)
    (hpub : ∀ p, KnownRemote parents ups listed p → CommitKeyed keys g tree filter config p) :
    KeyedBoundaryTrusted keys g d := by
  intro c hc p hfp hp hbase k hk
  have hcfg : d.config c = config p := (haudit.config_eq c hc).trans (haudit.boundary_config c hc p hfp hp hbase)
  rw [hcfg] at hk ⊢
  obtain ⟨hrec, hsel⟩ := hpub p (boundary_published haudit hc hfp hp) k hk
  rw [haudit.boundary_tree c hc p hfp hp, haudit.filter_eq c hc]
  refine ⟨hrec, fun x hx hs hr => hsel x hx ?_ hr⟩
  rwa [← haudit.boundary_selection c hc p hfp hp hbase x hx]

/-- **The keyless boundary is trusted under the genuine keys** when the
    remote's history authenticates under them. -/
theorem keyless_boundary_authentic_of_published {C A : Type} {keys : EpochKeys P} {real : List Nat → Suite}
    {g : GitState} {parents : C → List C} {ups : List (PushUpdate C)} {listed : List C} {tree : C → List Entry}
    {filter : C → List Nat → List Nat} {config : C → List Nat} {d : AuditedRange C A}
    (haudit : HookAudit parents ups listed tree filter config d)
    (hpub : ∀ p, KnownRemote parents ups listed p → CommitAuthenticUnder keys real g tree filter config p) :
    KeylessBoundaryAuthenticUnder keys real g d := by
  intro c hc p hfp hp hbase hk
  have hcfg : d.config c = config p := (haudit.config_eq c hc).trans (haudit.boundary_config c hc p hfp hp hbase)
  rw [hcfg] at hk ⊢
  obtain ⟨hrec, hsel⟩ := hpub p (boundary_published haudit hc hfp hp) hk
  rw [haudit.boundary_tree c hc p hfp hp, haudit.filter_eq c hc]
  refine ⟨hrec, fun x hx hs hr => hsel x hx ?_ hr⟩
  rwa [← haudit.boundary_selection c hc p hfp hp hbase x hx]

/-- **The keyless boundary has the envelope** when the remote's history
    has it. -/
theorem keyless_boundary_of_published {C A : Type} {keys : EpochKeys P} {σ₀ : Suite} {g : GitState}
    {parents : C → List C} {ups : List (PushUpdate C)} {listed : List C} {tree : C → List Entry}
    {filter : C → List Nat → List Nat} {config : C → List Nat} {d : AuditedRange C A}
    (haudit : HookAudit parents ups listed tree filter config d)
    (hpub : ∀ p, KnownRemote parents ups listed p → CommitEnveloped keys σ₀ g tree filter config p) :
    KeylessBoundaryTrusted keys σ₀ g d := by
  intro c hc p hfp hp hbase hk
  have hcfg : d.config c = config p := (haudit.config_eq c hc).trans (haudit.boundary_config c hc p hfp hp hbase)
  rw [hcfg] at hk ⊢
  have hsel := hpub p (boundary_published haudit hc hfp hp) hk
  rw [haudit.boundary_tree c hc p hfp hp, haudit.filter_eq c hc]
  intro x hx hs hr
  exact hsel x hx (by rwa [← haudit.boundary_selection c hc p hfp hp hbase x hx]) hr

/-- The keyed part, shared by both verdicts: a sent commit whose
    configuration has a key here authenticates under it. -/
theorem push_sent_keyed {C A : Type} (aans : StagedEvidence A) (acache : AuditedEntries A)
    (keys : EpochKeys P) (hkeys : KeysRealize inst keys) (g : GitState)
    {parents : C → List C} {ups : List (PushUpdate C)} {listed advertised : List C} {sent : C → Prop}
    {tree : C → List Entry} {filter : C → List Nat → List Nat} {config : C → List Nat} (d : AuditedRange C A)
    (hcontract : PushContract parents ups listed advertised sent)
    (haudit : HookAudit parents ups listed tree filter config d) (hedges : FirstParentEdges d)
    (hkeyed : ∀ c ∈ d.commits, ∀ k, keys (d.config c) = some k → KeyedAudit aans acache inst k.prims k.suite g (d.run c))
    (hpub : ∀ p, KnownRemote parents ups listed p → CommitKeyed keys g tree filter config p) :
    ∀ c, sent c → CommitKeyed keys g tree filter config c := by
  intro c hc k hk
  have hcd : c ∈ d.commits := (haudit.commits_iff c).mpr (sent_audited hcontract hc)
  have hcfg := haudit.config_eq c hcd
  have h := keyed_dag_audit_authenticated aans acache keys hkeys g d hedges hkeyed
    (keyed_boundary_of_published haudit hpub) c hcd k (by rw [hcfg]; exact hk)
  unfold AuditedCommitAuthentic at h
  rw [hcfg, haudit.tree_eq c hcd, haudit.filter_eq c hcd] at h
  exact h

/-! ## The default: authenticated publication -/

/-- **What a push admitted by default publishes.** Take the hook's audit of
    its range (`HookAudit`, A19, A20), accepted for every commit, keyed
    where this checkout has the configuration's key (each realizing its
    suite, A5) and keyless otherwise, along Git's first parents
    (`FirstParentEdges`, A11, A20); Git's push contract (`PushContract`,
    A30); the adapter's run flag (`hflag`: `authenticated` only when every
    keyless commit's verified `commit_needs_no_key` answered `true`); the
    hook's verdict with any setting but an explicit false not `refuse`
    (`hadmit`, `hsetting`); and the remote's own history authentic
    (`RemoteAuthentic`, A13). Then every commit Git sends authenticates
    under its configuration's key: this checkout's where it has it, the
    configuration's genuine key (`real`, any suite with the
    configuration's id) otherwise. -/
theorem push_publishes_authenticated {C A : Type} (aans : StagedEvidence A) (acache : AuditedEntries A)
    (keys : EpochKeys P) (hkeys : KeysRealize inst keys) (σ₀ : Suite) (real : List Nat → Suite)
    (hreal : ∀ config, (real config).digest16 config = σ₀.digest16 config) (g : GitState)
    {parents : C → List C} {ups : List (PushUpdate C)} {listed advertised : List C} {sent : C → Prop}
    {tree : C → List Entry} {filter : C → List Nat → List Nat} {config : C → List Nat} (d : AuditedRange C A)
    (hcontract : PushContract parents ups listed advertised sent)
    (haudit : HookAudit parents ups listed tree filter config d) (hedges : FirstParentEdges d)
    (hkeyed : ∀ c ∈ d.commits, ∀ k, keys (d.config c) = some k → KeyedAudit aans acache inst k.prims k.suite g (d.run c))
    (hkeyless : ∀ c ∈ d.commits, keys (d.config c) = none → KeylessAudit aans acache inst σ₀ g (d.run c))
    {authenticated : Bool} {setting : Transcrypt.V3Policy.PushSetting}
    (hflag : authenticated = true → ∀ c ∈ d.commits, keys (d.config c) = none →
      KeylessNeedsNoKey aans acache (d.run c).id (d.run c).base (d.run c).run)
    (hsetting : setting ≠ .disabled)
    (hadmit : pushAdmissionSpec authenticated (authenticatedPushRequiredSpec setting) ≠ .refuse)
    (hremote : RemoteAuthentic keys real g parents ups listed tree filter config) :
    ∀ c, sent c → CommitKeyed keys g tree filter config c ∧ CommitAuthenticUnder keys real g tree filter config c := by
  have hauth := pushAdmissionSpec_default hsetting hadmit
  intro c hc
  refine ⟨push_sent_keyed aans acache keys hkeys g d hcontract haudit hedges hkeyed (fun p hp => (hremote p hp).1) c hc,
    fun hk => ?_⟩
  have hcd : c ∈ d.commits := (haudit.commits_iff c).mpr (sent_audited hcontract hc)
  have hcfg := haudit.config_eq c hcd
  have h := keyless_dag_audit_authenticated_under (inst := inst) aans acache keys σ₀ real hreal g d hedges hkeyless
    (hflag hauth) (keyless_boundary_authentic_of_published haudit (fun p hp => (hremote p hp).2)) c hcd
    (by rw [hcfg]; exact hk)
  unfold AuditedCommitAuthentic at h
  rw [hcfg, haudit.tree_eq c hcd, haudit.filter_eq c hcd] at h
  exact h

/-- **No protected plaintext is sent, by default.** Under the hypotheses of
    `push_publishes_authenticated`, with the audit's selection the
    admission selection of each commit's committed policy and Git's
    effective attributes (`hfilter`, H-99): every path of a sent commit
    that its committed `.gitattributes` protect, or a local attribute
    source protects, unless it is metadata, is a regular file whose blob
    authenticates at that path under its configuration's key
    (`epochSuite`). A local source cannot unprotect a committed path, and an
    envelope alone is not enough: plaintext appended to a record does not
    authenticate. -/
theorem push_sends_no_protected_plaintext {C A : Type} (aans : StagedEvidence A) (acache : AuditedEntries A)
    (keys : EpochKeys P) (hkeys : KeysRealize inst keys) (σ₀ : Suite) (real : List Nat → Suite)
    (hreal : ∀ config, (real config).digest16 config = σ₀.digest16 config) (g : GitState)
    {parents : C → List C} {ups : List (PushUpdate C)} {listed advertised : List C} {sent : C → Prop}
    {tree : C → List Entry} {filter committed effective : C → List Nat → List Nat} {config : C → List Nat}
    (d : AuditedRange C A)
    (hfilter : ∀ c path, filter c path = admissionFilter (committed c) (effective c) path)
    (hcontract : PushContract parents ups listed advertised sent)
    (haudit : HookAudit parents ups listed tree filter config d) (hedges : FirstParentEdges d)
    (hkeyed : ∀ c ∈ d.commits, ∀ k, keys (d.config c) = some k → KeyedAudit aans acache inst k.prims k.suite g (d.run c))
    (hkeyless : ∀ c ∈ d.commits, keys (d.config c) = none → KeylessAudit aans acache inst σ₀ g (d.run c))
    {authenticated : Bool} {setting : Transcrypt.V3Policy.PushSetting}
    (hflag : authenticated = true → ∀ c ∈ d.commits, keys (d.config c) = none →
      KeylessNeedsNoKey aans acache (d.run c).id (d.run c).base (d.run c).run)
    (hsetting : setting ≠ .disabled)
    (hadmit : pushAdmissionSpec authenticated (authenticatedPushRequiredSpec setting) ≠ .refuse)
    (hremote : RemoteAuthentic keys real g parents ups listed tree filter config) :
    ∀ c, sent c → ∀ x ∈ tree c, Selected (committed c x.path) ∨ Selected (effective c x.path) → ¬ Reserved x.path →
      x.Regular ∧ ∃ content, g.blob x.oid = some content ∧
        AuthenticatedAt (epochSuite keys real (config c)) (config c) x content := by
  intro c hc x hx hs hr
  have hsel : Selected (filter c x.path) := by
    rw [hfilter]; exact selected_admissionFilter.mpr hs
  obtain ⟨hk, hl⟩ := push_publishes_authenticated aans acache keys hkeys σ₀ real hreal g d hcontract haudit hedges
    hkeyed hkeyless hflag hsetting hadmit hremote c hc
  cases hkey : keys (config c) with
  | none =>
    simp only [epochSuite, hkey]
    exact (hl hkey).2 x hx hsel hr
  | some k =>
    simp only [epochSuite, hkey]
    exact (hk k hkey).2 x hx hsel hr

/-- **The committed policy decides, by default** (H-99): the case of
    `push_sends_no_protected_plaintext` for a path the committed policy
    protects, whatever the local attribute sources (`effective`) say. -/
theorem committed_protection_published {C A : Type} (aans : StagedEvidence A) (acache : AuditedEntries A)
    (keys : EpochKeys P) (hkeys : KeysRealize inst keys) (σ₀ : Suite) (real : List Nat → Suite)
    (hreal : ∀ config, (real config).digest16 config = σ₀.digest16 config) (g : GitState)
    {parents : C → List C} {ups : List (PushUpdate C)} {listed advertised : List C} {sent : C → Prop}
    {tree : C → List Entry} {filter committed effective : C → List Nat → List Nat} {config : C → List Nat}
    (d : AuditedRange C A)
    (hfilter : ∀ c path, filter c path = admissionFilter (committed c) (effective c) path)
    (hcontract : PushContract parents ups listed advertised sent)
    (haudit : HookAudit parents ups listed tree filter config d) (hedges : FirstParentEdges d)
    (hkeyed : ∀ c ∈ d.commits, ∀ k, keys (d.config c) = some k → KeyedAudit aans acache inst k.prims k.suite g (d.run c))
    (hkeyless : ∀ c ∈ d.commits, keys (d.config c) = none → KeylessAudit aans acache inst σ₀ g (d.run c))
    {authenticated : Bool} {setting : Transcrypt.V3Policy.PushSetting}
    (hflag : authenticated = true → ∀ c ∈ d.commits, keys (d.config c) = none →
      KeylessNeedsNoKey aans acache (d.run c).id (d.run c).base (d.run c).run)
    (hsetting : setting ≠ .disabled)
    (hadmit : pushAdmissionSpec authenticated (authenticatedPushRequiredSpec setting) ≠ .refuse)
    (hremote : RemoteAuthentic keys real g parents ups listed tree filter config) :
    ∀ c, sent c → ∀ x ∈ tree c, Selected (committed c x.path) → ¬ Reserved x.path →
      x.Regular ∧ ∃ content, g.blob x.oid = some content ∧
        AuthenticatedAt (epochSuite keys real (config c)) (config c) x content :=
  fun c hc x hx hs => push_sends_no_protected_plaintext aans acache keys hkeys σ₀ real hreal g d hfilter hcontract
    haudit hedges hkeyed hkeyless hflag hsetting hadmit hremote c hc x hx (Or.inl hs)

/-! ## The explicit opt-out: envelopes only -/

/-- **What any admitted push publishes**, the explicit opt-out
    (`transcrypt.requireAuthenticatedPush=false`) included: under the
    hypotheses of `push_publishes_authenticated` without the verdict's, and
    with the remote's history admitted (`RemoteAdmitted`), every commit Git
    sends authenticates where this checkout has its configuration's key,
    and otherwise only has that configuration's envelope at every selected
    path: a record with plaintext appended has it too. -/
theorem push_publishes_enveloped {C A : Type} (aans : StagedEvidence A) (acache : AuditedEntries A)
    (keys : EpochKeys P) (hkeys : KeysRealize inst keys) (σ₀ : Suite) (g : GitState)
    {parents : C → List C} {ups : List (PushUpdate C)} {listed advertised : List C} {sent : C → Prop}
    {tree : C → List Entry} {filter : C → List Nat → List Nat} {config : C → List Nat} (d : AuditedRange C A)
    (hcontract : PushContract parents ups listed advertised sent)
    (haudit : HookAudit parents ups listed tree filter config d) (hedges : FirstParentEdges d)
    (hkeyed : ∀ c ∈ d.commits, ∀ k, keys (d.config c) = some k → KeyedAudit aans acache inst k.prims k.suite g (d.run c))
    (hkeyless : ∀ c ∈ d.commits, keys (d.config c) = none → KeylessAudit aans acache inst σ₀ g (d.run c))
    (hpub : RemoteAdmitted keys σ₀ g parents ups listed tree filter config) :
    ∀ c, sent c → CommitKeyed keys g tree filter config c ∧ CommitEnveloped keys σ₀ g tree filter config c := by
  intro c hc
  refine ⟨push_sent_keyed aans acache keys hkeys g d hcontract haudit hedges hkeyed (fun p hp => (hpub p hp).1) c hc,
    fun hk => ?_⟩
  have hcd : c ∈ d.commits := (haudit.commits_iff c).mpr (sent_audited hcontract hc)
  have hcfg := haudit.config_eq c hcd
  have h := keyless_dag_audit_enveloped (inst := inst) aans acache keys σ₀ g d hedges hkeyless
    (keyless_boundary_of_published haudit (fun p hp => (hpub p hp).2)) c hcd (by rw [hcfg]; exact hk)
  rw [hcfg, haudit.tree_eq c hcd, haudit.filter_eq c hcd] at h
  exact h

/-- **Only records are sent, whatever the verdict's setting.** Under the
    hypotheses of `push_publishes_enveloped`, every path that a sent
    commit's selection protects, unless it is metadata, is a regular file
    whose blob has a record envelope. This is all the explicit opt-out
    guarantees. -/
theorem push_sends_only_records {C A : Type} (aans : StagedEvidence A) (acache : AuditedEntries A)
    (keys : EpochKeys P) (hkeys : KeysRealize inst keys) (σ₀ : Suite) (g : GitState)
    {parents : C → List C} {ups : List (PushUpdate C)} {listed advertised : List C} {sent : C → Prop}
    {tree : C → List Entry} {filter : C → List Nat → List Nat} {config : C → List Nat} (d : AuditedRange C A)
    (hcontract : PushContract parents ups listed advertised sent)
    (haudit : HookAudit parents ups listed tree filter config d) (hedges : FirstParentEdges d)
    (hkeyed : ∀ c ∈ d.commits, ∀ k, keys (d.config c) = some k → KeyedAudit aans acache inst k.prims k.suite g (d.run c))
    (hkeyless : ∀ c ∈ d.commits, keys (d.config c) = none → KeylessAudit aans acache inst σ₀ g (d.run c))
    (hpub : RemoteAdmitted keys σ₀ g parents ups listed tree filter config) :
    ∀ c, sent c → ∀ x ∈ tree c, Selected (filter c x.path) → ¬ Reserved x.path →
      x.Regular ∧ ∃ content id, g.blob x.oid = some content ∧ EnvelopeOk content id := by
  intro c hc x hx hs hr
  obtain ⟨hk, hl⟩ := push_publishes_enveloped aans acache keys hkeys σ₀ g d hcontract haudit hedges
    hkeyed hkeyless hpub c hc
  cases hkey : keys (config c) with
  | none =>
    obtain ⟨hreg, content, hblob, henv⟩ := hl hkey x hx hs hr
    exact ⟨hreg, content, _, hblob, henv⟩
  | some k =>
    obtain ⟨hreg, content, hblob, pt, hopen⟩ := (hk k hkey).2 x hx hs hr
    exact ⟨hreg, content, _, hblob, opensTo_envelopeOk _ hopen⟩

end Transcrypt.V3Verification

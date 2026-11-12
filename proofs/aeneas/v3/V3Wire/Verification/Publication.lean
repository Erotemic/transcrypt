import V3Wire.Verification.History

/-!
# Publication: what `git push` sends once the pre-push hook admitted it

`History.lean` proves what an audit run establishes about the commits it
walked, given a trusted boundary: the first parents outside the range
(A13). This file closes the gap between that audit and the push it guards:
which commits the hook audits, which commits Git then sends, and where the
boundary lies.

* **The hook's range** (`HookRange`): `pre_push` (`audit.rs`; Bash
  `tc_cmd_pre_push`) runs `git rev-list` on every pushed commit, excluding
  the remote's current commit of each updated ref when this repository has
  it and, for a remote given by name, this remote's tracking refs
  (`--not --remotes=<name>`). A pushed tip that is no commit (a tag of a
  tree or blob, whose files `rev-list` would not walk) is refused before
  the audit, so every pushed object Git sends belongs to a pushed commit.
* **Git's push contract** (`PushContract`, A30): Git sends only commits
  reachable from a pushed commit and from no ref the remote advertised that
  this repository has; the remote commit the hook is told for an updated
  ref is one the remote advertised.
* **Every sent commit was audited, or lies behind a tracking ref**
  (`sent_audited_or_tracked`), and **every boundary parent is the remote's
  or a tracking ref's** (`boundary_outside`): pure graph facts.
* **No protected plaintext is sent** (`push_publishes_no_protected_plaintext`,
  `push_sends_no_protected_plaintext`): if the hook's audit accepted every
  commit of its range (keyed where this checkout has the configuration's
  key, keyless otherwise), then every commit Git sends keeps the record
  invariant under its own attributes: with the key, every selected path
  authenticates at that path; without it, has its configuration's envelope.
  In particular no path a sent commit's own attributes select holds
  anything but a v3 record. The trusted boundary is no longer an arbitrary
  parent (A13) but the remote's own history and this remote's tracking refs
  (`PublishedAdmitted`, A13): commits that are already public, or that an
  earlier push admitted.
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

/-- `c` is reachable from a pushed commit. -/
def Pushed {C : Type} (parents : C → List C) (ups : List (PushUpdate C)) (c : C) : Prop :=
  ∃ u ∈ ups, ∃ l, u.pushed = some l ∧ Reaches parents l c

/-- `c` is reachable from a remote commit the hook was told of. -/
def KnownRemote {C : Type} (parents : C → List C) (ups : List (PushUpdate C)) (c : C) : Prop :=
  ∃ u ∈ ups, ∃ r, u.remote = some r ∧ Reaches parents r c

/-- **What the hook audits**: `git rev-list <pushed>... ^<remote>... --not
    --remotes=<name>` (`tracking`: this remote's tracking refs; none for a
    remote given by URL). -/
def HookRange {C : Type} (parents : C → List C) (ups : List (PushUpdate C)) (tracking : List C) (c : C) : Prop :=
  Pushed parents ups c ∧ ¬ KnownRemote parents ups c ∧ ¬ ReachedFrom parents tracking c

/-- **A30: Git's push contract.** After the pre-push hook succeeded, Git
    sends only commits reachable from a pushed commit and from no ref the
    remote advertised that this repository has (`advertised`); the remote
    commit the hook is told for each updated ref is one it advertised. -/
structure PushContract {C : Type} (parents : C → List C) (ups : List (PushUpdate C)) (advertised : List C)
    (sent : C → Prop) : Prop where
  sends : ∀ c, sent c → Pushed parents ups c ∧ ¬ ReachedFrom parents advertised c
  told : ∀ u ∈ ups, ∀ r, u.remote = some r → r ∈ advertised

/-- **Every commit Git sends was audited by the hook, or lies behind one of
    this remote's tracking refs.** -/
theorem sent_audited_or_tracked {C : Type} {parents : C → List C} {ups : List (PushUpdate C)}
    {advertised tracking : List C} {sent : C → Prop} (h : PushContract parents ups advertised sent) {c : C}
    (hc : sent c) : HookRange parents ups tracking c ∨ ReachedFrom parents tracking c := by
  obtain ⟨hpushed, hadv⟩ := h.sends c hc
  by_cases ht : ReachedFrom parents tracking c
  · exact Or.inr ht
  · refine Or.inl ⟨hpushed, ?_, ht⟩
    rintro ⟨u, hu, r, hr, hreach⟩
    exact hadv ⟨r, h.told u hu r hr, hreach⟩

/-- **The audit's boundary is the remote's or a tracking ref's.** A parent
    of an audited commit that the hook did not audit is reachable from a
    remote commit it was told of, or from a tracking ref. -/
theorem boundary_outside {C : Type} {parents : C → List C} {ups : List (PushUpdate C)} {tracking : List C}
    {c p : C} (hc : HookRange parents ups tracking c) (hp : p ∈ parents c)
    (hout : ¬ HookRange parents ups tracking p) :
    KnownRemote parents ups p ∨ ReachedFrom parents tracking p := by
  obtain ⟨⟨u, hu, l, hl, hreach⟩, _, _⟩ := hc
  have hpushed : Pushed parents ups p := ⟨u, hu, l, hl, hreach.tail hp⟩
  by_cases hk : KnownRemote parents ups p
  · exact Or.inl hk
  · by_cases ht : ReachedFrom parents tracking p
    · exact Or.inr ht
    · exact absurd ⟨hpushed, hk, ht⟩ hout

/-! ## The hook's audit run -/

/-- **A20, A19: the hook's audit is of the hook's range.** The audit run
    walked exactly the commits `rev-list` printed for the range
    (`commits`), with Git's parents (`--parents`); it audited each commit's
    own tree and attributes under its own configuration; and a commit it
    compared with a first parent outside the range compared with that
    parent's tree, under the same configuration and the same selection
    when it trusted the parent (no attribute file or config changed). -/
structure HookAudit {C A : Type} (parents : C → List C) (ups : List (PushUpdate C)) (tracking : List C)
    (tree : C → List Entry) (filter : C → List Nat → List Nat) (config : C → List Nat) (d : AuditedRange C A) :
    Prop where
  commits_iff : ∀ c, c ∈ d.commits ↔ HookRange parents ups tracking c
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

/-- Without it, its selection has the configuration's envelope. -/
def CommitEnveloped {C : Type} (keys : EpochKeys P) (σ₀ : Suite) (g : GitState) (tree : C → List Entry)
    (filter : C → List Nat → List Nat) (config : C → List Nat) (c : C) : Prop :=
  keys (config c) = none → SelectionEnveloped (σ₀.digest16 (config c)) g (filter c) (tree c)

/-- **A13, for a push: published history was admitted.** Every commit
    reachable from a remote commit the hook was told of, or from this
    remote's tracking refs, keeps the record invariant: it is the remote's
    own history (audited when it was pushed there, or by the remote's
    pre-receive audit), or an earlier push of this repository that the hook
    admitted (Git updates a tracking ref after a push or a fetch). -/
def PublishedAdmitted {C : Type} (keys : EpochKeys P) (σ₀ : Suite) (g : GitState) (parents : C → List C)
    (ups : List (PushUpdate C)) (tracking : List C) (tree : C → List Entry) (filter : C → List Nat → List Nat)
    (config : C → List Nat) : Prop :=
  ∀ p, KnownRemote parents ups p ∨ ReachedFrom parents tracking p →
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

/-- A parent the hook did not audit is published. -/
theorem boundary_published {C A : Type} {parents : C → List C} {ups : List (PushUpdate C)} {tracking : List C}
    {tree : C → List Entry} {filter : C → List Nat → List Nat} {config : C → List Nat} {d : AuditedRange C A}
    (haudit : HookAudit parents ups tracking tree filter config d) {c p : C} (hc : c ∈ d.commits)
    (hfp : d.firstParent c = some p) (hp : p ∉ d.commits) :
    KnownRemote parents ups p ∨ ReachedFrom parents tracking p := by
  have hmem : p ∈ parents c := haudit.parents_eq ▸ firstParent_mem hfp
  exact boundary_outside ((haudit.commits_iff c).mp hc) hmem (fun h => hp ((haudit.commits_iff p).mpr h))

/-- **The keyed boundary of the hook's audit is trusted** when published
    history was admitted. -/
theorem keyed_boundary_of_published {C A : Type} {keys : EpochKeys P} {σ₀ : Suite} {g : GitState}
    {parents : C → List C} {ups : List (PushUpdate C)} {tracking : List C} {tree : C → List Entry}
    {filter : C → List Nat → List Nat} {config : C → List Nat} {d : AuditedRange C A}
    (haudit : HookAudit parents ups tracking tree filter config d)
    (hpub : PublishedAdmitted keys σ₀ g parents ups tracking tree filter config) :
    KeyedBoundaryTrusted keys g d := by
  intro c hc p hfp hp hbase k hk
  have hcfg : d.config c = config p := (haudit.config_eq c hc).trans (haudit.boundary_config c hc p hfp hp hbase)
  rw [hcfg] at hk ⊢
  obtain ⟨hrec, hsel⟩ := (hpub p (boundary_published haudit hc hfp hp)).1 k hk
  rw [haudit.boundary_tree c hc p hfp hp, haudit.filter_eq c hc]
  refine ⟨hrec, fun x hx hs hr => hsel x hx ?_ hr⟩
  rwa [← haudit.boundary_selection c hc p hfp hp hbase x hx]

/-- **The keyless boundary of the hook's audit is trusted** when published
    history was admitted. -/
theorem keyless_boundary_of_published {C A : Type} {keys : EpochKeys P} {σ₀ : Suite} {g : GitState}
    {parents : C → List C} {ups : List (PushUpdate C)} {tracking : List C} {tree : C → List Entry}
    {filter : C → List Nat → List Nat} {config : C → List Nat} {d : AuditedRange C A}
    (haudit : HookAudit parents ups tracking tree filter config d)
    (hpub : PublishedAdmitted keys σ₀ g parents ups tracking tree filter config) :
    KeylessBoundaryTrusted keys σ₀ g d := by
  intro c hc p hfp hp hbase hk
  have hcfg : d.config c = config p := (haudit.config_eq c hc).trans (haudit.boundary_config c hc p hfp hp hbase)
  rw [hcfg] at hk ⊢
  have hsel := (hpub p (boundary_published haudit hc hfp hp)).2 hk
  rw [haudit.boundary_tree c hc p hfp hp, haudit.filter_eq c hc]
  intro x hx hs hr
  exact hsel x hx (by rwa [← haudit.boundary_selection c hc p hfp hp hbase x hx]) hr

/-- **What a push admitted by the hook publishes.** Take the hook's audit
    of its range (`HookAudit`, A19, A20), accepted for every commit, keyed
    where this checkout has the configuration's key (each realizing its
    suite, A5) and keyless otherwise, along Git's first parents
    (`FirstParentEdges`, A11, A20); Git's push contract (`PushContract`,
    A30); and published history admitted (`PublishedAdmitted`, A13). Then
    every commit Git sends keeps the record invariant under its own
    configuration and attributes: with the key, every record and every
    selected path authenticate; without it, every selected path has the
    configuration's envelope. -/
theorem push_publishes_no_protected_plaintext {C A : Type} (aans : StagedEvidence A) (acache : AuditedEntries A)
    (keys : EpochKeys P) (hkeys : KeysRealize inst keys) (σ₀ : Suite) (g : GitState)
    {parents : C → List C} {ups : List (PushUpdate C)} {advertised tracking : List C} {sent : C → Prop}
    {tree : C → List Entry} {filter : C → List Nat → List Nat} {config : C → List Nat} (d : AuditedRange C A)
    (hcontract : PushContract parents ups advertised sent)
    (haudit : HookAudit parents ups tracking tree filter config d) (hedges : FirstParentEdges d)
    (hkeyed : ∀ c ∈ d.commits, ∀ k, keys (d.config c) = some k → KeyedAudit aans acache inst k.prims k.suite g (d.run c))
    (hkeyless : ∀ c ∈ d.commits, keys (d.config c) = none → KeylessAudit aans acache inst σ₀ g (d.run c))
    (hpub : PublishedAdmitted keys σ₀ g parents ups tracking tree filter config) :
    ∀ c, sent c → CommitKeyed keys g tree filter config c ∧ CommitEnveloped keys σ₀ g tree filter config c := by
  intro c hc
  rcases sent_audited_or_tracked (tracking := tracking) hcontract hc with hrange | htracked
  · have hcd : c ∈ d.commits := (haudit.commits_iff c).mpr hrange
    have hcfg := haudit.config_eq c hcd
    refine ⟨fun k hk => ?_, fun hk => ?_⟩
    · have h := keyed_dag_audit_authenticated aans acache keys hkeys g d hedges hkeyed
        (keyed_boundary_of_published haudit hpub) c hcd k (by rw [hcfg]; exact hk)
      unfold AuditedCommitAuthentic at h
      rw [hcfg, haudit.tree_eq c hcd, haudit.filter_eq c hcd] at h
      exact h
    · have h := keyless_dag_audit_enveloped (inst := inst) aans acache keys σ₀ g d hedges hkeyless
        (keyless_boundary_of_published haudit hpub) c hcd (by rw [hcfg]; exact hk)
      rw [hcfg, haudit.tree_eq c hcd, haudit.filter_eq c hcd] at h
      exact h
  · exact hpub c (Or.inr htracked)

/-- **No protected plaintext is sent.** Under the hypotheses of
    `push_publishes_no_protected_plaintext`, every path that a sent
    commit's own attributes select, unless it is metadata, is a regular
    file whose blob is a v3 record (has a record envelope): never
    plaintext. -/
theorem push_sends_no_protected_plaintext {C A : Type} (aans : StagedEvidence A) (acache : AuditedEntries A)
    (keys : EpochKeys P) (hkeys : KeysRealize inst keys) (σ₀ : Suite) (g : GitState)
    {parents : C → List C} {ups : List (PushUpdate C)} {advertised tracking : List C} {sent : C → Prop}
    {tree : C → List Entry} {filter : C → List Nat → List Nat} {config : C → List Nat} (d : AuditedRange C A)
    (hcontract : PushContract parents ups advertised sent)
    (haudit : HookAudit parents ups tracking tree filter config d) (hedges : FirstParentEdges d)
    (hkeyed : ∀ c ∈ d.commits, ∀ k, keys (d.config c) = some k → KeyedAudit aans acache inst k.prims k.suite g (d.run c))
    (hkeyless : ∀ c ∈ d.commits, keys (d.config c) = none → KeylessAudit aans acache inst σ₀ g (d.run c))
    (hpub : PublishedAdmitted keys σ₀ g parents ups tracking tree filter config) :
    ∀ c, sent c → ∀ x ∈ tree c, Selected (filter c x.path) → ¬ Reserved x.path →
      x.Regular ∧ ∃ content id, g.blob x.oid = some content ∧ EnvelopeOk content id := by
  intro c hc x hx hs hr
  obtain ⟨hk, hl⟩ := push_publishes_no_protected_plaintext aans acache keys hkeys σ₀ g d hcontract haudit hedges
    hkeyed hkeyless hpub c hc
  cases hkey : keys (config c) with
  | none =>
    obtain ⟨hreg, content, hblob, henv⟩ := hl hkey x hx hs hr
    exact ⟨hreg, content, _, hblob, henv⟩
  | some k =>
    obtain ⟨hreg, content, hblob, pt, hopen⟩ := (hk k hkey).2 x hx hs hr
    exact ⟨hreg, content, _, hblob, opensTo_envelopeOk _ hopen⟩

end Transcrypt.V3Verification

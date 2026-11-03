import V3Wire.Verification.ProductSecurity

/-!
# The keyed audit of one commit, and the start of a keyed history

`transcrypt-rs audit` (and the pre-push hook built on it) checks history the
pre-commit hook never saw: commits made with `--no-verify`, while locked, by
a rebase or by another party. `audit_commit` in `audit.rs` checks one commit
against its first parent. This file states what its acceptance guarantees,
as one transition with no traversal of the history: the extracted
`audit_check` chooses each examined entry's check, in the pre-commit hook's
vocabulary (`StagedCheck`), and the extracted `staged_verdict` decides it,
asking the adapter the same three questions (`StagedEvidence`).

* **The commit, as data.** `AuditedCommit`: the commit's tree, its first
  parent's tree (empty for a root commit), the blobs of the paths it
  deletes, and the `filter` value of each path under the commit's own
  attributes.
* **The adapter's contracts.** `AuditContracts`: the entries the audit
  examined and the facts it passed to `audit_check` are what Git reported
  (the diff contract: every other non-reserved entry of the tree is the
  parent's exactly, and only when the configuration is unchanged; A20, A19,
  A11, A21). `AuditAnswers`: the three answers mean what they say (A4, A21).
  `AuditSelectionAgrees`: the audit's selection of an entry it did not
  examine is the parent's (A19; the adapter examines the whole tree when an
  attribute file changes).
* **The run.** `auditPlan` only sequences `audit_check` and `staged_verdict`
  over the examined entries (`auditEntry`).

`keyed_audit_authenticates_commit`: a keyed audit that accepted a commit
makes its records authenticate (`RecordsAuthentic`, selection-independent)
given its parent's when it trusted the parent (`AuditBase.Parent`: the
configuration is unchanged), and with nothing for a root commit or a
configuration change (`AuditBase.Tree`); and every entry the commit's own
attributes select, unless it is repository metadata, is a regular file
whose record authenticates at its path (`SelectionAuthentic`), given the
parent's selection when the commit trusted it.
`keyless_audit_checks_envelopes`: without the key, every examined selected
entry is a regular file with this configuration's envelope that the parent
holds or that is no blob the commit deleted; no authenticity is claimed
(A14).
`audited_head_starts_keyed_history`: a keyed audit of the commit `HEAD`
names establishes the start condition of
`keyed_history_authenticated_by_guard`, and
`audited_head_keyed_history_authenticated` composes the two.
`keyed_audit_chain_authenticated`: a chain of keyed audits, each commit's
first parent the previous commit, keeps both invariants from a root commit
or a configuration change, or from a trusted first parent.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

variable {P : Type} {inst : V3Primitives P} {prims : P} {σ : Suite}

/-! ## The audit's check of each examined entry (model of `check_entries`) -/

/-- One entry the audit examined: the tree entry, the facts the adapter
    passed to `audit_check` and the path bytes, its blob when the check reads
    it (`reads_blob`: a selected entry's, read by its object id), and the
    adapter's answers about it (`StagedEvidence`). -/
structure AuditEntry (E : Type) where
  entry : Entry
  facts : AuditedEntry
  path : Slice U8
  record : Slice U8
  evidence : E

/-- One iteration of the loop in `check_entries`, as the verified core
    decides it: `audit_check` chooses the entry's check (or refuses a
    selected symlink) and `staged_verdict` whether it passes. The cache of
    passed records (`settled_by_cache`) is not modelled: an entry it settles
    passed the same check before. -/
def auditEntry {E : Type} (ans : StagedEvidence E) (id : Std.Array U8 16#usize) (keyed : Bool)
    (base : AuditBase) (e : AuditEntry E) : RustM Bool := do
  let c ← audit_check e.facts e.path keyed base
  match c with
  | none => ok false
  | some check => do
    let r ← staged_verdict ans e.evidence 0#usize check e.record id
    match r with
    | core.result.Result.Ok _ => ok true
    | core.result.Result.Err _ => ok false

/-- The audit checks every examined entry; one refusal refuses the commit. -/
def auditPlan {E : Type} (ans : StagedEvidence E) (id : Std.Array U8 16#usize) (keyed : Bool)
    (base : AuditBase) : List (AuditEntry E) → RustM Bool
  | [] => ok true
  | e :: es => do
    let b ← auditEntry ans id keyed base e
    if b then auditPlan ans id keyed base es else ok false

/-- An accepted plan accepted every entry. -/
theorem auditPlan_accepts {E : Type} {ans : StagedEvidence E} {id : Std.Array U8 16#usize} {keyed : Bool}
    {base : AuditBase} {es : List (AuditEntry E)} (h : auditPlan ans id keyed base es = ok true) :
    ∀ e ∈ es, auditEntry ans id keyed base e = ok true := by
  induction es with
  | nil => simp
  | cons e es ih =>
    unfold auditPlan at h
    cases he : auditEntry ans id keyed base e with
    | ok b =>
      rw [he] at h
      cases b
      · simp at h
      · simp only [bind_tc_ok, if_true] at h
        intro e' he'
        rcases List.mem_cons.1 he' with rfl | he'
        · exact he
        · exact ih h e' he'
    | fail _ => rw [he] at h; simp at h
    | div => rw [he] at h; simp at h

/-- An accepted entry: the verified check and verdict, both accepting. -/
theorem auditEntry_accepted {E : Type} {ans : StagedEvidence E} {id : Std.Array U8 16#usize} {keyed : Bool}
    {base : AuditBase} {e : AuditEntry E} (h : auditEntry ans id keyed base e = ok true) :
    ∃ check, audit_check e.facts e.path keyed base = ok (some check) ∧
      staged_verdict ans e.evidence 0#usize check e.record id = ok (core.result.Result.Ok ()) := by
  unfold auditEntry at h
  cases hc : audit_check e.facts e.path keyed base with
  | ok c =>
    rw [hc] at h
    simp only [bind_tc_ok] at h
    rcases c with _ | check
    · simp at h
    · refine ⟨check, rfl, ?_⟩
      dsimp only at h
      cases hv : staged_verdict ans e.evidence 0#usize check e.record id with
      | ok r =>
        rw [hv] at h
        rcases r with ⟨⟩ | x
        · rfl
        · simp at h
      | fail _ => rw [hv] at h; simp at h
      | div => rw [hv] at h; simp at h
  | fail _ => rw [hc] at h; simp at h
  | div => rw [hc] at h; simp at h

/-! ## The commit and the adapter's contracts -/

/-- One commit as the audit sees it: its tree (`ls-tree -r`), its first
    parent's tree (empty for a root commit), the blobs of the paths it
    deletes (`diff-tree` status `D`), and the effective `filter` value of
    each path under the commit's own attribute files (`check-attr --cached`
    against a temporary index holding exactly those files). -/
structure AuditedCommit where
  tree : List Entry
  parent : List Entry
  deleted : List (List Nat)
  filter : List Nat → List Nat

/-- **A20 (the diff contract), A19, A11, A21.** What the adapter's examined
    entries are, for one commit audited from `base`:

    * every non-reserved entry of the tree was examined, or the audit trusts
      the parent (`AuditBase.Parent`) and the parent holds exactly that entry
      (`diff-tree` lists every entry that differs from the parent's; the
      whole tree is examined for a root commit, a configuration change and
      an attribute change);
    * the facts passed to `audit_check` are about the examined entry: its
      path bytes; whether it is a regular file; whether the commit's
      attributes select it; whether the parent holds it exactly (not listed
      by `diff-tree`); whether its blob is that of a deleted path;
    * the blob read for a selected entry is the content of its object id. -/
structure AuditContracts {E : Type} (g : GitState) (c : AuditedCommit) (base : AuditBase)
    (es : List (AuditEntry E)) : Prop where
  covers : ∀ x ∈ c.tree, ¬ Reserved x.path → (∃ e ∈ es, e.entry = x) ∨ (base = .Parent ∧ x ∈ c.parent)
  path : ∀ e ∈ es, sliceBytes e.path = e.entry.path
  regular : ∀ e ∈ es, e.facts.regular = true ↔ e.entry.Regular
  selected : ∀ e ∈ es, e.facts.selected = true ↔ Selected (c.filter e.entry.path)
  held : ∀ e ∈ es, e.facts.held = true ↔ e.entry ∈ c.parent
  moved : ∀ e ∈ es, e.facts.moved = true ↔ e.entry.oid ∈ c.deleted
  objects : ∀ e ∈ es, e.facts.selected = true → GitObject g e.entry.oid e.record

/-- **A4, A21: the audit's answers** (`AuditEvidence` in `audit.rs`), each
    about the examined entry's own blob and path, under the configuration
    `config` with id `id`: `is_record` false means the blob has no envelope
    of this configuration (decided by `record_envelope_prefix_ok` from its
    size and first bytes); `opens` true means the verified `open_record`
    accepted the blob at the entry's path (`Key::open`); `elsewhere` is the
    fact `moved` the adapter passed. An answer the adapter could not find
    refuses the commit. -/
structure AuditAnswers {E : Type} (ans : StagedEvidence E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (g : GitState) (es : List (AuditEntry E)) :
    Prop where
  is_record : ∀ e ∈ es, ans.is_record e.evidence 0#usize ⦃ o => o = some false → ∃ content, g.blob e.entry.oid = some content ∧
      (maxRecord < content.length ∨ ∃ (size : Usize) (pre : Slice U8), size.val = content.length ∧
        sliceBytes pre = content.take Transcrypt.V3Wire.fileMinLen ∧
        record_envelope_prefix_ok size pre id = ok false) ⦄
  opens : ∀ e ∈ es, ans.opens e.evidence 0#usize ⦃ o => o = some true → ∃ (path record buf out : Slice U8),
      sliceBytes path = e.entry.path ∧ GitObject g e.entry.oid record ∧
      open_record pinst prims config path record buf = ok (core.result.Result.Ok (), out) ⦄
  elsewhere : ∀ e ∈ es, ans.elsewhere e.evidence 0#usize ⦃ o => o = some e.facts.moved ⦄

/-- **A19, for the audit.** The audit's selection of every non-reserved
    entry it did not examine is `pfilter`'s, the selection of the parent's
    audit. The adapter examines the whole tree when an attribute file
    changes, so an unexamined entry is in a commit whose attribute files
    are the parent's, evaluated against the same local attribute sources in
    one run. -/
def AuditSelectionAgrees {E : Type} (c : AuditedCommit) (es : List (AuditEntry E))
    (pfilter : List Nat → List Nat) : Prop :=
  ∀ x ∈ c.tree, ¬ Reserved x.path → (¬ ∃ e ∈ es, e.entry = x) → c.filter x.path = pfilter x.path

/-! ## What an audited commit is -/

/-- **The selection authenticates.** Every entry of `es` that `filter`
    selects, unless it is repository metadata (never encrypted), is a
    regular file whose blob authenticates at its path under `config`. -/
def SelectionAuthentic (σ : Suite) (config : List Nat) (g : GitState) (filter : List Nat → List Nat)
    (es : List Entry) : Prop :=
  ∀ x ∈ es, Selected (filter x.path) → ¬ Reserved x.path →
    x.Regular ∧ ∃ content, g.blob x.oid = some content ∧ AuthenticatedAt σ config x content

/-- **What the audit's check of one entry establishes.** For the examined
    entry `x`: if the commit's attributes select it and it is not metadata,
    it is a regular file whose blob, with the key, authenticates at its path
    and, without it, has this configuration's envelope and is held by the
    parent or is no blob the commit deleted; and with the key, if it is a
    regular, non-reserved file, its record authenticates where it has the
    envelope, or the audit trusted it from the parent, which holds it
    exactly. -/
structure AuditEntryChecked (σ : Suite) (config : List Nat) (keyed : Bool) (base : AuditBase) (g : GitState)
    (c : AuditedCommit) (x : Entry) : Prop where
  selected : Selected (c.filter x.path) → ¬ Reserved x.path → x.Regular ∧ ∃ content, g.blob x.oid = some content ∧
    (keyed = true → AuthenticatedAt σ config x content) ∧
    (keyed = false → EnvelopeOk content (σ.digest16 config) ∧ (x ∈ c.parent ∨ x.oid ∉ c.deleted))
  records : keyed = true → Selectable x → RecordAuthentic σ config g x ∨ (base = .Parent ∧ x ∈ c.parent)

/-- **One examined entry, end to end.** Under the audit's contracts, if the
    verified `audit_check` and `staged_verdict` accepted an examined entry,
    its tree entry is `AuditEntryChecked`. The primitives need to realize
    the suite only when the audit has the key. -/
theorem audit_entry_checked {E : Type} {ans : StagedEvidence E} {pinst : V3Primitives P} {prims : P}
    {config : Std.Array U8 55#usize} {id : Std.Array U8 16#usize} {g : GitState} {c : AuditedCommit}
    {base : AuditBase} {es : List (AuditEntry E)} {keyed : Bool}
    (hR : keyed = true → Realizes pinst prims σ) (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts g c base es) (hans : AuditAnswers ans pinst prims config id g es)
    {e : AuditEntry E} (he : e ∈ es) (hacc : auditEntry ans id keyed base e = ok true) :
    AuditEntryChecked σ (wireBytes config) keyed base g c e.entry := by
  obtain ⟨check, hc, hv⟩ := auditEntry_accepted hacc
  have hcheck := spec_result (audit_check_spec e.facts e.path keyed base) hc
  rw [hcon.path e he] at hcheck
  have hverdict := staged_verdict_ok ans e.evidence 0#usize check e.record id hv
  have hreg := hcon.regular e he
  have hsel := hcon.selected e he
  -- An accepted `opens` answer: the blob authenticates at the entry's path.
  have hopen : ans.opens e.evidence 0#usize = ok (some true) → keyed = true →
      ∃ content, g.blob e.entry.oid = some content ∧ AuthenticatedAt σ (wireBytes config) e.entry content := by
    intro ho hk
    obtain ⟨path, record, buf, out, hpath, hobj, hop⟩ := spec_result (hans.opens e he) ho rfl
    have hor := spec_result (open_record_spec (hR hk) config path record buf) hop
    rw [hpath] at hor
    exact ⟨_, hobj, _, hor⟩
  -- A record `is_record` denied has no envelope.
  have hnot : ans.is_record e.evidence 0#usize = ok (some false) → RecordAuthentic σ (wireBytes config) g e.entry := by
    intro hr
    obtain ⟨content, hc', hpre⟩ := spec_result (hans.is_record e he) hr rfl
    exact ⟨content, hc', fun henv => absurd (hid ▸ henv) (not_envelope_of_prefix hpre)⟩
  -- An unselected entry's selection part holds vacuously.
  have hunsel : e.facts.selected = false → Selected (c.filter e.entry.path) → False := fun hf hs => by
    rw [hsel.mpr hs] at hf; cases hf
  rcases check with _ | _ | _ | ec
  · -- Skip: metadata, or unprotected and not a record to check.
    simp only [AuditCheckOf] at hcheck
    refine ⟨fun hs hnr => ?_, fun hk ⟨hx, hnr⟩ => ?_⟩
    · rcases hcheck with hr | ⟨hf, -⟩
      · exact absurd hr hnr
      · exact (hunsel hf hs).elim
    · rcases hcheck with hr | ⟨-, hn | ⟨hh, hb⟩ | ⟨hkf, -⟩⟩
      · exact absurd hr hnr
      · rw [hreg.mpr hx] at hn; cases hn
      · exact Or.inr ⟨hb, (hcon.held e he).mp hh⟩
      · rw [hk] at hkf; cases hkf
  · -- NotRecord: without the key, unprotected, and no record of this configuration.
    obtain ⟨-, hf, -, -, hkf, -⟩ := hcheck
    exact ⟨fun hs _ => (hunsel hf hs).elim, fun hk => by rw [hk] at hkf; cases hkf⟩
  · -- AuthenticateIfRecord: with the key, unprotected, and a record of this configuration opens.
    obtain ⟨-, hf, -, -, hk⟩ := hcheck
    refine ⟨fun hs _ => (hunsel hf hs).elim, fun _ _ => Or.inl ?_⟩
    rcases hverdict with hr | ho
    · exact hnot hr
    · obtain ⟨content, hc', hat⟩ := hopen ho hk
      exact ⟨content, hc', fun _ => hat⟩
  · -- Protected: checked as `entry_check` decided, not incremental.
    obtain ⟨-, hst, hrt, hauth, henvc⟩ := hcheck
    have hx : e.entry.Regular := hreg.mp hrt
    have hb : g.blob e.entry.oid = some (sliceBytes e.record) := hcon.objects e he hst
    rcases ec with _ | _ | _
    · -- Authenticate: with the key, and the blob opens.
      have hk : keyed = true := (hauth.mp rfl).1
      obtain ⟨content, hc', hat⟩ := hopen hverdict hk
      refine ⟨fun _ _ => ⟨hx, content, hc', fun _ => hat, fun hkf => ?_⟩,
        fun _ _ => Or.inl ⟨content, hc', fun _ => hat⟩⟩
      rw [hk] at hkf; cases hkf
    · -- Envelope: without the key, held by the parent.
      obtain ⟨hnk, hh⟩ := henvc.mp rfl
      have hkf : keyed = false := by
        cases hkey : keyed
        · rfl
        · exact absurd ⟨hkey, fun h => by simp at h⟩ hnk
      have henv : EnvelopeOk (sliceBytes e.record) (σ.digest16 (wireBytes config)) := hid ▸ hverdict
      refine ⟨fun _ _ => ⟨hx, _, hb, fun hk => ?_, fun _ => ⟨henv, Or.inl ((hcon.held e he).mp hh)⟩⟩,
        fun hk => ?_⟩
      · rw [hk] at hkf; cases hkf
      · rw [hk] at hkf; cases hkf
    · -- EnvelopeNotMoved: without the key, the envelope, and no deleted path's blob.
      have hnk : ¬ (keyed = true ∧ ¬ (false = true ∧ e.facts.held = true)) := fun h => by
        simpa using hauth.mpr h
      have hkf : keyed = false := by
        cases hkey : keyed
        · rfl
        · exact absurd ⟨hkey, fun h => by simp at h⟩ hnk
      obtain ⟨henv, hel⟩ := hverdict
      have hmv : e.facts.moved = false := by
        have := spec_result (hans.elsewhere e he) hel
        simp only [Option.some.injEq] at this
        exact this.symm
      have hnd : e.entry.oid ∉ c.deleted := fun hd => by
        rw [(hcon.moved e he).mpr hd] at hmv; cases hmv
      refine ⟨fun _ _ => ⟨hx, _, hb, fun hk => ?_, fun _ => ⟨hid ▸ henv, Or.inr hnd⟩⟩, fun hk => ?_⟩
      · rw [hk] at hkf; cases hkf
      · rw [hk] at hkf; cases hkf

/-! ## One commit -/

/-- **The records of a keyed-audited commit authenticate.** If the keyed
    audit accepted the commit, its records authenticate (`RecordsAuthentic`),
    given its parent's when the audit trusted the parent. -/
theorem keyed_audit_records_authentic {E : Type} (g : GitState) (c : AuditedCommit) (base : AuditBase)
    (es : List (AuditEntry E)) (ans : StagedEvidence E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hR : Realizes pinst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts g c base es)
    (hans : AuditAnswers ans pinst prims config id g es)
    (hplan : auditPlan ans id true base es = ok true)
    (hparent : base = .Parent → RecordsAuthentic σ (wireBytes config) g c.parent) :
    RecordsAuthentic σ (wireBytes config) g c.tree := by
  intro y hy hsel
  rcases hcon.covers y hy hsel.2 with ⟨e, he, rfl⟩ | ⟨hb, hyp⟩
  · rcases (audit_entry_checked (fun _ => hR) hid hcon hans he (auditPlan_accepts hplan e he)).records rfl hsel with
      h | ⟨hb, hyp⟩
    · exact h
    · exact hparent hb _ hyp hsel
  · exact hparent hb y hyp hsel

/-- **The selection of a keyed-audited commit authenticates.** If the keyed
    audit accepted the commit, every entry its attributes select, unless it
    is metadata, is a regular file whose record authenticates at its path
    (`SelectionAuthentic`), given, when the audit trusted the parent, that
    the parent's selection `pfilter` authenticates and agrees on the entries
    the audit did not examine (`AuditSelectionAgrees`). -/
theorem keyed_audit_selection_authentic {E : Type} (g : GitState) (c : AuditedCommit) (base : AuditBase)
    (es : List (AuditEntry E)) (ans : StagedEvidence E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hR : Realizes pinst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts g c base es)
    (hans : AuditAnswers ans pinst prims config id g es)
    (hplan : auditPlan ans id true base es = ok true)
    (pfilter : List Nat → List Nat)
    (hpsel : base = .Parent → SelectionAuthentic σ (wireBytes config) g pfilter c.parent)
    (hagree : AuditSelectionAgrees c es pfilter) :
    SelectionAuthentic σ (wireBytes config) g c.filter c.tree := by
  intro x hx hs hnr
  by_cases hex : ∃ e ∈ es, e.entry = x
  · obtain ⟨e, he, rfl⟩ := hex
    obtain ⟨hreg, content, hc', hk, -⟩ :=
      (audit_entry_checked (fun _ => hR) hid hcon hans he (auditPlan_accepts hplan e he)).selected hs hnr
    exact ⟨hreg, content, hc', hk rfl⟩
  · rcases hcon.covers x hx hnr with hex' | ⟨hb, hxp⟩
    · exact absurd hex' hex
    · exact hpsel hb x hxp (hagree x hx hnr hex ▸ hs) hnr

/-- **The keyed audit of one commit.** Assume the audit's contracts
    (`AuditContracts`: the diff contract A20, Git's selection A19, object
    reads A11/A21), its answers (`AuditAnswers`, A4), primitives that realize
    the suite (`Realizes`, A5) and the configuration's id (A5). If the keyed
    audit of the commit accepted (`auditPlan` of the verified `audit_check`
    and `staged_verdict` returned `true`), then

    * **its records authenticate** (`RecordsAuthentic`: every regular,
      non-reserved entry of its tree whose blob has this configuration's
      envelope authenticates at its own path, whatever selects it), given
      the parent's records when the audit trusted the parent
      (`AuditBase.Parent`); a root commit or a configuration change
      (`AuditBase.Tree`) needs nothing;
    * **its selection authenticates** (`SelectionAuthentic`: every entry
      the commit's attributes select, unless it is metadata, is a regular
      file whose record authenticates at its path), given, when the audit
      trusted the parent, the parent's selection `pfilter` authenticated and
      agreeing on the entries the audit did not examine
      (`AuditSelectionAgrees`, A19). -/
theorem keyed_audit_authenticates_commit {E : Type} (g : GitState) (c : AuditedCommit) (base : AuditBase)
    (es : List (AuditEntry E)) (ans : StagedEvidence E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hR : Realizes pinst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts g c base es)
    (hans : AuditAnswers ans pinst prims config id g es)
    (hplan : auditPlan ans id true base es = ok true)
    (hparent : base = .Parent → RecordsAuthentic σ (wireBytes config) g c.parent)
    (pfilter : List Nat → List Nat)
    (hpsel : base = .Parent → SelectionAuthentic σ (wireBytes config) g pfilter c.parent)
    (hagree : AuditSelectionAgrees c es pfilter) :
    RecordsAuthentic σ (wireBytes config) g c.tree ∧ SelectionAuthentic σ (wireBytes config) g c.filter c.tree :=
  ⟨keyed_audit_records_authentic g c base es ans pinst prims config id hR hid hcon hans hplan hparent,
    keyed_audit_selection_authentic g c base es ans pinst prims config id hR hid hcon hans hplan pfilter hpsel hagree⟩

/-- **The keyless audit of one commit.** Under the same contracts (the
    primitives are never used), if the audit without the key accepted, every
    examined entry that the commit's attributes select, unless it is
    metadata, is a regular file with this configuration's envelope that the
    parent holds exactly or that is no blob of a path the commit deleted (no
    record moved without re-encryption). Nothing is claimed about
    authenticity: a forged envelope passes (A14). -/
theorem keyless_audit_checks_envelopes {E : Type} (g : GitState) (c : AuditedCommit) (base : AuditBase)
    (es : List (AuditEntry E)) (ans : StagedEvidence E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts g c base es)
    (hans : AuditAnswers ans pinst prims config id g es)
    (hplan : auditPlan ans id false base es = ok true) :
    ∀ e ∈ es, Selected (c.filter e.entry.path) → ¬ Reserved e.entry.path →
      e.entry.Regular ∧ ∃ content, g.blob e.entry.oid = some content ∧
        EnvelopeOk content (σ.digest16 (wireBytes config)) ∧ (e.entry ∈ c.parent ∨ e.entry.oid ∉ c.deleted) := by
  intro e he hs hnr
  obtain ⟨hreg, content, hc', -, hkl⟩ :=
    (audit_entry_checked (σ := σ) (fun h => by cases h) hid hcon hans he (auditPlan_accepts hplan e he)).selected hs hnr
  exact ⟨hreg, content, hc', hkl rfl⟩

/-! ## The start of a keyed history -/

/-- The commit's tree commits `config` as the regular file
    `.transcrypt/config`. -/
def CommitConfig (g : GitState) (tree : List Entry) (config : List Nat) : Prop :=
  ∃ c ∈ tree, c.path = ascii ".transcrypt/config" ∧ c.Regular ∧ g.blob c.oid = some config

/-- **A true guard commits `HEAD`'s configuration.** If the hook's verified
    `policy_unchanged` returned `true`, the configuration the index commits
    is the one `HEAD` commits: the index and `HEAD` have the same entry at
    `.transcrypt/config` (`hook_policy_guard`), the only one at that path
    in the sorted `HEAD`. -/
theorem config_of_guard_head {E : Type} {g : GitState} {run : HookEvidence g E} {config config' : List Nat}
    (hgit : HookContracts g run) (hguard : run.samePolicy = true)
    (hhead : CommitConfig g g.head config) (hcfg : ConfigCommitted g config') :
    config' = config := by
  have hpe : policyEntries g.index = policyEntries g.head := (hook_policy_guard hgit hguard).1
  obtain ⟨c', hc'm, hc'p, -, hc'b⟩ := hcfg
  obtain ⟨c, hcm, hcp, -, hcb⟩ := hhead
  have hc' : c' ∈ policyEntries g.head := hpe ▸ mem_policyEntries.mpr ⟨hc'm, Or.inr hc'p⟩
  have heq := (hook_snapshots_sorted hgit).2.1.eq_of_path (mem_policyEntries.mp hc').1 hcm (hc'p.trans hcp.symm)
  subst heq
  rw [hcb, Option.some.injEq] at hc'b
  exact hc'b.symm

/-- **An audited `HEAD` starts a keyed history.** Let a keyed audit have
    accepted a commit (`keyed_audit_authenticates_commit`, its parent's
    records given when it trusted the parent) under the configuration that
    commit commits (`CommitConfig`). If that commit is the `HEAD` of a later
    hook run (Git lists the same tree, A20, and objects keep their content,
    A11), then the start condition of `keyed_history_authenticated_by_guard`
    holds for that run: when its guard returned `true`, `HEAD`'s records
    authenticate under the configuration it commits. -/
theorem audited_head_starts_keyed_history {E A : Type} (g : GitState) (c : AuditedCommit) (base : AuditBase)
    (es : List (AuditEntry A)) (aans : StagedEvidence A)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hR : Realizes inst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts g c base es)
    (hans : AuditAnswers aans inst prims config id g es)
    (hplan : auditPlan aans id true base es = ok true)
    (hparent : base = .Parent → RecordsAuthentic σ (wireBytes config) g c.parent)
    (hconfig : CommitConfig g c.tree (wireBytes config))
    (k : CheckedCommit E) (hgit : HookContracts k.g k.run) (hcfg : ConfigCommitted k.g k.config)
    (hhead : k.g.head = c.tree)
    (hobjects : ∀ oid content, g.blob oid = some content → k.g.blob oid = some content) :
    k.run.samePolicy = true → RecordsAuthentic σ k.config k.g k.g.head := by
  intro hguard
  have hrec := keyed_audit_records_authentic g c base es aans inst prims config id hR hid hcon hans hplan hparent
  obtain ⟨y, hy, hyp, hyr, hyb⟩ := hconfig
  have hcfgeq : k.config = wireBytes config :=
    config_of_guard_head hgit hguard ⟨y, hhead ▸ hy, hyp, hyr, hobjects _ _ hyb⟩ hcfg
  intro x hx hsel
  rw [hhead] at hx
  obtain ⟨content, hc, hra⟩ := hrec x hx hsel
  rw [hcfgeq]
  exact ⟨content, hobjects _ _ hc, hra⟩

/-- **An audited `HEAD` followed by keyed commits stays authenticated.**
    Take commits `h 0, …, h n` as in `keyed_history_authenticated_by_guard`
    (each accepted by a keyed check, each made from the index checked before
    it), and let the commit `h 0`'s `HEAD` names have been accepted by the
    keyed audit, under the configuration it commits, with the same key
    (`audited_head_starts_keyed_history`). Then every commit's records and
    selected paths authenticate: no further assumption about the start of
    the history remains, only the audit's own (its parent's records, when
    it trusted the parent). -/
theorem audited_head_keyed_history_authenticated {E A : Type} (ans : StagedEvidence E) (hR : Realizes inst prims σ)
    (h : Nat → CheckedCommit E) (n : Nat)
    (hcommits : ∀ i ≤ n, KeyedCommit ans inst prims σ (h i))
    (hsteps : ∀ i < n, GuardedHistoryStep (h i) (h (i + 1)))
    (g : GitState) (c : AuditedCommit) (base : AuditBase) (es : List (AuditEntry A)) (aans : StagedEvidence A)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts g c base es)
    (hans : AuditAnswers aans inst prims config id g es)
    (hplan : auditPlan aans id true base es = ok true)
    (hparent : base = .Parent → RecordsAuthentic σ (wireBytes config) g c.parent)
    (hconfig : CommitConfig g c.tree (wireBytes config))
    (hhead : (h 0).g.head = c.tree)
    (hobjects : ∀ oid content, g.blob oid = some content → (h 0).g.blob oid = some content) :
    ∀ i ≤ n, RecordsAuthentic σ (h i).config (h i).g (h i).g.index ∧ AuthenticatedIndex σ (h i).config (h i).g := by
  have h0 := hcommits 0 (Nat.zero_le n)
  exact keyed_history_authenticated_by_guard ans hR h n hcommits hsteps (fun hg _ =>
    audited_head_starts_keyed_history g c base es aans config id hR hid hcon hans hplan hparent hconfig (h 0)
      h0.contracts h0.config hhead hobjects hg)

/-! ## A chain of audited commits -/

/-- One commit's audit in a run: the commit, its base, the entries it
    examined, and its configuration and id. -/
structure AuditRun (A : Type) where
  commit : AuditedCommit
  base : AuditBase
  entries : List (AuditEntry A)
  config : Std.Array U8 55#usize
  id : Std.Array U8 16#usize

/-- The commit's keyed audit accepted, with its contracts and answers. -/
structure KeyedAudit {A : Type} (ans : StagedEvidence A) (pinst : V3Primitives P) (prims : P) (σ : Suite)
    (g : GitState) (r : AuditRun A) : Prop where
  id : wireBytes r.id = σ.digest16 (wireBytes r.config)
  contracts : AuditContracts g r.commit r.base r.entries
  answers : AuditAnswers ans pinst prims r.config r.id g r.entries
  accepted : auditPlan ans r.id true r.base r.entries = ok true

/-- `r'` audits a child of `r`'s commit: its first parent is `r`'s commit;
    when it trusts the parent, its configuration is `r`'s (the adapter
    trusts the parent only when `diff-tree` does not list the config, A20,
    A11); and its selection of an entry it did not examine is `r`'s
    (`AuditSelectionAgrees`, A19). -/
structure AuditStep {A : Type} (r r' : AuditRun A) : Prop where
  parent : r'.commit.parent = r.commit.tree
  config : r'.base = .Parent → r'.config = r.config
  selection : AuditSelectionAgrees r'.commit r'.entries r.commit.filter

/-- **A chain of keyed audits.** Take audits `a 0, …, a n` in one object
    store, each a keyed audit that accepted (`KeyedAudit`, under one key),
    each commit's first parent the previous commit (`AuditStep`), and the
    first one starting from a root commit or a configuration change
    (`AuditBase.Tree`), or from a first parent outside the chain whose
    records and selection (under the first commit's attributes)
    authenticate. Then every commit's records and selection authenticate. -/
theorem keyed_audit_chain_authenticated {A : Type} (ans : StagedEvidence A) (hR : Realizes inst prims σ)
    (g : GitState) (a : Nat → AuditRun A) (n : Nat)
    (haudits : ∀ i ≤ n, KeyedAudit ans inst prims σ g (a i))
    (hsteps : ∀ i < n, AuditStep (a i) (a (i + 1)))
    (hstart : (a 0).base = .Parent → RecordsAuthentic σ (wireBytes (a 0).config) g (a 0).commit.parent ∧
      SelectionAuthentic σ (wireBytes (a 0).config) g (a 0).commit.filter (a 0).commit.parent) :
    ∀ i ≤ n, RecordsAuthentic σ (wireBytes (a i).config) g (a i).commit.tree ∧
      SelectionAuthentic σ (wireBytes (a i).config) g (a i).commit.filter (a i).commit.tree := by
  intro i hi
  induction i with
  | zero =>
    have ha := haudits 0 hi
    exact keyed_audit_authenticates_commit g _ _ _ ans inst prims _ _ hR ha.id ha.contracts ha.answers ha.accepted
      (fun hb => (hstart hb).1) (a 0).commit.filter (fun hb => (hstart hb).2) (fun _ _ _ _ => rfl)
  | succ k ih =>
    have hk := ih (by omega)
    have hs := hsteps k (by omega)
    have ha := haudits (k + 1) hi
    exact keyed_audit_authenticates_commit g _ _ _ ans inst prims _ _ hR ha.id ha.contracts ha.answers ha.accepted
      (fun hb => by rw [hs.parent, hs.config hb]; exact hk.1) (a k).commit.filter
      (fun hb => by rw [hs.parent, hs.config hb]; exact hk.2) hs.selection

end Transcrypt.V3Verification

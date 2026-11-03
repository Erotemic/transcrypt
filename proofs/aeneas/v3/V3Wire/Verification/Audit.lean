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
  examined and the facts it passed for them are what Git reported (the
  diff contract: every other non-reserved entry of the tree is the parent's
  exactly, and only when the configuration is unchanged; A20, A19).
  `AuditAnswers`: the blobs read, the paths, the three answers and the
  run's cache of checked records mean what they say (A4, A11, A21).
  `AuditSelectionAgrees`: the audit's selection of an entry it did not
  examine is the parent's (A19; the adapter examines the whole tree when an
  attribute file changes).
* **The run.** One call of the extracted `commit_verdict` (`AuditAccepted`),
  whose loop is proved to check every examined position in order
  (`commit_verdict_accepts`): `audit_check`, then, unless an earlier pass of
  the same record settles the check (`settled_by_cache`), `read_verdict`
  (`staged_verdict` on the blob read for that position).

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

/-! ## The audit's check of one commit (`audit_commit`) -/

/-- One commit's audit run as the adapter makes it: the entries it examined
    (tree entries, in order), the facts it passed for each to the verified
    `commit_verdict` (position by position), and its evidence in the state
    it passes to the call (`CommitEvidence` in `audit.rs`). -/
structure AuditedRun (E : Type) where
  entries : List Entry
  facts : Slice AuditedEntry
  start : E
  facts_len : facts.length = entries.length

/-- **The audit's check of the commit accepted.** The verified
    `commit_verdict`, called once with the run's facts, whether the audit
    has the key, the base and the configuration's id, returned `Ok` (A4:
    the adapter refuses the commit otherwise). -/
def AuditAccepted {E : Type} (ans : StagedEvidence E) (cache : AuditedEntries E) (id : Std.Array U8 16#usize)
    (keyed : Bool) (base : AuditBase) (run : AuditedRun E) : Prop :=
  ∃ s, commit_verdict ans cache run.start run.facts keyed base id = ok (core.result.Result.Ok (), s)

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

/-- **A20 (the diff contract), A19.** What the adapter's examined entries
    are, for one commit audited from `base`:

    * every non-reserved entry of the tree was examined, or the audit trusts
      the parent (`AuditBase.Parent`) and the parent holds exactly that entry
      (`diff-tree` lists every entry that differs from the parent's; the
      whole tree is examined for a root commit, a configuration change and
      an attribute change);
    * the facts passed at each position are about the entry examined there:
      whether it is a regular file; whether the commit's attributes select
      it; whether the parent holds it exactly (not listed by `diff-tree`);
      whether its blob is that of a deleted path. -/
structure AuditContracts {E : Type} (c : AuditedCommit) (base : AuditBase) (run : AuditedRun E) : Prop where
  covers : ∀ x ∈ c.tree, ¬ Reserved x.path → x ∈ run.entries ∨ (base = .Parent ∧ x ∈ c.parent)
  regular : ∀ (k : Nat) x a, run.entries[k]? = some x → run.facts.val[k]? = some a → (a.regular = true ↔ x.Regular)
  selected : ∀ (k : Nat) x a, run.entries[k]? = some x → run.facts.val[k]? = some a →
    (a.selected = true ↔ Selected (c.filter x.path))
  held : ∀ (k : Nat) x a, run.entries[k]? = some x → run.facts.val[k]? = some a → (a.held = true ↔ x ∈ c.parent)
  moved : ∀ (k : Nat) x a, run.entries[k]? = some x → run.facts.val[k]? = some a →
    (a.moved = true ↔ x.oid ∈ c.deleted)

/-- **A4, A11, A21: the audit's evidence, in the states `good` describes**
    (`CommitEvidence` in `audit.rs`). `good` holds of the start state and
    every `read` and `passed` keeps it; in such a state, about examined
    position `k`, whose entry is `x`, under the configuration `config` with
    id `id`, in an audit with the key or not (`keyed`):

    * `path` gives `x`'s path bytes;
    * `read` true: the blob `blob` then returns is the content of `x`'s
      object id (A11, A21);
    * `is_record` `some false`: the blob has no envelope of this
      configuration (decided by `record_envelope_prefix_ok` from its size and
      first bytes); `opens` `some true`: the verified `open_record` accepted
      the blob at `x`'s path (`Key::open`); `elsewhere` `some b`: `b` is the
      fact `moved` passed at `k`;
    * `checked` true (the run's cache of checked records): the blob, read
      by its object id, has this configuration's envelope and, with the key,
      the verified `open_record` accepted it at `x`'s path. The adapter
      records an entry only when the verified `commit_verdict` calls
      `passed` (after a selected entry's verdict accepted it), for its blob,
      configuration and path, and a configuration's key is fixed for the
      run (reviewed).

    An answer the adapter could not find is `none`, which the verified
    verdict refuses. -/
structure AuditAnswersIn {E : Type} (ans : StagedEvidence E) (cache : AuditedEntries E) (pinst : V3Primitives P)
    (prims : P) (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (keyed : Bool) (g : GitState)
    (run : AuditedRun E) (good : E → Prop) : Prop where
  start : good run.start
  read_good : ∀ s k b s', good s → ans.read s k = ok (b, s') → good s'
  passed_good : ∀ s k s', good s → cache.passed s k = ok s' → good s'
  path : ∀ s (k : Usize) x p, good s → run.entries[k.val]? = some x → cache.path s k = ok p → sliceBytes p = x.path
  read : ∀ s (k : Usize) s' x record, good s → run.entries[k.val]? = some x → ans.read s k = ok (true, s') →
    ans.blob s' = ok record → GitObject g x.oid record
  is_record : ∀ s (k : Usize) x, good s → run.entries[k.val]? = some x →
    ans.is_record s k ⦃ o => o = some false → ∃ content, g.blob x.oid = some content ∧
      (maxRecord < content.length ∨ ∃ (size : Usize) (pre : Slice U8), size.val = content.length ∧
        sliceBytes pre = content.take Transcrypt.V3Wire.fileMinLen ∧
        record_envelope_prefix_ok size pre id = ok false) ⦄
  opens : ∀ s (k : Usize) x, good s → run.entries[k.val]? = some x →
    ans.opens s k ⦃ o => o = some true → ∃ (path record buf out : Slice U8),
      sliceBytes path = x.path ∧ GitObject g x.oid record ∧
      open_record pinst prims config path record buf = ok (core.result.Result.Ok (), out) ⦄
  elsewhere : ∀ s (k : Usize) a, good s → run.facts.val[k.val]? = some a →
    ans.elsewhere s k ⦃ o => ∀ b, o = some b → b = a.moved ⦄
  checked : ∀ s (k : Usize) x, good s → run.entries[k.val]? = some x → cache.checked s k = ok true →
    ∃ record, GitObject g x.oid record ∧ EnvelopeOk (sliceBytes record) (wireBytes id) ∧
      (keyed = true → ∃ (path buf out : Slice U8), sliceBytes path = x.path ∧
        open_record pinst prims config path record buf = ok (core.result.Result.Ok (), out))

/-- **A4, A11, A21: the audit's answers mean what they say**
    (`AuditAnswersIn`) in the evidence states of the run. -/
def AuditAnswers {E : Type} (ans : StagedEvidence E) (cache : AuditedEntries E) (pinst : V3Primitives P)
    (prims : P) (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (keyed : Bool) (g : GitState)
    (run : AuditedRun E) : Prop :=
  ∃ good, AuditAnswersIn ans cache pinst prims config id keyed g run good

/-- **A19, for the audit.** The audit's selection of every non-reserved
    entry it did not examine is `pfilter`'s, the selection of the parent's
    audit. The adapter examines the whole tree when an attribute file
    changes, so an unexamined entry is in a commit whose attribute files
    are the parent's, evaluated against the same local attribute sources in
    one run. -/
def AuditSelectionAgrees {E : Type} (c : AuditedCommit) (run : AuditedRun E)
    (pfilter : List Nat → List Nat) : Prop :=
  ∀ x ∈ c.tree, ¬ Reserved x.path → x ∉ run.entries → c.filter x.path = pfilter x.path

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
    verified `commit_verdict` accepted examined position `k`
    (`CommitPositionAccepted`: its `audit_check`, then either an earlier
    pass of the same record or its `staged_verdict`), the entry examined
    there is `AuditEntryChecked`. The primitives need to realize the suite
    only when the audit has the key. -/
theorem audit_entry_checked {E : Type} {ans : StagedEvidence E} {cache : AuditedEntries E}
    {pinst : V3Primitives P} {prims : P}
    {config : Std.Array U8 55#usize} {id : Std.Array U8 16#usize} {g : GitState} {c : AuditedCommit}
    {base : AuditBase} {run : AuditedRun E} {keyed : Bool} {good : E → Prop}
    (hR : keyed = true → Realizes pinst prims σ) (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts c base run) (hans : AuditAnswersIn ans cache pinst prims config id keyed g run good)
    {k : Usize} {x : Entry} (hx : run.entries[k.val]? = some x)
    (hacc : CommitPositionAccepted ans cache good run.facts keyed base id k) :
    AuditEntryChecked σ (wireBytes config) keyed base g c x := by
  obtain ⟨s, path, a, check, hs, hp, ha, hc, hpass⟩ := hacc
  have hcheck := spec_result (audit_check_spec a path keyed base) hc
  rw [hans.path s k x path hs hx hp] at hcheck
  have hreg := hcon.regular k.val x a hx ha
  have hsel := hcon.selected k.val x a hx ha
  -- An opened blob authenticates at the entry's path.
  have hopened : ∀ (path' record buf out : Slice U8), keyed = true → sliceBytes path' = x.path →
      GitObject g x.oid record → open_record pinst prims config path' record buf = ok (core.result.Result.Ok (), out) →
      ∃ content, g.blob x.oid = some content ∧ AuthenticatedAt σ (wireBytes config) x content := by
    intro path' record buf out hk hpath hobj hop
    have hor := spec_result (open_record_spec (hR hk) config path' record buf) hop
    rw [hpath] at hor
    exact ⟨_, hobj, _, hor⟩
  -- An unselected entry's selection part holds vacuously.
  have hunsel : a.selected = false → Selected (c.filter x.path) → False := fun hf hs' => by
    rw [hsel.mpr hs'] at hf; cases hf
  rcases hpass with ⟨hsc, hch⟩ | ⟨t, hrv⟩
  · -- Settled by an earlier pass: a selected entry's `Authenticate` or `Envelope`.
    obtain ⟨record, hobj, henv, hkop⟩ := hans.checked s k x hs hx hch
    have hcases := (spec_result (settled_by_cache_spec check) hsc).mp rfl
    have henv' : EnvelopeOk (sliceBytes record) (σ.digest16 (wireBytes config)) := hid ▸ henv
    rcases hcases with rfl | rfl
    · obtain ⟨-, hst, hrt, hauth, -⟩ := hcheck
      have hk : keyed = true := (hauth.mp rfl).1
      have hxr : x.Regular := hreg.mp hrt
      obtain ⟨path', buf, out, hpath, hop⟩ := hkop hk
      obtain ⟨content, hc', hat⟩ := hopened path' record buf out hk hpath hobj hop
      refine ⟨fun _ _ => ⟨hxr, content, hc', fun _ => hat, fun hkf => ?_⟩,
        fun _ _ => Or.inl ⟨content, hc', fun _ => hat⟩⟩
      rw [hk] at hkf; cases hkf
    · obtain ⟨-, hst, hrt, hauth, henvc⟩ := hcheck
      have hxr : x.Regular := hreg.mp hrt
      obtain ⟨hnk, hh⟩ := henvc.mp rfl
      have hkf : keyed = false := by
        cases hkey : keyed
        · rfl
        · exact absurd ⟨hkey, fun h => by simp at h⟩ hnk
      refine ⟨fun _ _ => ⟨hxr, _, hobj, fun hk => ?_, fun _ => ⟨henv', Or.inl ((hcon.held k.val x a hx ha).mp hh)⟩⟩,
        fun hk => ?_⟩
      · rw [hk] at hkf; cases hkf
      · rw [hk] at hkf; cases hkf
  · -- Checked now: the blob read for it and the verdict.
    obtain ⟨-, hacc'⟩ := read_verdict_ok good hans.read_good hs hrv
    obtain ⟨hrd, record, hb, hv⟩ := hacc' rfl
    obtain ⟨ht, -⟩ := read_verdict_ok good hans.read_good hs hrv
    have hverdict := staged_verdict_ok ans t k check record id hv
    -- An accepted `opens` answer: the blob authenticates at the entry's path.
    have hopen : ans.opens t k = ok (some true) → keyed = true →
        ∃ content, g.blob x.oid = some content ∧ AuthenticatedAt σ (wireBytes config) x content := by
      intro ho hk
      obtain ⟨path', record', buf, out, hpath, hobj, hop⟩ := spec_result (hans.opens t k x ht hx) ho rfl
      exact hopened path' record' buf out hk hpath hobj hop
    -- A record `is_record` denied has no envelope.
    have hnot : ans.is_record t k = ok (some false) → RecordAuthentic σ (wireBytes config) g x := by
      intro hr
      obtain ⟨content, hc', hpre⟩ := spec_result (hans.is_record t k x ht hx) hr rfl
      exact ⟨content, hc', fun henv => absurd (hid ▸ henv) (not_envelope_of_prefix hpre)⟩
    rcases check with _ | _ | _ | ec
    · -- Skip: metadata, or unprotected and not a record to check.
      simp only [AuditCheckOf] at hcheck
      refine ⟨fun hs' hnr => ?_, fun hk ⟨hxr, hnr⟩ => ?_⟩
      · rcases hcheck with hr | ⟨hf, -⟩
        · exact absurd hr hnr
        · exact (hunsel hf hs').elim
      · rcases hcheck with hr | ⟨-, hn | ⟨hh, hb'⟩ | ⟨hkf, -⟩⟩
        · exact absurd hr hnr
        · rw [hreg.mpr hxr] at hn; cases hn
        · exact Or.inr ⟨hb', (hcon.held k.val x a hx ha).mp hh⟩
        · rw [hk] at hkf; cases hkf
    · -- NotRecord: without the key, unprotected, and no record of this configuration.
      obtain ⟨-, hf, -, -, hkf, -⟩ := hcheck
      exact ⟨fun hs' _ => (hunsel hf hs').elim, fun hk => by rw [hk] at hkf; cases hkf⟩
    · -- AuthenticateIfRecord: with the key, unprotected, and a record of this configuration opens.
      obtain ⟨-, hf, -, -, hk⟩ := hcheck
      refine ⟨fun hs' _ => (hunsel hf hs').elim, fun _ _ => Or.inl ?_⟩
      rcases hverdict with hr | ho
      · exact hnot hr
      · obtain ⟨content, hc', hat⟩ := hopen ho hk
        exact ⟨content, hc', fun _ => hat⟩
    · -- Protected: checked as `entry_check` decided, not incremental; its blob was read for it.
      obtain ⟨-, hst, hrt, hauth, henvc⟩ := hcheck
      have hxr : x.Regular := hreg.mp hrt
      have hblob : g.blob x.oid = some (sliceBytes record) := hans.read s k t x record hs hx (hrd rfl) hb
      rcases ec with _ | _ | _
      · -- Authenticate: with the key, and the blob opens.
        have hk : keyed = true := (hauth.mp rfl).1
        obtain ⟨content, hc', hat⟩ := hopen hverdict hk
        refine ⟨fun _ _ => ⟨hxr, content, hc', fun _ => hat, fun hkf => ?_⟩,
          fun _ _ => Or.inl ⟨content, hc', fun _ => hat⟩⟩
        rw [hk] at hkf; cases hkf
      · -- Envelope: without the key, held by the parent.
        obtain ⟨hnk, hh⟩ := henvc.mp rfl
        have hkf : keyed = false := by
          cases hkey : keyed
          · rfl
          · exact absurd ⟨hkey, fun h => by simp at h⟩ hnk
        have henv : EnvelopeOk (sliceBytes record) (σ.digest16 (wireBytes config)) := hid ▸ hverdict
        refine ⟨fun _ _ => ⟨hxr, _, hblob, fun hk => ?_, fun _ => ⟨henv, Or.inl ((hcon.held k.val x a hx ha).mp hh)⟩⟩,
          fun hk => ?_⟩
        · rw [hk] at hkf; cases hkf
        · rw [hk] at hkf; cases hkf
      · -- EnvelopeNotMoved: without the key, the envelope, and no deleted path's blob.
        have hnk : ¬ (keyed = true ∧ ¬ (false = true ∧ a.held = true)) := fun h => by
          simpa using hauth.mpr h
        have hkf : keyed = false := by
          cases hkey : keyed
          · rfl
          · exact absurd ⟨hkey, fun h => by simp at h⟩ hnk
        obtain ⟨henv, hel⟩ := hverdict
        have hmv : a.moved = false := (spec_result (hans.elsewhere t k a ht ha) hel false rfl).symm
        have hnd : x.oid ∉ c.deleted := fun hd => by
          rw [(hcon.moved k.val x a hx ha).mpr hd] at hmv; cases hmv
        refine ⟨fun _ _ => ⟨hxr, _, hblob, fun hk => ?_, fun _ => ⟨hid ▸ henv, Or.inr hnd⟩⟩, fun hk => ?_⟩
        · rw [hk] at hkf; cases hkf
        · rw [hk] at hkf; cases hkf

/-- Every entry an accepted audit examined is `AuditEntryChecked`: the
    verified `commit_verdict` checked every examined position
    (`commit_verdict_accepts`). -/
theorem audit_checked {E : Type} {ans : StagedEvidence E} {cache : AuditedEntries E}
    {pinst : V3Primitives P} {prims : P}
    {config : Std.Array U8 55#usize} {id : Std.Array U8 16#usize} {g : GitState} {c : AuditedCommit}
    {base : AuditBase} {run : AuditedRun E} {keyed : Bool}
    (hR : keyed = true → Realizes pinst prims σ) (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts c base run) (hans : AuditAnswers ans cache pinst prims config id keyed g run)
    (hplan : AuditAccepted ans cache id keyed base run) {x : Entry} (hx : x ∈ run.entries) :
    AuditEntryChecked σ (wireBytes config) keyed base g c x := by
  obtain ⟨good, hans⟩ := hans
  obtain ⟨s', hv⟩ := hplan
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hx
  have hpf : p < run.facts.length := by rw [run.facts_len]; exact hp
  have hpk : p < 2 ^ UScalarTy.Usize.numBits := by
    have := run.facts.property; scalar_tac
  exact audit_entry_checked hR hid hcon hans (k := Usize.ofNatCore p hpk) (by simp [Usize.ofNatCore])
    (commit_verdict_accepts good hans.read_good hans.passed_good hans.start hv _
      (by simpa [Usize.ofNatCore] using hpf))

/-! ## One commit -/

/-- **The records of a keyed-audited commit authenticate.** If the keyed
    audit accepted the commit, its records authenticate (`RecordsAuthentic`),
    given its parent's when the audit trusted the parent. -/
theorem keyed_audit_records_authentic {E : Type} (g : GitState) (c : AuditedCommit) (base : AuditBase)
    (run : AuditedRun E) (ans : StagedEvidence E) (cache : AuditedEntries E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hR : Realizes pinst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts c base run)
    (hans : AuditAnswers ans cache pinst prims config id true g run)
    (hplan : AuditAccepted ans cache id true base run)
    (hparent : base = .Parent → RecordsAuthentic σ (wireBytes config) g c.parent) :
    RecordsAuthentic σ (wireBytes config) g c.tree := by
  intro y hy hsel
  rcases hcon.covers y hy hsel.2 with hex | ⟨hb, hyp⟩
  · rcases (audit_checked (fun _ => hR) hid hcon hans hplan hex).records rfl hsel with h | ⟨hb, hyp⟩
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
    (run : AuditedRun E) (ans : StagedEvidence E) (cache : AuditedEntries E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hR : Realizes pinst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts c base run)
    (hans : AuditAnswers ans cache pinst prims config id true g run)
    (hplan : AuditAccepted ans cache id true base run)
    (pfilter : List Nat → List Nat)
    (hpsel : base = .Parent → SelectionAuthentic σ (wireBytes config) g pfilter c.parent)
    (hagree : AuditSelectionAgrees c run pfilter) :
    SelectionAuthentic σ (wireBytes config) g c.filter c.tree := by
  intro x hx hs hnr
  by_cases hex : x ∈ run.entries
  · obtain ⟨hreg, content, hc', hk, -⟩ := (audit_checked (fun _ => hR) hid hcon hans hplan hex).selected hs hnr
    exact ⟨hreg, content, hc', hk rfl⟩
  · rcases hcon.covers x hx hnr with hex' | ⟨hb, hxp⟩
    · exact absurd hex' hex
    · exact hpsel hb x hxp (hagree x hx hnr hex ▸ hs) hnr

/-- **The keyed audit of one commit.** Assume the audit's contracts
    (`AuditContracts`: the diff contract A20 and Git's selection A19), its
    evidence (`AuditAnswers`: object reads A11/A21 and answers A4),
    primitives that realize the suite (`Realizes`, A5) and the
    configuration's id (A5). If the keyed audit of the commit accepted
    (`AuditAccepted`: the verified `commit_verdict` returned `Ok`), then

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
    (run : AuditedRun E) (ans : StagedEvidence E) (cache : AuditedEntries E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hR : Realizes pinst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts c base run)
    (hans : AuditAnswers ans cache pinst prims config id true g run)
    (hplan : AuditAccepted ans cache id true base run)
    (hparent : base = .Parent → RecordsAuthentic σ (wireBytes config) g c.parent)
    (pfilter : List Nat → List Nat)
    (hpsel : base = .Parent → SelectionAuthentic σ (wireBytes config) g pfilter c.parent)
    (hagree : AuditSelectionAgrees c run pfilter) :
    RecordsAuthentic σ (wireBytes config) g c.tree ∧ SelectionAuthentic σ (wireBytes config) g c.filter c.tree :=
  ⟨keyed_audit_records_authentic g c base run ans cache pinst prims config id hR hid hcon hans hplan hparent,
    keyed_audit_selection_authentic g c base run ans cache pinst prims config id hR hid hcon hans hplan pfilter hpsel
      hagree⟩

/-- **The keyless audit of one commit.** Under the same contracts (the
    primitives are never used), if the audit without the key accepted, every
    examined entry that the commit's attributes select, unless it is
    metadata, is a regular file with this configuration's envelope that the
    parent holds exactly or that is no blob of a path the commit deleted (no
    record moved without re-encryption). Nothing is claimed about
    authenticity: a forged envelope passes (A14). -/
theorem keyless_audit_checks_envelopes {E : Type} (g : GitState) (c : AuditedCommit) (base : AuditBase)
    (run : AuditedRun E) (ans : StagedEvidence E) (cache : AuditedEntries E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts c base run)
    (hans : AuditAnswers ans cache pinst prims config id false g run)
    (hplan : AuditAccepted ans cache id false base run) :
    ∀ x ∈ run.entries, Selected (c.filter x.path) → ¬ Reserved x.path →
      x.Regular ∧ ∃ content, g.blob x.oid = some content ∧
        EnvelopeOk content (σ.digest16 (wireBytes config)) ∧ (x ∈ c.parent ∨ x.oid ∉ c.deleted) := by
  intro x hx hs hnr
  obtain ⟨hreg, content, hc', -, hkl⟩ :=
    (audit_checked (σ := σ) (fun h => by cases h) hid hcon hans hplan hx).selected hs hnr
  exact ⟨hreg, content, hc', hkl rfl⟩

/-! ## A keyless audit that needed no key -/

/-- **The keyless audit needed no key** (`check_entries` in `audit.rs`):
    once the keyless `commit_verdict` accepted the commit, the adapter asks
    the verified `commit_needs_no_key`, on the evidence state that call
    returned, whether the keyed audit would have needed the key for any
    examined entry, and it answered `true` (otherwise the run counts as
    checked by envelope only). -/
def KeylessNeedsNoKey {E : Type} (ans : StagedEvidence E) (cache : AuditedEntries E) (id : Std.Array U8 16#usize)
    (base : AuditBase) (run : AuditedRun E) : Prop :=
  ∀ s, commit_verdict ans cache run.start run.facts false base id = ok (core.result.Result.Ok (), s) →
    commit_needs_no_key ans cache s run.facts base = ok true

/-- **An examined entry that needs no key.** Under the audit's contracts,
    if examined position `k`, whose entry is `x`, needs no key in a `good`
    evidence state (`NeedsNoKeyAt`), then the commit's attributes do not
    select `x` unless it is metadata, and if `x` is a regular, non-reserved
    file its blob is no record of this configuration, or the audit trusted
    it from the parent, which holds it exactly. Nothing is opened, so no key
    and no suite realization is needed: any suite `σ` whose id is the
    configuration's will do. -/
theorem needs_no_key_entry {E : Type} {ans : StagedEvidence E} {cache : AuditedEntries E}
    {pinst : V3Primitives P} {prims : P}
    {config : Std.Array U8 55#usize} {id : Std.Array U8 16#usize} {g : GitState} {c : AuditedCommit}
    {base : AuditBase} {run : AuditedRun E} {keyed : Bool} {good : E → Prop}
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts c base run) (hans : AuditAnswersIn ans cache pinst prims config id keyed g run good)
    {s : E} (hs : good s) {k : Usize} {x : Entry} (hx : run.entries[k.val]? = some x)
    (hnk : NeedsNoKeyAt ans cache s run.facts base k) :
    (Selected (c.filter x.path) → ¬ Reserved x.path → False) ∧
    (Selectable x → RecordAuthentic σ (wireBytes config) g x ∨ (base = .Parent ∧ x ∈ c.parent)) := by
  obtain ⟨path, a, hp, ha, hcheck⟩ := hnk
  have hspec := fun c' (h : audit_check a path true base = ok c') =>
    spec_result (audit_check_spec a path true base) h
  rw [hans.path s k x path hs hx hp] at hspec
  have hreg := hcon.regular k.val x a hx ha
  have hsel := hcon.selected k.val x a hx ha
  have hunsel : a.selected = false → Selected (c.filter x.path) → False := fun hf hs' => by
    rw [hsel.mpr hs'] at hf; cases hf
  rcases hcheck with hskip | ⟨hair, hrec⟩
  · -- Skip, with the key: metadata, a symlink or submodule, or trusted from the parent.
    have hc := hspec _ hskip
    simp only [AuditCheckOf] at hc
    refine ⟨fun hs' hnr => ?_, fun ⟨hxr, hnr⟩ => ?_⟩
    · rcases hc with hr | ⟨hf, -⟩
      · exact hnr hr
      · exact hunsel hf hs'
    · rcases hc with hr | ⟨-, hn | ⟨hh, hb⟩ | ⟨hkf, -⟩⟩
      · exact absurd hr hnr
      · rw [hreg.mpr hxr] at hn; cases hn
      · exact Or.inr ⟨hb, (hcon.held k.val x a hx ha).mp hh⟩
      · cases hkf
  · -- AuthenticateIfRecord, and the blob is no record: nothing to authenticate.
    obtain ⟨-, hf, -, -, -⟩ := hspec _ hair
    refine ⟨fun hs' _ => hunsel hf hs', fun _ => Or.inl ?_⟩
    obtain ⟨content, hc', hpre⟩ := spec_result (hans.is_record s k x hs hx) hrec rfl
    exact ⟨content, hc', fun henv => absurd (hid ▸ henv) (not_envelope_of_prefix hpre)⟩

/-- **A keyless audit that needed no key authenticates the commit.** Assume
    the audit's contracts (`AuditContracts`, A20, A19) and its evidence
    without the key (`AuditAnswers`: the paths and the `is_record` answers,
    A4, A11, A21). If the keyless audit accepted the commit (`AuditAccepted`)
    and the verified `commit_needs_no_key` then answered `true`
    (`KeylessNeedsNoKey`), the commit keeps both invariants of the keyed
    audit under every suite `σ` whose id is the configuration's (A5:
    `config_id`), with no key and no `Realizes`, since no record is opened:

    * **its records authenticate** (`RecordsAuthentic`), given the parent's
      under `σ` when the audit trusted the parent (`AuditBase.Parent`): an
      examined regular, non-reserved file is no record of the configuration
      or is the parent's exactly;
    * **its selection authenticates** (`SelectionAuthentic`), given the
      parent's selection `pfilter` under `σ` and its agreement on the
      entries the audit did not examine (`AuditSelectionAgrees`, A19): an
      examined selected entry always needs the key, so every selected entry
      is the parent's.

    The `is_record` answer is trusted as for the keyed audit (A4, A21). -/
theorem keyless_audit_needing_no_key_authenticates {E : Type} (g : GitState) (c : AuditedCommit) (base : AuditBase)
    (run : AuditedRun E) (ans : StagedEvidence E) (cache : AuditedEntries E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts c base run)
    (hans : AuditAnswers ans cache pinst prims config id false g run)
    (hplan : AuditAccepted ans cache id false base run)
    (hnokey : KeylessNeedsNoKey ans cache id base run)
    (hparent : base = .Parent → RecordsAuthentic σ (wireBytes config) g c.parent)
    (pfilter : List Nat → List Nat)
    (hpsel : base = .Parent → SelectionAuthentic σ (wireBytes config) g pfilter c.parent)
    (hagree : AuditSelectionAgrees c run pfilter) :
    RecordsAuthentic σ (wireBytes config) g c.tree ∧ SelectionAuthentic σ (wireBytes config) g c.filter c.tree := by
  obtain ⟨good, hans⟩ := hans
  obtain ⟨s, hv⟩ := hplan
  have hs : good s := commit_verdict_ends_good good hans.read_good hans.passed_good hans.start hv
  have hall := commit_needs_no_key_true (hnokey s hv)
  -- Every examined entry needs no key.
  have hentry : ∀ x ∈ run.entries, (Selected (c.filter x.path) → ¬ Reserved x.path → False) ∧
      (Selectable x → RecordAuthentic σ (wireBytes config) g x ∨ (base = .Parent ∧ x ∈ c.parent)) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hx
    have hpf : p < run.facts.length := by rw [run.facts_len]; exact hp
    have hpk : p < 2 ^ UScalarTy.Usize.numBits := by
      have := run.facts.property; scalar_tac
    exact needs_no_key_entry hid hcon hans hs (k := Usize.ofNatCore p hpk) (by simp [Usize.ofNatCore])
      (hall _ (by simpa [Usize.ofNatCore] using hpf))
  refine ⟨fun y hy hsel => ?_, fun x hx hs' hnr => ?_⟩
  · rcases hcon.covers y hy hsel.2 with hex | ⟨hb, hyp⟩
    · rcases (hentry y hex).2 hsel with h | ⟨hb, hyp⟩
      · exact h
      · exact hparent hb _ hyp hsel
    · exact hparent hb y hyp hsel
  · by_cases hex : x ∈ run.entries
    · exact ((hentry x hex).1 hs' hnr).elim
    · rcases hcon.covers x hx hnr with hex' | ⟨hb, hxp⟩
      · exact absurd hex' hex
      · exact hpsel hb x hxp (hagree x hx hnr hex ▸ hs') hnr

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
    (run : AuditedRun A) (aans : StagedEvidence A) (acache : AuditedEntries A)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hR : Realizes inst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts c base run)
    (hans : AuditAnswers aans acache inst prims config id true g run)
    (hplan : AuditAccepted aans acache id true base run)
    (hparent : base = .Parent → RecordsAuthentic σ (wireBytes config) g c.parent)
    (hconfig : CommitConfig g c.tree (wireBytes config))
    (k : CheckedCommit E) (hgit : HookContracts k.g k.run) (hcfg : ConfigCommitted k.g k.config)
    (hhead : k.g.head = c.tree)
    (hobjects : ∀ oid content, g.blob oid = some content → k.g.blob oid = some content) :
    k.run.samePolicy = true → RecordsAuthentic σ k.config k.g k.g.head := by
  intro hguard
  have hrec := keyed_audit_records_authentic g c base run aans acache inst prims config id hR hid hcon hans hplan
    hparent
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
    (g : GitState) (c : AuditedCommit) (base : AuditBase) (run : AuditedRun A) (aans : StagedEvidence A)
    (acache : AuditedEntries A)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hcon : AuditContracts c base run)
    (hans : AuditAnswers aans acache inst prims config id true g run)
    (hplan : AuditAccepted aans acache id true base run)
    (hparent : base = .Parent → RecordsAuthentic σ (wireBytes config) g c.parent)
    (hconfig : CommitConfig g c.tree (wireBytes config))
    (hhead : (h 0).g.head = c.tree)
    (hobjects : ∀ oid content, g.blob oid = some content → (h 0).g.blob oid = some content) :
    ∀ i ≤ n, RecordsAuthentic σ (h i).config (h i).g (h i).g.index ∧ AuthenticatedIndex σ (h i).config (h i).g := by
  have h0 := hcommits 0 (Nat.zero_le n)
  exact keyed_history_authenticated_by_guard ans hR h n hcommits hsteps (fun hg _ =>
    audited_head_starts_keyed_history g c base run aans acache config id hR hid hcon hans hplan hparent hconfig (h 0)
      h0.contracts h0.config hhead hobjects hg)

/-! ## A chain of audited commits -/

/-- One commit's audit in a run: the commit, its base, the audit's run of
    `commit_verdict` (its examined entries, facts and evidence), and its
    configuration and id. -/
structure AuditRun (A : Type) where
  commit : AuditedCommit
  base : AuditBase
  run : AuditedRun A
  config : Std.Array U8 55#usize
  id : Std.Array U8 16#usize

/-- The commit's keyed audit accepted, with its contracts and answers. -/
structure KeyedAudit {A : Type} (ans : StagedEvidence A) (cache : AuditedEntries A) (pinst : V3Primitives P)
    (prims : P) (σ : Suite) (g : GitState) (r : AuditRun A) : Prop where
  id : wireBytes r.id = σ.digest16 (wireBytes r.config)
  contracts : AuditContracts r.commit r.base r.run
  answers : AuditAnswers ans cache pinst prims r.config r.id true g r.run
  accepted : AuditAccepted ans cache r.id true r.base r.run

/-- `r'` audits a child of `r`'s commit: its first parent is `r`'s commit;
    when it trusts the parent, its configuration is `r`'s (the adapter
    trusts the parent only when `diff-tree` does not list the config, A20,
    A11); and its selection of an entry it did not examine is `r`'s
    (`AuditSelectionAgrees`, A19). -/
structure AuditStep {A : Type} (r r' : AuditRun A) : Prop where
  parent : r'.commit.parent = r.commit.tree
  config : r'.base = .Parent → r'.config = r.config
  selection : AuditSelectionAgrees r'.commit r'.run r.commit.filter

/-- **A chain of keyed audits.** Take audits `a 0, …, a n` in one object
    store, each a keyed audit that accepted (`KeyedAudit`, under one key),
    each commit's first parent the previous commit (`AuditStep`), and the
    first one starting from a root commit or a configuration change
    (`AuditBase.Tree`), or from a first parent outside the chain whose
    records and selection (under the first commit's attributes)
    authenticate. Then every commit's records and selection authenticate. -/
theorem keyed_audit_chain_authenticated {A : Type} (ans : StagedEvidence A) (cache : AuditedEntries A)
    (hR : Realizes inst prims σ)
    (g : GitState) (a : Nat → AuditRun A) (n : Nat)
    (haudits : ∀ i ≤ n, KeyedAudit ans cache inst prims σ g (a i))
    (hsteps : ∀ i < n, AuditStep (a i) (a (i + 1)))
    (hstart : (a 0).base = .Parent → RecordsAuthentic σ (wireBytes (a 0).config) g (a 0).commit.parent ∧
      SelectionAuthentic σ (wireBytes (a 0).config) g (a 0).commit.filter (a 0).commit.parent) :
    ∀ i ≤ n, RecordsAuthentic σ (wireBytes (a i).config) g (a i).commit.tree ∧
      SelectionAuthentic σ (wireBytes (a i).config) g (a i).commit.filter (a i).commit.tree := by
  intro i hi
  induction i with
  | zero =>
    have ha := haudits 0 hi
    exact keyed_audit_authenticates_commit g _ _ _ ans cache inst prims _ _ hR ha.id ha.contracts ha.answers
      ha.accepted
      (fun hb => (hstart hb).1) (a 0).commit.filter (fun hb => (hstart hb).2) (fun _ _ _ _ => rfl)
  | succ k ih =>
    have hk := ih (by omega)
    have hs := hsteps k (by omega)
    have ha := haudits (k + 1) hi
    exact keyed_audit_authenticates_commit g _ _ _ ans cache inst prims _ _ hR ha.id ha.contracts ha.answers
      ha.accepted
      (fun hb => by rw [hs.parent, hs.config hb]; exact hk.1) (a k).commit.filter
      (fun hb => by rw [hs.parent, hs.config hb]; exact hk.2) hs.selection

end Transcrypt.V3Verification

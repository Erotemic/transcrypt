import V3Wire.Verification.Audit

/-!
# Product assurance: the top-level statement

`transcrypt_product_assurance` composes the product theorems of
`ProductSecurity.lean` and `Audit.lean` into one statement about one
checkout, one stored key and one history of commits:

* the **crypto context** is the output of the verified `unlock_stored_key`
  (`StoredKeyRun`, `StoredKeyUnlocked`), not an arbitrary primitive
  instance: the same primitives and configuration are the ones every
  publication check, audit, checkout and repair below uses;
* the **history** starts at a commit that a keyed audit accepted, or with a
  check that trusted nothing from `HEAD` (`HistoryStart`), and continues
  with keyed publications (`ValidCheckedPublication`), each committed by Git
  from the index checked before it (`GuardedHistoryStep`);
* the **conclusion** has four named parts: the stored key validated the
  context (`ValidatedCryptoContext`), every checked state is authenticated
  (`AuthenticatedRepositoryState`), checkout releases only authenticated
  plaintext (`AuthenticatedRecovery`), and the repair step never launders
  (`NoLaunderingRepair`).

The hypotheses are the external contracts (`KeyScheduleRealizes`, and
inside the named runs `HookContracts`, `HookAnswers`, `AuditContracts`,
`AuditAnswers`, `GuardedHistoryStep`, `RepairContracts`), the observed
accepted runs of the verified core, and the start of the audited range.
None states a conclusion.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

variable {P : Type} {inst : V3Primitives P}

/-! ## The crypto context -/

/-- One call of the stored-key decision, as `Key::load` makes it: whether the
    key file exists, its bytes, the current configuration's bytes, and the
    primitives and configuration it kept from the result; `id` is the
    configuration's public id the adapter computed (`config_id`). -/
structure StoredKeyRun (P : Type) where
  present : Bool
  file : Slice U8
  current : Slice U8
  keyed : P
  config : Std.Array U8 55#usize
  id : Std.Array U8 16#usize

/-- The suite of the key file's own key bytes (`storedKeyBytes`). -/
abbrev StoredKeyRun.suite (σk : List Nat → Suite) (k : StoredKeyRun P) : Suite :=
  σk (storedKeyBytes (sliceBytes k.file))

/-- **The stored key unlocked.** The verified `unlock_stored_key` returned
    the run's primitives and configuration (`Ok`, the only result on which
    `Key::load` uses the stored key), and the run's id is the suite's digest
    of that configuration (A5: `config_id` is the truncated SHA-256). -/
structure StoredKeyUnlocked (inst : V3Primitives P) (sched : V3KeySchedule P) (σk : List Nat → Suite)
    (k : StoredKeyRun P) : Prop where
  unlock : unlock_stored_key inst sched k.present k.file k.current = ok (core.result.Result.Ok (k.keyed, k.config))
  id : wireBytes k.id = (k.suite σk).digest16 (wireBytes k.config)

/-! ## The history -/

/-- **A keyed publication with the validated key.** The commit was accepted
    by a keyed pre-commit check (`KeyedCommit`: its run's Git contracts
    A11/A19–A21, the committed configuration, and the accepted check with
    the adapter's answers, A4), and that check used the primitives the
    stored-key decision returned, under the configuration it validated. -/
structure ValidCheckedPublication {E : Type} (ans : StagedEvidence E) (inst : V3Primitives P)
    (σk : List Nat → Suite) (k : StoredKeyRun P) (c : CheckedCommit E) : Prop
    extends KeyedCommit ans inst k.keyed (k.suite σk) c where
  validated : c.config = wireBytes k.config

/-- **A keyed audit of the range before the history.** Audits `a 0, …, a m`
    in one object store, each a keyed audit that accepted (`KeyedAudit`, with
    `AuditContracts` and `AuditAnswers`) with the validated primitives under
    the validated configuration, each commit's first parent the previous
    commit (`AuditStep`), and the first one starting from a root commit or a
    configuration change, or from a first parent outside the range whose
    records and selection authenticate (A13: what the remote already has). -/
structure KeyedAuditRange {A : Type} (aans : StagedEvidence A) (inst : V3Primitives P) (σk : List Nat → Suite)
    (k : StoredKeyRun P) (g : GitState) (a : Nat → AuditRun A) (m : Nat) : Prop where
  audits : ∀ i ≤ m, KeyedAudit aans inst k.keyed (k.suite σk) g (a i)
  validated : ∀ i ≤ m, (a i).config = k.config
  steps : ∀ i < m, AuditStep (a i) (a (i + 1))
  start : (a 0).base = .Parent → RecordsAuthentic (k.suite σk) (wireBytes (a 0).config) g (a 0).commit.parent ∧
    SelectionAuthentic (k.suite σk) (wireBytes (a 0).config) g (a 0).commit.filter (a 0).commit.parent

/-- **How the history starts.** The first commit's check trusted nothing
    from `HEAD` (`full`: not incremental, or the guard `false`), or the
    commit its `HEAD` names is the last of a keyed audit range (`audited`:
    Git lists the same tree, A20, and objects keep their content, A11). -/
inductive HistoryStart {E A : Type} (aans : StagedEvidence A) (inst : V3Primitives P) (σk : List Nat → Suite)
    (k : StoredKeyRun P) (c : CheckedCommit E) : Prop
  | full (hmode : c.mode = .full)
  | audited (g : GitState) (a : Nat → AuditRun A) (m : Nat) (hrange : KeyedAuditRange aans inst σk k g a m)
      (hhead : c.g.head = (a m).commit.tree)
      (hobjects : ∀ oid content, g.blob oid = some content → c.g.blob oid = some content)

/-! ## The conclusion -/

/-- **An authenticated repository state.** Every record of this
    configuration at a regular, non-reserved path of the index authenticates
    at that path, whatever selects it (`RecordsAuthentic`), and every path
    the committed attributes select is a regular, non-reserved file whose
    blob authenticates there (`AuthenticatedIndex`). -/
structure AuthenticatedRepositoryState (σ : Suite) (config : List Nat) (g : GitState) : Prop where
  records : RecordsAuthentic σ config g g.index
  selected : AuthenticatedIndex σ config g

/-- **Authenticated recovery** with the primitives `keyed` under `config`
    (id `id`): every smudge run releases only the plaintext the record
    authenticates to at its exact path, or keeps the record unchanged, and
    refuses a record it decided to open that does not authenticate
    (`CheckoutOutcome`); and with the key every genuine record opens to
    exactly its plaintext. -/
structure AuthenticatedRecovery (inst : V3Primitives P) (keyed : P) (σ : Suite) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) : Prop where
  releases : ∀ (unlocked keepRecord : Bool) (path record buf : Slice U8),
    smudgeModel inst keyed config id unlocked keepRecord path record buf ⦃ r =>
      CheckoutOutcome σ (wireBytes config) (wireBytes id) unlocked path record r ⦄
  opens : ∀ (path record buf : Slice U8) (pt : List Nat),
    OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes record) pt → buf.length = pt.length →
    smudgeModel inst keyed config id true false path record buf ⦃ r => ∃ out, r = some out ∧ sliceBytes out = pt ⦄

/-- **Transcrypt's product assurance.** Let a checkout's stored-key decision
    have unlocked (`StoredKeyUnlocked`: the verified `unlock_stored_key`
    returned the primitives `k.keyed` and the configuration `k.config` for
    the key file `k.file`), with the key-schedule contract
    `KeyScheduleRealizes` (A5, A17). Take a history of commits `h 0, …, h n`,
    each a keyed publication with exactly those primitives and that
    configuration (`ValidCheckedPublication`: the hook's Git contracts A11,
    A19–A21 and the adapter's answers A4), each made by Git from the index
    checked before it (`GuardedHistoryStep`, A22, A11), starting at a check
    that trusted nothing from `HEAD` or at a commit a keyed audit range with
    the same key accepted (`HistoryStart`; the audit's contracts A19–A21,
    A4, and the parent of its first commit when it lies outside the range,
    A13). Then, with `σ` the suite of the file's own key bytes:

    * **key use** (`ValidatedCryptoContext`): the key is used only for the
      configuration it authenticates, with its own check value, and every
      record its primitives open or seal is bound to that configuration and
      the exact path;
    * **publication and history** (`AuthenticatedRepositoryState`): every
      checked index keeps the record invariant and every selected path
      authenticates at that path under that configuration;
    * **recovery** (`AuthenticatedRecovery`): checkout with those primitives
      releases only plaintext authenticated at the exact path under that
      configuration, never on a failed authentication, and opens every
      genuine record;
    * **repair** (`NoLaunderingRepair`): every repair the hook decided with
      those primitives (`RepairContracts`: A4, A20, A21, A23) seals only the
      user's change or plaintext `protect` forced, rebinds only the user's
      move, and never launders content imported from a commit.

    Excluded, within these contracts: publishing plaintext, a forged
    record, a record sealed for another path or another configuration;
    releasing unauthenticated plaintext; turning imported content into an
    accepted record; using a stale, other-configuration or damaged key.
    Not excluded: what the contracts assume (Git, the adapter's loop and
    answers, the key schedule, AES-SIV/Argon2id security, A10), the
    incremental hook's trust in an unaudited local history (A24, A13),
    deterministic equality and replay of an old record at its path, and
    any confidentiality claim (none is proved). -/
theorem transcrypt_product_assurance {E A : Type} {sched : V3KeySchedule P} {σk : List Nat → Suite}
    (hK : KeyScheduleRealizes inst sched σk)
    (k : StoredKeyRun P) (hk : StoredKeyUnlocked inst sched σk k)
    (ans : StagedEvidence E) (h : Nat → CheckedCommit E) (n : Nat)
    (hcommits : ∀ i ≤ n, ValidCheckedPublication ans inst σk k (h i))
    (hsteps : ∀ i < n, GuardedHistoryStep (h i) (h (i + 1)))
    (aans : StagedEvidence A) (hstart : HistoryStart aans inst σk k (h 0)) :
    ValidatedCryptoContext inst (k.suite σk) (sliceBytes k.file) (sliceBytes k.current) k.keyed k.config ∧
    (∀ i ≤ n, AuthenticatedRepositoryState (k.suite σk) (wireBytes k.config) (h i).g) ∧
    AuthenticatedRecovery inst k.keyed (k.suite σk) k.config k.id ∧
    (∀ g run (hc : RepairContracts inst k.keyed g run), run.config = k.config →
      NoLaunderingRepair (k.suite σk) g run (g.index[run.i.val]'hc.entry)) := by
  have hctx := stored_key_binds_file_operations hK k.present k.file k.current k.keyed k.config hk.unlock
  have hR := hctx.realizes
  -- The start of the history: `HEAD`'s records, when the first check trusted them.
  have hfirst : (h 0).run.samePolicy = true → (h 0).mode = .incremental →
      RecordsAuthentic (k.suite σk) (h 0).config (h 0).g (h 0).g.head := by
    intro _ hinc
    cases hstart with
    | full hmode => rw [hmode] at hinc; cases hinc
    | audited g a m hrange hhead hobjects =>
      have hrec := (keyed_audit_chain_authenticated aans hR g a m hrange.audits hrange.steps hrange.start m
        (Nat.le_refl m)).1
      rw [hrange.validated m (Nat.le_refl m)] at hrec
      rw [(hcommits 0 (Nat.zero_le n)).validated, hhead]
      intro x hx hsel
      obtain ⟨content, hc, hra⟩ := hrec x hx hsel
      exact ⟨content, hobjects _ _ hc, hra⟩
  have hhist := keyed_history_authenticated_by_guard ans hR h n
    (fun i hi => (hcommits i hi).toKeyedCommit) hsteps hfirst
  refine ⟨hctx, fun i hi => ?_, ⟨fun unlocked keepRecord path record buf =>
      checkout_releases_only_authenticated_plaintext hR k.config k.id unlocked keepRecord path record buf,
    fun path record buf pt hop hl => checkout_opens_genuine_records hR k.config k.id hk.id path record buf pt hop hl⟩,
    fun g run hc _ => repair_never_launders g run hR hc⟩
  obtain ⟨hrec, hsel⟩ := hhist i hi
  rw [(hcommits i hi).validated] at hrec hsel
  exact ⟨hrec, hsel⟩

end Transcrypt.V3Verification

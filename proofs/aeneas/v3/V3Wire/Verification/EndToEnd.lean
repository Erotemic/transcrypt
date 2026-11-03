import V3Wire.Verification.Lifecycle
import V3Wire.Verification.Objects
import V3Wire.Verification.Snapshot
import V3Wire.Verification.Staged

/-!
# End to end: selected paths enter Git as authenticated ciphertext

The pre-commit hook (`transcrypt_rs::lifecycle::verify` with `seal`) is the
last code that sees the index before Git records a commit. This file states,
as one conditional theorem, what its acceptance guarantees about that commit,
and names every assumption it rests on.

* **Git, as data.** `GitState` is what Git holds when the hook runs: the
  index it will commit, `HEAD`, `HEAD^1`, the commits being brought in, the
  effective `filter` value of each path under the attributes being
  committed, and the object store.
* **Adapter contracts** (`docs/verification/V3-ASSUMPTIONS.md`): Git reports
  its snapshots exactly (`GitListing`, A20), answers `check-attr` with the
  committed attributes (`GitAttributes`, A19), and an object read by id
  returns that object (`GitObject`, A11, A21), gathered for one run as
  `HookContracts`; the adapter's blobs and answers to the verified check
  mean what they say (`HookAnswers`, A4, A11, A21); the crypto primitives
  realize the
  abstract suite (`Realizes`, A5); Git commits the index the hook checked
  (A22, stated in prose: the conclusion is about `g.index`).
* **The run.** `HookEvidence` is what the adapter obtained from the
  verified core, in five groups: the parsed snapshots (`HookSnapshots`:
  three `OrderedListing`s, as the adapter's `OrderedListing`: parsed, each
  path once, with checked object orders), the attribute selection
  (`HookSelection`), the `HEAD`/`HEAD^1` membership of each entry's exact
  record (`HookMembership`, `held_records`), the adapter's evidence
  (`HookStart`: the state it passes to the check), and the settled guard
  (`HookGuard`: the verified `policy_unchanged`). The check of every entry
  is one call of the extracted `index_verdict` (`HookAccepted`), whose loop
  is proved to check every position in order with the run's inputs
  (`staged_check`), read the blob when `reads_blob` says so, and pass it by
  `staged_verdict`, refusing otherwise (`index_verdict_accepts`). The
  adapter answers the verdict's questions (`StagedEvidence`) and refuses
  unless the call returned `Ok` (A4). For the repairs, `RepairInputs` are the
  values the adapter computed for one entry (its `Provenance` and its blob's
  `RecordClass`, on which the verified `repair_plan` decides) and
  `RepairContracts` what they are.

`hook_accepts_only_authenticated_ciphertext`: if the run accepted, the
index is an `AcceptedIndex`: every path the committed attributes select is
a regular, non-reserved entry (`AcceptedProtectedEntry`) whose blob, when
unlocked, authenticates at exactly that path under the committed
configuration (or, in the incremental hook, is unchanged since `HEAD` and
`HEAD^1` and has the v3 envelope; `KeyedEntryOk`); when locked, it has the
envelope of this configuration and is not a blob moved from another path
(`KeylessEnvelopeOk`). The proof goes through named steps: the snapshots
are sorted (`hook_snapshots_sorted`), the flags are Git's selection
(`hook_flags`), a selected entry is selectable (`hook_selectable`), the
verified loop accepted every position (`index_verdict_accepts`), and an
accepted position, by `staged_check_spec` and `staged_verdict_ok`, makes
its entry `EntryChecked` (`hook_entry_checked`).
`hook_records_authentic`: with the key, the run also keeps a record
invariant that does not depend on selection (`RecordsAuthentic`: every
regular, non-reserved entry whose blob has this configuration's envelope
authenticates at its own path), given `HEAD`'s only when it trusted `HEAD`;
`hook_authenticated_of_records`: with it, every selected entry
authenticates.
`hook_repairs_only_local_changes`: everything the hook re-encrypts before
that check was a local change of the user, and a rebind re-encrypts only a
record that authenticates at the path of the `HEAD` record it names, a place
it was moved from. `hook_provenance`: the provenance the verified
`entry_provenance` computes is where the content came from;
`hook_skips_only_unrepairable`: an entry whose blob the hook does not read
(`needs_record`) is neither the user's change nor forced.

The listings are sorted by path (the verified parse checks it), so lookups
are binary searches, and lookups by object id go through object orders that
the adapter sorts and `object_order_ok` checks.
`hook_accepts_only_authenticated_ciphertext_given_history` adds A24 in its
selection form (`HeadAuthentic`) and concludes that every selected entry
authenticates (`AuthenticatedIndex`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

variable {P : Type} {inst : V3Primitives P} {prims : P} {σ : Suite}

/-! ## Git, as data, and the adapter's contracts -/

/-- What Git holds when the pre-commit hook runs. `filter p` is the effective
    `filter` attribute of path `p` under the attributes being committed;
    `blob oid` is the content of an object. -/
structure GitState where
  index : List Entry
  head : List Entry
  parent : List Entry
  incoming : Option (List Entry)
  filter : List Nat → List Nat
  blob : List Nat → Option (List Nat)

/-- **A20.** The listing Git printed is exactly the listing of these
    well-formed entries (`ls-files --stage -z`; for a commit `ls-tree -r -z`,
    rewritten record by record to the same shape by the adapter). -/
def GitListing (listing : Slice U8) (es : List Entry) : Prop :=
  (∀ e ∈ es, EntryOk e) ∧ sliceBytes listing = listingBytes es

/-- **A19.** Git's answer to `check-attr --cached -z --stdin filter` for the
    index's paths reports each path's effective `filter` under the attributes
    being committed. -/
def GitAttributes (g : GitState) (response : Slice U8) : Prop :=
  (∀ e ∈ g.index, 0 ∉ g.filter e.path) ∧
    sliceBytes response = attrResponse ((g.index.map (·.path)).zip (g.index.map (fun e => g.filter e.path)))

/-- **A11, A21.** Bytes read by object id are that object's content: `git
    cat-file --batch` answers the requested id (its header is checked by the
    verified `parse_batch_header`), the adapter reads exactly the announced
    size, and an object id names one content. -/
def GitObject (g : GitState) (oid : List Nat) (content : Slice U8) : Prop :=
  g.blob oid = some (sliceBytes content)

theorem listingBytes_count (es : List Entry) (h : ∀ e ∈ es, EntryOk e) :
    (listingBytes es).count 0 = es.length := by
  induction es with
  | nil => simp [listingBytes]
  | cons e es ih =>
    have hn := entryRecord_no_nul (h e (by simp))
    simp only [listingBytes, List.flatMap_cons, List.count_append, List.length_cons] at ih ⊢
    rw [ih (fun x hx => h x (by simp [hx])), List.count_eq_zero_of_not_mem hn]
    simp; omega

/-! ## Snapshots as the adapter holds them -/

/-- A snapshot as the adapter's `Listing` holds it: Git's bytes, parsed by
    the verified core with one slot per NUL (as the adapter allocates);
    `unique`: each path once (an index or one tree; a merge of several trees
    may repeat a path). -/
structure ParsedListing (unique : Bool) where
  bytes : Slice U8
  ends0 : Slice Usize
  ends : Slice Usize
  ends0_len : ends0.length = (sliceBytes bytes).count 0
  parse : parse_listing bytes ends0 unique = ok (true, ends)

/-- A snapshot with its object order, as the adapter's `OrderedListing`:
    the order the adapter sorted, checked by the core. -/
structure OrderedListing extends ParsedListing true where
  order : Slice Usize
  order_ok : object_order_ok bytes ends order = ok true

/-- A snapshot of what Git printed exactly gives exactly its entries, sorted:
    each path once (`Sorted`). -/
theorem ParsedListing.of_git {es : List Entry} (l : ParsedListing true) (hg : GitListing l.bytes es) :
    ListingOf l.bytes l.ends es ∧ Sorted es := by
  have := spec_result (parse_listing_spec l.bytes l.ends0 true) l.parse
  obtain ⟨hL, hs⟩ := this.2 es ⟨hg.1, hg.2, by rw [l.ends0_len, hg.2, listingBytes_count es hg.1]⟩
  exact ⟨hL, orderedAs_true.mp (hs.mp rfl)⟩

/-- The same for the adapter's merge of several trees (paths may repeat):
    the entries are in path order (`PathOrdered`). -/
theorem ParsedListing.of_git_merged {es : List Entry} (l : ParsedListing false) (hg : GitListing l.bytes es) :
    ListingOf l.bytes l.ends es ∧ PathOrdered es := by
  have := spec_result (parse_listing_spec l.bytes l.ends0 false) l.parse
  obtain ⟨hL, hs⟩ := this.2 es ⟨hg.1, hg.2, by rw [l.ends0_len, hg.2, listingBytes_count es hg.1]⟩
  exact ⟨hL, orderedAs_false.mp (hs.mp rfl)⟩

/-- An ordered snapshot of what Git printed: its entries, sorted, and its
    order is an object order of them (`ObjectOrder`). -/
theorem OrderedListing.of_git {es : List Entry} (l : OrderedListing) (hg : GitListing l.bytes es) :
    ListingOf l.bytes l.ends es ∧ Sorted es ∧ ObjectOrder es l.order := by
  obtain ⟨hL, hs⟩ := l.toParsedListing.of_git hg
  exact ⟨hL, hs, (spec_result (object_order_ok_spec hL l.order) l.order_ok).mp rfl⟩

/-! ## The hook's final check -/

/-- The parsed snapshots: the index, `HEAD` and `HEAD^1`, each path once,
    with object orders. -/
structure HookSnapshots where
  index : OrderedListing
  head : OrderedListing
  parent : OrderedListing

/-- The attribute selection: the protected flags are Git's `check-attr`
    answer, checked against the index's own paths, and no protected entry
    is unselectable. -/
structure HookSelection (g : GitState) (index : OrderedListing) where
  response : Slice U8
  flags0 : Slice Bool
  flags : Slice Bool
  flags0_len : flags0.length = g.index.length
  attrs : parse_listing_attrs index.bytes index.ends response flags0 = ok (true, flags)
  selectable : ∃ sel : Usize, first_unselectable index.bytes index.ends flags = ok sel ∧ sel.val = g.index.length

/-- Membership: whether `HEAD` (every entry) and `HEAD^1` (protected
    entries) hold each entry's exact record, by `held_records`. -/
structure HookMembership (g : GitState) (index head parent : OrderedListing) (flags : Slice Bool) where
  all : Slice Bool
  inHead0 : Slice Bool
  inHead : Slice Bool
  inParent0 : Slice Bool
  inParent : Slice Bool
  all_true : all.val = List.replicate g.index.length true
  inHead0_len : inHead0.length = g.index.length
  in_head : held_records index.bytes index.ends all head.bytes head.ends inHead0 = ok (true, inHead)
  inParent0_len : inParent0.length = g.index.length
  in_parent : held_records index.bytes index.ends flags parent.bytes parent.ends inParent0 = ok (true, inParent)

/-- The adapter's evidence (`IndexEvidence` in `check_staged`) in the state
    it passes to the verified `index_verdict`. -/
structure HookStart (E : Type) where
  start : E

/-- The settled guard: the verified `policy_unchanged` on the three parsed
    snapshots returned `samePolicy`, which the run passes to
    `index_verdict` (`check_staged`: `guard`). -/
structure HookGuard (index head parent : OrderedListing) where
  samePolicy : Bool
  policy : policy_unchanged index.bytes index.ends head.bytes head.ends parent.bytes parent.ends =
    ok samePolicy

/-- What the adapter obtained from the verified core in the hook's final
    check (`check_staged`, after any sealing): it refuses the commit unless
    the results are as shown (A4). The five groups are flattened:
    `run.flags`, `run.inHead`, `run.start`, `run.samePolicy`, ... `E` is the
    type of the adapter's answers. -/
structure HookEvidence (g : GitState) (E : Type) extends HookSnapshots, HookSelection g index,
    HookMembership g index head parent flags, HookStart E, HookGuard index head parent

/-- **The hook's final check accepted.** The verified `index_verdict`, called
    once with the run's inputs (the parsed index listing, Git's selection,
    the `HEAD`/`HEAD^1` membership, the guard) and the adapter's evidence,
    returned `Ok` (A4: the adapter refuses the commit otherwise). -/
def HookAccepted {E : Type} (inst : StagedEvidence E) (id : Std.Array U8 16#usize) (keyed incremental : Bool)
    {g : GitState} (run : HookEvidence g E) : Prop :=
  ∃ s, index_verdict inst run.start run.index.bytes run.index.ends run.flags run.inHead run.inParent keyed
    incremental run.samePolicy id = ok (core.result.Result.Ok (), s)

/-- **A20, A19.** The Git contracts the hook relies on, for one run: Git
    reported the index, `HEAD` and `HEAD^1` exactly, and the committed
    attributes' `filter` values. -/
structure HookContracts {E : Type} (g : GitState) (run : HookEvidence g E) : Prop where
  index : GitListing run.index.bytes g.index
  head : GitListing run.head.bytes g.head
  parent : GitListing run.parent.bytes g.parent
  attributes : GitAttributes g run.response

/-- **A4, A11, A21: the adapter's evidence, in the states `good` describes.**
    `good` holds of the state the run starts in and every `read` keeps it;
    in such a state, what each of the adapter's answers about index position
    `k`, whose entry is `x`, means, under the configuration `config` with id
    `id`:

    * `read` true: the blob `blob` then returns is the content of `x`'s
      object id (`git cat-file` by the snapshot's id, A11, A21);
    * `is_record` `some false`: the blob `x` names is larger than any
      record, or the verified `record_envelope_prefix_ok` refused its size
      and first `fileMinLen` bytes (A21 for the bytes read);
    * `opens` `some true`: the verified `open_record` accepted that blob at
      `x`'s path under `config` (`Key::open`: the stored key's primitives
      `pinst`, or, in private mode, the agent's call of the same function,
      A6);
    * `elsewhere` `some b`: `b` is the result of the verified
      `blob_elsewhere` on the run's ordered snapshots at `k`.

    An answer the adapter could not find is `none`, which the verified
    verdict refuses. Which positions are checked, with which inputs, and that
    a refusal refuses, is `index_verdict`'s (`index_verdict_accepts`). -/
structure HookAnswersIn {E : Type} (inst : StagedEvidence E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (g : GitState) (run : HookEvidence g E)
    (good : E → Prop) : Prop where
  start : good run.start
  read_good : ∀ s k b s', good s → inst.read s k = ok (b, s') → good s'
  read : ∀ s (k : Usize) s' x record, good s → g.index[k.val]? = some x → inst.read s k = ok (true, s') →
    inst.blob s' = ok record → GitObject g x.oid record
  is_record : ∀ s (k : Usize) x, good s → g.index[k.val]? = some x →
    inst.is_record s k ⦃ o => o = some false → ∃ content, g.blob x.oid = some content ∧
      (maxRecord < content.length ∨ ∃ (size : Usize) (pre : Slice U8), size.val = content.length ∧
        sliceBytes pre = content.take Transcrypt.V3Wire.fileMinLen ∧
        record_envelope_prefix_ok size pre id = ok false) ⦄
  opens : ∀ s (k : Usize) x, good s → g.index[k.val]? = some x →
    inst.opens s k ⦃ o => o = some true → ∃ (path record buf out : Slice U8), sliceBytes path = x.path ∧
      GitObject g x.oid record ∧ open_record pinst prims config path record buf = ok (core.result.Result.Ok (), out) ⦄
  elsewhere : ∀ s (k : Usize), good s → inst.elsewhere s k ⦃ o => ∀ b, o = some b →
    blob_elsewhere run.index.bytes run.index.ends run.index.order k run.head.bytes run.head.ends
      run.head.order run.parent.bytes run.parent.ends run.parent.order = ok b ⦄

/-- **A4, A11, A21: the adapter's answers mean what they say**
    (`HookAnswersIn`) in the evidence states of the run, for some
    description `good` of them. -/
def HookAnswers {E : Type} (inst : StagedEvidence E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (g : GitState) (run : HookEvidence g E) :
    Prop :=
  ∃ good, HookAnswersIn inst pinst prims config id g run good

/-- A blob that `is_record` reports as no record has no envelope of this
    configuration: the prefix decision is the whole record's
    (`record_envelope_prefix_ok_spec`, `decodeFileHeaderShape_take`). -/
theorem not_envelope_of_prefix {content : List Nat} {id : Std.Array U8 16#usize}
    (h : maxRecord < content.length ∨ ∃ (size : Usize) (pre : Slice U8), size.val = content.length ∧
      sliceBytes pre = content.take Transcrypt.V3Wire.fileMinLen ∧
      record_envelope_prefix_ok size pre id = ok false) :
    ¬ EnvelopeOk content (wireBytes id) := by
  rintro ⟨hmax, hd⟩
  rcases h with h | ⟨size, pre, hs, hpre, hok⟩
  · omega
  · have := spec_result (record_envelope_prefix_ok_spec size pre id) hok
    have hmin := decodeFileHeaderShape_length hd
    refine absurd (this.mpr ⟨by omega, by omega, ?_, ?_⟩) (by simp)
    · rw [← sliceBytes_length, hpre, List.length_take]; omega
    · rw [hpre, decodeFileHeaderShape_take]; exact hd

/-! ## What an accepted commit is

The conclusion of the end-to-end theorem, in named parts. `config` is the
committed configuration's bytes; its id is `σ.digest16 config`. -/

/-- The index stages `config` as the regular file `.transcrypt/config`. -/
def ConfigCommitted (g : GitState) (config : List Nat) : Prop :=
  ∃ c ∈ g.index, c.path = ascii ".transcrypt/config" ∧ c.Regular ∧ g.blob c.oid = some config

/-- The index, `HEAD` and `HEAD^1` each list every path once, in Git's
    byte order. -/
def SnapshotsSorted (g : GitState) : Prop :=
  Sorted g.index ∧ Sorted g.head ∧ Sorted g.parent

/-- `content` is a record that authenticates at exactly `x`'s path under
    `config`. -/
def AuthenticatedAt (σ : Suite) (config : List Nat) (x : Entry) (content : List Nat) : Prop :=
  ∃ pt, OpensTo σ config x.path content pt

/-- The keyless check: `content` has this configuration's v3 envelope, and
    `x` is unchanged since `HEAD` and `HEAD^1` or its blob is not another
    path's (no record moved without the key). -/
def KeylessEnvelopeOk (σ : Suite) (config : List Nat) (g : GitState) (x : Entry) (content : List Nat) :
    Prop :=
  EnvelopeOk content (σ.digest16 config) ∧
    (Settled g.head g.parent x ∨ ¬ BlobElsewhere [g.index, g.head, g.parent] x)

/-- The keyed check: `content` authenticates at `x`'s path or, in the
    incremental hook, `x` is unchanged since `HEAD` and `HEAD^1` and has this
    configuration's envelope. -/
def KeyedEntryOk (σ : Suite) (config : List Nat) (incremental : Bool) (g : GitState) (x : Entry)
    (content : List Nat) : Prop :=
  AuthenticatedAt σ config x content ∨
    (incremental = true ∧ Settled g.head g.parent x ∧ EnvelopeOk content (σ.digest16 config))

/-- A selected index entry as an accepted commit has it: a regular,
    non-reserved file whose blob passes the keyed check with the key and the
    keyless check without it. -/
def AcceptedProtectedEntry (σ : Suite) (config : List Nat) (keyed incremental : Bool) (g : GitState)
    (x : Entry) : Prop :=
  Selectable x ∧ ∃ content, g.blob x.oid = some content ∧
    (keyed = true → KeyedEntryOk σ config incremental g x content) ∧
    (keyed = false → KeylessEnvelopeOk σ config g x content)

/-- An accepted index: every entry the committed attributes select is an
    `AcceptedProtectedEntry`. -/
def AcceptedIndex (σ : Suite) (config : List Nat) (keyed incremental : Bool) (g : GitState) : Prop :=
  ∀ x ∈ g.index, Selected (g.filter x.path) → AcceptedProtectedEntry σ config keyed incremental g x

/-- An authenticated index: every entry the committed attributes select is a
    regular, non-reserved file whose blob authenticates at its path. -/
def AuthenticatedIndex (σ : Suite) (config : List Nat) (g : GitState) : Prop :=
  ∀ x ∈ g.index, Selected (g.filter x.path) →
    Selectable x ∧ ∃ content, g.blob x.oid = some content ∧ AuthenticatedAt σ config x content

/-- **The record invariant at one entry.** The blob `x` names exists and, if
    it has this configuration's envelope, authenticates at `x`'s path. It
    says nothing about selection. -/
def RecordAuthentic (σ : Suite) (config : List Nat) (g : GitState) (x : Entry) : Prop :=
  ∃ content, g.blob x.oid = some content ∧
    (EnvelopeOk content (σ.digest16 config) → AuthenticatedAt σ config x content)

/-- **The records of a snapshot authenticate.** Every regular, non-reserved
    entry of `es` (the index, or `HEAD`) whose blob has this configuration's
    envelope authenticates at its own path, whatever Git's attributes, local
    attribute files included, select. -/
def RecordsAuthentic (σ : Suite) (config : List Nat) (g : GitState) (es : List Entry) : Prop :=
  ∀ y ∈ es, Selectable y → RecordAuthentic σ config g y

/-! ## The steps of the hook's final check -/

/-- The verified parses give exactly Git's snapshots, each path once. -/
theorem hook_snapshots_sorted {E : Type} {g : GitState} {run : HookEvidence g E} (hgit : HookContracts g run) :
    SnapshotsSorted g :=
  ⟨(run.index.of_git hgit.index).2.1, (run.head.of_git hgit.head).2.1, (run.parent.of_git hgit.parent).2.1⟩

/-- The protected flags are Git's selection of each index entry. -/
theorem hook_flags {E : Type} {g : GitState} {run : HookEvidence g E} (hgit : HookContracts g run) :
    run.flags.val = g.index.map (fun e => decide (Selected (g.filter e.path))) := by
  obtain ⟨hL, -, -⟩ := run.index.of_git hgit.index
  have hflags := (spec_result (parse_listing_attrs_spec hL run.response run.flags0) run.attrs).2
    (g.index.map (fun e => g.filter e.path)) ⟨by simp, by
      intro v hv; obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv; exact hgit.attributes.1 e he,
      run.flags0_len, hgit.attributes.2⟩
  rw [hflags.2, List.map_map]; rfl

/-- An entry's flag is Git's selection of it. -/
theorem hook_flag {E : Type} {g : GitState} {run : HookEvidence g E} (hgit : HookContracts g run)
    {k : Nat} (hk : k < g.index.length) :
    run.flags.val[k]! = true ↔ Selected (g.filter g.index[k].path) := by
  rw [hook_flags hgit, getElem!_pos _ k (by simp; omega)]; simp

/-- A selected entry is protected: its flag is set. -/
theorem hook_flag_of_selected {E : Type} {g : GitState} {run : HookEvidence g E} (hgit : HookContracts g run)
    {k : Nat} (hk : k < g.index.length) (hsx : Selected (g.filter g.index[k].path)) :
    run.flags.val[k]! = true :=
  (hook_flag hgit hk).mpr hsx

/-- `first_unselectable` found no protected entry that is not selectable. -/
theorem hook_selectable {E : Type} {g : GitState} {run : HookEvidence g E} (hgit : HookContracts g run)
    {x : Entry} (hx : x ∈ g.index) (hsx : Selected (g.filter x.path)) : Selectable x := by
  obtain ⟨hL, -, -⟩ := run.index.of_git hgit.index
  obtain ⟨sel, hsel0, hsel_none⟩ := run.selectable
  have hsel := spec_result (first_unselectable_spec hL run.flags (by
    rw [Slice.length, hook_flags hgit, List.length_map])) hsel0
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  exact hsel.2.1 k _ (by rw [hsel_none]; exact hk) (List.getElem?_eq_getElem hk)
    (hook_flag_of_selected hgit hk hsx)

/-- Membership in `HEAD` and `HEAD^1`: exactly the entry's record
    (`held_records`), and for `HEAD^1` only of protected entries. -/
theorem hook_membership {E : Type} {g : GitState} {run : HookEvidence g E} (hgit : HookContracts g run)
    {k : Nat} (hk : k < g.index.length) :
    (run.inHead.val[k]! = true ↔ g.index[k] ∈ g.head) ∧ run.inHead.length = g.index.length ∧
      (run.inParent.val[k]! = true ↔ run.flags.val[k]! = true ∧ g.index[k] ∈ g.parent) ∧
      run.inParent.length = g.index.length := by
  obtain ⟨hL, -, -⟩ := run.index.of_git hgit.index
  obtain ⟨hH, hHs, -⟩ := run.head.of_git hgit.head
  obtain ⟨hP, hPs, -⟩ := run.parent.of_git hgit.parent
  have hinH := spec_result (held_records_spec hL hH hHs run.all run.inHead0 (by
    rw [Slice.length, run.all_true, List.length_replicate]) run.inHead0_len) run.in_head
  have hinP := spec_result (held_records_spec hL hP hPs run.flags run.inParent0 (by
    rw [Slice.length, hook_flags hgit, List.length_map]) run.inParent0_len) run.in_parent
  have hall : run.all.val[k]! = true := by
    rw [run.all_true, getElem!_pos _ k (by simp; omega)]; simp
  refine ⟨?_, hinH.2.1, hinP.2.2 k _ hk (List.getElem?_eq_getElem hk), hinP.2.1⟩
  rw [hinH.2.2 k _ hk (List.getElem?_eq_getElem hk)]
  simp [hall]

/-- **What the check of one entry establishes.** For the entry `x` at a
    checked position: if it is selected, its blob passes the keyed check with
    the key and the keyless check without it; and with the key, if it is a
    regular, non-reserved file, its record authenticates where it has this
    configuration's envelope, or the incremental hook trusted it from `HEAD`
    under the guard (`HEAD` holds exactly that record). -/
structure EntryChecked (σ : Suite) (config : List Nat) (keyed incremental guard : Bool) (g : GitState)
    (x : Entry) : Prop where
  selected : Selected (g.filter x.path) → ∃ content, g.blob x.oid = some content ∧
    (keyed = true → KeyedEntryOk σ config incremental g x content) ∧
    (keyed = false → KeylessEnvelopeOk σ config g x content)
  records : keyed = true → Selectable x →
    RecordAuthentic σ config g x ∨ (incremental = true ∧ guard = true ∧ x ∈ g.head)

/-- An accepted `opens` answer: the entry's blob authenticates at its path. -/
theorem hook_opens {E : Type} {inst : StagedEvidence E} {pinst : V3Primitives P} {prims : P}
    {config : Std.Array U8 55#usize} {id : Std.Array U8 16#usize} {g : GitState} {run : HookEvidence g E}
    {good : E → Prop} (hR : Realizes pinst prims σ) (hans : HookAnswersIn inst pinst prims config id g run good)
    {s : E} (hs : good s) {k : Usize} {x : Entry} (hx : g.index[k.val]? = some x)
    (ho : inst.opens s k = ok (some true)) :
    ∃ content, g.blob x.oid = some content ∧ AuthenticatedAt σ (wireBytes config) x content := by
  obtain ⟨path, record, buf, out, hpath, hobj, hop⟩ := spec_result (hans.opens s k x hs hx) ho rfl
  have hor := spec_result (open_record_spec hR config path record buf) hop
  rw [hpath] at hor
  exact ⟨_, hobj, _, hor⟩

/-- **One entry's check, end to end.** Under the hook's contracts, if the
    verified `index_verdict` accepted position `k` (`PositionAccepted`: its
    `staged_check` on the run's inputs and its `staged_verdict`), the index
    entry at `k` is `EntryChecked`. -/
theorem hook_entry_checked {E : Type} {inst : StagedEvidence E} {pinst : V3Primitives P} {prims : P}
    {config : Std.Array U8 55#usize} {id : Std.Array U8 16#usize} {g : GitState} {run : HookEvidence g E}
    {keyed incremental : Bool} {good : E → Prop}
    (hR : Realizes pinst prims σ) (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hgit : HookContracts g run) (hans : HookAnswersIn inst pinst prims config id g run good)
    {k : Usize} {x : Entry} (hx : g.index[k.val]? = some x)
    (hacc : PositionAccepted inst good run.index.bytes run.index.ends run.flags run.inHead run.inParent keyed
      incremental run.samePolicy id k) :
    EntryChecked σ (wireBytes config) keyed incremental run.samePolicy g x := by
  obtain ⟨hL, hLs, hIo⟩ := run.index.of_git hgit.index
  obtain ⟨hH, hHs, hHo⟩ := run.head.of_git hgit.head
  obtain ⟨hP, hPs, hPo⟩ := run.parent.of_git hgit.parent
  have hk : k.val < g.index.length := (List.getElem?_eq_some_iff.mp hx).1
  have hxk : g.index[k.val] = x := (List.getElem?_eq_some_iff.mp hx).2
  obtain ⟨hmH, hHl, hmP, hPl⟩ := hook_membership hgit hk
  rw [hxk] at hmH hmP
  have hfx := hook_flag hgit hk
  rw [hxk] at hfx
  obtain ⟨s, check, record, hs, hc, hrd, hb, hv⟩ := hacc
  have hcheck := spec_result (staged_check_spec hL k hk run.flags run.inHead run.inParent
    (by rw [Slice.length, hook_flags hgit, List.length_map]) hHl hPl keyed incremental run.samePolicy) hc
  rw [hxk] at hcheck
  have hverdict := staged_verdict_ok inst s k check record id hv
  -- The blob of a protected entry was read for it: its object's content.
  have hblob : run.flags.val[k.val]! = true → g.blob x.oid = some (sliceBytes record) := by
    intro hf
    obtain ⟨e, rfl⟩ := (stagedCheckOf_reads hcheck).mpr hf
    obtain ⟨s0, hs0, hr0⟩ := hrd rfl
    exact hans.read s0 k s x record hs0 hx hr0 hb
  -- A record `is_record` denied has no envelope.
  have hnot : inst.is_record s k = ok (some false) → RecordAuthentic σ (wireBytes config) g x := by
    intro hr
    obtain ⟨content, hc', hpre⟩ := spec_result (hans.is_record s k x hs hx) hr rfl
    refine ⟨content, hc', fun henv => absurd (hid ▸ henv) (not_envelope_of_prefix hpre)⟩
  rcases check with _ | _ | _ | c
  · -- Skip: unprotected, and trusted from `HEAD` if it is a regular, non-reserved file with the key.
    obtain ⟨hf, hs'⟩ := hcheck
    refine ⟨fun hsx => absurd (hfx.mpr hsx) (by rw [hf]; simp), fun hkey ⟨hreg, hnres⟩ => ?_⟩
    rcases hs' with hn | ⟨hin, hres | hkf | ⟨hi, hg⟩⟩
    · exact absurd hreg hn
    · exact absurd hres hnres
    · rw [hkey] at hkf; cases hkf
    · exact Or.inr ⟨hi, hg, hmH.mp hin⟩
  · -- NotRecord: unprotected, and no record of this configuration.
    obtain ⟨hf, -, -⟩ := hcheck
    exact ⟨fun hsx => absurd (hfx.mpr hsx) (by rw [hf]; simp), fun _ _ => Or.inl (hnot hverdict)⟩
  · -- AuthenticateIfRecord: unprotected, and a record of this configuration opens.
    obtain ⟨hf, -⟩ := hcheck
    refine ⟨fun hsx => absurd (hfx.mpr hsx) (by rw [hf]; simp), fun _ _ => Or.inl ?_⟩
    rcases hverdict with hr | ho
    · exact hnot hr
    · obtain ⟨content, hc', hat⟩ := hook_opens hR hans hs hx ho
      exact ⟨content, hc', fun _ => hat⟩
  · -- Protected: checked as `entry_check` decided.
    obtain ⟨hf, hauth, henvc⟩ := hcheck
    have hb' := hblob hf
    rcases c with _ | _ | _
    · -- Authenticate: with the key, and the blob opens.
      have hk' := hauth.mp rfl
      obtain ⟨content, hc', hat⟩ := hook_opens hR hans hs hx hverdict
      rw [hb', Option.some.injEq] at hc'
      subst hc'
      refine ⟨fun _ => ⟨_, hb', fun _ => Or.inl hat, fun hkf => ?_⟩, fun _ _ => Or.inl ⟨_, hb', fun _ => hat⟩⟩
      rw [hkf] at hk'; exact absurd hk'.1 (by simp)
    · -- Envelope: settled, so `HEAD` and `HEAD^1` hold the record.
      obtain ⟨hk', hs'⟩ := henvc.mp rfl
      simp only [Bool.and_eq_true] at hs'
      obtain ⟨⟨hg, hin⟩, hip⟩ := hs'
      have hxh := hmH.mp hin
      have hxp := (hmP.mp hip).2
      have hset : Settled g.head g.parent x := ⟨⟨x, hxh, rfl, rfl⟩, ⟨x, hxp, rfl, rfl⟩⟩
      have henv : EnvelopeOk (sliceBytes record) (σ.digest16 (wireBytes config)) := hid ▸ hverdict
      have hinc : keyed = true → incremental = true := fun hkey => by
        by_contra hni
        exact hk' ⟨hkey, fun h => hni h.1⟩
      refine ⟨fun _ => ⟨_, hb', fun hkey => Or.inr ⟨hinc hkey, hset, henv⟩, fun _ => ⟨henv, Or.inl hset⟩⟩,
        fun hkey _ => Or.inr ⟨hinc hkey, hg, hxh⟩⟩
    · -- EnvelopeNotMoved: without the key, the envelope, and not another path's blob.
      have hnk : ¬ (keyed = true ∧ ¬ (incremental = true ∧
          (run.samePolicy && run.inHead.val[k.val]! && run.inParent.val[k.val]!) = true)) :=
        fun h => by simpa using hauth.mpr h
      have hns : ¬ (run.samePolicy && run.inHead.val[k.val]! && run.inParent.val[k.val]!) = true :=
        fun h => by simpa using henvc.mpr ⟨hnk, h⟩
      have hkf : keyed = false := by
        cases hkey : keyed
        · rfl
        · exact absurd ⟨hkey, fun h => hns h.2⟩ hnk
      obtain ⟨henv, hel⟩ := hverdict
      have hbe0 : blob_elsewhere run.index.bytes run.index.ends run.index.order k run.head.bytes
          run.head.ends run.head.order run.parent.bytes run.parent.ends run.parent.order = ok false :=
        spec_result (hans.elsewhere s k hs) hel false rfl
      have hbe := spec_result (blob_elsewhere_spec hL hLs hIo hH hHs hHo hP hPs hPo k hk) hbe0
      rw [hxk] at hbe
      refine ⟨fun _ => ⟨_, hb', fun hkey => absurd (hkf ▸ hkey) (by simp), fun _ =>
        ⟨hid ▸ henv, Or.inr (fun hb'' => absurd (hbe.mpr hb'') (by simp))⟩⟩,
        fun hkey => absurd (hkf ▸ hkey) (by simp)⟩

/-- Every entry of an accepted run is `EntryChecked`: the verified
    `index_verdict` checked every position (`index_verdict_accepts`), so
    each index entry's own check passed. -/
theorem hook_checked {E : Type} {inst : StagedEvidence E} {pinst : V3Primitives P} {prims : P}
    {config : Std.Array U8 55#usize} {id : Std.Array U8 16#usize} {g : GitState} {run : HookEvidence g E}
    {keyed incremental : Bool}
    (hR : Realizes pinst prims σ) (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hgit : HookContracts g run) (hans : HookAnswers inst pinst prims config id g run)
    (hcheck : HookAccepted inst id keyed incremental run)
    {x : Entry} (hx : x ∈ g.index) :
    EntryChecked σ (wireBytes config) keyed incremental run.samePolicy g x := by
  obtain ⟨good, hans⟩ := hans
  obtain ⟨s', hv⟩ := hcheck
  obtain ⟨hL, -, -⟩ := run.index.of_git hgit.index
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hx
  have hpe : p < run.index.ends.length := by rw [Slice.length, hL.ends_length]; exact hp
  have hpk : p < 2 ^ UScalarTy.Usize.numBits := by
    have := run.index.ends.property; scalar_tac
  exact hook_entry_checked hR hid hgit hans (k := Usize.ofNatCore p hpk) (by simp [Usize.ofNatCore])
    (index_verdict_accepts good hans.read_good hans.start hv _ (by simpa [Usize.ofNatCore] using hpe))

/-! ## End to end -/

/-- **End-to-end security of the pre-commit hook.** Assume the Git contracts:
    Git reports the index, `HEAD` and `HEAD^1` exactly (A20) and the
    committed attributes' `filter` values (A19); every blob the hook read is
    the content of its entry's object id and the adapter's answers mean what
    they say (`HookAnswers`, A4, A11, A21); the primitives realize the suite
    `σ` (A5), whose digest gives the configuration id (A5); and the
    configuration is the one committed as `.transcrypt/config` (checked by
    the adapter, A4). If the hook's final check accepted (`HookEvidence`,
    `HookAccepted`: the verified `index_verdict` returned `Ok`), then the
    index Git commits (A22) is an `AcceptedIndex`: every
    entry that the committed attributes select is a regular, non-reserved
    file whose blob

    * with the key, authenticates at exactly its own path under the
      committed configuration — or, in the incremental hook, is unchanged
      since `HEAD` and `HEAD^1` and has the v3 envelope of that
      configuration (checked when it was committed, and by the audit)
      (`KeyedEntryOk`);
    * without the key, has that envelope (A14: keyless checks cannot detect
      a forgery) and is unchanged since `HEAD` and `HEAD^1` or is not a blob
      of another path (no record moved without the key)
      (`KeylessEnvelopeOk`).

    The three snapshots are sorted (`SnapshotsSorted`: each path once, as
    Git lists them; the parse refuses a crafted tree that repeats a path), so
    "unchanged since `HEAD`" names the one entry `HEAD` has at that path.
    With A24 the settled case authenticates too
    (`hook_accepts_only_authenticated_ciphertext_given_history`,
    `hook_records_authentic`). -/
theorem hook_accepts_only_authenticated_ciphertext {E : Type} (g : GitState) (run : HookEvidence g E)
    (inst : StagedEvidence E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (keyed incremental : Bool)
    (hR : Realizes pinst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hgit : HookContracts g run)
    (hans : HookAnswers inst pinst prims config id g run)
    (hcfg : ConfigCommitted g (wireBytes config))
    (hcheck : HookAccepted inst id keyed incremental run) :
    ConfigCommitted g (wireBytes config) ∧ SnapshotsSorted g ∧
      AcceptedIndex σ (wireBytes config) keyed incremental g := by
  refine ⟨hcfg, hook_snapshots_sorted hgit, fun x hx hsx => ⟨hook_selectable hgit hx hsx, ?_⟩⟩
  exact (hook_checked hR hid hgit hans hcheck hx).selected hsx

/-! ## Settled entries and the checked history -/

/-- **A24 (checked history), by selection.** Every entry of `HEAD` whose
    path the committed attributes select is a record that authenticates at
    its path under the committed configuration. It holds when `HEAD` was
    accepted by this hook or by the keyed audit under the same attributes
    (local attribute files included) and configuration. -/
def HeadAuthentic (σ : Suite) (config : List Nat) (g : GitState) : Prop :=
  ∀ y ∈ g.head, Selected (g.filter y.path) →
    ∃ content, g.blob y.oid = some content ∧ AuthenticatedAt σ config y content

/-- **With the key and a checked history, every selected entry
    authenticates.** Under the hypotheses of
    `hook_accepts_only_authenticated_ciphertext` and `HeadAuthentic`, an
    accepted commit made with the key, incremental or not, stores at every
    path the committed attributes select a record that authenticates at that
    path (`AuthenticatedIndex`). -/
theorem hook_accepts_only_authenticated_ciphertext_given_history {E : Type} (g : GitState)
    (run : HookEvidence g E) (inst : StagedEvidence E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (incremental : Bool)
    (hR : Realizes pinst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hgit : HookContracts g run)
    (hans : HookAnswers inst pinst prims config id g run)
    (hcfg : ConfigCommitted g (wireBytes config))
    (hcheck : HookAccepted inst id true incremental run)
    (hhist : HeadAuthentic σ (wireBytes config) g) :
    AuthenticatedIndex σ (wireBytes config) g := by
  obtain ⟨-, -, h⟩ := hook_accepts_only_authenticated_ciphertext g run inst pinst prims config id true
    incremental hR hid hgit hans hcfg hcheck
  intro x hx hsx
  obtain ⟨hsel, content, hc, hk, -⟩ := h x hx hsx
  refine ⟨hsel, content, hc, ?_⟩
  rcases hk rfl with hop | ⟨-, ⟨⟨y, hy, hyo, hyp⟩, -⟩, -⟩
  · exact hop
  · -- Settled: `HEAD` holds the same blob at the same path, and A24 says it authenticates.
    obtain ⟨c', hc', pt, hpt⟩ := hhist y hy (hyp ▸ hsx)
    rw [hyo, hc, Option.some.injEq] at hc'
    subst hc'
    rw [hyp] at hpt
    exact ⟨pt, hpt⟩

/-- **The record invariant, one run.** A keyed check that accepted makes the
    index's records authenticate (`RecordsAuthentic`), whatever selects the
    paths, given that `HEAD`'s do under this configuration when the run
    trusted `HEAD` (incremental, with the guard `true`): an entry staged
    since `HEAD` was authenticated or is no record of this configuration,
    and one `HEAD` holds was authenticated if it is a record, or trusted
    from `HEAD`'s exactly equal record. -/
theorem hook_records_authentic {E : Type} (g : GitState) (run : HookEvidence g E)
    (inst : StagedEvidence E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (incremental : Bool)
    (hR : Realizes pinst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hgit : HookContracts g run)
    (hans : HookAnswers inst pinst prims config id g run)
    (hcheck : HookAccepted inst id true incremental run)
    (hhead : incremental = true → run.samePolicy = true → RecordsAuthentic σ (wireBytes config) g g.head) :
    RecordsAuthentic σ (wireBytes config) g g.index := by
  intro x hx hsel
  rcases (hook_checked hR hid hgit hans hcheck hx).records rfl hsel with h | ⟨hi, hg, hxh⟩
  · exact h
  · exact hhead hi hg x hxh hsel

/-- **Authenticated records authenticate the selection.** In a keyed check
    that accepted, every selected entry has this configuration's envelope;
    so where the index's records authenticate, every selected entry
    authenticates (`AuthenticatedIndex`). -/
theorem hook_authenticated_of_records {E : Type} (g : GitState) (run : HookEvidence g E)
    (inst : StagedEvidence E) (pinst : V3Primitives P) (prims : P)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (incremental : Bool)
    (hR : Realizes pinst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hgit : HookContracts g run)
    (hans : HookAnswers inst pinst prims config id g run)
    (hcheck : HookAccepted inst id true incremental run)
    (hrec : RecordsAuthentic σ (wireBytes config) g g.index) :
    AuthenticatedIndex σ (wireBytes config) g := by
  intro x hx hsx
  have hsel := hook_selectable hgit hx hsx
  obtain ⟨content, hc, hk, -⟩ := (hook_checked hR hid hgit hans hcheck hx).selected hsx
  refine ⟨hsel, content, hc, ?_⟩
  rcases hk rfl with hat | ⟨-, -, henv⟩
  · exact hat
  · obtain ⟨c', hc', hra⟩ := hrec x hx hsel
    rw [hc, Option.some.injEq] at hc'
    subst hc'
    exact hra henv

/-! ## The settled guard -/

/-- **The settled guard, end to end.** When the run's verified
    `policy_unchanged` returned `true`, Git's index, `HEAD` and `HEAD^1` have
    the same policy entries: every attribute file and the configuration, with
    mode and object id (`PolicyUnchanged`; A20 for the listings). -/
theorem hook_policy_guard {E : Type} {g : GitState} {run : HookEvidence g E} (hgit : HookContracts g run)
    (h : run.samePolicy = true) : PolicyUnchanged g.index g.head g.parent := by
  obtain ⟨hL, -, -⟩ := run.index.of_git hgit.index
  obtain ⟨hH, -, -⟩ := run.head.of_git hgit.head
  obtain ⟨hP, -, -⟩ := run.parent.of_git hgit.parent
  exact (policy_unchanged_sound hL hH hP (by rw [run.policy, h])).1

/-! ## The key the hook uses -/

/-- **Stored-key unlock.** `Key::load` uses a stored key only when the
    verified `stored_key_state` says `Unlocked`, with `authentic` computed by
    the verified `authenticate_config` under the primitives built from the
    stored key bytes (A17: `unlock_stored_key` takes them from
    `file[CONFIG_LEN..KEY_CHECK_START]`). Then the file holds exactly the
    current configuration and the key authenticates it (`ConfigAuthentic`, relative to `Realizes`, A5). -/
theorem stored_key_authenticates_current_config (hR : Realizes inst prims σ)
    (present : Bool) (file current : Slice U8) (config : Std.Array U8 55#usize)
    (hcur : sliceBytes current = wireBytes config) (authentic : Bool)
    (hauth : authentic = true → ∃ c, authenticate_config inst prims config = ok (core.result.Result.Ok c))
    (hstate : stored_key_state present file current authentic = ok transcrypt_v3_core.StoredKey.Unlocked) :
    present = true ∧ (sliceBytes file).length = keyFileLen ∧
      (sliceBytes file).take Transcrypt.V3Wire.configLen = wireBytes config ∧
      ConfigAuthentic σ (wireBytes config) := by
  have hs := spec_result (stored_key_state_spec present file current authentic) hstate
  have hu : storedKeySpec present (sliceBytes file) (sliceBytes current) authentic = .unlocked := by
    cases h : storedKeySpec present (sliceBytes file) (sliceBytes current) authentic <;>
      rw [h] at hs <;> simp [storedKeyResult] at hs ⊢
  obtain ⟨hp, hl, ht, ha⟩ := storedKeySpec_unlocked hu
  obtain ⟨c, hc⟩ := hauth ha
  have := spec_result (authenticate_config_spec hR config) hc
  exact ⟨hp, hl, ht.trans hcur, this.1⟩

/-! ## The hook's repairs: no laundering

The hook decides each protected entry's repair in the verified core, from
two typed facts: where its content came from (`entry_provenance`, from the
snapshots) and what its blob is (`RecordClass`, which the adapter finds with
the key). `needs_record` decides whether the blob is read at all, and
`repair_plan` decides the repair. The adapter gathers the evidence and
executes the plan (A4); `RepairContracts` states what its evidence is. -/

/-- What the adapter computed for one protected index entry in
    `seal_snapshot` and `classify`: the snapshots it parsed, the entry, the
    evidence it gathered and the results of the verified core it acts on.
    `RepairContracts` says what these values are. -/
structure RepairInputs where
  /-- The index and `HEAD`, each path once. -/
  index : ParsedListing true
  head : ParsedListing true
  /-- The protected flags and `HEAD` membership (`held_entries`), from
      which the adapter decides whether to list the incoming commits. -/
  flags : Slice Bool
  inHead0 : Slice Bool
  inHead : Slice Bool
  /-- The commits being brought in, as one listing, and whether they are
      known (`known`; when not, the adapter passes an empty listing, which
      the core does not read). -/
  incomingBytes : Slice U8
  incomingEnds : Slice Usize
  known : Bool
  /-- The entry, and whether `protect` forced it. -/
  i : Usize
  forced : Bool
  /-- Its provenance (`entry_provenance`). -/
  prov : transcrypt_v3_core.Provenance
  /-- Its path and blob, the configuration, and what the blob is. -/
  config : Std.Array U8 55#usize
  path : Slice U8
  record : Slice U8
  openBuf : Slice U8
  cls : transcrypt_v3_core.RecordClass
  /-- The decision (`repair_plan`). -/
  plan : transcrypt_v3_core.RepairPlan

/-- The staged blob does not open at the entry's own path. -/
def NotOpensHere (inst : V3Primitives P) (prims : P) (run : RepairInputs) : Prop :=
  ∀ r pt, open_record inst prims run.config run.path run.record run.openBuf = ok (r, pt) →
    r ≠ core.result.Result.Ok ()

/-- The staged blob has the v3 file header (`parse_file_header`). -/
def HasHeader (record : Slice U8) : Prop :=
  ∃ id, parse_file_header record = ok (core.result.Result.Ok id)

/-- The staged blob has no v3 file header. -/
def NoHeader (record : Slice U8) : Prop :=
  ∃ e, parse_file_header record = ok (core.result.Result.Err e)

/-- The staged blob opens at the path of record `j` of `HEAD`, which the
    verified `next_move_source` found over a checked object order of
    `HEAD`, from some offset: a place the entry may have been moved from. -/
def MovedFromAt (inst : V3Primitives P) (prims : P) (g : GitState) (run : RepairInputs) (j : Usize) : Prop :=
  ∃ (horder : Slice Usize) (from_ : Usize) (src buf pt : Slice U8),
    from_.val ≤ g.head.length ∧ object_order_ok run.head.bytes run.head.ends horder = ok true ∧
    next_move_source run.index.bytes run.index.ends run.i run.head.bytes run.head.ends horder from_ = ok j ∧
    j.val < g.head.length ∧ sliceBytes src = (g.head[j.val]?).elim [] (·.path) ∧
    open_record inst prims run.config src run.record buf = ok (core.result.Result.Ok (), pt)

/-- What each `RecordClass` the adapter reports means: it tried the key at
    the entry's path first, then read the header, then tried the move
    sources in order (`classify`). -/
def RecordEvidence (inst : V3Primitives P) (prims : P) (g : GitState) (run : RepairInputs) :
    transcrypt_v3_core.RecordClass → Prop
  | .OpensHere => ∃ pt, open_record inst prims run.config run.path run.record run.openBuf =
      ok (core.result.Result.Ok (), pt)
  | .Plaintext => NotOpensHere inst prims run ∧ NoHeader run.record
  | .MovedFrom j => NotOpensHere inst prims run ∧ HasHeader run.record ∧ MovedFromAt inst prims g run j
  | .Unusable => NotOpensHere inst prims run ∧ HasHeader run.record

/-- What the provenance of a `RepairInputs` is computed from: Git's
    snapshots (A20) and sequencing state (A23), and the verified core on
    them (A4). -/
structure ProvenanceContracts (g : GitState) (run : RepairInputs) : Prop where
  /-- **A20.** Git's index and `HEAD`, listed exactly. -/
  index : GitListing run.index.bytes g.index
  head : GitListing run.head.bytes g.head
  /-- A protected entry of the index. -/
  entry : run.i.val < g.index.length
  flags_len : run.flags.length = g.index.length
  protected_ : run.flags.val[run.i.val]! = true
  /-- `HEAD` membership (`held_entries`). -/
  inHead0_len : run.inHead0.length = g.index.length
  in_head : held_entries run.index.bytes run.index.ends run.flags run.head.bytes run.head.ends run.inHead0 =
    ok (true, run.inHead)
  /-- **A20, A23.** When `known`, the incoming commits the sequencing state
      names, listed exactly; otherwise they are not consulted, which
      happens only when there are none or `HEAD` holds the entry. -/
  incoming : run.known = true → ∃ m, ∃ l : ParsedListing false, g.incoming = some m ∧
    GitListing l.bytes m ∧ l.bytes = run.incomingBytes ∧ l.ends = run.incomingEnds
  lazy : run.known = false → g.incoming = none ∨ run.inHead.val[run.i.val]! = true
  /-- The provenance (`entry_provenance`). -/
  provenance : entry_provenance run.index.bytes run.index.ends run.i run.head.bytes run.head.ends
    run.incomingBytes run.incomingEnds run.known run.forced = ok run.prov

/-- `ProvenanceContracts`, and the evidence about the blob and the decision
    (A4): what the blob is, and `repair_plan` on the two. -/
structure RepairContracts (inst : V3Primitives P) (prims : P) (g : GitState) (run : RepairInputs) : Prop
    extends ProvenanceContracts g run where
  /-- What the blob is (`RecordEvidence`). -/
  record : RecordEvidence inst prims g run run.cls
  /-- The decision (`repair_plan`). -/
  decision : repair_plan run.prov run.cls = ok run.plan

/-- **Provenance, end to end.** The provenance the hook computed is where
    the entry's content came from, by Git's index, `HEAD` and the commits
    being brought in (`ProvenanceIs`), even when the hook did not list
    those commits. -/
theorem hook_provenance {g : GitState} {run : RepairInputs} (hc : ProvenanceContracts g run) :
    ProvenanceIs g.head g.incoming run.forced (g.index[run.i.val]'hc.entry) (provenanceSpecOf run.prov) := by
  obtain ⟨hL, hLs⟩ := run.index.of_git hc.index
  obtain ⟨hH, hHs⟩ := run.head.of_git hc.head
  have hi := hc.entry
  cases hk : run.known
  · -- Not listed: the core computed the provenance without incoming commits.
    have hp := spec_result (entry_provenance_spec (ms := none) hL hH hHs.pathOrdered (fun m hm => by cases hm)
      run.i hi run.forced) (by have := hc.provenance; rw [hk] at this; exact this)
    rcases hc.lazy hk with hn | hin
    · rw [hn]; exact hp
    · have hheld := spec_result (held_entries_spec hL hH hHs.pathOrdered run.flags run.inHead0 hc.flags_len
        hc.inHead0_len) hc.in_head
      have hh : Holds g.head g.index[run.i.val].oid g.index[run.i.val].path := by
        have := (hheld.2.2 run.i.val _ hi (List.getElem?_eq_getElem hi)).mp hin
        exact this.2
      exact (provenanceIs_held hh).mp hp
  · obtain ⟨m, l, hm, hgm, hb, he⟩ := hc.incoming hk
    obtain ⟨hM, hMo⟩ := l.of_git_merged hgm
    rw [hb, he] at hM
    have hp := spec_result (entry_provenance_spec (ms := some m) hL hH hHs.pathOrdered
      (fun m' hm' => by cases hm'; exact ⟨hM, hMo⟩) run.i hi run.forced)
      (by have := hc.provenance; rw [hk] at this; exact this)
    rw [hm]; exact hp

/-- **The hook skips only what it may not repair.** If `needs_record` tells
    the hook not to read an entry's blob, the entry is not the user's change
    and `protect` did not force it: no repair is missed. -/
theorem hook_skips_only_unrepairable (g : GitState) (run : RepairInputs) (hc : ProvenanceContracts g run)
    (hskip : needs_record run.prov = ok false) :
    ¬ UserStaged g.head g.incoming (g.index[run.i.val]'hc.entry) ∧ run.forced = false := by
  have hp := hook_provenance hc
  have hn := spec_result (needs_record_spec run.prov) hskip
  cases hq : run.prov <;> rw [hq] at hp hn <;>
    simp [provenanceSpecOf, Transcrypt.V3Policy.needsRecordSpec, Transcrypt.V3Policy.Repairable,
      ProvenanceIs] at hp hn
  · obtain ⟨hf, hh⟩ := hp
    exact ⟨fun hu => hu.not_committed hh, hf⟩
  · obtain ⟨hf, hh, hi⟩ := hp
    refine ⟨fun hu => ?_, hf⟩
    obtain ⟨-, m, hm, -⟩ := hu
    rw [hi] at hm
    cases hm

/-- **The pre-commit hook repairs only local changes.** For a protected
    entry `x` of Git's index (A20), with `HEAD` and the commits being brought
    in parsed exactly (A20, A23: the sequencing state names those commits),
    suppose the hook computed the entry's provenance with the verified
    `entry_provenance`, classified its blob as the adapter's evidence shows
    (`RecordEvidence`), and `repair_plan` decided to seal or re-seal it
    (`RepairContracts`). Then

    * the provenance is exactly where `x`'s content came from
      (`ProvenanceIs`), and `x` is the user's change (`UserStaged`: never
      content of `HEAD` or of an incoming commit), unless `protect` forced
      it and it is sealed;
    * it is a local change in the sense of the local-change test
      (`LocalChange`, with the envelope as the header parse reports it);
    * the blob did not already open at its path;
    * a seal seals only plaintext (no v3 header);
    * a rebind from `HEAD` record `j` re-encrypts the plaintext of a record
      with the header, of the user's change, that authenticates at the path
      of exactly that record of `HEAD`, a place it was moved from
      (`MoveSource`). -/
theorem hook_repairs_only_local_changes (g : GitState) (run : RepairInputs)
    (hR : Realizes inst prims σ) (hc : RepairContracts inst prims g run)
    (hrepair : run.plan = transcrypt_v3_core.RepairPlan.Seal ∨
      ∃ j, run.plan = transcrypt_v3_core.RepairPlan.Rebind j) :
    ProvenanceIs g.head g.incoming run.forced (g.index[run.i.val]'hc.entry) (provenanceSpecOf run.prov) ∧
      (UserStaged g.head g.incoming (g.index[run.i.val]'hc.entry) ∨
        (run.forced = true ∧ run.plan = transcrypt_v3_core.RepairPlan.Seal)) ∧
      (∀ envelope : Bool, (envelope = true ↔ HasHeader run.record) →
        LocalChange g.head g.incoming run.forced envelope (g.index[run.i.val]'hc.entry)) ∧
      NotOpensHere inst prims run ∧
      (run.plan = transcrypt_v3_core.RepairPlan.Seal →
        ∀ r, parse_file_header run.record = ok r → ∀ x, r ≠ core.result.Result.Ok x) ∧
      (∀ j, run.plan = transcrypt_v3_core.RepairPlan.Rebind j →
        UserStaged g.head g.incoming (g.index[run.i.val]'hc.entry) ∧ HasHeader run.record ∧
        ∃ h, g.head[j.val]? = some h ∧ MoveSource g.index (g.index[run.i.val]'hc.entry) h ∧
          ∃ pt, OpensTo σ (wireBytes run.config) h.path (sliceBytes run.record) pt) := by
  have hprov := hook_provenance hc.toProvenanceContracts
  have hdec := repair_plan_repairs_only_local hc.decision
  -- The two repairs, with what the decision says about their inputs.
  have hcases : (run.plan = .Seal ∧ run.cls = .Plaintext ∧
        (run.prov = .Local ∨ run.prov = .Forced)) ∨
      (∃ j, run.plan = .Rebind j ∧ run.cls = .MovedFrom j ∧ run.prov = .Local) := by
    rcases hrepair with h | ⟨j, h⟩
    · exact Or.inl ⟨h, hdec.1 h⟩
    · exact Or.inr ⟨j, h, hdec.2 j h⟩
  -- The blob's evidence.
  have hnot : NotOpensHere inst prims run := by
    have hrec := hc.record
    rcases hcases with ⟨-, hcl, -⟩ | ⟨j, -, hcl, -⟩ <;> rw [hcl] at hrec
    · exact hrec.1
    · exact hrec.1
  -- Seal and rebind are of the user's change, or of forced plaintext.
  have huser : run.prov = .Local → UserStaged g.head g.incoming (g.index[run.i.val]'hc.entry) := by
    intro hl; rw [hl] at hprov; exact hprov
  -- The header, as the evidence gives it.
  have hdet : ∀ {r r' : core.result.Result (Std.Array U8 16#usize) FormatError},
      parse_file_header run.record = ok r → parse_file_header run.record = ok r' → r = r' := by
    intro r r' h h'; rw [h] at h'; cases h'; rfl
  refine ⟨hprov, ?_, ?_, hnot, ?_, ?_⟩
  · rcases hcases with ⟨hs, -, hl | hf⟩ | ⟨j, -, -, hl⟩
    · exact Or.inl (huser hl)
    · rw [hf] at hprov
      exact Or.inr ⟨hprov.2, hs⟩
    · exact Or.inl (huser hl)
  · intro envelope henv
    rcases hcases with ⟨-, hcl, hl | hf⟩ | ⟨j, -, -, hl⟩
    · exact Or.inl (huser hl)
    · rw [hf] at hprov
      refine Or.inr ⟨hprov.2, ?_⟩
      have hrec := hc.record
      rw [hcl] at hrec
      obtain ⟨e, he⟩ := hrec.2
      cases envelope
      · rfl
      · obtain ⟨id, hid⟩ := henv.mp rfl
        cases hdet he hid
    · exact Or.inl (huser hl)
  · intro hs r hr v hv
    rcases hcases with ⟨-, hcl, -⟩ | ⟨j, hj, -, -⟩
    · have hrec := hc.record
      rw [hcl] at hrec
      obtain ⟨e, he⟩ := hrec.2
      subst hv
      cases hdet hr he
    · rw [hj] at hs; cases hs
  · intro j hj
    rcases hcases with ⟨hs, -, -⟩ | ⟨j', hj', hcl, hl⟩
    · rw [hj] at hs; cases hs
    · rw [hj] at hj'
      cases hj'
      have hrec := hc.record
      rw [hcl] at hrec
      obtain ⟨-, hhead, hmoved⟩ := hrec
      refine ⟨huser hl, hhead, ?_⟩
      obtain ⟨hL, hLs⟩ := run.index.of_git hc.index
      obtain ⟨hH, hHs⟩ := run.head.of_git hc.head
      obtain ⟨horder, from_, src, buf, pt, hfrom, hord, hnext, hjl, hsrc, hopen⟩ := hmoved
      have hHo := (spec_result (object_order_ok_spec hH horder) hord).mp rfl
      have hfirst := spec_result (next_move_source_spec hL hLs.pathOrdered hH hHo run.i hc.entry from_ hfrom) hnext
      obtain ⟨h, hhj, hms⟩ := hfirst.found hjl
      have hor := spec_result (open_record_spec hR run.config src run.record buf) hopen
      rw [hhj] at hsrc
      simp only [Option.elim] at hsrc
      rw [hsrc] at hor
      exact ⟨h, hhj, hms, _, hor⟩

end Transcrypt.V3Verification

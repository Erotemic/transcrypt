import V3Wire.Verification.Lifecycle
import V3Wire.Verification.Objects
import V3Wire.Verification.Snapshot

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
  `HookContracts`; the crypto primitives realize the abstract suite
  (`Realizes`, A5); Git commits the index the hook checked (A22, stated in
  prose: the conclusion is about `g.index`).
* **The run.** `HookEvidence` is what the adapter obtained from the
  verified core, in four groups: the parsed snapshots (`HookSnapshots`:
  three `OrderedListing`s, as the adapter's `OrderedListing`: parsed, each
  path once, with checked object orders), the attribute selection
  (`HookSelection`), the `HEAD`/`HEAD^1` membership (`HookMembership`), and
  the checked entries (`HookChecks`: each entry's fields, settled status
  and keyless move check), on which `hookPlan` (a model of the loop in
  `check_staged`, like `verifyPlan`) runs. The adapter acts only on these
  results (A4). For the repairs, `RepairInputs` are the values the adapter
  computed for one entry (its `Provenance` and its blob's `RecordClass`, on
  which the verified `repair_plan` decides) and `RepairContracts` what they
  are.

`hook_accepts_only_authenticated_ciphertext`: if the run accepted, the
index is an `AcceptedIndex`: every path the committed attributes select is
a regular, non-reserved entry (`AcceptedProtectedEntry`) whose blob, when
unlocked, authenticates at exactly that path under the committed
configuration (or, in the incremental hook, is unchanged since `HEAD` and
`HEAD^1` and has the v3 envelope; `KeyedEntryOk`); when locked, it has the
envelope of this configuration and is not a blob moved from another path
(`KeylessEnvelopeOk`). The proof goes through named steps: the snapshots
are sorted (`hook_snapshots_sorted`), the flags are Git's selection
(`hook_flags`), a selected entry is selectable (`hook_selectable`) and has a
check of its own blob at its own path (`hook_checks_selected`,
`ChecksEntry`), and an accepted check gives the conclusion
(`EntryAccepted.accepted`).
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
`hook_accepts_only_authenticated_ciphertext_given_history` adds A24 (the
history the incremental hook trusts was checked) and concludes that every
selected entry authenticates (`AuthenticatedIndex`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

variable {P : Type} {inst : V3Primitives P} {prims : P} {σ : Suite}

/-! ## The hook's check of each protected entry (model of `check_staged`) -/

/-- One protected index entry as the hook's final check sees it: its
    position, its path and blob (read by its object id), a plaintext buffer,
    whether it is unchanged since `HEAD` and `HEAD^1` (`held_entries`), and
    whether its blob is at another path (`blob_elsewhere`). -/
structure HookEntry where
  index : Usize
  path : Slice U8
  record : Slice U8
  buffer : Slice U8
  settled : Bool
  elsewhere : Bool

/-- The check `check_staged` makes of one protected entry, as the verified
    `entry_check` decides it: the blob must authenticate at the entry's path
    (`open_record`), or have this configuration's envelope
    (`record_envelope_ok`) and, for `EnvelopeNotMoved`, not be a blob of
    another path (a record moved without the key). The adapter also checks
    the header first; it accepts an entry only if this model does (A4). -/
def hookEntry (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) (keyed incremental : Bool) (e : HookEntry) : RustM Bool := do
  let check ← entry_check keyed incremental e.settled
  match check with
  | .Authenticate =>
    let (r, _) ← open_record inst prims config e.path e.record e.buffer
    match r with
    | core.result.Result.Ok _ => ok true
    | core.result.Result.Err _ => ok false
  | .Envelope =>
    let env ← record_envelope_ok e.record id
    ok env
  | .EnvelopeNotMoved =>
    let env ← record_envelope_ok e.record id
    ok (env && !e.elsewhere)

/-- The hook checks every protected entry; one refusal refuses the commit. -/
def hookPlan (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) (keyed incremental : Bool) : List HookEntry → RustM Bool
  | [] => ok true
  | e :: es => do
    let b ← hookEntry inst prims config id keyed incremental e
    if b then hookPlan inst prims config id keyed incremental es else ok false

/-- What an accepted entry is: with the key (unless settled in the
    incremental hook) a record authenticating at its path; otherwise a record
    with this configuration's envelope that, unless settled, is not another
    path's blob. -/
def EntryAccepted (σ : Suite) (config id : List Nat) (keyed incremental : Bool) (e : HookEntry) : Prop :=
  (keyed = true ∧ ¬ (incremental = true ∧ e.settled = true) →
    ∃ pt, OpensTo σ config (sliceBytes e.path) (sliceBytes e.record) pt) ∧
  (¬ (keyed = true ∧ ¬ (incremental = true ∧ e.settled = true)) →
    EnvelopeOk (sliceBytes e.record) id ∧ (e.settled = true ∨ e.elsewhere = false))

theorem EntryAccepted.of_opens {config id : List Nat} {keyed incremental : Bool} {e : HookEntry}
    (hk : keyed = true ∧ ¬ (incremental = true ∧ e.settled = true))
    (hop : ∃ pt, OpensTo σ config (sliceBytes e.path) (sliceBytes e.record) pt) :
    EntryAccepted σ config id keyed incremental e :=
  ⟨fun _ => hop, fun hn => absurd hk hn⟩

theorem EntryAccepted.of_envelope {config id : List Nat} {keyed incremental : Bool} {e : HookEntry}
    (hk : ¬ (keyed = true ∧ ¬ (incremental = true ∧ e.settled = true)))
    (henv : EnvelopeOk (sliceBytes e.record) id) (hs : e.settled = true ∨ e.elsewhere = false) :
    EntryAccepted σ config id keyed incremental e :=
  ⟨fun h' => absurd h' hk, fun _ => ⟨henv, hs⟩⟩

theorem hookEntry_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) (keyed incremental : Bool) (e : HookEntry) :
    hookEntry inst prims config id keyed incremental e ⦃ b =>
      b = true → EntryAccepted σ (wireBytes config) (wireBytes id) keyed incremental e ⦄ := by
  unfold hookEntry
  step with entry_check_spec keyed incremental e.settled as ⟨ c, hauth, henvc ⟩
  rcases c with _ | _ | _
  · have hk' := hauth.mp rfl
    step with open_record_spec h config e.path e.record e.buffer as ⟨ r, pt, hr ⟩
    rcases r with u | x
    · simp only at hr ⊢
      exact fun _ => EntryAccepted.of_opens hk' ⟨_, hr⟩
    · simp
  · obtain ⟨hk', hs⟩ := henvc.mp rfl
    step with record_envelope_ok_spec as ⟨ env, henv ⟩
    exact fun hb => EntryAccepted.of_envelope hk' (henv.mp hb) (Or.inl hs)
  · have hk' : ¬ (keyed = true ∧ ¬ (incremental = true ∧ e.settled = true)) := fun hk => by
      simpa using hauth.mpr hk
    step with record_envelope_ok_spec as ⟨ env, henv ⟩
    intro hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
    exact EntryAccepted.of_envelope hk' (henv.mp hb.1) (Or.inr hb.2)

theorem hookPlan_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) (keyed incremental : Bool) (es : List HookEntry) :
    hookPlan inst prims config id keyed incremental es ⦃ b =>
      b = true → ∀ e ∈ es, EntryAccepted σ (wireBytes config) (wireBytes id) keyed incremental e ⦄ := by
  induction es with
  | nil => simp [hookPlan]
  | cons e es ih =>
    unfold hookPlan
    step with hookEntry_spec h config id keyed incremental e as ⟨ b, hb ⟩
    split
    · rename_i hbt
      apply WP.spec_mono ih
      intro r hr hrt e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact hb hbt
      · exact hr hrt e' he'
    · simp

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

/-- Membership: in `HEAD` (every entry) and in `HEAD^1` (protected
    entries), by `held_entries`. -/
structure HookMembership (g : GitState) (index head parent : OrderedListing) (flags : Slice Bool) where
  all : Slice Bool
  inHead0 : Slice Bool
  inHead : Slice Bool
  inParent0 : Slice Bool
  inParent : Slice Bool
  all_true : all.val = List.replicate g.index.length true
  inHead0_len : inHead0.length = g.index.length
  in_head : held_entries index.bytes index.ends all head.bytes head.ends inHead0 = ok (true, inHead)
  inParent0_len : inParent0.length = g.index.length
  in_parent : held_entries index.bytes index.ends flags parent.bytes parent.ends inParent0 = ok (true, inParent)

/-- The checked entries: one check per protected entry, in index order,
    each at the entry's path field (`listing_fields`), settled only if
    `HEAD` and `HEAD^1` hold it (the adapter also requires unchanged
    attribute files and config), with the keyless move check
    (`blob_elsewhere`). -/
structure HookChecks (g : GitState) (index head parent : OrderedListing) (flags inHead inParent : Slice Bool) where
  entries : List HookEntry
  positions : entries.map (fun e => e.index.val) = (List.range g.index.length).filter (fun i => flags.val[i]!)
  fields : ∀ e ∈ entries, ∃ f, listing_fields index.bytes index.ends e.index = ok (core.option.Option.Some f) ∧
    sliceBytes e.path = (sliceBytes index.bytes).extract f.path_start.val f.end.val
  settled : ∀ e ∈ entries, e.settled = true → (inHead.val[e.index.val]! && inParent.val[e.index.val]!) = true
  elsewhere : ∀ e ∈ entries, blob_elsewhere index.bytes index.ends index.order e.index head.bytes head.ends
    head.order parent.bytes parent.ends parent.order = ok e.elsewhere

/-- What the adapter obtained from the verified core in the hook's final
    check (`check_staged`, after any sealing): it refuses the commit unless
    the results are as shown, and builds each protected entry's check from
    them (A4). The four groups are flattened: `run.flags`, `run.inHead`,
    `run.entries`, ... -/
structure HookEvidence (g : GitState) extends HookSnapshots, HookSelection g index,
    HookMembership g index head parent flags, HookChecks g index head parent flags inHead inParent

/-- **A20, A19, A11, A21.** The adapter contracts the hook relies on, for
    one run: Git reported the index, `HEAD` and `HEAD^1` exactly, and the
    committed attributes' `filter` values, and every blob checked is the
    content of its entry's object id. -/
structure HookContracts (g : GitState) (run : HookEvidence g) : Prop where
  index : GitListing run.index.bytes g.index
  head : GitListing run.head.bytes g.head
  parent : GitListing run.parent.bytes g.parent
  attributes : GitAttributes g run.response
  objects : ∀ e ∈ run.entries, ∃ x, g.index[e.index.val]? = some x ∧ GitObject g x.oid e.record

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

/-! ## The steps of the hook's final check -/

/-- The verified parses give exactly Git's snapshots, each path once. -/
theorem hook_snapshots_sorted {g : GitState} {run : HookEvidence g} (hgit : HookContracts g run) :
    SnapshotsSorted g :=
  ⟨(run.index.of_git hgit.index).2.1, (run.head.of_git hgit.head).2.1, (run.parent.of_git hgit.parent).2.1⟩

/-- The protected flags are Git's selection of each index entry. -/
theorem hook_flags {g : GitState} {run : HookEvidence g} (hgit : HookContracts g run) :
    run.flags.val = g.index.map (fun e => decide (Selected (g.filter e.path))) := by
  obtain ⟨hL, -, -⟩ := run.index.of_git hgit.index
  have hflags := (spec_result (parse_listing_attrs_spec hL run.response run.flags0) run.attrs).2
    (g.index.map (fun e => g.filter e.path)) ⟨by simp, by
      intro v hv; obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv; exact hgit.attributes.1 e he,
      run.flags0_len, hgit.attributes.2⟩
  rw [hflags.2, List.map_map]; rfl

/-- A selected entry is protected: its flag is set. -/
theorem hook_flag_of_selected {g : GitState} {run : HookEvidence g} (hgit : HookContracts g run)
    {k : Nat} (hk : k < g.index.length) (hsx : Selected (g.filter g.index[k].path)) :
    run.flags.val[k]! = true := by
  rw [hook_flags hgit, getElem!_pos _ k (by simp; omega)]; simp [hsx]

/-- `first_unselectable` found no protected entry that is not selectable. -/
theorem hook_selectable {g : GitState} {run : HookEvidence g} (hgit : HookContracts g run)
    {x : Entry} (hx : x ∈ g.index) (hsx : Selected (g.filter x.path)) : Selectable x := by
  obtain ⟨hL, -, -⟩ := run.index.of_git hgit.index
  obtain ⟨sel, hsel0, hsel_none⟩ := run.selectable
  have hsel := spec_result (first_unselectable_spec hL run.flags (by
    rw [Slice.length, hook_flags hgit, List.length_map])) hsel0
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  exact hsel.2.1 k _ (by rw [hsel_none]; exact hk) (List.getElem?_eq_getElem hk)
    (hook_flag_of_selected hgit hk hsx)

/-- The hook's check `e` is a check of the index entry `x`: of its blob, at
    its path, settled only if `x` is unchanged since `HEAD` and `HEAD^1`, and
    `elsewhere` exactly when its blob is at another path. -/
structure ChecksEntry (g : GitState) (x : Entry) (e : HookEntry) : Prop where
  blob : g.blob x.oid = some (sliceBytes e.record)
  path : sliceBytes e.path = x.path
  settled : e.settled = true → Settled g.head g.parent x
  elsewhere : e.elsewhere = true ↔ BlobElsewhere [g.index, g.head, g.parent] x

/-- Every selected index entry has a check among the hook's checks. -/
theorem hook_checks_selected {g : GitState} {run : HookEvidence g} (hgit : HookContracts g run)
    {x : Entry} (hx : x ∈ g.index) (hsx : Selected (g.filter x.path)) :
    ∃ e ∈ run.entries, ChecksEntry g x e := by
  obtain ⟨hL, hLs, hIo⟩ := run.index.of_git hgit.index
  obtain ⟨hH, hHs, hHo⟩ := run.head.of_git hgit.head
  obtain ⟨hP, hPs, hPo⟩ := run.parent.of_git hgit.parent
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hfk := hook_flag_of_selected hgit hk hsx
  -- The protected entry `k` has a check.
  have hmem : k ∈ run.entries.map (fun e => e.index.val) := by
    rw [run.positions]; exact List.mem_filter.mpr ⟨List.mem_range.mpr hk, hfk⟩
  obtain ⟨e, he, hek⟩ := List.mem_map.1 hmem
  refine ⟨e, he, ?_, ?_, ?_, ?_⟩
  -- Its blob is the entry's object (A11, A21).
  · obtain ⟨x', hx', hobj'⟩ := hgit.objects e he
    rw [hek, List.getElem?_eq_getElem hk, Option.some.injEq] at hx'
    subst hx'
    exact hobj'
  -- Its path is the entry's path.
  · obtain ⟨f, hf, hpath⟩ := run.fields e he
    have hfs := spec_result (listing_fields_spec hL e.index) hf
    obtain ⟨y, hy, -, -, hyp, -⟩ := FieldsOf.slices hL hfs.2
    rw [hek, List.getElem?_eq_getElem hk, Option.some.injEq] at hy
    subst hy
    rw [hyp] at hpath
    exact hpath
  -- Settled only if `HEAD` and `HEAD^1` hold it (`held_entries`).
  · intro hs
    have hinH := spec_result (held_entries_spec hL hH hHs.pathOrdered run.all run.inHead0 (by
      rw [Slice.length, run.all_true, List.length_replicate]) run.inHead0_len) run.in_head
    have hinP := spec_result (held_entries_spec hL hP hPs.pathOrdered run.flags run.inParent0 (by
      rw [Slice.length, hook_flags hgit, List.length_map]) run.inParent0_len) run.in_parent
    have hall : run.all.val[k]! = true := by
      rw [run.all_true, getElem!_pos _ k (by simp; omega)]; simp
    have := run.settled e he hs
    rw [hek, Bool.and_eq_true, hinH.2.2 k _ hk (List.getElem?_eq_getElem hk),
      hinP.2.2 k _ hk (List.getElem?_eq_getElem hk)] at this
    simp only [hall, hfk, true_and] at this
    exact this
  -- `elsewhere` is exactly `BlobElsewhere` (`blob_elsewhere`).
  · have := spec_result (blob_elsewhere_spec hL hLs hIo hH hHs hHo hP hPs hPo e.index (by omega))
      (run.elsewhere e he)
    simp only [hek] at this
    exact this

/-- A check that accepted a selected, selectable entry's blob makes it an
    `AcceptedProtectedEntry`. -/
theorem EntryAccepted.accepted {config : List Nat} {keyed incremental : Bool} {g : GitState}
    {x : Entry} {e : HookEntry} (hc : ChecksEntry g x e) (hsel : Selectable x)
    (hacc : EntryAccepted σ config (σ.digest16 config) keyed incremental e) :
    AcceptedProtectedEntry σ config keyed incremental g x := by
  refine ⟨hsel, _, hc.blob, fun hkey => ?_, fun hkey => ?_⟩
  · -- With the key: authenticated, unless settled in the incremental hook.
    by_cases hs : incremental = true ∧ e.settled = true
    · exact Or.inr ⟨hs.1, hc.settled hs.2, (hacc.2 (fun h => h.2 hs)).1⟩
    · obtain ⟨pt, hpt⟩ := hacc.1 ⟨hkey, hs⟩
      rw [hc.path] at hpt
      exact Or.inl ⟨pt, hpt⟩
  · -- Without the key: the envelope, and settled or not moved.
    obtain ⟨henv, hse⟩ := hacc.2 (fun h => by rw [hkey] at h; exact absurd h.1 (by simp))
    refine ⟨henv, ?_⟩
    rcases hse with hs | hs
    · exact Or.inl (hc.settled hs)
    · exact Or.inr (fun hb => by rw [← hc.elsewhere, hs] at hb; exact absurd hb (by simp))

/-! ## End to end -/

/-- **End-to-end security of the pre-commit hook.** Assume the adapter
    contracts: Git reports the index, `HEAD` and `HEAD^1` exactly (A20) and
    the committed attributes' `filter` values (A19); every blob the hook
    checked is the content of its entry's object id (A11, A21); the
    primitives realize the suite `σ` (A5), whose digest gives the
    configuration id (A5); and the configuration is the one committed as
    `.transcrypt/config` (checked by the adapter, A4). If the hook's final
    check accepted (`HookEvidence`, `hookPlan` returned `true`), then the
    index Git commits (A22) is an `AcceptedIndex`: every entry that the
    committed attributes select is a regular, non-reserved file whose blob

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
    (`hook_accepts_only_authenticated_ciphertext_given_history`). -/
theorem hook_accepts_only_authenticated_ciphertext (g : GitState) (run : HookEvidence g)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (keyed incremental : Bool)
    (hR : Realizes inst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hgit : HookContracts g run)
    (hcfg : ConfigCommitted g (wireBytes config))
    (hcheck : hookPlan inst prims config id keyed incremental run.entries = ok true) :
    ConfigCommitted g (wireBytes config) ∧ SnapshotsSorted g ∧
      AcceptedIndex σ (wireBytes config) keyed incremental g := by
  refine ⟨hcfg, hook_snapshots_sorted hgit, fun x hx hsx => ?_⟩
  -- Every check accepted (`hookPlan_spec`); the selected `x` has one.
  have hplan := spec_result (hookPlan_spec hR config id keyed incremental run.entries) hcheck rfl
  obtain ⟨e, he, hce⟩ := hook_checks_selected hgit hx hsx
  have hacc := hplan e he
  rw [hid] at hacc
  exact hacc.accepted hce (hook_selectable hgit hx hsx)

/-! ## Settled entries and the checked history -/

/-- **A24 (checked history).** Every entry of `HEAD` whose path the
    committed attributes select is a record that authenticates at its path
    under the committed configuration. It holds when `HEAD` was accepted by
    this hook or by the keyed audit under the same attributes and
    configuration: the hook counts an entry as settled only while no
    attribute file or the configuration changed since `HEAD` and `HEAD^1`,
    and `HEAD` is sorted (each path once), so the entry that held the blob
    is the only one at that path (`Sorted.holds_oid`). -/
def HeadAuthentic (σ : Suite) (config : List Nat) (g : GitState) : Prop :=
  ∀ y ∈ g.head, Selected (g.filter y.path) →
    ∃ content, g.blob y.oid = some content ∧ AuthenticatedAt σ config y content

/-- **With the key and a checked history, every selected entry
    authenticates.** Under the hypotheses of
    `hook_accepts_only_authenticated_ciphertext` and A24, an accepted commit
    made with the key, incremental or not, stores at every path the
    committed attributes select a record that authenticates at that path
    (`AuthenticatedIndex`). -/
theorem hook_accepts_only_authenticated_ciphertext_given_history (g : GitState) (run : HookEvidence g)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (incremental : Bool)
    (hR : Realizes inst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hgit : HookContracts g run)
    (hcfg : ConfigCommitted g (wireBytes config))
    (hcheck : hookPlan inst prims config id true incremental run.entries = ok true)
    (hhist : HeadAuthentic σ (wireBytes config) g) :
    AuthenticatedIndex σ (wireBytes config) g := by
  obtain ⟨-, -, h⟩ := hook_accepts_only_authenticated_ciphertext g run config id true incremental hR hid hgit
    hcfg hcheck
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

/-! ## The key the hook uses -/

/-- **Stored-key unlock.** `Key::load` uses a stored key only when the
    verified `stored_key_state` says `Unlocked`, with `authentic` computed by
    the verified `authenticate_config` under the primitives built from the
    stored key bytes (A17: the adapter builds them from `file[CONFIG_LEN..]`). Then
    the file holds exactly the current configuration and the key
    authenticates it (`ConfigAuthentic`, relative to `Realizes`, A5). -/
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

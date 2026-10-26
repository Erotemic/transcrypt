import V3Wire.Verification.Lifecycle
import V3Wire.Verification.Objects

/-!
# End to end: selected paths enter Git as authenticated ciphertext

The pre-commit hook (`transcrypt_v3::lifecycle::verify` with `seal`) is the
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
  returns that object (`GitObject`, A11, A21); the crypto primitives realize
  the abstract suite (`Realizes`, A5); Git commits the index the hook
  checked (A22, stated in prose: the conclusion is about `g.index`).
* **The run.** `HookRun` lists the results the adapter obtained from the
  verified core: the listing parse, the attribute flags, the selectability
  check, the `HEAD`/`HEAD^1` membership, the keyless move check, each
  entry's fields, and the per-entry checks `hookPlan` (a model of the loop
  in `check_staged`, like `verifyPlan`). The adapter acts only on these
  results (A4).

`hook_accepts_only_authenticated_ciphertext`: if the run accepted, every
path the committed attributes select is a regular, non-reserved entry whose
blob, when unlocked, authenticates at exactly that path under the committed
configuration (or, in the incremental hook, is unchanged since `HEAD` and
`HEAD^1` and has the v3 envelope); when locked, it has the envelope of this
configuration and is not a blob moved from another path.
`hook_repairs_only_local_changes`: everything the hook re-encrypts before
that check was a local change of the user, and a rebind re-encrypts only a
record that authenticates at a `HEAD` path it was moved from.

The listings are sorted by path (the verified parse checks it), so lookups
are binary searches, and lookups by object id go through object orders that
the adapter sorts and `object_order_ok` checks.
`hook_accepts_only_authenticated_ciphertext_given_history` adds A24 (the
history the incremental hook trusts was checked) and concludes that every
selected entry authenticates.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

/-- A verified function's specification applies to the result the adapter
    observed. -/
theorem spec_result {α : Type} {m : RustM α} {P : α → Prop} {r : α} (h : m ⦃ x => P x ⦄)
    (hm : m = ok r) : P r := by
  obtain ⟨y, hy, hP⟩ := WP.spec_imp_exists h
  rw [hm] at hy
  cases hy
  exact hP

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

/-- The check `check_staged` makes of one protected entry. With the key
    (and, in the incremental pre-commit hook, unless the entry is
    `settled`), the blob must authenticate at the entry's path
    (`open_record`). Otherwise it must have this configuration's envelope
    (`record_envelope_ok`), and, unless settled, must not be a blob of
    another path (a record moved without the key). The adapter also checks
    the header first; it accepts an entry only if this model does (A4). -/
def hookEntry (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) (keyed incremental : Bool) (e : HookEntry) : RustM Bool := do
  if keyed && !(incremental && e.settled) then
    let (r, _) ← open_record inst prims config e.path e.record e.buffer
    match r with
    | core.result.Result.Ok _ => ok true
    | core.result.Result.Err _ => ok false
  else
    let env ← record_envelope_ok e.record id
    ok (env && (e.settled || !e.elsewhere))

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
  split
  · rename_i hk
    have hk' : keyed = true ∧ ¬ (incremental = true ∧ e.settled = true) := by
      revert hk; cases keyed <;> cases incremental <;> cases e.settled <;> simp
    step with open_record_spec h config e.path e.record e.buffer as ⟨ r, pt, hr ⟩
    rcases r with u | x
    · simp only at hr ⊢
      exact fun _ => EntryAccepted.of_opens hk' ⟨_, hr⟩
    · simp
  · rename_i hk
    have hk' : ¬ (keyed = true ∧ ¬ (incremental = true ∧ e.settled = true)) := by
      revert hk; cases keyed <;> cases incremental <;> cases e.settled <;> simp
    step with record_envelope_ok_spec as ⟨ env, henv ⟩
    intro hb
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hb
    exact EntryAccepted.of_envelope hk' (henv.mp hb.1) hb.2

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

/-- A listing Git printed exactly, parsed by the verified core with one slot
    per NUL (as the adapter allocates), gives exactly its entries, and,
    accepted with `unique`, they are sorted: each path once (`Sorted`). -/
theorem listing_of_git {listing : Slice U8} {ends0 ends : Slice Usize} {es : List Entry}
    (hg : GitListing listing es) (hlen : ends0.length = (sliceBytes listing).count 0)
    (hp : parse_listing listing ends0 true = ok (true, ends)) : ListingOf listing ends es ∧ Sorted es := by
  have := spec_result (parse_listing_spec listing ends0 true) hp
  obtain ⟨hL, hs⟩ := this.2 es ⟨hg.1, hg.2, by rw [hlen, hg.2, listingBytes_count es hg.1]⟩
  exact ⟨hL, orderedAs_true.mp (hs.mp rfl)⟩

/-- The same for the adapter's merge of several trees (paths may repeat):
    the entries are in path order (`PathOrdered`). -/
theorem merged_listing_of_git {listing : Slice U8} {ends0 ends : Slice Usize} {es : List Entry}
    (hg : GitListing listing es) (hlen : ends0.length = (sliceBytes listing).count 0)
    (hp : parse_listing listing ends0 false = ok (true, ends)) : ListingOf listing ends es ∧ PathOrdered es := by
  have := spec_result (parse_listing_spec listing ends0 false) hp
  obtain ⟨hL, hs⟩ := this.2 es ⟨hg.1, hg.2, by rw [hlen, hg.2, listingBytes_count es hg.1]⟩
  exact ⟨hL, orderedAs_false.mp (hs.mp rfl)⟩

/-! ## The hook's final check -/

/-- The results the adapter obtained from the verified core in the hook's
    final check (`check_staged`, after any sealing): it refuses the commit
    unless they are as shown, and builds each protected entry's check from
    them (A4). `n` is the number of index entries. -/
structure HookRun (g : GitState) (index head parent response : Slice U8)
    (ends0 ends hends0 hends pends0 pends iorder horder porder : Slice Usize)
    (flags0 flags all inHead0 inHead inParent0 inParent : Slice Bool) (entries : List HookEntry) : Prop where
  /-- The three listings, parsed with one slot per NUL, each path once. -/
  ends0_len : ends0.length = (sliceBytes index).count 0
  parse : parse_listing index ends0 true = ok (true, ends)
  hends0_len : hends0.length = (sliceBytes head).count 0
  head_parse : parse_listing head hends0 true = ok (true, hends)
  pends0_len : pends0.length = (sliceBytes parent).count 0
  parent_parse : parse_listing parent pends0 true = ok (true, pends)
  /-- Their object orders (sorted by the adapter), checked by the core. -/
  index_order : object_order_ok index ends iorder = ok true
  head_order : object_order_ok head hends horder = ok true
  parent_order : object_order_ok parent pends porder = ok true
  /-- The protected flags: Git's answer checked against the listing's paths. -/
  flags0_len : flags0.length = g.index.length
  attrs : parse_listing_attrs index ends response flags0 = ok (true, flags)
  /-- No protected entry is unselectable. -/
  selectable : ∃ sel : Usize, first_unselectable index ends flags = ok sel ∧ sel.val = g.index.length
  /-- Membership in `HEAD` (every entry) and `HEAD^1` (protected entries). -/
  all_true : all.val = List.replicate g.index.length true
  inHead0_len : inHead0.length = g.index.length
  in_head : held_entries index ends all head hends inHead0 = ok (true, inHead)
  inParent0_len : inParent0.length = g.index.length
  in_parent : held_entries index ends flags parent pends inParent0 = ok (true, inParent)
  /-- One check per protected entry, in index order. -/
  positions : entries.map (fun e => e.index.val) = (List.range g.index.length).filter (fun i => flags.val[i]!)
  /-- Each check's path is the entry's path field (`listing_fields`). -/
  fields : ∀ e ∈ entries, ∃ f, listing_fields index ends e.index = ok (core.option.Option.Some f) ∧
    sliceBytes e.path = (sliceBytes index).extract f.path_start.val f.end.val
  /-- An entry counts as settled only if both `HEAD` and `HEAD^1` hold it
      (the adapter also requires unchanged attribute files and config). -/
  settled : ∀ e ∈ entries, e.settled = true → (inHead.val[e.index.val]! && inParent.val[e.index.val]!) = true
  elsewhere : ∀ e ∈ entries,
    blob_elsewhere index ends iorder e.index head hends horder parent pends porder = ok e.elsewhere

/-- **End-to-end security of the pre-commit hook.** Assume the adapter
    contracts: Git reports the index, `HEAD` and `HEAD^1` exactly (A20) and
    the committed attributes' `filter` values (A19); every blob the hook
    checked is the content of its entry's object id (A11, A21); the
    primitives realize the suite `σ` (A5), whose digest gives the
    configuration id (A5); and the configuration is the one committed as
    `.transcrypt/config` (checked by the adapter, A4). If the hook's final
    check accepted (`HookRun`, `hookPlan` returned `true`), then every entry of
    the index Git commits (A22) that the committed attributes select is a
    regular, non-reserved file whose blob

    * with the key, authenticates at exactly its own path under the
      committed configuration — or, in the incremental hook, is unchanged
      since `HEAD` and `HEAD^1` and has the v3 envelope of that
      configuration (checked when it was committed, and by the audit);
    * without the key, has that envelope (A14: keyless checks cannot detect
      a forgery) and is unchanged since `HEAD` and `HEAD^1` or is not a blob
      of another path (no record moved without the key).

    The three snapshots are sorted (`Sorted`: each path once, as Git lists
    them; the parse refuses a crafted tree that repeats a path), so
    "unchanged since `HEAD`" names the one entry `HEAD` has at that path.
    With A24 the settled case authenticates too
    (`hook_accepts_only_authenticated_ciphertext_given_history`). -/
theorem hook_accepts_only_authenticated_ciphertext (g : GitState)
    (index head parent response : Slice U8) (ends0 ends hends0 hends pends0 pends : Slice Usize)
    (iorder horder porder : Slice Usize)
    (flags0 flags all inHead0 inHead inParent0 inParent : Slice Bool) (entries : List HookEntry)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (keyed incremental : Bool)
    (hR : Realizes inst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hindex : GitListing index g.index) (hhead : GitListing head g.head) (hparent : GitListing parent g.parent)
    (hattr : GitAttributes g response)
    (hobj : ∀ e ∈ entries, ∃ x, g.index[e.index.val]? = some x ∧ GitObject g x.oid e.record)
    (hcfg : ∃ c ∈ g.index, c.path = ascii ".transcrypt/config" ∧ c.Regular ∧ g.blob c.oid = some (wireBytes config))
    (hrun : HookRun g index head parent response ends0 ends hends0 hends pends0 pends iorder horder porder
      flags0 flags all inHead0 inHead inParent0 inParent entries)
    (hcheck : hookPlan inst prims config id keyed incremental entries = ok true) :
    (∃ c ∈ g.index, c.path = ascii ".transcrypt/config" ∧ g.blob c.oid = some (wireBytes config)) ∧
    (Sorted g.index ∧ Sorted g.head ∧ Sorted g.parent) ∧
    ∀ x ∈ g.index, Selected (g.filter x.path) →
      Selectable x ∧ ∃ content, g.blob x.oid = some content ∧
        (keyed = true → (∃ pt, OpensTo σ (wireBytes config) x.path content pt) ∨
          (incremental = true ∧ Settled g.head g.parent x ∧ EnvelopeOk content (σ.digest16 (wireBytes config)))) ∧
        (keyed = false → EnvelopeOk content (σ.digest16 (wireBytes config)) ∧
          (Settled g.head g.parent x ∨ ¬ BlobElsewhere [g.index, g.head, g.parent] x)) := by
  -- The verified parses give exactly Git's snapshots, each path once.
  obtain ⟨hL, hLs⟩ := listing_of_git hindex hrun.ends0_len hrun.parse
  obtain ⟨hH, hHs⟩ := listing_of_git hhead hrun.hends0_len hrun.head_parse
  obtain ⟨hP, hPs⟩ := listing_of_git hparent hrun.pends0_len hrun.parent_parse
  refine ⟨by obtain ⟨c, hc, hp, _, hb⟩ := hcfg; exact ⟨c, hc, hp, hb⟩, ⟨hLs, hHs, hPs⟩, ?_⟩
  -- The object orders.
  have hIo := (spec_result (object_order_ok_spec hL iorder) hrun.index_order).mp rfl
  have hHo := (spec_result (object_order_ok_spec hH horder) hrun.head_order).mp rfl
  have hPo := (spec_result (object_order_ok_spec hP porder) hrun.parent_order).mp rfl
  -- The flags are Git's selection of each entry.
  have hflags := (spec_result (parse_listing_attrs_spec hL response flags0) hrun.attrs).2
    (g.index.map (fun e => g.filter e.path)) ⟨by simp, by
      intro v hv; obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv; exact hattr.1 e he,
      hrun.flags0_len, hattr.2⟩
  have hfl : flags.val = g.index.map (fun e => decide (Selected (g.filter e.path))) := by
    rw [hflags.2, List.map_map]; rfl
  -- No protected entry is unselectable.
  obtain ⟨sel, hsel0, hsel_none⟩ := hrun.selectable
  have hsel := spec_result (first_unselectable_spec hL flags (by
    rw [Slice.length, hfl, List.length_map])) hsel0
  -- Membership in `HEAD` and `HEAD^1`.
  have hinH := spec_result (held_entries_spec hL hH hHs.pathOrdered all inHead0 (by
    rw [Slice.length, hrun.all_true, List.length_replicate]) hrun.inHead0_len) hrun.in_head
  have hinP := spec_result (held_entries_spec hL hP hPs.pathOrdered flags inParent0 (by
    rw [Slice.length, hfl, List.length_map]) hrun.inParent0_len) hrun.in_parent
  have hplan := spec_result (hookPlan_spec hR config id keyed incremental entries) hcheck rfl
  intro x hx hsx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hfk : flags.val[k]! = true := by
    rw [hfl, getElem!_pos _ k (by simp; omega)]; simp [hsx]
  refine ⟨hsel.2.1 k _ (by rw [hsel_none]; exact hk) (List.getElem?_eq_getElem hk) hfk, ?_⟩
  -- The entry's check.
  have hmem : k ∈ entries.map (fun e => e.index.val) := by
    rw [hrun.positions]; exact List.mem_filter.mpr ⟨List.mem_range.mpr hk, hfk⟩
  obtain ⟨e, he, hek⟩ := List.mem_map.1 hmem
  have hacc := hplan e he
  obtain ⟨x', hx', hobj'⟩ := hobj e he
  rw [hek, List.getElem?_eq_getElem hk, Option.some.injEq] at hx'
  subst hx'
  -- Its path is the entry's path.
  obtain ⟨f, hf, hpath⟩ := hrun.fields e he
  have hfs := spec_result (listing_fields_spec hL e.index) hf
  obtain ⟨y, hy, -, -, hyp, -⟩ := FieldsOf.slices hL hfs.2
  rw [hek, List.getElem?_eq_getElem hk, Option.some.injEq] at hy
  subst hy
  rw [hyp] at hpath
  -- A settled entry is `Settled`.
  have hall : all.val[k]! = true := by
    rw [hrun.all_true, getElem!_pos _ k (by simp; omega)]; simp
  have hsett : e.settled = true → Settled g.head g.parent g.index[k] := by
    intro hs
    have := hrun.settled e he hs
    rw [hek, Bool.and_eq_true, hinH.2.2 k _ hk (List.getElem?_eq_getElem hk),
      hinP.2.2 k _ hk (List.getElem?_eq_getElem hk)] at this
    simp only [hall, hfk, true_and] at this
    exact this
  -- `elsewhere` is exactly `BlobElsewhere`.
  have hels : e.elsewhere = true ↔ BlobElsewhere [g.index, g.head, g.parent] g.index[k] := by
    have := spec_result (blob_elsewhere_spec hL hLs hIo hH hHs hHo hP hPs hPo e.index (by omega))
      (hrun.elsewhere e he)
    simp only [hek] at this
    exact this
  refine ⟨_, hobj', ?_, ?_⟩
  · intro hkey
    by_cases hs : incremental = true ∧ e.settled = true
    · right
      have := (hacc.2 (fun h => h.2 hs)).1
      rw [hid] at this
      exact ⟨hs.1, hsett hs.2, this⟩
    · left
      obtain ⟨pt, hpt⟩ := hacc.1 ⟨hkey, hs⟩
      rw [hpath] at hpt
      exact ⟨pt, hpt⟩
  · intro hkey
    obtain ⟨henv, hse⟩ := hacc.2 (fun h => by rw [hkey] at h; exact absurd h.1 (by simp))
    rw [hid] at henv
    refine ⟨henv, ?_⟩
    rcases hse with hs | hs
    · exact Or.inl (hsett hs)
    · exact Or.inr (fun hb => by rw [← hels] at hb; rw [hs] at hb; exact absurd hb (by simp))

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
    ∃ content, g.blob y.oid = some content ∧ ∃ pt, OpensTo σ config y.path content pt

/-- **With the key and a checked history, every selected entry
    authenticates.** Under the hypotheses of
    `hook_accepts_only_authenticated_ciphertext` and A24, an accepted commit
    made with the key, incremental or not, stores at every path the
    committed attributes select a record that authenticates at that path. -/
theorem hook_accepts_only_authenticated_ciphertext_given_history (g : GitState)
    (index head parent response : Slice U8) (ends0 ends hends0 hends pends0 pends : Slice Usize)
    (iorder horder porder : Slice Usize)
    (flags0 flags all inHead0 inHead inParent0 inParent : Slice Bool) (entries : List HookEntry)
    (config : Std.Array U8 55#usize) (id : Std.Array U8 16#usize) (incremental : Bool)
    (hR : Realizes inst prims σ)
    (hid : wireBytes id = σ.digest16 (wireBytes config))
    (hindex : GitListing index g.index) (hhead : GitListing head g.head) (hparent : GitListing parent g.parent)
    (hattr : GitAttributes g response)
    (hobj : ∀ e ∈ entries, ∃ x, g.index[e.index.val]? = some x ∧ GitObject g x.oid e.record)
    (hcfg : ∃ c ∈ g.index, c.path = ascii ".transcrypt/config" ∧ c.Regular ∧ g.blob c.oid = some (wireBytes config))
    (hrun : HookRun g index head parent response ends0 ends hends0 hends pends0 pends iorder horder porder
      flags0 flags all inHead0 inHead inParent0 inParent entries)
    (hcheck : hookPlan inst prims config id true incremental entries = ok true)
    (hhist : HeadAuthentic σ (wireBytes config) g) :
    ∀ x ∈ g.index, Selected (g.filter x.path) →
      Selectable x ∧ ∃ content, g.blob x.oid = some content ∧ ∃ pt, OpensTo σ (wireBytes config) x.path content pt := by
  obtain ⟨-, -, h⟩ := hook_accepts_only_authenticated_ciphertext g index head parent response ends0 ends hends0
    hends pends0 pends iorder horder porder flags0 flags all inHead0 inHead inParent0 inParent entries config id
    true incremental hR hid hindex hhead hparent hattr hobj hcfg hrun hcheck
  intro x hx hsx
  obtain ⟨hsel, content, hc, hk, -⟩ := h x hx hsx
  refine ⟨hsel, content, hc, ?_⟩
  rcases hk rfl with hop | ⟨-, ⟨⟨y, hy, hyo, hyp⟩, -⟩, -⟩
  · exact hop
  · obtain ⟨c', hc', pt, hpt⟩ := hhist y hy (hyp ▸ hsx)
    rw [hyo, hc, Option.some.injEq] at hc'
    subst hc'
    rw [hyp] at hpt
    exact ⟨pt, hpt⟩

/-! ## The key the hook uses -/

/-- **Stored-key unlock.** `Key::load` uses a stored key only when the
    verified `stored_key_state` says `Unlocked`, with `authentic` computed by
    the verified `authenticate_config` under the primitives built from the
    stored key bytes (A17: the adapter builds them from `file[55..]`). Then
    the file holds exactly the current configuration and the key
    authenticates it (`ConfigAuthentic`, relative to `Realizes`, A5). -/
theorem stored_key_authenticates_current_config (hR : Realizes inst prims σ)
    (present : Bool) (file current : Slice U8) (config : Std.Array U8 55#usize)
    (hcur : sliceBytes current = wireBytes config) (authentic : Bool)
    (hauth : authentic = true → ∃ c, authenticate_config inst prims config = ok (core.result.Result.Ok c))
    (hstate : stored_key_state present file current authentic = ok transcrypt_v3_core.StoredKey.Unlocked) :
    present = true ∧ (sliceBytes file).length = 119 ∧ (sliceBytes file).take 55 = wireBytes config ∧
      ConfigAuthentic σ (wireBytes config) := by
  have hs := spec_result (stored_key_state_spec present file current authentic) hstate
  have hu : storedKeySpec present (sliceBytes file) (sliceBytes current) authentic = .unlocked := by
    cases h : storedKeySpec present (sliceBytes file) (sliceBytes current) authentic <;>
      rw [h] at hs <;> simp [storedKeyResult] at hs ⊢
  obtain ⟨hp, hl, ht, ha⟩ := storedKeySpec_unlocked hu
  obtain ⟨c, hc⟩ := hauth ha
  have := spec_result (authenticate_config_spec hR config) hc
  exact ⟨hp, hl, ht.trans hcur, this.1⟩

/-! ## The hook's repairs: no laundering -/

theorem sealResult_eq_seal {a : Transcrypt.V3Policy.SealAction} :
    sealResult a = transcrypt_v3_core.SealAction.Seal ↔ a = .seal := by
  cases a <;> simp [sealResult]

theorem sealResult_eq_rebind {a : Transcrypt.V3Policy.SealAction} :
    sealResult a = transcrypt_v3_core.SealAction.Rebind ↔ a = .rebind := by
  cases a <;> simp [sealResult]

/-- **The pre-commit hook repairs only local changes.** For a protected
    entry `i` of Git's index (A20), with `HEAD` and the commits being brought
    in parsed exactly (A20, A23: the sequencing state names those commits),
    suppose the hook computed its inputs with the verified core — membership
    in `HEAD` and the incoming commits (`held_entries`; the incoming commits
    are only consulted when some protected entry changed, `known`), the
    local-change input (`is_local_change`), whether the blob opens at its own
    path (`open_record`), whether it has the v3 envelope
    (`parse_file_header`), and, for `moved`, a move source
    (`next_move_source`) at which it opens — and `seal_action` decided to
    seal or re-seal it. Then the entry is a local change of the user
    (`LocalChange`: never content of `HEAD` or of an incoming commit unless
    `protect` forced plaintext), it did not already open at its path, only
    plaintext is sealed, and a rebind re-encrypts exactly the plaintext of a
    record that authenticates at a `HEAD` path it was moved from
    (`MoveSource`). -/
theorem hook_repairs_only_local_changes (g : GitState)
    (index head incomingL : Slice U8) (iends0 ends hends0 hends mends horder : Slice Usize)
    (flags inHead0 inHead inInc0 inInc : Slice Bool) (i : Usize) (hi : i.val < g.index.length)
    (config : Std.Array U8 55#usize) (path record openBuf : Slice U8)
    (forced known opens envelope moved localc : Bool) (act : transcrypt_v3_core.SealAction)
    (hR : Realizes inst prims σ)
    (hindex : GitListing index g.index) (hilen : iends0.length = (sliceBytes index).count 0)
    (hparse : parse_listing index iends0 true = ok (true, ends))
    (hhead : GitListing head g.head) (hhlen : hends0.length = (sliceBytes head).count 0)
    (hhparse : parse_listing head hends0 true = ok (true, hends))
    (hflen : flags.length = g.index.length) (hfi : flags.val[i.val]! = true)
    (hInHead0 : inHead0.length = g.index.length)
    (hinH : held_entries index ends flags head hends inHead0 = ok (true, inHead))
    (hknown : known = true → ∃ m, ∃ mends0 : Slice Usize, g.incoming = some m ∧ GitListing incomingL m ∧
      mends0.length = (sliceBytes incomingL).count 0 ∧ parse_listing incomingL mends0 false = ok (true, mends) ∧
      inInc0.length = g.index.length ∧ held_entries index ends flags incomingL mends inInc0 = ok (true, inInc))
    (hlazy : known = false → g.incoming = none ∨ inHead.val[i.val]! = true)
    (hlocal : is_local_change inHead.val[i.val]! known (known && inInc.val[i.val]!) forced envelope = ok localc)
    (hopens : ∀ pt r, open_record inst prims config path record openBuf = ok (r, pt) →
      (opens = true ↔ r = core.result.Result.Ok ()))
    (henvelope : ∀ r, parse_file_header record = ok r → (envelope = true ↔ ∃ x, r = core.result.Result.Ok x))
    (hmoved : moved = true → ∃ (from_ j : Usize) (src buf pt : Slice U8), from_.val ≤ g.head.length ∧
      object_order_ok head hends horder = ok true ∧
      next_move_source index ends i head hends horder from_ = ok j ∧ j.val < g.head.length ∧
      sliceBytes src = (g.head[j.val]?).elim [] (·.path) ∧
      open_record inst prims config src record buf = ok (core.result.Result.Ok (), pt))
    (hseal : seal_action opens localc envelope moved = ok act)
    (hrepair : act = transcrypt_v3_core.SealAction.Seal ∨ act = transcrypt_v3_core.SealAction.Rebind) :
    LocalChange g.head g.incoming forced envelope g.index[i.val] ∧
      (∀ r pt, open_record inst prims config path record openBuf = ok (r, pt) → r ≠ core.result.Result.Ok ()) ∧
      (act = transcrypt_v3_core.SealAction.Seal →
        ∀ r, parse_file_header record = ok r → ∀ x, r ≠ core.result.Result.Ok x) ∧
      (act = transcrypt_v3_core.SealAction.Rebind → envelope = true ∧ ∃ h ∈ g.head,
        MoveSource g.index g.index[i.val] h ∧ ∃ pt, OpensTo σ (wireBytes config) h.path (sliceBytes record) pt) := by
  have hact := spec_result (seal_action_spec opens localc envelope moved) hseal
  -- What `seal_action` decided, in the spec's terms.
  have hspec : sealSpec opens localc envelope moved = .seal ∨ sealSpec opens localc envelope moved = .rebind := by
    rcases hrepair with h | h <;> rw [h] at hact
    · exact Or.inl (sealResult_eq_seal.mp hact.symm)
    · exact Or.inr (sealResult_eq_rebind.mp hact.symm)
  obtain ⟨hloc, hop⟩ := sealSpec_repairs_only_local hspec
  -- The verified parses give exactly Git's snapshots, each path once.
  obtain ⟨hL, hLs⟩ := listing_of_git hindex hilen hparse
  obtain ⟨hH, hHs⟩ := listing_of_git hhead hhlen hhparse
  -- `HEAD` membership.
  have hheld := spec_result (held_entries_spec hL hH hHs.pathOrdered flags inHead0 hflen hInHead0) hinH
  have hh : inHead.val[i.val]! = true ↔ Holds g.head g.index[i.val].oid g.index[i.val].path := by
    rw [hheld.2.2 i.val _ hi (List.getElem?_eq_getElem hi), hfi]; simp
  -- The local-change input is `LocalChange`.
  have hlc : localc = true ↔ LocalChange g.head g.incoming forced envelope g.index[i.val] := by
    cases hk : known
    · rw [hk, Bool.false_and] at hlocal
      have := spec_result (is_local_change_spec g.head none g.index[i.val] inHead.val[i.val]! false forced
        envelope hh (fun m hm => by cases hm)) hlocal
      rw [this, localChange_unknown]
      rcases hlazy hk with hn | hin
      · rw [hn, localChange_unknown]
      · rw [localChange_held (hh.mp hin)]
    · obtain ⟨m, mends0, hm, hgm, hmlen, hmparse, hlen, hinc⟩ := hknown hk
      obtain ⟨hM, hMo⟩ := merged_listing_of_git hgm hmlen hmparse
      have hheldM := spec_result (held_entries_spec hL hM hMo flags inInc0 hflen hlen) hinc
      have hii : inInc.val[i.val]! = true ↔ Holds m g.index[i.val].oid g.index[i.val].path := by
        rw [hheldM.2.2 i.val _ hi (List.getElem?_eq_getElem hi), hfi]; simp
      rw [hk, Bool.true_and] at hlocal
      have hl' : is_local_change inHead.val[i.val]! g.incoming.isSome inInc.val[i.val]! forced envelope =
          ok localc := by rw [hm]; exact hlocal
      have hres := spec_result (is_local_change_spec g.head g.incoming g.index[i.val] inHead.val[i.val]!
        inInc.val[i.val]! forced envelope hh (fun m' hm' => by rw [hm] at hm'; cases hm'; exact hii)) hl'
      exact hres
  refine ⟨hlc.mp hloc, fun r pt hr hok => ?_, fun hs => ?_, fun hrb => ?_⟩
  · have := (hopens pt r hr).mpr hok
    rw [hop] at this; cases this
  · rw [hs] at hact
    have : sealSpec opens localc envelope moved = .seal := sealResult_eq_seal.mp hact.symm
    have hpl := sealSpec_seal_plain this
    intro r hr x hx
    have := (henvelope r hr).mpr ⟨x, hx⟩
    rw [hpl] at this; cases this
  · rw [hrb] at hact
    have hsr : sealSpec opens localc envelope moved = .rebind := sealResult_eq_rebind.mp hact.symm
    obtain ⟨he, hm⟩ := sealSpec_rebind_moved hsr
    refine ⟨he, ?_⟩
    obtain ⟨from_, j, src, buf, pt, hfrom, hord, hnext, hj, hsrc, hopen⟩ := hmoved hm
    have hHo := (spec_result (object_order_ok_spec hH horder) hord).mp rfl
    have hfirst := spec_result (next_move_source_spec hL hLs.pathOrdered hH hHo i hi from_ hfrom) hnext
    obtain ⟨h, hhj, hms⟩ := hfirst.2.2.2 hj
    have hor := spec_result (open_record_spec hR config src record buf) hopen
    rw [hhj] at hsrc
    simp only [Option.elim] at hsrc
    rw [hsrc] at hor
    exact ⟨h, List.mem_of_getElem? hhj, hms, _, hor⟩

end Transcrypt.V3Verification

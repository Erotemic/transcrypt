import V3Wire.Verification.SnapshotListing

/-!
Git snapshot listings, part 2: byte order and parsing. `bytes_lt` is exactly
the spec's `BytesLt` (Git's order of paths), `listing_ordered` decides
whether a listing's paths are in that order (`OrderedAs`: `Sorted` or
`PathOrdered`), and `parse_listing` accepts exactly the listings of
well-formed entries in that order, computing `ListingOf` (sound and
complete).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core
open Transcrypt.V3Policy

/-! ## Byte order: `bytes_lt` and `listing_ordered` -/

/-- **Byte order.** `bytes_lt` is exactly `BytesLt`, Git's order of paths. -/
@[step]
theorem bytes_lt_spec (a b : Slice U8) :
    bytes_lt a b ⦃ r => r = true ↔ BytesLt (sliceBytes a) (sliceBytes b) ⦄ := by
  unfold bytes_lt bytes_lt_loop
  apply compare_loop _ (fun n => n ≤ a.length ∧ n ≤ b.length ∧
      (sliceBytes a).take n = (sliceBytes b).take n) (min a.length b.length) _ _ 0#usize (by simp)
    ⟨by simp, by simp, by simp⟩
  intro j hj ⟨hja, hjb, hc⟩
  have hla := sliceBytes_length a
  have hlb := sliceBytes_length b
  unfold bytes_lt_loop.body
  simp_len
  step*
  · rename_i hne
    subst i3_post2 i4_post2
    have hj1 : j.val < (sliceBytes a).length := by omega
    have hj2 : j.val < (sliceBytes b).length := by omega
    rw [bytesLt_drop hc, List.drop_eq_getElem_cons hj1, List.drop_eq_getElem_cons hj2,
      sliceBytes_getElem a j.val i3, sliceBytes_getElem b j.val i4]
    simp_bne at hne
    have hv : (a.val[j.val]).val ≠ (b.val[j.val]).val := fun h => hne (UScalar.eq_of_val_eq h)
    simp only [BytesLt, decide_eq_true_eq, hv, false_and, or_false]
    exact Iff.rfl
  · subst i3_post2 i4_post2
    rename_i heq
    simp_bne at heq
    refine ⟨i5_post, by omega, by omega, by omega, ?_⟩
    rw [i5_post, List.take_add_one, List.take_add_one, hc,
      List.getElem?_eq_getElem (by omega : j.val < (sliceBytes a).length),
      List.getElem?_eq_getElem (by omega : j.val < (sliceBytes b).length),
      sliceBytes_getElem a j.val i3, sliceBytes_getElem b j.val i4, heq]
  · have hjb2 : j.val = b.length := by scalar_tac
    have hja2 : j.val < a.length := by scalar_tac
    rw [bytesLt_drop hc, List.drop_eq_getElem_cons (by omega : j.val < (sliceBytes a).length),
      List.drop_eq_nil_of_le (by omega : (sliceBytes b).length ≤ j.val)]
    simp only [BytesLt, iff_false, decide_eq_true_eq]
    scalar_tac
  · have hja2 : j.val = a.length := by scalar_tac
    rw [bytesLt_drop hc, List.drop_eq_nil_of_le (by omega : (sliceBytes a).length ≤ j.val)]
    rcases Nat.lt_or_ge j.val b.length with hlt | hge
    · rw [List.drop_eq_getElem_cons (by omega : j.val < (sliceBytes b).length)]
      simp only [BytesLt, iff_true, decide_eq_true_eq]
      scalar_tac
    · rw [List.drop_eq_nil_of_le (by omega : (sliceBytes b).length ≤ j.val)]
      simp only [BytesLt, iff_false, decide_eq_true_eq]
      scalar_tac

/-- The order of a listing's paths that `parse_listing` checks: strictly
    increasing (`unique`), or never decreasing. -/
def PathRel : Bool → Entry → Entry → Prop
  | true, a, b => BytesLt a.path b.path
  | false, a, b => BytesLt a.path b.path ∨ a.path = b.path

def OrderedAs (unique : Bool) (es : List Entry) : Prop := es.Pairwise (PathRel unique)

theorem orderedAs_true {es : List Entry} : OrderedAs true es ↔ Sorted es := Iff.rfl

theorem orderedAs_false {es : List Entry} : OrderedAs false es ↔ PathOrdered es := Iff.rfl

theorem pathRel_trans (unique : Bool) (a b c : Entry) (h1 : PathRel unique a b) (h2 : PathRel unique b c) :
    PathRel unique a c := by
  cases unique
  · simp only [PathRel] at h1 h2 ⊢
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (bytesLt_trans h1 h2)
    · exact Or.inl (h2 ▸ h1)
    · exact Or.inl (h1 ▸ h2)
    · exact Or.inr (h1.trans h2)
  · simp only [PathRel] at h1 h2 ⊢
    exact bytesLt_trans h1 h2

theorem orderedAs_iff_adjacent (unique : Bool) (es : List Entry) :
    OrderedAs unique es ↔ ∀ k (h : k + 1 < es.length), PathRel unique es[k] es[k + 1] :=
  ⟨fun h k hk => List.pairwise_iff_getElem.mp h k (k + 1) (by omega) hk (by omega),
   pairwise_of_adjacent (pathRel_trans unique) es⟩

/-- **Path order.** For a listing of `es`, `listing_ordered` says exactly
    whether its paths are in the order `parse_listing` requires. -/
theorem listing_ordered_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (unique : Bool) :
    listing_ordered listing ends unique ⦃ b => b = true ↔ OrderedAs unique es ⦄ := by
  have hel := hL.ends_length
  unfold listing_ordered listing_ordered_loop
  apply compare_loop _ (fun n => 1 ≤ n ∧ ∀ k (h : k + 1 < es.length), k + 1 < n → PathRel unique es[k] es[k + 1])
    (max es.length 1) _ _ 1#usize (by simp) ⟨by simp, fun k _ hk => absurd hk (by simp)⟩
  intro i hi ⟨hi1, hinv⟩
  unfold listing_ordered_loop.body
  simp_len [bind_tc_ok]
  split
  · rename_i hlt
    have hin : i.val < es.length := by scalar_tac
    step as ⟨ i2, hi2 ⟩
    step with listing_fields_spec hL i2 as ⟨ o, ho ⟩
    rcases o with _ | p
    · exfalso; simp only at ho; omega
    obtain ⟨-, hp⟩ := ho
    obtain ⟨ep, hep, -, -, hpp, -, -, hp3, hp4⟩ := FieldsOf.slices hL hp
    simp only
    step with listing_fields_spec hL i as ⟨ o1, ho1 ⟩
    rcases o1 with _ | f
    · exfalso; simp only at ho1; omega
    obtain ⟨-, hf⟩ := ho1
    obtain ⟨ef, hef, -, -, hfp, -, -, hf3, hf4⟩ := FieldsOf.slices hL hf
    simp only
    step with index_range_spec listing p.path_start p.end hp3 hp4 as ⟨ prev, hprev ⟩
    step with index_range_spec listing f.path_start f.end hf3 hf4 as ⟨ path, hpath ⟩
    rw [hpp] at hprev
    rw [hfp] at hpath
    have hk : i2.val + 1 = i.val := by scalar_tac
    have hepi : es[i2.val]'(by omega) = ep := by
      rw [List.getElem?_eq_getElem (by omega)] at hep; exact Option.some.inj hep
    have hefi : es[i.val] = ef := by
      rw [List.getElem?_eq_getElem hin] at hef; exact Option.some.inj hef
    -- The pair `(i - 1, i)` decides.
    have hcont : PathRel unique ep ef → ∀ k (h : k + 1 < es.length), k + 1 < i.val + 1 →
        PathRel unique es[k] es[k + 1] := by
      intro hr k hk1 hk2
      rcases Nat.lt_or_ge (k + 1) i.val with hlt | hge
      · exact hinv k hk1 hlt
      · have hki : k = i2.val := by omega
        subst hki
        rw [← hepi, ← hefi] at hr
        simpa [hk] using hr
    have hdone : ¬ PathRel unique ep ef → ¬ OrderedAs unique es := by
      intro hr hall
      apply hr
      have := (orderedAs_iff_adjacent unique es).mp hall i2.val (by omega)
      rw [hepi] at this
      simpa [hk, hefi] using this
    cases unique
    · simp only [Bool.false_eq_true, ↓reduceIte]
      step with bytes_lt_spec prev path as ⟨ b, hb ⟩
      step with bytes_eq_spec prev path as ⟨ b1, hb1 ⟩
      have hord : (b || b1) = true ↔ PathRel false ep ef := by
        rw [Bool.or_eq_true, hb, hb1, ← sliceBytes_inj, hprev, hpath]
        simp [PathRel]
      split
      · rename_i hot
        step*
        exact ⟨i3_post, by omega, by omega, fun k hk1 hk2 => hcont (hord.mp hot) k hk1 (by omega)⟩
      · rename_i hot
        simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
        exact hdone (fun h => hot (hord.mpr h))
    · simp only [↓reduceIte]
      step with bytes_lt_spec prev path as ⟨ b, hb ⟩
      have hord : b = true ↔ PathRel true ep ef := by
        rw [hb, hprev, hpath]
        simp [PathRel]
      split
      · rename_i hot
        step*
        exact ⟨i3_post, by omega, by omega, fun k hk1 hk2 => hcont (hord.mp hot) k hk1 (by omega)⟩
      · rename_i hot
        simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
        exact hdone (fun h => hot (hord.mpr h))
  · rename_i hge
    simp only [WP.spec_ok, true_iff]
    rw [orderedAs_iff_adjacent]
    exact fun k hk => hinv k hk (by scalar_tac)

/-! ## `parse_listing` -/

/-- The prefix of a record before `SP 0 TAB`. -/
theorem entryRecord_split (e : Entry) :
    entryRecord e = (e.mode ++ [32] ++ e.oid) ++ [32, 48, 9] ++ e.path := by
  simp [entryRecord]

/-- Records of entries with TAB-free six-byte modes and TAB-free object
    ids determine their entries. -/
theorem entryRecord_inj {e e' : Entry} (hm : e.mode.length = 6) (hm' : e'.mode.length = 6)
    (h9 : 9 ∉ e.mode) (h9' : 9 ∉ e'.mode) (ho : 9 ∉ e.oid) (ho' : 9 ∉ e'.oid)
    (h : entryRecord e = entryRecord e') : e = e' := by
  have hP : 9 ∉ e.mode ++ [32] ++ e.oid := by simp [h9, ho]
  have hP' : 9 ∉ e'.mode ++ [32] ++ e'.oid := by simp [h9', ho']
  have hpre : (e.mode ++ [32] ++ e.oid) ++ [32, 48, 9] <+:
      (e'.mode ++ [32] ++ e'.oid) ++ [32, 48, 9] ++ e'.path := by
    rw [← entryRecord_split, ← h, entryRecord_split]
    exact List.prefix_append _ _
  have heq := (tab_prefix_iff hP hP').mp hpre
  have hpath : e.path = e'.path := by
    have := h
    rw [entryRecord_split, entryRecord_split, heq] at this
    exact List.append_cancel_left this
  have hmode : e.mode = e'.mode := by
    have := congrArg (List.take 6) heq
    simpa [List.take_append_of_le_length, hm, hm'] using this
  have hoid : e.oid = e'.oid := by
    have := congrArg (List.drop 7) heq
    rwa [List.drop_left' (by simp [hm]), List.drop_left' (by simp [hm'])] at this
  cases e; cases e'
  simp_all

/-- `record_ok` accepts exactly the records of entries with a six-byte
    TAB-free mode, an object id and a nonempty path. -/
theorem record_ok_spec (entry : Slice U8) :
    record_ok entry ⦃ b => b = true ↔ ∃ e : Entry, sliceBytes entry = entryRecord e ∧
      e.mode.length = 6 ∧ 9 ∉ e.mode ∧ ObjectId e.oid ∧ e.path ≠ [] ⦄ := by
  unfold record_ok
  have hl := sliceBytes_length entry
  step with parse_index_entry_spec as ⟨ r, hr ⟩
  rcases r with parsed | x
  · simp only at hr ⊢
    obtain ⟨mode, oid, heq, hm, hne, h9m, h9o, hp, _⟩ := hr
    have hol : 0 < oid.length := List.length_pos_iff.mpr hne
    generalize hP : (sliceBytes entry).drop parsed.path_start.val = P at heq hp
    have hpl := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil, hm] at hpl
    have hPl : P.length = (sliceBytes entry).length - parsed.path_start.val := by
      rw [← hP, List.length_drop]
    have hPpos : 0 < P.length := List.length_pos_iff.mpr hp
    have hps : parsed.path_start.val = 10 + oid.length := by omega
    step as ⟨ i, hi ⟩
    step with index_range_spec entry 7#usize i (by simp; omega) (by omega) as ⟨ s, hs ⟩
    have hso : sliceBytes s = oid := by
      rw [hs, List.extract_eq_take_drop, heq, hi, hps]
      have : mode ++ [32] ++ oid ++ [32, 48, 9] ++ P = (mode ++ [32]) ++ (oid ++ ([32, 48, 9] ++ P)) := by
        simp
      rw [this, List.drop_left' (by simp [hm]), show 10 + oid.length - 3 - 7 = oid.length by omega]
      simp
    step with is_object_id_spec as ⟨ b, hb ⟩
    rw [hb, hso]
    constructor
    · intro hoid
      exact ⟨⟨mode, oid, P⟩, by rw [entryRecord, ← heq], hm, h9m, hoid, hp⟩
    · rintro ⟨e, he, hem, he9, heo, _⟩
      have hee : (⟨mode, oid, P⟩ : Entry) = e :=
        entryRecord_inj hm hem h9m he9 h9o (objectId_no_tab heo) (by rw [entryRecord, ← heq, he])
      rw [← hee] at heo
      exact heo
  · simp only at hr ⊢
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro e he hm h9 hoid hp
    apply hr (decide e.Regular) e.path
    rw [he]
    refine ⟨e.mode, e.oid, rfl, hm, fun h0 => by have := h0 ▸ hoid.1; simp at this, h9,
      objectId_no_tab hoid, hp, by simp [Entry.Regular]⟩

/-- The listing is Git's exact listing of these well-formed entries, with
    one `ends` slot per entry. -/
def ListingHyp (listing : Slice U8) (ends : Slice Usize) (es : List Entry) : Prop :=
  (∀ e ∈ es, EntryOk e) ∧ sliceBytes listing = listingBytes es ∧ ends.length = es.length

/-- Loop invariant of `parse_listing` after `i` records. -/
def ParseInv (listing : Slice U8) (ends fl : Slice Usize) (ok : Bool) (st i : Nat) : Prop :=
  i ≤ ends.length ∧ fl.length = ends.length ∧ st ≤ listing.length ∧
  (ok = true → ∃ pre : List Entry, pre.length = i ∧ (∀ e ∈ pre, EntryOk e) ∧
     (sliceBytes listing).take st = listingBytes pre ∧
     (∀ k (hk : k < pre.length), fl.val[k]!.val = off pre k + (entryRecord pre[k]).length) ∧
     (∀ es, ListingHyp listing ends es → pre = es.take i)) ∧
  (∀ es, ListingHyp listing ends es → ok = true)

theorem off_append_le (pre : List Entry) (e : Entry) {k : Nat} (hk : k ≤ pre.length) :
    off (pre ++ [e]) k = off pre k := by
  simp only [off, List.take_append_of_le_length hk]

theorem entryRecord_no_nul {e : Entry} (he : EntryOk e) : 0 ∉ entryRecord e := by
  obtain ⟨_, _, h0m, hoid, _, h0p⟩ := he
  have h0o : 0 ∉ e.oid := hoid.not_mem_of_lt (by decide)
  simp [entryRecord, h0m, h0o, h0p]

/-- Under Git's listing, record `i` ends at the first NUL after its start. -/
theorem hyp_record_end {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hy : ListingHyp listing ends es) {i : Nat} (hi : i < es.length) :
    (sliceBytes listing)[off es i + (entryRecord es[i]).length]! = 0 ∧
    off es i + (entryRecord es[i]).length < listing.length ∧
    ∀ k, off es i ≤ k → k < off es i + (entryRecord es[i]).length → (sliceBytes listing)[k]! ≠ 0 := by
  obtain ⟨hok, hb, _⟩ := hy
  have hd := listingBytes_drop es i hi
  rw [← hb] at hd
  have hn := entryRecord_no_nul (hok _ (List.getElem_mem hi))
  have hlen := congrArg List.length hd
  simp only [List.length_drop, List.length_append, List.length_cons, sliceBytes_length] at hlen
  refine ⟨?_, by omega, fun k hk1 hk2 h0 => hn ?_⟩
  · have := congrArg (·[(entryRecord es[i]).length]?) hd
    simp only [List.getElem?_drop, List.getElem?_append_right (le_refl _), Nat.sub_self,
      List.getElem?_cons_zero] at this
    exact ((getElem?_eq_some_iff' _ _ 0).mp this).2
  · have := congrArg (·[k - off es i]?) hd
    simp only [List.getElem?_drop, show off es i + (k - off es i) = k by omega,
      List.getElem?_append_left (show k - off es i < (entryRecord es[i]).length by omega)] at this
    rw [(getElem?_eq_some_iff' _ _ 0).mpr ⟨by rw [sliceBytes_length]; omega, h0⟩] at this
    exact List.mem_of_getElem? this.symm

/-- **The listing parser.** If `parse_listing` accepts, the listing is
    exactly Git's listing of well-formed entries, `ends` records where each
    record ends (`ListingOf`), and the paths are in byte order, each once if
    `unique` (`OrderedAs`: `Sorted`, else `PathOrdered`). Conversely, for
    Git's listing of any well-formed entries with one slot per entry it
    computes exactly their ends, and accepts exactly when they are in that
    order. -/
theorem parse_listing_spec (listing : Slice U8) (ends : Slice Usize) (unique : Bool) :
    parse_listing listing ends unique ⦃ r =>
      (r.1 = true → ∃ es, ListingOf listing r.2 es ∧ OrderedAs unique es) ∧
      (∀ es, ListingHyp listing ends es → ListingOf listing r.2 es ∧ (r.1 = true ↔ OrderedAs unique es)) ⦄ := by
  have hLl := sliceBytes_length listing
  have hmax := listing.property
  unfold parse_listing parse_listing_loop
  simp_len [bind_tc_ok]
  step with loop.spec_decr_nat
    (fun s : Slice Usize × Bool × Usize × Usize => 2 * (ends.length - s.2.2.2.val) + (if s.2.1 then 1 else 0))
    (fun s : Slice Usize × Bool × Usize × Usize => ParseInv listing ends s.1 s.2.1 s.2.2.1.val s.2.2.2.val)
    (fun s : Slice Usize × Bool × Usize => ParseInv listing ends s.1 s.2.1 s.2.2.val ends.length)
    as ⟨ fl, okr, st, hinv ⟩
  · rintro ⟨fl, ok, st, i⟩ ⟨h1, h2, h3, h4, h5⟩
    dsimp only at h1 h2 h3 h4 h5 ⊢
    unfold parse_listing_loop.body
    simp_len [bind_tc_ok]
    split
    · rename_i hok
      obtain ⟨pre, hpl, hpok, hpt, hpe, hph⟩ := h4 hok
      have hstp : (listingBytes pre).length = st.val := by
        rw [← hpt, List.length_take, hLl]; omega
      split
      · rename_i hil
        have hi : i.val < ends.length := by scalar_tac
        -- Under Git's listing, the next record is entry `i`, ending at the first NUL.
        have hyend : ∀ es, ListingHyp listing ends es → ∃ hi' : i.val < es.length,
            off es i.val = st.val ∧
            (sliceBytes listing)[st.val + (entryRecord es[i.val]).length]! = 0 ∧
            st.val + (entryRecord es[i.val]).length < listing.length ∧
            ∀ k, st.val ≤ k → k < st.val + (entryRecord es[i.val]).length → (sliceBytes listing)[k]! ≠ 0 := by
          intro es hy
          have hi' : i.val < es.length := by rw [← hy.2.2]; exact hi
          have hoff : off es i.val = st.val := by
            rw [off, ← hph es hy, hstp]
          obtain ⟨a, b, c⟩ := hyp_record_end hy hi'
          rw [hoff] at a b c
          exact ⟨hi', hoff, a, b, c⟩
        step with find_byte_spec as ⟨ en, hscan, hen ⟩
        obtain ⟨hs1, hs2, hs3⟩ := hscan
        -- Under Git's listing, `en` is where entry `i` ends.
        have hyen : ∀ es, ListingHyp listing ends es → ∃ hi' : i.val < es.length,
            en.val = st.val + (entryRecord es[i.val]).length ∧ en.val < listing.length := by
          intro es hy
          obtain ⟨hi', _, a, b, c⟩ := hyend es hy
          have hev : en.val = st.val + (entryRecord es[i.val]).length := by
            rcases Nat.lt_trichotomy en.val (st.val + (entryRecord es[i.val]).length) with h | h | h
            · exfalso
              exact c en.val (by simpa using hs1) h (by have := hen (by rw [← hLl] at b; omega); simpa using this)
            · exact h
            · exfalso
              exact hs3 _ (by omega) h (by simpa using a)
          exact ⟨hi', hev, by omega⟩
        split
        · rename_i hen_lt
          have henl : en.val < listing.length := by scalar_tac
          have hse : st.val ≤ en.val := by simpa using hs1
          step with index_range_spec listing st en hse (by omega) as ⟨ rec, hrec ⟩
          step with record_ok_spec as ⟨ b, hb ⟩
          have hnul : ∀ x ∈ (sliceBytes listing).extract st.val en.val, x ≠ 0 := by
            intro x hx h0
            subst h0
            have := extract_nul_free (sliceBytes listing) (st := st.val) (k := en.val)
              (fun j hj1 hj2 hj0 => hs3 j hj1 hj2 ((getElem?_eq_some_iff' _ _ 0).mp hj0).2)
            exact this hx
          split
          · rename_i hbt
            obtain ⟨e, he, hm, h9m, hoid, hp⟩ := hb.mp hbt
            rw [hrec] at he
            have hok' : EntryOk e := by
              refine ⟨hm, h9m, fun h0 => hnul 0 (by rw [he]; simp [entryRecord, h0]) rfl, hoid, hp,
                fun h0 => hnul 0 (by rw [he]; simp [entryRecord, h0]) rfl⟩
            step as ⟨ fl2, hfl2l, hfl2 ⟩
            step as ⟨ st2, hst2 ⟩
            step as ⟨ i3, hi3 ⟩
            have hfv : fl2.val = fl.val.set i.val en := by rw [hfl2]; rfl
            have henl' : en.val < (sliceBytes listing).length := by rw [hLl]; exact henl
            have hrl : (entryRecord e).length = en.val - st.val := by
              rw [← he, List.extract_eq_take_drop, List.length_take, List.length_drop, hLl]; omega
            refine And.intro ?_ (by rw [if_pos trivial]; have := hi3; have := hi; omega)
            unfold ParseInv
            refine ⟨by omega, by rw [← h2, Slice.length, hfv, List.length_set], by omega,
              fun _ => ⟨pre ++ [e], by simp [hpl, hi3], ?_, ?_, ?_, ?_⟩, fun _ _ => rfl⟩
            · intro x hx
              rcases List.mem_append.1 hx with hx | hx
              · exact hpok x hx
              · rw [List.mem_singleton.1 hx]; exact hok'
            · rw [hst2, take_succ_of_nul _ hse ((getElem?_eq_some_iff' _ _ 0).mpr
                ⟨henl', hen henl⟩), hpt, he, listingBytes_append]
              simp [listingBytes]
            · intro k hk
              rw [hfv]
              simp only [List.length_append, List.length_singleton] at hk
              rcases Nat.lt_or_ge k i.val with hlt | hge
              · rw [getElem!_set_ne' _ _ (by omega), off_append_le pre e (by omega),
                  List.getElem_append_left (by omega)]
                exact hpe k (by omega)
              · have hki : k = i.val := by omega
                subst hki
                rw [getElem!_set_self' _ _ (by simp [Slice.length] at h2 ⊢; omega),
                  off_append_le pre e (by omega), List.getElem_append_right (by omega)]
                simp only [hpl, Nat.sub_self, List.getElem_cons_zero, off, List.take_of_length_le
                  (le_of_eq hpl), hstp]
                omega
            · intro es hy
              obtain ⟨hi', hev, -⟩ := hyen es hy
              have hrec' : (sliceBytes listing).extract st.val en.val = entryRecord es[i.val] := by
                have hd := listingBytes_drop es i.val hi'
                rw [← hy.2.1, (hyend es hy).2.1] at hd
                rw [List.extract_eq_take_drop, hd, hev, show st.val + (entryRecord es[i.val]).length - st.val =
                  (entryRecord es[i.val]).length by omega]
                simp
              have hes : e = es[i.val] := by
                have hok2 := hy.1 _ (List.getElem_mem hi')
                exact entryRecord_inj hm hok2.1 h9m hok2.2.1 (objectId_no_tab hoid)
                  (objectId_no_tab hok2.2.2.2.1) (he.symm.trans hrec')
              rw [hph es hy, hes, hi3, List.take_add_one, List.getElem?_eq_getElem hi']
              rfl
          · rename_i hbt
            refine And.intro ?_ (by simp)
            unfold ParseInv
            refine ⟨h1, h2, h3, fun h => absurd h (by simp), fun es hy => ?_⟩
            exfalso
            obtain ⟨hi', hev, -⟩ := hyen es hy
            apply hbt
            apply hb.mpr
            have hok2 := hy.1 _ (List.getElem_mem hi')
            refine ⟨es[i.val], ?_, hok2.1, hok2.2.1, hok2.2.2.2.1, hok2.2.2.2.2.1⟩
            rw [hrec]
            have hd := listingBytes_drop es i.val hi'
            rw [← hy.2.1, (hyend es hy).2.1] at hd
            rw [List.extract_eq_take_drop, hd, hev, show st.val + (entryRecord es[i.val]).length - st.val =
              (entryRecord es[i.val]).length by omega]
            simp
        · rename_i hen_lt
          refine And.intro ?_ (by simp)
          unfold ParseInv
          refine ⟨h1, h2, h3, fun h => absurd h (by simp), fun es hy => ?_⟩
          exfalso
          obtain ⟨hi', hev, hlt⟩ := hyen es hy
          apply hen_lt
          scalar_tac
      · rename_i hil
        simp only [WP.spec_ok]
        have : i.val = ends.length := by scalar_tac
        rw [← this]
        exact ⟨h1, h2, h3, fun _ => h4 hok, fun _ _ => rfl⟩
    · rename_i hok
      simp only [WP.spec_ok]
      refine ⟨by scalar_tac, h2, h3, fun h => absurd h (by simp), fun es hy => absurd (h5 es hy) hok⟩
  · refine ⟨by simp, rfl, by simp, fun _ => ⟨[], rfl, by simp, by simp [listingBytes], by simp,
      fun _ _ => by simp⟩, fun _ _ => rfl⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
    split
    · rename_i hok
      obtain ⟨pre, hpl, hpok, hpt, hpe, hph⟩ := h4 hok
      -- Under Git's listing, the loop read exactly its entries.
      have hpre : ∀ es, ListingHyp listing ends es → pre = es := by
        intro es hy
        have hpe' := hph es hy
        rwa [hy.2.2, List.take_of_length_le (le_refl _)] at hpe'
      split
      · rename_i hst
        have hstv : st.val = listing.length := by scalar_tac
        have hLp : ListingOf listing fl pre :=
          ⟨hpok, by rw [← hpt, hstv, ← hLl, List.take_length], by rw [h2, hpl], hpe⟩
        step with listing_ordered_spec hLp unique as ⟨ b, hb ⟩
        refine ⟨fun hbt => ⟨pre, hLp, hb.mp hbt⟩, fun es hy => ?_⟩
        rw [← hpre es hy]
        exact ⟨hLp, hb⟩
      · rename_i hst
        simp only [WP.spec_ok]
        refine ⟨fun h => absurd h (by simp), fun es hy => ?_⟩
        exfalso
        apply hst
        have hpe' := hpre es hy
        subst hpe'
        have := congrArg List.length (hpt.trans hy.2.1.symm)
        rw [List.length_take, hLl] at this
        scalar_tac
    · rename_i hok
      simp only [WP.spec_ok]
      exact ⟨fun h => absurd h (by simp), fun es hy => absurd (h5 es hy) hok⟩

end Transcrypt.V3Verification

import V3Wire.Verification.SnapshotLookup

/-!
Git snapshot listings, part 5: lookups by object id. `object_order_ok`
accepts exactly an object order of a listing (`ObjectOrder`: each record
once, by object id then position), through which `next_move_source`
finds the first `MoveSource` of an entry and `blob_elsewhere` decides
`BlobElsewhere` for sorted listings.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core
open Transcrypt.V3Policy

/-! ## Object orders -/

/-- The key of record `j`: its object id, then its position. -/
def keyOf (es : List Entry) (j : Nat) : List Nat × Nat := ((es[j]?.map (·.oid)).getD [], j)

theorem keyOf_of_lt {es : List Entry} {j : Nat} (h : j < es.length) : keyOf es j = (es[j].oid, j) := by
  simp [keyOf, List.getElem?_eq_getElem h]

/-- Keys in order: by object id in byte order, then by position. -/
def KeyLt (a b : List Nat × Nat) : Prop := BytesLt a.1 b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

theorem keyLt_irrefl (a : List Nat × Nat) : ¬ KeyLt a a := by
  rintro (h | ⟨_, h⟩)
  · exact bytesLt_irrefl _ h
  · exact Nat.lt_irrefl _ h

theorem keyLt_trans {a b c : List Nat × Nat} (h1 : KeyLt a b) (h2 : KeyLt b c) : KeyLt a c := by
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact Or.inl (bytesLt_trans h1 h2)
  · exact Or.inl (e2 ▸ h1)
  · exact Or.inl (e1 ▸ h2)
  · exact Or.inr ⟨e1.trans e2, Nat.lt_trans h1 h2⟩

/-- `order` lists the records of `es` by key: one slot per record, every
    slot a position, and the keys strictly increase, so each record is
    listed exactly once (`ObjectOrder.surj`). -/
def ObjectOrder (es : List Entry) (order : Slice Usize) : Prop :=
  order.length = es.length ∧ (∀ t (h : t < order.length), order.val[t].val < es.length) ∧
  (order.val.map (fun j => keyOf es j.val)).Pairwise KeyLt

theorem ObjectOrder.lt {es : List Entry} {order : Slice Usize} (ho : ObjectOrder es order) {s t : Nat}
    (hst : s < t) (ht : t < order.length) :
    KeyLt (keyOf es (order.val[s]'(by simp [Slice.length] at ht; omega)).val)
      (keyOf es (order.val[t]'(by simpa [Slice.length] using ht)).val) := by
  have := List.pairwise_iff_getElem.mp ho.2.2 s t (by simp [Slice.length] at ht ⊢; omega)
    (by simpa [Slice.length] using ht) hst
  simpa using this

/-- Slots are ordered as their keys. -/
theorem ObjectOrder.lt_iff {es : List Entry} {order : Slice Usize} (ho : ObjectOrder es order) {s t : Nat}
    (hs : s < order.length) (ht : t < order.length) :
    KeyLt (keyOf es (order.val[s]'(by simpa [Slice.length] using hs)).val)
      (keyOf es (order.val[t]'(by simpa [Slice.length] using ht)).val) ↔ s < t := by
  constructor
  · intro h
    by_contra hge
    rcases Nat.lt_or_ge t s with hlt | hge'
    · exact keyLt_irrefl _ (keyLt_trans h (ho.lt hlt hs))
    · have : s = t := by omega
      subst this; exact keyLt_irrefl _ h
  · intro h; exact ho.lt h ht

/-- Every record has a slot (pigeonhole: the keys, so the positions, are
    distinct). -/
theorem ObjectOrder.surj {es : List Entry} {order : Slice Usize} (ho : ObjectOrder es order) {j : Nat}
    (hj : j < es.length) : ∃ t, ∃ h : t < order.length, (order.val[t]'(by simpa [Slice.length] using h)).val = j := by
  have hnd : (order.val.map (·.val)).Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro s t hs ht hst heq
    simp only [List.length_map] at hs ht
    have := ho.lt (s := s) (t := t) hst (by simpa [Slice.length] using ht)
    simp only [List.getElem_map] at heq
    rw [heq] at this
    exact keyLt_irrefl _ this
  have hmem := mem_of_nodup_lt hnd (by simp [← ho.1, Slice.length]) (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hy
    exact ho.2.1 t (by simpa [Slice.length] using ht)) hj
  obtain ⟨t, ht, htj⟩ := List.getElem_of_mem hmem
  simp only [List.length_map] at ht
  exact ⟨t, by simpa [Slice.length] using ht, by simpa using htj⟩

theorem object_before_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (j : Usize) (oid : Slice U8) (at_ : Usize) :
    object_before listing ends j oid at_ ⦃ b => b = true ↔
      j.val < es.length ∧ KeyLt (keyOf es j.val) (sliceBytes oid, at_.val) ⦄ := by
  unfold object_before
  step with listing_fields_spec hL j as ⟨ o, ho ⟩
  rcases o with _ | f
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
    simp only at ho
    intro h; omega
  · obtain ⟨hj, hf⟩ := ho
    obtain ⟨e, he, -, hoid, -, hf1, hf2, -, -⟩ := FieldsOf.slices hL hf
    have hej : es[j.val] = e := (List.getElem?_eq_some_iff.mp he).2
    simp only
    step as ⟨ i, hi ⟩
    step with index_range_spec listing i f.oid_end (by omega) hf2 as ⟨ id, hid ⟩
    rw [hi, hoid] at hid
    step with bytes_lt_spec id oid as ⟨ b, hb ⟩
    step with bytes_eq_spec id oid as ⟨ b1, hb1 ⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, hb, hb1, ← sliceBytes_inj,
      hid, keyOf_of_lt hj, hej, KeyLt, hj, true_and]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, by scalar_tac⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, by scalar_tac⟩

/-- **Object orders.** `object_order_ok` accepts exactly the object orders
    of the listing: each record once, by object id and then position. -/
theorem object_order_ok_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (order : Slice Usize) :
    object_order_ok listing ends order ⦃ b => b = true ↔ ObjectOrder es order ⦄ := by
  have hel := hL.ends_length
  unfold object_order_ok
  simp_len [bind_tc_ok]
  split
  · rename_i hne
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro ho
    simp_bne at hne
    apply hne
    apply UScalar.eq_of_val_eq
    have := ho.1
    simp only [Slice.length] at this
    simp [this, hel]
  · rename_i hne
    have hlen : order.length = es.length := by
      simp_bne at hne
      have := congrArg UScalar.val hne
      simp [hel] at this; simpa [Slice.length] using this
    unfold object_order_ok_loop
    apply compare_loop _ (fun n => (∀ t (h : t < order.val.length), t < n → order.val[t].val < es.length) ∧
        ∀ t (h : t + 1 < order.val.length), t + 1 < n →
          KeyLt (keyOf es order.val[t].val) (keyOf es order.val[t + 1].val))
      order.length _ _ 0#usize (by simp) ⟨fun t _ h => absurd h (by simp), fun t _ h => absurd h (by simp)⟩
    intro t ht ⟨hr, hk⟩
    unfold object_order_ok_loop.body
    simp_len [bind_tc_ok]
    split
    · rename_i htl
      have ht' : t.val < order.length := by scalar_tac
      step as ⟨ htv, j, hj ⟩
      step with listing_fields_spec hL j as ⟨ o, ho ⟩
      rcases o with _ | f
      · simp only at ho
        simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
        intro hord
        have := hord.2.1 t.val ht'
        rw [← hj] at this
        omega
      · obtain ⟨hjl, hf⟩ := ho
        obtain ⟨e, he, -, hoid, -, hf1, hf2, -, -⟩ := FieldsOf.slices hL hf
        have hej : es[j.val] = e := (List.getElem?_eq_some_iff.mp he).2
        simp only
        have hjt : order.val[t.val].val = j.val := by rw [hj]
        -- Slot `t` is a position; with the pair `(t - 1, t)` in order, the invariant extends.
        have hcont : (t.val = 0 ∨ KeyLt (keyOf es order.val[t.val - 1]!.val) (keyOf es j.val)) →
            (∀ s (h : s < order.val.length), s < t.val + 1 → order.val[s].val < es.length) ∧
            ∀ s (h : s + 1 < order.val.length), s + 1 < t.val + 1 →
              KeyLt (keyOf es order.val[s].val) (keyOf es order.val[s + 1].val) := by
          intro hpair
          refine ⟨fun s hs hst => ?_, fun s hs hst => ?_⟩
          · rcases Nat.lt_or_ge s t.val with hlt | hge
            · exact hr s hs hlt
            · have : s = t.val := by omega
              subst this; rw [hjt]; exact hjl
          · rcases Nat.lt_or_ge (s + 1) t.val with hlt | hge
            · exact hk s hs hlt
            · have hs1 : s + 1 = t.val := by omega
              rcases hpair with h0 | hpair
              · omega
              · have : order.val[s + 1] = order.val[t.val] := by simp [hs1]
                rw [this, hjt]
                rw [getElem!_pos order.val (t.val - 1) (by simp [Slice.length] at ht' ⊢; omega)] at hpair
                simpa [show t.val - 1 = s by omega] using hpair
        split
        · rename_i htp
          have ht0 : 0 < t.val := htp
          step as ⟨ i1, hi1 ⟩
          step as ⟨ hi1l, i2, hi2 ⟩
          step as ⟨ i3, hi3 ⟩
          step with index_range_spec listing i3 f.oid_end (by omega) hf2 as ⟨ s, hs ⟩
          rw [hi3, hoid] at hs
          step with object_before_spec hL i2 s j as ⟨ b, hb ⟩
          have hi2v : i2.val = order.val[t.val - 1]!.val := by
            rw [hi2, ← getElem!_pos order.val i1.val hi1l, hi1]
          rw [hi2v, hs, ← hej, ← keyOf_of_lt hjl] at hb
          split
          · rename_i hbt
            step*
            exact ⟨t1_post, by omega, by rw [t1_post]; exact hcont (Or.inr (hb.mp hbt).2)⟩
          · rename_i hbt
            simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
            intro hord
            apply hbt
            apply hb.mpr
            have ht1 : t.val - 1 < order.length := by omega
            refine ⟨hord.2.1 _ ht1 |>.trans_eq' (by rw [getElem!_pos order.val (t.val - 1) (by simp [Slice.length] at ht1 ⊢; omega)]), ?_⟩
            have := hord.lt (s := t.val - 1) (t := t.val) (by omega) ht'
            rw [getElem!_pos order.val (t.val - 1) (by simp [Slice.length] at ht1 ⊢; omega)]
            rwa [hjt] at this
        · rename_i htp
          have ht0 : ¬ 0 < t.val := htp
          step*
          exact ⟨t1_post, by omega, by rw [t1_post]; exact hcont (Or.inl (by omega))⟩
    · rename_i htl
      simp only [WP.spec_ok, true_iff]
      have htv : t.val = order.length := by scalar_tac
      refine ⟨hlen, fun s hs => hr s hs (by omega), ?_⟩
      apply pairwise_of_adjacent (R := KeyLt) (fun _ _ _ h1 h2 => keyLt_trans h1 h2)
      intro k hkl
      simp only [List.length_map] at hkl
      simpa using hk k hkl (by simp [Slice.length] at htv; omega)

/-- Slots before one whose key is before `X` have keys before `X`. -/
theorem ObjectOrder.lt_of_le {es : List Entry} {order : Slice Usize} (ho : ObjectOrder es order)
    {X : List Nat × Nat} {s t : Nat} (hst : s ≤ t) (ht : t < order.val.length)
    (h : KeyLt (keyOf es order.val[t].val) X) : KeyLt (keyOf es (order.val[s]'(by omega)).val) X := by
  rcases Nat.lt_or_ge s t with hlt | hge
  · exact keyLt_trans (ho.lt hlt ht) h
  · have : s = t := by omega
    subst this; exact h

/-- `find_object` is the first slot whose key is not before `(oid, at)`. -/
theorem find_object_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) {order : Slice Usize} (ho : ObjectOrder es order) (oid : Slice U8)
    (at_ : Usize) :
    find_object listing ends order oid at_ ⦃ r => r.val ≤ order.val.length ∧
      (∀ t (h : t < order.val.length), t < r.val → KeyLt (keyOf es order.val[t].val) (sliceBytes oid, at_.val)) ∧
      (∀ t (h : t < order.val.length), r.val ≤ t →
        ¬ KeyLt (keyOf es order.val[t].val) (sliceBytes oid, at_.val)) ⦄ := by
  unfold find_object find_object_loop
  simp_len [bind_tc_ok]
  apply loop.spec_decr_nat (fun s : Usize × Usize => s.2.val - s.1.val)
    (fun s : Usize × Usize => Bisects order.val.length
      (fun t _ => KeyLt (keyOf es order.val[t].val) (sliceBytes oid, at_.val)) s.1.val s.2.val)
  · rintro ⟨low, high⟩ hI
    dsimp only at hI ⊢
    unfold find_object_loop.body
    split
    · step as ⟨ d, hd ⟩
      step as ⟨ d2, hd2 ⟩
      step as ⟨ mid, hmid ⟩
      obtain ⟨hm1, hm2⟩ := bisect_midpoint (by scalar_tac) hd (by scalar_tac) hmid
      have hmo : mid.val < order.val.length := by have := hI.2.1; omega
      step as ⟨ hml, j, hj ⟩
      step with object_before_spec hL j oid at_ as ⟨ b, hb ⟩
      have hjv : j.val = order.val[mid.val].val := by rw [hj]
      rw [hjv] at hb
      have hjn : order.val[mid.val].val < es.length := ho.2.1 mid.val (by simpa [Slice.length] using hmo)
      split
      · rename_i hbt
        step as ⟨ low1, hlow1 ⟩
        exact hI.above ho.lt_of_le hm1 hm2 hmo (hb.mp hbt).2 hlow1
      · rename_i hbt
        simp only [WP.spec_ok]
        exact hI.below ho.lt_of_le hm1 hm2 hmo fun hlt => hbt (hb.mpr ⟨hjn, hlt⟩)
    · simp only [WP.spec_ok]
      exact hI.done (by scalar_tac)
  · simpa using Bisects.start

theorem names_oid_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (j : Usize) (oid : Slice U8) :
    names_oid listing ends j oid ⦃ b => b = true ↔ ∃ e, es[j.val]? = some e ∧ e.oid = sliceBytes oid ⦄ := by
  unfold names_oid
  step with listing_fields_spec hL j as ⟨ o, ho ⟩
  rcases o with _ | f
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro e he
    simp only at ho
    have := (List.getElem?_eq_some_iff.mp he).1
    omega
  · obtain ⟨_, hf⟩ := ho
    obtain ⟨e, he, -, hoid, -, hf1, hf2, -, -⟩ := FieldsOf.slices hL hf
    simp only
    step as ⟨ i, hi ⟩
    step with index_range_spec listing i f.oid_end (by omega) hf2 as ⟨ s, hs ⟩
    apply WP.spec_mono (bytes_eq_spec s oid)
    intro b hb
    rw [hb, ← sliceBytes_inj, hs, hi, hoid]
    exact ⟨fun h => ⟨e, he, h⟩, fun ⟨e', he', h⟩ => by rw [he] at he'; cases he'; exact h⟩

/-! ## Move sources -/

/-- The `HEAD` entry `h` holds the blob `oid` at another path than `path`,
    and the index does not hold it at `h`'s path. -/
def MovedFrom (es : List Entry) (oid path : List Nat) (h : Entry) : Prop :=
  h.oid = oid ∧ h.path ≠ path ∧ ¬ Holds es h.oid h.path

theorem move_source_at_spec {index head : Slice U8} {index_ends head_ends : Slice Usize}
    {es hs : List Entry} (hI : ListingOf index index_ends es) (hIo : PathOrdered es)
    (hH : ListingOf head head_ends hs)
    (oid path : Slice U8) (h9 : 9 ∉ sliceBytes oid) (j : Usize) (hj : j.val < hs.length) :
    move_source_at index index_ends head head_ends oid path j ⦃ b =>
      b = true ↔ MovedFrom es (sliceBytes oid) (sliceBytes path) hs[j.val] ⦄ := by
  obtain ⟨hdrop, hend, hok⟩ := hH.record hj
  have hel := hH.ends_length
  have hiel := hI.ends_length
  have hm := hok.1
  have hrl := entryRecord_length _ hm
  have hin := hH.off_le (Nat.succ_le_of_lt hj)
  rw [off_succ hs _ hj] at hin
  unfold move_source_at
  simp_len [bind_tc_ok]
  step with record_start_spec hH j (by omega) as ⟨ st, hst ⟩
  step as ⟨ hjl, x, hx ⟩
  have hxv : x.val = st.val + (entryRecord hs[j.val]).length := by
    rw [hx, ← getElem!_pos head_ends.val j.val hjl, hend, hst]
  step with record_is_spec head st x oid path false hs[j.val] _ hok (by rw [hst]; exact hdrop)
    hxv h9 as ⟨ b, hb ⟩
  simp only [Bool.false_eq_true, iff_false] at hb
  split
  · rename_i hbt
    obtain ⟨hoe, hpe⟩ := hb.mp hbt
    have hol : oid.length = hs[j.val].oid.length := by rw [← sliceBytes_length, hoe]
    have hD7 : (sliceBytes head).drop (st.val + 7) = hs[j.val].oid ++ [32, 48, 9] ++ hs[j.val].path ++
        (0 :: listingBytes (hs.drop (j.val + 1))) := by
      rw [← List.drop_drop, hst, hdrop, entryRecord_drop7 _ hm]
    have hD10 : (sliceBytes head).drop (st.val + 10 + hs[j.val].oid.length) =
        hs[j.val].path ++ (0 :: listingBytes (hs.drop (j.val + 1))) := by
      rw [show st.val + 10 + hs[j.val].oid.length = (st.val + 7) + (hs[j.val].oid.length + 3) by omega,
        ← List.drop_drop, hD7]
      simp
    have hsrc : (sliceBytes head).extract (st.val + 10 + oid.length) x.val = hs[j.val].path := by
      rw [List.extract_eq_take_drop, hxv, hrl, hol, hD10, show st.val + (hs[j.val].oid.length +
        hs[j.val].path.length + 10) - (st.val + 10 + hs[j.val].oid.length) = hs[j.val].path.length by omega]
      simp
    have hLl := sliceBytes_length head
    have hmax := head.property
    step as ⟨ i1, hi1 ⟩
    step as ⟨ i3, hi3 ⟩
    have hi3v : i3.val = st.val + 10 + oid.length := by rw [hi3, hi1]; simp
    step with index_range_spec head i3 x (by omega) (by omega) as ⟨ source, source_post ⟩
    rw [hi3v, hsrc] at source_post
    have h9' : 9 ∉ sliceBytes oid := h9
    step with find_entry_spec hI hIo oid source h9' as ⟨ r, hr1, hr2, hr3 ⟩
    simp only [decide_eq_true_eq]
    rw [source_post] at hr2 hr3
    unfold MovedFrom
    constructor
    · intro hr
      refine ⟨hoe, hpe, ?_⟩
      rw [hoe]
      exact hr3 (by have := congrArg UScalar.val hr; simpa [hiel] using this)
    · rintro ⟨-, -, hn⟩
      apply UScalar.eq_of_val_eq
      have hlenv : index_ends.len.val = es.length := by simp [hiel]
      rw [hlenv]
      rcases Nat.lt_or_ge r.val es.length with h | h
      · exfalso
        obtain ⟨e, he, ho, hp⟩ := hr2 h
        exact hn ⟨e, List.mem_of_getElem? he, by rw [ho, hoe], hp⟩
      · omega
  · rename_i hbt
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    rintro ⟨ho, hp, _⟩
    exact hbt (hb.mpr ⟨ho, hp⟩)

/-- The record in slot `s` of an object order, and its key. -/
theorem ObjectOrder.slot {es : List Entry} {order : Slice Usize} (ho : ObjectOrder es order) {s : Nat}
    (hs : s < order.val.length) : ∃ e, es[(order.val[s]).val]? = some e ∧
      keyOf es (order.val[s]).val = (e.oid, (order.val[s]).val) := by
  have hj := ho.2.1 s (by simpa [Slice.length] using hs)
  exact ⟨_, List.getElem?_eq_getElem hj, keyOf_of_lt hj⟩

/-- A record of `oid` at a position from `from` on is in a slot from the
    first slot not before `(oid, from)` on. -/
theorem ObjectOrder.slot_of {es : List Entry} {order : Slice Usize} (ho : ObjectOrder es order)
    {O : List Nat} {from_ t0 k : Nat} {e : Entry} (hk : es[k]? = some e) (he : e.oid = O) (hfk : from_ ≤ k)
    (hbefore : ∀ t (h : t < order.val.length), t < t0 → KeyLt (keyOf es order.val[t].val) (O, from_)) :
    ∃ s, ∃ h : s < order.val.length, (order.val[s]).val = k ∧ t0 ≤ s := by
  have hkl : k < es.length := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨s, hs, hsk⟩ := ho.surj hkl
  have hs' : s < order.val.length := by simpa [Slice.length] using hs
  refine ⟨s, hs', hsk, ?_⟩
  by_contra hlt
  have := hbefore s hs' (by omega)
  rw [hsk, keyOf_of_lt hkl, (List.getElem?_eq_some_iff.mp hk).2, he] at this
  rcases this with h | ⟨_, h⟩
  · exact bytesLt_irrefl _ h
  · simp only at h; omega

theorem move_source_from_spec {index head : Slice U8} {index_ends head_ends : Slice Usize}
    {es hs : List Entry} (hI : ListingOf index index_ends es) (hIo : PathOrdered es)
    (hH : ListingOf head head_ends hs) {order : Slice Usize} (ho : ObjectOrder hs order)
    (oid path : Slice U8) (h9 : 9 ∉ sliceBytes oid) (from_ : Nat) (hf : from_ ≤ hs.length) (t0 : Usize)
    (ht0 : t0.val ≤ order.val.length)
    (hbefore : ∀ t (h : t < order.val.length), t < t0.val →
      KeyLt (keyOf hs order.val[t].val) (sliceBytes oid, from_))
    (hafter : ∀ t (h : t < order.val.length), t0.val ≤ t →
      ¬ KeyLt (keyOf hs order.val[t].val) (sliceBytes oid, from_)) :
    move_source_from index index_ends head head_ends order oid path t0 ⦃ r =>
      FirstFrom hs (MovedFrom es (sliceBytes oid) (sliceBytes path)) from_ hs.length r.val ⦄ := by
  have hel := hH.ends_length
  have hol : order.val.length = hs.length := by have := ho.1; simpa [Slice.length] using this
  unfold move_source_from move_source_from_loop FirstFrom
  apply loop.spec_decr_nat (fun t : Usize => order.val.length - t.val)
    (fun t : Usize => t0.val ≤ t.val ∧ t.val ≤ order.val.length ∧
      ∀ s (h : s < order.val.length), t0.val ≤ s → s < t.val → ∀ e, hs[(order.val[s]).val]? = some e →
        e.oid = sliceBytes oid ∧ ¬ MovedFrom es (sliceBytes oid) (sliceBytes path) e)
  · intro t ⟨h1, h2, h3⟩
    unfold move_source_from_loop.body
    simp_len [bind_tc_ok]
    -- A record of `oid` from `from` on that is not in a slot before `t` is in no slot before a
    -- slot `t` whose record is not of `oid`.
    have hcover : ∀ k e, from_ ≤ k → hs[k]? = some e → e.oid = sliceBytes oid →
        (∀ htl : t.val < order.val.length, ∀ e', hs[(order.val[t.val]'htl).val]? = some e' →
          e'.oid ≠ sliceBytes oid) →
        ¬ MovedFrom es (sliceBytes oid) (sliceBytes path) e := by
      intro k e hfk hk he hnot
      obtain ⟨s, hs', hsk, hts⟩ := ho.slot_of hk he hfk hbefore
      rcases Nat.lt_or_ge s t.val with hlt | hge
      · exact (h3 s hs' hts hlt e (by rw [hsk]; exact hk)).2
      · exfalso
        have htl : t.val < order.val.length := by omega
        obtain ⟨e', he', hkey'⟩ := ho.slot htl
        apply hnot htl e' he'
        rcases Nat.lt_or_ge t.val s with hts' | hts'
        · have hkl := ho.lt (s := t.val) (t := s) hts' (by simpa [Slice.length] using hs')
          rw [hkey', hsk, keyOf_of_lt (List.getElem?_eq_some_iff.mp hk).1,
            (List.getElem?_eq_some_iff.mp hk).2, he] at hkl
          by_contra heq
          rcases hkl with hkl | ⟨hkl, _⟩
          · apply hafter t.val htl h1
            rw [hkey']
            exact Or.inl hkl
          · exact heq hkl
        · have : s = t.val := by omega
          subst this
          rw [hsk, hk] at he'
          cases he'
          exact he
    split
    · rename_i htl
      have htl' : t.val < order.val.length := by scalar_tac
      step as ⟨ htv, j, hj ⟩
      have hjv : j.val = (order.val[t.val]).val := by rw [hj]
      obtain ⟨ej, hej, hkey⟩ := ho.slot htl'
      rw [← hjv] at hej hkey
      have hjn : j.val < hs.length := (List.getElem?_eq_some_iff.mp hej).1
      have hejj : hs[j.val] = ej := (List.getElem?_eq_some_iff.mp hej).2
      step with names_oid_spec hH j oid as ⟨ b, hb ⟩
      rw [hej] at hb
      split
      · rename_i hbt
        obtain ⟨_, he1, hoid⟩ := hb.mp hbt
        cases he1
        step with move_source_at_spec hI hIo hH oid path h9 j hjn as ⟨ b1, hb1 ⟩
        rw [hejj] at hb1
        split
        · rename_i hb1t
          simp only [WP.spec_ok]
          have hfj : from_ ≤ j.val := by
            by_contra hlt
            apply hafter t.val htl' h1
            rw [← hjv, hkey, hoid]
            exact Or.inr ⟨rfl, by omega⟩
          refine ⟨hfj, by omega, fun k e hk1 hk2 hke hm => ?_, fun _ => ⟨ej, hej, hb1.mp hb1t⟩⟩
          have heo : e.oid = sliceBytes oid := hm.1
          obtain ⟨s, hs', hsk, hts⟩ := ho.slot_of hke heo hk1 hbefore
          have hkl : k < hs.length := (List.getElem?_eq_some_iff.mp hke).1
          have hst : s < t.val := by
            apply (ho.lt_iff (by simpa [Slice.length] using hs') (by simpa [Slice.length] using htl')).mp
            rw [hsk, ← hjv, keyOf_of_lt hkl, hkey, (List.getElem?_eq_some_iff.mp hke).2, heo, hoid]
            exact Or.inr ⟨rfl, hk2⟩
          exact (h3 s hs' hts hst e (by rw [hsk]; exact hke)).2 hm
        · rename_i hb1t
          step as ⟨ t1, ht1 ⟩
          refine ⟨by omega, by omega, fun s hs' hts hst e he => ?_, by omega⟩
          rcases Nat.lt_or_ge s t.val with hlt | hge
          · exact h3 s hs' hts hlt e he
          · have : s = t.val := by omega
            subst this
            rw [← hjv, hej] at he
            cases he
            exact ⟨hoid, fun hm => hb1t (hb1.mpr hm)⟩
      · rename_i hbt
        simp only [WP.spec_ok]
        have hnv : head_ends.len.val = hs.length := by simp [hel]
        rw [hnv]
        refine ⟨hf, le_refl _, fun k e hk1 hk2 hke hm => ?_, fun h => absurd h (by omega)⟩
        apply hcover k e hk1 hke hm.1 _ hm
        intro _ e' he' hoe
        rw [← hjv, hej] at he'
        cases he'
        exact hbt (hb.mpr ⟨_, rfl, hoe⟩)
    · rename_i htl
      have htv : t.val = order.val.length := by scalar_tac
      simp only [WP.spec_ok]
      have hnv : head_ends.len.val = hs.length := by simp [hel]
      rw [hnv]
      refine ⟨hf, le_refl _, fun k e hk1 hk2 hke hm => ?_, fun h => absurd h (by omega)⟩
      exact hcover k e hk1 hke hm.1 (fun h => absurd h (by omega)) hm
  · exact ⟨le_refl _, ht0, fun s _ h1 h2 => absurd h2 (by omega)⟩

/-- **Move sources.** `next_move_source` returns the first `HEAD` entry at
    or after `from` that the staged entry `i` may have been moved from
    (`MoveSource`: the same blob at another path, which has left the index),
    or `HEAD`'s length if there is none. It looks the blob up in an object
    order of `HEAD`. -/
theorem next_move_source_spec {index head : Slice U8} {index_ends head_ends : Slice Usize}
    {es hs : List Entry} (hI : ListingOf index index_ends es) (hIo : PathOrdered es)
    (hH : ListingOf head head_ends hs) {order : Slice Usize} (ho : ObjectOrder hs order)
    (i : Usize) (hi : i.val < es.length) (from_ : Usize) (hf : from_.val ≤ hs.length) :
    next_move_source index index_ends i head head_ends order from_ ⦃ r =>
      FirstFrom hs (MoveSource es es[i.val]) from_.val hs.length r.val ⦄ := by
  unfold next_move_source
  step with listing_fields_spec hI i as ⟨ o, ho' ⟩
  rcases o with _ | f
  · exfalso; simp only at ho'; omega
  · obtain ⟨_, hf'⟩ := ho'
    obtain ⟨e, he, hok, hoid, hpath, hf1, hf2, hf3, hf4⟩ := FieldsOf.slices hI hf'
    have hei : es[i.val] = e := (List.getElem?_eq_some_iff.mp he).2
    simp only
    step as ⟨ i1, hi1 ⟩
    step with index_range_spec index i1 f.oid_end (by omega) (by omega) as ⟨ so, hso ⟩
    step with index_range_spec index f.path_start f.end hf3 hf4 as ⟨ sp, hsp ⟩
    rw [hi1, hoid] at hso
    rw [hpath] at hsp
    have h9 : 9 ∉ sliceBytes so := by rw [hso]; exact objectId_no_tab hok.2.2.2.1
    step with find_object_spec hH ho so from_ as ⟨ t, ht1, ht2, ht3 ⟩
    apply WP.spec_mono (move_source_from_spec hI hIo hH ho so sp h9 from_.val hf t ht1 ht2 ht3)
    intro r hr
    have hP : ∀ h, MovedFrom es (sliceBytes so) (sliceBytes sp) h ↔ MoveSource es es[i.val] h := by
      intro h
      rw [hei, hso, hsp]
      rfl
    obtain ⟨r1, r2, r3, r4⟩ := hr
    refine ⟨r1, r2, fun k h hk1 hk2 hkh => (hP h).not.mp (r3 k h hk1 hk2 hkh), fun hlt => ?_⟩
    obtain ⟨h, hh, hm⟩ := r4 hlt
    exact ⟨h, hh, (hP h).mp hm⟩

/-! ## The keyless move check: `blob_elsewhere` -/

theorem other_path_at_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) {order : Slice Usize} (ho : ObjectOrder es order) (t : Usize)
    (oid path : Slice U8) (h9 : 9 ∉ sliceBytes oid) :
    other_path_at listing ends order t oid path ⦃ b => b = true ↔
      ∃ h : t.val < order.val.length, ∃ e, es[(order.val[t.val]'h).val]? = some e ∧
        e.oid = sliceBytes oid ∧ e.path ≠ sliceBytes path ⦄ := by
  have hel := hL.ends_length
  unfold other_path_at
  simp_len [bind_tc_ok]
  split
  · rename_i htl
    have htl' : t.val < order.val.length := by scalar_tac
    step as ⟨ htv, j, hj ⟩
    have hjv : j.val = (order.val[t.val]).val := by rw [hj]
    have hjn : j.val < es.length := by rw [hjv]; exact ho.2.1 t.val (by simpa [Slice.length] using htl')
    split
    · obtain ⟨hdrop, hend, hok⟩ := hL.record hjn
      step with record_start_spec hL j (by omega) as ⟨ st, hst ⟩
      step as ⟨ hjl, x, hx ⟩
      have hxv : x.val = st.val + (entryRecord es[j.val]).length := by
        rw [hx, ← getElem!_pos ends.val j.val hjl, hend, hst]
      apply WP.spec_mono (record_is_spec listing st x oid path false es[j.val] _ hok (by rw [hst]; exact hdrop)
        hxv h9)
      intro b hb
      rw [hb]
      simp only [Bool.false_eq_true, iff_false]
      constructor
      · rintro ⟨ho', hp⟩
        exact ⟨htl', es[j.val], by rw [← hjv]; simp, ho', hp⟩
      · rintro ⟨_, e, he, ho', hp⟩
        rw [← hjv, List.getElem?_eq_getElem hjn, Option.some.injEq] at he
        subst he
        exact ⟨ho', hp⟩
    · rename_i hjl
      exfalso; apply hjl; scalar_tac
  · rename_i htl
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_exists]
    intro h; exfalso; scalar_tac

/-- A sorted listing has the blob `oid` at another path than `path`
    exactly when `elsewhere_in` says so: its records of `oid` are together
    in the object order, at most one of them at `path`. -/
theorem elsewhere_in_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (hS : Sorted es) {order : Slice Usize} (ho : ObjectOrder es order)
    (oid path : Slice U8) (h9 : 9 ∉ sliceBytes oid) :
    elsewhere_in listing ends order oid path ⦃ b => b = true ↔
      ∃ e ∈ es, e.oid = sliceBytes oid ∧ e.path ≠ sliceBytes path ⦄ := by
  unfold elsewhere_in
  simp_len [bind_tc_ok]
  step with find_object_spec hL ho oid 0#usize as ⟨ t, ht1, ht2, ht3 ⟩
  have hbefore : ∀ s (h : s < order.val.length), s < t.val →
      KeyLt (keyOf es order.val[s].val) (sliceBytes oid, (0#usize).val) := ht2
  -- A slot from `t` on whose key is before a key of `oid` holds `oid`.
  have hoid_of : ∀ s (hs : s < order.val.length) k (hk : k < es.length), t.val ≤ s →
      KeyLt (keyOf es (order.val[s]).val) (es[k].oid, k) → es[k].oid = sliceBytes oid →
      ∃ e, es[(order.val[s]).val]? = some e ∧ e.oid = sliceBytes oid := by
    intro s hs k hk hts hkl hko
    obtain ⟨e, he, hkey⟩ := ho.slot hs
    refine ⟨e, he, ?_⟩
    rw [hkey, hko] at hkl
    rcases hkl with hkl | ⟨hkl, _⟩
    · exfalso
      apply ht3 s hs hts
      rw [hkey]
      exact Or.inl hkl
    · exact hkl
  split
  · rename_i htl
    have htl' : t.val < order.val.length := by scalar_tac
    step with other_path_at_spec hL ho t oid path h9 as ⟨ b, hb ⟩
    step as ⟨ t1, ht1v ⟩
    step with other_path_at_spec hL ho t1 oid path h9 as ⟨ b1, hb1 ⟩
    simp only [Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · obtain ⟨_, e, he, ho', hp⟩ := hb.mp h
        exact ⟨e, List.mem_of_getElem? he, ho', hp⟩
      · obtain ⟨_, e, he, ho', hp⟩ := hb1.mp h
        exact ⟨e, List.mem_of_getElem? he, ho', hp⟩
    · rintro ⟨e, hmem, ho', hp⟩
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
      obtain ⟨s, hs, hsk, hts⟩ := ho.slot_of (List.getElem?_eq_getElem hk) ho' (Nat.zero_le k) hbefore
      rcases Nat.lt_or_ge s (t.val + 2) with hlt | hge
      · rcases (by omega : s = t.val ∨ s = t.val + 1) with hst | hst
        · left
          refine hb.mpr ⟨htl', es[k], ?_, ho', hp⟩
          have : (order.val[t.val]'htl') = order.val[s] := by simp [hst]
          rw [this, hsk]; simp
        · right
          have ht1' : t1.val < order.val.length := by omega
          refine hb1.mpr ⟨ht1', es[k], ?_, ho', hp⟩
          have : (order.val[t1.val]'ht1') = order.val[s] := by simp [ht1v, hst]
          rw [this, hsk]; simp
      · -- Slots `t` and `t + 1` both hold `oid`, at distinct positions, so at distinct paths.
        have ht1' : t1.val < order.val.length := by omega
        have hkey_s : keyOf es (order.val[s]).val = (es[k].oid, k) := by rw [hsk, keyOf_of_lt hk]
        obtain ⟨e0, he0, ho0⟩ := hoid_of t.val htl' k hk (le_refl _)
          (by rw [← hkey_s]; exact ho.lt (by omega) (by simpa [Slice.length] using hs)) ho'
        obtain ⟨e1, he1, ho1⟩ := hoid_of t1.val ht1' k hk (by omega)
          (by rw [← hkey_s]; exact ho.lt (by omega) (by simpa [Slice.length] using hs)) ho'
        have hj0 := ho.2.1 t.val (by simpa [Slice.length] using htl')
        have hj1 := ho.2.1 t1.val (by simpa [Slice.length] using ht1')
        have hne : (order.val[t.val]).val ≠ (order.val[t1.val]).val := by
          intro heq
          have := ho.lt (s := t.val) (t := t1.val) (by omega) (by simpa [Slice.length] using ht1')
          rw [heq] at this
          exact keyLt_irrefl _ this
        have hpne := Sorted.path_ne hS hj0 hj1 hne
        rw [List.getElem?_eq_getElem hj0, Option.some.injEq] at he0
        rw [List.getElem?_eq_getElem hj1, Option.some.injEq] at he1
        by_cases h0 : e0.path = sliceBytes path
        · right
          refine hb1.mpr ⟨ht1', e1, by rw [List.getElem?_eq_getElem hj1, he1], ho1, fun h1 => hpne ?_⟩
          rw [he0, he1, h0, h1]
        · left
          exact hb.mpr ⟨htl', e0, by rw [List.getElem?_eq_getElem hj0, he0], ho0, h0⟩
  · rename_i htl
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro e hmem ho' hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨s, hs, hsk, hts⟩ := ho.slot_of (List.getElem?_eq_getElem hk) ho' (Nat.zero_le k) hbefore
    exfalso
    have : t.val ≥ order.val.length := by scalar_tac
    omega

/-- **Keyless move check.** `blob_elsewhere` says exactly whether the blob
    of entry `i` of the index is at another path in the index, `HEAD` or its
    parent (`BlobElsewhere`), for sorted listings with their object orders. -/
theorem blob_elsewhere_spec {index head parent : Slice U8} {index_ends head_ends parent_ends : Slice Usize}
    {es hs ps : List Entry} {index_order head_order parent_order : Slice Usize}
    (hI : ListingOf index index_ends es) (hIs : Sorted es) (hIo : ObjectOrder es index_order)
    (hH : ListingOf head head_ends hs) (hHs : Sorted hs) (hHo : ObjectOrder hs head_order)
    (hP : ListingOf parent parent_ends ps) (hPs : Sorted ps) (hPo : ObjectOrder ps parent_order)
    (i : Usize) (hi : i.val < es.length) :
    blob_elsewhere index index_ends index_order i head head_ends head_order parent parent_ends parent_order
      ⦃ b => b = true ↔ BlobElsewhere [es, hs, ps] es[i.val] ⦄ := by
  unfold blob_elsewhere
  step with listing_fields_spec hI i as ⟨ o, ho ⟩
  rcases o with _ | f
  · exfalso; simp only at ho; omega
  · obtain ⟨_, hf'⟩ := ho
    obtain ⟨e, he, hok, hoid, hpath, hf1, hf2, hf3, hf4⟩ := FieldsOf.slices hI hf'
    have hei : es[i.val] = e := (List.getElem?_eq_some_iff.mp he).2
    simp only
    step as ⟨ i1, hi1 ⟩
    step with index_range_spec index i1 f.oid_end (by omega) (by omega) as ⟨ so, hso ⟩
    step with index_range_spec index f.path_start f.end hf3 hf4 as ⟨ sp, hsp ⟩
    rw [hi1, hoid] at hso
    rw [hpath] at hsp
    have h9 : 9 ∉ sliceBytes so := by rw [hso]; exact objectId_no_tab hok.2.2.2.1
    step with elsewhere_in_spec hI hIs hIo so sp h9 as ⟨ b, hb ⟩
    step with elsewhere_in_spec hH hHs hHo so sp h9 as ⟨ b1, hb1 ⟩
    step with elsewhere_in_spec hP hPs hPo so sp h9 as ⟨ b2, hb2 ⟩
    simp only [Bool.or_eq_true, hb, hb1, hb2, hso, hsp, hei, BlobElsewhere, List.mem_cons,
      List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    simp only [or_assoc]

end Transcrypt.V3Verification

import V3Wire.Verification.Attr
import V3Wire.Verification.Index
import V3Wire.Verification.Envelope
import Transcrypt.V3Policy
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
namespace Transcrypt.V3Verification
open transcrypt_v3_core

/-!
Functional refinement of the production Git snapshot functions: the inputs
of the pre-commit decisions. `parse_listing` accepts exactly the listings
`Transcrypt.V3Policy.listingBytes es` of well-formed entries and records
where each record ends (`ListingOf`); every query over such a listing
computes the spec's predicate on its entries: `listing_fields` (the fields
of one entry), `held_entries` (`Holds`), `is_local_change` (`LocalChange`),
`next_move_source` (`MoveSource`, first at or after an offset),
`blob_elsewhere` (`BlobElsewhere`), `parse_listing_attrs` (Git's attribute
answer for exactly the listing's paths, `attrResponse`) and
`first_unselectable` (`Selectable`).
-/

/-! ## Pure facts about listings -/

section Pure
open Transcrypt.V3Policy

/-- Where record `i` of the listing of `es` starts. -/
def off (es : List Entry) (i : Nat) : Nat := (listingBytes (es.take i)).length

theorem listingBytes_append (a b : List Entry) :
    listingBytes (a ++ b) = listingBytes a ++ listingBytes b := by
  simp [listingBytes, List.flatMap_append]

theorem listingBytes_take_succ (es : List Entry) (i : Nat) (h : i < es.length) :
    listingBytes (es.take (i + 1)) = listingBytes (es.take i) ++ (entryRecord es[i] ++ [0]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, listingBytes_append]
  simp [listingBytes]

theorem off_zero (es : List Entry) : off es 0 = 0 := by simp [off, listingBytes]

theorem off_succ (es : List Entry) (i : Nat) (h : i < es.length) :
    off es (i + 1) = off es i + (entryRecord es[i]).length + 1 := by
  simp only [off, listingBytes_take_succ es i h, List.length_append, List.length_singleton]
  omega

theorem off_length (es : List Entry) : off es es.length = (listingBytes es).length := by
  simp [off]

theorem listingBytes_drop (es : List Entry) (i : Nat) (h : i < es.length) :
    (listingBytes es).drop (off es i) = entryRecord es[i] ++ 0 :: listingBytes (es.drop (i + 1)) := by
  have hs : listingBytes es = listingBytes (es.take i) ++ listingBytes (es.drop i) := by
    rw [← listingBytes_append, List.take_append_drop]
  have hd : es.drop i = es[i] :: es.drop (i + 1) := List.drop_eq_getElem_cons h
  rw [hs, off, List.drop_left, hd]
  simp only [listingBytes, List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem off_mono (es : List Entry) {i j : Nat} (h : i ≤ j) : off es i ≤ off es j := by
  unfold off
  have e : listingBytes (es.take j) =
      listingBytes ((es.take j).take i) ++ listingBytes ((es.take j).drop i) := by
    rw [← listingBytes_append, List.take_append_drop]
  rw [e, List.take_take, Nat.min_eq_left h, List.length_append]
  omega

theorem entryRecord_length (e : Entry) (he : e.mode.length = 6) :
    (entryRecord e).length = e.oid.length + e.path.length + 10 := by
  simp [entryRecord, he]; omega

/-- A record's tail after the mode and its space. -/
theorem entryRecord_drop7 (e : Entry) (he : e.mode.length = 6) (rest : List Nat) :
    (entryRecord e ++ rest).drop 7 = e.oid ++ [32, 48, 9] ++ e.path ++ rest := by
  have : entryRecord e ++ rest = (e.mode ++ [32]) ++ (e.oid ++ [32, 48, 9] ++ e.path ++ rest) := by
    simp [entryRecord]
  rw [this, List.drop_left' (by simp [he])]

/-- After `P ++ [32, 48, 9]` with TAB-free `P`, the first TAB is at `|P| + 2`. -/
theorem first_tab_of_prefix {P X : List Nat} (hP : 9 ∉ P) (h : P ++ [32, 48, 9] <+: X) :
    X[P.length + 2]? = some 9 ∧ ∀ k < P.length + 2, X[k]? ≠ some 9 := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨?_, fun k hk => ?_⟩
  · rw [List.getElem?_append_left (by simp), List.getElem?_append_right (by omega)]
    simp
  rw [List.getElem?_append_left (by simp; omega)]
  rcases Nat.lt_or_ge k P.length with hkP | hkP
  · rw [List.getElem?_append_left hkP]
    intro h9
    exact hP (List.mem_of_getElem? h9)
  · rw [List.getElem?_append_right hkP]
    rcases (by omega : k - P.length = 0 ∨ k - P.length = 1) with h0 | h0 <;> rw [h0] <;> simp

theorem first_index_unique {X : List Nat} {a b : Nat}
    (ha : X[a]? = some 9 ∧ ∀ k < a, X[k]? ≠ some 9)
    (hb : X[b]? = some 9 ∧ ∀ k < b, X[k]? ≠ some 9) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd ha.1 (hb.2 a h)
  · exact h
  · exact absurd hb.1 (ha.2 b h)

/-- An object id followed by `SP 0 TAB` is determined by the record it
    starts: TAB-free ids, so the first TAB is right after it. -/
theorem tab_prefix_iff {q o r : List Nat} (hq : 9 ∉ q) (ho : 9 ∉ o) :
    q ++ [32, 48, 9] <+: o ++ [32, 48, 9] ++ r ↔ q = o := by
  constructor
  · intro h
    have h1 := first_tab_of_prefix hq h
    have h2 := first_tab_of_prefix ho (List.prefix_append (o ++ [32, 48, 9]) r)
    have hl : q.length = o.length := by have := first_index_unique h1 h2; omega
    have hq1 : q <+: o ++ [32, 48, 9] ++ r := (List.prefix_append q _).trans h
    have ho1 : o <+: o ++ [32, 48, 9] ++ r :=
      (List.prefix_append o [32, 48, 9]).trans (List.prefix_append _ r)
    exact (List.prefix_of_prefix_length_le hq1 ho1 hl.le).eq_of_length hl
  · rintro rfl
    exact List.prefix_append _ _

end Pure

theorem OID_END_bytes : sliceBytes (Array.to_slice OID_END) = [32, 48, 9] := by
  unfold OID_END sliceBytes
  decide

open Transcrypt.V3Policy in
/-- `listing` is exactly the listing of the well-formed entries `es`, and
    `ends[i]` is where record `i` ends (the position of its NUL). -/
def ListingOf (listing : Slice U8) (ends : Slice Usize) (es : List Transcrypt.V3Policy.Entry) : Prop :=
  (∀ e ∈ es, EntryOk e) ∧ sliceBytes listing = listingBytes es ∧ ends.length = es.length ∧
  ∀ i (h : i < es.length), ends.val[i]!.val = off es i + (entryRecord es[i]).length

theorem ListingOf.off_le {listing : Slice U8} {ends : Slice Usize} {es : List Transcrypt.V3Policy.Entry}
    (hL : ListingOf listing ends es) {i : Nat} (hi : i ≤ es.length) : off es i ≤ listing.length := by
  have := off_mono es hi
  rw [off_length, ← hL.2.1, sliceBytes_length] at this
  exact this

@[step]
theorem record_start_spec {listing : Slice U8} {ends : Slice Usize} {es : List Transcrypt.V3Policy.Entry}
    (hL : ListingOf listing ends es) (i : Usize) (hi : i.val ≤ es.length) :
    record_start ends i ⦃ s => s.val = off es i.val ⦄ := by
  unfold record_start
  split
  · rename_i h0
    simp [h0, off_zero]
  · rename_i h0
    have hi0 : 0 < i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exact absurd (UScalar.eq_of_val_eq (by simpa using h)) h0
      · exact h
    have hmax := listing.property
    have hle := hL.off_le hi
    have hk : (ends.val[i.val - 1]!).val + 1 = off es i.val := by
      rw [hL.2.2.2 (i.val - 1) (by omega), ← off_succ es _ (by omega)]
      congr 1; omega
    have hlen : ends.length = es.length := hL.2.2.1
    step as ⟨ i1, hi1 ⟩
    step as ⟨ hi1l, x, hx ⟩
    have hxv : x.val + 1 = off es i.val := by
      rw [← hk, hx, ← getElem!_pos ends.val i1.val hi1l, hi1]
    step*

theorem record_is_spec (listing : Slice U8) (start end_ : Usize) (oid path : Slice U8) (same : Bool)
    (e : Transcrypt.V3Policy.Entry) (rest : List Nat) (he : Transcrypt.V3Policy.EntryOk e)
    (hd : (sliceBytes listing).drop start.val = Transcrypt.V3Policy.entryRecord e ++ rest)
    (ht : end_.val = start.val + (Transcrypt.V3Policy.entryRecord e).length)
    (h9 : 9 ∉ sliceBytes oid) :
    record_is listing start end_ oid path same ⦃ b =>
      b = true ↔ (e.oid = sliceBytes oid ∧ (e.path = sliceBytes path ↔ same = true)) ⦄ := by
  obtain ⟨hm, h9m, h0m, hoid, hp, h0p⟩ := he
  have hrl := entryRecord_length e hm
  have hLl := sliceBytes_length listing
  have hin : start.val + (Transcrypt.V3Policy.entryRecord e).length ≤ listing.length := by
    have := congrArg List.length hd
    simp only [List.length_drop, List.length_append, hLl] at this
    have hpos : 0 < e.path.length := List.length_pos_iff.mpr hp
    omega
  have h9o : 9 ∉ e.oid := fun h => by
    rcases hoid.2 9 h with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
  have hD : (sliceBytes listing).drop (start.val + 7) = e.oid ++ [32, 48, 9] ++ e.path ++ rest := by
    rw [← List.drop_drop, hd, entryRecord_drop7 e hm]
  -- If the record names `oid`, it starts with `oid SP 0 TAB`.
  have hnames : e.oid = sliceBytes oid →
      sliceBytes oid ++ [32, 48, 9] <+: (sliceBytes listing).drop (start.val + 7) := by
    intro h
    rw [hD, ← h, List.append_assoc]
    exact List.prefix_append _ _
  have hol : e.oid = sliceBytes oid → oid.length = e.oid.length := by
    intro h; rw [h, sliceBytes_length]
  have hlenv : oid.len.val = oid.length := by simp
  have hb_of : e.oid = sliceBytes oid → start.val + 7 ≤ listing.length ∧
      sliceBytes oid <+: (sliceBytes listing).drop (start.val + 7) := fun h =>
    ⟨by scalar_tac, (List.prefix_append _ _).trans (hnames h)⟩
  have hb1_of : e.oid = sliceBytes oid → start.val + 7 + oid.length ≤ listing.length ∧
      [32, 48, 9] <+: (sliceBytes listing).drop (start.val + 7 + oid.length) := by
    intro h
    have := hnames h
    rw [prefix_append_iff, List.drop_drop, sliceBytes_length] at this
    exact ⟨by have := hol h; scalar_tac, this.2⟩
  unfold record_is
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hmax := listing.property
  step*
  -- (`step*` refutes a record too short for `oid` and a mismatching id with
  -- `hol` and `hb_of`.)
  -- `SP 0 TAB` does not follow: the record names another object.
  case h2 =>
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro h _
    apply ‹¬b1 = true›
    rw [b1_post, s_post, OID_END_bytes, at_post, i4_post, hlenv]
    exact hb1_of h
  -- The record names `oid`: compare the path.
  have hoid' : sliceBytes oid = e.oid := by
    have h1 := (b_post.mp ‹b = true›).2
    have h2 := (b1_post.mp ‹b1 = true›).2
    rw [s_post, OID_END_bytes, at_post, i4_post, hlenv, ← sliceBytes_length oid, ← List.drop_drop] at h2
    rw [i4_post] at h1
    have := (prefix_append_iff (sliceBytes oid) [32, 48, 9] _).mpr ⟨h1, h2⟩
    rw [hD] at this
    exact (tab_prefix_iff h9 h9o).mp (by simpa only [List.append_assoc] using this)
  have hpl : i6.val = e.path.length := by
    rw [i6_post1, i5_post1, at_post, i4_post, ht, hrl, hlenv, ← sliceBytes_length oid, hoid']
    omega
  have hP : (sliceBytes listing).drop («at».val + 3) = e.path ++ rest := by
    rw [at_post, i4_post, hlenv, ← sliceBytes_length oid, hoid', show start.val + 7 + e.oid.length + 3 =
      (start.val + 7) + (e.oid.length + 3) by omega, ← List.drop_drop, hD]
    simp
  split
  · rename_i hi6
    have hpl' : path.length = e.path.length := by
      rw [← hpl]; have := congrArg UScalar.val hi6; simpa using this.symm
    step*
    rw [x_post, hP] at here_post
    have hiff : here = true ↔ e.path = sliceBytes path := by
      rw [here_post]
      constructor
      · rintro ⟨_, hpre⟩
        have hlen : (sliceBytes path).length = e.path.length := by rw [sliceBytes_length, hpl']
        exact ((List.prefix_of_prefix_length_le hpre (List.prefix_append _ _) hlen.le).eq_of_length
          hlen).symm
      · intro h
        have hxl : «at».val + 3 ≤ listing.length := by
          have := i6_post2; have := i5_post1; have := i5_post2
          omega
        refine ⟨hxl, ?_⟩
        rw [← h]; exact List.prefix_append _ _
    rw [decide_eq_true_iff, Bool.eq_iff_iff, hiff]
    exact ⟨fun h => ⟨hoid'.symm, h⟩, fun h => h.2⟩
  · rename_i hi6
    have hne : e.path ≠ sliceBytes path := by
      intro h
      apply hi6
      apply UScalar.eq_of_val_eq
      rw [hpl, h, sliceBytes_length]; simp
    simp only [bind_tc_ok, WP.spec_ok]
    rw [decide_eq_true_iff, Bool.eq_iff_iff]
    constructor
    · intro h
      refine ⟨hoid'.symm, ⟨fun hp => absurd hp hne, fun hs => ?_⟩⟩
      exact absurd (h.mpr hs) (by simp)
    · rintro ⟨_, hps⟩
      exact ⟨fun h => absurd h (by simp), fun hs => absurd (hps.mpr hs) hne⟩

open Transcrypt.V3Policy

/-- Record `j` of a listing: where it lies, where it ends, and that it is
    well formed. -/
theorem ListingOf.record {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) {j : Nat} (hj : j < es.length) :
    (sliceBytes listing).drop (off es j) = entryRecord es[j] ++ 0 :: listingBytes (es.drop (j + 1)) ∧
    ends.val[j]!.val = off es j + (entryRecord es[j]).length ∧ EntryOk es[j] := by
  refine ⟨?_, hL.2.2.2 j hj, hL.1 _ (List.getElem_mem hj)⟩
  rw [hL.2.1]; exact listingBytes_drop es j hj

theorem ListingOf.ends_length {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) : ends.val.length = es.length := hL.2.2.1

/-- An entry of the listing names `oid` at `path` (`same`), or at another
    path (`!same`). -/
def Named (oid path : List Nat) (same : Bool) (e : Entry) : Prop :=
  e.oid = oid ∧ (e.path = path ↔ same = true)

/-- `r` is the first position in `[from, to)` whose entry satisfies `P`, or
    `to` if there is none. -/
def FirstFrom (es : List Entry) (P : Entry → Prop) (from_ to_ r : Nat) : Prop :=
  from_ ≤ r ∧ r ≤ to_ ∧ (∀ k e, from_ ≤ k → k < r → es[k]? = some e → ¬ P e) ∧
    (r < to_ → ∃ e, es[r]? = some e ∧ P e)

/-- An object id of a well-formed entry contains no TAB. -/
theorem objectId_no_tab {oid : List Nat} (h : ObjectId oid) : 9 ∉ oid := fun h9 => by
  rcases h.2 9 h9 with ⟨_, h⟩ | ⟨h, _⟩ <;> omega

theorem scan_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (oid path : Slice U8) (same : Bool) (h9 : 9 ∉ sliceBytes oid)
    (from_ to_ : Usize) (hft : from_.val ≤ to_.val) (hto : to_.val ≤ es.length) :
    scan listing ends from_ to_ oid path same ⦃ r =>
      FirstFrom es (Named (sliceBytes oid) (sliceBytes path) same) from_.val to_.val r.val ⦄ := by
  unfold scan scan_loop FirstFrom
  apply loop.spec_decr_nat (fun s => 2 * (to_.val - s.1.val) + (if s.2 then 0 else 1))
    (fun s => from_.val ≤ s.1.val ∧ s.1.val ≤ to_.val ∧
      (∀ k e, from_.val ≤ k → k < s.1.val → es[k]? = some e →
        ¬ Named (sliceBytes oid) (sliceBytes path) same e) ∧
      (s.2 = true → s.1.val < to_.val ∧
        ∃ e, es[s.1.val]? = some e ∧ Named (sliceBytes oid) (sliceBytes path) same e))
  · rintro ⟨j, found⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4 ⊢
    unfold scan_loop.body
    split
    · rename_i hf
      simp only [WP.spec_ok]
      exact ⟨h1, h2, h3, fun _ => (h4 hf).2⟩
    · rename_i hf
      split
      · rename_i hjt
        have hjt' : j.val < to_.val := by scalar_tac
        have hj : j.val < es.length := by omega
        obtain ⟨hdrop, hend, hok⟩ := hL.record hj
        have hel := hL.ends_length
        step with record_start_spec hL j (by omega) as ⟨ st, hst ⟩
        step as ⟨ hjl, x, hx ⟩
        have hxv : x.val = st.val + (entryRecord es[j.val]).length := by
          rw [hx, ← getElem!_pos ends.val j.val hjl, hend, hst]
        step with record_is_spec listing st x oid path same es[j.val] _ hok (by rw [hst]; exact hdrop)
          hxv h9 as ⟨ b, hb ⟩
        split
        · rename_i hbt
          simp only [WP.spec_ok]
          exact ⟨h1, h2, h3, fun _ => ⟨hjt', es[j.val], by simp, hb.mp hbt⟩, by simp⟩
        · rename_i hbt
          step as ⟨ j1, hj1 ⟩
          refine ⟨by omega, by omega, fun k e hk1 hk2 hke => ?_, fun h => absurd h (by simp),
            by simp only [Bool.false_eq_true, if_false]; omega⟩
          rcases Nat.lt_or_ge k j.val with hlt | hge
          · exact h3 k e hk1 hlt hke
          · have hkj : k = j.val := by omega
            subst hkj
            rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hke
            subst hke
            exact fun hn => hbt (hb.mpr hn)
      · rename_i hjt
        simp only [WP.spec_ok]
        have hjt' : to_.val ≤ j.val := by scalar_tac
        refine ⟨h1, h2, h3, fun h => absurd h (by omega)⟩
  · refine ⟨le_refl _, hft, fun k e hk1 hk2 => by dsimp only at hk2; omega, fun h => absurd h (by simp)⟩

/-- `find_entry` finds a record that names `oid` at `path` if there is one,
    whatever the hint. -/
theorem find_entry_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (oid path : Slice U8) (h9 : 9 ∉ sliceBytes oid) (hint : Usize) :
    find_entry listing ends oid path hint ⦃ r => r.val ≤ es.length ∧
      (r.val < es.length → ∃ e, es[r.val]? = some e ∧ e.oid = sliceBytes oid ∧ e.path = sliceBytes path) ∧
      (r.val = es.length → ¬ Holds es (sliceBytes oid) (sliceBytes path)) ⦄ := by
  have hel := hL.ends_length
  have hnamed : ∀ e, Named (sliceBytes oid) (sliceBytes path) true e ↔
      e.oid = sliceBytes oid ∧ e.path = sliceBytes path := by
    intro e; simp [Named]
  have hn : ends.len.val = es.length := by simp [← hel]
  have rest : ∀ f : Usize, f.val ≤ es.length →
      (do
        let j ← scan listing ends f ends.len oid path true
        if j < ends.len then ok j
        else
          let k ← scan listing ends 0#usize f oid path true
          if k < f then ok k else ok ends.len : RustM Usize) ⦃ r => r.val ≤ es.length ∧
        (r.val < es.length → ∃ e, es[r.val]? = some e ∧ e.oid = sliceBytes oid ∧ e.path = sliceBytes path) ∧
        (r.val = es.length → ¬ Holds es (sliceBytes oid) (sliceBytes path)) ⦄ := by
    intro f hf
    step with scan_spec hL oid path true h9 f ends.len (by omega) (by omega) as ⟨ j, hj ⟩
    obtain ⟨hj1, hj2, hj3, hj4⟩ := hj
    split
    · rename_i hjn
      have hjn' : j.val < es.length := by scalar_tac
      simp only [WP.spec_ok]
      obtain ⟨e, he, hne⟩ := hj4 (by omega)
      exact ⟨by omega, fun _ => ⟨e, he, (hnamed e).mp hne⟩, fun h => absurd h (by omega)⟩
    · rename_i hjn
      have hjv : j.val = es.length := by scalar_tac
      step with scan_spec hL oid path true h9 0#usize f (by simp) hf as ⟨ k, hk ⟩
      obtain ⟨hk1, hk2, hk3, hk4⟩ := hk
      split
      · rename_i hkf
        have hkf' : k.val < f.val := by scalar_tac
        simp only [WP.spec_ok]
        obtain ⟨e, he, hne⟩ := hk4 hkf'
        exact ⟨by omega, fun _ => ⟨e, he, (hnamed e).mp hne⟩, fun h => absurd h (by omega)⟩
      · rename_i hkf
        have hkf' : f.val ≤ k.val := by scalar_tac
        simp only [WP.spec_ok]
        refine ⟨by omega, fun h => absurd h (by omega), fun _ => ?_⟩
        rintro ⟨e, hmem, ho, hp⟩
        obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
        rcases Nat.lt_or_ge m f.val with hlt | hge
        · exact hk3 m _ (by simp) (by omega) (List.getElem?_eq_getElem hm) ((hnamed _).mpr ⟨ho, hp⟩)
        · exact hj3 m _ hge (by omega) (List.getElem?_eq_getElem hm) ((hnamed _).mpr ⟨ho, hp⟩)
  unfold find_entry
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  by_cases hh : hint < ends.len
  · simp only [hh, if_true, bind_tc_ok]
    exact rest hint (by scalar_tac)
  · simp only [hh, if_false, bind_tc_ok]
    exact rest ends.len (by omega)

/-! ## `listing_fields` -/

/-- The first TAB of a record is right after its object id and `SP 0`. -/
theorem record_tab {L : List Nat} {s : Nat} {e : Entry} {rest : List Nat} (he : EntryOk e)
    (hd : L.drop s = entryRecord e ++ rest) :
    s + 9 + e.oid.length < L.length ∧ L[s + 9 + e.oid.length]! = 9 ∧
      ∀ k, s ≤ k → k < s + 9 + e.oid.length → L[k]! ≠ 9 := by
  obtain ⟨hm, h9m, _, hoid, hp, _⟩ := he
  have h9o := objectId_no_tab hoid
  have hP : 9 ∉ e.mode ++ [32] ++ e.oid := by simp [h9m, h9o]
  have hpre : e.mode ++ [32] ++ e.oid ++ [32, 48, 9] <+: L.drop s := by
    rw [hd]
    exact (List.prefix_append _ e.path).trans (by simp [entryRecord])
  obtain ⟨h1, h2⟩ := first_tab_of_prefix hP hpre
  have hl : (e.mode ++ [32] ++ e.oid).length + 2 = 9 + e.oid.length := by simp [hm]; omega
  rw [hl, List.getElem?_drop, show s + (9 + e.oid.length) = s + 9 + e.oid.length by omega] at h1
  have hlt := (List.getElem?_eq_some_iff.mp h1).1
  refine ⟨by omega, ((getElem?_eq_some_iff' L _ 9).mp h1).2, fun k hk1 hk2 h9 => ?_⟩
  apply h2 (k - s) (by omega)
  rw [List.getElem?_drop, show s + (k - s) = k by omega]
  exact (getElem?_eq_some_iff' L k 9).mpr ⟨by omega, h9⟩

/-- A six-byte mode is a prefix of a record exactly when it is its mode. -/
theorem record_mode {L : List Nat} {s : Nat} {e : Entry} {rest : List Nat} (he : e.mode.length = 6)
    (hd : L.drop s = entryRecord e ++ rest) (M : List Nat) (hM : M.length = 6) :
    M <+: L.drop s ↔ e.mode = M := by
  rw [hd, show entryRecord e ++ rest = e.mode ++ ([32] ++ e.oid ++ [32, 48, 9] ++ e.path ++ rest) by
    simp [entryRecord]]
  constructor
  · intro h
    have := List.prefix_of_prefix_length_le h (List.prefix_append e.mode _) (by omega)
    exact (this.eq_of_length (by omega)).symm
  · rintro rfl
    exact List.prefix_append _ _

/-- What `listing_fields` returns for record `i`: its offsets (the object id
    is `[start + 7, oid_end)`, the path `[path_start, end)`) and whether its
    mode is regular. -/
def FieldsOf (es : List Entry) (i : Nat) (f : Fields) : Prop :=
  ∃ e, es[i]? = some e ∧ f.start.val = off es i ∧ f.oid_end.val = off es i + 7 + e.oid.length ∧
    f.path_start.val = off es i + 10 + e.oid.length ∧
    f.end.val = off es i + (entryRecord e).length ∧ (f.regular = true ↔ e.Regular)

@[step]
theorem listing_fields_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (i : Usize) :
    listing_fields listing ends i ⦃ o => match o with
      | none => es.length ≤ i.val
      | some f => i.val < es.length ∧ FieldsOf es i.val f ⦄ := by
  have hel := hL.ends_length
  unfold listing_fields
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  split
  · rename_i hge
    simp only [WP.spec_ok]
    scalar_tac
  · rename_i hlt
    have hi : i.val < es.length := by scalar_tac
    obtain ⟨hdrop, hend, hok⟩ := hL.record hi
    obtain ⟨tl, tv, tno⟩ := record_tab hok hdrop
    have hm := hok.1
    have hoidl : 40 ≤ es[i.val].oid.length := by rcases hok.2.2.2.1.1 with h | h <;> omega
    have hLl := sliceBytes_length listing
    have hin := hL.off_le (Nat.succ_le_of_lt hi)
    rw [off_succ es _ hi] at hin
    step with record_start_spec hL i (by omega) as ⟨ st, hst ⟩
    step as ⟨ hil, x, hx ⟩
    have hxv : x.val = st.val + (entryRecord es[i.val]).length := by
      rw [hx, ← getElem!_pos ends.val i.val hil, hend, hst]
    have hrl := entryRecord_length _ hm
    step with find_byte_spec as ⟨ tab, hscan, htab ⟩
    obtain ⟨ht1, ht2, ht3⟩ := hscan
    have htv : tab.val = st.val + 9 + es[i.val].oid.length := by
      rcases Nat.lt_trichotomy tab.val (st.val + 9 + es[i.val].oid.length) with h | h | h
      · exfalso
        have := htab (by rw [hLl] at tl; rw [← hst] at tl; omega)
        exact tno tab.val (by omega) (by omega) (by simpa using this)
      · exact h
      · exfalso
        exact ht3 _ (by omega) h (by rw [hst]; simpa using tv)
    rw [← hst] at hdrop
    have hmode : ∀ (M : Std.Array U8 6#usize) (m : List Nat), M.val.map (·.val) = m → ∀ c : Bool,
        (c = true ↔ st.val ≤ listing.length ∧
          sliceBytes (Array.to_slice M) <+: (sliceBytes listing).drop st.val) →
        (c = true ↔ es[i.val].mode = m) := by
      intro M m hM c hc
      have hs : sliceBytes (Array.to_slice M) = m := by rw [← hM]; rfl
      have hml : m.length = 6 := by rw [← hM]; simp
      rw [hc, hs, record_mode hm hdrop m hml]
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    step*
    have hb' := hmode _ _ REGULAR_MODE_matches_spec b (by rw [← s_post]; exact b_post)
    have hpost : ∀ (regular : Bool), (regular = true ↔ es[i.val].Regular) →
        (do
          let i4 ← tab - 2#usize
          let i5 ← tab + 1#usize
          ok (core.option.Option.Some
            { start := st, oid_end := i4, path_start := i5, «end» := x, regular := regular }) :
            RustM (core.option.Option Fields)) ⦃ o => match o with
          | core.option.Option.None => es.length ≤ i.val
          | core.option.Option.Some f => i.val < es.length ∧ FieldsOf es i.val f ⦄ := by
      intro regular hr
      step*
      refine ⟨hi, es[i.val], by simp, hst, ?_, ?_, by rw [hxv, hst], hr⟩
      · rw [i4_post1, htv, hst]; omega
      · rw [i5_post, htv, hst]; omega
    split
    · rename_i hbt
      simp only [bind_tc_ok]
      exact hpost true ⟨fun _ => Or.inl (hb'.mp hbt), fun _ => rfl⟩
    · rename_i hbt
      step as ⟨ s1, hs1 ⟩
      step with matches_at_spec as ⟨ b1, hb1 ⟩
      have hb1' := hmode _ _ EXECUTABLE_MODE_matches_spec b1 (by rw [← hs1]; exact hb1)
      apply hpost b1
      rw [hb1']
      constructor
      · exact Or.inr
      · rintro (h | h)
        · exact absurd (hb'.mpr h) hbt
        · exact h

/-- The slices `listing_fields` delimits are exactly the entry's object id
    and path. -/
theorem FieldsOf.slices {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) {i : Nat} {f : Fields} (hf : FieldsOf es i f) :
    ∃ e, es[i]? = some e ∧ EntryOk e ∧
      (sliceBytes listing).extract (f.start.val + 7) f.oid_end.val = e.oid ∧
      (sliceBytes listing).extract f.path_start.val f.end.val = e.path ∧
      f.start.val + 7 ≤ f.oid_end.val ∧ f.oid_end.val ≤ listing.length ∧
      f.path_start.val ≤ f.end.val ∧ f.end.val ≤ listing.length := by
  obtain ⟨e, he, hs, ho, hp, hend, _⟩ := hf
  have hi : i < es.length := (List.getElem?_eq_some_iff.mp he).1
  have hei : es[i] = e := (List.getElem?_eq_some_iff.mp he).2
  obtain ⟨hdrop, _, hok⟩ := hL.record hi
  rw [hei] at hdrop hok
  have hm := hok.1
  have hrl := entryRecord_length e hm
  have hin := hL.off_le (Nat.succ_le_of_lt hi)
  rw [off_succ es _ hi, hei] at hin
  have hD7 : (sliceBytes listing).drop (off es i + 7) = e.oid ++ [32, 48, 9] ++ e.path ++
      (0 :: listingBytes (es.drop (i + 1))) := by
    rw [← List.drop_drop, hdrop, entryRecord_drop7 e hm]
  have hD10 : (sliceBytes listing).drop (off es i + 10 + e.oid.length) =
      e.path ++ (0 :: listingBytes (es.drop (i + 1))) := by
    rw [show off es i + 10 + e.oid.length = (off es i + 7) + (e.oid.length + 3) by omega,
      ← List.drop_drop, hD7]
    simp
  refine ⟨e, he, hok, ?_, ?_, by omega, by omega, by omega, by omega⟩
  · rw [List.extract_eq_take_drop, hs, ho, hD7, show off es i + 7 + e.oid.length - (off es i + 7) =
      e.oid.length by omega]
    simp
  · rw [List.extract_eq_take_drop, hp, hend, hD10, show off es i + (entryRecord e).length -
      (off es i + 10 + e.oid.length) = e.path.length by omega]
    simp

/-! ## `held_entries` -/

theorem getElem!_set_ne' {α : Type} [Inhabited α] (l : List α) {i k : Nat} (v : α) (h : k ≠ i) :
    (l.set i v)[k]! = l[k]! := by
  simp only [getElem!_def, List.getElem?_set_ne (Ne.symm h)]

theorem getElem!_set_self' {α : Type} [Inhabited α] (l : List α) {i : Nat} (v : α) (h : i < l.length) :
    (l.set i v)[i]! = v := by
  simp only [getElem!_def, List.getElem?_set_self h]

/-- `held_entries` writes, for each entry `k` of the index, whether it is
    wanted and the other listing holds its blob at its path. -/
def HeldUpTo (es os : List Entry) (wanted held : Slice Bool) (n : Nat) : Prop :=
  ∀ k e, k < n → es[k]? = some e →
    (held.val[k]! = true ↔ wanted.val[k]! = true ∧ Holds os e.oid e.path)

theorem held_entries_spec {index other : Slice U8} {index_ends other_ends : Slice Usize}
    {es os : List Entry} (hI : ListingOf index index_ends es) (hO : ListingOf other other_ends os)
    (wanted held : Slice Bool) (hw : wanted.length = es.length) (hh : held.length = es.length) :
    held_entries index index_ends wanted other other_ends held ⦃ r =>
      r.1 = true ∧ r.2.length = es.length ∧ HeldUpTo es os wanted r.2 es.length ⦄ := by
  have hiel := hI.ends_length
  have hoel := hO.ends_length
  unfold held_entries held_entries_loop
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  have hc1 : ¬ (wanted.len != index_ends.len) = true := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not]; apply UScalar.eq_of_val_eq; simp [hw, ← hiel]
  have hc2 : ¬ (held.len != index_ends.len) = true := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not]; apply UScalar.eq_of_val_eq; simp [hh, ← hiel]
  simp only [hc1, hc2, if_false, Bool.false_eq_true]
  step with loop.spec_decr_nat (fun s : Slice Bool × Usize × Usize => es.length - s.2.2.val)
    (fun s : Slice Bool × Usize × Usize => s.2.2.val ≤ es.length ∧ s.1.length = es.length ∧ HeldUpTo es os wanted s.1 s.2.2.val)
    (fun h : Slice Bool => h.length = es.length ∧ HeldUpTo es os wanted h es.length) as ⟨ r, hr1, hr2 ⟩
  · rintro ⟨hd, hint, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3 ⊢
    unfold held_entries_loop.body
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
    split
    · rename_i hil
      have hi : i.val < es.length := by scalar_tac
      have hwl : i.val < wanted.length := by omega
      have hdl : i.val < hd.length := by omega
      -- After writing the right value `v` at `i`, the invariant holds at `i + 1`.
      have hnext : ∀ (v : Bool) (s : Slice Bool),
          (v = true ↔ wanted.val[i.val]! = true ∧ Holds os es[i.val].oid es[i.val].path) →
          s.val = hd.val.set i.val v →
          s.length = es.length ∧ HeldUpTo es os wanted s (i.val + 1) := by
        intro v s hv hsv
        refine ⟨by simp [Slice.length, hsv, ← h2], fun k e hk hke => ?_⟩
        rw [hsv]
        rcases Nat.lt_or_ge k i.val with hlt | hge
        · rw [getElem!_set_ne' _ _ (by omega)]
          exact h3 k e hlt hke
        · have hki : k = i.val := by omega
          subst hki
          rw [getElem!_set_self' _ _ (by simp [Slice.length] at h2 ⊢; omega)]
          rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hke
          subst hke
          exact hv
      step as ⟨ hiw, b, hb ⟩
      have hbw : b = wanted.val[i.val]! := by rw [hb, getElem!_pos wanted.val i.val hiw]
      by_cases hbv : b = true
      · simp only [hbv, if_true]
        step with listing_fields_spec hI i as ⟨ o, ho ⟩
        rcases o with _ | f
        · exfalso; simp only at ho; omega
        · obtain ⟨_, hf⟩ := ho
          obtain ⟨e, he, hok, hoid, hpath, hf1, hf2, hf3, hf4⟩ := FieldsOf.slices hI hf
          have hei : es[i.val] = e := (List.getElem?_eq_some_iff.mp he).2
          simp only
          step as ⟨ i2, hi2 ⟩
          step with index_range_spec index i2 f.oid_end (by omega) (by omega) as ⟨ so, hso ⟩
          step with index_range_spec index f.path_start f.end hf3 hf4 as ⟨ sp, hsp ⟩
          rw [hi2, hoid] at hso
          rw [hpath] at hsp
          have h9 : 9 ∉ sliceBytes so := by rw [hso]; exact objectId_no_tab hok.2.2.2.1
          step with find_entry_spec hO so sp h9 hint as ⟨ j, hj1, hj2, hj3 ⟩
          by_cases hjv : j < other_ends.len
          · simp only [hjv, if_true]
            step as ⟨ s, hil', hs ⟩
            step*
            have hsv : s.val = hd.val.set i.val true := by rw [hs]; rfl
            obtain ⟨hl', hu⟩ := hnext true s (by
              rw [← hbw, hei, ← hso, ← hsp]
              obtain ⟨e', he', ho', hp'⟩ := hj2 (by scalar_tac)
              exact ⟨fun _ => ⟨hbv, e', List.mem_of_getElem? he', ho', hp'⟩, fun _ => rfl⟩) hsv
            exact ⟨by omega, hl', by rw [show i2.val = i.val + 1 by scalar_tac]; exact hu, by omega⟩
          · simp only [hjv, if_false]
            step as ⟨ s, hil', hs ⟩
            step*
            have hsv : s.val = hd.val.set i.val false := by rw [hs]; rfl
            obtain ⟨hl', hu⟩ := hnext false s (by
              rw [← hbw, hei, ← hso, ← hsp]
              have := hj3 (by scalar_tac)
              simp only [Bool.false_eq_true, false_iff, not_and]
              exact fun _ => this) hsv
            exact ⟨by omega, hl', by rw [show i2.val = i.val + 1 by scalar_tac]; exact hu, by omega⟩
      · simp only [hbv, if_false, Bool.false_eq_true]
        step as ⟨ s, hil', hs ⟩
        step*
        have hsv : s.val = hd.val.set i.val false := by rw [hs]; rfl
        obtain ⟨hl', hu⟩ := hnext false s (by
          rw [← hbw]; simp only [Bool.false_eq_true, false_iff, not_and]; exact fun h => absurd h hbv) hsv
        exact ⟨by omega, hl', by rw [show i2.val = i.val + 1 by scalar_tac]; exact hu, by omega⟩
    · rename_i hil
      simp only [WP.spec_ok]
      have : i.val = es.length := by scalar_tac
      exact ⟨h2, this ▸ h3⟩
  · exact ⟨by simp, by simp [hh], fun k e hk => absurd hk (by simp)⟩
  · exact ⟨hr1, hr2⟩

/-! ## `is_local_change` -/

/-- `is_local_change` is exactly the spec's `LocalChange`, given whether
    `HEAD` and the incoming commits hold the entry (from `held_entries`). The
    adapter passes `incoming_known` = whether the incoming commits are known. -/
theorem is_local_change_spec (head : List Entry) (incoming : Option (List Entry)) (s : Entry)
    (inHead inIncoming forced envelope : Bool)
    (hh : inHead = true ↔ Holds head s.oid s.path)
    (hi : ∀ m, incoming = some m → (inIncoming = true ↔ Holds m s.oid s.path)) :
    is_local_change inHead incoming.isSome inIncoming forced envelope ⦃ r =>
      r = true ↔ LocalChange head incoming forced envelope s ⦄ := by
  unfold is_local_change LocalChange
  simp only [WP.spec_ok]
  rcases incoming with _ | m
  · simp
  · have him := hi m rfl
    cases inHead <;> cases inIncoming <;> cases forced <;> cases envelope <;> simp_all

/-! ## Move sources -/

/-- The `HEAD` entry `h` holds the blob `oid` at another path than `path`,
    and the index does not hold it at `h`'s path. -/
def MovedFrom (es : List Entry) (oid path : List Nat) (h : Entry) : Prop :=
  h.oid = oid ∧ h.path ≠ path ∧ ¬ Holds es h.oid h.path

theorem move_source_at_spec {index head : Slice U8} {index_ends head_ends : Slice Usize}
    {es hs : List Entry} (hI : ListingOf index index_ends es) (hH : ListingOf head head_ends hs)
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
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
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
    step with find_entry_spec hI oid source h9' 0#usize as ⟨ r, hr1, hr2, hr3 ⟩
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

theorem move_source_from_spec {index head : Slice U8} {index_ends head_ends : Slice Usize}
    {es hs : List Entry} (hI : ListingOf index index_ends es) (hH : ListingOf head head_ends hs)
    (oid path : Slice U8) (h9 : 9 ∉ sliceBytes oid) (from_ : Usize) (hf : from_.val ≤ hs.length) :
    move_source_from index index_ends head head_ends oid path from_ ⦃ r =>
      FirstFrom hs (MovedFrom es (sliceBytes oid) (sliceBytes path)) from_.val hs.length r.val ⦄ := by
  have hel := hH.ends_length
  unfold move_source_from move_source_from_loop FirstFrom
  apply loop.spec_decr_nat (fun s => 2 * (hs.length - s.1.val) + (if s.2 then 0 else 1))
    (fun s => from_.val ≤ s.1.val ∧ s.1.val ≤ hs.length ∧
      (∀ k e, from_.val ≤ k → k < s.1.val → hs[k]? = some e →
        ¬ MovedFrom es (sliceBytes oid) (sliceBytes path) e) ∧
      (s.2 = true → s.1.val < hs.length ∧
        ∃ e, hs[s.1.val]? = some e ∧ MovedFrom es (sliceBytes oid) (sliceBytes path) e))
  · rintro ⟨j, found⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4 ⊢
    unfold move_source_from_loop.body
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
    split
    · rename_i hfd
      simp only [WP.spec_ok]
      exact ⟨h1, h2, h3, fun _ => (h4 hfd).2⟩
    · rename_i hfd
      split
      · rename_i hjt
        have hj : j.val < hs.length := by scalar_tac
        step with move_source_at_spec hI hH oid path h9 j hj as ⟨ b, hb ⟩
        split
        · rename_i hbt
          simp only [WP.spec_ok]
          exact ⟨h1, h2, h3, fun _ => ⟨hj, hs[j.val], by simp, hb.mp hbt⟩, by simp⟩
        · rename_i hbt
          step as ⟨ j1, hj1 ⟩
          refine ⟨by omega, by omega, fun k e hk1 hk2 hke => ?_, fun h => absurd h (by simp),
            by simp only [Bool.false_eq_true, if_false]; omega⟩
          rcases Nat.lt_or_ge k j.val with hlt | hge
          · exact h3 k e hk1 hlt hke
          · have hkj : k = j.val := by omega
            subst hkj
            rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hke
            subst hke
            exact fun hn => hbt (hb.mpr hn)
      · rename_i hjt
        simp only [WP.spec_ok]
        have hjt' : hs.length ≤ j.val := by scalar_tac
        exact ⟨h1, h2, h3, fun h => absurd h (by omega)⟩
  · refine ⟨le_refl _, hf, fun k e hk1 hk2 => by dsimp only at hk2; omega, fun h => absurd h (by simp)⟩

/-- **Move sources.** `next_move_source` returns the first `HEAD` entry at
    or after `from` that the staged entry `i` may have been moved from
    (`MoveSource`: the same blob at another path, which has left the index),
    or `HEAD`'s length if there is none. -/
theorem next_move_source_spec {index head : Slice U8} {index_ends head_ends : Slice Usize}
    {es hs : List Entry} (hI : ListingOf index index_ends es) (hH : ListingOf head head_ends hs)
    (i : Usize) (hi : i.val < es.length) (from_ : Usize) (hf : from_.val ≤ hs.length) :
    next_move_source index index_ends i head head_ends from_ ⦃ r =>
      FirstFrom hs (MoveSource es es[i.val]) from_.val hs.length r.val ⦄ := by
  unfold next_move_source
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
    apply WP.spec_mono (move_source_from_spec hI hH so sp h9 from_ hf)
    intro r hr
    have hP : ∀ h, MovedFrom es (sliceBytes so) (sliceBytes sp) h ↔ MoveSource es es[i.val] h := by
      intro h
      rw [hei, hso, hsp]
      rfl
    obtain ⟨r1, r2, r3, r4⟩ := hr
    refine ⟨r1, r2, fun k h hk1 hk2 hkh => (hP h).not.mp (r3 k h hk1 hk2 hkh), fun hlt => ?_⟩
    obtain ⟨h, hh, hm⟩ := r4 hlt
    exact ⟨h, hh, (hP h).mp hm⟩

/-! ## `blob_elsewhere` -/

theorem scan_other_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (oid path : Slice U8) (h9 : 9 ∉ sliceBytes oid) :
    scan listing ends 0#usize ends.len oid path false ⦃ r =>
      (r.val < es.length ↔ ∃ e ∈ es, e.oid = sliceBytes oid ∧ e.path ≠ sliceBytes path) ∧
      r.val ≤ es.length ⦄ := by
  have hel := hL.ends_length
  have hn : ends.len.val = es.length := by simp [hel]
  apply WP.spec_mono (scan_spec hL oid path false h9 0#usize ends.len (by simp) (by omega))
  intro r ⟨r1, r2, r3, r4⟩
  rw [hn] at r2 r4
  refine ⟨⟨fun h => ?_, fun ⟨e, hmem, ho, hp⟩ => ?_⟩, r2⟩
  · obtain ⟨e, he, ho, hp⟩ := r4 h
    exact ⟨e, List.mem_of_getElem? he, ho, fun h' => by simp at hp; exact hp h'⟩
  · obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    by_contra hge
    exact r3 m _ (by simp) (by omega) (List.getElem?_eq_getElem hm) ⟨ho, by simp [hp]⟩

/-- **Keyless move check.** `blob_elsewhere` says exactly whether the blob
    of entry `i` of the index is at another path in the index, `HEAD` or its
    parent (`BlobElsewhere`). -/
theorem blob_elsewhere_spec {index head parent : Slice U8} {index_ends head_ends parent_ends : Slice Usize}
    {es hs ps : List Entry} (hI : ListingOf index index_ends es) (hH : ListingOf head head_ends hs)
    (hP : ListingOf parent parent_ends ps) (i : Usize) (hi : i.val < es.length) :
    blob_elsewhere index index_ends i head head_ends parent parent_ends ⦃ b =>
      b = true ↔ BlobElsewhere [es, hs, ps] es[i.val] ⦄ := by
  unfold blob_elsewhere
  step with listing_fields_spec hI i as ⟨ o, ho ⟩
  rcases o with _ | f
  · exfalso; simp only at ho; omega
  · obtain ⟨_, hf'⟩ := ho
    obtain ⟨e, he, hok, hoid, hpath, hf1, hf2, hf3, hf4⟩ := FieldsOf.slices hI hf'
    have hei : es[i.val] = e := (List.getElem?_eq_some_iff.mp he).2
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
    step as ⟨ i1, hi1 ⟩
    step with index_range_spec index i1 f.oid_end (by omega) (by omega) as ⟨ so, hso ⟩
    step with index_range_spec index f.path_start f.end hf3 hf4 as ⟨ sp, hsp ⟩
    rw [hi1, hoid] at hso
    rw [hpath] at hsp
    have h9 : 9 ∉ sliceBytes so := by rw [hso]; exact objectId_no_tab hok.2.2.2.1
    have hiel := hI.ends_length
    have hhel := hH.ends_length
    have hpel := hP.ends_length
    unfold BlobElsewhere
    rw [hei]
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    rw [← hso, ← hsp]
    step with scan_other_spec hI so sp h9 as ⟨ r1, hr1, hr1l ⟩
    split
    · rename_i hlt
      simp only [WP.spec_ok, true_iff]
      exact Or.inl (hr1.mp (by scalar_tac))
    · rename_i hlt
      have hn1 := mt hr1.mpr (by scalar_tac)
      step with scan_other_spec hH so sp h9 as ⟨ r2, hr2, hr2l ⟩
      split
      · rename_i hlt2
        simp only [WP.spec_ok, true_iff]
        exact Or.inr (Or.inl (hr2.mp (by scalar_tac)))
      · rename_i hlt2
        have hn2 := mt hr2.mpr (by scalar_tac)
        step with scan_other_spec hP so sp h9 as ⟨ r3, hr3, hr3l ⟩
        simp only [decide_eq_true_eq]
        have hlen3 : parent_ends.len.val = ps.length := by simp [hpel]
        constructor
        · intro h
          exact Or.inr (Or.inr (hr3.mp (by scalar_tac)))
        · rintro (h | h | h)
          · exact absurd h hn1
          · exact absurd h hn2
          · have := hr3.mpr h
            scalar_tac

/-! ## `parse_listing_attrs` -/

/-- Git's complete answer naming the listing's paths with these values. -/
def AttrsHyp (es : List Entry) (response : Slice U8) (flags : Slice Bool) (values : List (List Nat)) : Prop :=
  values.length = es.length ∧ (∀ v ∈ values, 0 ∉ v) ∧ flags.length = es.length ∧
    sliceBytes response = attrResponse ((es.map (·.path)).zip values)

/-- Loop invariant of `parse_listing_attrs` after `i` records. -/
def AttrsInv (es : List Entry) (response : Slice U8) (flags : Slice Bool)
    (fl : Slice Bool) (ok : Bool) (at_ i : Nat) : Prop :=
  i ≤ flags.length ∧ fl.length = flags.length ∧
  (ok = true → flags.length = es.length ∧ at_ ≤ response.length ∧
    ∃ vs : List (List Nat), vs.length = i ∧ (∀ v ∈ vs, 0 ∉ v) ∧
      (sliceBytes response).take at_ = attrResponse (((es.take i).map (·.path)).zip vs) ∧
      fl.val.take i = vs.map (fun v => decide (Selected v)) ∧
      (∀ values, AttrsHyp es response flags values → vs = values.take i)) ∧
  (∀ values, AttrsHyp es response flags values → ok = true)

theorem attrs_zip_take (es : List Entry) (values : List (List Nat)) (i : Nat) :
    ((es.map (·.path)).zip values).take i = ((es.take i).map (·.path)).zip (values.take i) := by
  simp only [List.zip, List.take_zipWith, List.map_take]

theorem parse_listing_attrs_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (response : Slice U8) (flags : Slice Bool) :
    parse_listing_attrs listing ends response flags ⦃ r =>
      (r.1 = true → ∃ values : List (List Nat), values.length = es.length ∧ (∀ v ∈ values, 0 ∉ v) ∧
        sliceBytes response = attrResponse ((es.map (·.path)).zip values) ∧
        r.2.val = values.map (fun v => decide (Selected v))) ∧
      (∀ values, AttrsHyp es response flags values →
        r.1 = true ∧ r.2.val = values.map (fun v => decide (Selected v))) ⦄ := by
  have hel := hL.ends_length
  have hRl := sliceBytes_length response
  unfold parse_listing_attrs parse_listing_attrs_loop
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  step with loop.spec_decr_nat
    (fun s : Slice Bool × Bool × Usize × Usize => 2 * (flags.length - s.2.2.2.val) + (if s.2.1 then 1 else 0))
    (fun s : Slice Bool × Bool × Usize × Usize => AttrsInv es response flags s.1 s.2.1 s.2.2.1.val s.2.2.2.val)
    (fun s : Slice Bool × Bool × Usize => AttrsInv es response flags s.1 s.2.1 s.2.2.val flags.length)
    as ⟨ fl, okr, atr, hinv ⟩
  · rintro ⟨fl, ok, at_, i⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4 ⊢
    unfold parse_listing_attrs_loop.body
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
    split
    · rename_i hok
      obtain ⟨hfe, hat, vs, hvl, hv0, hR, hF, hH⟩ := h3 hok
      split
      · rename_i hil
        have hi : i.val < es.length := by scalar_tac
        -- Under Git's answer, the next record is this path's.
        have hnext : ∀ values, AttrsHyp es response flags values →
            AttrRecordAt (sliceBytes response) at_.val es[i.val].path values[i.val]!
              (at_.val + (attrRecord es[i.val].path values[i.val]!).length) := by
          intro values hy
          obtain ⟨hvl', hv0', _, hS⟩ := hy
          have hq : i.val < ((es.map (·.path)).zip values).length := by simp [hvl']; omega
          have := hyp_record (qs := (es.map (·.path)).zip values) (a := at_.val) (i := i.val) (fun q hq => by
              obtain ⟨_, hm⟩ := List.of_mem_zip hq; exact hv0' _ hm) hS (by rw [hRl]; exact hat)
            (by rw [hR, hH values ⟨hvl', hv0', ‹_›, hS⟩, attrs_zip_take]) hq
          simpa [List.getElem_zip, getElem!_pos values i.val (by omega)] using this
        step with listing_fields_spec hL i as ⟨ o, ho ⟩
        rcases o with _ | f
        · exfalso; simp only at ho; omega
        · obtain ⟨_, hf'⟩ := ho
          obtain ⟨e, he, hok', hoid, hpath, hf1, hf2, hf3, hf4⟩ := FieldsOf.slices hL hf'
          have hei : es[i.val] = e := (List.getElem?_eq_some_iff.mp he).2
          simp only
          step with index_range_spec listing f.path_start f.end hf3 hf4 as ⟨ sp, hsp ⟩
          rw [hpath] at hsp
          step with parse_attr_record_spec response at_ sp as ⟨ r, hr ⟩
          rcases r with a | x
          · obtain ⟨v, hrec, hprot⟩ := hr
            simp only
            step as ⟨ fl2, hil2, hfl2 ⟩
            step as ⟨ i5, hi5 ⟩
            rw [hsp, ← hei] at hrec
            obtain ⟨hStake, hnextl⟩ := attrRecordAt_take hrec
            have hb : a.protected = decide (Selected v) := by
              by_cases hs : Selected v
              · rw [decide_eq_true hs]; exact hprot.mpr hs
              · rw [decide_eq_false hs]
                cases h : a.protected
                · rfl
                · exact absurd (hprot.mp h) hs
            have hfv : fl2.val = fl.val.set i.val a.protected := by rw [hfl2]; rfl
            refine ⟨⟨by omega, by rw [← h2, Slice.length, hfv, List.length_set], fun _ => ⟨hfe,
              by rw [hRl] at hnextl; exact hnextl, vs ++ [v], by simp [hvl, hi5], ?_, ?_, ?_, ?_⟩,
              fun _ _ => rfl⟩, by simp only [if_true]; omega⟩
            · intro w hw
              rcases List.mem_append.1 hw with hw | hw
              · exact hv0 w hw
              · rw [List.mem_singleton.1 hw]; exact hrec.1
            · rw [hStake, hR, hi5, List.take_add_one, List.getElem?_eq_getElem hi, List.map_append,
                List.zip_append (by simp [hvl]; omega), attrResponse_append]
              simp [attrResponse]
            · rw [hi5, hfv, take_set_succ _ _ _ (by simp [Slice.length] at h2 ⊢; omega), hF, hb]
              simp
            · intro values hy
              have hv := hnext values hy
              obtain ⟨hvq, -⟩ := attrRecordAt_unique hrec hv
              rw [hi5, hH values hy, List.take_add_one, List.getElem?_eq_getElem (by rw [hy.1]; exact hi), hvq,
                getElem!_pos values i.val (by rw [hy.1]; exact hi)]
              rfl
          · simp only
            refine ⟨⟨h1, h2, fun h => absurd h (by simp), fun values hy => ?_⟩, by simp only [if_false, Bool.false_eq_true]; omega⟩
            exfalso
            apply hr.2
            rw [hsp, ← hei]
            exact ⟨_, _, hnext values hy⟩
      · rename_i hil
        simp only [WP.spec_ok]
        have : i.val = flags.length := by scalar_tac
        rw [← this]
        exact ⟨h1, h2, fun _ => h3 hok, fun _ _ => rfl⟩
    · rename_i hok
      simp only [WP.spec_ok]
      refine ⟨by scalar_tac, h2, fun h => absurd h (by simp), fun values hy => absurd (h4 values hy) hok⟩
  · refine ⟨by simp, rfl, fun hok => ?_, fun values hy => ?_⟩
    · have hfe : flags.length = es.length := by
        have := of_decide_eq_true hok
        have := congrArg UScalar.val this
        simp [hel] at this; exact this
      refine ⟨hfe, by simp, [], rfl, by simp, by simp [attrResponse], by simp, fun _ _ => by simp⟩
    · apply decide_eq_true
      apply UScalar.eq_of_val_eq
      simp [hel, hy.2.2.1]
  · obtain ⟨h1, h2, h3, h4⟩ := hinv
    split
    · rename_i hok
      obtain ⟨hfe, hat, vs, hvl, hv0, hR, hF, hH⟩ := h3 hok
      rw [hfe] at hR hF hvl
      rw [List.take_of_length_le (Nat.le_refl es.length)] at hR
      have hflen : fl.val.length = es.length := h2.trans hfe
      rw [List.take_of_length_le (le_of_eq hflen)] at hF
      simp only [WP.spec_ok]
      refine ⟨fun hatr => ⟨vs, hvl, hv0, ?_, hF⟩, fun values hy => ?_⟩
      · have : atr.val = response.length := by
          have := of_decide_eq_true hatr; rw [this]; simp
        rw [← hR, this, ← hRl, List.take_length]
      · have hvs := hH values hy
        rw [hfe, List.take_of_length_le (by rw [hy.1])] at hvs
        subst hvs
        refine ⟨decide_eq_true ?_, hF⟩
        apply UScalar.eq_of_val_eq
        have hS := hy.2.2.2
        have := congrArg List.length (hR.trans hS.symm)
        rw [List.length_take, hRl] at this
        have hat' : atr.val = response.length := by omega
        rw [hat']; simp
    · rename_i hok
      simp only [WP.spec_ok]
      exact ⟨fun h => absurd h (by simp), fun values hy => absurd (h4 values hy) hok⟩

/-! ## `first_unselectable` -/

/-- Every flagged entry before `r` is selectable. -/
def SelectableUpTo (es : List Entry) (flags : Slice Bool) (r : Nat) : Prop :=
  ∀ k e, k < r → es[k]? = some e → flags.val[k]! = true → Selectable e

/-- **Selectability.** `first_unselectable` returns the first protected
    entry that is not `Selectable` (a symlink or submodule, or reserved
    metadata), or the number of entries if every protected entry is
    selectable. -/
theorem first_unselectable_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (flags : Slice Bool) (hfl : flags.length = es.length) :
    first_unselectable listing ends flags ⦃ r => r.val ≤ es.length ∧ SelectableUpTo es flags r.val ∧
      (r.val < es.length → flags.val[r.val]! = true ∧ ∃ e, es[r.val]? = some e ∧ ¬ Selectable e) ⦄ := by
  unfold first_unselectable first_unselectable_loop
  apply loop.spec_decr_nat (fun s : Usize × Bool => 2 * (es.length - s.1.val) + (if s.2 then 0 else 1))
    (fun s : Usize × Bool => s.1.val ≤ es.length ∧ SelectableUpTo es flags s.1.val ∧
      (s.2 = true → s.1.val < es.length ∧ flags.val[s.1.val]! = true ∧
        ∃ e, es[s.1.val]? = some e ∧ ¬ Selectable e))
  · rintro ⟨i, bad⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3 ⊢
    unfold first_unselectable_loop.body
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
    split
    · rename_i hb
      simp only [WP.spec_ok]
      obtain ⟨_, hf, he⟩ := h3 hb
      exact ⟨h1, h2, fun _ => ⟨hf, he⟩⟩
    · rename_i hb
      split
      · rename_i hil
        have hi : i.val < es.length := by scalar_tac
        step as ⟨ hfl', fb, hfb ⟩
        have hfbv : fb = flags.val[i.val]! := by rw [hfb, getElem!_pos flags.val i.val hfl']
        -- The verdict for entry `i`: unselectable iff flagged and not `Selectable`.
        have hcont : ∀ bad1 : Bool, (bad1 = true ↔ fb = true ∧ ¬ Selectable es[i.val]) →
            (if bad1 then ok (cont (i, true)) else do
              let i2 ← i + 1#usize
              ok (cont (i2, false)) : RustM (ControlFlow (Usize × Bool) Usize)) ⦃ r =>
              (r = cont (i, true) ∧ fb = true ∧ ¬ Selectable es[i.val]) ∨
              (∃ i2 : Usize, r = cont (i2, false) ∧ i2.val = i.val + 1 ∧
                ¬ (fb = true ∧ ¬ Selectable es[i.val])) ⦄ := by
          intro bad1 hv
          split
          · rename_i hbt
            exact Or.inl ⟨rfl, hv.mp hbt⟩
          · rename_i hbt
            step as ⟨ i2, hi2 ⟩
            exact Or.inr ⟨i2, rfl, hi2, fun h => hbt (hv.mpr h)⟩
        -- What follows from the verdict.
        have hsel : ∀ i2 : Usize, i2.val = i.val + 1 → ¬ (fb = true ∧ ¬ Selectable es[i.val]) →
            SelectableUpTo es flags i2.val := by
          intro i2 hi2 hnV k e hk hke hfk
          rcases Nat.lt_or_ge k i.val with hlt | hge
          · exact h2 k e hlt hke hfk
          · have hki : k = i.val := by omega
            subst hki
            rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hke
            subst hke
            by_contra hn
            exact hnV ⟨hfbv ▸ hfk, hn⟩
        split
        · rename_i hfbt
          step with listing_fields_spec hL i as ⟨ o, ho ⟩
          rcases o with _ | f
          · exfalso; simp only at ho; omega
          · obtain ⟨_, hf'⟩ := ho
            obtain ⟨e, he, hok', hoid, hpath, hf1, hf2, hf3, hf4⟩ := FieldsOf.slices hL hf'
            have hei : es[i.val] = e := (List.getElem?_eq_some_iff.mp he).2
            obtain ⟨e', he', -, -, -, -, hreg⟩ := hf'
            have hee : e' = e := by rw [he] at he'; exact (Option.some.inj he').symm
            subst hee
            dsimp only
            step with index_range_spec listing f.path_start f.end hf3 hf4 as ⟨ sp, hsp ⟩
            step with is_reserved_path_spec as ⟨ b1, hb1 ⟩
            rw [hsp, hpath] at hb1
            apply WP.spec_mono (hcont (decide (¬f.regular = true) || b1) ?_)
            · rintro r (⟨rfl, hf, hn⟩ | ⟨i2, rfl, hi2, hnV⟩)
              · exact ⟨h1, h2, fun _ => ⟨hi, hfbv ▸ hf, es[i.val], by simp, hn⟩, by simp⟩
              · exact ⟨by dsimp only; omega, hsel i2 hi2 hnV, fun h => absurd h (by simp),
                  by simp only [Bool.false_eq_true, if_false]; omega⟩
            rw [hei]
            unfold Selectable
            simp only [Bool.or_eq_true, hfbt, true_and]
            constructor
            · rintro (h | h) ⟨hr, hn⟩
              · exact absurd (hreg.mpr hr) (of_decide_eq_true h)
              · exact hn (hb1.mp h)
            · intro h
              by_cases hr : e'.Regular
              · exact Or.inr (hb1.mpr (Classical.byContradiction fun hn => h ⟨hr, hn⟩))
              · exact Or.inl (decide_eq_true (fun hfr => hr (hreg.mp hfr)))
        · rename_i hfbt
          simp only [bind_tc_ok]
          apply WP.spec_mono (hcont false (by simp [hfbt]))
          rintro r (⟨rfl, hf, hn⟩ | ⟨i2, rfl, hi2, hnV⟩)
          · exact absurd hf hfbt
          · exact ⟨by dsimp only; omega, hsel i2 hi2 hnV, fun h => absurd h (by simp),
              by simp only [Bool.false_eq_true, if_false]; omega⟩
      · rename_i hil
        simp only [WP.spec_ok]
        have hi : es.length ≤ i.val := by scalar_tac
        exact ⟨h1, h2, fun h => absurd h (by omega)⟩
  · exact ⟨by simp, fun k e hk => absurd hk (by simp), fun h => absurd h (by simp)⟩

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
  have h0o : 0 ∉ e.oid := fun h => by rcases hoid.2 0 h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
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
    exactly Git's listing of well-formed entries and `ends` records where each
    record ends (`ListingOf`); conversely it accepts Git's listing of any
    well-formed entries, with one slot per entry, and computes exactly their
    ends. -/
theorem parse_listing_spec (listing : Slice U8) (ends : Slice Usize) :
    parse_listing listing ends ⦃ r =>
      (r.1 = true → ∃ es, ListingOf listing r.2 es) ∧
      (∀ es, ListingHyp listing ends es → r.1 = true ∧ ListingOf listing r.2 es) ⦄ := by
  have hLl := sliceBytes_length listing
  have hmax := listing.property
  unfold parse_listing parse_listing_loop
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  step with loop.spec_decr_nat
    (fun s : Slice Usize × Bool × Usize × Usize => 2 * (ends.length - s.2.2.2.val) + (if s.2.1 then 1 else 0))
    (fun s : Slice Usize × Bool × Usize × Usize => ParseInv listing ends s.1 s.2.1 s.2.2.1.val s.2.2.2.val)
    (fun s : Slice Usize × Bool × Usize => ParseInv listing ends s.1 s.2.1 s.2.2.val ends.length)
    as ⟨ fl, okr, st, hinv ⟩
  · rintro ⟨fl, ok, st, i⟩ ⟨h1, h2, h3, h4, h5⟩
    dsimp only at h1 h2 h3 h4 h5 ⊢
    unfold parse_listing_loop.body
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
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
          refine ⟨hi', ?_, ?_⟩
          · rcases Nat.lt_trichotomy en.val (st.val + (entryRecord es[i.val]).length) with h | h | h
            · exfalso
              exact c en.val (by simpa using hs1) h (by have := hen (by rw [← hLl] at b; omega); simpa using this)
            · exact h
            · exfalso
              exact hs3 _ (by omega) h (by simpa using a)
          · rcases Nat.lt_trichotomy en.val (st.val + (entryRecord es[i.val]).length) with h | h | h
            · exfalso
              exact c en.val (by simpa using hs1) h (by have := hen (by rw [← hLl] at b; omega); simpa using this)
            · omega
            · exfalso
              exact hs3 _ (by omega) h (by simpa using a)
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
      simp only [WP.spec_ok]
      refine ⟨fun hst => ⟨pre, hpok, ?_, by rw [h2, hpl], hpe⟩, fun es hy => ?_⟩
      · have : st.val = listing.length := by
          have := of_decide_eq_true hst; rw [this]; simp
        rw [← hpt, this, ← hLl, List.take_length]
      · have hpe' := hph es hy
        rw [hy.2.2, List.take_of_length_le (le_refl _)] at hpe'
        subst hpe'
        have hst : st.val = listing.length := by
          have := congrArg List.length (hpt.trans hy.2.1.symm)
          rw [List.length_take, hLl] at this
          omega
        refine ⟨decide_eq_true (UScalar.eq_of_val_eq (by rw [hst]; simp)), hy.1, hy.2.1, by rw [h2, hy.2.2], hpe⟩
    · rename_i hok
      simp only [WP.spec_ok]
      exact ⟨fun h => absurd h (by simp), fun es hy => absurd (h5 es hy) hok⟩

end Transcrypt.V3Verification

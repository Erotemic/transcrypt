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
`Transcrypt.V3Policy.listingBytes es` of well-formed entries in Git's byte
order of paths (`Sorted`: each path once; or, for merged trees,
`PathOrdered`) and records where each record ends (`ListingOf`); every
query over such a listing computes the spec's predicate on its entries:
`listing_fields` (the fields of one entry), `held_entries` (`Holds`, by
binary search), `is_local_change` (`LocalChange`), `next_move_source`
(`MoveSource`, first at or after an offset, through an object order
checked by `object_order_ok`), `blob_elsewhere` (`BlobElsewhere`, likewise),
`parse_listing_attrs` (Git's attribute answer for exactly the listing's
paths, `attrResponse`) and `first_unselectable` (`Selectable`).
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

/-- `r` is the first position in `[from, to)` whose entry satisfies `P`, or
    `to` if there is none. -/
def FirstFrom (es : List Entry) (P : Entry → Prop) (from_ to_ r : Nat) : Prop :=
  from_ ≤ r ∧ r ≤ to_ ∧ (∀ k e, from_ ≤ k → k < r → es[k]? = some e → ¬ P e) ∧
    (r < to_ → ∃ e, es[r]? = some e ∧ P e)

/-- An object id of a well-formed entry contains no TAB. -/
theorem objectId_no_tab {oid : List Nat} (h : ObjectId oid) : 9 ∉ oid := fun h9 => by
  rcases h.2 9 h9 with ⟨_, h⟩ | ⟨h, _⟩ <;> omega

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

/-! ## Slice updates -/

theorem getElem!_set_ne' {α : Type} [Inhabited α] (l : List α) {i k : Nat} (v : α) (h : k ≠ i) :
    (l.set i v)[k]! = l[k]! := by
  simp only [getElem!_def, List.getElem?_set_ne (Ne.symm h)]

theorem getElem!_set_self' {α : Type} [Inhabited α] (l : List α) {i : Nat} (v : α) (h : i < l.length) :
    (l.set i v)[i]! = v := by
  simp only [getElem!_def, List.getElem?_set_self h]

/-! ## Byte order: `bytes_lt` and `listing_ordered` -/

theorem bytesLt_append_left (p a b : List Nat) : BytesLt (p ++ a) (p ++ b) ↔ BytesLt a b := by
  induction p with
  | nil => exact Iff.rfl
  | cons x p ih => simp only [List.cons_append, BytesLt, Nat.lt_irrefl, false_or, true_and, ih]

/-- Byte strings with a common prefix compare as their rests. -/
theorem bytesLt_drop {A B : List Nat} {j : Nat} (h : A.take j = B.take j) :
    BytesLt A B ↔ BytesLt (A.drop j) (B.drop j) := by
  conv_lhs => rw [← List.take_append_drop j A, ← List.take_append_drop j B, h]
  exact bytesLt_append_left _ _ _

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
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  step*
  · rename_i hne
    subst i3_post2 i4_post2
    have hj1 : j.val < (sliceBytes a).length := by omega
    have hj2 : j.val < (sliceBytes b).length := by omega
    rw [bytesLt_drop hc, List.drop_eq_getElem_cons hj1, List.drop_eq_getElem_cons hj2,
      sliceBytes_getElem a j.val i3, sliceBytes_getElem b j.val i4]
    simp only [bne_iff_ne, ne_eq] at hne
    have hv : (a.val[j.val]).val ≠ (b.val[j.val]).val := fun h => hne (UScalar.eq_of_val_eq h)
    simp only [BytesLt, decide_eq_true_eq, hv, false_and, or_false]
    exact Iff.rfl
  · subst i3_post2 i4_post2
    rename_i heq
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq
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

/-- A transitive relation holds pairwise if it holds between neighbors. -/
theorem pairwise_of_adjacent {α : Type} {R : α → α → Prop} (htr : ∀ a b c, R a b → R b c → R a c) :
    ∀ (l : List α), (∀ k (h : k + 1 < l.length), R l[k] l[k + 1]) → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    refine List.Pairwise.cons ?_ (pairwise_of_adjacent htr xs (fun k hk => h (k + 1) (by simp; omega)))
    have hall : ∀ m (hm : m < xs.length), R x xs[m] := by
      intro m
      induction m with
      | zero => exact fun hm => h 0 (by simp; omega)
      | succ m ih => exact fun hm => htr _ _ _ (ih (by omega)) (h (m + 1) (by simp; omega))
    intro y hy
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hy
    exact hall m hm

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
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
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

/-- Pigeonhole: `n` distinct numbers below `n` are all of them. -/
theorem mem_of_nodup_lt {L : List Nat} {n : Nat} (hd : L.Nodup) (hl : L.length = n) (hlt : ∀ x ∈ L, x < n)
    {j : Nat} (hj : j < n) : j ∈ L := by
  have hsub : L.toFinset ⊆ Finset.range n := by
    intro x hx; simp only [List.mem_toFinset] at hx; simpa using hlt x hx
  have hcard : (Finset.range n).card ≤ L.toFinset.card := by
    rw [List.toFinset_card_of_nodup hd, hl, Finset.card_range]
  have := Finset.eq_of_subset_of_card_le hsub hcard
  have hj' : j ∈ Finset.range n := Finset.mem_range.mpr hj
  rw [← this] at hj'
  exact List.mem_toFinset.mp hj'


/-! ## Path lookups: `find_path`, `find_entry`, `held_entries` -/

theorem path_before_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (j : Usize) (path : Slice U8) :
    path_before listing ends j path ⦃ b => b = true ↔
      ∃ e, es[j.val]? = some e ∧ BytesLt e.path (sliceBytes path) ⦄ := by
  unfold path_before
  step with listing_fields_spec hL j as ⟨ o, ho ⟩
  rcases o with _ | f
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro e he
    simp only at ho
    have := (List.getElem?_eq_some_iff.mp he).1
    omega
  · obtain ⟨_, hf⟩ := ho
    obtain ⟨e, he, -, -, hpath, -, -, hf3, hf4⟩ := FieldsOf.slices hL hf
    simp only
    step with index_range_spec listing f.path_start f.end hf3 hf4 as ⟨ s, hs ⟩
    apply WP.spec_mono (bytes_lt_spec s path)
    intro b hb
    rw [hb, hs, hpath]
    exact ⟨fun h => ⟨e, he, h⟩, fun ⟨e', he', h⟩ => by rw [he] at he'; cases he'; exact h⟩

theorem path_at_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (j : Usize) (path : Slice U8) :
    path_at listing ends j path ⦃ b => b = true ↔
      ∃ e, es[j.val]? = some e ∧ e.path = sliceBytes path ⦄ := by
  unfold path_at
  step with listing_fields_spec hL j as ⟨ o, ho ⟩
  rcases o with _ | f
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro e he
    simp only at ho
    have := (List.getElem?_eq_some_iff.mp he).1
    omega
  · obtain ⟨_, hf⟩ := ho
    obtain ⟨e, he, -, -, hpath, -, -, hf3, hf4⟩ := FieldsOf.slices hL hf
    simp only
    step with index_range_spec listing f.path_start f.end hf3 hf4 as ⟨ s, hs ⟩
    apply WP.spec_mono (bytes_eq_spec s path)
    intro b hb
    rw [hb, ← sliceBytes_inj, hs, hpath]
    exact ⟨fun h => ⟨e, he, h⟩, fun ⟨e', he', h⟩ => by rw [he] at he'; cases he'; exact h⟩

/-- In a listing in path order, paths before `P` come first. -/
theorem PathOrdered.lt_of_le {es : List Entry} (hO : PathOrdered es) {P : List Nat} {k m : Nat}
    (hkm : k ≤ m) (hm : m < es.length) (h : BytesLt es[m].path P) : BytesLt es[k].path P := by
  rcases Nat.lt_or_ge k m with hlt | hge
  · rcases List.pairwise_iff_getElem.mp hO k m (by omega) hm hlt with h' | h'
    · exact bytesLt_trans h' h
    · rw [h']; exact h
  · have : k = m := by omega
    subst this; exact h

/-- `find_path` is the first record whose path is not before `P`; all
    earlier paths are before it, no later one is. -/
theorem find_path_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (hO : PathOrdered es) (path : Slice U8) :
    find_path listing ends path ⦃ r => r.val ≤ es.length ∧
      (∀ k (h : k < es.length), k < r.val → BytesLt es[k].path (sliceBytes path)) ∧
      (∀ k (h : k < es.length), r.val ≤ k → ¬ BytesLt es[k].path (sliceBytes path)) ⦄ := by
  have hel := hL.ends_length
  unfold find_path find_path_loop
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  apply loop.spec_decr_nat (fun s : Usize × Usize => s.2.val - s.1.val)
    (fun s : Usize × Usize => s.1.val ≤ s.2.val ∧ s.2.val ≤ es.length ∧
      (∀ k (h : k < es.length), k < s.1.val → BytesLt es[k].path (sliceBytes path)) ∧
      (∀ k (h : k < es.length), s.2.val ≤ k → ¬ BytesLt es[k].path (sliceBytes path)))
  · rintro ⟨low, high⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4 ⊢
    unfold find_path_loop.body
    split
    · rename_i hlh
      have hlh' : low.val < high.val := by scalar_tac
      step as ⟨ d, hd ⟩
      step as ⟨ d2, hd2 ⟩
      step as ⟨ mid, hmid ⟩
      have hm1 : low.val ≤ mid.val := by scalar_tac
      have hm2 : mid.val < high.val := by
        have : d2.val ≤ d.val / 2 := by scalar_tac
        have : d.val / 2 < d.val := Nat.div_lt_self (by omega) (by omega)
        scalar_tac
      step with path_before_spec hL mid path as ⟨ b, hb ⟩
      have hmes : mid.val < es.length := by omega
      split
      · rename_i hbt
        obtain ⟨e, he, hlt⟩ := hb.mp hbt
        rw [List.getElem?_eq_getElem hmes, Option.some.injEq] at he
        subst he
        step as ⟨ low1, hlow1 ⟩
        refine ⟨by omega, h2, fun k hk hkl => PathOrdered.lt_of_le hO (by omega) hmes hlt, h4, by omega⟩
      · rename_i hbt
        simp only [WP.spec_ok]
        refine ⟨hm1, by omega, h3, fun k hk hkm hlt => hbt (hb.mpr ⟨_, List.getElem?_eq_getElem hmes,
          PathOrdered.lt_of_le hO hkm hk hlt⟩), by omega⟩
    · rename_i hlh
      simp only [WP.spec_ok]
      have : high.val ≤ low.val := by scalar_tac
      exact ⟨by omega, h3, fun k hk hkl => h4 k hk (by omega)⟩
  · exact ⟨by simp, by simp [hel], fun k _ hk => absurd hk (by simp), fun k hk hk2 => by simp [hel] at hk2; omega⟩


/-- After a path that comes after `P`, no path is `P`. -/
theorem PathOrdered.ne_of_gt {es : List Entry} (hO : PathOrdered es) {P : List Nat} {j k : Nat}
    (hjk : j ≤ k) (hk : k < es.length) (hj : BytesLt P es[j].path) : es[k].path ≠ P := by
  intro hkp
  rcases Nat.lt_or_ge j k with hlt | hge
  · rcases List.pairwise_iff_getElem.mp hO j k (by omega) hk hlt with h' | h'
    · rw [hkp] at h'; exact bytesLt_irrefl _ (bytesLt_trans hj h')
    · rw [h', hkp] at hj; exact bytesLt_irrefl _ hj
  · have : j = k := by omega
    subst this; rw [hkp] at hj; exact bytesLt_irrefl _ hj

/-- **Path lookup.** In a listing in path order, `find_entry` finds a record
    that names `oid` at `path` exactly when there is one. -/
theorem find_entry_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (hO : PathOrdered es) (oid path : Slice U8) (h9 : 9 ∉ sliceBytes oid) :
    find_entry listing ends oid path ⦃ r => r.val ≤ es.length ∧
      (r.val < es.length → ∃ e, es[r.val]? = some e ∧ e.oid = sliceBytes oid ∧ e.path = sliceBytes path) ∧
      (r.val = es.length → ¬ Holds es (sliceBytes oid) (sliceBytes path)) ⦄ := by
  have hel := hL.ends_length
  unfold find_entry find_entry_loop
  step with find_path_spec hL hO path as ⟨ j0, hj0l, hbefore, hafter ⟩
  apply loop.spec_decr_nat (fun j : Usize => es.length - j.val)
    (fun j : Usize => j0.val ≤ j.val ∧ j.val ≤ es.length ∧
      ∀ k (h : k < es.length), j0.val ≤ k → k < j.val →
        ¬ (es[k].oid = sliceBytes oid ∧ es[k].path = sliceBytes path))
  · intro j ⟨h1, h2, h3⟩
    unfold find_entry_loop.body
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
    split
    · rename_i hjn
      have hj : j.val < es.length := by scalar_tac
      step with path_at_spec hL j path as ⟨ b, hb ⟩
      rw [List.getElem?_eq_getElem hj] at hb
      split
      · rename_i hbt
        obtain ⟨e, he, hep⟩ := hb.mp hbt
        rw [Option.some.injEq] at he
        obtain ⟨hdrop, hend, hok⟩ := hL.record hj
        step with record_start_spec hL j (by omega) as ⟨ st, hst ⟩
        step as ⟨ hjl, x, hx ⟩
        have hxv : x.val = st.val + (entryRecord es[j.val]).length := by
          rw [hx, ← getElem!_pos ends.val j.val hjl, hend, hst]
        step with record_is_spec listing st x oid path true es[j.val] _ hok (by rw [hst]; exact hdrop)
          hxv h9 as ⟨ b1, hb1 ⟩
        split
        · rename_i hb1t
          simp only [WP.spec_ok]
          obtain ⟨ho, -⟩ := hb1.mp hb1t
          exact ⟨by omega, fun _ => ⟨es[j.val], by simp, ho, he ▸ hep⟩, fun h => absurd h (by omega)⟩
        · rename_i hb1t
          step as ⟨ j1, hj1 ⟩
          refine ⟨by omega, by omega, fun k hk hk1 hk2 hn => ?_, by omega⟩
          rcases Nat.lt_or_ge k j.val with hlt | hge
          · exact h3 k hk hk1 hlt hn
          · have hkj : k = j.val := by omega
            subst hkj
            exact hb1t (hb1.mpr ⟨hn.1, by simp [hn.2]⟩)
      · rename_i hbt
        simp only [WP.spec_ok]
        refine ⟨by scalar_tac, fun h => absurd h (by scalar_tac), fun _ => ?_⟩
        -- `es[j]` is after `path`: so is every later entry.
        have hne : es[j.val].path ≠ sliceBytes path := fun h => hbt (hb.mpr ⟨_, rfl, h⟩)
        have hgt : BytesLt (sliceBytes path) es[j.val].path := by
          rcases bytesLt_total es[j.val].path (sliceBytes path) with h | h | h
          · exact absurd h (hafter j.val hj h1)
          · exact absurd h hne
          · exact h
        rintro ⟨e, hmem, ho, hp⟩
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
        rcases Nat.lt_or_ge k j0.val with hlt | hge
        · have := hbefore k hk hlt
          rw [hp] at this
          exact bytesLt_irrefl _ this
        rcases Nat.lt_or_ge k j.val with hlt' | hge'
        · exact h3 k hk hge hlt' ⟨ho, hp⟩
        · exact PathOrdered.ne_of_gt hO hge' hk hgt hp
    · rename_i hjn
      simp only [WP.spec_ok]
      have hj : j.val = es.length := by scalar_tac
      refine ⟨by scalar_tac, fun h => absurd h (by scalar_tac), fun _ => ?_⟩
      rintro ⟨e, hmem, ho, hp⟩
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
      rcases Nat.lt_or_ge k j0.val with hlt | hge
      · have := hbefore k hk hlt
        rw [hp] at this
        exact bytesLt_irrefl _ this
      · exact h3 k hk hge (by omega) ⟨ho, hp⟩
  · exact ⟨le_refl _, hj0l, fun k _ hk1 hk2 => absurd hk2 (by omega)⟩


/-- `held_entries` writes, for each entry `k` of the index, whether it is
    wanted and the other listing holds its blob at its path. -/
def HeldUpTo (es os : List Entry) (wanted held : Slice Bool) (n : Nat) : Prop :=
  ∀ k e, k < n → es[k]? = some e →
    (held.val[k]! = true ↔ wanted.val[k]! = true ∧ Holds os e.oid e.path)

/-- **Membership.** `held_entries` says, for every wanted index entry,
    whether the other listing (in path order) holds its blob at its path. -/
theorem held_entries_spec {index other : Slice U8} {index_ends other_ends : Slice Usize}
    {es os : List Entry} (hI : ListingOf index index_ends es) (hO : ListingOf other other_ends os)
    (hOrd : PathOrdered os) (wanted held : Slice Bool) (hw : wanted.length = es.length)
    (hh : held.length = es.length) :
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
  step with loop.spec_decr_nat (fun s : Slice Bool × Usize => es.length - s.2.val)
    (fun s : Slice Bool × Usize => s.2.val ≤ es.length ∧ s.1.length = es.length ∧ HeldUpTo es os wanted s.1 s.2.val)
    (fun h : Slice Bool => h.length = es.length ∧ HeldUpTo es os wanted h es.length) as ⟨ r, hr1, hr2 ⟩
  · rintro ⟨hd, i⟩ ⟨h1, h2, h3⟩
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
          step with find_entry_spec hO hOrd so sp h9 as ⟨ j, hj1, hj2, hj3 ⟩
          step as ⟨ s, hil', hs ⟩
          step*
          have hsv : s.val = hd.val.set i.val (decide (j < other_ends.len)) := by rw [hs]; rfl
          obtain ⟨hl', hu⟩ := hnext _ s (by
            rw [← hbw, hei, ← hso, ← hsp, hbv, decide_eq_true_iff]
            simp only [true_and]
            constructor
            · intro hjl
              obtain ⟨e', he', ho', hp'⟩ := hj2 (by scalar_tac)
              exact ⟨e', List.mem_of_getElem? he', ho', hp'⟩
            · intro hho
              by_contra hjl
              exact hj3 (by scalar_tac) hho) hsv
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

theorem keyLt_total (a b : List Nat × Nat) : KeyLt a b ∨ a = b ∨ KeyLt b a := by
  rcases bytesLt_total a.1 b.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Nat.lt_trichotomy a.2 b.2 with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl (Prod.ext h h'))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
  · exact Or.inr (Or.inr (Or.inl h))

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
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  split
  · rename_i hne
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro ho
    simp only [bne_iff_ne, ne_eq] at hne
    apply hne
    apply UScalar.eq_of_val_eq
    have := ho.1
    simp only [Slice.length] at this
    simp [this, hel]
  · rename_i hne
    have hlen : order.length = es.length := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
      have := congrArg UScalar.val hne
      simp [hel] at this; simpa [Slice.length] using this
    unfold object_order_ok_loop
    apply compare_loop _ (fun n => (∀ t (h : t < order.val.length), t < n → order.val[t].val < es.length) ∧
        ∀ t (h : t + 1 < order.val.length), t + 1 < n →
          KeyLt (keyOf es order.val[t].val) (keyOf es order.val[t + 1].val))
      order.length _ _ 0#usize (by simp) ⟨fun t _ h => absurd h (by simp), fun t _ h => absurd h (by simp)⟩
    intro t ht ⟨hr, hk⟩
    unfold object_order_ok_loop.body
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
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
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  apply loop.spec_decr_nat (fun s : Usize × Usize => s.2.val - s.1.val)
    (fun s : Usize × Usize => s.1.val ≤ s.2.val ∧ s.2.val ≤ order.val.length ∧
      (∀ t (h : t < order.val.length), t < s.1.val → KeyLt (keyOf es order.val[t].val) (sliceBytes oid, at_.val)) ∧
      (∀ t (h : t < order.val.length), s.2.val ≤ t →
        ¬ KeyLt (keyOf es order.val[t].val) (sliceBytes oid, at_.val)))
  · rintro ⟨low, high⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4 ⊢
    unfold find_object_loop.body
    split
    · rename_i hlh
      have hlh' : low.val < high.val := by scalar_tac
      step as ⟨ d, hd ⟩
      step as ⟨ d2, hd2 ⟩
      step as ⟨ mid, hmid ⟩
      have hm1 : low.val ≤ mid.val := by scalar_tac
      have hm2 : mid.val < high.val := by
        have : d2.val ≤ d.val / 2 := by scalar_tac
        have : d.val / 2 < d.val := Nat.div_lt_self (by omega) (by omega)
        scalar_tac
      have hmo : mid.val < order.val.length := by omega
      step as ⟨ hml, j, hj ⟩
      step with object_before_spec hL j oid at_ as ⟨ b, hb ⟩
      have hjv : j.val = order.val[mid.val].val := by rw [hj]
      rw [hjv] at hb
      have hjn : order.val[mid.val].val < es.length := ho.2.1 mid.val (by simpa [Slice.length] using hmo)
      split
      · rename_i hbt
        have hlt := (hb.mp hbt).2
        step as ⟨ low1, hlow1 ⟩
        refine ⟨by omega, h2, fun t ht htl => ho.lt_of_le (by omega) hmo hlt, h4, by omega⟩
      · rename_i hbt
        simp only [WP.spec_ok]
        refine ⟨hm1, by omega, h3, fun t ht htm hlt => hbt (hb.mpr ⟨hjn, ho.lt_of_le htm ht hlt⟩), by omega⟩
    · rename_i hlh
      simp only [WP.spec_ok]
      have : high.val ≤ low.val := by scalar_tac
      exact ⟨by omega, h3, fun t ht htl => h4 t ht (by omega)⟩
  · exact ⟨by simp, by simp, fun t _ ht => absurd ht (by simp), fun t ht ht2 => by simp at ht2; omega⟩

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
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
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
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
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

/-- Distinct entries of a sorted snapshot have distinct paths. -/
theorem Sorted.path_ne {es : List Entry} (hS : Sorted es) {a b : Nat} (ha : a < es.length) (hb : b < es.length)
    (hab : a ≠ b) : es[a].path ≠ es[b].path := by
  intro heq
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · have := List.pairwise_iff_getElem.mp hS a b ha hb h
    rw [heq] at this; exact bytesLt_irrefl _ this
  · have := List.pairwise_iff_getElem.mp hS b a hb ha h
    rw [heq] at this; exact bytesLt_irrefl _ this

/-- A sorted listing has the blob `oid` at another path than `path`
    exactly when `elsewhere_in` says so: its records of `oid` are together
    in the object order, at most one of them at `path`. -/
theorem elsewhere_in_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (hS : Sorted es) {order : Slice Usize} (ho : ObjectOrder es order)
    (oid path : Slice U8) (h9 : 9 ∉ sliceBytes oid) :
    elsewhere_in listing ends order oid path ⦃ b => b = true ↔
      ∃ e ∈ es, e.oid = sliceBytes oid ∧ e.path ≠ sliceBytes path ⦄ := by
  unfold elsewhere_in
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
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

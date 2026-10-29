import V3Wire.Verification.Attr
import V3Wire.Verification.Index
import V3Wire.Verification.Envelope

/-!
Git snapshot listings, part 1: the shape of a listing. `ListingOf` says a
listing is exactly `Transcrypt.V3Policy.listingBytes es` of well-formed
entries with the end of each record recorded; `record_start`, `record_is`
and `listing_fields` (`listing_fields_spec`, `FieldsOf.slices`) read one
record of such a listing.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core
open Transcrypt.V3Policy

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
theorem entryRecord_drop_oidStart (e : Entry) (he : e.mode.length = modeLen) (rest : List Nat) :
    (entryRecord e ++ rest).drop oidStart = e.oid ++ [32, 48, 9] ++ e.path ++ rest := by
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

/-- An object id followed by `SP 0 TAB` is determined by the record it
    starts: TAB-free ids, so the first TAB is right after it. -/
theorem tab_prefix_iff {q o r : List Nat} (hq : 9 ∉ q) (ho : 9 ∉ o) :
    q ++ [32, 48, 9] <+: o ++ [32, 48, 9] ++ r ↔ q = o := by
  constructor
  · intro h
    have h1 := first_tab_of_prefix hq h
    have h2 := first_tab_of_prefix ho (List.prefix_append (o ++ [32, 48, 9]) r)
    have hl : q.length = o.length := by
      have := eq_of_first (P := fun k => _ = some 9) h1.1 h1.2 h2.1 h2.2; omega
    have hq1 : q <+: o ++ [32, 48, 9] ++ r := (List.prefix_append q _).trans h
    have ho1 : o <+: o ++ [32, 48, 9] ++ r :=
      (List.prefix_append o [32, 48, 9]).trans (List.prefix_append _ r)
    exact (List.prefix_of_prefix_length_le hq1 ho1 hl.le).eq_of_length hl
  · rintro rfl
    exact List.prefix_append _ _

end Pure

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
  have h9o := objectId_no_tab hoid
  have hD : (sliceBytes listing).drop (start.val + oidStart) = e.oid ++ [32, 48, 9] ++ e.path ++ rest := by
    rw [← List.drop_drop, hd, entryRecord_drop_oidStart e hm]
  -- If the record names `oid`, it starts with `oid SP 0 TAB`.
  have hnames : e.oid = sliceBytes oid →
      sliceBytes oid ++ [32, 48, 9] <+: (sliceBytes listing).drop (start.val + oidStart) := by
    intro h
    rw [hD, ← h, List.append_assoc]
    exact List.prefix_append _ _
  have hol : e.oid = sliceBytes oid → oid.length = e.oid.length := by
    intro h; rw [h, sliceBytes_length]
  have hlenv : oid.len.val = oid.length := by simp
  have hb_of : e.oid = sliceBytes oid → start.val + oidStart ≤ listing.length ∧
      sliceBytes oid <+: (sliceBytes listing).drop (start.val + oidStart) := fun h =>
    ⟨by scalar_tac, (List.prefix_append _ _).trans (hnames h)⟩
  have hb1_of : e.oid = sliceBytes oid → start.val + oidStart + oid.length ≤ listing.length ∧
      [32, 48, 9] <+: (sliceBytes listing).drop (start.val + oidStart + oid.length) := by
    intro h
    have := hnames h
    rw [prefix_append_iff, List.drop_drop, sliceBytes_length] at this
    exact ⟨by have := hol h; scalar_tac, this.2⟩
  unfold record_is
  simp_len
  have hmax := listing.property
  step*
  -- (`step*` refutes a record too short for `oid` and a mismatching id with
  -- `hol` and `hb_of`.)
  -- `SP 0 TAB` does not follow: the record names another object.
  case h2 =>
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro h _
    apply ‹¬b1 = true›
    rw [b1_post, s_post, OID_END_bytes, at_post, i4_post, OID_START_val, hlenv]
    exact hb1_of h
  -- The record names `oid`: compare the path.
  have hoid' : sliceBytes oid = e.oid := by
    have h1 := (b_post.mp ‹b = true›).2
    have h2 := (b1_post.mp ‹b1 = true›).2
    rw [s_post, OID_END_bytes, at_post, i4_post, OID_START_val, hlenv, ← sliceBytes_length oid, ← List.drop_drop] at h2
    rw [i4_post, OID_START_val] at h1
    have := (prefix_append_iff (sliceBytes oid) [32, 48, 9] _).mpr ⟨h1, h2⟩
    rw [hD] at this
    exact (tab_prefix_iff h9 h9o).mp (by simpa only [List.append_assoc] using this)
  have hpl : i6.val = e.path.length := by
    rw [i6_post1, i5_post1, at_post, i4_post, OID_START_val, ht, hrl, hlenv, ← sliceBytes_length oid, hoid']
    unfold_v3_bytes; omega
  have hP : (sliceBytes listing).drop («at».val + 3) = e.path ++ rest := by
    rw [at_post, i4_post, OID_START_val, hlenv, ← sliceBytes_length oid, hoid', show start.val + oidStart + e.oid.length + 3 =
      (start.val + oidStart) + (e.oid.length + 3) by omega, ← List.drop_drop, hD]
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

/-! ## `listing_fields` -/

/-- The first TAB of a record is right after its object id and `SP 0`. -/
theorem record_tab {L : List Nat} {s : Nat} {e : Entry} {rest : List Nat} (he : EntryOk e)
    (hd : L.drop s = entryRecord e ++ rest) :
    s + 9 + e.oid.length < L.length ∧ L[s + 9 + e.oid.length]! = 9 ∧
      ∀ k, s ≤ k → k < s + 9 + e.oid.length → L[k]! ≠ 9 := by
  obtain ⟨hm, h9m, _, hoid, hp, _⟩ := he
  unfold_v3_bytes
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
    is `[start + oidStart, oid_end)`, the path `[path_start, end)`) and whether its
    mode is regular. -/
def FieldsOf (es : List Entry) (i : Nat) (f : Fields) : Prop :=
  ∃ e, es[i]? = some e ∧ f.start.val = off es i ∧ f.oid_end.val = off es i + oidStart + e.oid.length ∧
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
  simp_len [bind_tc_ok]
  split
  · rename_i hge
    simp only [WP.spec_ok]
    scalar_tac
  · rename_i hlt
    have hi : i.val < es.length := by scalar_tac
    obtain ⟨hdrop, hend, hok⟩ := hL.record hi
    obtain ⟨tl, tv, tno⟩ := record_tab hok hdrop
    have hm := hok.1
    have hoidl : 40 ≤ es[i.val].oid.length := by rcases hok.2.2.2.1.1 with h | h <;> unfold_v3_bytes <;> omega
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
    have hmode : ∀ (M : Std.Array U8 6#usize) (m : List Nat), sliceBytes (Array.to_slice M) = m →
        ∀ c : Bool,
        (c = true ↔ st.val ≤ listing.length ∧
          sliceBytes (Array.to_slice M) <+: (sliceBytes listing).drop st.val) →
        (c = true ↔ es[i.val].mode = m) := by
      intro M m hM c hc
      have hml : m.length = 6 := by rw [← hM, sliceBytes_length]; simp
      rw [hc, hM, record_mode hm hdrop m hml]
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    step*
    have hb' := hmode _ _ REGULAR_MODE_bytes b (by rw [← s_post]; exact b_post)
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
      · rw [i4_post1, htv, hst]; unfold_v3_bytes; omega
      · rw [i5_post, htv, hst]; omega
    split
    · rename_i hbt
      simp only [bind_tc_ok]
      exact hpost true ⟨fun _ => Or.inl (hb'.mp hbt), fun _ => rfl⟩
    · rename_i hbt
      step as ⟨ s1, hs1 ⟩
      step with matches_at_spec as ⟨ b1, hb1 ⟩
      have hb1' := hmode _ _ EXECUTABLE_MODE_bytes b1 (by rw [← hs1]; exact hb1)
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
      (sliceBytes listing).extract (f.start.val + oidStart) f.oid_end.val = e.oid ∧
      (sliceBytes listing).extract f.path_start.val f.end.val = e.path ∧
      f.start.val + oidStart ≤ f.oid_end.val ∧ f.oid_end.val ≤ listing.length ∧
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
  have hDoid : (sliceBytes listing).drop (off es i + oidStart) = e.oid ++ [32, 48, 9] ++ e.path ++
      (0 :: listingBytes (es.drop (i + 1))) := by
    rw [← List.drop_drop, hdrop, entryRecord_drop_oidStart e hm]
  have hD10 : (sliceBytes listing).drop (off es i + 10 + e.oid.length) =
      e.path ++ (0 :: listingBytes (es.drop (i + 1))) := by
    rw [show off es i + 10 + e.oid.length = (off es i + oidStart) + (e.oid.length + 3) by unfold_v3_bytes; omega,
      ← List.drop_drop, hDoid]
    simp
  refine ⟨e, he, hok, ?_, ?_, by omega, by unfold_v3_bytes; omega, by omega, by omega⟩
  · rw [List.extract_eq_take_drop, hs, ho, hDoid, show off es i + oidStart + e.oid.length - (off es i + oidStart) =
      e.oid.length by omega]
    simp
  · rw [List.extract_eq_take_drop, hp, hend, hD10, show off es i + (entryRecord e).length -
      (off es i + 10 + e.oid.length) = e.path.length by omega]
    simp

end Transcrypt.V3Verification

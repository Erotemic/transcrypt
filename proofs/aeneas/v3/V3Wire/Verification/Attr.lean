import V3Wire.Verification.Path
import Transcrypt.V3Policy
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
namespace Transcrypt.V3Verification
open transcrypt_v3_core

/-!
Functional refinement of the production Git attribute-record parser
`parse_attr_record` (and its helper `find_nul`) against the independent
specification's `AttrRecordAt`: the parser accepts exactly the spec's
`git check-attr -z filter` record for the requested path at the given
offset, and reports exactly whether its value selects the v3 filter. A model
of the adapter's loop over a whole response (`attrFlagsModel`, mirroring
`transcrypt_v3::git::protected_flags`) succeeds exactly on Git's complete
answer `attrResponse` for the requested paths and returns their selections.
-/

/-! ## Pure facts about attribute records -/

section Pure
open Transcrypt.V3Policy

theorem prefix_append_iff {α : Type} (a b l : List α) :
    a ++ b <+: l ↔ a <+: l ∧ b <+: l.drop a.length := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨b ++ t, by simp⟩, ⟨t, by simp⟩⟩
  · rintro ⟨⟨u, rfl⟩, ⟨t, ht⟩⟩
    simp only [List.drop_left] at ht
    exact ⟨t, by rw [← ht]; simp⟩

theorem singleton_prefix_drop_iff (x : Nat) (l : List Nat) (k : Nat) :
    [x] <+: l.drop k ↔ l[k]? = some x := by
  by_cases hk : k < l.length
  · rw [List.drop_eq_getElem_cons hk, List.getElem?_eq_getElem hk, List.cons_prefix_cons]
    simp [eq_comm]
  · rw [List.drop_eq_nil_of_le (by omega), List.getElem?_eq_none (by omega)]
    simp

theorem filterAttr_length : filterAttr.length = 6 := by decide

theorem attrRecord_length (P v : List Nat) :
    (attrRecord P v).length = P.length + v.length + 9 := by
  simp [attrRecord, filterAttr_length]; omega

/-- A record at offset `s` is its path, a NUL, `filter`, a NUL, the value and
    a final NUL, at the corresponding offsets. -/
theorem attrRecord_prefix_iff (R P v : List Nat) (s : Nat) :
    attrRecord P v <+: R.drop s ↔
      P <+: R.drop s ∧ R[s + P.length]? = some 0 ∧
      filterAttr <+: R.drop (s + P.length + 1) ∧ R[s + P.length + 7]? = some 0 ∧
      v <+: R.drop (s + P.length + 8) ∧ R[s + P.length + 8 + v.length]? = some 0 := by
  have : attrRecord P v = P ++ ([0] ++ (filterAttr ++ ([0] ++ (v ++ [0])))) := by
    simp [attrRecord]
  rw [this]
  simp only [prefix_append_iff, List.drop_drop, singleton_prefix_drop_iff, filterAttr_length,
    List.length_singleton]

/-- A NUL-free prefix that is followed by NUL is determined by the list. -/
theorem nul_free_prefix_unique {D v v' : List Nat} (hv : v <+: D) (hv' : v' <+: D)
    (h0 : 0 ∉ v) (h0' : 0 ∉ v') (hz : D[v.length]? = some 0) (hz' : D[v'.length]? = some 0) :
    v = v' := by
  have key : ∀ {a b : List Nat}, a <+: D → b <+: D → 0 ∉ b → D[a.length]? = some 0 →
      ¬ a.length < b.length := by
    intro a b _ hb h0b hza hlt
    obtain ⟨t, rfl⟩ := hb
    rw [List.getElem?_append_left hlt] at hza
    exact h0b (List.mem_of_getElem? hza)
  have hl : v.length = v'.length := by
    have := key hv hv' h0' hz
    have := key hv' hv h0 hz'
    omega
  rcases List.prefix_of_prefix_length_le hv hv' (by omega) with h
  exact h.eq_of_length hl

/-- At a given offset, the record for a given path is unique. -/
theorem attrRecordAt_unique {R P v v' : List Nat} {s n n' : Nat}
    (h : AttrRecordAt R s P v n) (h' : AttrRecordAt R s P v' n') : v = v' ∧ n = n' := by
  obtain ⟨h0, hp, hn⟩ := h
  obtain ⟨h0', hp', hn'⟩ := h'
  rw [attrRecord_prefix_iff] at hp hp'
  have hz : (R.drop (s + P.length + 8))[v.length]? = some 0 := by
    rw [List.getElem?_drop]; exact hp.2.2.2.2.2
  have hz' : (R.drop (s + P.length + 8))[v'.length]? = some 0 := by
    rw [List.getElem?_drop]; exact hp'.2.2.2.2.2
  have hv := nul_free_prefix_unique hp.2.2.2.2.1 hp'.2.2.2.2.1 h0 h0' hz hz'
  subst hv
  exact ⟨rfl, by rw [hn, hn']⟩

theorem attrResponse_append (a b : List (List Nat × List Nat)) :
    attrResponse (a ++ b) = attrResponse a ++ attrResponse b := by
  simp [attrResponse, List.flatMap_append]

theorem attrResponse_take_succ (rs : List (List Nat × List Nat)) (i : Nat) (h : i < rs.length) :
    attrResponse (rs.take (i + 1)) = attrResponse (rs.take i) ++ attrRecord rs[i].1 rs[i].2 := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, attrResponse_append]
  simp [attrResponse]

/-- Git's complete answer for a list of records holds each record at the
    offset where the previous ones end. -/
theorem attrResponse_recordAt (rs : List (List Nat × List Nat)) (hv : ∀ r ∈ rs, 0 ∉ r.2)
    (i : Nat) (h : i < rs.length) :
    AttrRecordAt (attrResponse rs) (attrResponse (rs.take i)).length rs[i].1 rs[i].2
      (attrResponse (rs.take (i + 1))).length := by
  refine ⟨hv _ (List.getElem_mem h), ?_, ?_⟩
  · have : attrResponse rs = attrResponse (rs.take i) ++
        (attrRecord rs[i].1 rs[i].2 ++ attrResponse (rs.drop (i + 1))) := by
      rw [← List.append_assoc, ← attrResponse_take_succ rs i h, ← attrResponse_append,
        List.take_append_drop]
    rw [this, List.drop_left]
    exact List.prefix_append _ _
  · rw [attrResponse_take_succ rs i h, List.length_append]

end Pure

/-! ## `find_nul` -/

/-- `j` is reached from `f` over non-NUL bytes of `l`: either within `l`, or
    `j = f` when `f` is past the end. -/
def NulScan (l : List Nat) (f j : Nat) : Prop :=
  f ≤ j ∧ (j ≤ l.length ∨ j = f) ∧ ∀ k, f ≤ k → k < j → l[k]! ≠ 0

theorem find_nul_loop_spec (bytes : Slice U8) (f j : Usize)
    (h : NulScan (sliceBytes bytes) f.val j.val) :
    find_nul_loop bytes j ⦃ r => NulScan (sliceBytes bytes) f.val r.val ∧
      (r.val < bytes.length → (sliceBytes bytes)[r.val]! = 0) ⦄ := by
  unfold find_nul_loop
  apply loop.spec_decr_nat (fun s => bytes.length - s.val)
    (fun s => NulScan (sliceBytes bytes) f.val s.val)
  · intro j hj
    unfold find_nul_loop.body
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
    have hl := sliceBytes_length bytes
    step*
    · obtain ⟨h1, _, h3⟩ := hj
      subst i1_post2
      have hb : (sliceBytes bytes)[j.val]! ≠ 0 := by
        have := ‹(_ != 0#u8) = true›
        simp only [bne_iff_ne, ne_eq] at this
        rw [sliceBytes_getElem! bytes j.val i1]
        exact fun h0 => this (UScalar.eq_of_val_eq h0)
      refine ⟨⟨by omega, Or.inl (by omega), fun k hk1 hk2 => ?_⟩, by omega⟩
      rcases Nat.lt_or_ge k j.val with hlt | hge
      · exact h3 k hk1 hlt
      · rw [show k = j.val by omega]; exact hb
    · refine ⟨hj, fun _ => ?_⟩
      subst i1_post2
      have := ‹¬(_ != 0#u8) = true›
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
      rw [sliceBytes_getElem! bytes j.val i1, this]
      rfl
  · exact h

/-- `find_nul bytes from` is the first NUL at or after `from`, or the end of
    `bytes` (and `from` itself when `from` is past the end). -/
@[step]
theorem find_nul_spec (bytes : Slice U8) (f : Usize) :
    find_nul bytes f ⦃ r => NulScan (sliceBytes bytes) f.val r.val ∧
      (r.val < bytes.length → (sliceBytes bytes)[r.val]! = 0) ⦄ := by
  unfold find_nul
  exact find_nul_loop_spec bytes f f ⟨le_refl _, Or.inr rfl, fun k h1 h2 => absurd h2 (by omega)⟩

theorem index_range_spec (s : Slice U8) (a b : Usize) (hab : a.val ≤ b.val) (hb : b.val ≤ s.length) :
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      s { start := a, «end» := b } ⦃ r => sliceBytes r = (sliceBytes s).extract a.val b.val ⦄ := by
  unfold core.Slice.Insts.CoreOpsIndexIndex.index
  simp only [core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_slice, rust_primitives.slice.slice_length]
  have h1 : a ≤ b := by scalar_tac
  have h2 : b ≤ s.len := by scalar_tac
  simp only [h1, h2, if_true, Slice.subslice, bind_tc_ok]
  rw [if_pos ⟨hab, hb⟩]
  simp [sliceBytes, List.slice, List.map_take, List.map_drop]

/-! ## `parse_attr_record` -/

theorem FILTER_ATTR_bytes :
    sliceBytes (Array.to_slice FILTER_ATTR) = Transcrypt.V3Policy.filterAttr := by
  unfold FILTER_ATTR Transcrypt.V3Policy.filterAttr Transcrypt.V3Policy.ascii sliceBytes
  decide

theorem FILTER_DRIVER_bytes :
    sliceBytes (Array.to_slice FILTER_DRIVER) = Transcrypt.V3Policy.filterDriver := by
  unfold FILTER_DRIVER Transcrypt.V3Policy.filterDriver Transcrypt.V3Policy.ascii sliceBytes
  decide

theorem FILTER_ATTR_slice_length (t : Slice U8) (ht : t = Array.to_slice FILTER_ATTR) :
    t.len.val = 6 := by
  have := congrArg List.length FILTER_ATTR_bytes
  rw [sliceBytes_length, filterAttr_length] at this
  subst ht; simp at this ⊢

theorem getElem?_eq_some_iff' (l : List Nat) (k x : Nat) :
    l[k]? = some x ↔ k < l.length ∧ l[k]! = x := by
  constructor
  · intro h
    obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp h
    exact ⟨hk, by rw [getElem!_pos l k hk, he]⟩
  · rintro ⟨hk, he⟩
    rw [List.getElem?_eq_getElem hk, ← getElem!_pos l k hk, he]

theorem byte_zero_iff (R : Slice U8) (k : Nat) (hk : k < R.length) :
    (sliceBytes R)[k]! = 0 ↔ R.val[k] = 0#u8 := by
  rw [sliceBytes_getElem! R k hk]
  constructor
  · intro h; exact UScalar.eq_of_val_eq (by simpa using h)
  · intro h; rw [h]; rfl

/-- Everything a record at `s` says about the bytes of the response. -/
theorem attrRecordAt_facts {R P v : List Nat} {s n : Nat}
    (h : Transcrypt.V3Policy.AttrRecordAt R s P v n) :
    s + P.length + 8 + v.length < R.length ∧ P <+: R.drop s ∧ R[s + P.length]! = 0 ∧
      Transcrypt.V3Policy.filterAttr <+: R.drop (s + P.length + 1) ∧
      R[s + P.length + 7]! = 0 ∧ 0 ∉ v ∧ v <+: R.drop (s + P.length + 8) ∧
      R[s + P.length + 8 + v.length]! = 0 ∧ n = s + P.length + v.length + 9 := by
  obtain ⟨h0, hp, hn⟩ := h
  rw [attrRecord_prefix_iff, getElem?_eq_some_iff', getElem?_eq_some_iff',
    getElem?_eq_some_iff'] at hp
  rw [attrRecord_length] at hn
  exact ⟨hp.2.2.2.2.2.1, hp.1, hp.2.1.2, hp.2.2.1, hp.2.2.2.1.2, h0, hp.2.2.2.2.1,
    hp.2.2.2.2.2.2, by rw [hn]; omega⟩

/-- **The attribute parser accepts exactly the spec's records.** On success
    the record for `path` with some value lies at `start`, `next` is where it
    ends, and `protected` says whether that value selects the v3 filter; on
    failure no record for `path` lies at `start`. -/
@[step]
theorem parse_attr_record_spec (response : Slice U8) (start : Usize) (path : Slice U8) :
    parse_attr_record response start path ⦃ r => match r with
      | core.result.Result.Ok a => ∃ value,
          Transcrypt.V3Policy.AttrRecordAt (sliceBytes response) start.val (sliceBytes path)
            value a.next.val ∧
          (a.protected = true ↔ Transcrypt.V3Policy.Selected value)
      | core.result.Result.Err e => e = Refusal.Attribute ∧
          ¬ ∃ value next, Transcrypt.V3Policy.AttrRecordAt (sliceBytes response) start.val
            (sliceBytes path) value next ⦄ := by
  unfold parse_attr_record
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hRl := sliceBytes_length response
  have hPl := sliceBytes_length path
  have hmax := response.property
  step*
  -- `start` is past the end.
  · rintro ⟨v, n, hrec⟩
    have F := attrRecordAt_facts hrec
    rw [hRl, hPl] at F
    scalar_tac
  -- Too short for the path.
  · rintro ⟨v, n, hrec⟩
    have F := attrRecordAt_facts hrec
    rw [hRl, hPl] at F
    scalar_tac
  -- Too short for any record.
  · rintro ⟨v, n, hrec⟩
    have F := attrRecordAt_facts hrec
    rw [hRl, hPl] at F
    have := FILTER_ATTR_slice_length s s_post
    scalar_tac
  -- No NUL after the path.
  · rintro ⟨v, n, hrec⟩
    have F := attrRecordAt_facts hrec
    rw [hPl] at F
    subst i5_post2
    have := ‹(_ != 0#u8) = true›
    simp only [bne_iff_ne, ne_eq] at this
    apply this
    rw [← byte_zero_iff response name.val i5, name_post]
    simpa using F.2.2.1
  -- No NUL after `filter`.
  · rintro ⟨v, n, hrec⟩
    have F := attrRecordAt_facts hrec
    rw [hPl] at F
    subst i9_post2
    have := ‹(_ != 0#u8) = true›
    simp only [bne_iff_ne, ne_eq] at this
    apply this
    have h6 := FILTER_ATTR_slice_length s2 s2_post
    rw [← byte_zero_iff response i8.val i9, i8_post, i6_post, name_post, h6]
    simpa using F.2.2.2.2.1
  -- No NUL terminates the value.
  · rintro ⟨v, n, hrec⟩
    have F := attrRecordAt_facts hrec
    rw [hRl, hPl] at F
    have h6 := FILTER_ATTR_slice_length s3 s3_post
    have hend : «end».val = response.length := by
      have := congrArg UScalar.val ‹«end» = response.len›; simpa using this
    have hval : value.val = start.val + path.length + 8 := by
      rw [value_post, i11_post, name_post, h6]; simp
    obtain ⟨_, _, hscan⟩ := end_post1
    apply hscan (start.val + path.length + 8 + v.length) (by omega) (by omega)
    exact F.2.2.2.2.2.2.2.1
  -- Success.
  · have h6 := FILTER_ATTR_slice_length s3 s3_post
    have hval : value.val = start.val + path.length + 8 := by
      rw [value_post, i11_post, name_post, h6]; simp
    have hlen : start.val + path.length + 9 ≤ response.length := by
      have := FILTER_ATTR_slice_length s s_post
      scalar_tac
    obtain ⟨hve, hlim, hscan⟩ := end_post1
    have hend_lt : «end».val < response.length := by
      have : «end».val ≠ response.length := fun h =>
        ‹¬«end» = response.len› (by apply UScalar.eq_of_val_eq; simpa using h)
      rw [hRl] at hlim
      omega
    step with index_range_spec response value «end» hve (by omega) as ⟨ s4, hs4 ⟩
    step*
    refine ⟨(sliceBytes response).extract value.val «end».val, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro hm
      obtain ⟨k, hk, hk0⟩ := List.getElem_of_mem hm
      simp only [List.extract_eq_take_drop, List.getElem_take, List.getElem_drop,
        List.length_take, List.length_drop] at hk hk0
      apply hscan (value.val + k) (by omega) (by omega)
      rw [getElem!_pos _ _ (by rw [hRl]; omega), hk0]
    · rw [attrRecord_prefix_iff, getElem?_eq_some_iff', getElem?_eq_some_iff',
        getElem?_eq_some_iff', hPl, hRl]
      have hb := b_post.mp ‹b = true›
      have hb1 := b1_post.mp ‹b1 = true›
      have hpl : path.len.val = path.length := by simp
      rw [s1_post, FILTER_ATTR_bytes, i6_post, name_post, hpl] at hb1
      have hz1 : (sliceBytes response)[start.val + path.length]! = 0 := by
        subst i5_post2
        have := ‹¬(_ != 0#u8) = true›
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
        have hn : name.val = start.val + path.length := by rw [name_post]; simp
        rw [← hn]; exact (byte_zero_iff response name.val i5).mpr this
      have hz7 : (sliceBytes response)[start.val + path.length + 7]! = 0 := by
        subst i9_post2
        have := ‹¬(_ != 0#u8) = true›
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
        have h6' := FILTER_ATTR_slice_length s2 s2_post
        have : i8.val = start.val + path.length + 7 := by
          rw [i8_post, i6_post, name_post, h6']; simp
        rw [← this]; exact (byte_zero_iff response i8.val i9).mpr ‹_›
      have hextl : ((sliceBytes response).extract value.val «end».val).length =
          «end».val - value.val := by
        simp only [List.extract_eq_take_drop, List.length_take, List.length_drop, hRl]; omega
      refine ⟨hb.2, ⟨by omega, hz1⟩, by simpa using hb1.2, ⟨by omega, hz7⟩, ?_, ?_, ?_⟩
      · rw [← hval, List.extract_eq_take_drop]
        exact List.take_prefix _ _
      · rw [hextl]; omega
      · rw [hextl, show start.val + path.length + 8 + («end».val - value.val) = «end».val by omega]
        exact end_post2 hend_lt
    · rw [i12_post, attrRecord_length, hPl]
      simp only [List.extract_eq_take_drop, List.length_take, List.length_drop, hRl]
      omega
    · rw [b2_post, ← sliceBytes_inj, hs4, s5_post, FILTER_DRIVER_bytes]
      rfl
  -- `filter` does not follow.
  · rintro ⟨v, n, hrec⟩
    have F := attrRecordAt_facts hrec
    rw [hRl, hPl] at F
    apply ‹¬b1 = true›
    rw [b1_post, s1_post, FILTER_ATTR_bytes, i6_post, name_post]
    exact ⟨by scalar_tac, by simpa using F.2.2.2.1⟩
  -- The path does not match.
  · rintro ⟨v, n, hrec⟩
    have F := attrRecordAt_facts hrec
    rw [hRl] at F
    apply ‹¬b = true›
    rw [b_post]
    exact ⟨by omega, F.2.1⟩

/-! ## The adapter's loop over a whole `check-attr` response -/

instance (v : List Nat) : Decidable (Transcrypt.V3Policy.Selected v) :=
  inferInstanceAs (Decidable (v = Transcrypt.V3Policy.filterDriver))

/-- Model of the record loop of `transcrypt_v3::git::protected_flags`: parse
    one record per requested path, in order, each starting where the previous
    one ended; the response must end exactly after the last record. `none` =
    refusal ("unexpected git check-attr output"). -/
def attrFlagsLoop (response : Slice U8) : Usize → List (Slice U8) → RustM (Option (List Bool))
  | at_, [] => ok (if at_ = response.len then some [] else none)
  | at_, p :: ps => do
    let r ← parse_attr_record response at_ p
    match r with
    | core.result.Result.Ok a => do
      let rest ← attrFlagsLoop response a.next ps
      ok (rest.map (a.protected :: ·))
    | core.result.Result.Err _ => ok none

def attrFlagsModel (response : Slice U8) (paths : List (Slice U8)) : RustM (Option (List Bool)) :=
  attrFlagsLoop response 0#usize paths

theorem drop_eq_of_prefix_drop {l p : List Nat} {a : Nat} (h : p <+: l.drop a) :
    l.drop a = p ++ l.drop (a + p.length) := by
  obtain ⟨t, ht⟩ := h
  rw [← ht, ← List.drop_drop, ← ht, List.drop_left]

theorem attrFlagsLoop_sound (response : Slice U8) (paths : List (Slice U8)) (at_ : Usize) :
    attrFlagsLoop response at_ paths ⦃ r => ∀ flags, r = some flags →
      ∃ values : List (List Nat), values.length = paths.length ∧ (∀ v ∈ values, 0 ∉ v) ∧
        (sliceBytes response).drop at_.val =
          Transcrypt.V3Policy.attrResponse ((paths.map sliceBytes).zip values) ∧
        flags = values.map (fun v => decide (Transcrypt.V3Policy.Selected v)) ⦄ := by
  induction paths generalizing at_ with
  | nil =>
    simp only [attrFlagsLoop]
    split
    · rename_i heq
      simp only [WP.spec_ok, Option.some.injEq]
      rintro flags rfl
      refine ⟨[], rfl, by simp, ?_, rfl⟩
      rw [heq, List.drop_eq_nil_of_le (by simp [sliceBytes_length])]
      simp [Transcrypt.V3Policy.attrResponse]
    · simp
  | cons p ps ih =>
    simp only [attrFlagsLoop]
    step with parse_attr_record_spec response at_ p as ⟨ r, hr ⟩
    rcases r with a | e
    · obtain ⟨v, hrec, hprot⟩ := hr
      simp only
      apply WP.spec_bind (ih a.next)
      intro rest hrest
      simp only [WP.spec_ok]
      intro flags hflags
      cases rest with
      | none => cases hflags
      | some fs =>
        simp only [Option.map_some, Option.some.injEq] at hflags
        subst hflags
        obtain ⟨vs, hl, h0, hd, hf⟩ := hrest fs rfl
        obtain ⟨hv0, hp, hn⟩ := hrec
        refine ⟨v :: vs, by simp [hl], ?_, ?_, ?_⟩
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact hv0
          · exact h0 w hw
        · rw [drop_eq_of_prefix_drop hp, ← hn, hd]
          simp [Transcrypt.V3Policy.attrResponse]
        · rw [hf]
          simp only [List.map_cons, List.cons.injEq, and_true]
          cases hpr : a.protected <;> simp_all
    · simp

/-- **Soundness of the adapter's attribute loop.** If it returns flags, the
    whole response is exactly Git's answer `attrResponse` for the requested
    paths, in order, with some NUL-free values, and each flag says whether
    the corresponding value selects the v3 filter. -/
theorem attrFlagsModel_sound (response : Slice U8) (paths : List (Slice U8)) :
    attrFlagsModel response paths ⦃ r => ∀ flags, r = some flags →
      ∃ values : List (List Nat), values.length = paths.length ∧ (∀ v ∈ values, 0 ∉ v) ∧
        sliceBytes response =
          Transcrypt.V3Policy.attrResponse ((paths.map sliceBytes).zip values) ∧
        flags = values.map (fun v => decide (Transcrypt.V3Policy.Selected v)) ⦄ := by
  unfold attrFlagsModel
  apply WP.spec_mono (attrFlagsLoop_sound response paths 0#usize)
  intro r hr flags hf
  simpa using hr flags hf

theorem attrFlagsLoop_complete (response : Slice U8)
    (qs : List (List Nat × List Nat)) (hv : ∀ q ∈ qs, 0 ∉ q.2)
    (paths : List (Slice U8)) (hp : paths.map sliceBytes = qs.map (·.1)) (at_ : Usize)
    (hat : at_.val ≤ response.length)
    (hR : (sliceBytes response).drop at_.val = Transcrypt.V3Policy.attrResponse qs) :
    attrFlagsLoop response at_ paths ⦃ r =>
      r = some (qs.map (fun q => decide (Transcrypt.V3Policy.Selected q.2))) ⦄ := by
  induction paths generalizing qs at_ with
  | nil =>
    cases qs with
    | cons q qs => simp at hp
    | nil =>
      simp only [attrFlagsLoop]
      have : at_.val = response.length := by
        have := congrArg List.length hR
        simp only [List.length_drop, sliceBytes_length, Transcrypt.V3Policy.attrResponse,
          List.flatMap_nil, List.length_nil] at this
        omega
      rw [if_pos (by apply UScalar.eq_of_val_eq; simpa using this)]
      simp
  | cons p ps ih =>
    cases qs with
    | nil => simp at hp
    | cons q qs =>
      simp only [List.map_cons, List.cons.injEq] at hp
      obtain ⟨hp1, hps⟩ := hp
      have hrec : Transcrypt.V3Policy.AttrRecordAt (sliceBytes response) at_.val q.1 q.2
          (at_.val + (Transcrypt.V3Policy.attrRecord q.1 q.2).length) := by
        refine ⟨hv q (by simp), ?_, rfl⟩
        rw [hR]
        simp [Transcrypt.V3Policy.attrResponse]
      have hlen : at_.val + (Transcrypt.V3Policy.attrRecord q.1 q.2).length ≤ response.length := by
        have := congrArg List.length hR
        simp only [List.length_drop, sliceBytes_length, Transcrypt.V3Policy.attrResponse,
          List.flatMap_cons, List.length_append] at this
        omega
      simp only [attrFlagsLoop]
      step with parse_attr_record_spec response at_ p as ⟨ r, hr ⟩
      rcases r with a | e
      · obtain ⟨v, hrec', hprot⟩ := hr
        rw [hp1] at hrec'
        obtain ⟨rfl, hnext⟩ := attrRecordAt_unique hrec' hrec
        simp only
        apply WP.spec_bind (ih qs (fun q hq => hv q (by simp [hq])) hps a.next
          (by rw [hnext]; exact hlen) ?_)
        · intro rest hrest
          rw [hrest]
          simp only [Option.map_some, WP.spec_ok, List.map_cons, Option.some.injEq,
            List.cons.injEq, and_true]
          cases hpr : a.protected <;> simp_all
        · rw [hnext, ← List.drop_drop, hR]
          simp [Transcrypt.V3Policy.attrResponse]
      · exfalso
        apply hr.2
        rw [hp1]
        exact ⟨q.2, _, hrec⟩

/-- **Completeness of the adapter's attribute loop.** On Git's complete answer
    for the requested paths with NUL-free values, the loop parses every record
    back in order (ending exactly at the end of the response) and returns
    exactly whether each value selects the v3 filter. -/
theorem attrFlagsModel_complete (response : Slice U8)
    (qs : List (List Nat × List Nat)) (hv : ∀ q ∈ qs, 0 ∉ q.2)
    (paths : List (Slice U8)) (hp : paths.map sliceBytes = qs.map (·.1))
    (hR : sliceBytes response = Transcrypt.V3Policy.attrResponse qs) :
    attrFlagsModel response paths ⦃ r =>
      r = some (qs.map (fun q => decide (Transcrypt.V3Policy.Selected q.2))) ⦄ :=
  attrFlagsLoop_complete response qs hv paths hp 0#usize (by simp) (by simpa using hR)

end Transcrypt.V3Verification

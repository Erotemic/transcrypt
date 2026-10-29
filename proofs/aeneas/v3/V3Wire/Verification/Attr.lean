import V3Wire.Verification.Path

/-!
Functional refinement of the production Git attribute parsers against the
independent specification's `AttrRecordAt` / `attrResponse`.
`parse_attr_record` (with the helper `find_byte`, proved in `Bytes`) accepts exactly the spec's
`git check-attr -z filter` record for the requested path at the given offset
and reports exactly whether its value selects the v3 filter;
`parse_attr_response` (used by `transcrypt_rs::git::protected_flags`) accepts
exactly Git's complete answer for the NUL-terminated request and returns the
selection of every requested path.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core

/-! ## Pure facts about attribute records -/

section Pure
open Transcrypt.V3Policy

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

end Pure

/-! ## `parse_attr_record` -/

theorem FILTER_ATTR_slice_length (t : Slice U8) (ht : t = Array.to_slice FILTER_ATTR) :
    t.len.val = 6 := by
  have := congrArg List.length FILTER_ATTR_bytes
  rw [sliceBytes_length, filterAttr_length] at this
  subst ht; simp at this ⊢

theorem byte_zero_iff (R : Slice U8) (k : Nat) (hk : k < R.length) :
    (sliceBytes R)[k]! = 0 ↔ R.val[k] = 0#u8 := by
  rw [sliceBytes_getElem! R k hk]
  constructor
  · intro h; exact UScalar.eq_of_val_eq (by simpa using h)
  · intro h; rw [h]; rfl

/-- Everything a record at `s` says about the bytes of the response. -/
structure AttrFacts (R : List Nat) (s : Nat) (P v : List Nat) (n : Nat) : Prop where
  bound : s + P.length + 8 + v.length < R.length
  path : P <+: R.drop s
  nul_path : R[s + P.length]! = 0
  filter : Transcrypt.V3Policy.filterAttr <+: R.drop (s + P.length + 1)
  nul_filter : R[s + P.length + 7]! = 0
  value_nul_free : 0 ∉ v
  value : v <+: R.drop (s + P.length + 8)
  nul_value : R[s + P.length + 8 + v.length]! = 0
  next : n = s + P.length + v.length + 9

theorem attrRecordAt_facts {R P v : List Nat} {s n : Nat}
    (h : Transcrypt.V3Policy.AttrRecordAt R s P v n) : AttrFacts R s P v n := by
  obtain ⟨h0, hp, hn⟩ := h
  rw [attrRecord_prefix_iff, getElem?_eq_some_iff', getElem?_eq_some_iff',
    getElem?_eq_some_iff'] at hp
  rw [attrRecord_length] at hn
  exact ⟨hp.2.2.2.2.2.1, hp.1, hp.2.1.2, hp.2.2.1, hp.2.2.2.1.2, h0, hp.2.2.2.2.1,
    hp.2.2.2.2.2.2, by rw [hn]; omega⟩

/-- No record lies at `s` if none of the facts of one can hold. -/
theorem no_attrRecordAt {R P : List Nat} {s : Nat} (h : ∀ v n, AttrFacts R s P v n → False) :
    ¬ ∃ v n, Transcrypt.V3Policy.AttrRecordAt R s P v n :=
  fun ⟨v, n, hrec⟩ => h v n (attrRecordAt_facts hrec)

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
  simp_len
  have hRl := sliceBytes_length response
  have hPl := sliceBytes_length path
  have hmax := response.property
  -- Every rejection refutes the facts of a record at `start`; most need only
  -- its extent.
  have hbound : ∀ v n, AttrFacts (sliceBytes response) start.val (sliceBytes path) v n →
      start.val + path.length + 8 + v.length < response.length := fun v n F => by
    have := F.bound; rwa [hRl, hPl] at this
  step*
  -- `start` is past the end.
  · exact no_attrRecordAt fun v n F => by have := hbound v n F; scalar_tac
  -- Too short for the path.
  · exact no_attrRecordAt fun v n F => by have := hbound v n F; scalar_tac
  -- Too short for any record.
  · exact no_attrRecordAt fun v n F => by
      have := hbound v n F
      have := FILTER_ATTR_slice_length s s_post
      scalar_tac
  -- No NUL after the path.
  · refine no_attrRecordAt fun v n F => ?_
    subst i5_post2
    have := ‹(_ != 0#u8) = true›
    simp_bne at this
    apply this
    rw [← byte_zero_iff response name.val i5, name_post]
    simpa [hPl] using F.nul_path
  -- No NUL after `filter`.
  · refine no_attrRecordAt fun v n F => ?_
    subst i9_post2
    have := ‹(_ != 0#u8) = true›
    simp_bne at this
    apply this
    have h6 := FILTER_ATTR_slice_length s2 s2_post
    rw [← byte_zero_iff response i8.val i9, i8_post, i6_post, name_post, h6]
    simpa [hPl] using F.nul_filter
  -- No NUL terminates the value.
  · refine no_attrRecordAt fun v n F => ?_
    have := hbound v n F
    have h6 := FILTER_ATTR_slice_length s3 s3_post
    have hend : «end».val = response.length := by
      have := congrArg UScalar.val ‹«end» = response.len›; simpa using this
    have hval : value.val = start.val + path.length + 8 := by
      rw [value_post, i11_post, name_post, h6]; simp
    obtain ⟨_, _, hscan⟩ := end_post1
    apply hscan (start.val + path.length + 8 + v.length) (by omega) (by omega)
    simpa [hPl] using F.nul_value
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
        simp_bne at this
        have hn : name.val = start.val + path.length := by rw [name_post]; simp
        rw [← hn]; exact (byte_zero_iff response name.val i5).mpr this
      have hz7 : (sliceBytes response)[start.val + path.length + 7]! = 0 := by
        subst i9_post2
        have := ‹¬(_ != 0#u8) = true›
        simp_bne at this
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
  · refine no_attrRecordAt fun v n F => ?_
    apply ‹¬b1 = true›
    rw [b1_post, s1_post, FILTER_ATTR_bytes, i6_post, name_post]
    exact ⟨by have := hbound v n F; scalar_tac, by simpa [hPl] using F.filter⟩
  -- The path does not match.
  · refine no_attrRecordAt fun v n F => ?_
    apply ‹¬b = true›
    rw [b_post]
    exact ⟨by have := hbound v n F; omega, F.path⟩

/-! ## `parse_attr_response`: the whole answer, driven by the request -/

section Response
open Transcrypt.V3Policy

/-- The first NUL of `p ++ 0 :: t` with NUL-free `p` is at `p.length`. -/
theorem first_nul_eq {l p t : List Nat} (hl : l = p ++ 0 :: t) (hp : 0 ∉ p) {m : Nat}
    (hno : ∀ j < m, l[j]? ≠ some 0) (hm : l[m]? = some 0) : m = p.length := by
  subst hl
  rcases Nat.lt_trichotomy m p.length with h | h | h
  · rw [List.getElem?_append_left h] at hm
    exact absurd (List.mem_of_getElem? hm) hp
  · exact h
  · exact absurd (by simp) (hno p.length h)

theorem take_succ_of_nul (R : List Nat) {st k : Nat} (hsk : st ≤ k) (hk : R[k]? = some 0) :
    R.take (k + 1) = R.take st ++ (R.extract st k ++ [0]) := by
  have hkl : k < R.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [show k + 1 = st + (k - st + 1) by omega, List.take_add, List.extract_eq_take_drop,
    List.take_add_one, List.getElem?_drop, show st + (k - st) = k by omega, hk]
  simp

theorem extract_nul_free (R : List Nat) {st k : Nat}
    (hno : ∀ j, st ≤ j → j < k → R[j]? ≠ some 0) : 0 ∉ R.extract st k := by
  intro hm
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hm
  simp only [List.extract_eq_take_drop, List.getElem_take, List.getElem_drop,
    List.length_take, List.length_drop] at hj he
  exact hno (st + j) (by omega) (by omega) (by rw [List.getElem?_eq_getElem (by omega), he])

theorem take_add_of_prefix' (S c : List Nat) (j : Nat) (h : c <+: S.drop j) :
    S.take (j + c.length) = S.take j ++ c := by
  rw [List.take_add]
  congr 1
  exact (List.prefix_iff_eq_take.mp h).symm

theorem attrRecordAt_take {S P v : List Nat} {a n : Nat} (h : AttrRecordAt S a P v n) :
    S.take n = S.take a ++ attrRecord P v ∧ n ≤ S.length := by
  obtain ⟨_, hp, rfl⟩ := h
  refine ⟨take_add_of_prefix' S _ a hp, ?_⟩
  have := hp.length_le
  rw [List.length_drop] at this
  have hne : attrRecord P v ≠ [] := by simp [attrRecord]
  rcases Nat.lt_or_ge a S.length with h | h
  · omega
  · rw [List.drop_eq_nil_of_le h, List.prefix_nil] at hp; exact absurd hp hne

theorem flatMap_nul_take_drop (Q : List (List Nat)) (i : Nat) :
    Q.flatMap (· ++ [0]) = (Q.take i).flatMap (· ++ [0]) ++ (Q.drop i).flatMap (· ++ [0]) := by
  rw [← List.flatMap_append, List.take_append_drop]

theorem drop_of_take_eq {R A B : List Nat} {st : Nat} (hR : R = A ++ B) (hst : st ≤ R.length)
    (ht : R.take st = A) : R.drop st = B := by
  have : A.length = st := by rw [← ht]; simp; omega
  rw [hR, ← this, List.drop_left]

/-- Under Git's answer for request paths `Q`, the bytes between the current
    segment start and the next NUL are exactly the next requested path. -/
theorem hyp_segment {R : List Nat} {Q : List (List Nat)} (hQ : ∀ p ∈ Q, 0 ∉ p)
    (hR : R = Q.flatMap (· ++ [0])) {st k i : Nat} (hsk : st ≤ k)
    (ht : R.take st = (Q.take i).flatMap (· ++ [0]))
    (hno : ∀ j, st ≤ j → j < k → R[j]? ≠ some 0) (hk : R[k]? = some 0) :
    ∃ hi : i < Q.length, R.extract st k = Q[i] := by
  have hkl : k < R.length := (List.getElem?_eq_some_iff.mp hk).1
  have hD := drop_of_take_eq (hR.trans (flatMap_nul_take_drop Q i)) (by omega) ht
  by_cases hi : i < Q.length
  · refine ⟨hi, ?_⟩
    rw [List.drop_eq_getElem_cons hi, List.flatMap_cons] at hD
    have hD' : R.drop st = Q[i] ++ 0 :: (Q.drop (i + 1)).flatMap (· ++ [0]) := by
      rw [hD]; simp
    have hm := first_nul_eq hD' (hQ _ (List.getElem_mem hi)) (m := k - st)
      (fun j hj => by rw [List.getElem?_drop]; exact hno (st + j) (by omega) (by omega))
      (by rw [List.getElem?_drop, show st + (k - st) = k by omega]; exact hk)
    rw [List.extract_eq_take_drop, hD', hm, List.take_left]
  · have hq : Q.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [hq, List.flatMap_nil] at hD
    have := congrArg List.length hD
    simp at this
    omega

/-- At the end of the request, all requested paths have been consumed. -/
theorem hyp_final {R : List Nat} {Q : List (List Nat)} (hR : R = Q.flatMap (· ++ [0]))
    {st i : Nat} (hst : st ≤ R.length) (ht : R.take st = (Q.take i).flatMap (· ++ [0]))
    (hno : ∀ j, st ≤ j → j < R.length → R[j]? ≠ some 0) : Q.length ≤ i ∧ st = R.length := by
  have hD := drop_of_take_eq (hR.trans (flatMap_nul_take_drop Q i)) hst ht
  by_cases hi : i < Q.length
  · exfalso
    rw [List.drop_eq_getElem_cons hi, List.flatMap_cons] at hD
    have h0 : (R.drop st)[Q[i].length]? = some 0 := by rw [hD]; simp
    rw [List.getElem?_drop] at h0
    exact hno _ (by omega) (List.getElem?_eq_some_iff.mp h0).1 h0
  · refine ⟨by omega, ?_⟩
    have hq : Q.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [hq, List.flatMap_nil] at hD
    have := congrArg List.length hD
    simp at this
    omega

theorem attrResponse_drop_of_take {S : List Nat} {qs : List (List Nat × List Nat)}
    (hS : S = attrResponse qs) {a i : Nat} (hat : a ≤ S.length)
    (ht : S.take a = attrResponse (qs.take i)) : S.drop a = attrResponse (qs.drop i) := by
  apply drop_of_take_eq _ hat ht
  rw [hS, ← attrResponse_append, List.take_append_drop]

/-- Under Git's answer `attrResponse qs`, the next record is `qs[i]`'s. -/
theorem hyp_record {S : List Nat} {qs : List (List Nat × List Nat)} (hv : ∀ q ∈ qs, 0 ∉ q.2)
    (hS : S = attrResponse qs) {a i : Nat} (hat : a ≤ S.length)
    (ht : S.take a = attrResponse (qs.take i)) (hi : i < qs.length) :
    AttrRecordAt S a qs[i].1 qs[i].2 (a + (attrRecord qs[i].1 qs[i].2).length) := by
  refine ⟨hv _ (List.getElem_mem hi), ?_, rfl⟩
  rw [attrResponse_drop_of_take hS hat ht, List.drop_eq_getElem_cons hi]
  unfold attrResponse
  rw [List.flatMap_cons]
  exact List.prefix_append _ _

theorem zip_eq_split {ps vs : List (List Nat)} {X : List (List Nat × List Nat)}
    (hl : ps.length = vs.length) (h : ps.zip vs = X) :
    ps = X.map (·.1) ∧ vs = X.map (·.2) := by
  subst h
  exact ⟨(List.map_fst_zip (by omega)).symm, (List.map_snd_zip (by omega)).symm⟩

end Response

/-- The completeness hypothesis: `request` is the `-z --stdin` request for
    the paths of `qs` and `response` is Git's answer `attrResponse qs`. -/
def AttrHyp (request response : Slice U8) (flags : Slice Bool)
    (qs : List (List Nat × List Nat)) : Prop :=
  (∀ q ∈ qs, 0 ∉ q.1) ∧ (∀ q ∈ qs, 0 ∉ q.2) ∧
  sliceBytes request = (qs.map (·.1)).flatMap (· ++ [0]) ∧
  sliceBytes response = Transcrypt.V3Policy.attrResponse qs ∧ flags.length = qs.length

/-- Loop invariant of `parse_attr_response` at request offset `k`: while
    `ok`, the request up to `st` is the first `i` paths (each NUL-terminated),
    the current segment `[st, k)` has no NUL, the response up to `at` is
    their records, and the first `i` flags are their selections; under the
    completeness hypothesis `ok` stays set and the parsed records are `qs`'s. -/
def RespInv (request response : Slice U8) (flags : Slice Bool)
    (qs : List (List Nat × List Nat)) (fl : Slice Bool) (ok : Bool) (st at_ i k : Nat) : Prop :=
  k ≤ request.length ∧ fl.length = flags.length ∧
  (ok = true → st ≤ k ∧ (∀ j, st ≤ j → j < k → (sliceBytes request)[j]? ≠ some 0) ∧
    i ≤ flags.length ∧ at_ ≤ response.length ∧
    ∃ ps vs : List (List Nat), ps.length = i ∧ vs.length = i ∧
      (∀ p ∈ ps, 0 ∉ p) ∧ (∀ v ∈ vs, 0 ∉ v) ∧
      (sliceBytes request).take st = ps.flatMap (· ++ [0]) ∧
      (sliceBytes response).take at_ = Transcrypt.V3Policy.attrResponse (ps.zip vs) ∧
      fl.val.take i = vs.map (fun v => decide (Transcrypt.V3Policy.Selected v)) ∧
      (AttrHyp request response flags qs → ps.zip vs = qs.take i)) ∧
  (AttrHyp request response flags qs → ok = true)

theorem resp_body_spec (request response : Slice U8) (flags : Slice Bool)
    (qs : List (List Nat × List Nat)) (fl : Slice Bool) (ok : Bool) (st at_ i k : Usize)
    (hinv : RespInv request response flags qs fl ok st.val at_.val i.val k.val) :
    parse_attr_response_loop.body request response fl ok st at_ i k ⦃ cf => match cf with
      | .cont (fl', ok', st', at', i', k') =>
          RespInv request response flags qs fl' ok' st'.val at'.val i'.val k'.val ∧
          request.length - k'.val < request.length - k.val
      | .done (fl', ok', st', at', i') =>
          RespInv request response flags qs fl' ok' st'.val at'.val i'.val request.length ⦄ := by
  obtain ⟨hk, hfl, hok, hhyp⟩ := hinv
  unfold parse_attr_response_loop.body
  simp_len
  split
  · rename_i hokt
    obtain ⟨hst, hno, hi, hat, ps, vs, hpl, hvl, hp0, hv0, hR, hS, hF, hH⟩ := hok hokt
    have hRl := sliceBytes_length request
    step*
    · have hbyte := fun (y : U8) (hy : y = request.val[k.val]) =>
        (show (sliceBytes request)[k.val]? = some y.val by
          rw [List.getElem?_eq_getElem (by rw [hRl]; exact i2), hy]
          simp [sliceBytes])
      have hbyte := hbyte _ i2_post2
      split
      · rename_i hz
        have hk0 : (sliceBytes request)[k.val]? = some 0 := by rw [hbyte, hz]; rfl
        have hhi : AttrHyp request response flags qs → ∃ hi' : i.val < qs.length,
            (sliceBytes request).extract st.val k.val = qs[i.val].1 ∧
            (sliceBytes request).take st.val = ((qs.map (·.1)).take i.val).flatMap (· ++ [0]) ∧
            (sliceBytes response).take at_.val = Transcrypt.V3Policy.attrResponse (qs.take i.val) := by
          intro hy
          have hq1 := hy.1
          have hyR := hy.2.2.1
          have hz := hH hy
          have hps := (zip_eq_split (by omega) hz).1
          have htk : (sliceBytes request).take st.val =
              ((qs.map (·.1)).take i.val).flatMap (· ++ [0]) := by
            rw [hR, hps, List.map_take]
          obtain ⟨hiQ, hext⟩ := hyp_segment (Q := qs.map (·.1))
            (fun p hp => by
              obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp; exact hq1 q hq)
            hyR hst htk hno hk0
          simp only [List.length_map] at hiQ
          refine ⟨hiQ, by rw [hext]; simp, htk, by rw [hS, hz]⟩
        split
        · rename_i hif
          have hil : i.val < fl.length := by scalar_tac
          step with index_range_spec request st k hst (by omega) as ⟨ seg, hseg ⟩
          step with parse_attr_record_spec response at_ seg as ⟨ r, hr ⟩
          rcases r with a | e
          · obtain ⟨v, hrec, hprot⟩ := hr
            simp only
            step as ⟨ fl2, hfl2a, hfl2 ⟩
            step as ⟨ i5, hi5 ⟩
            step as ⟨ st2, hst2 ⟩
            step as ⟨ k1, hk1 ⟩
            have hpz : 0 ∉ sliceBytes seg := by rw [hseg]; exact extract_nul_free _ hno
            obtain ⟨hStake, hnext⟩ := attrRecordAt_take hrec
            have hRtake := take_succ_of_nul (sliceBytes request) hst hk0
            have hb : a.protected = decide (Transcrypt.V3Policy.Selected v) := by
              by_cases hs : Transcrypt.V3Policy.Selected v
              · rw [decide_eq_true hs]; exact hprot.mpr hs
              · rw [decide_eq_false hs]
                cases h : a.protected
                · rfl
                · exact absurd (hprot.mp h) hs
            have hfv : fl2.val = fl.val.set i.val a.protected := by rw [hfl2]; rfl
            have hzip : (ps ++ [sliceBytes seg]).zip (vs ++ [v]) = ps.zip vs ++ [(sliceBytes seg, v)] := by
              rw [List.zip_append (by omega)]; rfl
            refine ⟨⟨by omega, by rw [← hfl, Slice.length, hfv, List.length_set], fun _ => ⟨by omega,
              fun j h1 h2 => absurd h2 (by omega), by omega,
              by rw [sliceBytes_length] at hnext; exact hnext,
              ps ++ [sliceBytes seg], vs ++ [v], by simp [hpl, hi5], by simp [hvl, hi5], ?_, ?_, ?_, ?_, ?_, ?_⟩,
              fun _ => rfl⟩, by omega⟩
            · intro q hq
              rcases List.mem_append.1 hq with hq | hq
              · exact hp0 q hq
              · rw [List.mem_singleton.1 hq]; exact hpz
            · intro w hw
              rcases List.mem_append.1 hw with hw | hw
              · exact hv0 w hw
              · rw [List.mem_singleton.1 hw]; exact hrec.1
            · rw [hst2, hRtake, hR, ← hseg]
              simp [List.flatMap_append]
            · rw [hStake, hS, hzip, attrResponse_append]
              simp [Transcrypt.V3Policy.attrResponse]
            · rw [hi5, hfv, take_set_succ _ _ _ (by simpa using hil), hF, hb]
              simp
            · intro hy
              obtain ⟨hiq, hext, -, hat'⟩ := hhi hy
              have rec2 := hyp_record hy.2.1 hy.2.2.2.1 (by rw [sliceBytes_length]; exact hat) hat' hiq
              rw [hseg, hext] at hrec
              obtain ⟨hvq, -⟩ := attrRecordAt_unique hrec rec2
              rw [hzip, hH hy, hi5, List.take_add_one, List.getElem?_eq_getElem hiq, hseg, hext, hvq]
              rfl
          · simp only
            step*
            refine ⟨⟨by omega, hfl, fun h => absurd h (by simp), fun hy => ?_⟩, by omega⟩
            exfalso
            obtain ⟨hiq, hext, -, hat'⟩ := hhi hy
            apply hr.2
            rw [hseg, hext]
            exact ⟨_, _, hyp_record hy.2.1 hy.2.2.2.1 (by rw [sliceBytes_length]; exact hat) hat' hiq⟩
        · rename_i hif
          step*
          refine ⟨⟨by omega, hfl, fun h => absurd h (by simp), fun hy => ?_⟩, by omega⟩
          exfalso
          obtain ⟨hiq, -⟩ := hhi hy
          apply hif
          have := hy.2.2.2.2
          scalar_tac
      · rename_i hz
        have hk0 : (sliceBytes request)[k.val]? ≠ some 0 := by
          rw [hbyte]; intro h; apply hz; apply UScalar.eq_of_val_eq; simpa using h
        step*
        refine ⟨⟨by omega, hfl, fun _ => ⟨by omega, fun j h1 h2 => ?_, hi, hat, ps, vs, hpl, hvl,
          hp0, hv0, hR, hS, hF, hH⟩, fun _ => rfl⟩, by omega⟩
        rcases Nat.lt_or_ge j k.val with h | h
        · exact hno j h1 h
        · rw [show j = k.val by omega]; exact hk0
    · have hkl : k.val = request.length := by scalar_tac
      refine ⟨le_refl _, hfl, fun _ => ⟨by omega, by rw [← hkl]; exact hno, hi, hat, ps, vs, hpl,
        hvl, hp0, hv0, hR, hS, hF, hH⟩, fun _ => rfl⟩
  · rename_i hokf
    simp only [WP.spec_ok]
    refine ⟨by omega, hfl, fun h => absurd h (by simp), fun h => absurd (hhyp h) hokf⟩

theorem resp_loop_spec (request response : Slice U8) (flags : Slice Bool)
    (qs : List (List Nat × List Nat)) (fl : Slice Bool) (ok : Bool) (st at_ i k : Usize)
    (hinv : RespInv request response flags qs fl ok st.val at_.val i.val k.val) :
    parse_attr_response_loop request response fl ok st at_ i k ⦃ r =>
      RespInv request response flags qs r.1 r.2.1 r.2.2.1.val r.2.2.2.1.val r.2.2.2.2.val
        request.length ⦄ := by
  unfold parse_attr_response_loop
  apply loop.spec_decr_nat (fun s => request.length - s.2.2.2.2.2.val)
    (fun s => RespInv request response flags qs s.1 s.2.1 s.2.2.1.val s.2.2.2.1.val
      s.2.2.2.2.1.val s.2.2.2.2.2.val)
  · rintro ⟨fl', ok', st', at', i', k'⟩ h
    apply WP.spec_mono (resp_body_spec request response flags qs fl' ok' st' at' i' k' h)
    rintro (⟨_, _, _, _, _, _⟩ | ⟨_, _, _, _, _⟩) <;> exact id
  · exact hinv

theorem parse_attr_response_gen (request response : Slice U8) (flags : Slice Bool)
    (qs : List (List Nat × List Nat)) :
    parse_attr_response request response flags ⦃ r =>
      (r.1 = true → ∃ paths values : List (List Nat),
        paths.length = flags.length ∧ values.length = flags.length ∧
        (∀ p ∈ paths, 0 ∉ p) ∧ (∀ v ∈ values, 0 ∉ v) ∧
        sliceBytes request = paths.flatMap (· ++ [0]) ∧
        sliceBytes response = Transcrypt.V3Policy.attrResponse (paths.zip values) ∧
        r.2.val = values.map (fun v => decide (Transcrypt.V3Policy.Selected v))) ∧
      (AttrHyp request response flags qs →
        r.1 = true ∧ r.2.val = qs.map (fun q => decide (Transcrypt.V3Policy.Selected q.2))) ⦄ := by
  unfold parse_attr_response
  simp_len
  have hRl := sliceBytes_length request
  have hSl := sliceBytes_length response
  have hinit : RespInv request response flags qs flags true (0#usize).val (0#usize).val
      (0#usize).val (0#usize).val := by
    refine ⟨by simp, rfl, fun _ => ⟨by simp, fun j h1 h2 => absurd h2 (by simp), by simp, by simp,
      [], [], rfl, rfl, by simp, by simp, by simp, by simp [Transcrypt.V3Policy.attrResponse],
      by simp, fun _ => by simp⟩, fun _ => rfl⟩
  step with resp_loop_spec request response flags qs flags true 0#usize 0#usize 0#usize 0#usize
    hinit as ⟨ fl, ok, st, at_, i, hinv ⟩
  obtain ⟨-, hflen, hok, hhyp⟩ := hinv
  -- Consequences of the completeness hypothesis at the end of the request.
  have hfin : ok = true → AttrHyp request response flags qs →
      st.val = request.length ∧ i.val = qs.length ∧ at_.val = response.length ∧
      fl.val = qs.map (fun q => decide (Transcrypt.V3Policy.Selected q.2)) := by
    intro hokt hy
    obtain ⟨hst, hno, hi, hat, ps, vs, hpl, hvl, hp0, hv0, hR, hS, hF, hH⟩ := hok hokt
    have hz := hH hy
    obtain ⟨hps, hvs⟩ := zip_eq_split (by omega) hz
    have htk : (sliceBytes request).take st.val =
        ((qs.map (·.1)).take i.val).flatMap (· ++ [0]) := by
      rw [hR, hps, List.map_take]
    obtain ⟨hQ, hstR⟩ := hyp_final (Q := qs.map (·.1)) hy.2.2.1 (by omega) htk
      (by rw [hRl]; exact hno)
    simp only [List.length_map] at hQ
    have hpl' := congrArg List.length hps
    simp only [List.length_map, List.length_take] at hpl'
    have hiq : i.val = qs.length := by omega
    rw [hiq, List.take_of_length_le (le_refl _)] at hz
    have hat' : at_.val = response.length := by
      have := congrArg List.length (hS.trans (hz ▸ hy.2.2.2.1.symm))
      simp only [List.length_take, hSl] at this
      omega
    refine ⟨by omega, hiq, hat', ?_⟩
    have hfl' : fl.val.length = i.val := by
      have := hy.2.2.2.2; simp only [Slice.length] at hflen this ⊢; omega
    rw [← List.take_of_length_le (le_of_eq hfl'), hF, hvs, hiq, List.take_of_length_le (le_refl _)]
    simp
  split
  · rename_i hokt
    obtain ⟨hst, hno, hi, hat, ps, vs, hpl, hvl, hp0, hv0, hR, hS, hF, hH⟩ := hok hokt
    split
    · rename_i hstl
      have hst' : st.val = request.length := by scalar_tac
      split
      · rename_i hil
        have hi' : i.val = flags.length := by
          have := congrArg UScalar.val hil; simp at this; simp only [Slice.length] at hflen ⊢; omega
        simp only [WP.spec_ok]
        refine ⟨fun hat' => ⟨ps, vs, by omega, by omega, hp0, hv0, ?_, ?_, ?_⟩,
          fun hy => ?_⟩
        · rw [← hR, hst', ← hRl, List.take_length]
        · have : at_.val = response.length := by
            have := of_decide_eq_true hat'; rw [this]; simp
          rw [← hS, this, ← hSl, List.take_length]
        · have hfl' : fl.val.length = i.val := by simp only [Slice.length] at hflen hi' ⊢; omega
          rw [← List.take_of_length_le (le_of_eq hfl'), hF]
        · obtain ⟨_, _, hat', hflv⟩ := hfin hokt hy
          exact ⟨decide_eq_true (by apply UScalar.eq_of_val_eq; simpa using hat'), hflv⟩
      · rename_i hil
        simp only [WP.spec_ok]
        refine ⟨fun h => absurd h (by simp), fun hy => ?_⟩
        exfalso
        obtain ⟨_, hiq, _, _⟩ := hfin hokt hy
        apply hil
        apply UScalar.eq_of_val_eq
        have := hy.2.2.2.2
        simp only [Slice.length] at hflen this
        simp; omega
    · rename_i hstl
      simp only [WP.spec_ok]
      refine ⟨fun h => absurd h (by simp), fun hy => ?_⟩
      exfalso
      obtain ⟨hst', _, _, _⟩ := hfin hokt hy
      apply hstl
      apply UScalar.eq_of_val_eq
      simp; omega
  · rename_i hokf
    simp only [WP.spec_ok]
    exact ⟨fun h => absurd h (by simp), fun hy => absurd (hhyp hy) hokf⟩

/-- **Soundness of the verified attribute-response parser.** If
    `parse_attr_response` accepts, `request` is a list of NUL-free paths, each
    NUL-terminated, with one path per flag; `response` is exactly Git's answer
    `attrResponse` for those paths, in order, with NUL-free values; and each
    output flag says whether the corresponding value selects the v3 filter. -/
theorem parse_attr_response_spec (request response : Slice U8) (flags : Slice Bool) :
    parse_attr_response request response flags ⦃ r => r.1 = true →
      ∃ paths values : List (List Nat),
        paths.length = flags.length ∧ values.length = flags.length ∧
        (∀ p ∈ paths, 0 ∉ p) ∧ (∀ v ∈ values, 0 ∉ v) ∧
        sliceBytes request = paths.flatMap (· ++ [0]) ∧
        sliceBytes response = Transcrypt.V3Policy.attrResponse (paths.zip values) ∧
        r.2.val = values.map (fun v => decide (Transcrypt.V3Policy.Selected v)) ⦄ :=
  WP.spec_mono (parse_attr_response_gen request response flags []) (fun _ h => h.1)

/-- **Completeness of the verified attribute-response parser.** For the
    request built from NUL-free `paths` (one flag slot each) and Git's answer
    `attrResponse qs` naming those paths in order with NUL-free values,
    `parse_attr_response` accepts and returns exactly the selections. -/
theorem parse_attr_response_complete (request response : Slice U8) (flags : Slice Bool)
    (paths : List (List Nat)) (qs : List (List Nat × List Nat))
    (hp0 : ∀ p ∈ paths, 0 ∉ p) (hv0 : ∀ q ∈ qs, 0 ∉ q.2) (hq : qs.map (·.1) = paths)
    (hR : sliceBytes request = paths.flatMap (· ++ [0]))
    (hS : sliceBytes response = Transcrypt.V3Policy.attrResponse qs)
    (hf : flags.length = paths.length) :
    parse_attr_response request response flags ⦃ r => r.1 = true ∧
      r.2.val = qs.map (fun q => decide (Transcrypt.V3Policy.Selected q.2)) ⦄ := by
  have hy : AttrHyp request response flags qs := by
    subst hq
    refine ⟨fun q hq => hp0 _ (List.mem_map_of_mem hq), hv0, hR, hS, by simpa using hf⟩
  exact WP.spec_mono (parse_attr_response_gen request response flags qs) (fun _ h => h.2 hy)

end Transcrypt.V3Verification

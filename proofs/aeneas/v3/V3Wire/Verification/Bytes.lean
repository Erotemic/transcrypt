import V3Wire.Verification.Copy
import Transcrypt.V3Policy
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
namespace Transcrypt.V3Verification
open transcrypt_v3_core

/-!
Functional refinement of the production v3 byte-comparison decisions: byte
equality, the Git `check-attr -z` response check, and the hydrate/lock
lifecycle decisions. Each theorem names the Aeneas-generated translation and
relates its complete result to the independent specification in
`Transcrypt.V3Policy`; as `WP.spec` triples they also exclude panics and
divergence.
-/

theorem bytes_eq_loop_spec (a b : Slice U8) (hlen : a.length = b.length) (i : Usize)
    (hi : i.val ≤ a.length) (h : MatchesUpTo a.val b.val 0 i.val) :
    bytes_eq_loop a b i ⦃ r => r = true ↔ a.val = b.val ⦄ := by
  unfold bytes_eq_loop
  apply compare_loop _ (fun n => MatchesUpTo a.val b.val 0 n) a.length _ _ i hi h
  intro j hj hc
  unfold bytes_eq_loop.body
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  step*
  · refine ⟨i4_post, by omega, ?_⟩
    rw [i4_post]
    apply hc.step
    have hne := ‹¬(_ != _) = true›
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    rw [Nat.zero_add, getElem!_pos a.val j.val i2, getElem!_pos b.val j.val i3, ← i2_post2, ← i3_post2, hne]
  · rename_i hge
    have hj' : a.length ≤ j.val := by scalar_tac
    simp only [true_iff]
    apply List.ext_getElem (by simpa using hlen)
    intro k h1 h2
    have := hc k (by have : a.length = a.val.length := rfl; omega)
    rwa [Nat.zero_add, getElem!_pos a.val k h1, getElem!_pos b.val k h2] at this

@[step]
theorem bytes_eq_spec (a b : Slice U8) :
    bytes_eq a b ⦃ r => r = true ↔ a.val = b.val ⦄ := by
  unfold bytes_eq
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  step*
  rename_i hne
  have hlen : a.length = b.length := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    scalar_tac
  exact bytes_eq_loop_spec a b hlen 0#usize (by simp) (MatchesUpTo.zero _ _ _)

theorem sliceBytes_inj (a b : Slice U8) : sliceBytes a = sliceBytes b ↔ a.val = b.val := by
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun x y hxy => UScalar.eq_of_val_eq hxy) h
  · intro h
    simp [sliceBytes, h]

theorem map_prefix_drop_iff (l p : List U8) (j : Nat) (hp : 0 < p.length) :
    p.map (·.val) <+: (l.map (·.val)).drop j ↔
      j + p.length ≤ l.length ∧ MatchesUpTo l p j p.length := by
  rw [List.prefix_iff_eq_take]
  simp only [List.length_map]
  constructor
  · intro h
    have hlen := congrArg List.length h
    simp only [List.length_map, List.length_take, List.length_drop] at hlen
    refine ⟨by omega, fun k hk => ?_⟩
    have h2 := List.getElem_of_eq h (i := k) (by simpa using hk)
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop] at h2
    rw [getElem!_pos l (j + k) (by omega), getElem!_pos p k hk]
    exact UScalar.eq_of_val_eq h2.symm
  · rintro ⟨hlen, hm⟩
    apply List.ext_getElem (by simp; omega)
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    have := hm k (by simpa using h1)
    rw [getElem!_pos l (j + k) (by simp at h1; omega), getElem!_pos p k (by simpa using h1)] at this
    rw [this]

@[simp] theorem FILTER_ATTR_SUFFIX_length : FILTER_ATTR_SUFFIX.length = 22 := by simp

theorem FILTER_ATTR_SUFFIX_matches_spec :
    FILTER_ATTR_SUFFIX.val.map (·.val) = Transcrypt.V3Policy.filterAttrSuffix := by
  unfold FILTER_ATTR_SUFFIX Transcrypt.V3Policy.filterAttrSuffix Transcrypt.V3Policy.ascii
  decide

theorem filter_suffix_at_loop_spec (response : Slice U8) (j : Usize)
    (hj : j.val + 22 ≤ response.length) (k : Usize) (hk : k.val ≤ 22)
    (h : MatchesUpTo response.val FILTER_ATTR_SUFFIX.val j.val k.val) :
    filter_suffix_at_loop response j k ⦃ r =>
      r = true ↔ MatchesUpTo response.val FILTER_ATTR_SUFFIX.val j.val 22 ⦄ := by
  unfold filter_suffix_at_loop
  apply compare_loop _ (fun n => MatchesUpTo response.val FILTER_ATTR_SUFFIX.val j.val n) 22 _ _ k hk h
  intro m hm hc
  unfold filter_suffix_at_loop.body
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hF := FILTER_ATTR_SUFFIX_length
  have hrl : response.length = response.val.length := rfl
  step*
  · have hne := ‹(_ != _) = true›
    simp only [bne_iff_ne, ne_eq] at hne
    simp only [Bool.false_eq_true, false_iff]
    intro hall
    apply hne
    have := hall m.val (by omega)
    rw [getElem!_pos response.val (j.val + m.val) (by omega),
      getElem!_pos FILTER_ATTR_SUFFIX.val m.val i3] at this
    rw [i2_post2, i3_post2, ← this]
    simp only [i1_post]
  · refine ⟨k1_post, by omega, ?_⟩
    rw [k1_post]
    apply hc.step
    have hne := ‹¬(_ != _) = true›
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    rw [getElem!_pos response.val (j.val + m.val) (by omega),
      getElem!_pos FILTER_ATTR_SUFFIX.val m.val i3]
    rw [i2_post2, i3_post2] at hne
    simpa only [i1_post] using hne

@[step]
theorem filter_suffix_at_spec (response : Slice U8) (j : Usize) :
    filter_suffix_at response j ⦃ r => r = true ↔
      (j.val ≤ response.length ∧
        Transcrypt.V3Policy.filterAttrSuffix <+: (sliceBytes response).drop j.val) ⦄ := by
  have key : (j.val ≤ response.length ∧
        Transcrypt.V3Policy.filterAttrSuffix <+: (sliceBytes response).drop j.val) ↔
      (j.val + 22 ≤ response.length ∧
        MatchesUpTo response.val FILTER_ATTR_SUFFIX.val j.val 22) := by
    have h22 : FILTER_ATTR_SUFFIX.val.length = 22 := by simp
    rw [← FILTER_ATTR_SUFFIX_matches_spec, sliceBytes,
      map_prefix_drop_iff _ _ _ (by simp), h22]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by have := h.1; simp only [Slice.length] at this ⊢; omega, h⟩
  unfold filter_suffix_at
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  have hF := FILTER_ATTR_SUFFIX_length
  have hrl : response.length = response.val.length := rfl
  step*
  have hlen : j.val + 22 ≤ response.length := by
    have := ‹¬i1 < s.len›
    subst s_post
    scalar_tac
  apply WP.spec_mono (filter_suffix_at_loop_spec response j hlen 0#usize (by simp)
    (MatchesUpTo.zero _ _ _))
  intro r hr
  rw [key, hr]
  exact ⟨fun h => ⟨hlen, h⟩, fun h => h.2⟩

section AttrResponse
open Transcrypt.V3Policy

/-- The expected-response chunk produced for one request byte. -/
def attrChunk (b : Nat) : List Nat := if b = 0 then filterAttrSuffix else [b]

theorem expectedAttrResponse_append (p q : List Nat) :
    expectedAttrResponse (p ++ q) = expectedAttrResponse p ++ expectedAttrResponse q := by
  simp [expectedAttrResponse, List.flatMap_append]

theorem expectedAttrResponse_take_succ (Q : List Nat) (i : Nat) (h : i < Q.length) :
    expectedAttrResponse (Q.take (i + 1)) = expectedAttrResponse (Q.take i) ++ attrChunk Q[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, expectedAttrResponse_append]
  simp [expectedAttrResponse, attrChunk]

theorem expectedAttrResponse_drop (Q : List Nat) (i : Nat) (h : i < Q.length) :
    expectedAttrResponse (Q.drop i) = attrChunk Q[i] ++ expectedAttrResponse (Q.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons h]
  simp only [expectedAttrResponse, attrChunk, List.flatMap_cons]

/-- If the response so far is the expected prefix and the whole response is
    the expected one, the next expected chunk must follow. -/
theorem attrChunk_prefix_of_eq (R Q : List Nat) (i j : Nat) (hi : i < Q.length)
    (hj : j ≤ R.length) (htake : R.take j = expectedAttrResponse (Q.take i))
    (hR : R = expectedAttrResponse Q) : attrChunk Q[i] <+: R.drop j := by
  have hsplit : R = expectedAttrResponse (Q.take i) ++ expectedAttrResponse (Q.drop i) := by
    rw [← expectedAttrResponse_append, List.take_append_drop]; exact hR
  have hlen : (expectedAttrResponse (Q.take i)).length = j := by
    rw [← htake]; simp; omega
  have : R.drop j = expectedAttrResponse (Q.drop i) := by
    conv => lhs; rw [hsplit]
    rw [← hlen, List.drop_left]
  rw [this, expectedAttrResponse_drop Q i hi]
  exact List.prefix_append _ _

theorem take_add_of_prefix (R c : List Nat) (j : Nat) (h : c <+: R.drop j) :
    R.take (j + c.length) = R.take j ++ c := by
  rw [List.take_add]
  congr 1
  exact (List.prefix_iff_eq_take.mp h).symm

theorem filterAttrSuffix_length : filterAttrSuffix.length = 22 := by decide

theorem attr_step_zero_ok {R Q : List Nat} {i j : Nat} (hi : i < Q.length) (hq : Q[i] = 0)
    (htk : R.take j = expectedAttrResponse (Q.take i)) (hp : filterAttrSuffix <+: R.drop j) :
    j + 22 ≤ R.length ∧ R.take (j + 22) = expectedAttrResponse (Q.take (i + 1)) := by
  refine ⟨?_, ?_⟩
  · have := hp.length_le
    rw [filterAttrSuffix_length, List.length_drop] at this
    have : filterAttrSuffix ≠ [] := by decide
    rcases Nat.lt_or_ge j R.length with h | h
    · omega
    · rw [List.drop_eq_nil_of_le h, List.prefix_nil] at hp; contradiction
  · rw [expectedAttrResponse_take_succ Q i hi, ← htk, attrChunk, if_pos hq,
      ← take_add_of_prefix R _ j hp, filterAttrSuffix_length]

theorem attr_step_zero_fail {R Q : List Nat} {i j : Nat} (hi : i < Q.length) (hq : Q[i] = 0)
    (hj : j ≤ R.length) (htk : R.take j = expectedAttrResponse (Q.take i))
    (hnp : ¬ filterAttrSuffix <+: R.drop j) : R ≠ expectedAttrResponse Q := by
  intro hR
  have := attrChunk_prefix_of_eq R Q i j hi hj htk hR
  rw [attrChunk, if_pos hq] at this
  exact hnp this

theorem attr_step_byte_ok {R Q : List Nat} {i j : Nat} (hi : i < Q.length) (hj : j < R.length)
    (hq : Q[i] ≠ 0) (heq : R[j] = Q[i])
    (htk : R.take j = expectedAttrResponse (Q.take i)) :
    R.take (j + 1) = expectedAttrResponse (Q.take (i + 1)) := by
  rw [expectedAttrResponse_take_succ Q i hi, ← htk, attrChunk, if_neg hq,
    List.take_add_one, List.getElem?_eq_getElem hj, heq]
  rfl

theorem attr_step_byte_fail {R Q : List Nat} {i j : Nat} (hi : i < Q.length)
    (hq : Q[i] ≠ 0) (hj : j ≤ R.length) (htk : R.take j = expectedAttrResponse (Q.take i))
    (hne : ∀ h : j < R.length, R[j] ≠ Q[i]) : R ≠ expectedAttrResponse Q := by
  intro hR
  have := attrChunk_prefix_of_eq R Q i j hi hj htk hR
  rw [attrChunk, if_neg hq] at this
  rcases Nat.lt_or_ge j R.length with h | h
  · apply hne h
    have := this.getElem (i := 0) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_drop, Nat.add_zero] at this
    exact this.symm
  · rw [List.drop_eq_nil_of_le h] at this
    simp at this

theorem sliceBytes_length (s : Slice U8) : (sliceBytes s).length = s.length := by
  simp [sliceBytes]

theorem sliceBytes_getElem (s : Slice U8) (k : Nat) (h : k < s.length) :
    (sliceBytes s)[k]'(by rw [sliceBytes_length]; exact h) = (s.val[k]'h).val := by
  simp [sliceBytes]

/-- Loop invariant of `check_attr_response_ok`. -/
def AttrInv (request response : Slice U8) (s : Bool × Usize × Usize) : Prop :=
  s.2.1.val ≤ request.length ∧
  (s.1 = true → s.2.2.val ≤ response.length ∧
    (sliceBytes response).take s.2.2.val = expectedAttrResponse ((sliceBytes request).take s.2.1.val)) ∧
  (s.1 = false → sliceBytes response ≠ expectedAttrResponse (sliceBytes request))

theorem check_attr_response_ok_loop_spec (request response : Slice U8) (ok : Bool) (i j : Usize)
    (h : AttrInv request response (ok, i, j)) :
    check_attr_response_ok_loop request response ok i j ⦃ r =>
      (r.1 = true → r.2.val ≤ response.length ∧
        (sliceBytes response).take r.2.val = expectedAttrResponse (sliceBytes request)) ∧
      (r.1 = false → sliceBytes response ≠ expectedAttrResponse (sliceBytes request)) ⦄ := by
  unfold check_attr_response_ok_loop
  apply loop.spec_decr_nat (fun s => request.length - s.2.1.val) (AttrInv request response)
  · rintro ⟨ok, i, j⟩ ⟨hi, ht, hf⟩
    simp only
    unfold check_attr_response_ok_loop.body
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
    have hrl : response.length = response.val.length := rfl
    have hql : request.length = request.val.length := rfl
    have hF := FILTER_ATTR_SUFFIX_length
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      step*
    · simp only at hi ht hf
      obtain ⟨hjle, htk⟩ := ht trivial
      simp only [↓reduceIte]
      step*
      · have hiQ : i.val < (sliceBytes request).length := by rw [sliceBytes_length]; exact i2
        have hQi := sliceBytes_getElem request i.val i2
        have hjR : j.val ≤ (sliceBytes response).length := by rw [sliceBytes_length]; exact hjle
        split
        next hz =>
          have hq : (sliceBytes request)[i.val] = 0 := by rw [hQi, ← i2_post2, hz]; rfl
          simp only [bind_assoc_eq, bind_tc_ok]
          step*
          rename_i x _ x_post
          cases x
          · simp only [Bool.false_eq_true, ↓reduceIte, bind_tc_ok]
            step*
            simp only [AttrInv]
            refine ⟨⟨by omega, by simp, fun _ => ?_⟩, by omega⟩
            apply attr_step_zero_fail hiQ hq hjR htk
            intro hp
            simpa using x_post.mpr ⟨hjle, hp⟩
          · have hp := (x_post.mp rfl).2
            obtain ⟨h22, htk'⟩ := attr_step_zero_ok hiQ hq htk hp
            rw [sliceBytes_length] at h22
            have hmax := response.property
            simp only [↓reduceIte, bind_assoc_eq]
            step*
            have hs : _ = FILTER_ATTR_SUFFIX.to_slice := ‹_›
            have hx : x.val = j.val + 22 := by rw [x_post, hs]; simp
            simp only [AttrInv]
            refine ⟨⟨by omega, fun _ => ⟨by omega, ?_⟩, by simp⟩, by omega⟩
            rw [hx, i3_post]
            exact htk'
        next hz =>
          have hq : (sliceBytes request)[i.val] ≠ 0 := by
            rw [hQi]; intro h0; apply hz; rw [i2_post2]; exact UScalar.eq_of_val_eq h0
          split
          next hlt =>
            simp only [bind_assoc_eq]
            step*
            split
            next he =>
              simp only [bind_assoc_eq, bind_tc_ok]
              step*
              have hj' : j.val < (sliceBytes response).length := by
                rw [sliceBytes_length]; scalar_tac
              have heq : (sliceBytes response)[j.val] = (sliceBytes request)[i.val] := by
                rw [sliceBytes_getElem response j.val (by scalar_tac), hQi, ← x_post2, ← i2_post2, he]
              simp only [AttrInv]
              refine ⟨⟨by omega, fun _ => ⟨by scalar_tac, ?_⟩, by simp⟩, by omega⟩
              rw [x_post, i3_post]
              exact attr_step_byte_ok hiQ hj' hq heq htk
            next he =>
              simp only [bind_tc_ok]
              step*
              simp only [AttrInv]
              refine ⟨⟨by omega, by simp, fun _ => ?_⟩, by omega⟩
              apply attr_step_byte_fail hiQ hq hjR htk
              intro hj'
              rw [sliceBytes_getElem response j.val (by rw [sliceBytes_length] at hj'; exact hj'),
                hQi, ← x_post2, ← i2_post2]
              intro h0
              exact he (UScalar.eq_of_val_eq h0)
          next hge =>
            simp only [bind_tc_ok]
            step*
            simp only [AttrInv]
            refine ⟨⟨by omega, by simp, fun _ => ?_⟩, by omega⟩
            apply attr_step_byte_fail hiQ hq hjR htk
            intro hlt
            rw [sliceBytes_length] at hlt
            exfalso
            apply hge
            scalar_tac
      · rename_i hge
        have : request.length ≤ i.val := by scalar_tac
        refine ⟨fun _ => ⟨hjle, ?_⟩, by simp⟩
        rw [htk, List.take_of_length_le (by rw [sliceBytes_length]; omega)]
  · exact h

/-- The production Git attribute check accepts exactly the response that the
    specification expects for the request. -/
@[step]
theorem check_attr_response_ok_spec (request response : Slice U8) :
    check_attr_response_ok request response ⦃ r =>
      r = true ↔ sliceBytes response = expectedAttrResponse (sliceBytes request) ⦄ := by
  unfold check_attr_response_ok
  step with check_attr_response_ok_loop_spec request response true 0#usize 0#usize as ⟨ ok, j, ht, hf ⟩
  · refine ⟨by simp, fun _ => ⟨by simp, by simp [expectedAttrResponse]⟩, by simp⟩
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step*
  · obtain ⟨hjle, htk⟩ := ht rfl
    simp only [↓reduceIte]
    simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
    step*
    have hRl := sliceBytes_length response
    rw [decide_eq_true_iff]
    constructor
    · intro hj
      have : j.val = response.length := by rw [hj]; scalar_tac
      rw [← htk, List.take_of_length_le (by omega)]
    · intro hR
      have hlen := congrArg List.length htk
      rw [← hR, List.length_take] at hlen
      have : j.val = response.length := by omega
      apply UScalar.eq_of_val_eq
      rw [this]; scalar_tac

end AttrResponse

/-! ## Lifecycle decisions -/

/-- Rust encoding of the specification's hydrate decision. -/
def hydrateResult : Option Transcrypt.V3Policy.HydrateAction →
    core.result.Result HydrateAction Refusal
  | some .publish => .Ok .Publish
  | some .keep => .Ok .Keep
  | none => .Err .UnexpectedWorktree

/-- Rust encoding of the specification's lock decision. -/
def lockResult : Option Transcrypt.V3Policy.LockAction →
    core.result.Result LockAction Refusal
  | some .keep => .Ok .Keep
  | some .flush => .Ok .Flush
  | none => .Err .UnexpectedWorktree

theorem hydrateResult_injective : Function.Injective hydrateResult := by
  intro a b h
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> first | rfl | cases h

theorem lockResult_injective : Function.Injective lockResult := by
  intro a b h
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> first | rfl | cases h

@[step]
theorem hydrate_action_spec (w r p : Slice U8) :
    hydrate_action w r p ⦃ res =>
      res = hydrateResult
        (Transcrypt.V3Policy.hydrateSpec (sliceBytes w) (sliceBytes r) (sliceBytes p)) ⦄ := by
  unfold hydrate_action
  step*
  all_goals simp_all [Transcrypt.V3Policy.hydrateSpec, hydrateResult, sliceBytes_inj]

@[step]
theorem lock_action_spec (w r s : Slice U8) :
    lock_action w r s ⦃ res =>
      res = lockResult
        (Transcrypt.V3Policy.lockSpec (sliceBytes w) (sliceBytes r) (sliceBytes s)) ⦄ := by
  unfold lock_action
  step*
  all_goals simp_all [Transcrypt.V3Policy.lockSpec, lockResult, sliceBytes_inj]

end Transcrypt.V3Verification

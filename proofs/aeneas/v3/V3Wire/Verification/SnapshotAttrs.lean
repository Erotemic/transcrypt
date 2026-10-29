import V3Wire.Verification.SnapshotListing

/-!
Git snapshot listings, part 3: per-entry decisions over a listing.
`is_local_change` is exactly `LocalChange`, `parse_listing_attrs` accepts
exactly Git's attribute answer `attrResponse` for the listing's own paths,
and `first_unselectable` finds the first protected entry that is not
`Selectable`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core
open Transcrypt.V3Policy

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
  simp_len [bind_tc_ok]
  step with loop.spec_decr_nat
    (fun s : Slice Bool × Bool × Usize × Usize => 2 * (flags.length - s.2.2.2.val) + (if s.2.1 then 1 else 0))
    (fun s : Slice Bool × Bool × Usize × Usize => AttrsInv es response flags s.1 s.2.1 s.2.2.1.val s.2.2.2.val)
    (fun s : Slice Bool × Bool × Usize => AttrsInv es response flags s.1 s.2.1 s.2.2.val flags.length)
    as ⟨ fl, okr, atr, hinv ⟩
  · rintro ⟨fl, ok, at_, i⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4 ⊢
    unfold parse_listing_attrs_loop.body
    simp_len [bind_tc_ok]
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
    simp_len [bind_tc_ok]
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

end Transcrypt.V3Verification

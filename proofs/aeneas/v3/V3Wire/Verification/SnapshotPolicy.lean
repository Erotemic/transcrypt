import V3Wire.Verification.SnapshotOrder
import V3Wire.Verification.Path

/-!
Git snapshot listings, part 6: the protection policy. `policy_unchanged`
compares the records of the index, `HEAD` and `HEAD^1` at policy paths
(`is_policy_path`: every attribute file and the configuration) and accepts
exactly when their policy entries are the same (`policy_unchanged_spec`:
`PolicyUnchanged`). The pre-commit hook counts an entry as settled only then.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core
open Transcrypt.V3Policy

/-! ## Pure facts -/

/-- At a policy entry, the policy entries from there on start with it. -/
theorem policyEntries_drop_at {es : List Entry} {i : Nat} (hi : i < es.length) (hp : PolicyPath es[i].path) :
    policyEntries (es.drop i) = es[i] :: policyEntries (es.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  unfold policyEntries
  rw [List.filter_cons_of_pos (by simpa using hp)]

/-- Entries at other paths do not count. -/
theorem policyEntries_drop_skip {es : List Entry} {i r : Nat} (hir : i ≤ r)
    (hnone : ∀ k (h : k < es.length), i ≤ k → k < r → ¬ PolicyPath es[k].path) :
    policyEntries (es.drop i) = policyEntries (es.drop r) := by
  induction r, hir using Nat.le_induction with
  | base => rfl
  | succ r hir ih =>
    rw [ih (fun k h h1 h2 => hnone k h h1 (by omega))]
    rcases Nat.lt_or_ge r es.length with hr | hr
    · rw [List.drop_eq_getElem_cons hr]
      unfold policyEntries
      rw [List.filter_cons_of_neg (by simpa using hnone r hr hir (by omega))]
    · rw [List.drop_of_length_le hr, List.drop_of_length_le (by omega)]

/-- At a policy entry there are policy entries from there on. -/
theorem policyEntries_drop_ne_nil {es : List Entry} {i : Nat} (hi : i < es.length) (hp : PolicyPath es[i].path) :
    policyEntries (es.drop i) ≠ [] := by
  rw [policyEntries_drop_at hi hp]; exact List.cons_ne_nil _ _

theorem policyEntries_drop_length (es : List Entry) : policyEntries (es.drop es.length) = [] := by
  simp [policyEntries]

/-- A record names one entry: well-formed entries with the same record are
    equal (the mode has six bytes, and the object id no TAB). -/
theorem entryOk_record_inj {a b : Entry} (ha : EntryOk a) (hb : EntryOk b) (h : entryRecord a = entryRecord b) :
    a = b :=
  entryRecord_inj ha.mode_len hb.mode_len ha.mode_no_tab hb.mode_no_tab (objectId_no_tab ha.oid_ok)
    (objectId_no_tab hb.oid_ok) h

/-- The bytes `listing_fields` delimits from `start` to `end` are exactly
    the entry's record. -/
theorem FieldsOf.record {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) {i : Nat} {f : Fields} (hf : FieldsOf es i f) :
    ∃ e, es[i]? = some e ∧ EntryOk e ∧
      (sliceBytes listing).extract f.start.val f.end.val = entryRecord e ∧
      f.start.val ≤ f.end.val ∧ f.end.val ≤ listing.length := by
  obtain ⟨e, he, hok, -, -, -, -, -, hend⟩ := FieldsOf.slices hL hf
  obtain ⟨e', he', hs, -, -, he2, -⟩ := hf
  rw [he] at he'; cases he'
  have hi : i < es.length := (List.getElem?_eq_some_iff.mp he).1
  have hei : es[i] = e := (List.getElem?_eq_some_iff.mp he).2
  obtain ⟨hdrop, -, -⟩ := hL.record hi
  rw [hei] at hdrop
  refine ⟨e, he, hok, ?_, by omega, hend⟩
  rw [List.extract_eq_take_drop, hs, he2, hdrop, show off es i + (entryRecord e).length - off es i =
    (entryRecord e).length by omega]
  simp

/-! ## `policy_at`, `next_policy`, `same_record` -/

theorem policy_at_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (j : Usize) :
    policy_at listing ends j ⦃ b => b = true ↔ ∃ e, es[j.val]? = some e ∧ PolicyPath e.path ⦄ := by
  unfold policy_at
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
    apply WP.spec_mono (is_policy_path_spec s)
    intro b hb
    rw [hb, hs, hpath]
    exact ⟨fun h => ⟨e, he, h⟩, fun ⟨e', he', h⟩ => by rw [he] at he'; cases he'; exact h⟩

/-- `next_policy` is the first entry at a policy path from `from` on, or
    the number of entries. -/
theorem next_policy_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (from_ : Usize) (hf : from_.val ≤ es.length) :
    next_policy listing ends from_ ⦃ r => from_.val ≤ r.val ∧ r.val ≤ es.length ∧
      (∀ k (h : k < es.length), from_.val ≤ k → k < r.val → ¬ PolicyPath es[k].path) ∧
      (∀ h : r.val < es.length, PolicyPath es[r.val].path) ⦄ := by
  have hel := hL.ends_length
  unfold next_policy next_policy_loop
  apply loop.spec_decr_nat (fun j : Usize => es.length - j.val)
    (fun j : Usize => from_.val ≤ j.val ∧ j.val ≤ es.length ∧
      ∀ k (h : k < es.length), from_.val ≤ k → k < j.val → ¬ PolicyPath es[k].path)
  · intro j ⟨h1, h2, h3⟩
    unfold next_policy_loop.body
    simp_len [bind_tc_ok]
    split
    · rename_i hjn
      have hj : j.val < es.length := by scalar_tac
      step with policy_at_spec hL j as ⟨ b, hb ⟩
      rw [List.getElem?_eq_getElem hj] at hb
      split
      · rename_i hbt
        simp only [WP.spec_ok]
        obtain ⟨e, he, hp⟩ := hb.mp hbt
        rw [Option.some.injEq] at he
        exact ⟨h1, h2, h3, fun _ => he ▸ hp⟩
      · rename_i hbt
        step as ⟨ j1, hj1 ⟩
        refine ⟨by omega, by omega, fun k hk hk1 hk2 hn => ?_, by omega⟩
        rcases Nat.lt_or_ge k j.val with hlt | hge
        · exact h3 k hk hk1 hlt hn
        · have hkj : k = j.val := by omega
          subst hkj
          exact hbt (hb.mpr ⟨_, rfl, hn⟩)
    · rename_i hjn
      simp only [WP.spec_ok]
      exact ⟨h1, h2, h3, fun h => absurd h (by scalar_tac)⟩
  · exact ⟨le_refl _, hf, fun k _ hk1 hk2 => absurd hk2 (by omega)⟩

/-- `same_record` says whether entry `i` of one listing and entry `j` of
    another exist and are the same entry (mode, object id and path). -/
theorem same_record_spec {a b : Slice U8} {a_ends b_ends : Slice Usize} {es os : List Entry}
    (hA : ListingOf a a_ends es) (hB : ListingOf b b_ends os) (i j : Usize) :
    same_record a a_ends i b b_ends j ⦃ r => r = true ↔
      ∃ x y, es[i.val]? = some x ∧ os[j.val]? = some y ∧ x = y ⦄ := by
  unfold same_record
  step with listing_fields_spec hA i as ⟨ o, ho ⟩
  rcases o with _ | f
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro x _ hx
    simp only at ho
    have := (List.getElem?_eq_some_iff.mp hx).1
    omega
  · obtain ⟨_, hf⟩ := ho
    obtain ⟨x, hx, hxok, hxr, hf1, hf2⟩ := FieldsOf.record hA hf
    simp only
    step with listing_fields_spec hB j as ⟨ o1, ho1 ⟩
    rcases o1 with _ | g
    · simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro _ y _ hy
      simp only at ho1
      have := (List.getElem?_eq_some_iff.mp hy).1
      omega
    · obtain ⟨_, hg⟩ := ho1
      obtain ⟨y, hy, hyok, hyr, hg1, hg2⟩ := FieldsOf.record hB hg
      simp only
      step with index_range_spec a f.start f.end hf1 hf2 as ⟨ s, hs ⟩
      step with index_range_spec b g.start g.end hg1 hg2 as ⟨ s1, hs1 ⟩
      apply WP.spec_mono (bytes_eq_spec s s1)
      intro r hr
      rw [hr, ← sliceBytes_inj, hs, hs1, hxr, hyr]
      constructor
      · intro h; exact ⟨x, y, hx, hy, entryOk_record_inj hxok hyok h⟩
      · rintro ⟨x', y', hx', hy', rfl⟩
        rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'; rfl

/-! ## `same_policy` and `policy_unchanged` -/

/-- Where `same_policy` stands: at a policy entry (or the end) of each
    listing, with the policy entries equal iff those from there on are. -/
structure PolicyCursor (es os : List Entry) (i j : Nat) : Prop where
  i_le : i ≤ es.length
  j_le : j ≤ os.length
  at_i : ∀ h : i < es.length, PolicyPath es[i].path
  at_j : ∀ h : j < os.length, PolicyPath os[j].path
  rest : policyEntries es = policyEntries os ↔ policyEntries (es.drop i) = policyEntries (os.drop j)

theorem PolicyCursor.rest_nil_iff {es : List Entry} {i : Nat} (hi : i ≤ es.length)
    (hat : ∀ h : i < es.length, PolicyPath es[i].path) : policyEntries (es.drop i) = [] ↔ i = es.length := by
  constructor
  · intro h
    rcases Nat.lt_or_ge i es.length with hlt | hge
    · exact absurd h (policyEntries_drop_ne_nil hlt (hat hlt))
    · omega
  · rintro rfl; exact policyEntries_drop_length es

/-- **Same policy.** `same_policy` accepts two listings exactly when their
    policy entries (`policyEntries`: attribute files and configuration, with
    mode and object id, in order) are equal. -/
theorem same_policy_spec {a b : Slice U8} {a_ends b_ends : Slice Usize} {es os : List Entry}
    (hA : ListingOf a a_ends es) (hB : ListingOf b b_ends os) :
    same_policy a a_ends b b_ends ⦃ r => r = true ↔ policyEntries es = policyEntries os ⦄ := by
  have hael := hA.ends_length
  have hbel := hB.ends_length
  unfold same_policy same_policy_loop
  step with next_policy_spec hA 0#usize (by simp) as ⟨ i0, hi0a, hi0b, hi0c, hi0d ⟩
  step with next_policy_spec hB 0#usize (by simp) as ⟨ j0, hj0a, hj0b, hj0c, hj0d ⟩
  apply loop.spec_decr_nat (fun s : Usize × Usize => es.length - s.1.val)
    (fun s : Usize × Usize => PolicyCursor es os s.1.val s.2.val)
  · rintro ⟨i, j⟩ hc
    dsimp only at hc ⊢
    unfold same_policy_loop.body
    simp_len [bind_tc_ok]
    split
    · rename_i hil
      have hi : i.val < es.length := by scalar_tac
      have hPi := policyEntries_drop_at hi (hc.at_i hi)
      split
      · rename_i hjl
        have hj : j.val < os.length := by scalar_tac
        have hPj := policyEntries_drop_at hj (hc.at_j hj)
        step with same_record_spec hA hB i j as ⟨ b1, hb1 ⟩
        rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hb1
        split
        · rename_i hbt
          obtain ⟨x, y, hx, hy, hxy⟩ := hb1.mp hbt
          rw [Option.some.injEq] at hx hy
          step as ⟨ i3, hi3 ⟩
          step with next_policy_spec hA i3 (by omega) as ⟨ i4, hi4a, hi4b, hi4c, hi4d ⟩
          step as ⟨ i5, hi5 ⟩
          step with next_policy_spec hB i5 (by omega) as ⟨ j1, hj1a, hj1b, hj1c, hj1d ⟩
          refine ⟨⟨hi4b, hj1b, hi4d, hj1d, ?_⟩, by omega⟩
          rw [hc.rest, hPi, hPj, hx, hy, hxy, List.cons.injEq,
            policyEntries_drop_skip (by omega) (fun k h h1 h2 => hi4c k h (by omega) h2),
            policyEntries_drop_skip (by omega) (fun k h h1 h2 => hj1c k h (by omega) h2)]
          simp
        · rename_i hbt
          simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
          rw [hc.rest, hPi, hPj, List.cons.injEq]
          rintro ⟨hxy, -⟩
          exact hbt (hb1.mpr ⟨_, _, rfl, rfl, hxy⟩)
      · rename_i hjl
        have hj : j.val = os.length := by have := hc.j_le; scalar_tac
        split
        · rename_i hii; exfalso; have := congrArg UScalar.val hii; simp at this; omega
        · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
          rw [hc.rest, hPi, hj, policyEntries_drop_length]
          exact List.cons_ne_nil _ _
    · rename_i hil
      have hi : i.val = es.length := by have := hc.i_le; scalar_tac
      split
      · simp only [WP.spec_ok, decide_eq_true_iff]
        have hjv : (j = b_ends.len) ↔ j.val = os.length := by
          constructor
          · rintro rfl; simp [hbel]
          · intro h; apply UScalar.eq_of_val_eq; simp [h, hbel]
        rw [hc.rest, hi, policyEntries_drop_length, eq_comm (a := ([] : List Entry)),
          PolicyCursor.rest_nil_iff hc.j_le hc.at_j, hjv]
      · rename_i hii; exfalso; apply hii; apply UScalar.eq_of_val_eq; simp [hi, hael]
  · refine ⟨hi0b, hj0b, hi0d, hj0d, ?_⟩
    dsimp only
    rw [← policyEntries_drop_skip (Nat.zero_le _) (fun k h _ h2 => hi0c k h (Nat.zero_le _) h2),
      ← policyEntries_drop_skip (Nat.zero_le _) (fun k h _ h2 => hj0c k h (Nat.zero_le _) h2)]
    simp

/-- **Unchanged policy.** `policy_unchanged` accepts the listings of the
    index, `HEAD` and `HEAD^1` exactly when `PolicyUnchanged` holds of their
    entries: the same attribute files and configuration, with the same modes
    and object ids. No order or uniqueness of paths is assumed. -/
theorem policy_unchanged_spec {index head parent : Slice U8} {index_ends head_ends parent_ends : Slice Usize}
    {es hs ps : List Entry} (hI : ListingOf index index_ends es) (hH : ListingOf head head_ends hs)
    (hP : ListingOf parent parent_ends ps) :
    policy_unchanged index index_ends head head_ends parent parent_ends ⦃ r =>
      r = true ↔ PolicyUnchanged es hs ps ⦄ := by
  unfold policy_unchanged
  step with same_policy_spec hI hH as ⟨ b, hb ⟩
  step with same_policy_spec hI hP as ⟨ b1, hb1 ⟩
  simp only [Bool.and_eq_true, hb, hb1, PolicyUnchanged]

/-- **The settled guard.** When `policy_unchanged` returned `true` for the
    parsed index, `HEAD` and `HEAD^1`, the three snapshots have exactly the
    same entries (mode, object id, path) at every attribute file and at the
    configuration (`PolicyUnchanged.agree`), so they hold the same blob
    there (`PolicyUnchanged.holds`). This is the fact the hook's settled
    shortcut relies on: an entry settled in `HEAD` and `HEAD^1` was checked
    under the same selection and configuration. -/
theorem policy_unchanged_sound {index head parent : Slice U8} {index_ends head_ends parent_ends : Slice Usize}
    {es hs ps : List Entry} (hI : ListingOf index index_ends es) (hH : ListingOf head head_ends hs)
    (hP : ListingOf parent parent_ends ps)
    (h : policy_unchanged index index_ends head head_ends parent parent_ends = ok true) :
    PolicyUnchanged es hs ps ∧ ∀ e : Entry, PolicyPath e.path → (e ∈ es ↔ e ∈ hs) ∧ (e ∈ es ↔ e ∈ ps) := by
  have hu := (spec_result (policy_unchanged_spec hI hH hP) h).mp rfl
  exact ⟨hu, fun _ hp => hu.agree hp⟩

end Transcrypt.V3Verification

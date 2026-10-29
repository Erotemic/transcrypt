import V3Wire.Verification.SnapshotOrder

/-!
Git snapshot listings, part 4: path lookups. In a listing in path order,
`find_path` and `find_entry` are binary searches (`find_entry_spec`: a
record naming the blob at the path exactly when `Holds`), and
`held_entries` computes `Holds` for every wanted entry of the index.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core
open Transcrypt.V3Policy

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

/-- `find_path` is the first record whose path is not before `P`; all
    earlier paths are before it, no later one is. -/
theorem find_path_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (hO : PathOrdered es) (path : Slice U8) :
    find_path listing ends path ⦃ r => r.val ≤ es.length ∧
      (∀ k (h : k < es.length), k < r.val → BytesLt es[k].path (sliceBytes path)) ∧
      (∀ k (h : k < es.length), r.val ≤ k → ¬ BytesLt es[k].path (sliceBytes path)) ⦄ := by
  have hel := hL.ends_length
  unfold find_path find_path_loop
  simp_len [bind_tc_ok]
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
    simp_len [bind_tc_ok]
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
  simp_len [bind_tc_ok]
  have hc1 : ¬ (wanted.len != index_ends.len) = true := by
    simp_bne; apply UScalar.eq_of_val_eq; simp [hw, ← hiel]
  have hc2 : ¬ (held.len != index_ends.len) = true := by
    simp_bne; apply UScalar.eq_of_val_eq; simp [hh, ← hiel]
  simp only [hc1, hc2, if_false, Bool.false_eq_true]
  step with loop.spec_decr_nat (fun s : Slice Bool × Usize => es.length - s.2.val)
    (fun s : Slice Bool × Usize => s.2.val ≤ es.length ∧ s.1.length = es.length ∧ HeldUpTo es os wanted s.1 s.2.val)
    (fun h : Slice Bool => h.length = es.length ∧ HeldUpTo es os wanted h es.length) as ⟨ r, hr1, hr2 ⟩
  · rintro ⟨hd, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3 ⊢
    unfold held_entries_loop.body
    simp_len [bind_tc_ok]
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

end Transcrypt.V3Verification

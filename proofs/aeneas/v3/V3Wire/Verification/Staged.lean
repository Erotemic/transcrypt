import V3Wire.Verification.Snapshot
import V3Wire.Verification.Envelope
import V3Wire.Verification.Bytes
import V3Wire.Verification.Path
import V3Wire.Verification.Codec

/-!
Functional refinement of the pre-commit hook's final check of each index
entry: `held_records` (whether `HEAD` and `HEAD^1` hold an entry's exact
record), `staged_check` (which check an entry gets, `StagedCheckOf`),
`reads_blob` (whether the check reads the blob) and `staged_verdict`
(whether the entry passes, `VerdictOk`, from the blob and the adapter's
answers through `StagedEvidence`, each asked only when the check needs it).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core
open Transcrypt.V3Policy

/-! ## `held_records` -/

/-- `held_records` writes, for each entry `k` of the index, whether it is
    wanted and the other listing holds exactly that entry. -/
def RecordsUpTo (es os : List Entry) (wanted held : Slice Bool) (n : Nat) : Prop :=
  ∀ k e, k < n → es[k]? = some e → (held.val[k]! = true ↔ wanted.val[k]! = true ∧ e ∈ os)

/-- **Record membership.** `held_records` says, for every wanted index
    entry, whether the other listing (sorted: each path once) holds that
    very entry: its mode, object id and path. -/
theorem held_records_spec {index other : Slice U8} {index_ends other_ends : Slice Usize}
    {es os : List Entry} (hI : ListingOf index index_ends es) (hO : ListingOf other other_ends os)
    (hOs : Sorted os) (wanted held : Slice Bool) (hw : wanted.length = es.length)
    (hh : held.length = es.length) :
    held_records index index_ends wanted other other_ends held ⦃ r =>
      r.1 = true ∧ r.2.length = es.length ∧ RecordsUpTo es os wanted r.2 es.length ⦄ := by
  have hiel := hI.ends_length
  have hoel := hO.ends_length
  unfold held_records held_records_loop
  simp_len [bind_tc_ok]
  have hc1 : ¬ (wanted.len != index_ends.len) = true := by
    simp_bne; apply UScalar.eq_of_val_eq; simp [hw, ← hiel]
  have hc2 : ¬ (held.len != index_ends.len) = true := by
    simp_bne; apply UScalar.eq_of_val_eq; simp [hh, ← hiel]
  simp only [hc1, hc2, if_false, Bool.false_eq_true]
  step with loop.spec_decr_nat (fun s : Slice Bool × Usize => es.length - s.2.val)
    (fun s : Slice Bool × Usize => s.2.val ≤ es.length ∧ s.1.length = es.length ∧
      RecordsUpTo es os wanted s.1 s.2.val)
    (fun h : Slice Bool => h.length = es.length ∧ RecordsUpTo es os wanted h es.length) as ⟨ r, hr1, hr2 ⟩
  · rintro ⟨hd, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3 ⊢
    unfold held_records_loop.body
    simp_len [bind_tc_ok]
    split
    · rename_i hil
      have hi : i.val < es.length := by scalar_tac
      have hwl : i.val < wanted.length := by omega
      -- After writing the right value `v` at `i`, the invariant holds at `i + 1`.
      have hnext : ∀ (v : Bool) (s : Slice Bool),
          (v = true ↔ wanted.val[i.val]! = true ∧ es[i.val] ∈ os) →
          s.val = hd.val.set i.val v →
          s.length = es.length ∧ RecordsUpTo es os wanted s (i.val + 1) := by
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
          rw [OID_START_val] at hi2
          step with index_range_spec index i2 f.oid_end (by omega) (by omega) as ⟨ so, hso ⟩
          step with index_range_spec index f.path_start f.end hf3 hf4 as ⟨ sp, hsp ⟩
          rw [hi2, hoid] at hso
          rw [hpath] at hsp
          have h9 : tab ∉ sliceBytes so := by rw [hso]; exact objectId_no_tab hok.oid_ok
          step with find_entry_spec hO hOs.pathOrdered so sp h9 as ⟨ j, hj1, hj2, hj3 ⟩
          -- The record found at `e`'s path with `e`'s blob is `e` iff `HEAD` holds `e`.
          have hfound : ∀ (c : Bool), (c = true ↔ j.val < os.length ∧ ∃ x y, es[i.val]? = some x ∧
              os[j.val]? = some y ∧ x = y) → (c = true ↔ es[i.val] ∈ os) := by
            intro c hc
            rw [hc]
            constructor
            · rintro ⟨-, x, y, hx, hy, rfl⟩
              rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hx
              rw [hx]; exact List.mem_of_getElem? hy
            · intro hmem
              have hjl : j.val < os.length := by
                by_contra hn
                exact hj3 (by omega) ⟨_, hmem, by rw [hei, hso], by rw [hei, hsp]⟩
              obtain ⟨y, hy, hyo, hyp⟩ := hj2 hjl
              have hye : y = es[i.val] := hOs.eq_of_path (List.mem_of_getElem? hy) hmem
                (by rw [hyp, hei, hsp])
              exact ⟨hjl, es[i.val], y, List.getElem?_eq_getElem hi, hy, hye.symm⟩
          split
          · rename_i hjlt
            step with same_record_spec hI hO i j as ⟨ b1, hb1 ⟩
            step as ⟨ s, hil', hs ⟩
            step*
            have hsv : s.val = hd.val.set i.val b1 := by rw [hs]; rfl
            obtain ⟨hl', hu⟩ := hnext _ s (by
              rw [← hbw, hbv]; simp only [true_and]
              exact hfound b1 (by rw [hb1]; exact ⟨fun h => ⟨by scalar_tac, h⟩, fun h => h.2⟩)) hsv
            exact ⟨by omega, hl', by rw [show i2.val = i.val + 1 by scalar_tac]; exact hu, by omega⟩
          · rename_i hjlt
            step as ⟨ s, hil', hs ⟩
            step*
            have hsv : s.val = hd.val.set i.val false := by rw [hs]; rfl
            obtain ⟨hl', hu⟩ := hnext false s (by
              rw [← hbw, hbv]; simp only [true_and]
              exact hfound false (by simp only [Bool.false_eq_true, false_iff, not_and]; intro h; scalar_tac))
              hsv
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

/-! ## `staged_check` -/

/-- What `entry_check` decides with `settled` (`entry_check_spec`). -/
def EntryCheckOf (keyed incremental settled : Bool) (c : EntryCheck) : Prop :=
  (c = .Authenticate ↔ keyed = true ∧ ¬ (incremental = true ∧ settled = true)) ∧
    (c = .Envelope ↔ ¬ (keyed = true ∧ ¬ (incremental = true ∧ settled = true)) ∧ settled = true)

/-- What `staged_check` decides for the index entry `x`, given whether it is
    protected, whether `HEAD` and `HEAD^1` hold it, whether the check is
    keyed and incremental, and the settled guard. A protected entry is
    checked as `entry_check` decides, settled only under the guard and when
    both commits hold it; an unprotected symlink or submodule is skipped; an
    unprotected file staged since `HEAD` must not be a record; one `HEAD`
    holds is skipped only when it is reserved metadata, the check has no key,
    or the incremental hook trusts `HEAD` under the guard, and is otherwise
    authenticated if it is a record. -/
def StagedCheckOf (x : Entry) (protected_ inHead inParent keyed incremental guard : Bool) :
    StagedCheck → Prop
  | .Protected c => protected_ = true ∧ EntryCheckOf keyed incremental (guard && inHead && inParent) c
  | .Skip => protected_ = false ∧
      (¬ x.Regular ∨ (inHead = true ∧ (Reserved x.path ∨ keyed = false ∨ (incremental = true ∧ guard = true))))
  | .NotRecord => protected_ = false ∧ x.Regular ∧ inHead = false
  | .AuthenticateIfRecord => protected_ = false ∧ x.Regular ∧ inHead = true ∧ ¬ Reserved x.path ∧
      keyed = true ∧ (incremental = false ∨ guard = false)

/-- **The check of one entry.** `staged_check` on entry `i` of a listing
    decides `StagedCheckOf` its entry. -/
theorem staged_check_spec {listing : Slice U8} {ends : Slice Usize} {es : List Entry}
    (hL : ListingOf listing ends es) (i : Usize) (hi : i.val < es.length)
    (flags inHead inParent : Slice Bool) (hf : flags.length = es.length) (hh : inHead.length = es.length)
    (hp : inParent.length = es.length) (keyed incremental guard : Bool) :
    staged_check listing ends i flags inHead inParent keyed incremental guard ⦃ c =>
      StagedCheckOf es[i.val] flags.val[i.val]! inHead.val[i.val]! inParent.val[i.val]! keyed incremental
        guard c ⦄ := by
  unfold staged_check
  step as ⟨ hfl, b, hb ⟩
  have hbv : b = flags.val[i.val]! := by rw [hb, getElem!_pos flags.val i.val hfl]
  rw [← hbv]
  split
  · rename_i hbt
    step as ⟨ hhl, b1, hb1 ⟩
    step as ⟨ hpl, b2, hb2 ⟩
    have hb1v : b1 = inHead.val[i.val]! := by rw [hb1, getElem!_pos inHead.val i.val hhl]
    have hb2v : b2 = inParent.val[i.val]! := by rw [hb2, getElem!_pos inParent.val i.val hpl]
    step with entry_check_spec as ⟨ c, hc1, hc2 ⟩
    rw [← hb1v, ← hb2v]
    exact ⟨hbt, hc1, hc2⟩
  · rename_i hbt
    simp only [Bool.not_eq_true] at hbt
    step with listing_fields_spec hL i as ⟨ o, ho ⟩
    rcases o with _ | f
    · exfalso; simp only at ho; omega
    · obtain ⟨_, hf'⟩ := ho
      obtain ⟨e, he, -, -, hpath, -, -, hf3, hf4⟩ := FieldsOf.slices hL hf'
      have hei : es[i.val] = e := (List.getElem?_eq_some_iff.mp he).2
      obtain ⟨e', he', -, -, -, -, hreg⟩ := hf'
      have hee : e' = e := by rw [he] at he'; exact (Option.some.inj he').symm
      subst hee
      rw [hei]
      simp only
      split
      · rename_i hr
        have hR : e'.Regular := hreg.mp hr
        step as ⟨ hhl, b1, hb1 ⟩
        have hb1v : b1 = inHead.val[i.val]! := by rw [hb1, getElem!_pos inHead.val i.val hhl]
        rw [← hb1v]
        split
        · rename_i hb1t
          split
          · rename_i hkt
            split
            · rename_i hit
              split
              · rename_i hgt
                simp only [WP.spec_ok, StagedCheckOf]
                exact ⟨hbt, Or.inr ⟨hb1t, Or.inr (Or.inr ⟨hit, hgt⟩)⟩⟩
              · rename_i hgt
                step with index_range_spec listing f.path_start f.end hf3 hf4 as ⟨ sp, hsp ⟩
                step with is_reserved_path_spec as ⟨ r, hr' ⟩
                rw [hsp, hpath] at hr'
                split
                · rename_i hrt
                  simp only [WP.spec_ok, StagedCheckOf]
                  exact ⟨hbt, Or.inr ⟨hb1t, Or.inl (hr'.mp hrt)⟩⟩
                · rename_i hrt
                  simp only [WP.spec_ok, StagedCheckOf]
                  exact ⟨hbt, hR, hb1t, fun h => hrt (hr'.mpr h), hkt, Or.inr (by simpa using hgt)⟩
            · rename_i hit
              step with index_range_spec listing f.path_start f.end hf3 hf4 as ⟨ sp, hsp ⟩
              step with is_reserved_path_spec as ⟨ r, hr' ⟩
              rw [hsp, hpath] at hr'
              split
              · rename_i hrt
                simp only [WP.spec_ok, StagedCheckOf]
                exact ⟨hbt, Or.inr ⟨hb1t, Or.inl (hr'.mp hrt)⟩⟩
              · rename_i hrt
                simp only [WP.spec_ok, StagedCheckOf]
                exact ⟨hbt, hR, hb1t, fun h => hrt (hr'.mpr h), hkt, Or.inl (by simpa using hit)⟩
          · rename_i hkt
            simp only [WP.spec_ok, StagedCheckOf]
            exact ⟨hbt, Or.inr ⟨hb1t, Or.inr (Or.inl (by simpa using hkt))⟩⟩
        · rename_i hb1t
          simp only [WP.spec_ok, StagedCheckOf]
          exact ⟨hbt, hR, by simpa using hb1t⟩
      · rename_i hr
        simp only [WP.spec_ok, StagedCheckOf]
        exact ⟨hbt, Or.inl (fun h => hr (hreg.mpr h))⟩

/-- **The blob is read for exactly the protected entries.** -/
theorem reads_blob_spec (c : StagedCheck) :
    reads_blob c ⦃ b => b = true ↔ ∃ e, c = .Protected e ⦄ := by
  rcases c with _ | _ | _ | e <;> simp only [reads_blob, WP.spec_ok] <;> simp

/-- The check of an entry reads its blob exactly when the entry is protected:
    the adapter's `reads_blob` test and the selection agree. -/
theorem stagedCheckOf_reads {x : Entry} {protected_ inHead inParent keyed incremental guard : Bool}
    {c : StagedCheck} (h : StagedCheckOf x protected_ inHead inParent keyed incremental guard c) :
    (∃ e, c = .Protected e) ↔ protected_ = true := by
  cases c <;> simp only [StagedCheckOf] at h <;> simp [h.1]

/-! ## `staged_verdict` -/

/-- What an accepted verdict says about one entry, by its check: the
    adapter's answers (`StagedEvidence`) that the verdict asked for, and the
    envelope of the blob `record` for configuration id `id`. -/
def VerdictOk {E : Type} (inst : StagedEvidence E) (ev : E) (record : Slice U8)
    (id : Std.Array U8 16#usize) : StagedCheck → Prop
  | .Skip => True
  | .NotRecord => inst.is_record ev = ok false
  | .AuthenticateIfRecord => inst.is_record ev = ok false ∨ inst.opens ev = ok true
  | .Protected .Authenticate => inst.opens ev = ok true
  | .Protected .Envelope => EnvelopeOk (sliceBytes record) (wireBytes id)
  | .Protected .EnvelopeNotMoved => EnvelopeOk (sliceBytes record) (wireBytes id) ∧ inst.elsewhere ev = ok false

/-- **The verdict.** If `staged_verdict` accepted an entry, the answers it
    asked for and the blob's envelope are as its check requires
    (`VerdictOk`). -/
theorem staged_verdict_ok {E : Type} (inst : StagedEvidence E) (ev : E) (check : StagedCheck)
    (record : Slice U8) (id : Std.Array U8 16#usize)
    (h : staged_verdict inst ev check record id = ok (core.result.Result.Ok ())) :
    VerdictOk inst ev record id check := by
  unfold staged_verdict at h
  rcases check with _ | _ | _ | c
  · trivial
  · simp only [VerdictOk]
    cases hr : inst.is_record ev with
    | ok b => rw [hr] at h; cases b <;> simp_all
    | fail _ => rw [hr] at h; simp at h
    | div => rw [hr] at h; simp at h
  · simp only [VerdictOk]
    cases hr : inst.is_record ev with
    | ok b =>
      rw [hr] at h
      cases b
      · exact Or.inl rfl
      · cases ho : inst.opens ev with
        | ok b1 => rw [ho] at h; cases b1 <;> simp_all
        | fail _ => rw [ho] at h; simp at h
        | div => rw [ho] at h; simp at h
    | fail _ => rw [hr] at h; simp at h
    | div => rw [hr] at h; simp at h
  · obtain ⟨r, hr, -⟩ := WP.spec_imp_exists (parse_file_header_spec record)
    simp only [hr, bind_tc_ok] at h
    rcases r with found | err
    · simp only [lift, bind_tc_ok] at h
      obtain ⟨b, hb, -⟩ := WP.spec_imp_exists (bytes_eq_spec (Array.to_slice found) (Array.to_slice id))
      simp only [hb, bind_tc_ok] at h
      cases b
      · simp at h
      · simp only [if_true] at h
        unfold protected_verdict at h
        rcases c with _ | _ | _
        · simp only [VerdictOk]
          cases ho : inst.opens ev with
          | ok b1 => rw [ho] at h; cases b1 <;> simp_all
          | fail _ => rw [ho] at h; simp at h
          | div => rw [ho] at h; simp at h
        · obtain ⟨b1, hb1, hpost⟩ := WP.spec_imp_exists (record_envelope_ok_spec record id)
          simp only [hb1, bind_tc_ok] at h
          cases b1
          · simp at h
          · exact hpost.mp rfl
        · obtain ⟨b1, hb1, hpost⟩ := WP.spec_imp_exists (record_envelope_ok_spec record id)
          simp only [hb1, bind_tc_ok] at h
          cases b1
          · simp at h
          · simp only [if_true] at h
            refine ⟨hpost.mp rfl, ?_⟩
            cases he : inst.elsewhere ev with
            | ok b2 => rw [he] at h; cases b2 <;> simp_all
            | fail _ => rw [he] at h; simp at h
            | div => rw [he] at h; simp at h
    · simp at h

end Transcrypt.V3Verification

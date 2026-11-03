import V3Wire.Verification.Snapshot
import V3Wire.Verification.Envelope
import V3Wire.Verification.Bytes
import V3Wire.Verification.Path
import V3Wire.Verification.Codec

/-!
Functional refinement of the pre-commit hook's final check of each index
entry: `held_records` (whether `HEAD` and `HEAD^1` hold an entry's exact
record), `staged_check` (which check an entry gets, `StagedCheckOf`),
`reads_blob` (whether the check reads the blob), `staged_verdict`
(whether the entry passes, `VerdictOk`, from the blob and the adapter's
answers through `StagedEvidence`, each asked only when the check needs it)
and `index_verdict`, the loop over the whole index that the hook calls once
(`index_verdict_accepts`: if it accepted, every position was checked with the
run's inputs and passed, `PositionAccepted`).
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

/-- What an accepted verdict says about entry `i`, by its check: the
    adapter's answers (`StagedEvidence`, in the evidence state `ev`) that the
    verdict asked for, each found (`some`), and the envelope of the blob
    `record` for configuration id `id`. -/
def VerdictOk {E : Type} (inst : StagedEvidence E) (ev : E) (i : Usize) (record : Slice U8)
    (id : Std.Array U8 16#usize) : StagedCheck → Prop
  | .Skip => True
  | .NotRecord => inst.is_record ev i = ok (some false)
  | .AuthenticateIfRecord => inst.is_record ev i = ok (some false) ∨ inst.opens ev i = ok (some true)
  | .Protected .Authenticate => inst.opens ev i = ok (some true)
  | .Protected .Envelope => EnvelopeOk (sliceBytes record) (wireBytes id)
  | .Protected .EnvelopeNotMoved => EnvelopeOk (sliceBytes record) (wireBytes id) ∧ inst.elsewhere ev i = ok (some false)

/-- **The verdict.** If `staged_verdict` accepted entry `i`, the answers it
    asked for were found and are as its check requires, and so is the blob's
    envelope (`VerdictOk`). -/
theorem staged_verdict_ok {E : Type} (inst : StagedEvidence E) (ev : E) (i : Usize) (check : StagedCheck)
    (record : Slice U8) (id : Std.Array U8 16#usize)
    (h : staged_verdict inst ev i check record id = ok (core.result.Result.Ok ())) :
    VerdictOk inst ev i record id check := by
  unfold staged_verdict at h
  rcases check with _ | _ | _ | c
  · trivial
  · simp only [VerdictOk]
    cases hr : inst.is_record ev i with
    | ok o => rw [hr] at h; rcases o with _ | b <;> [simp at h; (cases b <;> simp_all)]
    | fail _ => rw [hr] at h; simp at h
    | div => rw [hr] at h; simp at h
  · simp only [VerdictOk]
    cases hr : inst.is_record ev i with
    | ok o =>
      rw [hr] at h
      rcases o with _ | b
      · simp at h
      · cases b
        · exact Or.inl rfl
        · cases ho : inst.opens ev i with
          | ok o1 => rw [ho] at h; rcases o1 with _ | b1 <;> [simp at h; (cases b1 <;> simp_all)]
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
          cases ho : inst.opens ev i with
          | ok o1 => rw [ho] at h; rcases o1 with _ | b1 <;> [simp at h; (cases b1 <;> simp_all)]
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
            cases he : inst.elsewhere ev i with
            | ok o2 => rw [he] at h; rcases o2 with _ | b2 <;> [simp at h; (cases b2 <;> simp_all)]
            | fail _ => rw [he] at h; simp at h
            | div => rw [he] at h; simp at h
    · simp at h

/-! ## `index_verdict`: the hook's check of every index entry -/

/-- **Partial correctness of a loop.** If `loop body x` returned `y` and every
    step of `body` from a state satisfying `inv` either stops with a result
    satisfying `post` or continues to a state satisfying `inv` with a smaller
    `measure`, then `y` satisfies `post`. -/
theorem loop_ok_of {α β : Type} {body : α → RustM (ControlFlow α β)} (measure : α → Nat) (inv : α → Prop)
    (post : β → Prop)
    (hbody : ∀ x r, inv x → body x = ok r → match r with
      | .cont x' => inv x' ∧ measure x' < measure x
      | .done y => post y) :
    ∀ x y, inv x → loop body x = ok y → post y := by
  intro x
  induction hm : measure x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro y hx h
    rw [loop] at h
    cases hb : body x with
    | ok r =>
      rw [hb] at h
      have hstep := hbody x r hx hb
      cases r with
      | cont x' => exact ih (measure x') (hm ▸ hstep.2) x' rfl y hstep.1 h
      | done y' =>
        simp only [ok.injEq] at h
        subst h
        exact hstep
    | fail e => rw [hb] at h; simp at h
    | div => rw [hb] at h; simp at h

/-- **The verdict after reading.** If `read_verdict` on entry `i` returned
    `(r, t)` from a state satisfying `good` (a property every `read` keeps),
    then `t` satisfies `good`; when the check reads a blob, `read` at `i`
    returned `true` and gave `t`, and otherwise `t` is the state it started
    in; and an accepted `r` is `staged_verdict` at `i` accepting the blob
    `blob t` returns. -/
theorem read_verdict_ok {E : Type} {inst : StagedEvidence E} (good : E → Prop)
    (hread : ∀ s k b s', good s → inst.read s k = ok (b, s') → good s')
    {s t : E} (hs : good s) {i : Usize} {c : StagedCheck} {id : Std.Array U8 16#usize}
    {r : core.result.Result Unit StagedRefusal}
    (h : read_verdict inst s i c id = ok (r, t)) :
    good t ∧ (r = core.result.Result.Ok () → (reads_blob c = ok true → inst.read s i = ok (true, t)) ∧
      ∃ record, inst.blob t = ok record ∧ staged_verdict inst t i c record id = ok (core.result.Result.Ok ())) := by
  unfold read_verdict at h
  cases hrb : reads_blob c with
  | fail _ => rw [hrb] at h; simp at h
  | div => rw [hrb] at h; simp at h
  | ok b =>
  rw [hrb] at h
  simp only [bind_tc_ok] at h
  cases b
  · simp only [Bool.false_eq_true, if_false] at h
    cases hb : inst.blob s with
    | fail _ => rw [hb] at h; simp at h
    | div => rw [hb] at h; simp at h
    | ok record =>
    rw [hb] at h
    simp only [bind_tc_ok] at h
    cases hv : staged_verdict inst s i c record id with
    | fail _ => rw [hv] at h; simp at h
    | div => rw [hv] at h; simp at h
    | ok v =>
    rw [hv] at h
    simp only [bind_tc_ok, ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs, fun hr => ⟨fun h' => absurd h' (by simp), record, hb, hr ▸ hv⟩⟩
  · simp only [if_true] at h
    cases hr : inst.read s i with
    | fail _ => rw [hr] at h; simp at h
    | div => rw [hr] at h; simp at h
    | ok p =>
    obtain ⟨b1, t'⟩ := p
    rw [hr] at h
    simp only [bind_tc_ok] at h
    have ht : good t' := hread s i b1 t' hs hr
    cases b1
    · simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ht, fun h' => by cases h'⟩
    · simp at h
      cases hb : inst.blob t' with
      | fail _ => rw [hb] at h; simp at h
      | div => rw [hb] at h; simp at h
      | ok record =>
      rw [hb] at h
      simp only [bind_tc_ok] at h
      cases hv : staged_verdict inst t' i c record id with
      | fail _ => rw [hv] at h; simp at h
      | div => rw [hv] at h; simp at h
      | ok v =>
      rw [hv] at h
      simp only [bind_tc_ok, ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ht, fun hr' => ⟨fun _ => rfl, record, hb, hr' ▸ hv⟩⟩

/-- **What the check of position `k` was** in a run of `index_verdict` whose
    evidence states satisfy `good`: from an evidence state `s` with
    `good s`, the entry got its check `c` (`staged_check` on the run's inputs
    at `k`) and `read_verdict` at `k` accepted it (its blob read for `k`
    when the check reads one, then `staged_verdict`; `read_verdict_ok`). -/
def PositionAccepted {E : Type} (inst : StagedEvidence E) (good : E → Prop) (index : Slice U8)
    (ends : Slice Usize) (flags inHead inParent : Slice Bool) (keyed incremental guard : Bool)
    (id : Std.Array U8 16#usize) (k : Usize) : Prop :=
  ∃ (s : E) (c : StagedCheck) (t : E), good s ∧
    staged_check index ends k flags inHead inParent keyed incremental guard = ok c ∧
    read_verdict inst s k c id = ok (core.result.Result.Ok (), t)

/-- What one step of `index_verdict`'s loop from position `i` leaves: it moves
    on to `i2` in a `good` state with every position below `i2` accepted and
    less of the listing left, or stops, accepting only with every position
    accepted. -/
def IndexStep {E : Type} (inst : StagedEvidence E) (good : E → Prop) (index : Slice U8) (ends : Slice Usize)
    (flags inHead inParent : Slice Bool) (keyed incremental guard : Bool) (id : Std.Array U8 16#usize)
    (i : Usize) : ControlFlow (E × Usize) ((core.result.Result Unit (Usize × StagedRefusal)) × E) → Prop
  | .cont (t, i2) => (good t ∧ ∀ k : Usize, k.val < i2.val →
      PositionAccepted inst good index ends flags inHead inParent keyed incremental guard id k) ∧
      ends.length - i2.val < ends.length - i.val
  | .done (res, _) => res = core.result.Result.Ok () → ∀ k : Usize, k.val < ends.length →
      PositionAccepted inst good index ends flags inHead inParent keyed incremental guard id k

/-- An extracted `i + 1` that succeeded is the successor of `i`. -/
theorem usize_succ {i i2 : Usize} (h : i + 1#usize = ok i2) : i2.val = i.val + 1 := by
  have hadd := UScalar.add_equiv i 1#usize
  rw [h] at hadd
  obtain ⟨-, hv, -⟩ := hadd
  simpa using hv

/-- One step of `index_verdict`'s loop at position `i`, after every earlier
    position was accepted (`IndexStep`): position `i` is accepted if the
    loop moves on, and the loop stops accepting only past the last
    position. -/
theorem index_verdict_body_ok {E : Type} {inst : StagedEvidence E} (good : E → Prop)
    (hread : ∀ s k b s', good s → inst.read s k = ok (b, s') → good s')
    {index : Slice U8} {ends : Slice Usize} {flags inHead inParent : Slice Bool}
    {keyed incremental guard : Bool} {id : Std.Array U8 16#usize} (s : E) (i : Usize)
    (r : ControlFlow (E × Usize) ((core.result.Result Unit (Usize × StagedRefusal)) × E))
    (hs : good s)
    (hprev : ∀ k : Usize, k.val < i.val →
      PositionAccepted inst good index ends flags inHead inParent keyed incremental guard id k)
    (h : index_verdict_loop.body inst index ends flags inHead inParent keyed incremental guard id s i = ok r) :
    IndexStep inst good index ends flags inHead inParent keyed incremental guard id i r := by
  unfold index_verdict_loop.body at h
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok] at h
  split at h
  · rename_i hil
    have hilt : i.val < ends.length := by scalar_tac
    cases hc : staged_check index ends i flags inHead inParent keyed incremental guard with
    | fail _ => rw [hc] at h; simp at h
    | div => rw [hc] at h; simp at h
    | ok c =>
    rw [hc] at h
    simp only [bind_tc_ok] at h
    cases hrv : read_verdict inst s i c id with
    | fail _ => rw [hrv] at h; simp at h
    | div => rw [hrv] at h; simp at h
    | ok p =>
    obtain ⟨v, t⟩ := p
    rw [hrv] at h
    simp only [bind_tc_ok] at h
    have ht := (read_verdict_ok good hread hs hrv).1
    rcases v with ⟨⟩ | refusal
    · simp at h
      cases hi2 : i + 1#usize with
      | fail _ => rw [hi2] at h; simp at h
      | div => rw [hi2] at h; simp at h
      | ok i2 =>
        rw [hi2] at h
        simp only [bind_tc_ok, ok.injEq] at h
        subst h
        have hi2v := usize_succ hi2
        refine ⟨⟨ht, fun k hk => ?_⟩, by omega⟩
        by_cases hki : k.val = i.val
        · have hkeq : k = i := UScalar.eq_of_val_eq hki
          subst hkeq
          exact ⟨s, c, t, hs, hc, hrv⟩
        · exact hprev k (by omega)
    · simp at h
      subst h
      simp [IndexStep]
  · rename_i hil
    simp only [ok.injEq] at h
    subst h
    intro _ k hk
    exact hprev k (by scalar_tac)

/-- **The hook's loop checks every entry.** If `index_verdict` accepted, on
    evidence whose states satisfy `good` from the start state `ev` on (a
    property every `read` keeps), then every position of the index listing
    was accepted (`PositionAccepted`): checked by `staged_check` with the
    run's inputs at that position, its blob read for that position when the
    check reads one, and passed by `staged_verdict`. -/
theorem index_verdict_accepts {E : Type} {inst : StagedEvidence E} (good : E → Prop)
    (hread : ∀ s k b s', good s → inst.read s k = ok (b, s') → good s')
    {ev ev' : E} (hev : good ev) {index : Slice U8} {ends : Slice Usize} {flags inHead inParent : Slice Bool}
    {keyed incremental guard : Bool} {id : Std.Array U8 16#usize}
    (h : index_verdict inst ev index ends flags inHead inParent keyed incremental guard id =
      ok (core.result.Result.Ok (), ev')) :
    ∀ k : Usize, k.val < ends.length →
      PositionAccepted inst good index ends flags inHead inParent keyed incremental guard id k := by
  unfold index_verdict index_verdict_loop at h
  refine loop_ok_of (fun x : E × Usize => ends.length - x.2.val)
    (fun x => good x.1 ∧ ∀ k : Usize, k.val < x.2.val →
      PositionAccepted inst good index ends flags inHead inParent keyed incremental guard id k)
    (fun y => y.1 = core.result.Result.Ok () → ∀ k : Usize, k.val < ends.length →
      PositionAccepted inst good index ends flags inHead inParent keyed incremental guard id k)
    ?_ (ev, 0#usize) _ ⟨hev, fun k hk => absurd hk (by simp)⟩ h rfl
  rintro ⟨s, i⟩ r ⟨hs, hprev⟩ hb
  have := index_verdict_body_ok good hread s i r hs hprev hb
  rcases r with ⟨t, i2⟩ | ⟨res, t⟩
  · exact this
  · exact this

/-! ## `audit_check` -/

/-- What `audit_check` decides for an entry of an audited commit with the
    facts `a` (regular, selected by the commit's attributes, held exactly by
    the first parent, a blob of a path the commit deletes), whose path is
    reserved metadata or not, in an audit with or without the key, from the
    base `base`. Reserved metadata is skipped; a selected entry is refused
    (`none`) unless it is a regular file, which is checked as `entry_check`
    decides, not incremental, settled when the parent holds it; an
    unprotected file is skipped when it is a symlink or submodule, or the
    parent holds it under the same configuration, or, without the key,
    unless it is a moved blob the parent does not hold, which must be no
    record; with the key any other unprotected file is authenticated if it
    is a record. -/
def AuditCheckOf (a : AuditedEntry) (reserved : Prop) (keyed : Bool) (base : AuditBase) :
    Option StagedCheck → Prop
  | none => ¬ reserved ∧ a.selected = true ∧ a.regular = false
  | some (.Protected c) => ¬ reserved ∧ a.selected = true ∧ a.regular = true ∧ EntryCheckOf keyed false a.held c
  | some .Skip => reserved ∨ (a.selected = false ∧
      (a.regular = false ∨ (a.held = true ∧ base = .Parent) ∨ (keyed = false ∧ ¬ (a.moved = true ∧ a.held = false))))
  | some .NotRecord => ¬ reserved ∧ a.selected = false ∧ a.regular = true ∧ ¬ (a.held = true ∧ base = .Parent) ∧
      keyed = false ∧ a.moved = true ∧ a.held = false
  | some .AuthenticateIfRecord => ¬ reserved ∧ a.selected = false ∧ a.regular = true ∧
      ¬ (a.held = true ∧ base = .Parent) ∧ keyed = true

/-- **The audit's check of one entry.** `audit_check` decides
    `AuditCheckOf` its facts and path. -/
theorem audit_check_spec (a : AuditedEntry) (path : Slice U8) (keyed : Bool) (base : AuditBase) :
    audit_check a path keyed base ⦃ r => AuditCheckOf a (Reserved (sliceBytes path)) keyed base r ⦄ := by
  obtain ⟨b, hb, hres⟩ := WP.spec_imp_exists (is_reserved_path_spec path)
  rcases a with ⟨regular, selected, held, moved⟩
  revert keyed
  cases b
  · have hr : ¬ Reserved (sliceBytes path) := fun h => by simpa using hres.mpr h
    intro keyed
    rcases base with _ | _ <;> rcases keyed with _ | _ <;> rcases regular with _ | _ <;> rcases selected with _ | _ <;>
      rcases held with _ | _ <;> rcases moved with _ | _ <;>
      simp [audit_check, hb, entry_check, AuditCheckOf, EntryCheckOf, hr]
  · have hr : Reserved (sliceBytes path) := hres.mp rfl
    intro keyed
    rcases base with _ | _ <;> simp [audit_check, hb, AuditCheckOf, hr]

/-! ## `commit_verdict`: the audit's check of every examined entry -/

/-- An extracted slice index that succeeded read the element at that
    position. -/
theorem slice_index_usize_ok {α : Type} {v : Slice α} {i : Usize} {a : α}
    (h : Slice.index_usize v i = ok a) : v.val[i.val]? = some a := by
  unfold Slice.index_usize at h
  split at h
  · simp at h
  · rename_i x hx
    simp only [ok.injEq] at h
    subst h
    simpa using hx

/-- **The checks an earlier pass settles**: exactly a selected entry's
    `Authenticate` and `Envelope`. -/
theorem settled_by_cache_spec (c : StagedCheck) :
    settled_by_cache c ⦃ b => b = true ↔ c = .Protected .Authenticate ∨ c = .Protected .Envelope ⦄ := by
  rcases c with _ | _ | _ | e
  · simp [settled_by_cache]
  · simp [settled_by_cache]
  · simp [settled_by_cache]
  · rcases e with _ | _ | _ <;> simp [settled_by_cache]

/-- **What the audit's check of examined position `k` was** in a run of
    `commit_verdict` whose evidence states satisfy `good`: from an evidence
    state `s` with `good s`, the path the evidence gave for `k` and the
    entry's facts got the check `c` (`audit_check`), and either an earlier
    pass settled it (`settled_by_cache` and `checked` at `k`) or
    `read_verdict` at `k` accepted it. -/
def CommitPositionAccepted {E : Type} (inst : StagedEvidence E) (cache : AuditedEntries E) (good : E → Prop)
    (entries : Slice AuditedEntry) (keyed : Bool) (base : AuditBase) (id : Std.Array U8 16#usize)
    (k : Usize) : Prop :=
  ∃ (s : E) (path : Slice U8) (facts : AuditedEntry) (c : StagedCheck), good s ∧
    cache.path s k = ok path ∧ entries.val[k.val]? = some facts ∧ audit_check facts path keyed base = ok (some c) ∧
    ((settled_by_cache c = ok true ∧ cache.checked s k = ok true) ∨
      ∃ t, read_verdict inst s k c id = ok (core.result.Result.Ok (), t))

/-- What one step of `commit_verdict`'s loop from position `i` leaves (as
    `IndexStep`). -/
def CommitLoopStep {E : Type} (inst : StagedEvidence E) (cache : AuditedEntries E) (good : E → Prop)
    (entries : Slice AuditedEntry) (keyed : Bool) (base : AuditBase) (id : Std.Array U8 16#usize) (i : Usize) :
    ControlFlow (E × Usize) ((core.result.Result Unit (Usize × AuditRefusal)) × E) → Prop
  | .cont (t, i2) => (good t ∧ ∀ k : Usize, k.val < i2.val →
      CommitPositionAccepted inst cache good entries keyed base id k) ∧
      entries.length - i2.val < entries.length - i.val
  | .done (res, _) => res = core.result.Result.Ok () → ∀ k : Usize, k.val < entries.length →
      CommitPositionAccepted inst cache good entries keyed base id k

/-- One step of `commit_verdict`'s loop at position `i`, after every earlier
    position was accepted (`CommitLoopStep`). -/
theorem commit_verdict_body_ok {E : Type} {inst : StagedEvidence E} {cache : AuditedEntries E}
    (good : E → Prop)
    (hread : ∀ s k b s', good s → inst.read s k = ok (b, s') → good s')
    (hpassed : ∀ s k s', good s → cache.passed s k = ok s' → good s')
    {entries : Slice AuditedEntry} {keyed : Bool} {base : AuditBase} {id : Std.Array U8 16#usize}
    (s : E) (i : Usize) (r : ControlFlow (E × Usize) ((core.result.Result Unit (Usize × AuditRefusal)) × E))
    (hs : good s)
    (hprev : ∀ k : Usize, k.val < i.val → CommitPositionAccepted inst cache good entries keyed base id k)
    (h : commit_verdict_loop.body inst cache entries keyed base id s i = ok r) :
    CommitLoopStep inst cache good entries keyed base id i r := by
  unfold commit_verdict_loop.body at h
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok] at h
  split at h
  · rename_i hil
    have hilt : i.val < entries.length := by scalar_tac
    cases hix : Slice.index_usize entries i with
    | fail _ => rw [hix] at h; simp at h
    | div => rw [hix] at h; simp at h
    | ok facts =>
    rw [hix] at h
    simp only [bind_tc_ok] at h
    have hfacts := slice_index_usize_ok hix
    cases hp : cache.path s i with
    | fail _ => rw [hp] at h; simp at h
    | div => rw [hp] at h; simp at h
    | ok path =>
    rw [hp] at h
    simp only [bind_tc_ok] at h
    cases ha : audit_check facts path keyed base with
    | fail _ => rw [ha] at h; simp at h
    | div => rw [ha] at h; simp at h
    | ok o =>
    rw [ha] at h
    simp only [bind_tc_ok] at h
    -- Moving on from a good state `t` with position `i` accepted.
    have hmove : ∀ (t : E), good t → CommitPositionAccepted inst cache good entries keyed base id i →
        (do
          let i2 ← i + 1#usize
          ok (cont (t, i2)) : RustM (ControlFlow (E × Usize) ((core.result.Result Unit (Usize × AuditRefusal)) × E)))
          = ok r → CommitLoopStep inst cache good entries keyed base id i r := by
      intro t ht hpos hstep
      cases hi2 : i + 1#usize with
      | fail _ => rw [hi2] at hstep; simp at hstep
      | div => rw [hi2] at hstep; simp at hstep
      | ok i2 =>
        rw [hi2] at hstep
        simp only [bind_tc_ok, ok.injEq] at hstep
        subst hstep
        have hi2v := usize_succ hi2
        refine ⟨⟨ht, fun k hk => ?_⟩, by omega⟩
        by_cases hki : k.val = i.val
        · have hkeq : k = i := UScalar.eq_of_val_eq hki
          subst hkeq
          exact hpos
        · exact hprev k (by omega)
    rcases o with _ | c
    · simp at h
      subst h
      simp [CommitLoopStep]
    · simp at h
      cases hsc : settled_by_cache c with
      | fail _ => rw [hsc] at h; simp at h
      | div => rw [hsc] at h; simp at h
      | ok b =>
      rw [hsc] at h
      simp only [bind_tc_ok] at h
      -- Whether an earlier pass settles it.
      have hsettled : ∀ settled : Bool, (if b = true then cache.checked s i else ok false) = ok settled →
          settled = true → settled_by_cache c = ok true ∧ cache.checked s i = ok true := by
        intro settled hset htrue
        subst htrue
        cases b
        · simp at hset
        · exact ⟨hsc, by simpa using hset⟩
      cases hst : (if b = true then cache.checked s i else ok false) with
      | fail _ => rw [hst] at h; simp at h
      | div => rw [hst] at h; simp at h
      | ok settled =>
      rw [hst] at h
      simp only [bind_tc_ok] at h
      cases settled
      · simp only [Bool.false_eq_true, if_false] at h
        cases hrv : read_verdict inst s i c id with
        | fail _ => rw [hrv] at h; simp at h
        | div => rw [hrv] at h; simp at h
        | ok p =>
        obtain ⟨v, t⟩ := p
        rw [hrv] at h
        simp only [bind_tc_ok] at h
        have ht := (read_verdict_ok good hread hs hrv).1
        rcases v with ⟨⟩ | refusal
        · simp at h
          have hpos : CommitPositionAccepted inst cache good entries keyed base id i :=
            ⟨s, path, facts, c, hs, hp, hfacts, ha, Or.inr ⟨t, hrv⟩⟩
          cases hrb : reads_blob c with
          | fail _ => rw [hrb] at h; simp at h
          | div => rw [hrb] at h; simp at h
          | ok b1 =>
          rw [hrb] at h
          simp only [bind_tc_ok] at h
          cases b1
          · simp only [Bool.false_eq_true, if_false, bind_tc_ok] at h
            exact hmove t ht hpos h
          · simp only [if_true] at h
            cases hps : cache.passed t i with
            | fail _ => rw [hps] at h; simp at h
            | div => rw [hps] at h; simp at h
            | ok t2 =>
            rw [hps] at h
            simp only [bind_tc_ok] at h
            exact hmove t2 (hpassed t i t2 ht hps) hpos h
        · simp at h
          subst h
          simp [CommitLoopStep]
      · simp only [if_true] at h
        exact hmove s hs ⟨s, path, facts, c, hs, hp, hfacts, ha, Or.inl (hsettled true hst rfl)⟩ h
  · rename_i hil
    simp only [ok.injEq] at h
    subst h
    intro _ k hk
    exact hprev k (by scalar_tac)

/-- **The audit's loop checks every examined entry.** If `commit_verdict`
    accepted, on evidence whose states satisfy `good` from the start state
    `ev` on (a property every `read` and `passed` keeps), then every examined
    position was accepted (`CommitPositionAccepted`): its check chosen by
    `audit_check` from its facts and path, and either settled by an earlier
    pass or read and passed by `staged_verdict`. -/
theorem commit_verdict_accepts {E : Type} {inst : StagedEvidence E} {cache : AuditedEntries E}
    (good : E → Prop)
    (hread : ∀ s k b s', good s → inst.read s k = ok (b, s') → good s')
    (hpassed : ∀ s k s', good s → cache.passed s k = ok s' → good s')
    {ev ev' : E} (hev : good ev) {entries : Slice AuditedEntry} {keyed : Bool} {base : AuditBase}
    {id : Std.Array U8 16#usize}
    (h : commit_verdict inst cache ev entries keyed base id = ok (core.result.Result.Ok (), ev')) :
    ∀ k : Usize, k.val < entries.length → CommitPositionAccepted inst cache good entries keyed base id k := by
  unfold commit_verdict commit_verdict_loop at h
  refine loop_ok_of (fun x : E × Usize => entries.length - x.2.val)
    (fun x => good x.1 ∧ ∀ k : Usize, k.val < x.2.val →
      CommitPositionAccepted inst cache good entries keyed base id k)
    (fun y => y.1 = core.result.Result.Ok () → ∀ k : Usize, k.val < entries.length →
      CommitPositionAccepted inst cache good entries keyed base id k)
    ?_ (ev, 0#usize) _ ⟨hev, fun k hk => absurd hk (by simp)⟩ h rfl
  rintro ⟨s, i⟩ r ⟨hs, hprev⟩ hb
  have := commit_verdict_body_ok good hread hpassed s i r hs hprev hb
  rcases r with ⟨t, i2⟩ | ⟨res, t⟩
  · exact this
  · exact this


end Transcrypt.V3Verification

import V3Wire.Verification.Refinement

/-!
Functional refinement of the production v3 byte-comparison decisions: byte
equality, prefix matching at an offset (`matches_at`), byte search
(`find_byte`) and the hydrate/lock/seal lifecycle decisions. Each theorem names the
Aeneas-generated translation and relates its complete result to the
independent specification in `Transcrypt.V3Policy`; as `WP.spec` triples
they also exclude panics and divergence.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core

theorem bytes_eq_loop_spec (a b : Slice U8) (hlen : a.length = b.length) (i : Usize)
    (hi : i.val ≤ a.length) (h : MatchesUpTo a.val b.val 0 i.val) :
    bytes_eq_loop a b i ⦃ r => r = true ↔ a.val = b.val ⦄ := by
  unfold bytes_eq_loop
  apply compare_loop _ (fun n => MatchesUpTo a.val b.val 0 n) a.length _ _ i hi h
  intro j hj hc
  unfold bytes_eq_loop.body
  simp_len
  step*
  · refine ⟨i4_post, by omega, ?_⟩
    rw [i4_post]
    apply hc.step
    have hne := ‹¬(_ != _) = true›
    simp_bne at hne
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
  simp_len
  step*
  rename_i hne
  have hlen : a.length = b.length := by
    simp_bne at hne
    scalar_tac
  exact bytes_eq_loop_spec a b hlen 0#usize (by simp) (MatchesUpTo.zero _ _ _)

theorem map_prefix_drop_iff (l p : List U8) (j : Nat) (hj : j ≤ l.length) :
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

/-! ## `matches_at` -/

theorem matches_at_loop_spec (bytes expected : Slice U8) (a : Usize)
    (hj : a.val + expected.length ≤ bytes.length) (k : Usize) (hk : k.val ≤ expected.length)
    (h : MatchesUpTo bytes.val expected.val a.val k.val) :
    matches_at_loop bytes a expected k ⦃ r =>
      r = true ↔ MatchesUpTo bytes.val expected.val a.val expected.length ⦄ := by
  unfold matches_at_loop
  apply compare_loop _ (fun n => MatchesUpTo bytes.val expected.val a.val n) expected.length _ _ k hk h
  intro m hm hc
  unfold matches_at_loop.body
  simp_len
  have hrl : bytes.length = bytes.val.length := rfl
  have hel : expected.length = expected.val.length := rfl
  step*
  · have hne := ‹(_ != _) = true›
    simp_bne at hne
    simp only [Bool.false_eq_true, false_iff]
    intro hall
    apply hne
    have := hall m.val (by omega)
    rw [getElem!_pos bytes.val (a.val + m.val) (by omega),
      getElem!_pos expected.val m.val (by omega)] at this
    rw [i2_post2, i3_post2, ← this]
    simp only [i1_post]
  · refine ⟨k1_post, by omega, ?_⟩
    rw [k1_post]
    apply hc.step
    have hne := ‹¬(_ != _) = true›
    simp_bne at hne
    rw [getElem!_pos bytes.val (a.val + m.val) (by omega),
      getElem!_pos expected.val m.val (by omega)]
    rw [i2_post2, i3_post2] at hne
    simpa only [i1_post] using hne

/-- `matches_at bytes at expected` holds iff `at` is within `bytes` and
    `expected` is a prefix of `bytes[at..]`. -/
@[step]
theorem matches_at_spec (bytes : Slice U8) (a : Usize) (expected : Slice U8) :
    matches_at bytes a expected ⦃ r => r = true ↔
      (a.val ≤ bytes.length ∧ sliceBytes expected <+: (sliceBytes bytes).drop a.val) ⦄ := by
  unfold matches_at
  simp_len
  have hrl : bytes.length = bytes.val.length := rfl
  have hel : expected.length = expected.val.length := rfl
  step*
  · simp only [Bool.false_eq_true, false_iff, not_and]
    intro hle hp
    have := hp.length_le
    simp only [sliceBytes, List.length_map, List.length_drop] at this
    scalar_tac
  · rename_i hge
    have hlen : a.val + expected.length ≤ bytes.length := by scalar_tac
    have hale : a.val ≤ bytes.length := by omega
    apply WP.spec_mono (matches_at_loop_spec bytes expected a hlen 0#usize (by simp)
      (MatchesUpTo.zero _ _ _))
    intro r hr
    rw [hr, sliceBytes, sliceBytes, map_prefix_drop_iff _ _ _ (by omega)]
    constructor
    · intro hm; exact ⟨hale, by omega, hm⟩
    · intro hm; exact hm.2.2

/-! ## `find_byte` -/

/-- `j` is reached from `f` over bytes of `l` other than `c`: either within
    `l`, or `j = f` when `f` is past the end. -/
def ByteScan (l : List Nat) (c f j : Nat) : Prop :=
  f ≤ j ∧ (j ≤ l.length ∨ j = f) ∧ ∀ k, f ≤ k → k < j → l[k]! ≠ c

theorem find_byte_loop_spec (bytes : Slice U8) (c : U8) (f j : Usize)
    (h : ByteScan (sliceBytes bytes) c.val f.val j.val) :
    find_byte_loop bytes c j ⦃ r => ByteScan (sliceBytes bytes) c.val f.val r.val ∧
      (r.val < bytes.length → (sliceBytes bytes)[r.val]! = c.val) ⦄ := by
  unfold find_byte_loop
  apply loop.spec_decr_nat (fun s => bytes.length - s.val)
    (fun s => ByteScan (sliceBytes bytes) c.val f.val s.val)
  · intro j hj
    unfold find_byte_loop.body
    simp_len
    have hl := sliceBytes_length bytes
    step*
    · obtain ⟨h1, _, h3⟩ := hj
      subst i1_post2
      have hb : (sliceBytes bytes)[j.val]! ≠ c.val := by
        have := ‹(_ != c) = true›
        simp_bne at this
        rw [sliceBytes_getElem! bytes j.val i1]
        exact fun h0 => this (UScalar.eq_of_val_eq h0)
      refine ⟨⟨by omega, Or.inl (by omega), fun k hk1 hk2 => ?_⟩, by omega⟩
      rcases Nat.lt_or_ge k j.val with hlt | hge
      · exact h3 k hk1 hlt
      · rw [show k = j.val by omega]; exact hb
    · refine ⟨hj, fun _ => ?_⟩
      subst i1_post2
      have := ‹¬(_ != c) = true›
      simp_bne at this
      rw [sliceBytes_getElem! bytes j.val i1, this]
  · exact h

/-- `find_byte bytes from c` is the first `c` at or after `from`, or the end
    of `bytes` (and `from` itself when `from` is past the end). -/
@[step]
theorem find_byte_spec (bytes : Slice U8) (f : Usize) (c : U8) :
    find_byte bytes f c ⦃ r => ByteScan (sliceBytes bytes) c.val f.val r.val ∧
      (r.val < bytes.length → (sliceBytes bytes)[r.val]! = c.val) ⦄ := by
  unfold find_byte
  exact find_byte_loop_spec bytes c f f ⟨le_refl _, Or.inr rfl, fun k h1 h2 => absurd h2 (by omega)⟩

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

/-- Rust encoding of the specification's pre-commit repair decision. -/
def sealResult : Transcrypt.V3Policy.SealAction → SealAction
  | .keep => .Keep
  | .seal => .Seal
  | .rebind => .Rebind
  | .leave => .Leave

/-- `seal_action` makes exactly the spec's repair decision, so the adapter's
    pre-commit hook re-encrypts only local changes
    (`sealSpec_repairs_only_local`). -/
@[step]
theorem seal_action_spec (opens isLocal envelope moved : Bool) :
    seal_action opens isLocal envelope moved ⦃ r =>
      r = sealResult (Transcrypt.V3Policy.sealSpec opens isLocal envelope moved) ⦄ := by
  rcases opens with _ | _ <;> rcases isLocal with _ | _ <;> rcases envelope with _ | _ <;>
    rcases moved with _ | _ <;>
    simp [seal_action, Transcrypt.V3Policy.sealSpec, sealResult]

/-- `entry_check` authenticates exactly when the key is available and the
    entry is not a settled one in the incremental hook; otherwise it checks
    the envelope, and skips the move check only for a settled entry. -/
@[step]
theorem entry_check_spec (keyed incremental settled : Bool) :
    entry_check keyed incremental settled ⦃ c =>
      (c = .Authenticate ↔ keyed = true ∧ ¬ (incremental = true ∧ settled = true)) ∧
      (c = .Envelope ↔ ¬ (keyed = true ∧ ¬ (incremental = true ∧ settled = true)) ∧
        settled = true) ⦄ := by
  rcases keyed with _ | _ <;> rcases incremental with _ | _ <;> rcases settled with _ | _ <;>
    simp [entry_check]

end Transcrypt.V3Verification

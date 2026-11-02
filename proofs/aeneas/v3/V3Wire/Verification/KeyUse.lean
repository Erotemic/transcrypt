import V3Wire.Verification.Protocol
import V3Wire.Verification.Objects

/-!
# The key a configuration is used with

`authenticate_key` is the only way the adapter obtains primitives for a
configuration: it builds them from key bytes with the adapter's key
schedule (`V3KeySchedule::from_key`) and returns them only if they
authenticate the configuration. `unlock_stored_key` applies it to the stored
key file: it selects the key bytes `file[CONFIG_LEN..KEY_FILE_LEN]`, and
returns their primitives, with the configuration they authenticated, exactly
when `stored_key_state` says `Unlocked`.

The primitives are related to key bytes by one contract on the key
schedule, `KeyScheduleRealizes`: whatever `from_key k` returns realizes the
suite of exactly the bytes `k` (`σ k`). That is the part of A5/A17 that
remains assumed about the key: the theorems here name the key bytes, so
"`from_key` builds primitives for a different key" is excluded by that
contract, and "the adapter pairs primitives with another configuration or
key source" is excluded by the core's code.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

variable {P : Type} {inst : V3Primitives P} {sched : V3KeySchedule P} {σ : List Nat → Suite}

/-- **The key schedule contract** (A5 under one key, for every key; A17).
    Primitives that `from_key` builds from the key bytes `key` realize the
    suite of exactly those bytes. `from_key` may refuse (`None`). -/
def KeyScheduleRealizes (inst : V3Primitives P) (sched : V3KeySchedule P) (σ : List Nat → Suite) : Prop :=
  ∀ key : Slice U8, WP.spec (sched.from_key key) (fun r =>
    ∀ p, r = core.option.Option.Some p → Realizes inst p (σ (sliceBytes key)))

/-- **Authenticated key.** `authenticate_key` returns only primitives that
    realize the suite of the given key bytes and under which the
    configuration authenticates. -/
theorem authenticate_key_spec (hK : KeyScheduleRealizes inst sched σ) (key : Slice U8)
    (config : Std.Array U8 55#usize) :
    authenticate_key inst sched key config ⦃ r => ∀ p, r = core.result.Result.Ok p →
      Realizes inst p (σ (sliceBytes key)) ∧ ConfigAuthentic (σ (sliceBytes key)) (wireBytes config) ⦄ := by
  unfold authenticate_key
  step with hK key as ⟨ o, ho ⟩
  match o with
  | core.option.Option.None => simp
  | core.option.Option.Some prims =>
    have hR := ho prims rfl
    simp only
    step with authenticate_config_spec hR config as ⟨ r, hr ⟩
    match r with
    | core.result.Result.Ok c =>
      simp only [core.result.Result.Ok.injEq, forall_eq', WP.spec_ok]
      exact ⟨hR, hr.1⟩
    | core.result.Result.Err e => simp

theorem unlock_stored_key_loop_spec (input : Slice U8) (hlen : input.length = Transcrypt.V3Wire.configLen)
    (base record : Std.Array U8 55#usize) (i : Usize) (hi : i.val ≤ Transcrypt.V3Wire.configLen)
    (h : Copied record.val base.val input.val 0 0 i.val) :
    unlock_stored_key_loop input record i ⦃ r =>
      Copied r.val base.val input.val 0 0 Transcrypt.V3Wire.configLen ⦄ := by
  unfold unlock_stored_key_loop
  apply copy_loop (val := fun o : Std.Array U8 55#usize => o.val) (bound := Transcrypt.V3Wire.configLen)
    _ _ _ _ _ _ _ _ hi h
  intro o k hk hc
  unfold_v3_bytes
  unfold unlock_stored_key_loop.body
  have ho : o.length = 55 := by simp
  have hID := CONFIG_LEN_val
  step*
  have hkb : k.val < 55 := by scalar_tac
  refine ⟨i2_post, by omega, ?_⟩
  rw [a_post, i2_post]
  apply Copied.array_step hc (by simp)
  · rw [i1_post2, Nat.zero_add, getElem!_pos input.val k.val i1]
  · simp; omega

/-- The key bytes of a stored key file: everything after the configuration. -/
def storedKeyBytes (file : List Nat) : List Nat := file.drop Transcrypt.V3Wire.configLen

/-- What `unlock_stored_key` returns, in terms of the bytes. `Ok` carries
    primitives realizing the suite of the file's key bytes (`storedKeyBytes`),
    and the configuration they authenticate, which is the current one and
    the one the file names; `Err` is a stored-key state of the
    specification, never `Unlocked`. -/
def StoredUnlock (inst : V3Primitives P) (σ : List Nat → Suite) (present : Bool) (file current : List Nat) :
    core.result.Result (P × Std.Array U8 55#usize) transcrypt_v3_core.StoredKey → Prop
  | .Ok (p, cfg) =>
      present = true ∧ file.length = keyFileLen ∧ file.take Transcrypt.V3Wire.configLen = current ∧
      wireBytes cfg = current ∧
      Realizes inst p (σ (storedKeyBytes file)) ∧ ConfigAuthentic (σ (storedKeyBytes file)) (wireBytes cfg)
  | .Err s => s ≠ .Unlocked ∧ ∃ authentic, s = storedKeyResult (storedKeySpec present file current authentic)

/-- `stored_key_state` with `authentic = false` is a state, never `Unlocked`. -/
theorem stored_key_state_unauthentic (present : Bool) (file current : Slice U8) :
    stored_key_state present file current false ⦃ sk =>
      sk ≠ .Unlocked ∧ ∃ authentic, sk = storedKeyResult
        (storedKeySpec present (sliceBytes file) (sliceBytes current) authentic) ⦄ := by
  apply WP.spec_mono (stored_key_state_spec present file current false)
  intro sk hsk
  refine ⟨?_, false, hsk⟩
  intro hu
  rw [hu] at hsk
  have h : storedKeySpec present (sliceBytes file) (sliceBytes current) false = .unlocked := by
    cases h : storedKeySpec present (sliceBytes file) (sliceBytes current) false <;>
      rw [h] at hsk <;> simp [storedKeyResult] at hsk ⊢
  exact absurd (storedKeySpec_unlocked h).2.2.2 (by simp)

/-- A stored-key state computed with `authentic = false` is `unlock_stored_key`'s
    refusal: never `Unlocked`. -/
theorem unlock_stored_key_refusal (present : Bool) (file current : Slice U8) :
    (stored_key_state present file current false >>= fun sk =>
      ok (core.result.Result.Err sk : core.result.Result (P × Std.Array U8 55#usize) transcrypt_v3_core.StoredKey))
      ⦃ r => StoredUnlock inst σ present (sliceBytes file) (sliceBytes current) r ⦄ := by
  step with stored_key_state_unauthentic present file current as ⟨ sk, hsk1, a, hsk2 ⟩
  simp only [StoredUnlock]
  exact ⟨hsk1, a, hsk2⟩

/-- **Stored-key selection.** `unlock_stored_key` returns primitives only for
    a present `keyFileLen`-byte file whose first `configLen` bytes are the
    current configuration; they realize the suite of the file's key bytes
    (the rest of the file) and that configuration authenticates under them.
    Otherwise it returns the specification's stored-key state. -/
theorem unlock_stored_key_spec (hK : KeyScheduleRealizes inst sched σ) (present : Bool)
    (file current : Slice U8) :
    unlock_stored_key inst sched present file current ⦃ r =>
      StoredUnlock inst σ present (sliceBytes file) (sliceBytes current) r ⦄ := by
  have hfl := sliceBytes_length file
  have hcl := sliceBytes_length current
  have hkf := KEY_FILE_LEN_val
  have hc := CONFIG_LEN_val
  induction present using Bool.rec
  · unfold unlock_stored_key
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact unlock_stored_key_refusal false file current
  unfold unlock_stored_key
  simp_len [bind_tc_ok]
  simp only [↓reduceIte]
  · split
    · exact unlock_stored_key_refusal true file current
    · rename_i h119
      have h119' : file.length = 119 := by
        simp_bne at h119
        have := congrArg UScalar.val h119; simpa [hkf] using this
      split
      · exact unlock_stored_key_refusal true file current
      · rename_i h55
        have h55' : current.length = 55 := by
          simp_bne at h55
          have := congrArg UScalar.val h55; simpa [hc] using this
        step with unlock_stored_key_loop_spec current h55' (Std.Array.repeat 55#usize 0#u8) as ⟨ cfg, hcfg ⟩
        · exact Copied.zero _ _ _ _
        have hcv : cfg.val = current.val := by
          rw [copied_full hcfg (by unfold_v3_bytes; simp) (by unfold_v3_bytes; simp [h55'])]
          exact List.take_of_length_le (by unfold_v3_bytes; simp [h55'])
        have hcb : wireBytes cfg = sliceBytes current := by
          simp only [wireBytes, sliceBytes, hcv]
        step with index_range_spec file CONFIG_LEN KEY_FILE_LEN (by rw [hc, hkf]; omega)
          (by rw [hkf]; omega) as ⟨ s, hs ⟩
        have hsk : sliceBytes s = storedKeyBytes (sliceBytes file) := by
          rw [hs, hc, hkf, List.extract_eq_take_drop, storedKeyBytes]
          apply List.take_of_length_le
          simp [hfl, h119']
        step with authenticate_key_spec hK s cfg as ⟨ r, hr ⟩
        match r with
        | core.result.Result.Ok prims =>
          obtain ⟨hR, hca⟩ := hr prims rfl
          simp only
          step with stored_key_state_spec true file current true as ⟨ sk, hsk' ⟩
          rcases sk with _ | _ | _ | _ <;> simp only [WP.spec_ok, StoredUnlock]
          · exact ⟨by simp, true, hsk'⟩
          · exact ⟨by simp, true, hsk'⟩
          · exact ⟨by simp, true, hsk'⟩
          · have hu : storedKeySpec true (sliceBytes file) (sliceBytes current) true = .unlocked := by
              cases h : storedKeySpec true (sliceBytes file) (sliceBytes current) true <;>
                rw [h] at hsk' <;> simp [storedKeyResult] at hsk' ⊢
            obtain ⟨-, hl, ht, -⟩ := storedKeySpec_unlocked hu
            rw [hsk] at hR hca
            exact ⟨trivial, hl, ht, hcb, hR, hca⟩
        | core.result.Result.Err _ =>
          simp only
          exact unlock_stored_key_refusal true file current

end Transcrypt.V3Verification

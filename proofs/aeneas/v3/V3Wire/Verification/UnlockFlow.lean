import V3Wire.Verification.Profiles
import V3Wire.Verification.KeyUse

/-!
# Unlocking with a passphrase, for every profile

A Lean model of the adapter's `ValidatedKey::unlock`
(`rust/crates/transcrypt-rs/src/lib.rs`), which calls two extracted core
functions in sequence: `derive_config_key` (the configuration's own profile
and salt select the derivation) and then `authenticate_key` (primitives are
built from exactly the derived bytes and returned only if they authenticate
the configuration). The model is the sequencing; both steps are the
production functions. What the adapter adds and the model does not cover is
the zeroization of the key buffer and the error messages (A4).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy (KeyDerivation passphraseOk profileKdf ConfigAuthentic Suite)

namespace Transcrypt.V3Verification

open transcrypt_v3_core

/-- `ValidatedKey::unlock`: derive the key for `config` from the passphrase,
    then authenticate it. Returns the outcome and the key buffer. -/
def unlockFlow {K P : Type} (kinst : V3Kdf K) (kdf : K) (inst : V3Primitives P) (sched : V3KeySchedule P)
    (config : Std.Array U8 55#usize) (pw : Slice U8) :
    RustM (core.result.Result P Refusal × Std.Array U8 64#usize) := do
  let (r, key) ← derive_config_key kinst kdf config pw (Std.Array.repeat 64#usize 0#u8)
  match r with
  | core.result.Result.Ok _ =>
    let a ← authenticate_key inst sched (Std.Array.to_slice key) config
    ok (a, key)
  | core.result.Result.Err e => ok (core.result.Result.Err e, key)

variable {K P : Type} {kinst : V3Kdf K} {kdf : K} {D : KeyDerivation}
  {inst : V3Primitives P} {sched : V3KeySchedule P} {σ : List Nat → Suite}

/-- **Unlock, for every profile.** If unlocking succeeds, the committed
    configuration is the encoding of some profile `prof` with some salt, the
    key is that profile's own derivation (`profileKdf prof`, fixed
    parameters) of the passphrase and that salt, and the primitives realize
    the suite of exactly that key, under which the configuration
    authenticates. So no configuration makes a passphrase unlock through
    another profile's derivation, other parameters or another salt, and the
    key in use is the one the configuration authenticates. -/
theorem unlock_uses_the_profile_key_and_authenticates (hK : KdfRealizes kinst kdf D)
    (hS : KeyScheduleRealizes inst sched σ) (config : Std.Array U8 55#usize) (pw : Slice U8) :
    unlockFlow kinst kdf inst sched config pw ⦃ r => ∀ prims, r.1 = core.result.Result.Ok prims →
      ∃ prof salt tag, wireBytes config = Transcrypt.V3Wire.encodeConfig prof salt tag ∧
        wireBytes r.2 = D.derive (profileKdf prof) (sliceBytes pw) salt ∧
        passphraseOk prof (sliceBytes pw) = true ∧
        Realizes inst prims (σ (wireBytes r.2)) ∧ ConfigAuthentic (σ (wireBytes r.2)) (wireBytes config) ⦄ := by
  unfold unlockFlow
  step with derive_config_key_uses_config_profile hK config pw (Std.Array.repeat 64#usize 0#u8) as ⟨ r1, key1, h1 ⟩
  rcases r1 with p | e
  · step with authenticate_key_spec hS (Std.Array.to_slice key1) config as ⟨ a, ha ⟩
    try simp only [WP.spec_ok]
    intro prims hp
    obtain ⟨salt, tag, he, hkey, hok⟩ := h1 p rfl
    have hsb : sliceBytes (Std.Array.to_slice key1) = wireBytes key1 := rfl
    obtain ⟨hR, hA⟩ := ha prims hp
    rw [hsb] at hR hA
    exact ⟨profileSpec p, salt, tag, he, hkey, hok, hR, hA⟩
  · try simp only [WP.spec_ok]
    intro prims hp
    cases hp

/-- `ValidatedKey::initialize` (`init`, `rekey`, `migrate`): derive the key of
    the chosen profile from the passphrase and a fresh salt, seal the new
    configuration with it, and authenticate the result. (The adapter builds
    the sealing primitives with `Keyed::new`, which is what `from_key` does
    for a 64-byte key, A17.) -/
def initFlow {K P : Type} (kinst : V3Kdf K) (kdf : K) (inst : V3Primitives P) (sched : V3KeySchedule P)
    (profile : Profile) (salt : Std.Array U8 32#usize) (pw : Slice U8) :
    RustM (core.result.Result (P × Std.Array U8 55#usize) Refusal × Std.Array U8 64#usize) := do
  let (r, key) ← derive_profile_key kinst kdf profile pw salt (Std.Array.repeat 64#usize 0#u8)
  match r with
  | core.result.Result.Err e => ok (core.result.Result.Err e, key)
  | core.result.Result.Ok _ =>
    let o ← sched.from_key (Std.Array.to_slice key)
    match o with
    | core.option.Option.None => ok (core.result.Result.Err Refusal.Primitive, key)
    | core.option.Option.Some sealing =>
      let c ← initialize_config inst sealing profile salt
      match c with
      | core.result.Result.Err e => ok (core.result.Result.Err e, key)
      | core.result.Result.Ok cfg =>
        let a ← authenticate_key inst sched (Std.Array.to_slice key) cfg
        match a with
        | core.result.Result.Ok prims => ok (core.result.Result.Ok (prims, cfg), key)
        | core.result.Result.Err e => ok (core.result.Result.Err e, key)

/-- **A new configuration has the chosen profile and its key.** If
    initialization succeeds, the new configuration is the encoding of the
    requested profile and the fresh salt, the key is that profile's
    derivation of the passphrase and salt, and the configuration
    authenticates under it (so `unlock` with the same passphrase derives the
    same key, `unlock_uses_the_profile_key_and_authenticates`). -/
theorem init_creates_the_profile_config (hK : KdfRealizes kinst kdf D)
    (hS : KeyScheduleRealizes inst sched σ) (profile : Profile) (salt : Std.Array U8 32#usize) (pw : Slice U8) :
    initFlow kinst kdf inst sched profile salt pw ⦃ r => ∀ prims cfg, r.1 = core.result.Result.Ok (prims, cfg) →
      (∃ tag, wireBytes cfg = Transcrypt.V3Wire.encodeConfig (profileSpec profile) (wireBytes salt) tag) ∧
        wireBytes r.2 = D.derive (profileKdf (profileSpec profile)) (sliceBytes pw) (wireBytes salt) ∧
        Realizes inst prims (σ (wireBytes r.2)) ∧ ConfigAuthentic (σ (wireBytes r.2)) (wireBytes cfg) ⦄ := by
  unfold initFlow
  step with derive_profile_key_spec hK profile pw salt (Std.Array.repeat 64#usize 0#u8) as ⟨ r1, key1, h1 ⟩
  have hsb : sliceBytes (Std.Array.to_slice key1) = wireBytes key1 := rfl
  rcases r1 with u | e
  · obtain ⟨_, hkey⟩ := h1
    step with hS (Std.Array.to_slice key1) as ⟨ o, ho ⟩
    rcases o with _ | sealing
    · try simp only [WP.spec_ok]
      intro prims cfg hp
      cases hp
    · have hR := ho sealing rfl
      rw [hsb] at hR
      step with initialize_config_spec hR profile salt as ⟨ c, hc ⟩
      rcases c with cfg | e
      · obtain ⟨_, hcfg⟩ := hc
        step with authenticate_key_spec hS (Std.Array.to_slice key1) cfg as ⟨ a, ha ⟩
        rcases a with prims | e
        · try simp only [WP.spec_ok]
          intro prims' cfg' hp
          simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          obtain ⟨hR2, hA⟩ := ha prims rfl
          rw [hsb] at hR2 hA
          exact ⟨⟨_, hcfg⟩, hkey, hR2, hA⟩
        · try simp only [WP.spec_ok]
          intro prims' cfg' hp
          cases hp
      · try simp only [WP.spec_ok]
        intro prims cfg hp
        cases hp
  · try simp only [WP.spec_ok]
    intro prims cfg hp
    cases hp

end Transcrypt.V3Verification

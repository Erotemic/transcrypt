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

end Transcrypt.V3Verification

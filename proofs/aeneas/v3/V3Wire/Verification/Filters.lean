import V3Wire.Verification.Protocol
import V3Wire.Verification.Envelope

/-!
Models of the Git filter decisions made by the adapter.

* `cleanModel` mirrors `transcrypt_v3::clean_file`: an input that already
  authentically opens at its path is returned unchanged (idempotent clean);
  anything else is sealed with `seal_record`. The agent's Encrypt operation
  and the reseal step of `lock` both go through this function.
* `lockedFilterModel` mirrors the clean and smudge filters when no agent is
  running: the input passes through unchanged only if its keyless envelope
  names the checkout's configuration; otherwise the filter refuses.

As with `Lifecycle.lean`, that the Rust adapter follows these models is
assumption A4; the theorems themselves rely only on the primitive contract
`Realizes` (A5).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

variable {P : Type} {inst : V3Primitives P} {prims : P} {σ : Suite}

/-- Model of `transcrypt_v3::clean_file`. `none` = refusal. -/
def cleanModel (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize)
    (path input openBuf sealBuf : Slice U8) : RustM (Option (Slice U8)) := do
  let (r, _) ← open_record inst prims config path input openBuf
  match r with
  | core.result.Result.Ok _ => ok (some input)
  | core.result.Result.Err _ =>
    let (s, out) ← seal_record inst prims config path input sealBuf
    match s with
    | core.result.Result.Ok _ => ok (some out)
    | core.result.Result.Err _ => ok none

/-- Clean either passes through an input that is already a genuine record at
    this path, or stores exactly the spec's sealed record of the input. -/
theorem cleanModel_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (path input openBuf sealBuf : Slice U8) :
    cleanModel inst prims config path input openBuf sealBuf ⦃ r => ∀ out, r = some out →
      (sliceBytes out = sliceBytes input ∧
        ∃ pt, OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes input) pt) ∨
      (MaySeal σ (wireBytes config) (sliceBytes path) (sliceBytes input) ∧
        sliceBytes out = sealedRecord σ (wireBytes config) (sliceBytes path) (sliceBytes input)) ⦄ := by
  unfold cleanModel
  step with open_record_spec h config path input openBuf as ⟨ r, pt, hr ⟩
  rcases r with u | x
  · simp only at hr ⊢
    simp only [WP.spec_ok, Option.some.injEq]
    rintro out rfl
    exact Or.inl ⟨rfl, _, hr⟩
  · simp only
    step with seal_record_spec h config path input sealBuf as ⟨ s, out, hs ⟩
    rcases s with u | y
    · simp only at hs ⊢
      simp only [WP.spec_ok, Option.some.injEq]
      rintro out' rfl
      exact Or.inr hs
    · simp

/-- Clean only ever stores genuine records. -/
theorem cleanModel_genuine (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (path input openBuf sealBuf : Slice U8) :
    cleanModel inst prims config path input openBuf sealBuf ⦃ r => ∀ out, r = some out →
      ∃ pt, OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes out) pt ⦄ := by
  apply WP.spec_mono (cleanModel_spec h config path input openBuf sealBuf)
  intro r hr out hout
  rcases hr out hout with ⟨heq, pt, hop⟩ | ⟨hmay, hseal⟩
  · exact ⟨pt, heq ▸ hop⟩
  · exact ⟨sliceBytes input, hseal ▸ seal_opens σ hmay⟩

/-- Idempotence: a genuine record (with a right-sized open buffer) is
    returned unchanged. -/
theorem cleanModel_idempotent (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (path input openBuf sealBuf : Slice U8) (pt : List Nat)
    (hop : OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes input) pt)
    (hl : openBuf.length = pt.length) :
    cleanModel inst prims config path input openBuf sealBuf ⦃ r => r = some input ⦄ := by
  unfold cleanModel
  step with open_record_complete h config path input openBuf pt hop hl as ⟨ r, buf, hr, _ ⟩
  rw [hr]
  simp

/-- Model of the clean and smudge filters when no agent is running. -/
def lockedFilterModel (input : Slice U8) (id : Std.Array U8 16#usize) :
    RustM (Option (Slice U8)) := do
  let k ← record_envelope_ok input id
  if k then ok (some input) else ok none

/-- Locked filters only ever pass through, unchanged, an input whose keyless
    envelope names this configuration. -/
theorem lockedFilterModel_spec (input : Slice U8) (id : Std.Array U8 16#usize) :
    lockedFilterModel input id ⦃ r => ∀ out, r = some out →
      out = input ∧ Transcrypt.V3Policy.EnvelopeOk (sliceBytes input) (wireBytes id) ⦄ := by
  unfold lockedFilterModel
  step with record_envelope_ok_spec input id as ⟨ k, hk ⟩
  split
  · rename_i hkt
    simp only [WP.spec_ok, Option.some.injEq]
    rintro out rfl
    exact ⟨rfl, hk.1 hkt⟩
  · simp

end Transcrypt.V3Verification

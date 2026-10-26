import V3Wire.Verification.Protocol
import V3Wire.Verification.Envelope

/-!
Models of the Git filter decisions made by the adapter.

* `cleanModel` mirrors `transcrypt_v3::clean_file`: an input that already
  authentically opens at its path is returned unchanged (idempotent clean);
  anything else is sealed with `seal_record`. The agent's Encrypt operation
  and the reseal step of `lock` both go through this function.
* `smudgeModel` mirrors the smudge filter of `transcrypt_v3`: the verified
  core decides (`smudge_action`); a record of this configuration is opened
  with `open_record` when the key is available (and, when `keepRecord` -- the
  adapter's private mode under a permissive umask -- the authenticated record
  itself is kept), any other v3 record is kept unchanged, and bytes without
  the v3 envelope are refused.
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

/-- Model of the smudge filter. `id` is the checkout's configuration id and
    `unlocked` whether the key is available. `none` = refusal. -/
def smudgeModel (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) (unlocked keepRecord : Bool) (path input buf : Slice U8) :
    RustM (Option (Slice U8)) := do
  let a ← smudge_action input id unlocked
  match a with
  | core.result.Result.Ok SmudgeAction.Keep => ok (some input)
  | core.result.Result.Ok SmudgeAction.Open =>
    let (r, out) ← open_record inst prims config path input buf
    match r with
    | core.result.Result.Ok _ => ok (some (if keepRecord then input else out))
    | core.result.Result.Err _ => ok none
  | core.result.Result.Err _ => ok none

/-- **Smudge never presents unauthenticated non-record bytes.** Its output is
    either the unchanged input, which then has the v3 file envelope (within
    the size bound) and, whenever the spec's smudge decision was to open it,
    authenticates at this path under this configuration; or exactly the
    plaintext that the input authentically opens to. -/
theorem smudgeModel_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) (unlocked keepRecord : Bool) (path input buf : Slice U8) :
    smudgeModel inst prims config id unlocked keepRecord path input buf ⦃ r => ∀ out, r = some out →
      (out = input ∧
        (∃ found, Transcrypt.V3Wire.decodeFileHeaderShape (sliceBytes input) = some found ∧
          input.length ≤ maxRecord) ∧
        (smudgeSpec (sliceBytes input) (wireBytes id) unlocked = some .open_ →
          ∃ pt, OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes input) pt)) ∨
      OpensTo σ (wireBytes config) (sliceBytes path) (sliceBytes input) (sliceBytes out) ⦄ := by
  unfold smudgeModel
  step with smudge_action_spec input id unlocked as ⟨ a, ha ⟩
  rcases a with (_ | _) | e
  · -- Open
    simp only
    step with open_record_spec h config path input buf as ⟨ r, out, hr ⟩
    rcases r with u | x
    · simp only at hr ⊢
      simp only [WP.spec_ok, Option.some.injEq]
      rintro out' rfl
      cases keepRecord
      · exact Or.inr hr
      · left
        obtain ⟨hl, hd⟩ := opensTo_envelopeOk σ hr
        refine ⟨rfl, ⟨_, hd, by rw [sliceBytes_length] at hl; exact hl⟩, fun _ => ⟨_, hr⟩⟩
    · simp
  · -- Keep
    obtain ⟨s, hs, ha'⟩ := ha
    have hk : s = .keep := by cases s <;> simp_all [smudgeResult]
    subst hk
    simp only [WP.spec_ok, Option.some.injEq]
    rintro out rfl
    left
    obtain ⟨found, hf, hl⟩ := smudgeSpec_keep_envelope hs
    refine ⟨rfl, ⟨found, hf, by rw [sliceBytes_length] at hl; exact hl⟩, fun ho => ?_⟩
    rw [hs] at ho
    cases ho
  · simp

end Transcrypt.V3Verification

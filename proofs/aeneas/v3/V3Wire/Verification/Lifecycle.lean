import V3Wire.Verification.Protocol
import V3Wire.Verification.Filters

/-!
End-to-end lifecycle guarantees for multi-file Git operations.

The effectful adapter (`rust/crates/transcrypt-v3/src/main.rs`) iterates over
the staged protected entries and calls the verified core for every decision.
Its sequencing is modeled here by small Lean functions (`hydratePlan`,
`lockPlan`, `verifyPlan`) that call the *Aeneas-generated* core functions in
the same order as the adapter. That the Rust adapter follows these models is
assumption A4 of `docs/verification/V3-ASSUMPTIONS.md` (reviewed and tested,
not proved). Given the models, the theorems below are unconditional apart
from the primitive contract `Realizes` (A5).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

variable {P : Type} {inst : V3Primitives P} {prims : P} {σ : Suite}

/-- One staged protected entry as seen by `hydrate`: its Git path, staged
    record, current worktree bytes, and a plaintext buffer. -/
structure HydrateEntry where
  path : Slice U8
  record : Slice U8
  worktree : Slice U8
  buffer : Slice U8

/-- Per-entry hydrate step: authenticate the staged record (`open_record`),
    then let the core decide (`hydrate_action`). `some pt` = publish `pt`. -/
def hydrateEntry (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize)
    (e : HydrateEntry) : RustM (core.result.Result (Option (Slice U8)) Refusal) := do
  let (r, pt) ← open_record inst prims config e.path e.record e.buffer
  match r with
  | core.result.Result.Err x => ok (core.result.Result.Err x)
  | core.result.Result.Ok _ =>
    let a ← hydrate_action e.worktree e.record pt
    match a with
    | core.result.Result.Ok HydrateAction.Publish => ok (core.result.Result.Ok (some pt))
    | core.result.Result.Ok HydrateAction.Keep => ok (core.result.Result.Ok none)
    | core.result.Result.Err x => ok (core.result.Result.Err x)

/-- The adapter validates *every* entry before publishing anything: one
    refusal aborts the whole operation (all-or-nothing preflight). -/
def hydratePlan (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize) :
    List HydrateEntry → RustM (core.result.Result (List (Option (Slice U8))) Refusal)
  | [] => ok (core.result.Result.Ok [])
  | e :: es => do
    let r ← hydrateEntry inst prims config e
    match r with
    | core.result.Result.Err x => ok (core.result.Result.Err x)
    | core.result.Result.Ok w =>
      let rs ← hydratePlan inst prims config es
      match rs with
      | core.result.Result.Ok ws => ok (core.result.Result.Ok (w :: ws))
      | core.result.Result.Err x => ok (core.result.Result.Err x)

/-- What a successful hydrate may do to one entry: either replace a worktree
    that is *exactly* the staged record by the plaintext that record
    authentically opens to at this path, or leave a worktree that already
    *is* that authentic plaintext. Nothing else is ever overwritten. -/
def HydrateSafe (σ : Suite) (config : List Nat) (e : HydrateEntry) : Option (Slice U8) → Prop
  | some pt => sliceBytes e.worktree = sliceBytes e.record ∧
      OpensTo σ config (sliceBytes e.path) (sliceBytes e.record) (sliceBytes pt)
  | none => ∃ pt, OpensTo σ config (sliceBytes e.path) (sliceBytes e.record) pt ∧
      sliceBytes e.worktree = pt

theorem hydrateEntry_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (e : HydrateEntry) :
    hydrateEntry inst prims config e ⦃ r => match r with
      | core.result.Result.Ok w => HydrateSafe σ (wireBytes config) e w
      | core.result.Result.Err _ => True ⦄ := by
  unfold hydrateEntry
  step with open_record_spec h config e.path e.record e.buffer as ⟨ r, pt, hr ⟩
  rcases r with u | x
  · simp only at hr ⊢
    step with hydrate_action_spec as ⟨ a, ha ⟩
    unfold hydrateSpec at ha
    by_cases h1 : sliceBytes e.worktree = sliceBytes e.record
    · rw [if_pos h1] at ha
      simp only [ha, hydrateResult, WP.spec_ok]
      exact ⟨h1, hr⟩
    · rw [if_neg h1] at ha
      by_cases h2 : sliceBytes e.worktree = sliceBytes pt
      · rw [if_pos h2] at ha
        simp only [ha, hydrateResult, WP.spec_ok]
        exact ⟨sliceBytes pt, hr, h2⟩
      · rw [if_neg h2] at ha
        simp [ha, hydrateResult]
  · simp

/-- **Hydrate safety.** If hydrate's preflight succeeds, every entry's planned
    action is safe; otherwise nothing is planned (and the adapter writes
    nothing). -/
theorem hydratePlan_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (es : List HydrateEntry) :
    hydratePlan inst prims config es ⦃ r => match r with
      | core.result.Result.Ok ws => List.Forall₂ (HydrateSafe σ (wireBytes config)) es ws
      | core.result.Result.Err _ => True ⦄ := by
  induction es with
  | nil => simp [hydratePlan]
  | cons e es ih =>
    unfold hydratePlan
    step with hydrateEntry_spec h config e as ⟨ r, hr ⟩
    rcases r with w | x
    · simp only at hr ⊢
      step with ih as ⟨ rs, hrs ⟩
      rcases rs with ws | x
      · exact List.Forall₂.cons hr hrs
      · simp
    · simp

/-- One staged entry as seen by `lock`: path, staged record, worktree, and
    the buffers the agent's Encrypt operation (`cleanModel`) uses to reseal
    the worktree: `openBuf` for its `open_record` attempt and `scratch` for
    its `seal_record` output. -/
structure LockEntry where
  path : Slice U8
  record : Slice U8
  worktree : Slice U8
  openBuf : Slice U8
  scratch : Slice U8

/-- Per-entry lock step as performed across the adapter and the agent: the
    agent reseals the worktree with clean semantics (`cleanModel`: a worktree
    that already is a genuine record is returned unchanged, anything else is
    sealed), and the core decides (`lock_action`). `true` = flush (replace
    worktree by the record). -/
def lockEntry (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize)
    (e : LockEntry) : RustM (core.result.Result Bool Refusal) := do
  let k ← bytes_eq e.worktree e.record
  if k then ok (core.result.Result.Ok false)
  else
    let c ← cleanModel inst prims config e.path e.worktree e.openBuf e.scratch
    match c with
    | none => ok (core.result.Result.Err Refusal.Primitive)
    | some resealed =>
      let a ← lock_action e.worktree e.record resealed
      match a with
      | core.result.Result.Ok LockAction.Flush => ok (core.result.Result.Ok true)
      | core.result.Result.Ok LockAction.Keep => ok (core.result.Result.Ok false)
      | core.result.Result.Err x => ok (core.result.Result.Err x)

/-- **Lock never loses data.** A flushed worktree is exactly the plaintext
    the staged record authentically opens to at this path; a kept worktree
    already is the staged record. -/
theorem lockEntry_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize) (e : LockEntry) :
    lockEntry inst prims config e ⦃ r => match r with
      | core.result.Result.Ok true =>
          OpensTo σ (wireBytes config) (sliceBytes e.path) (sliceBytes e.record) (sliceBytes e.worktree)
      | core.result.Result.Ok false => sliceBytes e.worktree = sliceBytes e.record
      | core.result.Result.Err _ => True ⦄ := by
  unfold lockEntry
  step with bytes_eq_spec as ⟨ k, hk ⟩
  split
  · rename_i hkt
    simp only [WP.spec_ok, sliceBytes, hk.1 hkt]
  · step with cleanModel_spec h config e.path e.worktree e.openBuf e.scratch as ⟨ c, hc ⟩
    rcases c with _ | resealed
    · simp
    · simp only
      step with lock_action_spec as ⟨ a, ha ⟩
      unfold lockSpec at ha
      by_cases h1 : sliceBytes e.worktree = sliceBytes e.record
      · rw [if_pos h1] at ha
        simp only [ha, lockResult, WP.spec_ok]; exact h1
      · rw [if_neg h1] at ha
        by_cases h2 : sliceBytes resealed = sliceBytes e.record
        · rw [if_pos h2] at ha
          simp only [ha, lockResult, WP.spec_ok]
          rcases hc resealed rfl with ⟨heq, _⟩ | ⟨hmay, hres⟩
          · -- Pass-through: the resealed bytes are the worktree, which is
            -- not the record, so `lock_action` cannot have flushed.
            exact absurd (heq.symm.trans h2) h1
          · rw [← h2, hres]
            exact seal_opens σ hmay
        · rw [if_neg h2] at ha
          simp [ha, lockResult]

/-- `verify-index` for the staged protected entries: every staged record
    must open at its own path under the checkout's config. -/
def verifyPlan (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize) :
    List HydrateEntry → RustM Bool
  | [] => ok true
  | e :: es => do
    let (r, _) ← open_record inst prims config e.path e.record e.buffer
    match r with
    | core.result.Result.Err _ => ok false
    | core.result.Result.Ok _ => verifyPlan inst prims config es

/-- **verify-index soundness.** If the pre-commit check passes, every staged
    protected record authentically opens at exactly its own Git path under
    the authenticated config: no staged plaintext, no record transplanted
    from another path or repository, no forged record (under A10). -/
theorem verifyPlan_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (es : List HydrateEntry) :
    verifyPlan inst prims config es ⦃ b => b = true →
      ∀ e ∈ es, ∃ pt, OpensTo σ (wireBytes config) (sliceBytes e.path) (sliceBytes e.record) pt ⦄ := by
  induction es with
  | nil => simp [verifyPlan]
  | cons e es ih =>
    unfold verifyPlan
    step with open_record_spec h config e.path e.record e.buffer as ⟨ r, pt, hr ⟩
    rcases r with u | x
    · simp only at hr ⊢
      apply WP.spec_mono ih
      intro b hb hbt e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact ⟨_, hr⟩
      · exact hb hbt e' he'
    · simp

/-- **Effective filter attribute.** If the core accepts Git's `check-attr`
    response for the request built from NUL-free paths, Git reported
    `filter: transcrypt-v3` for every one of those paths, in order. -/
theorem check_attr_paths (request response : Slice U8) (paths : List (List Nat))
    (hreq : sliceBytes request = attrRequest paths) (hnul : ∀ p ∈ paths, 0 ∉ p) :
    check_attr_response_ok request response ⦃ b => b = true →
      sliceBytes response = paths.flatMap (· ++ filterAttrSuffix) ⦄ := by
  apply WP.spec_mono (check_attr_response_ok_spec request response)
  intro b hb hbt
  rw [hb.1 hbt, hreq, expectedAttrResponse_paths paths hnul]

end Transcrypt.V3Verification

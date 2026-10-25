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

Hydrate, per protected entry: the *candidate* record is the staged record if
the entry has one and the worktree is exactly it, otherwise the worktree
itself if it has the v3 record envelope for this checkout
(`record_envelope_ok`), otherwise there is none. An *unmerged* entry (during a
merge) has no staged record, so its only possible candidate is the worktree.
A candidate is authenticated at the entry's path (`open_record`) and the core
decides (`hydrate_action`); on `Publish` the worktree is replaced by the
plaintext. Without a candidate, or without `Publish`, the file is left
untouched (the adapter may re-index it; that is not modeled here); for an
entry with a staged record the adapter first decrypts that record, for an
unmerged entry it does not. Any refusal aborts the whole operation before
anything is written.
`hydratePlan_spec`: every planned write replaces a worktree that is exactly an
authentic record at its own path, by exactly the plaintext it opens to.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Transcrypt.V3Policy

namespace Transcrypt.V3Verification

open transcrypt_v3_core

variable {P : Type} {inst : V3Primitives P} {prims : P} {σ : Suite}

/-- One protected entry as seen by `hydrate`: its Git path, staged record
    (`none` for an *unmerged* path during a merge, which has no staged record
    of its own), current worktree bytes, and a plaintext buffer. -/
structure HydrateEntry where
  path : Slice U8
  record : Option (Slice U8)
  worktree : Slice U8
  buffer : Slice U8

/-- The worktree itself when it has the v3 record envelope for this checkout
    (`id` is the config id), otherwise none. -/
def hydrateEnvelope (id : Std.Array U8 16#usize) (e : HydrateEntry) :
    RustM (Option (Slice U8)) := do
  let env ← record_envelope_ok e.worktree id
  if env then ok (some e.worktree) else ok none

/-- The record a worktree file holds, if any: the staged record when the
    entry has one and the worktree is exactly it, otherwise the worktree
    itself when it has the v3 record envelope (`hydrateEnvelope`), otherwise
    none. For an unmerged entry only the envelope check applies. -/
def hydrateCandidate (id : Std.Array U8 16#usize) (e : HydrateEntry) :
    RustM (Option (Slice U8)) :=
  match e.record with
  | some r => do
    let s ← bytes_eq e.worktree r
    if s then ok (some r) else hydrateEnvelope id e
  | none => hydrateEnvelope id e

theorem hydrateEnvelope_spec (id : Std.Array U8 16#usize) (e : HydrateEntry) :
    hydrateEnvelope id e ⦃ c => ∀ cand, c = some cand → sliceBytes cand = sliceBytes e.worktree ⦄ := by
  unfold hydrateEnvelope
  step with record_envelope_ok_spec as ⟨ env, _ ⟩
  split <;> simp

/-- A candidate record is always byte-for-byte the worktree. -/
theorem hydrateCandidate_spec (id : Std.Array U8 16#usize) (e : HydrateEntry) :
    hydrateCandidate id e ⦃ c => ∀ cand, c = some cand → sliceBytes cand = sliceBytes e.worktree ⦄ := by
  unfold hydrateCandidate
  split
  · step with bytes_eq_spec as ⟨ s, hs ⟩
    split
    · rename_i hst
      simp only [WP.spec_ok, Option.some.injEq]
      rintro cand rfl
      simp only [sliceBytes, hs.1 hst]
    · exact hydrateEnvelope_spec id e
  · exact hydrateEnvelope_spec id e

/-- Authenticate a candidate record at the entry's path (`open_record`; a
    refusal aborts) and let the core decide (`hydrate_action`).
    `some pt` = replace the worktree by `pt`. -/
def hydrateOpen (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize)
    (e : HydrateEntry) (cand : Slice U8) :
    RustM (core.result.Result (Option (Slice U8)) Refusal) := do
  let (r, pt) ← open_record inst prims config e.path cand e.buffer
  match r with
  | core.result.Result.Err x => ok (core.result.Result.Err x)
  | core.result.Result.Ok _ =>
    let a ← hydrate_action e.worktree cand pt
    match a with
    | core.result.Result.Ok HydrateAction.Publish => ok (core.result.Result.Ok (some pt))
    | _ => ok (core.result.Result.Ok none)

/-- Per-entry hydrate step. If the worktree holds a candidate record, it is
    authenticated and the core decides (`hydrateOpen`). Otherwise (or if the
    core does not publish) the file is left untouched; for an entry with a
    staged record the adapter still decrypts that record, and a refusal there
    also aborts. An unmerged entry (no staged record) is simply kept. -/
def hydrateEntry (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) (e : HydrateEntry) :
    RustM (core.result.Result (Option (Slice U8)) Refusal) := do
  let c ← hydrateCandidate id e
  let published ← match c with
    | Option.none => ok (core.result.Result.Ok Option.none)
    | Option.some cand => hydrateOpen inst prims config e cand
  match published with
  | core.result.Result.Err x => ok (core.result.Result.Err x)
  | core.result.Result.Ok (Option.some pt) => ok (core.result.Result.Ok (some pt))
  | core.result.Result.Ok Option.none =>
    match e.record with
    | Option.none => ok (core.result.Result.Ok none)
    | Option.some record =>
      let (r, _) ← open_record inst prims config e.path record e.buffer
      match r with
      | core.result.Result.Err x => ok (core.result.Result.Err x)
      | core.result.Result.Ok _ => ok (core.result.Result.Ok none)

/-- The adapter validates *every* entry before publishing anything: one
    refusal aborts the whole operation (all-or-nothing preflight). -/
def hydratePlan (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) :
    List HydrateEntry → RustM (core.result.Result (List (Option (Slice U8))) Refusal)
  | [] => ok (core.result.Result.Ok [])
  | e :: es => do
    let r ← hydrateEntry inst prims config id e
    match r with
    | core.result.Result.Err x => ok (core.result.Result.Err x)
    | core.result.Result.Ok w =>
      let rs ← hydratePlan inst prims config id es
      match rs with
      | core.result.Result.Ok ws => ok (core.result.Result.Ok (w :: ws))
      | core.result.Result.Err x => ok (core.result.Result.Err x)

/-- What a successful hydrate may do to one entry: replace a worktree that is
    *exactly* an authentic record at this path by the plaintext it opens to
    (unique by `opensTo_unique`), or write nothing. -/
def HydrateSafe (σ : Suite) (config : List Nat) (e : HydrateEntry) : Option (Slice U8) → Prop
  | some pt => OpensTo σ config (sliceBytes e.path) (sliceBytes e.worktree) (sliceBytes pt)
  | none => True

/-- A published plaintext is exactly what the worktree authentically opens
    to at this path: `hydrate_action` publishes only when the worktree *is*
    the candidate record. -/
theorem hydrateOpen_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (e : HydrateEntry) (cand : Slice U8) :
    hydrateOpen inst prims config e cand ⦃ p => ∀ pt,
      p = core.result.Result.Ok (some pt) →
        sliceBytes e.worktree = sliceBytes cand ∧
        OpensTo σ (wireBytes config) (sliceBytes e.path) (sliceBytes e.worktree) (sliceBytes pt) ⦄ := by
  unfold hydrateOpen
  step with open_record_spec h config e.path cand e.buffer as ⟨ r, pt, hr ⟩
  rcases r with u | x
  · simp only at hr ⊢
    step with hydrate_action_spec as ⟨ a, ha ⟩
    unfold hydrateSpec at ha
    by_cases h1 : sliceBytes e.worktree = sliceBytes cand
    · rw [if_pos h1] at ha
      simp only [ha, hydrateResult, WP.spec_ok, core.result.Result.Ok.injEq, Option.some.injEq]
      rintro _ rfl
      exact ⟨h1, h1 ▸ hr⟩
    · rw [if_neg h1] at ha
      split at ha <;> simp [ha, hydrateResult]
  · simp

theorem hydrateEntry_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) (e : HydrateEntry) :
    hydrateEntry inst prims config id e ⦃ r => match r with
      | core.result.Result.Ok w => HydrateSafe σ (wireBytes config) e w
      | core.result.Result.Err _ => True ⦄ := by
  unfold hydrateEntry
  step with hydrateCandidate_spec id e as ⟨ c, _ ⟩
  have hpub : (match c with
      | Option.none => (ok (core.result.Result.Ok Option.none) :
          RustM (core.result.Result (Option (Slice U8)) Refusal))
      | Option.some cand => hydrateOpen inst prims config e cand) ⦃ p => ∀ pt,
        p = core.result.Result.Ok (some pt) →
          OpensTo σ (wireBytes config) (sliceBytes e.path) (sliceBytes e.worktree) (sliceBytes pt) ⦄ := by
    rcases c with _ | cand
    · simp
    · apply WP.spec_mono (hydrateOpen_spec h config e cand)
      intro p hp pt hpt
      exact (hp pt hpt).2
  step with hpub as ⟨ p, hp ⟩
  rcases p with (_ | pt) | x
  · simp only
    split
    · simp [HydrateSafe]
    · rename_i record _
      step with open_record_spec h config e.path record e.buffer as ⟨ r, _, _ ⟩
      rcases r with u | x <;> simp [HydrateSafe]
  · simp only [WP.spec_ok, HydrateSafe]
    exact hp pt rfl
  · simp

/-- **Hydrate safety.** If hydrate's preflight succeeds, every planned write
    replaces a worktree that is exactly an authentic record at its own path
    with exactly the plaintext that record opens to; all other files are left
    untouched. This covers unmerged entries (no staged record) too: one is
    replaced only if its worktree itself is an authentic record at its path. Any refusal aborts the whole operation, so nothing is planned
    (and the adapter writes nothing). -/
theorem hydratePlan_spec (h : Realizes inst prims σ) (config : Std.Array U8 55#usize)
    (id : Std.Array U8 16#usize) (es : List HydrateEntry) :
    hydratePlan inst prims config id es ⦃ r => match r with
      | core.result.Result.Ok ws => List.Forall₂ (HydrateSafe σ (wireBytes config)) es ws
      | core.result.Result.Err _ => True ⦄ := by
  induction es with
  | nil => simp [hydratePlan]
  | cons e es ih =>
    unfold hydratePlan
    step with hydrateEntry_spec h config id e as ⟨ r, hr ⟩
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

/-- One staged protected entry as seen by `verify-index`: its Git path,
    staged record, and a plaintext buffer. -/
structure VerifyEntry where
  path : Slice U8
  record : Slice U8
  buffer : Slice U8

/-- `verify-index` for the staged protected entries: every staged record
    must open at its own path under the checkout's config. -/
def verifyPlan (inst : V3Primitives P) (prims : P) (config : Std.Array U8 55#usize) :
    List VerifyEntry → RustM Bool
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
    (es : List VerifyEntry) :
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

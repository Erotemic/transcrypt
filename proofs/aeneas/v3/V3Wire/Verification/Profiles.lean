import V3Wire.Verification.Protocol

/-!
Refinement of the production profile dispatch (`profile_kdf`,
`passphrase_ok`, `derive_profile_key`, `derive_config_key`) to the
independent profile specification `Transcrypt.V3Policy` (`profileKdf`,
`passphraseOk`, `profileKey`, `configKey`).

The adapter derives every key through `derive_profile_key` (a new
configuration: `init`, `rekey`, `migrate`) or `derive_config_key` (an
existing one: `unlock`). Key derivation itself is the adapter's `V3Kdf`
implementation, trusted to compute the function it is asked for
(`KdfRealizes`, assumption A26); *which* function and parameters it is asked
for is decided by the verified code below, from the committed configuration
alone. So no configuration can make a passphrase run under another
profile's derivation, a weaker parameter set, or none.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core
open Transcrypt.V3Policy (KeyDerivation passphraseOk profileKdf profileKey configKey)

/-- A production key-derivation description, in the specification. -/
def kdfSpec : transcrypt_v3_core.Kdf → Transcrypt.V3Policy.Kdf
  | .Argon2id m t p => .argon2id m.val t.val p.val
  | .Scrypt n r p => .scrypt n.val r.val p.val
  | .Pbkdf2Sha256 k => .pbkdf2Sha256 k.val

/-- The production profile table is the specification's: each profile gets
    exactly its function and parameters. -/
@[step]
theorem profile_kdf_spec (p : Profile) :
    profile_kdf p ⦃ k => kdfSpec k = profileKdf (profileSpec p) ⦄ := by
  unfold profile_kdf
  rcases p with _ | _ | _ <;>
    simp [kdfSpec, profileKdf, profileSpec, ARGON2ID_MEMORY_KIB, ARGON2ID_PASSES, ARGON2ID_LANES,
      SCRYPT_LOG_N, SCRYPT_R, SCRYPT_P, PBKDF2_ROUNDS]

/-- No NUL byte up to `n` in `l` exactly when `l` does not contain 0. -/
theorem not_contains_zero_iff (l : List Nat) :
    (∀ k, k < l.length → l[k]! ≠ 0) ↔ l.contains 0 = false := by
  constructor
  · intro h
    rw [Bool.eq_false_iff]
    intro hc
    rw [List.contains_iff_mem] at hc
    obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hc
    exact h k hk (by rw [getElem!_pos l k hk]; exact hkv)
  · intro h k hk hz
    rw [getElem!_pos l k hk] at hz
    have : l.contains 0 = true := List.contains_iff_mem.2 (hz ▸ List.getElem_mem hk)
    rw [h] at this
    cases this

/-- The production passphrase rule is the specification's. -/
@[step]
theorem passphrase_ok_spec (p : Profile) (pw : Slice U8) :
    passphrase_ok p pw ⦃ b => b = passphraseOk (profileSpec p) (sliceBytes pw) ⦄ := by
  unfold passphrase_ok
  simp_len [bind_tc_ok]
  have hl : (sliceBytes pw).length = pw.length := sliceBytes_length pw
  have hvl : pw.val.length = pw.length := rfl
  have hM := MAX_PASSPHRASE_val
  split
  · rename_i h0
    have : pw.length = 0 := by simpa using congrArg UScalar.val h0
    simp [passphraseOk, hl, this]
  · rename_i h0
    have hpos : 0 < pw.length := by
      have : pw.len.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by simpa using h))
      simpa using Nat.pos_of_ne_zero this
    split
    · rename_i hgt
      have : Transcrypt.V3Policy.maxPassphrase < pw.length := by
        have := hgt; simp only [GT.gt, UScalar.lt_equiv] at this; simpa [hM] using this
      simp only [WP.spec_ok]
      simp [passphraseOk, hl, hpos]; omega
    · rename_i hle
      have hle' : pw.length ≤ Transcrypt.V3Policy.maxPassphrase := by
        have := hle; simp only [GT.gt, UScalar.lt_equiv, not_lt] at this; simpa [hM] using this
      rcases p with _ | _ | _
      · dsimp only
        simp only [WP.spec_ok]
        simp [passphraseOk, profileSpec, hl, hpos, hle']
      all_goals
        dsimp only
        step with find_byte_spec as ⟨ i, hscan, hat ⟩
        have hzero := not_contains_zero_iff (sliceBytes pw)
        simp only [passphraseOk, profileSpec, hl, hpos, hle', decide_true, Bool.true_and]
        obtain ⟨_, hi, hne⟩ := hscan
        by_cases heq : i.val = pw.length
        · have hiu : i = pw.len := UScalar.eq_of_val_eq (by simpa using heq)
          rw [decide_eq_true hiu]
          have : (sliceBytes pw).contains 0 = false :=
            hzero.1 (fun k hk => hne k (Nat.zero_le _) (by rw [heq]; rw [hl] at hk; exact hk))
          simpa using this
        · have hlt : i.val < pw.length := by rw [hl] at hi; rcases hi with hi | hi <;> omega
          have hiu : ¬ i = pw.len := fun h => heq (by rw [h]; simp)
          rw [decide_eq_false hiu]
          have hz := hat hlt
          have : (sliceBytes pw).contains 0 = true := by
            cases hc : (sliceBytes pw).contains 0
            · exact absurd hz (hzero.2 hc i.val (by rw [hl]; exact hlt))
            · rfl
          simpa using this

/-- The trusted key-derivation boundary (assumption A26): when the adapter's
    `V3Kdf` reports success, it wrote exactly the key the named function
    gives for the passphrase and salt. It may fail; it never claims a
    success it did not compute. -/
structure KdfRealizes {K : Type} (inst : V3Kdf K) (kdf : K) (D : KeyDerivation) : Prop where
  derive : ∀ k pw salt key, WP.spec (inst.derive kdf k pw salt key) (fun r =>
    r.1 = true → wireBytes r.2 = D.derive (kdfSpec k) (sliceBytes pw) (wireBytes salt))

variable {K : Type} {inst : V3Kdf K} {kdf : K} {D : KeyDerivation}

/-- `derive_profile_key` derives exactly the profile's key, or refuses: a
    passphrase the profile refuses reaches no derivation, and a failed
    derivation is an error, never a fallback. -/
@[step]
theorem derive_profile_key_spec (h : KdfRealizes inst kdf D) (p : Profile) (pw : Slice U8)
    (salt : Std.Array U8 32#usize) (key : Std.Array U8 64#usize) :
    derive_profile_key inst kdf p pw salt key ⦃ r => match r.1 with
      | core.result.Result.Ok _ => passphraseOk (profileSpec p) (sliceBytes pw) = true ∧
          wireBytes r.2 = profileKey D (profileSpec p) (sliceBytes pw) (wireBytes salt)
      | core.result.Result.Err Refusal.Passphrase =>
          passphraseOk (profileSpec p) (sliceBytes pw) = false ∧ r.2 = key
      | core.result.Result.Err Refusal.Primitive => passphraseOk (profileSpec p) (sliceBytes pw) = true
      | core.result.Result.Err _ => False ⦄ := by
  unfold derive_profile_key
  step with passphrase_ok_spec as ⟨ b, hb ⟩
  split
  · rename_i hbt
    step with profile_kdf_spec as ⟨ k, hk ⟩
    step with h.derive k pw salt key as ⟨ b1, key1, hres ⟩
    split
    · rename_i hb1
      simp only [WP.spec_ok]
      refine ⟨by rw [← hb, hbt], ?_⟩
      rw [hres hb1, hk]; rfl
    · simp only [WP.spec_ok]
      rw [← hb, hbt]
  · rename_i hbf
    simp only [WP.spec_ok]
    exact ⟨by rw [← hb]; simpa using hbf, by trivial⟩

/-- `derive_config_key` is the specification's `configKey`: the derivation
    is decided by the configuration's own profile byte and salt. A
    configuration that does not decode (in particular one of an unknown
    profile) is refused before any derivation. -/
@[step]
theorem derive_config_key_spec (h : KdfRealizes inst kdf D) (config : Std.Array U8 55#usize)
    (pw : Slice U8) (key : Std.Array U8 64#usize) :
    derive_config_key inst kdf config pw key ⦃ r => match r.1 with
      | core.result.Result.Ok p =>
          configKey D (wireBytes config) (sliceBytes pw) = some (profileSpec p, wireBytes r.2)
      | core.result.Result.Err Refusal.Config =>
          Transcrypt.V3Wire.decodeConfigShape (wireBytes config) = none ∧ r.2 = key
      | core.result.Result.Err Refusal.Passphrase => configKey D (wireBytes config) (sliceBytes pw) = none
      | core.result.Result.Err Refusal.Primitive =>
          ∃ p salt tag, Transcrypt.V3Wire.decodeConfigShape (wireBytes config) = some (p, salt, tag) ∧
            passphraseOk p (sliceBytes pw) = true
      | core.result.Result.Err _ => False ⦄ := by
  unfold derive_config_key
  step with decode_config_exact_spec as ⟨ r, hr ⟩
  rcases r with c | e
  · simp only at hr ⊢
    have hshape := config_shape_of_eq c.profile c.salt c.tag hr
    have hw : config.val.map (fun b => b.val) = wireBytes config := rfl
    rw [hw] at hshape
    step with derive_profile_key_spec h c.profile pw c.salt key as ⟨ r1, key1, hres ⟩
    rcases r1 with _ | refusal
    · simp only [WP.spec_ok]
      obtain ⟨hok, hkey⟩ := hres
      simp only [configKey, hshape, hok, if_true, hkey]
    · simp only [WP.spec_ok]
      cases refusal <;> simp only at hres ⊢
      · exact ⟨_, _, _, hshape, hres⟩
      · simp only [configKey, hshape, hres.1]; rfl
  · simp only [WP.spec_ok]
    have hw : config.val.map (fun b => b.val) = wireBytes config := rfl
    refine ⟨?_, by trivial⟩
    cases e
    · exact hr.elim
    · rw [← hw]; exact config_shape_none_of_take hr
    · rw [← hw]; exact config_shape_none_of_profile hr (by unfold_v3_bytes; simp)

/-- **Profile dispatch.** When `derive_config_key` succeeds, the committed
    configuration is the encoding of the returned profile with some salt,
    and the key is that profile's own function (`profileKdf`, with its
    fixed parameters) of the passphrase and *that* salt. No other function,
    parameter set or salt is ever used for a configuration. -/
theorem derive_config_key_uses_config_profile (h : KdfRealizes inst kdf D)
    (config : Std.Array U8 55#usize) (pw : Slice U8) (key : Std.Array U8 64#usize) :
    derive_config_key inst kdf config pw key ⦃ r => ∀ p, r.1 = core.result.Result.Ok p →
      ∃ salt tag, wireBytes config = Transcrypt.V3Wire.encodeConfig (profileSpec p) salt tag ∧
        wireBytes r.2 = D.derive (profileKdf (profileSpec p)) (sliceBytes pw) salt ∧
        passphraseOk (profileSpec p) (sliceBytes pw) = true ⦄ := by
  apply WP.spec_mono (derive_config_key_spec h config pw key)
  intro r hr p hp
  rw [hp] at hr
  obtain ⟨salt, tag, he, _, hk, hok⟩ := Transcrypt.V3Policy.configKey_uses_its_profile hr
  exact ⟨salt, tag, he, hk, hok⟩

/-! ## Binding and determinism of the production records -/

section Binding

variable {P : Type} {inst : V3Primitives P} {prims : P} {σ : Transcrypt.V3Policy.Suite}

/-- **Path and configuration binding.** If the production `open_record`
    accepts, at `path'` under `config'`, a record that the production
    `seal_record` produced for `path` under `config`, with either one
    different, the key's AES-SIV collides on two different associated-data
    lists (`SivCollision`), which A10 rules out except with negligible
    probability. This covers records moved between paths, repositories and
    profiles (configurations of different profiles differ). -/
theorem open_record_of_other_context_needs_collision (h : Realizes inst prims σ)
    {sealedOut : Slice U8} {config config' : Std.Array U8 55#usize} {path path' plaintext : Slice U8}
    (hseal : Transcrypt.V3Policy.MaySeal σ (wireBytes config) (sliceBytes path) (sliceBytes plaintext) ∧
      sliceBytes sealedOut = Transcrypt.V3Policy.sealedRecord σ (wireBytes config) (sliceBytes path) (sliceBytes plaintext))
    (hdiff : wireBytes config ≠ wireBytes config' ∨ sliceBytes path ≠ sliceBytes path')
    (out : Slice U8) :
    open_record inst prims config' path' sealedOut out ⦃ r =>
      (∃ x, r.1 = core.result.Result.Ok x) → Transcrypt.V3Policy.SivCollision σ ⦄ := by
  apply WP.spec_mono (open_record_spec h config' path' sealedOut out)
  intro r hr hok
  obtain ⟨x, hx⟩ := hok
  rw [hx] at hr
  rw [hseal.2] at hr
  exact Transcrypt.V3Policy.transplant_needs_siv_collision σ hr hdiff

/-- **Determinism.** Two successful production seals at one path under one
    configuration produce the same record exactly when the plaintexts are
    equal: re-encrypting unchanged content changes nothing in Git, and
    equality of plaintexts at the same path is what records reveal. -/
theorem seal_record_deterministic {config : Std.Array U8 55#usize} {path p1 p2 o1 o2 : Slice U8}
    (h1 : sliceBytes o1 = Transcrypt.V3Policy.sealedRecord σ (wireBytes config) (sliceBytes path) (sliceBytes p1))
    (h2 : sliceBytes o2 = Transcrypt.V3Policy.sealedRecord σ (wireBytes config) (sliceBytes path) (sliceBytes p2)) :
    sliceBytes o1 = sliceBytes o2 ↔ sliceBytes p1 = sliceBytes p2 := by
  rw [h1, h2]
  exact Transcrypt.V3Policy.sealedRecord_eq_iff_same_context σ _ _ _ _

end Binding

end Transcrypt.V3Verification

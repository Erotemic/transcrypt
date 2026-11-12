import Transcrypt.V3Policy.Authentication

/-!
# Binding and determinism of records

What the record construction itself guarantees, for every profile (records
do not depend on the profile except through the configuration bytes, which
the associated data contains in full):

* **Determinism, exactly characterized.** A record is a function of the
  configuration, the path and the plaintext (`sealedRecord`); for one
  configuration and path, two records are equal exactly when their
  plaintexts are (`sealedRecord_eq_iff_same_context`). This is the whole
  of what deterministic encryption lets an observer of public Git compare
  *by equality*; whether the ciphertext reveals more is the computational
  assumption A10 (AES-SIV is a deterministic authenticated encryption),
  not a theorem here.
* **Binding.** A record sealed for one (configuration, path) that opens at
  another configuration or path gives two different associated-data lists
  with one AES-SIV output (`transplant_needs_siv_collision`): moving a
  record to another path, another repository or another profile requires
  forging AES-SIV.
-/

namespace Transcrypt.V3Policy

open Transcrypt.V3Wire

/-- Two distinct associated-data lists with the same AES-SIV output: what
    the AES-SIV assumption (A10) says an adversary without the key cannot
    produce, except with negligible probability. -/
def SivCollision (s : Suite) : Prop :=
  ∃ ad ad' pt pt', ad ≠ ad' ∧ s.siv ad pt = s.siv ad' pt'

/-- For one configuration and path, equal records means equal plaintexts,
    and conversely: determinism leaks exactly plaintext equality at the
    same path under the same configuration. -/
theorem sealedRecord_eq_iff_same_context (s : Suite) (config path pt pt' : List Nat) :
    sealedRecord s config path pt = sealedRecord s config path pt' ↔ pt = pt' := by
  constructor
  · intro h
    simp only [sealedRecord, encodeFile, List.append_assoc, List.append_cancel_left_eq] at h
    exact s.siv_injective _ _ _ h
  · rintro rfl; rfl

/-- Re-encrypting unchanged content gives the identical record: Git sees no
    change, and two clients that agree on the bytes agree on the object. -/
theorem sealedRecord_deterministic (s : Suite) {config path pt : List Nat} :
    sealedRecord s config path pt = sealedRecord s config path pt := rfl

/-- A record that was sealed for `(config, path)` and opens at
    `(config', path')`, with either one different, makes the key's AES-SIV
    collide on two different associated-data lists. -/
theorem transplant_needs_siv_collision (s : Suite) {config path pt config' path' pt' : List Nat}
    (hopen : OpensTo s config' path' (sealedRecord s config path pt) pt')
    (hdiff : config ≠ config' ∨ path ≠ path') :
    SivCollision s := by
  obtain ⟨-, -, -, h⟩ := hopen
  have hsiv : s.siv [fileDomain, config, path] pt = s.siv [fileDomain, config', path'] pt' := by
    have hid : (s.digest16 config).length = (s.digest16 config').length := by
      rw [s.digest16_length, s.digest16_length]
    simp only [sealedRecord, encodeFile, List.append_assoc] at h
    have h2 := List.append_cancel_left h
    exact (List.append_inj h2 hid).2
  refine ⟨[fileDomain, config, path], [fileDomain, config', path'], pt, pt', ?_, hsiv⟩
  intro hl
  simp only [List.cons.injEq, and_true] at hl
  rcases hdiff with hc | hp
  · exact hc hl.2.1
  · exact hp hl.2.2

/-- A record of one configuration never opens under another configuration
    whose identifier differs, whatever the key: the header names the
    configuration, and `OpensTo` requires the header of the configuration
    it opens under. Together with `transplant_needs_siv_collision` this
    covers records moved between profiles, since configurations of
    different profiles differ in their profile byte. -/
theorem other_config_needs_same_id_or_collision (s : Suite) {config path pt config' path' pt' : List Nat}
    (hopen : OpensTo s config' path' (sealedRecord s config path pt) pt')
    (hne : config ≠ config') :
    s.digest16 config = s.digest16 config' ∧ SivCollision s := by
  refine ⟨?_, transplant_needs_siv_collision s hopen (Or.inl hne)⟩
  obtain ⟨-, -, -, h⟩ := hopen
  simp only [sealedRecord, encodeFile, List.append_assoc] at h
  have h2 := List.append_cancel_left h
  have hid : (s.digest16 config).length = (s.digest16 config').length := by
    rw [s.digest16_length, s.digest16_length]
  exact (List.append_inj h2 hid).1

end Transcrypt.V3Policy

import V3Wire.Extraction
import Transcrypt.V3WireCodec

/-!
First source-derived v3 refinement obligations. These theorems refer to the
actual Charon/Aeneas output committed in `V3Wire.Extraction.Funs`, not a
manually reconstructed Rust model. They establish exact agreement of the
on-wire version discriminants with the independent specification.

The *complete* codec refinement (all 32-byte salts, 16-byte tags and IDs,
correct failure behavior, and the public slice boundary) remains to prove.
Neither these theorems nor byte-shape parsing establish AES-SIV authenticity.
-/

namespace Transcrypt.V3Verification

/-- Project Aeneas's fixed array of bitvector-backed bytes into the
    independent wire specification's natural-number byte representation. -/
def wireBytes {n : Aeneas.Std.Usize}
    (xs : Aeneas.Std.Array Aeneas.Std.U8 n) : List Nat :=
  xs.val.map (fun byte => byte.val)

/-- The actual translated Rust config magic agrees with the independent spec. -/
theorem extracted_config_magic_matches_spec :
    wireBytes transcrypt_v3_core.CONFIG_MAGIC = Transcrypt.V3Wire.configMagic := by
  unfold wireBytes transcrypt_v3_core.CONFIG_MAGIC Transcrypt.V3Wire.configMagic
  decide

/-- The actual translated Rust file magic agrees with the independent spec. -/
theorem extracted_file_magic_matches_spec :
    wireBytes transcrypt_v3_core.FILE_MAGIC = Transcrypt.V3Wire.fileMagic := by
  unfold wireBytes transcrypt_v3_core.FILE_MAGIC Transcrypt.V3Wire.fileMagic
  decide

/-- The two production wire families cannot have the same version marker. -/
theorem extracted_magic_disjoint :
    wireBytes transcrypt_v3_core.CONFIG_MAGIC ≠
      wireBytes transcrypt_v3_core.FILE_MAGIC := by
  rw [extracted_config_magic_matches_spec, extracted_file_magic_matches_spec]
  exact Transcrypt.V3Wire.magic_disjoint

end Transcrypt.V3Verification

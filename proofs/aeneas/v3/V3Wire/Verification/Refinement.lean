import V3Wire.Verification.Basic
import Transcrypt.V3Policy

/-!
The production constants of `transcrypt_v3_core`, as committed in the
Aeneas output `V3Wire.Extraction.Funs`, agree with the independent
specification. This is the one place for constant facts, named

* `X_val` (`@[simp]`) for a numeric constant `X`,
* `X_length` (`@[simp]`) for the length of a byte-array constant,
* `X_bytes` for its bytes as the specification's `List Nat`
  (`sliceBytes (Array.to_slice X) = …`),
* `X_spec` (`@[step]`) for a constant the extraction computes in `RustM`.

The two version markers (`extracted_*_magic_matches_spec`) are stated with
`wireBytes`. None of these facts establishes AES-SIV authenticity.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

namespace Transcrypt.V3Verification

open transcrypt_v3_core

/-! ## Version markers -/

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

/-! ## Numeric constants -/

@[simp] theorem ID_LEN_val : ID_LEN.val = 16 := by simp [ID_LEN]
@[simp] theorem SALT_LEN_val : SALT_LEN.val = 32 := by simp [SALT_LEN]
@[simp] theorem TAG_LEN_val : TAG_LEN.val = 16 := by simp [TAG_LEN]
@[simp] theorem CONFIG_PREFIX_LEN_val : CONFIG_PREFIX_LEN.val = 39 := by simp [CONFIG_PREFIX_LEN]
@[simp] theorem CONFIG_LEN_val : CONFIG_LEN.val = 55 := by simp [CONFIG_LEN]
@[simp] theorem FILE_HEADER_LEN_val : FILE_HEADER_LEN.val = 22 := by simp [FILE_HEADER_LEN]
@[simp] theorem MAX_PATH_val : MAX_PATH.val = Transcrypt.V3Policy.maxPath := by
  simp [MAX_PATH, Transcrypt.V3Policy.maxPath]
@[simp] theorem MAX_PKT_LEN_val : MAX_PKT_LEN.val = Transcrypt.V3Policy.maxPktLen := by
  simp [MAX_PKT_LEN, Transcrypt.V3Policy.maxPktLen]
@[simp] theorem KEY_LEN_val : KEY_LEN.val = 64 := by simp [KEY_LEN]
@[simp] theorem KEY_FILE_LEN_val : KEY_FILE_LEN.val = 119 := by simp [KEY_FILE_LEN]

@[step] theorem MAX_FILE_spec : MAX_FILE ⦃ x => x.val = Transcrypt.V3Policy.maxFile ⦄ := by
  unfold MAX_FILE; step*; simp [Transcrypt.V3Policy.maxFile, *]

@[step] theorem FILE_MIN_LEN_spec : FILE_MIN_LEN ⦃ x => x.val = 38 ⦄ := by
  unfold FILE_MIN_LEN
  step*
  · have := usize_max_ge; simp only [FILE_HEADER_LEN_val, TAG_LEN_val]; omega
  · simp [*]

@[step] theorem MAX_RECORD_spec : MAX_RECORD ⦃ x => x.val = Transcrypt.V3Policy.maxRecord ⦄ := by
  unfold MAX_RECORD
  step*
  · have := usize_max_ge; simp [Transcrypt.V3Policy.maxFile] at *; omega
  · simp [Transcrypt.V3Policy.maxRecord, *]; rfl

/-! The `_val` facts state the numbers, which `omega` and `scalar_tac`
compute with; these name the specification's length each one is. -/

theorem ID_LEN_matches_spec : ID_LEN.val = Transcrypt.V3Wire.idLen := ID_LEN_val
theorem SALT_LEN_matches_spec : SALT_LEN.val = Transcrypt.V3Wire.saltLen := SALT_LEN_val
theorem TAG_LEN_matches_spec : TAG_LEN.val = Transcrypt.V3Wire.tagLen := TAG_LEN_val
theorem CONFIG_PREFIX_LEN_matches_spec :
    CONFIG_PREFIX_LEN.val = Transcrypt.V3Wire.configMagicLen + Transcrypt.V3Wire.saltLen :=
  CONFIG_PREFIX_LEN_val
theorem CONFIG_LEN_matches_spec : CONFIG_LEN.val = Transcrypt.V3Wire.configLen := CONFIG_LEN_val
theorem FILE_HEADER_LEN_matches_spec : FILE_HEADER_LEN.val = Transcrypt.V3Wire.fileHeaderLen :=
  FILE_HEADER_LEN_val

/-! ## Byte-array constants -/

@[simp] theorem FILE_MAGIC_length : FILE_MAGIC.length = 6 := by simp
@[simp] theorem CONFIG_MAGIC_length : CONFIG_MAGIC.length = 7 := by simp
theorem FILE_MAGIC_length_matches_spec : FILE_MAGIC.length = Transcrypt.V3Wire.fileMagicLen :=
  FILE_MAGIC_length
theorem CONFIG_MAGIC_length_matches_spec : CONFIG_MAGIC.length = Transcrypt.V3Wire.configMagicLen :=
  CONFIG_MAGIC_length

theorem METADATA_DIR_bytes :
    sliceBytes (Array.to_slice METADATA_DIR) = Transcrypt.V3Policy.metadataDir := by
  unfold METADATA_DIR Transcrypt.V3Policy.metadataDir Transcrypt.V3Policy.ascii sliceBytes
  decide

theorem ATTRIBUTES_NAME_bytes :
    sliceBytes (Array.to_slice ATTRIBUTES_NAME) = Transcrypt.V3Policy.attributesName := by
  unfold ATTRIBUTES_NAME Transcrypt.V3Policy.attributesName Transcrypt.V3Policy.ascii sliceBytes
  decide

theorem ATTRIBUTES_SUFFIX_bytes :
    sliceBytes (Array.to_slice ATTRIBUTES_SUFFIX) =
      Transcrypt.V3Policy.slash :: Transcrypt.V3Policy.attributesName := by
  unfold ATTRIBUTES_SUFFIX Transcrypt.V3Policy.attributesName Transcrypt.V3Policy.slash
    Transcrypt.V3Policy.ascii sliceBytes
  decide

theorem MODULES_NAME_bytes :
    sliceBytes (Array.to_slice MODULES_NAME) = Transcrypt.V3Policy.modulesName := by
  unfold MODULES_NAME Transcrypt.V3Policy.modulesName Transcrypt.V3Policy.ascii sliceBytes
  decide

theorem FILTER_ATTR_bytes :
    sliceBytes (Array.to_slice FILTER_ATTR) = Transcrypt.V3Policy.filterAttr := by
  unfold FILTER_ATTR Transcrypt.V3Policy.filterAttr Transcrypt.V3Policy.ascii sliceBytes
  decide

theorem FILTER_DRIVER_bytes :
    sliceBytes (Array.to_slice FILTER_DRIVER) = Transcrypt.V3Policy.filterDriver := by
  unfold FILTER_DRIVER Transcrypt.V3Policy.filterDriver Transcrypt.V3Policy.ascii sliceBytes
  decide

theorem REGULAR_MODE_bytes :
    sliceBytes (Array.to_slice REGULAR_MODE) = Transcrypt.V3Policy.regularMode := by
  unfold REGULAR_MODE Transcrypt.V3Policy.regularMode Transcrypt.V3Policy.ascii sliceBytes
  decide

theorem EXECUTABLE_MODE_bytes :
    sliceBytes (Array.to_slice EXECUTABLE_MODE) = Transcrypt.V3Policy.executableMode := by
  unfold EXECUTABLE_MODE Transcrypt.V3Policy.executableMode Transcrypt.V3Policy.ascii sliceBytes
  decide

theorem BLOB_FIELD_bytes :
    sliceBytes (Array.to_slice BLOB_FIELD) = Transcrypt.V3Policy.blobField := by
  unfold BLOB_FIELD Transcrypt.V3Policy.blobField Transcrypt.V3Policy.ascii sliceBytes
  decide

/-- `SP 0 TAB`, which ends the object id of an index record. -/
theorem OID_END_bytes : sliceBytes (Array.to_slice OID_END) = [32, 48, 9] := by
  unfold OID_END sliceBytes
  decide

end Transcrypt.V3Verification

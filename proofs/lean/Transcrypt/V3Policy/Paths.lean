import Transcrypt.V3Policy.Constants

/-!
# Protected paths and their selection

Which byte strings may be authenticated as a protected path
(`CanonicalProtectedPath`), and how Git's `filter` attribute selects the
protected ones (`Selected`, `AttrRecordAt`, `attrResponse`).
-/

namespace Transcrypt.V3Policy

open Transcrypt.V3Wire

/-- The Git attribute selecting protected files, and the value that does. -/
def filterAttr : List Nat := ascii "filter"
def filterDriver : List Nat := ascii "transcrypt-v3"
def metadataDir : List Nat := ascii ".transcrypt/"
def attributesName : List Nat := ascii ".gitattributes"
def modulesName : List Nat := ascii ".gitmodules"
/-- The committed public configuration. -/
def configPath : List Nat := ascii ".transcrypt/config"

/-! ## Path policy -/

/-- Repository metadata that must stay readable without the key, whatever
    the attributes select: the committed configuration directory, every
    `.gitattributes` (Git reads it to decide what is protected) and the
    top-level `.gitmodules`. -/
def Reserved (path : List Nat) : Prop :=
  metadataDir <+: path ∨ path = attributesName ∨ (slash :: attributesName) <:+ path ∨
    path = modulesName

/-- An attribute file: the top-level `.gitattributes`, or one in any
    subdirectory. -/
def AttributesPath (path : List Nat) : Prop :=
  path = attributesName ∨ (slash :: attributesName) <:+ path

instance (path : List Nat) : Decidable (AttributesPath path) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Committed protection policy: an attribute file (which paths are
    protected) or the public configuration (under which key). -/
def PolicyPath (path : List Nat) : Prop := AttributesPath path ∨ path = configPath

instance (path : List Nat) : Decidable (PolicyPath path) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Every attribute file is reserved metadata. -/
theorem AttributesPath.reserved {path : List Nat} (h : AttributesPath path) : Reserved path := by
  unfold Reserved; rcases h with h | h <;> simp [h]

/-- So is every policy path: it is never a protected file. -/
theorem PolicyPath.reserved {path : List Nat} (h : PolicyPath path) : Reserved path := by
  rcases h with h | rfl
  · exact h.reserved
  · exact Or.inl ⟨ascii "config", by decide⟩

/-- A component is acceptable iff nonempty and neither `.` nor `..`. -/
def ComponentOk (c : List Nat) : Prop := c ≠ [] ∧ c ≠ [dot] ∧ c ≠ [dot, dot]

/-- The canonical authenticated-path policy of the v3 spec: nonempty, at most
    4096 bytes, no NUL, every `/`-separated component acceptable (which
    excludes absolute paths and empty, `.` and `..` components), and not
    reserved. *Which* of these paths are protected is the user's choice,
    expressed in Git attributes (below), not a property of the name. -/
def CanonicalProtectedPath (path : List Nat) : Prop :=
  path ≠ [] ∧ path.length ≤ maxPath ∧ 0 ∉ path ∧
  (∀ c ∈ path.splitOn slash, ComponentOk c) ∧ ¬ Reserved path

/-! ## Protected-file selection: Git's `filter` attribute -/

/-- One record of `git check-attr -z --stdin filter` output: the path as
    requested, the attribute name and its value, each NUL-terminated. -/
def attrRecord (path value : List Nat) : List Nat :=
  path ++ [0] ++ filterAttr ++ [0] ++ value ++ [0]

/-- A path is protected iff Git reports `filter` = `transcrypt-v3` for it. -/
def Selected (value : List Nat) : Prop := value = filterDriver

instance (value : List Nat) : Decidable (Selected value) :=
  inferInstanceAs (Decidable (value = filterDriver))

/-- `response` holds, at offset `start`, the record for `path` with the
    NUL-free value `value`; the next record starts at `next`. -/
def AttrRecordAt (response : List Nat) (start : Nat) (path value : List Nat) (next : Nat) : Prop :=
  0 ∉ value ∧ attrRecord path value <+: response.drop start ∧
    next = start + (attrRecord path value).length

/-- Git's complete answer to a request for the listed paths, in order. -/
def attrResponse (records : List (List Nat × List Nat)) : List Nat :=
  records.flatMap (fun r => attrRecord r.1 r.2)

end Transcrypt.V3Policy

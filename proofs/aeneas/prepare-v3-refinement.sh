#!/usr/bin/env bash
# Put the independently maintained v3 Lean specification into the *same*
# Lake package as the Aeneas-generated production Rust code. This is a
# prerequisite for a true refinement theorem, NOT itself a refinement proof.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
project="$root/rust/proofs/aeneas/generated/V3Core/lean"
source_spec="$root/proofs/lean/Transcrypt"

if [ ! -s "$project/V3Wire/Extraction.lean" ] || [ ! -s "$project/lakefile.toml" ] || [ ! -s "$project/V3Wire.lean" ]; then
  echo 'No generated V3Core Lean project. Run bash proofs/aeneas/translate-v3-core.sh.' >&2
  exit 2
fi
if [ ! -s "$source_spec/V3WireCodec.lean" ] || [ ! -s "$source_spec/V3Wire.lean" ]; then
  echo 'Missing independent Transcrypt v3 Lean specification.' >&2
  exit 2
fi
if ! grep -Eq '^[[:space:]]*import[[:space:]]+V3Wire[.]Extraction([[:space:]]|$)' "$project/V3Wire.lean"; then
  echo 'Generated root does not import the production Aeneas extraction.' >&2
  exit 2
fi

mkdir -p "$project/Transcrypt" "$project/V3Wire/Verification"
cp "$source_spec/V3Wire.lean" "$project/Transcrypt/V3Wire.lean"
cp "$source_spec/V3WireCodec.lean" "$project/Transcrypt/V3WireCodec.lean"
# Do not import the historical v2/policy theorems: the v3 proof project only
# needs the independent v3 specification, not the unrelated legacy modules.
printf 'import Transcrypt.V3WireCodec\n' > "$project/Transcrypt.lean"

# Hax creates one Lean package; our independently maintained spec is a
# second local library in that same package, compiled with its exact toolchain.
if ! grep -Eq '^[[:space:]]*name[[:space:]]*=[[:space:]]*"Transcrypt"[[:space:]]*$' "$project/lakefile.toml"; then
  printf '\n# Independent v3 protocol specification, staged from proofs/lean.\n[[lean_lib]]\nname = "Transcrypt"\n' >> "$project/lakefile.toml"
fi

# Important: this file intentionally makes NO assertion equating generated
# code to the specification. It ensures both artifacts are imported by the
# same checked library. Real refinement theorems must live in Verification/.
cat > "$project/V3Wire/Verification/IndependentSpec.lean" <<'LEAN'
import V3Wire.Extraction
import Transcrypt.V3WireCodec

/-
This module is the *shared elaboration boundary* between the real
Charon/Aeneas-generated v3 Rust code and the independently authored wire
specification. Importing both is not a proof of correspondence.

The next theorems must directly mention generated decode_config_exact,
encode_config, decode_file_header_exact, encode_file_header and prove
functional refinement of Transcrypt.V3Wire's shape functions. Do not insert
sorry, admit, axioms, or tautological self-comparison theorems here.
-/
LEAN

if ! grep -Eq '^[[:space:]]*import[[:space:]]+V3Wire[.]Verification[.]IndependentSpec([[:space:]]|$)' "$project/V3Wire.lean"; then
  # Imports must precede declarations in Lean; never append an import below
  # a generated namespace, doc declaration, or other non-import syntax.
  tmp=$(mktemp "$project/V3Wire.lean.XXXXXX")
  { printf 'import V3Wire.Verification.IndependentSpec\n'; cat "$project/V3Wire.lean"; } > "$tmp"
  mv "$tmp" "$project/V3Wire.lean"
fi

echo 'Independent v3 wire specification and generated Rust extraction now share one Lake project.'
echo 'No refinement theorem is claimed by this preparation step.'

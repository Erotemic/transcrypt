#!/usr/bin/env bash
# Build the cargo-hax/Aeneas output from the actual Rust source.
# This deliberately does not claim refinement to the independent V3WireCodec.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
project="$root/rust/proofs/aeneas/generated/V3Core/lean"
source_dir="$project/V3Wire"

if ! command -v lake >/dev/null 2>&1; then
  echo 'Missing lake; install Lean using elan.' >&2
  exit 2
fi
if [ ! -s "$project/lakefile.toml" ] || [ ! -s "$project/lean-toolchain" ] || [ ! -s "$source_dir/Extraction.lean" ]; then
  echo 'Missing generated Lean project. Run:' >&2
  echo '  bash proofs/aeneas/translate-v3-core.sh' >&2
  exit 2
fi
if [ ! -s "$project/V3Wire.lean" ] || ! grep -Eq '^[[:space:]]*import[[:space:]]+V3Wire[.]Extraction([[:space:]]|$)' "$project/V3Wire.lean"; then
  echo 'Generated Lean root must actively import V3Wire.Extraction.' >&2
  echo 'Do not count a successful build of an empty package.' >&2
  exit 3
fi

# Aeneas creates external-model templates for unsupported primitives. The
# build must not succeed by admitting those obligations, even when templates
# are not automatically imported by the generated library.
if grep -REn --include='*.lean' '(^|[^[:alnum:]_])(sorry|admit|axiom)([^[:alnum:]_]|$)' "$source_dir"; then
  echo 'Unproved generated or external-model declarations detected.' >&2
  echo 'Give each required external model an independently justified contract.' >&2
  exit 3
fi

(cd "$project" && lake build V3Wire)
echo 'The actual Rust-to-Lean extraction compiles.'
echo 'Refinement against the independent V3WireCodec is still to be proved.'

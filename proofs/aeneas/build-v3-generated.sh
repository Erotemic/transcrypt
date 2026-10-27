#!/usr/bin/env bash
# Compile the real Aeneas output AND the independent v3 specification in
# one kernel/toolchain. Checks that all imported local sources are hole-free.
# This is the preparation for (not completion of) generated-code refinement.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
project="$root/rust/proofs/aeneas/generated/V3Core/lean"
source_dir="$project/V3Wire"

if ! command -v lake >/dev/null 2>&1; then
	echo 'Missing lake; install Lean using elan.' >&2
	exit 2
fi
if ! command -v python3 >/dev/null 2>&1; then
	echo 'Missing python3, required only by the verification build scripts.' >&2
	exit 2
fi
if [ ! -s "$project/lakefile.toml" ] || [ ! -s "$project/lean-toolchain" ] || [ ! -s "$source_dir/Extraction.lean" ]; then
	echo 'Missing generated Lean project. Run:' >&2
	echo '  bash proofs/aeneas/translate-v3-core.sh' >&2
	exit 2
fi
if [ ! -s "$project/V3Wire.lean" ] || ! grep -Eq '^[[:space:]]*import[[:space:]]+V3Wire[.]Extraction([[:space:]]|$)' "$project/V3Wire.lean"; then
	echo 'Generated Lean root must actively import V3Wire.Extraction.' >&2
	exit 3
fi

bash "$root/proofs/aeneas/prepare-v3-refinement.sh"
python3 "$root/proofs/aeneas/check_v3_proof_tree.py" --root "$root"
(cd "$project" && lake build Transcrypt V3Wire)
echo 'The actual Rust-to-Lean extraction AND the independent v3 spec compile in one Lake project.'
echo 'A refinement theorem using the generated function definitions is still required.'

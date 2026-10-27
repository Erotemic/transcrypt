#!/usr/bin/env bash
# Compile checked-in real Aeneas extraction + source-of-truth Lean spec +
# direct generated-code refinement theorems without rerunning Charon.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
if ! command -v lake >/dev/null 2>&1; then
	echo 'Missing Lake/Lean (elan). Install Lean, then rerun.' >&2
	exit 2
fi
python3 "$root/proofs/aeneas/v3_snapshot.py" stage
cd "$root/proofs/aeneas/v3"
# Exact project pin is v4.31.0; mathlib must use this project's cache/version.
lake exe cache get
lake build Transcrypt V3Wire
printf '%s\n' 'Built checked-in production Aeneas extraction, independent spec and refinement module.'

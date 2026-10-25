#!/usr/bin/env bash
# Target the first source-derived Aeneas loop step lemmas in the pinned project.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
python3 "$root/proofs/aeneas/v3_snapshot.py" stage
cd "$root/proofs/aeneas/v3"
lake exe cache get
lake build V3Wire.Verification.CodecSteps

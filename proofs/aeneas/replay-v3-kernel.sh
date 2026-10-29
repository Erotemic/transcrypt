#!/usr/bin/env bash
# Replay every declaration the v3 proofs depend on, Lean's library and
# Mathlib included, through this machine's Lean kernel from scratch
# (leanchecker --fresh), rather than trusting .olean files compiled elsewhere.
# Run after build-v3-tracked.sh, or with V3_LEAN_ENV empty and LEAN_PATH set
# as check-v3-without-lake.sh does.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root/proofs/aeneas/v3"
for module in V3Wire Transcrypt; do
	${V3_LEAN_ENV-lake env} leanchecker --fresh "$module"
done
printf '%s\n' 'kernel replay: V3Wire and Transcrypt, with all their imports, re-checked from scratch.'

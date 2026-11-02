#!/usr/bin/env bash
# Compile checked-in real Aeneas extraction + source-of-truth Lean spec +
# direct generated-code refinement theorems without rerunning Charon.
# PYTHON names the Python 3 interpreter (default python3).
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
if ! command -v lake >/dev/null 2>&1; then
	echo 'Missing Lake/Lean (elan). Install Lean, then rerun.' >&2
	exit 2
fi
"${PYTHON:-python3}" "$root/proofs/aeneas/v3_snapshot.py" stage
cd "$root/proofs/aeneas/v3"
# Exact project pin is v4.31.0; mathlib must use this project's cache/version.
# The download is retried: a dropped connection fails some of its files, and
# a rerun fetches only the missing ones.
cache_attempts=3
for attempt in $(seq "$cache_attempts"); do
	lake exe cache get && break
	if [ "$attempt" -eq "$cache_attempts" ]; then
		exit 1
	fi
	echo "mathlib cache download failed (attempt $attempt of $cache_attempts); retrying" >&2
done
lake build Transcrypt V3Wire
printf '%s\n' 'Built checked-in production Aeneas extraction, independent spec and refinement module.'

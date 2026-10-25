#!/usr/bin/env bash
# Audit the axioms used by the headline v3 refinement theorems. Fails if any
# theorem uses sorryAx or an axiom beyond propext, Classical.choice and
# Quot.sound (Lean's standard axioms). Run after build-v3-tracked.sh.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root/proofs/aeneas/v3"
out=$(lake env lean audit/Axioms.lean 2>&1)
printf '%s\n' "$out"
expected=$(grep -c '^#print axioms' audit/Axioms.lean)
reported=$(printf '%s\n' "$out" | grep -c "depends on axioms" || true)
if [ "$reported" -ne "$expected" ]; then
  echo "axiom audit: expected $expected reports, got $reported" >&2
  exit 1
fi
if printf '%s\n' "$out" | grep -q "error"; then
  echo 'axiom audit: Lean reported an error' >&2
  exit 1
fi
bad=$(printf '%s\n' "$out" | grep "depends on axioms" \
  | sed -e 's/.*depends on axioms: \[//' -e 's/\]$//' | tr ',' '\n' \
  | sed 's/^ *//' | grep -v -x -e propext -e Classical.choice -e Quot.sound || true)
if [ -n "$bad" ]; then
  echo "axiom audit: nonstandard axioms: $bad" >&2
  exit 1
fi
echo "axiom audit: $expected theorems use only propext, Classical.choice, Quot.sound"

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
# Lean wraps long axiom lists over several lines; parse the whole output.
printf '%s\n' "$out" | python3 -c '
import re, sys
out = sys.stdin.read()
expected = int(sys.argv[1])
if re.search(r"\berror\b", out):
    sys.exit("axiom audit: Lean reported an error")
reports = re.findall(r"depends on axioms: \[([^\]]*)\]", out)
unaxiomatic = len(re.findall(r"does not depend on any axioms", out))
if len(reports) + unaxiomatic != expected:
    sys.exit(f"axiom audit: expected {expected} reports, got {len(reports) + unaxiomatic}")
standard = {"propext", "Classical.choice", "Quot.sound"}
bad = sorted({a.strip() for r in reports for a in r.split(",")} - standard)
if bad:
    sys.exit("axiom audit: nonstandard axioms: " + ", ".join(bad))
print(f"axiom audit: {expected} theorems use only propext, Classical.choice, Quot.sound")
' "$expected"

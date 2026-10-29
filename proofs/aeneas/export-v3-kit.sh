#!/usr/bin/env bash
# Package what check-v3-without-lake.sh needs on a system where Lake cannot
# fetch or build the dependencies: the compiled dependency modules (Mathlib,
# Aeneas, ...) in the proofs' import closure, and that closure in import
# order. Run after build-v3-tracked.sh. Usage: export-v3-kit.sh <out.tgz>
# PYTHON names the Python 3 interpreter (default python3).
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
cd "$root/proofs/aeneas/v3"
kit=$(mktemp -d)
trap 'rm -rf "$kit"' EXIT
cat >"$kit/closure.lean" <<'LEAN'
import Lean
open Lean
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `V3Wire}, {module := `Transcrypt}] {}
  for m in env.header.moduleNames do IO.println m
LEAN
lake env lean --run "$kit/closure.lean" >"$kit/closure.txt"
find .lake/packages -path '*/.lake/build/lib/lean' -type d >"$kit/roots.txt"
"${PYTHON:-python3}" - "$kit" <<'PY'
import os, sys
kit = sys.argv[1]
roots = open(f"{kit}/roots.txt").read().split()
own = ("Init", "Lean", "Std", "Lake", "V3Wire", "Transcrypt")
files = []
for module in open(f"{kit}/closure.txt").read().split():
    if module.split(".")[0] in own:
        continue  # the toolchain's own, or compiled by the checking machine
    stem = module.replace(".", "/")
    found = [f"{r}/{stem}{ext}" for r in roots
             for ext in (".olean", ".olean.server", ".olean.private", ".ir")
             if os.path.isfile(f"{r}/{stem}{ext}")]
    if not any(f.endswith(".olean") for f in found):
        sys.exit(f"export-v3-kit: no compiled module for {module}")
    files += found
open(f"{kit}/files.txt", "w").write("\n".join(files) + "\n")
PY
tar czf "$out" -T "$kit/files.txt" -C "$kit" closure.txt roots.txt
printf 'wrote %s\n' "$out"

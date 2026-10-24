#!/usr/bin/env bash
# Extract the *actual* Rust v3 wire core. Proof obligations remain to be closed.
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
for t in cargo charon aeneas sha256sum; do
  command -v "$t" >/dev/null 2>&1 || { echo "Missing $t" >&2; exit 2; }
done
out="$root/proofs/aeneas/generated/V3Core"
mkdir -p "$out"
(
  cd "$root/rust/crates/transcrypt-v3-core"
  charon cargo --preset=aeneas --dest-file "$out/v3-core.llbc"
)
aeneas -backend lean "$out/v3-core.llbc" -dest "$out" -subdir Translation -split-files -namespace TranscryptGenerated.V3Core
{
  cd "$root"
  sha256sum rust/crates/transcrypt-v3-core/src/lib.rs
  sha256sum "$out/v3-core.llbc"
  rustc --version
  charon --version || true
  aeneas --version || true
} > "$out/PROVENANCE.txt"
echo 'Extraction complete; do not claim verified refinement until generated Lean and independent theorems compile.'

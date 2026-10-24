#!/usr/bin/env bash
# Charon/Aeneas entrypoint for the ACTUAL no_std Rust legacy pure core.
# Translation is NOT a completed proof. Requires compatible pinned toolchain.
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
for tool in cargo charon aeneas sha256sum; do
    if ! command -v "$tool" >/dev/null 2>&1; then
        printf 'Missing %s; install the matched Charon/Aeneas/Rust toolchain\n' "$tool" >&2
        exit 2
    fi
done
out="$root/proofs/aeneas/generated/LegacyCore"
mkdir -p "$out"
llbc="$out/transcrypt-legacy-core.llbc"
(
    cd "$root/rust/crates/transcrypt-legacy-core"
    charon cargo --preset=aeneas --dest-file "$llbc"
)
aeneas -backend lean "$llbc" -dest "$out" -subdir Translation -split-files -namespace TranscryptGenerated.LegacyCore
{
    echo 'Source under verification:'
    cd "$root"
    sha256sum rust/crates/transcrypt-legacy-core/src/lib.rs
    echo 'Tool versions:'
    rustc --version
    cargo --version
    charon --version || true
    aeneas --version || true
    echo 'LLBC hash:'
    sha256sum "$llbc"
} > "$out/PROVENANCE.txt"
echo "Generated translation: $out"
echo 'No refinement theorem is claimed until the generated functions are linked to the independent Lean spec and compiled.'

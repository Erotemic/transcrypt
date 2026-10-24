#!/usr/bin/env bash
# Generate Lean FROM ACTUAL RUST, never from a handwritten lookalike.
# This is an opt-in developer tool, not a prerequisite for the shipped Bash.
# Generated output requires its own Aeneas Lean library and a subsequent
# refinement proof before any Rust formal-verification claim can be made.
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
for tool in cargo charon aeneas sha256sum; do
    if ! command -v "$tool" >/dev/null 2>&1; then
        printf 'Missing %s: install compatible pinned Rust/Charon/Aeneas toolchains\n' "$tool" >&2
        exit 2
    fi
done
out="$root/proofs/aeneas/generated"
mkdir -p "$out"
llbc="$out/transcrypt-policy.llbc"
(
    cd "$root/rust/crates/transcrypt-policy"
    charon cargo --preset=aeneas --dest-file "$llbc"
)
aeneas -backend lean "$llbc" -dest "$out" -subdir Policy -split-files -namespace TranscryptGenerated.Policy
{
    printf 'Rust source:\n'
    cd "$root"
    sha256sum rust/crates/transcrypt-policy/src/lib.rs
    printf '\nTool versions:\n'
    rustc --version
    cargo --version
    charon --version || true
    aeneas --version || true
    printf '\nGenerated LLBC SHA-256:\n'
    sha256sum "$llbc"
} > "$out/PROVENANCE.txt"
printf 'Generated Rust LLBC and candidate Lean translations under %s\n' "$out"
printf 'NOTE: translation alone is not a proof; inspect opaque functions and compile refinement theorems.\n'

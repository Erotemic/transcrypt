#!/usr/bin/env bash
# Standalone proof driver: no dependencies added to the shipped Bash tool.
set -eu
cd "$(dirname "$0")/../.."
# Translate the actual Rust expressions for the modeled safe subset.
# Unsupported syntax fails closed rather than retaining a stale hand model.
tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT
python3 proofs/sourcecheck/generate_z3_model.py \
    --kind base64 \
    --source rust-legacy/crates/transcrypt-protocol/src/base64_bits.rs \
    --output "$tmp/rust_source_model.h"
# A CI runner with libz3-dev installs the usual linker name. This container
# has only a versioned runtime library; LIBZ3 lets it link explicitly.
if [[ -n ${LIBZ3:-} ]]; then
    cc -std=c11 -Wall -Wextra -Werror -pedantic -O2 -I "$tmp" \
        proofs/smt/base64_bitvector.c "$LIBZ3" -o "$tmp/base64-proof"
else
    cc -std=c11 -Wall -Wextra -Werror -pedantic -O2 -I "$tmp" \
        proofs/smt/base64_bitvector.c -lz3 -o "$tmp/base64-proof"
fi
"$tmp/base64-proof"

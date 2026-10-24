#!/usr/bin/env bash
# Standalone proof driver: no dependencies added to the shipped Bash tool.
set -eu
cd "$(dirname "$0")/../.."
# The SMT harness is manually connected to production Rust expressions.
# Reject a changed production core until the proof model is reviewed.
if command -v sha256sum >/dev/null 2>&1; then
    sha256sum --check proofs/smt/source.sha256
elif command -v shasum >/dev/null 2>&1; then
    read -r expected path < proofs/smt/source.sha256
    actual=$(shasum -a 256 "$path")
    [[ ${actual%% *} == "$expected" ]] || {
        printf 'Rust bit core changed without re-review of SMT model\n' >&2
        exit 1
    }
else
    printf 'A SHA-256 hash checker is required for source/model binding\n' >&2
    exit 1
fi
tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT
# A CI runner with libz3-dev installs the usual linker name. This container
# has only a versioned runtime library; LIBZ3 lets it link explicitly.
if [[ -n ${LIBZ3:-} ]]; then
    cc -std=c11 -Wall -Wextra -Werror -pedantic -O2 \
        proofs/smt/base64_bitvector.c "$LIBZ3" -o "$tmp/base64-proof"
else
    cc -std=c11 -Wall -Wextra -Werror -pedantic -O2 \
        proofs/smt/base64_bitvector.c -lz3 -o "$tmp/base64-proof"
fi
"$tmp/base64-proof"

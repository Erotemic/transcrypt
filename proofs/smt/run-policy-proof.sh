#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")/../.."
if command -v sha256sum >/dev/null 2>&1; then
    sha256sum --check proofs/smt/policy-source.sha256
elif command -v shasum >/dev/null 2>&1; then
    read -r expected path < proofs/smt/policy-source.sha256
    actual=$(shasum -a 256 "$path")
    [[ ${actual%% *} == "$expected" ]] || {
        printf 'Rust policy source changed; re-review the SMT model\n' >&2
        exit 1
    }
else
    printf 'SHA-256 source check unavailable\n' >&2
    exit 1
fi
tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT
if [[ -n ${LIBZ3:-} ]]; then
    cc -std=c11 -Wall -Wextra -Werror -pedantic -O2 proofs/smt/policy_bitvector.c "$LIBZ3" -o "$tmp/policy-proof"
else
    cc -std=c11 -Wall -Wextra -Werror -pedantic -O2 proofs/smt/policy_bitvector.c -lz3 -o "$tmp/policy-proof"
fi
"$tmp/policy-proof"

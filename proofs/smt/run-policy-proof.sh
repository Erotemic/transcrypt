#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")/../.."
# The source-derived Boolean expressions remove the old manual
# SHA-fingerprint correspondence. Unsupported syntax is a hard failure.
tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT
python3 proofs/sourcecheck/generate_z3_model.py \
	--kind policy \
	--source rust-legacy/crates/transcrypt-policy/src/lib.rs \
	--output "$tmp/rust_source_model.h"
if [[ -n ${LIBZ3:-} ]]; then
	cc -std=c11 -Wall -Wextra -Werror -pedantic -O2 -I "$tmp" proofs/smt/policy_bitvector.c "$LIBZ3" -o "$tmp/policy-proof"
else
	cc -std=c11 -Wall -Wextra -Werror -pedantic -O2 -I "$tmp" proofs/smt/policy_bitvector.c -lz3 -o "$tmp/policy-proof"
fi
"$tmp/policy-proof"

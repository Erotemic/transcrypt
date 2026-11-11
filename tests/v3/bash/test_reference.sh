#!/usr/bin/env bash
# No cryptographic Python/Rust dependency required: independent vectors are
# checked as fixed bytes against OpenSSL CLI, then exercised in real Git.
set -euo pipefail
export LC_ALL=C
SOURCE_ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd -P)
CLI=$SOURCE_ROOT/contrib/v3/transcrypt-bash
VECTORS=$SOURCE_ROOT/tests/v3/bash/portable-p2-vectors.tsv
SCRATCH=$(mktemp -d "${TMPDIR:-/tmp}/transcrypt-p2-test.XXXXXXXX")
trap 'rm -rf -- "$SCRATCH"' EXIT
FAIL=0
assert() { "$@" || { printf 'FAIL: %s\n' "$*" >&2; exit 1; }; }
hex_bytes() { local s=$1 i; for ((i=0;i<${#s};i+=2)); do printf '%b' "\\x${s:i:2}"; done; }
hex_file() { od -An -tx1 -v <"$1" | tr -d ' \n'; }
export TRANSCRYPT_PASSWORD='correct horse battery staple'
mkdir "$SCRATCH/vectors"
cd "$SCRATCH/vectors"
git init -q
git config user.email test@example.invalid
git config user.name Test
mkdir .transcrypt
while IFS=$'\t' read -r name pathhex plainhex cfghex recordhex; do
    [[ $name == \#* || -z $name ]] && continue
    hex_bytes "$cfghex" > .transcrypt/config
    break
done <"$VECTORS"
"$CLI" unlock
count=0
while IFS=$'\t' read -r name pathhex plainhex cfghex recordhex; do
    [[ $name == \#* || -z $name ]] && continue
    path=$(hex_bytes "$pathhex")
    [[ $plainhex == '-' ]] && plainhex=''
    hex_bytes "$plainhex" >"$SCRATCH/plain"
    "$CLI" encrypt "$path" <"$SCRATCH/plain" >"$SCRATCH/record"
    [[ $(hex_file "$SCRATCH/record") == "$recordhex" ]] || { echo "vector mismatch: $name" >&2; exit 1; }
    "$CLI" decrypt "$path" <"$SCRATCH/record" >"$SCRATCH/opened"
    cmp -s "$SCRATCH/plain" "$SCRATCH/opened" || { echo "roundtrip mismatch: $name" >&2; exit 1; }
    if "$CLI" decrypt "another/$path" <"$SCRATCH/record" >"$SCRATCH/rejected" 2>/dev/null; then
        echo "wrong-path accepted: $name" >&2; exit 1
    fi
    ((count+=1))
done <"$VECTORS"
# Tamper the tag (position 23) and ensure no plaintext reaches stdout.
{ head -c 22 "$SCRATCH/record"; printf '\xff'; tail -c +24 "$SCRATCH/record"; } >"$SCRATCH/tampered"
if "$CLI" decrypt "$path" <"$SCRATCH/tampered" >"$SCRATCH/incorrect" 2>/dev/null; then
    echo 'modified ciphertext authenticated' >&2; exit 1
fi
[[ ! -s "$SCRATCH/incorrect" ]] || { echo 'unauthenticated plaintext released' >&2; exit 1; }
"$CLI" lock
if printf 'plaintext' | "$CLI" encrypt demo.secret >/dev/null 2>&1; then
    echo 'locked backend encrypted new plaintext' >&2; exit 1
fi
if TRANSCRYPT_PASSWORD=wrong-password "$CLI" unlock >/dev/null 2>&1; then
    echo 'wrong password unlocked config' >&2; exit 1
fi
printf 'PASS: %s independent byte vectors and negative-path checks\n' "$count"

# Exercise a real .gitattributes, index, commit, rename, rekey and disclosure.
cd "$SCRATCH"
mkdir lifecycle
cd lifecycle
git init -q
git config user.email test@example.invalid
git config user.name Test
printf 'hello\n' >one.secret
printf 'ordinary\n' >public.txt
git add one.secret public.txt
"$CLI" init --profile v3-scrypt-aes256-siv '*.secret'
"$CLI" verify-index
git commit -qm initial
# The index config is part of the publication contract.
original_cfg_oid=$(git rev-parse :.transcrypt/config)
wrong_cfg_oid=$(printf 'not-a-v3-config' | git hash-object -w --stdin)
git update-index --cacheinfo 100644 "$wrong_cfg_oid" .transcrypt/config
if "$CLI" verify-index >/dev/null 2>&1; then
    echo 'mismatched staged config passed verification' >&2; exit 1
fi
git update-index --cacheinfo 100644 "$original_cfg_oid" .transcrypt/config
# The explicit external diff must render authenticated Git blobs as plaintext.
printf 'HELLO\n' >one.secret
git add one.secret
if ! git diff --cached -- one.secret | grep -q 'HELLO'; then
    echo 'Git diff failed to display authenticated plaintext' >&2; exit 1
fi
printf 'hello\n' >one.secret
git add one.secret
[[ $(git show HEAD:one.secret | head -c 6 | od -An -tx1 -v | tr -d ' \n') == '545633460002' ]] || exit 1
assert git diff --quiet
git mv one.secret two.secret
"$CLI" rebind
"$CLI" verify-index
git commit -qm renamed
[[ $(git show HEAD:two.secret | "$CLI" decrypt two.secret) == hello ]] || exit 1
"$CLI" audit HEAD
"$CLI" lock
[[ $(git show HEAD:two.secret | "$CLI" smudge two.secret | head -c 6 | od -An -tx1 -v | tr -d ' \n') == '545633460002' ]] || exit 1
"$CLI" unlock
"$CLI" hydrate
TRANSCRYPT_PASSWORD='new sufficiently strong password' "$CLI" rekey
"$CLI" verify-index
git commit -qm rekeyed
[[ $(git show HEAD:two.secret | "$CLI" decrypt two.secret) == hello ]] || exit 1
"$CLI" unprotect '*.secret'
[[ $(git show :two.secret) == $'hello' ]] || exit 1
git commit -qm unprotected
[[ $(git show HEAD:two.secret) == $'hello' ]] || exit 1
# A new remote must see only authenticated objects for selected paths in
# every outgoing revision, including revisions before a local rekey.
git init --bare -q "$SCRATCH/remote.git"
git remote add origin "$SCRATCH/remote.git"
git push -q origin HEAD:refs/heads/main
# Simulate a malicious or defective clean filter followed by an apparently
# repaired HEAD. Pre-push must reject the intermediate plaintext Git object.
"$CLI" protect '*.secret'
git commit -qm protect-again
printf 'published plaintext would leak\n' >two.secret
git -c filter.transcrypt-v3.clean=cat add two.secret
git -c core.hooksPath=/dev/null commit -qm deliberately-unsafe
printf 'safe now\n' >two.secret
git add two.secret
git commit -qm repaired
if git push -q origin HEAD:refs/heads/main >"$SCRATCH/push.log" 2>&1; then
    echo 'pre-push failed to catch historical plaintext in outgoing range' >&2; exit 1
fi
printf 'PASS: full profile-2 Git lifecycle, rename, rekey, unprotect, diff and push-history refusal\n'

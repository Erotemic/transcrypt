#!/usr/bin/env bash
# Minimal Bash/OpenSSL verification of the shared released-v2 contract.
# Does not require Bats, Rust, Python, or a network connection.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
test_repo=$(mktemp -d)
trap 'rm -rf -- "$test_repo"' EXIT
cd "$test_repo"
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null
git init -q
git config --local transcrypt.version 2.3.2
git config --local transcrypt.cipher aes-256-cbc
git config --local transcrypt.password 'abc 123'
git config --local transcrypt.super-secret.cipher aes-256-cbc
git config --local transcrypt.super-secret.password 321cba
git config --local transcrypt.openssl-path openssl
printf 'My secret content\n' > sensitive_file

expected='U2FsdGVkX1/6ilR0PmJpAyCF7iG3+k4aBwbgVd48WaQXznsg42nXbQrlWsf/qiCg'
actual=$(bash "$root/transcrypt" clean sensitive_file < sensitive_file 2>/dev/null)
[[ $actual == "$expected" ]] || { echo 'legacy default golden vector mismatch' >&2; exit 1; }
[[ $(printf '%s\n' "$expected" | bash "$root/transcrypt" smudge) == 'My secret content' ]] || exit 1

cp sensitive_file super_sensitive_file
expected_named='U2FsdGVkX1+dAkIV/LAKXMmqjDNOGoOVK8Rmhw9tUnbR4dwBDglpkXIT3yzYBvoc'
actual=$(bash "$root/transcrypt" clean context=super-secret super_sensitive_file < super_sensitive_file 2>/dev/null)
[[ $actual == "$expected_named" ]] || { echo 'legacy named golden vector mismatch' >&2; exit 1; }
[[ $(printf '%s\n' "$expected_named" | bash "$root/transcrypt" smudge context=super-secret) == 'My secret content' ]] || exit 1

# Git clean must honor what was piped in, not the current worktree file size.
: > empty_worktree
actual=$(printf 'not empty\n' | bash "$root/transcrypt" clean empty_worktree 2>/dev/null)
[[ $actual == U2FsdGVk* ]] || { echo 'nonempty stdin incorrectly bypassed' >&2; exit 1; }

# Incorrect CBC padding must never emit a partial decrypted prefix.
corrupt='U2FsdGVkX1/6ilR0PmJpAyCF7iG3+k4aBwbgVd48WaQXznsg42nXbQrlWsf/qiCh'
actual=$(printf '%s\n' "$corrupt" | bash "$root/transcrypt" smudge)
[[ $actual == "$corrupt" ]] || { echo 'partial plaintext leaked on decryption failure' >&2; exit 1; }

# The provisional new-format marker must not be mistaken for v2 plaintext.
if printf 'TCRYPT3:secret' | bash "$root/transcrypt" clean empty_worktree >/dev/null 2>&1; then
    echo 'legacy clean accepted provisional secure ciphertext' >&2; exit 1
fi
if printf 'TCRYPT3:secret' | bash "$root/transcrypt" smudge >/dev/null 2>&1; then
    echo 'legacy smudge accepted provisional secure ciphertext' >&2; exit 1
fi

echo 'PASS: Bash legacy default/named vectors, stdin authority, no partial smudge, no v3 downgrade'

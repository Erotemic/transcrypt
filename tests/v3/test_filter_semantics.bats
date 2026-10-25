#!/usr/bin/env bats

load "$BATS_TEST_DIRNAME/../_test_helper.bash"

@test "legacy clean: nonempty stdin encrypted even if worktree file empty" {
  : > sensitive_file
  encrypted=$(printf 'staged content\n' | "$TRANSCRYPT" clean sensitive_file 2>/dev/null)
  [[ "$encrypted" == U2FsdGVk* ]]
}

@test "legacy smudge: failed decryption cannot leak partial plaintext" {
  local corrupt='U2FsdGVkX1/6ilR0PmJpAyCF7iG3+k4aBwgbVd48WaQXznsg42nXbQrlWsf/qiCh'
  local result
  result=$(printf '%s\n' "$corrupt" | "$TRANSCRYPT" smudge context=default)
  [ "$result" = "$corrupt" ]
}

@test "legacy filter: cannot silently treat provisional v3 records as v2" {
  : > sensitive_file
  run bash -c 'printf TCRYPT3:secret | "$1" clean sensitive_file' bash "$TRANSCRYPT"
  [ "$status" -ne 0 ]
  run bash -c 'printf TCRYPT3:secret | "$1" smudge context=default' bash "$TRANSCRYPT"
  [ "$status" -ne 0 ]
}

@test "legacy init: wrong password is rejected before persistent state changes" {
  encrypt_named_file sensitive_file 'My secret content'
  "$TRANSCRYPT" --uninstall --yes
  git reset --hard

  run "$TRANSCRYPT" --cipher=aes-256-cbc --password=WRONG --yes
  [ "$status" -ne 0 ]
  run git config --get --local transcrypt.password
  [ "$status" -ne 0 ]
  run git config --get --local transcrypt.version
  [ "$status" -ne 0 ]

  run "$TRANSCRYPT" --cipher=aes-256-cbc --password='abc 123' --yes
  [ "$status" -eq 0 ]
  run cat sensitive_file
  [ "$status" -eq 0 ]
  [ "${lines[0]}" = 'My secret content' ]
}

# F-01: the 8-byte "U2FsdGVk" marker (Base64 of "Salted") is not proof that
# input is ciphertext. Plaintext that begins with it must still be encrypted.
@test "legacy clean: plaintext beginning with the ciphertext marker is encrypted" {
  printf 'U2FsdGVkNOT_ENCRYPTED\nprivate_token=abcdefg\n' > marker.secret
  cp marker.secret "$BATS_TEST_TMPDIR/plain"
  encrypt_named_file marker.secret
  [ "$status" -eq 0 ]
  git cat-file blob HEAD:marker.secret > "$BATS_TEST_TMPDIR/stored"
  # The committed blob is not the plaintext ...
  run cmp -s "$BATS_TEST_TMPDIR/stored" "$BATS_TEST_TMPDIR/plain"
  [ "$status" -ne 0 ]
  run grep -q private_token "$BATS_TEST_TMPDIR/stored"
  [ "$status" -ne 0 ]
  # ... it is ciphertext that decrypts back to it,
  "$TRANSCRYPT" smudge context=default < "$BATS_TEST_TMPDIR/stored" > "$BATS_TEST_TMPDIR/decrypted"
  cmp "$BATS_TEST_TMPDIR/decrypted" "$BATS_TEST_TMPDIR/plain"
  # ... and a fresh checkout restores the plaintext with a clean status.
  rm marker.secret
  git checkout -- marker.secret
  cmp marker.secret "$BATS_TEST_TMPDIR/plain"
  check_repo_is_clean
}

@test "legacy clean: re-cleaning genuine ciphertext is byte-identical" {
  encrypt_named_file sensitive_file 'My secret content'
  git cat-file blob HEAD:sensitive_file > "$BATS_TEST_TMPDIR/stored"
  [ "$(cat "$BATS_TEST_TMPDIR/stored")" = 'U2FsdGVkX1/6ilR0PmJpAyCF7iG3+k4aBwbgVd48WaQXznsg42nXbQrlWsf/qiCg' ]
  "$TRANSCRYPT" clean context=default sensitive_file < "$BATS_TEST_TMPDIR/stored" > "$BATS_TEST_TMPDIR/recleaned"
  cmp "$BATS_TEST_TMPDIR/recleaned" "$BATS_TEST_TMPDIR/stored"
  # A worktree that holds the ciphertext itself also stays clean.
  cp "$BATS_TEST_TMPDIR/stored" sensitive_file
  git add sensitive_file
  [ "$(git rev-parse :sensitive_file)" = "$(git rev-parse HEAD:sensitive_file)" ]
}

@test "legacy clean: marker-prefixed ciphertext for another key is not passed through" {
  # Genuine OpenSSL ciphertext under a different password is plaintext to
  # this repository; it must be wrapped, never stored as-is.
  foreign=$(printf 'foreign secret' | openssl enc -e -a -aes-256-cbc -md MD5 -pass pass:other 2>/dev/null)
  [[ "$foreign" == U2FsdGVk* ]]
  out=$(printf '%s\n' "$foreign" | "$TRANSCRYPT" clean context=default sensitive_file 2>/dev/null)
  [[ "$out" == U2FsdGVk* ]]
  [ "$out" != "$foreign" ]
  [ "$(printf '%s\n' "$out" | "$TRANSCRYPT" smudge context=default)" = "$foreign" ]
}

@test "legacy clean: without a key only bytes Git already stores pass through" {
  "$TRANSCRYPT" --context=super-secret --cipher=aes-256-cbc --password=321cba --yes
  encrypt_named_file super_file 'Super secret' super-secret
  [ "$status" -eq 0 ]
  git cat-file blob HEAD:super_file > "$BATS_TEST_TMPDIR/stored"
  git config --local --unset transcrypt.super-secret.password
  # The undecrypted checkout of a context this clone lacks stays clean ...
  "$TRANSCRYPT" clean context=super-secret super_file < "$BATS_TEST_TMPDIR/stored" > "$BATS_TEST_TMPDIR/out"
  cmp "$BATS_TEST_TMPDIR/out" "$BATS_TEST_TMPDIR/stored"
  # ... but new marker-prefixed input can be neither verified nor encrypted.
  run bash -c 'printf "U2FsdGVkNOT_ENCRYPTED\n" | "$1" clean context=super-secret super_file' bash "$TRANSCRYPT"
  [ "$status" -ne 0 ]
  [[ "$output" != *NOT_ENCRYPTED* ]]
}

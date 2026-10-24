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

#!/usr/bin/env bats

load "$BATS_TEST_DIRNAME/../_test_helper.bash"

# Stage a plaintext blob directly into the index, bypassing the clean filter.
# Simulates a commit made by a tool that does not apply .gitattributes
# filters, or by a deliberately bypassed pre-commit hook.
stage_plaintext_directly() {
  local filename=$1 content=$2 oid
  oid=$(printf '%s' "$content" | git hash-object -w --stdin)
  git update-index --add --cacheinfo "100644,$oid,$filename"
}

@test "pathnames: --list preserves repeated spaces in filenames" {
  printf 'secret\n' > 'double  space'
  echo '"double  space" filter=crypt' >> .gitattributes
  git add .gitattributes 'double  space'
  git commit -qm 'encrypt'

  run $TRANSCRYPT --list
  [ "$status" -eq 0 ]
  [ "${lines[0]}" = "double  space" ]
}

@test "pathnames: --list preserves double-quoted filenames" {
  # Upstream issue #173
  local name='quo"te'
  printf 'secret\n' > "$name"
  echo "\"quo\\\"te\" filter=crypt" >> .gitattributes
  git add .gitattributes "$name"
  git commit -qm 'encrypt'

  run $TRANSCRYPT --list
  [ "$status" -eq 0 ]
  [ "${lines[0]}" = 'quo"te' ]
}

@test "pathnames: --list preserves backslash in filenames" {
  local name='back\slash'
  printf 'secret\n' > "$name"
  # .gitattributes pattern quoting requires an extra level of escaping
  # for a literal backslash: a quoted "\\" matches one literal "\"
  echo '"back\\\\slash" filter=crypt' >> .gitattributes
  git add .gitattributes "$name"
  git commit -qm 'encrypt'

  run $TRANSCRYPT --list
  [ "$status" -eq 0 ]
  [ "${lines[0]}" = 'back\slash' ]
}

@test "pathnames: pre-commit rejects unencrypted file whose name contains a newline" {
  local name=$'new\nline'
  printf 'sensitive data' > "$name"
  echo "\"new\\nline\" filter=crypt" >> .gitattributes
  git add .gitattributes
  stage_plaintext_directly "$name" 'sensitive data'

  run git commit -m 'attempt'
  [ "$status" -ne 0 ]
}

@test "pathnames: pre-commit rejects unencrypted file whose name contains repeated spaces" {
  local name='double  space'
  printf 'sensitive data' > "$name"
  echo '"double  space" filter=crypt' >> .gitattributes
  git add .gitattributes
  stage_plaintext_directly "$name" 'sensitive data'

  run git commit -m 'attempt'
  [ "$status" -ne 0 ]
}

@test "pathnames: encrypted file whose name contains a newline round-trips" {
  local name=$'new\nline'
  printf 'secret\n' > "$name"
  echo "\"new\\nline\" filter=crypt" >> .gitattributes
  git add .gitattributes "$name"
  git commit -qm 'encrypt'

  run cat "$name"
  [ "$status" -eq 0 ]
  [ "${lines[0]}" = "secret" ]
}

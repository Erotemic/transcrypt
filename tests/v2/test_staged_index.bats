#!/usr/bin/env bats

load "$BATS_TEST_DIRNAME/../_test_helper.bash"

# Hashing directly into the index models a Git client that bypasses clean
# filters. The cooperative hook must reject plaintext in a protected blob.
stage_plaintext_without_clean() {
  local path=$1 oid
  oid=$(printf 'index-only secret\n' | git hash-object -w --stdin)
  git update-index --add --cacheinfo "100644,$oid,$path"
}

@test "staged index: protected staged attributes override different worktree attributes" {
  echo 'secret filter=crypt diff=crypt merge=crypt' > .gitattributes
  git add .gitattributes
  stage_plaintext_without_clean secret

  # The old hook used the worktree's attributes, saw no protected paths,
  # and allowed a commit containing plaintext with protected attributes.
  : > .gitattributes
  run git commit -m 'attempt staged-attribute bypass'
  [ "$status" -ne 0 ]
  [[ "$output" = *'not encrypted in the Git index: secret'* ]]
}

@test "staged index: staged regular blob is checked even if worktree is a symlink" {
  echo 'secret filter=crypt diff=crypt merge=crypt' > .gitattributes
  git add .gitattributes
  stage_plaintext_without_clean secret
  ln -s nowhere secret

  # The old hook checked [[ -L secret ]] and skipped this staged blob.
  run git commit -m 'attempt worktree-symlink bypass'
  [ "$status" -ne 0 ]
  [[ "$output" = *'not encrypted in the Git index: secret'* ]]
}

@test "staged index: valid staged symlink is permitted when worktree is a regular file" {
  echo 'secret filter=crypt diff=crypt merge=crypt' > .gitattributes
  ln -s elsewhere secret
  git add .gitattributes secret
  rm secret
  printf 'not the staged file\n' > secret

  run git commit -m 'stage symlink only'
  [ "$status" -eq 0 ]
  [ "$(git ls-files -s secret | cut -d ' ' -f1)" = '120000' ]
}

@test "staged index: protected staged regular blob is checked when working file is missing" {
  echo 'secret filter=crypt diff=crypt merge=crypt' > .gitattributes
  git add .gitattributes
  stage_plaintext_without_clean secret
  rm -f secret
  run git commit -m 'attempt missing-worktree bypass'
  [ "$status" -ne 0 ]
  [[ "$output" = *'not encrypted in the Git index: secret'* ]]
}

@test "staged index: literal filename patterns are not expanded when checking index mode" {
  local name='secret[1]*?file'
  echo 'secret* filter=crypt diff=crypt merge=crypt' > .gitattributes
  git add .gitattributes
  stage_plaintext_without_clean "$name"
  run git commit -m 'attempt pattern-name bypass'
  [ "$status" -ne 0 ]
}

@test "staged index: normal encrypted file remains committable" {
  echo 'secret filter=crypt diff=crypt merge=crypt' > .gitattributes
  printf 'actual protected data\n' > secret
  git add .gitattributes secret
  run git commit -m 'normal encrypted commit'
  [ "$status" -eq 0 ]
  run git show HEAD:secret
  [ "$status" -eq 0 ]
  [[ "$output" == U2FsdGVk* ]]
}

@test "staged index: failure to enumerate Git attributes rejects pre-commit" {
  echo 'secret filter=crypt diff=crypt merge=crypt' > .gitattributes
  printf 'encrypted via filter\n' > secret
  git add .gitattributes secret

  # Intercept Git's check-attr subcommand only. An enumeration error must
  # not be interpreted as an empty list of files needing protection.
  local git_binary
  git_binary=$(command -v git)
  mkdir -p "$BATS_TEST_TMPDIR/intercept"
  printf '#!/bin/sh\nfor arg in "$@"; do\n  [ "$arg" = check-attr ] && exit 70\ndone\nexec "%s" "$@"\n' "$git_binary" > "$BATS_TEST_TMPDIR/intercept/git"
  chmod +x "$BATS_TEST_TMPDIR/intercept/git"

  mkdir -p "$BATS_TEST_TMPDIR/onlytmp"
  run env TMPDIR="$BATS_TEST_TMPDIR/onlytmp" PATH="$BATS_TEST_TMPDIR/intercept:$PATH" "$TRANSCRYPT" pre_commit
  [ "$status" -ne 0 ]
  [[ "$output" = *'cannot enumerate the staged protected paths'* ]]
  # Error paths must remove the temporary staged-path listing as well.
  [ "$(find "$BATS_TEST_TMPDIR/onlytmp" -type f | wc -l)" -eq 0 ]
}

@test "staged index: commits still work when nproc is not installed" {
  echo 'secret filter=crypt diff=crypt merge=crypt' > .gitattributes
  printf 'encrypted via filter\n' > secret
  git add .gitattributes secret
  mkdir -p "$BATS_TEST_TMPDIR/intercept"
  printf '#!/bin/sh\nexit 127\n' > "$BATS_TEST_TMPDIR/intercept/nproc"
  chmod +x "$BATS_TEST_TMPDIR/intercept/nproc"

  run env PATH="$BATS_TEST_TMPDIR/intercept:$PATH" git commit -m 'fallback to one process'
  [ "$status" -eq 0 ]
}

@test "staged index: local info attributes cannot hide staged portable encryption" {
  echo 'secret filter=crypt diff=crypt merge=crypt' > .gitattributes
  git add .gitattributes
  stage_plaintext_without_clean secret
  # info/attributes outranks index attributes even with --cached.
  # A clone will not have this local override, so the hook must consult
  # an independently isolated portable index view as well.
  echo 'secret -filter' > .git/info/attributes
  run git commit -m 'attempt local-attribute bypass'
  [ "$status" -ne 0 ]
  [[ "$output" = *'not encrypted in the Git index: secret'* ]]
}

@test "staged index: locally configured extra protected paths remain checked" {
  # The portable tree has no crypt attribute, but the local user's
  # info/attributes deliberately opts this path into encryption.
  echo 'secret filter=crypt' > .git/info/attributes
  stage_plaintext_without_clean secret
  run git commit -m 'attempt local filter bypass'
  [ "$status" -ne 0 ]
  [[ "$output" = *'not encrypted in the Git index: secret'* ]]
}

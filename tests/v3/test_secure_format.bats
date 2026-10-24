#!/usr/bin/env bats

load "$BATS_TEST_DIRNAME/../_test_helper.bash"

# Unlike the copied v2 regression tests in this directory, these tests use the
# authenticated v3 format rather than checking legacy ciphertext fixtures.
SETUP_SKIP_INIT_TRANSCRYPT=1

init_v3() {
  "$TRANSCRYPT" --format=v3 --cipher=aes-256-cbc --password='v3 test password' --yes
}

init_legacy() {
  "$TRANSCRYPT" --format=legacy --cipher=aes-256-cbc --password='v3 test password' --yes
}

add_secret() {
  printf 'A secret with a trailing newline\n' > secret.txt
  printf 'secret.txt filter=crypt diff=crypt merge=crypt\n' >> .gitattributes
  git add .transcrypt/config .gitattributes secret.txt
  git -c core.hooksPath=/dev/null commit -qm 'Test secret'
}

@test "v3: new empty repos use authenticated PBKDF2 by default" {
  run "$TRANSCRYPT" --cipher=aes-256-cbc --password='v3 test password' --yes
  [ "$status" -eq 0 ]
  [ "$(git config --file .transcrypt/config transcrypt.format)" = v3 ]
  [ "$(git config --file .transcrypt/config transcrypt.kdf)" = pbkdf2 ]
  [ "$(git config --file .transcrypt/config transcrypt.digest)" = sha256 ]
  [ "$(git config --file .transcrypt/config transcrypt.auth)" = hmac-sha256 ]
  [ "${#BATS_TEST_DESCRIPTION}" -gt 0 ]
  ! git config --file .transcrypt/config --get transcrypt.password
}

@test "v3: fixed plaintext gives identical encrypted Git object" {
  init_v3
  add_secret
  [ "$(git show --no-textconv HEAD:secret.txt | head -c8)" = 'TCRYPT3:' ]
  first=$(git rev-parse HEAD:secret.txt)
  git add secret.txt
  [ "$(git rev-parse :secret.txt)" = "$first" ]
  rm secret.txt
  git checkout HEAD -- secret.txt
  [ "$(cat secret.txt)" = 'A secret with a trailing newline' ]
  [ "$(git show HEAD:secret.txt --textconv)" = 'A secret with a trailing newline' ]
  git diff --exit-code
}

@test "v3: binary content survives clean and smudge" {
  init_v3
  printf 'A\0B\377\n' >secret.txt
  printf 'secret.txt filter=crypt diff=crypt merge=crypt\n' >>.gitattributes
  cp secret.txt expected.bin
  git add .transcrypt/config .gitattributes secret.txt
  git -c core.hooksPath=/dev/null commit -qm binary
  rm secret.txt
  git checkout HEAD -- secret.txt
  cmp -s secret.txt expected.bin
}

@test "v3: modified MAC is rejected without emitting plaintext" {
  init_v3
  add_secret
  git show --no-textconv HEAD:secret.txt >raw.txt
  sed 's/^TCRYPT3:/TCRYPT3:0/' raw.txt >tampered.txt
  if "$TRANSCRYPT" smudge context=default <tampered.txt >output.txt 2>err.txt; then
    echo 'tampered ciphertext was accepted'
    false
  fi
  [ ! -s output.txt ]
  grep -q 'authentication/decryption failed' err.txt
  if "$TRANSCRYPT" clean context=default secret.txt <tampered.txt >output.txt 2>err.txt; then
    echo 'tampered ciphertext was accepted by the clean filter'
    false
  fi
  [ ! -s output.txt ]
}

@test "v3: wrong password cannot overwrite checkout plaintext" {
  init_v3
  add_secret
  git clone -q "$TEST_REPO" "$BATS_TEST_TMPDIR/clone"
  cd "$BATS_TEST_TMPDIR/clone"
  cp secret.txt raw_before.txt
  if "$TRANSCRYPT" --password=wrong --cipher=aes-256-cbc --yes >log.txt 2>&1; then
    echo 'unlock accepted wrong password'
    false
  fi
  cmp -s raw_before.txt secret.txt
  [ "$(head -c8 secret.txt)" = 'TCRYPT3:' ]
  ! grep -q 'A secret with a trailing newline' secret.txt
  cd "$TEST_REPO"
}

@test "v3: a new clone with correct password decrypts" {
  init_v3
  add_secret
  git clone -q "$TEST_REPO" "$BATS_TEST_TMPDIR/clone"
  cd "$BATS_TEST_TMPDIR/clone"
  "$TRANSCRYPT" --password='v3 test password' --cipher=aes-256-cbc --yes
  [ "$(cat secret.txt)" = 'A secret with a trailing newline' ]
  cd "$TEST_REPO"
}

@test "v3: legacy migration stages authenticated blobs plus public config" {
  init_legacy
  printf 'A secret with a trailing newline\n' >secret.txt
  printf 'secret.txt filter=crypt diff=crypt merge=crypt\n' >>.gitattributes
  git add .gitattributes secret.txt
  git -c core.hooksPath=/dev/null commit -qm legacy
  [ "$(git show HEAD:secret.txt | head -c8)" = U2FsdGVk ]
  "$TRANSCRYPT" --migrate-v3 --yes
  [ "$(git show :secret.txt | head -c8)" = TCRYPT3: ]
  [ "$(git config --file .transcrypt/config transcrypt.format)" = v3 ]
  [ "$(git ls-files .transcrypt/config)" = .transcrypt/config ]
  [ "$(cat secret.txt)" = 'A secret with a trailing newline' ]
  git -c core.hooksPath=/dev/null commit -qm migrate
  rm secret.txt
  git checkout HEAD -- secret.txt
  [ "$(cat secret.txt)" = 'A secret with a trailing newline' ]
}

@test "v3: migration preflight rejects wrong legacy credentials without changes" {
  init_legacy
  printf 'password protected\n' >secret.txt
  printf 'secret.txt filter=crypt diff=crypt merge=crypt\n' >> .gitattributes
  git add .gitattributes secret.txt
  git -c core.hooksPath=/dev/null commit -qm legacy
  original=$(git rev-parse HEAD:secret.txt)
  git config transcrypt.password incorrect
  run "$TRANSCRYPT" --migrate-v3 --yes
  [ "$status" -ne 0 ]
  [[ $output == *'preflight failed'* || $output == *'repo is dirty'* ]]
  [ ! -e .transcrypt/config ]
  [ "$(git rev-parse :secret.txt)" = "$original" ]
  [ "$(head -c8 secret.txt)" != 'TCRYPT3:' ]
}

@test "v3: multiple contexts migrate to separate authenticated keys" {
  init_legacy
  "$TRANSCRYPT" --format=legacy --context=other --cipher=aes-256-cbc --password='other test password' --yes
  printf 'first\n' >first.txt; printf 'second\n' >second.txt
  printf 'first.txt filter=crypt diff=crypt merge=crypt\nsecond.txt filter=crypt-other diff=crypt-other merge=crypt-other\n' >>.gitattributes
  git add .gitattributes first.txt second.txt
  git -c core.hooksPath=/dev/null commit -qm legacy
  "$TRANSCRYPT" --migrate-v3 --yes
  [ "$(git show :first.txt | head -c8)" = TCRYPT3: ]
  [ "$(git show :second.txt | head -c8)" = TCRYPT3: ]
  [ "$(git show :first.txt)" != "$(git show :second.txt)" ]
  git -c core.hooksPath=/dev/null commit -qm migrate
  rm first.txt second.txt
  git checkout HEAD -- first.txt second.txt
  [ "$(cat first.txt)" = first ]
  [ "$(cat second.txt)" = second ]
}

@test "v3: rekey changes ciphertext but preserves plaintext and public salt" {
  init_v3
  add_secret
  original=$(git rev-parse HEAD:secret.txt)
  salt=$(git config --file .transcrypt/config transcrypt.base-salt)
  "$TRANSCRYPT" --rekey --cipher=aes-256-cbc --password='replacement password' --yes
  [ "$(git rev-parse :secret.txt)" != "$original" ]
  [ "$(git config --file .transcrypt/config transcrypt.base-salt)" = "$salt" ]
  git -c core.hooksPath=/dev/null commit -qm rekey
  rm secret.txt
  git checkout HEAD -- secret.txt
  [ "$(cat secret.txt)" = 'A secret with a trailing newline' ]
}

@test "v3: empty files remain compatible as empty git blobs" {
  init_v3
  : >empty.secret
  printf 'empty.secret filter=crypt diff=crypt merge=crypt\n' >>.gitattributes
  git add .transcrypt/config .gitattributes empty.secret
  git -c core.hooksPath=/dev/null commit -qm empty
  [ "$(git cat-file -s HEAD:empty.secret)" -eq 0 ]
  rm empty.secret
  git checkout HEAD -- empty.secret
  [ ! -s empty.secret ]
}

@test "v3: rejecting a config that tries to store a password" {
  init_v3
  printf '\npassword = leaked\n' >>.transcrypt/config
  run "$TRANSCRYPT" --display
  [ "$status" -ne 0 ]
  [[ $output == *'forbidden key'* ]]
}

@test "v3: smudge rejects authenticated blob with appended data" {
  init_v3
  add_secret
  git show --no-textconv HEAD:secret.txt >raw.txt
  printf 'untrusted trailing data\n' >>raw.txt
  if "$TRANSCRYPT" smudge context=default <raw.txt >out.txt 2>err.txt; then
    echo 'accepted unauthenticated trailing data'
    false
  fi
  [ ! -s out.txt ]
}

@test "v3: migration rejects ciphertext mistaken for unlocked legacy plaintext" {
  init_legacy
  printf 'legacy-data\n' >secret.txt
  printf 'secret.txt filter=crypt diff=crypt merge=crypt\n' >>.gitattributes
  git add .gitattributes secret.txt
  git -c core.hooksPath=/dev/null commit -qm legacy
  original=$(git rev-parse HEAD:secret.txt)
  git show --no-textconv HEAD:secret.txt >secret.txt
  # Git's cached file stat may report a modification even if clean is identical.
  git diff --exit-code -- secret.txt
  git update-index --refresh -- secret.txt >/dev/null 2>&1 || true
  git config transcrypt.password wrong
  if "$TRANSCRYPT" --migrate-v3 --yes >log.txt 2>&1; then
    echo 'accepted ciphertext as plaintext during migration'
    false
  fi
  grep -q 'preflight failed' log.txt
  [ ! -e .transcrypt/config ]
  [ "$(git rev-parse :secret.txt)" = "$original" ]
  [ -z "$(find .git -maxdepth 1 -name 'index.transcrypt.*' -print)" ]
}

@test "v3: flush removes credentials and leaves encrypted checkout" {
  init_v3
  add_secret
  run "$TRANSCRYPT" --flush-credentials --yes
  [ "$status" -eq 0 ]
  ! git config --get transcrypt.password
  [ "$(head -c8 secret.txt)" = TCRYPT3: ]
  [ -f .transcrypt/config ]
}

@test "v3: upgrade leaves public settings and authenticated files intact" {
  init_v3
  add_secret
  old_salt=$(git config --file .transcrypt/config transcrypt.base-salt)
  run "$TRANSCRYPT" --upgrade --yes
  [ "$status" -eq 0 ]
  [ "$(git config --file .transcrypt/config transcrypt.base-salt)" = "$old_salt" ]
  [ "$(cat secret.txt)" = 'A secret with a trailing newline' ]
  git diff --exit-code
}

@test "v3: normal pre-commit hook permits authenticated ciphertext" {
  init_v3
  printf 'hook-tested\n' > secret.txt
  printf 'secret.txt filter=crypt diff=crypt merge=crypt\n' >>.gitattributes
  git add .transcrypt/config .gitattributes secret.txt
  git commit -qm 'Encrypted with active pre-commit hook'
  [ "$(git show --no-textconv HEAD:secret.txt | head -c8)" = TCRYPT3: ]
}

@test "v3: migration commit succeeds with the installed hook active" {
  init_legacy
  printf 'legacy-hook\n' >secret.txt
  printf 'secret.txt filter=crypt diff=crypt merge=crypt\n' >>.gitattributes
  git add .gitattributes secret.txt
  git commit -qm legacy
  "$TRANSCRYPT" --migrate-v3 --yes
  git commit -qm 'Migrated to v3'
  [ "$(git show --no-textconv HEAD:secret.txt | head -c8)" = TCRYPT3: ]
}

@test "v3: names with spaces remain supported across migration" {
  init_legacy
  printf 'A spaced name secret\n' >'spaced secret.txt'
  printf '"spaced secret.txt" filter=crypt diff=crypt merge=crypt\n' >>.gitattributes
  git add .gitattributes 'spaced secret.txt'
  git -c core.hooksPath=/dev/null commit -qm 'Legacy space'
  "$TRANSCRYPT" --migrate-v3 --yes
  [ "$(git show --no-textconv :'spaced secret.txt' | head -c8)" = TCRYPT3: ]
  git -c core.hooksPath=/dev/null commit -qm 'Migrated space'
  rm 'spaced secret.txt'
  git checkout HEAD -- 'spaced secret.txt'
  [ "$(cat 'spaced secret.txt')" = 'A spaced name secret' ]
}

@test "v3: a Git clean filter does not drop input when working path is missing" {
  init_v3
  printf 'present only on stdin\n' >plaintext.txt
  "$TRANSCRYPT" clean context=default missing.secret <plaintext.txt >encrypted.txt
  [ "$(head -c8 encrypted.txt)" = TCRYPT3: ]
  "$TRANSCRYPT" smudge context=default <encrypted.txt >decrypted.txt
  cmp -s plaintext.txt decrypted.txt
}

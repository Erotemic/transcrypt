#!/usr/bin/env bats

SETUP_SKIP_INIT_TRANSCRYPT=1
load "$BATS_TEST_DIRNAME/_test_helper.bash"

@test "legacy OpenSSL migration: pbkdf2 legacy OpenSSL file migrates to authenticated v3" {
  git config transcrypt.version '3.0.0-pre'
  git config transcrypt.cipher 'aes-256-cbc'
  git config transcrypt.digest 'sha256'
  git config transcrypt.kdf 'pbkdf2'
  git config transcrypt.base-salt '0123456789abcdef0123456789abcdef'
  git config transcrypt.openssl-path 'openssl'
  git config transcrypt.password 'abc 123'

  mkdir -p .transcrypt
  git config -f .transcrypt/config transcrypt.version '3.0.0-pre'
  git config -f .transcrypt/config transcrypt.cipher 'aes-256-cbc'
  git config -f .transcrypt/config transcrypt.digest 'sha256'
  git config -f .transcrypt/config transcrypt.kdf 'pbkdf2'
  git config -f .transcrypt/config transcrypt.base-salt '0123456789abcdef0123456789abcdef'

  echo 'sensitive_file filter=crypt diff=crypt merge=crypt' > .gitattributes
  echo 'legacy secret' > plaintext
  ENC_PASS='abc 123' openssl enc -e -a -aes-256-cbc -md sha256 -pbkdf2 -pass env:ENC_PASS -in plaintext -out sensitive_file
  rm plaintext
  git add .gitattributes .transcrypt/config sensitive_file
  git commit -m 'Add legacy encrypted file'

  run ../tools/transcrypt-migrate-legacy-openssl --password='abc 123' --iterations=10000 --yes
  [ "$status" -eq 0 ]
  [[ "$output" = *"Migration staged successfully"* ]]

  run git show :sensitive_file --no-textconv
  [ "$status" -eq 0 ]
  [[ "$output" = *"transcrypt:v3"* ]]
  [[ "$output" = *"auth=hmac-sha256"* ]]

  git commit -m 'Migrate legacy OpenSSL encryption to v3'

  run git show HEAD:sensitive_file --textconv
  [ "$status" -eq 0 ]
  [ "$output" = 'legacy secret' ]
}

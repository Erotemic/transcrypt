#!/usr/bin/env bats

load "$BATS_TEST_DIRNAME/_test_helper.bash"

@test "security: diagnose crypto reports openssl and python capabilities" {
  run ../transcrypt --diagnose-crypto
  [ "$status" -eq 0 ]
  [[ "$output" = *"Crypto diagnostics for transcrypt"* ]]
  [[ "$output" = *"openssl version:"* ]]
  [[ "$output" = *"openssl enc -pbkdf2:"* ]]
  [[ "$output" = *"python3 PBKDF2 fallback:"* ]]
}

@test "security: audit warns about legacy crypto settings" {
  run ../transcrypt --audit
  [ "$status" -eq 0 ]
  [[ "$output" = *"Security audit for this transcrypt repository"* ]]
  [[ "$output" = *"Crypto format:  legacy"* ]]
  [[ "$output" = *"[HIGH] Legacy password derivation is enabled."* ]]
  [[ "$output" = *"[HIGH] Ciphertext authentication is not enabled."* ]]
}

@test "security: init writes non-secret public crypto config" {
  [ -f .transcrypt/config ]
  run cat .transcrypt/config
  [ "$status" -eq 0 ]
  [[ "$output" = *"cipher = aes-256-cbc"* ]]
  [[ "$output" = *"crypto-format = legacy"* ]]
  [[ "$output" = *"kdf = legacy"* ]]
  [[ "$output" != *"abc 123"* ]]
  [[ "$output" != *"password"* ]]
}

@test "security: secure mode encrypts with authenticated v3 envelope" {
  "$BATS_TEST_DIRNAME"/../transcrypt --uninstall --yes
  run "$BATS_TEST_DIRNAME"/../transcrypt --secure --iterations=10000 --cipher=aes-256-cbc --password='abc 123' --yes
  [ "$status" -eq 0 ]

  echo "My v3 secret" > sensitive_file
  echo "sensitive_file filter=crypt diff=crypt merge=crypt" > .gitattributes
  git add .gitattributes .transcrypt/config sensitive_file
  git commit -m "Encrypt v3 file"

  run git show HEAD:sensitive_file --no-textconv
  [ "$status" -eq 0 ]
  [[ "$output" = *"transcrypt:v3"* ]]
  [[ "$output" = *"kdf=pbkdf2"* ]]
  [[ "$output" = *"auth=hmac-sha256"* ]]

  run git show HEAD:sensitive_file --textconv
  [ "$status" -eq 0 ]
  [ "$output" = "My v3 secret" ]
}

@test "security: v3 textconv rejects tampered ciphertext" {
  "$BATS_TEST_DIRNAME"/../transcrypt --uninstall --yes
  "$BATS_TEST_DIRNAME"/../transcrypt --secure --iterations=10000 --cipher=aes-256-cbc --password='abc 123' --yes

  echo "My v3 secret" > sensitive_file
  echo "sensitive_file filter=crypt diff=crypt merge=crypt" > .gitattributes
  git add .gitattributes .transcrypt/config sensitive_file
  git commit -m "Encrypt v3 file"

  git show HEAD:sensitive_file --no-textconv > tampered-v3
  python3 - <<'PY'
from pathlib import Path
path = Path('tampered-v3')
lines = path.read_text().splitlines()
lines[-1] = ('A' if lines[-1][0] != 'A' else 'B') + lines[-1][1:]
path.write_text('\n'.join(lines) + '\n')
PY

  run "$BATS_TEST_DIRNAME"/../transcrypt textconv context=default tampered-v3
  [ "$status" -ne 0 ]
  [[ "$output" = *"unable to authenticate or decrypt transcrypt v3 payload"* ]]
  rm -f tampered-v3
}

@test "security: upgrade-crypto migrates legacy files to v3" {
  echo "Legacy secret" > sensitive_file
  echo "sensitive_file filter=crypt diff=crypt merge=crypt" > .gitattributes
  git add .gitattributes .transcrypt/config sensitive_file
  git commit -m "Encrypt legacy file"

  run git show HEAD:sensitive_file --no-textconv
  [ "$status" -eq 0 ]
  [[ "$output" = U2FsdGVk* ]]

  run "$BATS_TEST_DIRNAME"/../transcrypt --upgrade-crypto --iterations=10000 --yes
  [ "$status" -eq 0 ]
  [[ "$output" = *"rekeyed files have been staged"* ]]
  git commit -m "Upgrade crypto"

  run git show HEAD:sensitive_file --no-textconv
  [ "$status" -eq 0 ]
  [[ "$output" = *"transcrypt:v3"* ]]
  [[ "$output" = *"digest=sha256"* ]]
  [[ "$output" = *"auth=hmac-sha256"* ]]

  run git show HEAD:sensitive_file --textconv
  [ "$status" -eq 0 ]
  [ "$output" = "Legacy secret" ]
}

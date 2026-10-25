#!/usr/bin/env bats

load "$BATS_TEST_DIRNAME/../_test_helper.bash"

@test "pre-commit: pre-commit hook installed on init" {
  # Confirm pre-commit-crypt file is installed
  [ -f .git/hooks/pre-commit-crypt ]
  run cat .git/hooks/pre-commit-crypt
  [ "${lines[1]}" = '# Transcrypt pre-commit hook: fail if secret file in staging lacks the magic prefix "Salted" in B64' ]

  # Confirm hook is also installed/activated at pre-commit file name
  [ -f .git/hooks/pre-commit ]
  run cat .git/hooks/pre-commit
  [ "${lines[1]}" = '# Transcrypt pre-commit hook: fail if secret file in staging lacks the magic prefix "Salted" in B64' ]
}

@test "pre-commit: permit commit of encrypted file with encrypted content" {
  echo "Secret stuff" > sensitive_file
  encrypt_named_file sensitive_file

  echo " and more secrets" >> sensitive_file
  git add sensitive_file
  run git commit -m "Added more"
  [ "$status" -eq 0 ]

  run git log --format=oneline
  [ "$status" -eq 0 ]
  [[ "${lines[0]}" = *"Added more" ]]
  [[ "${lines[1]}" = *"Encrypt file \"sensitive_file\"" ]]
}

@test "pre-commit: reject commit of encrypted file with unencrypted content" {
  echo "Secret stuff" > sensitive_file
  encrypt_named_file sensitive_file

  echo " and more secrets" >> sensitive_file

  # Disable file's crypt config in .gitattributes, add change, then re-enable
  echo "" > .gitattributes
  git add sensitive_file
  echo "sensitive_file filter=crypt diff=crypt merge=crypt" > .gitattributes

  # Confirm the pre-commit rejects plain text content in what should be
  # an encrypted file
  run git commit -m "Added more"
  [ "$status" -ne 0 ]
  [[ "${output}" = *"Transcrypt managed file is not encrypted in the Git index: sensitive_file"* ]]
  [[ "${output}" = *"You probably staged this file using a tool that does not apply .gitattribute filters as required by Transcrypt."* ]]
  [[ "${output}" = *"Fix this by re-staging the file with a compatible tool or with Git on the command line:"* ]]
  [[ "${output}" = *"    git rm --cached -- sensitive_file"* ]]
  [[ "${output}" = *"    git add sensitive_file"* ]]
}

@test "pre-commit: pre-commit hook ignores symlinks to encrypted files" {
  echo "Secret stuff" > sensitive_file
  encrypt_named_file sensitive_file

  ln -s sensitive_file symlink_to_sensitive_file
  echo "\"symlink_to_sensitive_file\" filter=crypt diff=crypt merge=crypt" >> .gitattributes
  git add .gitattributes symlink_to_sensitive_file

  git commit -m "Commit symlink to encrypted file"
  [ "$status" -eq 0 ]

  rm symlink_to_sensitive_file
}

@test "pre-commit: warn and don't clobber existing pre-commit hook on init" {
  # Uninstall pre-existing transcrypt config from setup()
  run $TRANSCRYPT --uninstall --yes

  # Create a pre-existing pre-commit hook
  touch .git/hooks/pre-commit

  run $TRANSCRYPT --cipher=aes-256-cbc --password='abc 123' --yes
  [ "$status" -eq 0 ]
  [[ "${output}" = *"WARNING:"* ]]
  [[ "${output}" = *"Cannot install Git pre-commit hook script because file already exists: .git/hooks/pre-commit"* ]]
  [[ "${output}" = *"Please manually install the pre-commit script saved as: .git/hooks/pre-commit-crypt"* ]]

  # Confirm pre-commit-crypt file is installed, but not copied to pre-commit
  run cat .git/hooks/pre-commit-crypt
  [ "$status" -eq 0 ]
  [[ "${output}" = *'# Transcrypt pre-commit hook: fail if secret file in staging lacks the magic prefix "Salted" in B64'* ]]
  [ ! -s .git/hooks/pre-commit ] # Zero file size]
}

@test "pre-commit: de-activate and remove transcrypt's pre-commit hook" {
  $TRANSCRYPT --uninstall --yes
  [ ! -f .git/hooks/pre-commit ]
  [ ! -f .git/hooks/pre-commit-crypt ]
}

@test "pre-commit: warn and don't delete customised pre-commit hook on uninstall" {
  # Customise transcrypt's pre-commit hook
  echo "#" >> .git/hooks/pre-commit

  run $TRANSCRYPT --uninstall --yes
  [ "$status" -eq 0 ]
  [[ "${output}" = *'WARNING: Cannot safely disable Git pre-commit hook .git/hooks/pre-commit please check it yourself'* ]]
  [ -f .git/hooks/pre-commit ]
  [ ! -f .git/hooks/pre-commit-crypt ]
}

# F-01: the pre-commit check must not accept staged plaintext merely because
# it begins with the "U2FsdGVk" marker.
@test "pre-commit: reject staged plaintext beginning with the ciphertext marker" {
  encrypt_named_file sensitive_file 'Secret stuff'
  printf 'U2FsdGVkNOT_ENCRYPTED\nprivate_token=abcdefg\n' > sensitive_file
  # Stage the plaintext bypassing the clean filter.
  blob=$(git hash-object -w --no-filters sensitive_file)
  git update-index --cacheinfo "100644,$blob,sensitive_file"
  [ "$(git cat-file blob :sensitive_file | head -c8)" = 'U2FsdGVk' ]

  run git commit -m "Plaintext with marker"
  [ "$status" -ne 0 ]
  [[ "${output}" = *"Transcrypt managed file is not encrypted in the Git index: sensitive_file"* ]]
  run "$TRANSCRYPT" pre_commit
  [ "$status" -ne 0 ]
  [ "$(git rev-list --count HEAD)" -eq 1 ]
}

@test "pre-commit: reject marker-prefixed ciphertext copied from another path" {
  encrypt_named_file sensitive_file 'Secret stuff'
  encrypt_named_file other_file 'Other stuff'
  # Real ciphertext, but not this path's: its salt binds the other path.
  blob=$(git rev-parse HEAD:sensitive_file)
  git update-index --cacheinfo "100644,$blob,other_file"
  run "$TRANSCRYPT" pre_commit
  [ "$status" -ne 0 ]
}

@test "pre-commit: unchanged ciphertext of a context without a local key is accepted" {
  "$TRANSCRYPT" --context=super-secret --cipher=aes-256-cbc --password=321cba --yes
  encrypt_named_file super_file 'Super secret' super-secret
  [ "$status" -eq 0 ]
  # Simulate a checkout that holds only the default context's key.
  git config --local --unset transcrypt.super-secret.password
  encrypt_named_file sensitive_file 'Secret stuff'
  [ "$status" -eq 0 ]
  [ "$(git rev-list --count HEAD)" -eq 2 ]
  # A new marker-prefixed object for that path cannot be verified: rejected.
  blob=$(printf 'U2FsdGVkNOT_ENCRYPTED\n' | git hash-object -w --stdin --no-filters)
  git update-index --cacheinfo "100644,$blob,super_file"
  run "$TRANSCRYPT" pre_commit
  [ "$status" -ne 0 ]
}

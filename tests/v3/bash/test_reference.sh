#!/usr/bin/env bash
# The portable Bash client alone (Bash, Git, OpenSSL; no Rust or Python):
# the independent byte vectors of tests/v3/reference/portable-vectors.tsv,
# refusals, and real-Git workflows. Cross-client checks against transcrypt-rs
# are in tests/v3/conformance/run.sh.
set -euo pipefail
export LC_ALL=C
SOURCE_ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd -P)
CLI=$SOURCE_ROOT/contrib/v3/transcrypt-bash
VECTORS=$SOURCE_ROOT/tests/v3/reference/portable-vectors.tsv
SCRATCH=$(mktemp -d "${TMPDIR:-/tmp}/transcrypt-bash-test.XXXXXXXX")
trap 'rm -rf -- "$SCRATCH"' EXIT
# Independent of the caller's Git configuration (default branch name, commit
# signing, hooksPath, pull.rebase, ...): every run has its own empty global
# config and no system config. The branch name is a variable throughout;
# TRANSCRYPT_TEST_BRANCH picks it (CI runs a non-default one).
export HOME=$SCRATCH/home GIT_CONFIG_NOSYSTEM=1
unset XDG_CONFIG_HOME GIT_CONFIG_GLOBAL GIT_CONFIG_SYSTEM GIT_CONFIG_COUNT GIT_CONFIG_PARAMETERS \
    GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES GIT_NAMESPACE GIT_CEILING_DIRECTORIES
mkdir -p "$HOME"
BRANCH=${TRANSCRYPT_TEST_BRANCH:-main}
git config --global init.defaultBranch "$BRANCH"
PASS=0
ok() { PASS=$((PASS + 1)); printf 'ok %d - %s\n' "$PASS" "$*"; }
die() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }
hexb() { local s=$1 i o=''; [[ $s == - ]] && return 0; for ((i = 0; i < ${#s}; i += 2)); do o+="\\x${s:i:2}"; done; printf "$o"; }
hexf() { od -An -tx1 -v <"$1" | tr -d ' \n'; }
newrepo() {
    rm -rf -- "$SCRATCH/$1"; mkdir -p "$SCRATCH/$1"; cd "$SCRATCH/$1"
    git init -q; git config user.email t@example.invalid; git config user.name Test
    git config commit.gpgsign false
}
PASSPHRASE='correct horse battery staple'

# ---------------------------------------------------------------------------
# Independent vectors: config, key-check value and records, both profiles.
# ---------------------------------------------------------------------------
"$CLI" doctor >/dev/null 2>&1 || true
for profile in 2 3; do
    newrepo "vectors-$profile"
    mkdir .transcrypt
    first=1
    while IFS=$'\t' read -r p name pw salt key cfg check pathhex pt rec; do
        [[ $p == "$profile" ]] || continue
        if ((first)); then
            hexb "$cfg" >.transcrypt/config
            hexb "$pw" | "$CLI" unlock --password-stdin --no-hydrate 2>/dev/null
            [[ $(hexf .git/transcrypt-v3/key) == "$cfg$key$check" ]] || die "profile $profile: stored key file differs from the vector"
            first=0
        fi
        path=$(hexb "$pathhex"; printf x); path=${path%x}
        hexb "$pt" >"$SCRATCH/plain"
        "$CLI" encrypt "$path" <"$SCRATCH/plain" >"$SCRATCH/record"
        [[ $(hexf "$SCRATCH/record") == "$rec" ]] || die "profile $profile/$name: record differs from the vector"
        "$CLI" decrypt "$path" <"$SCRATCH/record" >"$SCRATCH/opened"
        cmp -s "$SCRATCH/plain" "$SCRATCH/opened" || die "profile $profile/$name: decrypt"
        if "$CLI" decrypt "other/$path" <"$SCRATCH/record" >"$SCRATCH/out" 2>/dev/null; then die "$name: wrong path accepted"; fi
        [[ ! -s $SCRATCH/out ]] || die "$name: plaintext released for a wrong path"
        size=$(wc -c <"$SCRATCH/record")
        for at in 6 22 $((size - 1)); do
            { head -c "$at" "$SCRATCH/record"; head -c 1 "$SCRATCH/record" | tail -c 1 >/dev/null
              printf '\xa5'; tail -c "+$((at + 2))" "$SCRATCH/record"; } >"$SCRATCH/tampered"
            if "$CLI" decrypt "$path" <"$SCRATCH/tampered" >"$SCRATCH/out" 2>/dev/null; then die "$name: tampering at $at accepted"; fi
            [[ ! -s $SCRATCH/out ]] || die "$name: unauthenticated plaintext released"
        done
        if "$CLI" decrypt "$path" < <(head -c "$((size - 1))" "$SCRATCH/record") >/dev/null 2>&1 && [[ -n $pt && $pt != - ]]; then
            die "$name: truncated record accepted"
        fi
    done <"$VECTORS"
    ok "profile $profile: stored key, config check value and every record match the independent vectors; tampering, truncation and wrong paths refused"
    # Relabelling the config's profile byte: the passphrase no longer unlocks it.
    for byte in 01 02 03 04; do
        [[ $byte == "0$profile" ]] && continue
        { head -c 6 .transcrypt/config; hexb "$byte"; tail -c +8 .transcrypt/config; } >"$SCRATCH/relabelled"
        cp "$SCRATCH/relabelled" .transcrypt/config
        if printf '%s' "$PASSPHRASE" | "$CLI" unlock --password-stdin --no-hydrate >"$SCRATCH/log" 2>&1; then die "relabelled profile $byte unlocked"; fi
        case $byte in
            01) grep -q 'only the Rust client' "$SCRATCH/log" || die 'profile 1 refusal does not name the Rust client' ;;
            04) grep -q 'profile 4' "$SCRATCH/log" || die 'unknown profile not named' ;;
            *) grep -q 'incorrect credentials' "$SCRATCH/log" || die "relabelled config (byte $byte) not refused as unauthentic" ;;
        esac
    done
    ok "profile $profile: a relabelled profile byte never unlocks; profile 1 and unknown profiles are named"
done

# ---------------------------------------------------------------------------
# A Bash-only repository, init to push.
# ---------------------------------------------------------------------------
newrepo life
printf 'hello\n' >one.env
printf 'ordinary\n' >public.txt
mkdir -p 'dir with space'
printf '\x00\xff binary\n' >'dir with space/blob.bin'
git add one.env public.txt 'dir with space/blob.bin'
git commit -qm 'plain start'
if printf 'short' | "$CLI" init --password-stdin '*.env' 2>/dev/null; then die 'short passphrase accepted'; fi
[[ ! -e .transcrypt ]] || die 'refused init left .transcrypt behind'
printf '%s\n' "$PASSPHRASE" | "$CLI" init --password-stdin '*.env' 'dir with space/**' 2>/dev/null
[[ $(head -c 7 .transcrypt/config | od -An -tx1 | tr -d ' \n') == 54434647330002 ]] || die 'init did not write profile 2'
grep -qx '\[attr\]transcrypt filter=transcrypt-v3 diff=transcrypt-v3 merge=transcrypt-v3 -text' .gitattributes || die 'macro missing'
grep -qx '"dir with space/\*\*" transcrypt' .gitattributes || die 'pattern with a blank not quoted'
[[ $(git cat-file blob :one.env | head -c 6 | od -An -tx1 | tr -d ' \n') == 545633460001 ]] || die 'protect did not encrypt the staged file'
git commit -qm 'enable v3'
"$CLI" audit HEAD 2>/dev/null
ok 'init with patterns: profile-2 config, quoted rules, staged records, audit'
[[ $(cat one.env) == hello ]] || die 'worktree should stay plaintext'
git diff --quiet || die 'status not clean after init'
printf 'changed\n' >one.env
git diff | grep -q '^+changed' || die 'diff driver does not show plaintext'
git commit -qam edit
[[ $(git show HEAD:one.env | "$CLI" decrypt one.env) == changed ]] || die 'commit not encrypted'
ok 'edit, diff and commit through the filters'

# Plaintext staged around the filter is sealed by pre-commit.
printf 'bypass\n' >one.env
git -c filter.transcrypt-v3.clean=cat -c filter.transcrypt-v3.required=false add one.env
[[ $(git cat-file blob :one.env) == bypass ]] || die 'setup: bypass did not stage plaintext'
git commit -qm 'bypass attempt'
[[ $(git show HEAD:one.env | "$CLI" decrypt one.env) == bypass ]] || die 'pre-commit did not seal plaintext staged around the filter'
ok 'pre-commit seals plaintext staged around the filter'

# git mv: the record is re-encrypted for the new path at commit.
git mv one.env two.env
git commit -qm rename
[[ $(git show HEAD:two.env | "$CLI" decrypt two.env) == bypass ]] || die 'rename not re-encrypted'
"$CLI" verify-index 2>/dev/null
ok 'git mv: pre-commit re-encrypts for the new path'

# A record copied to another path (no rename) is refused, not laundered.
git show HEAD:two.env >"$SCRATCH/rec"
oid=$(git hash-object -w --no-filters "$SCRATCH/rec")
git update-index --add --cacheinfo "100644,$oid,copy.env"
if git commit -qm copy 2>/dev/null; then die 'a record copied to another path was committed'; fi
git rm -q --cached copy.env
ok 'a record staged at a path it was not sealed for is refused'

# Lock, hydrate, unlock.
"$CLI" lock 2>/dev/null
[[ ! -e .git/transcrypt-v3/key ]] || die 'lock kept the key'
[[ $(head -c 4 two.env) == TV3F ]] || die 'lock left plaintext'
git diff --quiet || die 'locked checkout not clean'
printf 'locked edit\n' >two.env
if git add two.env 2>/dev/null; then die 'locked clean stored plaintext'; fi
git checkout -q -- two.env 2>/dev/null || git show HEAD:two.env >two.env
printf '%s\n' "$PASSPHRASE" | "$CLI" unlock --password-stdin 2>/dev/null
[[ $(cat two.env) == bypass ]] || die 'unlock did not hydrate'
git diff --quiet || die 'status not clean after unlock'
ok 'lock restores ciphertext and refuses plaintext; unlock hydrates'
printf 'uncommitted\n' >two.env
if "$CLI" lock 2>/dev/null; then die 'lock with uncommitted changes'; fi
[[ $(cat two.env) == uncommitted ]] || die 'refused lock lost an edit'
git checkout -q -- two.env
ok 'lock refuses (and keeps) uncommitted edits'

# Merge of protected files: clean, and conflicted with markers.
git checkout -q -b side
printf 'a\nb\nc\nside\n' >m.env; git add m.env; git commit -qm 'm base'
git checkout -q "$BRANCH"; git merge -q side
git checkout -q side; printf 'a\nB\nc\nside\n' >m.env; git commit -qam side-edit
git checkout -q "$BRANCH"; printf 'a\nb\nc\nside\nmaster\n' >m.env; git commit -qam master-edit
git merge -q side -m merge 2>/dev/null
[[ $(cat m.env) == $'a\nB\nc\nside\nmaster' ]] || die 'clean merge of a protected file'
git checkout -q side; printf 'x\n' >m.env; git commit -qam side-x
git checkout -q "$BRANCH"; printf 'y\n' >m.env; git commit -qam master-y
if git merge -q side 2>/dev/null; then die 'conflict expected'; fi
grep -q '<<<<<<< ours' m.env || die 'conflict markers missing in the worktree'
[[ $(git cat-file blob :2:m.env | head -c 4) == TV3F ]] || die 'conflict stage not encrypted'
printf 'resolved\n' >m.env; git add m.env; git commit -qm resolved
[[ $(git show HEAD:m.env | "$CLI" decrypt m.env) == resolved ]] || die 'resolution not encrypted'
ok 'merges: clean merge decrypted, conflict markers in plaintext, records in Git'

# Rekey and profile conversion to PBKDF2.
printf 'rekey passphrase number two\n' | "$CLI" rekey --password-stdin --profile=pbkdf2 2>/dev/null
git commit -qm rekey
[[ $(head -c 7 .transcrypt/config | od -An -tx1 | tr -d ' \n') == 54434647330003 ]] || die 'rekey did not convert to profile 3'
[[ $(git show HEAD:two.env | "$CLI" decrypt two.env) == bypass ]] || die 'rekeyed record'
git diff --quiet || die 'status not clean after rekey'
"$CLI" audit HEAD~1 2>&1 | grep -q 'envelope only' || die 'old epoch should audit by envelope'
ok 'rekey --profile=pbkdf2 converts and re-encrypts; old commits audit keylessly'

# Push: an intermediate plaintext commit is refused even after a fix.
git init -q --bare "$SCRATCH/remote.git"
git remote add origin "$SCRATCH/remote.git"
git push -q origin "$BRANCH" 2>/dev/null
printf 'leak\n' >two.env
git -c filter.transcrypt-v3.clean=cat -c filter.transcrypt-v3.required=false add two.env
git -c core.hooksPath=/dev/null commit -qm 'unsafe, hooks bypassed'
printf 'fixed\n' >two.env; git add two.env; git commit -qm fixed
if git push -q origin "$BRANCH" 2>"$SCRATCH/push.log"; then die 'pre-push accepted an intermediate plaintext commit'; fi
grep -q 'refusing to push' "$SCRATCH/push.log" || die 'pre-push refusal message'
git reset -q --hard HEAD~2
ok 'pre-push refuses a plaintext commit hidden behind a later fix'

# Unprotect publishes plaintext deliberately.
"$CLI" unprotect 'dir with space/**' 2>/dev/null
[[ $(git cat-file blob ':dir with space/blob.bin' | od -An -tx1 | tr -d ' \n') == 00ff2062696e6172790a ]] || die 'unprotect'
git commit -qm unprotect
ok 'unprotect stages plaintext'

# Fresh clone: install, unlock, files decrypt; a missing key keeps records.
git push -q origin "$BRANCH" 2>/dev/null
git clone -q "$SCRATCH/remote.git" "$SCRATCH/clone" 2>/dev/null
cd "$SCRATCH/clone"
git config user.email t@example.invalid; git config user.name Test
[[ $(head -c 4 two.env) == TV3F ]] || die 'clone without filters should hold ciphertext'
printf 'rekey passphrase number two\n' | "$CLI" unlock --password-stdin 2>/dev/null
[[ $(cat two.env) == bypass ]] || die 'clone unlock + hydrate'
git status --porcelain | grep -q . && die 'clone not clean after unlock'
ok 'fresh clone: unlock installs filters and decrypts'

# Linked worktree shares the key; lock flushes both.
git worktree add -q "$SCRATCH/wt" 2>/dev/null
[[ $(cat "$SCRATCH/wt/two.env") == bypass ]] || die 'linked worktree checkout not decrypted'
"$CLI" lock 2>/dev/null
[[ $(head -c 4 "$SCRATCH/wt/two.env") == TV3F ]] || die 'lock did not flush the linked worktree'
ok 'linked worktrees share the key; lock flushes every worktree'

"$CLI" uninstall 2>/dev/null
[[ -z $(git config --get filter.transcrypt-v3.clean || true) && ! -e .git/hooks/pre-commit ]] || die 'uninstall'
ok 'uninstall removes filters and hooks'

# ---------------------------------------------------------------------------
# Policy changes, subdirectories, staged-only versions, unprotected records,
# reencrypt, bare-repository audits (regressions from the 2026-11-11 review).
# ---------------------------------------------------------------------------
newrepo policy
printf 'SECRET=1\n' >secret.env
mkdir docs
printf 'doc\n' >docs/readme.txt
git add -A
git commit -qm start
printf '%s\n' "$PASSPHRASE" | "$CLI" init --password-stdin '*.env' 2>/dev/null
git commit -qm v3
# Another named filter claiming a protected file (git lfs track).
cp .gitattributes "$SCRATCH/attrs"
printf '*.env filter=lfs diff=lfs merge=lfs -text\n' >>.gitattributes
git add .gitattributes
printf 'SECRET=2\n' >secret.env
git -c filter.lfs.clean=cat -c filter.lfs.smudge=cat add secret.env
if git -c filter.lfs.clean=cat commit -qm lfs 2>"$SCRATCH/err"; then die 'a filter override of a protected file was committed'; fi
grep -q 'filter `lfs`' "$SCRATCH/err" || die 'filter override not named'
# A redefined macro (no filter) is refused too.
sed 's/^\[attr\]transcrypt filter=transcrypt-v3 /[attr]transcrypt /' "$SCRATCH/attrs" >.gitattributes
git add .gitattributes secret.env
if git commit -qm macro 2>"$SCRATCH/err"; then die 'a broken macro was committed'; fi
grep -q 'macro does not set filter' "$SCRATCH/err" || die 'broken macro not named'
cp "$SCRATCH/attrs" .gitattributes
git add .gitattributes
git add --renormalize secret.env
git commit -qm restored
ok 'a .gitattributes change that unprotects files (lfs override, broken macro) is refused'
# Commands from a subdirectory act on the whole repository.
cd docs
"$CLI" lock 2>/dev/null
[[ $(head -c 4 ../secret.env) == TV3F ]] || die 'lock from a subdirectory left plaintext'
printf '%s\n' "$PASSPHRASE" | "$CLI" unlock --password-stdin 2>/dev/null
[[ $(cat ../secret.env) == SECRET=2 ]] || die 'unlock from a subdirectory'
cd ..
git -c filter.transcrypt-v3.clean=cat -c filter.transcrypt-v3.required=false -c core.hooksPath=/dev/null commit -qm 'plaintext' --allow-empty
printf 'leak\n' >leak.env
git -c filter.transcrypt-v3.clean=cat -c filter.transcrypt-v3.required=false add leak.env
git -c core.hooksPath=/dev/null commit -qm 'plaintext leak'
if (cd docs && "$CLI" audit HEAD >/dev/null 2>&1); then die 'audit from a subdirectory missed plaintext'; fi
git reset -q --hard HEAD~2
ok 'lock, unlock and audit from a subdirectory act on the whole repository'
# protect keeps a staged-only version.
printf 'v1\n' >p.cfg
git add p.cfg
git commit -qm p
printf 'v1\nSTAGED-ONLY\n' >p.cfg
git add p.cfg
printf 'v1\nworktree\n' >p.cfg
"$CLI" protect p.cfg 2>/dev/null
[[ $(git cat-file blob :p.cfg | "$CLI" decrypt p.cfg) == $'v1\nSTAGED-ONLY' ]] || die 'protect lost the staged-only version'
[[ $(cat p.cfg) == $'v1\nworktree' ]] || die 'protect changed the worktree'
git add p.cfg
git commit -qm 'protect p.cfg'
ok 'protect keeps a staged-only version of a file'
# A record moved to an unprotected name is refused.
git mv secret.env secret.bak
if git commit -qm mv 2>"$SCRATCH/err"; then die 'a record at an unprotected name was committed'; fi
grep -q 'not protected' "$SCRATCH/err" || die 'unprotected record not named'
git mv secret.bak secret.env
ok 'a record moved to an unprotected name is refused'
# reencrypt brings a record across a rekey.
git checkout -q -b old
printf 'from the old branch\n' >old.env
git add old.env
git commit -qm 'old config'
git checkout -q "$BRANCH"
printf 'rekey passphrase number two\n' | "$CLI" rekey --password-stdin 2>/dev/null
git commit -qm rekey
# Staging the old branch's file brings its record, of the earlier config.
git checkout -q old -- old.env 2>/dev/null
[[ -n $(git ls-files old.env) ]] || die 'setup: old.env not staged'
printf '%s\n' "$PASSPHRASE" | "$CLI" reencrypt --password-stdin --yes 2>/dev/null
"$CLI" verify-index 2>/dev/null
git commit -qm 'brought forward'
[[ $(git show HEAD:old.env | "$CLI" decrypt old.env) == 'from the old branch' ]] || die 'reencrypt'
ok 'reencrypt re-encrypts a record of an earlier config under the current one'
# Bare repositories audit (server-side hooks); --max-commits refuses.
git init -q --bare "$SCRATCH/policy.git"
git push -q "$SCRATCH/policy.git" "$BRANCH" 2>/dev/null
(cd "$SCRATCH/policy.git" && "$CLI" audit "$BRANCH" >/dev/null 2>"$SCRATCH/err") || die "audit in a bare repository: $(cat "$SCRATCH/err")"
if (cd "$SCRATCH/policy.git" && "$CLI" audit --max-commits=1 "$BRANCH" >/dev/null 2>&1); then die '--max-commits did not refuse'; fi
ok 'audit runs in a bare repository; --max-commits refuses larger ranges'

# ---------------------------------------------------------------------------
# lock, configless branches and forged unprotected records (second review).
# ---------------------------------------------------------------------------
newrepo lock2
printf 'pub\n' >pub.txt
git add pub.txt
git commit -qm before-v3
printf 'SECRET=1\n' >secret.env
git add secret.env
git commit -qm secret
printf '%s\n' "$PASSPHRASE" | "$CLI" init --password-stdin '*.env' 2>/dev/null
git commit -qm v3
# Untracked and unmerged protected plaintext block lock; nothing changes.
printf 'new\n' >new.env
if "$CLI" lock 2>/dev/null; then die 'lock with an untracked protected file'; fi
[[ -e .git/transcrypt-v3/key && $(cat secret.env) == SECRET=1 ]] || die 'refused lock changed something'
rm new.env
git checkout -q -b side
printf 'SECRET=side\n' >secret.env
git commit -qam side
git checkout -q "$BRANCH"
printf 'SECRET=master\n' >secret.env
git commit -qam master
git merge -q side >/dev/null 2>&1 || true
if "$CLI" lock 2>/dev/null; then die 'lock with a conflicted protected file'; fi
git merge --abort
# A stale key (the config changed) cannot lock away plaintext.
cp .transcrypt/config "$SCRATCH/cfg"
printf 'rekey passphrase number two\n' | "$CLI" rekey --password-stdin 2>/dev/null
git reset -q --hard HEAD
cp "$SCRATCH/cfg" .transcrypt/config
printf 'rekey passphrase number two\n' | "$CLI" unlock --password-stdin --no-hydrate 2>/dev/null || true
git checkout -q -- .transcrypt/config
if "$CLI" lock 2>/dev/null && [[ $(cat secret.env) == SECRET=master ]]; then die 'a stale key locked away plaintext'; fi
printf '%s\n' "$PASSPHRASE" | "$CLI" unlock --password-stdin 2>/dev/null
"$CLI" lock 2>/dev/null
[[ $(head -c 4 secret.env) == TV3F ]] || die 'lock after unlock'
printf '%s\n' "$PASSPHRASE" | "$CLI" unlock --password-stdin 2>/dev/null
ok 'lock refuses untracked, conflicted and stale-key plaintext without changing anything'
# A branch from before v3 still commits files nothing protects.
git checkout -q -b pre HEAD~3
printf 'more\n' >>pub.txt
git commit -qam 'unprotected edit before v3' || die 'commit on a pre-v3 branch'
git checkout -q "$BRANCH"
ok 'commits on a branch from before init are accepted when nothing is protected'
# A forged record at an unprotected path that HEAD holds fails verify-index.
{ head -c 22 secret.env 2>/dev/null; git show HEAD:secret.env | head -c 22; } >/dev/null
git show HEAD:secret.env | head -c 22 >"$SCRATCH/forged"
head -c 40 /dev/urandom >>"$SCRATCH/forged"
oid=$(git hash-object -w --no-filters "$SCRATCH/forged")
git update-index --add --cacheinfo "100644,$oid,notes.bak"
git -c core.hooksPath=/dev/null commit -qm forged
if "$CLI" verify-index 2>/dev/null; then die 'a forged record at an unprotected path passed verify-index'; fi
git reset -q --hard HEAD~1
ok 'verify-index authenticates records at unprotected paths'

# ---------------------------------------------------------------------------
# v2 migration (needs the repository's Bash v2 script).
# ---------------------------------------------------------------------------
V2=$SOURCE_ROOT/transcrypt
if [[ -x $V2 ]]; then
    newrepo migrate
    printf 'v2 secret\n' >s.key; printf 'x\n' >plain.txt
    git add s.key plain.txt; git commit -qm init
    "$V2" -c aes-256-cbc -p 'v2-password' -y >/dev/null 2>&1
    printf 's.key filter=crypt diff=crypt merge=crypt\n' >.gitattributes
    git add .gitattributes; git add --renormalize s.key; git commit -qm 'v2 protect'
    [[ $(git cat-file blob HEAD:s.key | head -c 8) == U2FsdGVk ]] || die 'v2 setup'
    printf '%s\n' "$PASSPHRASE" | "$CLI" migrate --password-stdin 2>/dev/null
    git commit -qm 'convert to v3'
    [[ $(git show HEAD:s.key | "$CLI" decrypt s.key) == 'v2 secret' ]] || die 'migrate'
    grep -qx 's.key transcrypt' .gitattributes || die 'v2 rule not converted'
    ok 'migrate converts a v2 checkout: rules, records and config'
fi

printf 'PASS: %d Bash client checks\n' "$PASS"

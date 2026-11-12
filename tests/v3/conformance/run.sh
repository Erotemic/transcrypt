#!/usr/bin/env bash
# Bash/Rust conformance: the portable client (contrib/v3/transcrypt-bash) and
# the Rust client (transcrypt-rs) on the same repositories, in both
# directions. Each case checks a user-visible outcome: identical Git
# objects, plaintext recovered by the other client, the same refusals.
#
#   bash tests/v3/conformance/run.sh [path/to/transcrypt-rs]
#
# Default binary: rust/target/release/transcrypt-rs (cargo build --release).
set -euo pipefail
export LC_ALL=C
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd -P)
SH=$ROOT/contrib/v3/transcrypt-bash
RS=${1:-${TRANSCRYPT_RS:-$ROOT/rust/target/release/transcrypt-rs}}
[[ -x $RS ]] || { echo "missing $RS: run (cd rust && cargo build --release) or pass the binary" >&2; exit 2; }
RS=$(cd -- "$(dirname -- "$RS")" && pwd -P)/$(basename -- "$RS")
SCRATCH=$(mktemp -d "${TMPDIR:-/tmp}/transcrypt-conformance.XXXXXXXX")
[[ -n ${KEEP-} ]] || [[ -n ${KEEP-} ]] || trap 'rm -rf -- "$SCRATCH"' EXIT
PASS=0
ok() { PASS=$((PASS + 1)); printf 'ok %d - %s\n' "$PASS" "$*"; }
die() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }
P1='correct horse battery staple'
P2='a second passphrase, long enough'
# Run a client quietly (its messages go to the log).
sh_() { "$SH" "$@" 2>>"$SCRATCH/log"; }
rs_() { "$RS" "$@" 2>>"$SCRATCH/log"; }
cfg() { git config user.email t@example.invalid; git config user.name Test; git config commit.gpgsign false; }
blobs() { git ls-files -s | sort; }
profile_byte() { head -c 7 .transcrypt/config | tail -c 1 | od -An -tx1 | tr -d ' \n'; }
remote() { rm -rf "$SCRATCH/$1.git"; git init -q --bare "$SCRATCH/$1.git"; }
clone() { rm -rf "$SCRATCH/$2"; git clone -q "$SCRATCH/$1.git" "$SCRATCH/$2" 2>/dev/null; cd "$SCRATCH/$2"; cfg; }
# A repository with protected and public files, set up by client $1 ("sh"
# or "rs") with profile $2, pushed to remote $3.
seed() {
    local client=$1 profile=$2 name=$3
    rm -rf "$SCRATCH/$name-seed"; mkdir "$SCRATCH/$name-seed"; cd "$SCRATCH/$name-seed"
    git init -q; cfg
    printf 'API_KEY=1\n' >.env
    mkdir -p 'sub dir' raw
    printf '\x00\x01\xff binary\x00\n' >raw/blob.bin
    : >empty.env
    printf 'unicode ✓\n' >'sub dir/clé.env'
    printf 'non-utf8\n' >"$(printf 'raw/\xff\xfe.env')"
    printf 'public\n' >README
    git add -A; git commit -qm start
    if [[ $client == sh ]]; then
        printf '%s\n' "$P1" | sh_ init --password-stdin "--profile=$profile" '*.env' 'raw/**'
    else
        printf '%s\n' "$P1" | rs_ init --password-stdin "--profile=$profile" '*.env' 'raw/**'
    fi
    git commit -qm 'enable v3'
    remote "$name"; git push -q "$SCRATCH/$name.git" master 2>/dev/null
}
# Every protected file at HEAD authenticates with both clients' audits.
audits() {
    sh_ audit "$@" || die "transcrypt-bash audit $*"
    rs_ audit "$@" || die "transcrypt-rs audit $*"
}

for profile in scrypt pbkdf2; do
    for first in sh rs; do
        second=$([[ $first == sh ]] && echo rs || echo sh)
        name=$first-$profile
        # ------------------------------------------------------------------
        # Setup by one client, unlock and edit with the other.
        # ------------------------------------------------------------------
        seed "$first" "$profile" "$name"
        seed_blobs=$(blobs)
        clone "$name" "$name-a"
        [[ $(head -c 4 .env) == TV3F ]] || die "$name: clone without filters should hold records"
        printf '%s\n' "$P1" | "${second}_" unlock --password-stdin
        [[ $(cat .env) == API_KEY=1 && $(cat "$(printf 'raw/\xff\xfe.env')") == non-utf8 ]] || die "$name: $second could not decrypt $first's records"
        cmp -s raw/blob.bin <(printf '\x00\x01\xff binary\x00\n') || die "$name: binary file"
        [[ ! -s empty.env ]] || die "$name: empty file"
        [[ -z $(git status --porcelain) ]] || die "$name: $second's clone is not clean after unlock"
        # Re-cleaning every file with the other client gives the same objects.
        git add --renormalize -A
        [[ $(blobs) == "$seed_blobs" ]] || die "$name: $second re-encrypts $first's files to different bytes"
        ok "$profile: $first sets up, $second unlocks a clone, decrypts every file and re-encrypts byte-identically"

        # Edit, rename and commit with the second client; the first reads it.
        printf 'API_KEY=2\n' >.env
        git add .env
        git mv 'sub dir/clé.env' 'sub dir/moved.env'
        git commit -qm "edit and rename by $second"
        audits HEAD
        git push -q origin master 2>/dev/null
        cd "$SCRATCH/$name-seed"
        git pull -q --no-rebase "$SCRATCH/$name.git" master 2>/dev/null
        [[ $(cat .env) == API_KEY=2 && $(cat 'sub dir/moved.env') == 'unicode ✓' ]] || die "$name: $first could not read $second's commit"
        [[ -z $(git status --porcelain) ]] || die "$name: $first's checkout not clean after pull"
        ok "$profile: $second edits and renames (re-encrypted for the new path by its hook), $first pulls and reads it; both audits pass"

        # Divergent branches merged by the first client. (An empty protected
        # file makes `git merge` die with "stash failed": a Git bug with any
        # clean filter that maps empty to non-empty content; see the guide.)
        git rm -qf empty.env
        printf 'line1\nline2\nline3\n' >notes.env; git add notes.env; git commit -qm notes; git push -q "$SCRATCH/$name.git" master
        cd "$SCRATCH/$name-a"; git pull -q --no-rebase origin master 2>/dev/null
        printf 'line1\nline2 by second\nline3\n' >notes.env; git commit -qam "second's edit"; git push -q origin master:side 2>/dev/null
        cd "$SCRATCH/$name-seed"
        printf 'line1\nline2\nline3\nline4 by first\n' >notes.env; git commit -qam "first's edit"
        git fetch -q "$SCRATCH/$name.git" side
        git merge -q --no-edit FETCH_HEAD 2>/dev/null || die "$name: merge of the two clients' branches"
        [[ $(cat notes.env) == $'line1\nline2 by second\nline3\nline4 by first' ]] || die "$name: merged plaintext"
        audits HEAD
        ok "$profile: branches edited by both clients merge cleanly through $first's merge driver"

        # Stored key files are interchangeable in one checkout.
        sh_ install
        [[ $(cat notes.env) == $'line1\nline2 by second\nline3\nline4 by first' ]] || die 'switch'
        printf 'switched\n' >>.env; git add .env
        printf '%s\n' "$P1" | rs_ unlock --password-stdin --no-hydrate
        git commit -qm 'commit through the other hooks'
        audits HEAD
        ok "$profile: one checkout switches clients without re-unlocking or re-encrypting"

        # Rekey by the second client; the first must unlock again.
        cd "$SCRATCH/$name-a"; git pull -q --no-rebase "$SCRATCH/$name-seed" master 2>/dev/null
        printf '%s\n' "$P2" | "${second}_" rekey --password-stdin
        git commit -qm "rekey by $second"
        git push -q "$SCRATCH/$name.git" HEAD:rekeyed 2>/dev/null
        cd "$SCRATCH/$name-seed"
        git pull -q --no-rebase "$SCRATCH/$name.git" rekeyed 2>/dev/null || true
        [[ $(head -c 4 .env) == TV3F ]] || die "$name: a stale key decrypted records of the new config"
        printf 'new plaintext\n' >.env
        if git add .env 2>/dev/null; then die "$name: plaintext stored with a stale key"; fi
        [[ $(git cat-file blob :.env | head -c 4) == TV3F ]] || die "$name: plaintext staged"
        git checkout -q -- .env 2>/dev/null || true
        printf '%s\n' "$P2" | "${first}_" unlock --password-stdin
        [[ $(head -c 4 .env) != TV3F && -z $(git status --porcelain) ]] || die "$name: $first after $second's rekey"
        audits HEAD
        ok "$profile: $second rekeys; $first refuses to encrypt with the stale key, then unlocks with the new passphrase"
    done
done

# --------------------------------------------------------------------------
# Profile 1: Rust only. Bash names it and changes nothing.
# --------------------------------------------------------------------------
seed rs argon2id p1
clone p1 p1-a
before=$(git status --porcelain; blobs; git config --list --local | sort)
if printf '%s\n' "$P1" | "$SH" unlock --password-stdin >"$SCRATCH/p1.log" 2>&1; then die 'Bash unlocked profile 1'; fi
grep -q 'profile 1' "$SCRATCH/p1.log" || die 'profile 1 refusal is not named'
[[ ! -e .git/transcrypt-v3/key && $(git status --porcelain; blobs; git config --list --local | sort) == "$before" ]] || die 'Bash changed a profile-1 repository'
if "$SH" install >/dev/null 2>&1; then die 'Bash installed filters for profile 1'; fi
# Even a filter wired to the portable client by hand stores no plaintext.
git config filter.transcrypt-v3.clean "$(printf '%q' "$SH") clean %f"; git config filter.transcrypt-v3.required true
printf 'leak\n' >.env
if git add .env 2>/dev/null; then die 'a profile-1 file was staged through the portable client'; fi
[[ $(git cat-file blob :.env | head -c 4) == TV3F ]] || die 'plaintext staged'
git config --remove-section filter.transcrypt-v3
git checkout -q -- .env
"$SH" status | grep -q 'profile 1' || die 'status should describe profile 1'
ok 'profile 1: Bash names it, refuses unlock/install/clean, and changes nothing'
# Converting with Rust makes the repository portable.
printf '%s\n' "$P1" | rs_ unlock --password-stdin
printf '%s\n' "$P2" | rs_ rekey --password-stdin --profile=scrypt
git commit -qm 'convert to profile 2'
[[ $(profile_byte) == 02 ]] || die 'conversion'
cd "$SCRATCH"; rm -rf p1-b; git clone -q "$SCRATCH/p1-a" p1-b 2>/dev/null; cd p1-b; cfg
printf '%s\n' "$P2" | sh_ unlock --password-stdin
[[ $(cat .env) == API_KEY=1 ]] || die 'Bash after conversion'
"$SH" audit HEAD~1 2>&1 | grep -q 'envelope only' || die 'Bash audit of the profile-1 commit should be keyless'
ok 'profile 1 converted to 2 by Rust (rekey --profile=scrypt); Bash then unlocks it and audits the old commit keylessly'

# --------------------------------------------------------------------------
# Refusals both clients share.
# --------------------------------------------------------------------------
seed sh scrypt refusals
for client in sh rs; do
    clone refusals "refusals-$client"
    bin=$([[ $client == sh ]] && echo "$SH" || echo "$RS")
    if printf 'wrong passphrase, long enough\n' | "$bin" unlock --password-stdin >/dev/null 2>&1; then die "$client: wrong passphrase"; fi
    [[ ! -e .git/transcrypt-v3/key ]] || die "$client: wrong passphrase stored a key"
    printf '%s\n' "$P1" | "$bin" unlock --password-stdin 2>/dev/null
    # A record copied to another path.
    oid=$(git rev-parse :.env)
    git update-index --add --cacheinfo "100644,$oid,copy.env"
    if "$bin" verify-index >/dev/null 2>&1; then die "$client: record at a foreign path accepted"; fi
    git rm -q --cached copy.env
    # A tampered record.
    git cat-file blob "$oid" >"$SCRATCH/rec"
    size=$(wc -c <"$SCRATCH/rec")
    { head -c 30 "$SCRATCH/rec"; printf '\x5a'; tail -c "+32" "$SCRATCH/rec"; } >"$SCRATCH/bad"
    bad=$(git hash-object -w --no-filters "$SCRATCH/bad")
    git update-index --cacheinfo "100644,$bad,.env"
    if "$bin" verify-index >/dev/null 2>&1; then die "$client: tampered record accepted"; fi
    if git -c core.hooksPath=/dev/null commit -qm tampered >/dev/null 2>&1 && "$bin" audit HEAD >/dev/null 2>&1; then die "$client: audit accepted a tampered commit"; fi
    git reset -q --hard origin/master 2>/dev/null
    # An unknown profile byte: refused before anything changes.
    { head -c 6 .transcrypt/config; printf '\x07'; tail -c +8 .transcrypt/config; } >"$SCRATCH/cfg7"
    cp "$SCRATCH/cfg7" .transcrypt/config
    if printf '%s\n' "$P1" | "$bin" unlock --password-stdin >"$SCRATCH/u.log" 2>&1; then die "$client: unknown profile unlocked"; fi
    grep -q 'profile 7' "$SCRATCH/u.log" || die "$client: unknown profile not named"
    git checkout -q -- .transcrypt/config
    ok "$client: wrong passphrase, foreign-path record, tampered record, tampered commit and unknown profile refused"
done

# Pre-push: a plaintext intermediate commit is refused by both clients' hooks.
for client in sh rs; do
    clone refusals "push-$client"
    bin=$([[ $client == sh ]] && echo "$SH" || echo "$RS")
    printf '%s\n' "$P1" | "$bin" unlock --password-stdin 2>/dev/null
    printf 'leak\n' >.env
    git -c filter.transcrypt-v3.clean=cat -c filter.transcrypt-v3.process= -c filter.transcrypt-v3.required=false add .env
    git -c core.hooksPath=/dev/null commit -qm 'plaintext, hooks bypassed'
    printf 'fixed\n' >.env; git add .env; git commit -qm fixed
    if git push -q origin master 2>/dev/null; then die "$client: pre-push accepted an intermediate plaintext commit"; fi
    if "$SH" audit origin/master..HEAD >/dev/null 2>&1; then die 'Bash audit missed the plaintext commit'; fi
    if "$RS" audit origin/master..HEAD >/dev/null 2>&1; then die 'Rust audit missed the plaintext commit'; fi
    ok "$client: pre-push refuses a plaintext commit hidden behind a later fix; both audits flag it"
done

# --------------------------------------------------------------------------
# v2 migration by Bash, used by Rust (and the reverse).
# --------------------------------------------------------------------------
V2=$ROOT/transcrypt
for client in sh rs; do
    rm -rf "$SCRATCH/mig-$client"; mkdir "$SCRATCH/mig-$client"; cd "$SCRATCH/mig-$client"
    git init -q; cfg
    printf 'v2 secret\n' >s.key; printf 'x\n' >plain.txt
    git add s.key plain.txt; git commit -qm init
    "$V2" -c aes-256-cbc -p v2-password -y >/dev/null 2>&1
    printf 's.key filter=crypt diff=crypt merge=crypt\n' >.gitattributes
    git add .gitattributes; git add --renormalize s.key; git commit -qm 'v2 protect'
    if [[ $client == sh ]]; then printf '%s\n' "$P1" | sh_ migrate --password-stdin
    else printf '%s\n' "$P1" | rs_ migrate --password-stdin --profile=pbkdf2; fi
    git commit -qm 'convert to v3'
    other=$([[ $client == sh ]] && echo "$RS" || echo "$SH")
    cd "$SCRATCH"; rm -rf "mig-$client-clone"; git clone -q "mig-$client" "mig-$client-clone" 2>/dev/null; cd "mig-$client-clone"; cfg
    printf '%s\n' "$P1" | "$other" unlock --password-stdin 2>/dev/null
    [[ $(cat s.key) == 'v2 secret' ]] || die "$client migration not readable by the other client"
    ok "v2 migration by $client; a fresh clone unlocks with the other client"
done

printf 'PASS: %d conformance checks (transcrypt-bash vs %s)\n' "$PASS" "$RS"

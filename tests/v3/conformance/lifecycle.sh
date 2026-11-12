#!/usr/bin/env bash
# Lifecycle conformance of the two v3 clients (contrib/v3/transcrypt-bash
# and transcrypt-rs) beyond run.sh:
#
#   1. History rewriting across clients: rebase (clean and conflicted),
#      cherry-pick (clean and conflicted) and stash (including untracked
#      files), each done by one client and read, verified and audited by the
#      other.
#   2. Interruption: init, rekey, migrate, lock and unlock are killed (SIGKILL of
#      the whole process group) right before their k-th call of `git`, and of
#      `openssl` for the Bash client, for every k until the operation
#      completes; and, separately, that call is made to fail instead. After
#      every fault: no plaintext of a protected file in any Git object or in
#      $TMPDIR, an operation reported as successful really succeeded, and the
#      documented recovery (with either client) reaches a clean, verified,
#      audited state with every secret intact.
#   3. Recovery from a missing or damaged stored key and a wrong passphrase.
#
#   bash tests/v3/conformance/lifecycle.sh [path/to/transcrypt-rs]
#
# LIFECYCLE_FAULTS=quick checks every third fault point only (faster).
# LIFECYCLE_SECTIONS, LIFECYCLE_OPS and LIFECYCLE_CLIENTS select a subset
# (defaults "1 2 3", "init rekey lock unlock migrate" and "sh rs").
set -euo pipefail
export LC_ALL=C
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd -P)
SH=$ROOT/contrib/v3/transcrypt-bash
RS=${1:-${TRANSCRYPT_RS:-$ROOT/rust/target/release/transcrypt-rs}}
[[ -x $RS ]] || { echo "missing $RS: run (cd rust && cargo build --release) or pass the binary" >&2; exit 2; }
RS=$(cd -- "$(dirname -- "$RS")" && pwd -P)/$(basename -- "$RS")
V2=$ROOT/transcrypt
SCRATCH=$(mktemp -d "${TMPDIR:-/tmp}/transcrypt-lifecycle.XXXXXXXX")
[[ -n ${KEEP-} ]] || trap 'rm -rf -- "$SCRATCH"' EXIT
# Independent of the caller's Git configuration (see run.sh).
export HOME=$SCRATCH/home GIT_CONFIG_NOSYSTEM=1
unset XDG_CONFIG_HOME GIT_CONFIG_GLOBAL GIT_CONFIG_SYSTEM GIT_CONFIG_COUNT GIT_CONFIG_PARAMETERS \
    GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES GIT_NAMESPACE GIT_CEILING_DIRECTORIES
mkdir -p "$HOME"
BRANCH=${TRANSCRYPT_TEST_BRANCH:-main}
git config --global init.defaultBranch "$BRANCH"
git config --global user.email t@example.invalid
git config --global user.name Test
git config --global commit.gpgsign false
SECTIONS=" ${LIFECYCLE_SECTIONS:-1 2 3} "
OPS=${LIFECYCLE_OPS:-init rekey lock unlock migrate}
CLIENTS=${LIFECYCLE_CLIENTS:-sh rs}
PASS=0
ok() { PASS=$((PASS + 1)); printf 'ok %d - %s\n' "$PASS" "$*"; }
die() { printf 'FAIL: %s\n' "$*" >&2; [[ -s $SCRATCH/log ]] && tail -n 5 "$SCRATCH/log" >&2; exit 1; }
P1='correct horse battery staple'
P2='a second passphrase, long enough'
cli() { [[ $1 == sh ]] && printf %s "$SH" || printf %s "$RS"; }
otherof() { [[ $1 == sh ]] && echo rs || echo sh; }
run() { local c; c=$(cli "$1"); shift; "$c" "$@" 2>>"$SCRATCH/log"; }
# Every protected secret in these repositories contains MARK-; none may
# ever appear in a Git object (nothing was committed before protection).
leaks() { git cat-file --batch-all-objects --batch 2>/dev/null | grep -c 'MARK-' || true; }
no_leaks() { [[ $(leaks) == 0 ]] || die "$1: plaintext of a protected file in a Git object"; }
verified() {
    "$SH" verify-index 2>>"$SCRATCH/log" || die "$1: transcrypt-bash verify-index"
    "$RS" verify-index 2>>"$SCRATCH/log" || die "$1: transcrypt-rs verify-index"
}
audited() {
    "$SH" audit "${@:2}" >/dev/null 2>>"$SCRATCH/log" || die "$1: transcrypt-bash audit ${*:2}"
    "$RS" audit "${@:2}" >/dev/null 2>>"$SCRATCH/log" || die "$1: transcrypt-rs audit ${*:2}"
}
clean() { [[ -z $(git status --porcelain) ]] || die "$1: not clean: $(git status --porcelain | tr '\n' ' ')"; }
# Switch this checkout's filters and hooks to client $1 (transcrypt-rs
# installs them with unlock, which reuses the stored key once it authenticates).
use_client() {
    if [[ $1 == sh ]]; then run sh install; else printf '%s\n' "$P1" | run rs unlock --password-stdin; fi
}
has() { [[ $(cat -- "$2") == "$3" ]] || die "$1: $2 is '$(head -c 40 -- "$2")', expected '$3'"; }

# A repository with two protected files, set up by client $1, unlocked.
v3repo() {
    local client=$1 dir=$2
    rm -rf "$dir"; mkdir -p "$dir"; cd "$dir"; git init -q
    printf 'public\n' >README; git add README; git commit -qm seed
    printf '%s\n' "$P1" | run "$client" init --password-stdin --profile=scrypt '*.env'
    printf 'MARK-A-1\nline 2\nline 3\n' >a.env; mkdir -p d; printf 'MARK-B-1\n' >d/b.env
    git add -A; git commit -qm secrets
}

# ---------------------------------------------------------------------------
# 1. History rewriting across clients.
# ---------------------------------------------------------------------------
for x in $CLIENTS; do
    [[ $SECTIONS == *' 1 '* ]] || break
    y=$(otherof "$x")
    v3repo "$x" "$SCRATCH/hist-$x-seed"
    rm -rf "$SCRATCH/hist-$x.git"; git init -q --bare "$SCRATCH/hist-$x.git"
    git push -q "$SCRATCH/hist-$x.git" "$BRANCH" 2>/dev/null
    for c in "$x" "$y"; do
        rm -rf "$SCRATCH/hist-$x-$c"; git clone -q "$SCRATCH/hist-$x.git" "$SCRATCH/hist-$x-$c" 2>/dev/null
        cd "$SCRATCH/hist-$x-$c"; printf '%s\n' "$P1" | run "$c" unlock --password-stdin
    done

    # Rebase by $x onto commits pushed by $y, without and with a conflict.
    cd "$SCRATCH/hist-$x-$y"
    printf 'MARK-A-1\nline 2\nline 3 by %s\n' "$y" >a.env; git commit -qam "$y: line 3"
    git push -q origin "$BRANCH" 2>/dev/null
    cd "$SCRATCH/hist-$x-$x"
    printf 'MARK-A-1 by %s\nline 2\nline 3\n' "$x" >a.env; git commit -qam "$x: line 1"
    printf 'MARK-N-1\n' >n.env; git add n.env; git commit -qm "$x: new secret"
    git fetch -q origin 2>/dev/null
    git rebase -q "origin/$BRANCH" 2>>"$SCRATCH/log" || die "$x: rebase onto $y's commit"
    has "$x rebase" a.env "MARK-A-1 by $x"$'\nline 2\nline 3 by '"$y"
    verified "$x rebase"; clean "$x rebase"
    git push -q origin "$BRANCH" 2>>"$SCRATCH/log" || die "$x: pre-push refused the rebased commits"
    cd "$SCRATCH/hist-$x-$y"; git pull -q --ff-only 2>/dev/null
    has "$y reads $x's rebase" a.env "MARK-A-1 by $x"$'\nline 2\nline 3 by '"$y"; has "$y reads $x's rebase" n.env MARK-N-1
    verified "$y after rebase"; clean "$y after rebase"; audited "$y after rebase" "$BRANCH"
    git add --renormalize .
    [[ -z $(git status --porcelain) ]] || die "$y re-encrypts $x's rebased records differently"
    # Conflicting rebase: both edit line 2.
    printf 'MARK-A-1 by %s\nline 2 by %s\nline 3 by %s\n' "$x" "$y" "$y" >a.env; git commit -qam "$y: line 2"
    git push -q origin "$BRANCH" 2>/dev/null
    cd "$SCRATCH/hist-$x-$x"
    printf 'MARK-A-1 by %s\nline 2 by %s\nline 3 by %s\n' "$x" "$x" "$y" >a.env; git commit -qam "$x: line 2"
    git fetch -q origin 2>/dev/null
    if git rebase -q "origin/$BRANCH" >/dev/null 2>&1; then die "$x: conflicting rebase did not stop"; fi
    grep -q '^<<<<<<<' a.env || die "$x: rebase conflict markers missing from the plaintext"
    [[ $(git cat-file blob :2:a.env | head -c 4) == TV3F && $(git cat-file blob :3:a.env | head -c 4) == TV3F ]] \
        || die "$x: rebase conflict stages are not records"
    printf 'MARK-A-1 by %s\nline 2 resolved\nline 3 by %s\n' "$x" "$y" >a.env; git add a.env
    GIT_EDITOR=true git rebase --continue >/dev/null 2>>"$SCRATCH/log" || die "$x: rebase --continue"
    verified "$x conflicted rebase"; clean "$x conflicted rebase"
    git push -q origin "$BRANCH" 2>>"$SCRATCH/log" || die "$x: pre-push refused the resolved rebase"
    cd "$SCRATCH/hist-$x-$y"; git pull -q --ff-only 2>/dev/null
    has "$y reads $x's resolution" a.env "MARK-A-1 by $x"$'\nline 2 resolved\nline 3 by '"$y"
    verified "$y after conflicted rebase"; audited "$y after conflicted rebase" "$BRANCH"
    ok "$x rebases onto $y's commits (clean, then conflicted and resolved in plaintext); $y reads, verifies and audits"

    # Cherry-pick by $y of $x's commits on a side branch.
    cd "$SCRATCH/hist-$x-$x"
    git checkout -q -b side
    printf 'MARK-B-2 side\n' >d/b.env; git commit -qam "side: b"
    printf 'MARK-A-1 by %s\nline 2 side\nline 3 by %s\n' "$x" "$y" >a.env; git commit -qam "side: a"
    git push -q origin side 2>/dev/null
    git checkout -q "$BRANCH"
    cd "$SCRATCH/hist-$x-$y"; git fetch -q origin 2>/dev/null
    git cherry-pick "origin/side~1" >/dev/null 2>>"$SCRATCH/log" || die "$y: cherry-pick"
    has "$y cherry-pick" d/b.env 'MARK-B-2 side'
    [[ $(git rev-parse HEAD:d/b.env) == $(git rev-parse origin/side~1:d/b.env) ]] \
        || die "$y: cherry-picked record differs from the original (encryption is deterministic)"
    printf 'MARK-A-1 by %s\nline 2 main\nline 3 by %s\n' "$x" "$y" >a.env; git commit -qam "$y: line 2 main"
    if git cherry-pick origin/side >/dev/null 2>&1; then die "$y: conflicting cherry-pick did not stop"; fi
    grep -q '^<<<<<<<' a.env || die "$y: cherry-pick conflict markers missing"
    printf 'MARK-A-1 by %s\nline 2 both\nline 3 by %s\n' "$x" "$y" >a.env; git add a.env
    GIT_EDITOR=true git cherry-pick --continue >/dev/null 2>>"$SCRATCH/log" || die "$y: cherry-pick --continue"
    verified "$y cherry-pick"; clean "$y cherry-pick"
    git push -q origin "$BRANCH" 2>>"$SCRATCH/log" || die "$y: pre-push refused the cherry-picks"
    cd "$SCRATCH/hist-$x-$x"; git pull -q --ff-only 2>/dev/null
    has "$x reads $y's cherry-pick" a.env "MARK-A-1 by $x"$'\nline 2 both\nline 3 by '"$y"
    has "$x reads $y's cherry-pick" d/b.env 'MARK-B-2 side'
    verified "$x after cherry-pick"; audited "$x after cherry-pick" "$BRANCH"
    ok "$y cherry-picks $x's commits (byte-identical record; conflict resolved in plaintext); $x reads and audits"

    # Stash by $x (staged, unstaged and untracked protected changes), popped
    # by $y in the same checkout.
    cd "$SCRATCH/hist-$x-$x"
    printf 'MARK-A-3 unstaged\n' >a.env
    printf 'MARK-B-3 staged\n' >d/b.env; git add d/b.env
    printf 'MARK-U-1 untracked\n' >u.env
    run "$x" status >/dev/null
    git stash push -q -u 2>>"$SCRATCH/log" || die "$x: git stash -u"
    has "$x stash" d/b.env 'MARK-B-2 side'; [[ ! -e u.env ]] || die "$x: stash left the untracked file"
    no_leaks "$x stash"
    for rev in 'stash@{0}' 'stash@{0}^2' 'stash@{0}^3'; do
        git ls-tree -r --name-only "$rev" | grep '\.env$' | while IFS= read -r p; do
            [[ $(git cat-file blob "$rev:$p" | head -c 4) == TV3F ]] || die "$x: $rev:$p is not a record"
        done
    done
    use_client "$y"
    git stash pop -q --index 2>>"$SCRATCH/log" || die "$y: git stash pop --index"
    has "$y stash pop" a.env 'MARK-A-3 unstaged'; has "$y stash pop" d/b.env 'MARK-B-3 staged'
    has "$y stash pop" u.env 'MARK-U-1 untracked'
    [[ -n $(git diff --cached --name-only -- d/b.env) && -z $(git diff --cached --name-only -- a.env) ]] \
        || die "$y: stash pop --index did not restore what was staged"
    git add -A; git commit -qm "$y: commits the stashed work"
    verified "$y after stash"; clean "$y after stash"; no_leaks "$y after stash"
    git push -q origin "$BRANCH" 2>>"$SCRATCH/log" || die "$y: pre-push refused the stashed work"
    cd "$SCRATCH/hist-$x-$y"; git pull -q --ff-only 2>/dev/null
    has "$y reads the stashed work" u.env 'MARK-U-1 untracked'; audited "after stash" "$BRANCH"
    ok "$x stashes staged, unstaged and untracked protected changes as records; $y pops, commits and pushes them"
done

# ---------------------------------------------------------------------------
# 2. Interruption: a fault at every call of git (and openssl).
# ---------------------------------------------------------------------------
mkdir -p "$SCRATCH/bin"
for tool in git openssl; do
    real=$(command -v "$tool")
    cat >"$SCRATCH/bin/$tool" <<EOF
#!/bin/sh
if [ "\${FAULT_TOOL-}" = $tool ]; then
    n=\$(( \$(cat "\$FAULT_COUNTER" 2>/dev/null || echo 0) + 1 ))
    echo "\$n" >"\$FAULT_COUNTER"
    if [ "\$n" -eq "\$FAULT_AT" ]; then
        printf '%s\n' "\$*" >"\$FAULT_COUNTER.hit"
        [ "\$FAULT_MODE" = crash ] && kill -KILL 0
        echo 'injected failure' >&2
        exit 1
    fi
fi
exec '$real' "\$@"
EOF
    chmod +x "$SCRATCH/bin/$tool"
done
export PATH=$SCRATCH/bin:$PATH
STRIDE=1; [[ ${LIFECYCLE_FAULTS-} == quick ]] && STRIDE=3
FAULTS=0

# Templates, set up once: a v3 repository by each client, unlocked and
# locked; a Bash transcrypt (v2) checkout, unlocked.
for x in sh rs; do
    v3repo "$x" "$SCRATCH/tpl-$x-unlocked"
    rm -rf "$SCRATCH/tpl-$x-locked"; cp -a "$SCRATCH/tpl-$x-unlocked" "$SCRATCH/tpl-$x-locked"
    (cd "$SCRATCH/tpl-$x-locked" && run "$x" lock)
done
rm -rf "$SCRATCH/tpl-v2"; mkdir "$SCRATCH/tpl-v2"; cd "$SCRATCH/tpl-v2"; git init -q
printf 'public\n' >README; git add README; git commit -qm seed
"$V2" -c aes-256-cbc -p v2-password -y >/dev/null 2>&1
printf '*.key filter=crypt diff=crypt merge=crypt\n' >.gitattributes; git add .gitattributes; git commit -qm 'v2 rules'
printf 'MARK-K-1\n' >s.key; mkdir -p d; printf 'MARK-K-2\n' >d/t.key; git add -A; git commit -qm 'v2 secrets'
[[ $(git cat-file blob HEAD:s.key | head -c 8) == U2FsdGVk ]] || die 'v2 template: not v2 ciphertext'

# What every protected file must hold once a repository is recovered.
# A plain repository whose secrets are not committed yet (for init).
rm -rf "$SCRATCH/tpl-plain"; mkdir "$SCRATCH/tpl-plain"; cd "$SCRATCH/tpl-plain"; git init -q
printf 'public\n' >README; git add README; git commit -qm seed
printf 'MARK-A-1\nline 2\nline 3\n' >a.env; mkdir -p d; printf 'MARK-B-1\n' >d/b.env

expect_plain() {
    if [[ $1 == v2 ]]; then has "$2" s.key MARK-K-1; has "$2" d/t.key MARK-K-2
    else has "$2" a.env $'MARK-A-1\nline 2\nline 3'; has "$2" d/b.env MARK-B-1; fi
}
staged_config_differs() { [[ $(git rev-parse -q --verify :.transcrypt/config) != "$(git rev-parse -q --verify HEAD:.transcrypt/config)" ]]; }

# Recovery after a faulted operation $op by client $x (rc $rc); recovery
# steps run with client $r. These are the documented steps.
recover() {
    local op=$1 x=$2 r=$3 rc=$4 at=$5 undo=$6
    # A crash inside a Git command the client ran (one that ran a filter)
    # leaves Git's own index.lock: Git says to remove it, nothing else.
    [[ ! -e .git/index.lock ]] || rm -f .git/index.lock
    case $op in
    rekey)
        if ((rc == 0)); then
            # Reported as done: staged, in the worktree, and the key in use.
            staged_config_differs || die "$at: rekey reported success but staged nothing"
            [[ $(git rev-parse :.transcrypt/config) == $(git hash-object .transcrypt/config) ]] \
                || die "$at: rekey reported success but the worktree config is not the staged one"
            [[ $(run "$r" status) == *'key:        unlocked'* ]] || die "$at: rekey reported success but the new key is not in use"
            verified "$at"; git commit -qm rekey 2>>"$SCRATCH/log" || die "$at: commit the rekey"
        fi
        if ((rc != 0)) && staged_config_differs \
            && [[ $(git rev-parse :.transcrypt/config) != "$(git hash-object .transcrypt/config)" ]]; then
            [[ $(run sh status) == *'interrupted rekey'* && $(run rs status) == *'interrupted rekey'* ]] \
                || die "$at: status does not report the interrupted rekey"
        fi
        if ((rc == 0)); then
            :
        elif staged_config_differs && ((undo)); then
            # Undo the staged rekey (as status says): the index and the
            # config from HEAD without a refresh (no filter runs under the
            # stale key), then the old passphrase.
            git read-tree HEAD; git checkout -q HEAD -- .transcrypt/config
            printf '%s\n' "$P1" | run "$r" unlock --password-stdin || die "$at: unlock with the old passphrase after undoing"
        elif staged_config_differs; then
            # Finish it: the staged config in the worktree, the new passphrase.
            if [[ $(git rev-parse :.transcrypt/config) != "$(git hash-object .transcrypt/config)" ]]; then
                git checkout -q -- .transcrypt/config
            fi
            printf '%s\n' "$P2" | run "$r" unlock --password-stdin || die "$at: unlock with the new passphrase to finish"
            verified "$at finished"; expect_plain v3 "$at finished"
            git commit -qm rekey 2>>"$SCRATCH/log" || die "$at: commit the finished rekey"
        else
            ((rc != 0)) || die "$at: rekey reported success but staged nothing"
            [[ $(git hash-object .transcrypt/config) == $(git rev-parse HEAD:.transcrypt/config) ]] \
                || die "$at: worktree config changed although no rekey is staged"
            printf '%s\n' "$P1" | run "$r" unlock --password-stdin || die "$at: unlock with the old passphrase"
        fi
        ;;
    lock) ((rc == 0)) || run "$r" lock || die "$at: lock again" ;;
    unlock) ((rc == 0)) || printf '%s\n' "$P1" | run "$r" unlock --password-stdin || die "$at: unlock again" ;;
    init | migrate)
        # Rerunning an interrupted init or migrate, with the same
        # passphrase, completes it (by either client).
        if ((rc != 0)); then
            printf '%s\n' "$P1" | run "$r" "$op" --password-stdin --profile=scrypt ${INIT_PATTERN[@]+"${INIT_PATTERN[@]}"} \
                || die "$at: rerunning $op does not complete it"
        fi
        git add -A
        git commit -qm "$op" 2>>"$SCRATCH/log" || die "$at: commit after $op"
        ;;
    esac
    case $op in
    lock)
        [[ ! -e .git/transcrypt-v3/key ]] || die "$at: key still stored after lock"
        [[ $(git rev-parse :a.env) == $(git hash-object --no-filters a.env) ]] || die "$at: a.env is not its record after lock"
        printf '%s\n' "$P1" | run "$(otherof "$r")" unlock --password-stdin || die "$at: the other client unlocks"
        ;;
    esac
    expect_plain "$([[ $op == migrate ]] && echo v2 || echo v3)" "$at recovered"
    verified "$at recovered"; clean "$at recovered"; audited "$at recovered" HEAD; no_leaks "$at recovered"
}

# Run $op by client $x with a fault ($mode) at the k-th call of $tool, for
# every k until the operation completes, and check each outcome.
faults() {
    local x=$1 op=$2 tool=$3 mode=$4 k=1 rc tpl hit r undo
    POINTS=0
    INIT_PATTERN=()
    case $op in
    unlock) tpl=$SCRATCH/tpl-$x-locked ;;
    migrate) tpl=$SCRATCH/tpl-v2 ;;
    init) tpl=$SCRATCH/tpl-plain INIT_PATTERN=('*.env') ;;
    *) tpl=$SCRATCH/tpl-$x-unlocked ;;
    esac
    local input='' args=("$op" --password-stdin)
    case $op in
    rekey) input=$P2 ;;
    unlock) input=$P1 ;;
    migrate) input=$P1 args+=(--profile=scrypt) ;;
    init) input=$P1 args+=(--profile=scrypt '*.env') ;;
    lock) args=(lock) ;;
    esac
    while :; do
        rm -rf "$SCRATCH/f" "$SCRATCH/ftmp" "$SCRATCH/counter" "$SCRATCH/counter.hit"
        cp -a "$tpl" "$SCRATCH/f"; mkdir "$SCRATCH/ftmp"; cd "$SCRATCH/f"
        rc=0
        printf '%s\n' "$input" | FAULT_TOOL=$tool FAULT_MODE=$mode FAULT_AT=$k FAULT_COUNTER=$SCRATCH/counter TMPDIR=$SCRATCH/ftmp \
            perl -e 'setpgrp(0, 0); exec @ARGV or die' -- "$(cli "$x")" "${args[@]}" \
            >/dev/null 2>>"$SCRATCH/log" || rc=$?
        if [[ ! -e $SCRATCH/counter.hit ]]; then
            ((rc == 0)) || die "$x $op: failed without a fault ($rc)"
            break
        fi
        hit=$(head -c 60 "$SCRATCH/counter.hit")
        local at="$x $op, $mode at $tool call $k ($hit)"
        # (During migrate Git still runs Bash transcrypt v2's own filters,
        # whose mktemp files a crash leaves in $TMPDIR: v2's behavior.)
        local left ignore=()
        [[ $op == migrate ]] && ignore=(-name 'tmp.*' -prune -o)
        left=$(find "$SCRATCH/ftmp" -mindepth 1 ${ignore[@]+"${ignore[@]}"} -print | head -n 3)
        [[ -z $left ]] || die "$at: files left in \$TMPDIR: $(tr '\n' ' ' <<<"$left")"
        no_leaks "$at"
        # Alternate which client recovers, and finishing or undoing a rekey.
        r=$x; ((k % 2)) || r=$(otherof "$x")
        undo=$(((k / 2) % 2))
        recover "$op" "$x" "$r" "$rc" "$at" "$undo"
        POINTS=$((POINTS + 1)); FAULTS=$((FAULTS + 1))
        k=$((k + STRIDE))
        ((k < 400)) || die "$x $op: more than 400 $tool calls"
    done
    cd "$SCRATCH"
}

for x in $CLIENTS; do
    [[ $SECTIONS == *' 2 '* ]] || break
    for op in $OPS; do
        n=''
        for mode in crash fail; do
            for tool in git openssl; do
                [[ $tool == openssl && $x == rs ]] && continue
                faults "$x" "$op" "$tool" "$mode"
                n+="$mode/$tool $POINTS, "
            done
        done
        ok "$x $op: interrupted (crash) or failing at every call, then recovered: ${n%, } fault points"
    done
done

# ---------------------------------------------------------------------------
# 3. Recovery from a damaged or missing stored key, and a wrong passphrase.
# ---------------------------------------------------------------------------
for x in $CLIENTS; do
    [[ $SECTIONS == *' 3 '* ]] || break
    y=$(otherof "$x")
    rm -rf "$SCRATCH/k"; cp -a "$SCRATCH/tpl-$x-unlocked" "$SCRATCH/k"; cd "$SCRATCH/k"
    key=.git/transcrypt-v3/key
    cp "$key" "$SCRATCH/key.good"
    # Wrong passphrase on a locked checkout: refused, nothing changes. (An
    # unlocked transcrypt-rs reuses its authenticated stored key and does
    # not ask.)
    run "$x" lock
    cp a.env "$SCRATCH/a.locked"
    if printf 'not the passphrase at all\n' | run "$x" unlock --password-stdin; then die "$x: wrong passphrase accepted"; fi
    [[ ! -e $key ]] || die "$x: a wrong passphrase stored a key"
    cmp -s a.env "$SCRATCH/a.locked" || die "$x: a wrong passphrase changed the worktree"
    printf '%s\n' "$P1" | run "$x" unlock --password-stdin
    cmp -s "$key" "$SCRATCH/key.good" || die "$x: unlock stored a different key"
    expect_plain v3 "$x wrong passphrase"; clean "$x wrong passphrase"
    # Damaged key file (one byte of the key changed): refused, never used,
    # with each client's filters installed.
    damage() { printf '\x00' | dd of="$key" bs=1 seek=60 conv=notrunc 2>/dev/null; }
    printf 'MARK-A-9\n' >a.env
    for c in sh rs; do
        use_client "$c"
        damage
        [[ $(run "$c" status) == *'does not match'* ]] || die "$c: status does not report the damaged key"
        if git -c core.hooksPath=/dev/null add a.env 2>/dev/null && [[ $(git cat-file blob :a.env | head -c 4) != TV3F ]]; then
            die "$c: staged plaintext with a damaged key"
        fi
        git reset -q -- a.env 2>/dev/null || true
    done
    no_leaks "$x damaged key"
    damage
    printf '%s\n' "$P1" | run "$y" unlock --password-stdin || die "$y: unlock repairs a damaged key"
    cmp -s "$key" "$SCRATCH/key.good" || die "$y: unlock did not restore the key file"
    git checkout -q -- a.env; clean "$x damaged key repaired"
    # Missing key file: locked; unlock restores it.
    rm -f "$key"
    [[ $(run "$y" status) == *'key:        locked'* ]] || die "$y: status with the key file removed"
    printf '%s\n' "$P1" | run "$x" unlock --password-stdin || die "$x: unlock after the key was removed"
    expect_plain v3 "$x key removed"; verified "$x key removed"; clean "$x key removed"
    ok "$x/$y: a wrong passphrase changes nothing; a damaged or removed key is reported, never used, and unlock restores it"
done

printf 'PASS: %d lifecycle checks, %d faults injected (transcrypt-bash vs %s)\n' "$PASS" "$FAULTS" "$RS"

#!/usr/bin/env bash
# Time the pre-commit hook and `verify-index` on large repositories, the
# scenarios of docs/verification/V3-HANDOFF.md ("Performance"):
#
#   scripts/bench-hook.sh [BIN] [RUNS]
#
#   BIN   the transcrypt-rs binary to time (default: rust/target/release/
#         transcrypt-rs; build it with `cargo build --release`)
#   RUNS  repetitions of each timed step; the median is reported (default 5)
#
# Scenarios, each in a fresh repository under a temporary directory:
#   1. 10 000 files, 300 protected (unlocked): a commit of one unprotected
#      edit, of one protected edit, of a `git mv` of a protected file, and
#      `git status`;
#   2. 60 000 unprotected files, all rewritten and staged: `verify-index`;
#   3. a locked `verify-index` of a merge bringing 10 000 protected files.
# Prints one line per step: its name and the median wall time in seconds.
set -euo pipefail
shopt -s inherit_errexit

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
bin=$(realpath "${1:-$root/rust/target/release/transcrypt-rs}")
runs=${2:-5}
[ -x "$bin" ] || {
	echo "bench-hook: no binary at $bin" >&2
	exit 2
}
pass='long correct horse battery staple benchmark passphrase'
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Median wall time of RUNS runs of the function SETUP (untimed) then the
# function STEP, in seconds.
median() {
	local name=$1 setup=$2 step=$3 times=() run start end
	for ((run = 0; run < runs; run++)); do
		"$setup" >/dev/null 2>&1
		start=$(date +%s.%N)
		"$step" >/dev/null 2>&1
		end=$(date +%s.%N)
		times+=("$(echo "$end - $start" | bc)")
	done
	printf '%-44s %s\n' "$name" "$(printf '%s\n' "${times[@]}" | sort -n | sed -n "$(((runs + 1) / 2))p")"
}

# A repository with FILES files, PROTECTED of them `*.secret`, committed.
repository() {
	local repo=$1 files=$2 protected=$3 i
	git init -q -b main "$repo"
	git -C "$repo" config user.name bench
	git -C "$repo" config user.email bench@example.test
	echo public >"$repo/README"
	git -C "$repo" add README
	git -C "$repo" commit -qm seed
	(cd "$repo" && printf '%s\n' "$pass" | "$bin" init --password-stdin '*.secret' >/dev/null 2>&1)
	mkdir -p "$repo/d"
	for ((i = 0; i < files - protected; i++)); do echo "file $i" >"$repo/d/f$i.txt"; done
	for ((i = 0; i < protected; i++)); do echo "secret $i" >"$repo/d/s$i.secret"; done
	git -C "$repo" add -A
	git -C "$repo" commit -qm files
}

echo "binary: $bin"
echo "runs: $runs (median)"

# The timed steps and their setups, on the repository `$repo`; `n` numbers
# the edits so that each run changes something.
n=0
none() { :; }
edit_unprotected() {
	n=$((n + 1))
	echo "edit $n" >"$repo/d/f1.txt"
	git -C "$repo" add d/f1.txt
}
edit_protected() {
	n=$((n + 1))
	echo "edit $n" >"$repo/d/s1.secret"
	git -C "$repo" add d/s1.secret
}
moved=d/s2.secret
move_protected() {
	n=$((n + 1))
	git -C "$repo" mv "$moved" "d/moved-$n.secret"
	moved=d/moved-$n.secret
}
rewrite_all() {
	local j
	n=$((n + 1))
	for ((j = 0; j < 60000; j++)); do echo "rewrite $n $j" >"$repo/d/f$j.txt"; done
	git -C "$repo" add -A
}
restart_merge() {
	git -C "$repo" reset -q --hard main
	git -C "$repo" merge -q --no-commit --no-ff incoming
}
commit() { git -C "$repo" commit -qm step; }
status() { git -C "$repo" status --porcelain; }
verify_index() { (cd "$repo" && "$bin" verify-index); }

repo=$work/small
repository "$repo" 10000 300
median "10k/300: commit, unprotected edit" edit_unprotected commit
median "10k/300: commit, protected edit" edit_protected commit
median "10k/300: git mv protected + commit" move_protected commit
median "10k/300: git status" none status

repo=$work/large
repository "$repo" 60000 0
median "60k: verify-index after rewriting all" rewrite_all verify_index

repo=$work/merge
repository "$repo" 1 0
git -C "$repo" checkout -q -b incoming
for ((i = 0; i < 10000; i++)); do echo "secret $i" >"$repo/d/m$i.secret"; done
git -C "$repo" add -A
git -C "$repo" commit -qm incoming
git -C "$repo" checkout -q main 2>/dev/null
(cd "$repo" && "$bin" lock >/dev/null 2>&1)
median "locked merge of 10k protected: verify-index" restart_merge verify_index

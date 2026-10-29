#!/usr/bin/env bash
# Check the v3 proofs where Lake cannot set up the dependencies (NetBSD,
# OpenBSD; see ports/README.md). Compiles this project's modules with this
# machine's `lean` against the dependency modules in a kit from
# export-v3-kit.sh, replays every declaration, the dependencies' included,
# through this machine's kernel, and audits the axioms. The kit's compiled
# dependencies are therefore re-checked, not trusted.
# Usage: check-v3-without-lake.sh <kit.tgz>
# PYTHON names the Python 3 interpreter (default python3).
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
kit_archive=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
toolchain=$(sed 's/.*://' "$root/proofs/aeneas/v3/lean-toolchain")
case "$(lean --version)" in
*"version ${toolchain#v},"* | *"version ${toolchain#v} "*) ;;
*)
	echo "check-v3-without-lake: need Lean $toolchain, found: $(lean --version)" >&2
	exit 2
	;;
esac
"${PYTHON:-python3}" "$root/proofs/aeneas/v3_snapshot.py" stage
cd "$root/proofs/aeneas/v3"
kit=$(mktemp -d)
trap 'rm -rf "$kit"' EXIT
tar xzf "$kit_archive" -C "$kit"
build=$kit/build
LEAN_PATH=$build
while read -r dir; do LEAN_PATH=$LEAN_PATH:$kit/$dir; done <"$kit/roots.txt"
export LEAN_PATH
# The closure is in import order, so each module's imports are built first.
grep -E '^(V3Wire|Transcrypt)(\.|$)' "$kit/closure.txt" | while read -r module; do
	stem=${module//.//}
	mkdir -p "$build/$(dirname "$stem")"
	lean -o "$build/$stem.olean" -i "$build/$stem.ilean" "$stem.lean"
done
printf '%s\n' 'Built the production Aeneas extraction, independent spec and refinement module.'
V3_LEAN_ENV='' "$root/proofs/aeneas/replay-v3-kernel.sh"
V3_LEAN_ENV='' "$root/proofs/aeneas/check-v3-axioms.sh"

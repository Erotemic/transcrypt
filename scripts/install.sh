#!/bin/sh
# Install a transcrypt-v3 release binary: Linux (x86_64, arm64), FreeBSD
# (x86_64) or macOS (arm64, x86_64). On Windows, use install.ps1.
#
#   sh install.sh [--tag v3-X.Y.Z] [--from DIR] [--prefix DIR]
#
#   --tag TAG     the release to install (default: the newest v3-* release)
#   --from DIR    install from archives built locally by
#                 scripts/build-release.sh (no network)
#   --prefix DIR  install into DIR/bin (default: ~/.local)
#
# The archive is checked against the release's SHA256SUMS before anything
# is installed. Checking it against the GitHub build attestation as well
# needs the GitHub CLI: gh attestation verify ARCHIVE --repo Erotemic/transcrypt
set -eu

repo="Erotemic/transcrypt"
tag=""
from=""
prefix="${HOME}/.local"
while [ $# -gt 0 ]; do
	case "$1" in
	--tag)
		tag="$2"
		shift
		;;
	--from)
		from="$2"
		shift
		;;
	--prefix)
		prefix="$2"
		shift
		;;
	-h | --help)
		sed -n '2,14p' "$0" | sed 's/^# \{0,1\}//'
		exit 0
		;;
	*)
		echo "install: unknown argument: $1" >&2
		exit 2
		;;
	esac
	shift
done

fail() {
	echo "install: $*" >&2
	exit 1
}

case "$(uname -s)" in
Linux) os=linux ;;
FreeBSD) os=freebsd ;;
Darwin) os=macos ;;
*) fail "no release binary for $(uname -s) yet (docs/RELEASING.md); build from source: cd rust && cargo build --release" ;;
esac
case "$(uname -m)" in
x86_64 | amd64) arch=x86_64 ;;
aarch64 | arm64) arch=aarch64 ;;
*) fail "no release binary for $(uname -m) yet; build from source: cd rust && cargo build --release" ;;
esac
command -v git >/dev/null || fail "transcrypt-v3 needs Git (2.34 or later)"

if command -v sha256sum >/dev/null; then
	sha256() { sha256sum "$1" | cut -d ' ' -f 1; }
elif command -v shasum >/dev/null; then
	sha256() { shasum -a 256 "$1" | cut -d ' ' -f 1; }
else
	fail "missing sha256sum"
fi
fetch() {
	if command -v curl >/dev/null; then
		curl --proto '=https' --tlsv1.2 -fsSL "$1" -o "$2"
	elif command -v wget >/dev/null; then
		wget -q --https-only -O "$2" "$1"
	else
		fail "missing curl or wget"
	fi
}

work="$(mktemp -d)"
trap 'rm -r -- "$work"' EXIT

if [ -n "$from" ]; then
	cp -- "$from/SHA256SUMS" "$work/SHA256SUMS"
	archive=""
	for candidate in "$from"/transcrypt-v3-*-"$arch-$os".tar.gz; do
		if [ -f "$candidate" ]; then archive="${candidate##*/}"; fi
	done
	[ -n "$archive" ] || fail "no $arch-$os archive in $from"
	cp -- "$from/$archive" "$work/$archive"
else
	if [ -z "$tag" ]; then
		fetch "https://api.github.com/repos/$repo/releases" "$work/releases.json"
		tag="$(sed -n 's/^ *"tag_name": *"\(v3-[^"]*\)".*/\1/p' "$work/releases.json" | head -n 1)"
		[ -n "$tag" ] || fail "no v3 release found; pass --tag"
	fi
	archive="transcrypt-v3-${tag#v3-}-$arch-$os.tar.gz"
	base="https://github.com/$repo/releases/download/$tag"
	fetch "$base/SHA256SUMS" "$work/SHA256SUMS"
	fetch "$base/$archive" "$work/$archive"
fi

expected="$(awk -v name="$archive" '$2 == name { print $1 }' "$work/SHA256SUMS")"
[ -n "$expected" ] || fail "$archive is not listed in SHA256SUMS"
[ "$(sha256 "$work/$archive")" = "$expected" ] || fail "$archive does not match SHA256SUMS; nothing installed"

tar -xzf "$work/$archive" -C "$work"
mkdir -p "$prefix/bin"
cp "$work/${archive%.tar.gz}/transcrypt-v3" "$prefix/bin/transcrypt-v3.new"
chmod 0755 "$prefix/bin/transcrypt-v3.new"
mv -f "$prefix/bin/transcrypt-v3.new" "$prefix/bin/transcrypt-v3"
"$prefix/bin/transcrypt-v3" --version
case ":$PATH:" in
*":$prefix/bin:"*) ;;
*) echo "install: add $prefix/bin to your PATH" >&2 ;;
esac

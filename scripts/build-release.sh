#!/usr/bin/env bash
# Build the transcrypt-v3 release archives: static Linux binaries for x86_64
# and arm64, reproducible from the source commit. CI (.github/workflows/
# release.yml) runs exactly this script; it needs only rustup, Git, GNU tar,
# gzip and sha256sum (no C cross toolchain: Rust's bundled rust-lld links
# against the musl libc that ships with each target).
#
#   scripts/build-release.sh [--test] [--allow-dirty] [--out DIR] [TARGET...]
#
#   --test         also run the v3 test suite on each target this machine
#                  can execute (always on the native one)
#   --allow-dirty  build from a working tree with uncommitted changes (the
#                  archives are then not a release of any commit)
#   --out DIR      where to put the archives and SHA256SUMS (default dist/)
#   TARGET         x86_64-unknown-linux-musl and/or aarch64-unknown-linux-musl
#                  (default: both)
#
# The Rust toolchain is pinned (RUST_TOOLCHAIN, default below) so that
# anyone can rebuild an archive and compare its checksum.
set -euo pipefail

toolchain="${RUST_TOOLCHAIN:-1.98.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
out="$root/dist"
test=0
allow_dirty=0
targets=()
while [ $# -gt 0 ]; do
	case "$1" in
	--test) test=1 ;;
	--allow-dirty) allow_dirty=1 ;;
	--out)
		out="$(mkdir -p "$2" && cd "$2" && pwd -P)"
		shift
		;;
	-h | --help)
		sed -n '2,19p' "$0" | sed 's/^# \{0,1\}//'
		exit 0
		;;
	x86_64-unknown-linux-musl | aarch64-unknown-linux-musl) targets+=("$1") ;;
	*)
		echo "build-release: unsupported argument or target: $1" >&2
		exit 2
		;;
	esac
	shift
done
[ ${#targets[@]} -gt 0 ] || targets=(x86_64-unknown-linux-musl aarch64-unknown-linux-musl)

for tool in rustup git tar gzip sha256sum; do
	command -v "$tool" >/dev/null || {
		echo "build-release: missing $tool" >&2
		exit 1
	}
done
tar --version 2>/dev/null | grep -q 'GNU tar' || {
	echo "build-release: GNU tar is required" >&2
	exit 1
}

cd "$root"
if [ "$allow_dirty" = 0 ] && [ -n "$(git status --porcelain --untracked-files=no)" ]; then
	echo "build-release: uncommitted changes; commit them or pass --allow-dirty" >&2
	exit 1
fi
commit="$(git rev-parse HEAD)"
[ "$allow_dirty" = 0 ] || commit="$commit-dirty"
version="$(sed -n 's/^version = "\(.*\)"$/\1/p' rust/crates/transcrypt-v3/Cargo.toml | head -n 1)"
# Archive timestamps are the commit's, not the build's.
SOURCE_DATE_EPOCH="$(git log -1 --format=%ct)"
export SOURCE_DATE_EPOCH

rustup toolchain install --profile minimal --no-self-update "$toolchain" >/dev/null
rustup target add --toolchain "$toolchain" "${targets[@]}" >/dev/null
cargo=(rustup run "$toolchain" cargo)

# Static, stripped, path-independent binaries. RUSTFLAGS applies only to the
# target (not to host build scripts) because --target is always given.
export RUSTFLAGS="-C linker=rust-lld -C linker-flavor=ld.lld -C target-feature=+crt-static \
-C strip=symbols --remap-path-prefix=$root=/transcrypt --remap-path-prefix=${CARGO_HOME:-$HOME/.cargo}=/cargo"
export CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1
export CARGO_PROFILE_RELEASE_LTO=true
export CARGO_TARGET_DIR="$root/rust/target/release-dist"
export TRANSCRYPT_V3_COMMIT="$commit"

mkdir -p "$out"
archives=()
for target in "${targets[@]}"; do
	arch="${target%%-*}"
	echo "== $target"
	"${cargo[@]}" build --manifest-path rust/Cargo.toml --release --locked -p transcrypt-v3 --target "$target"
	bin="$CARGO_TARGET_DIR/$target/release/transcrypt-v3"
	if command -v readelf >/dev/null && readelf -lW "$bin" | grep -q 'program interpreter'; then
		echo "build-release: $target binary is not statically linked" >&2
		exit 1
	fi
	if runs="$("$bin" --version 2>/dev/null)"; then
		echo "$runs"
		if [ "$test" = 1 ]; then
			"${cargo[@]}" test --manifest-path rust/Cargo.toml --release --locked \
				-p transcrypt-v3 -p transcrypt-v3-core --target "$target"
		fi
	elif [ "$test" = 1 ]; then
		echo "build-release: cannot execute $target binaries here; tests skipped (CI tests it natively)" >&2
	fi
	name="transcrypt-v3-$version-$arch-linux"
	stage="$(mktemp -d)"
	mkdir "$stage/$name"
	install -m 0755 "$bin" "$stage/$name/transcrypt-v3"
	install -m 0644 LICENSE "$stage/$name/LICENSE"
	install -m 0644 docs/transcrypt-v3.md "$stage/$name/README.md"
	tar --sort=name --mtime="@$SOURCE_DATE_EPOCH" --owner=0 --group=0 --numeric-owner \
		-C "$stage" -cf - "$name" | gzip -n -9 >"$out/$name.tar.gz"
	rm -r -- "$stage"
	archives+=("$name.tar.gz")
done

cd "$out"
# Keep checksums of archives built earlier into the same directory.
touch SHA256SUMS
{
	grep -v -F -f <(printf '  %s\n' "${archives[@]}") SHA256SUMS || true
	sha256sum "${archives[@]}"
} | sort -k 2 >SHA256SUMS.new
mv SHA256SUMS.new SHA256SUMS
echo "== $out (commit $commit)"
cat SHA256SUMS

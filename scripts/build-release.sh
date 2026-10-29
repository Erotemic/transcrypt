#!/usr/bin/env bash
# Build the transcrypt-rs release archives, reproducible from the source
# commit. CI (.github/workflows/release.yml) runs exactly this script.
#
#   scripts/build-release.sh [--test] [--allow-dirty] [--out DIR] [TARGET...]
#
#   --test         also run the v3 test suite against each binary this
#                  machine can execute (always the native one)
#   --allow-dirty  build from a working tree with uncommitted changes (the
#                  archives are then not a release of any commit)
#   --out DIR      where to put the archives and SHA256SUMS (default dist/)
#   TARGET         default: every target this machine builds:
#                    on Linux:  x86_64-unknown-linux-musl, aarch64-unknown-linux-musl
#                               (static; no C toolchain: rust-lld links musl),
#                               x86_64-unknown-freebsd (needs clang; links the
#                               base libraries of the pinned FreeBSD release
#                               below, the oldest supported, and so runs on it
#                               and later releases),
#                               x86_64-pc-windows-gnu (static; needs mingw-w64)
#                    on macOS:  aarch64-apple-darwin, x86_64-apple-darwin
#
# Needs rustup, Git, GNU tar, gzip and sha256sum (or shasum); python3 for
# the Windows zip. The Rust toolchain is pinned (RUST_TOOLCHAIN, default
# below) so that anyone can rebuild an archive and compare its checksum.
# An archive for another OS is tested there by running the suite against
# its binary: TRANSCRYPT_RS_TEST_BIN=/path/to/transcrypt-rs cargo test -p
# transcrypt-rs (docs/RELEASING.md).
set -euo pipefail
# A failure inside $(...) (a missing tool, a bad checksum) stops the script.
shopt -s inherit_errexit

toolchain="${RUST_TOOLCHAIN:-1.98.0}"
# The FreeBSD release whose base libraries release binaries link against:
# the oldest supported, so the binary runs on it and later releases.
# (FreeBSD keeps libc.so.7 backward compatible. A static binary linked this
# way ran `--version` but crashed on every Git operation.)
freebsd_release=14.4-RELEASE
freebsd_base_sha256=769f60a6eea2938ad6b7943cfbcc17dfaf7d1f7ba59a32b869a00349302df853
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
		sed -n '2,26p' "$0" | sed 's/^# \{0,1\}//'
		exit 0
		;;
	x86_64-unknown-linux-musl | aarch64-unknown-linux-musl | x86_64-unknown-freebsd | x86_64-pc-windows-gnu | \
		aarch64-apple-darwin | x86_64-apple-darwin) targets+=("$1") ;;
	*)
		echo "build-release: unsupported argument or target: $1" >&2
		exit 2
		;;
	esac
	shift
done
host_os="$(uname -s)"
if [ ${#targets[@]} -eq 0 ]; then
	case "$host_os" in
	Linux) targets=(x86_64-unknown-linux-musl aarch64-unknown-linux-musl x86_64-unknown-freebsd x86_64-pc-windows-gnu) ;;
	Darwin) targets=(aarch64-apple-darwin x86_64-apple-darwin) ;;
	*)
		echo "build-release: name the targets to build on $host_os" >&2
		exit 2
		;;
	esac
fi

need() {
	command -v "$1" >/dev/null || {
		echo "build-release: missing $1${2:+ ($2)}" >&2
		exit 1
	}
}
for tool in rustup git gzip; do need "$tool"; done
tar=tar
command -v gtar >/dev/null && tar=gtar
"$tar" --version 2>/dev/null | grep -q 'GNU tar' || {
	echo "build-release: GNU tar is required (as tar or gtar)" >&2
	exit 1
}
if command -v sha256sum >/dev/null; then sha256=(sha256sum); else
	need shasum
	sha256=(shasum -a 256)
fi

cd "$root"
if [ "$allow_dirty" = 0 ] && [ -n "$(git status --porcelain --untracked-files=no)" ]; then
	echo "build-release: uncommitted changes; commit them or pass --allow-dirty" >&2
	exit 1
fi
commit="$(git rev-parse HEAD)"
[ "$allow_dirty" = 0 ] || commit="$commit-dirty"
version="$(sed -n 's/^version = "\(.*\)"$/\1/p' rust/crates/transcrypt-rs/Cargo.toml | head -n 1)"
# Archive timestamps are the commit's, not the build's.
SOURCE_DATE_EPOCH="$(git log -1 --format=%ct)"
export SOURCE_DATE_EPOCH

rustup toolchain install --profile minimal --no-self-update "$toolchain" >/dev/null
rustup target add --toolchain "$toolchain" "${targets[@]}" >/dev/null
cargo=(rustup run "$toolchain" cargo)
export CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1
export CARGO_PROFILE_RELEASE_LTO=true
export CARGO_TARGET_DIR="$root/rust/target/release-dist"
export TRANSCRYPT_RS_COMMIT="$commit"
# Stripped, path-independent binaries. RUSTFLAGS applies only to the target
# (not to host build scripts) because --target is always given.
common_flags="-C strip=symbols --remap-path-prefix=$root=/transcrypt --remap-path-prefix=${CARGO_HOME:-$HOME/.cargo}=/cargo"

# The FreeBSD libraries, from the pinned and checksummed base set.
freebsd_sysroot() {
	local dir="$CARGO_TARGET_DIR/sysroot/freebsd-$freebsd_release"
	if [ ! -f "$dir/usr/lib/libc.a" ]; then
		need curl
		mkdir -p "$dir"
		curl -fsSL -o "$dir.txz" "https://download.freebsd.org/releases/amd64/$freebsd_release/base.txz"
		echo "$freebsd_base_sha256  $dir.txz" | "${sha256[@]}" -c - >/dev/null || {
			echo "build-release: FreeBSD base.txz checksum mismatch" >&2
			exit 1
		}
		"$tar" -xJf "$dir.txz" -C "$dir" ./lib ./usr/lib 2>/dev/null
		rm -f "$dir.txz"
	fi
	echo "$dir"
}

# The linker flags of a target.
link_flags() {
	case "$1" in
	*-linux-musl) echo "-C linker=rust-lld -C linker-flavor=ld.lld -C target-feature=+crt-static" ;;
	x86_64-unknown-freebsd)
		need clang "the FreeBSD build links with clang and rust-lld"
		local lld sysroot host
		host="$(rustup run "$toolchain" rustc -vV | sed -n 's/^host: //p')"
		lld="$(rustup run "$toolchain" rustc --print sysroot)/lib/rustlib/$host/bin/gcc-ld"
		sysroot="$(freebsd_sysroot)"
		echo "-C linker=clang -C link-arg=--target=x86_64-unknown-freebsd${freebsd_release%-RELEASE} \
-C link-arg=--sysroot=$sysroot -C link-arg=-fuse-ld=lld -C link-arg=-B$lld \
-C link-arg=-Wno-unused-command-line-argument"
		;;
	x86_64-pc-windows-gnu)
		need x86_64-w64-mingw32-gcc "install mingw-w64"
		need x86_64-w64-mingw32-objdump "install mingw-w64"
		echo "-C linker=x86_64-w64-mingw32-gcc -C target-feature=+crt-static"
		;;
	*-apple-darwin)
		[ "$host_os" = Darwin ] || {
			echo "build-release: $1 is built on macOS" >&2
			exit 1
		}
		echo ""
		;;
	esac
}

# Refuse a binary that would need more than the OS itself provides.
check_self_contained() {
	local target="$1" bin="$2"
	case "$target" in
	*-linux-musl)
		if command -v readelf >/dev/null && readelf -lW "$bin" | grep -q 'program interpreter'; then
			echo "build-release: $target binary is not statically linked" >&2
			exit 1
		fi
		;;
	*-freebsd)
		need readelf
		local libs
		libs="$(readelf -dW "$bin" | sed -n 's/.*(NEEDED).*\[\(.*\)\]/\1/p')"
		if grep -qv -E '^(libc\.so\.7|libthr\.so\.3|libgcc_s\.so\.1|libm\.so\.5)$' <<<"$libs"; then
			echo "build-release: $target binary needs libraries outside FreeBSD's base system: $libs" >&2
			exit 1
		fi
		;;
	*-apple-darwin)
		local libs
		libs="$(otool -L "$bin" | tail -n +2 | awk '{ print $1 }')"
		if grep -qv -E '^(/usr/lib/|/System/)' <<<"$libs"; then
			echo "build-release: $target binary needs libraries macOS does not ship: $libs" >&2
			exit 1
		fi
		;;
	*-windows-gnu)
		local dlls
		dlls="$(x86_64-w64-mingw32-objdump -p "$bin" | sed -n 's/^\s*DLL Name: //p' | tr '[:upper:]' '[:lower:]' | sort -u)"
		if grep -qv -E '^(kernel32|ntdll|advapi32|ws2_32|bcryptprimitives|userenv|msvcrt|api-ms-win-[a-z0-9-]+)\.dll$' <<<"$dlls"; then
			echo "build-release: $target binary needs DLLs Windows does not ship: $dlls" >&2
			exit 1
		fi
		;;
	esac
}

# A reproducible archive of the staged directory $2/$3 at $1.
archive() {
	local file="$1" stage="$2" name="$3"
	case "$file" in
	*.zip)
		need python3 "for the Windows zip"
		# Stored, not deflated: the bytes then depend on no zlib version.
		python3 - "$file" "$stage" "$name" <<'EOF'
import os, sys, time, zipfile
file, stage, name = sys.argv[1:]
stamp = time.gmtime(max(int(os.environ["SOURCE_DATE_EPOCH"]), 315532800))[:6]
with zipfile.ZipFile(file, "w", zipfile.ZIP_STORED) as archive:
    for entry in sorted(os.listdir(os.path.join(stage, name))):
        info = zipfile.ZipInfo(f"{name}/{entry}", stamp)
        info.external_attr = 0o644 << 16
        with open(os.path.join(stage, name, entry), "rb") as source:
            archive.writestr(info, source.read())
EOF
		;;
	*)
		"$tar" --sort=name --mtime="@$SOURCE_DATE_EPOCH" --owner=0 --group=0 --numeric-owner \
			-C "$stage" -cf - "$name" | gzip -n -9 >"$file"
		;;
	esac
}

mkdir -p "$out"
archives=()
for target in "${targets[@]}"; do
	arch="${target%%-*}"
	case "$target" in
	*-linux-musl) os=linux exe="" ext=tar.gz ;;
	*-freebsd) os=freebsd exe="" ext=tar.gz ;;
	*-windows-gnu) os=windows exe=.exe ext=zip ;;
	*-apple-darwin) os=macos exe="" ext=tar.gz ;;
	esac
	echo "== $target"
	flags="$(link_flags "$target")"
	RUSTFLAGS="$flags $common_flags" \
		"${cargo[@]}" build --manifest-path rust/Cargo.toml --release --locked -p transcrypt-rs --target "$target"
	bin="$CARGO_TARGET_DIR/$target/release/transcrypt-rs$exe"
	check_self_contained "$target" "$bin"
	if runs="$("$bin" --version 2>/dev/null)"; then
		echo "$runs"
		if [ "$test" = 1 ]; then
			# The suite, run against the release binary itself.
			TRANSCRYPT_RS_TEST_BIN="$bin" "${cargo[@]}" test --manifest-path rust/Cargo.toml --locked \
				-p transcrypt-rs -p transcrypt-v3-core
		fi
	elif [ "$test" = 1 ]; then
		echo "build-release: cannot execute $target binaries here; test it on $os (docs/RELEASING.md)" >&2
	fi
	name="transcrypt-rs-$version-$arch-$os"
	stage="$(mktemp -d)"
	mkdir "$stage/$name"
	cp "$bin" "$stage/$name/transcrypt-rs$exe"
	cp LICENSE "$stage/$name/LICENSE"
	cp docs/verification/V3-USER-GUIDE.md "$stage/$name/README.md"
	chmod 0755 "$stage/$name/transcrypt-rs$exe"
	chmod 0644 "$stage/$name/LICENSE" "$stage/$name/README.md"
	archive "$out/$name.$ext" "$stage" "$name"
	rm -r -- "$stage"
	archives+=("$name.$ext")
done

cd "$out"
# Keep checksums of archives built earlier into the same directory (the
# other OS's builds, when they are collected for a release).
touch SHA256SUMS
{
	grep -v -F -f <(printf '  %s\n' "${archives[@]}") SHA256SUMS || true
	"${sha256[@]}" "${archives[@]}"
} | sort -k 2 >SHA256SUMS.new
mv SHA256SUMS.new SHA256SUMS
echo "== $out (commit $commit)"
cat SHA256SUMS

#!/bin/sh
# Build the pinned Lean toolchain from source on NetBSD or OpenBSD, with
# this directory's port applied (see README.md for the packages it needs).
# Usage: build-lean.sh <work dir>; prints the toolchain's bin directory.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
version=$(sed 's/.*://' "$here/../v3/lean-toolchain")
port=$here/lean-$version-bsd.patch
[ -f "$port" ] || {
	echo "build-lean: no port for Lean $version" >&2
	exit 2
}
case $(uname) in
NetBSD)
	# The base system's C++ library predates C++20's atomic::wait.
	prefix=/usr/pkg
	export CC=/usr/pkg/gcc14/bin/gcc CXX=/usr/pkg/gcc14/bin/g++
	export LDFLAGS="-Wl,-R/usr/pkg/gcc14/lib -Wl,-R/usr/pkg/lib"
	;;
OpenBSD) prefix=/usr/local ;;
*)
	echo "build-lean: for NetBSD and OpenBSD only" >&2
	exit 2
	;;
esac
mkdir -p "$1"
work=$(cd "$1" && pwd)
# Lean's build runs `make`, and needs GNU make.
mkdir -p "$work/bin"
ln -sf "$(command -v gmake)" "$work/bin/make"
PATH=$work/bin:$PATH
cd "$work"
[ -d lean4 ] || git clone -q --depth 1 -b "$version" https://github.com/leanprover/lean4
cd lean4
git checkout -q -- src stage0
git clean -qfd src stage0
for tree in src stage0/src; do patch -s -p1 -d "$tree" <"$port"; done
find src stage0/src -name '*.orig' -delete
rm -rf build/release
mkdir -p build/release
cd build/release
cmake ../.. -DCMAKE_BUILD_TYPE=Release -DCMAKE_PREFIX_PATH="$prefix" >&2
make -j"$(getconf NPROCESSORS_ONLN)" >&2
echo "$PWD/stage1/bin"

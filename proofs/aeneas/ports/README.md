# Checking the proofs on NetBSD and OpenBSD

Lean publishes no toolchain for NetBSD or OpenBSD, and Lake cannot fetch
Mathlib's cache there. The proofs are checked on those systems with Lean
built from source and without Lake:

1. Build Lean v4.31.0 (commit `68218e8`, the `lean-toolchain` pin) with
   `lean-v4.31.0-bsd.patch` applied to both `src/` and `stage0/src/`:

   ```sh
   git clone --depth 1 -b v4.31.0 https://github.com/leanprover/lean4
   cd lean4
   for d in src stage0/src; do patch -p1 -d $d < .../lean-v4.31.0-bsd.patch; done
   mkdir -p build/release && cd build/release
   cmake ../.. -DCMAKE_BUILD_TYPE=Release -DCMAKE_PREFIX_PATH=<pkg prefix>
   make -j8          # GNU make, first on PATH as `make`
   export PATH=$PWD/stage1/bin:$PATH
   ```

   NetBSD needs pkgsrc `cmake gmp libuv gmake pkgconf gcc14` and
   `CC=/usr/pkg/gcc14/bin/gcc CXX=/usr/pkg/gcc14/bin/g++
   LDFLAGS="-Wl,-R/usr/pkg/gcc14/lib -Wl,-R/usr/pkg/lib"` (the base system's C++ library predates
   C++20's `atomic::wait`). OpenBSD needs `pkg_add cmake gmp libuv gmake
   python%3` and builds with its base clang.

2. On a machine with Lake, after `build-v3-tracked.sh`, export the compiled
   dependencies: `export-v3-kit.sh v3-kit.tgz`.

3. On the BSD machine: `check-v3-without-lake.sh v3-kit.tgz`. It compiles
   this project's modules with the native `lean`, replays every declaration
   in their import closure through the native kernel (`leanchecker
   --fresh`, so the kit's Linux-compiled Mathlib and Aeneas are re-checked
   rather than trusted), and runs the axiom audit.

## What the patch changes

Only the runtime, where Lean 4.31 calls Linux interfaces these systems lack,
and the build's choice of linker flags; nothing in the kernel, elaborator or
library:

| File | Linux interface | NetBSD | OpenBSD |
| --- | --- | --- | --- |
| `runtime/io.cpp` | `<sys/random.h>` (unused: randomness is read from `/dev/urandom`) | present | include skipped |
| `runtime/io.cpp`, `util/path.cpp` | `/proc/<pid>/exe`, to find the toolchain | `KERN_PROC_PATHNAME` | `argv[0]` resolved against `PATH`, as Rust's `current_exe` does |
| `runtime/stack_overflow.cpp` | `pthread_getattr_np` | present | `pthread_stackseg_np` |
| `runtime/process.cpp` | `SYS_gettid`, `clearenv` | `_lwp_self`, empty `environ` | `getthrid`, empty `environ` |
| `CMakeLists.txt` | ELF linking (`-fPIC`, `$ORIGIN` rpaths, whole-archive Lake) for Linux only | as Linux | as Linux, plus `-z origin` so `ld.so` expands `$ORIGIN` |

Lean reports a resident-memory figure from `/proc/self/statm`, and reports
0 when it is absent; that needs no change.

#!/usr/bin/env bash
# Test the shell integration with fake cargo-hax/Lake. This does not prove that
# Rust translates to Lean. In particular, test cargo-hax's real multi-line
# `--version` shape, and ensure the scenario stays inside the Rust workspace.
set -euo pipefail
root=$(cd "$(dirname "$0")/../../.." && pwd)
crate="$root/rust/crates/transcrypt-v3-core"
workspace="$root/rust"
generated="$workspace/proofs/aeneas/generated/V3Core"

# Resolve the scenario path independently of the shell driver. In hax 0.4.2
# extraction outputs outside the Cargo workspace are rejected. The earlier
# mock overlooked this and passed although production extraction could not.
scenario_output=$(sed -n 's/^output-dir = "\([^"]*\)"[[:space:]]*$/\1/p' "$crate/hax.toml")
if [ -z "$scenario_output" ]; then
  echo 'Missing or ambiguous output-dir in the v3-wire scenario.' >&2
  exit 1
fi
resolved_output=$(realpath -m "$crate/$scenario_output")
expected_output="$generated/lean"
if [ "$resolved_output" != "$expected_output" ]; then
  printf 'Script/scenario extraction directories disagree:\n  scenario: %s\n  script:   %s\n' "$resolved_output" "$expected_output" >&2
  exit 1
fi
case "$resolved_output" in
  "$workspace"/*) ;;
  *) echo 'The hax scenario output must stay inside the Rust workspace.' >&2; exit 1;;
esac

work=$(mktemp -d)
# Never remove a genuine extraction from a developer's checkout.
if [ -e "$generated" ]; then
  echo 'Cannot run mocked bridge tests while an actual V3Core extraction exists.' >&2
  echo 'Run the real build script directly, or move your generated proof project.' >&2
  rm -rf "$work"
  exit 2
fi
trap 'rm -rf "$work" "$generated"' EXIT
mockbin="$work/bin"
mkdir -p "$mockbin"
export TEST_PROJECT="$generated/lean"
export TEST_LOG="$work/calls"

cat > "$mockbin/cargo" <<'MOCK'
#!/usr/bin/env bash
set -eu
printf 'cargo %s\n' "$*" >> "$TEST_LOG"
case "$*" in
  'hax --version')
    case "${HAX_FAKE_STYLE:-multiline}" in
      multiline) printf 'hax \nversion=%s\ncommit=unknown\n' "${HAX_FAKE_VERSION:-0.4.2}";;
      legacy) printf 'cargo-hax %s\n' "${HAX_FAKE_VERSION:-0.4.2}";;
      spoofed) printf 'hax \nversion=0.4.3\ncommit=0.4.2\n';;
      *) echo 'Unknown test version format' >&2; exit 19;;
    esac;;
  'hax extract --dry-run v3-wire')
    [ "${FAIL_DRY_RUN:-0}" != 1 ] || exit 16
    echo 'resolved scenario v3-wire (mock)' ;;
  'hax tools install')
    [ "${FAIL_INSTALL:-0}" != 1 ] || exit 17;;
  'hax tools show') echo 'charon mock; aeneas mock; lean mock';;
  'hax extract v3-wire')
    [ "${FAIL_EXTRACT:-0}" != 1 ] || exit 18
    [ "${SKIP_GENERATED:-0}" != 1 ] || exit 0
    mkdir -p "$TEST_PROJECT/V3Wire/Extraction"
    cat > "$TEST_PROJECT/V3Wire/Extraction/Funs.lean" <<'LEAN'
-- Mock declarations: only for testing the command path, NOT proof evidence.
def decode_config_exact := true
def encode_config := true
def decode_file_header_exact := true
def encode_file_header := true
LEAN
    echo 'import V3Wire.Extraction.Funs' > "$TEST_PROJECT/V3Wire/Extraction.lean"
    echo 'import V3Wire.Extraction' > "$TEST_PROJECT/V3Wire.lean"
    echo '[package]' > "$TEST_PROJECT/lakefile.toml"
    echo 'leanprover/lean4:v4.33.0' > "$TEST_PROJECT/lean-toolchain";;
  *) echo "Unexpected cargo invocation: $*" >&2; exit 19;;
esac
MOCK
cat > "$mockbin/lake" <<'MOCK'
#!/usr/bin/env bash
printf 'lake %s\n' "$*" >> "$TEST_LOG"
[ "$*" = 'build Transcrypt V3Wire' ]
MOCK
chmod +x "$mockbin/cargo" "$mockbin/lake"
export PATH="$mockbin:$PATH"

# This is the *actual observed* version format on the developer's machine.
# Suppress the real-driver success wording in a mocked test: a fake Lake exit
# must never look like an actual extracted/compiled Aeneas development.
AENEAS_ROOT=/no/aeneas bash "$root/proofs/aeneas/translate-v3-core.sh" > "$work/mock-translate.log"
AENEAS_ROOT=/no/aeneas bash "$root/proofs/aeneas/build-v3-generated.sh" > "$work/mock-build.log"
grep -Fxq 'cargo hax extract --dry-run v3-wire' "$TEST_LOG"
grep -Fxq 'cargo hax tools install' "$TEST_LOG"
grep -Fxq 'cargo hax extract v3-wire' "$TEST_LOG"
grep -Fxq 'lake build Transcrypt V3Wire' "$TEST_LOG"
[ -s "$generated/PROVENANCE.txt" ]
# Import the real production extraction and exact independent v3 spec in the
# same generated root, with no duplicate imports after repeated preparation.
grep -Fxq 'import V3Wire.Verification.IndependentSpec' "$TEST_PROJECT/V3Wire.lean"
cmp "$root/proofs/lean/Transcrypt/V3WireCodec.lean" "$TEST_PROJECT/Transcrypt/V3WireCodec.lean"
bash "$root/proofs/aeneas/prepare-v3-refinement.sh" > "$work/prepare-again.log"
[ "$(grep -Fxc 'import V3Wire.Verification.IndependentSpec' "$TEST_PROJECT/V3Wire.lean")" = 1 ]
[ "$(grep -Fxc 'name = "Transcrypt"' "$TEST_PROJECT/lakefile.toml")" = 1 ]
# The dry run must occur before tool installation, which must precede extraction.
first_dry=$(grep -nFx 'cargo hax extract --dry-run v3-wire' "$TEST_LOG" | head -1 | cut -d: -f1)
first_install=$(grep -nFx 'cargo hax tools install' "$TEST_LOG" | head -1 | cut -d: -f1)
first_extract=$(grep -nFx 'cargo hax extract v3-wire' "$TEST_LOG" | head -1 | cut -d: -f1)
[ "$first_dry" -lt "$first_install" ] && [ "$first_install" -lt "$first_extract" ]

# The build must reject admitted Lean declarations, not count an empty module.
cat >> "$TEST_PROJECT/V3Wire/Extraction/Funs.lean" <<'LEAN'
theorem bogus : False := by sorry
LEAN
if bash "$root/proofs/aeneas/build-v3-generated.sh" > "$work/admitted.log" 2>&1; then
  echo 'Build accepted admitted Lean declaration.' >&2; exit 1
fi
grep -Fq 'Admitted code in imported module' "$work/admitted.log"

# A dry-run failure aborts before attempting the costly managed install.
rm -rf "$generated"
: > "$TEST_LOG"
if FAIL_DRY_RUN=1 bash "$root/proofs/aeneas/translate-v3-core.sh" > "$work/dry-run.log" 2>&1; then
  echo 'Translation continued after a failed scenario dry run.' >&2; exit 1
fi
if grep -Fxq 'cargo hax tools install' "$TEST_LOG"; then
  echo 'Tool installation ran despite an invalid extraction scenario.' >&2; exit 1
fi
[ ! -e "$generated/PROVENANCE.txt" ]

# Tool-install and extraction failures must never write provenance.
if FAIL_INSTALL=1 bash "$root/proofs/aeneas/translate-v3-core.sh" > "$work/failed-install.log" 2>&1; then
  echo 'Translation accepted a failed tool installation.' >&2; exit 1
fi
[ ! -e "$generated/PROVENANCE.txt" ]
if FAIL_EXTRACT=1 bash "$root/proofs/aeneas/translate-v3-core.sh" > "$work/failed-extract.log" 2>&1; then
  echo 'Translation accepted a failed extraction.' >&2; exit 1
fi
[ ! -e "$generated/PROVENANCE.txt" ]

# A successful exit without actual generated modules is not a translation.
if SKIP_GENERATED=1 bash "$root/proofs/aeneas/translate-v3-core.sh" > "$work/empty-extract.log" 2>&1; then
  echo 'Translation accepted empty generated output.' >&2; exit 1
fi
grep -Fq 'Missing Lean extraction' "$work/empty-extract.log"

# The previous stub's single-line format remains acceptable, but mismatched
# versions and a misleading `commit=0.4.2` must both be rejected.
HAX_FAKE_STYLE=legacy bash "$root/proofs/aeneas/translate-v3-core.sh" > "$work/legacy-style.log"
rm -rf "$generated"
if HAX_FAKE_VERSION=0.4.3 bash "$root/proofs/aeneas/translate-v3-core.sh" > "$work/version-mismatch.log" 2>&1; then
  echo 'Translation accepted an unpinned hax release.' >&2; exit 1
fi
grep -Fq 'Expected cargo-hax 0.4.2' "$work/version-mismatch.log"
if HAX_FAKE_STYLE=spoofed bash "$root/proofs/aeneas/translate-v3-core.sh" > "$work/version-spoof.log" 2>&1; then
  echo 'Translation accepted a version number in the commit field.' >&2; exit 1
fi
grep -Fq 'Expected cargo-hax 0.4.2' "$work/version-spoof.log"

echo 'PASS: hax 0.4.2 real version format, workspace output path, dry-run, extraction/build and failure gates (mocked)' 

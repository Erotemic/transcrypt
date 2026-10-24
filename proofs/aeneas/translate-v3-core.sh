#!/usr/bin/env bash
# Translate the production Rust v3 wire codec via cargo-hax's managed,
# matched Charon/Aeneas toolchain. No ~/code/aeneas checkout is required.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
crate="$root/rust/crates/transcrypt-v3-core"
project="$root/rust/proofs/aeneas/generated/V3Core/lean"

if ! command -v cargo >/dev/null 2>&1; then
  echo 'Missing cargo; install the Rust toolchain using rustup.' >&2
  exit 2
fi
if ! cargo hax --version >/dev/null 2>&1; then
  cat >&2 <<'MESSAGE'
Missing cargo-hax. Install the pinned Lean backend driver:

  cargo install --locked --version 0.4.2 cargo-hax

No standalone Charon or Aeneas installation is necessary: cargo-hax downloads
and verifies a compatible pair. See https://pereq.dev/hax/manual/tools/
MESSAGE
  exit 2
fi
hax_version=$(cargo hax --version 2>/dev/null) || exit 2
# `cargo hax --version` in 0.4.2 reports multiple lines, e.g.:
#   hax
#   version=0.4.2
#   commit=unknown
# Older builds also report `cargo-hax 0.4.2`. Accept only these precise
# version fields, never a version number appearing in unrelated metadata.
if ! printf '%s\n' "$hax_version" | LC_ALL=C grep -Eq \
  '^(version=0[.]4[.]2|cargo-hax[[:space:]]+0[.]4[.]2)[[:space:]]*$'; then
  printf 'Expected cargo-hax 0.4.2, got: %s\n' "$hax_version" >&2
  echo 'Install: cargo install --locked --version 0.4.2 cargo-hax --force' >&2
  exit 2
fi
if ! command -v sha256sum >/dev/null 2>&1; then
  echo 'Missing sha256sum, needed for source provenance.' >&2
  exit 2
fi
if [ ! -f "$crate/hax.toml" ]; then
  echo "Missing the v3 extraction scenario: $crate/hax.toml" >&2
  exit 2
fi

(
  cd "$crate"
  # Check scenario resolution (especially its workspace-local output directory)
  # *before* downloading the managed toolchain.
  cargo hax extract --dry-run v3-wire
  # The 0.4.x driver manages these tools. Downloads are content-verified
  # against the release manifest and cached, not rebuilt with opam.
  cargo hax tools install
  cargo hax extract v3-wire
)

extraction="$project/V3Wire/Extraction"
if [ ! -s "$project/lakefile.toml" ] || [ ! -s "$project/V3Wire/Extraction.lean" ] || [ ! -d "$extraction" ]; then
  echo "Missing Lean extraction at $project; inspect cargo-hax output." >&2
  exit 1
fi
for name in decode_config_exact encode_config decode_file_header_exact encode_file_header; do
  if ! grep -RFq --include='*.lean' "$name" "$extraction"; then
    echo "Generated Lean does not mention production function: $name" >&2
    echo 'Check the scenario selection and Charon/Aeneas name translation.' >&2
    exit 1
  fi
done

mkdir -p "$(dirname "$project")"
{
  printf '# Source and extraction scenario (SHA-256)\n'
  (cd "$root" && sha256sum \
    rust/crates/transcrypt-v3-core/src/lib.rs \
    rust/crates/transcrypt-v3-core/hax.toml)
  printf '# Managed translator versions\n'
  (cd "$crate" && cargo hax --version && cargo hax tools show)
  printf '# Generated Lean source files\n'
  find "$extraction" -type f -name '*.lean' -print | LC_ALL=C sort | while IFS= read -r file; do
    sha256sum "$file"
  done
} > "$root/rust/proofs/aeneas/generated/V3Core/PROVENANCE.txt"

echo "Generated production v3 Lean extraction: $project"
echo 'Next: bash proofs/aeneas/build-v3-generated.sh'
echo 'Extraction is not a refinement proof; theorems must refer to generated definitions.'

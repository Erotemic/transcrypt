#!/usr/bin/env bash
# Lint every tracked shell script (except the Bats suites in tests/) with
# shellcheck and shfmt, as the CI lint job does. Pass --fix to apply shfmt's
# formatting instead of reporting it. CI pins shellcheck 0.10.0 and shfmt
# 3.10.0; other versions may disagree on details.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
for tool in shellcheck shfmt; do
	command -v "$tool" >/dev/null || {
		echo "lint-shell: missing $tool" >&2
		exit 1
	}
done
mapfile -t files < <(git ls-files -z | xargs -0 shfmt -f | grep -v '^tests/' | sort)
echo "lint-shell: ${#files[@]} scripts"
shellcheck "${files[@]}"
if [ "${1:-}" = --fix ]; then
	shfmt -w "${files[@]}"
else
	shfmt -d "${files[@]}"
fi

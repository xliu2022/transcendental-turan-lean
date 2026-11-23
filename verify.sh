#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

usage() {
  printf '%s\n' \
    'Usage: bash verify.sh [--checks-only | --comparator]' \
    '  --checks-only  Check source requirements and metadata without building.' \
    '  --comparator   Also run independent comparison and Lean/NanoDa on Linux.' \
    'Set TURAN_BUILD_JOBS to limit concurrent Lake builds (default: 2).'
}

if (( $# > 1 )); then
  usage >&2
  exit 2
fi
case "${1:-}" in
  ''|--checks-only|--comparator) ;;
  --help|-h) usage; exit 0 ;;
  *) usage >&2; exit 2 ;;
esac

python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
if [[ "${1:-}" == '--checks-only' ]]; then
  printf '%s\n' 'Source requirements and metadata checks passed.'
  exit 0
fi

verification_log_dir=$(mktemp -d "${TMPDIR:-/tmp}/transcendental-turan-verify.XXXXXX")
printf 'Fresh verification logs: %s\n' "$verification_log_dir"
lake exe cache get
python3 scripts/build-bounded.py --all --jobs "${TURAN_BUILD_JOBS:-2}" \
  --log-dir "$verification_log_dir/build"
lake build
python3 scripts/audit-axioms.py --log "$verification_log_dir/axioms.txt"

if [[ "${1:-}" == '--comparator' ]]; then
  bash scripts/verify-comparator.sh
fi

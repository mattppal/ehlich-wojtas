#!/usr/bin/env bash
# End-to-end local Palomar submit checks.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

if [[ -f "$HOME/.elan/env" ]]; then
  # shellcheck disable=SC1091
  source "$HOME/.elan/env"
fi

echo "== numerical bound =="
python3 scripts/check_bound.py

echo "== Palomar mechanical metadata =="
python3 scripts/check_palomar.py
ruby scripts/validate-formalization.rb formalization.yaml

echo "== lake build =="
lake build

echo "== Comparator + NanoDa =="
./scripts/verify-comparator.sh

echo "verify-submit.sh OK"

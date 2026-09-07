#!/usr/bin/env bash
# Re-runnable Palomar/Lean gates for the Ehlich–Wojtas formalization.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

if [[ -f "$HOME/.elan/env" ]]; then
  # shellcheck disable=SC1091
  source "$HOME/.elan/env"
fi

echo "== numerical bound =="
python3 scripts/check_bound.py

echo "== lake build =="
lake build

echo "== advertised statement =="
test -f Challenge.lean
test -f Solution.lean
test -f comparator.json
test -f formalization.yaml
test -f NOVELTY.md
test -f LICENSE
test -f README.md
grep -q 'theorem ehlich_wojtas_bound' Challenge.lean
grep -q 'theorem ehlich_wojtas_bound' Solution.lean
python3 - <<'PY'
import json
from pathlib import Path
cfg = json.loads(Path("comparator.json").read_text())
assert cfg["challenge_module"] == "Challenge"
assert cfg["solution_module"] == "Solution"
assert cfg["theorem_names"] == ["EhlichWojtas.ehlich_wojtas_bound"]
assert cfg["definition_names"] == []
print("comparator.json names match")
PY

echo "== Solution has no sorry =="
if grep -n 'sorry' Solution.lean EhlichWojtas.lean EhlichWojtas/*.lean; then
  echo "sorry remains in the proof development" >&2
  exit 1
fi

echo "== Challenge keeps its statement sorry =="
grep -q 'sorry' Challenge.lean

echo "verify.sh OK"

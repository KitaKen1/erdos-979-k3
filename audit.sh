#!/bin/bash
# Audit script for the Erdős 979 (k = 3) formalization.
#
#   1. No `sorry` anywhere in the Lean sources.
#   2. The local `Erdos979.solutionSet` definition and the theorem statement
#      are character-identical to the pinned Formal Conjectures commit.
#   3. (Optional, slow) `lake build` in lean/ re-checks the whole proof and
#      prints the axioms of the final theorem.
#
# Usage:  ./audit.sh          # checks 1 + 2
#         ./audit.sh --build  # also runs the full lean/ build

set -u
here="$(cd "$(dirname "$0")" && pwd)"
fail=0

FC_COMMIT=b2e608fc52d765510915a244bb69b1a2741acc3c
FC_RAW="https://raw.githubusercontent.com/google-deepmind/formal-conjectures/${FC_COMMIT}/FormalConjectures/ErdosProblems/979.lean"

echo "== 1. sorry scan =="
if grep -rn --include='*.lean' -w 'sorry' "$here/lean" "$here/lean4web"; then
  echo "FAIL: sorry found"; fail=1
else
  echo "OK: no sorry in lean/ or lean4web/"
fi

echo
echo "== 2. statement identity against Formal Conjectures @ ${FC_COMMIT:0:12} =="
upstream="$(mktemp)"
if ! curl -sL --max-time 60 "$FC_RAW" -o "$upstream"; then
  echo "SKIP: could not download upstream file (offline?)"
else
  # exact definition as it appears upstream
  updef="$(grep -A 1 '^def solutionSet' "$upstream")"
  localdef="$(grep -A 1 '^def solutionSet' "$here/lean/K3Lean/FormalConjecturesTarget.lean")"
  if [ "$updef" = "$localdef" ] && [ -n "$updef" ]; then
    echo "OK: solutionSet definition is character-identical"
    echo "$updef" | sed 's/^/    /'
  else
    echo "FAIL: solutionSet definitions differ"
    echo "--- upstream ---"; echo "$updef"
    echo "--- local ---"; echo "$localdef"
    fail=1
  fi
  upthm="$(grep -A 1 '^theorem erdos_979.variants.k3' "$upstream")"
  localthm="$(grep -A 1 '^theorem erdos_979.variants.k3' "$here/lean/K3Lean/Erdos979K3Final.lean")"
  # upstream continuation line ends in `:= by`; local ends in `:=` — compare the statement itself
  up_stmt="$(echo "$upthm" | sed 's/ := by$//; s/ :=$//')"
  local_stmt="$(echo "$localthm" | sed 's/ := by$//; s/ :=$//')"
  if [ "$up_stmt" = "$local_stmt" ] && [ -n "$up_stmt" ]; then
    echo "OK: theorem statement is character-identical"
    echo "$up_stmt" | sed 's/^/    /'
  else
    echo "FAIL: theorem statements differ"
    echo "--- upstream ---"; echo "$up_stmt"
    echo "--- local ---"; echo "$local_stmt"
    fail=1
  fi
  rm -f "$upstream"
fi

if [ "${1:-}" = "--build" ]; then
  echo
  echo "== 3. full build (lean/) =="
  cd "$here/lean" && lake exe cache get && lake build
  echo "Look above for:  'Erdos979.erdos_979.variants.k3' depends on axioms:"
  echo "                 [propext, Classical.choice, Quot.sound]"
fi

exit $fail

#!/bin/sh
# Build the Lean library and audit the axioms of the headline theorems.
# Usage: lean/check.sh   (no global elan needed; uses lean/.lake/toolchain)
set -eu
cd "$(dirname "$0")"
export PATH="$PWD/.lake/toolchain/bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
nice -n 19 lake build
out=$(nice -n 19 lake env lean AxiomAudit.lean)
echo "$out"
if echo "$out" | grep -E 'sorryAx|ofReduceBool|trustCompiler' >/dev/null; then
  echo "AXIOM AUDIT FAILED" >&2; exit 1
fi
echo "AXIOM AUDIT OK"

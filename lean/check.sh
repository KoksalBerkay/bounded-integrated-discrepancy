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
# Allowlist: every theorem listed in AxiomAudit.lean must be printed (by name)
# and may depend only on propext, Classical.choice and Quot.sound.
fail=0
for name in $(sed -n 's/^#print axioms //p' AxiomAudit.lean); do
  line=$(echo "$out" | grep -F "'$name' " | head -n 1)
  if [ -z "$line" ]; then echo "missing audit output for $name" >&2; fail=1; continue; fi
  case "$line" in *"does not depend on any axioms"*) continue ;; esac
  extra=$(echo "$line" | sed 's/.*depends on axioms: \[//; s/\]$//' | tr ',' '\n' \
    | sed 's/^ *//' | grep -v -x -E 'propext|Classical.choice|Quot.sound' || true)
  if [ -n "$extra" ]; then echo "$name uses unexpected axioms: $extra" >&2; fail=1; fi
done
if [ "$fail" -ne 0 ]; then echo "AXIOM AUDIT FAILED" >&2; exit 1; fi
seen=$(grep -c '^#print axioms' AxiomAudit.lean)
echo "AXIOM AUDIT OK ($seen theorems; only propext, Classical.choice, Quot.sound)"

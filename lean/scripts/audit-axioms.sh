#!/usr/bin/env bash
# Honesty audit for Results.lean.
#
# A declaration exported from Results.lean should depend only on the three standard Lean
# axioms (propext, Classical.choice, Quot.sound). A `native_decide` axiom or `sorryAx` in the
# dependency set means the statement is NOT fully proved by the kernel.
#
# Usage: scripts/audit-axioms.sh          audit every Results declaration
#        scripts/audit-axioms.sh NAME...  audit specific fully-qualified constants
set -euo pipefail
cd "$(dirname "$0")/.."

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

{
  echo "import Results"
  if [ "$#" -gt 0 ]; then
    for name in "$@"; do echo "#print axioms $name"; done
  else
    grep -oE "^(theorem|lemma) [A-Za-z0-9_']+" Results.lean \
      | awk '{print "#print axioms Results." $2}'
  fi
} > "$tmp/Audit.lean"

echo "== sorry in project sources =="
if grep -rn --include='*.lean' '\bsorry\b' EulersGem Results.lean EulersGem.lean; then
  echo "AUDIT FAIL: sorry found"
  exit 1
fi
echo "none"

echo
echo "== native_decide occurrences (each puts an axiom into everything downstream) =="
grep -rn --include='*.lean' 'native_decide' EulersGem Results.lean EulersGem.lean || echo "none"

echo
echo "== axiom dependencies of Results declarations =="
lake env lean "$tmp/Audit.lean" > "$tmp/log" 2>&1 || true

python3 - "$tmp/log" <<'PY'
import re, sys
text = open(sys.argv[1]).read()
# each record: 'Name' depends on axioms: [ ... ]   (possibly spread over lines)
records = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", text, re.S)
noaxiom = re.findall(r"'([^']+)' does not depend on any axioms", text)
bad = []
for name, axs in records:
    axl = [a.strip() for a in axs.replace('\n', ' ').split(',')]
    if any('native_decide' in a or 'sorryAx' in a for a in axl):
        bad.append((name, axl))
print(f"{len(records) + len(noaxiom)} declarations audited")
other_errors = [l for l in text.splitlines() if 'error' in l and 'depends on axioms' not in l]
for l in other_errors:
    print("  note:", l)
if bad:
    print()
    print("NOT kernel-proved (native_decide / sorryAx in the dependency set):")
    for name, axl in bad:
        offenders = [a for a in axl if 'native_decide' in a or 'sorryAx' in a]
        print(f"  {name}")
        for a in offenders:
            print(f"      {a}")
    print()
    print(f"AUDIT FAIL: {len(bad)} of {len(records) + len(noaxiom)} declarations")
    sys.exit(1)
print("AUDIT PASS: every declaration depends only on the standard axioms")
PY

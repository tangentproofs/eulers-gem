#!/usr/bin/env bash
# Comparator helper: list paper-facing theorems claimed in Results.lean.
# Same pattern as other tangentproofs repos (eliahou-collatz-bounds, leansieve).
set -euo pipefail
cd "$(dirname "$0")/.."
rg -n '^theorem |^lemma ' lean/Results.lean

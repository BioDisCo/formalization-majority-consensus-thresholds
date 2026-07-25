#!/usr/bin/env bash
# CI gate: fail if any sorry or axiom appears in theorem files.
set -euo pipefail

cd "$(dirname "$0")"

EXIT=0

echo "=== Checking for sorry/axiom in LVConsensus/**/*.lean ==="

while IFS= read -r -d '' f; do
  relative=${f#LVConsensus/}

  # Count sorry (excluding comments)
  sorry_count=$(grep -c '^\s*sorry' "$f" 2>/dev/null || true)
  # Count axiom declarations, including private/protected/noncomputable and
  # indented ones (a plain '^axiom ' misses `private axiom`). Match optional
  # leading modifier words then `axiom` + whitespace; the char-class form works
  # on BSD grep, where a literal `(private |...)*` alternation does not.
  # AxiomProbe.lean (run below) is the authoritative transitive check; this
  # fast grep is a first-line signal and may over-flag prose in block comments.
  axiom_count=$(grep -cE '^[[:space:]]*([a-zA-Z]+[[:space:]]+)*axiom[[:space:]]' "$f" 2>/dev/null || true)

  total=$((sorry_count + axiom_count))

  if [[ $total -gt 0 ]]; then
    echo "  FAIL  $relative: $sorry_count sorry, $axiom_count axiom"
    EXIT=1
  else
    echo "  OK    $relative"
  fi
done < <(find LVConsensus -type f -name '*.lean' -print0 | sort -z)

echo ""
echo "=== Building project ==="
if lake build 2>&1 | grep -q "^error:"; then
  echo "  FAIL  lake build failed"
  EXIT=1
else
  # Count total sorry warnings from build
  SORRY_WARNS=$(lake build 2>&1 | grep -c "declaration uses 'sorry'" || true)
  echo "  Total sorry warnings from build: $SORRY_WARNS"
  if [[ $SORRY_WARNS -gt 0 ]]; then
    echo "  FAIL  Build has sorry warnings"
    EXIT=1
  fi
fi

echo ""
echo "=== Auditing axiom dependencies (AxiomProbe.lean) ==="
# The per-file scan above only sees `sorry`/`axiom` written literally in a file.
# A theorem can still reach a `sorry` or a custom `axiom` (e.g. `coupling_nat_aux`)
# through an imported lemma. AxiomProbe.lean runs `collectAxioms` on every probed
# result and exits nonzero if any hides a custom axiom or if a verified-badge
# result regressed to `sorry` — things a grep cannot catch.
if AUDIT_OUT=$(lake env lean AxiomProbe.lean 2>&1); then
  echo "$AUDIT_OUT" | grep -E "AxiomProbe audit:" || echo "  OK    axiom audit passed"
else
  echo "$AUDIT_OUT" | grep -vE "has local changes" | grep -iE "audit|custom axiom|verified badge|depends on sorry" | sed 's/^/  /'
  echo "  FAIL  axiom audit (see AxiomProbe.lean)"
  EXIT=1
fi

exit $EXIT

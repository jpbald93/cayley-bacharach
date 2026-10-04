#!/bin/bash
# Gate for the Lean formalisation. It passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom` keyword (anywhere,
#    including one on a line of its own), `#eval`, `run_cmd`, `initialize`, `IO`, `set_option`,
#    or syntax-extension commands (`macro`, `elab`, `syntax`, `notation`, `import Lean`, ...),
#    which could redefine `#print axioms`;
#  * the library builds without errors;
#  * the gate itself (not a file in the repo) generates the `#print axioms` report for each
#    REQUIRED theorem, and each report is present exactly once;
#  * each REQUIRED theorem (with its transitive dependencies) uses only Lean's standard axioms
#    (propext, Classical.choice, Quot.sound).
# Trust boundary: the token filter is a heuristic over the project's .lean sources. The gate assumes
# the pinned toolchain, Mathlib and lake configuration are unmodified. It is not a sandbox, and it
# does not audit declarations other than the REQUIRED theorems.
# REQUIRED lists, fully qualified, every declaration cited in the accompanying paper plus one
# supporting theorem; definitions may use a subset of the standard axioms.
# Lean wraps long axiom lists across several lines, so the output is flattened before parsing.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="PlaneCubic"
LIB="CayleyBacharach"
REQUIRED="PlaneCubic PlaneCubic.AtLeastThree PlaneCubic.AtLeastThree.of_infinite PlaneCubic.CardGT PlaneCubic.Col4 PlaneCubic.CommonZero PlaneCubic.ExactlyMeetIn PlaneCubic.VanishesAt PlaneCubic.atLeastThree_iff_card PlaneCubic.card_add_one_le PlaneCubic.card_le_seven_of_not_atLeastThree PlaneCubic.cayley_bacharach PlaneCubic.cayley_bacharach_any PlaneCubic.cayley_bacharach_card3 PlaneCubic.cayley_bacharach_classical PlaneCubic.cayley_bacharach_classical_card PlaneCubic.cayley_bacharach_classical_card3 PlaneCubic.cayley_bacharach_classical_card8 PlaneCubic.cayley_bacharach_classical_finite PlaneCubic.cayley_bacharach_classical_fintype PlaneCubic.cayley_bacharach_classical_zmod3 PlaneCubic.cayley_bacharach_of_no_common_factor PlaneCubic.cayley_bacharach_of_no_common_factor_any PlaneCubic.classical_conic_case PlaneCubic.classical_line_case PlaneCubic.coeffs_eq_zero_of_forall_three PlaneCubic.col4_iff_exists_mulVec PlaneCubic.col4_iff_minors PlaneCubic.col4_iff_rank_le_two PlaneCubic.commonZero_iff PlaneCubic.conic_line_lemma PlaneCubic.conic_points PlaneCubic.conic_three PlaneCubic.conics_le_one PlaneCubic.conics_le_two PlaneCubic.conics_off_line_ge_two PlaneCubic.cross_eq_zero_iff_eq_smul PlaneCubic.cubic_four PlaneCubic.cubics_resid PlaneCubic.det_gram_eq_zero_iff PlaneCubic.det_gram_linMul PlaneCubic.det_gram_linMul_char_two PlaneCubic.eval PlaneCubic.evalC PlaneCubic.evalC_expand PlaneCubic.evalC_linMul PlaneCubic.evalC_smul_smul PlaneCubic.evalC_smul_vec PlaneCubic.eval_expand PlaneCubic.eval_mulLin PlaneCubic.eval_smul_smul PlaneCubic.eval_smul_vec PlaneCubic.exactlyMeetIn_iff PlaneCubic.exists_conic_off_line PlaneCubic.exists_linMul_of_det_gram_eq_zero PlaneCubic.false_of_conic PlaneCubic.finrank_cubicsThrough_le_two PlaneCubic.finrank_ker_evalMap_eq_two PlaneCubic.finrank_ker_evalMap_eq_two_any PlaneCubic.finrank_ker_evalMap_eq_two_iff PlaneCubic.finrank_ker_ge_of_conic PlaneCubic.finrank_ker_ge_of_line PlaneCubic.finrank_le_three_of_no3 PlaneCubic.general_position_of_no_common_factor PlaneCubic.gram PlaneCubic.gram_quadForm PlaneCubic.ker_evalMap_eq PlaneCubic.linMul PlaneCubic.line_comp_of_polar PlaneCubic.line_lemma PlaneCubic.line_lemma_false_zmod_two PlaneCubic.line_lemma_fintype PlaneCubic.line_points PlaneCubic.mem_onLine_iff_mem_ker PlaneCubic.mem_span_of_eight PlaneCubic.mulLin PlaneCubic.ne_zero_of_pairwise PlaneCubic.no_common_conic_card3 PlaneCubic.no_common_conic_of_exact PlaneCubic.no_common_line_card3 PlaneCubic.no_common_line_of_exact PlaneCubic.noncollinear_of_irreducible PlaneCubic.onLine PlaneCubic.pappus_clean PlaneCubic.pappus_generic PlaneCubic.pappus_lines_distinct PlaneCubic.pappus_of_cayley_bacharach PlaneCubic.pascal_clean PlaneCubic.pascal_clean_det PlaneCubic.pascal_generic PlaneCubic.pascal_of_cayley_bacharach PlaneCubic.pascal_points_off_conic PlaneCubic.polarC PlaneCubic.polarC_comm PlaneCubic.polarC_eq PlaneCubic.polarC_eq_bilin PlaneCubic.polarC_self PlaneCubic.vanishesAt_iff PlaneCubic.vanishesAt_smul_iff PlaneCubic.vanishesAt_smul_smul_iff"
SOURCES="CayleyBacharach/*.lean CayleyBacharach.lean"
[ -e .lake/packages/mathlib ] || lake exe cache get || { echo "FAIL: could not fetch Mathlib cache"; exit 1; }
if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
  echo "FAIL: forbidden token"; exit 1; fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
# The `#print axioms` queries are generated here rather than read from a file in the repo.
chk=$(mktemp --suffix=.lean -p . .gatecheck_XXXX)
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$')
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"

import Gtz.Design.StallLocus
import Gtz.Design.ComplementPairCriterion
import Gtz.Design.PivotGramIdempotent
import Gtz.Design.ResidualPairingLaw
import Gtz.Design.ComplementLeverageLaw
import Gtz.Design.NormalLeverageFloor
import Gtz.Design.FlatNormalBudget
import Gtz.Design.DirectionBudget
import Gtz.Design.LoadBearingTriple
import Gtz.Design.WholeLineMarginCriterion
import Gtz.Design.ComplementDeterminantLaw
import Gtz.Design.ComplementFormLaw
import Gtz.Design.TraceIdentity
import Gtz.Design.InverseTraceEscape
import Gtz.Design.ChartInverseTrace
import Gtz.Design.CrossLeverageBudget
import Gtz.Design.SharedAtomPivotExclusion
import Gtz.Design.OneLineCandidateExcess
import Gtz.Design.FlatCrossBudget
import Gtz.Design.DowndateInterlacing

/-!
# The grind vocabulary of the design layer

This module gives `grind` the domain rules of the design layer. It declares
39 equivalences of the layer as E-matching rules. It also declares two
multiplication patterns.

The module is a leaf. No module of the library imports it. Import it in an
attack file when you want the tactic power. The rules make elaboration slower
for each module that imports them.

## The measurement

The box is 191 goals of the 20 design modules that this file imports. Each
goal runs at 200000 heartbeats.

| tactic | solved | rate |
|---|---|---|
| `grind`, no rules | 4 | 2.1% |
| `bound` | 3 | 1.6% |
| `nlinarith` | 2 | 1.0% |
| `aesop` | 8 | 4.2% |
| the union of nine tactics | 12 | 6.3% |
| `grind`, with this module | 12 | 6.3% |

The union of the nine tactics and this module is 18 goals. This module reaches
six goals that no tactic of the box reaches. The two parts of the module are
disjoint. The rules alone give 10 goals. The patterns alone give 6 goals.

## Why the multiplication patterns are necessary

`grind` applies an ordered-ring rule backward against the goal. It does not
apply the rule forward from a hypothesis. The rule stays unused even when the
premise of the rule is a hypothesis of the goal.

Take a goal `1 + e - o >= 1 - p * (cap + 1)`, with the hypotheses
`o <= p * (e + 1)` and `e <= cap` and `0 <= p`. The goal needs one product
step, `p * (e + 1) <= p * (cap + 1)`. These four attempts fail:

- `grind`
- `grind [mul_le_mul_of_nonneg_left]`
- `attribute [grind ->] mul_le_mul_of_nonneg_left`
- the rule together with the premise `e + 1 <= cap + 1` as a hypothesis

The `grind_pattern` declarations of this module close the goal. Each pattern
names the two products of the rule. Then E-matching instantiates the rule
forward, and the linear part of `grind` completes the proof.
-/

set_option maxHeartbeats 400000

namespace Gtz

-- The multiplication patterns. Each one lets `grind` step a product forward.
grind_pattern mul_le_mul_of_nonneg_left => a * b, a * c

grind_pattern mul_le_mul_of_nonneg_right => b * a, c * a

-- The equivalences of the design layer, as E-matching rules.
attribute [grind] patternTightDominatedCoverProperty_iff_strictSelector
attribute [grind] dominates_iff_posSemidef_unitFrameSum
attribute [grind] directionChartTenthHeavyWeakToStrict_iff
attribute [grind] dominates_iff_posSemidef_smul_one_sub_subsetSum_compl
attribute [grind] compressed_dominates_iff
attribute [grind] posDef_insert_iff_no_common_null
attribute [grind] posDef_subsetSum_sub_one_iff_residualMatrix
attribute [grind] forall_gated_traceInverse_eq_one_iff_layer_eq_zero
attribute [grind] forall_circuitWindow_traceInverse_eq_one_iff_layer_eq_zero
attribute [grind] dominates_triple_iff_depthCap
attribute [grind] dominates_triple_iff_posSemidef_directionGramMatrix_submatrix
attribute [grind] dominates_triple_iff_posSemidef_correlationInvolution_submatrix
attribute [grind] dominates_triple_iff_posSemidef_hollowShift
attribute [grind] posSemidef_sub_vecMulVec_iff
attribute [grind] dominates_iff_posSemidef_unitFrameSum_six
attribute [grind] mem_dominationCone_iff
attribute [grind] isTie_iff_leverage_identity
attribute [grind] isTie_iff_rankTwo_planeLeverageIdentity
attribute [grind] dominatesAtLevel_iff_form
attribute [grind] posSemidef_sub_fieldAtom_iff
attribute [grind] stressFreeHingeHoldsSixThree_iff_no_stressFree_tie
attribute [grind] RatDesign.dominates_iff_cast
attribute [grind] posDef_pickSum_iff_det_atomColumnsOfPick_ne_zero
attribute [grind] stressFreeArmAt_iff_no_stressFree_tie
attribute [grind] posDef_subsetSum_sub_smul_one_iff_form
attribute [grind] posDef_subsetSum_iff_residualPairing
attribute [grind] traceInverse_eq_one_iff_sum_det_erase_eq_zero
attribute [grind] isTightDirectionOf_iff_mulVec_eq_zero
attribute [grind] erase_dominates_iff_pivot_le_one
attribute [grind] one_le_pivot_iff_det_le_adjugateReading
attribute [grind] erase_strictDominates_iff_pivot_lt_one
attribute [grind] stall_iff_forall_det_le_adjugateReading
attribute [grind] erase_dominates_iff_det_nonneg
attribute [grind] erase_dominates_iff_adjugateReading_le_det
attribute [grind] pairDominates_scaledAtomRows_iff_posSemidef
attribute [grind] planePairDominates_scaledAtomRows_iff_posSemidef
attribute [grind] planePairDominatesStrict_scaledAtomRows_iff_posDef
attribute [grind] dominates_triple_iff_posSemidef_tripleGapMatrix
attribute [grind] posDef_subsetSum_sub_one_iff_posDef_tripleGapMatrix

end Gtz

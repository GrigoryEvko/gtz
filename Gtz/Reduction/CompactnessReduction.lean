/-
# The compactness reduction: the boundary dichotomy PROVED, the sequential form
# REFUTED, and the shipped assembly's hypothesis shown TOO STRONG

The campaign proposed reducing `Gtz.GtzWeighted m k` to (a) the two rungs one size
down plus (b) the absence of an interior critical point below the threshold, by
compactifying the weight simplex and analysing the boundary.  Its Case B -- keep
the escaping atom, compress the survivors onto the orthogonal complement of its
direction -- was flagged as the weak point.  This file settles that step, and then
measures honestly what settling it buys.

## LEAD 1 -- SCOPE: THE INTERIOR HYPOTHESIS ALREADY IMPLIES THE GOAL

Read this before reading anything else in the file.  `Gtz.ChartGtzInterior` -- the
residue every assembly below is stated against -- implies `Gtz.GtzWeighted` at the
same size in four lines and with NO ladder, NO smaller rung and NO factorisation
leaf (`Gtz.gtzWeighted_of_chartGtzInterior`): a weighted design's chart point has
all weights positive, so the interior hypothesis applies to it directly.  It also
implies the full CLOSED statement `Gtz.ChartGtz` at the same size, again with no
smaller rungs, by mixing the weights toward uniform and letting the mixing tend to
zero (`Gtz.chartGtz_of_chartGtzInterior`; the finitely many candidate selections
let one mixing parameter serve them all).

Consequence, stated flatly: `Gtz.chartGtz_of_smaller_of_interior` and
`Gtz.chartGtz_of_interior` are SUBSUMED -- strictly more hypotheses for the same
conclusion -- and the boundary machinery is NOT load bearing for them.  What the
boundary machinery is load bearing for is `Gtz.weight_pos_of_forall_not_chartDominates`
(LEAD 3), and the difference is exactly the difference between the brief's
hypothesis (b) and `Gtz.ChartGtzInterior`.

## LEAD 2 -- THE SEQUENTIAL FORM IS REFUTED AT EVERY POSITIVE WEIGHT

`Gtz.CompressionLiftClaim` states Case B at an ARBITRARY weight at the escaping
label, i.e. as it would have to hold ALONG a minimizing sequence rather than only
at its limit.  `Gtz.not_compressionLiftClaim` REFUTES it, and
`Gtz.not_eventualCompressionLiftClaim` refutes the weaker reading that asks only
for SOME positive weight threshold below which Case B holds.  The witness is exact
and rational, and is a one-parameter family: `Gtz.liftFailureChart` on four
indices, rank two, every diagonal entry positive, carried with the weight
`pivotWeight` at the label `1` and `(1 - pivotWeight)/3` at the other three
(`Gtz.liftFailurePointAt`; the uniform-weight point `Gtz.liftFailurePoint` is its
`1/4` member).  At the label `1` the pivot is `1/3`, so at weight `1/4` the atom is
HEAVY (leverage `4/3 > 1`, `Gtz.liftFailure_isAllHeavy` -- the refutation is NOT
hiding in the light-atom branch `Gtz.dominating_of_light_atom` discharges for
free); the compressed point's gap at the survivor is EXACTLY zero at EVERY weight
(`Gtz.liftFailurePointAt_compressedGap_eq_zero`, a FROZEN tie, hence no margin at
any parameter value); and the lifted two-element selection fails at every positive
weight, at the probe `(-1, 1 + pivotWeight, 0, 0)`, with value
`-(1/3)(1 + t)t(2 + 3t)` (`Gtz.not_chartDominates_liftFailurePointAt`).  At `1/4`
the probe `(1, -4, 0, 0)` gives `-11/12` (`Gtz.not_chartDominates_liftFailure`).

The failure is LOCALISED.  `Gtz.chartDominates_image_of_chartPointDelete` shows the
deletion half of the lift is unconditional in the weight -- the renormalisation
`1/(1 - t_z) >= 1` is favourable.  The whole deficit sits at the Schur pivot: at
weight zero the upstairs pivot is `P_zz` and the deflation subtracts
`(P e_z)(P e_z)ᵀ / P_zz`, so the debt is paid on the nose; at weight `t_z > 0` the
upstairs pivot degrades to `P_zz - t_z` while the deflation still subtracts
`... / P_zz`, and the shortfall is first order in `t_z` against a downstairs margin
that the family freezes at zero.  So Case B must be stated at the LIMIT POINT; this
is the same shape as the recorded no-margin no-go -- ties exist, so nothing first
order can be paid for.

The frozen tie is NECESSARY, not incidental.  [EXACT, not mechanized] Perturbing
the family so the downstairs gap is `d > 0` instead of `0` gives upstairs
determinant `(d - t - 4 d t + 3 d t^2)/3`, which is `-t/3` at `d = 0` (negative at
every `t > 0`, which is the theorem above) but tends to `d/3 > 0` as `t -> 0` for
every `d > 0`.  A positive downstairs margin therefore DOES absorb the first-order
deficit once `t` is below roughly `d`.  Any claim that the sequential form fails
even with a positive downstairs margin is true only for weights bounded away from
zero and must not be read as strengthening the refutation.

## LEAD 3 -- AT THE LIMIT POINT THE BOUNDARY IS FREE, AND PROVED

`Gtz.exists_chartDominates_of_weight_eq_zero` is unconditional given the two
smaller rungs.  Its two cases are exhaustive by `|P e_z|² = P_zz`
(`Gtz.chartPointColumn_dotProduct_self`):

* `P_zz = 0` (ATOM-VANISHING) kills the whole column
  (`Gtz.chartPointColumn_eq_zero_of_diag_eq_zero`), so the survivors carry a
  genuine rank-preserving chart point one size down.  Consumes `(size, rank + 1)`.
  NOTE the campaign brief's reason for this case -- "deleting the zero row leaves
  the rows still summing to `I`" -- is FALSE at positive weight; the correct reason
  is the pivot identity above, and it is a statement about the chart, not the
  frame.
* `P_zz > 0` (DIRECTION-ESCAPE) deflates at the pivot, deletes the label, and
  lifts by one completion of the square (`Gtz.chartDominates_insert_of_deflate`).
  Consumes `(size, rank)`.

Both branches drop the SIZE by one, so any induction on this dichotomy is well
founded on the size ALONE; the rank window is a consequence, not an extra
hypothesis.  Nothing is transported: no margin, no rate, no subsequence, no further
extraction.  In particular the reduction is immune to the recorded drop-transfer
no-go for a structural reason -- there is nothing to transfer.

WHERE THIS IS NOT SUBSUMED, precisely.  Package the dichotomy as
`Gtz.weight_pos_of_forall_not_chartDominates`: given the two smaller rungs, EVERY
counterexample point is interior.  That is a statement about the GIVEN point, and
LEAD 1's density argument cannot replace it: density only moves SOME counterexample
into the interior, destroying whatever distinguished the original one.  A
compactness argument minimises a continuous objective over the CLOSED domain, where
the infimum is attained; to conclude that the minimiser carries first-order
(Clarke) data one needs that very minimiser to be interior, which is what this
packaging supplies and what density does not.  The interior is not compact, so
minimising there instead is not an option.  This is the whole reason the brief's
hypothesis (b) -- about interior CRITICAL points -- is weaker than
`Gtz.ChartGtzInterior`, and the only reason the boundary work is worth having.

## WHY THE CHART AND NOT THE DESIGN

`Gtz.ChartPoint` is the compactification of `Gtz.WeightedDesign`: same symmetric
idempotent chart of trace `rank`, but weights only NONNEGATIVE.  In the `(g, t)`
coordinates the boundary is singular (`g_c = v_c / sqrt t_c` blows up, and the
brief's `|Pperp v_c| / sqrt t_c` is an indeterminate `0/0`); in the chart the gap
`P - diag t` is AFFINE in `t` and extends continuously, and the `0/0` never forms
because the compression direction is the escaper's OWN direction.  The brief's
worry that the running direction differs from the limit direction is therefore
vacuous, and the compression is realised as the Schur complement of the chart
pivot (`Gtz.deflatedChartMatrix`) with no basis of the orthogonal complement chosen
and no square root anywhere.

## THE TRANSVERSE GAP CLAIM, CORRECTED

`Gtz.dotProduct_chartPointGap_eq_deflated_add_pivot` is the honest form of the
brief's "strict transverse gap `t_z/(1 - t_z)`": the upstairs gap form exceeds the
deflated one by exactly the rank-one PIVOT term.  That excess is the quantity the
Schur step must SPEND, not spare slack available to pay a cross term.  In the
`(g, t)` picture the advertised gap is literally `1/(1 - t_z)` times the downstairs
gap, i.e. a restatement of the induction hypothesis carrying zero information.

## WHAT IS AND IS NOT DELIVERED -- the ledger

PROVED (kernel-checked here, axioms `[propext, Classical.choice, Quot.sound]`
only):
  the closed chart domain and its gap; the pivot identity; deflation preserves
  symmetry, idempotency and drops the trace by one; deletion of a dead index;
  the unconditional deletion lift; the Schur step at vanishing weight; the boundary
  dichotomy and its counterexample-is-interior packaging; the singleton criterion;
  the ambient/submatrix Rayleigh dictionary in BOTH directions;
  `Gtz.dominates_iff_chartDominates`; `Gtz.gtzWeighted_of_chartGtz`; the weight
  relaxation and its gap identity; the density theorem
  `Gtz.chartGtz_of_chartGtzInterior` and its weighted corollary
  `Gtz.gtzWeighted_of_chartGtzInterior`; the (subsumed) per-rung reduction and
  size-induction ladder; both base rungs.

REFUTED AND RECORDED: `Gtz.CompressionLiftClaim` at positive weight, and
`Gtz.EventualCompressionLiftClaim` -- Case B below ANY positive weight threshold.

STATED WITH HYPOTHESIS: `Gtz.chartGtz_of_smaller_of_interior`,
`Gtz.chartGtz_of_interior`, `Gtz.gtzWeighted_of_interior` take
`Gtz.ChartGtzInterior` as a hypothesis (and are subsumed -- LEAD 1);
`Gtz.weight_pos_of_forall_not_chartDominates` takes the two smaller rungs;
`Gtz.chartGtzInterior_of_gtzWeighted` takes `Gtz.ChartPointHasDesign`.

UNPROVED LEAVES, all of them, named:
  1. `Gtz.ChartGtzInterior` -- domination at chart points with all weights
     strictly positive.  By LEAD 1 this is not a residue at all: it IMPLIES the
     weighted goal at that size outright.  It is NOT the brief's hypothesis (b),
     which is genuinely weaker: obtaining `Gtz.ChartGtzInterior` from "no interior
     critical point below the threshold" needs compactness of the closed chart
     domain plus ATTAINMENT of the infimum of a max-of-eigenvalue objective, plus a
     Clarke subdifferential calculus, plus LEAD 3's packaging to place the
     minimiser in the interior.  Mathlib has `isCompact_stdSimplex` and
     `Gtz.lambdaMinMat` with `Gtz.continuous_lambdaMinMat`, and this repository has
     `Gtz.isCompact_collaredSet` / `Gtz.isClosed_collaredSet` for the DESIGN
     configuration class (which compactifies away from the boundary, i.e.
     complementary to what is needed here), but there is NO nonsmooth-analysis
     layer anywhere, so that decomposition is not available and is not attempted.
  2. `Gtz.ChartPointHasDesign` -- the factorisation `P = V Vᵀ`, needing an
     orthonormal basis of the range of `P`.  Only the design-to-chart direction is
     shipped (`Gtz.chartPointOfDesign`).  This is the SOLE obstruction to feeding
     the already kernel-checked small rungs (`Gtz.gtzWeighted_of_le_five`,
     `Gtz.gtz_rank_two`, `Gtz.gtzWeighted_corank_two`) into any chart-side
     assembly.  CORRECTING an optimistic reading from the campaign notes: those
     theorems discharge the smaller rungs in the DESIGN form, and the chart-side
     statements consume the CHART form; the two are connected only through this
     leaf.  The leaf is TRUE (spectral theorem) and not vacuous, merely
     unmechanized.

## THE OBJECTIVE MISMATCH -- a defect in the brief's hypothesis (b)

The brief states (b) for `F(D) = max_C lambda_min(S_C)` with threshold one.  The
object a compactness argument on the chart produces is a minimiser of the CHART
objective `max_C lambda_min(W[C])` with threshold zero.  The two agree on their
THRESHOLD -- that is exactly `Gtz.dominates_iff_chartDominates`, via A1's
positive-diagonal congruence -- but NOT on their minimisers, because the congruence
`diagonal (sqrt t_C)` rescales non-uniformly, so a critical point of one is not a
critical point of the other.  Hypothesis (b) as written is therefore not what the
argument delivers, and any A2 harvest phrased for `F`
(`Gtz.Quantitative.CriticalQuadric`) does not transfer to the chart system as
stated.  Recorded, not repaired: this file states no stationarity hypothesis at all.

## THE CIRCULARITY FIREWALL

`Gtz.ChartGtzInterior` is a hypothesis in every statement that uses it, never
something derived, so the conditionality is in the types and not only in this
prose.  It is NOT weaker than the target and is not claimed to be: it implies
`Gtz.GtzWeighted` at that size with no leaf at all
(`Gtz.gtzWeighted_of_chartGtzInterior`), and with the factorisation leaf the
implication reverses (`Gtz.chartGtzInterior_of_gtzWeighted`), so the two are
equivalent.  The NET content of this file is therefore: the boundary of the
compactification is free, the crux that was supposed to be hard there is an
identity, and the sequential reading of that crux is false.  Whether the
compactness reduction BUYS anything turns entirely on Step 1 -- deriving the
interior obligation from a critical-point hypothesis -- which is untouched here.
Do not read the boundary result as progress on Step 1.

## PROVENANCE AND WIRING

The chart is `Gtz.LinAlg.ProjectionForm`'s (`Gtz.projectionOfDesign`,
`Gtz.projectionOfDesign_transpose`, `Gtz.projectionOfDesign_mul_self`,
`Gtz.trace_projectionOfDesign`), imported and not re-derived;
`Gtz.dominates_iff_posSemidef_projectionBlock_finset` is A1 and is what
`Gtz.dominates_iff_chartDominates` rides on.  `Gtz.Design.ProjectionChart`'s
field-generic copy is NOT used, and neither are the three rank-three
specialisations that file's header enumerates.  Nothing here duplicates
`Gtz.Reduction.Compression` (which compresses a DESIGN onto a subspace, at
positive weight) or `Gtz.Reduction.Deflation` (which DROPS a light atom); the
object below keeps the escaper and works at the boundary, which neither does.

This module is currently an ORPHAN: nothing imports it, so it is outside `Gtz.lean`'s
closure, outside the default `lake build` target and outside `Gtz/Audit.lean`'s
ledger, and nothing regression-protects it.  The only other genuinely orphaned
module in the repository is `Gtz.Ties.DiamondTie`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The closed chart domain -/

/-- A point of the CLOSED chart domain: a symmetric idempotent `chart` of trace
`rank` on the index space, together with NONNEGATIVE weights summing to one.

The boundary is included -- `weight` may vanish -- which is the whole point: this
is the compactification of `Gtz.WeightedDesign`, whose `weight_pos` field forbids
the boundary.  The domain is a PRODUCT: no compatibility constraint ties `chart`
to `weight`.

Note the chart, not the design, is primitive here.  In the `(g, t)` coordinates
the boundary `t_c -> 0` is singular (`g_c = v_c / sqrt t_c` blows up); in these
coordinates the gap `chart - diagonal weight` is AFFINE in `weight` and extends
continuously to the boundary.  That is the reason every boundary statement below
is an identity rather than an estimate. -/
structure ChartPoint (size rank : ℕ) where
  /-- The projection chart `P = V Vᵀ` on the index space. -/
  chart : Matrix (Fin size) (Fin size) ℝ
  /-- The weights, allowed to VANISH (this is the closed domain). -/
  weight : Fin size → ℝ
  /-- The chart is symmetric. -/
  isSymmetric : chartᵀ = chart
  /-- The chart is idempotent -- over ℝ with symmetry this is "orthogonal projection". -/
  isIdempotent : chart * chart = chart
  /-- The chart's trace is the rank. -/
  hasTraceRank : Matrix.trace chart = (rank : ℝ)
  /-- Weights are nonnegative. -/
  weight_nonneg : ∀ atomIndex, 0 ≤ weight atomIndex
  /-- Weights sum to one. -/
  weight_sum_one : ∑ atomIndex, weight atomIndex = 1

/-- The chart gap `W = P - diag t`.  Domination is `W[C] ⪰ 0`, weight-free in the
`(g, t)` picture and AFFINE in `t` here. -/
def chartPointGap (point : ChartPoint size rank) : Matrix (Fin size) (Fin size) ℝ :=
  point.chart - Matrix.diagonal point.weight

/-- The chart gap is symmetric. -/
theorem chartPointGap_transpose (point : ChartPoint size rank) :
    (chartPointGap point)ᵀ = chartPointGap point := by
  rw [chartPointGap, Matrix.transpose_sub, point.isSymmetric, Matrix.diagonal_transpose]

/-- Domination at a chart point, in AMBIENT Rayleigh form: the gap's quadratic
form is nonnegative on every vector supported on the selection.

Stated ambient rather than as a submatrix `PosSemidef` on purpose -- it is what
makes the Schur step below one line of completing the square, with no block
reindexing anywhere.  `chartDominates_iff_posSemidef_submatrix` proves the two
readings agree. -/
def ChartDominates (point : ChartPoint size rank) (selected : Finset (Fin size)) : Prop :=
  ∀ probe : Fin size → ℝ, (∀ atomIndex, atomIndex ∉ selected → probe atomIndex = 0) →
    0 ≤ probe ⬝ᵥ (chartPointGap point *ᵥ probe)

/-- Weighted GTZ on the CLOSED chart domain at size `(size, rank)`.  Strictly
stronger than `Gtz.GtzWeighted size rank` as a hypothesis, because it also
constrains boundary points; `gtzWeighted_of_chartGtz` is the easy direction. -/
def ChartGtz (size rank : ℕ) : Prop :=
  ∀ point : ChartPoint size rank, ∃ selected : Finset (Fin size),
    selected.card = rank ∧ ChartDominates point selected

/-- The chart is symmetric, entrywise. -/
theorem chartPoint_apply_comm (point : ChartPoint size rank) (rowIndex colIndex : Fin size) :
    point.chart colIndex rowIndex = point.chart rowIndex colIndex := by
  have hentry := congrFun (congrFun point.isSymmetric rowIndex) colIndex
  rwa [Matrix.transpose_apply] at hentry

/-- The pivot column `P e_z` of the chart at an index. -/
def chartPointColumn (point : ChartPoint size rank) (pivotIndex : Fin size) : Fin size → ℝ :=
  fun atomIndex => point.chart atomIndex pivotIndex

/-- **The chart is a projector on its own columns**: `P (P e_z) = P e_z`. -/
theorem chartPoint_mulVec_column (point : ChartPoint size rank) (pivotIndex : Fin size) :
    point.chart *ᵥ chartPointColumn point pivotIndex = chartPointColumn point pivotIndex := by
  funext atomIndex
  have hentry := congrFun (congrFun point.isIdempotent atomIndex) pivotIndex
  rw [Matrix.mul_apply] at hentry
  simpa only [Matrix.mulVec, dotProduct, chartPointColumn] using hentry

/-- **The pivot identity `|P e_z|² = P_zz`** -- the single fact that makes the
boundary dichotomy `P_zz = 0` versus `P_zz > 0` exhaustive AND makes the
vanishing case kill an entire row. -/
theorem chartPointColumn_dotProduct_self (point : ChartPoint size rank)
    (pivotIndex : Fin size) :
    chartPointColumn point pivotIndex ⬝ᵥ chartPointColumn point pivotIndex
      = point.chart pivotIndex pivotIndex := by
  have hentry := congrFun (congrFun point.isIdempotent pivotIndex) pivotIndex
  rw [Matrix.mul_apply] at hentry
  rw [dotProduct, ← hentry]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [chartPointColumn, chartPoint_apply_comm point pivotIndex atomIndex]

/-- Pairing against the pivot column is evaluating `P` at the pivot index. -/
theorem chartPointColumn_dotProduct (point : ChartPoint size rank) (pivotIndex : Fin size)
    (probe : Fin size → ℝ) :
    chartPointColumn point pivotIndex ⬝ᵥ probe = (point.chart *ᵥ probe) pivotIndex := by
  simp only [dotProduct, Matrix.mulVec, chartPointColumn]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [chartPoint_apply_comm point pivotIndex atomIndex]

/-- The chart's diagonal is nonnegative. -/
theorem chartPoint_diag_nonneg (point : ChartPoint size rank) (pivotIndex : Fin size) :
    0 ≤ point.chart pivotIndex pivotIndex := by
  rw [← chartPointColumn_dotProduct_self point pivotIndex, dotProduct]
  exact Finset.sum_nonneg fun atomIndex _ => mul_self_nonneg _

/-- **The atom-vanishing case in one line**: a vanishing chart diagonal entry
kills the WHOLE column (hence, by symmetry, the whole row).  This is why Case A
of the boundary dichotomy is free -- and it is NOT the reason the campaign brief
gives ("deleting the zero row leaves rows summing to `I`", which is false at
positive weight). -/
theorem chartPointColumn_eq_zero_of_diag_eq_zero (point : ChartPoint size rank)
    {pivotIndex : Fin size} (hdiag : point.chart pivotIndex pivotIndex = 0)
    (atomIndex : Fin size) : point.chart atomIndex pivotIndex = 0 := by
  have hsum : ∑ rowIndex, point.chart rowIndex pivotIndex * point.chart rowIndex pivotIndex
      = 0 := by
    rw [← hdiag, ← chartPointColumn_dotProduct_self point pivotIndex, dotProduct]
    rfl
  have hterm : point.chart atomIndex pivotIndex * point.chart atomIndex pivotIndex = 0 :=
    le_antisymm
      (hsum ▸ Finset.single_le_sum
        (f := fun rowIndex => point.chart rowIndex pivotIndex * point.chart rowIndex pivotIndex)
        (fun rowIndex _ => mul_self_nonneg _) (Finset.mem_univ atomIndex))
      (mul_self_nonneg _)
  exact mul_self_eq_zero.mp hterm

/-! ## Two rank-one brackets -/

/-- Left multiplication pushes into a rank-one factor. -/
theorem matrix_mul_vecMulVec {ambient : ℕ} (form : Matrix (Fin ambient) (Fin ambient) ℝ)
    (leftVec rightVec : Fin ambient → ℝ) :
    form * Matrix.vecMulVec leftVec rightVec
      = Matrix.vecMulVec (form *ᵥ leftVec) rightVec := by
  ext rowIndex colIndex
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Right multiplication pushes into a rank-one factor, through the transpose. -/
theorem vecMulVec_mul_matrix {ambient : ℕ} (form : Matrix (Fin ambient) (Fin ambient) ℝ)
    (leftVec rightVec : Fin ambient → ℝ) :
    Matrix.vecMulVec leftVec rightVec * form
      = Matrix.vecMulVec leftVec (formᵀ *ᵥ rightVec) := by
  ext rowIndex colIndex
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The rank-one quadratic form. -/
theorem dotProduct_vecMulVec_mulVec {ambient : ℕ} (leftVec probe : Fin ambient → ℝ) :
    probe ⬝ᵥ (Matrix.vecMulVec leftVec leftVec *ᵥ probe) = (leftVec ⬝ᵥ probe) ^ 2 := by
  rw [vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, dotProduct_comm probe leftVec]
  ring

/-! ## Deflation at a pivot: the compression, chart-side -/

/-- **The deflated chart** `P' = P - (P e_z)(P e_z)ᵀ / P_zz`.

This IS the "compress the survivors onto the orthogonal complement of `v_z`" step
of the campaign brief, in chart coordinates: the Gram matrix of the compressed
survivors is exactly the Schur complement of the pivot `P_zz`, so no basis of
`v_z`-perp has to be chosen and no square root appears.  One division, by the
pivot. -/
noncomputable def deflatedChartMatrix (point : ChartPoint size rank) (pivotIndex : Fin size) :
    Matrix (Fin size) (Fin size) ℝ :=
  point.chart - (point.chart pivotIndex pivotIndex)⁻¹ •
    Matrix.vecMulVec (chartPointColumn point pivotIndex) (chartPointColumn point pivotIndex)

theorem deflatedChartMatrix_transpose (point : ChartPoint size rank) (pivotIndex : Fin size) :
    (deflatedChartMatrix point pivotIndex)ᵀ = deflatedChartMatrix point pivotIndex := by
  rw [deflatedChartMatrix, Matrix.transpose_sub, Matrix.transpose_smul, point.isSymmetric]
  congr 2
  ext rowIndex colIndex
  simp only [Matrix.transpose_apply, Matrix.vecMulVec_apply]
  ring

/-- **The design-free deflation bracket**: subtracting `pivot⁻¹` times a rank-one
piece absorbed on both sides of an idempotent leaves an idempotent.  Stated
abstractly so the chart instance below is three one-line side conditions. -/
theorem rankOneDeflation_mul_self {ambient : ℕ}
    {base rankOne : Matrix (Fin ambient) (Fin ambient) ℝ} {pivotValue : ℝ}
    (hbase : base * base = base) (hleft : base * rankOne = rankOne)
    (hright : rankOne * base = rankOne)
    (hsquare : rankOne * rankOne = pivotValue • rankOne) (hpivot : pivotValue ≠ 0) :
    (base - pivotValue⁻¹ • rankOne) * (base - pivotValue⁻¹ • rankOne)
      = base - pivotValue⁻¹ • rankOne := by
  have hexpand : (base - pivotValue⁻¹ • rankOne) * (base - pivotValue⁻¹ • rankOne)
      = base * base - pivotValue⁻¹ • (base * rankOne) - pivotValue⁻¹ • (rankOne * base)
        + (pivotValue⁻¹ * pivotValue⁻¹) • (rankOne * rankOne) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub,
      smul_smul]
    abel
  have hcollapse : pivotValue⁻¹ * pivotValue⁻¹ * pivotValue = pivotValue⁻¹ := by
    field_simp
  rw [hexpand, hbase, hleft, hright, hsquare, smul_smul, hcollapse]
  abel

/-- **The deflated chart is again idempotent.**  Three cancellations, each an
instance of `P (P e_z) = P e_z` or `|P e_z|² = P_zz`. -/
theorem deflatedChartMatrix_mul_self (point : ChartPoint size rank) {pivotIndex : Fin size}
    (hpivot : point.chart pivotIndex pivotIndex ≠ 0) :
    deflatedChartMatrix point pivotIndex * deflatedChartMatrix point pivotIndex
      = deflatedChartMatrix point pivotIndex := by
  have hcolumn := chartPoint_mulVec_column point pivotIndex
  have hnorm := chartPointColumn_dotProduct_self point pivotIndex
  have htransposeColumn :
      point.chartᵀ *ᵥ chartPointColumn point pivotIndex = chartPointColumn point pivotIndex := by
    rw [point.isSymmetric]; exact hcolumn
  rw [deflatedChartMatrix]
  refine rankOneDeflation_mul_self point.isIdempotent ?_ ?_ ?_ hpivot
  · rw [matrix_mul_vecMulVec, hcolumn]
  · rw [vecMulVec_mul_matrix, htransposeColumn]
  · rw [vecMulVec_mul_vecMulVec, hnorm]

/-- The deflated chart's pivot column vanishes identically. -/
theorem deflatedChartMatrix_column_eq_zero (point : ChartPoint size rank)
    {pivotIndex : Fin size} (hpivot : point.chart pivotIndex pivotIndex ≠ 0)
    (atomIndex : Fin size) : deflatedChartMatrix point pivotIndex atomIndex pivotIndex = 0 := by
  have hnorm := chartPointColumn_dotProduct_self point pivotIndex
  simp only [deflatedChartMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, chartPointColumn]
  have hpivotValue : point.chart pivotIndex pivotIndex ≠ 0 := hpivot
  field_simp
  ring

/-- Deflation drops the trace by exactly one. -/
theorem trace_deflatedChartMatrix (point : ChartPoint size rank) {pivotIndex : Fin size}
    (hpivot : point.chart pivotIndex pivotIndex ≠ 0) :
    Matrix.trace (deflatedChartMatrix point pivotIndex) = (rank : ℝ) - 1 := by
  have hnorm := chartPointColumn_dotProduct_self point pivotIndex
  rw [deflatedChartMatrix, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_vecMulVec,
    hnorm, point.hasTraceRank, smul_eq_mul, inv_mul_cancel₀ hpivot]

/-- **The deflated chart point**: same weights, chart deflated at the pivot, rank
dropped by exactly one.  Stated `rank + 1 -> rank` so no truncated subtraction
appears. -/
noncomputable def deflatePoint (point : ChartPoint size (rank + 1)) (pivotIndex : Fin size)
    (hpivot : 0 < point.chart pivotIndex pivotIndex) : ChartPoint size rank where
  chart := deflatedChartMatrix point pivotIndex
  weight := point.weight
  isSymmetric := deflatedChartMatrix_transpose point pivotIndex
  isIdempotent := deflatedChartMatrix_mul_self point hpivot.ne'
  hasTraceRank := by
    rw [trace_deflatedChartMatrix point hpivot.ne']
    push_cast
    ring
  weight_nonneg := point.weight_nonneg
  weight_sum_one := point.weight_sum_one

/-- **The transverse comparison, honestly.**  On EVERY probe the upstairs gap form
exceeds the deflated gap form by exactly the rank-one pivot term
`(P e_z . probe)² / P_zz`.

This is the chart-side content of the campaign brief's "strict transverse gap
`t_z/(1 - t_z)`", and the reading has to be corrected: the excess is the PIVOT
term, the very quantity the Schur step must spend, not spare slack available to
pay a cross term.  In the `(g, t)` picture the advertised gap is literally
`1/(1 - t_z)` times the downstairs gap, i.e. a restatement of the induction
hypothesis carrying zero extra information. -/
theorem dotProduct_chartPointGap_eq_deflated_add_pivot (point : ChartPoint size rank)
    (pivotIndex : Fin size) (probe : Fin size → ℝ) :
    probe ⬝ᵥ (chartPointGap point *ᵥ probe)
      = probe ⬝ᵥ ((deflatedChartMatrix point pivotIndex - Matrix.diagonal point.weight)
            *ᵥ probe)
        + (point.chart pivotIndex pivotIndex)⁻¹
            * (chartPointColumn point pivotIndex ⬝ᵥ probe) ^ 2 := by
  have hshape : deflatedChartMatrix point pivotIndex - Matrix.diagonal point.weight
      = chartPointGap point - (point.chart pivotIndex pivotIndex)⁻¹ •
          Matrix.vecMulVec (chartPointColumn point pivotIndex)
            (chartPointColumn point pivotIndex) := by
    rw [deflatedChartMatrix, chartPointGap]
    abel
  rw [hshape, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, dotProduct_vecMulVec_mulVec]
  ring

/-! ## Deleting a dead index -/

/-- The surviving weights sum to `1 - t_z`. -/
theorem sum_weight_succAbove (point : ChartPoint (size + 1) rank)
    (deadIndex : Fin (size + 1)) :
    ∑ atomIndex : Fin size, point.weight (deadIndex.succAbove atomIndex)
      = 1 - point.weight deadIndex := by
  have hsplit := Fin.sum_univ_succAbove point.weight deadIndex
  rw [point.weight_sum_one] at hsplit
  linarith

/-- A principal submatrix that drops an index whose COLUMN vanishes commutes with
squaring -- so idempotency survives the deletion. -/
theorem submatrix_mul_self_of_column_eq_zero {ambient : ℕ}
    (form : Matrix (Fin (ambient + 1)) (Fin (ambient + 1)) ℝ)
    (deadIndex : Fin (ambient + 1)) (hcolumn : ∀ atomIndex, form atomIndex deadIndex = 0) :
    form.submatrix deadIndex.succAbove deadIndex.succAbove
        * form.submatrix deadIndex.succAbove deadIndex.succAbove
      = (form * form).submatrix deadIndex.succAbove deadIndex.succAbove := by
  ext rowIndex colIndex
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_succAbove
    (fun colRunner => form (deadIndex.succAbove rowIndex) colRunner
      * form colRunner (deadIndex.succAbove colIndex)) deadIndex,
    hcolumn (deadIndex.succAbove rowIndex), zero_mul, zero_add]

/-- Deleting an index drops the trace by that index's diagonal entry. -/
theorem trace_submatrix_succAbove {ambient : ℕ}
    (form : Matrix (Fin (ambient + 1)) (Fin (ambient + 1)) ℝ)
    (deadIndex : Fin (ambient + 1)) :
    Matrix.trace (form.submatrix deadIndex.succAbove deadIndex.succAbove)
      = Matrix.trace form - form deadIndex deadIndex := by
  have hsplit := Fin.sum_univ_succAbove (fun runner => form runner runner) deadIndex
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  rw [hsplit]
  ring

/-- **Restricting a quadratic form to the survivors** of an index the probe
already ignores.  This is the only bookkeeping lemma the whole boundary argument
needs -- no block matrix and no reindexing equivalence appears. -/
theorem dotProduct_mulVec_submatrix_succAbove {ambient : ℕ}
    (form : Matrix (Fin (ambient + 1)) (Fin (ambient + 1)) ℝ)
    (deadIndex : Fin (ambient + 1)) {probe : Fin (ambient + 1) → ℝ}
    (hdead : probe deadIndex = 0) :
    probe ⬝ᵥ (form *ᵥ probe)
      = (fun atomIndex => probe (deadIndex.succAbove atomIndex))
          ⬝ᵥ (form.submatrix deadIndex.succAbove deadIndex.succAbove
                *ᵥ fun atomIndex => probe (deadIndex.succAbove atomIndex)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  rw [Fin.sum_univ_succAbove
    (fun rowRunner => probe rowRunner
      * ∑ colRunner, form rowRunner colRunner * probe colRunner) deadIndex,
    hdead, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun rowIndex _ => ?_
  congr 1
  rw [Fin.sum_univ_succAbove
    (fun colRunner => form (deadIndex.succAbove rowIndex) colRunner * probe colRunner) deadIndex,
    hdead, mul_zero, zero_add]

/-- **Delete a dead index.**  The index must carry a vanishing chart COLUMN (hence
a vanishing diagonal entry, hence -- by `chartPointColumn_eq_zero_of_diag_eq_zero`
-- nothing more than a vanishing diagonal entry is really being asked) and a
weight below one; the surviving weights are renormalised by `1/(1 - t_z)`.

The rank is UNCHANGED: the deleted index contributed zero trace. -/
noncomputable def chartPointDelete (point : ChartPoint (size + 1) rank)
    (deadIndex : Fin (size + 1)) (hweight : point.weight deadIndex < 1)
    (hcolumn : ∀ atomIndex, point.chart atomIndex deadIndex = 0) : ChartPoint size rank where
  chart := point.chart.submatrix deadIndex.succAbove deadIndex.succAbove
  weight := fun atomIndex =>
    point.weight (deadIndex.succAbove atomIndex) / (1 - point.weight deadIndex)
  isSymmetric := by
    rw [Matrix.transpose_submatrix, point.isSymmetric]
  isIdempotent := by
    rw [submatrix_mul_self_of_column_eq_zero point.chart deadIndex hcolumn, point.isIdempotent]
  hasTraceRank := by
    rw [trace_submatrix_succAbove, point.hasTraceRank, hcolumn deadIndex, sub_zero]
  weight_nonneg := fun atomIndex =>
    div_nonneg (point.weight_nonneg _) (by linarith)
  weight_sum_one := by
    rw [← Finset.sum_div, sum_weight_succAbove point deadIndex]
    exact div_self (by linarith)

/-- **The deletion lift, unconditional in the deleted weight.**  A dominating
selection downstairs lifts verbatim, at ANY `t_z < 1`: the renormalisation
`1/(1 - t_z) >= 1` makes the downstairs gap SMALLER than the restricted upstairs
gap, so the transfer is favourable.

The boundary hypothesis `t_z = 0` is NOT needed here.  It is needed at exactly one
place, the Schur pivot of `chartDominates_insert_of_deflate` -- which is why the
refutation below lands there and nowhere else. -/
theorem chartDominates_image_of_chartPointDelete (point : ChartPoint (size + 1) rank)
    (deadIndex : Fin (size + 1)) (hweight : point.weight deadIndex < 1)
    (hcolumn : ∀ atomIndex, point.chart atomIndex deadIndex = 0)
    (selectedDown : Finset (Fin size))
    (hdown : ChartDominates (chartPointDelete point deadIndex hweight hcolumn) selectedDown) :
    ChartDominates point (selectedDown.image deadIndex.succAbove) := by
  classical
  intro probe hsupport
  have hpositive : 0 < 1 - point.weight deadIndex := by linarith
  have hdead : probe deadIndex = 0 := by
    refine hsupport deadIndex fun hmem => ?_
    obtain ⟨atomIndex, _, heq⟩ := Finset.mem_image.mp hmem
    exact Fin.succAbove_ne deadIndex atomIndex heq
  have hsupportDown : ∀ atomIndex : Fin size, atomIndex ∉ selectedDown →
      probe (deadIndex.succAbove atomIndex) = 0 := by
    intro atomIndex hnot
    refine hsupport _ fun hmem => ?_
    obtain ⟨other, hother, heq⟩ := Finset.mem_image.mp hmem
    exact hnot (Fin.succAbove_right_injective heq ▸ hother)
  have hdownValue := hdown (fun atomIndex => probe (deadIndex.succAbove atomIndex)) hsupportDown
  have hgapSplit : (chartPointGap point).submatrix deadIndex.succAbove deadIndex.succAbove
      = chartPointGap (chartPointDelete point deadIndex hweight hcolumn)
        + Matrix.diagonal (fun atomIndex =>
            point.weight (deadIndex.succAbove atomIndex) / (1 - point.weight deadIndex)
              - point.weight (deadIndex.succAbove atomIndex)) := by
    ext rowIndex colIndex
    simp only [chartPointGap, chartPointDelete, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.add_apply, Matrix.diagonal_apply]
    rcases eq_or_ne rowIndex colIndex with rfl | hne
    · rw [if_pos rfl, if_pos rfl, if_pos rfl]
      ring
    · rw [if_neg hne, if_neg hne,
        if_neg (fun heq => hne (Fin.succAbove_right_injective heq))]
      ring
  rw [dotProduct_mulVec_submatrix_succAbove (chartPointGap point) deadIndex hdead, hgapSplit,
    Matrix.add_mulVec, dotProduct_add]
  refine add_nonneg hdownValue ?_
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_nonneg fun atomIndex _ => ?_
  have hstep : point.weight (deadIndex.succAbove atomIndex)
      ≤ point.weight (deadIndex.succAbove atomIndex) / (1 - point.weight deadIndex) := by
    rw [le_div_iff₀ hpositive]
    nlinarith [point.weight_nonneg (deadIndex.succAbove atomIndex),
      point.weight_nonneg deadIndex]
  have hfactor : 0 ≤ point.weight (deadIndex.succAbove atomIndex)
      / (1 - point.weight deadIndex) - point.weight (deadIndex.succAbove atomIndex) := by
    linarith
  nlinarith [hfactor, sq_nonneg (probe (deadIndex.succAbove atomIndex))]

/-! ## The Schur step: the boundary hypothesis enters here and only here -/

/-- Bilinear expansion of a symmetric quadratic form against a coordinate spike. -/
theorem dotProduct_mulVec_add_spike {ambient : ℕ}
    (form : Matrix (Fin ambient) (Fin ambient) ℝ) (hsymm : formᵀ = form)
    (base : Fin ambient → ℝ) (spikeIndex : Fin ambient) (height : ℝ) :
    (base + height • Pi.single spikeIndex (1 : ℝ))
        ⬝ᵥ (form *ᵥ (base + height • Pi.single spikeIndex (1 : ℝ)))
      = base ⬝ᵥ (form *ᵥ base) + 2 * height * (form *ᵥ base) spikeIndex
        + height ^ 2 * form spikeIndex spikeIndex := by
  have hcolumn : form *ᵥ Pi.single spikeIndex (1 : ℝ)
      = fun rowIndex => form rowIndex spikeIndex := by
    funext rowIndex
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [Finset.sum_eq_single_of_mem spikeIndex (Finset.mem_univ spikeIndex)
      (fun other _ hother => by rw [if_neg hother, mul_zero]), if_pos rfl, mul_one]
  have hpairing : base ⬝ᵥ (fun rowIndex => form rowIndex spikeIndex)
      = (form *ᵥ base) spikeIndex := by
    simp only [dotProduct, Matrix.mulVec]
    refine Finset.sum_congr rfl fun rowIndex _ => ?_
    have hentry := congrFun (congrFun hsymm spikeIndex) rowIndex
    rw [Matrix.transpose_apply] at hentry
    rw [hentry]
    ring
  have hspikePair : Pi.single spikeIndex (1 : ℝ) ⬝ᵥ (form *ᵥ base)
      = (form *ᵥ base) spikeIndex := by
    rw [single_dotProduct, one_mul]
  have hspikeColumn : Pi.single spikeIndex (1 : ℝ) ⬝ᵥ (fun rowIndex => form rowIndex spikeIndex)
      = form spikeIndex spikeIndex := by
    rw [single_dotProduct, one_mul]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hcolumn, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hpairing, hspikePair, hspikeColumn]
  ring

/-- **THE SCHUR STEP.**  At a chart point whose weight at the pivot VANISHES, a
selection dominating the DEFLATED point lifts to that selection together with the
pivot.  The proof is one completion of the square: the pivot is `P_zz` on both
sides, so the deflation's rank-one debt is paid exactly.

`hweightZero` is load-bearing and cannot be relaxed: at `t_z > 0` the upstairs
pivot becomes `P_zz - t_z` while the deflation still subtracts
`(P e_z)(P e_z)ᵀ / P_zz`, and the mismatch is a genuine, unpaid deficit.
`not_compressionLiftClaim` below is an exact rational witness that the relaxed
statement is FALSE. -/
theorem chartDominates_insert_of_deflate (point : ChartPoint size (rank + 1))
    (pivotIndex : Fin size) (hpivot : 0 < point.chart pivotIndex pivotIndex)
    (hweightZero : point.weight pivotIndex = 0) (selected : Finset (Fin size))
    (hdown : ChartDominates (deflatePoint point pivotIndex hpivot) selected) :
    ChartDominates point (insert pivotIndex selected) := by
  classical
  intro probe hsupport
  have hgapSymm := chartPointGap_transpose point
  have htrimmedSupport : ∀ atomIndex,
      atomIndex ∉ selected → (if atomIndex = pivotIndex then 0 else probe atomIndex) = 0 := by
    intro atomIndex hnot
    rcases eq_or_ne atomIndex pivotIndex with rfl | hne
    · rw [if_pos rfl]
    · rw [if_neg hne]
      exact hsupport atomIndex fun hmem =>
        hnot ((Finset.mem_insert.mp hmem).resolve_left hne)
  have hdownValue := hdown (fun atomIndex =>
    if atomIndex = pivotIndex then 0 else probe atomIndex) htrimmedSupport
  have hdecomp : probe = (fun atomIndex => if atomIndex = pivotIndex then 0 else probe atomIndex)
      + probe pivotIndex • Pi.single pivotIndex (1 : ℝ) := by
    funext atomIndex
    rcases eq_or_ne atomIndex pivotIndex with rfl | hne
    · simp
    · simp [hne]
  have hpivotGap : chartPointGap point pivotIndex pivotIndex
      = point.chart pivotIndex pivotIndex := by
    rw [chartPointGap, Matrix.sub_apply, Matrix.diagonal_apply_eq, hweightZero, sub_zero]
  have hcross : (chartPointGap point
        *ᵥ fun atomIndex => if atomIndex = pivotIndex then 0 else probe atomIndex) pivotIndex
      = chartPointColumn point pivotIndex
        ⬝ᵥ fun atomIndex => if atomIndex = pivotIndex then 0 else probe atomIndex := by
    rw [chartPointColumn_dotProduct, chartPointGap, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.mulVec_diagonal, hweightZero, zero_mul, sub_zero]
  rw [hdecomp, dotProduct_mulVec_add_spike (chartPointGap point) hgapSymm, hcross, hpivotGap,
    dotProduct_chartPointGap_eq_deflated_add_pivot point pivotIndex]
  have hsquare : (point.chart pivotIndex pivotIndex)⁻¹
        * (chartPointColumn point pivotIndex
            ⬝ᵥ fun atomIndex => if atomIndex = pivotIndex then 0 else probe atomIndex) ^ 2
      + 2 * probe pivotIndex
          * (chartPointColumn point pivotIndex
              ⬝ᵥ fun atomIndex => if atomIndex = pivotIndex then 0 else probe atomIndex)
      + probe pivotIndex ^ 2 * point.chart pivotIndex pivotIndex
      = (point.chart pivotIndex pivotIndex)⁻¹
        * ((chartPointColumn point pivotIndex
              ⬝ᵥ fun atomIndex => if atomIndex = pivotIndex then 0 else probe atomIndex)
            + probe pivotIndex * point.chart pivotIndex pivotIndex) ^ 2 := by
    field_simp
    ring
  have hnonneg : 0 ≤ (point.chart pivotIndex pivotIndex)⁻¹
      * ((chartPointColumn point pivotIndex
            ⬝ᵥ fun atomIndex => if atomIndex = pivotIndex then 0 else probe atomIndex)
          + probe pivotIndex * point.chart pivotIndex pivotIndex) ^ 2 :=
    mul_nonneg (inv_nonneg.mpr hpivot.le) (sq_nonneg _)
  have hdeflatedShape : (fun atomIndex => if atomIndex = pivotIndex then 0 else probe atomIndex)
        ⬝ᵥ ((deflatedChartMatrix point pivotIndex - Matrix.diagonal point.weight)
            *ᵥ fun atomIndex => if atomIndex = pivotIndex then 0 else probe atomIndex)
      = (fun atomIndex => if atomIndex = pivotIndex then 0 else probe atomIndex)
        ⬝ᵥ (chartPointGap (deflatePoint point pivotIndex hpivot)
            *ᵥ fun atomIndex => if atomIndex = pivotIndex then 0 else probe atomIndex) := rfl
  rw [hdeflatedShape]
  linarith [hdownValue, hsquare, hnonneg]

/-- Domination on a SINGLETON is one sign condition on one diagonal entry. -/
theorem chartDominates_singleton (point : ChartPoint size rank) (atomIndex : Fin size)
    (hdiag : 0 ≤ chartPointGap point atomIndex atomIndex) :
    ChartDominates point {atomIndex} := by
  classical
  intro probe hsupport
  have hoff : ∀ other, other ≠ atomIndex → probe other = 0 := fun other hne =>
    hsupport other (by simpa only [Finset.mem_singleton] using hne)
  simp only [dotProduct, Matrix.mulVec]
  rw [Finset.sum_eq_single_of_mem atomIndex (Finset.mem_univ atomIndex)
      (fun other _ hother => by rw [hoff other hother, zero_mul]),
    Finset.sum_eq_single_of_mem atomIndex (Finset.mem_univ atomIndex)
      (fun other _ hother => by rw [hoff other hother, mul_zero])]
  have hshape : probe atomIndex * (chartPointGap point atomIndex atomIndex * probe atomIndex)
      = chartPointGap point atomIndex atomIndex * probe atomIndex ^ 2 := by ring
  rw [hshape]
  exact mul_nonneg hdiag (sq_nonneg _)

/-! ## The boundary dichotomy -/

/-- **THE BOUNDARY THEOREM.**  At a chart point with a VANISHING weight the closed
domain's conclusion follows from the two smaller rungs, unconditionally.

Case A (`P_zz = 0`, atom-vanishing) consumes `(size, rank + 1)`; Case B
(`P_zz > 0`, direction-escape) consumes `(size, rank)`.  Both drop the SIZE by
one, so the reduction below is well founded on the size alone -- the rank window
is a consequence, not an extra hypothesis.

Nothing is transported: no margin, no rate, no subsequence.  Case A restricts a
projection whose whole `z`-row vanishes; Case B is a completion of the square
whose pivot matches on the nose because the weight at the pivot is zero. -/
theorem exists_chartDominates_of_weight_eq_zero (hsameRank : ChartGtz size (rank + 1))
    (hdropRank : ChartGtz size rank) (point : ChartPoint (size + 1) (rank + 1))
    (deadIndex : Fin (size + 1)) (hweightZero : point.weight deadIndex = 0) :
    ∃ selected : Finset (Fin (size + 1)),
      selected.card = rank + 1 ∧ ChartDominates point selected := by
  classical
  have hweight : point.weight deadIndex < 1 := by rw [hweightZero]; norm_num
  rcases eq_or_lt_of_le (chartPoint_diag_nonneg point deadIndex) with hvanishes | hescapes
  · have hcolumn := chartPointColumn_eq_zero_of_diag_eq_zero point hvanishes.symm
    obtain ⟨selectedDown, hcard, hdown⟩ :=
      hsameRank (chartPointDelete point deadIndex hweight hcolumn)
    refine ⟨selectedDown.image deadIndex.succAbove, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (Fin.succAbove_right_injective), hcard]
    · exact chartDominates_image_of_chartPointDelete point deadIndex hweight hcolumn
        selectedDown hdown
  · have hcolumn := deflatedChartMatrix_column_eq_zero point hescapes.ne'
    obtain ⟨selectedDown, hcard, hdown⟩ :=
      hdropRank (chartPointDelete (deflatePoint point deadIndex hescapes) deadIndex
        hweight hcolumn)
    refine ⟨insert deadIndex (selectedDown.image deadIndex.succAbove), ?_, ?_⟩
    · have hfresh : deadIndex ∉ selectedDown.image deadIndex.succAbove := by
        intro hmem
        obtain ⟨atomIndex, _, heq⟩ := Finset.mem_image.mp hmem
        exact Fin.succAbove_ne deadIndex atomIndex heq
      rw [Finset.card_insert_of_notMem hfresh,
        Finset.card_image_of_injective _ (Fin.succAbove_right_injective), hcard]
    · refine chartDominates_insert_of_deflate point deadIndex hescapes hweightZero _ ?_
      exact chartDominates_image_of_chartPointDelete (deflatePoint point deadIndex hescapes)
        deadIndex hweight hcolumn selectedDown hdown

/-- **EVERY COUNTEREXAMPLE IS INTERIOR** -- the packaging in which the boundary
theorem is genuinely load bearing, and the one a compactness argument consumes.

The density theorem `chartGtz_of_chartGtzInterior` subsumes the assemblies below,
but it does NOT subsume this: density only relocates SOME counterexample into the
interior, whereas this keeps the GIVEN point and merely reports where it must live.
A compactness argument minimises a continuous objective over the CLOSED domain --
the only place the infimum is attained, the interior being non-compact -- and then
needs THAT minimiser to be interior before any first-order (Clarke) data can be
read off it.  That is exactly what this supplies. -/
theorem weight_pos_of_forall_not_chartDominates (hsameRank : ChartGtz size (rank + 1))
    (hdropRank : ChartGtz size rank) (point : ChartPoint (size + 1) (rank + 1))
    (hfails : ∀ selected : Finset (Fin (size + 1)), selected.card = rank + 1 →
      ¬ ChartDominates point selected) (atomIndex : Fin (size + 1)) :
    0 < point.weight atomIndex := by
  rcases eq_or_lt_of_le (point.weight_nonneg atomIndex) with hzero | hpositive
  · obtain ⟨selected, hcard, hdominates⟩ :=
      exists_chartDominates_of_weight_eq_zero hsameRank hdropRank point atomIndex hzero.symm
    exact absurd hdominates (hfails selected hcard)
  · exact hpositive

/-! ## The compression-lift claim: PROVED at the boundary, REFUTED off it -/

/-- **The compressed point**: deflate at the escaping label, then delete it and
renormalise the surviving weights by `1/(1 - t_z)`.  This is exactly the
`(size, rank)` object the campaign brief's Case B builds -- "keep the escaper,
compress the survivors onto `v_z`-perp" -- with the compression realised as the
Schur complement of the chart pivot, so no basis of `v_z`-perp is chosen and no
square root appears. -/
noncomputable def compressPoint (point : ChartPoint (size + 1) (rank + 1))
    (pivotIndex : Fin (size + 1)) (hpivot : 0 < point.chart pivotIndex pivotIndex)
    (hweight : point.weight pivotIndex < 1) : ChartPoint size rank :=
  chartPointDelete (deflatePoint point pivotIndex hpivot) pivotIndex hweight
    (deflatedChartMatrix_column_eq_zero point hpivot.ne')

/-- **THE CLAIM THE CAMPAIGN BRIEF'S CASE B MAKES**, stated at an ARBITRARY weight
at the escaping label -- i.e. as it would have to hold ALONG a minimizing
sequence, not only at its limit point.

`compressionLiftClaim_of_weight_eq_zero` proves it whenever the weight at the
label VANISHES.  `not_compressionLiftClaim` REFUTES it in general, with an exact
rational witness.  Both are theorems below; the pair is the honest boundary of
the reduction. -/
def CompressionLiftClaim (size rank : ℕ) : Prop :=
  ∀ (point : ChartPoint (size + 1) (rank + 1)) (pivotIndex : Fin (size + 1))
    (hpivot : 0 < point.chart pivotIndex pivotIndex) (hweight : point.weight pivotIndex < 1)
    (selectedDown : Finset (Fin size)),
    ChartDominates (compressPoint point pivotIndex hpivot hweight) selectedDown →
    ChartDominates point (insert pivotIndex (selectedDown.image pivotIndex.succAbove))

/-- **The claim holds at the boundary.**  Composite of the unconditional deletion
lift and the Schur step. -/
theorem compressionLiftClaim_of_weight_eq_zero (point : ChartPoint (size + 1) (rank + 1))
    (pivotIndex : Fin (size + 1)) (hpivot : 0 < point.chart pivotIndex pivotIndex)
    (hweight : point.weight pivotIndex < 1) (hweightZero : point.weight pivotIndex = 0)
    (selectedDown : Finset (Fin size))
    (hdown : ChartDominates (compressPoint point pivotIndex hpivot hweight) selectedDown) :
    ChartDominates point (insert pivotIndex (selectedDown.image pivotIndex.succAbove)) := by
  refine chartDominates_insert_of_deflate point pivotIndex hpivot hweightZero _ ?_
  exact chartDominates_image_of_chartPointDelete (deflatePoint point pivotIndex hpivot)
    pivotIndex hweight (deflatedChartMatrix_column_eq_zero point hpivot.ne') selectedDown hdown

/-! ### The refuting witness

`liftFailureChart` is a rational symmetric idempotent of trace two on four
indices with EVERY diagonal entry positive.  It is carried with a ONE-PARAMETER
weight (`liftFailurePointAt`), of which the UNIFORM weight `1/4` is the member
`liftFailurePoint` described below.  At the label `1`:

* the pivot is `P_11 = 1/3` and the weight is `1/4`, so `P_zz - t_z = 1/12 > 0`
  and the leverage is `P_zz / t_z = 4/3 > 1`.  Every leverage of this point
  exceeds one (`liftFailure_isAllHeavy`), so the witness sits squarely in the
  AllHeavy / "dust" branch and is NOT in the light-atom branch
  `Gtz.dominating_of_light_atom` discharges for free;
* downstairs the compressed gap at the survivor `0` is EXACTLY zero -- a tie, so
  there is no margin to pay the pivot mismatch with.  This is the frozen-tie
  mechanism: the finite-weight deficit is first order in `t_z` while the
  downstairs margin is zero, so no smallness of `t_z` can repair it;
* upstairs the `2 x 2` gap on `{0, 1}` is `[[5/12, 1/3], [1/3, 1/12]]`, with
  determinant `-11/144 < 0`.  The probe `(1, -4, 0, 0)` gives `-11/12`.

[EXACT] All of that is rational and re-derived inside Lean below.  The witness
has all weights positive, so it also corresponds to a genuine real
`Gtz.WeightedDesign`; that correspondence (the chart-to-design direction) is NOT
mechanized here and nothing below uses it. -/
noncomputable def liftFailureChart : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2/3, 1/3, 0, 1/3;
     1/3, 1/3, 1/3, 0;
     0, 1/3, 2/3, -1/3;
     1/3, 0, -1/3, 1/3]

theorem liftFailureChart_transpose : liftFailureChartᵀ = liftFailureChart := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [liftFailureChart]

theorem liftFailureChart_mul_self : liftFailureChart * liftFailureChart = liftFailureChart := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [liftFailureChart, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

theorem trace_liftFailureChart : Matrix.trace liftFailureChart = (2 : ℝ) := by
  simp [Matrix.trace, Fin.sum_univ_four, liftFailureChart]
  norm_num

/-- **The refuting FAMILY**: `liftFailureChart` carried with the weight
`pivotWeight` at the escaping label `1` and `(1 - pivotWeight)/3` at the other
three.  One parameter, exact and rational at every value, and the downstairs tie is
FROZEN along the whole family -- which is what makes the refutation survive the
limit `pivotWeight -> 0`. -/
noncomputable def liftFailurePointAt (pivotWeight : ℝ) (hlow : 0 ≤ pivotWeight)
    (hhigh : pivotWeight ≤ 1) : ChartPoint 4 2 where
  chart := liftFailureChart
  weight := fun atomIndex => if atomIndex = 1 then pivotWeight else (1 - pivotWeight) / 3
  isSymmetric := liftFailureChart_transpose
  isIdempotent := liftFailureChart_mul_self
  hasTraceRank := by rw [trace_liftFailureChart]; norm_num
  weight_nonneg := fun atomIndex => by
    rcases eq_or_ne atomIndex 1 with rfl | hne
    · simpa using hlow
    · rw [if_neg hne]; linarith
  weight_sum_one := by
    have hzeroIndex : (0 : Fin 4) ≠ 1 := by decide
    have htwoIndex : (2 : Fin 4) ≠ 1 := by decide
    have hthreeIndex : (3 : Fin 4) ≠ 1 := by decide
    rw [Fin.sum_univ_four, if_neg hzeroIndex, if_pos rfl, if_neg htwoIndex, if_neg hthreeIndex]
    ring

theorem liftFailurePointAt_weight_pivot (pivotWeight : ℝ) (hlow : 0 ≤ pivotWeight)
    (hhigh : pivotWeight ≤ 1) :
    (liftFailurePointAt pivotWeight hlow hhigh).weight 1 = pivotWeight := by
  simp [liftFailurePointAt]

theorem liftFailurePointAt_pivot_pos (pivotWeight : ℝ) (hlow : 0 ≤ pivotWeight)
    (hhigh : pivotWeight ≤ 1) : 0 < (liftFailurePointAt pivotWeight hlow hhigh).chart 1 1 := by
  norm_num [liftFailurePointAt, liftFailureChart]

theorem liftFailure_succAbove : (1 : Fin 4).succAbove (0 : Fin 3) = 0 := by decide

/-- **The tie is FROZEN**: the compressed gap at the survivor is exactly zero at
EVERY weight, so the downstairs margin never grows to pay the first-order pivot
deficit, no matter how small the weight at the escaping label is made. -/
theorem liftFailurePointAt_compressedGap_eq_zero (pivotWeight : ℝ) (hlow : 0 ≤ pivotWeight)
    (hhigh : pivotWeight ≤ 1) (hlt : pivotWeight < 1) :
    chartPointGap (compressPoint (liftFailurePointAt pivotWeight hlow hhigh) 1
      (liftFailurePointAt_pivot_pos pivotWeight hlow hhigh)
      (by rw [liftFailurePointAt_weight_pivot]; exact hlt)) 0 0 = 0 := by
  have hne : (1 : ℝ) - pivotWeight ≠ 0 := by linarith
  simp only [chartPointGap, compressPoint, chartPointDelete, deflatePoint, deflatedChartMatrix,
    chartPointColumn, liftFailurePointAt, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.diagonal_apply_eq, smul_eq_mul,
    liftFailure_succAbove]
  norm_num [liftFailureChart]
  field_simp
  norm_num

/-- **The lift fails at EVERY positive weight**, at the probe
`(-1, 1 + t, 0, 0)`, with value `-(1/3)(1 + t)t(2 + 3t)`. -/
theorem not_chartDominates_liftFailurePointAt (pivotWeight : ℝ) (hlow : 0 ≤ pivotWeight)
    (hhigh : pivotWeight ≤ 1) (hpos : 0 < pivotWeight) :
    ¬ ChartDominates (liftFailurePointAt pivotWeight hlow hhigh) (insert 1 {0}) := by
  intro hdominates
  have hsupport : ∀ atomIndex : Fin 4, atomIndex ∉ (insert 1 {0} : Finset (Fin 4)) →
      (![-1, 1 + pivotWeight, 0, 0] : Fin 4 → ℝ) atomIndex = 0 := by
    intro atomIndex _
    fin_cases atomIndex
    · exact absurd (by decide : (0 : Fin 4) ∈ (insert 1 {0} : Finset (Fin 4))) (by assumption)
    · exact absurd (by decide : (1 : Fin 4) ∈ (insert 1 {0} : Finset (Fin 4))) (by assumption)
    · rfl
    · rfl
  have hvalue := hdominates (![-1, 1 + pivotWeight, 0, 0] : Fin 4 → ℝ) hsupport
  simp [chartPointGap, liftFailurePointAt, liftFailureChart, dotProduct, Matrix.mulVec,
    Matrix.diagonal_apply, Fin.sum_univ_four] at hvalue
  nlinarith [hvalue, hpos, sq_nonneg pivotWeight]

/-- The uniform-weight witness: the `1/4` member of the family, at which all four
weights are `1/4`. -/
noncomputable def liftFailurePoint : ChartPoint 4 2 :=
  liftFailurePointAt (1 / 4) (by norm_num) (by norm_num)

theorem liftFailure_pivot_pos : 0 < liftFailurePoint.chart 1 1 := by
  norm_num [liftFailurePoint, liftFailurePointAt, liftFailureChart]

theorem liftFailure_weight_lt_one : liftFailurePoint.weight 1 < 1 := by
  norm_num [liftFailurePoint, liftFailurePointAt]

/-- **The witness is ALL HEAVY**: every leverage `P_cc / t_c` exceeds one, so the
refutation is not hiding in the light-atom branch. -/
theorem liftFailure_isAllHeavy (atomIndex : Fin 4) :
    liftFailurePoint.weight atomIndex < liftFailurePoint.chart atomIndex atomIndex := by
  fin_cases atomIndex <;> norm_num [liftFailurePoint, liftFailurePointAt, liftFailureChart]

/-- Downstairs the compressed gap at the survivor is EXACTLY zero: a tie, with no
margin available to pay the finite-weight pivot mismatch. -/
theorem liftFailure_compressedGap_eq_zero :
    chartPointGap (compressPoint liftFailurePoint 1 liftFailure_pivot_pos
      liftFailure_weight_lt_one) 0 0 = 0 := by
  simp only [chartPointGap, compressPoint, chartPointDelete, deflatePoint, deflatedChartMatrix,
    chartPointColumn, liftFailurePoint, liftFailurePointAt, Matrix.submatrix_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.diagonal_apply_eq,
    smul_eq_mul, liftFailure_succAbove]
  norm_num [liftFailureChart]

/-- Upstairs the two-element selection FAILS to dominate: the probe `(1, -4, 0, 0)`
gives `-11/12`. -/
theorem not_chartDominates_liftFailure :
    ¬ ChartDominates liftFailurePoint (insert 1 {0}) := by
  intro hdominates
  have hsupport : ∀ atomIndex : Fin 4, atomIndex ∉ (insert 1 {0} : Finset (Fin 4)) →
      (![1, -4, 0, 0] : Fin 4 → ℝ) atomIndex = 0 := by
    intro atomIndex _
    fin_cases atomIndex
    · exact absurd (by decide : (0 : Fin 4) ∈ (insert 1 {0} : Finset (Fin 4))) (by assumption)
    · exact absurd (by decide : (1 : Fin 4) ∈ (insert 1 {0} : Finset (Fin 4))) (by assumption)
    · rfl
    · rfl
  have hvalue := hdominates (![1, -4, 0, 0] : Fin 4 → ℝ) hsupport
  simp [chartPointGap, liftFailurePoint, liftFailurePointAt, liftFailureChart, dotProduct,
    Matrix.mulVec, Matrix.diagonal_apply, Fin.sum_univ_four] at hvalue
  norm_num at hvalue

/-- **THE REFUTATION.**  The compression lift is FALSE at positive weight: an exact
rational chart point of size four and rank two, all diagonal entries positive, all
leverages above one, uniform weight `1/4`, on which the compressed point dominates
at a survivor while the lifted two-element selection does not.

The failure is located precisely at the Schur pivot: at weight zero the upstairs
pivot is `P_zz` and the deflation subtracts `(P e_z)(P e_z)ᵀ / P_zz`, so the debt
is paid exactly; at weight `t_z > 0` the upstairs pivot degrades to `P_zz - t_z`
while the deflation still subtracts `.../ P_zz`, and the shortfall is unpaid.

CONSEQUENCE FOR THE REDUCTION.  Case B of the compactness reduction may only be
stated at the LIMIT POINT, never along the minimizing sequence.  The "for small
enough `t_z`" phrasing is dead too, and that is not an extrapolation from this
single point but the separate theorem `not_eventualCompressionLiftClaim` below. -/
theorem not_compressionLiftClaim : ¬ CompressionLiftClaim 3 1 := by
  intro hclaim
  have hlifted := hclaim liftFailurePoint 1 liftFailure_pivot_pos liftFailure_weight_lt_one {0}
    (chartDominates_singleton _ 0 (le_of_eq liftFailure_compressedGap_eq_zero.symm))
  rw [show ({0} : Finset (Fin 3)).image (1 : Fin 4).succAbove = {0} from by decide] at hlifted
  exact not_chartDominates_liftFailure hlifted

/-- **Case B below SOME positive weight threshold** -- the weakest sequential
reading of the campaign brief's Case B, and the one a minimizing-sequence argument
would actually try to use, since along such a sequence the weight at the escaping
label tends to zero. -/
def EventualCompressionLiftClaim (size rank : ℕ) : Prop :=
  ∃ threshold : ℝ, 0 < threshold ∧
    ∀ (point : ChartPoint (size + 1) (rank + 1)) (pivotIndex : Fin (size + 1))
      (hpivot : 0 < point.chart pivotIndex pivotIndex) (hweight : point.weight pivotIndex < 1),
      point.weight pivotIndex < threshold →
      ∀ selectedDown : Finset (Fin size),
        ChartDominates (compressPoint point pivotIndex hpivot hweight) selectedDown →
        ChartDominates point (insert pivotIndex (selectedDown.image pivotIndex.succAbove))

/-- **NO WEIGHT THRESHOLD SAVES CASE B.**  Whatever threshold is proposed, the
family supplies a counterexample below it: the tie downstairs is frozen at zero
while the pivot deficit is first order in the weight, so shrinking the weight
shrinks the deficit and the margin at the same rate and never overtakes it.

This is the theorem the campaign brief's Case B needs and does not have.  What it
does NOT say -- and the distinction matters, because the opposite reading has been
asserted -- is that a POSITIVE downstairs margin also fails to save the lift.  It
does save it: perturbing this family so the downstairs gap is `d > 0` makes the
upstairs determinant `(d - t - 4 d t + 3 d t^2)/3`, which tends to `d/3 > 0` as the
weight `t` tends to zero.  The frozen tie is essential, not incidental. -/
theorem not_eventualCompressionLiftClaim : ¬ EventualCompressionLiftClaim 3 1 := by
  rintro ⟨threshold, hthreshold, hclaim⟩
  set pivotWeight : ℝ := min (threshold / 2) (1 / 2) with hpivotWeight
  have hpos : 0 < pivotWeight := lt_min (by linarith) (by norm_num)
  have hhalf : pivotWeight ≤ 1 / 2 := min_le_right _ _
  have hlow : 0 ≤ pivotWeight := hpos.le
  have hhigh : pivotWeight ≤ 1 := by linarith
  have hlt : pivotWeight < 1 := by linarith
  have hsmall : pivotWeight < threshold := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hweight : (liftFailurePointAt pivotWeight hlow hhigh).weight 1 < 1 := by
    rw [liftFailurePointAt_weight_pivot]; exact hlt
  have hlifted := hclaim (liftFailurePointAt pivotWeight hlow hhigh) 1
    (liftFailurePointAt_pivot_pos pivotWeight hlow hhigh) hweight
    (by rw [liftFailurePointAt_weight_pivot]; exact hsmall) {0}
    (chartDominates_singleton _ 0
      (le_of_eq (liftFailurePointAt_compressedGap_eq_zero pivotWeight hlow hhigh hlt).symm))
  rw [show ({0} : Finset (Fin 3)).image (1 : Fin 4).succAbove = {0} from by decide] at hlifted
  exact not_chartDominates_liftFailurePointAt pivotWeight hlow hhigh hpos hlifted

/-! ## The bridge to `Gtz.GtzWeighted` -/

/-- The `ambient x selectionSize` matrix injecting a selected coordinate vector
into the ambient index space. -/
def selectionInjection {selectionSize ambient : ℕ} (pick : Fin selectionSize → Fin ambient) :
    Matrix (Fin ambient) (Fin selectionSize) ℝ :=
  Matrix.of fun rowIndex selectedIndex => if pick selectedIndex = rowIndex then 1 else 0

theorem transpose_selectionInjection_mul {selectionSize ambient : ℕ}
    (form : Matrix (Fin ambient) (Fin ambient) ℝ) (pick : Fin selectionSize → Fin ambient) :
    (selectionInjection pick)ᵀ * form = form.submatrix pick id := by
  ext leftIndex colIndex
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selectionInjection, Matrix.of_apply,
    Matrix.submatrix_apply, id_eq]
  rw [Finset.sum_eq_single_of_mem (pick leftIndex) (Finset.mem_univ _)
      (fun other _ hother => by rw [if_neg fun heq => hother heq.symm, zero_mul]),
    if_pos rfl, one_mul]

theorem submatrix_mul_selectionInjection {selectionSize ambient : ℕ}
    (form : Matrix (Fin ambient) (Fin ambient) ℝ) (pick : Fin selectionSize → Fin ambient) :
    form.submatrix pick id * selectionInjection pick = form.submatrix pick pick := by
  ext leftIndex rightIndex
  simp only [Matrix.mul_apply, selectionInjection, Matrix.of_apply, Matrix.submatrix_apply,
    id_eq]
  rw [Finset.sum_eq_single_of_mem (pick rightIndex) (Finset.mem_univ _)
      (fun other _ hother => by rw [if_neg fun heq => hother heq.symm, mul_zero]),
    if_pos rfl, mul_one]

/-- Moving a rectangular matrix across a pairing. -/
theorem mulVec_dotProduct_transpose {rows cols : ℕ}
    (rectangular : Matrix (Fin rows) (Fin cols) ℝ) (source : Fin cols → ℝ)
    (target : Fin rows → ℝ) :
    (rectangular *ᵥ source) ⬝ᵥ target = source ⬝ᵥ (rectangularᵀ *ᵥ target) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The ambient/submatrix Rayleigh dictionary.**  Spreading a selected vector into
the ambient space computes the submatrix's quadratic form. -/
theorem dotProduct_selectionInjection_mulVec {selectionSize ambient : ℕ}
    (form : Matrix (Fin ambient) (Fin ambient) ℝ) (pick : Fin selectionSize → Fin ambient)
    (probe : Fin selectionSize → ℝ) :
    (selectionInjection pick *ᵥ probe) ⬝ᵥ (form *ᵥ (selectionInjection pick *ᵥ probe))
      = probe ⬝ᵥ (form.submatrix pick pick *ᵥ probe) := by
  rw [mulVec_dotProduct_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    transpose_selectionInjection_mul, submatrix_mul_selectionInjection]

/-- The spread vector is supported on the selection. -/
theorem selectionInjection_mulVec_eq_zero_of_notMem {selectionSize ambient : ℕ}
    (pick : Fin selectionSize → Fin ambient) (probe : Fin selectionSize → ℝ)
    {rowIndex : Fin ambient} (hmiss : ∀ selectedIndex, pick selectedIndex ≠ rowIndex) :
    (selectionInjection pick *ᵥ probe) rowIndex = 0 := by
  simp only [Matrix.mulVec, dotProduct, selectionInjection, Matrix.of_apply]
  exact Finset.sum_eq_zero fun selectedIndex _ => by
    rw [if_neg (hmiss selectedIndex), zero_mul]

/-- A probe supported on a selection IS the spread of its restriction. -/
theorem eq_selectionInjection_mulVec_of_support {ambient rankValue : ℕ}
    (selected : Finset (Fin ambient)) (hcard : selected.card = rankValue)
    {probe : Fin ambient → ℝ}
    (hsupport : ∀ atomIndex, atomIndex ∉ selected → probe atomIndex = 0) :
    probe = selectionInjection (selected.orderEmbOfFin hcard)
      *ᵥ fun selectedIndex => probe (selected.orderEmbOfFin hcard selectedIndex) := by
  classical
  have hrange : Set.range (selected.orderEmbOfFin hcard) = ↑selected :=
    Finset.range_orderEmbOfFin selected hcard
  funext rowIndex
  simp only [Matrix.mulVec, dotProduct, selectionInjection, Matrix.of_apply]
  by_cases hmem : rowIndex ∈ selected
  · obtain ⟨witnessIndex, hwitness⟩ : ∃ witnessIndex,
        selected.orderEmbOfFin hcard witnessIndex = rowIndex := by
      have : rowIndex ∈ Set.range (selected.orderEmbOfFin hcard) := by
        rw [hrange]; exact hmem
      exact this
    rw [Finset.sum_eq_single_of_mem witnessIndex (Finset.mem_univ _)
        (fun other _ hother => by
          rw [if_neg fun heq => hother
            ((selected.orderEmbOfFin hcard).injective (heq.trans hwitness.symm)), zero_mul]),
      if_pos hwitness, one_mul, hwitness]
  · rw [hsupport rowIndex hmem]
    refine (Finset.sum_eq_zero fun selectedIndex _ => ?_).symm
    have hne : selected.orderEmbOfFin hcard selectedIndex ≠ rowIndex := by
      intro heq
      refine hmem (heq ▸ ?_)
      have hin : selected.orderEmbOfFin hcard selectedIndex
          ∈ Set.range (selected.orderEmbOfFin hcard) := ⟨selectedIndex, rfl⟩
      rw [hrange] at hin
      exact hin
    rw [if_neg hne, zero_mul]

/-- **Chart domination IS submatrix positivity**, both directions. -/
theorem chartDominates_iff_posSemidef_submatrix (point : ChartPoint size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) :
    ChartDominates point selected
      ↔ ((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)).PosSemidef := by
  classical
  have hrange : Set.range (selected.orderEmbOfFin hcard) = ↑selected :=
    Finset.range_orderEmbOfFin selected hcard
  have hhermitian : ((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard)).IsHermitian := by
    show ((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard))ᴴ = _
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_submatrix,
      chartPointGap_transpose]
  constructor
  · intro hdominates
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hhermitian, fun probe => ?_⟩
    rw [star_trivial, ← dotProduct_selectionInjection_mulVec]
    refine hdominates _ fun atomIndex hnot => ?_
    refine selectionInjection_mulVec_eq_zero_of_notMem _ _ fun selectedIndex heq => hnot ?_
    have hin : selected.orderEmbOfFin hcard selectedIndex
        ∈ Set.range (selected.orderEmbOfFin hcard) := ⟨selectedIndex, rfl⟩
    rw [hrange] at hin
    exact heq ▸ hin
  · intro hpsd probe hsupport
    rw [eq_selectionInjection_mulVec_of_support selected hcard hsupport,
      dotProduct_selectionInjection_mulVec]
    have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2
      (fun selectedIndex => probe (selected.orderEmbOfFin hcard selectedIndex))
    rwa [star_trivial] at hvalue

/-- A weighted design read as a chart point. -/
noncomputable def chartPointOfDesign {atoms rankValue : ℕ}
    (design : WeightedDesign atoms rankValue) : ChartPoint atoms rankValue where
  chart := projectionOfDesign design
  weight := design.weight
  isSymmetric := projectionOfDesign_transpose design
  isIdempotent := projectionOfDesign_mul_self design
  hasTraceRank := trace_projectionOfDesign design
  weight_nonneg := fun atomIndex => (design.weight_pos atomIndex).le
  weight_sum_one := design.weight_sum_one

theorem chartPointGap_submatrix_chartPointOfDesign {atoms rankValue : ℕ}
    (design : WeightedDesign atoms rankValue) (selected : Finset (Fin atoms))
    (hcard : selected.card = rankValue) :
    (chartPointGap (chartPointOfDesign design)).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard)
      = (projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)
        - Matrix.diagonal (fun selectedIndex =>
            design.weight (selected.orderEmbOfFin hcard selectedIndex)) := by
  ext leftIndex rightIndex
  simp only [chartPointGap, chartPointOfDesign, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.diagonal_apply]
  rcases eq_or_ne leftIndex rightIndex with rfl | hne
  · rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hne,
      if_neg fun heq => hne ((selected.orderEmbOfFin hcard).injective heq)]

/-- **Chart domination and design domination agree.** -/
theorem dominates_iff_chartDominates {atoms rankValue : ℕ}
    (design : WeightedDesign atoms rankValue) (selected : Finset (Fin atoms))
    (hcard : selected.card = rankValue) :
    Dominates design selected ↔ ChartDominates (chartPointOfDesign design) selected := by
  rw [dominates_iff_posSemidef_projectionBlock_finset design selected hcard,
    chartDominates_iff_posSemidef_submatrix (chartPointOfDesign design) selected hcard,
    chartPointGap_submatrix_chartPointOfDesign design selected hcard]

/-- **The easy direction of the bridge**: the closed chart statement implies the
weighted statement. -/
theorem gtzWeighted_of_chartGtz {atoms rankValue : ℕ} (hchart : ChartGtz atoms rankValue) :
    GtzWeighted atoms rankValue := by
  intro design
  obtain ⟨selected, hcard, hdominates⟩ := hchart (chartPointOfDesign design)
  exact ⟨selected, hcard, (dominates_iff_chartDominates design selected hcard).mpr hdominates⟩

/-! ## The assembly, as an implication from stated hypotheses -/

/-- **The interior obligation**, isolated as a hypothesis.  This is the residue the
reduction leaves: domination at chart points whose weights are all STRICTLY
positive.

WHAT THIS IS NOT.  The campaign brief's hypothesis (b) is sharper -- "no interior
Clarke-critical point of the objective has value below the threshold" -- and
deriving `ChartGtzInterior` from it needs two ingredients that are NOT in this
file and not in Mathlib: (i) compactness of the closed chart domain plus attainment
of the infimum of a max-of-eigenvalue objective, and (ii) a Clarke
subdifferential calculus (Mathlib has none).  There is also a genuine OBJECTIVE
MISMATCH: `Gtz.lambdaMinMat (subsetSum D C)` and `Gtz.lambdaMinMat` of the chart
gap block share their THRESHOLD but not their minimisers, because the two are
related by the non-uniform congruence `diagonal (sqrt t_C)`, so a critical point of
one is not a critical point of the other.  Both are recorded in the module header;
`ChartGtzInterior` is deliberately the WEAKEST hypothesis under which the boundary
work below is stated, and it is an UNPROVED LEAF. -/
def ChartGtzInterior (size rank : ℕ) : Prop :=
  ∀ point : ChartPoint size rank, (∀ atomIndex, 0 < point.weight atomIndex) →
    ∃ selected : Finset (Fin size), selected.card = rank ∧ ChartDominates point selected

/-- **The one-rung assembly -- SUBSUMED, kept for the record.**  The closed
statement at `(size + 1, rank + 1)` follows from the interior obligation at that
size together with the two smaller rungs.

Do NOT read this as "the reduction".  `chartGtz_of_chartGtzInterior` proves the
same conclusion from `hinterior` ALONE, so the two smaller-rung hypotheses are
dead weight here and the boundary theorem is not load bearing for this statement.
The boundary theorem's live packaging is
`weight_pos_of_forall_not_chartDominates`. -/
theorem chartGtz_of_smaller_of_interior (hsameRank : ChartGtz size (rank + 1))
    (hdropRank : ChartGtz size rank) (hinterior : ChartGtzInterior (size + 1) (rank + 1)) :
    ChartGtz (size + 1) (rank + 1) := by
  intro point
  by_cases hpositive : ∀ atomIndex, 0 < point.weight atomIndex
  · exact hinterior point hpositive
  · obtain ⟨deadIndex, hdead⟩ := not_forall.mp hpositive
    exact exists_chartDominates_of_weight_eq_zero hsameRank hdropRank point deadIndex
      (le_antisymm (not_lt.mp hdead) (point.weight_nonneg deadIndex))

/-- There is NO chart point on the empty index set: the weights would have to sum
to one over nothing.  So the size-zero rung is vacuous, and it is the induction's
base case. -/
theorem chartGtz_size_zero (rankValue : ℕ) : ChartGtz 0 rankValue := by
  intro point
  exact absurd point.weight_sum_one (by simp)

/-- The rank-zero rung is free: the empty selection dominates. -/
theorem chartGtz_rank_zero (atoms : ℕ) : ChartGtz atoms 0 := by
  intro point
  refine ⟨∅, Finset.card_empty, fun probe hsupport => ?_⟩
  have hzero : probe = 0 := funext fun atomIndex => hsupport atomIndex (by simp)
  rw [hzero]
  simp

/-- **The size ladder -- SUBSUMED, kept for the record.**  Induction on the SIZE
alone: every rung consumes only the two rungs one size below, so the whole closed
statement follows from the interior obligation at every rung, and the rank window
is a consequence of the induction rather than an extra hypothesis.

Subsumed by `chartGtz_of_chartGtzInterior`, which needs the interior obligation at
ONE size to conclude at that same size, where this needs it at every size. -/
theorem chartGtz_of_interior (hinterior : ∀ atoms rankValue, ChartGtzInterior atoms rankValue)
    (atoms : ℕ) : ∀ rankValue, ChartGtz atoms rankValue := by
  induction atoms with
  | zero => exact chartGtz_size_zero
  | succ previousSize inductiveHypothesis =>
      intro rankValue
      cases rankValue with
      | zero => exact chartGtz_rank_zero (previousSize + 1)
      | succ previousRank =>
          exact chartGtz_of_smaller_of_interior (inductiveHypothesis (previousRank + 1))
            (inductiveHypothesis previousRank) (hinterior (previousSize + 1) (previousRank + 1))

/-- The weighted consequence of the ladder. -/
theorem gtzWeighted_of_interior
    (hinterior : ∀ atoms rankValue, ChartGtzInterior atoms rankValue) (atoms rankValue : ℕ) :
    GtzWeighted atoms rankValue :=
  gtzWeighted_of_chartGtz (chartGtz_of_interior hinterior atoms rankValue)

/-! ## The interior obligation already implies both conclusions

This section measures the two assemblies above.  It shows the interior obligation
alone -- no smaller rung, no ladder, no factorisation leaf -- yields the weighted
goal at the same size, and also the full CLOSED chart statement at the same size.
Both assemblies above are therefore subsumed, and the boundary machinery is load
bearing only in the `weight_pos_of_forall_not_chartDominates` packaging, which
keeps the given point rather than relocating a counterexample. -/

/-- There is no chart point on an empty index set, so any chart point witnesses a
positive size. -/
theorem size_pos_of_chartPoint (point : ChartPoint size rank) : 0 < size := by
  rcases Nat.eq_zero_or_pos size with hzero | hpositive
  · subst hzero
    exact absurd point.weight_sum_one (by simp)
  · exact hpositive

/-- **Mix the weights toward uniform**, leaving the chart alone.  At any positive
mixing every weight is strictly positive, so the mixed point is INTERIOR; at
mixing zero it is the original point.  The chart is untouched, so no idempotency
or trace obligation is re-incurred. -/
noncomputable def relaxedChartPoint (point : ChartPoint size rank) (mixing : ℝ)
    (hlow : 0 ≤ mixing) (hhigh : mixing ≤ 1) : ChartPoint size rank where
  chart := point.chart
  weight := fun atomIndex => (1 - mixing) * point.weight atomIndex + mixing / (size : ℝ)
  isSymmetric := point.isSymmetric
  isIdempotent := point.isIdempotent
  hasTraceRank := point.hasTraceRank
  weight_nonneg := fun atomIndex => by
    have hcast : (0 : ℝ) < (size : ℝ) := by exact_mod_cast size_pos_of_chartPoint point
    have hweight := point.weight_nonneg atomIndex
    have hcomplement : 0 ≤ 1 - mixing := by linarith
    positivity
  weight_sum_one := by
    have hcast : (0 : ℝ) < (size : ℝ) := by exact_mod_cast size_pos_of_chartPoint point
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, point.weight_sum_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

/-- The mixed gap form differs from the original by a term LINEAR in the mixing --
which is what lets one mixing parameter serve all finitely many selections at
once. -/
theorem dotProduct_gap_relaxedChartPoint (point : ChartPoint size rank) (mixing : ℝ)
    (hlow : 0 ≤ mixing) (hhigh : mixing ≤ 1) (probe : Fin size → ℝ) :
    probe ⬝ᵥ (chartPointGap (relaxedChartPoint point mixing hlow hhigh) *ᵥ probe)
      = probe ⬝ᵥ (chartPointGap point *ᵥ probe)
        - mixing * ∑ atomIndex, ((size : ℝ)⁻¹ - point.weight atomIndex)
            * probe atomIndex ^ 2 := by
  have hdiagonalForm : ∀ weights : Fin size → ℝ,
      probe ⬝ᵥ (Matrix.diagonal weights *ᵥ probe)
        = ∑ atomIndex, weights atomIndex * probe atomIndex ^ 2 := by
    intro weights
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [chartPointGap, relaxedChartPoint, Matrix.sub_mulVec, dotProduct_sub,
    hdiagonalForm]
  rw [sub_sub, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **THE DENSITY THEOREM.**  The interior obligation implies the CLOSED statement
at the SAME size, with no smaller rungs anywhere.

Suppose no selection dominates at a boundary point.  Each of the finitely many
candidate selections then carries a failing probe, normalised to gap value `-1`.
Mixing the weights toward uniform changes each of those values by a term linear in
the mixing, so a single mixing small enough to keep all of them negative exists --
take the reciprocal of one plus the sum of the linear coefficients' magnitudes.
That mixed point is interior and has no dominating selection, contradicting the
hypothesis.

This is what makes `chartGtz_of_smaller_of_interior` and `chartGtz_of_interior`
subsumed.  It does NOT replace `weight_pos_of_forall_not_chartDominates`: the
counterexample it produces is a DIFFERENT point, so nothing distinguishing the
original point -- in particular being a minimiser -- survives. -/
theorem chartGtz_of_chartGtzInterior (hinterior : ChartGtzInterior size rank) :
    ChartGtz size rank := by
  classical
  intro point
  by_contra hnoSelection
  push Not at hnoSelection
  have hsize : 0 < size := size_pos_of_chartPoint point
  have hcast : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsize
  have hnormalisedProbe : ∀ selected : Finset (Fin size), ∃ probe : Fin size → ℝ,
      selected.card = rank →
        (∀ atomIndex, atomIndex ∉ selected → probe atomIndex = 0) ∧
          probe ⬝ᵥ (chartPointGap point *ᵥ probe) = -1 := by
    intro selected
    by_cases hcard : selected.card = rank
    · have hfails := hnoSelection selected hcard
      rw [ChartDominates] at hfails
      push Not at hfails
      obtain ⟨rawProbe, hsupport, hvalue⟩ := hfails
      have hnegative : (0 : ℝ) < -(rawProbe ⬝ᵥ (chartPointGap point *ᵥ rawProbe)) := by linarith
      have hroot := Real.mul_self_sqrt hnegative.le
      have hrootNonzero :
          Real.sqrt (-(rawProbe ⬝ᵥ (chartPointGap point *ᵥ rawProbe))) ≠ 0 := by
        intro hzero
        rw [hzero] at hroot
        simp at hroot
        linarith
      refine ⟨(Real.sqrt (-(rawProbe ⬝ᵥ (chartPointGap point *ᵥ rawProbe))))⁻¹ • rawProbe,
        fun _ => ⟨fun atomIndex hnot => by simp [hsupport atomIndex hnot], ?_⟩⟩
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      field_simp
      linarith [hroot]
    · exact ⟨0, fun hbad => absurd hbad hcard⟩
  choose failProbe hfailProbe using hnormalisedProbe
  set linearCoefficient : Finset (Fin size) → ℝ := fun selected =>
    ∑ atomIndex, ((size : ℝ)⁻¹ - point.weight atomIndex) * failProbe selected atomIndex ^ 2
    with hlinearCoefficient
  set candidates : Finset (Finset (Fin size)) :=
    Finset.univ.filter (fun selected => selected.card = rank) with hcandidates
  set coefficientBudget : ℝ := ∑ selected ∈ candidates, |linearCoefficient selected|
    with hcoefficientBudget
  have hbudgetNonneg : 0 ≤ coefficientBudget := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set mixing : ℝ := (1 + coefficientBudget)⁻¹ with hmixing
  have hmixingPos : 0 < mixing := by rw [hmixing]; positivity
  have hmixingLeOne : mixing ≤ 1 := by
    rw [hmixing]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hmixingScale : mixing * (1 + coefficientBudget) = 1 := by rw [hmixing]; field_simp
  have hmixedPositive : ∀ atomIndex,
      0 < (relaxedChartPoint point mixing hmixingPos.le hmixingLeOne).weight atomIndex := by
    intro atomIndex
    have hshifted : 0 ≤ (1 - mixing) * point.weight atomIndex :=
      mul_nonneg (by linarith) (point.weight_nonneg atomIndex)
    have huniform : 0 < mixing / (size : ℝ) := div_pos hmixingPos hcast
    simp only [relaxedChartPoint]
    linarith
  obtain ⟨selected, hcard, hdominates⟩ :=
    hinterior (relaxedChartPoint point mixing hmixingPos.le hmixingLeOne) hmixedPositive
  obtain ⟨hsupport, hvalue⟩ := hfailProbe selected hcard
  have hchosen := hdominates (failProbe selected) hsupport
  rw [dotProduct_gap_relaxedChartPoint, hvalue] at hchosen
  have hmember : selected ∈ candidates := by
    rw [hcandidates]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩
  have hbounded : |linearCoefficient selected| ≤ coefficientBudget :=
    Finset.single_le_sum (f := fun other => |linearCoefficient other|)
      (fun _ _ => abs_nonneg _) hmember
  have hlowerBound : -coefficientBudget ≤ linearCoefficient selected := by
    have := neg_abs_le (linearCoefficient selected)
    linarith
  have hscaled : mixing * (-coefficientBudget) ≤ mixing * linearCoefficient selected :=
    mul_le_mul_of_nonneg_left hlowerBound hmixingPos.le
  have hfold : linearCoefficient selected
      = ∑ atomIndex, ((size : ℝ)⁻¹ - point.weight atomIndex)
          * failProbe selected atomIndex ^ 2 := rfl
  rw [← hfold] at hchosen
  nlinarith [hchosen, hscaled, hmixingScale, hmixingPos]

/-- **The interior obligation implies the weighted goal outright**, in four lines
and with no leaf: a weighted design's chart point has all weights positive, so the
interior obligation applies to it directly.

This is the sharpest statement of what `ChartGtzInterior` costs as a hypothesis,
and the reason the file's assemblies must not be advertised as buying anything on
their own. -/
theorem gtzWeighted_of_chartGtzInterior {atoms rankValue : ℕ}
    (hinterior : ChartGtzInterior atoms rankValue) : GtzWeighted atoms rankValue := by
  intro design
  obtain ⟨selected, hcard, hdominates⟩ :=
    hinterior (chartPointOfDesign design) (fun atomIndex => design.weight_pos atomIndex)
  exact ⟨selected, hcard, (dominates_iff_chartDominates design selected hcard).mpr hdominates⟩

/-- **The missing link in the OTHER direction**, named so the gap is citable: every
chart point with strictly positive weights comes from a weighted design.

This is the chart-to-design factorisation `P = V Vᵀ`, which needs an orthonormal
basis of the range of `P`; nothing in the repository supplies it, and only the
design-to-chart direction (`chartPointOfDesign`) is shipped.  It is the sole
obstruction to feeding the ALREADY KERNEL-CHECKED small rungs
(`Gtz.gtzWeighted_of_le_five`, `Gtz.gtz_rank_two`, `Gtz.gtzWeighted_corank_two`)
into `ChartGtzInterior` and hence into the ladder above.  UNPROVED LEAF. -/
def ChartPointHasDesign (size rank : ℕ) : Prop :=
  ∀ point : ChartPoint size rank, (∀ atomIndex, 0 < point.weight atomIndex) →
    ∃ design : WeightedDesign size rank, chartPointOfDesign design = point

/-- With the factorisation, the shipped weighted rungs DO feed the ladder. -/
theorem chartGtzInterior_of_gtzWeighted {atoms rankValue : ℕ}
    (hfactors : ChartPointHasDesign atoms rankValue) (hweighted : GtzWeighted atoms rankValue) :
    ChartGtzInterior atoms rankValue := by
  intro point hpositive
  obtain ⟨design, hdesign⟩ := hfactors point hpositive
  obtain ⟨selected, hcard, hdominates⟩ := hweighted design
  refine ⟨selected, hcard, ?_⟩
  rw [← hdesign]
  exact (dominates_iff_chartDominates design selected hcard).mp hdominates

end Gtz

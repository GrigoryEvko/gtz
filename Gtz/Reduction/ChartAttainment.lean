/-
# S1 -- ATTAINMENT.  The closed chart domain is COMPACT and the chart objective
# ATTAINS its minimum on it

`Gtz.Reduction.CompactnessReduction`'s "UNPROVED LEAVES" note records, of the
passage from a critical-point hypothesis to `Gtz.ChartGtzInterior`, that it needs
"compactness of the closed chart domain plus ATTAINMENT of the infimum of a
max-of-eigenvalue objective", and states flatly that the decomposition "is not
available and is not attempted".  The compactness-and-attainment half of that
sentence is discharged here.  Nothing else in that sentence is touched: no Clarke
subdifferential appears, no first-order data is read off the minimiser, and no
cell is closed.

## WHAT IS PROVED, and it is elementary

The closed chart domain is carried on the RAW configuration space
`(Fin size -> Fin size -> R) x (Fin size -> R)` -- the same ambient
`Gtz.collaredSet` and `Gtz.subsetSumRaw` use, so the shipped norm and continuity
vocabulary applies verbatim.  `Gtz.chartDomain` cuts it out by five NON-STRICT
SCALAR conditions (symmetry, idempotency, the trace, weight nonnegativity, the
weight sum), so `Gtz.isClosed_chartDomain` is five `isClosed_eq` / `isClosed_le`
steps and no matrix-valued separation axiom is needed anywhere.

Boundedness is one inequality, `Gtz.abs_chartEntry_le_one_of_mem_chartDomain`:
symmetry plus idempotency give `sum_r P_rc^2 = P_cc` at every column, so
`P_cc^2 <= P_cc` forces `0 <= P_cc <= 1` and then `P_rc^2 <= P_cc <= 1`.  Every
chart entry lies in `[-1, 1]` and every weight in `[0, 1]`, so the whole domain
sits in the unit ball and `Gtz.isCompact_chartDomain` is Heine-Borel
(`Metric.isCompact_of_isClosed_isBounded`) in a finite-dimensional space.  NO
MANIFOLD, no Grassmannian and no spectral factorisation is used; the domain is a
PRODUCT and the chart is never factorised as `V Vᵀ`, so this file is independent
of the `Gtz.ChartPointHasDesign` leaf.

The objective is `G = max_C lambda_min(W[C])` over the `rank`-subsets, with `W`
the affine chart gap `P - diag t`.  `Gtz.chartBlockValue` is the per-subset
least eigenvalue -- `Gtz.lambdaMinMat` of the gap's principal block, junk `0` at
a subset of the wrong cardinality so the definition is total -- and
`Gtz.chartObjectiveRaw` is the `Finset.sup'` of those over
`Gtz.chartCandidates`.  Continuity is the shipped Weyl bound
`Gtz.lipschitzWith_lambdaMinCLM` through `Gtz.continuous_lambdaMinMat`, composed
with entrywise continuity of the gap and closed under a finite `sup'`
(`Continuous.finset_sup'_apply`); the Lipschitz constant is not needed and is not
tracked.  Attainment is then the extreme value theorem.

## THE THRESHOLD DICTIONARY, which is what makes the objective the right one

`Gtz.zero_le_chartObjective_iff_exists_chartDominates`: `0 <= G(point)` exactly
when some `rank`-subset chart-dominates.  The threshold is ZERO, not one: this is
the CHART objective, and `Gtz.Reduction.CompactnessReduction`'s recorded
OBJECTIVE MISMATCH stands undisturbed -- the design objective
`max_C lambda_min(S_C)` with threshold one has the same threshold but NOT the same
minimisers, because the two are related by the non-uniform congruence
`diagonal (sqrt t_C)`.  Nothing here transports a minimiser across that
congruence and nothing here should be read as doing so.

The per-subset half runs through the shipped
`Gtz.chartDominates_iff_posSemidef_submatrix` and the zero-threshold twin
`Gtz.zero_le_lambdaMinMat_iff_posSemidef` of the shipped
`Gtz.one_le_lambdaMinMat_iff_posSemidef`; the twin is a genuine variant (the
shipped statement is about `M - 1`) and is proved by the same two `ciInf` steps,
not obtained from it.

## THE CONSUMABLE FORM

`Gtz.exists_interior_minimiser_of_not_chartGtz` is the statement the chain wants.
Given the two smaller rungs and a FAILURE of the closed chart statement at
`(size + 1, rank + 1)` it produces ONE chart point that

  * minimises the chart objective over the whole closed domain,
  * has objective value STRICTLY NEGATIVE,
  * admits no dominating `(rank + 1)`-subset, and
  * has ALL WEIGHTS STRICTLY POSITIVE.

The last clause is not proved here: it is exactly
`Gtz.weight_pos_of_forall_not_chartDominates`, the shipped boundary dichotomy,
whose own docstring says it is the packaging "a compactness argument consumes"
and that the density theorem cannot replace it.  This file supplies the
compactness argument that packaging was waiting for, and the two compose in one
line.  At `(6, 3)` the hypotheses read `ChartGtz 5 3` and `ChartGtz 5 2`.

`Gtz.exists_interior_minimiser_of_not_gtzWeighted` is the same statement entered
from a failure of the WEIGHTED target itself, via the shipped easy bridge
`Gtz.gtzWeighted_of_chartGtz`.  At `(6, 3)` it reads: if `Gtz.GtzWeighted 6 3` is
false then, given `Gtz.ChartGtz 5 3` and `Gtz.ChartGtz 5 2`, some chart point has
all six weights strictly positive, no dominating triple, strictly negative chart
objective, AND minimal chart objective over the whole closed domain.  Minimality
is the only new word, and it is what every stationarity argument in the campaign
silently assumed.

The converse direction is `Gtz.chartGtz_of_isMin_of_nonneg`, with the weighted
reading `Gtz.gtzWeighted_of_isMin_of_nonneg`: a single minimiser with nonnegative
value decides the whole closed statement.  So after this file `Gtz.ChartGtz` is
equivalent to one scalar sign at one point.

Two guards keep the whole file from being vacuously true:
`Gtz.exists_chartObjective_isMin_fourTwo` fires attainment on the shipped `(4, 2)`
witness `Gtz.liftFailurePoint`, and `Gtz.chartBlockValue_liftFailure_neg` turns
the shipped `Gtz.not_chartDominates_liftFailure` into a strictly negative block
value, so the threshold really separates and the dictionary points the right way.

## WHAT THIS DOES NOT BUY -- read this before citing the file

It closes NO cell.  `Gtz.GtzWeighted 6 3` and `Gtz.GtzWeighted 7 3` are exactly
as open as before.  It supplies no stationarity, no multiplier, no tangent
direction and no second-order data; `Gtz.IsChartStationaryData` is nowhere in
scope.  It removes ONE named scaffolding gap -- the minimiser now EXISTS and is
now known to be interior -- and that is its entire content.  In particular the
minimiser produced here is not proved to be a critical point of anything, because
this repository carries no subdifferential calculus and this file adds none.

`Gtz.ChartPointHasDesign` is untouched and remains the sole obstruction to
feeding the shipped design-side rungs into the chart-side ladder.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.CompactnessReduction
import Gtz.Quantitative.MarginContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The zero-threshold twin of the shipped `lambdaMinMat` dictionary

`Gtz.one_le_lambdaMinMat_iff_posSemidef` reads `1 <= lambda_min M` as
`(M - 1) >= 0`, which is the DESIGN threshold.  The chart threshold is zero, so
the corresponding statement is `0 <= lambda_min M` iff `M >= 0`; it is a
different statement about a different matrix and is proved the same way, by the
two `ciInf` steps of the shipped proof with `0` in place of `1`. -/

section ZeroThreshold

variable {blockRank : ℕ} [Nonempty (Fin blockRank)]

/-- `0 <= lambda_min M` exactly when `M`'s quadratic form is nonnegative
everywhere.  The zero-threshold twin of `Gtz.one_le_lambdaMinMat_iff_forall`. -/
theorem zero_le_lambdaMinMat_iff_forall (block : Matrix (Fin blockRank) (Fin blockRank) ℝ) :
    0 ≤ lambdaMinMat block
      ↔ ∀ probe : EuclideanSpace ℝ (Fin blockRank), 0 ≤ probe ⬝ᵥ block *ᵥ probe := by
  rw [lambdaMinMat, lambdaMinCLM, le_ciInf_iff (rayleigh_bddBelow _)]
  constructor
  · intro hrayleigh probe
    rcases eq_or_ne probe 0 with rfl | hnonzero
    · simp
    · have hquotient := hrayleigh ⟨probe, hnonzero⟩
      rw [rayleigh_toEuclideanCLM_eq] at hquotient
      have hpositive : 0 < ‖probe‖ ^ 2 := by positivity
      rwa [le_div_iff₀ hpositive, zero_mul] at hquotient
  · rintro hform ⟨probe, hnonzero⟩
    rw [rayleigh_toEuclideanCLM_eq]
    have hpositive : 0 < ‖probe‖ ^ 2 := by positivity
    rw [le_div_iff₀ hpositive, zero_mul]
    exact hform probe

/-- `0 <= lambda_min M` iff `M >= 0` for symmetric `M`: `lambda_min` is the
smallest eigenvalue, and being nonnegative is positive semidefiniteness. -/
theorem zero_le_lambdaMinMat_iff_posSemidef
    (block : Matrix (Fin blockRank) (Fin blockRank) ℝ) (hhermitian : block.IsHermitian) :
    0 ≤ lambdaMinMat block ↔ block.PosSemidef := by
  rw [zero_le_lambdaMinMat_iff_forall, Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro hform
    refine ⟨hhermitian, fun probe => ?_⟩
    have hvalue := hform (WithLp.toLp 2 probe)
    rw [star_trivial]
    linarith [hvalue]
  · rintro ⟨_, hform⟩ probe
    have hvalue := hform (probe : Fin blockRank → ℝ)
    rw [star_trivial] at hvalue
    linarith [hvalue]

end ZeroThreshold

/-! ## The closed chart domain as a subset of the raw configuration space -/

/-- **The closed chart domain**, cut out of the raw configuration space by five
NON-STRICT SCALAR conditions: the chart is symmetric, the chart is idempotent
(written entrywise, so no matrix multiplication appears in the set), the chart's
diagonal sums to the rank, the weights are nonnegative, and the weights sum to
one.

Scalar rather than matrix-valued on purpose -- closedness is then five
`isClosed_eq` / `isClosed_le` steps over `R` and needs no separation axiom on a
matrix space.  `Gtz.chartPointOfMem` and `Gtz.chartConfig_mem_chartDomain`
identify membership with `Gtz.ChartPoint` in both directions. -/
def chartDomain (size rank : ℕ) : Set ((Fin size → Fin size → ℝ) × (Fin size → ℝ)) :=
  { config |
      (∀ rowIndex colIndex, config.1 colIndex rowIndex = config.1 rowIndex colIndex)
      ∧ (∀ rowIndex colIndex,
          ∑ midIndex, config.1 rowIndex midIndex * config.1 midIndex colIndex
            = config.1 rowIndex colIndex)
      ∧ (∑ diagIndex, config.1 diagIndex diagIndex = (rank : ℝ))
      ∧ (∀ atomIndex, 0 ≤ config.2 atomIndex)
      ∧ (∑ atomIndex, config.2 atomIndex = 1) }

/-- A chart point's raw configuration lies in the closed chart domain. -/
theorem chartConfig_mem_chartDomain (point : ChartPoint size rank) :
    ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ))
      ∈ chartDomain size rank := by
  refine ⟨fun rowIndex colIndex => chartPoint_apply_comm point rowIndex colIndex, ?_, ?_,
    point.weight_nonneg, point.weight_sum_one⟩
  · intro rowIndex colIndex
    have hentry := congrFun (congrFun point.isIdempotent rowIndex) colIndex
    rwa [Matrix.mul_apply] at hentry
  · simpa only [Matrix.trace, Matrix.diag_apply] using point.hasTraceRank

/-- A member of the closed chart domain IS a chart point.  No factorisation is
involved: the chart stays a matrix and is never written as `V Vᵀ`, so this is
unrelated to the `Gtz.ChartPointHasDesign` leaf. -/
def chartPointOfMem {config : (Fin size → Fin size → ℝ) × (Fin size → ℝ)}
    (hmem : config ∈ chartDomain size rank) : ChartPoint size rank where
  chart := Matrix.of config.1
  weight := config.2
  isSymmetric := by
    ext rowIndex colIndex
    simpa only [Matrix.transpose_apply, Matrix.of_apply] using hmem.1 rowIndex colIndex
  isIdempotent := by
    ext rowIndex colIndex
    simpa only [Matrix.mul_apply, Matrix.of_apply] using hmem.2.1 rowIndex colIndex
  hasTraceRank := by
    simpa only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply] using hmem.2.2.1
  weight_nonneg := hmem.2.2.2.1
  weight_sum_one := hmem.2.2.2.2

/-! ## Boundedness: every chart entry lies in `[-1, 1]` -/

/-- **The entry bound.**  Symmetry plus idempotency give `sum_r P_rc^2 = P_cc` at
every column, so `P_cc^2 <= P_cc` with `P_cc >= 0` forces `P_cc <= 1`, and then
every entry of that column satisfies `P_rc^2 <= P_cc <= 1`.

This is the whole of boundedness: the chart lives in the cube and the weights in
the simplex, so the domain sits inside the unit ball. -/
theorem abs_chartEntry_le_one_of_mem_chartDomain
    {config : (Fin size → Fin size → ℝ) × (Fin size → ℝ)}
    (hmem : config ∈ chartDomain size rank) (rowIndex colIndex : Fin size) :
    |config.1 rowIndex colIndex| ≤ 1 := by
  obtain ⟨hsymmetric, hidempotent, _, _, _⟩ := hmem
  have hcolumnNorm : ∑ midIndex, config.1 midIndex colIndex * config.1 midIndex colIndex
      = config.1 colIndex colIndex := by
    rw [← hidempotent colIndex colIndex]
    exact Finset.sum_congr rfl fun midIndex _ => by rw [hsymmetric midIndex colIndex]
  have hentrySquare : ∀ someRow : Fin size,
      config.1 someRow colIndex * config.1 someRow colIndex ≤ config.1 colIndex colIndex := by
    intro someRow
    calc config.1 someRow colIndex * config.1 someRow colIndex
        ≤ ∑ midIndex, config.1 midIndex colIndex * config.1 midIndex colIndex :=
          Finset.single_le_sum
            (f := fun midIndex => config.1 midIndex colIndex * config.1 midIndex colIndex)
            (fun _ _ => mul_self_nonneg _) (Finset.mem_univ someRow)
      _ = config.1 colIndex colIndex := hcolumnNorm
  have hdiagNonneg : 0 ≤ config.1 colIndex colIndex := by
    rw [← hcolumnNorm]
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hdiagLeOne : config.1 colIndex colIndex ≤ 1 := by
    nlinarith [hentrySquare colIndex, hdiagNonneg]
  have hsquareLeOne : config.1 rowIndex colIndex * config.1 rowIndex colIndex ≤ 1 :=
    le_trans (hentrySquare rowIndex) hdiagLeOne
  rw [abs_le]
  constructor <;> nlinarith [hsquareLeOne]

/-- The chart diagonal is at most one -- the chart-point reading of the entry
bound.  The companion lower bound `Gtz.chartPoint_diag_nonneg` is shipped. -/
theorem chartPoint_diag_le_one (point : ChartPoint size rank) (pivotIndex : Fin size) :
    point.chart pivotIndex pivotIndex ≤ 1 := by
  have hbound := abs_chartEntry_le_one_of_mem_chartDomain
    (chartConfig_mem_chartDomain point) pivotIndex pivotIndex
  exact (abs_le.mp hbound).2

/-- **The rank window is free.**  A chart point exists only when `rank <= size`:
the trace is the sum of `size` diagonal entries, each at most one.  So the
candidate family below is nonempty at every chart point and no side hypothesis
has to be carried. -/
theorem rank_le_size_of_chartPoint (point : ChartPoint size rank) : rank ≤ size := by
  have hdiagSum : ∑ diagIndex, point.chart diagIndex diagIndex = (rank : ℝ) := by
    simpa only [Matrix.trace, Matrix.diag_apply] using point.hasTraceRank
  have hcast : (rank : ℝ) ≤ (size : ℝ) := by
    rw [← hdiagSum]
    calc ∑ diagIndex, point.chart diagIndex diagIndex
        ≤ ∑ _diagIndex : Fin size, (1 : ℝ) :=
          Finset.sum_le_sum fun diagIndex _ => chartPoint_diag_le_one point diagIndex
      _ = (size : ℝ) := by simp
  exact_mod_cast hcast

/-! ## The domain is compact -/

/-- **The closed chart domain is closed.**  Five non-strict scalar conditions,
each the preimage of a closed set under a continuous map. -/
theorem isClosed_chartDomain (size rank : ℕ) : IsClosed (chartDomain size rank) := by
  have hchartEntry : ∀ rowIndex colIndex : Fin size,
      Continuous fun config : (Fin size → Fin size → ℝ) × (Fin size → ℝ) =>
        config.1 rowIndex colIndex := fun _ _ => by fun_prop
  have hweightEntry : ∀ atomIndex : Fin size,
      Continuous fun config : (Fin size → Fin size → ℝ) × (Fin size → ℝ) =>
        config.2 atomIndex := fun _ => by fun_prop
  have hsymmetricClosed :
      IsClosed {config : (Fin size → Fin size → ℝ) × (Fin size → ℝ) |
        ∀ rowIndex colIndex, config.1 colIndex rowIndex = config.1 rowIndex colIndex} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun rowIndex => ?_
    rw [Set.setOf_forall]
    exact isClosed_iInter fun colIndex =>
      isClosed_eq (hchartEntry colIndex rowIndex) (hchartEntry rowIndex colIndex)
  have hidempotentClosed :
      IsClosed {config : (Fin size → Fin size → ℝ) × (Fin size → ℝ) |
        ∀ rowIndex colIndex,
          ∑ midIndex, config.1 rowIndex midIndex * config.1 midIndex colIndex
            = config.1 rowIndex colIndex} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun rowIndex => ?_
    rw [Set.setOf_forall]
    refine isClosed_iInter fun colIndex => isClosed_eq ?_ (hchartEntry rowIndex colIndex)
    exact continuous_finsetSum _ fun midIndex _ =>
      (hchartEntry rowIndex midIndex).mul (hchartEntry midIndex colIndex)
  have htraceClosed :
      IsClosed {config : (Fin size → Fin size → ℝ) × (Fin size → ℝ) |
        ∑ diagIndex, config.1 diagIndex diagIndex = (rank : ℝ)} :=
    isClosed_eq (continuous_finsetSum _ fun diagIndex _ => hchartEntry diagIndex diagIndex)
      continuous_const
  have hweightNonnegClosed :
      IsClosed {config : (Fin size → Fin size → ℝ) × (Fin size → ℝ) |
        ∀ atomIndex, 0 ≤ config.2 atomIndex} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun atomIndex =>
      isClosed_le continuous_const (hweightEntry atomIndex)
  have hweightSumClosed :
      IsClosed {config : (Fin size → Fin size → ℝ) × (Fin size → ℝ) |
        ∑ atomIndex, config.2 atomIndex = 1} :=
    isClosed_eq (continuous_finsetSum _ fun atomIndex _ => hweightEntry atomIndex)
      continuous_const
  exact hsymmetricClosed.inter (hidempotentClosed.inter
    (htraceClosed.inter (hweightNonnegClosed.inter hweightSumClosed)))

/-- **THE COMPACTNESS THEOREM.**  Closed plus bounded in a finite-dimensional
space.  Every chart entry is in `[-1, 1]` and every weight in `[0, 1]`, so the
sup norm of the whole configuration is at most one.

This is Heine-Borel and nothing else: no manifold structure on the set of
symmetric idempotents is used or asserted, and the domain's compactness is
NOT inherited from `Gtz.isCompact_collaredSet`, which compactifies the DESIGN
class away from the weight boundary -- exactly the complementary region. -/
theorem isCompact_chartDomain (size rank : ℕ) : IsCompact (chartDomain size rank) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_chartDomain size rank) ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, ?_⟩
  rintro ⟨chart, weight⟩ hmem
  have hchartNorm : ‖chart‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro rowIndex
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro colIndex
    rw [Real.norm_eq_abs]
    exact abs_chartEntry_le_one_of_mem_chartDomain hmem rowIndex colIndex
  have hweightNorm : ‖weight‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro atomIndex
    rw [Real.norm_eq_abs, abs_of_nonneg (hmem.2.2.2.1 atomIndex)]
    exact weight_le_one_of_sum_one hmem.2.2.2.2 hmem.2.2.2.1 atomIndex
  calc ‖((chart, weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ))‖
      = max ‖chart‖ ‖weight‖ := rfl
    _ ≤ 1 := max_le hchartNorm hweightNorm

/-! ## The chart objective -/

/-- The chart gap `W = P - diag t` on a raw configuration.  Affine in the whole
configuration, which is why every continuity statement below is entrywise. -/
noncomputable def chartGapRaw (config : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) :
    Matrix (Fin size) (Fin size) ℝ :=
  Matrix.of config.1 - Matrix.diagonal config.2

/-- On a chart point's configuration the raw gap IS `Gtz.chartPointGap`. -/
theorem chartGapRaw_chartConfig (point : ChartPoint size rank) :
    chartGapRaw ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ))
      = chartPointGap point := rfl

theorem continuous_chartGapRaw (size : ℕ) :
    Continuous fun config : (Fin size → Fin size → ℝ) × (Fin size → ℝ) =>
      chartGapRaw config := by
  refine continuous_matrix fun rowIndex colIndex => ?_
  rcases eq_or_ne rowIndex colIndex with rfl | hoffDiagonal
  · simp only [chartGapRaw, Matrix.sub_apply, Matrix.of_apply, Matrix.diagonal_apply_eq]
    fun_prop
  · simp only [chartGapRaw, Matrix.sub_apply, Matrix.of_apply,
      Matrix.diagonal_apply_ne _ hoffDiagonal, sub_zero]
    fun_prop

/-- The least eigenvalue of the gap's principal block at a selection, junk `0` at
a selection of the wrong cardinality so the definition is TOTAL.  The junk branch
is never reached on `Gtz.chartCandidates`. -/
noncomputable def chartBlockValue (rank : ℕ) [Nonempty (Fin rank)]
    (config : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) (selected : Finset (Fin size)) : ℝ :=
  if hcard : selected.card = rank then
    lambdaMinMat ((chartGapRaw config).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard))
  else 0

/-- The selections the objective maximises over: every subset of the right
cardinality. -/
def chartCandidates (size rank : ℕ) : Finset (Finset (Fin size)) :=
  Finset.univ.filter fun selected => selected.card = rank

theorem mem_chartCandidates_iff (size rank : ℕ) (selected : Finset (Fin size)) :
    selected ∈ chartCandidates size rank ↔ selected.card = rank := by
  simp [chartCandidates]

theorem chartCandidates_nonempty (hrank : rank ≤ size) :
    (chartCandidates size rank).Nonempty := by
  obtain ⟨selected, _, hcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin size))) (n := rank)
      (by simpa using hrank)
  exact ⟨selected, (mem_chartCandidates_iff size rank selected).mpr hcard⟩

/-- **The chart objective** `G = max_C lambda_min(W[C])` on a raw configuration.
The nonemptiness of the candidate family is supplied by `rank <= size`, which
`Gtz.rank_le_size_of_chartPoint` derives from any chart point, so no genuine side
hypothesis is being smuggled in. -/
noncomputable def chartObjectiveRaw (size rank : ℕ) [Nonempty (Fin rank)] (hrank : rank ≤ size)
    (config : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) : ℝ :=
  (chartCandidates size rank).sup' (chartCandidates_nonempty hrank)
    fun selected => chartBlockValue rank config selected

/-- **The chart objective at a chart point.** -/
noncomputable def chartObjective [Nonempty (Fin rank)] (point : ChartPoint size rank) : ℝ :=
  chartObjectiveRaw size rank (rank_le_size_of_chartPoint point) (point.chart, point.weight)

theorem chartObjective_eq_chartObjectiveRaw [Nonempty (Fin rank)]
    (point : ChartPoint size rank) (hrank : rank ≤ size) :
    chartObjective point
      = chartObjectiveRaw size rank hrank
          ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) := rfl

theorem chartObjective_chartPointOfMem [Nonempty (Fin rank)]
    {config : (Fin size → Fin size → ℝ) × (Fin size → ℝ)}
    (hmem : config ∈ chartDomain size rank) (hrank : rank ≤ size) :
    chartObjective (chartPointOfMem hmem) = chartObjectiveRaw size rank hrank config := rfl

/-! ## Continuity -/

theorem continuous_chartBlockValue (size rank : ℕ) [Nonempty (Fin rank)]
    (selected : Finset (Fin size)) :
    Continuous fun config : (Fin size → Fin size → ℝ) × (Fin size → ℝ) =>
      chartBlockValue rank config selected := by
  by_cases hcard : selected.card = rank
  · simp only [chartBlockValue, dif_pos hcard]
    exact continuous_lambdaMinMat.comp
      ((continuous_chartGapRaw size).matrix_submatrix _ _)
  · simp only [chartBlockValue, dif_neg hcard]
    exact continuous_const

/-- **The chart objective is continuous.**  Weyl
(`Gtz.lipschitzWith_lambdaMinCLM`, shipped) through
`Gtz.continuous_lambdaMinMat`, composed with the entrywise continuity of the
affine gap and closed under a finite `sup'`.  No Lipschitz constant is tracked
and none is needed. -/
theorem continuous_chartObjectiveRaw (size rank : ℕ) [Nonempty (Fin rank)]
    (hrank : rank ≤ size) : Continuous (chartObjectiveRaw size rank hrank) := by
  refine Continuous.finset_sup'_apply (chartCandidates_nonempty hrank) ?_
  exact fun selected _ => continuous_chartBlockValue size rank selected

/-! ## The threshold dictionary -/

/-- The gap's principal block is symmetric. -/
theorem isHermitian_chartPointGap_submatrix (point : ChartPoint size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) :
    ((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard)).IsHermitian := by
  show ((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
    (selected.orderEmbOfFin hcard))ᴴ = _
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_submatrix,
    chartPointGap_transpose]

theorem chartBlockValue_chartConfig [Nonempty (Fin rank)] (point : ChartPoint size rank)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) :
    chartBlockValue rank
        ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) selected
      = lambdaMinMat ((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)) := by
  rw [chartBlockValue, dif_pos hcard]
  rfl

/-- **Per subset**: the block value is nonnegative exactly when the selection
chart-dominates.  The shipped `Gtz.chartDominates_iff_posSemidef_submatrix`
supplies the right-hand identification. -/
theorem zero_le_chartBlockValue_iff_chartDominates [Nonempty (Fin rank)]
    (point : ChartPoint size rank) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) :
    0 ≤ chartBlockValue rank
        ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) selected
      ↔ ChartDominates point selected := by
  rw [chartBlockValue_chartConfig point hcard,
    zero_le_lambdaMinMat_iff_posSemidef _
      (isHermitian_chartPointGap_submatrix point selected hcard),
    ← chartDominates_iff_posSemidef_submatrix point selected hcard]

/-- **THE THRESHOLD DICTIONARY.**  The chart objective is nonnegative exactly
when some `rank`-subset chart-dominates.  The threshold is ZERO, not one -- this
is the chart objective, and the recorded objective mismatch with the design
objective `max_C lambda_min(S_C)` is untouched. -/
theorem zero_le_chartObjective_iff_exists_chartDominates [Nonempty (Fin rank)]
    (point : ChartPoint size rank) :
    0 ≤ chartObjective point
      ↔ ∃ selected : Finset (Fin size), selected.card = rank ∧ ChartDominates point selected := by
  rw [chartObjective, chartObjectiveRaw, Finset.le_sup'_iff]
  constructor
  · rintro ⟨selected, hmember, hvalue⟩
    have hcard : selected.card = rank :=
      (mem_chartCandidates_iff size rank selected).mp hmember
    exact ⟨selected, hcard, (zero_le_chartBlockValue_iff_chartDominates point hcard).mp hvalue⟩
  · rintro ⟨selected, hcard, hdominates⟩
    exact ⟨selected, (mem_chartCandidates_iff size rank selected).mpr hcard,
      (zero_le_chartBlockValue_iff_chartDominates point hcard).mpr hdominates⟩

/-! ## Attainment -/

/-- Attainment on the raw configuration space: the extreme value theorem against
`Gtz.isCompact_chartDomain` and `Gtz.continuous_chartObjectiveRaw`. -/
theorem exists_isMinOn_chartObjectiveRaw (size rank : ℕ) [Nonempty (Fin rank)]
    (hrank : rank ≤ size) (hnonempty : (chartDomain size rank).Nonempty) :
    ∃ minimiser ∈ chartDomain size rank, ∀ other ∈ chartDomain size rank,
      chartObjectiveRaw size rank hrank minimiser ≤ chartObjectiveRaw size rank hrank other := by
  obtain ⟨minimiser, hmember, hmin⟩ := (isCompact_chartDomain size rank).exists_isMinOn hnonempty
    (continuous_chartObjectiveRaw size rank hrank).continuousOn
  exact ⟨minimiser, hmember, fun other hother => isMinOn_iff.mp hmin other hother⟩

/-- **THE ATTAINMENT THEOREM.**  Given any chart point at all, the chart
objective attains its minimum over the whole closed chart domain at some chart
point.  The witness is what makes the domain nonempty; it also supplies
`rank <= size`, so no side hypothesis is carried. -/
theorem exists_chartObjective_isMin [Nonempty (Fin rank)] (witness : ChartPoint size rank) :
    ∃ minimiser : ChartPoint size rank,
      ∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point := by
  have hrank : rank ≤ size := rank_le_size_of_chartPoint witness
  have hnonempty : (chartDomain size rank).Nonempty :=
    ⟨_, chartConfig_mem_chartDomain witness⟩
  obtain ⟨config, hmember, hmin⟩ := exists_isMinOn_chartObjectiveRaw size rank hrank hnonempty
  refine ⟨chartPointOfMem hmember, fun point => ?_⟩
  have hvalue := hmin ((point.chart, point.weight) :
    (Fin size → Fin size → ℝ) × (Fin size → ℝ)) (chartConfig_mem_chartDomain point)
  rw [chartObjective_chartPointOfMem hmember hrank, chartObjective_eq_chartObjectiveRaw point hrank]
  exact hvalue

/-! ## The consumable packagings -/

/-- **ONE SCALAR SIGN AT ONE POINT DECIDES THE CLOSED STATEMENT.**  A minimiser
with nonnegative objective value gives `Gtz.ChartGtz` outright. -/
theorem chartGtz_of_isMin_of_nonneg [Nonempty (Fin rank)] (minimiser : ChartPoint size rank)
    (hmin : ∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point)
    (hnonneg : 0 ≤ chartObjective minimiser) : ChartGtz size rank := fun point =>
  (zero_le_chartObjective_iff_exists_chartDominates point).mp
    (le_trans hnonneg (hmin point))

/-- The weighted reading of the same fact, through the shipped easy bridge
`Gtz.gtzWeighted_of_chartGtz`: one nonnegative scalar at one minimising chart
point gives `Gtz.GtzWeighted` at that size. -/
theorem gtzWeighted_of_isMin_of_nonneg [Nonempty (Fin rank)] (minimiser : ChartPoint size rank)
    (hmin : ∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point)
    (hnonneg : 0 ≤ chartObjective minimiser) : GtzWeighted size rank :=
  gtzWeighted_of_chartGtz (chartGtz_of_isMin_of_nonneg minimiser hmin hnonneg)

/-- **THE MINIMISING COUNTEREXAMPLE.**  If the closed chart statement fails then
the failure is realised at a GLOBAL MINIMISER of the chart objective, whose value
is strictly negative and at which no selection of the right cardinality
dominates.

This is the object every compactness argument in the campaign wanted and none
had.  It carries no first-order data: this file adds no subdifferential calculus
and the minimiser is not proved to be a critical point of anything. -/
theorem exists_minimiser_of_not_chartGtz [Nonempty (Fin rank)] (hfail : ¬ ChartGtz size rank) :
    ∃ minimiser : ChartPoint size rank,
      (∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point)
      ∧ chartObjective minimiser < 0
      ∧ ∀ selected : Finset (Fin size), selected.card = rank →
          ¬ ChartDominates minimiser selected := by
  obtain ⟨witness, hwitness⟩ : ∃ point : ChartPoint size rank,
      ∀ selected : Finset (Fin size), selected.card = rank → ¬ ChartDominates point selected := by
    by_contra hall
    refine hfail fun point => ?_
    by_contra hnone
    exact hall ⟨point, fun selected hcard hdominates => hnone ⟨selected, hcard, hdominates⟩⟩
  obtain ⟨minimiser, hmin⟩ := exists_chartObjective_isMin witness
  have hwitnessNegative : chartObjective witness < 0 := by
    by_contra hnonneg
    obtain ⟨selected, hcard, hdominates⟩ :=
      (zero_le_chartObjective_iff_exists_chartDominates witness).mp (not_lt.mp hnonneg)
    exact hwitness selected hcard hdominates
  have hminimiserNegative : chartObjective minimiser < 0 :=
    lt_of_le_of_lt (hmin witness) hwitnessNegative
  refine ⟨minimiser, hmin, hminimiserNegative, fun selected hcard hdominates => ?_⟩
  exact absurd ((zero_le_chartObjective_iff_exists_chartDominates minimiser).mpr
    ⟨selected, hcard, hdominates⟩) (not_le.mpr hminimiserNegative)

/-- **S1's DELIVERABLE.**  Given the two smaller rungs, a failure of the closed
chart statement at `(size + 1, rank + 1)` is realised at ONE chart point which
minimises the chart objective, has strictly negative value, admits no dominating
selection, and has ALL WEIGHTS STRICTLY POSITIVE.

The interior clause is the shipped boundary dichotomy
`Gtz.weight_pos_of_forall_not_chartDominates`, whose own docstring says it is the
packaging "a compactness argument consumes" and that the density theorem
`Gtz.chartGtz_of_chartGtzInterior` cannot replace it, because density relocates
the counterexample and destroys whatever distinguished it -- here, being a
minimiser.  This theorem is that composition.  At `(6, 3)` the hypotheses read
`Gtz.ChartGtz 5 3` and `Gtz.ChartGtz 5 2`.

WHAT IT DOES NOT DO: it closes no cell, it produces no multiplier, and it does
not say the minimiser is critical.  Reading first-order data off this point needs
a descent argument that is not in this file and not in this repository. -/
theorem exists_interior_minimiser_of_not_chartGtz (hsameRank : ChartGtz size (rank + 1))
    (hdropRank : ChartGtz size rank) (hfail : ¬ ChartGtz (size + 1) (rank + 1)) :
    ∃ minimiser : ChartPoint (size + 1) (rank + 1),
      (∀ point : ChartPoint (size + 1) (rank + 1),
        chartObjective minimiser ≤ chartObjective point)
      ∧ chartObjective minimiser < 0
      ∧ (∀ selected : Finset (Fin (size + 1)), selected.card = rank + 1 →
          ¬ ChartDominates minimiser selected)
      ∧ ∀ atomIndex, 0 < minimiser.weight atomIndex := by
  obtain ⟨minimiser, hmin, hnegative, hfails⟩ := exists_minimiser_of_not_chartGtz hfail
  exact ⟨minimiser, hmin, hnegative, hfails,
    weight_pos_of_forall_not_chartDominates hsameRank hdropRank minimiser hfails⟩

/-- **ENTRY FROM THE TARGET'S OWN FAILURE.**  `Gtz.ChartGtz` implies
`Gtz.GtzWeighted` (shipped, `Gtz.gtzWeighted_of_chartGtz`), so a failure of the
WEIGHTED statement is a failure of the closed chart statement and the minimising
interior counterexample applies verbatim.

At `(6, 3)` this reads: if `Gtz.GtzWeighted 6 3` is false, then -- given
`Gtz.ChartGtz 5 3` and `Gtz.ChartGtz 5 2` -- there is a chart point with all six
weights strictly positive, no dominating triple, strictly negative chart
objective, and MINIMAL chart objective over the whole closed domain.  That
minimality is the only new word, and it is what every stationarity argument in
the campaign silently assumed. -/
theorem exists_interior_minimiser_of_not_gtzWeighted (hsameRank : ChartGtz size (rank + 1))
    (hdropRank : ChartGtz size rank) (hfail : ¬ GtzWeighted (size + 1) (rank + 1)) :
    ∃ minimiser : ChartPoint (size + 1) (rank + 1),
      (∀ point : ChartPoint (size + 1) (rank + 1),
        chartObjective minimiser ≤ chartObjective point)
      ∧ chartObjective minimiser < 0
      ∧ (∀ selected : Finset (Fin (size + 1)), selected.card = rank + 1 →
          ¬ ChartDominates minimiser selected)
      ∧ ∀ atomIndex, 0 < minimiser.weight atomIndex :=
  exists_interior_minimiser_of_not_chartGtz hsameRank hdropRank fun hchart =>
    hfail (gtzWeighted_of_chartGtz hchart)

/-! ## Non-vacuity

Everything above is an implication, and an implication whose objects do not exist
is worthless.  These two guards use the shipped `(4, 2)` witness
`Gtz.liftFailurePoint` to show that the domain is inhabited, that attainment
fires on it, and that the threshold dictionary points the right way. -/

/-- **THE ATTAINMENT THEOREM FIRES.**  The shipped `(4, 2)` chart point
`Gtz.liftFailurePoint` inhabits the domain, so a minimiser of the chart objective
exists at `(4, 2)`.  Guards against the whole file being vacuously true. -/
theorem exists_chartObjective_isMin_fourTwo :
    ∃ minimiser : ChartPoint 4 2,
      ∀ point : ChartPoint 4 2, chartObjective minimiser ≤ chartObjective point :=
  exists_chartObjective_isMin liftFailurePoint

/-- **THE DICTIONARY POINTS THE RIGHT WAY.**  `Gtz.not_chartDominates_liftFailure`
says the selection `{0, 1}` fails to dominate at `Gtz.liftFailurePoint`; the
dictionary turns that into a STRICTLY NEGATIVE block value there.  So
`Gtz.chartBlockValue` is not constantly nonnegative and the threshold really
separates. -/
theorem chartBlockValue_liftFailure_neg :
    chartBlockValue 2
        ((liftFailurePoint.chart, liftFailurePoint.weight) :
          (Fin 4 → Fin 4 → ℝ) × (Fin 4 → ℝ))
        (insert 1 {0}) < 0 := by
  by_contra hnonneg
  exact not_chartDominates_liftFailure
    ((zero_le_chartBlockValue_iff_chartDominates liftFailurePoint
      (by decide : (insert 1 {0} : Finset (Fin 4)).card = 2)).mp (not_lt.mp hnonneg))

end Gtz

/-
# The chart core: a design is ONE symmetric matrix and ONE quadratic equation

A weighted design is `m` vectors, `m` weights, and Parseval.  Its chart
`P = V Vᵀ` (`Gtz.projectionOfDesign`) is a rank-`k` orthogonal projection on the
INDEX space, and the campaign already reads domination off the chart GAP

    `M := P - diag t`

both weakly (`Gtz.dominates_iff_posSemidef_projectionBlock`) and strictly
(`Gtz.posDef_gap_iff_posDef_projectionBlock`).  What no shipped statement does is
say what the pair `(M, t)` HAS to satisfy, so nothing downstream can quantify over
charts without carrying a design.  This module supplies that.

## The quadratic equation

`P = M + diag t` is idempotent, so

    **`M M + M T + T M + T T = M + T`,   `T := diag t`**

and, together with `tr M = k − 1`, `t_c > 0`, `Σ t_c = 1`, THAT IS THE WHOLE
DESIGN CONDITION.  `Gtz.ChartCore` packages exactly those five items.  No vector,
no Parseval, no Gram matrix, and no projection appears in the structure: the
projection is DERIVED (`Gtz.ChartCore.chart`) and its idempotence is the quadratic
equation rearranged (`Gtz.chartQuadratic_iff_mul_self`).

The trace reading is worth naming on its own.  `tr(M + T) = k` and `Σ t_c = 1`, so
`tr M = k − 1` at EVERY design of rank `k` — a weight-free normalisation of the
gap, which is why the structure carries it in that form.

## The equivalence, both ways

* `Gtz.chartCoreOfDesign` sends a design to its core.
* `Gtz.exists_design_of_chartCore` sends a core back to a design with the SAME
  weights and the SAME gap.  It runs through `Gtz.chartPointHasDesign`, which the
  repository has carried since the compactness ladder landed, so the only new step
  is the quadratic-equation half.

Without the second map the chart proves nothing about the conjecture, because a
statement about all `M` would be a statement about a superset of the designs.
With it, `Gtz.gtzWeighted_iff_chartCore` and `Gtz.hingeHoldsAtSize_iff_chartCore`
are EQUIVALENCES, at every size and every rank:

    **`GtzWeighted m k` ⟺ every real symmetric `M` and positive `t` solving the
     quadratic equation with `tr M = k − 1` carry a `k`-subset `C` with
     `M[C, C] ⪰ 0`.**

    **`HingeHoldsAtSize m k` ⟺ whenever some `M[C, C] ⪰ 0` and no `M[C, C] ≻ 0`,
     two labels satisfy `(M_pp + t_p)(M_qq + t_q) = M_pq²`.**

At `(6,3)` the right sides mention a `6 × 6` real symmetric matrix, its twenty
`3 × 3` principal blocks, and six positive numbers.  Nothing else.

## The pair readings

`Gtz.ChartCore.HasParallelPairCore` is the vanishing of the `2 × 2` determinant of
the CHART on a pair, written in the gap: `(M_pp + t_p)(M_qq + t_q) − M_pq²`.  That
is `t_p t_q` times the landed `Gtz.pairGramMinor`
(`Gtz.chartPairDeterminant_eq_weight_mul_pairGramMinor`), so it vanishes exactly at
a parallel pair, and the weights cannot make it vanish spuriously.

The complementary `2 × 2` determinant — the same block shifted by `T − 1` instead
of by `T` — is the campaign's PAIRING CAP slack
(`Gtz.chartCoPairDeterminant_eq_pairCapSlack`), which at `(6,3)` vanishes exactly
when the complementary four atoms are coplanar
(`Gtz.pairCapSlack_eq_zero_iff_fourCoplanar'`).  So both halves of the `(6,3)`
hinge dictionary are one `2 × 2` block of `M`, read against two different
diagonal shifts, and `diag(t(1−t))` is the product of the two.

## What was already landed, and is NOT re-derived here

Job A of this lane's brief is shipped in full and this module only cites it:
`Gtz.dominates_iff_posSemidef_projectionBlock{,_finset}` and
`Gtz.posDef_gap_iff_posDef_projectionBlock` are the weak and strict block
criteria, `Gtz.chartGap` and `Gtz.chartGapRayleigh_{pos_of_fixed,neg_of_killed}`
are the field-generic gap and its two Rayleigh statements, and
`Gtz.chartPointHasDesign` is the factorisation.  What is new is the QUADRATIC
presentation, the realisation stated at the gap rather than at the projection, and
the two design-free equivalences.

The chart dual of `Gtz/Quantitative/ChartDuality.lean` — the complement chart
`1 − P` — is a DIFFERENT object from the sharp dual, and the module records that it
does not transport domination.  Nothing here uses it.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.CompactnessReduction
import Gtz.Reduction.ChartPointFactorisation
import Gtz.Reduction.SplitTransfer
import Gtz.Certificates.ResidueDissolution
import Gtz.Wave.TieParallelPairWeightRegular
import Gtz.Wave.SharpShareCoAtom
import Gtz.Wave.ComplementVolumeRowLaw
import Gtz.Quantitative.ChartDuality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — the quadratic equation is idempotence, rearranged

One lemma carries the whole translation.  Everything below reads it in one
direction or the other, and nothing else about the equation is ever needed. -/

/-- **THE QUADRATIC EQUATION IS IDEMPOTENCE.**  Expanding `(M + T)(M + T)` gives the
four terms of the equation, so the equation says exactly that `M + T` is
idempotent.  No hypothesis on `M` or `T`: this is the distributive law. -/
theorem chartQuadratic_iff_mul_self {size : ℕ}
    (gapMatrix shiftMatrix : Matrix (Fin size) (Fin size) ℝ) :
    gapMatrix * gapMatrix + gapMatrix * shiftMatrix + shiftMatrix * gapMatrix
        + shiftMatrix * shiftMatrix = gapMatrix + shiftMatrix
      ↔ (gapMatrix + shiftMatrix) * (gapMatrix + shiftMatrix) = gapMatrix + shiftMatrix := by
  have hexpand : (gapMatrix + shiftMatrix) * (gapMatrix + shiftMatrix)
      = gapMatrix * gapMatrix + gapMatrix * shiftMatrix + shiftMatrix * gapMatrix
        + shiftMatrix * shiftMatrix := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  rw [hexpand]

/-- A principal submatrix of a diagonal matrix along an INJECTIVE index map is the
diagonal of the restricted entries. -/
theorem submatrix_diagonal_of_injective {size selectionSize : ℕ} (entry : Fin size → ℝ)
    {pick : Fin selectionSize → Fin size} (hpick : Function.Injective pick) :
    (Matrix.diagonal entry).submatrix pick pick
      = Matrix.diagonal fun selectedIndex => entry (pick selectedIndex) := by
  ext leftIndex rightIndex
  rcases eq_or_ne leftIndex rightIndex with rfl | hne
  · rw [Matrix.submatrix_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · rw [Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ (fun heq => hne (hpick heq)),
      Matrix.diagonal_apply_ne _ hne]

/-! ## Part 2 — the chart core

Five fields.  A real symmetric matrix, a positive weight vector on the simplex, one
quadratic matrix equation, and one trace normalisation.  A `Gtz.WeightedDesign`
carries eleven pieces of data and a Parseval identity in `ℝ^k`; a `Gtz.ChartCore`
carries none of that, and Part 3 shows the two are interchangeable. -/

/-- **THE CHART CORE.**  A symmetric `size × size` gap `M` together with a positive
weight vector `t` on the simplex, satisfying

    `M M + M T + T M + T T = M + T`,   `T = diag t`,   `tr M = rank − 1`.

`Gtz.exists_design_of_chartCore` shows these are exactly the gaps of designs. -/
structure ChartCore (size rank : ℕ) where
  /-- The chart gap `M = P − diag t`. -/
  gap : Matrix (Fin size) (Fin size) ℝ
  /-- The weights. -/
  weight : Fin size → ℝ
  /-- The gap is symmetric. -/
  gap_transpose : gapᵀ = gap
  /-- The weights are strictly positive. -/
  weight_pos : ∀ atomIndex, 0 < weight atomIndex
  /-- The weights sum to one. -/
  weight_sum_one : ∑ atomIndex, weight atomIndex = 1
  /-- **The realizability equation.**  This single line replaces Parseval. -/
  isQuadratic :
    gap * gap + gap * Matrix.diagonal weight + Matrix.diagonal weight * gap
      + Matrix.diagonal weight * Matrix.diagonal weight = gap + Matrix.diagonal weight
  /-- The gap's trace is the rank less one — the weight-free normalisation. -/
  hasTraceRank : Matrix.trace gap = (rank : ℝ) - 1

variable {size rank : ℕ}

/-- The chart of a core: the gap shifted back by the weight diagonal. -/
def ChartCore.chart (core : ChartCore size rank) : Matrix (Fin size) (Fin size) ℝ :=
  core.gap + Matrix.diagonal core.weight

theorem ChartCore.chart_transpose (core : ChartCore size rank) :
    (core.chart)ᵀ = core.chart := by
  rw [ChartCore.chart, Matrix.transpose_add, core.gap_transpose, Matrix.diagonal_transpose]

/-- **The chart of a core is idempotent** — the quadratic equation, read forwards. -/
theorem ChartCore.chart_mul_self (core : ChartCore size rank) :
    core.chart * core.chart = core.chart :=
  (chartQuadratic_iff_mul_self core.gap (Matrix.diagonal core.weight)).mp core.isQuadratic

/-- **The chart of a core has trace the rank.**  The gap contributes `rank − 1` and
the weight diagonal contributes the total weight, which is one. -/
theorem ChartCore.trace_chart (core : ChartCore size rank) :
    Matrix.trace core.chart = (rank : ℝ) := by
  rw [ChartCore.chart, Matrix.trace_add, core.hasTraceRank, Matrix.trace_diagonal,
    core.weight_sum_one]
  ring

/-- A core read as a chart point of the compactness ladder. -/
def ChartCore.toChartPoint (core : ChartCore size rank) : ChartPoint size rank where
  chart := core.chart
  weight := core.weight
  isSymmetric := core.chart_transpose
  isIdempotent := core.chart_mul_self
  hasTraceRank := core.trace_chart
  weight_nonneg := fun atomIndex => (core.weight_pos atomIndex).le
  weight_sum_one := core.weight_sum_one

@[simp] theorem ChartCore.toChartPoint_chart (core : ChartCore size rank) :
    core.toChartPoint.chart = core.chart := rfl

@[simp] theorem ChartCore.toChartPoint_weight (core : ChartCore size rank) :
    core.toChartPoint.weight = core.weight := rfl

/-! ## Part 3 — a design IS a chart core

Both maps.  The forward map spends only idempotence of the projection; the backward
map spends the shipped factorisation of a positive-weight chart point. -/

/-- **THE CHART GAP OF A DESIGN**, `M = P − diag t`, over `ℝ`.  This is the real
reading of the field-generic `Gtz.chartGap`, pinned by
`Gtz.chartGap_eq_projectionBlockGap`, and it is the matrix every statement below is
about. -/
noncomputable def chartGapOfDesign (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  projectionOfDesign D - Matrix.diagonal D.weight

theorem chartGapOfDesign_transpose (D : WeightedDesign m k) :
    (chartGapOfDesign D)ᵀ = chartGapOfDesign D := by
  rw [chartGapOfDesign, Matrix.transpose_sub, projectionOfDesign_transpose,
    Matrix.diagonal_transpose]

/-- The gap plus the weight diagonal is the chart, on the nose. -/
theorem chartGapOfDesign_add_weightDiagonal (D : WeightedDesign m k) :
    chartGapOfDesign D + Matrix.diagonal D.weight = projectionOfDesign D := by
  rw [chartGapOfDesign]
  abel

/-- Off the diagonal the gap is the chart. -/
theorem chartGapOfDesign_apply_of_ne (D : WeightedDesign m k) {leftLabel rightLabel : Fin m}
    (hne : leftLabel ≠ rightLabel) :
    chartGapOfDesign D leftLabel rightLabel = projectionOfDesign D leftLabel rightLabel := by
  rw [chartGapOfDesign, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hne, sub_zero]

/-- On the diagonal the gap is the weighted heavy excess `t_c(ℓ_c − 1)`. -/
theorem chartGapOfDesign_diagonal (D : WeightedDesign m k) (atomIndex : Fin m) :
    chartGapOfDesign D atomIndex atomIndex
      = D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1) := by
  rw [chartGapOfDesign, Matrix.sub_apply, Matrix.diagonal_apply_eq,
    projectionOfDesign_diagonal]
  ring

/-- **THE TRACE OF THE GAP IS THE RANK LESS ONE**, at every design, with no weight
surviving.  The projection contributes `k` and the weight diagonal one. -/
theorem trace_chartGapOfDesign (D : WeightedDesign m k) :
    Matrix.trace (chartGapOfDesign D) = (k : ℝ) - 1 := by
  rw [chartGapOfDesign, Matrix.trace_sub, trace_projectionOfDesign, Matrix.trace_diagonal,
    D.weight_sum_one]

/-- **THE REALIZABILITY EQUATION HOLDS AT EVERY DESIGN.**  Only idempotence of the
projection is spent. -/
theorem chartGapOfDesign_isQuadratic (D : WeightedDesign m k) :
    chartGapOfDesign D * chartGapOfDesign D
        + chartGapOfDesign D * Matrix.diagonal D.weight
        + Matrix.diagonal D.weight * chartGapOfDesign D
        + Matrix.diagonal D.weight * Matrix.diagonal D.weight
      = chartGapOfDesign D + Matrix.diagonal D.weight := by
  rw [chartQuadratic_iff_mul_self, chartGapOfDesign_add_weightDiagonal]
  exact projectionOfDesign_mul_self D

/-- **THE FORWARD MAP.**  Every design carries a chart core. -/
noncomputable def chartCoreOfDesign (D : WeightedDesign m k) : ChartCore m k where
  gap := chartGapOfDesign D
  weight := D.weight
  gap_transpose := chartGapOfDesign_transpose D
  weight_pos := D.weight_pos
  weight_sum_one := D.weight_sum_one
  isQuadratic := chartGapOfDesign_isQuadratic D
  hasTraceRank := trace_chartGapOfDesign D

@[simp] theorem chartCoreOfDesign_gap (D : WeightedDesign m k) :
    (chartCoreOfDesign D).gap = chartGapOfDesign D := rfl

@[simp] theorem chartCoreOfDesign_weight (D : WeightedDesign m k) :
    (chartCoreOfDesign D).weight = D.weight := rfl

theorem chartCoreOfDesign_chart (D : WeightedDesign m k) :
    (chartCoreOfDesign D).chart = projectionOfDesign D :=
  chartGapOfDesign_add_weightDiagonal D

/-- **THE BACKWARD MAP — THE REALISATION THEOREM.**  Every chart core is the chart
core of a weighted design, with the SAME weights and the SAME gap.  So the
quadratic equation, the trace normalisation and the open simplex are not merely
NECESSARY for a gap: they are sufficient, and the chart is a genuine equivalence
rather than a one-way map.

The projection half is the shipped `Gtz.chartPointHasDesign`; the quadratic half is
`Gtz.ChartCore.chart_mul_self`, which is the equation rearranged. -/
theorem exists_design_of_chartCore (core : ChartCore m k) :
    ∃ D : WeightedDesign m k, D.weight = core.weight ∧ chartGapOfDesign D = core.gap := by
  obtain ⟨D, hpoint⟩ :=
    chartPointHasDesign m k core.toChartPoint (fun atomIndex => core.weight_pos atomIndex)
  have hweight : D.weight = core.weight := congrArg ChartPoint.weight hpoint
  have hchart : projectionOfDesign D = core.chart := congrArg ChartPoint.chart hpoint
  refine ⟨D, hweight, ?_⟩
  rw [chartGapOfDesign, hchart, hweight, ChartCore.chart]
  abel

/-- The realisation, stated as surjectivity of the forward map onto cores up to the
two data fields. -/
theorem exists_design_chartCoreOfDesign_eq (core : ChartCore m k) :
    ∃ D : WeightedDesign m k,
      (chartCoreOfDesign D).gap = core.gap ∧ (chartCoreOfDesign D).weight = core.weight := by
  obtain ⟨D, hweight, hgap⟩ := exists_design_of_chartCore core
  exact ⟨D, hgap, hweight⟩

/-! ## Part 4 — domination is a principal block of the gap

The two block criteria are shipped.  What is added is the reading along a SUBSET's
order embedding of the GAP itself, which is the form the design-free statements
quantify over. -/

/-- The gap's block along an injective selection is the chart block against the
weight diagonal — so the shipped criteria apply to it verbatim. -/
theorem chartGapOfDesign_submatrix (D : WeightedDesign m k) {selectionSize : ℕ}
    {pick : Fin selectionSize → Fin m} (hpick : Function.Injective pick) :
    (chartGapOfDesign D).submatrix pick pick
      = (projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal fun selectedIndex => D.weight (pick selectedIndex) := by
  ext leftIndex rightIndex
  simp only [Matrix.submatrix_apply, chartGapOfDesign, Matrix.sub_apply]
  congr 1
  rcases eq_or_ne leftIndex rightIndex with rfl | hne
  · rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ (fun heq => hne (hpick heq)),
      Matrix.diagonal_apply_ne _ hne]

/-- **DOMINATION IS A POSITIVE SEMIDEFINITE BLOCK OF THE GAP.**  Read along a
`rank`-subset's order embedding. -/
theorem dominates_iff_posSemidef_chartGapBlock (D : WeightedDesign m k)
    (selected : Finset (Fin m)) (hcard : selected.card = k) :
    Dominates D selected
      ↔ ((chartGapOfDesign D).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)).PosSemidef := by
  rw [chartGapOfDesign_submatrix D (selected.orderEmbOfFin hcard).injective]
  exact dominates_iff_posSemidef_projectionBlock_finset D selected hcard

/-- **STRICT DOMINATION IS A POSITIVE DEFINITE BLOCK OF THE GAP.**  The strict twin,
read the same way. -/
theorem posDef_gap_iff_posDef_chartGapBlock (D : WeightedDesign m k)
    (selected : Finset (Fin m)) (hcard : selected.card = k) :
    (subsetSum D selected - 1).PosDef
      ↔ ((chartGapOfDesign D).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)).PosDef := by
  have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  rw [chartGapOfDesign_submatrix D (selected.orderEmbOfFin hcard).injective]
  conv_lhs => rw [← himage]
  exact posDef_gap_iff_posDef_projectionBlock D _ (selected.orderEmbOfFin hcard).injective

/-! ## Part 5 — the design-free statements

Both quantify over `Gtz.ChartCore` and mention no design, no atom and no Parseval.
Both are EQUIVALENCES, and the backward direction of each is exactly the
realisation theorem. -/

/-- Domination in the core: a `rank`-subset whose gap block is positive
semidefinite. -/
def ChartCore.HasDominatingBlock (core : ChartCore size rank) : Prop :=
  ∃ (selected : Finset (Fin size)) (hcard : selected.card = rank),
    ((core.gap).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard)).PosSemidef

/-- A tie in the core: some gap block is positive semidefinite and none is positive
definite. -/
def ChartCore.IsTieCore (core : ChartCore size rank) : Prop :=
  core.HasDominatingBlock
    ∧ ∀ (selected : Finset (Fin size)) (hcard : selected.card = rank),
        ¬ ((core.gap).submatrix (selected.orderEmbOfFin hcard)
            (selected.orderEmbOfFin hcard)).PosDef

/-- A parallel pair in the core: a `2 × 2` CHART determinant that vanishes, written
in the gap.  The shift is by the weight diagonal, and the complementary reading of
Part 7 shifts by `T − 1` instead. -/
def ChartCore.HasParallelPairCore (core : ChartCore size rank) : Prop :=
  ∃ leftLabel rightLabel : Fin size, leftLabel ≠ rightLabel
    ∧ (core.gap leftLabel leftLabel + core.weight leftLabel)
        * (core.gap rightLabel rightLabel + core.weight rightLabel)
      = core.gap leftLabel rightLabel ^ 2

/-- **THE WEIGHTED TARGET IS A STATEMENT ABOUT ONE SYMMETRIC MATRIX.**  At every
size and every rank, `Gtz.GtzWeighted` holds exactly when every real symmetric `M`
and every positive `t` on the simplex solving the realizability equation with
`tr M = rank − 1` carry a `rank`-subset whose principal block of `M` is positive
semidefinite.

The forward direction is the block criterion at a design; the backward direction is
the realisation theorem, and without it the right side would quantify over a strict
superset of the designs and prove nothing. -/
theorem gtzWeighted_iff_chartCore (m k : ℕ) :
    GtzWeighted m k ↔ ∀ core : ChartCore m k, core.HasDominatingBlock := by
  constructor
  · intro hgtz core
    obtain ⟨D, hweight, hgap⟩ := exists_design_of_chartCore core
    obtain ⟨selected, hcard, hdominates⟩ := hgtz D
    refine ⟨selected, hcard, ?_⟩
    rw [← hgap]
    exact (dominates_iff_posSemidef_chartGapBlock D selected hcard).mp hdominates
  · intro hcore D
    obtain ⟨selected, hcard, hblock⟩ := hcore (chartCoreOfDesign D)
    exact ⟨selected, hcard, (dominates_iff_posSemidef_chartGapBlock D selected hcard).mpr hblock⟩

/-- The `(6,3)` reading: a `6 × 6` real symmetric matrix, six positive numbers
summing to one, one quadratic matrix equation, and twenty `3 × 3` blocks. -/
theorem gtzWeighted_six_three_iff_chartCore :
    GtzWeighted 6 3 ↔ ∀ core : ChartCore 6 3, core.HasDominatingBlock :=
  gtzWeighted_iff_chartCore 6 3

/-! ## Part 6 — the tie and the parallel pair in the core

The tie transfers through both block criteria; the parallel pair transfers through
the landed pair minor.  Together they turn the hinge into a matrix statement. -/

/-- The chart determinant of a pair is the weighted pair Gram minor.  Both factors
of the weight are strictly positive, so the two vanish together. -/
theorem chartPairDeterminant_eq_weight_mul_pairGramMinor (D : WeightedDesign m k)
    {leftLabel rightLabel : Fin m} (hne : leftLabel ≠ rightLabel) :
    (chartGapOfDesign D leftLabel leftLabel + D.weight leftLabel)
        * (chartGapOfDesign D rightLabel rightLabel + D.weight rightLabel)
        - chartGapOfDesign D leftLabel rightLabel ^ 2
      = D.weight leftLabel * D.weight rightLabel * pairGramMinor D leftLabel rightLabel := by
  have hleft : chartGapOfDesign D leftLabel leftLabel + D.weight leftLabel
      = D.weight leftLabel * leverageOf (D.atom leftLabel) := by
    rw [chartGapOfDesign_diagonal]; ring
  have hright : chartGapOfDesign D rightLabel rightLabel + D.weight rightLabel
      = D.weight rightLabel * leverageOf (D.atom rightLabel) := by
    rw [chartGapOfDesign_diagonal]; ring
  have hoff : chartGapOfDesign D leftLabel rightLabel
      = Real.sqrt (D.weight leftLabel) * Real.sqrt (D.weight rightLabel)
        * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) := by
    rw [chartGapOfDesign_apply_of_ne D hne, projectionOfDesign_apply]
  have hsquare : (Real.sqrt (D.weight leftLabel) * Real.sqrt (D.weight rightLabel)) ^ 2
      = D.weight leftLabel * D.weight rightLabel := by
    rw [mul_pow, Real.sq_sqrt (D.weight_pos leftLabel).le,
      Real.sq_sqrt (D.weight_pos rightLabel).le]
  rw [hleft, hright, hoff, pairGramMinor, mul_pow, hsquare]
  ring

/-- **A PARALLEL PAIR IS A VANISHING CHART PAIR DETERMINANT.**  Both directions, at
every size and rank.  The `Gtz.HasParallelPair` predicate allows a zero ratio, and
so does this: a zero atom makes its own row of the chart vanish. -/
theorem hasParallelPair_iff_chartCore (D : WeightedDesign m k) :
    HasParallelPair D ↔ (chartCoreOfDesign D).HasParallelPairCore := by
  constructor
  · rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
    refine ⟨keptLabel, dropLabel, hne, ?_⟩
    have hminor := pairGramMinor_eq_zero_of_smul D hparallel
    have hbridge := chartPairDeterminant_eq_weight_mul_pairGramMinor D hne
    rw [hminor, mul_zero] at hbridge
    show (chartGapOfDesign D keptLabel keptLabel + D.weight keptLabel)
        * (chartGapOfDesign D dropLabel dropLabel + D.weight dropLabel)
      = chartGapOfDesign D keptLabel dropLabel ^ 2
    linarith [hbridge]
  · rintro ⟨leftLabel, rightLabel, hne, hzero⟩
    have hbridge := chartPairDeterminant_eq_weight_mul_pairGramMinor D hne
    have hgap : (chartGapOfDesign D leftLabel leftLabel + D.weight leftLabel)
        * (chartGapOfDesign D rightLabel rightLabel + D.weight rightLabel)
      = chartGapOfDesign D leftLabel rightLabel ^ 2 := hzero
    rw [hgap, sub_self] at hbridge
    have hpos : (0 : ℝ) < D.weight leftLabel * D.weight rightLabel :=
      mul_pos (D.weight_pos leftLabel) (D.weight_pos rightLabel)
    have hminor : pairGramMinor D leftLabel rightLabel = 0 := by
      rcases mul_eq_zero.mp hbridge.symm with hbad | hgood
      · exact absurd hbad (ne_of_gt hpos)
      · exact hgood
    rw [pairGramMinor] at hminor
    rcases (leverageDefect_eq_zero_iff (D.atom leftLabel) (D.atom rightLabel)).mp hminor with
      hzeroAtom | ⟨ratio, hratio⟩
    · exact ⟨rightLabel, leftLabel, 0, Ne.symm hne, by rw [hzeroAtom, zero_smul]⟩
    · exact ⟨leftLabel, rightLabel, ratio, hne, hratio⟩

/-- **A TIE IS A TIE OF THE CORE.**  Both halves are the two block criteria read
along the same order embeddings. -/
theorem isTie_iff_chartCore (D : WeightedDesign m k) :
    IsTie D ↔ (chartCoreOfDesign D).IsTieCore := by
  constructor
  · rintro ⟨⟨selected, hcard, hdominates⟩, hnostrict⟩
    refine ⟨⟨selected, hcard,
      (dominates_iff_posSemidef_chartGapBlock D selected hcard).mp hdominates⟩, ?_⟩
    intro other hother hposDef
    exact hnostrict other hother
      ((posDef_gap_iff_posDef_chartGapBlock D other hother).mpr hposDef)
  · rintro ⟨⟨selected, hcard, hblock⟩, hnostrict⟩
    refine ⟨⟨selected, hcard,
      (dominates_iff_posSemidef_chartGapBlock D selected hcard).mpr hblock⟩, ?_⟩
    intro other hother hposDef
    exact hnostrict other hother
      ((posDef_gap_iff_posDef_chartGapBlock D other hother).mp hposDef)

/-- **THE HINGE IS A STATEMENT ABOUT ONE SYMMETRIC MATRIX.**  At every size and
every rank, `Gtz.HingeHoldsAtSize` holds exactly when every chart core whose gap
blocks are all non-definite but not all indefinite carries two labels `p ≠ q` with

    `(M_pp + t_p)(M_qq + t_q) = M_pq²` .

No design, no atom, no Parseval and no bracket appears on the right. -/
theorem hingeHoldsAtSize_iff_chartCore (m k : ℕ) :
    HingeHoldsAtSize m k
      ↔ ∀ core : ChartCore m k, core.IsTieCore → core.HasParallelPairCore := by
  constructor
  · intro hhinge core htie
    obtain ⟨D, hweight, hgap⟩ := exists_design_of_chartCore core
    have htieD : IsTie D := by
      refine (isTie_iff_chartCore D).mpr ?_
      obtain ⟨⟨selected, hcard, hblock⟩, hnostrict⟩ := htie
      refine ⟨⟨selected, hcard, ?_⟩, ?_⟩
      · show ((chartGapOfDesign D).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)).PosSemidef
        rw [hgap]; exact hblock
      · intro other hother hposDef
        refine hnostrict other hother ?_
        rw [← hgap]
        exact hposDef
    obtain ⟨leftLabel, rightLabel, hne, hparallel⟩ :=
      (hasParallelPair_iff_chartCore D).mp (hhinge D htieD)
    refine ⟨leftLabel, rightLabel, hne, ?_⟩
    simp only [chartCoreOfDesign_gap, chartCoreOfDesign_weight] at hparallel
    rw [← hgap, ← hweight]
    exact hparallel
  · intro hcore D htie
    exact (hasParallelPair_iff_chartCore D).mpr (hcore (chartCoreOfDesign D)
      ((isTie_iff_chartCore D).mp htie))

/-- The `(6,3)` reading of the hinge, design-free. -/
theorem hingeHoldsAtSize_six_three_iff_chartCore :
    HingeHoldsAtSize 6 3
      ↔ ∀ core : ChartCore 6 3, core.IsTieCore → core.HasParallelPairCore :=
  hingeHoldsAtSize_iff_chartCore 6 3

/-! ## Part 7 — the complementary pair reading

The same `2 × 2` block of the gap, shifted by `T − 1` instead of by `T`.  At
`(6,3)` its vanishing is coplanarity of the complementary four atoms, so both
halves of the hinge dictionary live in ONE block of `M`. -/

/-- **THE COMPLEMENTARY PAIR DETERMINANT IS THE PAIRING-CAP SLACK.**  Shifting the
pair block of the gap by `T − 1` rather than by `T` produces the campaign's
`Gtz.pairCapSlack`, whose four-square expansion is
`Gtz.pairCapSlack_eq_sum_complement_volumes'`. -/
theorem chartCoPairDeterminant_eq_pairCapSlack (D : WeightedDesign m k)
    {leftLabel rightLabel : Fin m} (hne : leftLabel ≠ rightLabel) :
    (1 - D.weight leftLabel - chartGapOfDesign D leftLabel leftLabel)
        * (1 - D.weight rightLabel - chartGapOfDesign D rightLabel rightLabel)
        - chartGapOfDesign D leftLabel rightLabel ^ 2
      = pairCapSlack D leftLabel rightLabel := by
  have hleft : 1 - D.weight leftLabel - chartGapOfDesign D leftLabel leftLabel
      = 1 - D.weight leftLabel * leverageOf (D.atom leftLabel) := by
    rw [chartGapOfDesign_diagonal]; ring
  have hright : 1 - D.weight rightLabel - chartGapOfDesign D rightLabel rightLabel
      = 1 - D.weight rightLabel * leverageOf (D.atom rightLabel) := by
    rw [chartGapOfDesign_diagonal]; ring
  have hoff : chartGapOfDesign D leftLabel rightLabel
      = Real.sqrt (D.weight leftLabel) * Real.sqrt (D.weight rightLabel)
        * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) := by
    rw [chartGapOfDesign_apply_of_ne D hne, projectionOfDesign_apply]
  have hsquare : (Real.sqrt (D.weight leftLabel) * Real.sqrt (D.weight rightLabel)) ^ 2
      = D.weight leftLabel * D.weight rightLabel := by
    rw [mul_pow, Real.sq_sqrt (D.weight_pos leftLabel).le,
      Real.sq_sqrt (D.weight_pos rightLabel).le]
  rw [hleft, hright, hoff, pairCapSlack, mul_pow, hsquare]

/-- **THE TWO SHIFTS MULTIPLY TO THE PAIR MASS.**  The two diagonal shifts of the
same pair block are `t_c` and `t_c − 1`, whose product is `−t_c(1 − t_c)`.  That
entry is the square of the diagonal `Gtz.pairRootDiagonal` of the duality module,
so the two halves of the dictionary are separated by exactly the pair mass and by
nothing else. -/
theorem weight_mul_one_sub_weight_eq (D : WeightedDesign m k) (atomIndex : Fin m) :
    D.weight atomIndex * (D.weight atomIndex - 1)
      = -(D.weight atomIndex * (1 - D.weight atomIndex)) := by
  ring

/-- **BOTH HALVES OF THE `(6,3)` DICTIONARY, IN THE GAP.**  A pair of a `(6,3)`
design is parallel exactly when its gap block shifted by `T` is singular, and the
complementary four atoms are coplanar exactly when the SAME block shifted by
`T − 1` is singular. -/
theorem sixThree_pair_dictionary_in_chartGap (D : WeightedDesign 6 3)
    {leftLabel rightLabel firstOther secondOther thirdOther fourthOther : Fin 6}
    (hpq : leftLabel ≠ rightLabel) (hpx : leftLabel ≠ firstOther)
    (hpy : leftLabel ≠ secondOther) (hpz : leftLabel ≠ thirdOther)
    (hpw : leftLabel ≠ fourthOther) (hqx : rightLabel ≠ firstOther)
    (hqy : rightLabel ≠ secondOther) (hqz : rightLabel ≠ thirdOther)
    (hqw : rightLabel ≠ fourthOther) (hxy : firstOther ≠ secondOther)
    (hxz : firstOther ≠ thirdOther) (hxw : firstOther ≠ fourthOther)
    (hyz : secondOther ≠ thirdOther) (hyw : secondOther ≠ fourthOther)
    (hzw : thirdOther ≠ fourthOther) :
    ((chartGapOfDesign D leftLabel leftLabel + D.weight leftLabel)
          * (chartGapOfDesign D rightLabel rightLabel + D.weight rightLabel)
        = chartGapOfDesign D leftLabel rightLabel ^ 2
      ↔ pairGramMinor D leftLabel rightLabel = 0)
    ∧ ((1 - D.weight leftLabel - chartGapOfDesign D leftLabel leftLabel)
          * (1 - D.weight rightLabel - chartGapOfDesign D rightLabel rightLabel)
        = chartGapOfDesign D leftLabel rightLabel ^ 2
      ↔ FourCoplanar D firstOther secondOther thirdOther fourthOther) := by
  have hbridge := chartPairDeterminant_eq_weight_mul_pairGramMinor D hpq
  have hpos : (0 : ℝ) < D.weight leftLabel * D.weight rightLabel :=
    mul_pos (D.weight_pos leftLabel) (D.weight_pos rightLabel)
  have hcobridge := chartCoPairDeterminant_eq_pairCapSlack D hpq
  refine ⟨?_, ?_⟩
  · constructor
    · intro hzero
      rw [hzero, sub_self] at hbridge
      rcases mul_eq_zero.mp hbridge.symm with hbad | hgood
      · exact absurd hbad (ne_of_gt hpos)
      · exact hgood
    · intro hminor
      rw [hminor, mul_zero] at hbridge
      linarith [hbridge]
  · have hiff := pairCapSlack_eq_zero_iff_fourCoplanar' D hpq hpx hpy hpz hpw hqx hqy hqz hqw
      hxy hxz hxw hyz hyw hzw
    constructor
    · intro hzero
      refine hiff.mp ?_
      rw [← hcobridge, hzero, sub_self]
    · intro hcoplanar
      have hslack := hiff.mpr hcoplanar
      rw [← hcobridge] at hslack
      linarith [hslack]

end Gtz

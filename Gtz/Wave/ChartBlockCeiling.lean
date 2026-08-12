import Gtz.Reduction.ChartAttainment

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The chart block ceiling — every block value sits below the objective

The chart objective is the MAXIMUM of the block values over all subsets of
the right cardinality.  Thus every block value sits below the objective,
at every chart point, with no minimality input: the bound is the
supremum's defining property.  At a crux the objective is negative, and
the ceiling becomes a strong global constraint on the gap: no compressed
block has a least eigenvalue above the chart value.

The both-parallel probe of 2026-08-12 found a first-order witness whose
gap carries compressed blocks with least eigenvalues ABOVE the value.
The ceiling excludes that witness.  The ceiling is the missing export of
the rank-four rung.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.chartBlockValue_le_chartObjective` — **THE CEILING.**
* `Gtz.lambdaMinMat_gap_submatrix_le_chartObjective` — the eigenvalue
  form.

## Vacuity

The statements are unconditional: they hold at every chart point.
-/

namespace Gtz

variable {size rank : ℕ}

/-- **THE CEILING.**  Every block value sits below the chart objective:
the objective is the supremum of the block values. -/
theorem chartBlockValue_le_chartObjective [Nonempty (Fin rank)]
    (point : ChartPoint size rank) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) :
    chartBlockValue rank ((point.chart, point.weight) :
        (Fin size → Fin size → ℝ) × (Fin size → ℝ)) selected
      ≤ chartObjective point := by
  rw [chartObjective, chartObjectiveRaw]
  exact Finset.le_sup' _ ((mem_chartCandidates_iff size rank selected).mpr hcard)

/-- The eigenvalue form of the ceiling: the least eigenvalue of every
compressed gap block sits below the chart objective. -/
theorem lambdaMinMat_gap_submatrix_le_chartObjective [Nonempty (Fin rank)]
    (point : ChartPoint size rank) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) :
    lambdaMinMat ((chartGapRaw ((point.chart, point.weight) :
          (Fin size → Fin size → ℝ) × (Fin size → ℝ))).submatrix
        (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard))
      ≤ chartObjective point := by
  have hceiling := chartBlockValue_le_chartObjective point hcard
  rw [chartBlockValue, dif_pos hcard] at hceiling
  exact hceiling

end Gtz

import Gtz.Wave.ChartBlockCeiling
import Gtz.Quantitative.HollowInvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The ceiling margin kill — a dominated block kills the chart point

The ceiling caps every compressed gap block at the chart objective.  Thus
no block's quadratic form can dominate a margin above the objective: the
Rayleigh characterization turns the quadratic domination into the bound
`margin <= lambdaMin`, against the ceiling.  The margin form avoids the
eigenvalue attainment: a branch kill supplies an explicit margin, and the
positive semidefinite shift does the rest.

This is the consumer of the ceiling.  A branch kill produces a card-`rank`
subset whose compressed gap dominates `margin * |v|^2` with
`chartObjective < margin`, and the crux dies.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.chartGapRaw_transpose_eq` — the gap is symmetric when the chart is.
* `Gtz.gap_submatrix_transpose_eq` — and so is every compression.
* `Gtz.false_of_gap_submatrix_margin` — **THE MARGIN KILL.**

## Vacuity

The statements hold at every chart point with a symmetric chart.  The
kill's hypotheses are contradictory at every such point, and a branch
proof discharges them from its structure.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-- The raw gap is symmetric when the chart is. -/
theorem chartGapRaw_transpose_eq
    {config : (Fin size → Fin size → ℝ) × (Fin size → ℝ)}
    (hsymm : ∀ rowIndex colIndex, config.1 rowIndex colIndex = config.1 colIndex rowIndex) :
    (chartGapRaw config)ᵀ = chartGapRaw config := by
  ext rowIndex colIndex
  simp only [chartGapRaw, Matrix.transpose_apply, Matrix.sub_apply, Matrix.of_apply,
    Matrix.diagonal_apply]
  rw [hsymm colIndex rowIndex]
  by_cases heq : rowIndex = colIndex
  · rw [heq]
  · rw [if_neg heq, if_neg fun hcontra => heq hcontra.symm]

/-- Every compression of a symmetric gap is symmetric. -/
theorem gap_submatrix_transpose_eq
    (point : ChartPoint size rank)
    (hchartSymm : ∀ rowIndex colIndex,
      point.chart rowIndex colIndex = point.chart colIndex rowIndex)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) :
    ((chartGapRaw ((point.chart, point.weight) :
          (Fin size → Fin size → ℝ) × (Fin size → ℝ))).submatrix
        (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard))ᵀ
      = (chartGapRaw ((point.chart, point.weight) :
          (Fin size → Fin size → ℝ) × (Fin size → ℝ))).submatrix
        (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) := by
  rw [Matrix.transpose_submatrix, chartGapRaw_transpose_eq hchartSymm]

/-- **THE MARGIN KILL.**  No compressed gap block dominates a margin above
the chart objective: the domination lifts the least eigenvalue above the
ceiling. -/
theorem false_of_gap_submatrix_margin [Nonempty (Fin rank)]
    (point : ChartPoint size rank)
    (hchartSymm : ∀ rowIndex colIndex,
      point.chart rowIndex colIndex = point.chart colIndex rowIndex)
    {selected : Finset (Fin size)} (hcard : selected.card = rank)
    {margin : ℝ} (hgt : chartObjective point < margin)
    (hquad : ∀ probe : Fin rank → ℝ,
      margin * (probe ⬝ᵥ probe)
        ≤ probe ⬝ᵥ ((chartGapRaw ((point.chart, point.weight) :
              (Fin size → Fin size → ℝ) × (Fin size → ℝ))).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ probe)) :
    False := by
  have hsymmA := gap_submatrix_transpose_eq point hchartSymm hcard
  have hceiling := lambdaMinMat_gap_submatrix_le_chartObjective point hcard
  set A : Matrix (Fin rank) (Fin rank) ℝ :=
    (chartGapRaw ((point.chart, point.weight) :
        (Fin size → Fin size → ℝ) × (Fin size → ℝ))).submatrix
      (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) with hAdef
  have hpsd : (A - margin • (1 : Matrix (Fin rank) (Fin rank) ℝ)).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
        Matrix.transpose_smul, Matrix.transpose_one, hsymmA]
    · intro probe
      have hstar : star probe = probe := by
        ext coordIndex
        simp
      rw [hstar, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_smul]
      simp only [smul_eq_mul]
      linarith [hquad probe]
  have hlift := (le_lambdaMinMat_iff_posSemidef_sub_smul_one A hsymmA margin).mpr hpsd
  linarith

end Gtz

/-
# The chart inverse-trace law

`Gtz.pivot_sum_eq_rank_add_trace_inv` reads the design-level gap `S_Q - 1` and
prices a stalled base set by `trace ((S_Q - 1)⁻¹)`.  A chart gap subtracts the
MASS matrix rather than the identity,

  `directionChartGap = ∑_{c ∈ S} (m c / w c) • A c  -  ∑_c m c • A c`

so the design-level law does not transport verbatim: the selected part is the
gap plus the mass matrix, not the gap plus one.  Carrying the mass matrix
through gives the chart form

  `∑_{c ∈ S} chartLadderPivot c = 3 + trace (gap⁻¹ * massMatrix)`

and a stalled selection of `j` labels above the rank prices `trace (gap⁻¹ *
massMatrix)` by `j`.  Division-free through the adjugate, the price reads

  `(card S - 3) * det gap  ≤  trace (adjugate gap * massMatrix)`

At the trivial chart, where the mass equals the weight and the mass matrix is
Parseval's identity, this collapses to the design-level law.  Everywhere else
the mass matrix is the correction the design form is missing, and it is the
reason the design-level criterion cannot be compared against a chart residual
without it.
-/
import Mathlib
import Gtz.Design.StallLocus
import Gtz.Design.KFourDescentLadder

namespace Gtz

open Matrix

variable {size : ℕ}

-- AUDIT-DUPLICATE (2026-08-17): ONE matrix carries FOUR names in this repo.
-- Byte-identical bodies: `Gtz.chartMassMoment`
-- (Gtz/Wave/ThreeLinesSlideElimination.lean), and once the direction is fixed
-- to `kFourDirection`, `Gtz.kFourLaplacian` (Gtz/Wave/KirchhoffSignTower.lean)
-- and `Gtz.kFourMassMoment` (Gtz/Wave/KFourTreeLaplacian.lean).
-- Exactly ONE bridge exists, `Gtz.chartMassMatrix_kFour_eq_kFourLaplacian`,
-- proved by `rfl`.  The two missing bridges are also `rfl`.
-- COST: the leverage toolkit of ThreeLinesSlideElimination.lean (the veto
-- `Gtz.weight_lt_chartMassLeverage_of_posDef_gap`, the counting law
-- `Gtz.three_le_card_overLevered`, the criterion
-- `Gtz.posDef_directionChartGap_of_dualStrict`) cannot reach any lane that
-- speaks `chartMassMatrix`, although
-- `Gtz.posDef_chartMassMatrix_kFour`
-- (Gtz/Wave/TriangleStallClosureDeflation.lean) already supplies its
-- positive-definiteness hypothesis unconditionally at every K4 chart point.
/-- The total mass matrix of a chart point: the term the chart gap subtracts. -/
noncomputable def chartMassMatrix (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ label, mass label • atomMatrix (direction label)

/-- The selected part of a chart gap is the gap plus the mass matrix. -/
theorem selectedPart_eq_gap_add_massMatrix (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) :
    ∑ label ∈ selected, (mass label / weight label) • atomMatrix (direction label)
      = directionChartGap direction mass weight selected
        + chartMassMatrix direction mass := by
  rw [directionChartGap, chartMassMatrix]
  abel

/-- A scaled atom traced against any matrix is that matrix's quadratic form at
the direction, scaled. -/
theorem trace_mul_smul_atomMatrix (N : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ)
    (v : Fin 3 → ℝ) :
    Matrix.trace (N * (s • atomMatrix v)) = s * (v ⬝ᵥ (N *ᵥ v)) := by
  rw [atomMatrix, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, smul_eq_mul, dotProduct_comm]

/-- **The chart inverse-trace law.**  The chart pivot sum over a selection is
the rank plus the trace of the inverse gap against the mass matrix.  The mass
matrix is what the design-level law replaces by the identity. -/
theorem chartPivot_sum_eq_rank_add_trace_inv_mul_mass
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size))
    (hgap : (directionChartGap direction mass weight selected).PosDef) :
    ∑ label ∈ selected, chartLadderPivot direction mass weight selected label
      = 3 + Matrix.trace ((directionChartGap direction mass weight selected)⁻¹
          * chartMassMatrix direction mass) := by
  set G := directionChartGap direction mass weight selected with hG
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.mpr (ne_of_gt hgap.det_pos)
  have hsum : ∑ label ∈ selected, chartLadderPivot direction mass weight selected label
      = Matrix.trace (G⁻¹
          * ∑ label ∈ selected, (mass label / weight label) • atomMatrix (direction label)) := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun label _ => by
      rw [chartLadderPivot, trace_mul_smul_atomMatrix]
  rw [hsum, selectedPart_eq_gap_add_massMatrix, ← hG, Matrix.mul_add, Matrix.trace_add,
    Matrix.nonsing_inv_mul _ hdet, Matrix.trace_one, Fintype.card_fin]
  norm_num

/-- **The chart stall price.**  A selection every label of which carries chart
pivot at least one prices the inverse gap against the mass matrix by its excess
cardinality. -/
theorem card_sub_rank_le_trace_inv_mul_mass_of_chart_stall
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size))
    (hgap : (directionChartGap direction mass weight selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot direction mass weight selected label) :
    ((selected.card : ℝ) - 3)
      ≤ Matrix.trace ((directionChartGap direction mass weight selected)⁻¹
          * chartMassMatrix direction mass) := by
  have hlaw := chartPivot_sum_eq_rank_add_trace_inv_mul_mass direction mass weight
    selected hgap
  have hge : (selected.card : ℝ)
      ≤ ∑ label ∈ selected, chartLadderPivot direction mass weight selected label := by
    calc (selected.card : ℝ) = ∑ _l ∈ selected, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum hstall
  linarith

/-- The inverse gap against the mass matrix, read through the adjugate.  This
clears the division from the chart price. -/
theorem trace_inv_mul_lt_iff_trace_adjugate_mul_lt (G N : Matrix (Fin 3) (Fin 3) ℝ)
    (hdet : 0 < G.det) (c : ℝ) :
    Matrix.trace (G⁻¹ * N) < c ↔ Matrix.trace (G.adjugate * N) < c * G.det := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul, inv_mul_eq_div, div_lt_iff₀ hdet]

/-- **The chart escape, division-free.**  One polynomial inequality between the
adjugate of the gap read against the mass matrix and the determinant, scaled by
the excess cardinality, forces some label's chart pivot below one. -/
theorem exists_chartPivot_lt_one_of_trace_adjugate_mul_mass_lt
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size))
    (hgap : (directionChartGap direction mass weight selected).PosDef)
    (hadj : Matrix.trace ((directionChartGap direction mass weight selected).adjugate
        * chartMassMatrix direction mass)
      < ((selected.card : ℝ) - 3)
        * (directionChartGap direction mass weight selected).det) :
    ∃ label ∈ selected,
      chartLadderPivot direction mass weight selected label < 1 := by
  by_contra hno
  push Not at hno
  have hprice := card_sub_rank_le_trace_inv_mul_mass_of_chart_stall direction mass weight
    selected hgap hno
  have hlt := (trace_inv_mul_lt_iff_trace_adjugate_mul_lt _ _ hgap.det_pos _).mpr hadj
  linarith

/-- **The chart stall is pinned, division-free.**  Every stalled selection
satisfies the negation of the chart criterion, so that criterion can never fire
at a stall.  The chart transport of `Gtz.not_adjugateTrace_lt_of_stall`. -/
theorem not_trace_adjugate_mul_mass_lt_of_chart_stall
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size))
    (hgap : (directionChartGap direction mass weight selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot direction mass weight selected label) :
    ¬ (Matrix.trace ((directionChartGap direction mass weight selected).adjugate
        * chartMassMatrix direction mass)
      < ((selected.card : ℝ) - 3)
        * (directionChartGap direction mass weight selected).det) := by
  intro hadj
  obtain ⟨label, hmem, hlt⟩ :=
    exists_chartPivot_lt_one_of_trace_adjugate_mul_mass_lt direction mass weight
      selected hgap hadj
  exact absurd (hstall label hmem) (not_le.mpr hlt)

end Gtz

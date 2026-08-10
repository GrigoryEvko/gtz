import Gtz.Quantitative.RungThreeAggregate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-!
# The quadratic equation of the projection gap

For a weighted design put `Q = P - T`, where `P` is its projection chart and
`T = diag(weight)`.  Idempotence `P² = P` is equivalent to the Riccati equation

    Q² = Q + T - Q T - T Q - T².

The existing chart development records the first three power traces of `Q`.
The untraced equation is stronger: after pivoting a live pair, it controls the
whole covariance of the four completion columns rather than only their sum.
-/

/-- The untraced quadratic equation satisfied by every design's chart gap. -/
theorem chartGapMatrix_mul_self (design : WeightedDesign size rank) :
    chartGapMatrix design * chartGapMatrix design
      = chartGapMatrix design + Matrix.diagonal design.weight
          - chartGapMatrix design * Matrix.diagonal design.weight
          - Matrix.diagonal design.weight * chartGapMatrix design
          - Matrix.diagonal design.weight * Matrix.diagonal design.weight := by
  have hidem := projectionOfDesign_mul_self design
  simp only [chartGapMatrix]
  noncomm_ring
  rw [hidem]
  abel

/-- Off the diagonal, the quadratic equation is a weighted eigenvector law. -/
theorem sum_chartGapMatrix_mul_offDiagonal (design : WeightedDesign size rank)
    {rowIndex colIndex : Fin size} (hne : rowIndex ≠ colIndex) :
    ∑ middleIndex : Fin size,
        chartGapMatrix design rowIndex middleIndex
          * chartGapMatrix design middleIndex colIndex
      = (1 - design.weight rowIndex - design.weight colIndex)
          * chartGapMatrix design rowIndex colIndex := by
  have hentry := congrFun
    (congrFun (chartGapMatrix_mul_self design) rowIndex) colIndex
  simp only [Matrix.add_apply, Matrix.sub_apply] at hentry
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.diagonal_mul_diagonal] at hentry
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, if_neg hne] at hentry
  linarith

/-- On the diagonal, the squared row norm is pinned by the weight and the gap
diagonal. -/
theorem sum_sq_chartGapMatrix_row (design : WeightedDesign size rank)
    (rowIndex : Fin size) :
    ∑ colIndex : Fin size, chartGapMatrix design rowIndex colIndex ^ 2
      = (1 - 2 * design.weight rowIndex)
          * chartGapMatrix design rowIndex rowIndex
        + design.weight rowIndex * (1 - design.weight rowIndex) := by
  have hentry := congrFun
    (congrFun (chartGapMatrix_mul_self design) rowIndex) rowIndex
  have hsymm : (chartGapMatrix design)ᵀ = chartGapMatrix design := by
    rw [chartGapMatrix, Matrix.transpose_sub, projectionOfDesign_transpose,
      Matrix.diagonal_transpose]
  have hcomm : ∀ colIndex : Fin size,
      chartGapMatrix design colIndex rowIndex
        = chartGapMatrix design rowIndex colIndex := by
    intro colIndex
    have := congrFun (congrFun hsymm rowIndex) colIndex
    simpa only [Matrix.transpose_apply] using this
  simp only [Matrix.add_apply, Matrix.sub_apply] at hentry
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.diagonal_mul_diagonal] at hentry
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, if_pos, hcomm] at hentry
  simp only [pow_two]
  linarith

/-- The chart gap is symmetric. -/
theorem chartGapMatrix_transpose (design : WeightedDesign size rank) :
    (chartGapMatrix design)ᵀ = chartGapMatrix design := by
  rw [chartGapMatrix, Matrix.transpose_sub, projectionOfDesign_transpose,
    Matrix.diagonal_transpose]

/-! ## The covariance outside a fixed pair -/

/-- The squared chart coupling from `rowIndex` to every label outside a fixed
pair.  This is one diagonal entry of the pair's outside-column covariance. -/
noncomputable def chartOutsideVariance (design : WeightedDesign size rank)
    (rowIndex omittedIndex : Fin size) : ℝ :=
  ∑ colIndex ∈ ((Finset.univ : Finset (Fin size)).erase rowIndex).erase omittedIndex,
    chartGapMatrix design rowIndex colIndex ^ 2

/-- The mixed chart coupling to every label outside a fixed pair. -/
noncomputable def chartOutsideCovariance (design : WeightedDesign size rank)
    (first second : Fin size) : ℝ :=
  ∑ colIndex ∈ ((Finset.univ : Finset (Fin size)).erase first).erase second,
    chartGapMatrix design first colIndex * chartGapMatrix design colIndex second

/-- The first diagonal of the outside covariance, with the two insider columns
peeled from the projection quadratic equation. -/
theorem chartOutsideVariance_eq (design : WeightedDesign size rank)
    {first second : Fin size} (hdistinct : first ≠ second) :
    chartOutsideVariance design first second
      = (1 - 2 * design.weight first) * chartGapMatrix design first first
          + design.weight first * (1 - design.weight first)
          - chartGapMatrix design first first ^ 2
          - chartGapMatrix design first second ^ 2 := by
  let summand := fun colIndex : Fin size => chartGapMatrix design first colIndex ^ 2
  have hfirst : first ∈ (Finset.univ : Finset (Fin size)) := Finset.mem_univ first
  have hsecond : second ∈ (Finset.univ.erase first : Finset (Fin size)) :=
    Finset.mem_erase.mpr ⟨hdistinct.symm, Finset.mem_univ second⟩
  have hpeelFirst := Finset.add_sum_erase (Finset.univ : Finset (Fin size)) summand hfirst
  have hpeelSecond := Finset.add_sum_erase
    (Finset.univ.erase first : Finset (Fin size)) summand hsecond
  have hrow := sum_sq_chartGapMatrix_row design first
  simp only [chartOutsideVariance] at hpeelFirst hpeelSecond ⊢
  rw [← hpeelFirst, ← hpeelSecond] at hrow
  dsimp only [summand] at hrow
  linarith

/-- The off-diagonal of the outside covariance. -/
theorem chartOutsideCovariance_eq (design : WeightedDesign size rank)
    {first second : Fin size} (hdistinct : first ≠ second) :
    chartOutsideCovariance design first second
      = (1 - design.weight first - design.weight second
          - chartGapMatrix design first first - chartGapMatrix design second second)
          * chartGapMatrix design first second := by
  let summand := fun colIndex : Fin size =>
    chartGapMatrix design first colIndex * chartGapMatrix design colIndex second
  have hfirst : first ∈ (Finset.univ : Finset (Fin size)) := Finset.mem_univ first
  have hsecond : second ∈ (Finset.univ.erase first : Finset (Fin size)) :=
    Finset.mem_erase.mpr ⟨hdistinct.symm, Finset.mem_univ second⟩
  have hpeelFirst := Finset.add_sum_erase (Finset.univ : Finset (Fin size)) summand hfirst
  have hpeelSecond := Finset.add_sum_erase
    (Finset.univ.erase first : Finset (Fin size)) summand hsecond
  have hrow := sum_chartGapMatrix_mul_offDiagonal design hdistinct
  simp only [chartOutsideCovariance] at hpeelFirst hpeelSecond ⊢
  rw [← hpeelFirst, ← hpeelSecond] at hrow
  dsimp only [summand] at hrow
  nlinarith

/-- The determinant of the full two-dimensional outside covariance is pinned
by the pair block and the two weights.  Unlike its trace contraction, this
retains the spread of the four completion columns. -/
theorem chartOutsideCovariance_det_eq (design : WeightedDesign size rank)
    {first second : Fin size} (hdistinct : first ≠ second) :
    chartOutsideVariance design first second
          * chartOutsideVariance design second first
        - chartOutsideCovariance design first second ^ 2
      = ((1 - 2 * design.weight first) * chartGapMatrix design first first
            + design.weight first * (1 - design.weight first)
            - chartGapMatrix design first first ^ 2
            - chartGapMatrix design first second ^ 2)
          * ((1 - 2 * design.weight second) * chartGapMatrix design second second
            + design.weight second * (1 - design.weight second)
            - chartGapMatrix design second second ^ 2
            - chartGapMatrix design first second ^ 2)
        - ((1 - design.weight first - design.weight second
            - chartGapMatrix design first first - chartGapMatrix design second second)
            * chartGapMatrix design first second) ^ 2 := by
  have hsymm : chartGapMatrix design second first = chartGapMatrix design first second := by
    have hentry := congrFun (congrFun (chartGapMatrix_transpose design) first) second
    simpa only [Matrix.transpose_apply] using hentry
  rw [chartOutsideVariance_eq design hdistinct,
    chartOutsideVariance_eq design hdistinct.symm,
    chartOutsideCovariance_eq design hdistinct, hsymm]

end Gtz

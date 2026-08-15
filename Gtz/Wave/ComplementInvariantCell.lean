import Gtz.Wave.ComplementTripleCriterion
import Gtz.Design.SharpSpreadCell
import Gtz.Design.ComplementDiagonalDominance
import Gtz.Design.PivotThirdDominance

/-!
# The invariant expansion of the complement determinant, and the pair-data cell

The complement matrix of an omitted triple is `M = D - D V D` on the three
omitted labels, with `D` the diagonal of boosts and `V` the inverse form of the
full gap.  Writing `M = D^(1/2) (1 - G) D^(1/2)` identifies the Gram matrix `G`
whose diagonal is the pivot and whose off-diagonal squares are the boosted
crosses.  The corpus reads `G` through two invariants only: the pivot trace `T`
and the Frobenius spread `F`.  Those two determine the first two elementary
symmetric functions of `G`.  They do not determine the third.

This file supplies the third.  The determinant of `G` carries exactly one term
that no pair of labels can read, the TRIPLE CROSS

  `W = (m i / w i) (m j / w j) (m k / w k) V(i,j) V(i,k) V(j,k)`,

and the central identity of this file is that its square is already pair data:

  `W ^ 2 = q(i,j) * q(i,k) * q(j,k)`      (`sq_tripleBoostedCross`)

where `q` is `pairBoostedCrossSq`.  So the pair data pins the MAGNITUDE of the
triple cross and leaves only its SIGN unread.  The determinant of the complement
splits accordingly,

  `det = (boosts) * (pairDetBudget - 2 * W)`,

with `pairDetBudget` a polynomial in the pivots and the boosted crosses alone.
Two cells follow, and both are division-free and root-free.

* `posDef_directionChartGap_compl_triple_of_pairBudget` asks the budget to
  exceed twice the triple cross in the worst sign, which by the pinning identity
  is the root-free pair of inequalities `0 < A` and `4 * Q < A ^ 2`.  This is the
  sharpest cell available to a reader of pair data: the constant four cannot be
  lowered (`pairBudget_constant_sharp`).
* `posDef_directionChartGap_compl_triple_of_hadamardBudget` asks the strictly
  cheaper `pivotCrossSum < pairDetBudget`, which reads no triple product at all.
  It rests on `two_tripleBoostedCross_le_pivotCrossSum`, the explicit Hadamard
  inequality `det G <= (product of pivots)` written in pivot coordinates.

Neither statement, and no proof here, mentions an eigenvalue, a matrix square
root or a spectral radius.  The single square root that the geometry suggests is
removed once and for all by the pinning identity.
-/

namespace Gtz

variable {size : ℕ}

/-! ## 1. The triple cross and its pinning identity -/

/-- **THE TRIPLE CROSS.**  The one term of the omitted Gram determinant that no
pair of labels reads: the three boosts against the product of the three
off-diagonal inverse-form readings. -/
noncomputable def tripleBoostedCross (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) : ℝ :=
  (mass i / weight i) * (mass j / weight j) * (mass k / weight k)
    * fullInverseForm direction mass weight i j
    * fullInverseForm direction mass weight i k
    * fullInverseForm direction mass weight j k

/-- **THE PINNING IDENTITY.**  The square of the triple cross is the product of
the three boosted crosses.  The pair data therefore fixes the magnitude of the
triple cross exactly and leaves only its sign unread.  This is what removes
every square root from the cells below. -/
theorem sq_tripleBoostedCross (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) :
    tripleBoostedCross direction mass weight i j k ^ 2
      = pairBoostedCrossSq direction mass weight i j
        * pairBoostedCrossSq direction mass weight i k
        * pairBoostedCrossSq direction mass weight j k := by
  simp only [tripleBoostedCross, pairBoostedCrossSq]
  ring

/-- The product of the three boosted crosses is nonnegative, being a square. -/
theorem prod_pairBoostedCrossSq_nonneg (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) :
    0 ≤ pairBoostedCrossSq direction mass weight i j
      * pairBoostedCrossSq direction mass weight i k
      * pairBoostedCrossSq direction mass weight j k := by
  rw [← sq_tripleBoostedCross]
  exact sq_nonneg _

/-- The triple cross is symmetric in its first two labels. -/
theorem tripleBoostedCross_swap_first (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size) :
    tripleBoostedCross direction mass weight i j k
      = tripleBoostedCross direction mass weight j i k := by
  simp only [tripleBoostedCross]
  rw [fullInverseForm_comm direction mass weight huniv i j]
  ring

/-! ## 2. The pair Cauchy-Schwarz in pivot coordinates -/

/-- **The boosted cross never exceeds the product of the two pivots.**  This is
the resolvent Cauchy-Schwarz multiplied by the two boosts, and it is the two by
two positive-semidefiniteness of the omitted Gram written without a matrix. -/
theorem pairBoostedCrossSq_le_pivot_mul (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (a b : Fin size) (hboostA : 0 ≤ mass a / weight a) (hboostB : 0 ≤ mass b / weight b) :
    pairBoostedCrossSq direction mass weight a b
      ≤ fullPivot direction mass weight a * fullPivot direction mass weight b := by
  have hcs := sq_fullInverseForm_le_mul direction mass weight huniv a b
  simp only [pairBoostedCrossSq, fullPivot]
  nlinarith [mul_nonneg hboostA hboostB, hcs]

/-- The boosted cross is nonnegative. -/
theorem pairBoostedCrossSq_nonneg' (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a b : Fin size)
    (hboostA : 0 ≤ mass a / weight a) (hboostB : 0 ≤ mass b / weight b) :
    0 ≤ pairBoostedCrossSq direction mass weight a b := by
  simp only [pairBoostedCrossSq]
  have := mul_nonneg hboostA hboostB
  nlinarith [sq_nonneg (fullInverseForm direction mass weight a b)]

/-! ## 3. The budget: the part of the determinant that pair data reads -/

/-- The product of the three pivots of an omitted triple. -/
noncomputable def pivotTripleProduct (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) : ℝ :=
  fullPivot direction mass weight i * fullPivot direction mass weight j
    * fullPivot direction mass weight k

/-- Each pivot against the boosted cross of the other two. -/
noncomputable def pivotCrossSum (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) : ℝ :=
  fullPivot direction mass weight i * pairBoostedCrossSq direction mass weight j k
    + fullPivot direction mass weight j * pairBoostedCrossSq direction mass weight i k
    + fullPivot direction mass weight k * pairBoostedCrossSq direction mass weight i j

/-- **THE PAIR BUDGET.**  Everything in the complement determinant that the
pivots and the boosted crosses determine.  The determinant is this budget less
twice the triple cross, and nothing else. -/
noncomputable def pairDetBudget (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) : ℝ :=
  (1 - fullPivot direction mass weight i) * (1 - fullPivot direction mass weight j)
      * (1 - fullPivot direction mass weight k)
    - (1 - fullPivot direction mass weight i) * pairBoostedCrossSq direction mass weight j k
    - (1 - fullPivot direction mass weight j) * pairBoostedCrossSq direction mass weight i k
    - (1 - fullPivot direction mass weight k) * pairBoostedCrossSq direction mass weight i j

/-- **The budget in the two landed invariants.**  The pair budget is the trace
and the spread and the two remaining pivot polynomials.  The middle term is the
second elementary symmetric function of the omitted Gram, which is exactly
`(T ^ 2 - F) / 2`. -/
theorem pairDetBudget_eq_invariants (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) :
    pairDetBudget direction mass weight i j k
      = 1 - pivotTrace direction mass weight i j k
        + (pivotTrace direction mass weight i j k ^ 2
            - frobeniusSpread direction mass weight i j k) / 2
        - pivotTripleProduct direction mass weight i j k
        + pivotCrossSum direction mass weight i j k := by
  simp only [pairDetBudget, pivotTrace, frobeniusSpread, pivotTripleProduct, pivotCrossSum]
  ring

/-- **The second elementary symmetric function of the omitted Gram.**  It reads
the trace and the spread only, and it is the sum of the three two by two
principal minors. -/
theorem sq_pivotTrace_sub_frobeniusSpread (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) :
    (pivotTrace direction mass weight i j k ^ 2
        - frobeniusSpread direction mass weight i j k) / 2
      = (fullPivot direction mass weight i * fullPivot direction mass weight j
          - pairBoostedCrossSq direction mass weight i j)
        + (fullPivot direction mass weight i * fullPivot direction mass weight k
          - pairBoostedCrossSq direction mass weight i k)
        + (fullPivot direction mass weight j * fullPivot direction mass weight k
          - pairBoostedCrossSq direction mass weight j k) := by
  simp only [pivotTrace, frobeniusSpread]
  ring

/-! ## 4. The determinant splits into budget and triple cross -/

/-- **THE INVARIANT EXPANSION OF THE COMPLEMENT DETERMINANT.**  The determinant
of the complement matrix on three omitted labels is the product of their three
boosts, times the pair budget less twice the triple cross.  Every dependence on
data beyond the pivots and the boosted crosses is confined to the single term
`tripleBoostedCross`. -/
theorem complementTripleDeterminant_eq_budget_sub_cross
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    complementTripleDeterminant direction mass weight i j k
      = (mass i / weight i) * (mass j / weight j) * (mass k / weight k)
        * (pairDetBudget direction mass weight i j k
            - 2 * tripleBoostedCross direction mass weight i j k) := by
  simp only [complementTripleDeterminant, ternaryDeterminant]
  rw [complementMatrixEntry_diag, complementMatrixEntry_diag, complementMatrixEntry_diag,
    complementMatrixEntry_off direction mass weight hij,
    complementMatrixEntry_off direction mass weight hik,
    complementMatrixEntry_off direction mass weight hjk]
  simp only [pairDetBudget, tripleBoostedCross, pairBoostedCrossSq, fullPivot]
  ring

/-- The complement determinant is positive exactly when the budget beats twice
the triple cross, once the three boosts are positive. -/
theorem complementTripleDeterminant_pos_iff
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hboostI : 0 < mass i / weight i) (hboostJ : 0 < mass j / weight j)
    (hboostK : 0 < mass k / weight k) :
    0 < complementTripleDeterminant direction mass weight i j k
      ↔ 2 * tripleBoostedCross direction mass weight i j k
          < pairDetBudget direction mass weight i j k := by
  rw [complementTripleDeterminant_eq_budget_sub_cross direction mass weight hij hik hjk]
  constructor
  · intro h
    nlinarith [mul_pos (mul_pos hboostI hboostJ) hboostK]
  · intro h
    have hpos : 0 < (mass i / weight i) * (mass j / weight j) * (mass k / weight k) :=
      mul_pos (mul_pos hboostI hboostJ) hboostK
    nlinarith

/-! ## 5. The root-free positivity of the determinant

Two independent sufficient conditions.  The first is sharp for a reader of pair
data.  The second is cheaper and reads no product of three boosted crosses.
-/

/-- **THE SHARP PAIR CONDITION.**  A positive budget whose square beats four
times the product of the three boosted crosses forces the determinant positive,
whatever the sign of the triple cross.  The pinning identity turns the square
root that the geometry suggests into this polynomial pair. -/
theorem two_tripleBoostedCross_lt_of_sq
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size)
    (hA : 0 < pairDetBudget direction mass weight i j k)
    (hsq : 4 * (pairBoostedCrossSq direction mass weight i j
        * pairBoostedCrossSq direction mass weight i k
        * pairBoostedCrossSq direction mass weight j k)
      < pairDetBudget direction mass weight i j k ^ 2) :
    2 * tripleBoostedCross direction mass weight i j k
      < pairDetBudget direction mass weight i j k := by
  set A := pairDetBudget direction mass weight i j k with hAdef
  set W := tripleBoostedCross direction mass weight i j k with hWdef
  have hW2 : W ^ 2
      = pairBoostedCrossSq direction mass weight i j
        * pairBoostedCrossSq direction mass weight i k
        * pairBoostedCrossSq direction mass weight j k := by
    rw [hWdef]; exact sq_tripleBoostedCross direction mass weight i j k
  rw [← hW2] at hsq
  nlinarith [hA, hsq, sq_nonneg (A - 2 * W), sq_nonneg (A + 2 * W)]

/-- **THE CONSTANT FOUR IS SHARP.**  At equality the determinant can vanish, so
no smaller constant certifies positivity from pair data alone.  With the budget
equal to twice the triple cross the square of the budget is exactly four times
the product of the boosted crosses. -/
theorem pairBudget_constant_sharp
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size)
    (hEq : pairDetBudget direction mass weight i j k
      = 2 * tripleBoostedCross direction mass weight i j k) :
    pairDetBudget direction mass weight i j k ^ 2
      = 4 * (pairBoostedCrossSq direction mass weight i j
        * pairBoostedCrossSq direction mass weight i k
        * pairBoostedCrossSq direction mass weight j k) := by
  rw [hEq, ← sq_tripleBoostedCross direction mass weight i j k]
  ring

/-- **THE EXPLICIT HADAMARD INEQUALITY.**  Twice the triple cross never exceeds
the pivot cross sum.  Equivalently the determinant of the omitted Gram never
exceeds the product of its diagonal.  The proof is one arithmetic-geometric step
against the pinning identity, with the pair Cauchy-Schwarz supplying the
comparison, and it takes no root. -/
theorem pivotCrossSum_nonneg_and_sq_ge
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size) (hboost : ∀ label, 0 ≤ mass label / weight label) :
    0 ≤ pivotCrossSum direction mass weight i j k
      ∧ 4 * tripleBoostedCross direction mass weight i j k ^ 2
        ≤ pivotCrossSum direction mass weight i j k ^ 2 := by
  set W := tripleBoostedCross direction mass weight i j k with hWdef
  set qij := pairBoostedCrossSq direction mass weight i j with hqij
  set qik := pairBoostedCrossSq direction mass weight i k with hqik
  set qjk := pairBoostedCrossSq direction mass weight j k with hqjk
  set pi_ := fullPivot direction mass weight i with hpi
  set pj_ := fullPivot direction mass weight j with hpj
  set pk_ := fullPivot direction mass weight k with hpk
  have hW2 : W ^ 2 = qij * qik * qjk := by
    rw [hWdef, hqij, hqik, hqjk]; exact sq_tripleBoostedCross direction mass weight i j k
  have hqij0 : 0 ≤ qij :=
    pairBoostedCrossSq_nonneg' direction mass weight i j (hboost i) (hboost j)
  have hqik0 : 0 ≤ qik :=
    pairBoostedCrossSq_nonneg' direction mass weight i k (hboost i) (hboost k)
  have hqjk0 : 0 ≤ qjk :=
    pairBoostedCrossSq_nonneg' direction mass weight j k (hboost j) (hboost k)
  have hcs : qij ≤ pi_ * pj_ :=
    pairBoostedCrossSq_le_pivot_mul direction mass weight huniv i j (hboost i) (hboost j)
  have hpi0 : 0 ≤ pi_ :=
    fullPivot_nonneg_of_boost direction mass weight huniv i (hboost i)
  have hpj0 : 0 ≤ pj_ :=
    fullPivot_nonneg_of_boost direction mass weight huniv j (hboost j)
  have hpk0 : 0 ≤ pk_ :=
    fullPivot_nonneg_of_boost direction mass weight huniv k (hboost k)
  -- the two-term arithmetic-geometric bound already beats twice the cross
  have hkey : 4 * W ^ 2 ≤ (pi_ * qjk + pj_ * qik) ^ 2 := by
    have hmul : qij * (qik * qjk) ≤ (pi_ * pj_) * (qik * qjk) := by
      have : 0 ≤ qik * qjk := mul_nonneg hqik0 hqjk0
      nlinarith [hcs, this]
    nlinarith [sq_nonneg (pi_ * qjk - pj_ * qik), hW2, hmul]
  have hsum0 : 0 ≤ pi_ * qjk + pj_ * qik := by
    have := mul_nonneg hpi0 hqjk0
    have := mul_nonneg hpj0 hqik0
    linarith
  have hlast : 0 ≤ pk_ * qij := mul_nonneg hpk0 hqij0
  have hSeq : pivotCrossSum direction mass weight i j k
      = pi_ * qjk + pj_ * qik + pk_ * qij := by
    simp only [pivotCrossSum, ← hpi, ← hpj, ← hpk, ← hqij, ← hqik, ← hqjk]
  rw [hSeq]
  refine ⟨by linarith, ?_⟩
  nlinarith [hkey, hsum0, hlast]

/-- **The explicit Hadamard inequality.**  Twice the triple cross never exceeds
the pivot cross sum. -/
theorem two_tripleBoostedCross_le_pivotCrossSum
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size) (hboost : ∀ label, 0 ≤ mass label / weight label) :
    2 * tripleBoostedCross direction mass weight i j k
      ≤ pivotCrossSum direction mass weight i j k := by
  obtain ⟨hS0, hsq⟩ :=
    pivotCrossSum_nonneg_and_sq_ge direction mass weight huniv i j k hboost
  nlinarith [hS0, hsq]

/-- **The mirror bound.**  The triple cross is bounded below by the negated
pivot cross sum, so the pair data brackets it on both sides. -/
theorem neg_pivotCrossSum_le_two_tripleBoostedCross
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size) (hboost : ∀ label, 0 ≤ mass label / weight label) :
    -pivotCrossSum direction mass weight i j k
      ≤ 2 * tripleBoostedCross direction mass weight i j k := by
  obtain ⟨hS0, hsq⟩ :=
    pivotCrossSum_nonneg_and_sq_ge direction mass weight huniv i j k hboost
  nlinarith [hS0, hsq]

/-- **THE HADAMARD CONDITION.**  A budget above the pivot cross sum forces the
determinant positive.  It reads the pivots and the boosted crosses linearly and
never forms the product of three boosted crosses. -/
theorem two_tripleBoostedCross_lt_of_hadamard
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size) (hboost : ∀ label, 0 ≤ mass label / weight label)
    (hbudget : pivotCrossSum direction mass weight i j k
      < pairDetBudget direction mass weight i j k) :
    2 * tripleBoostedCross direction mass weight i j k
      < pairDetBudget direction mass weight i j k := by
  have := two_tripleBoostedCross_le_pivotCrossSum direction mass weight huniv i j k hboost
  linarith

/-- **THE OMITTED GRAM DETERMINANT NEVER EXCEEDS ITS DIAGONAL PRODUCT.**  This is
Hadamard for the omitted Gram, written entirely in pivot coordinates with no
matrix and no root. -/
theorem gramDeterminant_le_pivotTripleProduct
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size) (hboost : ∀ label, 0 ≤ mass label / weight label) :
    pivotTripleProduct direction mass weight i j k
        + 2 * tripleBoostedCross direction mass weight i j k
        - pivotCrossSum direction mass weight i j k
      ≤ pivotTripleProduct direction mass weight i j k := by
  have := two_tripleBoostedCross_le_pivotCrossSum direction mass weight huniv i j k hboost
  linarith

/-! ## 6. The two cells -/

/-- The diagonal complement entry is positive exactly below pivot one. -/
theorem complementMatrixEntry_diag_pos
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (a : Fin size) (hboost : 0 < mass a / weight a)
    (hpivot : fullPivot direction mass weight a < 1) :
    0 < complementMatrixEntry direction mass weight a a := by
  rw [complementMatrixEntry_diag]
  exact mul_pos hboost (by linarith)

/-- The second leading minor of the complement in pivot coordinates. -/
theorem complementSecondMinor_eq
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {a b : Fin size} (hab : a ≠ b) :
    complementMatrixEntry direction mass weight a a
        * complementMatrixEntry direction mass weight b b
        - complementMatrixEntry direction mass weight a b ^ 2
      = (mass a / weight a) * (mass b / weight b)
        * ((1 - fullPivot direction mass weight a)
            * (1 - fullPivot direction mass weight b)
          - pairBoostedCrossSq direction mass weight a b) := by
  rw [complementMatrixEntry_diag, complementMatrixEntry_diag,
    complementMatrixEntry_off direction mass weight hab]
  simp only [pairBoostedCrossSq, fullPivot]
  ring

/-- The second leading minor is positive exactly when the deflated pair product
beats the boosted cross. -/
theorem complementSecondMinor_pos
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {a b : Fin size} (hab : a ≠ b)
    (hboostA : 0 < mass a / weight a) (hboostB : 0 < mass b / weight b)
    (hpair : pairBoostedCrossSq direction mass weight a b
      < (1 - fullPivot direction mass weight a) * (1 - fullPivot direction mass weight b)) :
    0 < complementMatrixEntry direction mass weight a a
        * complementMatrixEntry direction mass weight b b
        - complementMatrixEntry direction mass weight a b ^ 2 := by
  rw [complementSecondMinor_eq direction mass weight hab]
  exact mul_pos (mul_pos hboostA hboostB) (by linarith)

/-- **THE PAIR-BUDGET CELL.**  Below pivot one, past the deflated pair product,
with a positive budget whose square beats four times the product of the three
boosted crosses, the selection omitting the triple is strictly positive
definite.  No eigenvalue, no matrix square root and no spectral radius appears
in the statement or in the proof. -/
theorem posDef_directionChartGap_compl_triple_of_pairBudget
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hboostI : 0 < mass i / weight i) (hboostJ : 0 < mass j / weight j)
    (hboostK : 0 < mass k / weight k)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hpivot : fullPivot direction mass weight i < 1)
    (hpair : pairBoostedCrossSq direction mass weight i j
      < (1 - fullPivot direction mass weight i) * (1 - fullPivot direction mass weight j))
    (hA : 0 < pairDetBudget direction mass weight i j k)
    (hsq : 4 * (pairBoostedCrossSq direction mass weight i j
        * pairBoostedCrossSq direction mass weight i k
        * pairBoostedCrossSq direction mass weight j k)
      < pairDetBudget direction mass weight i j k ^ 2) :
    (directionChartGap direction mass weight
      (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef := by
  refine (posDef_directionChartGap_compl_triple_iff direction mass weight hij hik hjk
    hboostI hboostJ hboostK huniv).mpr ?_
  refine ⟨complementMatrixEntry_diag_pos direction mass weight i hboostI hpivot,
    complementSecondMinor_pos direction mass weight hij hboostI hboostJ hpair, ?_⟩
  refine (complementTripleDeterminant_pos_iff direction mass weight hij hik hjk
    hboostI hboostJ hboostK).mpr ?_
  exact two_tripleBoostedCross_lt_of_sq direction mass weight i j k hA hsq

/-- **THE HADAMARD CELL.**  The cheaper reading: a budget above the pivot cross
sum.  It forms no product of three boosted crosses. -/
theorem posDef_directionChartGap_compl_triple_of_hadamardBudget
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (hboostI : 0 < mass i / weight i) (hboostJ : 0 < mass j / weight j)
    (hboostK : 0 < mass k / weight k)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hpivot : fullPivot direction mass weight i < 1)
    (hpair : pairBoostedCrossSq direction mass weight i j
      < (1 - fullPivot direction mass weight i) * (1 - fullPivot direction mass weight j))
    (hbudget : pivotCrossSum direction mass weight i j k
      < pairDetBudget direction mass weight i j k) :
    (directionChartGap direction mass weight
      (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef := by
  refine (posDef_directionChartGap_compl_triple_iff direction mass weight hij hik hjk
    hboostI hboostJ hboostK huniv).mpr ?_
  refine ⟨complementMatrixEntry_diag_pos direction mass weight i hboostI hpivot,
    complementSecondMinor_pos direction mass weight hij hboostI hboostJ hpair, ?_⟩
  refine (complementTripleDeterminant_pos_iff direction mass weight hij hik hjk
    hboostI hboostJ hboostK).mpr ?_
  exact two_tripleBoostedCross_lt_of_hadamard direction mass weight huniv i j k hboost hbudget

/-! ## 7. Relations to the landed invariant cells -/

/-- **The sharp cell forces the second symmetric function positive.**  The gap
between the two thresholds is the square `(T - 3) ^ 2`, so the sharp spread
condition is strictly the stronger reading of the trace and the spread except at
trace three, where the two agree. -/
theorem secondSymmetric_pos_of_sharpSpread
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size)
    (hsharp : 2 * frobeniusSpread direction mass weight i j k
      < sharpThreshold (pivotTrace direction mass weight i j k)) :
    frobeniusSpread direction mass weight i j k
      < pivotTrace direction mass weight i j k ^ 2
        - 4 * pivotTrace direction mass weight i j k + 6 := by
  simp only [sharpThreshold] at hsharp
  nlinarith [sq_nonneg (pivotTrace direction mass weight i j k - 3)]

/-- The threshold gap between the two readings is exactly the shifted square. -/
theorem sharpThreshold_gap (pivotTraceValue : ℝ) :
    2 * (pivotTraceValue ^ 2 - 4 * pivotTraceValue + 6)
        - sharpThreshold pivotTraceValue
      = (pivotTraceValue - 3) ^ 2 := by
  simp only [sharpThreshold]
  ring

/-- **The budget is the determinant reading of the trace, the spread and the two
pivot polynomials.**  Together with the pinning identity this says that the
pivots and the boosted crosses determine the complement determinant up to the
sign of one term. -/
theorem pairDetBudget_sub_cross_eq_invariants
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size) :
    pairDetBudget direction mass weight i j k
        - 2 * tripleBoostedCross direction mass weight i j k
      = 1 - pivotTrace direction mass weight i j k
        + (pivotTrace direction mass weight i j k ^ 2
            - frobeniusSpread direction mass weight i j k) / 2
        - pivotTripleProduct direction mass weight i j k
        + pivotCrossSum direction mass weight i j k
        - 2 * tripleBoostedCross direction mass weight i j k := by
  rw [pairDetBudget_eq_invariants]

/-! ## 8. The two-sided bracket and the covering consumer -/

/-- **THE DETERMINANT BRACKET.**  The complement determinant, divided by the
three boosts, lies within the pivot cross sum of the pair budget.  So the pair
data locates the determinant inside an interval of half-width `pivotCrossSum`,
and the sign of the triple cross is the only remaining freedom. -/
theorem pairDetBudget_sub_cross_bracket
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size) (hboost : ∀ label, 0 ≤ mass label / weight label) :
    pairDetBudget direction mass weight i j k
        - pivotCrossSum direction mass weight i j k
      ≤ pairDetBudget direction mass weight i j k
          - 2 * tripleBoostedCross direction mass weight i j k
    ∧ pairDetBudget direction mass weight i j k
          - 2 * tripleBoostedCross direction mass weight i j k
      ≤ pairDetBudget direction mass weight i j k
          + pivotCrossSum direction mass weight i j k := by
  have hupper := two_tripleBoostedCross_le_pivotCrossSum direction mass weight huniv i j k hboost
  have hlower :=
    neg_pivotCrossSum_le_two_tripleBoostedCross direction mass weight huniv i j k hboost
  exact ⟨by linarith, by linarith⟩

/-- **The Hadamard cell is the weaker reading.**  A budget above the pivot cross
sum already forces a positive determinant, hence the sharp pair condition's
conclusion, without forming the triple product. -/
theorem hadamardBudget_imp_det_pos
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size) (hboost : ∀ label, 0 ≤ mass label / weight label)
    (hbudget : pivotCrossSum direction mass weight i j k
      < pairDetBudget direction mass weight i j k) :
    0 < pairDetBudget direction mass weight i j k
      - 2 * tripleBoostedCross direction mass weight i j k := by
  have := two_tripleBoostedCross_le_pivotCrossSum direction mass weight huniv i j k hboost
  linarith

/-- **The pair-budget cover.**  At every chart point some omitted triple clears
the pair budget.  This is the covering shape the consolidated statement
consumes. -/
def PairBudgetCovers (direction : Fin size → (Fin 3 → ℝ)) : Prop :=
  ∀ point : DirectionChartPoint size,
    ∃ i j k : Fin size, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      fullPivot direction point.mass point.weight i < 1 ∧
      pairBoostedCrossSq direction point.mass point.weight i j
        < (1 - fullPivot direction point.mass point.weight i)
          * (1 - fullPivot direction point.mass point.weight j) ∧
      0 < pairDetBudget direction point.mass point.weight i j k ∧
      4 * (pairBoostedCrossSq direction point.mass point.weight i j
          * pairBoostedCrossSq direction point.mass point.weight i k
          * pairBoostedCrossSq direction point.mass point.weight j k)
        < pairDetBudget direction point.mass point.weight i j k ^ 2

/-- **The cover supplies a strictly positive definite selection at every chart
point.**  Its card-three witness is the omitted triple's complement. -/
theorem exists_posDef_compl_triple_of_pairBudgetCovers
    (direction : Fin size → (Fin 3 → ℝ)) (hcover : PairBudgetCovers direction)
    (point : DirectionChartPoint size)
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef) :
    ∃ i j k : Fin size, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (directionChartGap direction point.mass point.weight
        (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef := by
  obtain ⟨i, j, k, hij, hik, hjk, hpivot, hpair, hA, hsq⟩ := hcover point
  have hboostI : 0 < point.mass i / point.weight i :=
    div_pos (point.mass_pos i) (point.weight_pos i)
  have hboostJ : 0 < point.mass j / point.weight j :=
    div_pos (point.mass_pos j) (point.weight_pos j)
  have hboostK : 0 < point.mass k / point.weight k :=
    div_pos (point.mass_pos k) (point.weight_pos k)
  exact ⟨i, j, k, hij, hik, hjk,
    posDef_directionChartGap_compl_triple_of_pairBudget direction point.mass point.weight
      hij hik hjk hboostI hboostJ hboostK huniv hpivot hpair hA hsq⟩

end Gtz

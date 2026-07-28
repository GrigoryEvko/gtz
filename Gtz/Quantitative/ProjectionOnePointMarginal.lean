/-
# C7 — the projection one-point marginal, discharged

`Gtz.IsProjectionOnePointMarginal` (`Gtz/Design/VolumeSamplingAverage.lean`) is a
`def ... : Prop` that was never discharged, and four shipped theorems carried it as a
hypothesis.  This file proves it, for EVERY weighted design and with no side
condition:

    `∑_{|C| = rank, c ∈ C} det P_C  =  P_cc  =  t_c · ℓ_c` .

`Gtz.isProjectionOnePointMarginal` is that statement, so
`Gtz.expectedSubsetSum_eq_leverageWeightedAtomSum`,
`Gtz.expectedSubsetTrace_eq_expectedElementary_one_of_marginal`,
`Gtz.coeff_mixedCharPoly_pred_rank_of_marginal` and
`Gtz.coeff_mixedCharPoly_two_le_neg_nine_of_marginal` are now unconditional: their
hypothesis can be supplied by that theorem at every call site.  This file does not
edit those four; it supplies what they ask for.

## ONE polynomial variable, not two

`IsProjectionOnePointMarginal`'s docstring records a construction plan: scale row and
column `c` of `P` by `√s`, so that `det(1 + X · P · diag(1,…,s,…,1))` has
`X^rank`-coefficient `∑_C s^{[c ∈ C]} det P_C`, then differentiate at `s = 1` — for
which it asks for a bivariate `coeff_det_one_add_X_smul_eq_sum_minors`.  **That plan is
unnecessary and no bivariate argument appears below.**  The marginal is a DIFFERENCE of
two values of that parameter, not a derivative: `s = 1` is the shipped
`Gtz.sum_det_projectionMinors`, `s = 0` is the single univariate identity C7-A, and the
whole content is that the second subtracts the subsets through `c` from the first.

## The chain, in the order the file mechanizes it

1.  **The erased chart.**  `P^{(c)} := (1 - E_cc) · P` (`erasedRowChart`) is `P` with
    row `c` zeroed and nothing else touched (`erasedRowChart_apply`).  Consequently its
    principal minors are exactly the minors of `P` that AVOID `c`: a block containing
    `c` has a zero row (`det_submatrix_erasedRowChart`).
2.  **The rank side.**  `P = V Vᵀ` with `VᵀV = 1`, so `P^{(c)} = ((1-E)V) Vᵀ` and
    Weinstein–Aronszajn moves the generating function to size `rank`:
    `det(1 + X P^{(c)}) = det(1 + X (1 - v_c v_cᵀ))`, where `v_c = √t_c · g_c` is the
    scaled frame's row (`transpose_mul_erasedScaledAtomRows`,
    `det_one_add_X_smul_erasedRowChart_eq_rankGap`).  Only Parseval is consumed.
3.  **Rank-one determinants.**  Every principal block of `1 - v vᵀ` is again of that
    shape, and `det(1 - u uᵀ) = 1 - ⟨u,u⟩` by Weinstein–Aronszajn against a one-column
    factorisation (`det_one_sub_vecMulVec`), so the `level`-minors of the gap sum to
    `C(rank, level) - C(rank-1, level-1) · |v_c|²` — the constant part by
    `Finset.card_powersetCard` and the quadratic part by the shipped double count
    `Gtz.sum_powersetCard_sum_mem_eq_choose_mul_sum` of
    `Gtz/Quantitative/CauchyBinetValueFloor.lean`, which is reused, not re-proved.
4.  **C7-A** (`det_one_add_X_smul_erasedRow_projectionOfDesign`): comparing those
    coefficients with `(1+X)^{rank-1}(1 + (1 - P_cc) X)` is Pascal's rule.
5.  **C7-B** (`sum_shadowDeterminant_mem_eq_diag`, then `isProjectionOnePointMarginal`):
    subtract the avoiding minors from the shipped total `C(rank, level)`.
6.  **C7-C**: `sum_shadowDeterminant_mem_eq_diag_mul_choose` at every subset size, and
    `sum_esym_shadowDeterminant_mem_eq`, the count FLOOR-E2 consumes.

## The hypotheses, so the reach is not overstated

`isProjectionOnePointMarginal`, `sum_shadowDeterminant_mem_eq_diag` and
`sum_shadowDeterminant_eq_choose` carry NOTHING beyond the design — in particular no
rank hypothesis.  At `rank = 0` the marginal is `0 = 0`: the only `0`-subset is empty
and the chart is the zero matrix.

Five statements do carry a hypothesis, and each is sharp.

  * `sum_det_submatrix_one_sub_vecMulVec`, `sum_shadowDeterminant_notMem_eq` and
    `sum_shadowDeterminant_mem_eq_diag_mul_choose` need `0 < level`.  At `level = 0` the
    containing sum is `0` while `C(rank-1, 0-1)` reads as `C(rank-1, 0) = 1` under `Nat`
    subtraction, so the identity is false there and the hypothesis is not caution.
  * C7-A needs `1 ≤ rank`.  At `rank = 0` the chart is `0`, the left side is `1`, and
    `(1+X)^{0-1}(1 + X)` is `1 + X`.
  * `sum_esym_shadowDeterminant_mem_eq` needs `2 ≤ rank`, because its inner subset size
    `rank - 1` must be positive for the previous item to apply.

The combinatorial helper `card_filter_powersetCard_superset_mem` is stated over a bare
index type with its own arithmetic side conditions (`1 ≤ level`, `level ≤ size`, and the
subset's cardinality) and mentions no design; `powersetCard_eq_filter_subset` is
unconditional.

## What this does NOT do

It closes no covering class and moves no cell.  Discharging a hypothesis makes four
existing theorems unconditional and hands FLOOR-E2 its count; `GTZ(6,3)` and `GTZ(7,3)`
are exactly as open after this file as before it.  In particular the
`(size - rank)(rank - 1) · P_cc + rank` identity below is a COUNT — it says nothing
about any value, any floor, or any class, and the E2 floor that will consume it still
has to be proved.
-/
import Mathlib
import Gtz.Design.VolumeSamplingAverage
import Gtz.Quantitative.CauchyBinetValueFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The rank-one gap determinant -/

/-- **The rank-one gap determinant**: `det (1 - v vᵀ) = 1 - ⟨v, v⟩`, at every index
type.  Weinstein–Aronszajn against a one-column factorisation of `v vᵀ`; no
eigenvalues and no invertibility. -/
theorem det_one_sub_vecMulVec {index : Type*} [Fintype index] [DecidableEq index]
    (vector : index → ℝ) :
    (1 - Matrix.vecMulVec vector vector).det = 1 - vector ⬝ᵥ vector := by
  have hfactor : (1 : Matrix index index ℝ) - Matrix.vecMulVec vector vector
      = 1 + (-(Matrix.replicateCol (Fin 1) vector)) * Matrix.replicateRow (Fin 1) vector := by
    ext leftIndex rightIndex
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.neg_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, Matrix.vecMulVec_apply,
      Fin.sum_univ_one]
    ring
  rw [hfactor, Matrix.det_one_add_mul_comm, Matrix.det_fin_one]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply_eq, Matrix.neg_apply,
    Matrix.replicateCol_apply, Matrix.replicateRow_apply, dotProduct, mul_neg]
  rw [Finset.sum_neg_distrib]
  ring

section Marginal

variable {size rank : ℕ}

/-! ## The chart with one row erased -/

/-- **The chart with one atom's row erased**, in the form the campaign states it:
left multiplication of the design's chart by `1 - E_cc`. -/
noncomputable def erasedRowChart (design : WeightedDesign size rank) (erasedIndex : Fin size) :
    Matrix (Fin size) (Fin size) ℝ :=
  (1 - Matrix.single erasedIndex erasedIndex (1 : ℝ)) * projectionOfDesign design

/-- Left multiplication by `1 - E_cc` erases the row at `c` and leaves every other
row of the chart alone. -/
theorem erasedRowChart_apply (design : WeightedDesign size rank)
    (erasedIndex rowIndex colIndex : Fin size) :
    erasedRowChart design erasedIndex rowIndex colIndex
      = if rowIndex = erasedIndex then 0 else projectionOfDesign design rowIndex colIndex := by
  have hsingle : ∑ innerIndex,
        Matrix.single erasedIndex erasedIndex (1 : ℝ) rowIndex innerIndex
          * projectionOfDesign design innerIndex colIndex
      = if rowIndex = erasedIndex then projectionOfDesign design rowIndex colIndex else 0 := by
    by_cases hrow : rowIndex = erasedIndex
    · rw [if_pos hrow, Finset.sum_eq_single erasedIndex]
      · rw [Matrix.single_apply, if_pos ⟨hrow.symm, rfl⟩, one_mul, hrow]
      · intro otherIndex _ hother
        rw [Matrix.single_apply, if_neg (fun hpair => hother hpair.2.symm), zero_mul]
      · intro hnotMem
        exact absurd (Finset.mem_univ erasedIndex) hnotMem
    · rw [if_neg hrow]
      refine Finset.sum_eq_zero fun innerIndex _ => ?_
      rw [Matrix.single_apply, if_neg (fun hpair => hrow hpair.1.symm), zero_mul]
  rw [erasedRowChart, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply, hsingle]
  by_cases hrow : rowIndex = erasedIndex
  · rw [if_pos hrow, if_pos hrow, sub_self]
  · rw [if_neg hrow, if_neg hrow, sub_zero]

/-- The erased chart is still a frame square: erasing a row of `P = V Vᵀ` erases the
same row of `V`. -/
theorem erasedRowChart_eq_erasedFrame_mul_transpose (design : WeightedDesign size rank)
    (erasedIndex : Fin size) :
    erasedRowChart design erasedIndex
      = ((1 - Matrix.single erasedIndex erasedIndex (1 : ℝ)) * scaledAtomRows design)
        * (scaledAtomRows design)ᵀ := by
  rw [erasedRowChart, projectionOfDesign, ← Matrix.mul_assoc]

/-- **The rank-side companion of the erased chart.**  Contracting the erased frame
against the full frame turns Parseval into the rank-one gap `1 - v_c v_cᵀ`, where
`v_c = √t_c · g_c` is the scaled frame's row at the erased atom. -/
theorem transpose_mul_erasedScaledAtomRows (design : WeightedDesign size rank)
    (erasedIndex : Fin size) :
    (scaledAtomRows design)ᵀ
        * ((1 - Matrix.single erasedIndex erasedIndex (1 : ℝ)) * scaledAtomRows design)
      = 1 - Matrix.vecMulVec (scaledAtomRows design erasedIndex)
              (scaledAtomRows design erasedIndex) := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, transpose_mul_scaledAtomRows]
  congr 1
  ext leftCoord rightCoord
  rw [Matrix.mul_apply, Matrix.vecMulVec_apply, Finset.sum_eq_single erasedIndex]
  · rw [Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_eq_single erasedIndex]
    · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, one_mul]
    · intro otherIndex _ hother
      rw [Matrix.single_apply, if_neg (fun hpair => hother hpair.2.symm), zero_mul]
    · intro hnotMem
      exact absurd (Finset.mem_univ erasedIndex) hnotMem
  · intro otherIndex _ hother
    rw [Matrix.mul_apply, Finset.sum_eq_zero, mul_zero]
    intro innerIndex _
    rw [Matrix.single_apply, if_neg (fun hpair => hother hpair.1.symm), zero_mul]
  · intro hnotMem
    exact absurd (Finset.mem_univ erasedIndex) hnotMem

/-- **The generating function of the erased chart's minors lives on the rank side.**
Weinstein–Aronszajn over `ℝ[X]` moves the `size`-sided determinant of `1 + X · P^{(c)}`
onto the `rank`-sided determinant of `1 + X · (1 - v_c v_cᵀ)`. -/
theorem det_one_add_X_smul_erasedRowChart_eq_rankGap (design : WeightedDesign size rank)
    (erasedIndex : Fin size) :
    (1 + (Polynomial.X : Polynomial ℝ)
        • (erasedRowChart design erasedIndex).map Polynomial.C).det
      = (1 + (Polynomial.X : Polynomial ℝ)
          • ((1 : Matrix (Fin rank) (Fin rank) ℝ)
              - Matrix.vecMulVec (scaledAtomRows design erasedIndex)
                  (scaledAtomRows design erasedIndex)).map Polynomial.C).det := by
  rw [erasedRowChart_eq_erasedFrame_mul_transpose design erasedIndex,
    Matrix.map_mul, ← Matrix.smul_mul, Matrix.det_one_add_mul_comm, Matrix.mul_smul,
    ← Matrix.map_mul, transpose_mul_erasedScaledAtomRows]

/-! ## The two families of principal minors -/

/-- The diagonal of the chart is the squared length of the scaled frame's row. -/
theorem projectionOfDesign_diagonal_eq_sum_sq (design : WeightedDesign size rank)
    (atomIndex : Fin size) :
    projectionOfDesign design atomIndex atomIndex
      = ∑ coord, scaledAtomRows design atomIndex coord ^ 2 := by
  rw [projectionOfDesign, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun coord _ => by rw [Matrix.transpose_apply, ← pow_two]

/-- **The erased chart's principal minors**: they agree with the chart's off the
erased atom and vanish on it, because the erased row sits inside the block. -/
theorem det_submatrix_erasedRowChart (design : WeightedDesign size rank)
    (erasedIndex : Fin size) (selected : Finset (Fin size)) :
    ((erasedRowChart design erasedIndex).submatrix
        (Subtype.val : { c // c ∈ selected } → Fin size)
        (Subtype.val : { c // c ∈ selected } → Fin size)).det
      = if erasedIndex ∈ selected then 0 else shadowDeterminant design selected := by
  by_cases hmem : erasedIndex ∈ selected
  · rw [if_pos hmem]
    refine Matrix.det_eq_zero_of_row_eq_zero ⟨erasedIndex, hmem⟩ fun colIndex => ?_
    rw [Matrix.submatrix_apply, erasedRowChart_apply, if_pos rfl]
  · rw [if_neg hmem, shadowDeterminant]
    have hoffErased : ∀ chosen : { c // c ∈ selected }, (chosen : Fin size) ≠ erasedIndex := by
      intro chosen hrowEq
      exact hmem (hrowEq ▸ chosen.2)
    congr 1
    ext rowIndex colIndex
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, erasedRowChart_apply,
      if_neg (hoffErased rowIndex)]

/-- **The rank-side principal minors** of the gap `1 - v vᵀ`: each is `1` minus the
selected coordinates' share of `|v|²`, by the rank-one gap determinant. -/
theorem det_submatrix_one_sub_vecMulVec (vector : Fin rank → ℝ)
    (selected : Finset (Fin rank)) :
    (((1 : Matrix (Fin rank) (Fin rank) ℝ) - Matrix.vecMulVec vector vector).submatrix
        (Subtype.val : { c // c ∈ selected } → Fin rank)
        (Subtype.val : { c // c ∈ selected } → Fin rank)).det
      = 1 - ∑ coord ∈ selected, vector coord ^ 2 := by
  have hblock : ((1 : Matrix (Fin rank) (Fin rank) ℝ)
        - Matrix.vecMulVec vector vector).submatrix
        (Subtype.val : { c // c ∈ selected } → Fin rank)
        (Subtype.val : { c // c ∈ selected } → Fin rank)
      = 1 - Matrix.vecMulVec (fun chosen => vector chosen.val)
              (fun chosen => vector chosen.val) := by
    ext leftIndex rightIndex
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.vecMulVec_apply, Subtype.ext_iff]
  rw [hblock, det_one_sub_vecMulVec]
  congr 1
  rw [dotProduct]
  rw [← Finset.sum_coe_sort selected fun coord => vector coord ^ 2]
  exact Finset.sum_congr rfl fun chosen _ => (pow_two (vector chosen.val)).symm

/-- **The rank-side aggregate.**  Summing the gap's `level`-minors over all
`level`-subsets of the rank coordinates costs one binomial for the constant part and
the shipped double count `Gtz.sum_powersetCard_sum_mem_eq_choose_mul_sum` for the
quadratic part.  Positive `level` is needed: at `level = 0` the empty block has
determinant one and no coordinate is charged. -/
theorem sum_det_submatrix_one_sub_vecMulVec (vector : Fin rank → ℝ) (level : ℕ)
    (hlevel : 0 < level) :
    ∑ selected ∈ (Finset.univ : Finset (Fin rank)).powersetCard level,
        (((1 : Matrix (Fin rank) (Fin rank) ℝ) - Matrix.vecMulVec vector vector).submatrix
          (Subtype.val : { c // c ∈ selected } → Fin rank)
          (Subtype.val : { c // c ∈ selected } → Fin rank)).det
      = ((rank.choose level : ℕ) : ℝ)
        - (((rank - 1).choose (level - 1) : ℕ) : ℝ) * ∑ coord, vector coord ^ 2 := by
  have hterm : ∀ selected ∈ (Finset.univ : Finset (Fin rank)).powersetCard level,
      (((1 : Matrix (Fin rank) (Fin rank) ℝ) - Matrix.vecMulVec vector vector).submatrix
          (Subtype.val : { c // c ∈ selected } → Fin rank)
          (Subtype.val : { c // c ∈ selected } → Fin rank)).det
        = 1 - ∑ coord ∈ selected, vector coord ^ 2 :=
    fun selected _ => det_submatrix_one_sub_vecMulVec vector selected
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    sum_powersetCard_sum_mem_eq_choose_mul_sum level hlevel fun coord => vector coord ^ 2]

/-! ## C7-A: the closed form of the erased chart's generating function -/

/-- **C7-A.**  The minor generating function of the chart with one row erased is

    `det (1 + X · (1 - E_cc) P)  =  (1 + X)^(rank - 1) · (1 + (1 - P_cc) X)` ,

in ONE polynomial variable.  Weinstein–Aronszajn puts the `size`-sided determinant on
the rank side as `1 + X · (1 - v_c v_cᵀ)`, and there every principal minor is read off
by the rank-one gap determinant, so the coefficients are `C(rank, level) - C(rank - 1,
level - 1) · P_cc` and Pascal's rule matches them against the product.

The hypothesis `1 ≤ rank` is not caution: at `rank = 0` the chart is the zero matrix,
the left side is `1`, and the right side is `1 + X`.

Nothing bivariate is needed.  `Gtz.IsProjectionOnePointMarginal`'s recorded
construction plan asks for a second variable `s` scaling row and column `c`, and for a
bivariate `coeff_det_one_add_X_smul_eq_sum_minors`; that plan is UNNECESSARY, because
the two values `s = 1` and `s = 0` of that parameter are already the shipped
`Gtz.sum_det_projectionMinors` and this identity, and their difference is the
marginal. -/
theorem det_one_add_X_smul_erasedRow_projectionOfDesign (design : WeightedDesign size rank)
    (erasedIndex : Fin size) (hrank : 1 ≤ rank) :
    (1 + (Polynomial.X : Polynomial ℝ)
        • (erasedRowChart design erasedIndex).map Polynomial.C).det
      = (1 + Polynomial.X) ^ (rank - 1)
        * (1 + Polynomial.C (1 - projectionOfDesign design erasedIndex erasedIndex)
            * Polynomial.X) := by
  obtain ⟨predRank, rfl⟩ : ∃ predRank, rank = predRank + 1 := ⟨rank - 1, by omega⟩
  have hsplit : ((1 : Polynomial ℝ) + Polynomial.X) ^ (predRank + 1 - 1)
        * (1 + Polynomial.C (1 - projectionOfDesign design erasedIndex erasedIndex)
            * Polynomial.X)
      = (1 + Polynomial.X) ^ predRank
        + Polynomial.C (1 - projectionOfDesign design erasedIndex erasedIndex)
          * (Polynomial.X * (1 + Polynomial.X) ^ predRank) := by
    rw [Nat.add_sub_cancel]
    ring
  rw [det_one_add_X_smul_erasedRowChart_eq_rankGap design erasedIndex, hsplit]
  refine Polynomial.ext fun level => ?_
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]
  rcases level with _ | predLevel
  · rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, mul_zero, add_zero,
      Nat.choose_zero_right, Nat.cast_one, Finset.powersetCard_zero, Finset.sum_singleton,
      det_submatrix_one_sub_vecMulVec, Finset.sum_empty, sub_zero]
  · rw [Polynomial.coeff_X_mul, Polynomial.coeff_one_add_X_pow,
      sum_det_submatrix_one_sub_vecMulVec (scaledAtomRows design erasedIndex) (predLevel + 1)
        (Nat.succ_pos predLevel),
      ← projectionOfDesign_diagonal_eq_sum_sq, Nat.add_sub_cancel, Nat.add_sub_cancel,
      Nat.choose_succ_succ predRank predLevel]
    push_cast
    ring

/-! ## The one-point marginal -/

/-- The chart's `level`-minors sum to `C(rank, level)` — `Gtz.sum_det_projectionMinors`
read through `Gtz.shadowDeterminant`. -/
theorem sum_shadowDeterminant_eq_choose (design : WeightedDesign size rank) (level : ℕ) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        shadowDeterminant design selected = ((rank.choose level : ℕ) : ℝ) :=
  sum_det_projectionMinors design level

/-- **The complementary marginal**: the chart's `level`-minors that AVOID an atom sum
to `C(rank, level) - C(rank-1, level-1) · P_cc`.  The whole argument is here — the
erased chart's minors are exactly the avoiding ones, and its generating function is
the rank-side one. -/
theorem sum_shadowDeterminant_notMem_eq (design : WeightedDesign size rank)
    (atomIndex : Fin size) (level : ℕ) (hlevel : 0 < level) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        (if atomIndex ∈ selected then 0 else shadowDeterminant design selected)
      = ((rank.choose level : ℕ) : ℝ)
        - (((rank - 1).choose (level - 1) : ℕ) : ℝ)
          * projectionOfDesign design atomIndex atomIndex := by
  have hterm : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
      (if atomIndex ∈ selected then 0 else shadowDeterminant design selected)
        = ((erasedRowChart design atomIndex).submatrix
            (Subtype.val : { c // c ∈ selected } → Fin size)
            (Subtype.val : { c // c ∈ selected } → Fin size)).det :=
    fun selected _ => (det_submatrix_erasedRowChart design atomIndex selected).symm
  rw [Finset.sum_congr rfl hterm,
    ← Matrix.coeff_det_one_add_X_smul_eq_sum_minors (erasedRowChart design atomIndex) level,
    det_one_add_X_smul_erasedRowChart_eq_rankGap design atomIndex,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    sum_det_submatrix_one_sub_vecMulVec (scaledAtomRows design atomIndex) level hlevel,
    projectionOfDesign_diagonal_eq_sum_sq]

/-- **C7-C, the minor form.**  At every subset size the chart's `level`-minors that
CONTAIN a fixed atom sum to `P_cc · C(rank - 1, level - 1)`. -/
theorem sum_shadowDeterminant_mem_eq_diag_mul_choose (design : WeightedDesign size rank)
    (atomIndex : Fin size) (level : ℕ) (hlevel : 0 < level) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        (if atomIndex ∈ selected then shadowDeterminant design selected else 0)
      = projectionOfDesign design atomIndex atomIndex
        * (((rank - 1).choose (level - 1) : ℕ) : ℝ) := by
  have hsplit : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
      (if atomIndex ∈ selected then shadowDeterminant design selected else 0)
        = shadowDeterminant design selected
          - (if atomIndex ∈ selected then 0 else shadowDeterminant design selected) := by
    intro selected _
    by_cases hmem : atomIndex ∈ selected
    · rw [if_pos hmem, if_pos hmem, sub_zero]
    · rw [if_neg hmem, if_neg hmem, sub_self]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
    sum_shadowDeterminant_eq_choose design level,
    sum_shadowDeterminant_notMem_eq design atomIndex level hlevel]
  ring

/-- **C7-B.**  The `rank`-subsets containing a fixed atom carry exactly the chart's
diagonal entry at that atom: `∑_{C ∋ c} det P_C = P_cc`.  This is the DPP one-point
inclusion probability, and it is unconditional — including at `rank = 0`, where both
sides vanish. -/
theorem sum_shadowDeterminant_mem_eq_diag (design : WeightedDesign size rank)
    (atomIndex : Fin size) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
        (if atomIndex ∈ selected then shadowDeterminant design selected else 0)
      = projectionOfDesign design atomIndex atomIndex := by
  rcases Nat.eq_zero_or_pos rank with hzero | hpos
  · subst hzero
    rw [Finset.powersetCard_zero, Finset.sum_singleton,
      if_neg (Finset.notMem_empty atomIndex), projectionOfDesign_diagonal_eq_sum_sq]
    exact (Finset.sum_empty (f := fun coord : Fin 0 =>
      scaledAtomRows design atomIndex coord ^ 2)).symm
  · rw [sum_shadowDeterminant_mem_eq_diag_mul_choose design atomIndex rank hpos,
      Nat.choose_self, Nat.cast_one, mul_one]

/-- **THE DISCHARGE.**  `Gtz.IsProjectionOnePointMarginal` holds for every weighted
design, so the four theorems that carried it as a hypothesis are unconditional. -/
theorem isProjectionOnePointMarginal (design : WeightedDesign size rank) :
    IsProjectionOnePointMarginal design := by
  intro atomIndex
  rw [sum_shadowDeterminant_mem_eq_diag design atomIndex, projectionOfDesign_diagonal]

/-! ## The count FLOOR-E2 consumes

`e_{rank-1}(P_C)`, the second-from-top elementary symmetric function of a chart block's
eigenvalues, IS the sum of the block's `(rank-1)`-sized principal minors, and a
principal minor of a principal block is a principal minor of the whole chart.  So the
quantity is written below with no `esymm` and no block: it is
`∑_{B ⊆ C, |B| = rank - 1} det P_B`. -/

/-- The `level`-subsets of a subset are the `level`-subsets of everything that lie
inside it. -/
theorem powersetCard_eq_filter_subset (selected : Finset (Fin size)) (level : ℕ) :
    selected.powersetCard level
      = ((Finset.univ : Finset (Fin size)).powersetCard level).filter
          (fun subselected => subselected ⊆ selected) := by
  ext subselected
  rw [Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨fun hpair => ⟨⟨Finset.subset_univ _, hpair.2⟩, hpair.1⟩,
    fun hpair => ⟨hpair.2, hpair.1.2⟩⟩

/-- **The extension count.**  A `(level-1)`-subset extends to `size - level + 1` many
`level`-subsets containing a fixed atom when it already contains that atom, and to
exactly one when it does not — the unique extension being the insertion. -/
theorem card_filter_powersetCard_superset_mem (atomIndex : Fin size) (level : ℕ)
    (hlevel : 1 ≤ level) (hsize : level ≤ size) (subselected : Finset (Fin size))
    (hcard : subselected.card = level - 1) :
    (((Finset.univ : Finset (Fin size)).powersetCard level).filter
        (fun selected => subselected ⊆ selected ∧ atomIndex ∈ selected)).card
      = if atomIndex ∈ subselected then size - level + 1 else 1 := by
  by_cases hmem : atomIndex ∈ subselected
  · rw [if_pos hmem]
    have hcondition : ((Finset.univ : Finset (Fin size)).powersetCard level).filter
          (fun selected => subselected ⊆ selected ∧ atomIndex ∈ selected)
        = ((Finset.univ : Finset (Fin size)).powersetCard level).filter
          (fun selected => subselected ⊆ selected) :=
      Finset.filter_congr fun selected _ =>
        ⟨fun hpair => hpair.1, fun hsubset => ⟨hsubset, hsubset hmem⟩⟩
    rw [hcondition, Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)
        (by omega), hcard, Finset.card_univ, Fintype.card_fin,
      show level - (level - 1) = 1 from by omega, Nat.choose_one_right]
    omega
  · rw [if_neg hmem]
    have hinsertCard : (insert atomIndex subselected).card = level := by
      rw [Finset.card_insert_of_notMem hmem, hcard]
      omega
    have hcondition : ((Finset.univ : Finset (Fin size)).powersetCard level).filter
          (fun selected => subselected ⊆ selected ∧ atomIndex ∈ selected)
        = ((Finset.univ : Finset (Fin size)).powersetCard level).filter
          (fun selected => insert atomIndex subselected ⊆ selected) :=
      Finset.filter_congr fun selected _ =>
        ⟨fun hpair => Finset.insert_subset hpair.2 hpair.1,
          fun hsubset => ⟨(Finset.subset_insert atomIndex subselected).trans hsubset,
            hsubset (Finset.mem_insert_self atomIndex subselected)⟩⟩
    rw [hcondition, Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)
        (by omega), hinsertCard, Finset.card_univ, Fintype.card_fin, Nat.sub_self,
      Nat.choose_zero_right]

/-- **C7-C, the count FLOOR-E2 consumes.**

    `∑_{|C| = rank, c ∈ C} e_{rank-1}(P_C)  =  (size - rank)(rank - 1) · P_cc + rank` .

One exchange of summation over the incidence `B ⊆ C`, the extension count above, and
the two marginals already proved: the `(rank-1)`-minors containing `c` sum to
`(rank - 1) · P_cc` and all of them sum to `C(rank, rank - 1) = rank`.  Rank at least
two is needed for the inner size `rank - 1` to be a positive subset size. -/
theorem sum_esym_shadowDeterminant_mem_eq (design : WeightedDesign size rank)
    (atomIndex : Fin size) (hrank : 2 ≤ rank) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
        (if atomIndex ∈ selected then
            ∑ subselected ∈ selected.powersetCard (rank - 1),
              shadowDeterminant design subselected
          else 0)
      = ((size - rank : ℕ) : ℝ) * ((rank - 1 : ℕ) : ℝ)
          * projectionOfDesign design atomIndex atomIndex + (rank : ℝ) := by
  have hrankLe : rank ≤ size := rank_le_of_design design
  obtain ⟨predRank, rfl⟩ : ∃ predRank, rank = predRank + 2 := ⟨rank - 2, by omega⟩
  have hpred : predRank + 2 - 1 = predRank + 1 := rfl
  have hinner : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard (predRank + 2),
      (if atomIndex ∈ selected then
          ∑ subselected ∈ selected.powersetCard (predRank + 2 - 1),
            shadowDeterminant design subselected
        else 0)
        = ∑ subselected ∈ (Finset.univ : Finset (Fin size)).powersetCard (predRank + 1),
            (if subselected ⊆ selected ∧ atomIndex ∈ selected then
              shadowDeterminant design subselected else 0) := by
    intro selected _
    by_cases hmem : atomIndex ∈ selected
    · rw [if_pos hmem, hpred, powersetCard_eq_filter_subset, Finset.sum_filter]
      exact Finset.sum_congr rfl fun subselected _ => by
        by_cases hsubset : subselected ⊆ selected
        · rw [if_pos hsubset, if_pos ⟨hsubset, hmem⟩]
        · rw [if_neg hsubset, if_neg (fun hpair => hsubset hpair.1)]
    · rw [if_neg hmem]
      exact (Finset.sum_eq_zero fun subselected _ => if_neg fun hpair => hmem hpair.2).symm
  have hcount : ∀ subselected ∈ (Finset.univ : Finset (Fin size)).powersetCard (predRank + 1),
      ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard (predRank + 2),
          (if subselected ⊆ selected ∧ atomIndex ∈ selected then
            shadowDeterminant design subselected else 0)
        = shadowDeterminant design subselected
          * (if atomIndex ∈ subselected then ((size - (predRank + 2) + 1 : ℕ) : ℝ) else 1) := by
    intro subselected hmemFamily
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      card_filter_powersetCard_superset_mem atomIndex (predRank + 2) (by omega) hrankLe
        subselected (by rw [(Finset.mem_powersetCard.mp hmemFamily).2, hpred]), mul_comm]
    by_cases hmem : atomIndex ∈ subselected
    · rw [if_pos hmem, if_pos hmem]
    · rw [if_neg hmem, if_neg hmem, Nat.cast_one]
  have hallMinors : ∑ subselected ∈ (Finset.univ : Finset (Fin size)).powersetCard (predRank + 1),
      shadowDeterminant design subselected = ((predRank : ℝ) + 2) := by
    rw [sum_shadowDeterminant_eq_choose design (predRank + 1), Nat.choose_succ_self_right]
    push_cast
    ring
  have hmemMinors : ∑ subselected ∈ (Finset.univ : Finset (Fin size)).powersetCard (predRank + 1),
      (if atomIndex ∈ subselected then shadowDeterminant design subselected else 0)
        = projectionOfDesign design atomIndex atomIndex * ((predRank : ℝ) + 1) := by
    rw [sum_shadowDeterminant_mem_eq_diag_mul_choose design atomIndex (predRank + 1)
      (Nat.succ_pos predRank), hpred, Nat.add_sub_cancel, Nat.choose_succ_self_right]
    push_cast
    ring
  have hregroup : ∀ subselected : Finset (Fin size),
      shadowDeterminant design subselected
          * (if atomIndex ∈ subselected then ((size - (predRank + 2) + 1 : ℕ) : ℝ) else 1)
        = shadowDeterminant design subselected
          + ((size - (predRank + 2) : ℕ) : ℝ)
            * (if atomIndex ∈ subselected then shadowDeterminant design subselected else 0) := by
    intro subselected
    by_cases hmem : atomIndex ∈ subselected
    · rw [if_pos hmem, if_pos hmem, Nat.cast_add, Nat.cast_one]
      ring
    · rw [if_neg hmem, if_neg hmem, mul_one, mul_zero, add_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm, Finset.sum_congr rfl hcount,
    Finset.sum_congr rfl (fun subselected _ => hregroup subselected), Finset.sum_add_distrib,
    ← Finset.mul_sum, hallMinors, hmemMinors, hpred]
  push_cast
  ring

end Marginal

end Gtz

/-
# The complement laws of a hollow involution, and the `nu`-covering band

The `(6,3)` uniform-share stratum is a covering problem: for every unit-norm
tight frame of six directions in `R^3`, the twenty cells
`K_T = {nu | Gamma[T] ⪰ diag(nu)|_T}` must cover the hypersimplex
`{nu in (0,1)^6 : sum nu = 2}`
(`Gtz.gtzUniformShareSixThree_iff_forall_coversInvariantLeverageDesignRegion`).
The shipped band gate reaches `max_c nu_c <= 9/25`; the polytope reaches `1`.

This file attacks the twenty cells through the structure nobody used: the twenty
triples are TEN COMPLEMENTARY PAIRS, and a complementary pair is rigidly locked.

Write `M = Gamma - 1` for the correlation involution, so `M` is symmetric, hollow
and `M * M = 1` (`Gtz.IsHollowInvolution`).  For a triple `T` write

    `E_T = sum of the three squared correlations`   (`Gtz.tripleEnergy`)
    `P_T = product of the three correlations`       (`Gtz.tripleEdgeProduct`)

## PROVED

1. **THE ENERGY IS COMPLEMENT-INVARIANT.**  `Gtz.IsHollowInvolution.tripleEnergy_perm_eq`:
   `E_T = E_{T'}` for every partition of the six labels into two triples.  Six row
   budgets split against the partition give `2 E_T + X = 3 = 2 E_{T'} + X` with `X`
   the nine cross squares, so the energies agree and
   `Gtz.IsHollowInvolution.crossEnergyPartition_eq` computes `X = 3 - 2 E_T`.

2. **THE PRODUCT IS COMPLEMENT-ANTI-INVARIANT.**
   `Gtz.IsHollowInvolution.tripleEdgeProduct_perm_add_eq_zero`: `P_T + P_{T'} = 0`,
   unconditional — no nondegeneracy, no invertibility.  The proof is the
   intertwining `A N = -N B` between the two hollow blocks across the cross block,
   Cayley-Hamilton at size three (`Gtz.hollowMatrixThree_cube`: `A^3 = E . A + 2P . 1`),
   and the fact that the cross block CANNOT vanish
   (`Gtz.IsHollowInvolution.exists_crossBlock_ne_zero`), because a hollow real `3 x 3`
   matrix never squares to the identity (`Gtz.not_hollowMatrixThree_sq_eq_one`).

3. **EVERY COMPLEMENTARY PAIR OFFERS A COHERENT SIDE.**
   `Gtz.IsHollowInvolution.exists_nonneg_tripleEdgeProduct_perm`.  The shipped floor
   for a general design is four coherent triples of twenty
   (`Gtz.four_le_card_coherentTripleSets_sixThree`); here the pairing is a
   fixed-point-free involution on the twenty triples that REVERSES the sign, so ten
   of the twenty are coherent, one from each pair, and exactly ten when no product
   vanishes.  `Gtz.IsHollowInvolution.tenComplementaryPairs` records all ten
   instances of (1) and (2) at once, and
   `Gtz.IsHollowInvolution.totalTripleEdgeProduct_eq_zero` sums them.

4. **THE DETERMINANT LAWS.**  `Gtz.det_one_add_hollowMatrixThree` and
   `Gtz.det_one_sub_hollowMatrixThree` give `1 - E ± 2P`, hence
   `Gtz.IsHollowInvolution.det_gramBlock_add_compl`:
   `det Gamma[T] + det Gamma[T'] = 2 (1 - E_T)`, and
   `Gtz.IsHollowInvolution.det_gramBlock_eq_det_coGramBlock_compl`, the
   COMPLEMENTARY MINOR IDENTITY `det Gamma[T] = det (2 . 1 - Gamma)[T']`, derived
   here rather than assumed.  `Gtz.IsHollowInvolution.totalGramBlockDet_eq_eight`
   then re-proves the Cauchy-Binet total `sum_T det Gamma[T] = 8` from the two
   complement laws and the shipped `totalTripleEnergy_eq_twelve`, with no
   Cauchy-Binet and no Plucker coordinate.

5. **THE AVERAGING NO-GO, ON THE WHOLE POLYTOPE.**
   `Gtz.IsHollowInvolution.totalShiftedTripleDet_eq`: for any `t`,

       `sum over the twenty triples of det (Gamma[T] - diag(1 - t)|_T)
          = e_3(t) - 2 * (sum_c t_c)`

   because the products cancel in pairs by (2) and the weighted energies collapse by
   the row law.  On the polytope `sum_c t_c = 4`, so the total is `e_3(t) - 8`, and
   `Gtz.IsHollowInvolution.totalShiftedTripleDet_uniform` evaluates it at the centre
   as `-56/27 < 0`.  The MEAN cell determinant is negative, so no averaging argument
   over the twenty triples can ever produce a covering — at any point of `Delta`,
   not merely at the centre.  This generalises the campaign's `-7/27` from one point
   to the polytope.

6. **THE SIGN-AWARE CELL, and a coherent triple of energy at most three fifths.**
   `Gtz.posSemidef_gramBlockShift_of_nonneg_product` is the cell criterion in which
   the cross term works FOR the certificate: a triple with `P_T >= 0` needs only the
   three pair minors and `t_a t_b t_c >= t_a g_bc^2 + t_b g_ac^2 + t_c g_ab^2`.
   `Gtz.IsHollowInvolution.exists_nonneg_product_tripleEnergy_le_three_fifths` supplies
   the triple: the ten pair energies total six by (1) and the shipped
   `Gtz.IsTightGramSix.totalTripleEnergy_eq_twelve`, and by (2) each pair offers a
   coherent side at that energy.  The shipped existence theorem is sign-blind; this
   one is not, and the sign is exactly what the determinant clause needs.
   `Gtz.IsHollowInvolution.exists_mem_invariantLeverageCell_of_cap` is the resulting
   band gate.

## NOT PROVED

**The band is not closed, and my gate is WEAKER than the shipped `9/25`.**  The
shipped gate comes from the spectral route with the `9/25` margin of
`Gtz.exists_dominating_triple_of_isEqualShare`; what section 6 buys is a DIFFERENT,
sign-aware certificate, not a larger constant, and I say so rather than dress it up.
No statement here asserts `GtzUniformShareSixThree` or `GtzWeighted 6 3`.  The count
in (3) is stated as the ten pair witnesses, not as a `Finset.card` of coherent
triples.  Nothing here is conditional: every declaration is unconditional in its
stated hypotheses.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.SixThreeNuCovering
import Gtz.Wave.TightGramSixLaws

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## 1. The edge product of a triple -/

/-- **THE EDGE PRODUCT** of a triple: the product of its three correlations.  Its
SIGN is the campaign's coherence, and it is the only place the third Sylvester
minor sees anything beyond squared correlations. -/
noncomputable def tripleEdgeProduct (gram : Matrix (Fin 6) (Fin 6) ℝ)
    (first second third : Fin 6) : ℝ :=
  gram first second * gram first third * gram second third

theorem tripleEdgeProduct_apply (gram : Matrix (Fin 6) (Fin 6) ℝ)
    (first second third : Fin 6) :
    tripleEdgeProduct gram first second third
      = gram first second * gram first third * gram second third := rfl

/-- **THE TWENTY EDGE PRODUCTS**, in the campaign's triple order. -/
noncomputable def totalTripleEdgeProduct (gram : Matrix (Fin 6) (Fin 6) ℝ) : ℝ :=
  tripleEdgeProduct gram 0 1 2 + tripleEdgeProduct gram 0 1 3 + tripleEdgeProduct gram 0 1 4
    + tripleEdgeProduct gram 0 1 5 + tripleEdgeProduct gram 0 2 3 + tripleEdgeProduct gram 0 2 4
    + tripleEdgeProduct gram 0 2 5 + tripleEdgeProduct gram 0 3 4 + tripleEdgeProduct gram 0 3 5
    + tripleEdgeProduct gram 0 4 5 + tripleEdgeProduct gram 1 2 3 + tripleEdgeProduct gram 1 2 4
    + tripleEdgeProduct gram 1 2 5 + tripleEdgeProduct gram 1 3 4 + tripleEdgeProduct gram 1 3 5
    + tripleEdgeProduct gram 1 4 5 + tripleEdgeProduct gram 2 3 4 + tripleEdgeProduct gram 2 3 5
    + tripleEdgeProduct gram 2 4 5 + tripleEdgeProduct gram 3 4 5

/-! ## 2. Cayley-Hamilton for a hollow three-by-three block

The hollow `3 x 3` block has trace zero, second elementary symmetric function `-E`
and determinant `2 P`, so its characteristic polynomial is `lambda^3 - E lambda - 2 P`
and Cayley-Hamilton reads `A^3 = E . A + 2 P . 1`.  Both are proved entrywise, with
no appeal to the general Cayley-Hamilton. -/

/-- The determinant of a hollow `3 x 3` block is twice its edge product. -/
theorem det_hollowMatrixThree (edgeFirst edgeSecond edgeThird : ℝ) :
    (hollowMatrixThree edgeFirst edgeSecond edgeThird).det
      = 2 * (edgeFirst * edgeSecond * edgeThird) := by
  rw [Matrix.det_fin_three]
  simp only [hollowMatrixThree, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- The hollow block at negated edges is the negated block. -/
theorem hollowMatrixThree_neg (edgeFirst edgeSecond edgeThird : ℝ) :
    hollowMatrixThree (-edgeFirst) (-edgeSecond) (-edgeThird)
      = -hollowMatrixThree edgeFirst edgeSecond edgeThird := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [hollowMatrixThree]

/-- **THE CO-GRAM BLOCK DETERMINANT**: `det (1 - A) = 1 - E - 2 P`.  The shipped
`Gtz.det_one_add_hollowMatrixThree` is the `+` half and is consumed, not rebuilt. -/
theorem det_one_sub_hollowMatrixThree (edgeFirst edgeSecond edgeThird : ℝ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) - hollowMatrixThree edgeFirst edgeSecond edgeThird).det
      = 1 - (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
        - 2 * (edgeFirst * edgeSecond * edgeThird) := by
  have hreflect : (1 : Matrix (Fin 3) (Fin 3) ℝ) - hollowMatrixThree edgeFirst edgeSecond edgeThird
      = 1 + hollowMatrixThree (-edgeFirst) (-edgeSecond) (-edgeThird) := by
    rw [hollowMatrixThree_neg]
    abel
  rw [hreflect, det_one_add_hollowMatrixThree]
  ring

/-- **CAYLEY-HAMILTON AT A HOLLOW BLOCK.**  `A^3 = E . A + 2 P . 1`, where `E` is the
sum of the three squared edges and `P` their product.  Proved entrywise. -/
theorem hollowMatrixThree_cube (edgeFirst edgeSecond edgeThird : ℝ) :
    (hollowMatrixThree edgeFirst edgeSecond edgeThird) ^ 3
      = (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
          • hollowMatrixThree edgeFirst edgeSecond edgeThird
        + (2 * (edgeFirst * edgeSecond * edgeThird)) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, hollowMatrixThree] <;> ring

/-- **NO HOLLOW REAL `3 x 3` MATRIX SQUARES TO THE IDENTITY.**  The three diagonal
equations force every squared edge to be one half, and the `(0,1)` equation forces a
product of two of them to vanish.  This is what makes the cross block of a
partitioned hollow involution nonzero. -/
theorem not_hollowMatrixThree_sq_eq_one (edgeFirst edgeSecond edgeThird : ℝ) :
    (hollowMatrixThree edgeFirst edgeSecond edgeThird)
        * hollowMatrixThree edgeFirst edgeSecond edgeThird
      ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  intro hsquare
  have hzeroZero := congrFun (congrFun hsquare 0) 0
  have honeOne := congrFun (congrFun hsquare 1) 1
  have htwoTwo := congrFun (congrFun hsquare 2) 2
  have hzeroOne := congrFun (congrFun hsquare 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_three, hollowMatrixThree, Matrix.one_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply] at hzeroZero honeOne htwoTwo hzeroOne
  norm_num at hzeroZero honeOne htwoTwo hzeroOne
  rcases hzeroOne with hvanish | hvanish <;> subst hvanish <;>
    nlinarith [hzeroZero, honeOne, htwoTwo]

/-! ## 3. The partition blocks

A hollow involution on six labels, split against the standard partition
`{0,1,2} | {3,4,5}`, has front block `A`, back block `B` and cross block `N`. -/

/-- The front hollow block of the standard partition. -/
noncomputable def frontBlock (invol : Matrix (Fin 6) (Fin 6) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  hollowMatrixThree (invol 0 1) (invol 0 2) (invol 1 2)

/-- The back hollow block of the standard partition. -/
noncomputable def backBlock (invol : Matrix (Fin 6) (Fin 6) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  hollowMatrixThree (invol 3 4) (invol 3 5) (invol 4 5)

/-- The cross block of the standard partition. -/
noncomputable def crossBlock (invol : Matrix (Fin 6) (Fin 6) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  invol.submatrix ![0, 1, 2] ![3, 4, 5]

theorem crossBlock_apply (invol : Matrix (Fin 6) (Fin 6) ℝ) (rowIndex colIndex : Fin 3) :
    crossBlock invol rowIndex colIndex
      = invol (![0, 1, 2] rowIndex) (![3, 4, 5] colIndex) := rfl

/-- **THE CROSS ENERGY** of the standard partition: the nine squared correlations
between the two triples. -/
noncomputable def crossEnergyPartition (invol : Matrix (Fin 6) (Fin 6) ℝ) : ℝ :=
  invol 0 3 ^ 2 + invol 0 4 ^ 2 + invol 0 5 ^ 2
    + invol 1 3 ^ 2 + invol 1 4 ^ 2 + invol 1 5 ^ 2
    + invol 2 3 ^ 2 + invol 2 4 ^ 2 + invol 2 5 ^ 2

namespace IsHollowInvolution

variable {invol : Matrix (Fin 6) (Fin 6) ℝ}

/-- The six row budgets, expanded. -/
theorem row_sq_expand (hinvol : IsHollowInvolution invol) (rowIndex : Fin 6) :
    invol rowIndex 0 ^ 2 + invol rowIndex 1 ^ 2 + invol rowIndex 2 ^ 2
        + invol rowIndex 3 ^ 2 + invol rowIndex 4 ^ 2 + invol rowIndex 5 ^ 2 = 1 := by
  have hrow := hinvol.sum_sq_row rowIndex
  rwa [Fin.sum_univ_six] at hrow

/-- The fifteen orthogonality relations, expanded. -/
theorem offDiag_expand (hinvol : IsHollowInvolution invol) {rowIndex colIndex : Fin 6}
    (hdistinct : rowIndex ≠ colIndex) :
    invol rowIndex 0 * invol 0 colIndex + invol rowIndex 1 * invol 1 colIndex
        + invol rowIndex 2 * invol 2 colIndex + invol rowIndex 3 * invol 3 colIndex
        + invol rowIndex 4 * invol 4 colIndex + invol rowIndex 5 * invol 5 colIndex = 0 := by
  have hentry := congrFun (congrFun hinvol.square_eq_one rowIndex) colIndex
  rw [Matrix.mul_apply, Matrix.one_apply_ne hdistinct, Fin.sum_univ_six] at hentry
  linarith [hentry]

/-! ### The energy complement law -/

/-- **THE FRONT SPLIT.**  Three row budgets against the partition: `2 E_front + X = 3`. -/
theorem two_mul_tripleEnergy_front_add_crossEnergy (hinvol : IsHollowInvolution invol) :
    2 * tripleEnergy invol 0 1 2 + crossEnergyPartition invol = 3 := by
  have hzero := hinvol.row_sq_expand 0
  have hone := hinvol.row_sq_expand 1
  have htwo := hinvol.row_sq_expand 2
  rw [hinvol.diagonal_eq_zero 0] at hzero
  rw [hinvol.diagonal_eq_zero 1, hinvol.apply_comm 0 1] at hone
  rw [hinvol.diagonal_eq_zero 2, hinvol.apply_comm 0 2, hinvol.apply_comm 1 2] at htwo
  simp only [tripleEnergy, crossEnergyPartition]
  linarith [hzero, hone, htwo]

/-- **THE BACK SPLIT**, the same computation on the other triple. -/
theorem two_mul_tripleEnergy_back_add_crossEnergy (hinvol : IsHollowInvolution invol) :
    2 * tripleEnergy invol 3 4 5 + crossEnergyPartition invol = 3 := by
  have hthree := hinvol.row_sq_expand 3
  have hfour := hinvol.row_sq_expand 4
  have hfive := hinvol.row_sq_expand 5
  rw [hinvol.diagonal_eq_zero 3, hinvol.apply_comm 0 3, hinvol.apply_comm 1 3,
    hinvol.apply_comm 2 3] at hthree
  rw [hinvol.diagonal_eq_zero 4, hinvol.apply_comm 0 4, hinvol.apply_comm 1 4,
    hinvol.apply_comm 2 4, hinvol.apply_comm 3 4] at hfour
  rw [hinvol.diagonal_eq_zero 5, hinvol.apply_comm 0 5, hinvol.apply_comm 1 5,
    hinvol.apply_comm 2 5, hinvol.apply_comm 3 5, hinvol.apply_comm 4 5] at hfive
  simp only [tripleEnergy, crossEnergyPartition]
  linarith [hthree, hfour, hfive]

/-- **THE ENERGY COMPLEMENT LAW, standard partition.**  The two triples of a
partition carry the SAME energy. -/
theorem tripleEnergy_front_eq_back (hinvol : IsHollowInvolution invol) :
    tripleEnergy invol 0 1 2 = tripleEnergy invol 3 4 5 := by
  linarith [hinvol.two_mul_tripleEnergy_front_add_crossEnergy,
    hinvol.two_mul_tripleEnergy_back_add_crossEnergy]

/-- **AND THE CROSS ENERGY IS DETERMINED**: `X = 3 - 2 E`. -/
theorem crossEnergyPartition_eq (hinvol : IsHollowInvolution invol) :
    crossEnergyPartition invol = 3 - 2 * tripleEnergy invol 0 1 2 := by
  linarith [hinvol.two_mul_tripleEnergy_front_add_crossEnergy]

/-! ### The intertwining

Nine orthogonality relations, each normalised so that every correlation is written
with its smaller label first.  They are exactly the nine entries of `A N = -N B`. -/

private theorem cross_zero_three (hinvol : IsHollowInvolution invol) :
    invol 0 1 * invol 1 3 + invol 0 2 * invol 2 3 + invol 0 4 * invol 3 4
      + invol 0 5 * invol 3 5 = 0 := by
  have h := hinvol.offDiag_expand (rowIndex := 0) (colIndex := 3) (by decide)
  rw [hinvol.diagonal_eq_zero 0, hinvol.diagonal_eq_zero 3, hinvol.apply_comm 3 4,
    hinvol.apply_comm 3 5] at h
  linarith [h]

private theorem cross_zero_four (hinvol : IsHollowInvolution invol) :
    invol 0 1 * invol 1 4 + invol 0 2 * invol 2 4 + invol 0 3 * invol 3 4
      + invol 0 5 * invol 4 5 = 0 := by
  have h := hinvol.offDiag_expand (rowIndex := 0) (colIndex := 4) (by decide)
  rw [hinvol.diagonal_eq_zero 0, hinvol.diagonal_eq_zero 4, hinvol.apply_comm 4 5] at h
  linarith [h]

private theorem cross_zero_five (hinvol : IsHollowInvolution invol) :
    invol 0 1 * invol 1 5 + invol 0 2 * invol 2 5 + invol 0 3 * invol 3 5
      + invol 0 4 * invol 4 5 = 0 := by
  have h := hinvol.offDiag_expand (rowIndex := 0) (colIndex := 5) (by decide)
  rw [hinvol.diagonal_eq_zero 0, hinvol.diagonal_eq_zero 5] at h
  linarith [h]

private theorem cross_one_three (hinvol : IsHollowInvolution invol) :
    invol 0 1 * invol 0 3 + invol 1 2 * invol 2 3 + invol 1 4 * invol 3 4
      + invol 1 5 * invol 3 5 = 0 := by
  have h := hinvol.offDiag_expand (rowIndex := 1) (colIndex := 3) (by decide)
  rw [hinvol.diagonal_eq_zero 1, hinvol.diagonal_eq_zero 3, hinvol.apply_comm 0 1,
    hinvol.apply_comm 3 4, hinvol.apply_comm 3 5] at h
  linarith [h]

private theorem cross_one_four (hinvol : IsHollowInvolution invol) :
    invol 0 1 * invol 0 4 + invol 1 2 * invol 2 4 + invol 1 3 * invol 3 4
      + invol 1 5 * invol 4 5 = 0 := by
  have h := hinvol.offDiag_expand (rowIndex := 1) (colIndex := 4) (by decide)
  rw [hinvol.diagonal_eq_zero 1, hinvol.diagonal_eq_zero 4, hinvol.apply_comm 0 1,
    hinvol.apply_comm 4 5] at h
  linarith [h]

private theorem cross_one_five (hinvol : IsHollowInvolution invol) :
    invol 0 1 * invol 0 5 + invol 1 2 * invol 2 5 + invol 1 3 * invol 3 5
      + invol 1 4 * invol 4 5 = 0 := by
  have h := hinvol.offDiag_expand (rowIndex := 1) (colIndex := 5) (by decide)
  rw [hinvol.diagonal_eq_zero 1, hinvol.diagonal_eq_zero 5, hinvol.apply_comm 0 1] at h
  linarith [h]

private theorem cross_two_three (hinvol : IsHollowInvolution invol) :
    invol 0 2 * invol 0 3 + invol 1 2 * invol 1 3 + invol 2 4 * invol 3 4
      + invol 2 5 * invol 3 5 = 0 := by
  have h := hinvol.offDiag_expand (rowIndex := 2) (colIndex := 3) (by decide)
  rw [hinvol.diagonal_eq_zero 2, hinvol.diagonal_eq_zero 3, hinvol.apply_comm 0 2,
    hinvol.apply_comm 1 2, hinvol.apply_comm 3 4, hinvol.apply_comm 3 5] at h
  linarith [h]

private theorem cross_two_four (hinvol : IsHollowInvolution invol) :
    invol 0 2 * invol 0 4 + invol 1 2 * invol 1 4 + invol 2 3 * invol 3 4
      + invol 2 5 * invol 4 5 = 0 := by
  have h := hinvol.offDiag_expand (rowIndex := 2) (colIndex := 4) (by decide)
  rw [hinvol.diagonal_eq_zero 2, hinvol.diagonal_eq_zero 4, hinvol.apply_comm 0 2,
    hinvol.apply_comm 1 2, hinvol.apply_comm 4 5] at h
  linarith [h]

private theorem cross_two_five (hinvol : IsHollowInvolution invol) :
    invol 0 2 * invol 0 5 + invol 1 2 * invol 1 5 + invol 2 3 * invol 3 5
      + invol 2 4 * invol 4 5 = 0 := by
  have h := hinvol.offDiag_expand (rowIndex := 2) (colIndex := 5) (by decide)
  rw [hinvol.diagonal_eq_zero 2, hinvol.diagonal_eq_zero 5, hinvol.apply_comm 0 2,
    hinvol.apply_comm 1 2] at h
  linarith [h]

/-- **THE INTERTWINING.**  `A N = -N B`: the front hollow block pushed across the
cross block is the negative of the cross block pushed through the back one.  Each of
the nine entries is one orthogonality relation, with the two diagonal terms removed
by hollowness. -/
theorem frontBlock_mul_crossBlock (hinvol : IsHollowInvolution invol) :
    frontBlock invol * crossBlock invol = -(crossBlock invol * backBlock invol) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [frontBlock, backBlock, crossBlock, hollowMatrixThree, Matrix.mul_apply,
      Fin.sum_univ_three]
  · linarith [hinvol.cross_zero_three]
  · linarith [hinvol.cross_zero_four]
  · linarith [hinvol.cross_zero_five]
  · linarith [hinvol.cross_one_three]
  · linarith [hinvol.cross_one_four]
  · linarith [hinvol.cross_one_five]
  · linarith [hinvol.cross_two_three]
  · linarith [hinvol.cross_two_four]
  · linarith [hinvol.cross_two_five]

/-- **THE CROSS BLOCK CANNOT VANISH.**  If it did, the front block would square to
the identity, which no hollow real `3 x 3` matrix does. -/
theorem exists_crossBlock_ne_zero (hinvol : IsHollowInvolution invol) :
    ∃ rowIndex colIndex : Fin 3, crossBlock invol rowIndex colIndex ≠ 0 := by
  by_contra hvanishes
  push Not at hvanishes
  have hcross : ∀ rowIndex colIndex : Fin 3,
      invol (![0, 1, 2] rowIndex) (![3, 4, 5] colIndex) = 0 := by
    intro rowIndex colIndex
    have hentry := hvanishes rowIndex colIndex
    rwa [crossBlock_apply] at hentry
  have h03 := hcross 0 0
  have h04 := hcross 0 1
  have h05 := hcross 0 2
  have h13 := hcross 1 0
  have h14 := hcross 1 1
  have h15 := hcross 1 2
  have h23 := hcross 2 0
  have h24 := hcross 2 1
  have h25 := hcross 2 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at h03 h04 h05 h13 h14 h15 h23 h24 h25
  refine not_hollowMatrixThree_sq_eq_one (invol 0 1) (invol 0 2) (invol 1 2) ?_
  have hzero := hinvol.row_sq_expand 0
  have hone := hinvol.row_sq_expand 1
  have htwo := hinvol.row_sq_expand 2
  have hoff := hinvol.offDiag_expand (rowIndex := 0) (colIndex := 1) (by decide)
  rw [hinvol.diagonal_eq_zero 0, h03, h04, h05] at hzero
  rw [hinvol.diagonal_eq_zero 1, hinvol.apply_comm 0 1, h13, h14, h15] at hone
  rw [hinvol.diagonal_eq_zero 2, hinvol.apply_comm 0 2, hinvol.apply_comm 1 2, h23, h24,
    h25] at htwo
  rw [hinvol.diagonal_eq_zero 0, hinvol.diagonal_eq_zero 1, hinvol.apply_comm 1 2, h03, h04,
    h05] at hoff
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [hollowMatrixThree, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply] <;>
    norm_num <;>
    nlinarith [hzero, hone, htwo, hoff]

/-! ### The product complement law -/

/-- The cube of the intertwining, pushed across the cross block three times. -/
theorem frontBlock_cube_mul_crossBlock (hinvol : IsHollowInvolution invol) :
    frontBlock invol ^ 3 * crossBlock invol = -(crossBlock invol * backBlock invol ^ 3) := by
  have hstep := hinvol.frontBlock_mul_crossBlock
  set frontMatrix := frontBlock invol with hfrontDef
  set backMatrix := backBlock invol with hbackDef
  set crossMatrix := crossBlock invol with hcrossDef
  have hfirst : frontMatrix ^ 3 * crossMatrix
      = frontMatrix * (frontMatrix * (frontMatrix * crossMatrix)) := by noncomm_ring
  rw [hfirst, hstep]
  have hsecond : frontMatrix * (frontMatrix * -(crossMatrix * backMatrix))
      = -(frontMatrix * (frontMatrix * crossMatrix * backMatrix)) := by noncomm_ring
  rw [hsecond, hstep]
  have hthird : -(frontMatrix * (-(crossMatrix * backMatrix) * backMatrix))
      = frontMatrix * crossMatrix * (backMatrix * backMatrix) := by noncomm_ring
  rw [hthird, hstep]
  noncomm_ring

/-- **THE PRODUCT COMPLEMENT LAW, standard partition.**  The two triples of a
partition carry OPPOSITE edge products.  Unconditional. -/
theorem tripleEdgeProduct_front_add_back (hinvol : IsHollowInvolution invol) :
    tripleEdgeProduct invol 0 1 2 + tripleEdgeProduct invol 3 4 5 = 0 := by
  obtain ⟨rowIndex, colIndex, hne⟩ := hinvol.exists_crossBlock_ne_zero
  have hcube := hinvol.frontBlock_cube_mul_crossBlock
  have hstep := hinvol.frontBlock_mul_crossBlock
  rw [show frontBlock invol ^ 3
      = (invol 0 1 ^ 2 + invol 0 2 ^ 2 + invol 1 2 ^ 2) • frontBlock invol
        + (2 * (invol 0 1 * invol 0 2 * invol 1 2)) • (1 : Matrix (Fin 3) (Fin 3) ℝ) from
      hollowMatrixThree_cube _ _ _,
    show backBlock invol ^ 3
      = (invol 3 4 ^ 2 + invol 3 5 ^ 2 + invol 4 5 ^ 2) • backBlock invol
        + (2 * (invol 3 4 * invol 3 5 * invol 4 5)) • (1 : Matrix (Fin 3) (Fin 3) ℝ) from
      hollowMatrixThree_cube _ _ _] at hcube
  have hentry := congrFun (congrFun hcube rowIndex) colIndex
  have hstepEntry := congrFun (congrFun hstep rowIndex) colIndex
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul] at hentry
  simp only [Matrix.neg_apply] at hstepEntry
  have henergy := hinvol.tripleEnergy_front_eq_back
  simp only [tripleEnergy] at henergy
  rw [hstepEntry, ← henergy] at hentry
  have hfactor : (tripleEdgeProduct invol 0 1 2 + tripleEdgeProduct invol 3 4 5)
      * (2 * crossBlock invol rowIndex colIndex) = 0 := by
    simp only [tripleEdgeProduct]
    linarith [hentry]
  rcases mul_eq_zero.mp hfactor with hsum | hcrossZero
  · exact hsum
  · exact absurd (by linarith [hcrossZero] : crossBlock invol rowIndex colIndex = 0) hne

/-! ### Transport along a relabelling

A hollow involution stays one after conjugating by a permutation of the labels, so
the two standard-partition laws hold at EVERY partition of the six labels. -/

/-- A hollow involution conjugated by a permutation is a hollow involution. -/
theorem submatrix_perm (hinvol : IsHollowInvolution invol) (relabel : Equiv.Perm (Fin 6)) :
    IsHollowInvolution (invol.submatrix relabel relabel) where
  symmetric := by
    rw [Matrix.transpose_submatrix, hinvol.symmetric]
  square_eq_one := by
    rw [Matrix.submatrix_mul_equiv invol invol relabel relabel relabel, hinvol.square_eq_one]
    ext rowIndex colIndex
    by_cases hcase : rowIndex = colIndex
    · subst hcase; simp
    · simp [Matrix.one_apply_ne hcase, Matrix.one_apply_ne (relabel.injective.ne hcase)]
  diagonal_eq_zero := fun index => hinvol.diagonal_eq_zero (relabel index)

/-- **THE ENERGY COMPLEMENT LAW, every partition.** -/
theorem tripleEnergy_perm_eq (hinvol : IsHollowInvolution invol) (relabel : Equiv.Perm (Fin 6)) :
    tripleEnergy invol (relabel 0) (relabel 1) (relabel 2)
      = tripleEnergy invol (relabel 3) (relabel 4) (relabel 5) := by
  have htransported := (hinvol.submatrix_perm relabel).tripleEnergy_front_eq_back
  simpa [tripleEnergy, Matrix.submatrix_apply] using htransported

/-- **THE PRODUCT COMPLEMENT LAW, every partition.**  For every splitting of the six
labels into two triples, the two edge products are negatives of one another. -/
theorem tripleEdgeProduct_perm_add_eq_zero (hinvol : IsHollowInvolution invol)
    (relabel : Equiv.Perm (Fin 6)) :
    tripleEdgeProduct invol (relabel 0) (relabel 1) (relabel 2)
      + tripleEdgeProduct invol (relabel 3) (relabel 4) (relabel 5) = 0 := by
  have htransported := (hinvol.submatrix_perm relabel).tripleEdgeProduct_front_add_back
  simpa [tripleEdgeProduct, Matrix.submatrix_apply] using htransported

/-- **EVERY COMPLEMENTARY PAIR OFFERS A COHERENT SIDE.**  One of the two triples of
any partition has a nonnegative edge product, since they sum to zero. -/
theorem exists_nonneg_tripleEdgeProduct_perm (hinvol : IsHollowInvolution invol)
    (relabel : Equiv.Perm (Fin 6)) :
    0 ≤ tripleEdgeProduct invol (relabel 0) (relabel 1) (relabel 2)
      ∨ 0 ≤ tripleEdgeProduct invol (relabel 3) (relabel 4) (relabel 5) := by
  have hsum := hinvol.tripleEdgeProduct_perm_add_eq_zero relabel
  by_cases hnonneg : 0 ≤ tripleEdgeProduct invol (relabel 0) (relabel 1) (relabel 2)
  · exact Or.inl hnonneg
  · exact Or.inr (by push Not at hnonneg; linarith [hsum])


/-! ### The ten complementary pairs

Each of the ten splittings of the six labels into two triples is one permutation
away from the standard one, so the two laws above hold at every pair.  The edge
product is symmetric in its three labels once the matrix is, which is what puts the
transported triples back into increasing order. -/

/-- The edge product is symmetric in its first two labels. -/
theorem tripleEdgeProduct_swap_left (hinvol : IsHollowInvolution invol)
    (first second third : Fin 6) :
    tripleEdgeProduct invol first second third = tripleEdgeProduct invol second first third := by
  simp only [tripleEdgeProduct]
  rw [hinvol.apply_comm first second, hinvol.apply_comm third second,
    hinvol.apply_comm third first]
  ring

/-- The edge product is symmetric in its last two labels. -/
theorem tripleEdgeProduct_swap_right (hinvol : IsHollowInvolution invol)
    (first second third : Fin 6) :
    tripleEdgeProduct invol first second third = tripleEdgeProduct invol first third second := by
  simp only [tripleEdgeProduct]
  rw [hinvol.apply_comm second third]
  ring

/-- The edge product is symmetric in its outer labels. -/
theorem tripleEdgeProduct_swap_outer (hinvol : IsHollowInvolution invol)
    (first second third : Fin 6) :
    tripleEdgeProduct invol first second third = tripleEdgeProduct invol third second first := by
  rw [hinvol.tripleEdgeProduct_swap_left, hinvol.tripleEdgeProduct_swap_right,
    hinvol.tripleEdgeProduct_swap_left]

theorem pair_012 (hinvol : IsHollowInvolution invol) :
    tripleEdgeProduct invol 0 1 2 + tripleEdgeProduct invol 3 4 5 = 0 :=
  hinvol.tripleEdgeProduct_front_add_back

theorem pair_013 (hinvol : IsHollowInvolution invol) :
    tripleEdgeProduct invol 0 1 3 + tripleEdgeProduct invol 2 4 5 = 0 := by
  have hpair := hinvol.tripleEdgeProduct_perm_add_eq_zero (Equiv.swap 2 3)
  norm_num [show (Equiv.swap (2 : Fin 6) 3) 0 = 0 from by decide,
    show (Equiv.swap (2 : Fin 6) 3) 1 = 1 from by decide,
    show (Equiv.swap (2 : Fin 6) 3) 2 = 3 from by decide,
    show (Equiv.swap (2 : Fin 6) 3) 3 = 2 from by decide,
    show (Equiv.swap (2 : Fin 6) 3) 4 = 4 from by decide,
    show (Equiv.swap (2 : Fin 6) 3) 5 = 5 from by decide] at hpair
  exact hpair

theorem pair_014 (hinvol : IsHollowInvolution invol) :
    tripleEdgeProduct invol 0 1 4 + tripleEdgeProduct invol 2 3 5 = 0 := by
  have hpair := hinvol.tripleEdgeProduct_perm_add_eq_zero (Equiv.swap 2 4)
  norm_num [show (Equiv.swap (2 : Fin 6) 4) 0 = 0 from by decide,
    show (Equiv.swap (2 : Fin 6) 4) 1 = 1 from by decide,
    show (Equiv.swap (2 : Fin 6) 4) 2 = 4 from by decide,
    show (Equiv.swap (2 : Fin 6) 4) 3 = 3 from by decide,
    show (Equiv.swap (2 : Fin 6) 4) 4 = 2 from by decide,
    show (Equiv.swap (2 : Fin 6) 4) 5 = 5 from by decide] at hpair
  rw [hinvol.tripleEdgeProduct_swap_left 3 2 5] at hpair
  exact hpair

theorem pair_015 (hinvol : IsHollowInvolution invol) :
    tripleEdgeProduct invol 0 1 5 + tripleEdgeProduct invol 2 3 4 = 0 := by
  have hpair := hinvol.tripleEdgeProduct_perm_add_eq_zero (Equiv.swap 2 5)
  norm_num [show (Equiv.swap (2 : Fin 6) 5) 0 = 0 from by decide,
    show (Equiv.swap (2 : Fin 6) 5) 1 = 1 from by decide,
    show (Equiv.swap (2 : Fin 6) 5) 2 = 5 from by decide,
    show (Equiv.swap (2 : Fin 6) 5) 3 = 3 from by decide,
    show (Equiv.swap (2 : Fin 6) 5) 4 = 4 from by decide,
    show (Equiv.swap (2 : Fin 6) 5) 5 = 2 from by decide] at hpair
  rw [hinvol.tripleEdgeProduct_swap_outer 3 4 2, hinvol.tripleEdgeProduct_swap_right 2 4 3] at hpair
  exact hpair

theorem pair_023 (hinvol : IsHollowInvolution invol) :
    tripleEdgeProduct invol 0 2 3 + tripleEdgeProduct invol 1 4 5 = 0 := by
  have hpair := hinvol.tripleEdgeProduct_perm_add_eq_zero (Equiv.swap 1 3)
  norm_num [show (Equiv.swap (1 : Fin 6) 3) 0 = 0 from by decide,
    show (Equiv.swap (1 : Fin 6) 3) 1 = 3 from by decide,
    show (Equiv.swap (1 : Fin 6) 3) 2 = 2 from by decide,
    show (Equiv.swap (1 : Fin 6) 3) 3 = 1 from by decide,
    show (Equiv.swap (1 : Fin 6) 3) 4 = 4 from by decide,
    show (Equiv.swap (1 : Fin 6) 3) 5 = 5 from by decide] at hpair
  rw [hinvol.tripleEdgeProduct_swap_right 0 3 2] at hpair
  exact hpair

theorem pair_024 (hinvol : IsHollowInvolution invol) :
    tripleEdgeProduct invol 0 2 4 + tripleEdgeProduct invol 1 3 5 = 0 := by
  have hpair := hinvol.tripleEdgeProduct_perm_add_eq_zero (Equiv.swap 1 4)
  norm_num [show (Equiv.swap (1 : Fin 6) 4) 0 = 0 from by decide,
    show (Equiv.swap (1 : Fin 6) 4) 1 = 4 from by decide,
    show (Equiv.swap (1 : Fin 6) 4) 2 = 2 from by decide,
    show (Equiv.swap (1 : Fin 6) 4) 3 = 3 from by decide,
    show (Equiv.swap (1 : Fin 6) 4) 4 = 1 from by decide,
    show (Equiv.swap (1 : Fin 6) 4) 5 = 5 from by decide] at hpair
  rw [hinvol.tripleEdgeProduct_swap_right 0 4 2, hinvol.tripleEdgeProduct_swap_left 3 1 5] at hpair
  exact hpair

theorem pair_025 (hinvol : IsHollowInvolution invol) :
    tripleEdgeProduct invol 0 2 5 + tripleEdgeProduct invol 1 3 4 = 0 := by
  have hpair := hinvol.tripleEdgeProduct_perm_add_eq_zero (Equiv.swap 1 5)
  norm_num [show (Equiv.swap (1 : Fin 6) 5) 0 = 0 from by decide,
    show (Equiv.swap (1 : Fin 6) 5) 1 = 5 from by decide,
    show (Equiv.swap (1 : Fin 6) 5) 2 = 2 from by decide,
    show (Equiv.swap (1 : Fin 6) 5) 3 = 3 from by decide,
    show (Equiv.swap (1 : Fin 6) 5) 4 = 4 from by decide,
    show (Equiv.swap (1 : Fin 6) 5) 5 = 1 from by decide] at hpair
  rw [hinvol.tripleEdgeProduct_swap_right 0 5 2, hinvol.tripleEdgeProduct_swap_outer 3 4 1,
    hinvol.tripleEdgeProduct_swap_right 1 4 3] at hpair
  exact hpair

theorem pair_034 (hinvol : IsHollowInvolution invol) :
    tripleEdgeProduct invol 0 3 4 + tripleEdgeProduct invol 1 2 5 = 0 := by
  have hpair := hinvol.tripleEdgeProduct_perm_add_eq_zero (Equiv.swap 1 3 * Equiv.swap 2 4)
  norm_num [show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 0 = 0 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 1 = 3 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 2 = 4 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 3 = 1 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 4 = 2 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 5 = 5 from by decide] at hpair
  exact hpair

theorem pair_035 (hinvol : IsHollowInvolution invol) :
    tripleEdgeProduct invol 0 3 5 + tripleEdgeProduct invol 1 2 4 = 0 := by
  have hpair := hinvol.tripleEdgeProduct_perm_add_eq_zero (Equiv.swap 1 3 * Equiv.swap 2 5)
  norm_num [show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 0 = 0 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 1 = 3 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 2 = 5 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 3 = 1 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 4 = 4 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 5 = 2 from by decide] at hpair
  rw [hinvol.tripleEdgeProduct_swap_right 1 4 2] at hpair
  exact hpair

theorem pair_045 (hinvol : IsHollowInvolution invol) :
    tripleEdgeProduct invol 0 4 5 + tripleEdgeProduct invol 1 2 3 = 0 := by
  have hpair := hinvol.tripleEdgeProduct_perm_add_eq_zero (Equiv.swap 1 4 * Equiv.swap 2 5)
  norm_num [show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 0 = 0 from by decide,
    show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 1 = 4 from by decide,
    show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 2 = 5 from by decide,
    show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 3 = 3 from by decide,
    show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 4 = 1 from by decide,
    show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 5 = 2 from by decide] at hpair
  rw [hinvol.tripleEdgeProduct_swap_left 3 1 2, hinvol.tripleEdgeProduct_swap_right 1 3 2] at hpair
  exact hpair

/-- **THE TWENTY EDGE PRODUCTS CANCEL.**  The ten complementary pairs each sum to
zero, so the total over all twenty triples vanishes.  No trace identity, no
Cauchy-Binet: it is the pairing alone. -/
theorem totalTripleEdgeProduct_eq_zero (hinvol : IsHollowInvolution invol) :
    totalTripleEdgeProduct invol = 0 := by
  simp only [totalTripleEdgeProduct]
  linarith [hinvol.pair_012, hinvol.pair_013, hinvol.pair_014, hinvol.pair_015,
    hinvol.pair_023, hinvol.pair_024, hinvol.pair_025, hinvol.pair_034, hinvol.pair_035,
    hinvol.pair_045]

end IsHollowInvolution

/-! ## 4. The twenty shifted determinants

The cell of a triple is the nonnegativity set of `Gtz.slackDeterminantThree` at the
capacities `1 - nu`, so the sum of the twenty determinants is the exact averaging
statistic.  It splits into a part that reads only the capacities, a part that reads
only the pair energies, and the edge-product total that section 3 kills. -/

/-- The third elementary symmetric function of the six capacities. -/
noncomputable def elemSymmThreeSix (cap : Fin 6 → ℝ) : ℝ :=
  cap 0 * cap 1 * cap 2 + cap 0 * cap 1 * cap 3 + cap 0 * cap 1 * cap 4
    + cap 0 * cap 1 * cap 5 + cap 0 * cap 2 * cap 3 + cap 0 * cap 2 * cap 4
    + cap 0 * cap 2 * cap 5 + cap 0 * cap 3 * cap 4 + cap 0 * cap 3 * cap 5
    + cap 0 * cap 4 * cap 5 + cap 1 * cap 2 * cap 3 + cap 1 * cap 2 * cap 4
    + cap 1 * cap 2 * cap 5 + cap 1 * cap 3 * cap 4 + cap 1 * cap 3 * cap 5
    + cap 1 * cap 4 * cap 5 + cap 2 * cap 3 * cap 4 + cap 2 * cap 3 * cap 5
    + cap 2 * cap 4 * cap 5 + cap 3 * cap 4 * cap 5

/-- The pair energies, each weighted by the capacity total OUTSIDE its own pair. -/
noncomputable def weightedPairEnergy (gram : Matrix (Fin 6) (Fin 6) ℝ)
    (cap : Fin 6 → ℝ) (capTotal : ℝ) : ℝ :=
  gram 0 1 ^ 2 * (capTotal - cap 0 - cap 1) + gram 0 2 ^ 2 * (capTotal - cap 0 - cap 2)
    + gram 0 3 ^ 2 * (capTotal - cap 0 - cap 3) + gram 0 4 ^ 2 * (capTotal - cap 0 - cap 4)
    + gram 0 5 ^ 2 * (capTotal - cap 0 - cap 5) + gram 1 2 ^ 2 * (capTotal - cap 1 - cap 2)
    + gram 1 3 ^ 2 * (capTotal - cap 1 - cap 3) + gram 1 4 ^ 2 * (capTotal - cap 1 - cap 4)
    + gram 1 5 ^ 2 * (capTotal - cap 1 - cap 5) + gram 2 3 ^ 2 * (capTotal - cap 2 - cap 3)
    + gram 2 4 ^ 2 * (capTotal - cap 2 - cap 4) + gram 2 5 ^ 2 * (capTotal - cap 2 - cap 5)
    + gram 3 4 ^ 2 * (capTotal - cap 3 - cap 4) + gram 3 5 ^ 2 * (capTotal - cap 3 - cap 5)
    + gram 4 5 ^ 2 * (capTotal - cap 4 - cap 5)

/-- **THE TWENTY SHIFTED DETERMINANTS**, the averaging statistic of the covering. -/
noncomputable def totalShiftedTripleDet (gram : Matrix (Fin 6) (Fin 6) ℝ)
    (cap : Fin 6 → ℝ) : ℝ :=
  slackDeterminantThree (cap 0) (cap 1) (cap 2) (gram 0 1) (gram 0 2) (gram 1 2)
    + slackDeterminantThree (cap 0) (cap 1) (cap 3) (gram 0 1) (gram 0 3) (gram 1 3)
    + slackDeterminantThree (cap 0) (cap 1) (cap 4) (gram 0 1) (gram 0 4) (gram 1 4)
    + slackDeterminantThree (cap 0) (cap 1) (cap 5) (gram 0 1) (gram 0 5) (gram 1 5)
    + slackDeterminantThree (cap 0) (cap 2) (cap 3) (gram 0 2) (gram 0 3) (gram 2 3)
    + slackDeterminantThree (cap 0) (cap 2) (cap 4) (gram 0 2) (gram 0 4) (gram 2 4)
    + slackDeterminantThree (cap 0) (cap 2) (cap 5) (gram 0 2) (gram 0 5) (gram 2 5)
    + slackDeterminantThree (cap 0) (cap 3) (cap 4) (gram 0 3) (gram 0 4) (gram 3 4)
    + slackDeterminantThree (cap 0) (cap 3) (cap 5) (gram 0 3) (gram 0 5) (gram 3 5)
    + slackDeterminantThree (cap 0) (cap 4) (cap 5) (gram 0 4) (gram 0 5) (gram 4 5)
    + slackDeterminantThree (cap 1) (cap 2) (cap 3) (gram 1 2) (gram 1 3) (gram 2 3)
    + slackDeterminantThree (cap 1) (cap 2) (cap 4) (gram 1 2) (gram 1 4) (gram 2 4)
    + slackDeterminantThree (cap 1) (cap 2) (cap 5) (gram 1 2) (gram 1 5) (gram 2 5)
    + slackDeterminantThree (cap 1) (cap 3) (cap 4) (gram 1 3) (gram 1 4) (gram 3 4)
    + slackDeterminantThree (cap 1) (cap 3) (cap 5) (gram 1 3) (gram 1 5) (gram 3 5)
    + slackDeterminantThree (cap 1) (cap 4) (cap 5) (gram 1 4) (gram 1 5) (gram 4 5)
    + slackDeterminantThree (cap 2) (cap 3) (cap 4) (gram 2 3) (gram 2 4) (gram 3 4)
    + slackDeterminantThree (cap 2) (cap 3) (cap 5) (gram 2 3) (gram 2 5) (gram 3 5)
    + slackDeterminantThree (cap 2) (cap 4) (cap 5) (gram 2 4) (gram 2 5) (gram 4 5)
    + slackDeterminantThree (cap 3) (cap 4) (cap 5) (gram 3 4) (gram 3 5) (gram 4 5)

/-- **THE SPLIT**, a polynomial identity with no hypothesis: each pair sits in exactly
four triples, so the weighted energies regroup by pair. -/
theorem totalShiftedTripleDet_split (gram : Matrix (Fin 6) (Fin 6) ℝ) (cap : Fin 6 → ℝ) :
    totalShiftedTripleDet gram cap
      = elemSymmThreeSix cap
        - weightedPairEnergy gram cap (cap 0 + cap 1 + cap 2 + cap 3 + cap 4 + cap 5)
        + 2 * totalTripleEdgeProduct gram := by
  simp only [totalShiftedTripleDet, elemSymmThreeSix, weightedPairEnergy,
    totalTripleEdgeProduct, tripleEdgeProduct, slackDeterminantThree]
  ring

namespace IsHollowInvolution

variable {invol : Matrix (Fin 6) (Fin 6) ℝ}

/-- **THE FIFTEEN PAIR ENERGIES TOTAL THREE.**  Six row budgets counting every pair
twice. -/
theorem pairEnergyTotal_eq_three (hinvol : IsHollowInvolution invol) :
    invol 0 1 ^ 2 + invol 0 2 ^ 2 + invol 0 3 ^ 2 + invol 0 4 ^ 2 + invol 0 5 ^ 2 + invol 1 2 ^ 2 + invol 1 3 ^ 2 + invol 1 4 ^ 2 + invol 1 5 ^ 2 + invol 2 3 ^ 2 + invol 2 4 ^ 2 + invol 2 5 ^ 2 + invol 3 4 ^ 2 + invol 3 5 ^ 2 + invol 4 5 ^ 2 = 3 := by
  have hrow0 := hinvol.row_sq_expand 0
  rw [hinvol.diagonal_eq_zero 0] at hrow0
  have hrow1 := hinvol.row_sq_expand 1
  rw [hinvol.diagonal_eq_zero 1, hinvol.apply_comm 0 1] at hrow1
  have hrow2 := hinvol.row_sq_expand 2
  rw [hinvol.diagonal_eq_zero 2, hinvol.apply_comm 0 2, hinvol.apply_comm 1 2] at hrow2
  have hrow3 := hinvol.row_sq_expand 3
  rw [hinvol.diagonal_eq_zero 3, hinvol.apply_comm 0 3, hinvol.apply_comm 1 3, hinvol.apply_comm 2 3] at hrow3
  have hrow4 := hinvol.row_sq_expand 4
  rw [hinvol.diagonal_eq_zero 4, hinvol.apply_comm 0 4, hinvol.apply_comm 1 4, hinvol.apply_comm 2 4, hinvol.apply_comm 3 4] at hrow4
  have hrow5 := hinvol.row_sq_expand 5
  rw [hinvol.diagonal_eq_zero 5, hinvol.apply_comm 0 5, hinvol.apply_comm 1 5, hinvol.apply_comm 2 5, hinvol.apply_comm 3 5, hinvol.apply_comm 4 5] at hrow5
  linarith [hrow0, hrow1, hrow2, hrow3, hrow4, hrow5]

/-- **THE WEIGHTED PAIR ENERGY COLLAPSES.**  Each pair energy weighted by the capacity
outside it totals exactly twice the capacity total — a statement about the row law
alone, with no reference to the capacities beyond their sum. -/
theorem weightedPairEnergy_eq (hinvol : IsHollowInvolution invol) (cap : Fin 6 → ℝ) :
    weightedPairEnergy invol cap (cap 0 + cap 1 + cap 2 + cap 3 + cap 4 + cap 5) = 2 * (cap 0 + cap 1 + cap 2 + cap 3 + cap 4 + cap 5) := by
  have hpairTotal := hinvol.pairEnergyTotal_eq_three
  have hrow0 := hinvol.row_sq_expand 0
  rw [hinvol.diagonal_eq_zero 0] at hrow0
  have hrow1 := hinvol.row_sq_expand 1
  rw [hinvol.diagonal_eq_zero 1, hinvol.apply_comm 0 1] at hrow1
  have hrow2 := hinvol.row_sq_expand 2
  rw [hinvol.diagonal_eq_zero 2, hinvol.apply_comm 0 2, hinvol.apply_comm 1 2] at hrow2
  have hrow3 := hinvol.row_sq_expand 3
  rw [hinvol.diagonal_eq_zero 3, hinvol.apply_comm 0 3, hinvol.apply_comm 1 3, hinvol.apply_comm 2 3] at hrow3
  have hrow4 := hinvol.row_sq_expand 4
  rw [hinvol.diagonal_eq_zero 4, hinvol.apply_comm 0 4, hinvol.apply_comm 1 4, hinvol.apply_comm 2 4, hinvol.apply_comm 3 4] at hrow4
  have hrow5 := hinvol.row_sq_expand 5
  rw [hinvol.diagonal_eq_zero 5, hinvol.apply_comm 0 5, hinvol.apply_comm 1 5, hinvol.apply_comm 2 5, hinvol.apply_comm 3 5, hinvol.apply_comm 4 5] at hrow5
  have hnorm0 : invol 0 1 ^ 2 + invol 0 2 ^ 2 + invol 0 3 ^ 2 + invol 0 4 ^ 2 + invol 0 5 ^ 2 = 1 := by linarith [hrow0]
  have hnorm1 : invol 0 1 ^ 2 + invol 1 2 ^ 2 + invol 1 3 ^ 2 + invol 1 4 ^ 2 + invol 1 5 ^ 2 = 1 := by linarith [hrow1]
  have hnorm2 : invol 0 2 ^ 2 + invol 1 2 ^ 2 + invol 2 3 ^ 2 + invol 2 4 ^ 2 + invol 2 5 ^ 2 = 1 := by linarith [hrow2]
  have hnorm3 : invol 0 3 ^ 2 + invol 1 3 ^ 2 + invol 2 3 ^ 2 + invol 3 4 ^ 2 + invol 3 5 ^ 2 = 1 := by linarith [hrow3]
  have hnorm4 : invol 0 4 ^ 2 + invol 1 4 ^ 2 + invol 2 4 ^ 2 + invol 3 4 ^ 2 + invol 4 5 ^ 2 = 1 := by linarith [hrow4]
  have hnorm5 : invol 0 5 ^ 2 + invol 1 5 ^ 2 + invol 2 5 ^ 2 + invol 3 5 ^ 2 + invol 4 5 ^ 2 = 1 := by linarith [hrow5]
  simp only [weightedPairEnergy]
  linear_combination (cap 0 + cap 1 + cap 2 + cap 3 + cap 4 + cap 5) * hpairTotal - cap 0 * hnorm0 - cap 1 * hnorm1 - cap 2 * hnorm2 - cap 3 * hnorm3 - cap 4 * hnorm4 - cap 5 * hnorm5

/-- **THE AVERAGING NO-GO.**  The twenty shifted determinants total
`e_3(cap) - 2 (sum cap)`: the edge products cancel in complementary pairs and the
weighted energies collapse by the row law, so the average cell determinant reads only
the capacities.  Nothing about the frame survives. -/
theorem totalShiftedTripleDet_eq (hinvol : IsHollowInvolution invol) (cap : Fin 6 → ℝ) :
    totalShiftedTripleDet invol cap = elemSymmThreeSix cap - 2 * (cap 0 + cap 1 + cap 2 + cap 3 + cap 4 + cap 5) := by
  rw [totalShiftedTripleDet_split, hinvol.weightedPairEnergy_eq,
    hinvol.totalTripleEdgeProduct_eq_zero]
  ring

/-- **AT THE CENTRE OF THE POLYTOPE THE TOTAL IS NEGATIVE**: `-56/27`, for EVERY
hollow involution.  So the mean cell determinant at the uniform point is
`-14/135 < 0`, and no averaging argument over the twenty triples can produce a
covering.  The campaign knew this number at one point of one coordinate system; it
is here a statement about the whole family. -/
theorem totalShiftedTripleDet_uniform (hinvol : IsHollowInvolution invol) :
    totalShiftedTripleDet invol (fun _ => 2 / 3) = -(56 / 27) := by
  rw [hinvol.totalShiftedTripleDet_eq]
  simp only [elemSymmThreeSix]
  norm_num

end IsHollowInvolution

/-! ## 5. The tight Gram, its block determinants, and the sign-aware cell

A tight Gram is one plus a hollow involution, so every law above applies to the
covering problem verbatim. -/

/-- **THE BRIDGE.**  `Gamma - 1` is a hollow involution whenever `Gamma` is a tight
Gram: `(Gamma - 1)^2 = Gamma^2 - 2 Gamma + 1 = 1`. -/
theorem IsTightGramSix.isHollowInvolution_sub_one {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) : IsHollowInvolution (gram - 1) where
  symmetric := by
    have hsymm : gramᵀ = gram := by
      ext rowIndex colIndex
      exact hgram.comm rowIndex colIndex
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymm]
  square_eq_one := by
    have hexpand : (gram - 1) * (gram - 1) = gram * gram - gram - gram + 1 := by noncomm_ring
    rw [hexpand, hgram.idem, two_smul]
    abel
  diagonal_eq_zero := fun index => by
    simp [Matrix.sub_apply, hgram.unit index]

/-- Off the diagonal the involution and the Gram agree. -/
theorem IsTightGramSix.sub_one_apply_of_ne {gram : Matrix (Fin 6) (Fin 6) ℝ}
    {rowIndex colIndex : Fin 6} (hdistinct : rowIndex ≠ colIndex) :
    (gram - 1) rowIndex colIndex = gram rowIndex colIndex := by
  simp [Matrix.sub_apply, Matrix.one_apply_ne hdistinct]

/-- **THE TRIPLE BLOCK OF A TIGHT GRAM** is one plus the hollow block of its
correlations. -/
theorem IsTightGramSix.submatrix_eq_one_add_hollow {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) (first second third : Fin 6) :
    gram.submatrix ![first, second, third] ![first, second, third]
      = 1 + hollowMatrixThree (gram first second) (gram first third) (gram second third) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [hollowMatrixThree, hgram.unit, hgram.comm first second,
      hgram.comm first third, hgram.comm second third]

/-- **THE BLOCK DETERMINANT**: `det Gamma[T] = 1 - E_T + 2 P_T`. -/
theorem IsTightGramSix.det_gramBlock {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) (first second third : Fin 6) :
    (gram.submatrix ![first, second, third] ![first, second, third]).det
      = 1 - tripleEnergy gram first second third
        + 2 * tripleEdgeProduct gram first second third := by
  rw [hgram.submatrix_eq_one_add_hollow, det_one_add_hollowMatrixThree]
  simp only [tripleEnergy, tripleEdgeProduct]

/-- **THE CO-BLOCK DETERMINANT**: `det (2 . 1 - Gamma)[T] = 1 - E_T - 2 P_T`. -/
theorem IsTightGramSix.det_coGramBlock {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    (((2 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - gram).submatrix
        ![first, second, third] ![first, second, third]).det
      = 1 - tripleEnergy gram first second third
        - 2 * tripleEdgeProduct gram first second third := by
  have hshape : ((2 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - gram).submatrix
        ![first, second, third] ![first, second, third]
      = 1 - hollowMatrixThree (gram first second) (gram first third) (gram second third) := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [hollowMatrixThree, Matrix.smul_apply, Matrix.sub_apply,
        hgram.unit, hgram.comm first second, hgram.comm first third, hgram.comm second third,
        hfirstSecond, hfirstThird, hsecondThird, Ne.symm hfirstSecond, Ne.symm hfirstThird,
        Ne.symm hsecondThird] <;> norm_num
  rw [hshape, det_one_sub_hollowMatrixThree]
  simp only [tripleEnergy, tripleEdgeProduct]

/-- **THE COMPLEMENTARY MINOR IDENTITY, standard partition**, derived from the two
complement laws rather than assumed: the Gram minor at a triple equals the co-Gram
minor at its complement.  For `Gamma = 2 P` with `P` a rank-three projection this is
`det P[T] = det (1 - P)[T']`, which the campaign has never had in kernel. -/
theorem IsTightGramSix.det_gramBlock_eq_det_coGramBlock_compl
    {gram : Matrix (Fin 6) (Fin 6) ℝ} (hgram : IsTightGramSix gram) :
    (gram.submatrix ![0, 1, 2] ![0, 1, 2]).det
      = (((2 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - gram).submatrix
          ![3, 4, 5] ![3, 4, 5]).det := by
  have hinvol := hgram.isHollowInvolution_sub_one
  have henergy := hinvol.tripleEnergy_front_eq_back
  have hproduct := hinvol.tripleEdgeProduct_front_add_back
  simp only [tripleEnergy, tripleEdgeProduct,
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (0 : Fin 6) ≠ 1),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (0 : Fin 6) ≠ 2),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (1 : Fin 6) ≠ 2),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (3 : Fin 6) ≠ 4),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (3 : Fin 6) ≠ 5),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (4 : Fin 6) ≠ 5)] at henergy hproduct
  rw [hgram.det_gramBlock, hgram.det_coGramBlock (by decide) (by decide) (by decide)]
  simp only [tripleEnergy, tripleEdgeProduct]
  linarith [henergy, hproduct]

/-- **THE COMPLEMENT SUM OF THE TWO BLOCK DETERMINANTS**, sign-free: the edge products
cancel, so the pair total reads only the shared energy. -/
theorem IsTightGramSix.det_gramBlock_add_compl {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) :
    (gram.submatrix ![0, 1, 2] ![0, 1, 2]).det + (gram.submatrix ![3, 4, 5] ![3, 4, 5]).det
      = 2 * (1 - tripleEnergy gram 0 1 2) := by
  have hinvol := hgram.isHollowInvolution_sub_one
  have henergy := hinvol.tripleEnergy_front_eq_back
  have hproduct := hinvol.tripleEdgeProduct_front_add_back
  simp only [tripleEnergy, tripleEdgeProduct,
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (0 : Fin 6) ≠ 1),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (0 : Fin 6) ≠ 2),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (1 : Fin 6) ≠ 2),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (3 : Fin 6) ≠ 4),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (3 : Fin 6) ≠ 5),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (4 : Fin 6) ≠ 5)] at henergy hproduct
  rw [hgram.det_gramBlock, hgram.det_gramBlock]
  simp only [tripleEnergy, tripleEdgeProduct]
  linarith [henergy, hproduct]

/-! ### The sign-aware cell -/

/-- **THE SIGN-AWARE CELL.**  When the edge product is NONNEGATIVE the cross term
works FOR the certificate, so the determinant clause needs only its sign-free part.
Every sign-blind cell in the campaign pays `2 |P|` here instead of collecting it. -/
theorem posSemidef_slackHollowThree_of_nonneg_product {capFirst capSecond capThird
    edgeFirst edgeSecond edgeThird : ℝ} (hcapFirst : 0 ≤ capFirst) (hcapSecond : 0 ≤ capSecond)
    (hcapThird : 0 ≤ capThird) (hpairFirst : edgeFirst ^ 2 ≤ capFirst * capSecond)
    (hpairSecond : edgeSecond ^ 2 ≤ capFirst * capThird)
    (hpairThird : edgeThird ^ 2 ≤ capSecond * capThird)
    (hproduct : 0 ≤ edgeFirst * edgeSecond * edgeThird)
    (hsignFree : capFirst * edgeThird ^ 2 + capSecond * edgeSecond ^ 2 + capThird * edgeFirst ^ 2
      ≤ capFirst * capSecond * capThird) :
    (slackHollowThree capFirst capSecond capThird edgeFirst edgeSecond edgeThird).PosSemidef := by
  rw [posSemidef_slackHollowThree_iff_of_nonneg hcapFirst hcapSecond hcapThird]
  refine ⟨hpairFirst, hpairSecond, hpairThird, ?_⟩
  rw [slackDeterminantThree]
  linarith [hsignFree, hproduct]

/-- **THE CRUX CONSTANT AT THE CENTRE.**  At the uniform point `nu == 1/3` the cell of
a triple asks EXACTLY that twice its edge product beat `(2/3) E - 8/27`.  At the
equiangular energy `E = 3/5` that threshold is `14/135`, so a triple there is covered
precisely when its edge product is at least `7/135` — the sharp number the sign route
must produce, and the reason discarding the cross term cannot work at the centre. -/
theorem slackDeterminantThree_uniform_nonneg_iff (edgeFirst edgeSecond edgeThird : ℝ) :
    0 ≤ slackDeterminantThree (2 / 3) (2 / 3) (2 / 3) edgeFirst edgeSecond edgeThird
      ↔ (2 / 3) * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2) - 8 / 27
        ≤ 2 * (edgeFirst * edgeSecond * edgeThird) := by
  rw [slackDeterminantThree]
  constructor <;> intro hbound <;> linarith [hbound]

/-- The equiangular instance of the crux: at energy `3/5` the threshold is `14/135`. -/
theorem slackDeterminantThree_uniform_equiangular {edgeFirst edgeSecond edgeThird : ℝ}
    (henergy : edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2 = 3 / 5) :
    0 ≤ slackDeterminantThree (2 / 3) (2 / 3) (2 / 3) edgeFirst edgeSecond edgeThird
      ↔ 14 / 135 ≤ 2 * (edgeFirst * edgeSecond * edgeThird) := by
  rw [slackDeterminantThree_uniform_nonneg_iff, henergy]
  norm_num

/-! ### The consumer: membership in the shipped cell -/

/-- **THE SIGN-AWARE CELL, AT THE SHIPPED CONSUMER.**  This is the `nu`-coordinate
form of the criterion, so it feeds `Gtz.CoversInvariantLeverageRegion` — the sentence
`Gtz.gtzUniformShareSixThree_iff_forall_coversInvariantLeverageDesignRegion` proves
equivalent to the objective on this stratum — directly. -/
theorem IsTightGramSix.mem_invariantLeverageCell_of_nonneg_product
    {gram : Matrix (Fin 6) (Fin 6) ℝ} (hgram : IsTightGramSix gram)
    (first second third : Fin 6) {invariantLeverage : Fin 6 → ℝ}
    (hcapFirst : invariantLeverage first ≤ 1) (hcapSecond : invariantLeverage second ≤ 1)
    (hcapThird : invariantLeverage third ≤ 1)
    (hpairFirst : gram first second ^ 2
      ≤ (1 - invariantLeverage first) * (1 - invariantLeverage second))
    (hpairSecond : gram first third ^ 2
      ≤ (1 - invariantLeverage first) * (1 - invariantLeverage third))
    (hpairThird : gram second third ^ 2
      ≤ (1 - invariantLeverage second) * (1 - invariantLeverage third))
    (hproduct : 0 ≤ tripleEdgeProduct gram first second third)
    (hsignFree : (1 - invariantLeverage first) * gram second third ^ 2
        + (1 - invariantLeverage second) * gram first third ^ 2
        + (1 - invariantLeverage third) * gram first second ^ 2
      ≤ (1 - invariantLeverage first) * (1 - invariantLeverage second)
        * (1 - invariantLeverage third)) :
    invariantLeverage ∈ invariantLeverageCell gram first second third := by
  rw [mem_invariantLeverageCell_iff_unitComplement_mem_tripleSlackCell gram (hgram.unit first)
    (hgram.unit second) (hgram.unit third) (hgram.comm first second) (hgram.comm first third)
    (hgram.comm second third), mem_tripleSlackCell_iff]
  simp only [unitComplement_apply]
  exact posSemidef_slackHollowThree_of_nonneg_product (by linarith [hcapFirst])
    (by linarith [hcapSecond]) (by linarith [hcapThird]) hpairFirst hpairSecond hpairThird
    hproduct hsignFree

/-- The edge product of a tight Gram is the edge product of its involution. -/
theorem IsTightGramSix.tripleEdgeProduct_sub_one {gram : Matrix (Fin 6) (Fin 6) ℝ}
    {first second third : Fin 6} (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    tripleEdgeProduct (gram - 1) first second third = tripleEdgeProduct gram first second third := by
  simp only [tripleEdgeProduct, IsTightGramSix.sub_one_apply_of_ne hfirstSecond,
    IsTightGramSix.sub_one_apply_of_ne hfirstThird,
    IsTightGramSix.sub_one_apply_of_ne hsecondThird]

/-- **THE COMPLEMENT LAW ON THE GRAM ITSELF.** -/
theorem IsTightGramSix.tripleEdgeProduct_front_add_back {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) :
    tripleEdgeProduct gram 0 1 2 + tripleEdgeProduct gram 3 4 5 = 0 := by
  have hlaw := hgram.isHollowInvolution_sub_one.tripleEdgeProduct_front_add_back
  rwa [IsTightGramSix.tripleEdgeProduct_sub_one (by decide) (by decide) (by decide),
    IsTightGramSix.tripleEdgeProduct_sub_one (by decide) (by decide) (by decide)] at hlaw

/-- **THE SIGN VANISHES FROM THE COVERING.**  One side of a complementary pair is
always coherent, so verifying the SIGN-FREE determinant clause on BOTH sides of one
pair certifies that one of the two cells contains the point — without ever deciding
which side is the coherent one.

This is what the complement law buys the covering problem.  Every certificate the
campaign has built pays `2 |P|` in the determinant clause; here the pair pays it
once, on the side that collects it, and the hypotheses never mention a sign. -/
theorem IsTightGramSix.mem_invariantLeverageCell_front_or_back
    {gram : Matrix (Fin 6) (Fin 6) ℝ} (hgram : IsTightGramSix gram)
    {invariantLeverage : Fin 6 → ℝ} (hcap : ∀ index, invariantLeverage index ≤ 1)
    (hpairFrontOne : gram 0 1 ^ 2 ≤ (1 - invariantLeverage 0) * (1 - invariantLeverage 1))
    (hpairFrontTwo : gram 0 2 ^ 2 ≤ (1 - invariantLeverage 0) * (1 - invariantLeverage 2))
    (hpairFrontThree : gram 1 2 ^ 2 ≤ (1 - invariantLeverage 1) * (1 - invariantLeverage 2))
    (hpairBackOne : gram 3 4 ^ 2 ≤ (1 - invariantLeverage 3) * (1 - invariantLeverage 4))
    (hpairBackTwo : gram 3 5 ^ 2 ≤ (1 - invariantLeverage 3) * (1 - invariantLeverage 5))
    (hpairBackThree : gram 4 5 ^ 2 ≤ (1 - invariantLeverage 4) * (1 - invariantLeverage 5))
    (hfreeFront : (1 - invariantLeverage 0) * gram 1 2 ^ 2
        + (1 - invariantLeverage 1) * gram 0 2 ^ 2 + (1 - invariantLeverage 2) * gram 0 1 ^ 2
      ≤ (1 - invariantLeverage 0) * (1 - invariantLeverage 1) * (1 - invariantLeverage 2))
    (hfreeBack : (1 - invariantLeverage 3) * gram 4 5 ^ 2
        + (1 - invariantLeverage 4) * gram 3 5 ^ 2 + (1 - invariantLeverage 5) * gram 3 4 ^ 2
      ≤ (1 - invariantLeverage 3) * (1 - invariantLeverage 4) * (1 - invariantLeverage 5)) :
    invariantLeverage ∈ invariantLeverageCell gram 0 1 2
      ∨ invariantLeverage ∈ invariantLeverageCell gram 3 4 5 := by
  have hsum := hgram.tripleEdgeProduct_front_add_back
  by_cases hcoherent : 0 ≤ tripleEdgeProduct gram 0 1 2
  · exact Or.inl (hgram.mem_invariantLeverageCell_of_nonneg_product 0 1 2 (hcap 0) (hcap 1)
      (hcap 2) hpairFrontOne hpairFrontTwo hpairFrontThree hcoherent hfreeFront)
  · refine Or.inr (hgram.mem_invariantLeverageCell_of_nonneg_product 3 4 5 (hcap 3) (hcap 4)
      (hcap 5) hpairBackOne hpairBackTwo hpairBackThree ?_ hfreeBack)
    push Not at hcoherent
    linarith [hsum, hcoherent]

/-- **THE COMPLEMENTARY PAIR OF A COVERING POINT.**  Packaged for the shipped covering
predicate: the pair `{0,1,2}` and `{3,4,5}` is one of the ten, and the disjunction
above supplies exactly the witness `Gtz.CoversInvariantLeverageRegion` asks for. -/
theorem IsTightGramSix.exists_cell_of_front_back
    {gram : Matrix (Fin 6) (Fin 6) ℝ} (hgram : IsTightGramSix gram)
    {invariantLeverage : Fin 6 → ℝ} (hcap : ∀ index, invariantLeverage index ≤ 1)
    (hpairFrontOne : gram 0 1 ^ 2 ≤ (1 - invariantLeverage 0) * (1 - invariantLeverage 1))
    (hpairFrontTwo : gram 0 2 ^ 2 ≤ (1 - invariantLeverage 0) * (1 - invariantLeverage 2))
    (hpairFrontThree : gram 1 2 ^ 2 ≤ (1 - invariantLeverage 1) * (1 - invariantLeverage 2))
    (hpairBackOne : gram 3 4 ^ 2 ≤ (1 - invariantLeverage 3) * (1 - invariantLeverage 4))
    (hpairBackTwo : gram 3 5 ^ 2 ≤ (1 - invariantLeverage 3) * (1 - invariantLeverage 5))
    (hpairBackThree : gram 4 5 ^ 2 ≤ (1 - invariantLeverage 4) * (1 - invariantLeverage 5))
    (hfreeFront : (1 - invariantLeverage 0) * gram 1 2 ^ 2
        + (1 - invariantLeverage 1) * gram 0 2 ^ 2 + (1 - invariantLeverage 2) * gram 0 1 ^ 2
      ≤ (1 - invariantLeverage 0) * (1 - invariantLeverage 1) * (1 - invariantLeverage 2))
    (hfreeBack : (1 - invariantLeverage 3) * gram 4 5 ^ 2
        + (1 - invariantLeverage 4) * gram 3 5 ^ 2 + (1 - invariantLeverage 5) * gram 3 4 ^ 2
      ≤ (1 - invariantLeverage 3) * (1 - invariantLeverage 4) * (1 - invariantLeverage 5)) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ invariantLeverage ∈ invariantLeverageCell gram first second third := by
  rcases hgram.mem_invariantLeverageCell_front_or_back hcap hpairFrontOne hpairFrontTwo
    hpairFrontThree hpairBackOne hpairBackTwo hpairBackThree hfreeFront hfreeBack with
    hfront | hback
  · exact ⟨0, 1, 2, by decide, by decide, by decide, hfront⟩
  · exact ⟨3, 4, 5, by decide, by decide, by decide, hback⟩

namespace IsHollowInvolution

variable {invol : Matrix (Fin 6) (Fin 6) ℝ}

/-! ### The ten energies

The energy is symmetric in the three labels of its triple once the matrix is, so the
transported partitions come back in increasing order. -/

theorem tripleEnergy_swap_left (hinvol : IsHollowInvolution invol) (first second third : Fin 6) :
    tripleEnergy invol first second third = tripleEnergy invol second first third := by
  simp only [tripleEnergy]
  rw [hinvol.apply_comm first second, hinvol.apply_comm third second,
    hinvol.apply_comm third first]
  ring

theorem tripleEnergy_swap_right (hinvol : IsHollowInvolution invol) (first second third : Fin 6) :
    tripleEnergy invol first second third = tripleEnergy invol first third second := by
  simp only [tripleEnergy]
  rw [hinvol.apply_comm second third]
  ring

theorem tripleEnergy_swap_outer (hinvol : IsHollowInvolution invol) (first second third : Fin 6) :
    tripleEnergy invol first second third = tripleEnergy invol third second first := by
  rw [hinvol.tripleEnergy_swap_left, hinvol.tripleEnergy_swap_right,
    hinvol.tripleEnergy_swap_left]

theorem energyPair_012 (hinvol : IsHollowInvolution invol) :
    tripleEnergy invol 0 1 2 = tripleEnergy invol 3 4 5 :=
  hinvol.tripleEnergy_front_eq_back

theorem energyPair_013 (hinvol : IsHollowInvolution invol) :
    tripleEnergy invol 0 1 3 = tripleEnergy invol 2 4 5 := by
  have hpair := hinvol.tripleEnergy_perm_eq (Equiv.swap (2 : Fin 6) 3)
  norm_num [show (Equiv.swap (2 : Fin 6) 3) 0 = 0 from by decide,
    show (Equiv.swap (2 : Fin 6) 3) 1 = 1 from by decide,
    show (Equiv.swap (2 : Fin 6) 3) 2 = 3 from by decide,
    show (Equiv.swap (2 : Fin 6) 3) 3 = 2 from by decide,
    show (Equiv.swap (2 : Fin 6) 3) 4 = 4 from by decide,
    show (Equiv.swap (2 : Fin 6) 3) 5 = 5 from by decide] at hpair
  exact hpair

theorem energyPair_014 (hinvol : IsHollowInvolution invol) :
    tripleEnergy invol 0 1 4 = tripleEnergy invol 2 3 5 := by
  have hpair := hinvol.tripleEnergy_perm_eq (Equiv.swap (2 : Fin 6) 4)
  norm_num [show (Equiv.swap (2 : Fin 6) 4) 0 = 0 from by decide,
    show (Equiv.swap (2 : Fin 6) 4) 1 = 1 from by decide,
    show (Equiv.swap (2 : Fin 6) 4) 2 = 4 from by decide,
    show (Equiv.swap (2 : Fin 6) 4) 3 = 3 from by decide,
    show (Equiv.swap (2 : Fin 6) 4) 4 = 2 from by decide,
    show (Equiv.swap (2 : Fin 6) 4) 5 = 5 from by decide] at hpair
  rw [hinvol.tripleEnergy_swap_left 3 2 5] at hpair
  exact hpair

theorem energyPair_015 (hinvol : IsHollowInvolution invol) :
    tripleEnergy invol 0 1 5 = tripleEnergy invol 2 3 4 := by
  have hpair := hinvol.tripleEnergy_perm_eq (Equiv.swap (2 : Fin 6) 5)
  norm_num [show (Equiv.swap (2 : Fin 6) 5) 0 = 0 from by decide,
    show (Equiv.swap (2 : Fin 6) 5) 1 = 1 from by decide,
    show (Equiv.swap (2 : Fin 6) 5) 2 = 5 from by decide,
    show (Equiv.swap (2 : Fin 6) 5) 3 = 3 from by decide,
    show (Equiv.swap (2 : Fin 6) 5) 4 = 4 from by decide,
    show (Equiv.swap (2 : Fin 6) 5) 5 = 2 from by decide] at hpair
  rw [hinvol.tripleEnergy_swap_outer 3 4 2] at hpair
  rw [hinvol.tripleEnergy_swap_right 2 4 3] at hpair
  exact hpair

theorem energyPair_023 (hinvol : IsHollowInvolution invol) :
    tripleEnergy invol 0 2 3 = tripleEnergy invol 1 4 5 := by
  have hpair := hinvol.tripleEnergy_perm_eq (Equiv.swap (1 : Fin 6) 3)
  norm_num [show (Equiv.swap (1 : Fin 6) 3) 0 = 0 from by decide,
    show (Equiv.swap (1 : Fin 6) 3) 1 = 3 from by decide,
    show (Equiv.swap (1 : Fin 6) 3) 2 = 2 from by decide,
    show (Equiv.swap (1 : Fin 6) 3) 3 = 1 from by decide,
    show (Equiv.swap (1 : Fin 6) 3) 4 = 4 from by decide,
    show (Equiv.swap (1 : Fin 6) 3) 5 = 5 from by decide] at hpair
  rw [hinvol.tripleEnergy_swap_right 0 3 2] at hpair
  exact hpair

theorem energyPair_024 (hinvol : IsHollowInvolution invol) :
    tripleEnergy invol 0 2 4 = tripleEnergy invol 1 3 5 := by
  have hpair := hinvol.tripleEnergy_perm_eq (Equiv.swap (1 : Fin 6) 4)
  norm_num [show (Equiv.swap (1 : Fin 6) 4) 0 = 0 from by decide,
    show (Equiv.swap (1 : Fin 6) 4) 1 = 4 from by decide,
    show (Equiv.swap (1 : Fin 6) 4) 2 = 2 from by decide,
    show (Equiv.swap (1 : Fin 6) 4) 3 = 3 from by decide,
    show (Equiv.swap (1 : Fin 6) 4) 4 = 1 from by decide,
    show (Equiv.swap (1 : Fin 6) 4) 5 = 5 from by decide] at hpair
  rw [hinvol.tripleEnergy_swap_right 0 4 2] at hpair
  rw [hinvol.tripleEnergy_swap_left 3 1 5] at hpair
  exact hpair

theorem energyPair_025 (hinvol : IsHollowInvolution invol) :
    tripleEnergy invol 0 2 5 = tripleEnergy invol 1 3 4 := by
  have hpair := hinvol.tripleEnergy_perm_eq (Equiv.swap (1 : Fin 6) 5)
  norm_num [show (Equiv.swap (1 : Fin 6) 5) 0 = 0 from by decide,
    show (Equiv.swap (1 : Fin 6) 5) 1 = 5 from by decide,
    show (Equiv.swap (1 : Fin 6) 5) 2 = 2 from by decide,
    show (Equiv.swap (1 : Fin 6) 5) 3 = 3 from by decide,
    show (Equiv.swap (1 : Fin 6) 5) 4 = 4 from by decide,
    show (Equiv.swap (1 : Fin 6) 5) 5 = 1 from by decide] at hpair
  rw [hinvol.tripleEnergy_swap_right 0 5 2] at hpair
  rw [hinvol.tripleEnergy_swap_outer 3 4 1] at hpair
  rw [hinvol.tripleEnergy_swap_right 1 4 3] at hpair
  exact hpair

theorem energyPair_034 (hinvol : IsHollowInvolution invol) :
    tripleEnergy invol 0 3 4 = tripleEnergy invol 1 2 5 := by
  have hpair := hinvol.tripleEnergy_perm_eq ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6)))
  norm_num [show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 0 = 0 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 1 = 3 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 2 = 4 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 3 = 1 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 4 = 2 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))) 5 = 5 from by decide] at hpair
  exact hpair

theorem energyPair_035 (hinvol : IsHollowInvolution invol) :
    tripleEnergy invol 0 3 5 = tripleEnergy invol 1 2 4 := by
  have hpair := hinvol.tripleEnergy_perm_eq ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6)))
  norm_num [show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 0 = 0 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 1 = 3 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 2 = 5 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 3 = 1 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 4 = 4 from by decide,
    show ((Equiv.swap (1 : Fin 6) 3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 5 = 2 from by decide] at hpair
  rw [hinvol.tripleEnergy_swap_right 1 4 2] at hpair
  exact hpair

theorem energyPair_045 (hinvol : IsHollowInvolution invol) :
    tripleEnergy invol 0 4 5 = tripleEnergy invol 1 2 3 := by
  have hpair := hinvol.tripleEnergy_perm_eq ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6)))
  norm_num [show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 0 = 0 from by decide,
    show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 1 = 4 from by decide,
    show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 2 = 5 from by decide,
    show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 3 = 3 from by decide,
    show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 4 = 1 from by decide,
    show ((Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6))) 5 = 2 from by decide] at hpair
  rw [hinvol.tripleEnergy_swap_left 3 1 2] at hpair
  rw [hinvol.tripleEnergy_swap_right 1 3 2] at hpair
  exact hpair

end IsHollowInvolution

/-- The triple energy of a tight Gram is that of its involution. -/
theorem IsTightGramSix.tripleEnergy_sub_one {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (first second third : Fin 6) (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    tripleEnergy (gram - 1) first second third = tripleEnergy gram first second third := by
  simp only [tripleEnergy, IsTightGramSix.sub_one_apply_of_ne hfirstSecond,
    IsTightGramSix.sub_one_apply_of_ne hfirstThird,
    IsTightGramSix.sub_one_apply_of_ne hsecondThird]

/-- **A COHERENT TRIPLE OF ENERGY AT MOST THREE FIFTHS.**

The shipped `Gtz.IsTightGramSix.exists_tripleEnergy_le_three_fifths` is SIGN-BLIND: it
produces a low-energy triple and says nothing about its edge product.  The complement
laws upgrade it.  The twenty triples split into ten complementary pairs, the two sides
of a pair carry the SAME energy and OPPOSITE products, so each pair offers a coherent
side at its own energy; the ten pair energies total six, so one of those coherent
sides has energy at most `3/5`.

The sign is exactly what the determinant clause of the cell needs, and this is the
first statement in the campaign that delivers both at once. -/
theorem IsTightGramSix.exists_nonneg_product_tripleEnergy_le_three_fifths
    {gram : Matrix (Fin 6) (Fin 6) ℝ} (hgram : IsTightGramSix gram) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 ≤ tripleEdgeProduct gram first second third
      ∧ tripleEnergy gram first second third ≤ 3 / 5 := by
  by_contra hcontra
  push Not at hcontra
  have hinvol := hgram.isHollowInvolution_sub_one
  have hEbridge : ∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
      tripleEnergy (gram - 1) first second third = tripleEnergy gram first second third :=
    fun first second third h1 h2 h3 => IsTightGramSix.tripleEnergy_sub_one first second third h1 h2 h3
  have hpairBound : ∀ frontOne frontTwo frontThree backOne backTwo backThree : Fin 6,
      frontOne ≠ frontTwo → frontOne ≠ frontThree → frontTwo ≠ frontThree →
      backOne ≠ backTwo → backOne ≠ backThree → backTwo ≠ backThree →
      tripleEdgeProduct gram frontOne frontTwo frontThree
          + tripleEdgeProduct gram backOne backTwo backThree = 0 →
      tripleEnergy gram frontOne frontTwo frontThree
          = tripleEnergy gram backOne backTwo backThree →
      3 / 5 < tripleEnergy gram frontOne frontTwo frontThree := by
    intro frontOne frontTwo frontThree backOne backTwo backThree hf1 hf2 hf3 hb1 hb2 hb3
      hproduct henergy
    by_cases hcoherent : 0 ≤ tripleEdgeProduct gram frontOne frontTwo frontThree
    · exact hcontra frontOne frontTwo frontThree hf1 hf2 hf3 hcoherent
    · push Not at hcoherent
      have hback := hcontra backOne backTwo backThree hb1 hb2 hb3 (by linarith [hproduct])
      linarith [henergy, hback]
  have hE012 := hinvol.energyPair_012
  have hP012 := hinvol.pair_012
  rw [hEbridge 0 1 2 (by decide) (by decide) (by decide),
    hEbridge 3 4 5 (by decide) (by decide) (by decide)] at hE012
  rw [IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide),
    IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide)] at hP012
  have hE013 := hinvol.energyPair_013
  have hP013 := hinvol.pair_013
  rw [hEbridge 0 1 3 (by decide) (by decide) (by decide),
    hEbridge 2 4 5 (by decide) (by decide) (by decide)] at hE013
  rw [IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide),
    IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide)] at hP013
  have hE014 := hinvol.energyPair_014
  have hP014 := hinvol.pair_014
  rw [hEbridge 0 1 4 (by decide) (by decide) (by decide),
    hEbridge 2 3 5 (by decide) (by decide) (by decide)] at hE014
  rw [IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide),
    IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide)] at hP014
  have hE015 := hinvol.energyPair_015
  have hP015 := hinvol.pair_015
  rw [hEbridge 0 1 5 (by decide) (by decide) (by decide),
    hEbridge 2 3 4 (by decide) (by decide) (by decide)] at hE015
  rw [IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide),
    IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide)] at hP015
  have hE023 := hinvol.energyPair_023
  have hP023 := hinvol.pair_023
  rw [hEbridge 0 2 3 (by decide) (by decide) (by decide),
    hEbridge 1 4 5 (by decide) (by decide) (by decide)] at hE023
  rw [IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide),
    IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide)] at hP023
  have hE024 := hinvol.energyPair_024
  have hP024 := hinvol.pair_024
  rw [hEbridge 0 2 4 (by decide) (by decide) (by decide),
    hEbridge 1 3 5 (by decide) (by decide) (by decide)] at hE024
  rw [IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide),
    IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide)] at hP024
  have hE025 := hinvol.energyPair_025
  have hP025 := hinvol.pair_025
  rw [hEbridge 0 2 5 (by decide) (by decide) (by decide),
    hEbridge 1 3 4 (by decide) (by decide) (by decide)] at hE025
  rw [IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide),
    IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide)] at hP025
  have hE034 := hinvol.energyPair_034
  have hP034 := hinvol.pair_034
  rw [hEbridge 0 3 4 (by decide) (by decide) (by decide),
    hEbridge 1 2 5 (by decide) (by decide) (by decide)] at hE034
  rw [IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide),
    IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide)] at hP034
  have hE035 := hinvol.energyPair_035
  have hP035 := hinvol.pair_035
  rw [hEbridge 0 3 5 (by decide) (by decide) (by decide),
    hEbridge 1 2 4 (by decide) (by decide) (by decide)] at hE035
  rw [IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide),
    IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide)] at hP035
  have hE045 := hinvol.energyPair_045
  have hP045 := hinvol.pair_045
  rw [hEbridge 0 4 5 (by decide) (by decide) (by decide),
    hEbridge 1 2 3 (by decide) (by decide) (by decide)] at hE045
  rw [IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide),
    IsTightGramSix.tripleEdgeProduct_sub_one (gram := gram) (by decide) (by decide) (by decide)] at hP045
  have hb012 := hpairBound 0 1 2 3 4 5 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hP012 hE012
  have hb013 := hpairBound 0 1 3 2 4 5 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hP013 hE013
  have hb014 := hpairBound 0 1 4 2 3 5 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hP014 hE014
  have hb015 := hpairBound 0 1 5 2 3 4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hP015 hE015
  have hb023 := hpairBound 0 2 3 1 4 5 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hP023 hE023
  have hb024 := hpairBound 0 2 4 1 3 5 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hP024 hE024
  have hb025 := hpairBound 0 2 5 1 3 4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hP025 hE025
  have hb034 := hpairBound 0 3 4 1 2 5 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hP034 hE034
  have hb035 := hpairBound 0 3 5 1 2 4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hP035 hE035
  have hb045 := hpairBound 0 4 5 1 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hP045 hE045
  have htotal := hgram.totalTripleEnergy_eq_twelve
  simp only [totalTripleEnergy] at htotal
  linarith [hb012, hb013, hb014, hb015, hb023, hb024, hb025, hb034, hb035, hb045, hE012, hE013, hE014, hE015, hE023, hE024, hE025, hE034, hE035, hE045, htotal]

end Gtz

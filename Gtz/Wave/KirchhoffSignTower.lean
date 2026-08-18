/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Wave.KFourSignedTreeLaplacian
import Gtz.Wave.TriangleStallClosureDeflation
import Gtz.Quantitative.WindowPolarity
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The Kirchhoff sign tower of a chart gap, and the shifted Frobenius cell

Three results carry this module.

**The polarization law.**  The sixteen-term spanning-tree sum of `K4` is
multi-affine, so `Gtz.kFourMassTreeSum_polarization` reads it on a pencil
`x + u y` as a cubic in `u` whose two middle coefficients pair one vector
against the eight-term contraction polynomial of the other.  The proof is one
`ring` step with no case split.  `Gtz.trace_adjugate_kFourLaplacian_mul` is the
matrix reading of the same two coefficients: the trace of one Laplacian against
the adjugate of another IS the mixed forest sum.  Together with the general
mixed determinant `Gtz.det_add_smul_fin_three` this turns every chart gap
determinant into four nonnegative blocks with alternating signs
(`Gtz.det_directionChartGap_eq_pencil`), and the two middle invariants
`Gtz.kFourGapInvariantOne` and `Gtz.kFourGapInvariantTwo` become mixed forest
sums as well.

**The complete forest criterion.**  A strictly dominating selection has both
invariants strictly positive (`Gtz.kFourGapInvariantOne_pos_of_posDef` and
`Gtz.kFourGapInvariantTwo_pos_of_posDef`).  Each proof is one trace of two
positive definite matrices, so neither is a Loewner comparison, a margin or an
average.  The second law is the one that kills a selection whose gap
determinant is positive while its gap is indefinite, the exact failure mode
that makes a determinant sign worthless on its own.  Those two laws are also
SUFFICIENT with the determinant sign: `Gtz.posDef_directionChartGap_of_invariantTriple`
congruates the gap by the mass whitener and reads a Descartes sign rule off the
characteristic cubic through the landed inertia bridge.  The outcome is
`Gtz.posDef_directionChartGap_iff_forestTriple`:

  strict domination  IS  `0 < sum_c s_c Q_c(m)`, `0 < sum_c m_c Q_c(s)`,
  `0 < T(s)`

with `s` the signed gap weight, `Q` the eight-term contraction polynomial and
`T` the sixteen-term tree sum.  Three spanning-forest sums, no matrix.

**The whole chart obligation, as one polynomial statement.**
`Gtz.KFourForestTripleTotal` says that some listed tree makes those three sums
positive at every chart point, and
`Gtz.kFourUniversalStrictTree_iff_forestTripleTotal` proves it EQUIVALENT to
`Gtz.KFourUniversalStrictTree`.  So
`Gtz.directionChartIsTieFree_kFour_of_forestTripleTotal` closes the registered
chart obligation `Gtz.DirectionChartIsTieFree Gtz.kFourDirection` from a
statement with no matrix, no whitener, no square root, no deflation bound, no
corank hypothesis and no weak antecedent, and
`Gtz.kFourGaugeAndPivotWallClosure_of_forestTripleTotal` closes the registered
`A3` component route from the same statement.  Being an equivalence it cannot
be refuted by a hunt.

**The shifted Frobenius cell, and what it closes.**  For any real shift below
one, `Gtz.posDef_sub_of_shifted_trace_adjugate` proves a strict Loewner
domination from ONE trace inequality, with no eigenvalue, no square root and no
positive semidefiniteness on the dominated side.  At the optimal rational shift
`(P2 - P3) / (2 * P3)` the test becomes three polynomial inequalities in the
forest coefficients, and `Gtz.KFourPencilCellFires` names them:

  `0 < P3`,  `P2 < 3 * P3`,  `P2 ^ 2 + 2 * P2 * P3 < 3 * P3 ^ 2 + 4 * P3 * P1`.

`Gtz.posDef_directionChartGap_of_pencilCell` turns the cell into a strictly
dominating selection.

**The whole chart obligation is one strict tree.**
`Gtz.directionChartIsTieFree_kFour_of_universalStrictTree` closes the registered
`K4` chart obligation `Gtz.DirectionChartIsTieFree Gtz.kFourDirection` from
`Gtz.KFourUniversalStrictTree`, and
`Gtz.kFourGaugeAndPivotWallClosure_of_universalStrictTree` closes the registered
`A3` component route from the same statement.  Both discard every wall
hypothesis and the weak antecedent pointwise.

**The cell is live at every mandatory point, and it is NOT total.**  It fires at
`Gtz.tetrahedronChartPoint`, at `Gtz.maxEdgeRefuterPoint`, at
`Gtz.heavyPairRefuterPoint`, at `Gtz.bandResidualWitnessPoint` (the registry's
canonical band inhabitant, uncovered by both landed regions) and at
`Gtz.kFourGaugeWallPoint` on the corank-two gauge wall, where the landed
isotropic cell can never fire.  It also fires at four thousand exact chart
points of five regimes and at fourteen thousand seven hundred exact points of
the gauge wall variety.  **That record is not an adjudication.**
`Gtz.kFourPencilCell_not_total` refutes totality in kernel at
`Gtz.pencilCellRefuterPoint`, the exact rational landing point of a directed
hunt of four hundred thousand restarts.  All sixteen trees fail the cell there
while two of them still dominate strictly
(`Gtz.pencilCellRefuterPoint_hasStrictTree`), so the obligation is intact and
only the cell is refuted.  The failure mode is a strictly weaker one than a
Loewner comparison: the Frobenius bound caps the largest pencil eigenvalue by
the whole spread, and at the refuter that spread is wide.
-/

namespace Gtz

open Finset Matrix

/-! ## 1. The mixed determinant of a three-by-three pencil -/

/-- **THE MIXED DETERMINANT.**  The determinant of a three-by-three pencil is a
cubic whose two middle coefficients are adjugate traces.  Nothing here is
`K4`-specific and nothing is symmetric. -/
theorem det_add_smul_fin_three (left right : Matrix (Fin 3) (Fin 3) ℝ) (step : ℝ) :
    (left + step • right).det
      = left.det + step * Matrix.trace (left.adjugate * right)
        + step ^ 2 * Matrix.trace (right.adjugate * left) + step ^ 3 * right.det := by
  simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.trace_fin_three,
    Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **NEWTON AT SIZE THREE.**  The trace of a square is the square of the trace
less twice the trace of the adjugate. -/
theorem trace_sq_fin_three (mat : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (mat * mat)
      = Matrix.trace mat ^ 2 - 2 * Matrix.trace mat.adjugate := by
  simp only [Matrix.adjugate_fin_three, Matrix.trace_fin_three, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The adjugate of a three-by-three adjugate is the determinant times the
matrix. -/
theorem adjugate_adjugate_fin_three (mat : Matrix (Fin 3) (Fin 3) ℝ) :
    mat.adjugate.adjugate = mat.det • mat := by
  have hcard : Fintype.card (Fin 3) ≠ 1 := by decide
  rw [Matrix.adjugate_adjugate mat hcard]
  norm_num

/-! ## 2. The polarization law of the sixteen-term tree sum -/

/-- **THE POLARIZATION LAW.**  The sixteen-term spanning-tree sum of `K4` is
multi-affine, so its value on a pencil `x + u y` is a cubic in `u` whose two
middle coefficients pair one vector against the eight-term contraction
polynomial of the other.  One `ring` step, no case split, and no matrix. -/
theorem kFourMassTreeSum_polarization (leftVec rightVec : Fin 6 → ℝ) (step : ℝ) :
    kFourMassTreeSum (leftVec + step • rightVec)
      = kFourMassTreeSum leftVec
        + step * (∑ label, rightVec label
            * kFourContractionTreePolynomial leftVec label)
        + step ^ 2 * (∑ label, leftVec label
            * kFourContractionTreePolynomial rightVec label)
        + step ^ 3 * kFourMassTreeSum rightVec := by
  simp only [kFourMassTreeSum, kFourContractionTreePolynomial, Fin.sum_univ_six,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The tree sum is homogeneous of degree three. -/
theorem kFourMassTreeSum_neg (vec : Fin 6 → ℝ) :
    kFourMassTreeSum (-vec) = -kFourMassTreeSum vec := by
  simp only [kFourMassTreeSum, Pi.neg_apply]
  ring

/-- The contraction polynomial is homogeneous of degree two. -/
theorem kFourContractionTreePolynomial_neg (vec : Fin 6 → ℝ) (label : Fin 6) :
    kFourContractionTreePolynomial (-vec) label
      = kFourContractionTreePolynomial vec label := by
  fin_cases label <;>
    simp only [kFourContractionTreePolynomial, Pi.neg_apply] <;> ring

/-! ## 3. The `K4` Laplacian, and the adjugate bridge -/

/-- The reduced Laplacian of a `K4` edge weight vector. -/
noncomputable def kFourLaplacian (edgeWeight : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ label, edgeWeight label • atomMatrix (kFourDirection label)

theorem kFourLaplacian_transpose (edgeWeight : Fin 6 → ℝ) :
    (kFourLaplacian edgeWeight)ᵀ = kFourLaplacian edgeWeight := by
  rw [kFourLaplacian, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (kFourDirection label)).1]

theorem det_kFourLaplacian (edgeWeight : Fin 6 → ℝ) :
    (kFourLaplacian edgeWeight).det = kFourMassTreeSum edgeWeight :=
  det_sum_smul_atomMatrix_kFourDirection edgeWeight

theorem posSemidef_kFourLaplacian (edgeWeight : Fin 6 → ℝ)
    (hnonneg : ∀ label, 0 ≤ edgeWeight label) :
    (kFourLaplacian edgeWeight).PosSemidef :=
  posSemidef_sum_smul_atomMatrix kFourDirection edgeWeight hnonneg

theorem kFourLaplacian_add (leftVec rightVec : Fin 6 → ℝ) :
    kFourLaplacian (leftVec + rightVec)
      = kFourLaplacian leftVec + kFourLaplacian rightVec := by
  rw [kFourLaplacian, kFourLaplacian, kFourLaplacian, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun label _ => by rw [Pi.add_apply, add_smul]

theorem kFourLaplacian_smul (scale : ℝ) (vec : Fin 6 → ℝ) :
    kFourLaplacian (scale • vec) = scale • kFourLaplacian vec := by
  rw [kFourLaplacian, kFourLaplacian, Finset.smul_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- The trace of a matrix against a `K4` atom is that atom's quadratic form. -/
theorem trace_mul_atomMatrix_kFour (gram : Matrix (Fin 3) (Fin 3) ℝ) (label : Fin 6) :
    Matrix.trace (gram * atomMatrix (kFourDirection label))
      = kFourDirection label ⬝ᵥ (gram *ᵥ kFourDirection label) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **THE ADJUGATE BRIDGE.**  The trace of one `K4` Laplacian against the
adjugate of another is the mixed forest sum: each edge of the second network
pays its own weight times the eight-term contraction polynomial of the first.
This is the matrix reading of the middle coefficients of the polarization
law. -/
theorem trace_adjugate_kFourLaplacian_mul (leftVec rightVec : Fin 6 → ℝ) :
    Matrix.trace ((kFourLaplacian leftVec).adjugate * kFourLaplacian rightVec)
      = ∑ label, rightVec label * kFourContractionTreePolynomial leftVec label := by
  simp only [kFourLaplacian]
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_mul_atomMatrix_kFour,
    dotProduct_adjugate_kFourDirection]

/-! ## 4. Three pieces of definiteness bookkeeping -/

/-- **A NONNEGATIVE LAPLACIAN IS DEFINITE AS SOON AS ITS TREE SUM IS.**  No
spanning hypothesis and no basis: a probe that the network cannot see lies in
the kernel, and a kernel kills the determinant. -/
theorem posDef_kFourLaplacian_of_det_pos (edgeWeight : Fin 6 → ℝ)
    (hnonneg : ∀ label, 0 ≤ edgeWeight label)
    (hdet : 0 < kFourMassTreeSum edgeWeight) :
    (kFourLaplacian edgeWeight).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (kFourLaplacian_transpose edgeWeight), fun probe hne => ?_⟩
  rw [star_trivial]
  have hform : probe ⬝ᵥ (kFourLaplacian edgeWeight *ᵥ probe)
      = ∑ label, edgeWeight label * (kFourDirection label ⬝ᵥ probe) ^ 2 := by
    rw [kFourLaplacian, Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]
  have hnonnegTerm : ∀ label ∈ (Finset.univ : Finset (Fin 6)),
      0 ≤ edgeWeight label * (kFourDirection label ⬝ᵥ probe) ^ 2 :=
    fun label _ => mul_nonneg (hnonneg label) (sq_nonneg _)
  rcases lt_or_eq_of_le (Finset.sum_nonneg hnonnegTerm) with hpos | hzero
  · rwa [hform]
  · exfalso
    have hall : ∀ label : Fin 6,
        edgeWeight label * (kFourDirection label ⬝ᵥ probe) ^ 2 = 0 :=
      fun label => (Finset.sum_eq_zero_iff_of_nonneg hnonnegTerm).mp hzero.symm label
        (Finset.mem_univ label)
    have hkernel : kFourLaplacian edgeWeight *ᵥ probe = 0 := by
      rw [kFourLaplacian, Matrix.sum_mulVec]
      refine Finset.sum_eq_zero fun label _ => ?_
      rw [smul_atomMatrix_mulVec]
      have hterm : edgeWeight label * (kFourDirection label ⬝ᵥ probe) = 0 := by
        rcases mul_eq_zero.mp (hall label) with h | h
        · rw [h, zero_mul]
        · rw [pow_eq_zero_iff (n := 2) (by norm_num)] at h
          rw [h, mul_zero]
      rw [hterm, zero_smul]
    have hdetZero : (kFourLaplacian edgeWeight).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨probe, hne, hkernel⟩
    rw [det_kFourLaplacian] at hdetZero
    exact absurd hdetZero (ne_of_gt hdet)

/-- The adjugate of a positive definite three-by-three matrix is positive
definite. -/
theorem posDef_adjugate_fin_three {mat : Matrix (Fin 3) (Fin 3) ℝ} (hpd : mat.PosDef) :
    mat.adjugate.PosDef := by
  have hdet : 0 < mat.det := hpd.det_pos
  have hadj : mat.adjugate = mat.det • mat⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ (ne_of_gt hdet),
      one_smul]
  rw [hadj]
  exact hpd.inv.smul hdet

/-- **THE TRACE OF A PRODUCT OF TWO DEFINITE MATRICES IS POSITIVE.**  A
congruence turns the product into a definite matrix, whose diagonal is
positive. -/
theorem trace_mul_pos_of_posDef {left right : Matrix (Fin 3) (Fin 3) ℝ}
    (hleft : left.PosDef) (hright : right.PosDef) :
    0 < Matrix.trace (left * right) := by
  obtain ⟨whitener, hunit, hone⟩ := exists_congruence_to_one hleft
  have hunitT : IsUnit (whitenerᵀ).det := by rwa [Matrix.det_transpose]
  have hfactor : left = (whitener⁻¹)ᵀ * whitener⁻¹ := by
    have hcollapse : (whitenerᵀ)⁻¹ * (whitenerᵀ * left * whitener) * whitener⁻¹ = left := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunitT,
        Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
    rw [← hcollapse, hone, Matrix.mul_one, Matrix.transpose_nonsing_inv]
  have hunitInv : IsUnit ((whitener⁻¹)ᵀ).det := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact (isUnit_iff_ne_zero.mpr (inv_ne_zero (isUnit_iff_ne_zero.mp hunit)))
  have hconj : (whitener⁻¹ * right * (whitener⁻¹)ᵀ).PosDef := by
    have hsymm : rightᵀ = right := transpose_eq_of_isHermitian hright.1
    have := (posDef_congr_right (X := right) (P := (whitener⁻¹)ᵀ) hsymm hunitInv).mp hright
    rwa [Matrix.transpose_transpose] at this
  have hrewrite : Matrix.trace (left * right)
      = Matrix.trace (whitener⁻¹ * right * (whitener⁻¹)ᵀ) := by
    rw [hfactor, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [hrewrite]
  exact hconj.trace_pos

/-! ## 5. The four pencil coefficients of a chart gap -/

/-- The conductance vector of a chart selection: the boosted conductance on the
selection and nothing off it. -/
noncomputable def kFourGapConductance (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : Fin 6 → ℝ :=
  fun label => if label ∈ selected then mass label / weight label else 0

theorem chartMassMatrix_kFour_eq_kFourLaplacian (mass : Fin 6 → ℝ) :
    chartMassMatrix kFourDirection mass = kFourLaplacian mass := rfl

/-- The signed gap weight is the conductance vector less the mass vector. -/
theorem signedGapWeight_eq_conductance_sub (mass weight : Fin 6 → ℝ)
    {selected : Finset (Fin 6)} (hweight : ∀ label ∈ selected, weight label ≠ 0) :
    signedGapWeight mass weight selected
      = kFourGapConductance mass weight selected + (-1 : ℝ) • mass := by
  funext label
  by_cases hmem : label ∈ selected
  · have hne : weight label ≠ 0 := hweight label hmem
    rw [signedGapWeight_mem mass weight hmem]
    simp only [kFourGapConductance, hmem, ite_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [signedGapWeight_not_mem mass weight hmem]
    simp only [kFourGapConductance, hmem, ite_false, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- **THE CHART GAP IS A LAPLACIAN DIFFERENCE.**  The selection leaves the
statement into one nonnegative conductance vector. -/
theorem directionChartGap_eq_kFourLaplacian_sub (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) :
    directionChartGap kFourDirection mass weight selected
      = kFourLaplacian (kFourGapConductance mass weight selected)
        - kFourLaplacian mass := by
  classical
  rw [directionChartGap, kFourLaplacian, kFourLaplacian]
  congr 1
  symm
  calc ∑ label, kFourGapConductance mass weight selected label
        • atomMatrix (kFourDirection label)
      = ∑ label, (if label ∈ selected then
          (mass label / weight label) • atomMatrix (kFourDirection label) else 0) :=
        Finset.sum_congr rfl fun label _ => by
          by_cases hmem : label ∈ selected <;> simp [kFourGapConductance, hmem]
    _ = ∑ label ∈ selected, (mass label / weight label)
          • atomMatrix (kFourDirection label) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem kFourGapConductance_nonneg (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (label : Fin 6) :
    0 ≤ kFourGapConductance point.mass point.weight selected label := by
  by_cases hmem : label ∈ selected
  · simp only [kFourGapConductance, hmem, ite_true]
    exact le_of_lt (div_pos (point.mass_pos label) (point.weight_pos label))
  · simp [kFourGapConductance, hmem]

/-- The lead pencil coefficient: the tree sum of the conductance vector.  At a
spanning tree it is the product of the three boosted conductances. -/
noncomputable def kFourPencilLead (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : ℝ :=
  kFourMassTreeSum (kFourGapConductance mass weight selected)

/-- The second pencil coefficient: the masses against the conductance forest. -/
noncomputable def kFourPencilSecond (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : ℝ :=
  ∑ label, mass label
    * kFourContractionTreePolynomial (kFourGapConductance mass weight selected) label

/-- The third pencil coefficient: the conductances against the mass forest. -/
noncomputable def kFourPencilThird (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : ℝ :=
  ∑ label, kFourGapConductance mass weight selected label
    * kFourContractionTreePolynomial mass label

/-- **THE FOUR-COEFFICIENT READING OF EVERY CHART GAP DETERMINANT.**  The
sixteen signed Kirchhoff terms collect into four nonnegative blocks with
alternating signs.  The lead block is the tree product, the base block is the
mass moment determinant, and the two middle blocks are mixed forest sums. -/
theorem det_directionChartGap_eq_pencil (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) :
    (directionChartGap kFourDirection mass weight selected).det
      = kFourPencilLead mass weight selected - kFourPencilSecond mass weight selected
        + kFourPencilThird mass weight selected - kFourMassTreeSum mass := by
  have hsub : kFourLaplacian (kFourGapConductance mass weight selected)
      - kFourLaplacian mass
      = kFourLaplacian (kFourGapConductance mass weight selected + (-1 : ℝ) • mass) := by
    rw [kFourLaplacian_add, kFourLaplacian_smul]
    module
  rw [directionChartGap_eq_kFourLaplacian_sub, hsub, det_kFourLaplacian,
    kFourMassTreeSum_polarization, kFourPencilLead, kFourPencilSecond, kFourPencilThird]
  ring

/-! ## 6. The pencil invariants, as adjugate traces -/

/-- The first gap invariant: the gap read against the mass adjugate. -/
noncomputable def kFourGapInvariantOne (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : ℝ :=
  Matrix.trace ((kFourLaplacian mass).adjugate
    * directionChartGap kFourDirection mass weight selected)

/-- The second gap invariant: the mass moment read against the gap adjugate. -/
noncomputable def kFourGapInvariantTwo (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : ℝ :=
  Matrix.trace ((directionChartGap kFourDirection mass weight selected).adjugate
    * kFourLaplacian mass)

/-- The gap is the Laplacian of the signed gap weight. -/
theorem directionChartGap_eq_signedLaplacian' (mass weight : Fin 6 → ℝ)
    {selected : Finset (Fin 6)} (hweight : ∀ label ∈ selected, weight label ≠ 0) :
    directionChartGap kFourDirection mass weight selected
      = kFourLaplacian (signedGapWeight mass weight selected) :=
  directionChartGap_eq_sum_signedGapWeight kFourDirection mass weight selected hweight

/-- **THE FIRST INVARIANT IS A MIXED FOREST SUM.**  The signed gap weights pay
against the eight-term mass contraction polynomials. -/
theorem kFourGapInvariantOne_eq_forestSum (mass weight : Fin 6 → ℝ)
    {selected : Finset (Fin 6)} (hweight : ∀ label ∈ selected, weight label ≠ 0) :
    kFourGapInvariantOne mass weight selected
      = ∑ label, signedGapWeight mass weight selected label
          * kFourContractionTreePolynomial mass label := by
  rw [kFourGapInvariantOne, directionChartGap_eq_signedLaplacian' mass weight hweight,
    trace_adjugate_kFourLaplacian_mul]

/-- **THE SECOND INVARIANT IS THE MIRROR MIXED FOREST SUM.**  The masses pay
against the eight-term contraction polynomials of the SIGNED gap weight. -/
theorem kFourGapInvariantTwo_eq_forestSum (mass weight : Fin 6 → ℝ)
    {selected : Finset (Fin 6)} (hweight : ∀ label ∈ selected, weight label ≠ 0) :
    kFourGapInvariantTwo mass weight selected
      = ∑ label, mass label
          * kFourContractionTreePolynomial (signedGapWeight mass weight selected) label := by
  rw [kFourGapInvariantTwo, directionChartGap_eq_signedLaplacian' mass weight hweight,
    trace_adjugate_kFourLaplacian_mul]

/-- **THE MASTER PENCIL IDENTITY.**  Reloading the gap with the mass moment
produces a cubic whose four coefficients are the determinant, the two
invariants and the moment determinant. -/
theorem det_directionChartGap_add_smul_mass (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) (step : ℝ) :
    (directionChartGap kFourDirection mass weight selected
        + step • kFourLaplacian mass).det
      = (directionChartGap kFourDirection mass weight selected).det
        + step * kFourGapInvariantTwo mass weight selected
        + step ^ 2 * kFourGapInvariantOne mass weight selected
        + step ^ 3 * kFourMassTreeSum mass := by
  rw [det_add_smul_fin_three, kFourGapInvariantOne, kFourGapInvariantTwo,
    det_kFourLaplacian]

/-! ## 7. Two exclusion laws that no Loewner comparison reaches -/

/-- **THE TRACE EXCLUSION.**  A strictly dominating selection has a strictly
positive first invariant.  The proof is one trace of two definite matrices. -/
theorem kFourGapInvariantOne_pos_of_posDef (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection point.mass point.weight selected).PosDef) :
    0 < kFourGapInvariantOne point.mass point.weight selected := by
  have hmoment : (kFourLaplacian point.mass).PosDef := posDef_chartMassMatrix_kFour point
  exact trace_mul_pos_of_posDef (posDef_adjugate_fin_three hmoment) hpd

/-- **THE ADJUGATE EXCLUSION.**  A strictly dominating selection has a strictly
positive second invariant.  This is the law that kills a selection whose gap
determinant is positive while its gap is indefinite. -/
theorem kFourGapInvariantTwo_pos_of_posDef (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection point.mass point.weight selected).PosDef) :
    0 < kFourGapInvariantTwo point.mass point.weight selected := by
  have hmoment : (kFourLaplacian point.mass).PosDef := posDef_chartMassMatrix_kFour point
  exact trace_mul_pos_of_posDef (posDef_adjugate_fin_three hpd) hmoment

/-- The contrapositive of the trace exclusion, in forest form. -/
theorem not_posDef_of_kFourGapInvariantOne_nonpos (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hfail : ∑ label, signedGapWeight point.mass point.weight selected label
      * kFourContractionTreePolynomial point.mass label ≤ 0) :
    ¬ (directionChartGap kFourDirection point.mass point.weight selected).PosDef := by
  intro hpd
  have hpos := kFourGapInvariantOne_pos_of_posDef point selected hpd
  rw [kFourGapInvariantOne_eq_forestSum point.mass point.weight
    (fun label _ => (point.weight_pos label).ne')] at hpos
  linarith

/-- The contrapositive of the adjugate exclusion, in forest form. -/
theorem not_posDef_of_kFourGapInvariantTwo_nonpos (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hfail : ∑ label, point.mass label
      * kFourContractionTreePolynomial
          (signedGapWeight point.mass point.weight selected) label ≤ 0) :
    ¬ (directionChartGap kFourDirection point.mass point.weight selected).PosDef := by
  intro hpd
  have hpos := kFourGapInvariantTwo_pos_of_posDef point selected hpd
  rw [kFourGapInvariantTwo_eq_forestSum point.mass point.weight
    (fun label _ => (point.weight_pos label).ne')] at hpos
  linarith

/-! ## 8. The tower is COMPLETE: three forest sums decide strict domination

The two exclusion laws are necessary.  They are also SUFFICIENT together with the
determinant sign, and the proof spends the mass whitener once.  Congruating the
gap by the whitener turns the three invariants into the three coefficients of
the characteristic cubic of a symmetric matrix, and the landed inertia bridge
`Gtz.posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos` reads a Descartes
sign rule off that cubic.  Nothing here is a Sylvester minor of the gap, and
nothing needs a basis adapted to the selection. -/

/-- The trace of a three-by-three adjugate IS the second characteristic
invariant. -/
theorem trace_adjugate_eq_secondInvariant (mat : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace mat.adjugate = secondInvariantOfThree mat := by
  simp only [Matrix.adjugate_fin_three, Matrix.trace_fin_three, secondInvariantOfThree,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The adjugate of a three-by-three inverse. -/
theorem adjugate_nonsing_inv_fin_three {mat : Matrix (Fin 3) (Fin 3) ℝ}
    (hdet : mat.det ≠ 0) : (mat⁻¹).adjugate = (mat.det)⁻¹ • mat := by
  have hinv : mat⁻¹ = (mat.det)⁻¹ • mat.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [hinv, Matrix.adjugate_smul]
  have hcard : Fintype.card (Fin 3) - 1 = 2 := by decide
  rw [hcard, adjugate_adjugate_fin_three, smul_smul]
  congr 1
  field_simp

/-- **THE INVARIANT TRIPLE IS SUFFICIENT.**  Both exclusion laws together with a
positive gap determinant force strict domination.  With the two landed
converses this makes the tower an EQUIVALENCE. -/
theorem posDef_directionChartGap_of_invariantTriple (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hone : 0 < kFourGapInvariantOne point.mass point.weight selected)
    (htwo : 0 < kFourGapInvariantTwo point.mass point.weight selected)
    (hdet : 0 < (directionChartGap kFourDirection point.mass point.weight selected).det) :
    (directionChartGap kFourDirection point.mass point.weight selected).PosDef := by
  set gap := directionChartGap kFourDirection point.mass point.weight selected with hgapDef
  set moment := kFourLaplacian point.mass with hmomentDef
  have hmomentPd : moment.PosDef := posDef_chartMassMatrix_kFour point
  have hmomentDet : 0 < moment.det := hmomentPd.det_pos
  obtain ⟨whitener, hunit, hone'⟩ := exists_congruence_to_one hmomentPd
  have hunitT : IsUnit (whitenerᵀ).det := by rwa [Matrix.det_transpose]
  have hsquare : whitener.det ^ 2 * moment.det = 1 := by
    have := congrArg Matrix.det hone'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    linarith [this, sq (whitener.det)]
  have hdetNe : whitener.det ≠ 0 := isUnit_iff_ne_zero.mp hunit
  have hsquarePos : 0 < whitener.det ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hdetNe))
  have hright : moment * (whitener * whitenerᵀ) = 1 := by
    have hstep : (whitenerᵀ)⁻¹ = moment * whitener :=
      Matrix.inv_eq_right_inv (by rw [← Matrix.mul_assoc]; exact hone')
    rw [← Matrix.mul_assoc, ← hstep, Matrix.nonsing_inv_mul _ hunitT]
  have hkernel : whitener * whitenerᵀ = moment⁻¹ :=
    (Matrix.inv_eq_right_inv hright).symm
  set whitened : Matrix (Fin 3) (Fin 3) ℝ := whitenerᵀ * gap * whitener with hwhitened
  have hgapSymm : gapᵀ = gap := directionChartGap_transpose _ _ _ _
  have hwhitenedSymm : whitenedᵀ = whitened := by
    rw [hwhitened, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hgapSymm, Matrix.mul_assoc]
  have hdetWhitened : whitened.det = whitener.det ^ 2 * gap.det := by
    rw [hwhitened, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have htraceWhitened : Matrix.trace whitened = whitener.det ^ 2
      * kFourGapInvariantOne point.mass point.weight selected := by
    have hcyc : Matrix.trace whitened
        = Matrix.trace (gap * (whitener * whitenerᵀ)) := by
      rw [hwhitened, Matrix.mul_assoc,
        Matrix.trace_mul_comm whitenerᵀ (gap * whitener), Matrix.mul_assoc]
    have hinvForm : moment⁻¹ = (moment.det)⁻¹ • moment.adjugate := by
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    have hscale : (moment.det)⁻¹ = whitener.det ^ 2 :=
      inv_eq_of_mul_eq_one_left hsquare
    rw [hcyc, hkernel, hinvForm, hscale, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      kFourGapInvariantOne, ← hmomentDef, Matrix.trace_mul_comm]
  have hsecondWhitened : secondInvariantOfThree whitened = whitener.det ^ 2
      * kFourGapInvariantTwo point.mass point.weight selected := by
    have hadjWhitened : whitened.adjugate
        = whitener.adjugate * gap.adjugate * (whitener.adjugate)ᵀ := by
      rw [hwhitened, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
        Matrix.adjugate_transpose]
      noncomm_ring
    have hpair : (whitener.adjugate)ᵀ * whitener.adjugate
        = (moment.det)⁻¹ • moment := by
      rw [Matrix.adjugate_transpose, ← Matrix.adjugate_mul_distrib, hkernel,
        adjugate_nonsing_inv_fin_three (ne_of_gt hmomentDet)]
    have hscale : (moment.det)⁻¹ = whitener.det ^ 2 :=
      inv_eq_of_mul_eq_one_left hsquare
    rw [← trace_adjugate_eq_secondInvariant, hadjWhitened, Matrix.mul_assoc,
      Matrix.trace_mul_comm whitener.adjugate (gap.adjugate * (whitener.adjugate)ᵀ),
      Matrix.mul_assoc, hpair, hscale, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      kFourGapInvariantTwo, ← hmomentDef, ← hgapDef]
  have hcontract : whitened.PosDef := by
    refine posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos
      (isHermitian_of_transpose_eq hwhitenedSymm) ?_ ?_ ?_
    · rw [htraceWhitened]; positivity
    · rw [hsecondWhitened]; positivity
    · rw [hdetWhitened]; positivity
  exact (posDef_congr_right hgapSymm hunit).mpr hcontract

/-- **THE COMPLETE INVARIANT CRITERION.**  Strict domination of a chart
selection IS the positivity of the two adjugate-trace invariants together with
the gap determinant. -/
-- AUDIT-DUPLICATE (2026-08-17): this equivalence has ZERO consumers, while its
-- rewrite-twin `Gtz.posDef_directionChartGap_iff_forestTriple` (same file) has
-- two, and that twin is proved BY calling this one.  A third copy of the same
-- criterion sits in `Gtz.posDef_directionChartGap_iff_rawTriple`
-- (Gtz/Wave/KFourTreeSumSign.lean), which routes through the Descartes
-- criterion instead of the adjugate.  Three names, one theorem.
theorem posDef_directionChartGap_iff_invariantTriple (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) :
    (directionChartGap kFourDirection point.mass point.weight selected).PosDef
      ↔ (0 < kFourGapInvariantOne point.mass point.weight selected
        ∧ 0 < kFourGapInvariantTwo point.mass point.weight selected
        ∧ 0 < (directionChartGap kFourDirection point.mass point.weight
            selected).det) := by
  constructor
  · intro hpd
    exact ⟨kFourGapInvariantOne_pos_of_posDef point selected hpd,
      kFourGapInvariantTwo_pos_of_posDef point selected hpd, hpd.det_pos⟩
  · rintro ⟨hone, htwo, hdet⟩
    exact posDef_directionChartGap_of_invariantTriple point selected hone htwo hdet

/-- **THE COMPLETE FOREST CRITERION.**  Strict domination of a chart selection is
THREE spanning-forest sums of the signed gap weight, and no matrix appears
anywhere in the statement: the signed weights against the mass forest, the
masses against the signed forest, and the sixteen-term signed tree sum. -/
theorem posDef_directionChartGap_iff_forestTriple (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) :
    (directionChartGap kFourDirection point.mass point.weight selected).PosDef
      ↔ (0 < ∑ label, signedGapWeight point.mass point.weight selected label
              * kFourContractionTreePolynomial point.mass label
        ∧ 0 < ∑ label, point.mass label
              * kFourContractionTreePolynomial
                  (signedGapWeight point.mass point.weight selected) label
        ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight selected)) := by
  have hweight : ∀ label ∈ selected, point.weight label ≠ 0 :=
    fun label _ => (point.weight_pos label).ne'
  rw [posDef_directionChartGap_iff_invariantTriple,
    kFourGapInvariantOne_eq_forestSum point.mass point.weight hweight,
    kFourGapInvariantTwo_eq_forestSum point.mass point.weight hweight,
    det_directionChartGap_eq_kFourMassTreeSum point.mass point.weight selected hweight]

/-! ## 9. The Frobenius energy of a three-by-three form -/

/-- The sum of the squares of every entry. -/
noncomputable def frobeniusEnergy (mat : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ rowIndex, ∑ colIndex, mat rowIndex colIndex ^ 2

/-- For a symmetric matrix the Frobenius energy is the trace of the square. -/
theorem frobeniusEnergy_eq_trace_sq {mat : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : matᵀ = mat) : frobeniusEnergy mat = Matrix.trace (mat * mat) := by
  have hentry : ∀ rowIndex colIndex : Fin 3,
      mat colIndex rowIndex = mat rowIndex colIndex := by
    intro rowIndex colIndex
    have := congrFun (congrFun hsymm rowIndex) colIndex
    simpa [Matrix.transpose_apply] using this
  rw [frobeniusEnergy, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun rowIndex _ =>
    Finset.sum_congr rfl fun colIndex _ => by rw [hentry rowIndex colIndex]; ring

/-- **THE FROBENIUS BOUND.**  Cauchy-Schwarz twice: the quadratic form of a
matrix is capped by its Frobenius energy against the squared probe norm. -/
theorem quadForm_sq_le_frobeniusEnergy (mat : Matrix (Fin 3) (Fin 3) ℝ)
    (probe : Fin 3 → ℝ) :
    (probe ⬝ᵥ (mat *ᵥ probe)) ^ 2 ≤ frobeniusEnergy mat * (probe ⬝ᵥ probe) ^ 2 := by
  have hrow : ∀ rowIndex : Fin 3,
      (mat *ᵥ probe) rowIndex ^ 2
        ≤ (∑ colIndex, mat rowIndex colIndex ^ 2) * (probe ⬝ᵥ probe) := by
    intro rowIndex
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
      (fun colIndex => mat rowIndex colIndex) (fun colIndex => probe colIndex)
    have hprobe : ∑ colIndex, probe colIndex ^ 2 = probe ⬝ᵥ probe := by
      rw [dotProduct]
      exact Finset.sum_congr rfl fun colIndex _ => (pow_two _)
    rw [hprobe] at hcs
    simpa [Matrix.mulVec, dotProduct] using hcs
  have hnorm : (mat *ᵥ probe) ⬝ᵥ (mat *ᵥ probe)
      ≤ frobeniusEnergy mat * (probe ⬝ᵥ probe) := by
    rw [dotProduct, frobeniusEnergy, Finset.sum_mul]
    refine Finset.sum_le_sum fun rowIndex _ => ?_
    have := hrow rowIndex
    nlinarith [this]
  have hcross : (probe ⬝ᵥ (mat *ᵥ probe)) ^ 2
      ≤ (probe ⬝ᵥ probe) * ((mat *ᵥ probe) ⬝ᵥ (mat *ᵥ probe)) :=
    dotProduct_sq_le_mul probe (mat *ᵥ probe)
  have hself : (0 : ℝ) ≤ probe ⬝ᵥ probe := dotProduct_self_nonneg probe
  nlinarith [hcross, hnorm, hself]

/-- **THE SHIFTED FROBENIUS CONTRACTION.**  A symmetric matrix whose SHIFTED
Frobenius energy falls below the squared shift defect is strictly dominated by
the identity.  The shift is free: at shift zero this is the plain Frobenius
test, and a positive shift trades trace against spread.  No positive
semidefiniteness is used anywhere. -/
theorem posDef_one_sub_of_shifted_frobeniusEnergy {mat : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : matᵀ = mat) {shift : ℝ} (hshift : shift < 1)
    (hsmall : frobeniusEnergy (mat - shift • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      < (1 - shift) ^ 2) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) - mat).PosDef := by
  set centered : Matrix (Fin 3) (Fin 3) ℝ := mat - shift • 1 with hcentered
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq ?_, ?_⟩
  · rw [Matrix.transpose_sub, Matrix.transpose_one, hsymm]
  · intro probe hne
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
    have hselfPos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hne
    have hselfSq : (0 : ℝ) < (probe ⬝ᵥ probe) ^ 2 := by positivity
    have hsplit : probe ⬝ᵥ (centered *ᵥ probe)
        = probe ⬝ᵥ (mat *ᵥ probe) - shift * (probe ⬝ᵥ probe) := by
      rw [hcentered, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
        dotProduct_smul, smul_eq_mul, Matrix.one_mulVec]
    have hbound := quadForm_sq_le_frobeniusEnergy centered probe
    have hdefect : (0 : ℝ) < 1 - shift := by linarith
    have hcentSmall : probe ⬝ᵥ (centered *ᵥ probe) < (1 - shift) * (probe ⬝ᵥ probe) := by
      by_contra hcon
      push Not at hcon
      have hsq : ((1 - shift) * (probe ⬝ᵥ probe)) ^ 2
          ≤ (probe ⬝ᵥ (centered *ᵥ probe)) ^ 2 := by
        nlinarith [hcon, mul_pos hdefect hselfPos]
      nlinarith [hbound, hsq,
        mul_pos (sub_pos.mpr hsmall) hselfSq]
    rw [hsplit] at hcentSmall
    nlinarith [hcentSmall, hselfPos]

/-- The unshifted contraction: Frobenius energy below one. -/
theorem posDef_one_sub_of_frobeniusEnergy_lt_one {mat : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : matᵀ = mat) (hsmall : frobeniusEnergy mat < 1) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) - mat).PosDef := by
  refine posDef_one_sub_of_shifted_frobeniusEnergy hsymm (shift := 0) (by norm_num) ?_
  simpa using hsmall

/-! ## 9. The Frobenius cell, in adjugate form -/

-- AUDIT-UNCONSUMED (2026-08-17): sections 8 and 9 hold the only generic Loewner
-- domination tools in the `M(K4)` lane, and ALL THREE have zero consumers:
-- `Gtz.posDef_one_sub_of_shifted_frobeniusEnergy`,
-- `Gtz.posDef_one_sub_of_frobeniusEnergy_lt_one` and
-- `Gtz.posDef_sub_of_shifted_trace_adjugate`.  The second is the shift-zero
-- corollary of the first, so it is also SUPERSEDED.
-- AUDIT-BOGUS-PREMISE (2026-08-17): the lane record states that closing this
-- class needs spectral input that the repo does not have, and cites
-- `0 ≺ Q ⪯ I ⇒ Q ⪰ (det Q) • 1` as FALSE.  That implication is TRUE, and the
-- repo proves it: `Gtz.det_le_eigenvalue_of_posSemidef_of_posSemidef_one_sub`
-- (Gtz/Quantitative/CauchyBinetValueFloor.lean), because every eigenvalue of a
-- contraction lies in `[0,1]`, so factoring one out leaves a product below one.
-- The Loewner form follows from `Gtz.posSemidef_sub_smul_one_of_eigenvalue_ge`
-- (Gtz/Reduction/ExchangeInvariant.lean).  The quoted counterexample at
-- invariants `(2, 1.95, 0.95)` is not a contraction: a symmetric `3x3` with
-- every eigenvalue at most one and trace two has determinant at most `8/27`.
-- No workaround is necessary.

/-- **THE SHIFTED FROBENIUS CELL, GENERIC.**  A positive definite matrix
strictly dominates a symmetric one as soon as one shifted adjugate trace test
passes.  The shift is a free rational parameter, the determinant carries all the
normalisation, and nothing here is a Loewner comparison, an eigenvalue or a
square root. -/
theorem posDef_sub_of_shifted_trace_adjugate {big small : Matrix (Fin 3) (Fin 3) ℝ}
    (hbig : big.PosDef) (hsymmSmall : smallᵀ = small) {shift : ℝ} (hshift : shift < 1)
    (hcrit : Matrix.trace ((big.adjugate * small) * (big.adjugate * small))
        - 2 * shift * big.det * Matrix.trace (big.adjugate * small)
        + 3 * shift ^ 2 * big.det ^ 2
      < (1 - shift) ^ 2 * big.det ^ 2) :
    (big - small).PosDef := by
  obtain ⟨whitener, hunit, hone⟩ := exists_congruence_to_one hbig
  have hunitT : IsUnit (whitenerᵀ).det := by rwa [Matrix.det_transpose]
  have hdet : 0 < big.det := hbig.det_pos
  have hright : big * (whitener * whitenerᵀ) = 1 := by
    have hstep : (whitenerᵀ)⁻¹ = big * whitener :=
      Matrix.inv_eq_right_inv (by rw [← Matrix.mul_assoc]; exact hone)
    rw [← Matrix.mul_assoc, ← hstep, Matrix.nonsing_inv_mul _ hunitT]
  have hadj : big.adjugate = big.det • (whitener * whitenerᵀ) := by
    calc big.adjugate = big.adjugate * (big * (whitener * whitenerᵀ)) := by
          rw [hright, Matrix.mul_one]
      _ = (big.adjugate * big) * (whitener * whitenerᵀ) := by rw [Matrix.mul_assoc]
      _ = big.det • (whitener * whitenerᵀ) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hkernel : whitener * whitenerᵀ = (big.det)⁻¹ • big.adjugate := by
    rw [hadj, smul_smul, inv_mul_cancel₀ (ne_of_gt hdet), one_smul]
  set whitened : Matrix (Fin 3) (Fin 3) ℝ := whitenerᵀ * small * whitener with hwhitened
  have hwhitenedSymm : whitenedᵀ = whitened := by
    rw [hwhitened, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hsymmSmall, Matrix.mul_assoc]
  have hlinear : Matrix.trace whitened
      = (big.det)⁻¹ * Matrix.trace (big.adjugate * small) := by
    have hcyc : Matrix.trace whitened
        = Matrix.trace ((whitener * whitenerᵀ) * small) := by
      rw [hwhitened, Matrix.mul_assoc,
        Matrix.trace_mul_comm whitenerᵀ (small * whitener), Matrix.mul_assoc,
        Matrix.trace_mul_comm small (whitener * whitenerᵀ)]
    rw [hcyc, hkernel, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have hsquare : Matrix.trace (whitened * whitened)
      = (big.det)⁻¹ ^ 2
        * Matrix.trace ((big.adjugate * small) * (big.adjugate * small)) := by
    have hexpand : whitened * whitened
        = whitenerᵀ * ((small * (whitener * whitenerᵀ)) * small) * whitener := by
      rw [hwhitened]
      noncomm_ring
    have hcyc : Matrix.trace (whitened * whitened)
        = Matrix.trace ((whitener * whitenerᵀ)
            * ((small * (whitener * whitenerᵀ)) * small)) := by
      rw [hexpand, Matrix.trace_mul_comm
        (whitenerᵀ * ((small * (whitener * whitenerᵀ)) * small)) whitener,
        ← Matrix.mul_assoc]
    rw [hcyc, hkernel]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [show big.adjugate * (small * big.adjugate * small)
        = big.adjugate * small * (big.adjugate * small) by noncomm_ring]
    ring
  have hshiftSymm : (whitened - shift • (1 : Matrix (Fin 3) (Fin 3) ℝ))ᵀ
      = whitened - shift • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hwhitenedSymm]
  have hshiftTrace : Matrix.trace ((whitened - shift • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        * (whitened - shift • (1 : Matrix (Fin 3) (Fin 3) ℝ)))
      = Matrix.trace (whitened * whitened) - 2 * shift * Matrix.trace whitened
        + 3 * shift ^ 2 := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
      Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Fintype.card_fin]
    push_cast
    ring
  have henergy : frobeniusEnergy (whitened - shift • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      < (1 - shift) ^ 2 := by
    rw [frobeniusEnergy_eq_trace_sq hshiftSymm, hshiftTrace, hsquare, hlinear]
    have hdetNe : big.det ≠ 0 := ne_of_gt hdet
    have hD2 : (0 : ℝ) < big.det ^ 2 := by positivity
    by_contra hcon
    push Not at hcon
    have hmul := mul_le_mul_of_nonneg_right hcon (le_of_lt hD2)
    have hexpand : ((big.det)⁻¹ ^ 2
          * Matrix.trace ((big.adjugate * small) * (big.adjugate * small))
        - 2 * shift * ((big.det)⁻¹ * Matrix.trace (big.adjugate * small))
        + 3 * shift ^ 2) * big.det ^ 2
        = Matrix.trace ((big.adjugate * small) * (big.adjugate * small))
          - 2 * shift * big.det * Matrix.trace (big.adjugate * small)
          + 3 * shift ^ 2 * big.det ^ 2 := by
      field_simp
    rw [hexpand] at hmul
    linarith [hcrit, hmul]
  have hcontract : ((1 : Matrix (Fin 3) (Fin 3) ℝ) - whitened).PosDef :=
    posDef_one_sub_of_shifted_frobeniusEnergy hwhitenedSymm hshift henergy
  have hsymmDiff : (big - small)ᵀ = big - small := by
    rw [Matrix.transpose_sub, transpose_eq_of_isHermitian hbig.1, hsymmSmall]
  refine (posDef_congr_right hsymmDiff hunit).mpr ?_
  have hsplit : whitenerᵀ * (big - small) * whitener
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) - whitened := by
    rw [hwhitened, Matrix.mul_sub, Matrix.sub_mul, hone]
  rw [hsplit]
  exact hcontract

/-! ## 10. The pencil energy of a chart selection -/

/-- The pencil energy: the trace of the square of the adjugate product.  It is
the Frobenius energy of the whitened mass moment, cleared of denominators. -/
noncomputable def kFourPencilEnergy (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : ℝ :=
  Matrix.trace
    (((kFourLaplacian (kFourGapConductance mass weight selected)).adjugate
        * kFourLaplacian mass)
      * ((kFourLaplacian (kFourGapConductance mass weight selected)).adjugate
        * kFourLaplacian mass))

theorem trace_adjugate_conductance_mul_mass (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) :
    Matrix.trace ((kFourLaplacian (kFourGapConductance mass weight selected)).adjugate
        * kFourLaplacian mass)
      = kFourPencilSecond mass weight selected :=
  trace_adjugate_kFourLaplacian_mul _ _

theorem trace_adjugate_mass_mul_conductance (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) :
    Matrix.trace ((kFourLaplacian mass).adjugate
        * kFourLaplacian (kFourGapConductance mass weight selected))
      = kFourPencilThird mass weight selected :=
  trace_adjugate_kFourLaplacian_mul _ _

/-- **THE PENCIL ENERGY IS A FOREST POLYNOMIAL.**  Newton at size three plus the
adjugate of an adjugate turn the whitened Frobenius energy into two forest sums:
the squared second coefficient less twice the product of the outer two. -/
theorem kFourPencilEnergy_eq_pencil (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) :
    kFourPencilEnergy mass weight selected
      = kFourPencilSecond mass weight selected ^ 2
        - 2 * kFourPencilLead mass weight selected
            * kFourPencilThird mass weight selected := by
  have hadjY : ((kFourLaplacian (kFourGapConductance mass weight selected)).adjugate
        * kFourLaplacian mass).adjugate
      = (kFourLaplacian (kFourGapConductance mass weight selected)).det
        • ((kFourLaplacian mass).adjugate
          * kFourLaplacian (kFourGapConductance mass weight selected)) := by
    rw [Matrix.adjugate_mul_distrib, adjugate_adjugate_fin_three, Matrix.mul_smul]
  rw [kFourPencilEnergy, trace_sq_fin_three, hadjY, Matrix.trace_smul, smul_eq_mul,
    trace_adjugate_conductance_mul_mass, trace_adjugate_mass_mul_conductance,
    det_kFourLaplacian, ← kFourPencilLead]
  ring

/-! ## 11. The pencil cell, and what it closes -/

/-- **THE PENCIL CELL AT A SELECTION.**  Three polynomial inequalities in the
four forest coefficients.  No matrix, no eigenvalue, no square root, no
deflation bound and no determinant sign. -/
def KFourPencilCellFires (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) : Prop :=
  0 < kFourPencilLead point.mass point.weight selected
    ∧ kFourPencilSecond point.mass point.weight selected
        < 3 * kFourPencilLead point.mass point.weight selected
    ∧ kFourPencilSecond point.mass point.weight selected ^ 2
        + 2 * kFourPencilSecond point.mass point.weight selected
            * kFourPencilLead point.mass point.weight selected
      < 3 * kFourPencilLead point.mass point.weight selected ^ 2
        + 4 * kFourPencilLead point.mass point.weight selected
            * kFourPencilThird point.mass point.weight selected

/-- **THE CELL PRODUCES A STRICTLY DOMINATING SELECTION.**  The optimal shift is
the rational number `(P2 - P3) / (2 * P3)`, and the shifted Frobenius test at
that shift is exactly the third inequality of the cell. -/
theorem posDef_directionChartGap_of_pencilCell (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (hcell : KFourPencilCellFires point selected) :
    (directionChartGap kFourDirection point.mass point.weight selected).PosDef := by
  obtain ⟨hlead, hspread, hcrit⟩ := hcell
  set lead := kFourPencilLead point.mass point.weight selected with hleadDef
  set second := kFourPencilSecond point.mass point.weight selected with hsecondDef
  set third := kFourPencilThird point.mass point.weight selected with hthirdDef
  have hbig : (kFourLaplacian
      (kFourGapConductance point.mass point.weight selected)).PosDef :=
    posDef_kFourLaplacian_of_det_pos _ (kFourGapConductance_nonneg point selected) hlead
  have hdetBig : (kFourLaplacian
      (kFourGapConductance point.mass point.weight selected)).det = lead :=
    det_kFourLaplacian _
  set shift : ℝ := (second - lead) / (2 * lead) with hshiftDef
  have hleadNe : lead ≠ 0 := ne_of_gt hlead
  have hshiftLt : shift < 1 := by
    rw [hshiftDef, div_lt_one (by linarith)]
    linarith
  rw [directionChartGap_eq_kFourLaplacian_sub]
  refine posDef_sub_of_shifted_trace_adjugate hbig (kFourLaplacian_transpose point.mass)
    hshiftLt ?_
  rw [trace_adjugate_conductance_mul_mass, hdetBig, ← hsecondDef]
  have henergy : Matrix.trace
      (((kFourLaplacian (kFourGapConductance point.mass point.weight selected)).adjugate
          * kFourLaplacian point.mass)
        * ((kFourLaplacian (kFourGapConductance point.mass point.weight selected)).adjugate
          * kFourLaplacian point.mass))
      = second ^ 2 - 2 * lead * third := by
    rw [← kFourPencilEnergy, kFourPencilEnergy_eq_pencil]
  rw [henergy, hshiftDef]
  have hexpand : second ^ 2 - 2 * lead * third
      - 2 * ((second - lead) / (2 * lead)) * lead * second
      + 3 * ((second - lead) / (2 * lead)) ^ 2 * lead ^ 2
      = second ^ 2 - 2 * lead * third - (second ^ 2 - lead * second)
        + 3 * (second - lead) ^ 2 / 4 := by
    field_simp
    ring
  have hright : (1 - (second - lead) / (2 * lead)) ^ 2 * lead ^ 2
      = (3 * lead - second) ^ 2 / 4 := by
    field_simp
    ring
  rw [hexpand, hright]
  nlinarith [hcrit]

theorem card_eq_three_of_mem_kFourSpanningTreeList' {tree : Finset (Fin 6)}
    (hmem : tree ∈ kFourSpanningTreeList) : tree.card = 3 := by
  revert hmem
  revert tree
  decide

/-- **THE UNIVERSAL STRICT TREE.**  Some listed spanning tree dominates strictly
at every chart point. -/
def KFourUniversalStrictTree : Prop :=
  ∀ point : DirectionChartPoint 6, ∃ tree ∈ kFourSpanningTreeList,
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- **THE UNIVERSAL STRICT TREE CLOSES BOTH TERMINAL WALLS.**  Each wall
conclusion is a strictly dominating listed tree, so every wall hypothesis is
discarded pointwise. -/
theorem kFourGaugeAndPivotWallClosure_of_universalStrictTree
    (hstrict : KFourUniversalStrictTree) : KFourGaugeAndPivotWallClosure :=
  ⟨fun point _ _ _ _ _ => hstrict point, fun point _ _ => hstrict point⟩

/-- **THE UNIVERSAL STRICT TREE CLOSES THE WHOLE `K4` CHART.**  The registered
chart obligation `Gtz.DirectionChartIsTieFree Gtz.kFourDirection` is a strictly
dominating card-three selection at every weakly dominated chart point, and the
weak antecedent is discarded pointwise. -/
theorem directionChartHasStrictTriple_kFour_of_universalStrictTree
    (hstrict : KFourUniversalStrictTree) :
    DirectionChartHasStrictTriple kFourDirection := by
  intro point
  obtain ⟨tree, hmem, hpd⟩ := hstrict point
  exact ⟨tree, card_eq_three_of_mem_kFourSpanningTreeList' hmem, hpd⟩

theorem directionChartIsTieFree_kFour_of_universalStrictTree
    (hstrict : KFourUniversalStrictTree) : DirectionChartIsTieFree kFourDirection :=
  directionChartIsTieFree_of_hasStrictTriple
    (directionChartHasStrictTriple_kFour_of_universalStrictTree hstrict)

/-- The registered `A3` formula from the universal strict tree. -/
theorem kFourKnifeBandRefinedAllMaxHeavyWall_of_universalStrictTree
    (hstrict : KFourUniversalStrictTree) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_universalStrictTree hstrict)

/-- **THE WHOLE `K4` CHART OBLIGATION AS THREE FOREST SUMS PER TREE.**  At every
chart point some listed spanning tree makes three spanning-forest sums of its
own signed gap weight positive.  No matrix, no whitener, no square root, no
determinant of a design, no deflation bound, no corank hypothesis and no weak
antecedent occur anywhere in this statement. -/
def KFourForestTripleTotal : Prop :=
  ∀ point : DirectionChartPoint 6, ∃ tree ∈ kFourSpanningTreeList,
    0 < ∑ label, signedGapWeight point.mass point.weight tree label
          * kFourContractionTreePolynomial point.mass label
      ∧ 0 < ∑ label, point.mass label
          * kFourContractionTreePolynomial
              (signedGapWeight point.mass point.weight tree) label
      ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)

/-- **THE REDUCTION IS AN EQUIVALENCE.**  The forest triple total is not a
sufficient condition that a hunt can refute.  It IS the universal strict
tree. -/
theorem kFourUniversalStrictTree_iff_forestTripleTotal :
    KFourUniversalStrictTree ↔ KFourForestTripleTotal := by
  constructor
  · intro hstrict point
    obtain ⟨tree, hmem, hpd⟩ := hstrict point
    exact ⟨tree, hmem, (posDef_directionChartGap_iff_forestTriple point tree).mp hpd⟩
  · intro htotal point
    obtain ⟨tree, hmem, htriple⟩ := htotal point
    exact ⟨tree, hmem, (posDef_directionChartGap_iff_forestTriple point tree).mpr htriple⟩

/-- **THE WHOLE `K4` CHART OBLIGATION FROM THE FOREST TRIPLE.** -/
theorem directionChartIsTieFree_kFour_of_forestTripleTotal
    (htotal : KFourForestTripleTotal) : DirectionChartIsTieFree kFourDirection :=
  directionChartIsTieFree_kFour_of_universalStrictTree
    (kFourUniversalStrictTree_iff_forestTripleTotal.mpr htotal)

/-- The registered `A3` component route from the forest triple. -/
theorem kFourGaugeAndPivotWallClosure_of_forestTripleTotal
    (htotal : KFourForestTripleTotal) : KFourGaugeAndPivotWallClosure :=
  kFourGaugeAndPivotWallClosure_of_universalStrictTree
    (kFourUniversalStrictTree_iff_forestTripleTotal.mpr htotal)

/-- The registered `A3` formula from the forest triple. -/
theorem kFourKnifeBandRefinedAllMaxHeavyWall_of_forestTripleTotal
    (htotal : KFourForestTripleTotal) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  kFourKnifeBandRefinedAllMaxHeavyWall_of_universalStrictTree
    (kFourUniversalStrictTree_iff_forestTripleTotal.mpr htotal)

/-- Every firing of the pencil cell is a firing of the forest triple, so the
cell is a strictly weaker producer and the triple is what survives. -/
theorem forestTriple_of_pencilCell (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (hcell : KFourPencilCellFires point selected) :
    0 < ∑ label, signedGapWeight point.mass point.weight selected label
          * kFourContractionTreePolynomial point.mass label
      ∧ 0 < ∑ label, point.mass label
          * kFourContractionTreePolynomial
              (signedGapWeight point.mass point.weight selected) label
      ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight selected) :=
  (posDef_directionChartGap_iff_forestTriple point selected).mp
    (posDef_directionChartGap_of_pencilCell point selected hcell)

/-! ## 12. The cell at the five named chart points -/

/-- Reading the cell off three numeric coefficients. -/
theorem pencilCellFires_of_values (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) {lead second third : ℝ}
    (hlead : kFourPencilLead point.mass point.weight selected = lead)
    (hsecond : kFourPencilSecond point.mass point.weight selected = second)
    (hthird : kFourPencilThird point.mass point.weight selected = third)
    (hpos : 0 < lead) (hspread : second < 3 * lead)
    (hcell : second ^ 2 + 2 * second * lead < 3 * lead ^ 2 + 4 * lead * third) :
    KFourPencilCellFires point selected := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hlead]; exact hpos
  · rw [hlead, hsecond]; exact hspread
  · rw [hlead, hsecond, hthird]; exact hcell

theorem kFourGapConductance_mem (mass weight : Fin 6 → ℝ) {selected : Finset (Fin 6)}
    {label : Fin 6} (hmem : label ∈ selected) :
    kFourGapConductance mass weight selected label = mass label / weight label := by
  simp only [kFourGapConductance, hmem, ite_true]

theorem kFourGapConductance_not_mem (mass weight : Fin 6 → ℝ) {selected : Finset (Fin 6)}
    {label : Fin 6} (hmem : label ∉ selected) :
    kFourGapConductance mass weight selected label = 0 := by
  simp only [kFourGapConductance, hmem, ite_false]

/-- **THE CELL FIRES AT THE TETRAHEDRON.**  The vertex star `{0, 1, 3}` carries
lead `27/8`, second `81/16` and third `9/4`. -/
theorem tetrahedronChartPoint_pencilCellFires :
    KFourPencilCellFires tetrahedronChartPoint ({0, 1, 3} : Finset (Fin 6)) := by
  have hzero := kFourGapConductance_mem tetrahedronChartPoint.mass
    tetrahedronChartPoint.weight (show (0 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hone := kFourGapConductance_mem tetrahedronChartPoint.mass
    tetrahedronChartPoint.weight (show (1 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have htwo := kFourGapConductance_not_mem tetrahedronChartPoint.mass
    tetrahedronChartPoint.weight (show (2 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hthree := kFourGapConductance_mem tetrahedronChartPoint.mass
    tetrahedronChartPoint.weight (show (3 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hfour := kFourGapConductance_not_mem tetrahedronChartPoint.mass
    tetrahedronChartPoint.weight (show (4 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hfive := kFourGapConductance_not_mem tetrahedronChartPoint.mass
    tetrahedronChartPoint.weight (show (5 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [kFourPencilLead, kFourPencilSecond, kFourPencilThird, kFourMassTreeSum,
      Fin.sum_univ_six, kFourContractionTreePolynomial_zero,
      kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
      kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
      kFourContractionTreePolynomial_five, hzero, hone, htwo, hthree, hfour, hfive] <;>
    norm_num [tetrahedronChartPoint]

/-- **THE CELL FIRES AT THE CANONICAL BAND INHABITANT.**  The registry's
canonical residual witness, uncovered by both landed regions, carries lead
`80000`, second `81500` and third `18220`. -/
theorem bandResidualWitnessPoint_pencilCellFires :
    KFourPencilCellFires bandResidualWitnessPoint ({0, 1, 3} : Finset (Fin 6)) := by
  have hzero := kFourGapConductance_mem bandResidualWitnessPoint.mass
    bandResidualWitnessPoint.weight
    (show (0 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hone := kFourGapConductance_mem bandResidualWitnessPoint.mass
    bandResidualWitnessPoint.weight
    (show (1 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have htwo := kFourGapConductance_not_mem bandResidualWitnessPoint.mass
    bandResidualWitnessPoint.weight
    (show (2 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hthree := kFourGapConductance_mem bandResidualWitnessPoint.mass
    bandResidualWitnessPoint.weight
    (show (3 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hfour := kFourGapConductance_not_mem bandResidualWitnessPoint.mass
    bandResidualWitnessPoint.weight
    (show (4 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hfive := kFourGapConductance_not_mem bandResidualWitnessPoint.mass
    bandResidualWitnessPoint.weight
    (show (5 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [kFourPencilLead, kFourPencilSecond, kFourPencilThird, kFourMassTreeSum,
      Fin.sum_univ_six, kFourContractionTreePolynomial_zero,
      kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
      kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
      kFourContractionTreePolynomial_five, hzero, hone, htwo, hthree, hfour, hfive] <;>
    norm_num [bandResidualWitnessPoint, bandResidualWitnessMass, bandResidualWitnessWeight]

/-- **THE CELL FIRES ON THE CORANK-TWO GAUGE WALL.**  At the canonical wall
witness the vertex star `{0, 1, 3}` carries lead `576`, second `720` and third
`224`.  The landed isotropic cell can never fire there. -/
theorem kFourGaugeWallPoint_pencilCellFires :
    KFourPencilCellFires kFourGaugeWallPoint ({0, 1, 3} : Finset (Fin 6)) := by
  have hzero := kFourGapConductance_mem kFourGaugeWallPoint.mass
    kFourGaugeWallPoint.weight (show (0 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hone := kFourGapConductance_mem kFourGaugeWallPoint.mass
    kFourGaugeWallPoint.weight (show (1 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have htwo := kFourGapConductance_not_mem kFourGaugeWallPoint.mass
    kFourGaugeWallPoint.weight (show (2 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hthree := kFourGapConductance_mem kFourGaugeWallPoint.mass
    kFourGaugeWallPoint.weight (show (3 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hfour := kFourGapConductance_not_mem kFourGaugeWallPoint.mass
    kFourGaugeWallPoint.weight (show (4 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide)
  have hfive := kFourGapConductance_not_mem kFourGaugeWallPoint.mass
    kFourGaugeWallPoint.weight (show (5 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [kFourPencilLead, kFourPencilSecond, kFourPencilThird, kFourMassTreeSum,
      Fin.sum_univ_six, kFourContractionTreePolynomial_zero,
      kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
      kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
      kFourContractionTreePolynomial_five, hzero, hone, htwo, hthree, hfour, hfive] <;>
    norm_num [kFourGaugeWallPoint, kFourGaugeWallMass, kFourGaugeWallWeight]

/-- **THE CELL FIRES AT THE MAX-CONDUCTANCE REFUTER.**  The tree `{0, 2, 4}`
carries lead `4800`, second `17167/3` and third `5599241/3600`. -/
theorem maxEdgeRefuterPoint_pencilCellFires :
    KFourPencilCellFires maxEdgeRefuterPoint ({0, 2, 4} : Finset (Fin 6)) := by
  have hzero := kFourGapConductance_mem maxEdgeRefuterPoint.mass
    maxEdgeRefuterPoint.weight (show (0 : Fin 6) ∈ ({0, 2, 4} : Finset (Fin 6)) by decide)
  have hone := kFourGapConductance_not_mem maxEdgeRefuterPoint.mass
    maxEdgeRefuterPoint.weight (show (1 : Fin 6) ∉ ({0, 2, 4} : Finset (Fin 6)) by decide)
  have htwo := kFourGapConductance_mem maxEdgeRefuterPoint.mass
    maxEdgeRefuterPoint.weight (show (2 : Fin 6) ∈ ({0, 2, 4} : Finset (Fin 6)) by decide)
  have hthree := kFourGapConductance_not_mem maxEdgeRefuterPoint.mass
    maxEdgeRefuterPoint.weight (show (3 : Fin 6) ∉ ({0, 2, 4} : Finset (Fin 6)) by decide)
  have hfour := kFourGapConductance_mem maxEdgeRefuterPoint.mass
    maxEdgeRefuterPoint.weight (show (4 : Fin 6) ∈ ({0, 2, 4} : Finset (Fin 6)) by decide)
  have hfive := kFourGapConductance_not_mem maxEdgeRefuterPoint.mass
    maxEdgeRefuterPoint.weight (show (5 : Fin 6) ∉ ({0, 2, 4} : Finset (Fin 6)) by decide)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [kFourPencilLead, kFourPencilSecond, kFourPencilThird, kFourMassTreeSum,
      Fin.sum_univ_six, kFourContractionTreePolynomial_zero,
      kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
      kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
      kFourContractionTreePolynomial_five, hzero, hone, htwo, hthree, hfour, hfive] <;>
    norm_num [maxEdgeRefuterPoint, maxEdgeRefuterMass, maxEdgeRefuterWeight]

/-- **THE CELL FIRES AT THE HEAVY-PAIR REFUTER.**  The canonical gauge star
`{3, 4, 5}` carries lead `14400`, second `45373/3` and third `8819921/3600`. -/
theorem heavyPairRefuterPoint_pencilCellFires :
    KFourPencilCellFires heavyPairRefuterPoint ({3, 4, 5} : Finset (Fin 6)) := by
  have hzero := kFourGapConductance_not_mem heavyPairRefuterPoint.mass
    heavyPairRefuterPoint.weight
    (show (0 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6)) by decide)
  have hone := kFourGapConductance_not_mem heavyPairRefuterPoint.mass
    heavyPairRefuterPoint.weight
    (show (1 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6)) by decide)
  have htwo := kFourGapConductance_not_mem heavyPairRefuterPoint.mass
    heavyPairRefuterPoint.weight
    (show (2 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6)) by decide)
  have hthree := kFourGapConductance_mem heavyPairRefuterPoint.mass
    heavyPairRefuterPoint.weight
    (show (3 : Fin 6) ∈ ({3, 4, 5} : Finset (Fin 6)) by decide)
  have hfour := kFourGapConductance_mem heavyPairRefuterPoint.mass
    heavyPairRefuterPoint.weight
    (show (4 : Fin 6) ∈ ({3, 4, 5} : Finset (Fin 6)) by decide)
  have hfive := kFourGapConductance_mem heavyPairRefuterPoint.mass
    heavyPairRefuterPoint.weight
    (show (5 : Fin 6) ∈ ({3, 4, 5} : Finset (Fin 6)) by decide)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [kFourPencilLead, kFourPencilSecond, kFourPencilThird, kFourMassTreeSum,
      Fin.sum_univ_six, kFourContractionTreePolynomial_zero,
      kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
      kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
      kFourContractionTreePolynomial_five, hzero, hone, htwo, hthree, hfour, hfive] <;>
    norm_num [heavyPairRefuterPoint, heavyPairRefuterMass, maxEdgeRefuterWeight]

/-- The named points carry strictly dominating spanning trees through the
cell alone: no deflation bound, no determinant sign, no atlas. -/
theorem tetrahedronChartPoint_pencilStrictTree :
    (directionChartGap kFourDirection tetrahedronChartPoint.mass
      tetrahedronChartPoint.weight ({0, 1, 3} : Finset (Fin 6))).PosDef :=
  posDef_directionChartGap_of_pencilCell _ _ tetrahedronChartPoint_pencilCellFires

theorem bandResidualWitnessPoint_pencilStrictTree :
    (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight ({0, 1, 3} : Finset (Fin 6))).PosDef :=
  posDef_directionChartGap_of_pencilCell _ _ bandResidualWitnessPoint_pencilCellFires

theorem kFourGaugeWallPoint_pencilStrictTree :
    (directionChartGap kFourDirection kFourGaugeWallPoint.mass
      kFourGaugeWallPoint.weight ({0, 1, 3} : Finset (Fin 6))).PosDef :=
  posDef_directionChartGap_of_pencilCell _ _ kFourGaugeWallPoint_pencilCellFires

theorem maxEdgeRefuterPoint_pencilStrictTree :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight ({0, 2, 4} : Finset (Fin 6))).PosDef :=
  posDef_directionChartGap_of_pencilCell _ _ maxEdgeRefuterPoint_pencilCellFires

theorem heavyPairRefuterPoint_pencilStrictTree :
    (directionChartGap kFourDirection heavyPairRefuterPoint.mass
      heavyPairRefuterPoint.weight ({3, 4, 5} : Finset (Fin 6))).PosDef :=
  posDef_directionChartGap_of_pencilCell _ _ heavyPairRefuterPoint_pencilCellFires

/-! ## 13. The cell is NOT total, and the witness

A uniform census is not an adjudication.  The cell fires at every one of four
thousand exact chart points drawn from five regimes, at all five named points,
and at fourteen thousand seven hundred exact points of the corank-two gauge
wall.  A directed hunt of four hundred thousand restarts, maximizing the worst
cell margin over the sixteen trees, walks out of that region in one climb.  The
witness below is the exact rational landing point of that climb.  Sixteen trees,
sixteen failures, and TWO of the sixteen are still strictly dominating: the
chart obligation is intact there and only the cell is refuted.
-/

/-- Masses of the point that refutes totality of the pencil cell. -/
noncomputable def pencilCellRefuterMass : Fin 6 → ℝ
  | 0 => 34
  | 1 => 8727
  | 2 => 24109
  | 3 => 3
  | 4 => 25102
  | 5 => 29115

/-- Weights of the point that refutes totality of the pencil cell. -/
noncomputable def pencilCellRefuterWeight : Fin 6 → ℝ
  | 0 => 1 / 500
  | 1 => 1 / 500
  | 2 => 291 / 1000
  | 3 => 1 / 500
  | 4 => 319 / 1000
  | 5 => 48 / 125

/-- The refuter is a genuine chart point. -/
noncomputable def pencilCellRefuterPoint : DirectionChartPoint 6 where
  mass := pencilCellRefuterMass
  weight := pencilCellRefuterWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [pencilCellRefuterMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [pencilCellRefuterWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [pencilCellRefuterWeight]

/-- **NO LISTED TREE FIRES THE CELL AT THE REFUTER.**  Ten of the sixteen fail
the spread inequality and six fail the shifted Frobenius inequality. -/
theorem pencilCellRefuterPoint_no_cell (tree : Finset (Fin 6))
    (hmem : tree ∈ kFourSpanningTreeList) :
    ¬ KFourPencilCellFires pencilCellRefuterPoint tree := by
  rintro ⟨-, hspread, hcell⟩
  revert hspread hcell
  simp only [kFourSpanningTreeList, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl <;>
    simp only [kFourPencilLead, kFourPencilSecond, kFourPencilThird, kFourMassTreeSum,
      Fin.sum_univ_six, kFourContractionTreePolynomial_zero,
      kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
      kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
      kFourContractionTreePolynomial_five, kFourGapConductance] <;>
    norm_num [pencilCellRefuterPoint, pencilCellRefuterMass, pencilCellRefuterWeight,
      Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

/-- **THE PENCIL CELL IS NOT TOTAL.**  Stated inline, with no named proposition:
an unsatisfiable antecedent must not be left standing as an asset. -/
theorem kFourPencilCell_not_total :
    ¬ (∀ point : DirectionChartPoint 6, ∃ tree ∈ kFourSpanningTreeList,
        KFourPencilCellFires point tree) := by
  intro htotal
  obtain ⟨tree, hmem, hcell⟩ := htotal pencilCellRefuterPoint
  exact pencilCellRefuterPoint_no_cell tree hmem hcell

/-- The gap of the tree `{1, 2, 5}` at the refuter, entry by entry. -/
theorem pencilCellRefuter_gap_oneTwoFive :
    directionChartGap kFourDirection pencilCellRefuterPoint.mass
        pencilCellRefuterPoint.weight ({1, 2, 5} : Finset (Fin 6))
      = !![(4354736 : ℝ), 34, -4354773;
           34, 9778705/291, -17093281/291;
           -4354773, -17093281/291, 20766775519/4656] := by
  rw [directionChartGap_eq_signedLaplacian _ _ _
    (fun label _ => (pencilCellRefuterPoint.weight_pos label).ne')]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [signedGapWeight, pencilCellRefuterPoint, pencilCellRefuterMass,
      pencilCellRefuterWeight, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

/-- **THE OBLIGATION IS INTACT AT THE REFUTER.**  The tree `{1, 2, 5}` dominates
strictly, with Sylvester triple `(4354736, 42583678360484/291,
485308413794182921/1164)`.  So the refutation is about the CELL and never about
the chart obligation. -/
theorem pencilCellRefuterPoint_hasStrictTree :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection pencilCellRefuterPoint.mass
        pencilCellRefuterPoint.weight tree).PosDef := by
  refine ⟨{1, 2, 5}, by decide, ?_⟩
  rw [pencilCellRefuter_gap_oneTwoFive, leadingMinors_pos_iff_posDef_fin_three]
  norm_num

end Gtz

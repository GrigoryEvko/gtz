/-
# The all-heavy residual of both hinges, reduced to one scalar at the dropped atom

## What is landed already, and is CONSUMED here rather than proved again

* `Gtz.exists_deflatedGapBound` (Gtz/Design/StratumEmptinessLedger.lean:399) — the
  sharp deflation transport at a label whose SHARE is below one.  It returns a
  card-`rank` subset that AVOIDS the label.
* `Gtz.posDef_on_orthogonal_of_deflatedGapBound` (:475) — the transported gap is
  positive on every direction orthogonal to the dropped atom, at EVERY leverage.
  It had ZERO consumers anywhere in the tree.
* `Gtz.sum_weight_mul_leverage` (Gtz/LinAlg/ProjectionForm.lean:161) — the trace
  identity, the weighted leverages sum to the rank.
* `Gtz.sum_weight_mul_leverage_sub_one` (Gtz/Quantitative/ChartHadamard.lean:293)
  — the same identity shifted, the weighted excesses total `rank - 1`.
* `Gtz.dotProduct_subsetSum_mulVec_self` (Gtz/Wave/ArgmaxBlockFloor.lean:299).
* `Gtz.weight_mul_leverage_le_one` (Gtz/Ties/AllTied.lean:153) — the share cap.
* `Gtz.polarPairing_eq_zero_of_saturated` (Gtz/Reduction/PolarTiltLedger.lean) —
  a saturated pole is orthogonal to every other atom.
* `Gtz.dotProduct_mulVec_comm_of_transpose_eq`
  (Gtz/Reduction/TwoVanishedBoundary.lean:700).
* `Gtz.mulVec_eq_zero_of_posSemidef_of_dotProduct_zero`
  (Gtz/Quantitative/ChartSecondOrder.lean:86).
* `Gtz.leverage_one_le_of_isTie`, `Gtz.leverage_one_le_of_isTie_sixThree`,
  `Gtz.forall_leverage_one_le_of_isTie` (Gtz/Wave/LightAtomTieFloor.lean:69).

## What this file does

The two off-path hinges hold on the strictly light branch.  Their residual is the
ALL-HEAVY region.  There the deflation still runs — its hypothesis is the SHARE,
not the leverage — and it still delivers a positive floor on the whole hyperplane
orthogonal to the dropped atom.  So on the all-heavy stratum a `rank`-dimensional
positivity question has a `(rank - 1)`-dimensional half that is FREE.

Section 1 makes that precise with no design in sight, in two forms.

The SCALAR form.  A symmetric matrix with a positive margin on one hyperplane is
positive definite EXACTLY when it is positive on the affine coset
`pivot + hyperplane` (`Gtz.posDef_iff_pivotCoset`), and ONE square-root-free
scalar inequality is sufficient (`Gtz.posDef_of_pivotMargin_of_pivotSurplus`):

  `(pivot . pivot) * |gap pivot|^2 - (pivot . gap pivot)^2
      <  margin * (pivot . pivot) * (pivot . gap pivot)` .

The left side is the coupling out of the pivot direction, the right side is the
pivot surplus paid at the hyperplane margin.  No coordinate is named, no
eigenvalue appears, and the rank is free.

The LOSSLESS form.  A form that is positive definite on a hyperplane has at most
one non-positive eigenvalue, because two of them would span a plane that meets
the hyperplane.  The determinant therefore decides the last one:
`Gtz.posDef_iff_det_pos_of_planePosDef` is an EQUIVALENCE with no margin in it.

Section 2 supplies the margin the landed hyperplane lemma discards.  That
lemma's docstring names `t/(1 - t)`, its statement delivers only `0 <`.

Section 3 composes.  Its headline is
`Gtz.posDef_iff_gapDet_pos_of_deflatedGapBound`: on the all-heavy stratum, with
the deflated bound in hand, strict domination IS one determinant sign.  Section 4
carries the composition to both registry obligations.  Section 5 decides the
unit-leverage boundary and forces the dropped atom into the KERNEL of the gap at
a tie.  Section 6 answers what an all-leverage-one design is.  Section 7 reads
the pivot value in the design's own vocabulary.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.ProjectionForm
import Gtz.Design.LeverageBound
import Gtz.Design.StratumEmptinessLedger
import Gtz.Reduction.PolarTiltLedger
import Gtz.Reduction.TwoVanishedBoundary
import Gtz.Quantitative.ChartSecondOrder
import Gtz.Certificates.ResidueDissolution
import Gtz.Reduction.SplitTransfer
import Gtz.Wave.LightAtomTieFloor
import Gtz.Wave.ArgmaxBlockFloor

namespace Gtz

open Finset Matrix RealInnerProductSpace

/-! ## 1. The pivot criterion: one hyperplane margin plus one scalar

Nothing here mentions a design.  A symmetric matrix, one nonzero pivot vector,
and a positive lower bound on the form over the pivot's orthogonal hyperplane.
Everything is square-root free: the pivot is never normalized. -/

section PivotCriterion

variable {rank : ℕ}

/-- Scaling a vector scales a quadratic form by the square. -/
theorem dotProduct_mulVec_smul_self (gapMatrix : Matrix (Fin rank) (Fin rank) ℝ)
    (scale : ℝ) (vec : Fin rank → ℝ) :
    (scale • vec) ⬝ᵥ (gapMatrix *ᵥ (scale • vec))
      = scale ^ 2 * (vec ⬝ᵥ (gapMatrix *ᵥ vec)) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/-- **THE FORM SPLIT ALONG A PIVOT.**  A symmetric form on `residual + c • pivot`
expands into the residual value, twice the coupling, and the pivot value.  No
orthogonality and no normalization are used. -/
theorem dotProduct_mulVec_pivot_expansion
    {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ} (hsymm : gapMatrixᵀ = gapMatrix)
    (pivotVec residualVec : Fin rank → ℝ) (component : ℝ) :
    (residualVec + component • pivotVec)
        ⬝ᵥ (gapMatrix *ᵥ (residualVec + component • pivotVec))
      = residualVec ⬝ᵥ (gapMatrix *ᵥ residualVec)
        + 2 * component * (residualVec ⬝ᵥ (gapMatrix *ᵥ pivotVec))
        + component ^ 2 * (pivotVec ⬝ᵥ (gapMatrix *ᵥ pivotVec)) := by
  have hswap : pivotVec ⬝ᵥ (gapMatrix *ᵥ residualVec)
      = residualVec ⬝ᵥ (gapMatrix *ᵥ pivotVec) :=
    dotProduct_mulVec_comm_of_transpose_eq hsymm pivotVec residualVec
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    add_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct,
    smul_dotProduct, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hswap]
  ring

/-- **THE PIVOT COSET IS THE WHOLE TEST.**  A symmetric form that is strictly
positive on the pivot's orthogonal hyperplane is positive definite EXACTLY when
it is positive at every point of the affine coset `pivot + hyperplane`.  The
codimension-one half of positive definiteness is discharged by the hypothesis,
and one affine slice is what remains. -/
theorem posDef_iff_pivotCoset {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ}
    (hsymm : gapMatrixᵀ = gapMatrix) {pivotVec : Fin rank → ℝ} (hpivotNe : pivotVec ≠ 0)
    (hplane : ∀ flatVec : Fin rank → ℝ, flatVec ⬝ᵥ pivotVec = 0 → flatVec ≠ 0 →
      0 < flatVec ⬝ᵥ (gapMatrix *ᵥ flatVec)) :
    gapMatrix.PosDef
      ↔ ∀ flatVec : Fin rank → ℝ, flatVec ⬝ᵥ pivotVec = 0 →
          0 < (pivotVec + flatVec) ⬝ᵥ (gapMatrix *ᵥ (pivotVec + flatVec)) := by
  have hpivotNorm : 0 < pivotVec ⬝ᵥ pivotVec := dotProduct_self_pos hpivotNe
  constructor
  · intro hposDef flatVec hflat
    have hne : pivotVec + flatVec ≠ 0 := by
      intro hzero
      have hread : (pivotVec + flatVec) ⬝ᵥ pivotVec = 0 := by rw [hzero, zero_dotProduct]
      rw [add_dotProduct, hflat, add_zero] at hread
      exact absurd hread hpivotNorm.ne'
    have hvalue := hposDef.dotProduct_mulVec_pos hne
    rwa [star_trivial] at hvalue
  · intro hcoset
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hsymm, fun testVec htestNe => ?_⟩
    rw [star_trivial]
    have hflat : (testVec - ((testVec ⬝ᵥ pivotVec) / (pivotVec ⬝ᵥ pivotVec)) • pivotVec)
        ⬝ᵥ pivotVec = 0 := by
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul,
        div_mul_cancel₀ _ hpivotNorm.ne', sub_self]
    by_cases hzeroComponent : (testVec ⬝ᵥ pivotVec) / (pivotVec ⬝ᵥ pivotVec) = 0
    · have hrebuild : testVec
          = testVec - ((testVec ⬝ᵥ pivotVec) / (pivotVec ⬝ᵥ pivotVec)) • pivotVec := by
        rw [hzeroComponent, zero_smul, sub_zero]
      have hresidualNe : testVec - ((testVec ⬝ᵥ pivotVec) / (pivotVec ⬝ᵥ pivotVec)) • pivotVec
          ≠ 0 := by
        rw [← hrebuild]; exact htestNe
      have hvalue := hplane _ hflat hresidualNe
      rw [← hrebuild] at hvalue
      exact hvalue
    · have hscaledFlat : (((testVec ⬝ᵥ pivotVec) / (pivotVec ⬝ᵥ pivotVec))⁻¹
          • (testVec - ((testVec ⬝ᵥ pivotVec) / (pivotVec ⬝ᵥ pivotVec)) • pivotVec))
          ⬝ᵥ pivotVec = 0 := by
        rw [smul_dotProduct, smul_eq_mul, hflat, mul_zero]
      have hcosetValue := hcoset _ hscaledFlat
      have hrebuild : testVec
          = ((testVec ⬝ᵥ pivotVec) / (pivotVec ⬝ᵥ pivotVec))
            • (pivotVec + ((testVec ⬝ᵥ pivotVec) / (pivotVec ⬝ᵥ pivotVec))⁻¹
              • (testVec - ((testVec ⬝ᵥ pivotVec) / (pivotVec ⬝ᵥ pivotVec)) • pivotVec)) := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ hzeroComponent, one_smul]
        abel
      rw [hrebuild, dotProduct_mulVec_smul_self]
      have hsquarePos : 0 < ((testVec ⬝ᵥ pivotVec) / (pivotVec ⬝ᵥ pivotVec)) ^ 2 := by
        positivity
      exact mul_pos hsquarePos hcosetValue

/-- **THE GRAM COUPLING BOUND.**  For a vector orthogonal to the pivot, the
pairing against any second vector is controlled by the Gram determinant of the
pivot and that vector.  Pure vector algebra, square-root free, no matrix. -/
theorem pivotNorm_mul_sq_dotProduct_le_of_orthogonal
    (pivotVec imageVec flatVec : Fin rank → ℝ) (hflat : flatVec ⬝ᵥ pivotVec = 0) :
    (pivotVec ⬝ᵥ pivotVec) * (flatVec ⬝ᵥ imageVec) ^ 2
      ≤ (flatVec ⬝ᵥ flatVec)
        * ((pivotVec ⬝ᵥ pivotVec) * (imageVec ⬝ᵥ imageVec)
          - (pivotVec ⬝ᵥ imageVec) ^ 2) := by
  have hcauchy := dotProduct_sq_le_mul flatVec
    ((pivotVec ⬝ᵥ pivotVec) • imageVec - (pivotVec ⬝ᵥ imageVec) • pivotVec)
  have hleft : flatVec
        ⬝ᵥ ((pivotVec ⬝ᵥ pivotVec) • imageVec - (pivotVec ⬝ᵥ imageVec) • pivotVec)
      = (pivotVec ⬝ᵥ pivotVec) * (flatVec ⬝ᵥ imageVec) := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      hflat, mul_zero, sub_zero]
  have hright : ((pivotVec ⬝ᵥ pivotVec) • imageVec - (pivotVec ⬝ᵥ imageVec) • pivotVec)
        ⬝ᵥ ((pivotVec ⬝ᵥ pivotVec) • imageVec - (pivotVec ⬝ᵥ imageVec) • pivotVec)
      = (pivotVec ⬝ᵥ pivotVec)
        * ((pivotVec ⬝ᵥ pivotVec) * (imageVec ⬝ᵥ imageVec)
          - (pivotVec ⬝ᵥ imageVec) ^ 2) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm imageVec pivotVec]
    ring
  rw [hleft, hright] at hcauchy
  rcases eq_or_lt_of_le (dotProduct_self_nonneg pivotVec) with hzero | hpos
  · have hpivotZero : pivotVec = 0 := eq_zero_of_dotProduct_self_eq_zero hzero.symm
    rw [hpivotZero]
    simp
  · nlinarith [hcauchy, hpos]

/-- **THE SCALAR CORE OF THE CRITERION.**  All six quantities are real numbers:
the hyperplane margin, the pivot norm and value, the flat norm and value, the
coupling total, and the cross term.  This is the whole arithmetic content of the
pivot criterion, isolated so no matrix appears in it. -/
theorem cosetValue_pos_of_scalars {marginVal pivotNorm pivotValue flatNorm flatValue
    couplingVal crossVal : ℝ}
    (hmargin : 0 < marginVal) (hpivotNorm : 0 < pivotNorm) (hflatNorm : 0 ≤ flatNorm)
    (hflatFloor : marginVal * flatNorm ≤ flatValue)
    (hcoupling : pivotNorm * crossVal ^ 2 ≤ flatNorm * couplingVal)
    (hcouplingNonneg : 0 ≤ couplingVal)
    (hsurplus : couplingVal < marginVal * pivotNorm * pivotValue) :
    0 < flatValue + 2 * crossVal + pivotValue := by
  have hmarginNorm : 0 < marginVal * pivotNorm := mul_pos hmargin hpivotNorm
  have hpivotValuePos : 0 < pivotValue := by
    by_contra hnonpos
    push Not at hnonpos
    have hprod : 0 ≤ (marginVal * pivotNorm) * (-pivotValue) :=
      mul_nonneg hmarginNorm.le (neg_nonneg.mpr hnonpos)
    nlinarith [hcouplingNonneg, hsurplus, hprod]
  rcases eq_or_lt_of_le hflatNorm with hzero | hflatPos
  · have hstep : pivotNorm * crossVal ^ 2 ≤ 0 := by rw [← hzero] at hcoupling; linarith
    have hsqNonpos : crossVal ^ 2 ≤ 0 := by
      by_contra hcontra
      push Not at hcontra
      nlinarith [mul_pos hpivotNorm hcontra]
    have hcrossZero : crossVal = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hsqNonpos (sq_nonneg crossVal))
    have hflatValueNonneg : 0 ≤ flatValue := by rw [← hzero] at hflatFloor; linarith
    rw [hcrossZero]
    linarith
  · have hflatValuePos : 0 < flatValue := by
      nlinarith [hflatFloor, mul_pos hmargin hflatPos]
    have hpivotProdPos : 0 < pivotNorm * pivotValue := mul_pos hpivotNorm hpivotValuePos
    have hstep : flatNorm * couplingVal < flatNorm * (marginVal * pivotNorm * pivotValue) :=
      mul_lt_mul_of_pos_left hsurplus hflatPos
    have hmono : marginVal * flatNorm * (pivotNorm * pivotValue)
        ≤ flatValue * (pivotNorm * pivotValue) :=
      mul_le_mul_of_nonneg_right hflatFloor hpivotProdPos.le
    have hchain : pivotNorm * crossVal ^ 2 < flatValue * (pivotNorm * pivotValue) := by
      nlinarith [hcoupling, hstep, hmono]
    have hkey : crossVal ^ 2 < flatValue * pivotValue := by
      by_contra hcontra
      push Not at hcontra
      nlinarith [mul_le_mul_of_nonneg_left hcontra hpivotNorm.le, hchain]
    nlinarith [hkey, hflatValuePos, hpivotValuePos, sq_nonneg (flatValue - pivotValue)]

/-- **THE PIVOT CRITERION.**  A symmetric matrix with a strictly positive margin
on one hyperplane is positive definite as soon as ONE square-root-free scalar
inequality holds at the pivot: the coupling out of the pivot direction is beaten
by the pivot surplus paid at the margin.

This is the rank-uniform reduction the all-heavy residual needs.  It names no
coordinate, it needs no eigenvalue, and the pivot may be chosen to suit the
design.  Sylvester needs `rank` nested leading minors in a fixed basis and does
not lift across a split hinge. -/
theorem posDef_of_pivotMargin_of_pivotSurplus
    {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ} (hsymm : gapMatrixᵀ = gapMatrix)
    {pivotVec : Fin rank → ℝ} (hpivotNe : pivotVec ≠ 0) {margin : ℝ} (hmargin : 0 < margin)
    (hplane : ∀ flatVec : Fin rank → ℝ, flatVec ⬝ᵥ pivotVec = 0 →
      margin * (flatVec ⬝ᵥ flatVec) ≤ flatVec ⬝ᵥ (gapMatrix *ᵥ flatVec))
    (hsurplus : (pivotVec ⬝ᵥ pivotVec)
          * ((gapMatrix *ᵥ pivotVec) ⬝ᵥ (gapMatrix *ᵥ pivotVec))
          - (pivotVec ⬝ᵥ (gapMatrix *ᵥ pivotVec)) ^ 2
        < margin * (pivotVec ⬝ᵥ pivotVec) * (pivotVec ⬝ᵥ (gapMatrix *ᵥ pivotVec))) :
    gapMatrix.PosDef := by
  have hpivotNormPos : 0 < pivotVec ⬝ᵥ pivotVec := dotProduct_self_pos hpivotNe
  have hcouplingNonneg : 0 ≤ (pivotVec ⬝ᵥ pivotVec)
      * ((gapMatrix *ᵥ pivotVec) ⬝ᵥ (gapMatrix *ᵥ pivotVec))
      - (pivotVec ⬝ᵥ (gapMatrix *ᵥ pivotVec)) ^ 2 := by
    have hcs := dotProduct_sq_le_mul pivotVec (gapMatrix *ᵥ pivotVec)
    linarith
  have hplanePos : ∀ flatVec : Fin rank → ℝ, flatVec ⬝ᵥ pivotVec = 0 → flatVec ≠ 0 →
      0 < flatVec ⬝ᵥ (gapMatrix *ᵥ flatVec) := fun flatVec hflat hflatNe =>
    lt_of_lt_of_le (mul_pos hmargin (dotProduct_self_pos hflatNe)) (hplane flatVec hflat)
  refine (posDef_iff_pivotCoset hsymm hpivotNe hplanePos).mpr fun flatVec hflat => ?_
  rw [show pivotVec + flatVec = flatVec + (1 : ℝ) • pivotVec by rw [one_smul]; abel,
    dotProduct_mulVec_pivot_expansion hsymm pivotVec flatVec 1]
  have hcore := cosetValue_pos_of_scalars hmargin hpivotNormPos
    (dotProduct_self_nonneg flatVec) (hplane flatVec hflat)
    (pivotNorm_mul_sq_dotProduct_le_of_orthogonal pivotVec (gapMatrix *ᵥ pivotVec) flatVec hflat)
    hcouplingNonneg hsurplus
  linarith [hcore]

/-! ### 1b. The lossless form: one determinant

The scalar test of section 1 replaces the restriction of the form to the
hyperplane by a single margin, and that replacement loses.  It need not: a form
that is positive definite on a hyperplane has AT MOST ONE non-positive
eigenvalue, because two of them would span a plane meeting the hyperplane.  So
the sign of the determinant decides the last one, and the criterion becomes an
EQUIVALENCE with no margin in it at all. -/

theorem dotProduct_ofLp {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    (x.ofLp) ⬝ᵥ (y.ofLp) = ⟪x, y⟫ := by
  rw [PiLp.inner_apply]
  simp [dotProduct, RCLike.inner_apply, mul_comm]

theorem posDef_of_planePosDef_of_det_pos {rank : ℕ}
    {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ} (hsymm : gapMatrixᵀ = gapMatrix)
    {pivotVec : Fin rank → ℝ}
    (hplane : ∀ v : Fin rank → ℝ, v ⬝ᵥ pivotVec = 0 → v ≠ 0 → 0 < v ⬝ᵥ (gapMatrix *ᵥ v))
    (hdet : 0 < gapMatrix.det) : gapMatrix.PosDef := by
  classical
  have hherm : gapMatrix.IsHermitian := isHermitian_of_transpose_eq hsymm
  set eigen : Fin rank → ℝ := hherm.eigenvalues with heigen
  set u : Fin rank → (Fin rank → ℝ) := fun j => (hherm.eigenvectorBasis j).ofLp with hu
  have horth : ∀ i j, u i ⬝ᵥ u j = if i = j then 1 else 0 := by
    intro i j
    rw [hu, dotProduct_ofLp]
    exact orthonormal_iff_ite.mp (hherm.eigenvectorBasis).orthonormal i j
  have hact : ∀ j, gapMatrix *ᵥ u j = eigen j • u j := fun j =>
    hherm.mulVec_eigenvectorBasis j
  have hself : ∀ j, u j ⬝ᵥ (gapMatrix *ᵥ u j) = eigen j := by
    intro j
    rw [hact j, dotProduct_smul, smul_eq_mul, horth j j]
    simp
  have hunit : ∀ j, u j ≠ 0 := by
    intro j hzero
    have := horth j j
    rw [hzero, zero_dotProduct] at this
    simp at this
  -- an eigenvector orthogonal to the pivot has a positive eigenvalue
  have hflatPos : ∀ j, u j ⬝ᵥ pivotVec = 0 → 0 < eigen j := by
    intro j hflat
    have := hplane (u j) hflat (hunit j)
    rwa [hself j] at this
  -- at most one nonpositive eigenvalue
  have hpair : ∀ i j : Fin rank, i ≠ j → 0 < eigen i ∨ 0 < eigen j := by
    intro i j hne
    by_cases hi : u i ⬝ᵥ pivotVec = 0
    · exact Or.inl (hflatPos i hi)
    by_cases hj : u j ⬝ᵥ pivotVec = 0
    · exact Or.inr (hflatPos j hj)
    by_contra hboth
    push Not at hboth
    obtain ⟨hnegi, hnegj⟩ := hboth
    have h11 : u i ⬝ᵥ u i = 1 := by rw [horth i i]; simp
    have h22 : u j ⬝ᵥ u j = 1 := by rw [horth j j]; simp
    have h12 : u i ⬝ᵥ u j = 0 := by rw [horth i j]; simp [hne]
    have h21 : u j ⬝ᵥ u i = 0 := by rw [horth j i]; simp [Ne.symm hne]
    set ci : ℝ := u j ⬝ᵥ pivotVec with hci
    set cj : ℝ := -(u i ⬝ᵥ pivotVec) with hcj
    have hcine : ci ≠ 0 := hj
    set v : Fin rank → ℝ := ci • u i + cj • u j with hv
    have hvflat : v ⬝ᵥ pivotVec = 0 := by
      rw [hv, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
        hci, hcj]
      ring
    have hvnorm : v ⬝ᵥ v = ci ^ 2 + cj ^ 2 := by
      rw [hv]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        h11, h22, h12, h21]
      ring
    have hvne : v ≠ 0 := by
      intro hzero
      rw [hzero, zero_dotProduct] at hvnorm
      have hcipos : 0 < ci ^ 2 :=
        lt_of_le_of_ne (sq_nonneg ci) (Ne.symm (pow_ne_zero 2 hcine))
      nlinarith [sq_nonneg cj, hvnorm, hcipos]
    have hvalue : v ⬝ᵥ (gapMatrix *ᵥ v) = ci ^ 2 * eigen i + cj ^ 2 * eigen j := by
      rw [hv]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hact, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, h11, h22, h12, h21]
      ring
    have hcontra := hplane v hvflat hvne
    rw [hvalue] at hcontra
    nlinarith [sq_nonneg ci, sq_nonneg cj, hnegi, hnegj, hcontra]
  -- every eigenvalue is positive
  have hallpos : ∀ i, 0 < eigen i := by
    intro i
    by_contra hnonpos
    push Not at hnonpos
    have hrest : ∀ j ∈ Finset.univ.erase i, 0 < eigen j := by
      intro j hj
      rcases hpair i j (Finset.ne_of_mem_erase hj).symm with h | h
      · exact absurd h (not_lt.mpr hnonpos)
      · exact h
    have hprodpos : 0 < ∏ j ∈ Finset.univ.erase i, eigen j :=
      Finset.prod_pos hrest
    have hdetform : gapMatrix.det = ∏ j, eigen j := by
      rw [hherm.det_eq_prod_eigenvalues]
      simp [heigen]
    have hsplit : ∏ j, eigen j = eigen i * ∏ j ∈ Finset.univ.erase i, eigen j :=
      (Finset.mul_prod_erase Finset.univ eigen (Finset.mem_univ i)).symm
    rw [hdetform, hsplit] at hdet
    nlinarith [hdet, hprodpos, hnonpos]
  exact hherm.posDef_iff_eigenvalues_pos.mpr hallpos

/-- **THE DETERMINANT CRITERION IS AN EQUIVALENCE.**  On the hyperplane-positive
region the determinant decides positive definiteness outright. -/
theorem posDef_iff_det_pos_of_planePosDef {rank : ℕ}
    {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ} (hsymm : gapMatrixᵀ = gapMatrix)
    {pivotVec : Fin rank → ℝ}
    (hplane : ∀ v : Fin rank → ℝ, v ⬝ᵥ pivotVec = 0 → v ≠ 0 →
      0 < v ⬝ᵥ (gapMatrix *ᵥ v)) :
    gapMatrix.PosDef ↔ 0 < gapMatrix.det :=
  ⟨fun hposDef => hposDef.det_pos, posDef_of_planePosDef_of_det_pos hsymm hplane⟩

/-- **THE EXACT OBSTRUCTION.**  A nonpositive pivot value refutes positive
definiteness outright, whatever the hyperplane margin.  So the scalar the
criterion asks for is necessary as well as sufficient in its sign. -/
theorem not_posDef_of_pivotValue_nonpos {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ}
    {pivotVec : Fin rank → ℝ} (hpivotNe : pivotVec ≠ 0)
    (hnonpos : pivotVec ⬝ᵥ (gapMatrix *ᵥ pivotVec) ≤ 0) : ¬ gapMatrix.PosDef := by
  intro hposDef
  have hvalue := hposDef.dotProduct_mulVec_pos hpivotNe
  rw [star_trivial] at hvalue
  linarith

end PivotCriterion

/-! ## 2. The margin the landed hyperplane lemma discards

`Gtz.posDef_on_orthogonal_of_deflatedGapBound` states `0 <` and its docstring
names the margin `t/(1 - t)`.  The margin is what the pivot criterion consumes,
so it is extracted here, division free. -/

section DeflatedMargin

variable {m k : ℕ}

/-- **THE HYPERPLANE MARGIN, DIVISION FREE.**  The deflated gap bound gives more
than positivity off the dropped atom: it gives the explicit floor
`t * |v|^2 <= (1 - t) * v . (S_C - I) v`, at EVERY leverage of the dropped atom. -/
theorem deflatedGapBound_orthogonal_margin (D : WeightedDesign (m + 1) k)
    (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
      - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef)
    (probeVec : Fin k → ℝ) (horthogonal : D.atom dropLabel ⬝ᵥ probeVec = 0) :
    D.weight dropLabel * (probeVec ⬝ᵥ probeVec)
      ≤ ((1 : ℝ) - D.weight dropLabel)
        * (probeVec ⬝ᵥ ((subsetSum D selected - 1) *ᵥ probeVec)) := by
  have hcomplement : probeVec ⬝ᵥ
        (((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel)) *ᵥ probeVec)
      = probeVec ⬝ᵥ probeVec := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm probeVec (D.atom dropLabel), horthogonal, mul_zero, sub_zero]
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 probeVec
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    hcomplement] at hform
  linarith

/-- **THE BOUND'S READING AT THE DROPPED ATOM.**  Against its own atom the
deflated bound says only `t * l * (1 - l) <= (1 - t) * (a . (S_C - I) a)`, which
is vacuous the moment the leverage reaches one.  This is exactly why the
all-heavy region is the residual, and it names the one direction the hyperplane
margin does not cover. -/
theorem deflatedGapBound_pivot_reading (D : WeightedDesign (m + 1) k)
    (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
      - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef) :
    D.weight dropLabel * (leverageOf (D.atom dropLabel)
        * ((1 : ℝ) - leverageOf (D.atom dropLabel)))
      ≤ ((1 : ℝ) - D.weight dropLabel)
        * (D.atom dropLabel ⬝ᵥ ((subsetSum D selected - 1) *ᵥ D.atom dropLabel)) := by
  have hleverage : D.atom dropLabel ⬝ᵥ D.atom dropLabel = leverageOf (D.atom dropLabel) :=
    (leverageOf_eq_dotProduct (D.atom dropLabel)).symm
  have hcomplement : D.atom dropLabel ⬝ᵥ
        (((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel))
          *ᵥ D.atom dropLabel)
      = leverageOf (D.atom dropLabel) * ((1 : ℝ) - leverageOf (D.atom dropLabel)) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, hleverage]
    ring
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 (D.atom dropLabel)
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    hcomplement] at hform
  linarith

/-- The subset gap of a design is symmetric. -/
theorem transpose_subsetSum_sub_one_eq (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    (subsetSum D selected - 1)ᵀ = subsetSum D selected - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum_transpose]

/-- A heavy atom is nonzero. -/
theorem atom_ne_zero_of_one_le_leverage (D : WeightedDesign m k) (label : Fin m)
    (hheavy : 1 ≤ leverageOf (D.atom label)) : D.atom label ≠ 0 := by
  intro hzero
  have hvanishes : leverageOf (D.atom label) = 0 := by
    rw [hzero]; simp [leverageOf]
  rw [hvanishes] at hheavy
  linarith

end DeflatedMargin

/-! ## 3. The all-heavy criterion

The deflation supplies the hyperplane margin, the atom supplies the pivot, and
one square-root-free scalar closes the gap.  Nothing here is rank three, and
nothing here asks the atom to be light. -/

section AllHeavyCriterion

variable {m k : ℕ}

/-- The pivot scalar of a design at a label and a subset, written out. -/
def PivotSurplusAt {size rank : ℕ} (design : WeightedDesign size rank)
    (dropLabel : Fin size) (selected : Finset (Fin size)) : Prop :=
  ((1 : ℝ) - design.weight dropLabel)
      * ((design.atom dropLabel ⬝ᵥ design.atom dropLabel)
          * (((subsetSum design selected - 1) *ᵥ design.atom dropLabel)
              ⬝ᵥ ((subsetSum design selected - 1) *ᵥ design.atom dropLabel))
        - (design.atom dropLabel
            ⬝ᵥ ((subsetSum design selected - 1) *ᵥ design.atom dropLabel)) ^ 2)
    < design.weight dropLabel * (design.atom dropLabel ⬝ᵥ design.atom dropLabel)
      * (design.atom dropLabel ⬝ᵥ ((subsetSum design selected - 1) *ᵥ design.atom dropLabel))

/-- The deflated gap bound of a design at a label and a subset, written out. -/
def DeflatedGapBoundAt {size rank : ℕ} (design : WeightedDesign size rank)
    (dropLabel : Fin size) (selected : Finset (Fin size)) : Prop :=
  (((1 : ℝ) - design.weight dropLabel) • (subsetSum design selected - 1)
    - design.weight dropLabel • (1 - atomMatrix (design.atom dropLabel))).PosSemidef

/-- **THE PIVOT SCALAR CARRIES ITS OWN NON-DEGENERACY.**  Every term of the test
is a multiple of the atom's Gram data, so a zero atom collapses both sides to
zero and the strict inequality fails.  No heaviness hypothesis is therefore
needed anywhere the pivot scalar appears. -/
theorem atom_ne_zero_of_pivotSurplus {size rank : ℕ} (design : WeightedDesign size rank)
    (dropLabel : Fin size) (selected : Finset (Fin size))
    (hsurplus : PivotSurplusAt design dropLabel selected) : design.atom dropLabel ≠ 0 := by
  intro hzero
  rw [PivotSurplusAt, hzero] at hsurplus
  simp at hsurplus

/-- **THE ALL-HEAVY STRICT DOMINATOR.**  Given the deflated gap bound at a label,
the subset dominates STRICTLY as soon as one scalar inequality holds at that
atom's own direction.  The whole hyperplane orthogonal to the atom is discharged
by the bound, so this is the exact residual of the deflation lane, reduced from
`rank` dimensions to one.  No leverage hypothesis appears. -/
theorem posDef_of_deflatedGapBound_of_pivotSurplus (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : DeflatedGapBoundAt D dropLabel selected)
    (hsurplusProp : PivotSurplusAt D dropLabel selected) :
    (subsetSum D selected - 1).PosDef := by
  have hatomNe := atom_ne_zero_of_pivotSurplus D dropLabel selected hsurplusProp
  have hsurplus := hsurplusProp
  rw [PivotSurplusAt] at hsurplus
  rw [DeflatedGapBoundAt] at hbound
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hsurvivingMass : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hmarginPos : 0 < D.weight dropLabel / (1 - D.weight dropLabel) :=
    div_pos hweightPos hsurvivingMass
  refine posDef_of_pivotMargin_of_pivotSurplus
    (transpose_subsetSum_sub_one_eq D selected) hatomNe hmarginPos ?_ ?_
  · intro flatVec hflat
    have horthogonal : D.atom dropLabel ⬝ᵥ flatVec = 0 := by
      rw [dotProduct_comm]; exact hflat
    have hmargin := deflatedGapBound_orthogonal_margin D dropLabel selected hbound flatVec
      horthogonal
    rw [div_mul_eq_mul_div, div_le_iff₀ hsurvivingMass]
    nlinarith [hmargin, hsurvivingMass]
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, lt_div_iff₀ hsurvivingMass]
    nlinarith [hsurplus, hsurvivingMass]

/-- The gap determinant test at a subset. -/
def GapDetPositiveAt {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) : Prop :=
  0 < (subsetSum design selected - 1).det

/-- **THE DEFLATED BOUND SUPPLIES THE HYPERPLANE HALF.**  This is the landed
`Gtz.posDef_on_orthogonal_of_deflatedGapBound`, which had no consumer anywhere in
the tree, read in the argument order the pivot criterion wants.  Nothing is
proved here. -/
theorem planePosDef_of_deflatedGapBound (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : DeflatedGapBoundAt D dropLabel selected) :
    ∀ flatVec : Fin k → ℝ, flatVec ⬝ᵥ D.atom dropLabel = 0 → flatVec ≠ 0 →
      0 < flatVec ⬝ᵥ ((subsetSum D selected - 1) *ᵥ flatVec) := fun flatVec hflat hflatNe =>
  posDef_on_orthogonal_of_deflatedGapBound D dropLabel selected hbound hsize flatVec hflatNe
    (by rw [dotProduct_comm]; exact hflat)

/-- **THE ALL-HEAVY RESIDUAL IS ONE DETERMINANT SIGN.**  With the deflated gap
bound in hand at ANY label, the subset dominates STRICTLY exactly when its gap
determinant is positive.  An EQUIVALENCE, at every rank, with no margin, no
coupling term, no plane quantifier and no leverage hypothesis.

This is the sharpest form of the deflation lane's residual.  The pivot scalar of
`Gtz.posDef_of_deflatedGapBound_of_pivotSurplus` is a sufficient shadow of it and
loses, because it replaces the restriction of the gap to the hyperplane by a
single margin. -/
theorem posDef_iff_gapDet_pos_of_deflatedGapBound (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : DeflatedGapBoundAt D dropLabel selected) :
    (subsetSum D selected - 1).PosDef ↔ GapDetPositiveAt D selected :=
  posDef_iff_det_pos_of_planePosDef (transpose_subsetSum_sub_one_eq D selected)
    (planePosDef_of_deflatedGapBound D hsize dropLabel selected hbound)

/-- **THE DETERMINANT WITNESS REFUTES THE TIE, UNCONDITIONALLY.**  No predecessor
cell, no leverage hypothesis, no heaviness.  One label, one card-`rank` subset
carrying the deflated bound, and one determinant sign. -/
theorem not_isTie_of_detWitness {size rank : ℕ} (hsize : 2 ≤ size)
    (design : WeightedDesign size rank) (dropLabel : Fin size)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hbound : DeflatedGapBoundAt design dropLabel selected)
    (hdet : GapDetPositiveAt design selected) : ¬ IsTie design := by
  obtain ⟨predSize, hsplit⟩ : ∃ predSize : ℕ, size = predSize + 1 := ⟨size - 1, by omega⟩
  subst hsplit
  exact fun htie => htie.2 selected hcard
    ((posDef_iff_gapDet_pos_of_deflatedGapBound design (by omega) dropLabel selected
      hbound).mpr hdet)

/-- **THE TIE CEILING, IN ITS SHARPEST FORM.**  At a tie EVERY card-`rank` subset
carrying the deflated gap bound at ANY label has non-positive gap determinant.
One polynomial inequality in the design's own data, at every rank, with no
predecessor cell and no leverage floor spent. -/
theorem gapDet_nonpos_of_isTie {size rank : ℕ} (hsize : 2 ≤ size)
    (design : WeightedDesign size rank) (htie : IsTie design) (dropLabel : Fin size)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hbound : DeflatedGapBoundAt design dropLabel selected) :
    (subsetSum design selected - 1).det ≤ 0 := by
  by_contra hpos
  push Not at hpos
  exact not_isTie_of_detWitness hsize design dropLabel selected hcard hbound hpos htie

/-- **THE PIVOT SCALAR IS A SHADOW OF THE DETERMINANT.**  Whenever the scalar
test fires under the bound, the determinant is positive.  So nothing the scalar
route reaches is outside the determinant route, and the converse fails. -/
theorem gapDet_pos_of_pivotSurplus_of_deflatedGapBound (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : DeflatedGapBoundAt D dropLabel selected)
    (hsurplus : PivotSurplusAt D dropLabel selected) : GapDetPositiveAt D selected :=
  (posDef_iff_gapDet_pos_of_deflatedGapBound D hsize dropLabel selected hbound).mp
    (posDef_of_deflatedGapBound_of_pivotSurplus D hsize dropLabel selected hbound hsurplus)

/-- **THE SHARE HYPOTHESIS IS FREE OFF THE ISOLATED ATOM.**  The deflation asks
the SHARE to be below one.  Saturation forces every other atom orthogonal to this
one (`Gtz.polarPairing_eq_zero_of_saturated`), so a single non-orthogonal partner
discharges the hypothesis. -/
theorem weight_mul_leverage_lt_one_of_exists_partner (D : WeightedDesign m k)
    (label partner : Fin m) (hne : partner ≠ label)
    (hpartner : D.atom partner ⬝ᵥ D.atom label ≠ 0) :
    D.weight label * leverageOf (D.atom label) < 1 := by
  have hleverage : D.atom label ⬝ᵥ D.atom label = leverageOf (D.atom label) :=
    (leverageOf_eq_dotProduct (D.atom label)).symm
  have hcap : D.weight label * leverageOf (D.atom label) ≤ 1 := by
    rw [← hleverage]; exact weight_mul_selfDotProduct_le_one D label
  rcases lt_or_eq_of_le hcap with hlt | heq
  · exact hlt
  · exact absurd (polarPairing_eq_zero_of_saturated D (by rw [hleverage]; exact heq) hne)
      hpartner

/-- **THE HINGE CRITERION IS UNCONDITIONAL.**  A design of size at least two, one
label, and one card-`rank` subset carrying the deflated gap bound and the pivot
scalar together refute the tie.  NO predecessor cell, NO leverage hypothesis and
NO heaviness appear: the pivot scalar carries its own non-degeneracy, and the
bound carries the hyperplane. -/
theorem not_isTie_of_pivotWitness {size rank : ℕ} (hsize : 2 ≤ size)
    (design : WeightedDesign size rank) (dropLabel : Fin size)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hbound : DeflatedGapBoundAt design dropLabel selected)
    (hsurplus : PivotSurplusAt design dropLabel selected) : ¬ IsTie design := by
  obtain ⟨predSize, hsplit⟩ : ∃ predSize : ℕ, size = predSize + 1 := ⟨size - 1, by omega⟩
  subst hsplit
  exact fun htie => htie.2 selected hcard
    (posDef_of_deflatedGapBound_of_pivotSurplus design (by omega) dropLabel selected hbound
      hsurplus)

/-- **THE DEFLATION CERTIFIES THAT THE WITNESS REGION IS NOT EMPTY.**  At a label
of share below one the predecessor cell hands back a card-`rank` subset AVOIDING
that label which carries the bound.  So the existential the criterion consumes
quantifies over a region that is provably inhabited, and only the pivot scalar is
open. -/
theorem exists_deflatedGapBoundAt (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (dropLabel : Fin (m + 1))
    (hshare : D.weight dropLabel * leverageOf (D.atom dropLabel) < 1) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = k ∧ dropLabel ∉ selected ∧
      DeflatedGapBoundAt D dropLabel selected :=
  exists_deflatedGapBound D hsize hsmaller dropLabel hshare

/-- **THE ALL-HEAVY HINGE CRITERION, ASSEMBLED.**  A label of share below one and
ONE card-`rank` subset carrying both the bound and the pivot scalar give a strict
dominator. -/
theorem exists_posDef_of_pivotWitness (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1))) (hcard : selected.card = k)
    (hbound : DeflatedGapBoundAt D dropLabel selected)
    (hsurplus : PivotSurplusAt D dropLabel selected) :
    ∃ witness : Finset (Fin (m + 1)), witness.card = k ∧
      (subsetSum D witness - 1).PosDef :=
  ⟨selected, hcard,
    posDef_of_deflatedGapBound_of_pivotSurplus D hsize dropLabel selected hbound hsurplus⟩

/-- **THE TIE REFUSES THE PIVOT SCALAR EVERYWHERE.**  Unconditional
contrapositive: at a tie NO label and NO card-`rank` subset carrying the deflated
bound passes the pivot scalar.  This is the sharpest form of the ceiling, and it
needs neither the predecessor cell nor the leverage floor. -/
theorem not_pivotSurplus_of_isTie {size rank : ℕ} (hsize : 2 ≤ size)
    (design : WeightedDesign size rank) (htie : IsTie design) (dropLabel : Fin size)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hbound : DeflatedGapBoundAt design dropLabel selected) :
    ¬ PivotSurplusAt design dropLabel selected := fun hsurplus =>
  not_isTie_of_pivotWitness hsize design dropLabel selected hcard hbound hsurplus htie

/-- **THE TIE CEILING AT EVERY LABEL OF SHARE BELOW ONE.**  The deflation names a
subset, and the ceiling holds there.  Nothing is assumed beyond the tie and the
predecessor cell. -/
theorem exists_pivotRefusal_of_isTie (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (htie : IsTie D) (dropLabel : Fin (m + 1))
    (hshare : D.weight dropLabel * leverageOf (D.atom dropLabel) < 1) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = k ∧ dropLabel ∉ selected ∧
      DeflatedGapBoundAt D dropLabel selected ∧
      ¬ PivotSurplusAt D dropLabel selected := by
  obtain ⟨selected, hcard, hnotMem, hbound⟩ :=
    exists_deflatedGapBound D hsize hsmaller dropLabel hshare
  exact ⟨selected, hcard, hnotMem, hbound,
    not_pivotSurplus_of_isTie (by omega) D htie dropLabel selected hcard hbound⟩

/-- **THE TIE'S COSET REFUSAL, EXACT.**  The pivot coset equivalence turns the
tie into a single named direction: at every label of share below one there is a
vector orthogonal to that atom at which the affine slice `atom + flat` fails.
This is an equivalence-grade statement, not a sufficient condition, so nothing is
lost in passing to it. -/
theorem exists_cosetRefusal_of_isTie (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (htie : IsTie D) (dropLabel : Fin (m + 1))
    (hshare : D.weight dropLabel * leverageOf (D.atom dropLabel) < 1) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = k ∧ dropLabel ∉ selected ∧
      ∃ flatVec : Fin k → ℝ, flatVec ⬝ᵥ D.atom dropLabel = 0 ∧
        (D.atom dropLabel + flatVec)
            ⬝ᵥ ((subsetSum D selected - 1) *ᵥ (D.atom dropLabel + flatVec)) ≤ 0 := by
  obtain ⟨selected, hcard, hnotMem, hbound⟩ :=
    exists_deflatedGapBound D hsize hsmaller dropLabel hshare
  have hatomNe := atom_ne_zero_of_one_le_leverage D dropLabel
    (leverage_one_le_of_isTie D hsize hsmaller htie dropLabel)
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hsurvivingMass : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hplanePos := planePosDef_of_deflatedGapBound D hsize dropLabel selected hbound
  refine ⟨selected, hcard, hnotMem, ?_⟩
  by_contra hall
  push Not at hall
  exact htie.2 selected hcard
    ((posDef_iff_pivotCoset (transpose_subsetSum_sub_one_eq D selected) hatomNe hplanePos).mpr
      hall)

end AllHeavyCriterion

/-! ## 4. The producers for the two off-path hinges

Both obligations conclude a parallel pair out of a tie and hand over the
predecessor cell.  Section 3 discharges the conclusion by refuting the tie, and
it asks for ONE label and ONE subset carrying two things: the deflated gap bound,
which the predecessor cell supplies, and one polynomial inequality, which is the
whole open content.

HONEST READING.  Like every producer whose route is a strict dominator, the
hypothesis here is false on any design that IS a tie.  The implication is one
that a counterexample would refute, not one that a tie satisfies.  Its value over
the four dead excess-dominance producers, which asked for a combinatorial
selection at every design of the cell, is the SIZE of what it asks: one
polynomial inequality at one label and one subset, on the all-heavy stratum only,
and the subset needs no search because the deflation names one.

MEASURED, 2026-08-16, in exact rationals.  The sample uses designs built from a
Cayley rational orthonormal basis and rational weights, so every number is exact
and no floating point enters.  The calibration anchor is the `(4,3)` tetrahedron
tie, where a bound-carrying subset exists and NEITHER test fires, as it must not.

* `(6,3)`, 300 designs: the pivot scalar fires at 224, the determinant at 300.
  Of the 107 all-heavy designs the pivot scalar fires at 92 and the determinant
  at 107.
* `(8,4)`, 120 designs: pivot 68, determinant 120.  All-heavy 53: pivot 36,
  determinant 53.
* `(9,4)`, 80 designs: pivot 46, determinant 80.
* `(10,4)`, 60 designs: pivot 33, determinant 60.
* Across 37319 bound-carrying label-and-subset pairs at the four cells the
  determinant sign and positive definiteness agreed every time, no exception.

**THE HYPOTHESIS OF THE THREE SCALAR PRODUCERS IS REFUTED AT `(6,3)`.**  An exact
all-heavy design exists that is not a tie and that carries NO pivot witness at
any label and any subset.  The scalar producers stay because their proof is
elementary and spends no spectral theorem, and because every pivot witness is a
determinant witness (`Gtz.hasDetWitness_of_hasPivotWitness`).  The DETERMINANT
producers are the live ones. -/

section HingeProducers

/-- **THE HINGE, FROM ONE PIVOT WITNESS.**  Stated at a bare size, with the
predecessor cell exactly as both registry obligations carry it.  The predecessor
is spent only on the existence of a bound-carrying subset. -/
theorem hasParallelPair_of_isTie_of_pivotWitness {size rank : ℕ} (hsize : 2 ≤ size)
    (design : WeightedDesign size rank) (dropLabel : Fin size)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hbound : DeflatedGapBoundAt design dropLabel selected)
    (hsurplus : PivotSurplusAt design dropLabel selected)
    (htie : IsTie design) : HasParallelPair design :=
  absurd htie (not_isTie_of_pivotWitness hsize design dropLabel selected hcard hbound hsurplus)

/-- The witness the hinge producers ask for, at one design. -/
def HasPivotWitness {size rank : ℕ} (design : WeightedDesign size rank) : Prop :=
  ∃ (dropLabel : Fin size) (selected : Finset (Fin size)), selected.card = rank ∧
    DeflatedGapBoundAt design dropLabel selected ∧ PivotSurplusAt design dropLabel selected

/-- **A PRODUCER FOR THE THRESHOLD-CELL HINGE.**  Its hypothesis asks, at every
all-heavy design of the cell, for ONE label and ONE card-`rank` subset carrying
the deflated bound and the pivot scalar.  The registry's own predecessor
hypothesis discharges the heaviness through the landed leverage floor. -/
theorem obligationThresholdCellHingeRankFourAndUp_of_pivotWitness
    (hpivot : ∀ rank : ℕ, 4 ≤ rank →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
        (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design) :
    ∀ rank : ℕ, 4 ≤ rank →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor design htie
  have hsize : 2 ≤ rank * (rank + 1) / 2 := by
    have hmono : 4 * 5 / 2 ≤ rank * (rank + 1) / 2 :=
      Nat.div_le_div_right (Nat.mul_le_mul hrank (by omega))
    omega
  obtain ⟨dropLabel, selected, hcard, hbound, hsurplus⟩ := hpivot rank hrank design
    (forall_leverage_one_le_of_isTie hsize hpredecessor design htie)
  exact hasParallelPair_of_isTie_of_pivotWitness hsize design dropLabel selected hcard
    hbound hsurplus htie

/-- **A PRODUCER FOR THE SUB-THRESHOLD BAND HINGE.**  Same shape on the band's
cells.  The band's own lower bound `2 * rank <= size` supplies the two labels the
leverage floor needs. -/
theorem obligationSubThresholdBandHinge_of_pivotWitness
    (hpivot : ∀ rank : ℕ, 3 ≤ rank → ∀ size : ℕ, 2 * rank ≤ size →
      size < rank * (rank + 1) / 2 → ∀ design : WeightedDesign size rank,
        (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design) :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank size hlow hhigh hpredecessor design htie
  have hsize : 2 ≤ size := by omega
  obtain ⟨dropLabel, selected, hcard, hbound, hsurplus⟩ := hpivot rank hrank size hlow hhigh
    design (forall_leverage_one_le_of_isTie hsize hpredecessor design htie)
  exact hasParallelPair_of_isTie_of_pivotWitness hsize design dropLabel selected hcard
    hbound hsurplus htie

/-- **AT `(6,3)` THE PIVOT WITNESS CLOSES THE HINGE OUTRIGHT.**  No predecessor
hypothesis appears, because `Gtz.gtzWeighted_of_le_five` supplies it. -/
theorem hingeConclusion_sixThree_of_pivotWitness
    (hpivot : ∀ design : WeightedDesign 6 3,
      (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design) :
    ∀ design : WeightedDesign 6 3, IsTie design → HasParallelPair design := by
  intro design htie
  obtain ⟨dropLabel, selected, hcard, hbound, hsurplus⟩ := hpivot design
    (fun label => leverage_one_le_of_isTie_sixThree design htie label)
  exact hasParallelPair_of_isTie_of_pivotWitness (by norm_num) design dropLabel selected hcard
    hbound hsurplus htie

/-- The determinant witness the sharp hinge producers ask for, at one design. -/
def HasDetWitness {size rank : ℕ} (design : WeightedDesign size rank) : Prop :=
  ∃ (dropLabel : Fin size) (selected : Finset (Fin size)), selected.card = rank ∧
    DeflatedGapBoundAt design dropLabel selected ∧ GapDetPositiveAt design selected

/-- **THE HINGE, FROM ONE DETERMINANT SIGN.** -/
theorem hasParallelPair_of_isTie_of_detWitness {size rank : ℕ} (hsize : 2 ≤ size)
    (design : WeightedDesign size rank) (hwitness : HasDetWitness design)
    (htie : IsTie design) : HasParallelPair design := by
  obtain ⟨dropLabel, selected, hcard, hbound, hdet⟩ := hwitness
  exact absurd htie (not_isTie_of_detWitness hsize design dropLabel selected hcard hbound hdet)

/-- **THE SHARP PRODUCER FOR THE THRESHOLD-CELL HINGE.**  Its hypothesis asks, at
every all-heavy design of the cell, for ONE label and ONE card-`rank` subset
carrying the deflated bound with a positive gap determinant.  Every ingredient
except that one sign is landed. -/
theorem obligationThresholdCellHingeRankFourAndUp_of_detWitness
    (hdet : ∀ rank : ℕ, 4 ≤ rank →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
        (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design) :
    ∀ rank : ℕ, 4 ≤ rank →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor design htie
  have hsize : 2 ≤ rank * (rank + 1) / 2 := by
    have hmono : 4 * 5 / 2 ≤ rank * (rank + 1) / 2 :=
      Nat.div_le_div_right (Nat.mul_le_mul hrank (by omega))
    omega
  exact hasParallelPair_of_isTie_of_detWitness hsize design
    (hdet rank hrank design (forall_leverage_one_le_of_isTie hsize hpredecessor design htie))
    htie

/-- **THE SHARP PRODUCER FOR THE SUB-THRESHOLD BAND HINGE.** -/
theorem obligationSubThresholdBandHinge_of_detWitness
    (hdet : ∀ rank : ℕ, 3 ≤ rank → ∀ size : ℕ, 2 * rank ≤ size →
      size < rank * (rank + 1) / 2 → ∀ design : WeightedDesign size rank,
        (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design) :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank size hlow hhigh hpredecessor design htie
  have hsize : 2 ≤ size := by omega
  exact hasParallelPair_of_isTie_of_detWitness hsize design
    (hdet rank hrank size hlow hhigh design
      (forall_leverage_one_le_of_isTie hsize hpredecessor design htie)) htie

/-- **AT `(6,3)` THE DETERMINANT WITNESS CLOSES THE HINGE OUTRIGHT.**  No
predecessor hypothesis appears, because `Gtz.gtzWeighted_of_le_five` supplies
it. -/
theorem hingeConclusion_sixThree_of_detWitness
    (hdet : ∀ design : WeightedDesign 6 3,
      (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design) :
    ∀ design : WeightedDesign 6 3, IsTie design → HasParallelPair design := fun design htie =>
  hasParallelPair_of_isTie_of_detWitness (by norm_num) design
    (hdet design fun label => leverage_one_le_of_isTie_sixThree design htie label) htie

/-- **THE DETERMINANT WITNESS IS WEAKER THAN THE PIVOT WITNESS.**  Every pivot
witness is a determinant witness, so the sharp producers subsume the scalar
ones. -/
theorem hasDetWitness_of_hasPivotWitness {m k : ℕ} (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (hwitness : HasPivotWitness D) : HasDetWitness D := by
  obtain ⟨dropLabel, selected, hcard, hbound, hsurplus⟩ := hwitness
  exact ⟨dropLabel, selected, hcard, hbound,
    gapDet_pos_of_pivotSurplus_of_deflatedGapBound D hsize dropLabel selected hbound hsurplus⟩

/-- **THE WITNESS REGION IS INHABITED WHEREVER A SHARE FALLS BELOW ONE.**  The
non-vacuity certificate for the three producers: the deflation supplies the
bound half of the witness at every such label, so only the pivot scalar is
open. -/
theorem exists_boundHalf_of_pivotWitness {size rank : ℕ} (hsize : 2 ≤ size)
    (hpredecessor : GtzWeighted (size - 1) rank) (design : WeightedDesign size rank)
    (dropLabel : Fin size)
    (hshare : design.weight dropLabel * leverageOf (design.atom dropLabel) < 1) :
    ∃ selected : Finset (Fin size), selected.card = rank ∧ dropLabel ∉ selected ∧
      DeflatedGapBoundAt design dropLabel selected := by
  obtain ⟨predSize, hsplit⟩ : ∃ predSize : ℕ, size = predSize + 1 := ⟨size - 1, by omega⟩
  subst hsplit
  rw [Nat.add_sub_cancel] at hpredecessor
  exact exists_deflatedGapBound design (by omega) hpredecessor dropLabel hshare

end HingeProducers

/-! ## 5. The boundary: leverage exactly one

At leverage exactly one the coupling term of the criterion disappears and the
whole test becomes the SIGN of the pivot value.  What the deflation gives there
is an EQUIVALENCE, not a sufficient condition, so the boundary is decided rather
than approximated.  At a tie the decision forces the atom into the kernel of the
gap, which pins the tight direction exactly. -/

section UnitLeverage

variable {m k : ℕ}

/-- **THE COSET VALUE AT UNIT LEVERAGE.**  With the leverage exactly one, the
dropped atom's own defect reads the affine slice `atom + flat` as the FLAT norm
alone: the atom's contribution cancels exactly.  So the deflation's margin
carries the whole slice, and no coupling term survives. -/
theorem unitLeverage_coset_floor (D : WeightedDesign (m + 1) k)
    (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
      - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef)
    (hunit : leverageOf (D.atom dropLabel) = 1)
    (flatVec : Fin k → ℝ) (hflat : flatVec ⬝ᵥ D.atom dropLabel = 0) :
    D.weight dropLabel * (flatVec ⬝ᵥ flatVec)
      ≤ ((1 : ℝ) - D.weight dropLabel)
        * ((D.atom dropLabel + flatVec)
            ⬝ᵥ ((subsetSum D selected - 1) *ᵥ (D.atom dropLabel + flatVec))) := by
  have hleverage : D.atom dropLabel ⬝ᵥ D.atom dropLabel = 1 := by
    rw [leverageOf_eq_dotProduct] at hunit; exact hunit
  have horthogonal : D.atom dropLabel ⬝ᵥ flatVec = 0 := by
    rw [dotProduct_comm]; exact hflat
  have hleft : D.atom dropLabel ⬝ᵥ (D.atom dropLabel + flatVec) = 1 := by
    rw [dotProduct_add, hleverage, horthogonal, add_zero]
  have hright : (D.atom dropLabel + flatVec) ⬝ᵥ D.atom dropLabel = 1 := by
    rw [add_dotProduct, hleverage, hflat, add_zero]
  have hself : (D.atom dropLabel + flatVec) ⬝ᵥ (D.atom dropLabel + flatVec)
      = 1 + flatVec ⬝ᵥ flatVec := by
    rw [dotProduct_add, add_dotProduct, add_dotProduct, hleverage, horthogonal, hflat]
    ring
  have hcomplement : (D.atom dropLabel + flatVec) ⬝ᵥ
        (((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel))
          *ᵥ (D.atom dropLabel + flatVec))
      = flatVec ⬝ᵥ flatVec := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, hleft, hright, hself]
    ring
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 (D.atom dropLabel + flatVec)
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    hcomplement] at hform
  linarith

/-- **THE BOUNDARY IS DECIDED.**  At a label of leverage exactly one the deflated
subset dominates STRICTLY exactly when the gap reads that atom's own direction
positively.  An equivalence, at every rank, with no coupling term and no plane
quantifier left. -/
theorem posDef_iff_pivotValue_pos_of_unitLeverage (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
      - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef)
    (hunit : leverageOf (D.atom dropLabel) = 1) :
    (subsetSum D selected - 1).PosDef
      ↔ 0 < D.atom dropLabel ⬝ᵥ ((subsetSum D selected - 1) *ᵥ D.atom dropLabel) := by
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hsurvivingMass : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hatomNe : D.atom dropLabel ≠ 0 :=
    atom_ne_zero_of_one_le_leverage D dropLabel (le_of_eq hunit.symm)
  have hplanePos := planePosDef_of_deflatedGapBound D hsize dropLabel selected hbound
  rw [posDef_iff_pivotCoset (transpose_subsetSum_sub_one_eq D selected) hatomNe hplanePos]
  constructor
  · intro hcoset
    have hzero := hcoset 0 (by rw [zero_dotProduct])
    rwa [add_zero] at hzero
  · intro hvalue flatVec hflat
    by_cases hflatZero : flatVec = 0
    · rw [hflatZero, add_zero]; exact hvalue
    · have hfloor := unitLeverage_coset_floor D dropLabel selected hbound hunit flatVec hflat
      nlinarith [hfloor, hsurvivingMass, mul_pos hweightPos (dotProduct_self_pos hflatZero)]

/-- **THE UNIT-LEVERAGE ATOM OF A TIE IS A KERNEL VECTOR.**  At a tie the
deflated subset dominates weakly, so the atom's reading is nonnegative, while the
boundary equivalence forbids it from being positive.  The two pin it to zero, and
a positive semidefinite matrix annihilates its isotropic vectors.  So the tight
direction of that subset's gap is the ATOM ITSELF, named exactly.

This turns the ledger's `Gtz.StratumIsTieFreeAtUnitLeverage` residue into a
rigidity: the boundary branch of
`Gtz.allHeavy_or_exists_leverage_eq_one_of_isTie` carries a determined tight
direction rather than an unknown one. -/
theorem exists_kernel_atom_of_isTie_of_unitLeverage (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (hsmaller : GtzWeighted m k) (htie : IsTie D)
    (dropLabel : Fin (m + 1)) (hunit : leverageOf (D.atom dropLabel) = 1) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = k ∧ dropLabel ∉ selected ∧
      (subsetSum D selected - 1).PosSemidef ∧
      (subsetSum D selected - 1) *ᵥ D.atom dropLabel = 0 := by
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hsurvivingMass : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hshare : D.weight dropLabel * leverageOf (D.atom dropLabel) < 1 := by
    rw [hunit, mul_one]; exact hweightLtOne
  obtain ⟨selected, hcard, hnotMem, hbound⟩ :=
    exists_deflatedGapBound D hsize hsmaller dropLabel hshare
  have hcomplementPsd :
      (D.weight dropLabel
        • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel))).PosSemidef := by
    refine Matrix.PosSemidef.smul ?_ hweightPos.le
    refine (posSemidef_sub_vecMulVec_iff 1 Matrix.PosDef.one (D.atom dropLabel)).mpr ?_
    rw [inv_one, Matrix.one_mulVec, dotProduct_self_eq_sum_sq]
    exact le_of_eq hunit
  have hscaledPsd : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)).PosSemidef := by
    have hsplit : ((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
        = (D.weight dropLabel
            • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel)))
          + (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
            - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))) := by
      module
    rw [hsplit]
    exact hcomplementPsd.add hbound
  have hgapPsd : (subsetSum D selected - 1).PosSemidef := by
    have hunscale : subsetSum D selected - 1
        = (((1 : ℝ) - D.weight dropLabel)⁻¹)
          • (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)) := by
      rw [smul_smul, inv_mul_cancel₀ hsurvivingMass.ne', one_smul]
    rw [hunscale]
    exact hscaledPsd.smul (inv_nonneg.mpr hsurvivingMass.le)
  have hnonneg : 0 ≤ D.atom dropLabel ⬝ᵥ ((subsetSum D selected - 1) *ᵥ D.atom dropLabel) := by
    have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hgapPsd).2 (D.atom dropLabel)
    rwa [star_trivial] at hform
  have hnotPos : ¬ 0 < D.atom dropLabel ⬝ᵥ ((subsetSum D selected - 1) *ᵥ D.atom dropLabel) :=
    fun hpos => htie.2 selected hcard
      ((posDef_iff_pivotValue_pos_of_unitLeverage D hsize dropLabel selected hbound hunit).mpr
        hpos)
  have hzero : D.atom dropLabel ⬝ᵥ ((subsetSum D selected - 1) *ᵥ D.atom dropLabel) = 0 := by
    linarith [le_of_not_gt hnotPos, hnonneg]
  exact ⟨selected, hcard, hnotMem, hgapPsd,
    mulVec_eq_zero_of_posSemidef_of_dotProduct_zero hgapPsd hzero⟩

/-- **THE KERNEL READING AT `(6,3)`, UNCONDITIONALLY.**  The predecessor cell is
landed at five points, so the boundary branch of the `(6,3)` dichotomy carries
the rigidity with no open hypothesis. -/
theorem exists_kernel_atom_of_isTie_of_unitLeverage_sixThree (D : WeightedDesign 6 3)
    (htie : IsTie D) (dropLabel : Fin 6) (hunit : leverageOf (D.atom dropLabel) = 1) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ dropLabel ∉ selected ∧
      (subsetSum D selected - 1).PosSemidef ∧
      (subsetSum D selected - 1) *ᵥ D.atom dropLabel = 0 :=
  exists_kernel_atom_of_isTie_of_unitLeverage (m := 5) (k := 3) D (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) htie dropLabel hunit

end UnitLeverage

/-! ## 6. What an all-leverage-one design is

The trace identity decides it: the weighted leverages sum to the rank, so if
every leverage is one the weights sum to the rank, and the weights sum to one.
Rank one is the only survivor.  The all-heavy stratum therefore meets the
boundary everywhere ONLY at rank one, and above rank one every design carries a
STRICTLY heavy atom. -/

section LeverageBudget

variable {m k : ℕ}

/-- **ALL LEVERAGES ONE FORCES RANK ONE.**  The trace identity against the weight
normalization.  This is the exact reason the boundary of section 5 is a per-label
condition and never a global one. -/
theorem rank_eq_one_of_forall_leverage_eq_one (D : WeightedDesign m k)
    (hunit : ∀ label : Fin m, leverageOf (D.atom label) = 1) : k = 1 := by
  have htrace := sum_weight_mul_leverage D
  have hsum : ∑ label, D.weight label * leverageOf (D.atom label)
      = ∑ label, D.weight label :=
    Finset.sum_congr rfl fun label _ => by rw [hunit label, mul_one]
  rw [hsum, D.weight_sum_one] at htrace
  exact_mod_cast htrace.symm

/-- **ABOVE RANK ONE EVERY DESIGN CARRIES A STRICTLY HEAVY ATOM.**  The landed
budget `Gtz.sum_weight_mul_leverage_sub_one` is positive, and a positive total
needs a positive term.  No heaviness hypothesis is used: the atom found here is
strictly heavy whatever the rest of the design does. -/
theorem exists_one_lt_leverage_of_two_le_rank (D : WeightedDesign m k) (hrank : 2 ≤ k) :
    ∃ label : Fin m, 1 < leverageOf (D.atom label) := by
  have hbudget := sum_weight_mul_leverage_sub_one D
  have hcast : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrank
  have hlt : ∑ _label : Fin m, (0 : ℝ)
      < ∑ label, D.weight label * (leverageOf (D.atom label) - 1) := by
    rw [Finset.sum_const_zero, hbudget]
    linarith
  obtain ⟨label, _, hlabel⟩ := Finset.exists_lt_of_sum_lt hlt
  exact ⟨label, by nlinarith [hlabel, D.weight_pos label]⟩

/-- **AT RANK ONE THE ALL-HEAVY STRATUM IS THE BOUNDARY.**  Every atom of a
rank-one design whose leverages are all at least one has leverage exactly one.
With the theorem above this is a clean dichotomy: rank one sits entirely on the
unit-leverage boundary, and every higher rank has a strictly heavy atom. -/
theorem forall_leverage_eq_one_of_rank_one_of_heavy (D : WeightedDesign m 1)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label)) (label : Fin m) :
    leverageOf (D.atom label) = 1 := by
  have hbudget := sum_weight_mul_leverage_sub_one D
  rw [Nat.cast_one, sub_self] at hbudget
  have hterms : ∀ other : Fin m, other ∈ Finset.univ →
      0 ≤ D.weight other * (leverageOf (D.atom other) - 1) := fun other _ =>
    mul_nonneg (D.weight_pos other).le (by linarith [hheavy other])
  have hterm : D.weight label * (leverageOf (D.atom label) - 1) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hbudget label (Finset.mem_univ label)
  rcases mul_eq_zero.mp hterm with hzero | hzero
  · exact absurd hzero (D.weight_pos label).ne'
  · linarith

/-- **THE ALL-HEAVY RESIDUAL IS NEVER ENTIRELY ON THE BOUNDARY ABOVE RANK ONE.**
At rank two and above no design at all, tie or not, has every atom at leverage
exactly one, so the boundary decided in section 5 is met at some labels and
missed at others. -/
theorem not_forall_leverage_eq_one_of_two_le_rank (D : WeightedDesign m k) (hrank : 2 ≤ k) :
    ¬ ∀ label : Fin m, leverageOf (D.atom label) = 1 := by
  intro hunit
  have hone := rank_eq_one_of_forall_leverage_eq_one D hunit
  omega

end LeverageBudget

/-! ## 7. The pivot value in the design's own vocabulary

Everything above reads the pivot value as a matrix form.  It is one subtraction
away from the design: the subset's UNWEIGHTED reading of the dropped atom, minus
that atom's own leverage.  So the whole residual of the deflation lane is the
question whether the deflated subset over-reads the atom it dropped. -/

section PivotReading

variable {m k : ℕ}

/-- **THE PIVOT VALUE IS AN OVER-READING.**  Plumbing, from the landed
`Gtz.dotProduct_subsetSum_mulVec_self`. -/
theorem pivotValue_eq_reading_sub_leverage (D : WeightedDesign m k)
    (selected : Finset (Fin m)) (dropLabel : Fin m) :
    D.atom dropLabel ⬝ᵥ ((subsetSum D selected - 1) *ᵥ D.atom dropLabel)
      = (∑ c ∈ selected, (D.atom c ⬝ᵥ D.atom dropLabel) ^ 2)
        - leverageOf (D.atom dropLabel) := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    dotProduct_subsetSum_mulVec_self, leverageOf_eq_dotProduct]

/-- **A STRICT DOMINATOR OVER-READS EVERY ATOM, AT EVERY RANK.**  The general
rank form of the landed rank-three `Gtz.leverage_lt_sum_pairing_sq_of_posDef`
(Gtz/Reduction/PolarGapDeterminant.lean:619), which cannot be used at rank four
and up because its design type fixes rank three.  This is the sign half of the
pivot criterion, and it holds with no deflation input. -/
theorem leverage_lt_reading_of_posDef (D : WeightedDesign m k)
    (selected : Finset (Fin m)) (dropLabel : Fin m)
    (hatomNe : D.atom dropLabel ≠ 0)
    (hposDef : (subsetSum D selected - 1).PosDef) :
    leverageOf (D.atom dropLabel)
      < ∑ c ∈ selected, (D.atom c ⬝ᵥ D.atom dropLabel) ^ 2 := by
  have hvalue := hposDef.dotProduct_mulVec_pos hatomNe
  rw [star_trivial, pivotValue_eq_reading_sub_leverage D selected dropLabel] at hvalue
  linarith

/-- **AT A UNIT-LEVERAGE TIE THE DEFLATED SUBSET READS THE DROPPED ATOM EXACTLY
AT ONE.**  The boundary equivalence caps the reading, weak domination floors it,
and the two meet.  One scalar equation, in the design's own data, holding at
every rank on the whole unit-leverage boundary of a tie. -/
theorem reading_eq_one_of_isTie_of_unitLeverage (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (hsmaller : GtzWeighted m k) (htie : IsTie D)
    (dropLabel : Fin (m + 1)) (hunit : leverageOf (D.atom dropLabel) = 1) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = k ∧ dropLabel ∉ selected ∧
      ∑ c ∈ selected, (D.atom c ⬝ᵥ D.atom dropLabel) ^ 2 = 1 := by
  obtain ⟨selected, hcard, hnotMem, hposSemidef, hkernel⟩ :=
    exists_kernel_atom_of_isTie_of_unitLeverage D hsize hsmaller htie dropLabel hunit
  refine ⟨selected, hcard, hnotMem, ?_⟩
  have hvalue : D.atom dropLabel ⬝ᵥ ((subsetSum D selected - 1) *ᵥ D.atom dropLabel) = 0 := by
    rw [hkernel, dotProduct_zero]
  rw [pivotValue_eq_reading_sub_leverage D selected dropLabel, hunit] at hvalue
  linarith

/-- **THE SAME AT `(6,3)`, UNCONDITIONALLY.** -/
theorem reading_eq_one_of_isTie_of_unitLeverage_sixThree (D : WeightedDesign 6 3)
    (htie : IsTie D) (dropLabel : Fin 6) (hunit : leverageOf (D.atom dropLabel) = 1) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ dropLabel ∉ selected ∧
      ∑ c ∈ selected, (D.atom c ⬝ᵥ D.atom dropLabel) ^ 2 = 1 :=
  reading_eq_one_of_isTie_of_unitLeverage (m := 5) (k := 3) D (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) htie dropLabel hunit

/-- **THE OVER-READING IS NECESSARY AT EVERY LABEL OF A STRICT DOMINATOR, AND ITS
SIGN IS THE WHOLE RESIDUAL AT THE BOUNDARY.**  Assembled statement of what
sections 3, 5 and 7 give: with the deflated gap bound in hand at a unit-leverage
label, strict domination is EXACTLY the strict over-reading of the dropped
atom. -/
theorem posDef_iff_one_lt_reading_of_unitLeverage (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
      - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef)
    (hunit : leverageOf (D.atom dropLabel) = 1) :
    (subsetSum D selected - 1).PosDef
      ↔ 1 < ∑ c ∈ selected, (D.atom c ⬝ᵥ D.atom dropLabel) ^ 2 := by
  rw [posDef_iff_pivotValue_pos_of_unitLeverage D hsize dropLabel selected hbound hunit,
    pivotValue_eq_reading_sub_leverage D selected dropLabel, hunit]
  constructor <;> intro hstep <;> linarith

end PivotReading

end Gtz

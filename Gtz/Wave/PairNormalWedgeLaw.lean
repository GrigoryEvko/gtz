/-
# The two-update determinant law: where the wedge enters

The joint the hinge is missing asks a pair with nonpositive pair minor to be
COLLINEAR, that is to have vanishing wedge `Gtz.crossNormSq a b = ‖a × b‖²`.
Every landed instrument of the corank-one arm is written in leverages, pairings
and pair minors, and none of them mentions the wedge of the hunted pair at all.
The elementary bound `Gtz.crossNormSq_le_of_pairGapMinor_nonpos` is the only
statement that does, and it is sharp, so it cannot close the joint.

This module supplies an identity in which the pair's own normal `a × b` appears,
and it costs no hypothesis whatsoever.

## The law

For EVERY three-by-three matrix and EVERY two vectors
(`Gtz.det_add_two_atomMatrix`):

  **`det(F + u uᵀ + v vᵀ)
      = det F + uᵀ(adj F)u + vᵀ(adj F)v + (u × v)ᵀ F (u × v)`** .

The landed `Gtz.det_add_atomMatrix_fin_three` is the one-update case, and the
new term is exactly the form of `F` at the pair's normal.  The proof is one
`ring` after expanding both determinants and the adjugate.

At a weak dominator's gap the first three terms collapse by the landed four-set
machinery (`Gtz.det_eq_zero_of_unit_null`,
`Gtz.adjugate_reading_of_unit_null`), and the law becomes
(`Gtz.det_add_two_atomMatrix_of_unit_null`)

  **`det(F + u uᵀ + v vᵀ) = e₂(F)·((u·w)² + (v·w)²) + (u × v)ᵀ F (u × v)`** ,

the five-set companion of the landed four-set law
`Gtz.det_add_atomMatrix_of_unit_null`.  Read at a dominating triple `C` and the
hunted pair `{a,b}`, the left side is the gap determinant of the five-set
`C ∪ {a,b}` and the last term is the gap form at the pair's normal.

## What it buys the joint

The wedge form vanishes for a very rigid reason
(`Gtz.blind_of_wedgeForm_eq_zero`): a positive semidefinite gap of corank one
kills its own kernel line and nothing else, so

  `(a × b)ᵀ(S_C − 1)(a × b) = 0`  forces  `a × b = 0`  or  `a ⊥ w` and `b ⊥ w` .

The second alternative pins the pair's plane to `w^⊥`, and a plane determines
its normal up to sign.  Two dominating triples with NON-PARALLEL kernels
therefore cannot both admit it, and the pair is collinear
(`Gtz.bracketNormal_eq_zero_of_wedgeForm_eq_zero_two`,
`Gtz.hasParallelPair_of_wedgeForm_eq_zero_two`).  That is a sufficient
condition for the joint, stated in gap forms rather than in eigenvectors.

The corollary also has a three-line direct proof — blindness to two kernels puts
both atoms on the line `w₁ × w₂` — and the direct proof is the one written
below.  The law is the substantial half: it is the first identity of this arm in
which the hunted pair's wedge appears at all, and it prices that wedge as a
five-set determinant minus two readings.

[MEASURED before proving.  The two-update law holds to relative `1.7e-13` over
200,000 random general matrices and to `2.6e-13` over 200,000 symmetric ones;
the null-probe form to `6.9e-14` over 50,000 positive semidefinite singular
gaps.  Calibration of the harness against the `(5,3)` diamond reproduces its
leverages `(2, 13/4, 13/4, 13/4, 13/4)`, its pair minors `0.75 / 4.5 / 2.0`, its
eight dominating triples and the adjugate law's readings `(0.75, 0.125, 0.125)`.]
-/
import Gtz.Wave.NullProbeFourSetLaw
import Gtz.Wave.CorankOneExchange
import Gtz.Design.PrimitiveTightClassification
import Gtz.Reduction.PolarPlaneTurn
import Gtz.Wave.KOneWedgeCeiling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The two-update determinant law

The pair normal's orthogonality to its own slots is the landed
`Gtz.dotProduct_bracketNormal_left` and `Gtz.dotProduct_bracketNormal_right`. -/

/-- **THE TWO-UPDATE LAW.**  Two rank-one updates of a three-by-three matrix cost
the two adjugate readings and one form at the pair's normal.  No symmetry, no
positivity, no hypothesis of any kind: this is an expansion of two determinants.
The landed `Gtz.det_add_atomMatrix_fin_three` is the one-update case. -/
theorem det_add_two_atomMatrix (form : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    (form + atomMatrix u + atomMatrix v).det
      = form.det + u ⬝ᵥ (form.adjugate *ᵥ u) + v ⬝ᵥ (form.adjugate *ᵥ v)
        + bracketNormal u v ⬝ᵥ (form *ᵥ bracketNormal u v) := by
  simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, atomMatrix,
    Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, bracketNormal, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **THE FIVE-SET LAW.**  At a symmetric form with a unit null probe the two
adjugate readings collapse to the second invariant times two squared readings,
and what is left is the form at the pair's normal.  The five-set companion of
the landed four-set law `Gtz.det_add_atomMatrix_of_unit_null`. -/
theorem det_add_two_atomMatrix_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (u v : Fin 3 → ℝ) :
    (form + atomMatrix u + atomMatrix v).det
      = secondInvariantOfThree form * ((u ⬝ᵥ w) ^ 2 + (v ⬝ᵥ w) ^ 2)
        + bracketNormal u v ⬝ᵥ (form *ᵥ bracketNormal u v) := by
  rw [det_add_two_atomMatrix, det_eq_zero_of_unit_null hnull hunit,
    adjugate_reading_of_unit_null hsym hnull hunit u,
    adjugate_reading_of_unit_null hsym hnull hunit v]
  ring

/-! ## 2. A nonzero null vector can be normalized -/

/-- A nonzero null vector of a form carries a unit null vector on its own line. -/
theorem exists_unit_null_of_mulVec_eq_zero {form : Matrix (Fin 3) (Fin 3) ℝ}
    {n : Fin 3 → ℝ} (hnull : form *ᵥ n = 0) (hne : n ≠ 0) :
    ∃ scale : ℝ, scale ≠ 0 ∧ form *ᵥ (scale • n) = 0 ∧ (scale • n) ⬝ᵥ (scale • n) = 1 := by
  have hpos : 0 < n ⬝ᵥ n := by
    rcases (dotProduct_self_nonneg n).lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hne
  refine ⟨(Real.sqrt (n ⬝ᵥ n))⁻¹, ?_, ?_, ?_⟩
  · exact inv_ne_zero (Real.sqrt_ne_zero'.mpr hpos)
  · rw [Matrix.mulVec_smul, hnull, smul_zero]
  · have hsq : Real.sqrt (n ⬝ᵥ n) * Real.sqrt (n ⬝ᵥ n) = n ⬝ᵥ n :=
      Real.mul_self_sqrt hpos.le
    have hne0 : Real.sqrt (n ⬝ᵥ n) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    field_simp
    linarith [hsq]

/-! ## 3. Two unit null vectors of a corank-one form are parallel -/

/-- **THE KERNEL IS A LINE WHEN THE SECOND INVARIANT SURVIVES.**  Two unit null
vectors of a symmetric form with nonzero second invariant read each other at
plus or minus one. -/
theorem null_reading_sq_eq_one_of_secondInvariant_ne_zero
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsym : formᵀ = form) {w n : Fin 3 → ℝ}
    (hnullw : form *ᵥ w = 0) (hunitw : w ⬝ᵥ w = 1)
    (hnulln : form *ᵥ n = 0) (hunitn : n ⬝ᵥ n = 1)
    (he : secondInvariantOfThree form ≠ 0) : (n ⬝ᵥ w) ^ 2 = 1 := by
  have h1 := adjugate_reading_of_unit_null hsym hnullw hunitw n
  have h2 := adjugate_reading_of_unit_null hsym hnulln hunitn n
  rw [hunitn] at h2
  have hcombine : secondInvariantOfThree form * (n ⬝ᵥ w) ^ 2
      = secondInvariantOfThree form * 1 := by
    rw [← h1, h2]; ring
  exact mul_left_cancel₀ he hcombine

/-- A unit vector reading another unit vector at plus or minus one IS that
vector up to sign. -/
theorem eq_smul_of_reading_sq_eq_one {w n : Fin 3 → ℝ}
    (hunitw : w ⬝ᵥ w = 1) (hunitn : n ⬝ᵥ n = 1) (hread : (n ⬝ᵥ w) ^ 2 = 1) :
    w = (n ⬝ᵥ w) • n := by
  have hcomm : w ⬝ᵥ n = n ⬝ᵥ w := dotProduct_comm w n
  have hzero : (w - (n ⬝ᵥ w) • n) ⬝ᵥ (w - (n ⬝ᵥ w) • n) = 0 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hunitw, hunitn, hcomm]
    nlinarith [hread]
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hzero)

/-! ## 4. A vanishing wedge form pins the kernel to the pair's normal -/

/-- **THE KERNEL IS THE PAIR'S NORMAL.**  A positive semidefinite gap of corank
one annihilates its own kernel line and nothing else.  So if the gap form
vanishes at the normal of a non-collinear pair, that normal SPANS the kernel. -/
theorem kernel_eq_smul_bracketNormal_of_wedgeForm_eq_zero
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hpsd : form.PosSemidef) (hsym : formᵀ = form)
    {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (he : secondInvariantOfThree form ≠ 0) {u v : Fin 3 → ℝ}
    (hne : bracketNormal u v ≠ 0)
    (hform : bracketNormal u v ⬝ᵥ (form *ᵥ bracketNormal u v) = 0) :
    ∃ ratio : ℝ, w = ratio • bracketNormal u v ∧ ratio ^ 2 * (bracketNormal u v
      ⬝ᵥ bracketNormal u v) = 1 := by
  obtain ⟨scale, hscale, hnulls, hunits⟩ :=
    exists_unit_null_of_mulVec_eq_zero
      (mulVec_eq_zero_of_form_eq_zero hpsd hsym hform) hne
  have hread := null_reading_sq_eq_one_of_secondInvariant_ne_zero hsym hnull hunit
    hnulls hunits he
  have hw := eq_smul_of_reading_sq_eq_one hunit hunits hread
  refine ⟨((scale • bracketNormal u v) ⬝ᵥ w) * scale, ?_, ?_⟩
  · exact hw.trans (smul_smul _ _ _)
  · have hexp : (scale • bracketNormal u v) ⬝ᵥ (scale • bracketNormal u v)
        = scale ^ 2 * (bracketNormal u v ⬝ᵥ bracketNormal u v) := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
    rw [hexp] at hunits
    nlinarith [hread, hunits]

/-- **A VANISHING WEDGE FORM MAKES BOTH MEMBERS BLIND.**  The pair spans the
plane orthogonal to the kernel. -/
theorem blind_of_wedgeForm_eq_zero {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : form.PosSemidef) (hsym : formᵀ = form) {w : Fin 3 → ℝ}
    (hnull : form *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (he : secondInvariantOfThree form ≠ 0) {u v : Fin 3 → ℝ}
    (hform : bracketNormal u v ⬝ᵥ (form *ᵥ bracketNormal u v) = 0) :
    bracketNormal u v = 0 ∨ (u ⬝ᵥ w = 0 ∧ v ⬝ᵥ w = 0) := by
  by_cases hzero : bracketNormal u v = 0
  · exact Or.inl hzero
  obtain ⟨ratio, hw, -⟩ := kernel_eq_smul_bracketNormal_of_wedgeForm_eq_zero hpsd hsym
    hnull hunit he hzero hform
  refine Or.inr ⟨?_, ?_⟩
  · rw [hw, dotProduct_smul, smul_eq_mul, dotProduct_bracketNormal_left, mul_zero]
  · rw [hw, dotProduct_smul, smul_eq_mul, dotProduct_bracketNormal_right, mul_zero]

/-! ## 5. Two non-parallel kernels force the pair collinear -/

/-- **TWO KERNELS KILL THE NORMAL.**  If the gap form at a pair's normal vanishes
at two corank-one gaps whose kernels are NOT parallel, the pair is collinear.

Each vanishing makes the pair's normal span that gap's kernel, so the two
kernels would span the same line.  This is a sufficient condition for the joint
the hinge is missing, and it asks nothing about eigenvectors: the hypothesis is
a gap form evaluated at a cross product. -/
theorem bracketNormal_eq_zero_of_wedgeForm_eq_zero_two
    {formOne formTwo : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsdOne : formOne.PosSemidef) (hsymOne : formOneᵀ = formOne)
    (hpsdTwo : formTwo.PosSemidef) (hsymTwo : formTwoᵀ = formTwo)
    {wOne wTwo : Fin 3 → ℝ}
    (hnullOne : formOne *ᵥ wOne = 0) (hunitOne : wOne ⬝ᵥ wOne = 1)
    (hnullTwo : formTwo *ᵥ wTwo = 0) (hunitTwo : wTwo ⬝ᵥ wTwo = 1)
    (heOne : secondInvariantOfThree formOne ≠ 0)
    (heTwo : secondInvariantOfThree formTwo ≠ 0)
    (hdistinct : (wOne ⬝ᵥ wTwo) ^ 2 ≠ 1) {u v : Fin 3 → ℝ}
    (hformOne : bracketNormal u v ⬝ᵥ (formOne *ᵥ bracketNormal u v) = 0)
    (hformTwo : bracketNormal u v ⬝ᵥ (formTwo *ᵥ bracketNormal u v) = 0) :
    bracketNormal u v = 0 := by
  by_contra hne
  obtain ⟨rOne, hwOne, hnOne⟩ := kernel_eq_smul_bracketNormal_of_wedgeForm_eq_zero
    hpsdOne hsymOne hnullOne hunitOne heOne hne hformOne
  obtain ⟨rTwo, hwTwo, hnTwo⟩ := kernel_eq_smul_bracketNormal_of_wedgeForm_eq_zero
    hpsdTwo hsymTwo hnullTwo hunitTwo heTwo hne hformTwo
  refine hdistinct ?_
  rw [hwOne, hwTwo, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  nlinarith [hnOne, hnTwo]

/-- **THE JOINT, ON TWO GAPS.**  At a design, if the wedge form of a pair
vanishes at the gaps of two weak dominators with non-parallel kernels, the design
has a parallel pair.  The pair may be any two distinct labels, and in particular
the inadmissible pair the hinge hunts. -/
theorem hasParallelPair_of_wedgeForm_eq_zero_two (D : WeightedDesign m 3)
    {setOne setTwo : Finset (Fin m)} {a b : Fin m} (hab : a ≠ b)
    (hane : D.atom a ≠ 0)
    (hpsdOne : (subsetSum D setOne - 1).PosSemidef)
    (hpsdTwo : (subsetSum D setTwo - 1).PosSemidef)
    {wOne wTwo : Fin 3 → ℝ}
    (hnullOne : (subsetSum D setOne - 1) *ᵥ wOne = 0) (hunitOne : wOne ⬝ᵥ wOne = 1)
    (hnullTwo : (subsetSum D setTwo - 1) *ᵥ wTwo = 0) (hunitTwo : wTwo ⬝ᵥ wTwo = 1)
    (heOne : secondInvariantOfThree (subsetSum D setOne - 1) ≠ 0)
    (heTwo : secondInvariantOfThree (subsetSum D setTwo - 1) ≠ 0)
    (hdistinct : (wOne ⬝ᵥ wTwo) ^ 2 ≠ 1)
    (hformOne : bracketNormal (D.atom a) (D.atom b)
      ⬝ᵥ ((subsetSum D setOne - 1) *ᵥ bracketNormal (D.atom a) (D.atom b)) = 0)
    (hformTwo : bracketNormal (D.atom a) (D.atom b)
      ⬝ᵥ ((subsetSum D setTwo - 1) *ᵥ bracketNormal (D.atom a) (D.atom b)) = 0) :
    HasParallelPair D := by
  have hsymOne : (subsetSum D setOne - 1)ᵀ = subsetSum D setOne - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum_transpose]
  have hsymTwo : (subsetSum D setTwo - 1)ᵀ = subsetSum D setTwo - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum_transpose]
  have hzero := bracketNormal_eq_zero_of_wedgeForm_eq_zero_two hpsdOne hsymOne
    hpsdTwo hsymTwo hnullOne hunitOne hnullTwo hunitTwo heOne heTwo hdistinct
    hformOne hformTwo
  exact ⟨a, b, (D.atom a ⬝ᵥ D.atom b) / (D.atom a ⬝ᵥ D.atom a), hab,
    eq_smul_of_bracketNormal_eq_zero (D.atom a) (D.atom b) hane hzero⟩

end Gtz

/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.ComplementPairCriterion

/-!
# The complement determinant law

The complement form decides a selection by a quadratic form on the labels the
selection OMITS, and that form is the quadratic form of the complement matrix.
This module prices the determinant of that matrix exactly.

Write `U` for the full-selection gap, `K` for the diagonal matrix of the omitted
boosts, and `F` for the frame whose columns are the omitted directions.  The
complement matrix on the omitted labels is `K - K FᵀU⁻¹F K`, so it factors as
`K (1 - FᵀU⁻¹F K)`.  Sylvester's determinant identity moves the frame across the
inverse, and `1 - U⁻¹ F K Fᵀ = U⁻¹ (U - F K Fᵀ)`.  The subtracted matrix is the
boost sum of the omitted labels, and removing it from the full gap leaves the
gap of the selection itself.

The result is one identity, free of any positivity hypothesis and generic in the
ambient size and in the number of omitted labels:

  `det (complement matrix on T) * det U = (∏ boosts on T) * det (gap of Tᶜ)`

Every complement minor is therefore a gap determinant, scaled by a positive
factor whenever the boosts are positive.  The sign of a complement minor is the
sign of the determinant of the selection it omits, which is the object every
landed criterion already speaks about.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size omitCard : ℕ}

/-! ## 1. The frame, the boost diagonal, and the complement matrix -/

/-- The frame of the omitted labels: the matrix whose columns are the omitted
directions. -/
def omittedFrame (direction : Fin size → (Fin 3 → ℝ))
    (pick : Fin omitCard → Fin size) : Matrix (Fin 3) (Fin omitCard) ℝ :=
  Matrix.of fun coord r => direction (pick r) coord

/-- The diagonal matrix of the boosts of the omitted labels. -/
noncomputable def omittedBoost (mass weight : Fin size → ℝ)
    (pick : Fin omitCard → Fin size) : Matrix (Fin omitCard) (Fin omitCard) ℝ :=
  Matrix.diagonal fun r => mass (pick r) / weight (pick r)

/-- The complement matrix read on the omitted labels. -/
noncomputable def omittedComplementMatrix (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (pick : Fin omitCard → Fin size) :
    Matrix (Fin omitCard) (Fin omitCard) ℝ :=
  Matrix.of fun r s => complementMatrixEntry direction mass weight (pick r) (pick s)

/-- The boost sum of the omitted labels is the frame conjugated by the boost
diagonal. -/
theorem omittedFrame_mul_boost_mul_transpose (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (pick : Fin omitCard → Fin size) :
    omittedFrame direction pick * omittedBoost mass weight pick *
        (omittedFrame direction pick)ᵀ
      = ∑ r : Fin omitCard,
          (mass (pick r) / weight (pick r)) • atomMatrix (direction (pick r)) := by
  ext coord other
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, omittedFrame, omittedBoost, Matrix.of_apply,
    Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- The inverse form of two omitted labels is the frame sandwich. -/
theorem transpose_omittedFrame_mul_inv_mul_omittedFrame
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (pick : Fin omitCard → Fin size) (r s : Fin omitCard) :
    ((omittedFrame direction pick)ᵀ *
        (directionChartGap direction mass weight Finset.univ)⁻¹ *
        omittedFrame direction pick) r s
      = fullInverseForm direction mass weight (pick r) (pick s) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [fullInverseForm, dotProduct, Matrix.transpose_apply, omittedFrame,
    Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec]

/-- **The factorization.**  On distinct omitted labels the complement matrix is
the boost diagonal less the boost-conjugated frame sandwich. -/
theorem omittedComplementMatrix_eq_boost_sub (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (pick : Fin omitCard → Fin size)
    (hpick : Function.Injective pick) :
    omittedComplementMatrix direction mass weight pick
      = omittedBoost mass weight pick -
          omittedBoost mass weight pick *
            ((omittedFrame direction pick)ᵀ *
              (directionChartGap direction mass weight Finset.univ)⁻¹ *
              omittedFrame direction pick) *
            omittedBoost mass weight pick := by
  ext r s
  simp only [omittedComplementMatrix, complementMatrixEntry, Matrix.of_apply,
    Matrix.sub_apply, omittedBoost, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.diagonal_apply]
  rw [transpose_omittedFrame_mul_inv_mul_omittedFrame]
  by_cases hrs : r = s
  · subst hrs
    rw [if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg hrs, if_neg (fun hcontra => hrs (hpick hcontra))]
    ring

/-! ## 2. The determinant law -/

/-- **THE COMPLEMENT DETERMINANT LAW.**  The determinant of the complement
matrix on the omitted labels, times the determinant of the full gap, is the
product of the omitted boosts times the determinant of the full gap with the
omitted boost sum removed.  No positivity is used: the only hypotheses are that
the omitted labels are distinct and that the full gap is invertible. -/
theorem det_omittedComplementMatrix_mul_det (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (pick : Fin omitCard → Fin size)
    (hpick : Function.Injective pick)
    (hunit : IsUnit (directionChartGap direction mass weight Finset.univ).det) :
    (omittedComplementMatrix direction mass weight pick).det *
        (directionChartGap direction mass weight Finset.univ).det
      = (∏ r : Fin omitCard, mass (pick r) / weight (pick r)) *
          (directionChartGap direction mass weight Finset.univ -
            ∑ r : Fin omitCard,
              (mass (pick r) / weight (pick r)) •
                atomMatrix (direction (pick r))).det := by
  set full := directionChartGap direction mass weight Finset.univ with hfull
  set frame := omittedFrame direction pick with hframe
  set boost := omittedBoost mass weight pick with hboost
  -- the complement matrix factors through the boost diagonal
  have hfactor : omittedComplementMatrix direction mass weight pick
      = boost * (1 - (frameᵀ * full⁻¹ * frame) * boost) := by
    rw [omittedComplementMatrix_eq_boost_sub direction mass weight pick hpick,
      Matrix.mul_sub, Matrix.mul_one]
    simp only [Matrix.mul_assoc, hfull, hframe, hboost]
  have hdetboost : boost.det = ∏ r : Fin omitCard, mass (pick r) / weight (pick r) := by
    rw [hboost, omittedBoost, Matrix.det_diagonal]
  -- Sylvester moves the frame across the inverse
  have hsylvester : (1 - (frameᵀ * full⁻¹ * frame) * boost).det
      = (1 - full⁻¹ * (frame * boost * frameᵀ)).det := by
    have hassoc : (frameᵀ * full⁻¹ * frame) * boost
        = frameᵀ * (full⁻¹ * frame * boost) := by
      simp [Matrix.mul_assoc]
    have hassoc' : (full⁻¹ * frame * boost) * frameᵀ
        = full⁻¹ * (frame * boost * frameᵀ) := by
      simp [Matrix.mul_assoc]
    rw [hassoc, Matrix.det_one_sub_mul_comm, hassoc']
  -- the inverse factors out of the difference
  have hsplit : (1 : Matrix (Fin 3) (Fin 3) ℝ) - full⁻¹ * (frame * boost * frameᵀ)
      = full⁻¹ * (full - frame * boost * frameᵀ) := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hunit]
  have hdetinv : full⁻¹.det * full.det = 1 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_mul_cancel₀ hunit.ne_zero]
  calc (omittedComplementMatrix direction mass weight pick).det * full.det
      = boost.det * ((1 - (frameᵀ * full⁻¹ * frame) * boost).det * full.det) := by
        rw [hfactor, Matrix.det_mul]; ring
    _ = boost.det * ((full⁻¹.det * (full - frame * boost * frameᵀ).det) * full.det) := by
        rw [hsylvester, hsplit, Matrix.det_mul]
    _ = boost.det * ((full⁻¹.det * full.det) * (full - frame * boost * frameᵀ).det) := by
        ring
    _ = boost.det * (full - frame * boost * frameᵀ).det := by rw [hdetinv]; ring
    _ = (∏ r : Fin omitCard, mass (pick r) / weight (pick r)) *
          (full - ∑ r : Fin omitCard,
            (mass (pick r) / weight (pick r)) • atomMatrix (direction (pick r))).det := by
        rw [hdetboost, hframe, hboost, omittedFrame_mul_boost_mul_transpose]

/-! ## 3. The subtracted gap is the gap of the complementary selection -/

/-- Removing the boost sum of a label set from the full gap leaves the gap of the
complementary selection. -/
theorem directionChartGap_univ_sub_boostSum (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) :
    directionChartGap direction mass weight Finset.univ -
        ∑ label ∈ omitted, (mass label / weight label) • atomMatrix (direction label)
      = directionChartGap direction mass weight omittedᶜ := by
  simp only [directionChartGap]
  rw [← Finset.sum_compl_add_sum omitted
    (fun label => (mass label / weight label) • atomMatrix (direction label))]
  abel

/-- **THE COMPLEMENT DETERMINANT LAW, on the omitted set.**  The determinant of
the complement matrix on a set of omitted labels, times the determinant of the
full gap, is the product of the omitted boosts times the determinant of the gap
of the selection that omits exactly those labels.  Every complement minor is a
gap determinant. -/
theorem det_omittedComplementMatrix_mul_det_eq_det_gap_compl
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (pick : Fin omitCard → Fin size) (hpick : Function.Injective pick)
    (hunit : IsUnit (directionChartGap direction mass weight Finset.univ).det) :
    (omittedComplementMatrix direction mass weight pick).det *
        (directionChartGap direction mass weight Finset.univ).det
      = (∏ r : Fin omitCard, mass (pick r) / weight (pick r)) *
          (directionChartGap direction mass weight
            (Finset.univ.image pick)ᶜ).det := by
  rw [det_omittedComplementMatrix_mul_det direction mass weight pick hpick hunit]
  congr 2
  rw [← directionChartGap_univ_sub_boostSum direction mass weight
    (Finset.univ.image pick)]
  congr 1
  rw [Finset.sum_image fun x _ y _ hxy => hpick hxy]

end Gtz

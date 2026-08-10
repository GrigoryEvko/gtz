import Gtz.Design.LineBranchFreePairBracketExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12000000

namespace Gtz

open Matrix

/-- The gap of the full free triple in the unit-axis model. -/
def unitAxisAbstractFreeTripleGap
    (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  hiddenForm + atomMatrix (freeAtom 0) + atomMatrix (freeAtom 1)
    + atomMatrix (freeAtom 2) - 1

/-- Subtracting a rank-one atom changes a `3 x 3` determinant by its
adjugate reading.  No invertibility hypothesis is needed. -/
theorem det_sub_atomMatrix_fin_three
    (form : Matrix (Fin 3) (Fin 3) ℝ) (vector : Fin 3 → ℝ) :
    (form - atomMatrix vector).det
      = form.det - dotProduct vector (form.adjugate *ᵥ vector) := by
  simp [Matrix.det_fin_three, Matrix.adjugate_fin_three, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- The adjugate paired with its matrix has trace `3 det` in dimension
three. -/
theorem trace_adjugate_mul_self_fin_three
    (form : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (form.adjugate * form) = 3 * form.det := by
  rw [Matrix.adjugate_mul, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin]
  ring

/-- Compact form of the complete weighted free-pair determinant ledger.

The left side is the numerator of `freePairRowAggregate`.  Instead of the
forty-term bracket expansion, the right side has one full-free determinant
and one adjugate trace pairing. -/
theorem weighted_freePair_det_sum_eq_adjugateBalance
    (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (freeWeight : Fin 3 → ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ) :
    -((freeWeight 0 + freeWeight 1)
          * (hiddenForm + atomMatrix (freeAtom 0)
              + atomMatrix (freeAtom 1) - 1).det
      + (freeWeight 0 + freeWeight 2)
          * (hiddenForm + atomMatrix (freeAtom 0)
              + atomMatrix (freeAtom 2) - 1).det
      + (freeWeight 1 + freeWeight 2)
          * (hiddenForm + atomMatrix (freeAtom 1)
              + atomMatrix (freeAtom 2) - 1).det)
      = (freeWeight 0 + freeWeight 1 + freeWeight 2)
          * (unitAxisAbstractFreeTripleGap hiddenForm freeAtom).det
        + Matrix.trace
            ((unitAxisAbstractFreeTripleGap hiddenForm freeAtom).adjugate
              * ((freeWeight 0 + freeWeight 1 + freeWeight 2)
                    • (1 - hiddenForm)
                - (freeWeight 0 • atomMatrix (freeAtom 0)
                  + freeWeight 1 • atomMatrix (freeAtom 1)
                  + freeWeight 2 • atomMatrix (freeAtom 2)))) := by
  let fullGap := unitAxisAbstractFreeTripleGap hiddenForm freeAtom
  have hpairZero :
      hiddenForm + atomMatrix (freeAtom 0) + atomMatrix (freeAtom 1) - 1
        = fullGap - atomMatrix (freeAtom 2) := by
    simp [fullGap, unitAxisAbstractFreeTripleGap]
    abel
  have hpairOne :
      hiddenForm + atomMatrix (freeAtom 0) + atomMatrix (freeAtom 2) - 1
        = fullGap - atomMatrix (freeAtom 1) := by
    simp [fullGap, unitAxisAbstractFreeTripleGap]
    abel
  have hpairTwo :
      hiddenForm + atomMatrix (freeAtom 1) + atomMatrix (freeAtom 2) - 1
        = fullGap - atomMatrix (freeAtom 0) := by
    simp [fullGap, unitAxisAbstractFreeTripleGap]
    abel
  have hmetric :
      1 - hiddenForm
        = atomMatrix (freeAtom 0) + atomMatrix (freeAtom 1)
            + atomMatrix (freeAtom 2) - fullGap := by
    simp [fullGap, unitAxisAbstractFreeTripleGap]
    abel
  have htraceMetric :
      Matrix.trace (fullGap.adjugate * (1 - hiddenForm))
        = dotProduct (freeAtom 0) (fullGap.adjugate *ᵥ freeAtom 0)
          + dotProduct (freeAtom 1) (fullGap.adjugate *ᵥ freeAtom 1)
          + dotProduct (freeAtom 2) (fullGap.adjugate *ᵥ freeAtom 2)
          - 3 * fullGap.det := by
    rw [hmetric, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add,
      trace_mul_atomMatrix, trace_mul_atomMatrix, trace_mul_atomMatrix,
      trace_adjugate_mul_self_fin_three]
  have htraceWeighted :
      Matrix.trace
          (fullGap.adjugate
            * (freeWeight 0 • atomMatrix (freeAtom 0)
              + freeWeight 1 • atomMatrix (freeAtom 1)
              + freeWeight 2 • atomMatrix (freeAtom 2)))
        = freeWeight 0
              * dotProduct (freeAtom 0) (fullGap.adjugate *ᵥ freeAtom 0)
          + freeWeight 1
              * dotProduct (freeAtom 1) (fullGap.adjugate *ᵥ freeAtom 1)
          + freeWeight 2
              * dotProduct (freeAtom 2) (fullGap.adjugate *ᵥ freeAtom 2) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
      Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
      trace_mul_atomMatrix, trace_mul_atomMatrix, trace_mul_atomMatrix]
    simp only [smul_eq_mul]
  rw [hpairZero, hpairOne, hpairTwo,
    det_sub_atomMatrix_fin_three, det_sub_atomMatrix_fin_three,
    det_sub_atomMatrix_fin_three]
  change _ = _ * fullGap.det + _
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul,
    Matrix.trace_smul, htraceMetric, htraceWeighted]
  simp only [smul_eq_mul]
  ring

/-- Parseval rewrites the trace correction as a base-weight defect matrix. -/
theorem weighted_freePair_det_sum_eq_adjugateBalance_of_frame
    (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (baseWeight freeWeight : Fin 3 → ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ)
    (hframe : hiddenForm
        + freeWeight 0 • atomMatrix (freeAtom 0)
        + freeWeight 1 • atomMatrix (freeAtom 1)
        + freeWeight 2 • atomMatrix (freeAtom 2)
      = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)) :
    -((freeWeight 0 + freeWeight 1)
          * (hiddenForm + atomMatrix (freeAtom 0)
              + atomMatrix (freeAtom 1) - 1).det
      + (freeWeight 0 + freeWeight 2)
          * (hiddenForm + atomMatrix (freeAtom 0)
              + atomMatrix (freeAtom 2) - 1).det
      + (freeWeight 1 + freeWeight 2)
          * (hiddenForm + atomMatrix (freeAtom 1)
              + atomMatrix (freeAtom 2) - 1).det)
      = (freeWeight 0 + freeWeight 1 + freeWeight 2)
          * (unitAxisAbstractFreeTripleGap hiddenForm freeAtom).det
        - Matrix.trace
            ((unitAxisAbstractFreeTripleGap hiddenForm freeAtom).adjugate
              * ((1 - (freeWeight 0 + freeWeight 1 + freeWeight 2))
                    • (1 - hiddenForm)
                - Matrix.diagonal baseWeight)) := by
  rw [weighted_freePair_det_sum_eq_adjugateBalance]
  have hweighted :
      freeWeight 0 • atomMatrix (freeAtom 0)
          + freeWeight 1 • atomMatrix (freeAtom 1)
          + freeWeight 2 • atomMatrix (freeAtom 2)
        = 1 - hiddenForm - Matrix.diagonal baseWeight := by
    calc
      _ = (hiddenForm
              + freeWeight 0 • atomMatrix (freeAtom 0)
              + freeWeight 1 • atomMatrix (freeAtom 1)
              + freeWeight 2 • atomMatrix (freeAtom 2)) - hiddenForm := by
            abel
      _ = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)
              - hiddenForm := by rw [hframe]
      _ = _ := by
        ext row col
        fin_cases row <;> fin_cases col <;>
          simp [Matrix.diagonal] <;> ring
  rw [hweighted]
  have hcorrection :
      (freeWeight 0 + freeWeight 1 + freeWeight 2) • (1 - hiddenForm)
          - (1 - hiddenForm - Matrix.diagonal baseWeight)
        = -((1 - (freeWeight 0 + freeWeight 1 + freeWeight 2))
              • (1 - hiddenForm) - Matrix.diagonal baseWeight) := by
    ext row col
    simp
    ring
  rw [hcorrection, Matrix.mul_neg, Matrix.trace_neg]
  ring

/-- The compact adjugate balance for the actual transported tight-line
design.  Positivity of the left factor reduces the conditional hinge to the
sign of this single determinant--trace expression. -/
theorem unitAxisMetricDet_mul_freePairRowAggregate_eq_adjugateBalance
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (1 - unitAxisHiddenForm design).det * freePairRowAggregate design
      = (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
            + unitAxisFreeWeight design 2)
          * (unitAxisAbstractFreeTripleGap (unitAxisHiddenForm design)
              (unitAxisFreeAtom design)).det
        - Matrix.trace
            ((unitAxisAbstractFreeTripleGap (unitAxisHiddenForm design)
                (unitAxisFreeAtom design)).adjugate
              * ((1 - (unitAxisFreeWeight design 0
                        + unitAxisFreeWeight design 1
                        + unitAxisFreeWeight design 2))
                    • (1 - unitAxisHiddenForm design)
                - Matrix.diagonal (unitAxisBaseWeight design))) := by
  rw [unitAxisMetricDet_mul_freePairRowAggregate_eq_neg_detSum design hlineFree]
  simp only [unitAxisFrameFreePairGap,
    unitAxisFrameHiddenForm_eq_unitAxisHiddenForm design hlineFree]
  apply weighted_freePair_det_sum_eq_adjugateBalance_of_frame
  simpa [unitAxisBaseWeight, unitAxisFreeWeight, freeThreeLabel] using
    unitAxisFiveVectorIdentity design hlineFree

end Gtz

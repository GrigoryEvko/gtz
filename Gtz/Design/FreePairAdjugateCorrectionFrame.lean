import Gtz.Design.LineBranchFreePairAdjugateBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12000000

namespace Gtz

open Matrix

/-! # The correction frame of the free-pair adjugate balance

`Gtz.unitAxisMetricDet_mul_freePairRowAggregate_eq_adjugateBalance` writes the
scaled free-pair row aggregate as two terms: the free-triple gap determinant
scaled by the free weight total, minus one adjugate trace against the
transported metric less the base-weight diagonal.  This file names and signs the
difference between those two terms.

`unitAxisFreePairCorrectionFrame` is the gap between `U * fullGap` and the
Parseval defect, and `unitAxisFreePairCorrectionFrame_posDef_of_lineFree` makes
it POSITIVE DEFINITE from line-freeness alone.  That is the shape the failed
routes never had: line-freeness entering as a NONVANISHING that produces a
strict sign, rather than as a magnitude to be bounded below.  Every attempt to
give the aggregate a sign through a bound on some quantity has died, and the
recorded reason is always the same -- the quantity in question decays to zero
inside the branch, so no bound of the form `at least c` survives.

WHAT IT DOES NOT DO.  A positive-definite correction frame does not sign the
aggregate: the aggregate is refuted negative at exact rational-atom designs
meeting every antecedent with no strict one-slot swap and every leverage above
one, and `Gtz.exists_design_freePairRowAggregate_neg_and_exists_pos` exhibits
both signs.  What is landed here is the frame, its positivity and the balance it
sits in; the sign of the aggregate is not among them.
-/

def unitAxisAbstractFreePairDefect
    (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (freeWeight : Fin 3 → ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  unitAxisFreeWeightedFrame freeWeight freeAtom
    - (freeWeight 0 + freeWeight 1 + freeWeight 2) • (1 - hiddenForm)

/-- The positive correction between `U * fullGap` and the Parseval defect. -/

def unitAxisFreePairCorrectionFrame
    (freeWeight : Fin 3 → ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (freeWeight 1 + freeWeight 2) • atomMatrix (freeAtom 0)
    + (freeWeight 0 + freeWeight 2) • atomMatrix (freeAtom 1)
    + (freeWeight 0 + freeWeight 1) • atomMatrix (freeAtom 2)

/-- The defect lies strictly below `U` times the full-free gap by a weighted
frame containing all three free atoms. -/

theorem freeWeightSum_smul_freeTripleGap_sub_defect_eq_correctionFrame
    (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (freeWeight : Fin 3 → ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ) :
    (freeWeight 0 + freeWeight 1 + freeWeight 2)
          • unitAxisAbstractFreeTripleGap hiddenForm freeAtom
        - unitAxisAbstractFreePairDefect hiddenForm freeWeight freeAtom
      = unitAxisFreePairCorrectionFrame freeWeight freeAtom := by
  ext row col
  simp [unitAxisAbstractFreeTripleGap, unitAxisAbstractFreePairDefect,
    unitAxisFreePairCorrectionFrame, unitAxisFreeWeightedFrame]
  ring

/-- Positive free weights and a nonsingular free frame make the correction
strictly positive definite. -/

theorem unitAxisFreePairCorrectionFrame_posDef
    (freeWeight : Fin 3 → ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ)
    (hweight : ∀ index, 0 < freeWeight index)
    (hdet : (freeAtomRowFrame freeAtom).det ≠ 0) :
    (unitAxisFreePairCorrectionFrame freeWeight freeAtom).PosDef := by
  have hcoefficient : ∀ index : Fin 3,
      0 < (freeWeight 0 + freeWeight 1 + freeWeight 2) - freeWeight index := by
    intro index
    fin_cases index <;> simp <;>
      linarith [hweight 0, hweight 1, hweight 2]
  have hframe := unitAxisFreeWeightedFrame_posDef
    (fun index => (freeWeight 0 + freeWeight 1 + freeWeight 2)
      - freeWeight index) freeAtom hcoefficient hdet
  have heq :
      unitAxisFreeWeightedFrame
          (fun index => (freeWeight 0 + freeWeight 1 + freeWeight 2)
            - freeWeight index) freeAtom
        = unitAxisFreePairCorrectionFrame freeWeight freeAtom := by
    ext row col
    simp [unitAxisFreePairCorrectionFrame, unitAxisFreeWeightedFrame]
    ring
  rw [← heq]
  exact hframe

/-- Subtracting a rank-one atom changes a `3 x 3` determinant by its
adjugate reading.  No invertibility hypothesis is needed. -/

theorem weighted_freePair_det_sum_eq_det_sub_trace_defect
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
        - Matrix.trace
            ((unitAxisAbstractFreeTripleGap hiddenForm freeAtom).adjugate
              * unitAxisAbstractFreePairDefect hiddenForm freeWeight freeAtom) := by
  rw [weighted_freePair_det_sum_eq_adjugateBalance]
  unfold unitAxisAbstractFreePairDefect unitAxisFreeWeightedFrame
  have hmatrix :
      (freeWeight 0 + freeWeight 1 + freeWeight 2) • (1 - hiddenForm)
          - (freeWeight 0 • atomMatrix (freeAtom 0)
            + freeWeight 1 • atomMatrix (freeAtom 1)
            + freeWeight 2 • atomMatrix (freeAtom 2))
        = -(freeWeight 0 • atomMatrix (freeAtom 0)
            + freeWeight 1 • atomMatrix (freeAtom 1)
            + freeWeight 2 • atomMatrix (freeAtom 2)
            - (freeWeight 0 + freeWeight 1 + freeWeight 2) • (1 - hiddenForm)) := by
    abel
  rw [hmatrix, Matrix.mul_neg, Matrix.trace_neg]
  ring

/-- The scalar sign at the heart of the compact adjugate balance.  If two
eigenvalues of the correction-whitened full gap lie strictly above `1 / U`
and the third is negative, then `e₂ - 2 U e₃` is strictly positive.  The
statement is division-free so it can be consumed by polynomial arguments. -/

theorem pos_secondSymmetric_sub_two_mul_thirdSymmetric
    {weightSum first second third : ℝ}
    (hweightSum : 0 < weightSum)
    (hfirst : 1 < weightSum * first)
    (hsecond : 1 < weightSum * second)
    (hthird : third < 0) :
    0 < first * second + first * third + second * third
      - 2 * weightSum * first * second * third := by
  have hfirstPos : 0 < first := by
    by_contra hnonpos
    have hproductNonpos : weightSum * first ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hweightSum.le (not_lt.mp hnonpos)
    linarith
  have hsecondPos : 0 < second := by
    by_contra hnonpos
    have hproductNonpos : weightSum * second ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hweightSum.le (not_lt.mp hnonpos)
    linarith
  have hfirstSecond : 0 < first * second := mul_pos hfirstPos hsecondPos
  have hfirstSlack : 0 < first * (weightSum * second - 1) :=
    mul_pos hfirstPos (by linarith)
  have hsecondSlack : 0 < second * (weightSum * first - 1) :=
    mul_pos hsecondPos (by linarith)
  have htailCoefficient :
      0 < 2 * weightSum * first * second - first - second := by
    nlinarith [hfirstSlack, hsecondSlack]
  have htail :
      0 < (-third) * (2 * weightSum * first * second - first - second) :=
    mul_pos (by linarith) htailCoefficient
  nlinarith [hfirstSecond, htail]

/-- Matrix-literal version of
`pos_secondSymmetric_sub_two_mul_thirdSymmetric`.  This is the exact compact
adjugate balance after both positive congruences have diagonalized the full
gap. -/

theorem diagonal_adjugateBalance_pos
    {weightSum first second third : ℝ}
    (hweightSum : 0 < weightSum)
    (hfirst : 1 < weightSum * first)
    (hsecond : 1 < weightSum * second)
    (hthird : third < 0) :
    0 < weightSum * (Matrix.diagonal ![first, second, third]).det
      - Matrix.trace
          ((Matrix.diagonal ![first, second, third]).adjugate
            * (weightSum • Matrix.diagonal ![first, second, third] - 1)) := by
  have hscalar := pos_secondSymmetric_sub_two_mul_thirdSymmetric
    hweightSum hfirst hsecond hthird
  have hexpand :
      weightSum * (Matrix.diagonal ![first, second, third]).det
          - Matrix.trace
              ((Matrix.diagonal ![first, second, third]).adjugate
                * (weightSum • Matrix.diagonal ![first, second, third] - 1))
        = first * second + first * third + second * third
            - 2 * weightSum * first * second * third := by
    simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    simp
    ring
  rw [hexpand]
  exact hscalar

/-- Parseval rewrites the trace correction as a base-weight defect matrix. -/

theorem unitAxisFreePairCorrectionFrame_posDef_of_lineFree
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (unitAxisFreePairCorrectionFrame (unitAxisFreeWeight design)
      (unitAxisFreeAtom design)).PosDef := by
  apply unitAxisFreePairCorrectionFrame_posDef
  · intro index
    exact design.weight_pos (freeThreeLabel index)
  · rw [freeAtomRowFrame_unitAxisFreeAtom]
    exact unitAxisFreeFrame_det_ne_zero design hlineFree



end Gtz

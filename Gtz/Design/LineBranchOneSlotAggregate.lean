import Gtz.Design.LineBranchOneSlotDeterminant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6000000

namespace Gtz

open Matrix

/-! ## The normalization-sensitive one-slot aggregate

The three free atoms disappear after weighting the determinant-update identity
by their design weights and spending the five-vector Parseval identity.  This
is the scalar constraint carried by simultaneous refusal of the three
one-slot completions at a fixed live base pair.
-/

/-- A three-term weighted quadratic-form sum is the trace pairing against the
weighted atom-matrix sum. -/
theorem three_weighted_quadForm_eq_trace
    (form : Matrix (Fin 3) (Fin 3) ℝ)
    (firstWeight secondWeight thirdWeight : ℝ)
    (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    firstWeight * (firstVec ⬝ᵥ (form *ᵥ firstVec))
        + secondWeight * (secondVec ⬝ᵥ (form *ᵥ secondVec))
        + thirdWeight * (thirdVec ⬝ᵥ (form *ᵥ thirdVec))
      = Matrix.trace
          (form * (firstWeight • atomMatrix firstVec
            + secondWeight • atomMatrix secondVec
            + thirdWeight • atomMatrix thirdVec)) := by
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    trace_mul_atomMatrix, trace_mul_atomMatrix, trace_mul_atomMatrix]
  simp only [smul_eq_mul]

/-- Weighted determinant updates for three atoms collapse to one trace. -/
theorem three_weighted_det_add_atomMatrix_eq
    (form : Matrix (Fin 3) (Fin 3) ℝ)
    (firstWeight secondWeight thirdWeight : ℝ)
    (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    firstWeight * (form + atomMatrix firstVec).det
        + secondWeight * (form + atomMatrix secondVec).det
        + thirdWeight * (form + atomMatrix thirdVec).det
      = (firstWeight + secondWeight + thirdWeight) * form.det
        + Matrix.trace
            (form.adjugate * (firstWeight • atomMatrix firstVec
              + secondWeight • atomMatrix secondVec
              + thirdWeight • atomMatrix thirdVec)) := by
  rw [det_add_atomMatrix_fin_three, det_add_atomMatrix_fin_three,
    det_add_atomMatrix_fin_three,
    ← three_weighted_quadForm_eq_trace]
  ring

/-- Spend a matrix identity for the weighted atom sum. -/
theorem three_weighted_det_add_atomMatrix_eq_of_frame
    (form target hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (firstWeight secondWeight thirdWeight : ℝ)
    (firstVec secondVec thirdVec : Fin 3 → ℝ)
    (hframe : hiddenForm
        + firstWeight • atomMatrix firstVec
        + secondWeight • atomMatrix secondVec
        + thirdWeight • atomMatrix thirdVec = target) :
    firstWeight * (form + atomMatrix firstVec).det
        + secondWeight * (form + atomMatrix secondVec).det
        + thirdWeight * (form + atomMatrix thirdVec).det
      = (firstWeight + secondWeight + thirdWeight) * form.det
        + Matrix.trace (form.adjugate * (target - hiddenForm)) := by
  rw [three_weighted_det_add_atomMatrix_eq]
  have hsum : firstWeight • atomMatrix firstVec
          + secondWeight • atomMatrix secondVec
          + thirdWeight • atomMatrix thirdVec
        = target - hiddenForm := by
    rw [← hframe]
    abel
  rw [hsum]

/-- The exact one-slot determinant aggregate in the unit-axis tight-line
normal form.  The right side contains no free-atom coordinate. -/
theorem unitAxisHiddenOneSlot_weighted_det_sum_eq
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (omittedBase : Fin 3) :
    design.weight 3
          * (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
              (unitAxisFreeAtom design) omittedBase 0).det
        + design.weight 4
          * (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
              (unitAxisFreeAtom design) omittedBase 1).det
        + design.weight 5
          * (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
              (unitAxisFreeAtom design) omittedBase 2).det
      = (design.weight 3 + design.weight 4 + design.weight 5)
          * (unitAxisHiddenForm design
              - atomMatrix (Pi.single omittedBase 1)).det
        + Matrix.trace
            ((unitAxisHiddenForm design
                - atomMatrix (Pi.single omittedBase 1)).adjugate
              * (Matrix.diagonal (fun coordinate =>
                    1 - design.weight (baseThreeLabel coordinate))
                  - unitAxisHiddenForm design)) := by
  let form := unitAxisHiddenForm design - atomMatrix (Pi.single omittedBase 1)
  have hgap : ∀ freeIndex : Fin 3,
      unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
          (unitAxisFreeAtom design) omittedBase freeIndex
        = form + atomMatrix (unitAxisFreeAtom design freeIndex) := by
    intro freeIndex
    simp [unitAxisHiddenOneSlotGap, form]
    abel
  rw [hgap 0, hgap 1, hgap 2]
  exact three_weighted_det_add_atomMatrix_eq_of_frame form
    (Matrix.diagonal (fun coordinate =>
      1 - design.weight (baseThreeLabel coordinate)))
    (unitAxisHiddenForm design)
    (design.weight 3) (design.weight 4) (design.weight 5)
    (unitAxisFreeAtom design 0) (unitAxisFreeAtom design 1)
    (unitAxisFreeAtom design 2)
    (unitAxisFiveVectorIdentity design hlineFree)

/-- Simultaneous refusal of the three one-slot candidates at an omitted base
coordinate forces the free-atom-free aggregate scalar to be nonpositive. -/
theorem unitAxisHiddenOneSlot_aggregate_nonpos_of_refusal
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (omittedBase : Fin 3)
    (hrefusal : ∀ freeIndex : Fin 3,
      (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) omittedBase freeIndex).det ≤ 0) :
    (design.weight 3 + design.weight 4 + design.weight 5)
          * (unitAxisHiddenForm design
              - atomMatrix (Pi.single omittedBase 1)).det
        + Matrix.trace
            ((unitAxisHiddenForm design
                - atomMatrix (Pi.single omittedBase 1)).adjugate
              * (Matrix.diagonal (fun coordinate =>
                    1 - design.weight (baseThreeLabel coordinate))
                  - unitAxisHiddenForm design)) ≤ 0 := by
  have hzero := mul_nonpos_of_nonneg_of_nonpos (design.weight_pos 3).le (hrefusal 0)
  have hone := mul_nonpos_of_nonneg_of_nonpos (design.weight_pos 4).le (hrefusal 1)
  have htwo := mul_nonpos_of_nonneg_of_nonpos (design.weight_pos 5).le (hrefusal 2)
  rw [← unitAxisHiddenOneSlot_weighted_det_sum_eq design hlineFree omittedBase]
  linarith

/-! ## A base-only scalar form

The following scalar is permutation-invariant.  In dimension three, for fixed
`omittedBase` and another coordinate `i`, the expression
`trace H - H_rr - H_ii` is the diagonal entry at the unique third coordinate.
This avoids choosing names for the two retained axes.
-/

noncomputable def unitAxisHiddenOneSlotAggregateScalar
    (design : WeightedDesign 6 3) (omittedBase : Fin 3) : ℝ :=
  let hiddenForm := unitAxisHiddenForm design
  2 * hiddenForm.adjugate omittedBase omittedBase
    + ∑ coordinate ∈ (Finset.univ.erase omittedBase),
        hiddenForm.adjugate coordinate coordinate
    - ∑ coordinate ∈ (Finset.univ.erase omittedBase),
        hiddenForm coordinate coordinate
    + ∑ coordinate ∈ (Finset.univ.erase omittedBase),
        design.weight (baseThreeLabel coordinate)
          * (hiddenForm.adjugate omittedBase omittedBase
              - hiddenForm.adjugate coordinate coordinate
              + Matrix.trace hiddenForm
              - hiddenForm omittedBase omittedBase
              - hiddenForm coordinate coordinate)

/-- After singularity and weight normalization are spent, the free-coordinate-
free aggregate has the explicit scalar form above. -/
theorem unitAxisHiddenOneSlot_aggregate_eq_scalar
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (omittedBase : Fin 3) :
    (design.weight 3 + design.weight 4 + design.weight 5)
          * (unitAxisHiddenForm design
              - atomMatrix (Pi.single omittedBase 1)).det
        + Matrix.trace
            ((unitAxisHiddenForm design
                - atomMatrix (Pi.single omittedBase 1)).adjugate
              * (Matrix.diagonal (fun coordinate =>
                    1 - design.weight (baseThreeLabel coordinate))
                  - unitAxisHiddenForm design))
      = unitAxisHiddenOneSlotAggregateScalar design omittedBase := by
  classical
  have hdet := unitAxisHiddenForm_det_eq_zero design hlineFree hdominates
    htightNe htight
  have hweight := design.weight_sum_one
  rw [Fin.sum_univ_six] at hweight
  have hfree : design.weight 3 + design.weight 4 + design.weight 5
      = 1 - (design.weight 0 + design.weight 1 + design.weight 2) := by
    linarith [hweight]
  have hsym := unitAxisHiddenForm_transpose design
  have h01 := congrFun (congrFun hsym 0) 1
  have h02 := congrFun (congrFun hsym 0) 2
  have h12 := congrFun (congrFun hsym 1) 2
  rw [hfree]
  fin_cases omittedBase <;>
    simp [unitAxisHiddenOneSlotAggregateScalar, Matrix.det_fin_three,
      Matrix.adjugate_fin_three, Matrix.trace, Matrix.diag,
      atomMatrix, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Fin.sum_univ_three, baseThreeLabel] at hdet h01 h02 h12 ⊢ <;>
    rw [h01, h02, h12] at hdet ⊢ <;>
    linear_combination
      -(design.weight 0 + design.weight 1 + design.weight 2 + 2) * hdet

/-- Simultaneous refusal gives the explicit base-only inequality. -/
theorem unitAxisHiddenOneSlot_scalar_nonpos_of_refusal
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (omittedBase : Fin 3)
    (hrefusal : ∀ freeIndex : Fin 3,
      (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) omittedBase freeIndex).det ≤ 0) :
    unitAxisHiddenOneSlotAggregateScalar design omittedBase ≤ 0 := by
  rw [← unitAxisHiddenOneSlot_aggregate_eq_scalar design hlineFree hdominates
    htightNe htight omittedBase]
  exact unitAxisHiddenOneSlot_aggregate_nonpos_of_refusal design hlineFree
    omittedBase hrefusal

end Gtz

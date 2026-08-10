import Gtz.Design.LineBranchLineFreeCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix

/-- A one-slot swap in the line-branch unit-axis model: omit one base axis and
insert one free atom. -/
def unitAxisHiddenOneSlotGap (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ) (omittedBase freeIndex : Fin 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  hiddenForm + atomMatrix (freeAtom freeIndex) - atomMatrix (Pi.single omittedBase 1)

/-- A distance-two swap in the line-branch unit-axis model: retain one base
axis and insert two free atoms. -/
def unitAxisHiddenDistanceTwoGap (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ)
    (retainedBase freeOne freeTwo : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  hiddenForm + atomMatrix (freeAtom freeOne) + atomMatrix (freeAtom freeTwo)
    - planeAxisPenaltyExcept (fun _ : Fin 3 => (1 : ℝ)) retainedBase

/-- The all-free complement in the line-branch unit-axis model. -/
def unitAxisHiddenComplementGap (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  hiddenForm + atomMatrix (freeAtom 0) + atomMatrix (freeAtom 1)
    + atomMatrix (freeAtom 2) - 1

theorem unitAxisHiddenOneSlotGap_transpose
    (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ) (htranspose : hiddenFormᵀ = hiddenForm)
    (freeAtom : Fin 3 → Fin 3 → ℝ) (omittedBase freeIndex : Fin 3) :
    (unitAxisHiddenOneSlotGap hiddenForm freeAtom omittedBase freeIndex)ᵀ
      = unitAxisHiddenOneSlotGap hiddenForm freeAtom omittedBase freeIndex := by
  unfold unitAxisHiddenOneSlotGap atomMatrix
  rw [Matrix.transpose_sub, Matrix.transpose_add, htranspose,
    Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec]

theorem unitAxisHiddenDistanceTwoGap_transpose
    (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ) (htranspose : hiddenFormᵀ = hiddenForm)
    (freeAtom : Fin 3 → Fin 3 → ℝ)
    (retainedBase freeOne freeTwo : Fin 3) :
    (unitAxisHiddenDistanceTwoGap hiddenForm freeAtom retainedBase freeOne freeTwo)ᵀ
      = unitAxisHiddenDistanceTwoGap hiddenForm freeAtom retainedBase freeOne freeTwo := by
  unfold unitAxisHiddenDistanceTwoGap planeAxisPenaltyExcept atomMatrix
  rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_add, htranspose,
    Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec, diagonal_transpose]

/-- Line-freeness supplies a positive unpenalized corner for every one-slot
candidate. The hidden form contributes only a nonnegative diagonal term. -/
theorem unitAxisHiddenOneSlotGap_corner_pos
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hhidden : (unitAxisHiddenForm design).PosSemidef)
    (omittedBase freeIndex front : Fin 3) (hfront : front ≠ omittedBase) :
    0 < unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
      (unitAxisFreeAtom design) omittedBase freeIndex front front := by
  have hdiag : 0 ≤ unitAxisHiddenForm design front front := hhidden.diag_nonneg
  have hfree : unitAxisFreeAtom design freeIndex front ≠ 0 :=
    unitAxisFreeAtom_coordinate_ne_zero design hlineFree freeIndex front
  simp only [unitAxisHiddenOneSlotGap, Matrix.sub_apply, Matrix.add_apply,
    atomMatrix, Matrix.vecMulVec_apply, Pi.single_apply, hfront, if_false,
    mul_zero]
  nlinarith [sq_pos_of_ne_zero hfree]

/-- Line-freeness supplies the positive retained-axis corner for every
distance-two candidate. No off-conicity is used. -/
theorem unitAxisHiddenDistanceTwoGap_retained_corner_pos
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hhidden : (unitAxisHiddenForm design).PosSemidef)
    (retainedBase freeOne freeTwo : Fin 3) :
    0 < unitAxisHiddenDistanceTwoGap (unitAxisHiddenForm design)
      (unitAxisFreeAtom design) retainedBase freeOne freeTwo
        retainedBase retainedBase := by
  have hdiag : 0 ≤ unitAxisHiddenForm design retainedBase retainedBase :=
    hhidden.diag_nonneg
  have hfree : unitAxisFreeAtom design freeOne retainedBase ≠ 0 :=
    unitAxisFreeAtom_coordinate_ne_zero design hlineFree freeOne retainedBase
  simp only [unitAxisHiddenDistanceTwoGap, Matrix.sub_apply, Matrix.add_apply,
    atomMatrix, Matrix.vecMulVec_apply, planeAxisPenaltyExcept,
    Matrix.diagonal_apply, if_pos, sub_zero]
  nlinarith [sq_pos_of_ne_zero hfree,
    sq_nonneg (unitAxisFreeAtom design freeTwo retainedBase)]

/-- Two-sign Sylvester test for every one-slot line-branch candidate. -/
theorem unitAxisHiddenOneSlotGap_posDef_iff_two_reindexedMinors
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hhidden : (unitAxisHiddenForm design).PosSemidef)
    (omittedBase freeIndex : Fin 3) (reindex : Fin 3 ≃ Fin 3)
    (hfront : reindex 0 ≠ omittedBase) :
    let gap := unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
      (unitAxisFreeAtom design) omittedBase freeIndex
    gap.PosDef ↔
      (0 < gap (reindex 0) (reindex 0) * gap (reindex 1) (reindex 1)
          - gap (reindex 0) (reindex 1) ^ 2
        ∧ 0 < gap (reindex 0) (reindex 0) * gap (reindex 1) (reindex 1)
              * gap (reindex 2) (reindex 2)
            - gap (reindex 0) (reindex 0) * gap (reindex 1) (reindex 2) ^ 2
            - gap (reindex 0) (reindex 1) ^ 2 * gap (reindex 2) (reindex 2)
            + 2 * gap (reindex 0) (reindex 1) * gap (reindex 0) (reindex 2)
                * gap (reindex 1) (reindex 2)
            - gap (reindex 0) (reindex 2) ^ 2 * gap (reindex 1) (reindex 1)) := by
  dsimp only
  apply posDef_finThree_iff_two_reindexedMinors_of_corner_pos
  · exact unitAxisHiddenOneSlotGap_transpose _
      (unitAxisHiddenForm_transpose design) _ _ _
  · exact unitAxisHiddenOneSlotGap_corner_pos design hlineFree hhidden
      omittedBase freeIndex (reindex 0) hfront

/-- Two-sign Sylvester test for every distance-two line-branch candidate. -/
theorem unitAxisHiddenDistanceTwoGap_posDef_iff_two_reindexedMinors
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hhidden : (unitAxisHiddenForm design).PosSemidef)
    (retainedBase freeOne freeTwo : Fin 3) (reindex : Fin 3 ≃ Fin 3)
    (hfront : reindex 0 = retainedBase) :
    let gap := unitAxisHiddenDistanceTwoGap (unitAxisHiddenForm design)
      (unitAxisFreeAtom design) retainedBase freeOne freeTwo
    gap.PosDef ↔
      (0 < gap (reindex 0) (reindex 0) * gap (reindex 1) (reindex 1)
          - gap (reindex 0) (reindex 1) ^ 2
        ∧ 0 < gap (reindex 0) (reindex 0) * gap (reindex 1) (reindex 1)
              * gap (reindex 2) (reindex 2)
            - gap (reindex 0) (reindex 0) * gap (reindex 1) (reindex 2) ^ 2
            - gap (reindex 0) (reindex 1) ^ 2 * gap (reindex 2) (reindex 2)
            + 2 * gap (reindex 0) (reindex 1) * gap (reindex 0) (reindex 2)
                * gap (reindex 1) (reindex 2)
            - gap (reindex 0) (reindex 2) ^ 2 * gap (reindex 1) (reindex 1)) := by
  dsimp only
  apply posDef_finThree_iff_two_reindexedMinors_of_corner_pos
  · exact unitAxisHiddenDistanceTwoGap_transpose _
      (unitAxisHiddenForm_transpose design) _ _ _ _
  · rw [hfront]
    exact unitAxisHiddenDistanceTwoGap_retained_corner_pos design hlineFree
      hhidden retainedBase freeOne freeTwo

end Gtz

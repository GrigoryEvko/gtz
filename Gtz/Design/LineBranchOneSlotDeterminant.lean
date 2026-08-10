import Gtz.Design.LineBranchBasePairLiveness
import Gtz.Design.PlaneBranchComplementSelector

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6000000

namespace Gtz

open Matrix

/-- Restricting a one-slot gap to the two coordinates not omitted removes the
negative coordinate projector entirely. -/
theorem unitAxisHiddenOneSlotGap_submatrix_succAbove
    (design : WeightedDesign 6 3) (omittedBase freeIndex : Fin 3) :
    (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) omittedBase freeIndex).submatrix
          omittedBase.succAbove omittedBase.succAbove
      = (unitAxisHiddenForm design).submatrix
          omittedBase.succAbove omittedBase.succAbove
        + atomMatrix (fun coordinate : Fin 2 =>
            unitAxisFreeAtom design freeIndex
              (omittedBase.succAbove coordinate)) := by
  ext row col
  simp [unitAxisHiddenOneSlotGap, Matrix.submatrix_apply, atomMatrix,
    Matrix.vecMulVec_apply, Fin.succAbove_ne]

/-- For a nonzero kernel coordinate, every one-slot candidate omitting that
coordinate has a positive-definite surviving two-dimensional block. -/
theorem unitAxisHiddenOneSlotGap_survivingBlock_posDef
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (omittedBase freeIndex : Fin 3)
    (homitted : unitAxisTightVector design tightDir omittedBase ≠ 0) :
    ((unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) omittedBase freeIndex).submatrix
          omittedBase.succAbove omittedBase.succAbove).PosDef := by
  rw [unitAxisHiddenOneSlotGap_submatrix_succAbove]
  exact (unitAxisHiddenForm_submatrix_posDef_of_tightCoordinate_ne_zero
    design hlineFree hdominates htight hline omittedBase homitted).add_posSemidef
      (posSemidef_atomMatrix _)

/-- Put the omitted coordinate last, so the first two leading coordinates are
exactly its surviving principal block. -/
def unitAxisOmittedLastOrder (omittedBase : Fin 3) : Fin 3 ≃ Fin 3 :=
  Equiv.swap 2 omittedBase

@[simp] theorem unitAxisOmittedLastOrder_two (omittedBase : Fin 3) :
    unitAxisOmittedLastOrder omittedBase 2 = omittedBase := by
  simp [unitAxisOmittedLastOrder]

/-- In dimension three, a symmetric form with a positive-definite principal
block is positive definite exactly when its full determinant is positive. -/
theorem posDef_finThree_iff_det_pos_of_complementSubmatrix_posDef
    (form : Matrix (Fin 3) (Fin 3) ℝ) (hsym : formᵀ = form)
    (omittedBase : Fin 3)
    (hblock : (form.submatrix omittedBase.succAbove omittedBase.succAbove).PosDef) :
    form.PosDef ↔ 0 < form.det := by
  let order := unitAxisOmittedLastOrder omittedBase
  have hlower : ∀ row col : Fin 3, form col row = form row col := by
    intro row col
    have hentry := congrFun (congrFun hsym row) col
    simpa only [Matrix.transpose_apply] using hentry
  have hcorner : 0 < form (order 0) (order 0) := by
    fin_cases omittedBase
    · have hdiag := hblock.diag_pos (i := (1 : Fin 2))
      simpa [order, unitAxisOmittedLastOrder, Equiv.swap_apply_def,
        Matrix.submatrix_apply, Fin.succAbove] using hdiag
    · have hdiag := hblock.diag_pos (i := (0 : Fin 2))
      simpa [order, unitAxisOmittedLastOrder, Equiv.swap_apply_def,
        Matrix.submatrix_apply, Fin.succAbove] using hdiag
    · have hdiag := hblock.diag_pos (i := (0 : Fin 2))
      simpa [order, unitAxisOmittedLastOrder, Equiv.swap_apply_def,
        Matrix.submatrix_apply, Fin.succAbove] using hdiag
  have hminor :
      0 < form (order 0) (order 0) * form (order 1) (order 1)
        - form (order 0) (order 1) ^ 2 := by
    have hdetBlock := hblock.det_pos
    fin_cases omittedBase
    all_goals
      simp [Matrix.det_fin_two, Matrix.submatrix_apply, order,
        unitAxisOmittedLastOrder, Equiv.swap_apply_def, Fin.succAbove]
        at hdetBlock ⊢
    · rw [hlower 1 2] at hdetBlock ⊢
      nlinarith
    · rw [hlower 0 2] at hdetBlock
      nlinarith
    · rw [hlower 0 1] at hdetBlock
      nlinarith
  have hdetCriterion :
      form (order 0) (order 0) * form (order 1) (order 1) * form (order 2) (order 2)
          - form (order 0) (order 0) * form (order 1) (order 2) ^ 2
          - form (order 0) (order 1) ^ 2 * form (order 2) (order 2)
          + 2 * form (order 0) (order 1) * form (order 0) (order 2)
              * form (order 1) (order 2)
          - form (order 0) (order 2) ^ 2 * form (order 1) (order 1)
        = form.det := by
    rw [← Matrix.det_submatrix_equiv_self order form, Matrix.det_fin_three]
    simp only [Matrix.submatrix_apply]
    rw [hlower (order 0) (order 1), hlower (order 0) (order 2),
      hlower (order 1) (order 2)]
    ring
  rw [posDef_finThree_iff_reindexedLeadingMinors form hsym order,
    hdetCriterion, and_iff_right hcorner, and_iff_right hminor]

/-- On every live omitted-base coordinate, each one-slot candidate costs one
sign only: positivity of its determinant. -/
theorem unitAxisHiddenOneSlotGap_posDef_iff_det_pos_of_tightCoordinate_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (omittedBase freeIndex : Fin 3)
    (homitted : unitAxisTightVector design tightDir omittedBase ≠ 0) :
    (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) omittedBase freeIndex).PosDef ↔
      0 < (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) omittedBase freeIndex).det := by
  apply posDef_finThree_iff_det_pos_of_complementSubmatrix_posDef
  · exact unitAxisHiddenOneSlotGap_transpose _
      (unitAxisHiddenForm_transpose design) _ _ _
  · exact unitAxisHiddenOneSlotGap_survivingBlock_posDef design hlineFree
      hdominates htight hline omittedBase freeIndex homitted

/-- Exact one-slot determinant ledger at a tight line. The positive candidate
must overcome precisely the omitted base pair's cofactor. -/
theorem unitAxisHiddenOneSlotGap_det_eq_adjugateDemand
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (omittedBase freeIndex : Fin 3) :
    (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) omittedBase freeIndex).det
      = -(unitAxisHiddenForm design).adjugate omittedBase omittedBase
        + unitAxisFreeAtom design freeIndex ⬝ᵥ
            ((unitAxisHiddenForm design
                - atomMatrix (Pi.single omittedBase 1)).adjugate *ᵥ
              unitAxisFreeAtom design freeIndex) := by
  let hiddenForm := unitAxisHiddenForm design
  let freeVector := unitAxisFreeAtom design freeIndex
  have hgap : unitAxisHiddenOneSlotGap hiddenForm
      (unitAxisFreeAtom design) omittedBase freeIndex
        = (hiddenForm - atomMatrix (Pi.single omittedBase 1))
            + atomMatrix freeVector := by
    simp [unitAxisHiddenOneSlotGap, hiddenForm, freeVector]
    abel
  rw [hgap, det_add_atomMatrix_fin_three, det_sub_axisAtom_fin_three,
    unitAxisHiddenForm_det_eq_zero design hlineFree hdominates htightNe htight]
  simp [hiddenForm, freeVector]

/-- There is a base pair for which all three one-slot candidates are governed
by one sharp, division-free scalar inequality. -/
theorem exists_unitAxisBasePair_oneSlot_adjugateCriterion
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    ∃ omittedBase : Fin 3,
      0 < (unitAxisHiddenForm design).adjugate omittedBase omittedBase
        ∧ ∀ freeIndex : Fin 3,
          (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
              (unitAxisFreeAtom design) omittedBase freeIndex).PosDef ↔
            (unitAxisHiddenForm design).adjugate omittedBase omittedBase
              < unitAxisFreeAtom design freeIndex ⬝ᵥ
                  ((unitAxisHiddenForm design
                      - atomMatrix (Pi.single omittedBase 1)).adjugate *ᵥ
                    unitAxisFreeAtom design freeIndex) := by
  have hkernelNe := unitAxisTightVector_ne_zero design hlineFree htightNe
  have hexists : ∃ omittedBase : Fin 3,
      unitAxisTightVector design tightDir omittedBase ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hkernelNe
    funext omittedBase
    exact hall omittedBase
  obtain ⟨omittedBase, homitted⟩ := hexists
  refine ⟨omittedBase,
    unitAxisHiddenForm_adjugate_diag_pos_of_tightCoordinate_ne_zero
      design hlineFree hdominates htight hline omittedBase homitted, ?_⟩
  intro freeIndex
  rw [unitAxisHiddenOneSlotGap_posDef_iff_det_pos_of_tightCoordinate_ne_zero
    design hlineFree hdominates htight hline omittedBase freeIndex homitted,
    unitAxisHiddenOneSlotGap_det_eq_adjugateDemand design hlineFree hdominates
      htightNe htight omittedBase freeIndex]
  constructor <;> intro hineq <;> linarith

end Gtz

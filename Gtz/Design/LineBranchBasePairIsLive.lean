import Gtz.Design.LineBranchOneSlotDeterminant
import Gtz.Reduction.BranchTwoRational

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6000000

namespace Gtz

open Matrix Finset

/-- The unit-axis subset gap is the original subset gap under the same
congruence used to normalize the base atoms. -/
theorem unitAxisHiddenSubsetGap_eq_congr_gap
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (selected : Finset (Fin 6)) :
    unitAxisHiddenSubsetGap (unitAxisFreeAtom design)
        (unitAxisHiddenForm design) selected
      = (unitAxisBaseNormalizer design)ᵀ
          * (subsetSum design selected - 1)
          * unitAxisBaseNormalizer design := by
  let P := unitAxisBaseNormalizer design
  have hatom := unitAxisBaseNormalizer_atom_eq_axisBaseAtom design hlineFree
  have hmetric : 1 - unitAxisHiddenForm design = Pᵀ * P := by
    symm
    exact unitAxisBaseNormalizer_metric_eq_one_sub_hiddenForm design
  simp only [unitAxisHiddenSubsetGap]
  rw [hmetric]
  change (∑ label ∈ selected,
      atomMatrix ((axisBaseAtom (fun _ : Fin 3 => (1 : ℝ))
        (unitAxisFreeAtom design)) label)) - Pᵀ * P = _
  rw [← hatom, sum_atomMatrix_conj, subsetSum]
  noncomm_ring

/-- Congruence multiplies every normalized subset determinant by the positive
square of the base normalizer determinant. -/
theorem unitAxisHiddenSubsetGap_det_eq_det_sq_mul
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (selected : Finset (Fin 6)) :
    (unitAxisHiddenSubsetGap (unitAxisFreeAtom design)
        (unitAxisHiddenForm design) selected).det
      = (unitAxisBaseNormalizer design).det ^ 2
          * (subsetSum design selected - 1).det := by
  rw [unitAxisHiddenSubsetGap_eq_congr_gap design hlineFree selected,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Erasing base coordinate `axis` leaves exactly the hidden form minus that
coordinate projector. -/
theorem unitAxisHiddenSubsetGap_baseErase
    (design : WeightedDesign 6 3) (axis : Fin 3) :
    unitAxisHiddenSubsetGap (unitAxisFreeAtom design)
        (unitAxisHiddenForm design)
        (({0, 1, 2} : Finset (Fin 6)).erase (baseThreeLabel axis))
      = unitAxisHiddenForm design - atomMatrix (Pi.single axis 1) := by
  fin_cases axis
  all_goals
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [unitAxisHiddenSubsetGap, axisBaseAtom, baseThreeLabel,
        atomMatrix, Matrix.vecMulVec_apply]

/-- The original pair left after erasing a nonzero tight coordinate has
positive pair-gap excess. -/
theorem pairGapExcessOf_baseErase_pos_of_tightCoordinate_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (axis : Fin 3)
    (haxis : unitAxisTightVector design tightDir axis ≠ 0) :
    0 < pairGapExcessOf design
      (baseThreeLabel (axis.succAbove 0))
      (baseThreeLabel (axis.succAbove 1)) := by
  let selected := ({0, 1, 2} : Finset (Fin 6)).erase (baseThreeLabel axis)
  have hhiddenNeg :
      (unitAxisHiddenSubsetGap (unitAxisFreeAtom design)
        (unitAxisHiddenForm design) selected).det < 0 := by
    rw [show selected = ({0, 1, 2} : Finset (Fin 6)).erase
      (baseThreeLabel axis) from rfl,
      unitAxisHiddenSubsetGap_baseErase]
    exact unitAxisHiddenBasePairGap_det_neg_of_tightCoordinate_ne_zero
      design hlineFree hdominates htightNe htight hline axis haxis
  have hdetScale := unitAxisHiddenSubsetGap_det_eq_det_sq_mul
    design hlineFree selected
  have hnormalizerNe : (unitAxisBaseNormalizer design).det ≠ 0 :=
    isUnit_iff_ne_zero.mp (unitAxisBaseNormalizer_det_isUnit design hlineFree)
  have hscalePos : 0 < (unitAxisBaseNormalizer design).det ^ 2 :=
    sq_pos_of_ne_zero hnormalizerNe
  have horiginalNeg : (subsetSum design selected - 1).det < 0 := by
    nlinarith [hdetScale]
  have hselected : selected =
      {baseThreeLabel (axis.succAbove 0), baseThreeLabel (axis.succAbove 1)} := by
    fin_cases axis <;> decide
  rw [hselected] at horiginalNeg
  have hpairShift :
      subsetSum design
          {baseThreeLabel (axis.succAbove 0), baseThreeLabel (axis.succAbove 1)} - 1
        = pairGramShift
          (design.atom (baseThreeLabel (axis.succAbove 0)))
          (design.atom (baseThreeLabel (axis.succAbove 1))) := by
    have hlabelNe : baseThreeLabel (axis.succAbove (0 : Fin 2)) ≠
        baseThreeLabel (axis.succAbove (1 : Fin 2)) :=
      by fin_cases axis <;> decide
    rw [subsetSum]
    rw [Finset.sum_pair hlabelNe]
    simp [pairGramShift]
  rw [hpairShift, pairGramShift_det] at horiginalNeg
  have hpositive := neg_lt_zero.mp horiginalNeg
  simpa only [pairGapExcessOf, gapExcessOf, gapPairingOf,
    leverageOf_eq_dotProduct] using hpositive

/-- On the tight-line branch, at least one of the three ORIGINAL base pairs is
live. This is the coordinate-free form of the base-pair signature observed in
the Wave-B census. -/
theorem exists_isLivePair_baseTriple_of_hasTightLineAt
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
    ∃ firstLabel secondLabel : Fin 6,
      firstLabel ∈ ({0, 1, 2} : Finset (Fin 6))
        ∧ secondLabel ∈ ({0, 1, 2} : Finset (Fin 6))
        ∧ firstLabel ≠ secondLabel
        ∧ IsLivePair design firstLabel secondLabel := by
  have hkernelNe := unitAxisTightVector_ne_zero design hlineFree htightNe
  obtain ⟨axis, haxis⟩ : ∃ axis : Fin 3,
      unitAxisTightVector design tightDir axis ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hkernelNe (funext hall)
  let firstLabel := baseThreeLabel (axis.succAbove 0)
  let secondLabel := baseThreeLabel (axis.succAbove 1)
  have hpairPos : 0 < pairGapExcessOf design firstLabel secondLabel :=
    pairGapExcessOf_baseErase_pos_of_tightCoordinate_ne_zero design hlineFree
      hdominates htightNe htight hline axis haxis
  have hbasePsd : (tripleGapMatrix design 0 1 2).PosSemidef :=
    (dominates_triple_iff_posSemidef_tripleGapMatrix design
      (by decide) (by decide) (by decide)).mp hdominates
  have hbaseDiag : ∀ baseIndex : Fin 3,
      0 ≤ gapExcessOf design (baseThreeLabel baseIndex) := by
    intro baseIndex
    have hdiag := hbasePsd.diag_nonneg (i := baseIndex)
    fin_cases baseIndex <;>
      simpa [baseThreeLabel, tripleGapMatrix,
        gapExcessOf_eq_heavyExcess] using hdiag
  have hfirstNonneg : 0 ≤ gapExcessOf design firstLabel := by
    exact hbaseDiag (axis.succAbove 0)
  have hsecondNonneg : 0 ≤ gapExcessOf design secondLabel := by
    exact hbaseDiag (axis.succAbove 1)
  have hfirstPos : 0 < gapExcessOf design firstLabel := by
    rw [pairGapExcessOf] at hpairPos
    nlinarith [sq_nonneg (gapPairingOf design firstLabel secondLabel)]
  have hsecondPos : 0 < gapExcessOf design secondLabel := by
    rw [pairGapExcessOf] at hpairPos
    nlinarith [sq_nonneg (gapPairingOf design firstLabel secondLabel)]
  refine ⟨firstLabel, secondLabel, ?_, ?_, ?_, hfirstPos, hsecondPos, hpairPos⟩
  · fin_cases axis <;> decide
  · fin_cases axis <;> decide
  · fin_cases axis <;> decide

end Gtz

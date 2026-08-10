import Gtz.Design.LineBranchCandidateCorners

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6000000

namespace Gtz

open Matrix Finset

/-- The one-slot subset represented by its omitted base coordinate and inserted
free coordinate. -/
noncomputable def unitAxisOneSlotSubset (omittedBase freeIndex : Fin 3) : Finset (Fin 6) :=
  insert (freeThreeLabel freeIndex)
    (({0, 1, 2} : Finset (Fin 6)).erase (baseThreeLabel omittedBase))

/-- The distance-two subset represented by its retained base coordinate and
two distinct free coordinates. -/
noncomputable def unitAxisDistanceTwoSubset (retainedBase freeOne freeTwo : Fin 3) :
    Finset (Fin 6) :=
  {baseThreeLabel retainedBase, freeThreeLabel freeOne, freeThreeLabel freeTwo}

theorem unitAxisOneSlotSubset_card (omittedBase freeIndex : Fin 3) :
    (unitAxisOneSlotSubset omittedBase freeIndex).card = 3 := by
  fin_cases omittedBase <;> fin_cases freeIndex <;>
    decide

theorem unitAxisDistanceTwoSubset_card
    (retainedBase : Fin 3) {freeOne freeTwo : Fin 3}
    (hdistinct : freeOne ≠ freeTwo) :
    (unitAxisDistanceTwoSubset retainedBase freeOne freeTwo).card = 3 := by
  fin_cases retainedBase <;> fin_cases freeOne <;> fin_cases freeTwo <;>
    simp_all [unitAxisDistanceTwoSubset, baseThreeLabel, freeThreeLabel]

/-- The normalized subset gap of a one-slot set is the named one-slot matrix. -/
theorem unitAxisHiddenSubsetGap_oneSlot
    (freeAtom : Fin 3 → Fin 3 → ℝ) (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (omittedBase freeIndex : Fin 3) :
    unitAxisHiddenSubsetGap freeAtom hiddenForm
        (unitAxisOneSlotSubset omittedBase freeIndex)
      = unitAxisHiddenOneSlotGap hiddenForm freeAtom omittedBase freeIndex := by
  fin_cases omittedBase <;> fin_cases freeIndex
  all_goals
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [unitAxisHiddenSubsetGap, unitAxisOneSlotSubset,
        unitAxisHiddenOneSlotGap, axisBaseAtom, baseThreeLabel, freeThreeLabel,
        atomMatrix, Matrix.vecMulVec_apply] <;> ring

/-- The normalized subset gap of a distance-two set is the named distance-two
matrix. -/
theorem unitAxisHiddenSubsetGap_distanceTwo
    (freeAtom : Fin 3 → Fin 3 → ℝ) (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (retainedBase : Fin 3) {freeOne freeTwo : Fin 3}
    (hdistinct : freeOne ≠ freeTwo) :
    unitAxisHiddenSubsetGap freeAtom hiddenForm
        (unitAxisDistanceTwoSubset retainedBase freeOne freeTwo)
      = unitAxisHiddenDistanceTwoGap hiddenForm freeAtom retainedBase freeOne freeTwo := by
  fin_cases retainedBase <;> fin_cases freeOne <;> fin_cases freeTwo <;>
    simp at hdistinct
  all_goals
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [unitAxisHiddenSubsetGap, unitAxisDistanceTwoSubset,
        unitAxisHiddenDistanceTwoGap, planeAxisPenaltyExcept, axisBaseAtom,
        baseThreeLabel, freeThreeLabel, atomMatrix] <;> ring

theorem unitAxisHiddenSubsetGap_complement
    (freeAtom : Fin 3 → Fin 3 → ℝ) (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ) :
    unitAxisHiddenSubsetGap freeAtom hiddenForm ({3, 4, 5} : Finset (Fin 6))
      = unitAxisHiddenComplementGap hiddenForm freeAtom := by
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [unitAxisHiddenSubsetGap, unitAxisHiddenComplementGap,
      axisBaseAtom, atomMatrix] <;> ring

/-- The exact normalized 9+9+1 candidate family on the line branch. -/
def UnitAxisHiddenNineteenCandidate (design : WeightedDesign 6 3) : Prop :=
  (∃ omittedBase freeIndex : Fin 3,
      (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) omittedBase freeIndex).PosDef)
    ∨ (∃ retainedBase freeOne freeTwo : Fin 3, freeOne ≠ freeTwo ∧
      (unitAxisHiddenDistanceTwoGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) retainedBase freeOne freeTwo).PosDef)
    ∨ (unitAxisHiddenComplementGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design)).PosDef

/-- Exact candidate reduction for the tight-line branch. The tight base is the
only excluded triple; the remaining nineteen split as 9 one-slot, 9
distance-two, and the complement. -/
theorem exists_posDef_cardThree_iff_unitAxisHiddenNineteenCandidate
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    (∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef)
      ↔ UnitAxisHiddenNineteenCandidate design := by
  classical
  have hbaseNot :
      ¬ (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
    not_posDef_baseTripleGap_of_tightDirection design htightNe htight
  have honeSlot : ∀ omittedBase freeIndex,
      (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
          (unitAxisFreeAtom design) omittedBase freeIndex).PosDef ↔
        (subsetSum design (unitAxisOneSlotSubset omittedBase freeIndex) - 1).PosDef := by
    intro omittedBase freeIndex
    rw [← unitAxisHiddenSubsetGap_oneSlot]
    exact posDef_gap_iff_unitAxisHiddenSubsetGap design hlineFree _
  have hdistanceTwo : ∀ retainedBase freeOne freeTwo, freeOne ≠ freeTwo →
      ((unitAxisHiddenDistanceTwoGap (unitAxisHiddenForm design)
          (unitAxisFreeAtom design) retainedBase freeOne freeTwo).PosDef ↔
        (subsetSum design
          (unitAxisDistanceTwoSubset retainedBase freeOne freeTwo) - 1).PosDef) := by
    intro retainedBase freeOne freeTwo hdistinct
    rw [← unitAxisHiddenSubsetGap_distanceTwo _ _ retainedBase hdistinct]
    exact posDef_gap_iff_unitAxisHiddenSubsetGap design hlineFree _
  have hcomplement :
      (unitAxisHiddenComplementGap (unitAxisHiddenForm design)
          (unitAxisFreeAtom design)).PosDef ↔
        (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
    rw [← unitAxisHiddenSubsetGap_complement]
    exact posDef_gap_iff_unitAxisHiddenSubsetGap design hlineFree _
  constructor
  · rintro ⟨selected, hcard, hpos⟩
    have hpow : selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3 :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    rcases cardThreeFinsetsOfSix_enumeration selected hpow with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hbaseNot hpos)
    · left; refine ⟨2, 0, (honeSlot 2 0).mpr ?_⟩
      simpa only [show unitAxisOneSlotSubset 2 0 = {0, 1, 3} by decide] using hpos
    · left; refine ⟨2, 1, (honeSlot 2 1).mpr ?_⟩
      simpa only [show unitAxisOneSlotSubset 2 1 = {0, 1, 4} by decide] using hpos
    · left; refine ⟨2, 2, (honeSlot 2 2).mpr ?_⟩
      simpa only [show unitAxisOneSlotSubset 2 2 = {0, 1, 5} by decide] using hpos
    · left; refine ⟨1, 0, (honeSlot 1 0).mpr ?_⟩
      simpa only [show unitAxisOneSlotSubset 1 0 = {0, 2, 3} by decide] using hpos
    · left; refine ⟨1, 1, (honeSlot 1 1).mpr ?_⟩
      simpa only [show unitAxisOneSlotSubset 1 1 = {0, 2, 4} by decide] using hpos
    · left; refine ⟨1, 2, (honeSlot 1 2).mpr ?_⟩
      simpa only [show unitAxisOneSlotSubset 1 2 = {0, 2, 5} by decide] using hpos
    · right; left
      exact ⟨0, 0, 1, by decide,
        (hdistanceTwo 0 0 1 (by decide)).mpr
          (by simpa only [show unitAxisDistanceTwoSubset 0 0 1 = {0, 3, 4} by decide] using hpos)⟩
    · right; left
      exact ⟨0, 0, 2, by decide,
        (hdistanceTwo 0 0 2 (by decide)).mpr
          (by simpa only [show unitAxisDistanceTwoSubset 0 0 2 = {0, 3, 5} by decide] using hpos)⟩
    · right; left
      exact ⟨0, 1, 2, by decide,
        (hdistanceTwo 0 1 2 (by decide)).mpr
          (by simpa only [show unitAxisDistanceTwoSubset 0 1 2 = {0, 4, 5} by decide] using hpos)⟩
    · left; refine ⟨0, 0, (honeSlot 0 0).mpr ?_⟩
      simpa only [show unitAxisOneSlotSubset 0 0 = {1, 2, 3} by decide] using hpos
    · left; refine ⟨0, 1, (honeSlot 0 1).mpr ?_⟩
      simpa only [show unitAxisOneSlotSubset 0 1 = {1, 2, 4} by decide] using hpos
    · left; refine ⟨0, 2, (honeSlot 0 2).mpr ?_⟩
      simpa only [show unitAxisOneSlotSubset 0 2 = {1, 2, 5} by decide] using hpos
    · right; left
      exact ⟨1, 0, 1, by decide,
        (hdistanceTwo 1 0 1 (by decide)).mpr
          (by simpa only [show unitAxisDistanceTwoSubset 1 0 1 = {1, 3, 4} by decide] using hpos)⟩
    · right; left
      exact ⟨1, 0, 2, by decide,
        (hdistanceTwo 1 0 2 (by decide)).mpr
          (by simpa only [show unitAxisDistanceTwoSubset 1 0 2 = {1, 3, 5} by decide] using hpos)⟩
    · right; left
      exact ⟨1, 1, 2, by decide,
        (hdistanceTwo 1 1 2 (by decide)).mpr
          (by simpa only [show unitAxisDistanceTwoSubset 1 1 2 = {1, 4, 5} by decide] using hpos)⟩
    · right; left
      exact ⟨2, 0, 1, by decide,
        (hdistanceTwo 2 0 1 (by decide)).mpr
          (by simpa only [show unitAxisDistanceTwoSubset 2 0 1 = {2, 3, 4} by decide] using hpos)⟩
    · right; left
      exact ⟨2, 0, 2, by decide,
        (hdistanceTwo 2 0 2 (by decide)).mpr
          (by simpa only [show unitAxisDistanceTwoSubset 2 0 2 = {2, 3, 5} by decide] using hpos)⟩
    · right; left
      exact ⟨2, 1, 2, by decide,
        (hdistanceTwo 2 1 2 (by decide)).mpr
          (by simpa only [show unitAxisDistanceTwoSubset 2 1 2 = {2, 4, 5} by decide] using hpos)⟩
    · right; right; exact hcomplement.mpr hpos
  · rintro (honeSlotCandidate | hdistanceTwoCandidate | hcomplementCandidate)
    · obtain ⟨omittedBase, freeIndex, hpos⟩ := honeSlotCandidate
      exact ⟨unitAxisOneSlotSubset omittedBase freeIndex,
        unitAxisOneSlotSubset_card omittedBase freeIndex,
        (honeSlot omittedBase freeIndex).mp hpos⟩
    · obtain ⟨retainedBase, freeOne, freeTwo, hdistinct, hpos⟩ :=
        hdistanceTwoCandidate
      exact ⟨unitAxisDistanceTwoSubset retainedBase freeOne freeTwo,
        unitAxisDistanceTwoSubset_card retainedBase hdistinct,
        (hdistanceTwo retainedBase freeOne freeTwo hdistinct).mp hpos⟩
    · exact ⟨{3, 4, 5}, by decide, hcomplement.mp hcomplementCandidate⟩

/-- The tight-line frontier restated entirely in its normalized nineteen
candidate coordinates. -/
def UThreeSixUnitAxisNineteenCandidateBranch : Prop :=
  ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    tightDir ≠ 0 →
    IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir →
    HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir →
    UnitAxisHiddenNineteenCandidate design

/-- No information is lost in the normalized finite line-branch reduction. -/
theorem uThreeSixTightLineBranch_iff_unitAxisNineteenCandidateBranch :
    UThreeSixTightLineBranch ↔ UThreeSixUnitAxisNineteenCandidateBranch := by
  constructor
  · intro hline design tightDir hlineFree hoffConic hdominates htightNe htight hkernel
    apply (exists_posDef_cardThree_iff_unitAxisHiddenNineteenCandidate
      design tightDir hlineFree htightNe htight).mp
    exact hline design tightDir hlineFree hoffConic hdominates htightNe htight hkernel
  · intro hnormalized design tightDir hlineFree hoffConic hdominates htightNe htight hkernel
    apply (exists_posDef_cardThree_iff_unitAxisHiddenNineteenCandidate
      design tightDir hlineFree htightNe htight).mpr
    exact hnormalized design tightDir hlineFree hoffConic hdominates htightNe htight hkernel

end Gtz

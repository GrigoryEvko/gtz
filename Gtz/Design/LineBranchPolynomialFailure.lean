import Gtz.Design.LineBranchCandidateReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6000000

namespace Gtz

open Matrix

/-- A coordinate different from the omitted axis, used as the free positive
corner of a one-slot candidate. -/
def unitAxisOneSlotFront (omittedBase : Fin 3) : Fin 3 :=
  if omittedBase = 0 then 1 else 0

def unitAxisOneSlotOrder (omittedBase : Fin 3) : Fin 3 ≃ Fin 3 :=
  Equiv.swap 0 (unitAxisOneSlotFront omittedBase)

@[simp] theorem unitAxisOneSlotOrder_zero (omittedBase : Fin 3) :
    unitAxisOneSlotOrder omittedBase 0 = unitAxisOneSlotFront omittedBase := by
  simp [unitAxisOneSlotOrder]

theorem unitAxisOneSlotFront_ne (omittedBase : Fin 3) :
    unitAxisOneSlotFront omittedBase ≠ omittedBase := by
  fin_cases omittedBase <;> decide

noncomputable def unitAxisHiddenOneSlotBlockMinor (design : WeightedDesign 6 3)
    (omittedBase freeIndex : Fin 3) : ℝ :=
  let gap := unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
    (unitAxisFreeAtom design) omittedBase freeIndex
  let order := unitAxisOneSlotOrder omittedBase
  gap (order 0) (order 0) * gap (order 1) (order 1)
    - gap (order 0) (order 1) ^ 2

noncomputable def unitAxisHiddenOneSlotDetCriterion (design : WeightedDesign 6 3)
    (omittedBase freeIndex : Fin 3) : ℝ :=
  let gap := unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
    (unitAxisFreeAtom design) omittedBase freeIndex
  let order := unitAxisOneSlotOrder omittedBase
  gap (order 0) (order 0) * gap (order 1) (order 1) * gap (order 2) (order 2)
    - gap (order 0) (order 0) * gap (order 1) (order 2) ^ 2
    - gap (order 0) (order 1) ^ 2 * gap (order 2) (order 2)
    + 2 * gap (order 0) (order 1) * gap (order 0) (order 2)
        * gap (order 1) (order 2)
    - gap (order 0) (order 2) ^ 2 * gap (order 1) (order 1)

theorem unitAxisHiddenOneSlotGap_posDef_iff_two_signs
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hhidden : (unitAxisHiddenForm design).PosSemidef)
    (omittedBase freeIndex : Fin 3) :
    (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) omittedBase freeIndex).PosDef ↔
      0 < unitAxisHiddenOneSlotBlockMinor design omittedBase freeIndex
        ∧ 0 < unitAxisHiddenOneSlotDetCriterion design omittedBase freeIndex := by
  simpa only [unitAxisHiddenOneSlotBlockMinor,
    unitAxisHiddenOneSlotDetCriterion] using
      (unitAxisHiddenOneSlotGap_posDef_iff_two_reindexedMinors
        design hlineFree hhidden omittedBase freeIndex
          (unitAxisOneSlotOrder omittedBase)
          (by simpa using unitAxisOneSlotFront_ne omittedBase))

noncomputable def unitAxisHiddenDistanceTwoBlockMinor (design : WeightedDesign 6 3)
    (retainedBase freeOne freeTwo : Fin 3) : ℝ :=
  let gap := unitAxisHiddenDistanceTwoGap (unitAxisHiddenForm design)
    (unitAxisFreeAtom design) retainedBase freeOne freeTwo
  let order := planeAxisFrontEquiv retainedBase
  gap (order 0) (order 0) * gap (order 1) (order 1)
    - gap (order 0) (order 1) ^ 2

noncomputable def unitAxisHiddenDistanceTwoDetCriterion (design : WeightedDesign 6 3)
    (retainedBase freeOne freeTwo : Fin 3) : ℝ :=
  let gap := unitAxisHiddenDistanceTwoGap (unitAxisHiddenForm design)
    (unitAxisFreeAtom design) retainedBase freeOne freeTwo
  let order := planeAxisFrontEquiv retainedBase
  gap (order 0) (order 0) * gap (order 1) (order 1) * gap (order 2) (order 2)
    - gap (order 0) (order 0) * gap (order 1) (order 2) ^ 2
    - gap (order 0) (order 1) ^ 2 * gap (order 2) (order 2)
    + 2 * gap (order 0) (order 1) * gap (order 0) (order 2)
        * gap (order 1) (order 2)
    - gap (order 0) (order 2) ^ 2 * gap (order 1) (order 1)

theorem unitAxisHiddenDistanceTwoGap_posDef_iff_two_signs
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hhidden : (unitAxisHiddenForm design).PosSemidef)
    (retainedBase freeOne freeTwo : Fin 3) :
    (unitAxisHiddenDistanceTwoGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) retainedBase freeOne freeTwo).PosDef ↔
      0 < unitAxisHiddenDistanceTwoBlockMinor design retainedBase freeOne freeTwo
        ∧ 0 < unitAxisHiddenDistanceTwoDetCriterion design retainedBase freeOne freeTwo := by
  simpa only [unitAxisHiddenDistanceTwoBlockMinor,
    unitAxisHiddenDistanceTwoDetCriterion] using
      (unitAxisHiddenDistanceTwoGap_posDef_iff_two_reindexedMinors
        design hlineFree hhidden retainedBase freeOne freeTwo
          (planeAxisFrontEquiv retainedBase) (planeAxisFrontEquiv_zero retainedBase))

theorem unitAxisHiddenComplementGap_transpose
    (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ) (htranspose : hiddenFormᵀ = hiddenForm)
    (freeAtom : Fin 3 → Fin 3 → ℝ) :
    (unitAxisHiddenComplementGap hiddenForm freeAtom)ᵀ
      = unitAxisHiddenComplementGap hiddenForm freeAtom := by
  unfold unitAxisHiddenComplementGap atomMatrix
  rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_add,
    Matrix.transpose_add, htranspose, Matrix.transpose_vecMulVec,
    Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec, transpose_one]

noncomputable def unitAxisHiddenComplementCorner (design : WeightedDesign 6 3) : ℝ :=
  unitAxisHiddenComplementGap (unitAxisHiddenForm design)
    (unitAxisFreeAtom design) 0 0

noncomputable def unitAxisHiddenComplementBlockMinor (design : WeightedDesign 6 3) : ℝ :=
  let gap := unitAxisHiddenComplementGap (unitAxisHiddenForm design)
    (unitAxisFreeAtom design)
  gap 0 0 * gap 1 1 - gap 0 1 ^ 2

noncomputable def unitAxisHiddenComplementDetCriterion (design : WeightedDesign 6 3) : ℝ :=
  (unitAxisHiddenComplementGap (unitAxisHiddenForm design)
    (unitAxisFreeAtom design)).det

theorem unitAxisHiddenComplementGap_posDef_iff_three_signs
    (design : WeightedDesign 6 3) :
    (unitAxisHiddenComplementGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design)).PosDef ↔
      0 < unitAxisHiddenComplementCorner design
        ∧ 0 < unitAxisHiddenComplementBlockMinor design
        ∧ 0 < unitAxisHiddenComplementDetCriterion design := by
  let gap := unitAxisHiddenComplementGap (unitAxisHiddenForm design)
    (unitAxisFreeAtom design)
  have hsym : gapᵀ = gap := unitAxisHiddenComplementGap_transpose _
    (unitAxisHiddenForm_transpose design) _
  have hdet : gap 0 0 * gap 1 1 * gap 2 2 - gap 0 0 * gap 1 2 ^ 2
          - gap 0 1 ^ 2 * gap 2 2 + 2 * gap 0 1 * gap 0 2 * gap 1 2
          - gap 0 2 ^ 2 * gap 1 1 = gap.det := by
    have hlower : ∀ row col : Fin 3, gap col row = gap row col := by
      intro row col
      have hentry := congrFun (congrFun hsym row) col
      simpa only [Matrix.transpose_apply] using hentry
    rw [Matrix.det_fin_three, hlower 0 1, hlower 0 2, hlower 1 2]
    ring
  simpa only [Equiv.refl_apply, unitAxisHiddenComplementCorner,
    unitAxisHiddenComplementBlockMinor, unitAxisHiddenComplementDetCriterion,
    gap, hdet] using
      (posDef_finThree_iff_reindexedLeadingMinors gap hsym (Equiv.refl (Fin 3)))

/-- The 39 scalar refusals left by failure of all nineteen line-branch
candidates: two signs for each of 9 one-slot and 9 unordered distance-two
gaps, and three signs for the complement. The distance-two quantifier is
written over distinct ordered labels; swapping them repeats the same gap. -/
def UnitAxisHiddenPolynomialFailure (design : WeightedDesign 6 3) : Prop :=
  (∀ omittedBase freeIndex : Fin 3,
      unitAxisHiddenOneSlotBlockMinor design omittedBase freeIndex ≤ 0
        ∨ unitAxisHiddenOneSlotDetCriterion design omittedBase freeIndex ≤ 0)
    ∧ (∀ retainedBase freeOne freeTwo : Fin 3, freeOne ≠ freeTwo →
      unitAxisHiddenDistanceTwoBlockMinor design retainedBase freeOne freeTwo ≤ 0
        ∨ unitAxisHiddenDistanceTwoDetCriterion design retainedBase freeOne freeTwo ≤ 0)
    ∧ (unitAxisHiddenComplementCorner design ≤ 0
      ∨ unitAxisHiddenComplementBlockMinor design ≤ 0
      ∨ unitAxisHiddenComplementDetCriterion design ≤ 0)

/-- Failure of the normalized nineteen candidates is exactly the finite
polynomial sign obstruction. -/
theorem not_unitAxisHiddenNineteenCandidate_iff_polynomialFailure
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hhidden : (unitAxisHiddenForm design).PosSemidef) :
    ¬ UnitAxisHiddenNineteenCandidate design ↔
      UnitAxisHiddenPolynomialFailure design := by
  constructor
  · intro hfailure
    refine ⟨?_, ?_, ?_⟩
    · intro omittedBase freeIndex
      by_cases hblock : unitAxisHiddenOneSlotBlockMinor design
          omittedBase freeIndex ≤ 0
      · exact Or.inl hblock
      · right
        by_contra hdet
        apply hfailure
        left
        refine ⟨omittedBase, freeIndex, ?_⟩
        exact (unitAxisHiddenOneSlotGap_posDef_iff_two_signs
          design hlineFree hhidden omittedBase freeIndex).mpr
            ⟨lt_of_not_ge hblock, lt_of_not_ge hdet⟩
    · intro retainedBase freeOne freeTwo hdistinct
      by_cases hblock : unitAxisHiddenDistanceTwoBlockMinor design
          retainedBase freeOne freeTwo ≤ 0
      · exact Or.inl hblock
      · right
        by_contra hdet
        apply hfailure
        right; left
        refine ⟨retainedBase, freeOne, freeTwo, hdistinct, ?_⟩
        exact (unitAxisHiddenDistanceTwoGap_posDef_iff_two_signs
          design hlineFree hhidden retainedBase freeOne freeTwo).mpr
            ⟨lt_of_not_ge hblock, lt_of_not_ge hdet⟩
    · by_cases hcorner : unitAxisHiddenComplementCorner design ≤ 0
      · exact Or.inl hcorner
      · right
        by_cases hblock : unitAxisHiddenComplementBlockMinor design ≤ 0
        · exact Or.inl hblock
        · right
          by_contra hdet
          apply hfailure
          right; right
          exact (unitAxisHiddenComplementGap_posDef_iff_three_signs design).mpr
            ⟨lt_of_not_ge hcorner, lt_of_not_ge hblock, lt_of_not_ge hdet⟩
  · rintro ⟨honeSlotFailure, hdistanceTwoFailure, hcomplementFailure⟩
    rintro (honeSlot | hdistanceTwo | hcomplement)
    · obtain ⟨omittedBase, freeIndex, hpos⟩ := honeSlot
      obtain ⟨hblock, hdet⟩ :=
        (unitAxisHiddenOneSlotGap_posDef_iff_two_signs
          design hlineFree hhidden omittedBase freeIndex).mp hpos
      rcases honeSlotFailure omittedBase freeIndex with hblockFailure | hdetFailure
      · linarith
      · linarith
    · obtain ⟨retainedBase, freeOne, freeTwo, hdistinct, hpos⟩ := hdistanceTwo
      obtain ⟨hblock, hdet⟩ :=
        (unitAxisHiddenDistanceTwoGap_posDef_iff_two_signs
          design hlineFree hhidden retainedBase freeOne freeTwo).mp hpos
      rcases hdistanceTwoFailure retainedBase freeOne freeTwo hdistinct with
        hblockFailure | hdetFailure
      · linarith
      · linarith
    · obtain ⟨hcorner, hblock, hdet⟩ :=
        (unitAxisHiddenComplementGap_posDef_iff_three_signs design).mp hcomplement
      rcases hcomplementFailure with hcornerFailure | hblockFailure | hdetFailure
      · linarith
      · linarith
      · linarith

/-- The original tight-line failure, with the normal form and all scalar
refusals packaged in one theorem-ready witness. -/
def UnitAxisLineFailureWitness (design : WeightedDesign 6 3)
    (tightDir : Fin 3 → ℝ) : Prop :=
  unitAxisHiddenForm design
        + design.weight 3 • atomMatrix (unitAxisFreeAtom design 0)
        + design.weight 4 • atomMatrix (unitAxisFreeAtom design 1)
        + design.weight 5 • atomMatrix (unitAxisFreeAtom design 2)
      = Matrix.diagonal (fun coordinate =>
          1 - design.weight (baseThreeLabel coordinate))
    ∧ Matrix.trace (unitAxisHiddenForm design)
        + design.weight 3 *
            ((unitAxisFreeAtom design 0 ⬝ᵥ unitAxisFreeAtom design 0) - 1)
        + design.weight 4 *
            ((unitAxisFreeAtom design 1 ⬝ᵥ unitAxisFreeAtom design 1) - 1)
        + design.weight 5 *
            ((unitAxisFreeAtom design 2 ⬝ᵥ unitAxisFreeAtom design 2) - 1)
      = 2
    ∧ (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design
        = 1 - unitAxisHiddenForm design
    ∧ (unitAxisHiddenForm design).PosSemidef
    ∧ unitAxisTightVector design tightDir ≠ 0
    ∧ unitAxisHiddenForm design *ᵥ unitAxisTightVector design tightDir = 0
    ∧ (∀ other : Fin 3 → ℝ,
        unitAxisHiddenForm design *ᵥ other = 0 ↔
          ∃ ratio : ℝ, other = ratio • unitAxisTightVector design tightDir)
    ∧ (freeOffDiagonalGrid (unitAxisFreeAtom design)).det ≠ 0
    ∧ (unitAxisFreeFrame design).det ≠ 0
    ∧ UnitAxisHiddenPolynomialFailure design

theorem not_exists_posDef_cardThree_iff_unitAxisLineFailureWitness
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    ¬ (∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) ↔
      UnitAxisLineFailureWitness design tightDir := by
  have hhidden := unitAxisHiddenForm_posSemidef design hlineFree hdominates
  have hcandidates := exists_posDef_cardThree_iff_unitAxisHiddenNineteenCandidate
    design tightDir hlineFree htightNe htight
  have hfailure := not_unitAxisHiddenNineteenCandidate_iff_polynomialFailure
    design hlineFree hhidden
  constructor
  · intro hnone
    have hpoly : UnitAxisHiddenPolynomialFailure design :=
      hfailure.mp (fun hcandidatesExist => hnone (hcandidates.mpr hcandidatesExist))
    obtain ⟨hframe, hmetric, hpsd, htightVector, hkernel, hkernelSpan,
      hoffDiagonal, hfreeFrame, _htransport⟩ :=
        tightLine_unitAxisNormalForm design tightDir hlineFree hoffConic hdominates
          htightNe htight hline
    exact ⟨hframe, unitAxisHiddenForm_trace_normalization design hlineFree,
      hmetric, hpsd, htightVector, hkernel, hkernelSpan,
      hoffDiagonal, hfreeFrame, hpoly⟩
  · rintro ⟨_hframe, _htrace, _hmetric, hpsd, _htightVector, _hkernel,
      _hkernelSpan, _hoffDiagonal, _hfreeFrame, hpoly⟩
    intro hexists
    exact (hfailure.mpr hpoly) (hcandidates.mp hexists)

end Gtz

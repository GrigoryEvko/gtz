import Gtz.Design.FreePairPlane
import Gtz.Wave.TenthHeavyLineResidualWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-!
# The one-line joint blind spot has ten possible winners

The line-normal blind spot already excludes every strict triple containing
two atoms of the distinguished line `{0,1,2}`.  This leaves exactly ten of the
twenty triples: the free triple and the nine triples containing one line atom
and two free atoms.  They are exactly the existing
`Gtz.PlaneBranchTenCandidate` selector from the line-free U(3,6) plane branch.

This module packages that finite endpoint and wires it into the tenth-heavy
residual.  The resulting proposition is equivalent to
`Gtz.PatternHeavyWeakToStrict`; it is a smaller formula, not an additional
assumption.
-/

/-- The finite matroid calculation behind the one-line localization.  A
card-three subset outside the ten line-sparse candidates contains two
distinct labels from `{0,1,2}`. -/
theorem finSix_cardThree_nonLineSparse_contains_linePair :
    ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (selected = {0, 3, 4} ∨ selected = {0, 3, 5} ∨
        selected = {0, 4, 5} ∨
        selected = {1, 3, 4} ∨ selected = {1, 3, 5} ∨
        selected = {1, 4, 5} ∨ selected = {2, 3, 4} ∨
        selected = {2, 3, 5} ∨ selected = {2, 4, 5} ∨
        selected = {3, 4, 5}) →
      ∃ pairFirst pairSecond thirdLabel : Fin 6,
        pairFirst ≠ pairSecond ∧ pairFirst ≠ thirdLabel ∧ pairSecond ≠ thirdLabel ∧
        pairFirst ∈ ({0, 1, 2} : Finset (Fin 6)) ∧
        pairSecond ∈ ({0, 1, 2} : Finset (Fin 6)) ∧
        selected = {pairFirst, pairSecond, thirdLabel} := by
  decide

/-- In the one-line normal blind spot, every strict triple is one of the ten
line-sparse candidates.  The proof uses the actual unit line normal supplied
by the pattern and the unguarded flat-pair lift equivalence. -/
theorem oneLine_strictTriple_eq_lineSparse_of_normalBlind
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (hblind : IsOneLineNormalBlindSpot design)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    selected = {0, 3, 4} ∨ selected = {0, 3, 5} ∨
      selected = {0, 4, 5} ∨
      selected = {1, 3, 4} ∨ selected = {1, 3, 5} ∨
      selected = {1, 4, 5} ∨ selected = {2, 3, 4} ∨
      selected = {2, 3, 5} ∨ selected = {2, 4, 5} ∨
      selected = {3, 4, 5} := by
  obtain ⟨normalVec, hunit, horthogonal⟩ :=
    oneLine_exists_unitLineNormal design hpattern
  by_contra hnonSparse
  obtain ⟨pairFirst, pairSecond, thirdLabel, hFirstSecond, hFirstThird,
      hSecondThird, hFirstMem, hSecondMem, hselected⟩ :=
    finSix_cardThree_nonLineSparse_contains_linePair selected hcard hnonSparse
  have hpairPosDef :
      (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef := by
    rwa [← hselected]
  have hfires := (posDef_tripleGap_iff_flatPairFires design hunit pairFirst pairSecond
    thirdLabel hFirstSecond hFirstThird hSecondThird
    (by simpa [normalReading] using horthogonal pairFirst hFirstMem)
    (by simpa [normalReading] using horthogonal pairSecond hSecondMem)).mp hpairPosDef
  have hmargin := (posDef_tripleGap_iff_pos_liftMargin design hunit pairFirst pairSecond
    thirdLabel hFirstSecond hFirstThird hSecondThird hfires.1 hfires.2.1).mp hpairPosDef
  exact hblind normalVec hunit horthogonal pairFirst pairSecond thirdLabel hFirstSecond
    hFirstThird hSecondThird ⟨hfires.1, hfires.2.1, hmargin⟩

/-- The existing plane-branch selector has an unconditional introduction
rule: its ten disjuncts directly package a strict card-three witness. -/
theorem exists_posDef_cardThree_of_planeBranchTenCandidate
    (design : WeightedDesign 6 3) (hcandidates : PlaneBranchTenCandidate design) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - 1).PosDef := by
  rcases hcandidates with h034 | h035 | h045 | h134 | h135 | h145 | h234 | h235 | h245 | h345
  · exact ⟨{0, 3, 4}, by decide, h034⟩
  · exact ⟨{0, 3, 5}, by decide, h035⟩
  · exact ⟨{0, 4, 5}, by decide, h045⟩
  · exact ⟨{1, 3, 4}, by decide, h134⟩
  · exact ⟨{1, 3, 5}, by decide, h135⟩
  · exact ⟨{1, 4, 5}, by decide, h145⟩
  · exact ⟨{2, 3, 4}, by decide, h234⟩
  · exact ⟨{2, 3, 5}, by decide, h235⟩
  · exact ⟨{2, 4, 5}, by decide, h245⟩
  · exact ⟨{3, 4, 5}, by decide, h345⟩

/-- A strict triple in the one-line normal blind spot produces exactly the
same ten-candidate selector used by the line-free plane branch. -/
theorem planeBranchTenCandidate_of_oneLine_strictTriple_of_normalBlind
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (hblind : IsOneLineNormalBlindSpot design)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    PlaneBranchTenCandidate design := by
  have hshape := oneLine_strictTriple_eq_lineSparse_of_normalBlind design hpattern
    hblind selected hcard hposDef
  rcases hshape with h034 | h035 | h045 | h134 | h135 | h145 | h234 | h235 | h245 | h345
  · exact Or.inl (by simpa only [h034] using hposDef)
  · exact Or.inr (Or.inl (by simpa only [h035] using hposDef))
  · exact Or.inr (Or.inr (Or.inl (by simpa only [h045] using hposDef)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [h134] using hposDef))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [h135] using hposDef)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (by simpa only [h145] using hposDef))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (by simpa only [h234] using hposDef)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (by simpa only [h235] using hposDef))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (by simpa only [h245] using hposDef)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (by simpa only [h345] using hposDef)))))))))

/-- The exact one-line residual after the tenth-light theorem, pair-cap
engine, line-normal lift criterion, and line-pair localization have all fired.
Only the ten line-sparse triples remain as possible strict witnesses. -/
def OneLineTenthHeavyJointBlindLineSparse : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
    (∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel) →
    IsCapBlindSpot design →
    IsOneLineNormalBlindSpot design →
    (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
    PlaneBranchTenCandidate design

/-- A line-sparse witness is, in particular, an arbitrary strict card-three
witness, so the ten-candidate residual reconstructs the preceding joint-blind
residual. -/
theorem tenthHeavyJointBlind_oneLine_of_lineSparse
    (hresidual : OneLineTenthHeavyJointBlindLineSparse) :
    OneLineTenthHeavyJointBlindWeakToStrict := by
  intro design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak
  exact exists_posDef_cardThree_of_planeBranchTenCandidate design
    (hresidual design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak)

/-- Conversely, an arbitrary strict witness produced in the joint blind spot
is forced into the ten-candidate list. -/
theorem lineSparse_oneLine_of_tenthHeavyJointBlind
    (hresidual : OneLineTenthHeavyJointBlindWeakToStrict) :
    OneLineTenthHeavyJointBlindLineSparse := by
  intro design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak
  obtain ⟨selected, hcard, hposDef⟩ :=
    hresidual design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak
  exact planeBranchTenCandidate_of_oneLine_strictTriple_of_normalBlind design hpattern
    hlineBlind selected hcard hposDef

/-- The ten-candidate residual and the prior joint-blind residual are
equivalent. -/
theorem oneLineTenthHeavyJointBlindLineSparse_iff_jointBlind :
    OneLineTenthHeavyJointBlindLineSparse ↔
      OneLineTenthHeavyJointBlindWeakToStrict :=
  ⟨tenthHeavyJointBlind_oneLine_of_lineSparse,
    lineSparse_oneLine_of_tenthHeavyJointBlind⟩

/-- The ten-candidate statement reconstructs the public one-line
weak-to-strict obligation. -/
theorem patternHeavyWeakToStrict_oneLine_of_tenthHeavyJointBlindLineSparse
    (hresidual : OneLineTenthHeavyJointBlindLineSparse) :
    PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  patternHeavyWeakToStrict_oneLine_of_tenthHeavyJointBlind
    (tenthHeavyJointBlind_oneLine_of_lineSparse hresidual)

/-- Any proof of the public one-line obligation restricts to the exact
ten-candidate residual. -/
theorem tenthHeavyJointBlindLineSparse_oneLine_of_patternHeavyWeakToStrict
    (hupgrade :
      PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    OneLineTenthHeavyJointBlindLineSparse :=
  lineSparse_oneLine_of_tenthHeavyJointBlind
    (tenthHeavyJointBlind_oneLine_of_patternHeavyWeakToStrict hupgrade)

/-- The final one-line registry formula is equivalent to its former public
statement. -/
theorem oneLineTenthHeavyJointBlindLineSparse_iff :
    OneLineTenthHeavyJointBlindLineSparse ↔
      PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  ⟨patternHeavyWeakToStrict_oneLine_of_tenthHeavyJointBlindLineSparse,
    tenthHeavyJointBlindLineSparse_oneLine_of_patternHeavyWeakToStrict⟩

end Gtz

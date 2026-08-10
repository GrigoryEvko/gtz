import Gtz.Design.OneLineLiftCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-!
# Two meeting lines: the two-normal residual has only four candidates

At a normal flat on a three-point line, a nonpositive shadow-gap determinant
for every pair on the line excludes every strict triple containing two labels
from that line.  Applying this once to `{0,1,2}` and once to `{0,3,4}` leaves
only the four transversals `{1,3,5}`, `{1,4,5}`, `{2,3,5}`, `{2,4,5}`.

The headline `Gtz.twoMeetingLines_heavyWeakToStrict_of_transversalResidual`
concludes `Gtz.PatternHeavyWeakToStrict` at the two-meeting-lines pattern,
which is character for character
`Skeleton.obligationHeavyWeakToStrictTwoMeetingLines`.

**THE JOINT BLIND SPOT IS NONEMPTY, SO THE RESIDUAL IS GENUINE.**  An earlier
draft of this docstring called emptiness of the joint blind spot "a cheap
first-class target" on the grounds that emptiness would make the residual
vacuous.  Emptiness is refuted on two independent grounds.

FIRST, emptiness is STRICTLY STRONGER than the obligation it would discharge.
Emptiness says every antecedent design fails one of the two blind conditions,
which by the flat-pair equivalence says every antecedent design carries a
strictly dominating NON-transversal.  That already implies the hypothesis of
`Gtz.twoMeetingLines_heavyWeakToStrict_of_capBlindSpot` and discharges the
obligation by itself, without this module.  So emptiness is not a shortcut to
the obligation; it is a harder statement than the obligation.

SECOND, emptiness is false.  A census over designs realizing this pattern
EXACTLY -- dependent triples precisely `{0,1,2}` and `{0,3,4}`, all eighteen
other brackets bounded away from zero -- found antecedent designs (heavy,
cap-blind, carrying a weak dominator) whose strictly dominating triples are
entirely transversals, at a rate near 0.4% of antecedent designs.  Such a
design is jointly blind and satisfies the obligation, which is exactly the
configuration emptiness forbids and the obligation permits.

A structural fact from the same census, worth recording because it is easy to
assume otherwise: the two planes are NEVER perpendicular on this stratum.  If
they were, an orthonormal frame puts both normals on coordinate axes, the
Parseval `(y,z)` entry reads `w5 * q * r = 0`, and the free atom is forced onto
one of the two planes -- creating a third dependent triple and contradicting
the IFF in `Gtz.HasLinePattern`.  Any parametrization that fixes both normals
to be orthogonal is searching an EMPTY set.

What remains untested is whether the four-candidate residual is provable, not
whether it is vacuous.  It is not vacuous.
-/

/-- The finite matroid calculation behind the two-normal localization: among
the twenty three-subsets of six labels, the sixteen non-transversals contain a
pair from one of the two lines.  Decided in the kernel, so it stays inside the
allowed axiom triple. -/
theorem finSix_cardThree_nontransversal_contains_meetingLinePair :
    ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (selected = {1, 3, 5} ∨ selected = {1, 4, 5} ∨
        selected = {2, 3, 5} ∨ selected = {2, 4, 5}) →
      (∃ pairFirst pairSecond thirdLabel : Fin 6,
          pairFirst ≠ pairSecond ∧ pairFirst ≠ thirdLabel ∧ pairSecond ≠ thirdLabel ∧
          pairFirst ∈ ({0, 1, 2} : Finset (Fin 6)) ∧
          pairSecond ∈ ({0, 1, 2} : Finset (Fin 6)) ∧
          selected = {pairFirst, pairSecond, thirdLabel}) ∨
        ∃ pairFirst pairSecond thirdLabel : Fin 6,
          pairFirst ≠ pairSecond ∧ pairFirst ≠ thirdLabel ∧ pairSecond ≠ thirdLabel ∧
          pairFirst ∈ ({0, 3, 4} : Finset (Fin 6)) ∧
          pairSecond ∈ ({0, 3, 4} : Finset (Fin 6)) ∧
          selected = {pairFirst, pairSecond, thirdLabel} := by
  decide

/-- The lift criterion is blind along the pairs of `lineTriple` at one fixed
unit normal.  This is deliberately weaker than `IsOneLineNormalBlindSpot`: it
only quantifies over pairs from the line, because those are exactly the pairs
needed for the transversal localization. -/
def IsLinePairLiftBlindAt (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (lineTriple : Finset (Fin 6)) : Prop :=
  ∀ pairFirst ∈ lineTriple, ∀ pairSecond ∈ lineTriple, ∀ thirdLabel : Fin 6,
    pairFirst ≠ pairSecond → pairFirst ≠ thirdLabel → pairSecond ≠ thirdLabel →
      ¬ (0 < shadowPairing design normalVec pairFirst pairFirst - 1 ∧
        0 < shadowGapDeterminant design normalVec pairFirst pairSecond ∧
        liftLeverage design normalVec pairFirst pairSecond thirdLabel <
          normalReading design normalVec thirdLabel ^ 2 *
            shadowGapDeterminant design normalVec pairFirst pairSecond)

/-- The four possible winners after both meeting-line pair families are
excluded by their own normals. -/
def TwoMeetingLinesTransversalStrict (design : WeightedDesign 6 3) : Prop :=
  (subsetSum design ({1, 3, 5} : Finset (Fin 6)) - 1).PosDef ∨
    (subsetSum design ({1, 4, 5} : Finset (Fin 6)) - 1).PosDef ∨
    (subsetSum design ({2, 3, 5} : Finset (Fin 6)) - 1).PosDef ∨
    (subsetSum design ({2, 4, 5} : Finset (Fin 6)) - 1).PosDef

/-- If all pairs on both meeting lines have nonpositive shadow-gap determinant
at their respective normals, every strictly dominating triple is one of the
four transversals through the open label `5`. -/
theorem twoMeetingLines_strictTriple_eq_transversal_of_bothLinePairBlind
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hfirstPairDead : ∀ lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)),
      ∀ lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)),
        shadowGapDeterminant design normalFirst lineFirst lineSecond ≤ 0)
    (hsecondPairDead : ∀ lineFirst ∈ ({0, 3, 4} : Finset (Fin 6)),
      ∀ lineSecond ∈ ({0, 3, 4} : Finset (Fin 6)),
        shadowGapDeterminant design normalSecond lineFirst lineSecond ≤ 0)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    selected = {1, 3, 5} ∨ selected = {1, 4, 5} ∨
      selected = {2, 3, 5} ∨ selected = {2, 4, 5} := by
  by_contra hnontransversal
  obtain hfirst | hsecond :=
    finSix_cardThree_nontransversal_contains_meetingLinePair selected hcard
      hnontransversal
  · obtain ⟨pairFirst, pairSecond, thirdLabel, hFirstSecond, hFirstThird, hSecondThird,
      hFirstMem, hSecondMem, hselected⟩ := hfirst
    apply (not_posDef_tripleGap_of_flatPair_of_shadowGapDeterminant_nonpos design normalFirst
      pairFirst pairSecond thirdLabel hFirstSecond hFirstThird hSecondThird
      (by simpa [normalReading] using horthFirst pairFirst hFirstMem)
      (by simpa [normalReading] using horthFirst pairSecond hSecondMem)
      (hfirstPairDead pairFirst hFirstMem pairSecond hSecondMem))
    rwa [← hselected]
  · obtain ⟨pairFirst, pairSecond, thirdLabel, hFirstSecond, hFirstThird, hSecondThird,
      hFirstMem, hSecondMem, hselected⟩ := hsecond
    apply (not_posDef_tripleGap_of_flatPair_of_shadowGapDeterminant_nonpos design normalSecond
      pairFirst pairSecond thirdLabel hFirstSecond hFirstThird hSecondThird
      (by simpa [normalReading] using horthSecond pairFirst hFirstMem)
      (by simpa [normalReading] using horthSecond pairSecond hSecondMem)
      (hsecondPairDead pairFirst hFirstMem pairSecond hSecondMem))
    rwa [← hselected]

/-- The exact localization under the criterion's genuine blind spot.  A strict
triple containing two atoms of either line would fire the lift criterion at
that line's unit normal, by the unguarded flat-pair equivalence. -/
theorem twoMeetingLines_strictTriple_eq_transversal_of_bothLineNormalBlind
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4})
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    selected = {1, 3, 5} ∨ selected = {1, 4, 5} ∨
      selected = {2, 3, 5} ∨ selected = {2, 4, 5} := by
  by_contra hnontransversal
  obtain hfirst | hsecond :=
    finSix_cardThree_nontransversal_contains_meetingLinePair selected hcard
      hnontransversal
  · obtain ⟨pairFirst, pairSecond, thirdLabel, hFirstSecond, hFirstThird, hSecondThird,
      hFirstMem, hSecondMem, hselected⟩ := hfirst
    have hfires := (posDef_tripleGap_iff_flatPairFires design hunitFirst pairFirst pairSecond
      thirdLabel hFirstSecond hFirstThird hSecondThird
      (by simpa [normalReading] using horthFirst pairFirst hFirstMem)
      (by simpa [normalReading] using horthFirst pairSecond hSecondMem)).mp (by
        rwa [← hselected])
    exact hblindFirst pairFirst hFirstMem pairSecond hSecondMem thirdLabel hFirstSecond
      hFirstThird hSecondThird hfires
  · obtain ⟨pairFirst, pairSecond, thirdLabel, hFirstSecond, hFirstThird, hSecondThird,
      hFirstMem, hSecondMem, hselected⟩ := hsecond
    have hfires := (posDef_tripleGap_iff_flatPairFires design hunitSecond pairFirst pairSecond
      thirdLabel hFirstSecond hFirstThird hSecondThird
      (by simpa [normalReading] using horthSecond pairFirst hFirstMem)
      (by simpa [normalReading] using horthSecond pairSecond hSecondMem)).mp (by
        rwa [← hselected])
    exact hblindSecond pairFirst hFirstMem pairSecond hSecondMem thirdLabel hFirstSecond
      hFirstThird hSecondThird hfires

/-- **Four-candidate reduction of the two-meeting-lines Skeleton obligation.**
Outside either line-pair blind spot the lift criterion itself supplies a strict
triple.  In the joint blind spot, it is enough to prove one of the four mixed
transversals. -/
theorem twoMeetingLines_heavyWeakToStrict_of_transversalResidual
    (hresidual : ∀ design : WeightedDesign 6 3,
      HasLinePattern design
        (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∀ normalFirst normalSecond : Fin 3 → ℝ,
        normalFirst ⬝ᵥ normalFirst = 1 → normalSecond ⬝ᵥ normalSecond = 1 →
        (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
          design.atom lineLabel ⬝ᵥ normalFirst = 0) →
        (∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
          design.atom lineLabel ⬝ᵥ normalSecond = 0) →
        IsLinePairLiftBlindAt design normalFirst {0, 1, 2} →
        IsLinePairLiftBlindAt design normalSecond {0, 3, 4} →
        TwoMeetingLinesTransversalStrict design) :
    PatternHeavyWeakToStrict
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) := by
  refine twoMeetingLines_heavyWeakToStrict_of_capBlindSpot
    (fun design hpattern hheavy hcapBlind hweak => ?_)
  obtain ⟨normalFirst, normalSecond, hunitFirst, hunitSecond, horthFirst, horthSecond⟩ :=
    twoMeetingLines_exists_unitLineNormals design hpattern
  by_cases hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2}
  · by_cases hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4}
    · rcases hresidual design hpattern hheavy hcapBlind hweak normalFirst normalSecond
        hunitFirst hunitSecond horthFirst horthSecond hblindFirst hblindSecond with
        h135 | h145 | h235 | h245
      · exact ⟨{1, 3, 5}, by decide, h135⟩
      · exact ⟨{1, 4, 5}, by decide, h145⟩
      · exact ⟨{2, 3, 5}, by decide, h235⟩
      · exact ⟨{2, 4, 5}, by decide, h245⟩
    · simp only [IsLinePairLiftBlindAt] at hblindSecond
      push Not at hblindSecond
      obtain ⟨pairFirst, hFirstMem, pairSecond, hSecondMem, thirdLabel,
        hFirstSecond, hFirstThird, hSecondThird, hcorner, hdet, hcollapse⟩ := hblindSecond
      refine ⟨{pairFirst, pairSecond, thirdLabel},
        card_labelTriple_eq_three hFirstSecond hFirstThird hSecondThird, ?_⟩
      exact (posDef_tripleGap_iff_flatPairFires design hunitSecond pairFirst pairSecond
        thirdLabel hFirstSecond hFirstThird hSecondThird
        (by simpa [normalReading] using horthSecond pairFirst hFirstMem)
        (by simpa [normalReading] using horthSecond pairSecond hSecondMem)).mpr
          ⟨hcorner, hdet, hcollapse⟩
  · simp only [IsLinePairLiftBlindAt] at hblindFirst
    push Not at hblindFirst
    obtain ⟨pairFirst, hFirstMem, pairSecond, hSecondMem, thirdLabel,
      hFirstSecond, hFirstThird, hSecondThird, hcorner, hdet, hcollapse⟩ := hblindFirst
    refine ⟨{pairFirst, pairSecond, thirdLabel},
      card_labelTriple_eq_three hFirstSecond hFirstThird hSecondThird, ?_⟩
    exact (posDef_tripleGap_iff_flatPairFires design hunitFirst pairFirst pairSecond
      thirdLabel hFirstSecond hFirstThird hSecondThird
      (by simpa [normalReading] using horthFirst pairFirst hFirstMem)
      (by simpa [normalReading] using horthFirst pairSecond hSecondMem)).mpr
        ⟨hcorner, hdet, hcollapse⟩

end Gtz

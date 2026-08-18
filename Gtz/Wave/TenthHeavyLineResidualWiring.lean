import Gtz.Design.TwoMeetingLinesTransversal
import Gtz.Wave.TenthLightPatternWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The tenth-heavy line residuals after every landed lift has fired

The generic tenth-light split in `Gtz.Wave.TenthLightPatternWiring` removes all
designs whose raw weights are below `1 / 10`.  The line-class modules already
remove two further regions:

* `Gtz.patternHeavyWeakToStrict_oneLine_of_lineNormalBlindSpot` reduces the
  one-line class to the joint pair-cap and line-normal blind spot;
* `Gtz.twoMeetingLines_heavyWeakToStrict_of_transversalResidual` reduces the
  two-meeting-lines class, after both normal lifts are blind, to four explicit
  transversal triples.

This module composes those reductions.  The resulting Props are logically
equivalent to the former pattern obligations, but their quantified regions
contain every useful fact already produced by the tree: leverage heaviness, a
raw-heavy label, a weak dominator, cap blindness, and the relevant normal-lift
blindness.  No producer is silently re-demanded of the eventual proof.
-/

namespace Gtz

open Matrix Finset

/-! ## One three-point line -/

/-- The exact one-line residual after the tenth-light theorem, pair-cap engine,
and line-normal lift criterion have all fired. -/
def OneLineTenthHeavyJointBlindWeakToStrict : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
    (∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel) →
    IsCapBlindSpot design →
    IsOneLineNormalBlindSpot design →
    (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - 1).PosDef

/-- The joint-blind tenth-heavy residual reconstructs the full one-line
weak-to-strict statement.  In the only branch not covered by the residual,
all raw weights are below one tenth, so the unconditional tenth theorem closes
the design before either blind-spot hypothesis is used. -/
theorem patternHeavyWeakToStrict_oneLine_of_tenthHeavyJointBlind
    (hresidual : OneLineTenthHeavyJointBlindWeakToStrict) :
    PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  apply patternHeavyWeakToStrict_oneLine_of_lineNormalBlindSpot
  intro design hpattern hheavy hcapBlind hlineBlind hweak
  by_cases hweightHeavy : ∃ heavyLabel : Fin 6,
      1 / 10 ≤ design.weight heavyLabel
  · exact hresidual design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak
  · apply exists_posDef_triple_of_weights_lt_tenth design
    intro label
    exact lt_of_not_ge fun hge => hweightHeavy ⟨label, hge⟩

/-- Any proof of the former one-line statement restricts to the narrowed
residual. -/
theorem tenthHeavyJointBlind_oneLine_of_patternHeavyWeakToStrict
    (hupgrade :
      PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    OneLineTenthHeavyJointBlindWeakToStrict := by
  intro design hpattern hheavy _hweightHeavy _hcapBlind _hlineBlind hweak
  exact hupgrade design hpattern hheavy hweak

/-- The one-line residual is an equivalent presentation of the former public
obligation, not a stronger sufficient condition. -/
theorem oneLineTenthHeavyJointBlindWeakToStrict_iff :
    OneLineTenthHeavyJointBlindWeakToStrict ↔
      PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  ⟨patternHeavyWeakToStrict_oneLine_of_tenthHeavyJointBlind,
    tenthHeavyJointBlind_oneLine_of_patternHeavyWeakToStrict⟩

/-- Equivalence with the immediately preceding tenth-heavy registry formula. -/
theorem oneLineTenthHeavyJointBlindWeakToStrict_iff_tenthHeavy :
    OneLineTenthHeavyJointBlindWeakToStrict ↔
      PatternHeavyWeakToStrictTenthHeavy
        (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  oneLineTenthHeavyJointBlindWeakToStrict_iff.trans
    (patternHeavyWeakToStrictTenthHeavy_iff _).symm

/-! ## Two meeting three-point lines -/

/-- The exact two-meeting-lines residual after the tenth-light theorem, the
pair-cap engine, and both line-normal lift criteria have fired.  In the joint
blind spot every possible strict winner is one of the four transversals named
by `Gtz.TwoMeetingLinesTransversalStrict`.

#NOT-THE-AXIOM.  This Prop is no longer the registry entry.  The axiom is
`Skeleton.obligationSeededTransversalTwoMeetingLines`
(Skeleton/Obligations.lean:283), whose Prop is
`Gtz.TwoMeetingLinesSeededTransversal` (Gtz/Wave/FlatPairWeakSeed.lean:651).
That form carries `Gtz.TwoMeetingLinesWeakSeed` in its antecedent, so a prover
receives the pinch, the trichotomy and the transversal arm for free.  The two
Props are interderivable by `Gtz.twoMeetingLinesSeededTransversal_iff` (:695).
Start from the seeded form, not from this one. -/
def TwoMeetingLinesTenthHeavyJointBlindTransversal : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
    (∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel) →
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
      TwoMeetingLinesTransversalStrict design

/-- The narrowed four-transversal residual reconstructs the full
two-meeting-lines weak-to-strict statement.  On the all-light branch the
unconditional strict triple is localized to the same four transversals by the
two-normal blind-spot theorem. -/
theorem patternHeavyWeakToStrict_twoMeetingLines_of_tenthHeavyJointBlindTransversal
    (hresidual : TwoMeetingLinesTenthHeavyJointBlindTransversal) :
    PatternHeavyWeakToStrict
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) := by
  apply twoMeetingLines_heavyWeakToStrict_of_transversalResidual
  intro design hpattern hheavy hcapBlind hweak normalFirst normalSecond
    hunitFirst hunitSecond horthFirst horthSecond hblindFirst hblindSecond
  by_cases hweightHeavy : ∃ heavyLabel : Fin 6,
      1 / 10 ≤ design.weight heavyLabel
  · exact hresidual design hpattern hheavy hweightHeavy hcapBlind hweak
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond
  · obtain ⟨selected, hcard, hposDef⟩ :=
      exists_posDef_triple_of_weights_lt_tenth design (by
        intro label
        exact lt_of_not_ge fun hge => hweightHeavy ⟨label, hge⟩)
    have hshape := twoMeetingLines_strictTriple_eq_transversal_of_bothLineNormalBlind
      design normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond selected hcard hposDef
    rcases hshape with h135 | h145 | h235 | h245
    · exact Or.inl (by simpa only [h135] using hposDef)
    · exact Or.inr (Or.inl (by simpa only [h145] using hposDef))
    · exact Or.inr (Or.inr (Or.inl (by simpa only [h235] using hposDef)))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [h245] using hposDef)))

/-- Any proof of the former two-meeting-lines statement restricts to the
four-transversal residual; the blind-spot shape theorem localizes its selected
strict triple. -/
theorem tenthHeavyJointBlindTransversal_twoMeetingLines_of_patternHeavyWeakToStrict
    (hupgrade : PatternHeavyWeakToStrict
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])) :
    TwoMeetingLinesTenthHeavyJointBlindTransversal := by
  intro design hpattern hheavy _hweightHeavy _hcapBlind hweak normalFirst normalSecond
    hunitFirst hunitSecond horthFirst horthSecond hblindFirst hblindSecond
  obtain ⟨selected, hcard, hposDef⟩ := hupgrade design hpattern hheavy hweak
  have hshape := twoMeetingLines_strictTriple_eq_transversal_of_bothLineNormalBlind
    design normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
    hblindFirst hblindSecond selected hcard hposDef
  rcases hshape with h135 | h145 | h235 | h245
  · exact Or.inl (by simpa only [h135] using hposDef)
  · exact Or.inr (Or.inl (by simpa only [h145] using hposDef))
  · exact Or.inr (Or.inr (Or.inl (by simpa only [h235] using hposDef)))
  · exact Or.inr (Or.inr (Or.inr (by simpa only [h245] using hposDef)))

/-- The two-meeting-lines residual is an equivalent presentation of the former
public obligation. -/
theorem twoMeetingLinesTenthHeavyJointBlindTransversal_iff :
    TwoMeetingLinesTenthHeavyJointBlindTransversal ↔
      PatternHeavyWeakToStrict
        (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  ⟨patternHeavyWeakToStrict_twoMeetingLines_of_tenthHeavyJointBlindTransversal,
    tenthHeavyJointBlindTransversal_twoMeetingLines_of_patternHeavyWeakToStrict⟩

/-- Equivalence with the immediately preceding tenth-heavy registry formula. -/
theorem twoMeetingLinesTenthHeavyJointBlindTransversal_iff_tenthHeavy :
    TwoMeetingLinesTenthHeavyJointBlindTransversal ↔
      PatternHeavyWeakToStrictTenthHeavy
        (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  twoMeetingLinesTenthHeavyJointBlindTransversal_iff.trans
    (patternHeavyWeakToStrictTenthHeavy_iff _).symm

end Gtz

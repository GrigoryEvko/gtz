import Gtz.Design.LineClassObstructions
import Gtz.Wave.ProjectionDictionary

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The tenth-light closure wired into the chartless pattern obligations

`Gtz.PatternHeavyWeakToStrict` uses *leverage* heaviness.  It therefore still
quantifies over designs whose six raw weights are all below one tenth.  The
unconditional real tenth floor closes that entire region independently of the
line pattern and independently of the leverage hypotheses.

This module separates the two notions of heaviness explicitly.  The surviving
pattern residual keeps the landed leverage floor and additionally receives a
label whose design weight is at least `1 / 10`.  The generic IFF proves that
this is an equivalent presentation of `Gtz.PatternHeavyWeakToStrict` at every
six-label pattern, so both chartless registry entries can consume it without
duplicating a proof.
-/

namespace Gtz

open Matrix Finset

/-- The residual after spending the all-light theorem at a six-label line
pattern.  `hheavy` is the existing leverage-heavy hypothesis; `hweightHeavy`
is the new raw-weight witness. -/
def PatternHeavyWeakToStrictTenthHeavy (pattern : LinePattern 6) : Prop :=
  ∀ design : WeightedDesign 6 3, HasLinePattern design pattern →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
    (∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel) →
    (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - 1).PosDef

/-- The tenth-heavy residual reconstructs the original pattern property.  If
no raw weight reaches one tenth, the projection dictionary supplies a strict
triple before any pattern or leverage information is used. -/
theorem patternHeavyWeakToStrict_of_tenthHeavy (pattern : LinePattern 6)
    (hresidual : PatternHeavyWeakToStrictTenthHeavy pattern) :
    PatternHeavyWeakToStrict pattern := by
  intro design hpattern hheavy hweak
  by_cases hweightHeavy : ∃ heavyLabel : Fin 6,
      1 / 10 ≤ design.weight heavyLabel
  · exact hresidual design hpattern hheavy hweightHeavy hweak
  · apply exists_posDef_triple_of_weights_lt_tenth design
    intro label
    exact lt_of_not_ge fun hge => hweightHeavy ⟨label, hge⟩

/-- The original pattern property trivially restricts to the tenth-heavy
region. -/
theorem tenthHeavy_of_patternHeavyWeakToStrict (pattern : LinePattern 6)
    (hupgrade : PatternHeavyWeakToStrict pattern) :
    PatternHeavyWeakToStrictTenthHeavy pattern := by
  intro design hpattern hheavy _hweightHeavy hweak
  exact hupgrade design hpattern hheavy hweak

/-- At every six-label line pattern, adding the explicit tenth-heavy witness
changes the formula but not its logical strength. -/
theorem patternHeavyWeakToStrictTenthHeavy_iff (pattern : LinePattern 6) :
    PatternHeavyWeakToStrictTenthHeavy pattern ↔ PatternHeavyWeakToStrict pattern :=
  ⟨patternHeavyWeakToStrict_of_tenthHeavy pattern,
    tenthHeavy_of_patternHeavyWeakToStrict pattern⟩

/-- Direct consumer for the one-line class. -/
theorem patternHeavyWeakToStrict_oneLine_of_tenthHeavy
    (hresidual : PatternHeavyWeakToStrictTenthHeavy
      (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  patternHeavyWeakToStrict_of_tenthHeavy _ hresidual

/-- Direct consumer for the two-meeting-lines class. -/
theorem patternHeavyWeakToStrict_twoMeetingLines_of_tenthHeavy
    (hresidual : PatternHeavyWeakToStrictTenthHeavy
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])) :
    PatternHeavyWeakToStrict
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  patternHeavyWeakToStrict_of_tenthHeavy _ hresidual

end Gtz

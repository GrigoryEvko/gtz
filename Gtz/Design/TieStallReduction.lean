import Gtz.Design.DesignDescentPort
import Gtz.Certificates.ResidueDissolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The no-strict ledger forces a card-four stall

The design-level descent says that every weighted `(6,3)` design carries a
strictly dominating card-three subset, or a stalled positive definite
card-four subset.  Several registry residuals carry a NO-STRICT LEDGER: an
explicit hypothesis that no card-three subset dominates strictly.  That ledger
denies the descent's first branch outright, so it forces the second.

This module spends that observation.  The reduction needs no pattern, no
chart, and no property of the design beyond the ledger itself.

The tie form is the same statement in the campaign's own vocabulary.  `IsTie`
is a weak dominator together with the no-strict ledger, so its second
conjunct is exactly the hypothesis the reduction consumes:

* every tie carries a stalled positive definite card-four subset;
* a design whose card-four subsets all move is therefore not a tie.

That last theorem is the shape the stratum obligations consume, because
tie-freeness is what they conclude.

The results:

* `DesignCardFourStallEscape` — the stall escape at a single design;
* `exists_cardFour_stall_of_noStrict` — the reduction;
* `exists_cardFour_stall_of_isTie` — the tie form;
* `false_of_noStrict_of_stallEscape` — the ledger consumer, which is the
  shape a counterexample residual applies;
* `not_isTie_of_stallEscape` — the tie-freeness consumer.
-/

namespace Gtz

open Finset Matrix

/-! ## The escape at a single design -/

/-- **The stall escape at a design.**  Every positive definite card-four
subset carries a label whose ladder pivot is below one, so no card-four
subset of this design stalls. -/
def DesignCardFourStallEscape (design : WeightedDesign 6 3) : Prop :=
  ∀ sel : Finset (Fin 6), sel.card = 4 → (subsetSum design sel - 1).PosDef →
    ∃ label ∈ sel, chartLadderPivot design.atom (designChartPoint design).mass
      (designChartPoint design).weight sel label < 1

/-! ## The reduction -/

/-- **THE NO-STRICT LEDGER FORCES A STALL.**  A design at which no card-three
subset dominates strictly carries a stalled positive definite card-four
subset.  The descent supplies the dichotomy and the ledger kills its first
branch.  No pattern hypothesis and no chart construction enter. -/
theorem exists_cardFour_stall_of_noStrict (design : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    ∃ sel : Finset (Fin 6), sel.card = 4
      ∧ (subsetSum design sel - 1).PosDef
      ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot design.atom
          (designChartPoint design).mass (designChartPoint design).weight sel label := by
  rcases design_cardThree_or_cardFour_stall design with ⟨sel, hcard, hposDef⟩ | hstall
  · exact absurd hposDef (hnoStrict sel hcard)
  · exact hstall

/-- **EVERY TIE CARRIES A CARD-FOUR STALL.**  The second conjunct of `IsTie`
is the no-strict ledger, so a tie hands the reduction its hypothesis. -/
theorem exists_cardFour_stall_of_isTie (design : WeightedDesign 6 3)
    (htie : IsTie design) :
    ∃ sel : Finset (Fin 6), sel.card = 4
      ∧ (subsetSum design sel - 1).PosDef
      ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot design.atom
          (designChartPoint design).mass (designChartPoint design).weight sel label :=
  exists_cardFour_stall_of_noStrict design htie.2

/-! ## The consumers -/

/-- **The ledger consumer.**  A no-strict ledger and a stall escape are
contradictory.  A counterexample residual carrying the ledger therefore
follows from the escape alone, whatever its other hypotheses are. -/
theorem false_of_noStrict_of_stallEscape (design : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef)
    (hescape : DesignCardFourStallEscape design) : False := by
  obtain ⟨sel, hcard, hposDef, hstall⟩ := exists_cardFour_stall_of_noStrict design hnoStrict
  obtain ⟨label, hmem, hlt⟩ := hescape sel hcard hposDef
  exact absurd (hstall label hmem) (not_le.mpr hlt)

/-- **The tie-freeness consumer.**  A design whose card-four subsets all move
is not a tie.  This is the shape the stratum obligations conclude. -/
theorem not_isTie_of_stallEscape (design : WeightedDesign 6 3)
    (hescape : DesignCardFourStallEscape design) : ¬ IsTie design :=
  fun htie => false_of_noStrict_of_stallEscape design htie.2 hescape

end Gtz

import Gtz.Design.ParsevalComplementCriterion
import Gtz.Design.TwoMeetingLinesComplementCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-!
# The Parseval criterion at the two meeting lines

The four transversal complements are the shared atom together with the two
unused private atoms.  The conclusion is a disjunction over the four
transversals, so ONE light complement suffices, and each line contributes its
own private atom to the sum being tested.

The leverage form of this criterion is silent once the cap reaches a quarter,
because heaviness alone puts each complement's leverage sum at three or more.
The Parseval form tests the complement's WEIGHTED leverage instead, which the
complement's own weights are free to keep small however large the cap is.

* the four instances `twoMeetingLinesTransversalStrict_of_*_weightedLight`;
* `twoMeetingLinesTransversalStrict_of_min_weightedCompl_lt`, the min-of-four
  form, whose hypothesis is the weakest of the four;
* `twoMeetingLinesResidual_of_min_weightedCompl_lt`, stated against the
  residual's own hypotheses, consuming none of them.
-/

/-! ## The four weighted complement sums -/

/-- The weighted complement of the transversal `{1,3,5}`. -/
theorem sum_compl_transversal_oneThreeFive_weightedLeverage (design : WeightedDesign 6 3) :
    (∑ label ∈ (({1, 3, 5} : Finset (Fin 6)))ᶜ,
        design.weight label * leverageOf (design.atom label))
      = design.weight 0 * leverageOf (design.atom 0)
        + design.weight 2 * leverageOf (design.atom 2)
        + design.weight 4 * leverageOf (design.atom 4) := by
  rw [compl_transversal_oneThreeFive]
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-- The weighted complement of the transversal `{1,4,5}`. -/
theorem sum_compl_transversal_oneFourFive_weightedLeverage (design : WeightedDesign 6 3) :
    (∑ label ∈ (({1, 4, 5} : Finset (Fin 6)))ᶜ,
        design.weight label * leverageOf (design.atom label))
      = design.weight 0 * leverageOf (design.atom 0)
        + design.weight 2 * leverageOf (design.atom 2)
        + design.weight 3 * leverageOf (design.atom 3) := by
  rw [compl_transversal_oneFourFive]
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-- The weighted complement of the transversal `{2,3,5}`. -/
theorem sum_compl_transversal_twoThreeFive_weightedLeverage (design : WeightedDesign 6 3) :
    (∑ label ∈ (({2, 3, 5} : Finset (Fin 6)))ᶜ,
        design.weight label * leverageOf (design.atom label))
      = design.weight 0 * leverageOf (design.atom 0)
        + design.weight 1 * leverageOf (design.atom 1)
        + design.weight 4 * leverageOf (design.atom 4) := by
  rw [compl_transversal_twoThreeFive]
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-- The weighted complement of the transversal `{2,4,5}`. -/
theorem sum_compl_transversal_twoFourFive_weightedLeverage (design : WeightedDesign 6 3) :
    (∑ label ∈ (({2, 4, 5} : Finset (Fin 6)))ᶜ,
        design.weight label * leverageOf (design.atom label))
      = design.weight 0 * leverageOf (design.atom 0)
        + design.weight 1 * leverageOf (design.atom 1)
        + design.weight 3 * leverageOf (design.atom 3) := by
  rw [compl_transversal_twoFourFive]
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-! ## The four instances -/

/-- A lightly weighted `{0,2,4}` closes the residual through `{1,3,5}`. -/
theorem twoMeetingLinesTransversalStrict_of_oneThreeFive_weightedLight
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : design.weight 0 * leverageOf (design.atom 0)
        + design.weight 2 * leverageOf (design.atom 2)
        + design.weight 4 * leverageOf (design.atom 4) < 1 - cap) :
    TwoMeetingLinesTransversalStrict design := by
  refine Or.inl (posDef_of_weightedComplLeverage_lt design hcap _ ?_)
  rw [sum_compl_transversal_oneThreeFive_weightedLeverage]
  exact hlt

/-- A lightly weighted `{0,2,3}` closes the residual through `{1,4,5}`. -/
theorem twoMeetingLinesTransversalStrict_of_oneFourFive_weightedLight
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : design.weight 0 * leverageOf (design.atom 0)
        + design.weight 2 * leverageOf (design.atom 2)
        + design.weight 3 * leverageOf (design.atom 3) < 1 - cap) :
    TwoMeetingLinesTransversalStrict design := by
  refine Or.inr (Or.inl (posDef_of_weightedComplLeverage_lt design hcap _ ?_))
  rw [sum_compl_transversal_oneFourFive_weightedLeverage]
  exact hlt

/-- A lightly weighted `{0,1,4}` closes the residual through `{2,3,5}`. -/
theorem twoMeetingLinesTransversalStrict_of_twoThreeFive_weightedLight
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : design.weight 0 * leverageOf (design.atom 0)
        + design.weight 1 * leverageOf (design.atom 1)
        + design.weight 4 * leverageOf (design.atom 4) < 1 - cap) :
    TwoMeetingLinesTransversalStrict design := by
  refine Or.inr (Or.inr (Or.inl (posDef_of_weightedComplLeverage_lt design hcap _ ?_)))
  rw [sum_compl_transversal_twoThreeFive_weightedLeverage]
  exact hlt

/-- A lightly weighted `{0,1,3}` closes the residual through `{2,4,5}`. -/
theorem twoMeetingLinesTransversalStrict_of_twoFourFive_weightedLight
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : design.weight 0 * leverageOf (design.atom 0)
        + design.weight 1 * leverageOf (design.atom 1)
        + design.weight 3 * leverageOf (design.atom 3) < 1 - cap) :
    TwoMeetingLinesTransversalStrict design := by
  refine Or.inr (Or.inr (Or.inr (posDef_of_weightedComplLeverage_lt design hcap _ ?_)))
  rw [sum_compl_transversal_twoFourFive_weightedLeverage]
  exact hlt

/-! ## The min-of-four form -/

/-- **THE WEAKEST OF THE FOUR HYPOTHESES.**  The shared atom's weighted leverage
plus the lighter private of each line: one light complement out of four closes
the residual, so this is the hypothesis actually needed.

Both minima are taken over a line's two private atoms, and the two lines choose
independently. -/
theorem twoMeetingLinesTransversalStrict_of_min_weightedCompl_lt
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : design.weight 0 * leverageOf (design.atom 0)
        + min (design.weight 1 * leverageOf (design.atom 1))
              (design.weight 2 * leverageOf (design.atom 2))
        + min (design.weight 3 * leverageOf (design.atom 3))
              (design.weight 4 * leverageOf (design.atom 4)) < 1 - cap) :
    TwoMeetingLinesTransversalStrict design := by
  rcases le_total (design.weight 1 * leverageOf (design.atom 1))
      (design.weight 2 * leverageOf (design.atom 2)) with hone | hone <;>
    rcases le_total (design.weight 3 * leverageOf (design.atom 3))
      (design.weight 4 * leverageOf (design.atom 4)) with hthree | hthree
  · rw [min_eq_left hone, min_eq_left hthree] at hlt
    exact twoMeetingLinesTransversalStrict_of_twoFourFive_weightedLight design hcap hlt
  · rw [min_eq_left hone, min_eq_right hthree] at hlt
    exact twoMeetingLinesTransversalStrict_of_twoThreeFive_weightedLight design hcap hlt
  · rw [min_eq_right hone, min_eq_left hthree] at hlt
    exact twoMeetingLinesTransversalStrict_of_oneFourFive_weightedLight design hcap hlt
  · rw [min_eq_right hone, min_eq_right hthree] at hlt
    exact twoMeetingLinesTransversalStrict_of_oneThreeFive_weightedLight design hcap hlt

/-- **The residual holds on the lightly-weighted-complement region**, with none
of the residual's own hypotheses consumed. -/
theorem twoMeetingLinesResidual_of_min_weightedCompl_lt
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : design.weight 0 * leverageOf (design.atom 0)
        + min (design.weight 1 * leverageOf (design.atom 1))
              (design.weight 2 * leverageOf (design.atom 2))
        + min (design.weight 3 * leverageOf (design.atom 3))
              (design.weight 4 * leverageOf (design.atom 4)) < 1 - cap)
    (_hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (_hweightHeavy : ∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel)
    (_hweak : ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) :
    TwoMeetingLinesTransversalStrict design :=
  twoMeetingLinesTransversalStrict_of_min_weightedCompl_lt design hcap hlt

end Gtz

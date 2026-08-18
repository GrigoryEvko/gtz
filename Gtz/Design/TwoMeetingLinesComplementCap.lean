import Gtz.Design.OneLineComplementCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-!
# The complement-leverage criterion at two meeting lines, and the normal needle

The complement-leverage criterion closes a selection whose complement carries
little leverage.  The two-meeting-lines residual asks for ONE of four
transversals, so the criterion only needs ONE of four complements to be light.
Each complement is the shared atom together with the two UNUSED private atoms,
one from each line, so the four complement leverage sums are

    l 0 + l i + l j,    i in {1, 2},  j in {3, 4},

and the effective hypothesis is the minimum of the four.

The same needle that drives the criterion also prices a LINE from below.  At a
unit normal of a line every atom of that line reads zero, so the whole universal
floor falls on the complement:

    1 <= cap * (sum over the complement of the squared readings).

Two consequences.  The criterion can never fire at a line, which is the
consistency check a sufficient criterion owes a family of degenerate triples.
And at the normal of one line the two private atoms of the OTHER line split the
floor, so one of them alone carries a positive transversal gap there.

## #ZERO-CONSUMER — every declaration in this module

Nothing outside this file and the two umbrellas cites any theorem here.
`Gtz.twoMeetingLinesResidual_of_min_complLeverage_lt` (:204) already discharges
the registry residual on a named slab and consumes none of the residual's own
hypotheses, and it is wired to nothing.

## #LIVE, not refuted

The criterion hypothesis is `cap * (l0 + min(l1,l2) + min(l3,l4)) < 1 - cap`.
The needle floor of this same module gives `cap * (l3 + l4 + l5) >= 1 - cap` and
`cap * (l1 + l2 + l5) >= 1 - cap` at the two line normals.  The three label sets
differ, so the floors do not refute the criterion.  Heaviness alone puts the
criterion sum at three or more, so the criterion is silent once the cap reaches
a quarter.  The Parseval form in Gtz/Design/TwoMeetingLinesParsevalCap.lean is
the answer to that, and it is also unconsumed.
-/

variable {size rank : ℕ}

/-! ## The normal needle -/

/-- **THE NORMAL NEEDLE.**  At a unit normal of a line, the line's own atoms read
zero, so the universal floor falls entirely on the complement.

Division-free: the reciprocal of the cap never appears. -/
theorem one_le_cap_mul_sum_compl_sq_of_lineNormal (design : WeightedDesign size rank)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (lineLabels : Finset (Fin size)) (normal : Fin rank → ℝ)
    (hunit : normal ⬝ᵥ normal = 1)
    (horth : ∀ label ∈ lineLabels, design.atom label ⬝ᵥ normal = 0) :
    1 ≤ cap * ∑ label ∈ lineLabelsᶜ, (design.atom label ⬝ᵥ normal) ^ 2 := by
  have hneedle := universal_needle design hcap normal
  have hzero : (∑ label ∈ lineLabels, (design.atom label ⬝ᵥ normal) ^ 2) = 0 :=
    Finset.sum_eq_zero fun label hlabel => by rw [horth label hlabel]; ring
  have hsplit : (∑ label ∈ lineLabels, (design.atom label ⬝ᵥ normal) ^ 2)
      + ∑ label ∈ lineLabelsᶜ, (design.atom label ⬝ᵥ normal) ^ 2
      = ∑ label, (design.atom label ⬝ᵥ normal) ^ 2 :=
    Finset.sum_add_sum_compl lineLabels _
  have hfull : normal ⬝ᵥ ((subsetSum design Finset.univ - 1) *ᵥ normal)
      = (∑ label ∈ lineLabelsᶜ, (design.atom label ⬝ᵥ normal) ^ 2) - 1 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
      Matrix.one_mulVec, hunit]
    linarith [hsplit, hzero]
  rw [hfull, hunit] at hneedle
  linarith

/-- **A LINE'S COMPLEMENT IS LEVERAGE-HEAVY.**  Cauchy-Schwarz turns the normal
needle into a floor on the complement's leverage sum. -/
theorem one_le_cap_mul_sum_compl_leverage_of_lineNormal (design : WeightedDesign size rank)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap) (label : Fin size)
    (lineLabels : Finset (Fin size)) (normal : Fin rank → ℝ)
    (hunit : normal ⬝ᵥ normal = 1)
    (horth : ∀ freeLabel ∈ lineLabels, design.atom freeLabel ⬝ᵥ normal = 0) :
    1 ≤ cap * ∑ freeLabel ∈ lineLabelsᶜ, leverageOf (design.atom freeLabel) := by
  have hneedle :=
    one_le_cap_mul_sum_compl_sq_of_lineNormal design hcap lineLabels normal hunit horth
  have hcapPos : 0 < cap := pos_of_weight_le design hcap label
  have hbound : (∑ freeLabel ∈ lineLabelsᶜ, (design.atom freeLabel ⬝ᵥ normal) ^ 2)
      ≤ ∑ freeLabel ∈ lineLabelsᶜ, leverageOf (design.atom freeLabel) := by
    refine Finset.sum_le_sum fun freeLabel _ => ?_
    have hcs := sq_dotProduct_le_leverage_mul (design.atom freeLabel) normal
    rw [hunit, mul_one] at hcs
    exact hcs
  nlinarith

/-- **THE CRITERION NEVER FIRES AT A LINE.**  A line's complement always fails
the complement-leverage hypothesis, so the criterion cannot certify a degenerate
triple.  This is the consistency check the criterion owes. -/
theorem not_cap_mul_sum_compl_leverage_lt_of_lineNormal (design : WeightedDesign size rank)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap) (label : Fin size)
    (lineLabels : Finset (Fin size)) (normal : Fin rank → ℝ)
    (hunit : normal ⬝ᵥ normal = 1)
    (horth : ∀ freeLabel ∈ lineLabels, design.atom freeLabel ⬝ᵥ normal = 0) :
    ¬ (cap * (∑ freeLabel ∈ lineLabelsᶜ, leverageOf (design.atom freeLabel)) < 1 - cap) := by
  intro hlt
  have hfloor := one_le_cap_mul_sum_compl_leverage_of_lineNormal design hcap label
    lineLabels normal hunit horth
  have hcapPos : 0 < cap := pos_of_weight_le design hcap label
  linarith

/-! ## The four transversal complement leverage sums -/

/-- The complement of `{1,3,5}` carries the shared atom and the two unused
private atoms `2` and `4`. -/
theorem sum_compl_transversal_oneThreeFive_leverage (design : WeightedDesign 6 3) :
    (∑ label ∈ (({1, 3, 5} : Finset (Fin 6)))ᶜ, leverageOf (design.atom label))
      = leverageOf (design.atom 0) + leverageOf (design.atom 2)
        + leverageOf (design.atom 4) := by
  rw [compl_transversal_oneThreeFive]
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-- The complement of `{1,4,5}`. -/
theorem sum_compl_transversal_oneFourFive_leverage (design : WeightedDesign 6 3) :
    (∑ label ∈ (({1, 4, 5} : Finset (Fin 6)))ᶜ, leverageOf (design.atom label))
      = leverageOf (design.atom 0) + leverageOf (design.atom 2)
        + leverageOf (design.atom 3) := by
  rw [compl_transversal_oneFourFive]
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-- The complement of `{2,3,5}`. -/
theorem sum_compl_transversal_twoThreeFive_leverage (design : WeightedDesign 6 3) :
    (∑ label ∈ (({2, 3, 5} : Finset (Fin 6)))ᶜ, leverageOf (design.atom label))
      = leverageOf (design.atom 0) + leverageOf (design.atom 1)
        + leverageOf (design.atom 4) := by
  rw [compl_transversal_twoThreeFive]
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-- The complement of `{2,4,5}`. -/
theorem sum_compl_transversal_twoFourFive_leverage (design : WeightedDesign 6 3) :
    (∑ label ∈ (({2, 4, 5} : Finset (Fin 6)))ᶜ, leverageOf (design.atom label))
      = leverageOf (design.atom 0) + leverageOf (design.atom 1)
        + leverageOf (design.atom 3) := by
  rw [compl_transversal_twoFourFive]
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-! ## The four criterion instances -/

/-- A light `{0,2,4}` closes the residual through the transversal `{1,3,5}`. -/
theorem twoMeetingLinesTransversalStrict_of_oneThreeFive_light
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : cap * (leverageOf (design.atom 0) + leverageOf (design.atom 2)
        + leverageOf (design.atom 4)) < 1 - cap) :
    TwoMeetingLinesTransversalStrict design := by
  refine Or.inl (posDef_of_cap_mul_complLeverageSum_lt design hcap _ 0 ?_)
  rw [sum_compl_transversal_oneThreeFive_leverage]
  exact hlt

/-- A light `{0,2,3}` closes the residual through the transversal `{1,4,5}`. -/
theorem twoMeetingLinesTransversalStrict_of_oneFourFive_light
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : cap * (leverageOf (design.atom 0) + leverageOf (design.atom 2)
        + leverageOf (design.atom 3)) < 1 - cap) :
    TwoMeetingLinesTransversalStrict design := by
  refine Or.inr (Or.inl (posDef_of_cap_mul_complLeverageSum_lt design hcap _ 0 ?_))
  rw [sum_compl_transversal_oneFourFive_leverage]
  exact hlt

/-- A light `{0,1,4}` closes the residual through the transversal `{2,3,5}`. -/
theorem twoMeetingLinesTransversalStrict_of_twoThreeFive_light
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : cap * (leverageOf (design.atom 0) + leverageOf (design.atom 1)
        + leverageOf (design.atom 4)) < 1 - cap) :
    TwoMeetingLinesTransversalStrict design := by
  refine Or.inr (Or.inr (Or.inl (posDef_of_cap_mul_complLeverageSum_lt design hcap _ 0 ?_)))
  rw [sum_compl_transversal_twoThreeFive_leverage]
  exact hlt

/-- A light `{0,1,3}` closes the residual through the transversal `{2,4,5}`. -/
theorem twoMeetingLinesTransversalStrict_of_twoFourFive_light
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : cap * (leverageOf (design.atom 0) + leverageOf (design.atom 1)
        + leverageOf (design.atom 3)) < 1 - cap) :
    TwoMeetingLinesTransversalStrict design := by
  refine Or.inr (Or.inr (Or.inr (posDef_of_cap_mul_complLeverageSum_lt design hcap _ 0 ?_)))
  rw [sum_compl_transversal_twoFourFive_leverage]
  exact hlt

/-! ## The minimum of the four -/

/-- **THE FOUR-COMPLEMENT CRITERION.**  Only ONE of the four complements need be
light, so the effective leverage sum is the shared atom plus the LIGHTER private
atom of each line.

This is strictly weaker than a single-candidate criterion: each line contributes
its minimum, not a fixed atom. -/
theorem twoMeetingLinesTransversalStrict_of_min_complLeverage_lt
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : cap * (leverageOf (design.atom 0)
        + min (leverageOf (design.atom 1)) (leverageOf (design.atom 2))
        + min (leverageOf (design.atom 3)) (leverageOf (design.atom 4))) < 1 - cap) :
    TwoMeetingLinesTransversalStrict design := by
  rcases le_total (leverageOf (design.atom 1)) (leverageOf (design.atom 2)) with hfirst | hfirst <;>
    rcases le_total (leverageOf (design.atom 3)) (leverageOf (design.atom 4)) with
      hsecond | hsecond
  · rw [min_eq_left hfirst, min_eq_left hsecond] at hlt
    exact twoMeetingLinesTransversalStrict_of_twoFourFive_light design hcap hlt
  · rw [min_eq_left hfirst, min_eq_right hsecond] at hlt
    exact twoMeetingLinesTransversalStrict_of_twoThreeFive_light design hcap hlt
  · rw [min_eq_right hfirst, min_eq_left hsecond] at hlt
    exact twoMeetingLinesTransversalStrict_of_oneFourFive_light design hcap hlt
  · rw [min_eq_right hfirst, min_eq_right hsecond] at hlt
    exact twoMeetingLinesTransversalStrict_of_oneThreeFive_light design hcap hlt

/-- **The residual holds on the light-complement slab.**  The criterion consumes
none of the residual's own hypotheses: no line pattern, no blind spot, no weak
dominator and no line normal. -/
theorem twoMeetingLinesResidual_of_min_complLeverage_lt
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : cap * (leverageOf (design.atom 0)
        + min (leverageOf (design.atom 1)) (leverageOf (design.atom 2))
        + min (leverageOf (design.atom 3)) (leverageOf (design.atom 4))) < 1 - cap)
    (_hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (_hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (_hweightHeavy : ∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel)
    (_hcapBlind : IsCapBlindSpot design)
    (_hweak : ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) :
    TwoMeetingLinesTransversalStrict design :=
  twoMeetingLinesTransversalStrict_of_min_complLeverage_lt design hcap hlt

/-! ## The normal of one line splits the other line's privates -/

/-- The gap form of the transversal `{1,3,5}` at a normal of the first line drops
its own first-line atom. -/
theorem transversal_oneThreeFive_gap_at_lineOneNormal (design : WeightedDesign 6 3)
    (normal : Fin 3 → ℝ) (hunit : normal ⬝ᵥ normal = 1)
    (horth : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normal = 0) :
    normal ⬝ᵥ ((subsetSum design ({1, 3, 5} : Finset (Fin 6)) - 1) *ᵥ normal)
      = (design.atom 3 ⬝ᵥ normal) ^ 2 + (design.atom 5 ⬝ᵥ normal) ^ 2 - 1 := by
  have hsum : (∑ label ∈ ({1, 3, 5} : Finset (Fin 6)), (design.atom label ⬝ᵥ normal) ^ 2)
      = (design.atom 1 ⬝ᵥ normal) ^ 2 + (design.atom 3 ⬝ᵥ normal) ^ 2
        + (design.atom 5 ⬝ᵥ normal) ^ 2 := by
    simp [Finset.sum_insert, Finset.mem_insert, add_assoc]
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
    Matrix.one_mulVec, hunit, hsum, horth 1 (by decide)]
  ring

/-- The gap form of the transversal `{1,4,5}` at a normal of the first line. -/
theorem transversal_oneFourFive_gap_at_lineOneNormal (design : WeightedDesign 6 3)
    (normal : Fin 3 → ℝ) (hunit : normal ⬝ᵥ normal = 1)
    (horth : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normal = 0) :
    normal ⬝ᵥ ((subsetSum design ({1, 4, 5} : Finset (Fin 6)) - 1) *ᵥ normal)
      = (design.atom 4 ⬝ᵥ normal) ^ 2 + (design.atom 5 ⬝ᵥ normal) ^ 2 - 1 := by
  have hsum : (∑ label ∈ ({1, 4, 5} : Finset (Fin 6)), (design.atom label ⬝ᵥ normal) ^ 2)
      = (design.atom 1 ⬝ᵥ normal) ^ 2 + (design.atom 4 ⬝ᵥ normal) ^ 2
        + (design.atom 5 ⬝ᵥ normal) ^ 2 := by
    simp [Finset.sum_insert, Finset.mem_insert, add_assoc]
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
    Matrix.one_mulVec, hunit, hsum, horth 1 (by decide)]
  ring

/-- **THE NORMAL PICKS A PRIVATE ATOM.**  At a normal of the first line the whole
universal floor sits on the second line's privates and the free atom, so the
heavier of the two privates carries a strictly positive transversal gap there.

The cap bound `cap < 1 / 2` is what turns the split floor `1 / (2 * cap)` into a
value above one. -/
theorem exists_transversal_gap_pos_at_lineOneNormal (design : WeightedDesign 6 3)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap) (hcapLt : cap < 1 / 2)
    (normal : Fin 3 → ℝ) (hunit : normal ⬝ᵥ normal = 1)
    (horth : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normal = 0) :
    0 < normal ⬝ᵥ ((subsetSum design ({1, 3, 5} : Finset (Fin 6)) - 1) *ᵥ normal)
      ∨ 0 < normal ⬝ᵥ ((subsetSum design ({1, 4, 5} : Finset (Fin 6)) - 1) *ᵥ normal) := by
  have hcapPos : 0 < cap := pos_of_weight_le design hcap 0
  have hcompl : (({0, 1, 2} : Finset (Fin 6)))ᶜ = ({3, 4, 5} : Finset (Fin 6)) := by decide
  have hfloor := one_le_cap_mul_sum_compl_sq_of_lineNormal design hcap
    ({0, 1, 2} : Finset (Fin 6)) normal hunit horth
  rw [hcompl] at hfloor
  have hsum : (∑ label ∈ ({3, 4, 5} : Finset (Fin 6)), (design.atom label ⬝ᵥ normal) ^ 2)
      = (design.atom 3 ⬝ᵥ normal) ^ 2 + (design.atom 4 ⬝ᵥ normal) ^ 2
        + (design.atom 5 ⬝ᵥ normal) ^ 2 := by
    simp [Finset.sum_insert, Finset.mem_insert, add_assoc]
  rw [hsum] at hfloor
  rw [transversal_oneThreeFive_gap_at_lineOneNormal design normal hunit horth,
    transversal_oneFourFive_gap_at_lineOneNormal design normal hunit horth]
  rcases le_total ((design.atom 4 ⬝ᵥ normal) ^ 2) ((design.atom 3 ⬝ᵥ normal) ^ 2) with
    hmax | hmax
  · exact Or.inl (by nlinarith [sq_nonneg (design.atom 5 ⬝ᵥ normal)])
  · exact Or.inr (by nlinarith [sq_nonneg (design.atom 5 ⬝ᵥ normal)])

/-- The gap form of the transversal `{1,3,5}` at a normal of the second line
drops its own second-line atom. -/
theorem transversal_oneThreeFive_gap_at_lineTwoNormal (design : WeightedDesign 6 3)
    (normal : Fin 3 → ℝ) (hunit : normal ⬝ᵥ normal = 1)
    (horth : ∀ label ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normal = 0) :
    normal ⬝ᵥ ((subsetSum design ({1, 3, 5} : Finset (Fin 6)) - 1) *ᵥ normal)
      = (design.atom 1 ⬝ᵥ normal) ^ 2 + (design.atom 5 ⬝ᵥ normal) ^ 2 - 1 := by
  have hsum : (∑ label ∈ ({1, 3, 5} : Finset (Fin 6)), (design.atom label ⬝ᵥ normal) ^ 2)
      = (design.atom 1 ⬝ᵥ normal) ^ 2 + (design.atom 3 ⬝ᵥ normal) ^ 2
        + (design.atom 5 ⬝ᵥ normal) ^ 2 := by
    simp [Finset.sum_insert, Finset.mem_insert, add_assoc]
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
    Matrix.one_mulVec, hunit, hsum, horth 3 (by decide)]
  ring

/-- The gap form of the transversal `{2,3,5}` at a normal of the second line. -/
theorem transversal_twoThreeFive_gap_at_lineTwoNormal (design : WeightedDesign 6 3)
    (normal : Fin 3 → ℝ) (hunit : normal ⬝ᵥ normal = 1)
    (horth : ∀ label ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normal = 0) :
    normal ⬝ᵥ ((subsetSum design ({2, 3, 5} : Finset (Fin 6)) - 1) *ᵥ normal)
      = (design.atom 2 ⬝ᵥ normal) ^ 2 + (design.atom 5 ⬝ᵥ normal) ^ 2 - 1 := by
  have hsum : (∑ label ∈ ({2, 3, 5} : Finset (Fin 6)), (design.atom label ⬝ᵥ normal) ^ 2)
      = (design.atom 2 ⬝ᵥ normal) ^ 2 + (design.atom 3 ⬝ᵥ normal) ^ 2
        + (design.atom 5 ⬝ᵥ normal) ^ 2 := by
    simp [Finset.sum_insert, Finset.mem_insert, add_assoc]
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
    Matrix.one_mulVec, hunit, hsum, horth 3 (by decide)]
  ring

/-- **THE SECOND NORMAL PICKS A PRIVATE ATOM.**  The mirror statement: at a normal
of the second line the floor sits on the FIRST line's privates and the free atom,
so the heavier of `1` and `2` carries a strictly positive transversal gap there.

Together with the first-line statement, the two normals choose the two private
atoms of a transversal independently: one line's normal selects the other line's
private. -/
theorem exists_transversal_gap_pos_at_lineTwoNormal (design : WeightedDesign 6 3)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap) (hcapLt : cap < 1 / 2)
    (normal : Fin 3 → ℝ) (hunit : normal ⬝ᵥ normal = 1)
    (horth : ∀ label ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normal = 0) :
    0 < normal ⬝ᵥ ((subsetSum design ({1, 3, 5} : Finset (Fin 6)) - 1) *ᵥ normal)
      ∨ 0 < normal ⬝ᵥ ((subsetSum design ({2, 3, 5} : Finset (Fin 6)) - 1) *ᵥ normal) := by
  have hcapPos : 0 < cap := pos_of_weight_le design hcap 0
  have hcompl : (({0, 3, 4} : Finset (Fin 6)))ᶜ = ({1, 2, 5} : Finset (Fin 6)) := by decide
  have hfloor := one_le_cap_mul_sum_compl_sq_of_lineNormal design hcap
    ({0, 3, 4} : Finset (Fin 6)) normal hunit horth
  rw [hcompl] at hfloor
  have hsum : (∑ label ∈ ({1, 2, 5} : Finset (Fin 6)), (design.atom label ⬝ᵥ normal) ^ 2)
      = (design.atom 1 ⬝ᵥ normal) ^ 2 + (design.atom 2 ⬝ᵥ normal) ^ 2
        + (design.atom 5 ⬝ᵥ normal) ^ 2 := by
    simp [Finset.sum_insert, Finset.mem_insert, add_assoc]
  rw [hsum] at hfloor
  rw [transversal_oneThreeFive_gap_at_lineTwoNormal design normal hunit horth,
    transversal_twoThreeFive_gap_at_lineTwoNormal design normal hunit horth]
  rcases le_total ((design.atom 2 ⬝ᵥ normal) ^ 2) ((design.atom 1 ⬝ᵥ normal) ^ 2) with
    hmax | hmax
  · exact Or.inl (by nlinarith [sq_nonneg (design.atom 5 ⬝ᵥ normal)])
  · exact Or.inr (by nlinarith [sq_nonneg (design.atom 5 ⬝ᵥ normal)])

end Gtz

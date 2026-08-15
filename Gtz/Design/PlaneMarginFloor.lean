import Gtz.Design.DustWeightCollar
import Gtz.Design.LeverageBound
import Gtz.LinAlg.ProjectionForm

/-!
# The plane-margin floor, and the weight ceiling it forces

`Gtz.PlaneMarginProducerAtLightLabel` is the one open statement of A1's dust leg.
At every light label it asks for a pair that covers the plane of that label with
relative surplus `marginRatio` AND whose leverages sum below
`marginRatio * (leverageOf insert - 1)`.

This file proves the two demands FIGHT, measures the fight exactly, and turns the
measurement into refutations that read a single weight.

**The floor.**  A pair covering the plane of `a` with surplus `marginRatio`
carries squared length at least `2 * (1 + marginRatio)` between the two labels.
The proof needs no orthonormal basis and no division.  The three explicit vectors
`![0, a 2, -a 1]`, `![-a 2, 0, a 0]` and `![a 1, -a 0, 0]` are each orthogonal to
`a`, their squared lengths sum to `2 * leverageOf a`, and the squared readings of
any `b` against them sum to the Lagrange gap `leverageOf b * leverageOf a -
(b ⬝ᵥ a) ^ 2`.  Feeding the three into the margin and adding gives the floor.

**The collision.**  The floor meets the leverage gate and forces
`3 * marginRatio + 2 < marginRatio * leverageOf (atom insert)`, so the producer
fires only at labels of LARGE leverage.  The gate also hands back
`1 < leverageOf (atom insert)` for free, so the nondegeneracy side condition of
the floor never has to be supplied by a consumer.

**The ceiling.**  `Gtz.weighted_leverage_le_one` caps `weight * leverage` by one.
Against the floor that becomes `weight * (3 * marginRatio + 2) < marginRatio`, a
statement about a WEIGHT alone.  Summing it over any set of light labels and
using `Gtz.sum_weight_mul_leverage` gives
`(3 * marginRatio + 2) * (∑ light weights) ≤ 3 * marginRatio`, and taking the set
to be everything yields `3 * marginRatio + 2 ≤ 3 * marginRatio`, which is false.

So the producer implies that **no** line-free off-conic design has all of its
weights below the dust threshold, and one design with a single label of weight in
the band `[marginRatio / (3 * marginRatio + 2), dustThreshold]` refutes it
outright -- with no pair, no margin and no leverage ever computed.
-/

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Three explicit probes in the plane of an atom -/

/-- The first probe in the plane of `a`. -/
def planeProbeZero (a : Fin 3 → ℝ) : Fin 3 → ℝ := ![0, a 2, -a 1]

/-- The second probe in the plane of `a`. -/
def planeProbeOne (a : Fin 3 → ℝ) : Fin 3 → ℝ := ![-a 2, 0, a 0]

/-- The third probe in the plane of `a`. -/
def planeProbeTwo (a : Fin 3 → ℝ) : Fin 3 → ℝ := ![a 1, -a 0, 0]

theorem planeProbeZero_orth (a : Fin 3 → ℝ) : a ⬝ᵥ planeProbeZero a = 0 := by
  simp [planeProbeZero, dotProduct, Fin.sum_univ_three]; ring

theorem planeProbeOne_orth (a : Fin 3 → ℝ) : a ⬝ᵥ planeProbeOne a = 0 := by
  simp [planeProbeOne, dotProduct, Fin.sum_univ_three]; ring

theorem planeProbeTwo_orth (a : Fin 3 → ℝ) : a ⬝ᵥ planeProbeTwo a = 0 := by
  simp [planeProbeTwo, dotProduct, Fin.sum_univ_three]; ring

/-- **THE THREE PROBES CARRY TWICE THE LEVERAGE.**  Their squared lengths sum to
`2 * leverageOf a`, so the plane of `a` is measured without ever building an
orthonormal basis for it. -/
theorem sum_planeProbe_leverage (a : Fin 3 → ℝ) :
    planeProbeZero a ⬝ᵥ planeProbeZero a + planeProbeOne a ⬝ᵥ planeProbeOne a
      + planeProbeTwo a ⬝ᵥ planeProbeTwo a = 2 * leverageOf a := by
  simp [planeProbeZero, planeProbeOne, planeProbeTwo, leverageOf, dotProduct,
    Fin.sum_univ_three]
  ring

/-- **THE LAGRANGE READING.**  The squared readings of `b` against the three
probes sum to the Lagrange gap of the pair `(b, a)`. -/
theorem sum_sq_dot_planeProbe (b a : Fin 3 → ℝ) :
    (b ⬝ᵥ planeProbeZero a) ^ 2 + (b ⬝ᵥ planeProbeOne a) ^ 2
        + (b ⬝ᵥ planeProbeTwo a) ^ 2
      = leverageOf b * leverageOf a - (b ⬝ᵥ a) ^ 2 := by
  simp [planeProbeZero, planeProbeOne, planeProbeTwo, leverageOf, dotProduct,
    Fin.sum_univ_three]
  ring

/-- The Lagrange gap never exceeds the product of the leverages. -/
theorem lagrange_gap_le (b a : Fin 3 → ℝ) :
    leverageOf b * leverageOf a - (b ⬝ᵥ a) ^ 2 ≤ leverageOf b * leverageOf a := by
  nlinarith [sq_nonneg (b ⬝ᵥ a)]

/-! ## The floor forced by a plane margin -/

/-- **THE KEPT-LEVERAGE FLOOR.**  A pair that covers the plane of `insertLabel`
with relative surplus `marginRatio` carries at least `2 * (1 + marginRatio)` of
leverage between the two kept labels.  No orthonormal basis, no division, and no
hypothesis on the pattern. -/
theorem planeMargin_kept_leverage_floor (design : WeightedDesign m 3)
    {keptOne keptTwo insertLabel : Fin m} {marginRatio : ℝ}
    (hatomPos : 0 < leverageOf (design.atom insertLabel))
    (hmargin : PlaneMarginAt design keptOne keptTwo insertLabel marginRatio) :
    2 * (1 + marginRatio)
      ≤ leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo) := by
  set a : Fin 3 → ℝ := design.atom insertLabel with ha
  set p : Fin 3 → ℝ := design.atom keptOne with hp
  set q : Fin 3 → ℝ := design.atom keptTwo with hq
  have h0 := hmargin (planeProbeZero a) (planeProbeZero_orth a)
  have h1 := hmargin (planeProbeOne a) (planeProbeOne_orth a)
  have h2 := hmargin (planeProbeTwo a) (planeProbeTwo_orth a)
  have hsumProbe := sum_planeProbe_leverage a
  have hsumP := sum_sq_dot_planeProbe p a
  have hsumQ := sum_sq_dot_planeProbe q a
  have hboundP := lagrange_gap_le p a
  have hboundQ := lagrange_gap_le q a
  have hadd : (1 + marginRatio) * (2 * leverageOf a)
      ≤ (leverageOf p * leverageOf a - (p ⬝ᵥ a) ^ 2)
        + (leverageOf q * leverageOf a - (q ⬝ᵥ a) ^ 2) := by
    rw [← hsumProbe, ← hsumP, ← hsumQ]
    nlinarith [h0, h1, h2]
  nlinarith [hadd, hboundP, hboundQ, hatomPos]

/-- **THE GATE PAYS FOR ITS OWN NONDEGENERACY.**  The leverage gate already forces
the insert atom strictly heavy, so no consumer has to supply positivity of its
leverage separately. -/
theorem one_lt_insert_leverage_of_gate (design : WeightedDesign m k)
    {keptOne keptTwo insertLabel : Fin m} {marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hgap : leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
      < marginRatio * (leverageOf (design.atom insertLabel) - 1)) :
    1 < leverageOf (design.atom insertLabel) := by
  have hkeptNonneg : 0 ≤ leverageOf (design.atom keptOne)
      + leverageOf (design.atom keptTwo) :=
    add_nonneg (leverageOf_nonneg _) (leverageOf_nonneg _)
  nlinarith [hgap, hkeptNonneg, hmarginPos]

/-- **THE PRODUCER'S OWN HYPOTHESES FORCE A HEAVY INSERT LABEL.**  The plane
margin and the leverage gate cannot both hold unless the insert leverage clears
`3 + 2 / marginRatio`, stated here without division. -/
theorem planeMarginGate_insert_leverage_gt (design : WeightedDesign m 3)
    {keptOne keptTwo insertLabel : Fin m} {marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hmargin : PlaneMarginAt design keptOne keptTwo insertLabel marginRatio)
    (hgap : leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
      < marginRatio * (leverageOf (design.atom insertLabel) - 1)) :
    3 * marginRatio + 2 < marginRatio * leverageOf (design.atom insertLabel) := by
  have hheavy := one_lt_insert_leverage_of_gate design hmarginPos hgap
  have hatomPos : 0 < leverageOf (design.atom insertLabel) := by linarith
  have hfloor := planeMargin_kept_leverage_floor design hatomPos hmargin
  nlinarith [hfloor, hgap]

/-! ## The weight ceiling the floor implies -/

/-- **THE FLOOR BECOMES A CEILING ON THE WEIGHT.**  `weighted_leverage_le_one`
caps `weight * leverage` by one, so a label the gate can serve carries weight
strictly below `marginRatio / (3 * marginRatio + 2)`.  The statement reads only a
weight: no pair, no margin and no leverage survive in it. -/
theorem weight_ceiling_of_planeMarginGate (design : WeightedDesign m 3)
    {keptOne keptTwo insertLabel : Fin m} {marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hmargin : PlaneMarginAt design keptOne keptTwo insertLabel marginRatio)
    (hgap : leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
      < marginRatio * (leverageOf (design.atom insertLabel) - 1)) :
    design.weight insertLabel * (3 * marginRatio + 2) < marginRatio := by
  have hfloor := planeMarginGate_insert_leverage_gt design hmarginPos hmargin hgap
  have hcap : design.weight insertLabel * leverageOf (design.atom insertLabel) ≤ 1 :=
    weighted_leverage_le_one design insertLabel
  have hwpos : 0 < design.weight insertLabel := design.weight_pos insertLabel
  nlinarith [hfloor, hcap, hwpos, hmarginPos]

/-! ## What the producer costs, label by label and in bulk -/

/-- **THE PRODUCER'S NECESSARY CONDITION AT ONE LABEL.**  If the producer holds,
then at every line-free off-conic design each label of weight at most the dust
threshold clears the leverage floor. -/
theorem producer_forces_leverage_floor {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hproducer : PlaneMarginProducerAtLightLabel dustThreshold marginRatio)
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (lightLabel : Fin 6) (hlight : design.weight lightLabel ≤ dustThreshold) :
    3 * marginRatio + 2 < marginRatio * leverageOf (design.atom lightLabel) := by
  obtain ⟨keptOne, keptTwo, _, _, _, hmargin, hgap⟩ :=
    hproducer design hpattern hoffConic lightLabel hlight
  exact planeMarginGate_insert_leverage_gt design hmarginPos hmargin hgap

/-- **THE WEIGHT VERSION.**  Every light label of every line-free off-conic design
carries weight strictly below `marginRatio / (3 * marginRatio + 2)`. -/
theorem producer_forces_weight_ceiling {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hproducer : PlaneMarginProducerAtLightLabel dustThreshold marginRatio)
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (lightLabel : Fin 6) (hlight : design.weight lightLabel ≤ dustThreshold) :
    design.weight lightLabel * (3 * marginRatio + 2) < marginRatio := by
  obtain ⟨keptOne, keptTwo, _, _, _, hmargin, hgap⟩ :=
    hproducer design hpattern hoffConic lightLabel hlight
  exact weight_ceiling_of_planeMarginGate design hmarginPos hmargin hgap

/-- **THE BULK BOUND.**  Over any set of light labels the producer caps the total
weight, through the trace identity `sum_weight_mul_leverage`.  This is the
statement that becomes contradictory when the set is everything. -/
theorem producer_light_weight_sum_le {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hproducer : PlaneMarginProducerAtLightLabel dustThreshold marginRatio)
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (lightSet : Finset (Fin 6))
    (hlight : ∀ c ∈ lightSet, design.weight c ≤ dustThreshold) :
    (3 * marginRatio + 2) * (∑ c ∈ lightSet, design.weight c) ≤ 3 * marginRatio := by
  have hterm : ∀ c ∈ lightSet,
      (3 * marginRatio + 2) * design.weight c
        ≤ marginRatio * (design.weight c * leverageOf (design.atom c)) := by
    intro c hc
    have hfloor := producer_forces_leverage_floor hmarginPos hproducer design hpattern
      hoffConic c (hlight c hc)
    have hwpos : 0 < design.weight c := design.weight_pos c
    nlinarith [hfloor, hwpos]
  have hsumLight :
      (3 * marginRatio + 2) * (∑ c ∈ lightSet, design.weight c)
        ≤ marginRatio * (∑ c ∈ lightSet, design.weight c * leverageOf (design.atom c)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hsubset :
      (∑ c ∈ lightSet, design.weight c * leverageOf (design.atom c))
        ≤ ∑ c, design.weight c * leverageOf (design.atom c) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro c _ _
    exact mul_nonneg (design.weight_pos c).le (leverageOf_nonneg _)
  rw [sum_weight_mul_leverage design] at hsubset
  norm_num at hsubset
  nlinarith [hsumLight, hsubset, hmarginPos]

/-! ## The refutations -/

/-- **THE REFUTATION FROM ONE WEIGHT.**  A line-free off-conic design carrying a
label whose weight is at most the dust threshold and at least
`marginRatio / (3 * marginRatio + 2)` kills the producer at those constants.  No
pair, no margin and no leverage is computed anywhere in the hypothesis. -/
theorem not_planeMarginProducer_of_weight_band {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (lightLabel : Fin 6) (hlight : design.weight lightLabel ≤ dustThreshold)
    (hband : marginRatio ≤ design.weight lightLabel * (3 * marginRatio + 2)) :
    ¬ PlaneMarginProducerAtLightLabel dustThreshold marginRatio := by
  intro hproducer
  have h := producer_forces_weight_ceiling hmarginPos hproducer design hpattern hoffConic
    lightLabel hlight
  linarith

/-- **THE REFUTATION FROM A BOUNDED LEVERAGE.**  The same kill read on the
leverage side, for a witness whose leverage is the convenient quantity. -/
theorem not_planeMarginProducer_of_bounded_light_leverage {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (lightLabel : Fin 6) (hlight : design.weight lightLabel ≤ dustThreshold)
    (hbounded : marginRatio * leverageOf (design.atom lightLabel)
      ≤ 3 * marginRatio + 2) :
    ¬ PlaneMarginProducerAtLightLabel dustThreshold marginRatio := by
  intro hproducer
  have h := producer_forces_leverage_floor hmarginPos hproducer design hpattern hoffConic
    lightLabel hlight
  linarith

/-- **NO DESIGN IS ENTIRELY LIGHT.**  The producer forces every line-free
off-conic design to carry a label of weight strictly above the dust threshold.
The proof takes the bulk bound at the whole label set, where the weights sum to
one and the bound reads `3 * marginRatio + 2 ≤ 3 * marginRatio`. -/
theorem producer_forces_heavy_label {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hproducer : PlaneMarginProducerAtLightLabel dustThreshold marginRatio)
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom) :
    ∃ c : Fin 6, dustThreshold < design.weight c := by
  by_contra hall
  push Not at hall
  have hbulk := producer_light_weight_sum_le hmarginPos hproducer design hpattern hoffConic
    Finset.univ (fun c _ => hall c)
  rw [design.weight_sum_one] at hbulk
  linarith

/-- **THE WHOLE-DESIGN REFUTATION.**  One line-free off-conic design all of whose
weights sit at or below the dust threshold refutes the producer outright, at every
positive margin ratio.  Such a design exists whenever the threshold reaches one
sixth, because six weights summing to one cannot all exceed one sixth. -/
theorem not_planeMarginProducer_of_all_weights_le {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hall : ∀ c : Fin 6, design.weight c ≤ dustThreshold) :
    ¬ PlaneMarginProducerAtLightLabel dustThreshold marginRatio := by
  intro hproducer
  obtain ⟨c, hc⟩ := producer_forces_heavy_label hmarginPos hproducer design hpattern hoffConic
  exact absurd (hall c) (not_le.mpr hc)

/-! ## The pair the gate keeps, and the pairs it cannot keep -/

/-- **NO PAIR AT ALL WORKS AT A LABEL OF BOUNDED LEVERAGE.**  The floor is a
statement about every pair at once, so a label whose leverage misses the floor
admits no admissible pair whatsoever.  This is the form a consumer needs: it
closes the existential rather than one instance of it. -/
theorem not_exists_planeMarginGate_of_bounded_leverage (design : WeightedDesign m 3)
    {insertLabel : Fin m} {marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hbounded : marginRatio * leverageOf (design.atom insertLabel)
      ≤ 3 * marginRatio + 2) :
    ¬ ∃ keptOne keptTwo : Fin m,
        PlaneMarginAt design keptOne keptTwo insertLabel marginRatio ∧
        leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
          < marginRatio * (leverageOf (design.atom insertLabel) - 1) := by
  rintro ⟨keptOne, keptTwo, hmargin, hgap⟩
  have h := planeMarginGate_insert_leverage_gt design hmarginPos hmargin hgap
  linarith

/-- **THE KEPT PAIR CANNOT BE TOO HEAVY.**  The floor bounds the kept leverages
from below while `weighted_leverage_le_one` bounds them from above by the inverse
weights, so the two kept weights satisfy a product inequality with no leverage in
it at all. -/
theorem keptPair_weight_product_le (design : WeightedDesign m 3)
    {keptOne keptTwo insertLabel : Fin m} {marginRatio : ℝ}
    (hatomPos : 0 < leverageOf (design.atom insertLabel))
    (hmargin : PlaneMarginAt design keptOne keptTwo insertLabel marginRatio) :
    2 * (1 + marginRatio) * (design.weight keptOne * design.weight keptTwo)
      ≤ design.weight keptOne + design.weight keptTwo := by
  have hfloor := planeMargin_kept_leverage_floor design hatomPos hmargin
  have hcapOne : design.weight keptOne * leverageOf (design.atom keptOne) ≤ 1 :=
    weighted_leverage_le_one design keptOne
  have hcapTwo : design.weight keptTwo * leverageOf (design.atom keptTwo) ≤ 1 :=
    weighted_leverage_le_one design keptTwo
  have hposOne : 0 < design.weight keptOne := design.weight_pos keptOne
  have hposTwo : 0 < design.weight keptTwo := design.weight_pos keptTwo
  -- Scale each leverage ceiling by the other weight, then add.
  have hscaledOne : design.weight keptTwo
      * (design.weight keptOne * leverageOf (design.atom keptOne))
      ≤ design.weight keptTwo * 1 :=
    mul_le_mul_of_nonneg_left hcapOne hposTwo.le
  have hscaledTwo : design.weight keptOne
      * (design.weight keptTwo * leverageOf (design.atom keptTwo))
      ≤ design.weight keptOne * 1 :=
    mul_le_mul_of_nonneg_left hcapTwo hposOne.le
  -- Scale the floor by the product of the two weights.
  have hprodPos : 0 < design.weight keptOne * design.weight keptTwo :=
    mul_pos hposOne hposTwo
  have hscaledFloor : design.weight keptOne * design.weight keptTwo
        * (2 * (1 + marginRatio))
      ≤ design.weight keptOne * design.weight keptTwo
        * (leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)) :=
    mul_le_mul_of_nonneg_left hfloor hprodPos.le
  nlinarith [hscaledOne, hscaledTwo, hscaledFloor]

/-- **THE DUST COLLAR INHERITS THE CEILING.**  Reading the producer's weight
ceiling against the dust threshold shows the producer is available only when the
threshold itself sits below `marginRatio / (3 * marginRatio + 2)`, or else the
design carries no light label for it to serve. -/
theorem producer_threshold_or_no_light_label {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hproducer : PlaneMarginProducerAtLightLabel dustThreshold marginRatio)
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (lightLabel : Fin 6) (hlight : design.weight lightLabel ≤ dustThreshold) :
    design.weight lightLabel * (3 * marginRatio + 2) < marginRatio
      ∧ 3 * marginRatio + 2 < marginRatio * leverageOf (design.atom lightLabel) :=
  ⟨producer_forces_weight_ceiling hmarginPos hproducer design hpattern hoffConic
      lightLabel hlight,
    producer_forces_leverage_floor hmarginPos hproducer design hpattern hoffConic
      lightLabel hlight⟩

/-- **THE SMALLEST WEIGHT IS ALWAYS AT MOST ONE SIXTH.**  Six positive weights
summing to one cannot all exceed one sixth, so the all-light hypothesis of the
whole-design refutation is reachable for every threshold at or above one sixth. -/
theorem exists_weight_le_sixth (design : WeightedDesign 6 3) :
    ∃ c : Fin 6, design.weight c ≤ 1 / 6 := by
  by_contra hall
  push Not at hall
  have hsum : (1 : ℝ) / 6 * 6 < ∑ c, design.weight c := by
    have := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
      (fun c (_ : c ∈ (Finset.univ : Finset (Fin 6))) => hall c)
    simpa using this
  rw [design.weight_sum_one] at hsum
  norm_num at hsum

end Gtz

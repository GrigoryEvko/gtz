import Gtz.Wave.WedgeLeakCriterion
import Gtz.Wave.KFourTriangleStallSharpening
import Gtz.Wave.OneLineSurvivorWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-
# The wedge balance, split at the flat labels

`Gtz.posDef_iff_normalSurplus_and_wedgeBalance` decides strict domination of ANY
subset at ANY unit normal by two data: a normal surplus, and the WEDGE BALANCE
`Gtz.WedgeBalanceAt` at every in-plane probe.  The balance is a difference of
three double sums of squared wedge shadows.  This file factors it.

THE SPLIT.  Take any set of labels FLAT at the normal.  A wedge shadow of two
flat labels vanishes, and a wedge shadow of a flat label against any other label
loses one of its two terms.  So each of the three totals breaks into a product
of two one-dimensional sums plus a total over the SHARP labels alone.  The three
products recombine, and what comes out is

  `inside + outside - crossing = (flat reading gap) * (sharp energy gap) + (sharp balance)`.

Both factors then simplify.  Weighted Parseval turns the sharp energy gap into
the plain NORMAL SURPLUS of the selected subset, with the flat labels gone.  The
weight deficit turns the flat reading gap into

  `(unweighted probe reading of the SELECTED flat labels) - (weighted probe leak of ALL flat labels)`.

That is `Gtz.flatSplitLead`.  Nothing here is rank three, nothing is size six,
and no pattern is named.

WHAT IT CORRECTS.  `Gtz.not_wedgeBeatsLeak_of_full_leak` says a full leak refuses
the criterion.  Read through the split, that obstruction lives ENTIRELY in the
case where the selected subset holds NO flat label, because only there is the
lead `-leak * surplus`, which is never positive.  A selected subset holding one
flat label pays `leak - reading` instead, and that quantity has NO sign.  The
averaging law `Gtz.sum_weight_mul_flatReading_sub_flatLeak` proves the payment is
negative for SOME flat label at every probe whose leak is positive.  So the leak
floor obstructs the free triple and nothing else.

THE ONE-LINE READING.  At the one-line pattern the flat set is the line.  The
free triple has empty flat part, and the split reproduces the landed
`Gtz.planeCover_iff_wedgeTotal_gt_surplus_mul_leak`.  Each of the nine MIXED
triples has one line atom and two free atoms, and its balance is

  `((a_i . p)^2 - leak) * ((a_x . n)^2 + (a_y . n)^2 - 1)
     + d_x d_y W(x,y)^2 - w_z (d_x W(x,z)^2 + d_y W(y,z)^2)`

with `z` the omitted free atom.  Every term is a polynomial in the design.

THE WEAK DOMINATOR.  A card-three weak dominator meets the line in three, two,
one or zero labels.  Three is refused by `Gtz.not_dominates_of_coplanar_triple`.
Two is `Gtz.planePair_sq_of_dominates`: the flat pair covers the whole plane, and
its pair gap excess is nonnegative unless the two atoms are dependent.  One and
zero give the normal surplus of the free part.
-/

namespace Gtz

open Finset Matrix

/-! ## 1.  The wedge total on two supports

`Gtz.wedgeTotal` runs one support against itself and halves.  `Gtz.mixedWedgeTotal`
runs a subset against its complement.  Both are instances of one object, and the
landed `Gtz.sum_sum_wedgeSq_eq_lagrange_pair` already evaluates it. -/

/-- The measure-weighted wedge total across two supports, with a measure on each
side.  `Gtz.wedgeTotal` is the halved diagonal case and `Gtz.mixedWedgeTotal` is
the subset against complement case. -/
noncomputable def crossWedgeTotal {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ)
    (leftSupport rightSupport : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) : ℝ :=
  ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
    leftMeasure leftLabel * rightMeasure rightLabel
      * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2

theorem wedgeTotal_eq_crossWedgeTotal {size rank : ℕ} (design : WeightedDesign size rank)
    (measure : Fin size → ℝ) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    wedgeTotal design measure selected normalVec probeVec
      = crossWedgeTotal design measure measure selected selected normalVec probeVec / 2 :=
  rfl

theorem mixedWedgeTotal_eq_crossWedgeTotal {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ) :
    mixedWedgeTotal design selected normalVec probeVec
      = crossWedgeTotal design (weightDeficit design) design.weight selected selectedᶜ
          normalVec probeVec :=
  rfl

theorem crossWedgeTotal_empty_left {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ) (rightSupport : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    crossWedgeTotal design leftMeasure rightMeasure ∅ rightSupport normalVec probeVec = 0 := by
  simp [crossWedgeTotal]

theorem crossWedgeTotal_empty_right {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ) (leftSupport : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    crossWedgeTotal design leftMeasure rightMeasure leftSupport ∅ normalVec probeVec = 0 := by
  simp [crossWedgeTotal]

theorem wedgeTotal_empty {size rank : ℕ} (design : WeightedDesign size rank)
    (measure : Fin size → ℝ) (normalVec probeVec : Fin rank → ℝ) :
    wedgeTotal design measure ∅ normalVec probeVec = 0 := by
  simp [wedgeTotal]

theorem wedgeTotal_singleton {size rank : ℕ} (design : WeightedDesign size rank)
    (measure : Fin size → ℝ) (label : Fin size) (normalVec probeVec : Fin rank → ℝ) :
    wedgeTotal design measure {label} normalVec probeVec = 0 := by
  simp [wedgeTotal, wedgeShadow_self]

/-- On a pair the wedge total is the single unordered pair term. -/
theorem wedgeTotal_pair {size rank : ℕ} (design : WeightedDesign size rank)
    (measure : Fin size → ℝ) {leftLabel rightLabel : Fin size}
    (hdistinct : leftLabel ≠ rightLabel) (normalVec probeVec : Fin rank → ℝ) :
    wedgeTotal design measure {leftLabel, rightLabel} normalVec probeVec
      = measure leftLabel * measure rightLabel
        * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2 := by
  rw [wedgeTotal, Finset.sum_pair hdistinct]
  rw [Finset.sum_pair hdistinct, Finset.sum_pair hdistinct]
  rw [wedgeShadow_self, wedgeShadow_self,
    wedgeShadow_swap design normalVec probeVec leftLabel rightLabel]
  ring

/-- A right support with one label collapses the cross total to a single sum. -/
theorem crossWedgeTotal_singleton_right {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ) (leftSupport : Finset (Fin size))
    (rightLabel : Fin size) (normalVec probeVec : Fin rank → ℝ) :
    crossWedgeTotal design leftMeasure rightMeasure leftSupport {rightLabel} normalVec probeVec
      = ∑ leftLabel ∈ leftSupport, leftMeasure leftLabel * rightMeasure rightLabel
          * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2 := by
  simp [crossWedgeTotal]

/-! ## 2.  Flat labels lose their wedge

A label FLAT at the normal reads it as zero.  Two flat labels wedge to zero, and
a flat label against a sharp one keeps only the sharp normal reading times the
flat probe reading. -/

theorem wedgeShadow_eq_zero_of_flat_flat {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec probeVec : Fin rank → ℝ) {leftLabel rightLabel : Fin size}
    (hleft : design.atom leftLabel ⬝ᵥ normalVec = 0)
    (hright : design.atom rightLabel ⬝ᵥ normalVec = 0) :
    wedgeShadow design normalVec probeVec leftLabel rightLabel = 0 := by
  unfold wedgeShadow
  rw [hleft, hright]
  ring

/-- The wedge square with a FLAT left label. -/
theorem wedgeShadow_sq_of_left_flat {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec probeVec : Fin rank → ℝ) {leftLabel : Fin size} (rightLabel : Fin size)
    (hleft : design.atom leftLabel ⬝ᵥ normalVec = 0) :
    wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2
      = (design.atom leftLabel ⬝ᵥ probeVec) ^ 2
        * (design.atom rightLabel ⬝ᵥ normalVec) ^ 2 := by
  unfold wedgeShadow
  rw [hleft]
  ring

/-- The wedge square with a FLAT right label. -/
theorem wedgeShadow_sq_of_right_flat {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec probeVec : Fin rank → ℝ) (leftLabel : Fin size) {rightLabel : Fin size}
    (hright : design.atom rightLabel ⬝ᵥ normalVec = 0) :
    wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2
      = (design.atom leftLabel ⬝ᵥ normalVec) ^ 2
        * (design.atom rightLabel ⬝ᵥ probeVec) ^ 2 := by
  unfold wedgeShadow
  rw [hright]
  ring

/-- Two flat supports carry no wedge at all. -/
theorem crossWedgeTotal_eq_zero_of_flat {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ)
    {leftSupport rightSupport : Finset (Fin size)} (normalVec probeVec : Fin rank → ℝ)
    (hleft : ∀ label ∈ leftSupport, design.atom label ⬝ᵥ normalVec = 0)
    (hright : ∀ label ∈ rightSupport, design.atom label ⬝ᵥ normalVec = 0) :
    crossWedgeTotal design leftMeasure rightMeasure leftSupport rightSupport
        normalVec probeVec = 0 := by
  refine Finset.sum_eq_zero fun leftLabel hleftMem => Finset.sum_eq_zero fun rightLabel hrightMem =>
    ?_
  rw [wedgeShadow_eq_zero_of_flat_flat design normalVec probeVec (hleft leftLabel hleftMem)
    (hright rightLabel hrightMem)]
  ring

/-- A FLAT left support factors the cross total into probe energy times normal
energy. -/
theorem crossWedgeTotal_of_left_flat {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ)
    {leftSupport : Finset (Fin size)} (rightSupport : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ)
    (hleft : ∀ label ∈ leftSupport, design.atom label ⬝ᵥ normalVec = 0) :
    crossWedgeTotal design leftMeasure rightMeasure leftSupport rightSupport normalVec probeVec
      = (∑ label ∈ leftSupport, leftMeasure label * (design.atom label ⬝ᵥ probeVec) ^ 2)
        * ∑ label ∈ rightSupport, rightMeasure label
            * (design.atom label ⬝ᵥ normalVec) ^ 2 := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun leftLabel hleftMem => Finset.sum_congr rfl fun rightLabel _ => ?_
  rw [wedgeShadow_sq_of_left_flat design normalVec probeVec rightLabel (hleft leftLabel hleftMem)]
  ring

/-- A FLAT right support factors the cross total the other way. -/
theorem crossWedgeTotal_of_right_flat {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ)
    (leftSupport : Finset (Fin size)) {rightSupport : Finset (Fin size)}
    (normalVec probeVec : Fin rank → ℝ)
    (hright : ∀ label ∈ rightSupport, design.atom label ⬝ᵥ normalVec = 0) :
    crossWedgeTotal design leftMeasure rightMeasure leftSupport rightSupport normalVec probeVec
      = (∑ label ∈ leftSupport, leftMeasure label * (design.atom label ⬝ᵥ normalVec) ^ 2)
        * ∑ label ∈ rightSupport, rightMeasure label
            * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun leftLabel _ => Finset.sum_congr rfl fun rightLabel hrightMem => ?_
  rw [wedgeShadow_sq_of_right_flat design normalVec probeVec leftLabel (hright rightLabel hrightMem)]
  ring

/-! ## 3.  Splitting a support at the flat set -/

/-- The generic support split, on the left. -/
theorem crossWedgeTotal_split_left {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ)
    (leftSupport rightSupport flatSet : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    crossWedgeTotal design leftMeasure rightMeasure leftSupport rightSupport normalVec probeVec
      = crossWedgeTotal design leftMeasure rightMeasure (leftSupport \ flatSet) rightSupport
            normalVec probeVec
        + crossWedgeTotal design leftMeasure rightMeasure (leftSupport ∩ flatSet) rightSupport
            normalVec probeVec := by
  classical
  have hsplit := Finset.sum_sdiff
    (f := fun leftLabel => ∑ rightLabel ∈ rightSupport,
      leftMeasure leftLabel * rightMeasure rightLabel
        * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2)
    (Finset.inter_subset_left (s₁ := leftSupport) (s₂ := flatSet))
  rw [Finset.sdiff_inter_self_left] at hsplit
  exact hsplit.symm

/-- The generic support split, on the right. -/
theorem crossWedgeTotal_split_right {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ)
    (leftSupport rightSupport flatSet : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    crossWedgeTotal design leftMeasure rightMeasure leftSupport rightSupport normalVec probeVec
      = crossWedgeTotal design leftMeasure rightMeasure leftSupport (rightSupport \ flatSet)
            normalVec probeVec
        + crossWedgeTotal design leftMeasure rightMeasure leftSupport (rightSupport ∩ flatSet)
            normalVec probeVec := by
  classical
  unfold crossWedgeTotal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun leftLabel _ => ?_
  have hsplit := Finset.sum_sdiff
    (f := fun rightLabel => leftMeasure leftLabel * rightMeasure rightLabel
      * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2)
    (Finset.inter_subset_left (s₁ := rightSupport) (s₂ := flatSet))
  rw [Finset.sdiff_inter_self_left] at hsplit
  exact hsplit.symm

/-- **THE WEDGE TOTAL, SPLIT AT THE FLAT SET.**  The flat part of the support
contributes one product, and the sharp part keeps its own wedge total. -/
theorem wedgeTotal_flatSplit {size rank : ℕ} (design : WeightedDesign size rank)
    (measure : Fin size → ℝ) (selected flatSet : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    wedgeTotal design measure selected normalVec probeVec
      = (∑ label ∈ selected ∩ flatSet, measure label * (design.atom label ⬝ᵥ probeVec) ^ 2)
          * (∑ label ∈ selected \ flatSet, measure label
              * (design.atom label ⬝ᵥ normalVec) ^ 2)
        + wedgeTotal design measure (selected \ flatSet) normalVec probeVec := by
  classical
  have hflatSub : ∀ label ∈ selected ∩ flatSet, design.atom label ⬝ᵥ normalVec = 0 :=
    fun label hmem => hflat label (Finset.mem_of_mem_inter_right hmem)
  rw [wedgeTotal_eq_crossWedgeTotal, wedgeTotal_eq_crossWedgeTotal]
  rw [crossWedgeTotal_split_left design measure measure selected selected flatSet normalVec probeVec]
  rw [crossWedgeTotal_split_right design measure measure (selected \ flatSet) selected flatSet
      normalVec probeVec,
    crossWedgeTotal_split_right design measure measure (selected ∩ flatSet) selected flatSet
      normalVec probeVec]
  rw [crossWedgeTotal_eq_zero_of_flat design measure measure normalVec probeVec hflatSub hflatSub]
  rw [crossWedgeTotal_of_right_flat design measure measure (selected \ flatSet) normalVec probeVec
      hflatSub,
    crossWedgeTotal_of_left_flat design measure measure (selected \ flatSet) normalVec probeVec
      hflatSub]
  ring

/-- **THE CROSSING TOTAL, SPLIT AT THE FLAT SET.** -/
theorem mixedWedgeTotal_flatSplit {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    mixedWedgeTotal design selected normalVec probeVec
      = (∑ label ∈ selected ∩ flatSet, weightDeficit design label
            * (design.atom label ⬝ᵥ probeVec) ^ 2)
          * (∑ label ∈ selectedᶜ \ flatSet, design.weight label
              * (design.atom label ⬝ᵥ normalVec) ^ 2)
        + (∑ label ∈ selectedᶜ ∩ flatSet, design.weight label
              * (design.atom label ⬝ᵥ probeVec) ^ 2)
          * (∑ label ∈ selected \ flatSet, weightDeficit design label
              * (design.atom label ⬝ᵥ normalVec) ^ 2)
        + crossWedgeTotal design (weightDeficit design) design.weight
            (selected \ flatSet) (selectedᶜ \ flatSet) normalVec probeVec := by
  classical
  have hleftFlat : ∀ label ∈ selected ∩ flatSet, design.atom label ⬝ᵥ normalVec = 0 :=
    fun label hmem => hflat label (Finset.mem_of_mem_inter_right hmem)
  have hrightFlat : ∀ label ∈ selectedᶜ ∩ flatSet, design.atom label ⬝ᵥ normalVec = 0 :=
    fun label hmem => hflat label (Finset.mem_of_mem_inter_right hmem)
  rw [mixedWedgeTotal_eq_crossWedgeTotal]
  rw [crossWedgeTotal_split_left design (weightDeficit design) design.weight selected selectedᶜ
      flatSet normalVec probeVec]
  rw [crossWedgeTotal_split_right design (weightDeficit design) design.weight
      (selected \ flatSet) selectedᶜ flatSet normalVec probeVec,
    crossWedgeTotal_split_right design (weightDeficit design) design.weight
      (selected ∩ flatSet) selectedᶜ flatSet normalVec probeVec]
  rw [crossWedgeTotal_eq_zero_of_flat design (weightDeficit design) design.weight normalVec probeVec
      hleftFlat hrightFlat]
  rw [crossWedgeTotal_of_right_flat design (weightDeficit design) design.weight
      (selected \ flatSet) normalVec probeVec hrightFlat,
    crossWedgeTotal_of_left_flat design (weightDeficit design) design.weight
      (selectedᶜ \ flatSet) normalVec probeVec hleftFlat]
  ring

/-! ## 4.  The master split

Three splits recombine into a product of two differences plus the balance of the
SHARP labels alone.  No positivity, no normalization, no rank. -/

/-- The wedge balance, written as a signed quantity. -/
noncomputable def wedgeBalanceValue {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ) : ℝ :=
  wedgeTotal design (weightDeficit design) selected normalVec probeVec
    + wedgeTotal design design.weight selectedᶜ normalVec probeVec
    - mixedWedgeTotal design selected normalVec probeVec

theorem wedgeBalanceAt_iff_pos_wedgeBalanceValue {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    WedgeBalanceAt design selected normalVec probeVec
      ↔ 0 < wedgeBalanceValue design selected normalVec probeVec := by
  unfold WedgeBalanceAt wedgeBalanceValue
  constructor <;> intro h <;> linarith

/-- The balance carried by the SHARP labels alone. -/
noncomputable def sharpBalanceValue {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ) : ℝ :=
  wedgeTotal design (weightDeficit design) (selected \ flatSet) normalVec probeVec
    + wedgeTotal design design.weight (selectedᶜ \ flatSet) normalVec probeVec
    - crossWedgeTotal design (weightDeficit design) design.weight
        (selected \ flatSet) (selectedᶜ \ flatSet) normalVec probeVec

/-- **THE MASTER SPLIT.**  The wedge balance factors into a product of a probe
difference and a normal difference, plus the sharp balance.  The only hypothesis
is that the named set is flat at the normal. -/
theorem wedgeBalanceValue_flatSplit {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    wedgeBalanceValue design selected normalVec probeVec
      = ((∑ label ∈ selected ∩ flatSet, weightDeficit design label
              * (design.atom label ⬝ᵥ probeVec) ^ 2)
            - ∑ label ∈ selectedᶜ ∩ flatSet, design.weight label
                * (design.atom label ⬝ᵥ probeVec) ^ 2)
          * ((∑ label ∈ selected \ flatSet, weightDeficit design label
                * (design.atom label ⬝ᵥ normalVec) ^ 2)
              - ∑ label ∈ selectedᶜ \ flatSet, design.weight label
                  * (design.atom label ⬝ᵥ normalVec) ^ 2)
        + sharpBalanceValue design selected flatSet normalVec probeVec := by
  unfold wedgeBalanceValue sharpBalanceValue
  rw [wedgeTotal_flatSplit design (weightDeficit design) selected flatSet normalVec probeVec hflat,
    wedgeTotal_flatSplit design design.weight selectedᶜ flatSet normalVec probeVec hflat,
    mixedWedgeTotal_flatSplit design selected flatSet normalVec probeVec hflat]
  ring

/-! ## 5.  The normal factor is the plain normal surplus

Dropping the flat labels costs nothing at the normal, and weighted Parseval then
removes the whole weight measure.  The second factor of the master split carries
no weight and no deficit at all. -/

/-- A normal-energy sum ignores the flat labels. -/
theorem sum_sdiff_flat_normalSq {size rank : ℕ} (design : WeightedDesign size rank)
    (support flatSet : Finset (Fin size)) (normalVec : Fin rank → ℝ)
    (coefficient : Fin size → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    ∑ label ∈ support \ flatSet, coefficient label * (design.atom label ⬝ᵥ normalVec) ^ 2
      = ∑ label ∈ support, coefficient label * (design.atom label ⬝ᵥ normalVec) ^ 2 := by
  classical
  have hsplit := Finset.sum_sdiff
    (f := fun label => coefficient label * (design.atom label ⬝ᵥ normalVec) ^ 2)
    (Finset.inter_subset_left (s₁ := support) (s₂ := flatSet))
  rw [Finset.sdiff_inter_self_left] at hsplit
  have hzero : ∑ label ∈ support ∩ flatSet,
      coefficient label * (design.atom label ⬝ᵥ normalVec) ^ 2 = 0 :=
    Finset.sum_eq_zero fun label hmem => by
      rw [hflat label (Finset.mem_of_mem_inter_right hmem)]; ring
  rw [hzero, add_zero] at hsplit
  exact hsplit

/-- **THE SHARP NORMAL GAP IS THE NORMAL SURPLUS.**  The second factor of the
master split is the unweighted normal surplus of the whole selected subset.  No
weight, no deficit, and no flat label survives in it. -/
theorem sharpNormalGap_eq_normalSurplus {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (normalVec : Fin rank → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    (∑ label ∈ selected \ flatSet, weightDeficit design label
          * (design.atom label ⬝ᵥ normalVec) ^ 2)
        - ∑ label ∈ selectedᶜ \ flatSet, design.weight label
            * (design.atom label ⬝ᵥ normalVec) ^ 2
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec := by
  classical
  rw [sum_sdiff_flat_normalSq design selected flatSet normalVec (weightDeficit design) hflat,
    sum_sdiff_flat_normalSq design selectedᶜ flatSet normalVec design.weight hflat]
  have hdeficit : ∑ label ∈ selected, weightDeficit design label
        * (design.atom label ⬝ᵥ normalVec) ^ 2
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2)
        - ∑ label ∈ selected, design.weight label
            * (design.atom label ⬝ᵥ normalVec) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by unfold weightDeficit; ring
  have hparseval := dotProduct_self_eq_sum_weight_mul_sq design normalVec
  have hcompl := Finset.sum_add_sum_compl selected
    (fun label => design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2)
  rw [hdeficit]
  linarith [hparseval, hcompl]

/-! ## 6.  The probe factor is a reading against the flat leak -/

/-- The weight the FLAT labels spend on a probe.  It is the landed
`Gtz.complementLeak` of the flat set's complement, so it is one object, not a
second one. -/
noncomputable def flatLeak {size rank : ℕ} (design : WeightedDesign size rank)
    (flatSet : Finset (Fin size)) (probeVec : Fin rank → ℝ) : ℝ :=
  complementLeak design flatSetᶜ probeVec

theorem flatLeak_eq_sum {size rank : ℕ} (design : WeightedDesign size rank)
    (flatSet : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    flatLeak design flatSet probeVec
      = ∑ label ∈ flatSet, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
  unfold flatLeak complementLeak
  rw [compl_compl]

theorem flatLeak_nonneg {size rank : ℕ} (design : WeightedDesign size rank)
    (flatSet : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    0 ≤ flatLeak design flatSet probeVec :=
  complementLeak_nonneg design flatSetᶜ probeVec

/-- **THE PROBE FACTOR.**  The first factor of the master split is the plain
unweighted probe reading of the SELECTED flat labels, minus the weighted leak of
ALL the flat labels. -/
theorem flatProbeGap_eq_reading_sub_flatLeak {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    (∑ label ∈ selected ∩ flatSet, weightDeficit design label
          * (design.atom label ⬝ᵥ probeVec) ^ 2)
        - ∑ label ∈ selectedᶜ ∩ flatSet, design.weight label
            * (design.atom label ⬝ᵥ probeVec) ^ 2
      = (∑ label ∈ selected ∩ flatSet, (design.atom label ⬝ᵥ probeVec) ^ 2)
        - flatLeak design flatSet probeVec := by
  classical
  have hdeficit : ∑ label ∈ selected ∩ flatSet, weightDeficit design label
        * (design.atom label ⬝ᵥ probeVec) ^ 2
      = (∑ label ∈ selected ∩ flatSet, (design.atom label ⬝ᵥ probeVec) ^ 2)
        - ∑ label ∈ selected ∩ flatSet, design.weight label
            * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by unfold weightDeficit; ring
  have hsplit := Finset.sum_sdiff
    (f := fun label => design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)
    (Finset.inter_subset_left (s₁ := flatSet) (s₂ := selected))
  rw [Finset.sdiff_inter_self_left] at hsplit
  have hleftSwap : flatSet ∩ selected = selected ∩ flatSet := Finset.inter_comm _ _
  have hrightSwap : flatSet \ selected = selectedᶜ ∩ flatSet := by
    rw [Finset.sdiff_eq_inter_compl, Finset.inter_comm]
  rw [hleftSwap, hrightSwap] at hsplit
  rw [hdeficit, flatLeak_eq_sum]
  linarith [hsplit]

/-! ## 7.  The master reading -/

/-- The LEAD of the flat split: the selected flat labels read the probe, and pay
the whole flat leak for it.  The free triple of a one-line design has an EMPTY
selected flat part, so its lead is minus the leak. -/
noncomputable def flatSplitLead {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (probeVec : Fin rank → ℝ) : ℝ :=
  (∑ label ∈ selected ∩ flatSet, (design.atom label ⬝ᵥ probeVec) ^ 2)
    - flatLeak design flatSet probeVec

/-- **THE FLAT SPLIT, READ.**  The wedge balance of any subset at any normal is
the LEAD times the NORMAL SURPLUS, plus the balance of the sharp labels.  The
only hypothesis is flatness of the named set. -/
theorem wedgeBalanceValue_flatSplit_reading {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    wedgeBalanceValue design selected normalVec probeVec
      = flatSplitLead design selected flatSet probeVec
          * ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2)
              - normalVec ⬝ᵥ normalVec)
        + sharpBalanceValue design selected flatSet normalVec probeVec := by
  rw [wedgeBalanceValue_flatSplit design selected flatSet normalVec probeVec hflat,
    flatProbeGap_eq_reading_sub_flatLeak design selected flatSet probeVec,
    sharpNormalGap_eq_normalSurplus design selected flatSet normalVec hflat]
  rfl

/-- **STRICT DOMINATION, DECIDED BY THE FLAT SPLIT.**  At any rank, any subset
and any unit normal with a named flat set, the gap is positive definite exactly
when the normal surplus is positive and the split value is positive at every
in-plane probe. -/
theorem posDef_iff_flatSplitBalance {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (unitNormal : Fin rank → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ unitNormal = 0) :
    (subsetSum design selected - 1).PosDef
      ↔ (1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
        ∧ ∀ probeVec : Fin rank → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
            0 < flatSplitLead design selected flatSet probeVec
                  * ((∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2) - 1)
                + sharpBalanceValue design selected flatSet unitNormal probeVec := by
  rw [posDef_iff_normalSurplus_and_wedgeBalance design selected unitNormal hunit]
  constructor
  · rintro ⟨hsurplus, hbalance⟩
    refine ⟨hsurplus, fun probeVec horthogonal hprobeNe => ?_⟩
    have hvalue := (wedgeBalanceAt_iff_pos_wedgeBalanceValue design selected unitNormal
      probeVec).mp (hbalance probeVec horthogonal hprobeNe)
    rw [wedgeBalanceValue_flatSplit_reading design selected flatSet unitNormal probeVec hflat,
      hunit] at hvalue
    exact hvalue
  · rintro ⟨hsurplus, hsplit⟩
    refine ⟨hsurplus, fun probeVec horthogonal hprobeNe => ?_⟩
    refine (wedgeBalanceAt_iff_pos_wedgeBalanceValue design selected unitNormal probeVec).mpr ?_
    rw [wedgeBalanceValue_flatSplit_reading design selected flatSet unitNormal probeVec hflat,
      hunit]
    exact hsplit probeVec horthogonal hprobeNe

/-! ## 8.  The flat leak is beaten on average

The lead asks a selected flat label to read the probe above the WHOLE flat leak.
The weights of the flat set sum to less than one whenever one label sits outside
it, and that alone makes the demand satisfiable at every probe. -/

/-- The weights of a proper subset sum to strictly less than one. -/
theorem sum_weight_lt_one_of_notMem {size rank : ℕ} (design : WeightedDesign size rank)
    {flatSet : Finset (Fin size)} {outsideLabel : Fin size} (houtside : outsideLabel ∉ flatSet) :
    ∑ label ∈ flatSet, design.weight label < 1 := by
  classical
  have hsplit := Finset.sum_add_sum_compl flatSet design.weight
  have htotal := design.weight_sum_one
  have hcomplPos : 0 < ∑ label ∈ flatSetᶜ, design.weight label :=
    Finset.sum_pos (fun label _ => design.weight_pos label)
      ⟨outsideLabel, Finset.mem_compl.mpr houtside⟩
  linarith [hsplit, htotal, hcomplPos]

/-- **THE AVERAGING LAW OF THE FLAT LEAK.**  Weighting each flat label's payment
by its own weight leaves exactly the leak times the weight the flat set does not
own.  No hypothesis. -/
theorem sum_weight_mul_flatReading_sub_flatLeak {size rank : ℕ}
    (design : WeightedDesign size rank) (flatSet : Finset (Fin size))
    (probeVec : Fin rank → ℝ) :
    ∑ label ∈ flatSet, design.weight label
        * ((design.atom label ⬝ᵥ probeVec) ^ 2 - flatLeak design flatSet probeVec)
      = (1 - ∑ label ∈ flatSet, design.weight label) * flatLeak design flatSet probeVec := by
  have hexpand : ∑ label ∈ flatSet, design.weight label
        * ((design.atom label ⬝ᵥ probeVec) ^ 2 - flatLeak design flatSet probeVec)
      = (∑ label ∈ flatSet, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)
        - (∑ label ∈ flatSet, design.weight label) * flatLeak design flatSet probeVec := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by ring
  rw [hexpand, ← flatLeak_eq_sum]
  ring

/-- **SOME FLAT LABEL BEATS THE LEAK.**  At every probe carrying a positive flat
leak, one flat label reads that probe strictly above the whole leak.  So the LEAD
of the flat split is positive for SOME choice of selected flat label, at every
probe separately.  The choice is probe-dependent. -/
theorem exists_flatLabel_flatLeak_lt {size rank : ℕ} (design : WeightedDesign size rank)
    {flatSet : Finset (Fin size)} {outsideLabel : Fin size} (houtside : outsideLabel ∉ flatSet)
    {probeVec : Fin rank → ℝ} (hleak : 0 < flatLeak design flatSet probeVec) :
    ∃ flatLabel ∈ flatSet,
      flatLeak design flatSet probeVec < (design.atom flatLabel ⬝ᵥ probeVec) ^ 2 := by
  classical
  by_contra hcontra
  have hall : ∀ label ∈ flatSet,
      (design.atom label ⬝ᵥ probeVec) ^ 2 ≤ flatLeak design flatSet probeVec := by
    intro label hmem
    by_contra hlt
    exact hcontra ⟨label, hmem, lt_of_not_ge hlt⟩
  have hnonpos : ∑ label ∈ flatSet, design.weight label
      * ((design.atom label ⬝ᵥ probeVec) ^ 2 - flatLeak design flatSet probeVec) ≤ 0 :=
    Finset.sum_nonpos fun label hmem => by
      nlinarith [design.weight_pos label, hall label hmem]
  rw [sum_weight_mul_flatReading_sub_flatLeak design flatSet probeVec] at hnonpos
  have hweight := sum_weight_lt_one_of_notMem design houtside
  nlinarith [hnonpos, hleak, hweight]

/-! ## 9.  Where the leak floor obstructs, and where it does not

`Gtz.not_wedgeBeatsLeak_of_full_leak` refuses the criterion when the leak is full.
Its hypothesis is that the COMPLEMENT of the selected subset is flat at the
normal, which at a fixed flat set means `flatSetᶜ ⊆ selected`.  At equal cardinal
that pins the selected subset to `flatSetᶜ`, whose lead is minus the leak.  Every
other selected subset pays a lead with no sign. -/

/-- A selected subset disjoint from the flat set has lead exactly minus the
leak. -/
theorem flatSplitLead_eq_neg_flatLeak_of_disjoint {size rank : ℕ}
    (design : WeightedDesign size rank) {selected flatSet : Finset (Fin size)}
    (hdisjoint : selected ∩ flatSet = ∅) (probeVec : Fin rank → ℝ) :
    flatSplitLead design selected flatSet probeVec = -flatLeak design flatSet probeVec := by
  unfold flatSplitLead
  rw [hdisjoint, Finset.sum_empty]
  ring

theorem flatSplitLead_nonpos_of_disjoint {size rank : ℕ}
    (design : WeightedDesign size rank) {selected flatSet : Finset (Fin size)}
    (hdisjoint : selected ∩ flatSet = ∅) (probeVec : Fin rank → ℝ) :
    flatSplitLead design selected flatSet probeVec ≤ 0 := by
  rw [flatSplitLead_eq_neg_flatLeak_of_disjoint design hdisjoint probeVec]
  linarith [flatLeak_nonneg design flatSet probeVec]

/-- **THE BLIND COMPLEMENT PINS THE SELECTED SUBSET.**  A selected subset whose
complement lies in the flat set, and whose cardinal matches, IS the flat set's
complement.  This is the exact locus of the section-seven obstruction. -/
theorem eq_compl_of_compl_subset_of_card {size : ℕ} {selected flatSet : Finset (Fin size)}
    (hsubset : flatSetᶜ ⊆ selected) (hcard : selected.card = flatSetᶜ.card) :
    selected = flatSetᶜ :=
  (Finset.eq_of_subset_of_card_le hsubset (le_of_eq hcard)).symm

/-- With every sharp label selected, the outside sharp part is empty and the
sharp balance is one nonnegative wedge total. -/
theorem sharpBalanceValue_eq_of_compl_subset {size rank : ℕ} (design : WeightedDesign size rank)
    {selected flatSet : Finset (Fin size)} (hsubset : flatSetᶜ ⊆ selected)
    (normalVec probeVec : Fin rank → ℝ) :
    sharpBalanceValue design selected flatSet normalVec probeVec
      = wedgeTotal design (weightDeficit design) (selected \ flatSet) normalVec probeVec := by
  classical
  have hempty : selectedᶜ \ flatSet = ∅ := by
    rw [Finset.sdiff_eq_inter_compl, Finset.eq_empty_iff_forall_notMem]
    intro label hmem
    rw [Finset.mem_inter, Finset.mem_compl, Finset.mem_compl] at hmem
    exact hmem.1 (hsubset (Finset.mem_compl.mpr hmem.2))
  unfold sharpBalanceValue
  rw [hempty, wedgeTotal_empty, crossWedgeTotal_empty_right]
  ring

theorem sharpBalanceValue_nonneg_of_compl_subset {size rank : ℕ}
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    {selected flatSet : Finset (Fin size)} (hsubset : flatSetᶜ ⊆ selected)
    (normalVec probeVec : Fin rank → ℝ) :
    0 ≤ sharpBalanceValue design selected flatSet normalVec probeVec := by
  rw [sharpBalanceValue_eq_of_compl_subset design hsubset normalVec probeVec]
  exact wedgeTotal_nonneg design (weightDeficit design) (selected \ flatSet) normalVec probeVec
    fun label _ => (weightDeficit_pos design hsize label).le

/-- **THE PRODUCER.**  A positive lead, a positive normal surplus and a
nonnegative sharp balance give the wedge balance.  The lead is where a selected
flat label pays for itself, and it is the only term the leak enters. -/
theorem wedgeBalanceAt_of_flatSplitLead_pos {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (unitNormal probeVec : Fin rank → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ unitNormal = 0)
    (hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
    (hlead : 0 < flatSplitLead design selected flatSet probeVec)
    (hsharp : 0 ≤ sharpBalanceValue design selected flatSet unitNormal probeVec) :
    WedgeBalanceAt design selected unitNormal probeVec := by
  refine (wedgeBalanceAt_iff_pos_wedgeBalanceValue design selected unitNormal probeVec).mpr ?_
  rw [wedgeBalanceValue_flatSplit_reading design selected flatSet unitNormal probeVec hflat, hunit]
  nlinarith [hlead, hsurplus, hsharp]

/-! ## 10.  A WEAK dominator with a flat pair covers the whole plane

Every landed in-plane covering law of a flat pair starts from a POSITIVE
DEFINITE gap.  The obligation supplies only a weak dominator.  This section runs
the argument from `Gtz.Dominates` alone.

The probe is tilted out of the plane by exactly the amount that annihilates the
third atom, and no division is needed: scale the tilt by the third atom's own
normal reading. -/

/-- **THE FLAT-PAIR PLANE LAW, FROM A WEAK DOMINATOR.**  Division free, at every
rank and every size.  The third atom pays its own squared probe reading on the
left, so the inequality is strictly stronger than plain plane covering. -/
theorem planePair_sq_of_dominates {size rank : ℕ} (design : WeightedDesign size rank)
    {flatFirst flatSecond freeLabel : Fin size}
    (hFirstSecond : flatFirst ≠ flatSecond) (hFirstFree : flatFirst ≠ freeLabel)
    (hSecondFree : flatSecond ≠ freeLabel)
    (unitNormal probeVec : Fin rank → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hprobe : probeVec ⬝ᵥ unitNormal = 0)
    (hFirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hSecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hdominates : Dominates design {flatFirst, flatSecond, freeLabel}) :
    (probeVec ⬝ᵥ probeVec) * (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2
        + (design.atom freeLabel ⬝ᵥ probeVec) ^ 2
      ≤ (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2
        * ((design.atom flatFirst ⬝ᵥ probeVec) ^ 2
            + (design.atom flatSecond ⬝ᵥ probeVec) ^ 2) := by
  classical
  set freeNormal : ℝ := design.atom freeLabel ⬝ᵥ unitNormal with hfreeNormal
  set freeProbe : ℝ := design.atom freeLabel ⬝ᵥ probeVec with hfreeProbe
  set tilt : Fin rank → ℝ := freeNormal • probeVec - freeProbe • unitNormal with htilt
  have hread : ∀ label : Fin size, design.atom label ⬝ᵥ tilt
      = freeNormal * (design.atom label ⬝ᵥ probeVec)
        - freeProbe * (design.atom label ⬝ᵥ unitNormal) := by
    intro label
    rw [htilt, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hnormalProbe : unitNormal ⬝ᵥ probeVec = 0 := by rw [dotProduct_comm]; exact hprobe
  have hself : tilt ⬝ᵥ tilt = freeNormal ^ 2 * (probeVec ⬝ᵥ probeVec) + freeProbe ^ 2 := by
    rw [htilt]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hunit, hprobe, hnormalProbe]
    ring
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 tilt
  rw [star_trivial, dotProduct_subsetSum_sub_one_mulVec_eq_sumSq design
    ({flatFirst, flatSecond, freeLabel} : Finset (Fin size)) tilt] at hform
  rw [Finset.sum_insert (by simp [hFirstSecond, hFirstFree]),
    Finset.sum_insert (by simp [hSecondFree]), Finset.sum_singleton] at hform
  rw [hread flatFirst, hread flatSecond, hread freeLabel, hFirstFlat, hSecondFlat, hself] at hform
  rw [← hfreeNormal, ← hfreeProbe] at hform
  nlinarith [hform]

/-- The third atom of a weak dominator whose other two members are flat reads
the normal at least at unit square.  This consumes the landed
`Gtz.single_survivor_overcovers` at the design level. -/
theorem one_le_freeNormalSq_of_dominates {size rank : ℕ} (design : WeightedDesign size rank)
    {flatFirst flatSecond freeLabel : Fin size}
    (hFirstFree : flatFirst ≠ freeLabel) (hSecondFree : flatSecond ≠ freeLabel)
    (unitNormal : Fin rank → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hFirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hSecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hdominates : Dominates design {flatFirst, flatSecond, freeLabel}) :
    1 ≤ (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 := by
  classical
  have hmem : freeLabel ∈ ({flatFirst, flatSecond, freeLabel} : Finset (Fin size)) := by simp
  have hblind : ∀ label ∈ ({flatFirst, flatSecond, freeLabel} : Finset (Fin size)),
      label ≠ freeLabel → design.atom label ⬝ᵥ unitNormal = 0 := by
    intro label hlabel hne
    rcases Finset.mem_insert.mp hlabel with rfl | hrest
    · exact hFirstFlat
    · rcases Finset.mem_insert.mp hrest with rfl | hlast
      · exact hSecondFlat
      · exact absurd (Finset.mem_singleton.mp hlast) hne
  have hcover := single_survivor_overcovers design hmem unitNormal hblind hdominates
  rw [hunit] at hcover
  exact hcover

/-- **THE FLAT PAIR COVERS THE PLANE.**  Plain plane covering, from a weak
dominator alone. -/
theorem planePair_dominates_inPlane_of_dominates {size rank : ℕ}
    (design : WeightedDesign size rank) {flatFirst flatSecond freeLabel : Fin size}
    (hFirstSecond : flatFirst ≠ flatSecond) (hFirstFree : flatFirst ≠ freeLabel)
    (hSecondFree : flatSecond ≠ freeLabel)
    (unitNormal probeVec : Fin rank → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hprobe : probeVec ⬝ᵥ unitNormal = 0)
    (hFirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hSecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hdominates : Dominates design {flatFirst, flatSecond, freeLabel}) :
    probeVec ⬝ᵥ probeVec
      ≤ (design.atom flatFirst ⬝ᵥ probeVec) ^ 2
        + (design.atom flatSecond ⬝ᵥ probeVec) ^ 2 := by
  have hsq := planePair_sq_of_dominates design hFirstSecond hFirstFree hSecondFree unitNormal
    probeVec hunit hprobe hFirstFlat hSecondFlat hdominates
  have hheavy := one_le_freeNormalSq_of_dominates design hFirstFree hSecondFree unitNormal hunit
    hFirstFlat hSecondFlat hdominates
  nlinarith [hsq, hheavy, sq_nonneg (design.atom freeLabel ⬝ᵥ probeVec)]

/-! ## 11.  From the plane law to the pair minor

The pair's own span is inside the plane, so the plane law restricted to it is a
nonnegative binary quadratic form.  Its determinant is the Gram determinant times
the pair gap excess. -/

/-- A nonnegative binary quadratic form has nonnegative determinant.  Elementary
and division free. -/
theorem nonneg_det_of_nonneg_binaryForm {formFirst formCross formSecond : ℝ}
    (hform : ∀ leftScale rightScale : ℝ, 0 ≤ formFirst * leftScale ^ 2
      + 2 * formCross * leftScale * rightScale + formSecond * rightScale ^ 2) :
    0 ≤ formFirst * formSecond - formCross ^ 2 := by
  have hfirst := hform 1 0
  have hsecond := hform 0 1
  have hleft := hform (-formCross) formFirst
  have hright := hform formSecond (-formCross)
  have hplus := hform 1 1
  have hminus := hform 1 (-1)
  rcases lt_or_eq_of_le (by nlinarith [hfirst] : (0 : ℝ) ≤ formFirst) with hpos | hzero
  · nlinarith [hleft, hpos]
  · rcases lt_or_eq_of_le (by nlinarith [hsecond] : (0 : ℝ) ≤ formSecond) with hposSecond | hzeroSecond
    · nlinarith [hright, hposSecond]
    · nlinarith [hplus, hminus, hzero, hzeroSecond]

/-- **THE PAIR MINOR OF A WEAK DOMINATOR'S FLAT PAIR.**  The Gram determinant of
the flat pair times its gap excess is nonnegative.  So a flat pair inside a weak
card-three dominator has nonnegative gap excess as soon as the two atoms are
independent. -/
theorem gramDet_mul_pairGapExcess_nonneg_of_dominates {size rank : ℕ}
    (design : WeightedDesign size rank) {flatFirst flatSecond freeLabel : Fin size}
    (hFirstSecond : flatFirst ≠ flatSecond) (hFirstFree : flatFirst ≠ freeLabel)
    (hSecondFree : flatSecond ≠ freeLabel)
    (unitNormal : Fin rank → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hFirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hSecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hdominates : Dominates design {flatFirst, flatSecond, freeLabel}) :
    0 ≤ (leverageOf (design.atom flatFirst) * leverageOf (design.atom flatSecond)
          - gapPairingOf design flatFirst flatSecond ^ 2)
        * pairGapExcessOf design flatFirst flatSecond := by
  set leverageFirst : ℝ := design.atom flatFirst ⬝ᵥ design.atom flatFirst with hleverageFirst
  set leverageSecond : ℝ := design.atom flatSecond ⬝ᵥ design.atom flatSecond with hleverageSecond
  set pairing : ℝ := design.atom flatFirst ⬝ᵥ design.atom flatSecond with hpairing
  have hform : ∀ leftScale rightScale : ℝ,
      0 ≤ (leverageFirst ^ 2 + pairing ^ 2 - leverageFirst) * leftScale ^ 2
        + 2 * (pairing * (leverageFirst + leverageSecond - 1)) * leftScale * rightScale
        + (pairing ^ 2 + leverageSecond ^ 2 - leverageSecond) * rightScale ^ 2 := by
    intro leftScale rightScale
    set probeVec : Fin rank → ℝ :=
      leftScale • design.atom flatFirst + rightScale • design.atom flatSecond with hprobeVec
    have hprobeNormal : probeVec ⬝ᵥ unitNormal = 0 := by
      rw [hprobeVec, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
        hFirstFlat, hSecondFlat]
      ring
    have hreadFirst : design.atom flatFirst ⬝ᵥ probeVec
        = leftScale * leverageFirst + rightScale * pairing := by
      rw [hprobeVec, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hreadSecond : design.atom flatSecond ⬝ᵥ probeVec
        = leftScale * pairing + rightScale * leverageSecond := by
      rw [hprobeVec, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        hpairing, dotProduct_comm (design.atom flatSecond) (design.atom flatFirst)]
    have hselfProbe : probeVec ⬝ᵥ probeVec
        = leftScale ^ 2 * leverageFirst + 2 * leftScale * rightScale * pairing
          + rightScale ^ 2 * leverageSecond := by
      rw [hprobeVec]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [← hleverageFirst, ← hleverageSecond, ← hpairing,
        dotProduct_comm (design.atom flatSecond) (design.atom flatFirst), ← hpairing]
      ring
    have hcover := planePair_dominates_inPlane_of_dominates design hFirstSecond hFirstFree
      hSecondFree unitNormal probeVec hunit hprobeNormal hFirstFlat hSecondFlat hdominates
    rw [hselfProbe, hreadFirst, hreadSecond] at hcover
    nlinarith [hcover]
  have hdet := nonneg_det_of_nonneg_binaryForm hform
  have hrewrite : leverageOf (design.atom flatFirst) = leverageFirst := by
    rw [leverageOf_eq_dotProduct_self]
  have hrewriteSecond : leverageOf (design.atom flatSecond) = leverageSecond := by
    rw [leverageOf_eq_dotProduct_self]
  have hpairRewrite : gapPairingOf design flatFirst flatSecond = pairing := rfl
  rw [hrewrite, hrewriteSecond, hpairRewrite]
  unfold pairGapExcessOf gapExcessOf gapPairingOf
  rw [leverageOf_eq_dotProduct_self, leverageOf_eq_dotProduct_self, ← hleverageFirst,
    ← hleverageSecond, ← hpairing]
  nlinarith [hdet]

/-- **THE PAIR GAP EXCESS OF A WEAK DOMINATOR'S FLAT PAIR.**  Under independence
of the two flat atoms the minor itself is nonnegative.  This is the weak
counterpart of `Gtz.pairGapExcessOf_pos_of_posDef_tripleGapMatrix`. -/
theorem pairGapExcessOf_nonneg_of_dominates_flatPair {size rank : ℕ}
    (design : WeightedDesign size rank) {flatFirst flatSecond freeLabel : Fin size}
    (hFirstSecond : flatFirst ≠ flatSecond) (hFirstFree : flatFirst ≠ freeLabel)
    (hSecondFree : flatSecond ≠ freeLabel)
    (unitNormal : Fin rank → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hFirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hSecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hindependent : 0 < leverageOf (design.atom flatFirst) * leverageOf (design.atom flatSecond)
      - gapPairingOf design flatFirst flatSecond ^ 2)
    (hdominates : Dominates design {flatFirst, flatSecond, freeLabel}) :
    0 ≤ pairGapExcessOf design flatFirst flatSecond := by
  have hproduct := gramDet_mul_pairGapExcess_nonneg_of_dominates design hFirstSecond hFirstFree
    hSecondFree unitNormal hunit hFirstFlat hSecondFlat hdominates
  exact nonneg_of_mul_nonneg_right hproduct hindependent

/-! ## 12.  The mixed shape, evaluated

A selected subset holding exactly one flat label, two sharp labels, and leaving
exactly one sharp label outside is the shape of every MIXED triple of the
one-line class and of every TRANSVERSAL of the two-meeting-lines class.  Its lead
and its sharp balance both collapse to named scalars. -/

/-- The lead of a subset holding exactly one flat label. -/
theorem flatSplitLead_of_inter_singleton {size rank : ℕ} (design : WeightedDesign size rank)
    {selected flatSet : Finset (Fin size)} {flatLabel : Fin size}
    (hinter : selected ∩ flatSet = {flatLabel}) (probeVec : Fin rank → ℝ) :
    flatSplitLead design selected flatSet probeVec
      = (design.atom flatLabel ⬝ᵥ probeVec) ^ 2 - flatLeak design flatSet probeVec := by
  unfold flatSplitLead
  rw [hinter, Finset.sum_singleton]

/-- The sharp balance of a subset with two sharp labels inside and one outside. -/
theorem sharpBalanceValue_of_pair_singleton {size rank : ℕ} (design : WeightedDesign size rank)
    {selected flatSet : Finset (Fin size)} {sharpFirst sharpSecond sharpOutside : Fin size}
    (hsharpDistinct : sharpFirst ≠ sharpSecond)
    (hinside : selected \ flatSet = {sharpFirst, sharpSecond})
    (houtside : selectedᶜ \ flatSet = {sharpOutside})
    (normalVec probeVec : Fin rank → ℝ) :
    sharpBalanceValue design selected flatSet normalVec probeVec
      = weightDeficit design sharpFirst * weightDeficit design sharpSecond
          * wedgeShadow design normalVec probeVec sharpFirst sharpSecond ^ 2
        - design.weight sharpOutside
          * (weightDeficit design sharpFirst
                * wedgeShadow design normalVec probeVec sharpFirst sharpOutside ^ 2
              + weightDeficit design sharpSecond
                * wedgeShadow design normalVec probeVec sharpSecond sharpOutside ^ 2) := by
  unfold sharpBalanceValue
  rw [hinside, houtside, wedgeTotal_singleton,
    wedgeTotal_pair design (weightDeficit design) hsharpDistinct normalVec probeVec,
    crossWedgeTotal_singleton_right, Finset.sum_pair hsharpDistinct]
  ring

/-- **THE MIXED SHAPE, DECIDED.**  One flat label inside, two sharp labels
inside, one sharp label outside.  Strict domination is the normal surplus of the
two sharp members plus a single scalar comparison at every in-plane probe.  Every
quantity is a polynomial in the design, and the flat leak appears exactly once,
subtracted from the reading of the SELECTED flat label. -/
theorem posDef_iff_mixedFlatSplit {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (unitNormal : Fin rank → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ unitNormal = 0)
    {flatLabel sharpFirst sharpSecond sharpOutside : Fin size}
    (hsharpDistinct : sharpFirst ≠ sharpSecond)
    (hinter : selected ∩ flatSet = {flatLabel})
    (hinside : selected \ flatSet = {sharpFirst, sharpSecond})
    (houtside : selectedᶜ \ flatSet = {sharpOutside}) :
    (subsetSum design selected - 1).PosDef
      ↔ (1 < (design.atom sharpFirst ⬝ᵥ unitNormal) ^ 2
              + (design.atom sharpSecond ⬝ᵥ unitNormal) ^ 2)
        ∧ ∀ probeVec : Fin rank → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
            design.weight sharpOutside
                * (weightDeficit design sharpFirst
                      * wedgeShadow design unitNormal probeVec sharpFirst sharpOutside ^ 2
                    + weightDeficit design sharpSecond
                      * wedgeShadow design unitNormal probeVec sharpSecond sharpOutside ^ 2)
              < ((design.atom flatLabel ⬝ᵥ probeVec) ^ 2 - flatLeak design flatSet probeVec)
                    * ((design.atom sharpFirst ⬝ᵥ unitNormal) ^ 2
                        + (design.atom sharpSecond ⬝ᵥ unitNormal) ^ 2 - 1)
                  + weightDeficit design sharpFirst * weightDeficit design sharpSecond
                    * wedgeShadow design unitNormal probeVec sharpFirst sharpSecond ^ 2 := by
  have hnormalSum : ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2
      = (design.atom sharpFirst ⬝ᵥ unitNormal) ^ 2
        + (design.atom sharpSecond ⬝ᵥ unitNormal) ^ 2 := by
    have hdrop := sum_sdiff_flat_normalSq design selected flatSet unitNormal (fun _ => 1) hflat
    simp only [one_mul] at hdrop
    rw [← hdrop, hinside, Finset.sum_pair hsharpDistinct]
  rw [posDef_iff_flatSplitBalance design selected flatSet unitNormal hunit hflat, hnormalSum]
  constructor
  · rintro ⟨hsurplus, hsplit⟩
    refine ⟨hsurplus, fun probeVec horthogonal hprobeNe => ?_⟩
    have hvalue := hsplit probeVec horthogonal hprobeNe
    rw [flatSplitLead_of_inter_singleton design hinter probeVec,
      sharpBalanceValue_of_pair_singleton design hsharpDistinct hinside houtside unitNormal
        probeVec] at hvalue
    linarith [hvalue]
  · rintro ⟨hsurplus, hcompare⟩
    refine ⟨hsurplus, fun probeVec horthogonal hprobeNe => ?_⟩
    have hvalue := hcompare probeVec horthogonal hprobeNe
    rw [flatSplitLead_of_inter_singleton design hinter probeVec,
      sharpBalanceValue_of_pair_singleton design hsharpDistinct hinside houtside unitNormal
        probeVec]
    linarith [hvalue]

/-! ## 13.  The one-line class, and the two-meeting-lines class

At the one-line pattern the flat set is the line `{0, 1, 2}`.  Every one of the
nine MIXED candidates has the shape of section 12, and so does every one of the
four TRANSVERSALS of the two-meeting-lines class at the first line's normal.  So
one selector formula covers both residual axioms. -/

/-- The line of the one-line pattern reads its own normal as zero at every
member. -/
theorem oneLine_lineSet_flat (design : WeightedDesign 6 3) {unitNormal : Fin 3 → ℝ}
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0) :
    ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.atom label ⬝ᵥ unitNormal = 0 :=
  hlineFlat

/-- **THE FLAT-SPLIT SELECTOR AT A LINE.**  A card-three subset with positive
normal surplus and a positive split value at every in-plane probe.  Both residual
line axioms consume exactly this. -/
def LineFlatSplitSelectorAt (design : WeightedDesign 6 3) (unitNormal : Fin 3 → ℝ) : Prop :=
  ∃ selected : Finset (Fin 6), selected.card = 3
    ∧ (1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
    ∧ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
        0 < flatSplitLead design selected ({0, 1, 2} : Finset (Fin 6)) probeVec
              * ((∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2) - 1)
            + sharpBalanceValue design selected ({0, 1, 2} : Finset (Fin 6)) unitNormal probeVec

/-- The selector returns a strict card-three witness. -/
theorem exists_posDef_cardThree_of_lineFlatSplitSelectorAt (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hselector : LineFlatSplitSelectorAt design unitNormal) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  obtain ⟨selected, hcard, hsurplus, hsplit⟩ := hselector
  exact ⟨selected, hcard,
    (posDef_iff_flatSplitBalance design selected ({0, 1, 2} : Finset (Fin 6)) unitNormal hunit
      hlineFlat).mpr ⟨hsurplus, hsplit⟩⟩

/-- A strict card-three witness returns the selector. -/
theorem lineFlatSplitSelectorAt_of_exists_posDef_cardThree (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hwitness : ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef) :
    LineFlatSplitSelectorAt design unitNormal := by
  obtain ⟨selected, hcard, hposDef⟩ := hwitness
  obtain ⟨hsurplus, hsplit⟩ :=
    (posDef_iff_flatSplitBalance design selected ({0, 1, 2} : Finset (Fin 6)) unitNormal hunit
      hlineFlat).mp hposDef
  exact ⟨selected, hcard, hsurplus, hsplit⟩

/-! ### The one-line door -/

/-- **THE ONE-LINE RESIDUAL, THROUGH THE FLAT SPLIT.**  The whole joint blind
spot residual, with the strict card-three witness replaced by the flat-split
selector at the pattern's own line normal. -/
def OneLineFlatSplitResidual : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
    (∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel) →
    IsCapBlindSpot design →
    IsOneLineNormalBlindSpot design →
    (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
    ∀ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1 →
      (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ unitNormal = 0) →
      LineFlatSplitSelectorAt design unitNormal

theorem oneLineTenthHeavyJointBlindLineSparse_of_flatSplitResidual
    (hresidual : OneLineFlatSplitResidual) : OneLineTenthHeavyJointBlindLineSparse := by
  intro design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak
  obtain ⟨unitNormal, hunit, hlineFlat⟩ := oneLine_exists_unitNormal design hpattern
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_cardThree_of_lineFlatSplitSelectorAt design hunit hlineFlat
      (hresidual design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak unitNormal hunit
        hlineFlat)
  exact planeBranchTenCandidate_of_oneLine_strictTriple_of_normalBlind design hpattern hlineBlind
    selected hcard hposDef

theorem flatSplitResidual_of_oneLineTenthHeavyJointBlindLineSparse
    (hresidual : OneLineTenthHeavyJointBlindLineSparse) : OneLineFlatSplitResidual := by
  intro design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak unitNormal hunit hlineFlat
  exact lineFlatSplitSelectorAt_of_exists_posDef_cardThree design hunit hlineFlat
    (exists_posDef_cardThree_of_planeBranchTenCandidate design
      (hresidual design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak))

/-- **THE ONE-LINE DOOR IS EXACT.**  The flat-split residual is equivalent to the
registry formula, so the entrance carries no hidden vacuity. -/
theorem oneLineFlatSplitResidual_iff :
    OneLineFlatSplitResidual ↔ OneLineTenthHeavyJointBlindLineSparse :=
  ⟨oneLineTenthHeavyJointBlindLineSparse_of_flatSplitResidual,
    flatSplitResidual_of_oneLineTenthHeavyJointBlindLineSparse⟩

/-! ### The two-meeting-lines door

The twin residual is NOT the same formula.  Four differences, all recorded here.

* Its pattern is `[[0,1,2],[0,3,4]]`, so the first line is the same set but the
  design carries a second line through the shared atom `0`.
* It has no `Gtz.IsOneLineNormalBlindSpot` hypothesis.  Instead it quantifies
  over TWO explicit unit normals, one flat on each line, and assumes
  `Gtz.IsLinePairLiftBlindAt` at each.
* Its endpoint is `Gtz.TwoMeetingLinesTransversalStrict`, four disjuncts, not the
  ten of `Gtz.PlaneBranchTenCandidate`.
* Its four transversals all carry the open atom `5`.

What TRANSPORTS is section 12.  The first normal is flat on `{0,1,2}`, and each
of the four transversals holds exactly one label of `{0,1,2}`, two labels of
`{3,4,5}`, and leaves one label of `{3,4,5}` outside.  That is the mixed shape,
character for character.  So `Gtz.LineFlatSplitSelectorAt` at the FIRST normal
serves both classes, and the only class-specific work is the endpoint bridge. -/

/-- The four transversals are card-three strict witnesses. -/
theorem exists_posDef_cardThree_of_twoMeetingLinesTransversalStrict
    (design : WeightedDesign 6 3) (hstrict : TwoMeetingLinesTransversalStrict design) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  rcases hstrict with h135 | h145 | h235 | h245
  · exact ⟨{1, 3, 5}, by decide, h135⟩
  · exact ⟨{1, 4, 5}, by decide, h145⟩
  · exact ⟨{2, 3, 5}, by decide, h235⟩
  · exact ⟨{2, 4, 5}, by decide, h245⟩

/-- **THE TWO-MEETING-LINES RESIDUAL, THROUGH THE FLAT SPLIT.**  Same selector,
same flat set `{0, 1, 2}`, read at the FIRST line's normal. -/
def TwoMeetingLinesFlatSplitResidual : Prop :=
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
      LineFlatSplitSelectorAt design normalFirst

theorem twoMeetingLinesTenthHeavyJointBlindTransversal_of_flatSplitResidual
    (hresidual : TwoMeetingLinesFlatSplitResidual) :
    TwoMeetingLinesTenthHeavyJointBlindTransversal := by
  intro design hpattern hheavy hweightHeavy hcapBlind hweak normalFirst normalSecond
    hunitFirst hunitSecond horthFirst horthSecond hblindFirst hblindSecond
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_cardThree_of_lineFlatSplitSelectorAt design hunitFirst horthFirst
      (hresidual design hpattern hheavy hweightHeavy hcapBlind hweak normalFirst normalSecond
        hunitFirst hunitSecond horthFirst horthSecond hblindFirst hblindSecond)
  have hshape := twoMeetingLines_strictTriple_eq_transversal_of_bothLineNormalBlind design
    normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond hblindFirst
    hblindSecond selected hcard hposDef
  rcases hshape with h135 | h145 | h235 | h245
  · exact Or.inl (by simpa only [h135] using hposDef)
  · exact Or.inr (Or.inl (by simpa only [h145] using hposDef))
  · exact Or.inr (Or.inr (Or.inl (by simpa only [h235] using hposDef)))
  · exact Or.inr (Or.inr (Or.inr (by simpa only [h245] using hposDef)))

theorem flatSplitResidual_of_twoMeetingLinesTenthHeavyJointBlindTransversal
    (hresidual : TwoMeetingLinesTenthHeavyJointBlindTransversal) :
    TwoMeetingLinesFlatSplitResidual := by
  intro design hpattern hheavy hweightHeavy hcapBlind hweak normalFirst normalSecond
    hunitFirst hunitSecond horthFirst horthSecond hblindFirst hblindSecond
  exact lineFlatSplitSelectorAt_of_exists_posDef_cardThree design hunitFirst horthFirst
    (exists_posDef_cardThree_of_twoMeetingLinesTransversalStrict design
      (hresidual design hpattern hheavy hweightHeavy hcapBlind hweak normalFirst normalSecond
        hunitFirst hunitSecond horthFirst horthSecond hblindFirst hblindSecond))

/-- **THE TWO-MEETING-LINES DOOR IS EXACT.** -/
theorem twoMeetingLinesFlatSplitResidual_iff :
    TwoMeetingLinesFlatSplitResidual ↔ TwoMeetingLinesTenthHeavyJointBlindTransversal :=
  ⟨twoMeetingLinesTenthHeavyJointBlindTransversal_of_flatSplitResidual,
    flatSplitResidual_of_twoMeetingLinesTenthHeavyJointBlindTransversal⟩

/-- **ONE SELECTOR, TWO AXIOMS.**  A design-level producer of the flat-split
selector at a unit normal flat on `{0, 1, 2}` retires both residual line
formulas at once. -/
theorem oneLine_and_twoMeetingLines_of_lineFlatSplitSelector
    (hselector : ∀ design : WeightedDesign 6 3, ∀ unitNormal : Fin 3 → ℝ,
      unitNormal ⬝ᵥ unitNormal = 1 →
      (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ unitNormal = 0) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      LineFlatSplitSelectorAt design unitNormal) :
    OneLineTenthHeavyJointBlindLineSparse
      ∧ TwoMeetingLinesTenthHeavyJointBlindTransversal := by
  constructor
  · refine oneLineTenthHeavyJointBlindLineSparse_of_flatSplitResidual ?_
    intro design hpattern hheavy _hweightHeavy hcapBlind _hlineBlind hweak unitNormal hunit hflat
    exact hselector design unitNormal hunit hflat hheavy hcapBlind hweak
  · refine twoMeetingLinesTenthHeavyJointBlindTransversal_of_flatSplitResidual ?_
    intro design hpattern hheavy _hweightHeavy hcapBlind hweak normalFirst normalSecond
      hunitFirst _hunitSecond horthFirst _horthSecond _hblindFirst _hblindSecond
    exact hselector design normalFirst hunitFirst horthFirst hheavy hcapBlind hweak

/-! ## 14.  The weak dominator, split by how often it meets the line

The residual hands over a card-three WEAK dominator and nothing else.  It meets
the line in three, two, one or zero labels, and each count carries its own
structural consequence.  Section 10 supplies the count-two case, the landed
`Gtz.not_dominates_of_coplanar_triple` refuses count three, and the design-level
`Gtz.blindSubset_dominates_overcovers` handles count one. -/

/-- Removing the one flat member of a distinct triple leaves the other two. -/
theorem sdiff_singleton_of_triple {size : ℕ} {flatLabel sharpFirst sharpSecond : Fin size}
    (hFlatFirst : flatLabel ≠ sharpFirst) (hFlatSecond : flatLabel ≠ sharpSecond) :
    ({flatLabel, sharpFirst, sharpSecond} : Finset (Fin size)) \ {flatLabel}
      = {sharpFirst, sharpSecond} := by
  ext label
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hne⟩
    rcases hmem with rfl | hrest
    · exact absurd rfl hne
    · exact hrest
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inl rfl), fun heq => hFlatFirst heq.symm⟩
    · exact ⟨Or.inr (Or.inr rfl), fun heq => hFlatSecond heq.symm⟩

/-- **COUNT THREE IS REFUSED.**  A card-three weak dominator never holds three
labels of a coplanar line.  Stated as a bound on the meeting number. -/
theorem oneLine_dominator_lineCount_le_two (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hnormalNe : unitNormal ≠ 0)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {dominator : Finset (Fin 6)} (hcard : dominator.card = 3)
    (hdominates : Dominates design dominator) :
    (dominator ∩ ({0, 1, 2} : Finset (Fin 6))).card ≤ 2 := by
  classical
  by_contra hthree
  have hge : 3 ≤ (dominator ∩ ({0, 1, 2} : Finset (Fin 6))).card := by omega
  have hlineCard : ({0, 1, 2} : Finset (Fin 6)).card = 3 := by decide
  have hinterEq : dominator ∩ ({0, 1, 2} : Finset (Fin 6)) = ({0, 1, 2} : Finset (Fin 6)) :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hlineCard]; exact hge)
  have hsubset : ({0, 1, 2} : Finset (Fin 6)) ⊆ dominator := by
    rw [← hinterEq]; exact Finset.inter_subset_left
  exact not_dominates_of_coplanar_triple design hsubset (by rw [hcard, hlineCard])
    unitNormal hnormalNe hlineFlat hdominates

/-- **COUNT TWO: THE LINE PAIR COVERS THE PLANE.**  The one-line reading of the
weak plane law of section 10. -/
theorem oneLine_dominator_linePair_covers_plane (design : WeightedDesign 6 3)
    {unitNormal probeVec : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hprobe : probeVec ⬝ᵥ unitNormal = 0)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstFree : lineFirst ≠ freeLabel)
    (hSecondFree : lineSecond ≠ freeLabel)
    (hdominates : Dominates design {lineFirst, lineSecond, freeLabel}) :
    probeVec ⬝ᵥ probeVec
      ≤ (design.atom lineFirst ⬝ᵥ probeVec) ^ 2
        + (design.atom lineSecond ⬝ᵥ probeVec) ^ 2 :=
  planePair_dominates_inPlane_of_dominates design hFirstSecond hFirstFree hSecondFree unitNormal
    probeVec hunit hprobe (hlineFlat lineFirst hFirstMem) (hlineFlat lineSecond hSecondMem)
    hdominates

/-- **COUNT TWO: THE LINE PAIR MINOR.**  Under independence of the two line
atoms the pair gap excess of a weak dominator's line pair is nonnegative.  The
pair-cap blind spot then caps that same nonnegative quantity from above. -/
theorem oneLine_dominator_linePair_gapExcess_nonneg (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstFree : lineFirst ≠ freeLabel)
    (hSecondFree : lineSecond ≠ freeLabel)
    (hindependent : 0 < leverageOf (design.atom lineFirst) * leverageOf (design.atom lineSecond)
      - gapPairingOf design lineFirst lineSecond ^ 2)
    (hdominates : Dominates design {lineFirst, lineSecond, freeLabel}) :
    0 ≤ pairGapExcessOf design lineFirst lineSecond :=
  pairGapExcessOf_nonneg_of_dominates_flatPair design hFirstSecond hFirstFree hSecondFree
    unitNormal hunit (hlineFlat lineFirst hFirstMem) (hlineFlat lineSecond hSecondMem)
    hindependent hdominates

/-- **COUNT ONE: THE FREE PAIR CARRIES THE NORMAL.**  A weak dominator holding
one line atom and two free atoms forces those two free atoms to read the normal
at unit square between them.  This consumes the landed
`Gtz.blindSubset_dominates_overcovers` at the design level. -/
theorem oneLine_dominator_freePair_normal_sum (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {lineLabel freeFirst freeSecond : Fin 6}
    (hlineMem : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hLineFirst : lineLabel ≠ freeFirst) (hLineSecond : lineLabel ≠ freeSecond)
    (hFreeDistinct : freeFirst ≠ freeSecond)
    (hdominates : Dominates design {lineLabel, freeFirst, freeSecond}) :
    1 ≤ (design.atom freeFirst ⬝ᵥ unitNormal) ^ 2
      + (design.atom freeSecond ⬝ᵥ unitNormal) ^ 2 := by
  classical
  have hsub : ({lineLabel} : Finset (Fin 6))
      ⊆ ({lineLabel, freeFirst, freeSecond} : Finset (Fin 6)) := by
    intro label hlabel
    rw [Finset.mem_singleton] at hlabel
    subst hlabel
    simp
  have hblind : ∀ label ∈ ({lineLabel} : Finset (Fin 6)),
      design.atom label ⬝ᵥ unitNormal = 0 := by
    intro label hlabel
    rw [Finset.mem_singleton.mp hlabel]
    exact hlineFlat lineLabel hlineMem
  have hcover := blindSubset_dominates_overcovers design hsub unitNormal hblind hdominates
  rw [sdiff_singleton_of_triple hLineFirst hLineSecond, Finset.sum_pair hFreeDistinct,
    hunit] at hcover
  exact hcover

end Gtz

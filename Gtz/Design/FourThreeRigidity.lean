/-
# The `(4,3)` invariant rigidity: a heavy four-atom rank-three tie is the tetrahedron

A `(4,3)` design has exactly four card-three subsets, one per omitted label, and
the complement of such a subset is the SINGLE omitted label.  So the landed
complement engine `Gtz.posDef_subsetSum_of_outside_share_lt` fires at
`labelsOtherThan omitted` as soon as the omitted atom's outside mass stays below
`1 - maxWeight` in every direction; Cauchy-Schwarz
(`Gtz.atomOverlap_sq_le_leverage_mul_normSq`) caps that mass by
`atomShare omitted` times the probe norm, so the whole certificate collapses to
one scalar comparison.  Contrapositive: a design with NO strictly dominating
triple has every share pinned from below by `1 - maxWeight`.

Three things come out, and the second is not what the route suggests.

* **The per-label pin (target (a)) is real.**  It is stated here at every size
  and every rank, for an arbitrary weight bound, in
  `one_sub_le_atomShare_of_not_posDef_labelsOtherThan`.

* **The SUMMED inequality is VACUOUS.**  Adding the four pins against
  `Gtz.sum_atomShare_eq_rank` yields `1 <= bound 0 + bound 1 + bound 2 + bound 3`
  for any family of weight bounds -- and that inequality holds for EVERY
  probability vector on four points with no design, no Parseval, and no
  domination hypothesis whatsoever: pair the labels `0 <-> 1`, `2 <-> 3` and sum.
  Both routes are proved below, the engine one as
  `one_le_sum_otherWeightBound_of_noStrictTriple` and the design-free one as
  `one_le_sum_bound_of_sum_eq_one`, so the engine's contribution at the level of
  the inequality is exactly nothing.  The sorted reading `1 <= 3 t(1) + t(2)` is
  likewise a simplex tautology (`one_le_three_mul_topWeight_add_secondWeight`),
  not a rigidity statement.

* **The content is the EQUALITY CASE, and it is sharp.**  The four pins are
  slacks against an exact budget: `sum_atomShare_slack_eq` records
  `sum_c (atomShare c - (1 - topWeight)) = 4 * topWeight - 1`.  At
  `topWeight = 1/4` -- the uniform weighting, the only one the cap
  `weight <= 1/4` allows -- the budget is ZERO, every slack vanishes, and the
  design is rigid at the level of its Gram invariants: every leverage is `3`,
  every pairing squares to `1`, every triple of pairings multiplies to `-1`,
  every triple has `discriminantTrace = 6` and `discriminantTie = 0`, and the
  design is an exact tie.  That is the invariant-level classification of the
  regular tetrahedron, with no orthogonal normal form anywhere.

Sharpness is witnessed by the shipped `Gtz.tetraDesign`: its shares are exactly
`3/4 = 1 - 1/4`, so it sits ON the complement-engine boundary at all four of its
triples, exactly as `Gtz.tetraDesign_pairCap_attained` puts it on the pair-cap
boundary at all six of its pairs.
-/
import Gtz.Design.ComplementEngine
import Gtz.Design.VolumeSamplingAverage
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.PhaseFreeNoGo
import Gtz.Reduction.BranchTransferConstants
import Gtz.Ties.TetrahedronCertifiedTie
import Gtz.Certificates.ResidueDissolution
import Gtz.LinAlg.PsdKit
import Gtz.Design.LeverageBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## Part 1. The complement of a single label -/

/-- **The labels other than a given one.**  At size four this is the generic
card-three subset: every triple of a `(4,3)` design is `labelsOtherThan c` for
exactly one omitted label `c`, and its complement is the singleton `{c}`. -/
def labelsOtherThan (omitted : Fin size) : Finset (Fin size) :=
  ({omitted} : Finset (Fin size))ᶜ

theorem mem_labelsOtherThan {omitted label : Fin size} :
    label ∈ labelsOtherThan omitted ↔ label ≠ omitted := by
  simp [labelsOtherThan]

/-- The complement of the complement: exactly the omitted label. -/
theorem compl_labelsOtherThan (omitted : Fin size) :
    (labelsOtherThan omitted)ᶜ = ({omitted} : Finset (Fin size)) := by
  rw [labelsOtherThan, compl_compl]

theorem card_labelsOtherThan (omitted : Fin size) :
    (labelsOtherThan omitted).card = size - 1 := by
  rw [labelsOtherThan, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]

/-- At four labels the omission is a TRIPLE -- the subset size GTZ asks about at
rank three. -/
theorem card_labelsOtherThan_ofFourLabels (omitted : Fin 4) :
    (labelsOtherThan omitted).card = 3 := by
  rw [card_labelsOtherThan]

/-! ## Part 2. The outside mass of a single atom is capped by its share -/

/-- **Cauchy-Schwarz, in share form.**  One atom's weighted Parseval mass in the
direction `probe` never exceeds its share times the probe's norm.  This is the
step that lets the complement engine read a single scalar instead of a
direction-by-direction bound: the largest eigenvalue of the rank-one outside
block `weight * atomMatrix` is exactly `atomShare`, and nothing about
eigenvalues is needed to say so. -/
theorem weight_mul_atomOverlap_sq_le_atomShare_mul (design : WeightedDesign size rank)
    (label : Fin size) (probe : Fin rank → ℝ) :
    design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
      ≤ atomShare design label * (probe ⬝ᵥ probe) := by
  have hcauchy := atomOverlap_sq_le_leverage_mul_normSq (design.atom label) probe
  have hweightPos := design.weight_pos label
  rw [atomShare, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcauchy hweightPos.le

/-! ## Part 3. The complement engine at a single-label complement -/

/-- **THE ENGINE, SPECIALISED.**  If the omitted atom's share stays strictly
below `1 - boundWeight`, where `boundWeight` bounds every OTHER weight, then the
labels other than it strictly dominate.  Rank-generic, size-generic, no
heaviness: the whole certificate is the one scalar `atomShare omitted`. -/
theorem posDef_subsetSum_labelsOtherThan_of_atomShare_lt (design : WeightedDesign size rank)
    (omitted : Fin size) {boundWeight : ℝ} (hboundPos : 0 < boundWeight)
    (hbound : ∀ label, label ≠ omitted → design.weight label ≤ boundWeight)
    (hshare : atomShare design omitted < 1 - boundWeight) :
    (subsetSum design (labelsOtherThan omitted) - 1).PosDef := by
  refine posDef_subsetSum_of_outside_share_lt design (labelsOtherThan omitted)
    boundWeight hboundPos (fun label hlabel => hbound label (mem_labelsOtherThan.mp hlabel))
    (fun probe hprobeNe => ?_)
  rw [compl_labelsOtherThan, Finset.sum_singleton]
  have hnormPos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
  have hcap := weight_mul_atomOverlap_sq_le_atomShare_mul design omitted probe
  nlinarith [hcap, hnormPos, hshare]

/-- The weak reading of the same certificate. -/
theorem dominates_labelsOtherThan_of_atomShare_lt (design : WeightedDesign size rank)
    (omitted : Fin size) {boundWeight : ℝ} (hboundPos : 0 < boundWeight)
    (hbound : ∀ label, label ≠ omitted → design.weight label ≤ boundWeight)
    (hshare : atomShare design omitted < 1 - boundWeight) :
    Dominates design (labelsOtherThan omitted) :=
  (posDef_subsetSum_labelsOtherThan_of_atomShare_lt design omitted hboundPos
    hbound hshare).posSemidef

/-- **A GTZ-positive certificate at `(4,3)`**: one under-weight share hands over a
dominating triple outright. -/
theorem exists_dominatingTriple_of_atomShare_lt (design : WeightedDesign 4 3)
    (omitted : Fin 4) {boundWeight : ℝ} (hboundPos : 0 < boundWeight)
    (hbound : ∀ label, label ≠ omitted → design.weight label ≤ boundWeight)
    (hshare : atomShare design omitted < 1 - boundWeight) :
    ∃ candidate : Finset (Fin 4), candidate.card = 3 ∧ Dominates design candidate :=
  ⟨labelsOtherThan omitted, card_labelsOtherThan_ofFourLabels omitted,
    dominates_labelsOtherThan_of_atomShare_lt design omitted hboundPos hbound hshare⟩

/-! ## Part 4. Target (a): the per-label pin -/

/-- **TARGET (a), rank- and size-generic.**  If the labels other than `omitted`
fail to strictly dominate, the omitted atom's share is at least `1 - boundWeight`
for EVERY bound on the other weights.  Instantiating at the maximum of the other
weights gives the sharpest reading; instantiating at the global maximum gives the
reading that sums cleanly. -/
theorem one_sub_le_atomShare_of_not_posDef_labelsOtherThan (design : WeightedDesign size rank)
    (omitted : Fin size) {boundWeight : ℝ} (hboundPos : 0 < boundWeight)
    (hbound : ∀ label, label ≠ omitted → design.weight label ≤ boundWeight)
    (hnotPosDef : ¬ (subsetSum design (labelsOtherThan omitted) - 1).PosDef) :
    1 - boundWeight ≤ atomShare design omitted := by
  by_contra hcontra
  exact hnotPosDef (posDef_subsetSum_labelsOtherThan_of_atomShare_lt design omitted
    hboundPos hbound (not_le.mp hcontra))

/-- **TARGET (a) at `(4,3)`.**  A design with no strictly dominating triple has
every share pinned from below. -/
theorem one_sub_le_atomShare_of_noStrictTriple (design : WeightedDesign 4 3)
    {boundWeight : ℝ} (hboundPos : 0 < boundWeight)
    (hbound : ∀ label, design.weight label ≤ boundWeight)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef)
    (omitted : Fin 4) :
    1 - boundWeight ≤ atomShare design omitted :=
  one_sub_le_atomShare_of_not_posDef_labelsOtherThan design omitted hboundPos
    (fun label _ => hbound label)
    (hnoStrictTriple (labelsOtherThan omitted) (card_labelsOtherThan_ofFourLabels omitted))

/-- The same pin from a shipped tie. -/
theorem one_sub_le_atomShare_of_isTie (design : WeightedDesign 4 3)
    {boundWeight : ℝ} (hboundPos : 0 < boundWeight)
    (hbound : ∀ label, design.weight label ≤ boundWeight) (htie : IsTie design)
    (omitted : Fin 4) :
    1 - boundWeight ≤ atomShare design omitted :=
  one_sub_le_atomShare_of_noStrictTriple design hboundPos hbound htie.2 omitted

/-! ## Part 5. Target (b): the summed reading, and why it is vacuous -/

/-- The four shares of a `(4,3)` design total the rank. -/
theorem sum_atomShare_fourLabels_eq_three (design : WeightedDesign 4 3) :
    atomShare design 0 + atomShare design 1 + atomShare design 2 + atomShare design 3 = 3 := by
  have htotal := sum_atomShare_eq_rank design
  rw [Fin.sum_univ_four] at htotal
  rw [htotal]
  norm_num

/-- **THE SLACK BUDGET.**  Unconditional: the four gaps between the shares and the
pin level `1 - topWeight` total exactly `4 * topWeight - 1`, a pure weight
quantity.  Every rigidity statement below is this identity read at
`topWeight = 1/4`, where the budget is zero. -/
theorem sum_atomShare_slack_eq (design : WeightedDesign 4 3) (topWeight : ℝ) :
    (atomShare design 0 - (1 - topWeight)) + (atomShare design 1 - (1 - topWeight))
        + (atomShare design 2 - (1 - topWeight)) + (atomShare design 3 - (1 - topWeight))
      = 4 * topWeight - 1 := by
  have htotal := sum_atomShare_fourLabels_eq_three design
  linarith

/-- **The summed reading of target (a), engine route.**  Summing the four pins
against the share total gives `1 <= 4 * topWeight`. -/
theorem one_le_four_mul_topWeight_of_noStrictTriple (design : WeightedDesign 4 3)
    {topWeight : ℝ} (hboundPos : 0 < topWeight)
    (hbound : ∀ label, design.weight label ≤ topWeight)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef) :
    1 ≤ 4 * topWeight := by
  have hzero := one_sub_le_atomShare_of_noStrictTriple design hboundPos hbound hnoStrictTriple 0
  have hone := one_sub_le_atomShare_of_noStrictTriple design hboundPos hbound hnoStrictTriple 1
  have htwo := one_sub_le_atomShare_of_noStrictTriple design hboundPos hbound hnoStrictTriple 2
  have hthree := one_sub_le_atomShare_of_noStrictTriple design hboundPos hbound hnoStrictTriple 3
  have htotal := sum_atomShare_fourLabels_eq_three design
  linarith

/-- **The summed reading, per-label bounds.**  The sharpest instantiation of
target (a) lets each label carry its own bound `bound omitted` on the OTHER three
weights; summing the four pins gives `1 <= sum of the bounds`.  With the bound
family `fun omitted => max of the other three weights` this is the sorted reading
`1 <= 3 t(1) + t(2)` the route predicts. -/
theorem one_le_sum_otherWeightBound_of_noStrictTriple (design : WeightedDesign 4 3)
    (bound : Fin 4 → ℝ) (hboundPos : ∀ omitted, 0 < bound omitted)
    (hbound : ∀ omitted other : Fin 4, other ≠ omitted → design.weight other ≤ bound omitted)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef) :
    1 ≤ bound 0 + bound 1 + bound 2 + bound 3 := by
  have hpin : ∀ omitted : Fin 4, 1 - bound omitted ≤ atomShare design omitted := fun omitted =>
    one_sub_le_atomShare_of_not_posDef_labelsOtherThan design omitted (hboundPos omitted)
      (hbound omitted)
      (hnoStrictTriple (labelsOtherThan omitted) (card_labelsOtherThan_ofFourLabels omitted))
  have htotal := sum_atomShare_fourLabels_eq_three design
  have hzero := hpin 0
  have hone := hpin 1
  have htwo := hpin 2
  have hthree := hpin 3
  linarith

/-- **THE SUMMED READING IS A SIMPLEX TAUTOLOGY.**  There is no design here at
all: any four reals summing to one -- positivity is not even used -- together
with any family of bounds on the other three, satisfy the same inequality that
the engine route reaches.  Pair the labels `0 <-> 1` and
`2 <-> 3` -- a fixed-point-free involution -- and add the four bound instances.
So the complement engine contributes exactly nothing at the level of the summed
inequality; its content is the PER-LABEL pin and the equality case, not the sum.
Compare `one_le_sum_otherWeightBound_of_noStrictTriple`, which reaches this very
conclusion the long way round, through Parseval and the domination hypothesis. -/
theorem one_le_sum_bound_of_sum_eq_one (weight bound : Fin 4 → ℝ)
    (hweightSum : weight 0 + weight 1 + weight 2 + weight 3 = 1)
    (hbound : ∀ omitted other : Fin 4, other ≠ omitted → weight other ≤ bound omitted) :
    1 ≤ bound 0 + bound 1 + bound 2 + bound 3 := by
  have hzero := hbound 0 1 (by decide)
  have hone := hbound 1 0 (by decide)
  have htwo := hbound 2 3 (by decide)
  have hthree := hbound 3 2 (by decide)
  linarith

/-- The tautology, read on a design's own weights. -/
theorem one_le_sum_otherWeightBound (design : WeightedDesign 4 3) (bound : Fin 4 → ℝ)
    (hbound : ∀ omitted other : Fin 4, other ≠ omitted → design.weight other ≤ bound omitted) :
    1 ≤ bound 0 + bound 1 + bound 2 + bound 3 := by
  have hweightSum := design.weight_sum_one
  rw [Fin.sum_univ_four] at hweightSum
  exact one_le_sum_bound_of_sum_eq_one design.weight bound hweightSum hbound

/-- **THE SORTED READING OF TARGET (b), AND IT IS ALSO A TAUTOLOGY.**  With the
maximiser normalised to label `0` -- which is exactly what sorting the weights
means, relabelling being free -- the route's predicted conclusion
`1 <= 3 t(1) + t(2)` follows from the weight simplex alone: the total is at most
`topWeight + 3 * secondWeight`, and swapping two units of the ordered gap turns
that into `3 * topWeight + secondWeight`.  No design, no Parseval, no domination
hypothesis.  This is the statement the complement-engine route was expected to
deliver as a rigidity theorem; it carries no information about the design. -/
theorem one_le_three_mul_topWeight_add_secondWeight (weight : Fin 4 → ℝ)
    {topWeight secondWeight : ℝ}
    (hweightSum : weight 0 + weight 1 + weight 2 + weight 3 = 1)
    (htopBound : weight 0 ≤ topWeight)
    (hsecondBound : ∀ label : Fin 4, label ≠ 0 → weight label ≤ secondWeight)
    (hordered : secondWeight ≤ topWeight) :
    1 ≤ 3 * topWeight + secondWeight := by
  have hone := hsecondBound 1 (by decide)
  have htwo := hsecondBound 2 (by decide)
  have hthree := hsecondBound 3 (by decide)
  linarith

/-- The global-bound reading of the same tautology: `1 <= 4 * topWeight` needs
nothing but the weight simplex.  Compare
`one_le_four_mul_topWeight_of_noStrictTriple`. -/
theorem one_le_four_mul_topWeight (design : WeightedDesign 4 3) {topWeight : ℝ}
    (hbound : ∀ label, design.weight label ≤ topWeight) :
    1 ≤ 4 * topWeight := by
  have hweightSum := design.weight_sum_one
  rw [Fin.sum_univ_four] at hweightSum
  have hzero := hbound 0
  have hone := hbound 1
  have htwo := hbound 2
  have hthree := hbound 3
  linarith

/-- **THE UPPER PIN -- the content the summed inequality does not carry.**  The
slack budget caps each individual slack, so a design with no strictly dominating
triple has every share squeezed into `[1 - topWeight, 3 * topWeight]`.  The window
is nonempty exactly when `topWeight >= 1/4` and collapses to the single point
`3/4` at `topWeight = 1/4`. -/
theorem atomShare_le_three_mul_topWeight_of_noStrictTriple (design : WeightedDesign 4 3)
    {topWeight : ℝ} (hboundPos : 0 < topWeight)
    (hbound : ∀ label, design.weight label ≤ topWeight)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef)
    (omitted : Fin 4) :
    atomShare design omitted ≤ 3 * topWeight := by
  have hpin : ∀ label : Fin 4, 1 - topWeight ≤ atomShare design label :=
    one_sub_le_atomShare_of_noStrictTriple design hboundPos hbound hnoStrictTriple
  have htotal := sum_atomShare_fourLabels_eq_three design
  have hzero := hpin 0
  have hone := hpin 1
  have htwo := hpin 2
  have hthree := hpin 3
  have hvalueZero : atomShare design 0 ≤ 3 * topWeight := by linarith
  have hvalueOne : atomShare design 1 ≤ 3 * topWeight := by linarith
  have hvalueTwo : atomShare design 2 ≤ 3 * topWeight := by linarith
  have hvalueThree : atomShare design 3 ≤ 3 * topWeight := by linarith
  fin_cases omitted
  · exact hvalueZero
  · exact hvalueOne
  · exact hvalueTwo
  · exact hvalueThree

/-! ## Part 6. The rigidity ladder at the uniform weighting -/

/-- A weight cap at the uniform value forces uniformity: four positive numbers
summing to one, none above `1/4`, are all `1/4`. -/
theorem weight_eq_quarter_of_weight_le_quarter (design : WeightedDesign 4 3)
    (hcap : ∀ label, design.weight label ≤ 1 / 4) (label : Fin 4) :
    design.weight label = 1 / 4 := by
  have hweightSum := design.weight_sum_one
  rw [Fin.sum_univ_four] at hweightSum
  have hzero := hcap 0
  have hone := hcap 1
  have htwo := hcap 2
  have hthree := hcap 3
  have hvalueZero : design.weight 0 = 1 / 4 := by linarith
  have hvalueOne : design.weight 1 = 1 / 4 := by linarith
  have hvalueTwo : design.weight 2 = 1 / 4 := by linarith
  have hvalueThree : design.weight 3 = 1 / 4 := by linarith
  fin_cases label
  · exact hvalueZero
  · exact hvalueOne
  · exact hvalueTwo
  · exact hvalueThree

/-- **THE SHARE RIGIDITY.**  At the uniform weighting the pin level is `3/4` and
the share total is `3`: four numbers at least `3/4` summing to `3` are all
exactly `3/4`.  The complement-engine boundary is attained at every label
simultaneously. -/
theorem atomShare_eq_three_quarters_of_noStrictTriple (design : WeightedDesign 4 3)
    (hcap : ∀ label, design.weight label ≤ 1 / 4)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef)
    (label : Fin 4) :
    atomShare design label = 3 / 4 := by
  have hpin : ∀ other : Fin 4, 1 - (1 / 4 : ℝ) ≤ atomShare design other :=
    one_sub_le_atomShare_of_noStrictTriple design (by norm_num) hcap hnoStrictTriple
  have htotal := sum_atomShare_fourLabels_eq_three design
  have hzero := hpin 0
  have hone := hpin 1
  have htwo := hpin 2
  have hthree := hpin 3
  have hvalueZero : atomShare design 0 = 3 / 4 := by linarith
  have hvalueOne : atomShare design 1 = 3 / 4 := by linarith
  have hvalueTwo : atomShare design 2 = 3 / 4 := by linarith
  have hvalueThree : atomShare design 3 = 3 / 4 := by linarith
  fin_cases label
  · exact hvalueZero
  · exact hvalueOne
  · exact hvalueTwo
  · exact hvalueThree

/-- **THE LEVERAGE RIGIDITY.**  Every atom of such a design has leverage exactly
three -- the regular tetrahedron's signature, read off the shares. -/
theorem leverageOf_eq_three_of_noStrictTriple (design : WeightedDesign 4 3)
    (hcap : ∀ label, design.weight label ≤ 1 / 4)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef)
    (label : Fin 4) :
    leverageOf (design.atom label) = 3 := by
  have hshare := atomShare_eq_three_quarters_of_noStrictTriple design hcap hnoStrictTriple label
  have hweight := weight_eq_quarter_of_weight_le_quarter design hcap label
  rw [atomShare, hweight] at hshare
  linarith

/-- The same statement in the discriminant system's vocabulary. -/
theorem heavyExcess_eq_two_of_noStrictTriple (design : WeightedDesign 4 3)
    (hcap : ∀ label, design.weight label ≤ 1 / 4)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef)
    (label : Fin 4) :
    heavyExcess design label = 2 := by
  rw [heavyExcess, leverageOf_eq_three_of_noStrictTriple design hcap hnoStrictTriple label]
  norm_num

/-! ### The Gram relations -/

/-- **Polarised Parseval read on two atoms**: the Gram is reproduced by its own
weighted square. -/
theorem atomPairing_eq_sum_weight_mul_atomPairing (design : WeightedDesign size 3)
    (first second : Fin size) :
    atomPairing design first second
      = ∑ label, design.weight label
          * (atomPairing design label first * atomPairing design label second) :=
  dotProduct_eq_sum_weight_mul_pair design (design.atom first) (design.atom second)

/-- The Gram row relation at the uniform weighting: `G^2 = 4 G`. -/
theorem sum_atomPairing_mul_atomPairing_eq_four_mul (design : WeightedDesign 4 3)
    (hweight : ∀ label, design.weight label = 1 / 4) (first second : Fin 4) :
    atomPairing design 0 first * atomPairing design 0 second
        + atomPairing design 1 first * atomPairing design 1 second
        + atomPairing design 2 first * atomPairing design 2 second
        + atomPairing design 3 first * atomPairing design 3 second
      = 4 * atomPairing design first second := by
  have hpolar := atomPairing_eq_sum_weight_mul_atomPairing design first second
  rw [Fin.sum_univ_four, hweight 0, hweight 1, hweight 2, hweight 3] at hpolar
  linarith

/-- **The scalar Cauchy-Schwarz step.**  Two Gram rows of squared length `3`
overlapping in `-2 * crossFirst` force `crossFirst` into `[-1, 1]`: the two
signed row sums are sums of squares, so both `8 - 8 crossFirst` and
`8 + 8 crossFirst` are nonnegative. -/
theorem sq_le_one_of_gramRowRelations (crossFirst crossSecond crossThird
    partnerFirst partnerSecond : ℝ)
    (hfirstRow : crossFirst ^ 2 + crossSecond ^ 2 + crossThird ^ 2 = 3)
    (hsecondRow : crossFirst ^ 2 + partnerFirst ^ 2 + partnerSecond ^ 2 = 3)
    (hpairing : crossSecond * partnerFirst + crossThird * partnerSecond = -2 * crossFirst) :
    crossFirst ^ 2 ≤ 1 := by
  have hplus : 2 * (1 - crossFirst) ^ 2 + (crossSecond + partnerFirst) ^ 2
      + (crossThird + partnerSecond) ^ 2 = 8 - 8 * crossFirst := by
    linear_combination hfirstRow + hsecondRow + 2 * hpairing
  have hminus : 2 * (1 + crossFirst) ^ 2 + (crossSecond - partnerFirst) ^ 2
      + (crossThird - partnerSecond) ^ 2 = 8 + 8 * crossFirst := by
    linear_combination hfirstRow + hsecondRow - 2 * hpairing
  nlinarith [sq_nonneg (1 - crossFirst), sq_nonneg (1 + crossFirst),
    sq_nonneg (crossSecond + partnerFirst), sq_nonneg (crossThird + partnerSecond),
    sq_nonneg (crossSecond - partnerFirst), sq_nonneg (crossThird - partnerSecond)]

/-- **THE PAIRING RIGIDITY, six values.**  Leverage three at the uniform weighting
forces every off-diagonal Gram entry to `+-1`.  Each row of `G` has squared
off-diagonal length `3`, each entry is capped at `1` by the step above, and three
numbers at most one summing to three are all one. -/
theorem gramSquares_eq_one_of_leverage_three (design : WeightedDesign 4 3)
    (hleverage : ∀ label, leverageOf (design.atom label) = 3)
    (hweight : ∀ label, design.weight label = 1 / 4) :
    atomPairing design 0 1 ^ 2 = 1 ∧ atomPairing design 0 2 ^ 2 = 1
      ∧ atomPairing design 0 3 ^ 2 = 1 ∧ atomPairing design 1 2 ^ 2 = 1
      ∧ atomPairing design 1 3 ^ 2 = 1 ∧ atomPairing design 2 3 ^ 2 = 1 := by
  have hrel := sum_atomPairing_mul_atomPairing_eq_four_mul design hweight
  have hcomm : ∀ leftLabel rightLabel : Fin 4,
      atomPairing design rightLabel leftLabel = atomPairing design leftLabel rightLabel :=
    fun leftLabel rightLabel => atomPairing_comm design rightLabel leftLabel
  have hself : ∀ label : Fin 4, atomPairing design label label = 3 := by
    intro label
    rw [atomPairing_self, hleverage]
  have rowZero : atomPairing design 0 1 ^ 2 + atomPairing design 0 2 ^ 2
      + atomPairing design 0 3 ^ 2 = 3 := by
    have hrow := hrel 0 0
    rw [hself 0, hcomm 0 1, hcomm 0 2, hcomm 0 3] at hrow
    linear_combination hrow
  have rowOne : atomPairing design 0 1 ^ 2 + atomPairing design 1 2 ^ 2
      + atomPairing design 1 3 ^ 2 = 3 := by
    have hrow := hrel 1 1
    rw [hself 1, hcomm 1 2, hcomm 1 3] at hrow
    linear_combination hrow
  have rowTwo : atomPairing design 0 2 ^ 2 + atomPairing design 1 2 ^ 2
      + atomPairing design 2 3 ^ 2 = 3 := by
    have hrow := hrel 2 2
    rw [hself 2, hcomm 2 3] at hrow
    linear_combination hrow
  have rowThree : atomPairing design 0 3 ^ 2 + atomPairing design 1 3 ^ 2
      + atomPairing design 2 3 ^ 2 = 3 := by
    have hrow := hrel 3 3
    rw [hself 3] at hrow
    linear_combination hrow
  have pairZeroOne : atomPairing design 0 2 * atomPairing design 1 2
      + atomPairing design 0 3 * atomPairing design 1 3
      = -2 * atomPairing design 0 1 := by
    have hrow := hrel 0 1
    rw [hself 0, hself 1, hcomm 0 1, hcomm 0 2, hcomm 1 2, hcomm 0 3, hcomm 1 3] at hrow
    linear_combination hrow
  have pairZeroTwo : atomPairing design 0 1 * atomPairing design 1 2
      + atomPairing design 0 3 * atomPairing design 2 3
      = -2 * atomPairing design 0 2 := by
    have hrow := hrel 0 2
    rw [hself 0, hself 2, hcomm 0 1, hcomm 0 2, hcomm 0 3, hcomm 2 3] at hrow
    linear_combination hrow
  have pairZeroThree : atomPairing design 0 1 * atomPairing design 1 3
      + atomPairing design 0 2 * atomPairing design 2 3
      = -2 * atomPairing design 0 3 := by
    have hrow := hrel 0 3
    rw [hself 0, hself 3, hcomm 0 1, hcomm 0 2, hcomm 0 3] at hrow
    linear_combination hrow
  have pairOneTwo : atomPairing design 0 1 * atomPairing design 0 2
      + atomPairing design 1 3 * atomPairing design 2 3
      = -2 * atomPairing design 1 2 := by
    have hrow := hrel 1 2
    rw [hself 1, hself 2, hcomm 1 2, hcomm 1 3, hcomm 2 3] at hrow
    linear_combination hrow
  have pairOneThree : atomPairing design 0 1 * atomPairing design 0 3
      + atomPairing design 1 2 * atomPairing design 2 3
      = -2 * atomPairing design 1 3 := by
    have hrow := hrel 1 3
    rw [hself 1, hself 3, hcomm 1 2, hcomm 1 3] at hrow
    linear_combination hrow
  have pairTwoThree : atomPairing design 0 2 * atomPairing design 0 3
      + atomPairing design 1 2 * atomPairing design 1 3
      = -2 * atomPairing design 2 3 := by
    have hrow := hrel 2 3
    rw [hself 2, hself 3, hcomm 2 3] at hrow
    linear_combination hrow
  have capZeroOne := sq_le_one_of_gramRowRelations (atomPairing design 0 1)
    (atomPairing design 0 2) (atomPairing design 0 3) (atomPairing design 1 2)
    (atomPairing design 1 3) rowZero rowOne pairZeroOne
  have capZeroTwo := sq_le_one_of_gramRowRelations (atomPairing design 0 2)
    (atomPairing design 0 1) (atomPairing design 0 3) (atomPairing design 1 2)
    (atomPairing design 2 3) (by linarith) (by linarith) pairZeroTwo
  have capZeroThree := sq_le_one_of_gramRowRelations (atomPairing design 0 3)
    (atomPairing design 0 1) (atomPairing design 0 2) (atomPairing design 1 3)
    (atomPairing design 2 3) (by linarith) (by linarith) pairZeroThree
  have capOneTwo := sq_le_one_of_gramRowRelations (atomPairing design 1 2)
    (atomPairing design 0 1) (atomPairing design 1 3) (atomPairing design 0 2)
    (atomPairing design 2 3) (by linarith) (by linarith) pairOneTwo
  have capOneThree := sq_le_one_of_gramRowRelations (atomPairing design 1 3)
    (atomPairing design 0 1) (atomPairing design 1 2) (atomPairing design 0 3)
    (atomPairing design 2 3) (by linarith) (by linarith) pairOneThree
  have capTwoThree := sq_le_one_of_gramRowRelations (atomPairing design 2 3)
    (atomPairing design 0 2) (atomPairing design 1 2) (atomPairing design 0 3)
    (atomPairing design 1 3) (by linarith) (by linarith) pairTwoThree
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Every off-diagonal pairing of such a design squares to one. -/
theorem atomPairing_sq_eq_one_of_leverage_three (design : WeightedDesign 4 3)
    (hleverage : ∀ label, leverageOf (design.atom label) = 3)
    (hweight : ∀ label, design.weight label = 1 / 4)
    {first second : Fin 4} (hdistinct : first ≠ second) :
    atomPairing design first second ^ 2 = 1 := by
  obtain ⟨hZeroOne, hZeroTwo, hZeroThree, hOneTwo, hOneThree, hTwoThree⟩ :=
    gramSquares_eq_one_of_leverage_three design hleverage hweight
  have hcomm : ∀ leftLabel rightLabel : Fin 4,
      atomPairing design rightLabel leftLabel = atomPairing design leftLabel rightLabel :=
    fun leftLabel rightLabel => atomPairing_comm design rightLabel leftLabel
  fin_cases first <;> fin_cases second <;>
    first
      | exact absurd rfl hdistinct
      | assumption
      | (rw [hcomm]; assumption)

/-- **The sign lemma.**  Two signs summing to twice the negated anchor sign are
both the negated anchor: `(left + anchor)^2 + (right + anchor)^2` vanishes. -/
theorem eq_neg_of_unitSquares_of_sum (leftSign rightSign anchorSign : ℝ)
    (hleft : leftSign ^ 2 = 1) (hright : rightSign ^ 2 = 1) (hanchor : anchorSign ^ 2 = 1)
    (hsum : leftSign + rightSign = -2 * anchorSign) :
    leftSign = -anchorSign := by
  have hvanish : (leftSign + anchorSign) ^ 2 + (rightSign + anchorSign) ^ 2 = 0 := by
    linear_combination hleft + hright - 2 * hanchor + 2 * anchorSign * hsum
  have hsquare : (leftSign + anchorSign) ^ 2 = 0 := by
    nlinarith [sq_nonneg (leftSign + anchorSign), sq_nonneg (rightSign + anchorSign)]
  have hzero := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsquare
  linarith

/-- **The off-pair product law.**  For three distinct labels, the third label's
two pairings against the first two multiply to the NEGATED pairing of the first
two.  Proved from the Gram row relation at the pair `(pivot, first)`: peeling the
pivot, the partner and the third label leaves a single fourth label, both
remaining products are signs, and they sum to `-2` times the pair's pairing.  No
enumeration of `Fin 4` appears -- the fourth label is produced by a cardinality
argument. -/
theorem atomPairing_mul_atomPairing_eq_neg_atomPairing (design : WeightedDesign 4 3)
    (hleverage : ∀ label, leverageOf (design.atom label) = 3)
    (hweight : ∀ label, design.weight label = 1 / 4)
    {pivot first second : Fin 4} (hpivotFirst : pivot ≠ first)
    (hpivotSecond : pivot ≠ second) (hfirstSecond : first ≠ second) :
    atomPairing design second pivot * atomPairing design second first
      = - atomPairing design pivot first := by
  classical
  have hunit : ∀ leftLabel rightLabel : Fin 4, leftLabel ≠ rightLabel →
      atomPairing design leftLabel rightLabel ^ 2 = 1 :=
    fun leftLabel rightLabel hne =>
      atomPairing_sq_eq_one_of_leverage_three design hleverage hweight hne
  have hself : ∀ label : Fin 4, atomPairing design label label = 3 := by
    intro label
    rw [atomPairing_self, hleverage]
  have htotal : ∑ label : Fin 4,
        atomPairing design label pivot * atomPairing design label first
      = 4 * atomPairing design pivot first := by
    have hpolar := atomPairing_eq_sum_weight_mul_atomPairing design pivot first
    have hscale : ∑ label : Fin 4, design.weight label
          * (atomPairing design label pivot * atomPairing design label first)
        = (1 / 4) * ∑ label : Fin 4,
            atomPairing design label pivot * atomPairing design label first := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun label _ => by rw [hweight label]
    rw [hscale] at hpolar
    linarith
  have hpivotMem : pivot ∈ (Finset.univ : Finset (Fin 4)) := Finset.mem_univ pivot
  have hfirstMem : first ∈ (Finset.univ : Finset (Fin 4)).erase pivot :=
    Finset.mem_erase.mpr ⟨Ne.symm hpivotFirst, Finset.mem_univ first⟩
  have hsecondMem : second ∈ ((Finset.univ : Finset (Fin 4)).erase pivot).erase first :=
    Finset.mem_erase.mpr ⟨Ne.symm hfirstSecond,
      Finset.mem_erase.mpr ⟨Ne.symm hpivotSecond, Finset.mem_univ second⟩⟩
  have hpeelPivot := Finset.add_sum_erase (Finset.univ : Finset (Fin 4))
    (fun label => atomPairing design label pivot * atomPairing design label first) hpivotMem
  have hpeelFirst := Finset.add_sum_erase ((Finset.univ : Finset (Fin 4)).erase pivot)
    (fun label => atomPairing design label pivot * atomPairing design label first) hfirstMem
  have hpeelSecond :=
    Finset.add_sum_erase (((Finset.univ : Finset (Fin 4)).erase pivot).erase first)
      (fun label => atomPairing design label pivot * atomPairing design label first) hsecondMem
  have hcardResidual :
      ((((Finset.univ : Finset (Fin 4)).erase pivot).erase first).erase second).card = 1 := by
    rw [Finset.card_erase_of_mem hsecondMem, Finset.card_erase_of_mem hfirstMem,
      Finset.card_erase_of_mem hpivotMem, Finset.card_univ, Fintype.card_fin]
  obtain ⟨fourth, hresidual⟩ := Finset.card_eq_one.mp hcardResidual
  have hfourthMem :
      fourth ∈ (((Finset.univ : Finset (Fin 4)).erase pivot).erase first).erase second := by
    rw [hresidual]
    exact Finset.mem_singleton_self fourth
  have hsumResidual : ∑ label ∈ (((Finset.univ : Finset (Fin 4)).erase pivot).erase first).erase
        second, atomPairing design label pivot * atomPairing design label first
      = atomPairing design fourth pivot * atomPairing design fourth first := by
    rw [hresidual, Finset.sum_singleton]
  have hfourthFirst : fourth ≠ first :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase hfourthMem)).1
  have hfourthPivot : fourth ≠ pivot :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase
      (Finset.mem_of_mem_erase hfourthMem))).1
  have hpairSq := hunit pivot first hpivotFirst
  have hsecondPivotSq := hunit second pivot (Ne.symm hpivotSecond)
  have hsecondFirstSq := hunit second first (Ne.symm hfirstSecond)
  have hfourthPivotSq := hunit fourth pivot hfourthPivot
  have hfourthFirstSq := hunit fourth first hfourthFirst
  have hleftSq : (atomPairing design second pivot * atomPairing design second first) ^ 2 = 1 := by
    rw [mul_pow, hsecondPivotSq, hsecondFirstSq]
    norm_num
  have hrightSq : (atomPairing design fourth pivot * atomPairing design fourth first) ^ 2 = 1 := by
    rw [mul_pow, hfourthPivotSq, hfourthFirstSq]
    norm_num
  have hpivotTerm : atomPairing design pivot pivot = 3 := hself pivot
  have hfirstTerm : atomPairing design first first = 3 := hself first
  have hswap : atomPairing design first pivot = atomPairing design pivot first :=
    atomPairing_comm design first pivot
  rw [hsumResidual] at hpeelSecond
  rw [← hpeelSecond] at hpeelFirst
  rw [← hpeelFirst] at hpeelPivot
  rw [← hpeelPivot, hpivotTerm, hfirstTerm, hswap] at htotal
  refine eq_neg_of_unitSquares_of_sum _
    (atomPairing design fourth pivot * atomPairing design fourth first)
    (atomPairing design pivot first) hleftSq hrightSq hpairSq ?_
  linarith

/-- **THE TRIPLE-PRODUCT RIGIDITY.**  The three pairings of any triple multiply to
`-1`.  This is the invariant that pins the tetrahedron's Gram beyond the entrywise
`+-1`: the signs cannot be chosen independently. -/
theorem atomPairing_tripleProduct_eq_neg_one (design : WeightedDesign 4 3)
    (hleverage : ∀ label, leverageOf (design.atom label) = 3)
    (hweight : ∀ label, design.weight label = 1 / 4)
    {pivot first second : Fin 4} (hpivotFirst : pivot ≠ first)
    (hpivotSecond : pivot ≠ second) (hfirstSecond : first ≠ second) :
    atomPairing design pivot first * atomPairing design pivot second
        * atomPairing design first second
      = -1 := by
  have hproduct := atomPairing_mul_atomPairing_eq_neg_atomPairing design hleverage hweight
    hpivotFirst hpivotSecond hfirstSecond
  have hpairSq := atomPairing_sq_eq_one_of_leverage_three design hleverage hweight hpivotFirst
  have hswapSecond : atomPairing design pivot second = atomPairing design second pivot :=
    atomPairing_comm design pivot second
  have hswapFirst : atomPairing design first second = atomPairing design second first :=
    atomPairing_comm design first second
  rw [hswapSecond, hswapFirst]
  linear_combination atomPairing design pivot first * hproduct - hpairSq

/-! ### The discriminant system at the rigid Gram -/

/-- Every triple of such a design sits exactly on the tie boundary. -/
theorem discriminantTie_eq_zero_of_noStrictTriple (design : WeightedDesign 4 3)
    (hcap : ∀ label, design.weight label ≤ 1 / 4)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef)
    {pivot first second : Fin 4} (hpivotFirst : pivot ≠ first)
    (hpivotSecond : pivot ≠ second) (hfirstSecond : first ≠ second) :
    discriminantTie design pivot first second = 0 := by
  have hweight := weight_eq_quarter_of_weight_le_quarter design hcap
  have hleverage := leverageOf_eq_three_of_noStrictTriple design hcap hnoStrictTriple
  have hexcess := heavyExcess_eq_two_of_noStrictTriple design hcap hnoStrictTriple
  have htriple := atomPairing_tripleProduct_eq_neg_one design hleverage hweight
    hpivotFirst hpivotSecond hfirstSecond
  have hpivotFirstSq :=
    atomPairing_sq_eq_one_of_leverage_three design hleverage hweight hpivotFirst
  have hpivotSecondSq :=
    atomPairing_sq_eq_one_of_leverage_three design hleverage hweight hpivotSecond
  have hfirstSecondSq :=
    atomPairing_sq_eq_one_of_leverage_three design hleverage hweight hfirstSecond
  rw [discriminantTie, hexcess pivot, hexcess first, hexcess second]
  linear_combination (-2) * hfirstSecondSq + (-2) * hpivotFirstSq + (-2) * hpivotSecondSq
    + 2 * htriple

/-- Every triple of such a design has trace leg exactly six. -/
theorem discriminantTrace_eq_six_of_noStrictTriple (design : WeightedDesign 4 3)
    (hcap : ∀ label, design.weight label ≤ 1 / 4)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef)
    {pivot first second : Fin 4} (hpivotFirst : pivot ≠ first)
    (hpivotSecond : pivot ≠ second) :
    discriminantTrace design pivot first second = 6 := by
  have hweight := weight_eq_quarter_of_weight_le_quarter design hcap
  have hleverage := leverageOf_eq_three_of_noStrictTriple design hcap hnoStrictTriple
  have hexcess := heavyExcess_eq_two_of_noStrictTriple design hcap hnoStrictTriple
  have hpivotFirstSq :=
    atomPairing_sq_eq_one_of_leverage_three design hleverage hweight hpivotFirst
  have hpivotSecondSq :=
    atomPairing_sq_eq_one_of_leverage_three design hleverage hweight hpivotSecond
  rw [discriminantTrace, hexcess pivot, hexcess first, hexcess second]
  linarith

/-- Every triple of such a design DOMINATES weakly -- the tie's existence half,
supplied by the shipped narrowing `Gtz.dominates_triple_iff_discriminantSystem`. -/
theorem dominates_triple_of_noStrictTriple (design : WeightedDesign 4 3)
    (hcap : ∀ label, design.weight label ≤ 1 / 4)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef)
    {pivot first second : Fin 4} (hpivotFirst : pivot ≠ first)
    (hpivotSecond : pivot ≠ second) (hfirstSecond : first ≠ second) :
    Dominates design {pivot, first, second} := by
  have hleverage := leverageOf_eq_three_of_noStrictTriple design hcap hnoStrictTriple
  have hpivotHeavy : 1 < leverageOf (design.atom pivot) := by
    rw [hleverage pivot]
    norm_num
  refine (dominates_triple_iff_discriminantSystem design hpivotFirst hpivotSecond
    hfirstSecond hpivotHeavy).mpr ⟨?_, ?_⟩
  · rw [discriminantTrace_eq_six_of_noStrictTriple design hcap hnoStrictTriple
      hpivotFirst hpivotSecond]
    norm_num
  · rw [discriminantTie_eq_zero_of_noStrictTriple design hcap hnoStrictTriple
      hpivotFirst hpivotSecond hfirstSecond]

/-- **THE CAPSTONE.**  A `(4,3)` design whose weights never exceed the uniform
value and which has NO strictly dominating triple is an exact tie: every triple
weakly dominates and none strictly does.  So the hypothesis "no strict dominator"
is not merely consistent at `(4,3)` -- it forces the maximal degeneracy. -/
theorem isTie_of_noStrictTriple (design : WeightedDesign 4 3)
    (hcap : ∀ label, design.weight label ≤ 1 / 4)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef) :
    IsTie design :=
  ⟨⟨{0, 1, 2}, by decide,
    dominates_triple_of_noStrictTriple design hcap hnoStrictTriple
      (by decide) (by decide) (by decide)⟩,
    hnoStrictTriple⟩

/-- **THE `(4,3)` INVARIANT RIGIDITY, packaged.**  Weights at the uniform cap and
no strictly dominating triple pin every Gram invariant of the design: all four
weights are `1/4`, all four leverages are `3`, all six pairings square to `1`,
and every triple of pairings multiplies to `-1`.  That data is precisely the
regular tetrahedron's Gram, up to the sign flips `g -> -g` that leave every atom
matrix unchanged; no orthogonal normal form is computed anywhere. -/
theorem gramRigidity_of_noStrictTriple (design : WeightedDesign 4 3)
    (hcap : ∀ label, design.weight label ≤ 1 / 4)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef) :
    (∀ label : Fin 4, design.weight label = 1 / 4)
      ∧ (∀ label : Fin 4, leverageOf (design.atom label) = 3)
      ∧ (∀ first second : Fin 4, first ≠ second → atomPairing design first second ^ 2 = 1)
      ∧ (∀ pivot first second : Fin 4, pivot ≠ first → pivot ≠ second → first ≠ second →
          atomPairing design pivot first * atomPairing design pivot second
            * atomPairing design first second = -1) := by
  have hweight := weight_eq_quarter_of_weight_le_quarter design hcap
  have hleverage := leverageOf_eq_three_of_noStrictTriple design hcap hnoStrictTriple
  exact ⟨hweight, hleverage,
    fun _ _ hdistinct =>
      atomPairing_sq_eq_one_of_leverage_three design hleverage hweight hdistinct,
    fun _ _ _ hpivotFirst hpivotSecond hfirstSecond =>
      atomPairing_tripleProduct_eq_neg_one design hleverage hweight hpivotFirst hpivotSecond
        hfirstSecond⟩

/-- **THE SIGN NORMALISATION.**  The `+-1` pattern of the pairings is not free:
the triple-product law says exactly that the pattern is a coboundary.  Anchoring
at label `0` produces signs with `atomPairing first second = -(sign first * sign
second)` for every distinct pair -- so the whole Gram is determined by four signs
and nothing else. -/
theorem exists_signChoice_of_noStrictTriple (design : WeightedDesign 4 3)
    (hcap : ∀ label, design.weight label ≤ 1 / 4)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef) :
    ∃ signChoice : Fin 4 → ℝ, (∀ label : Fin 4, signChoice label ^ 2 = 1)
      ∧ ∀ first second : Fin 4, first ≠ second →
          atomPairing design first second = -(signChoice first * signChoice second) := by
  classical
  have hweight := weight_eq_quarter_of_weight_le_quarter design hcap
  have hleverage := leverageOf_eq_three_of_noStrictTriple design hcap hnoStrictTriple
  have hunit : ∀ leftLabel rightLabel : Fin 4, leftLabel ≠ rightLabel →
      atomPairing design leftLabel rightLabel ^ 2 = 1 :=
    fun _ _ hne => atomPairing_sq_eq_one_of_leverage_three design hleverage hweight hne
  refine ⟨fun label => if label = 0 then 1 else - atomPairing design 0 label, ?_, ?_⟩
  · intro label
    dsimp only
    by_cases hzero : label = 0
    · rw [if_pos hzero]
      norm_num
    · rw [if_neg hzero, neg_sq]
      exact hunit 0 label (Ne.symm hzero)
  · intro first second hdistinct
    dsimp only
    by_cases hfirstZero : first = 0
    · have hsecondZero : second ≠ 0 := by
        rw [hfirstZero] at hdistinct
        exact Ne.symm hdistinct
      rw [if_pos hfirstZero, if_neg hsecondZero, hfirstZero]
      ring
    · by_cases hsecondZero : second = 0
      · rw [if_neg hfirstZero, if_pos hsecondZero, hsecondZero,
          atomPairing_comm design first 0]
        ring
      · rw [if_neg hfirstZero, if_neg hsecondZero]
        have htriple := atomPairing_tripleProduct_eq_neg_one design hleverage hweight
          (Ne.symm hfirstZero) (Ne.symm hsecondZero) hdistinct
        have hfirstSq := hunit 0 first (Ne.symm hfirstZero)
        have hsecondSq := hunit 0 second (Ne.symm hsecondZero)
        linear_combination
          (atomPairing design 0 first * atomPairing design 0 second) * htriple
            - atomPairing design first second * atomPairing design 0 second ^ 2 * hfirstSq
            - atomPairing design first second * hsecondSq

/-- **THE CROWN: the Gram IS the tetrahedron's.**  Flipping each atom by its sign
-- an operation that changes no atom matrix, hence no subset sum, hence nothing
the GTZ problem can see -- turns the design's Gram into `diag 3` with every
off-diagonal entry exactly `-1`.  That is precisely the Gram of
`Gtz.tetraAtom`.  The classification is complete at the invariant level; only the
orthogonal transformation carrying one realisation to another is left unnamed,
and it carries no information a Gram does not. -/
theorem exists_tetrahedralGram_of_noStrictTriple (design : WeightedDesign 4 3)
    (hcap : ∀ label, design.weight label ≤ 1 / 4)
    (hnoStrictTriple : ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum design candidate - 1).PosDef) :
    ∃ normalisedAtom : Fin 4 → (Fin 3 → ℝ),
      (∀ label : Fin 4, atomMatrix (normalisedAtom label) = atomMatrix (design.atom label))
        ∧ (∀ label : Fin 4, normalisedAtom label ⬝ᵥ normalisedAtom label = 3)
        ∧ ∀ first second : Fin 4, first ≠ second →
            normalisedAtom first ⬝ᵥ normalisedAtom second = -1 := by
  obtain ⟨signChoice, hsignSq, hpairing⟩ :=
    exists_signChoice_of_noStrictTriple design hcap hnoStrictTriple
  have hleverage := leverageOf_eq_three_of_noStrictTriple design hcap hnoStrictTriple
  refine ⟨fun label => signChoice label • design.atom label, ?_, ?_, ?_⟩
  · intro label
    rw [atomMatrix_smul, hsignSq label, one_smul]
  · intro label
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← leverageOf_eq_dotProduct, hleverage label]
    nlinarith [hsignSq label]
  · intro first second hdistinct
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      show design.atom first ⬝ᵥ design.atom second = atomPairing design first second from rfl,
      hpairing first second hdistinct]
    nlinarith [hsignSq first, hsignSq second]

/-- The tetrahedron's own Gram, for comparison with the crown: leverage three and
every distinct pairing exactly `-1`. -/
theorem tetraAtom_dot_eq_neg_one {first second : Fin 4} (hdistinct : first ≠ second) :
    tetraAtom first ⬝ᵥ tetraAtom second = -1 := by
  fin_cases first <;> fin_cases second <;>
    simp_all [tetraAtom, dotProduct, Fin.sum_univ_three]

/-! ## Part 7. Target (c): sharpness at the regular tetrahedron -/

theorem tetraDesign_weight_apply (label : Fin 4) : tetraDesign.weight label = 1 / 4 := rfl

/-- Every tetrahedron share is exactly `3/4`. -/
theorem tetraDesign_atomShare (label : Fin 4) : atomShare tetraDesign label = 3 / 4 := by
  rw [atomShare, tetraDesign_weight_apply, tetraDesign_leverage]
  norm_num

/-- **SHARPNESS OF TARGET (a).**  At the tetrahedron the per-label pin holds with
EQUALITY: the share equals `1 - weight` exactly, so the complement engine's
hypothesis fails by precisely zero at all four triples.  This is the four-triple
analogue of the shipped six-pair statement
`Gtz.tetraDesign_pairCap_attained`. -/
theorem tetraDesign_atomShare_eq_one_sub_weight (label other : Fin 4) :
    atomShare tetraDesign label = 1 - tetraDesign.weight other := by
  rw [tetraDesign_atomShare, tetraDesign_weight_apply]
  norm_num

/-- The engine can never fire at the tetrahedron: the strict hypothesis is exactly
missed. -/
theorem tetraDesign_not_atomShare_lt_one_sub_weight (label other : Fin 4) :
    ¬ atomShare tetraDesign label < 1 - tetraDesign.weight other := by
  rw [tetraDesign_atomShare_eq_one_sub_weight label other]
  exact lt_irrefl _

/-- **SHARPNESS OF TARGET (b), summed.**  The four pins add up with no slack: the
share total `3` equals `4 * (1 - 1/4)` on the nose, so the slack budget
`4 * topWeight - 1` is zero at the tetrahedron. -/
theorem tetraDesign_sum_atomShare_slack_eq_zero :
    (atomShare tetraDesign 0 - (1 - 1 / 4)) + (atomShare tetraDesign 1 - (1 - 1 / 4))
        + (atomShare tetraDesign 2 - (1 - 1 / 4)) + (atomShare tetraDesign 3 - (1 - 1 / 4))
      = 0 := by
  rw [tetraDesign_atomShare, tetraDesign_atomShare, tetraDesign_atomShare, tetraDesign_atomShare]
  norm_num

/-- **SHARPNESS OF TARGET (b), bound form.**  The tetrahedron's own weight family
is a legitimate bound family for `one_le_sum_otherWeightBound`, and its four
bounds total exactly `1`: the inequality is ATTAINED, so no strengthening of the
summed statement is available. -/
theorem tetraDesign_sum_otherWeightBound_eq_one :
    tetraDesign.weight 0 + tetraDesign.weight 1 + tetraDesign.weight 2
        + tetraDesign.weight 3 = 1 := by
  rw [tetraDesign_weight_apply, tetraDesign_weight_apply, tetraDesign_weight_apply,
    tetraDesign_weight_apply]
  norm_num

/-- **SHARPNESS OF TARGET (b), sorted form.**  The tetrahedron attains
`1 <= 3 t(1) + t(2)` with equality: `3/4 + 1/4 = 1`. -/
theorem tetraDesign_three_mul_topWeight_add_secondWeight_eq_one :
    3 * tetraDesign.weight 0 + tetraDesign.weight 1 = 1 := by
  rw [tetraDesign_weight_apply, tetraDesign_weight_apply]
  norm_num

theorem tetraDesign_weight_le_quarter (label : Fin 4) : tetraDesign.weight label ≤ 1 / 4 := by
  rw [tetraDesign_weight_apply]

/-- The tetrahedron has no strictly dominating triple -- the second half of the
shipped tie. -/
theorem tetraDesign_noStrictTriple (candidate : Finset (Fin 4)) (hcard : candidate.card = 3) :
    ¬ (subsetSum tetraDesign candidate - 1).PosDef :=
  tetraDesign_isTie.2 candidate hcard

/-- **NON-VACUITY, AND A SOUNDNESS CROSS-CHECK.**  The rigidity's hypotheses hold
at the shipped tetrahedron, and the invariants it predicts are the ones the tree
already records independently (`Gtz.tetraDesign_leverage`,
`Gtz.tetraAtom_dot_sq_of_ne`).  So the theorem is neither vacuous nor in conflict
with the shipped fixture data. -/
theorem tetraDesign_gramRigidity :
    (∀ label : Fin 4, tetraDesign.weight label = 1 / 4)
      ∧ (∀ label : Fin 4, leverageOf (tetraDesign.atom label) = 3)
      ∧ (∀ first second : Fin 4, first ≠ second → atomPairing tetraDesign first second ^ 2 = 1)
      ∧ (∀ pivot first second : Fin 4, pivot ≠ first → pivot ≠ second → first ≠ second →
          atomPairing tetraDesign pivot first * atomPairing tetraDesign pivot second
            * atomPairing tetraDesign first second = -1) :=
  gramRigidity_of_noStrictTriple tetraDesign tetraDesign_weight_le_quarter
    tetraDesign_noStrictTriple

/-- The rigidity's pairing conclusion agrees with the shipped tetrahedron data. -/
theorem tetraDesign_atomPairing_sq_eq_tetraAtom_dot_sq {first second : Fin 4}
    (hdistinct : first ≠ second) :
    atomPairing tetraDesign first second ^ 2 = (tetraAtom first ⬝ᵥ tetraAtom second) ^ 2 := by
  rw [tetraDesign_gramRigidity.2.2.1 first second hdistinct,
    tetraAtom_dot_sq_of_ne hdistinct]

end Gtz

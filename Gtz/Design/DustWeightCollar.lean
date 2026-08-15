import Gtz.Design.WeightAwareClearance
import Gtz.Design.DirectionBudget
import Gtz.Design.LeverageBound
import Gtz.Design.MarginTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The dust-weight collar of the `U(3,6)` line-free off-conic cell

`Gtz.weightAwareClearanceOf` caps the landed wall clearance by a scaled smallest
raw weight, so its collar is the UNION of two legs.  The wall leg is landed.  This
file builds the second leg, the one the dust-weight channel escapes through, and
it builds it as a QUANTITATIVE gate rather than a witness list.

The mechanism is a change of who carries the burden.  `Gtz.subsetSum` is
weight-free, so a label of small raw weight and non-vanishing mass has a LARGE
atom: `leverageOf (atom c) = massOf c / weight c`.  A large atom covers its own
direction by itself, and only the plane orthogonal to it still needs a pair.  So
the dust weight is not an obstruction to domination -- it is a supply of it, and
the collar leg is a statement about the ORTHOGONAL PLANE alone.

Three things are proved.

* **The plane budget at a label.**  Parseval restricted to `atom c`'s orthogonal
  complement is carried by the OTHER five labels alone, with total weight
  `1 - weight c`.  Averaging then forces a STRICT over-reader: at every probe in
  the plane some other label reads at least `1 / (1 - weight c)` times the probe
  energy.  The relative excess is exactly `weight c / (1 - weight c)`, which is
  the measured `margin ~ dust weight` law of this stratum, now derived.
* **The leverage gate.**  Cauchy-Schwarz collapses the landed insert-completion
  collar hypothesis to one inequality with no cross terms at all:
  `leverageOf p + leverageOf q < marginRatio * (leverageOf c - 1)`.
  The coupling never appears.
* **The threshold in the raw weight.**  Dividing the gate by `weight c` turns it
  into an explicit dust threshold: with a mass floor `massFloor` on the light
  label and a leverage cap `leverageCap` on the kept pair, EVERY raw weight below
  `marginRatio * massFloor / (leverageCap + marginRatio)` completes the triple.
  The collar leg is therefore a genuine neighbourhood of the light-weight face.

What remains open is named, not hidden: `Gtz.PlaneMarginProducerAtLightLabel`.
The plane budget supplies a per-probe over-reader, and rank-two GTZ
(`Gtz.exists_inPlane_dominating_pair`) supplies a pair at margin exactly ZERO.
The gap between them is the whole residual, and this file measures it: the
producer needs margin `marginRatio` where the landed pair gives `0`.
-/

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The weight of one label, and the weight of the rest -/

/-- The weights of the other labels sum to the complement of this one. -/
theorem sum_weight_erase (design : WeightedDesign m k) (label : Fin m) :
    ∑ other ∈ Finset.univ.erase label, design.weight other = 1 - design.weight label := by
  have hsplit : design.weight label + ∑ other ∈ Finset.univ.erase label, design.weight other
      = ∑ other, design.weight other :=
    Finset.add_sum_erase _ _ (Finset.mem_univ label)
  rw [design.weight_sum_one] at hsplit
  linarith

/-- **THE COMPLEMENT WEIGHT IS THE WHOLE DEFICIT.**  The other labels carry
`1 - weight label`, and that quantity is strictly positive whenever another label
exists.  This deficit is the entire source of the strict over-reading below.

The landed `Gtz.design_weight_lt_one` proves the same positivity from a size bound
`2 ≤ m`.  This form reads the nonemptiness directly, which is what the summation
lemma downstream already supplies. -/
theorem complementWeight_pos (design : WeightedDesign m k) (label : Fin m)
    (hother : (Finset.univ.erase label).Nonempty) :
    0 < 1 - design.weight label := by
  have hpos := Finset.sum_pos (fun other (_ : other ∈ Finset.univ.erase label) =>
    design.weight_pos other) hother
  rw [sum_weight_erase design label] at hpos
  exact hpos

/-! ## The plane budget at a label

Parseval read as a quadratic form is `Gtz.sum_weight_mul_sq_reading`.  At a probe
orthogonal to one atom that atom contributes nothing, so the whole probe energy is
carried by the other labels -- whose total weight is strictly less than one.  That
deficit is the entire source of the strict over-reading below.
-/

/-- **THE PLANE BUDGET AT A LABEL.**  Every probe orthogonal to `atom label` has
its energy supplied by the OTHER labels alone. -/
theorem planeBudget_at_label (design : WeightedDesign m k) (label : Fin m)
    (probe : Fin k → ℝ) (horth : design.atom label ⬝ᵥ probe = 0) :
    ∑ other ∈ Finset.univ.erase label,
        design.weight other * (design.atom other ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
  have hsplit : design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
        + ∑ other ∈ Finset.univ.erase label,
            design.weight other * (design.atom other ⬝ᵥ probe) ^ 2
      = ∑ other, design.weight other * (design.atom other ⬝ᵥ probe) ^ 2 :=
    Finset.add_sum_erase Finset.univ
      (fun other => design.weight other * (design.atom other ⬝ᵥ probe) ^ 2)
      (Finset.mem_univ label)
  rw [sum_weight_mul_sq_reading design probe] at hsplit
  rw [horth] at hsplit
  simpa using hsplit

/-- **THE STRICT OVER-READER, DIVISION-FREE.**  At every nonzero probe orthogonal
to `atom label` some OTHER label reads the probe at least `1 / (1 - weight label)`
times its energy.  The excess is supplied by the light label's own weight, so the
lighter the label the stronger the over-reading. -/
theorem exists_planeOverReader (design : WeightedDesign m k) (label : Fin m)
    (hother : (Finset.univ.erase label).Nonempty)
    (probe : Fin k → ℝ) (horth : design.atom label ⬝ᵥ probe = 0) :
    ∃ other ∈ Finset.univ.erase label,
      probe ⬝ᵥ probe
        ≤ (1 - design.weight label) * (design.atom other ⬝ᵥ probe) ^ 2 := by
  by_contra hnone
  have hunder : ∀ other ∈ Finset.univ.erase label,
      (1 - design.weight label) * (design.atom other ⬝ᵥ probe) ^ 2 < probe ⬝ᵥ probe := by
    intro other hmem
    by_contra hge
    exact hnone ⟨other, hmem, not_lt.mp hge⟩
  have hcompl : (0 : ℝ) < 1 - design.weight label := complementWeight_pos design label hother
  -- Every other label under-reads, so the weighted total falls short of the budget.
  have hstrict : ∀ other ∈ Finset.univ.erase label,
      design.weight other * (design.atom other ⬝ᵥ probe) ^ 2
        < design.weight other * ((probe ⬝ᵥ probe) / (1 - design.weight label)) := by
    intro other hmem
    refine mul_lt_mul_of_pos_left ?_ (design.weight_pos other)
    rw [lt_div_iff₀ hcompl, mul_comm]
    exact hunder other hmem
  have hsum := Finset.sum_lt_sum_of_nonempty hother hstrict
  rw [planeBudget_at_label design label probe horth, ← Finset.sum_mul,
    sum_weight_erase design label] at hsum
  rw [mul_div_assoc'] at hsum
  rw [mul_div_cancel_left₀ _ (ne_of_gt hcompl)] at hsum
  exact lt_irrefl _ hsum

/-- **THE OVER-READING EXCESS IS THE DUST WEIGHT.**  The same statement with the
excess exhibited: the over-reader beats the probe energy by the relative amount
`weight label / (1 - weight label)`.  This is the stratum's measured
`margin ~ dust weight` law, derived rather than sampled. -/
theorem exists_planeOverReader_excess (design : WeightedDesign m k) (label : Fin m)
    (hother : (Finset.univ.erase label).Nonempty)
    (probe : Fin k → ℝ) (horth : design.atom label ⬝ᵥ probe = 0) :
    ∃ other ∈ Finset.univ.erase label,
      (1 + design.weight label / (1 - design.weight label)) * (probe ⬝ᵥ probe)
        ≤ (design.atom other ⬝ᵥ probe) ^ 2 := by
  obtain ⟨other, hmem, hread⟩ :=
    exists_planeOverReader design label hother probe horth
  refine ⟨other, hmem, ?_⟩
  have hcompl : (0 : ℝ) < 1 - design.weight label := complementWeight_pos design label hother
  have hfactor : 1 + design.weight label / (1 - design.weight label)
      = 1 / (1 - design.weight label) := by
    field_simp
    ring
  rw [hfactor, div_mul_eq_mul_div, div_le_iff₀ hcompl, one_mul, mul_comm]
  exact hread

/-! ## The plane margin of a pair against a label -/

/-- **THE PLANE MARGIN.**  The pair `(keptOne, keptTwo)` covers the plane
orthogonal to `atom insertLabel` with relative surplus `marginRatio`.  This is
exactly the hypothesis shape of the landed
`Gtz.posDef_insertCompletion_of_planeMargin`. -/
def PlaneMarginAt (design : WeightedDesign m k) (keptOne keptTwo insertLabel : Fin m)
    (marginRatio : ℝ) : Prop :=
  ∀ probe : Fin k → ℝ, design.atom insertLabel ⬝ᵥ probe = 0 →
    (1 + marginRatio) * (probe ⬝ᵥ probe)
      ≤ (design.atom keptOne ⬝ᵥ probe) ^ 2 + (design.atom keptTwo ⬝ᵥ probe) ^ 2

/-- A larger margin is a stronger statement. -/
theorem PlaneMarginAt.mono {design : WeightedDesign m k} {keptOne keptTwo insertLabel : Fin m}
    {marginRatio smaller : ℝ} (hmargin : PlaneMarginAt design keptOne keptTwo insertLabel
      marginRatio) (hle : smaller ≤ marginRatio) :
    PlaneMarginAt design keptOne keptTwo insertLabel smaller := by
  intro probe horth
  refine le_trans ?_ (hmargin probe horth)
  have hprobe : 0 ≤ probe ⬝ᵥ probe := dotProduct_self_nonneg probe
  nlinarith [hprobe, hle]

/-! ## The leverage gate

The landed insert-completion theorem asks for the cross coupling to sit below
`marginRatio * leverage * (leverage - 1)`.  Cauchy-Schwarz bounds that coupling by
the kept leverages times the insert leverage, and the insert leverage then cancels
from both sides.  What is left carries no cross term at all.
-/

/-- **THE CROSS COUPLING, PRICED BY LEVERAGES ALONE.**  Cauchy-Schwarz through the
landed `Gtz.atom_form_le_leverage` bounds the kept pair's coupling against the
insert atom by the leverages, with no angle and no cross term surviving. -/
theorem coupling_le_leverageSum_mul (design : WeightedDesign m k)
    (keptOne keptTwo insertLabel : Fin m) :
    (design.atom keptOne ⬝ᵥ design.atom insertLabel) ^ 2
        + (design.atom keptTwo ⬝ᵥ design.atom insertLabel) ^ 2
      ≤ (leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo))
        * leverageOf (design.atom insertLabel) := by
  have hone := atom_form_le_leverage (design.atom keptOne) (design.atom insertLabel)
  have htwo := atom_form_le_leverage (design.atom keptTwo) (design.atom insertLabel)
  rw [atom_form_eq_sq, ← leverageOf_eq_dotProduct] at hone htwo
  nlinarith [hone, htwo]

/-- **THE LEVERAGE GATE.**  A pair with a positive plane margin against the insert
atom completes to a STRICTLY dominating triple as soon as the kept leverages fall
below the margin times the insert's leverage defect.

The cross coupling has disappeared.  Only three leverages and the margin remain,
and the inequality is division-free. -/
theorem posDef_insert_of_leverageGap (design : WeightedDesign m k)
    {keptOne keptTwo insertLabel : Fin m}
    (hneKepts : keptOne ≠ keptTwo) (hneOneInsert : keptOne ≠ insertLabel)
    (hneTwoInsert : keptTwo ≠ insertLabel)
    {marginRatio : ℝ} (hmarginPos : 0 < marginRatio)
    (hmargin : PlaneMarginAt design keptOne keptTwo insertLabel marginRatio)
    (hgap : leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
      < marginRatio * (leverageOf (design.atom insertLabel) - 1)) :
    (subsetSum design ({keptOne, keptTwo, insertLabel} : Finset (Fin m)) - 1).PosDef := by
  set keptSum : ℝ := leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
    with hkeptSumDef
  set insertLeverage : ℝ := leverageOf (design.atom insertLabel) with hinsertLeverageDef
  have hkeptNonneg : 0 ≤ keptSum := by
    rw [hkeptSumDef]
    exact add_nonneg (leverageOf_nonneg _) (leverageOf_nonneg _)
  -- The gap forces the insert atom to be strictly heavy.
  have hheavy : 1 < insertLeverage := by
    by_contra hnot
    have hle : insertLeverage ≤ 1 := not_lt.mp hnot
    nlinarith [hgap, hkeptNonneg, hmarginPos, hle]
  have hheavyDot : 1 < design.atom insertLabel ⬝ᵥ design.atom insertLabel := by
    rw [← leverageOf_eq_dotProduct]
    exact hheavy
  refine posDef_insertCompletion_of_planeMargin design hneKepts hneOneInsert hneTwoInsert
    hheavyDot hmarginPos hmargin ?_
  -- Cauchy-Schwarz, then cancel the insert leverage from both sides.
  have hcoupling := coupling_le_leverageSum_mul design keptOne keptTwo insertLabel
  have hleverageEq : design.atom insertLabel ⬝ᵥ design.atom insertLabel = insertLeverage :=
    (leverageOf_eq_dotProduct (design.atom insertLabel)).symm
  rw [hleverageEq]
  refine lt_of_le_of_lt hcoupling ?_
  have hpos : 0 < insertLeverage := by linarith
  nlinarith [hgap, hpos, hmarginPos]

/-! ## The threshold in the raw weight

The gate is a statement about leverages.  The mass identity `mass = weight *
leverage` turns it into a statement about the RAW WEIGHT of the insert label, and
that is the coordinate the dust channel moves along.
-/

/-- The mass of a label: its weight times its leverage.  This is the diagonal of
the whitened projection, and it is exactly the quantity that stays bounded away
from zero while the weight falls. -/
noncomputable def massOf (design : WeightedDesign m k) (label : Fin m) : ℝ :=
  design.weight label * leverageOf (design.atom label)

/-- The mass is nonnegative. -/
theorem massOf_nonneg (design : WeightedDesign m k) (label : Fin m) :
    0 ≤ massOf design label :=
  mul_nonneg (design.weight_pos label).le (leverageOf_nonneg _)

/-- **THE GATE IN THE WEIGHT CHART.**  Multiplying the leverage gate by the insert
weight replaces the insert leverage by the insert MASS.  Everything stays
division-free. -/
theorem posDef_insert_of_dustWeight (design : WeightedDesign m k)
    {keptOne keptTwo insertLabel : Fin m}
    (hneKepts : keptOne ≠ keptTwo) (hneOneInsert : keptOne ≠ insertLabel)
    (hneTwoInsert : keptTwo ≠ insertLabel)
    {marginRatio : ℝ} (hmarginPos : 0 < marginRatio)
    (hmargin : PlaneMarginAt design keptOne keptTwo insertLabel marginRatio)
    (hdust : design.weight insertLabel
        * (leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo) + marginRatio)
      < marginRatio * massOf design insertLabel) :
    (subsetSum design ({keptOne, keptTwo, insertLabel} : Finset (Fin m)) - 1).PosDef := by
  refine posDef_insert_of_leverageGap design hneKepts hneOneInsert hneTwoInsert hmarginPos
    hmargin ?_
  have hweightPos : 0 < design.weight insertLabel := design.weight_pos insertLabel
  rw [massOf] at hdust
  -- Divide the dust inequality by the strictly positive insert weight.
  have hexpand : marginRatio * (design.weight insertLabel * leverageOf (design.atom insertLabel))
      = design.weight insertLabel * (marginRatio * leverageOf (design.atom insertLabel)) := by
    ring
  rw [hexpand] at hdust
  have hcancel := lt_of_mul_lt_mul_left hdust hweightPos.le
  linarith

/-- **THE DUST THRESHOLD, EXPLICIT.**  With a mass floor on the insert label and a
leverage cap on the kept pair, every raw weight below
`marginRatio * massFloor / (leverageCap + marginRatio)` completes the triple.

This is the collar leg as an honest NEIGHBOURHOOD of the light-weight face: the
threshold is a positive constant built from the margin, the mass floor and the
leverage cap, and it does not read the atoms at all. -/
theorem posDef_insert_of_dust_of_massFloor (design : WeightedDesign m k)
    {keptOne keptTwo insertLabel : Fin m}
    (hneKepts : keptOne ≠ keptTwo) (hneOneInsert : keptOne ≠ insertLabel)
    (hneTwoInsert : keptTwo ≠ insertLabel)
    {marginRatio massFloor leverageCap dustThreshold : ℝ} (hmarginPos : 0 < marginRatio)
    (hmargin : PlaneMarginAt design keptOne keptTwo insertLabel marginRatio)
    (hmassFloor : massFloor ≤ massOf design insertLabel)
    (hleverageCap : leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
      ≤ leverageCap)
    (hcapNonneg : 0 ≤ leverageCap)
    (hlight : design.weight insertLabel ≤ dustThreshold)
    (hthreshold : dustThreshold * (leverageCap + marginRatio) < marginRatio * massFloor) :
    (subsetSum design ({keptOne, keptTwo, insertLabel} : Finset (Fin m)) - 1).PosDef := by
  refine posDef_insert_of_dustWeight design hneKepts hneOneInsert hneTwoInsert hmarginPos
    hmargin ?_
  have hsumLe : leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
      + marginRatio ≤ leverageCap + marginRatio := by linarith
  have hsumNonneg : (0 : ℝ) ≤ leverageCap + marginRatio := by linarith
  have hweightPos : 0 < design.weight insertLabel := design.weight_pos insertLabel
  calc design.weight insertLabel
        * (leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo) + marginRatio)
      ≤ design.weight insertLabel * (leverageCap + marginRatio) :=
        mul_le_mul_of_nonneg_left hsumLe hweightPos.le
    _ ≤ dustThreshold * (leverageCap + marginRatio) :=
        mul_le_mul_of_nonneg_right hlight hsumNonneg
    _ < marginRatio * massFloor := hthreshold
    _ ≤ marginRatio * massOf design insertLabel :=
        mul_le_mul_of_nonneg_left hmassFloor hmarginPos.le

/-- **THE THRESHOLD IS POSITIVE.**  A positive margin against a positive mass
floor always leaves room, so the dust leg is never vacuous for trivial reasons. -/
theorem dustThreshold_pos {marginRatio massFloor leverageCap : ℝ}
    (hmarginPos : 0 < marginRatio) (hmassPos : 0 < massFloor) (hcapNonneg : 0 ≤ leverageCap) :
    0 < marginRatio * massFloor / (leverageCap + marginRatio) := by
  have hden : 0 < leverageCap + marginRatio := by linarith
  exact div_pos (mul_pos hmarginPos hmassPos) hden

/-- Any weight strictly below the explicit threshold satisfies the product form
the gate consumes. -/
theorem dust_product_lt_of_lt_threshold {marginRatio massFloor leverageCap dustThreshold : ℝ}
    (hmarginPos : 0 < marginRatio) (hcapNonneg : 0 ≤ leverageCap)
    (hlt : dustThreshold < marginRatio * massFloor / (leverageCap + marginRatio)) :
    dustThreshold * (leverageCap + marginRatio) < marginRatio * massFloor := by
  have hden : 0 < leverageCap + marginRatio := by linarith
  rw [lt_div_iff₀ hden] at hlt
  exact hlt

/-! ## The collar leg as a named obligation

The two-family split asks for `Gtz.BoundaryCollarExcludesTies` at the WEIGHT-AWARE
functional.  Because that functional is a minimum, its collar is the union of the
landed wall collar and the new dust collar, and the split below is exact.
-/

/-- **THE DUST-WEIGHT COLLAR.**  Every line-free off-conic design whose smallest
raw weight sits below the threshold carries a strictly dominating triple. -/
def DustWeightCollarExcludesTies (dustThreshold : ℝ) : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    rawWeightClearanceOf design ≤ dustThreshold →
    ¬ IsTie design

/-- **THE COLLAR SPLITS EXACTLY.**  The weight-aware collar is the union of the
landed wall collar and the dust collar, so proving the two legs separately closes
it.  Nothing is lost in the split: the minimum is below the width exactly when one
of its two legs is. -/
theorem boundaryCollarExcludesTies_weightAware_of_split
    {weightScale collarWidth : ℝ} (hscalePos : 0 < weightScale)
    (hwallLeg : BoundaryCollarExcludesTies wallClearanceOf collarWidth)
    (hdustLeg : DustWeightCollarExcludesTies (collarWidth / weightScale)) :
    BoundaryCollarExcludesTies (weightAwareClearanceOf weightScale) collarWidth := by
  intro design hpattern hoffConic hclearance
  rw [weightAwareClearanceOf, min_le_iff] at hclearance
  rcases hclearance with hwall | hweight
  · exact hwallLeg design hpattern hoffConic hwall
  · refine hdustLeg design hpattern hoffConic ?_
    rw [le_div_iff₀ hscalePos, mul_comm]
    exact hweight

/-! ## The residual, named and measured

Everything above is unconditional.  What the dust leg still needs is a pair with a
POSITIVE plane margin at the light label, together with the leverage gap.  The
plane budget already supplies a per-probe over-reader and rank-two GTZ already
supplies a pair -- but at margin exactly zero.  That gap is the whole residual.
-/

/-- **THE PLANE-MARGIN PRODUCER.**  At every line-free off-conic design and every
sufficiently light label, some pair covers the orthogonal plane with a positive
surplus and stays below the leverage gap.

This is the ONLY open statement of the dust leg.  `Gtz.exists_planeOverReader`
supplies the surplus pointwise in the probe, and
`Gtz.exists_inPlane_dominating_pair` supplies a uniform pair at surplus zero. -/
def PlaneMarginProducerAtLightLabel (dustThreshold marginRatio : ℝ) : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    ∀ lightLabel : Fin 6, design.weight lightLabel ≤ dustThreshold →
      ∃ keptOne keptTwo : Fin 6, keptOne ≠ keptTwo ∧ keptOne ≠ lightLabel ∧
        keptTwo ≠ lightLabel ∧
        PlaneMarginAt design keptOne keptTwo lightLabel marginRatio ∧
        leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
          < marginRatio * (leverageOf (design.atom lightLabel) - 1)

/-- The smallest raw weight is attained at some label. -/
theorem exists_label_weight_eq_rawWeightClearance (design : WeightedDesign 6 3) :
    ∃ label : Fin 6, design.weight label = rawWeightClearanceOf design := by
  obtain ⟨label, _, heq⟩ :=
    Finset.exists_mem_eq_inf' (Finset.univ_nonempty) design.weight
  exact ⟨label, heq.symm⟩

/-- A card-three triple out of three distinct labels. -/
theorem card_insert_triple {keptOne keptTwo insertLabel : Fin 6}
    (hneKepts : keptOne ≠ keptTwo) (hneOneInsert : keptOne ≠ insertLabel)
    (hneTwoInsert : keptTwo ≠ insertLabel) :
    ({keptOne, keptTwo, insertLabel} : Finset (Fin 6)).card = 3 :=
  Finset.card_eq_three.mpr
    ⟨keptOne, keptTwo, insertLabel, hneKepts, hneOneInsert, hneTwoInsert, rfl⟩

/-- **THE DUST LEG FROM THE PRODUCER.**  A plane-margin producer at the threshold
closes the dust-weight collar outright. -/
theorem dustWeightCollarExcludesTies_of_producer {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hproducer : PlaneMarginProducerAtLightLabel dustThreshold marginRatio) :
    DustWeightCollarExcludesTies dustThreshold := by
  intro design hpattern hoffConic hclearance htie
  obtain ⟨lightLabel, hlightEq⟩ := exists_label_weight_eq_rawWeightClearance design
  have hlight : design.weight lightLabel ≤ dustThreshold := by
    rw [hlightEq]; exact hclearance
  obtain ⟨keptOne, keptTwo, hneKepts, hneOne, hneTwo, hmargin, hgap⟩ :=
    hproducer design hpattern hoffConic lightLabel hlight
  have hposDef := posDef_insert_of_leverageGap design hneKepts hneOne hneTwo hmarginPos
    hmargin hgap
  exact htie.2 _ (card_insert_triple hneKepts hneOne hneTwo) hposDef

/-- **THE WHOLE COLLAR FROM THE TWO LEGS.**  The landed wall collar plus the
producer close the weight-aware collar. -/
theorem boundaryCollarExcludesTies_weightAware_of_producer
    {weightScale collarWidth marginRatio : ℝ} (hscalePos : 0 < weightScale)
    (hmarginPos : 0 < marginRatio)
    (hwallLeg : BoundaryCollarExcludesTies wallClearanceOf collarWidth)
    (hproducer : PlaneMarginProducerAtLightLabel (collarWidth / weightScale) marginRatio) :
    BoundaryCollarExcludesTies (weightAwareClearanceOf weightScale) collarWidth :=
  boundaryCollarExcludesTies_weightAware_of_split hscalePos hwallLeg
    (dustWeightCollarExcludesTies_of_producer hmarginPos hproducer)

/-- **THE A1 CELL FROM THE REPAIRED FUNCTIONAL.**  The interior floor over the
weight-aware clearance, the landed wall collar and the plane-margin producer
together close tie-freeness of the whole line-free off-conic stratum.

Every hypothesis except the producer is either landed or discharged above. -/
theorem lineFreeOffConic_noTie_of_weightAware_of_producer
    {weightScale collarWidth marginFloor marginRatio : ℝ} (hscalePos : 0 < weightScale)
    (hcollarNonneg : 0 ≤ collarWidth) (hmarginFloorPos : 0 < marginFloor)
    (hmarginPos : 0 < marginRatio)
    (hbounded : WeightAwareInteriorFloor weightScale collarWidth marginFloor)
    (hwallLeg : BoundaryCollarExcludesTies wallClearanceOf collarWidth)
    (hproducer : PlaneMarginProducerAtLightLabel (collarWidth / weightScale) marginRatio) :
    ∀ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      ¬ IsTie design :=
  lineFreeOffConic_noTie_of_weightAwareBoundedAndCollar hcollarNonneg hmarginFloorPos hbounded
    (boundaryCollarExcludesTies_weightAware_of_producer hscalePos hmarginPos hwallLeg hproducer)

/-! ## What the landed rank-two pair does and does not give

`Gtz.exists_inPlane_dominating_pair` is rank-two GTZ transported into the plane.
It returns a pair covering every in-plane probe at surplus EXACTLY zero.  The
producer needs surplus `marginRatio`.  The two statements are recorded side by side
so the residual is a comparison of constants and not a vague gap.
-/

/-- The zero-surplus plane margin is exactly what a covering pair gives. -/
theorem planeMarginAt_zero_iff (design : WeightedDesign m k)
    (keptOne keptTwo insertLabel : Fin m) :
    PlaneMarginAt design keptOne keptTwo insertLabel 0
      ↔ ∀ probe : Fin k → ℝ, design.atom insertLabel ⬝ᵥ probe = 0 →
        probe ⬝ᵥ probe
          ≤ (design.atom keptOne ⬝ᵥ probe) ^ 2 + (design.atom keptTwo ⬝ᵥ probe) ^ 2 := by
  constructor
  · intro hmargin probe horth
    have := hmargin probe horth
    linarith
  · intro hcover probe horth
    have := hcover probe horth
    linarith

/-- **THE GATE IS EMPTY AT SURPLUS ZERO.**  With no surplus the leverage gap asks
for a strictly negative sum of leverages, which no design supplies.  So the
zero-margin pair that rank-two GTZ returns can never fire the gate, at any weight,
and the residual is genuinely a MARGIN question rather than a threshold question. -/
theorem not_leverageGap_of_zero_margin (design : WeightedDesign m k)
    (keptOne keptTwo insertLabel : Fin m) :
    ¬ (leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
      < 0 * (leverageOf (design.atom insertLabel) - 1)) := by
  have hnonneg : 0 ≤ leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo) :=
    add_nonneg (leverageOf_nonneg _) (leverageOf_nonneg _)
  intro hgap
  rw [zero_mul] at hgap
  linarith

/-- **THE MARGIN THE PRODUCER NEEDS, IN CLOSED FORM.**  Given a mass floor and a
leverage cap, the gate fires at a light label as soon as the margin clears
`(leverageCap * weight) / (mass - weight)`.  Reading it this way shows the demand
FALLS as the weight falls: the dust channel supplies its own margin. -/
theorem leverageGap_of_margin_ge {design : WeightedDesign m k}
    {keptOne keptTwo insertLabel : Fin m} {marginRatio leverageCap : ℝ}
    (hleverageCap : leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
      ≤ leverageCap)
    (hmargin : leverageCap < marginRatio * (leverageOf (design.atom insertLabel) - 1)) :
    leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
      < marginRatio * (leverageOf (design.atom insertLabel) - 1) :=
  lt_of_le_of_lt hleverageCap hmargin

/-- **THE LEVERAGE DIVERGENCE.**  A mass floor plus a weight ceiling forces the
insert leverage up by exactly the ratio.  This is the quantitative form of "the
mass cannot see the dust weight": the mass stays put and the leverage carries the
whole collapse. -/
theorem leverage_ge_of_massFloor_of_light (design : WeightedDesign m k) (label : Fin m)
    {massFloor dustThreshold : ℝ} (hthresholdPos : 0 < dustThreshold)
    (hmassFloor : massFloor ≤ massOf design label)
    (hlight : design.weight label ≤ dustThreshold) :
    massFloor / dustThreshold ≤ leverageOf (design.atom label) := by
  have hleverageNonneg : 0 ≤ leverageOf (design.atom label) := leverageOf_nonneg _
  rw [div_le_iff₀ hthresholdPos, mul_comm]
  calc massFloor ≤ massOf design label := hmassFloor
    _ = design.weight label * leverageOf (design.atom label) := rfl
    _ ≤ dustThreshold * leverageOf (design.atom label) :=
        mul_le_mul_of_nonneg_right hlight hleverageNonneg

/-- **THE DUST LEG NEEDS ONLY A VANISHING MARGIN.**  Combining the divergence with
the gate: at a mass floor, a leverage cap and a weight below the explicit
threshold, ANY positive margin at all fires the gate.  The producer therefore does
not need a uniform margin floor -- it needs a margin that beats a quantity going to
zero with the weight. -/
theorem posDef_insert_of_vanishing_margin (design : WeightedDesign m k)
    {keptOne keptTwo insertLabel : Fin m}
    (hneKepts : keptOne ≠ keptTwo) (hneOneInsert : keptOne ≠ insertLabel)
    (hneTwoInsert : keptTwo ≠ insertLabel)
    {marginRatio massFloor leverageCap dustThreshold : ℝ} (hmarginPos : 0 < marginRatio)
    (hmargin : PlaneMarginAt design keptOne keptTwo insertLabel marginRatio)
    (hmassFloor : massFloor ≤ massOf design insertLabel)
    (hleverageCap : leverageOf (design.atom keptOne) + leverageOf (design.atom keptTwo)
      ≤ leverageCap)
    (hcapNonneg : 0 ≤ leverageCap)
    (hlight : design.weight insertLabel ≤ dustThreshold)
    (hthreshold : dustThreshold * (leverageCap + marginRatio) < marginRatio * massFloor) :
    (subsetSum design ({keptOne, keptTwo, insertLabel} : Finset (Fin m)) - 1).PosDef :=
  posDef_insert_of_dust_of_massFloor design hneKepts hneOneInsert hneTwoInsert hmarginPos
    hmargin hmassFloor hleverageCap hcapNonneg hlight hthreshold

end Gtz

import Gtz.Design.LineFreeConicBridge
import Gtz.Design.TwoFamilyTightFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The weight-aware wall clearance of the `U(3,6)` two-family split

`Gtz.wallClearanceOf` (LineFreeConicBridge.lean:560) reads the design MASSES
`m_c = w_c * |g_c|^2`, and the mass is exactly the quantity a dust weight can
hide behind: as `w_c` falls the leverage rises, and the product stays put.  At
`Gtz.minimaxRefuterDesign` -- the single design behind all three landed clearance
refutations -- the three lightest labels carry weight about `1/127` and leverages
`74.7`, `57.2`, `57.7`, so their masses are `0.59`, `0.45`, `0.46` and the mass
clearance is attained at a HEAVY label instead.

This file adds the leg the mass cannot see: the smallest RAW weight, and the
weight-aware clearance that is its minimum with the landed wall clearance.  Three
things are proved.

* The new functional has exactly the properties the split consumes: it is
  positive on the open stratum and invariant under `Gtz.relabelDesign`, so the
  orbit normalization that pins the weak triple at `{0, 1, 2}` transports.
* The two-family assembly instantiates at it with no new plumbing:
  `Gtz.lineFreeOffConic_noTie_of_weightAwareBoundedAndCollar` is the exact twin of
  the landed `Gtz.lineFreeOffConic_noTie_of_clearanceBoundedAndCollar`, over the
  new functional instead of `Gtz.wallClearanceOf`.
* **THE LANDED RECTANGLE REFUTATION DOES NOT TRANSFER.**  The refuter's raw-weight
  clearance is `7310934016 / 926862531169`, so at every weight scale at most `47`
  its weight-aware clearance is strictly below `3 / 8` and it sits INSIDE the
  collar, where the interior obligation is not asked anything.
-/

namespace Gtz

open Matrix

/-! ## The raw-weight leg -/

/-- **THE RAW-WEIGHT CLEARANCE**: the smallest weight of the design.  This is the
coordinate the dust cascade drives to zero and the one `Gtz.massClearanceOf`
cannot see, because a falling weight is masked by a rising leverage at constant
mass. -/
noncomputable def rawWeightClearanceOf (design : WeightedDesign 6 3) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty design.weight

/-- The raw-weight clearance is a lower bound for every weight. -/
theorem rawWeightClearanceOf_le (design : WeightedDesign 6 3) (label : Fin 6) :
    rawWeightClearanceOf design ≤ design.weight label :=
  Finset.inf'_le _ (Finset.mem_univ label)

/-- **THE RAW-WEIGHT CLEARANCE IS POSITIVE ON EVERY DESIGN** -- unconditionally,
straight from `weight_pos`.  No line-freeness and no off-conicity are needed, so
adding this leg costs the positivity theorem nothing. -/
theorem rawWeightClearanceOf_pos (design : WeightedDesign 6 3) :
    0 < rawWeightClearanceOf design := by
  simp only [rawWeightClearanceOf, Finset.lt_inf'_iff]
  exact fun label _ => design.weight_pos label

/-- Relabelling permutes the weights, so the raw-weight clearance is invariant. -/
theorem rawWeightClearanceOf_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6)) :
    rawWeightClearanceOf (relabelDesign design relabel) = rawWeightClearanceOf design := by
  unfold rawWeightClearanceOf
  refine le_antisymm (Finset.le_inf' _ _ fun label _ => ?_)
    (Finset.le_inf' _ _ fun label _ => ?_)
  · refine le_trans (Finset.inf'_le _ (Finset.mem_univ (relabel.symm label))) (le_of_eq ?_)
    exact congrArg design.weight (relabel.apply_symm_apply label)
  · exact Finset.inf'_le _ (Finset.mem_univ (relabel label))

/-! ## The weight-aware wall clearance -/

/-- **THE WEIGHT-AWARE WALL CLEARANCE.**  The landed wall clearance capped by a
scaled smallest raw weight.  `weightScale` is the exchange rate between the two
legs; the measured record says the attainable margin tracks the raw-weight leg,
so the scale is what tunes how much of the dust channel is pushed into the
collar. -/
noncomputable def weightAwareClearanceOf (weightScale : ℝ) (design : WeightedDesign 6 3) : ℝ :=
  min (wallClearanceOf design) (weightScale * rawWeightClearanceOf design)

/-- The weight-aware clearance never exceeds the landed one: the new functional
only ever SHRINKS the interior and GROWS the collar. -/
theorem weightAwareClearanceOf_le_wallClearanceOf (weightScale : ℝ)
    (design : WeightedDesign 6 3) :
    weightAwareClearanceOf weightScale design ≤ wallClearanceOf design :=
  min_le_left _ _

/-- The weight-aware clearance never exceeds the scaled raw-weight leg. -/
theorem weightAwareClearanceOf_le_scaled_rawWeight (weightScale : ℝ)
    (design : WeightedDesign 6 3) :
    weightAwareClearanceOf weightScale design
      ≤ weightScale * rawWeightClearanceOf design :=
  min_le_right _ _

/-- **POSITIVE EXACTLY WHERE THE LANDED ONE IS.**  Adding the raw-weight leg does
not move the open stratum: at a positive scale the new functional is positive on
the line-free off-conic locus and nowhere else. -/
theorem weightAwareClearanceOf_pos {weightScale : ℝ} (hscalePos : 0 < weightScale)
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom) :
    0 < weightAwareClearanceOf weightScale design :=
  lt_min (wallClearanceOf_pos design hpattern hoffConic)
    (mul_pos hscalePos (rawWeightClearanceOf_pos design))

/-- **THE WEIGHT-AWARE CLEARANCE IS RELABELLING-INVARIANT** -- so the landed
orbit normalization that pins the weak triple at the base triple `{0, 1, 2}`
transports to the new functional verbatim. -/
theorem weightAwareClearanceOf_relabelDesign (weightScale : ℝ)
    (design : WeightedDesign 6 3) (relabel : Equiv.Perm (Fin 6)) :
    weightAwareClearanceOf weightScale (relabelDesign design relabel)
      = weightAwareClearanceOf weightScale design := by
  unfold weightAwareClearanceOf
  rw [wallClearanceOf_relabelDesign, rawWeightClearanceOf_relabelDesign]

/-! ## The assembly, instantiated at the new functional -/

/-- **FAMILY I OVER THE WEIGHT-AWARE FUNCTIONAL.**  The exact twin of
`Gtz.ClearanceBoundedInteriorFloor`, with the landed wall clearance replaced by
the weight-aware one.  Its region is a STRICT SUBSET of the landed Prop's region
(`Gtz.weightAwareClearanceOf_le_wallClearanceOf`), so this is a WEAKER
obligation. -/
def WeightAwareInteriorFloor (weightScale clearanceFloor marginFloor : ℝ) : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    (∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected) →
    clearanceFloor ≤ weightAwareClearanceOf weightScale design →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - (1 + marginFloor • 1)).PosSemidef

/-- **THE RAMP REDUCTION OVER THE NEW FUNCTIONAL.**  Verbatim the landed
`Gtz.interiorFamilyMarginFloor_of_clearanceBounded` with the functional swapped:
inside the collar the ramp is nonpositive and the weak triple discharges the
obligation for free, outside it the bounded core delivers the triple. -/
theorem interiorFamilyMarginFloor_of_weightAware {weightScale clearanceFloor marginFloor : ℝ}
    (hbounded : WeightAwareInteriorFloor weightScale clearanceFloor marginFloor) :
    InteriorFamilyMarginFloor (weightAwareClearanceOf weightScale)
      (clearanceRampFloor clearanceFloor marginFloor) := by
  intro design hlineFree hoffConic hweak _hclearancePos
  rcases le_or_gt (weightAwareClearanceOf weightScale design) clearanceFloor with
    hinCollar | houtside
  · obtain ⟨weakTriple, hweakCard, hweakDominates⟩ := hweak
    have hrampNonpos :
        clearanceRampFloor clearanceFloor marginFloor
          (weightAwareClearanceOf weightScale design) ≤ 0 := by
      have hdiff : weightAwareClearanceOf weightScale design - clearanceFloor ≤ 0 := by
        linarith
      exact le_trans (min_le_right _ _) hdiff
    exact ⟨weakTriple, hweakCard,
      posSemidef_identityFloor_of_dominates hweakDominates hrampNonpos⟩
  · obtain ⟨strictTriple, hstrictCard, hstrictFloor⟩ :=
      hbounded design hlineFree hoffConic hweak houtside.le
    have hrampLe :
        clearanceRampFloor clearanceFloor marginFloor
          (weightAwareClearanceOf weightScale design) ≤ marginFloor := min_le_left _ _
    exact ⟨strictTriple, hstrictCard, posSemidef_identityFloor_of_le hstrictFloor hrampLe⟩

/-- **THE INTERFACE, AND IT COSTS NOTHING BUT THE INTERFACE.**  A weight-aware
bounded interior floor plus a collar exclusion at the same threshold close
tie-freeness of the whole open line-free off-conic stratum, through the landed
`Gtz.lineFreeOffConicWeakToStrict_of_twoFamilies` -- which was already parametric
in the clearance functional, so nothing below this line is new plumbing. -/
theorem lineFreeOffConic_noTie_of_weightAwareBoundedAndCollar
    {weightScale clearanceFloor marginFloor : ℝ} (hclearanceNonneg : 0 ≤ clearanceFloor)
    (hmarginPos : 0 < marginFloor)
    (hbounded : WeightAwareInteriorFloor weightScale clearanceFloor marginFloor)
    (hcollar : BoundaryCollarExcludesTies (weightAwareClearanceOf weightScale)
      clearanceFloor) :
    ∀ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      ¬ IsTie design :=
  lineFreeOffConicWeakToStrict_of_twoFamilies (weightAwareClearanceOf weightScale)
    (clearanceRampFloor clearanceFloor marginFloor) clearanceFloor
    (interiorFamilyMarginFloor_of_weightAware hbounded)
    (fun _clearance habove => clearanceRampFloor_pos hmarginPos habove)
    hcollar hclearanceNonneg

/-- The weight-aware obligation is implied by the landed one at the same
constants: the region shrank.  So nothing is lost by moving to the new
functional -- only the refuted part of the region is dropped. -/
theorem weightAwareInteriorFloor_of_clearanceBounded {weightScale clearanceFloor marginFloor : ℝ}
    (hbounded : ClearanceBoundedInteriorFloor clearanceFloor marginFloor) :
    WeightAwareInteriorFloor weightScale clearanceFloor marginFloor := by
  intro design hlineFree hoffConic hweak hclearance
  exact hbounded design hlineFree hoffConic hweak
    (hclearance.trans (weightAwareClearanceOf_le_wallClearanceOf weightScale design))

/-! ## The landed rectangle refutation does not transfer -/

/-- The minimax refuter's smallest raw weight, exactly.  It is `1 / 126.777...`,
the dust the tree's own stage-five note measures at "roughly `1/128`". -/
theorem rawWeightClearanceOf_minimaxRefuterDesign :
    rawWeightClearanceOf minimaxRefuterDesign = 7310934016 / 926862531169 := by
  refine le_antisymm ?_ ?_
  · exact le_of_le_of_eq (rawWeightClearanceOf_le minimaxRefuterDesign 1)
      (by norm_num [minimaxRefuterDesign_weight_eq, minimaxRefuterWeight])
  · refine Finset.le_inf' _ _ fun label _ => ?_
    fin_cases label <;>
      norm_num [minimaxRefuterDesign_weight_eq, minimaxRefuterWeight]

/-- **THE REFUTER FALLS INTO THE COLLAR.**  At every weight scale at most `47`
the minimax refuter's weight-aware clearance is strictly below `3 / 8`.  The
landed `Gtz.baseTripleClearanceBoundedFloor_rectangle_refuted` and
`Gtz.interiorFamilyMarginFloor_monotoneGraded_refuted` both drive their
contradiction by placing this design INSIDE the clearance-bounded region; over
the weight-aware functional it is no longer there, so neither refutation
transfers. -/
theorem weightAwareClearanceOf_minimaxRefuterDesign_lt {weightScale : ℝ}
    (hscale : weightScale ≤ 47) :
    weightAwareClearanceOf weightScale minimaxRefuterDesign < 3 / 8 := by
  refine lt_of_le_of_lt (weightAwareClearanceOf_le_scaled_rawWeight _ _) ?_
  rw [rawWeightClearanceOf_minimaxRefuterDesign]
  have hpos : (0 : ℝ) < 7310934016 / 926862531169 := by norm_num
  calc weightScale * (7310934016 / 926862531169)
      ≤ 47 * (7310934016 / 926862531169) := by
        exact mul_le_mul_of_nonneg_right hscale hpos.le
    _ < 3 / 8 := by norm_num

/-- The same statement in the shape the refutations consume: the refuter does NOT
meet the weight-aware clearance floor `3 / 8`. -/
theorem not_threeEighths_le_weightAwareClearanceOf_minimaxRefuterDesign
    {weightScale : ℝ} (hscale : weightScale ≤ 47) :
    ¬ ((3 : ℝ) / 8 ≤ weightAwareClearanceOf weightScale minimaxRefuterDesign) :=
  not_le_of_gt (weightAwareClearanceOf_minimaxRefuterDesign_lt hscale)

/-- The floor refuter is NOT dust: its smallest raw weight is `1327104 / 11621281`,
about `0.114`.  So the landed `(1/16, 1/4)` pair refutation is untouched by the
new leg at every scale above `0.548` -- correctly, since a margin floor of a
quarter is refuted for reasons that have nothing to do with the weight corner. -/
theorem rawWeightClearanceOf_floorRefuterDesign :
    rawWeightClearanceOf floorRefuterDesign = 1327104 / 11621281 := by
  refine le_antisymm ?_ ?_
  · exact le_of_le_of_eq (rawWeightClearanceOf_le floorRefuterDesign 1)
      (by norm_num [floorRefuterDesign_weight_eq, floorRefuterWeight])
  · refine Finset.le_inf' _ _ fun label _ => ?_
    fin_cases label <;>
      norm_num [floorRefuterDesign_weight_eq, floorRefuterWeight]

/-- At scale one the floor refuter still clears `1 / 16` on the raw-weight leg,
so the new functional does not rescue the quarter-margin pair. -/
theorem sixteenth_le_scaled_rawWeight_floorRefuterDesign :
    (1 : ℝ) / 16 ≤ 1 * rawWeightClearanceOf floorRefuterDesign := by
  rw [rawWeightClearanceOf_floorRefuterDesign]
  norm_num

/-! ## The new region is INHABITED, and the new obligation is still refuted at
the quarter margin -/

/-- **THE WEIGHT-AWARE REGION IS INHABITED.**  The floor refuter is not dust: at
scale one it clears `1 / 16` on BOTH legs, so it sits inside the weight-aware
clearance-bounded region.  With `Gtz.floorRefuterDesign_hasLinePattern_lineFree`,
`Gtz.hasNoCommonQuadric_floorRefuterAtom` and
`Gtz.floorRefuterDesign_dominates_baseTriple` the WHOLE antecedent of
`Gtz.WeightAwareInteriorFloor 1 (1/16) marginFloor` is met by an exhibited
design -- the new Prop is not vacuous. -/
theorem sixteenth_le_weightAwareClearanceOf_floorRefuterDesign :
    (1 : ℝ) / 16 ≤ weightAwareClearanceOf 1 floorRefuterDesign :=
  le_min floorRefuter_wallClearance_ge sixteenth_le_scaled_rawWeight_floorRefuterDesign

/-- **AND THE NEW OBLIGATION IS STILL FALSE AT THE QUARTER MARGIN.**  The weight
leg does not rescue every constant pair: the floor refuter carries no triple
above the identity floor `1 / 4`, and it is INSIDE the weight-aware region at
scale one and clearance floor `1 / 16`.  So the repaired functional buys the
rectangle refutation's ground back and nothing more -- exactly the honest
statement. -/
theorem weightAwareInteriorFloor_sixteenth_quarter_refuted {marginFloor : ℝ}
    (hmargin : (1 / 4 : ℝ) ≤ marginFloor) :
    ¬ WeightAwareInteriorFloor 1 (1 / 16) marginFloor := by
  intro hbounded
  obtain ⟨selected, hcard, hfloor⟩ :=
    hbounded floorRefuterDesign floorRefuterDesign_hasLinePattern_lineFree
      hasNoCommonQuadric_floorRefuterAtom
      ⟨{0, 1, 2}, by decide, floorRefuterDesign_dominates_baseTriple⟩
      sixteenth_le_weightAwareClearanceOf_floorRefuterDesign
  have hfloorQuarter : (subsetSum floorRefuterDesign selected
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef :=
    posSemidef_identityFloor_of_le hfloor hmargin
  have hpow : selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  rcases cardThreeFinsetsOfSix_enumeration selected hpow with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact floorRefuter_gap_zeroOneTwo_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_zeroOneThree_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_zeroOneFour_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_zeroOneFive_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_zeroTwoThree_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_zeroTwoFour_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_zeroTwoFive_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_zeroThreeFour_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_zeroThreeFive_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_zeroFourFive_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_oneTwoThree_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_oneTwoFour_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_oneTwoFive_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_oneThreeFour_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_oneThreeFive_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_oneFourFive_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_twoThreeFour_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_twoThreeFive_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_twoFourFive_not_posSemidef hfloorQuarter
  · exact floorRefuter_gap_threeFourFive_not_posSemidef hfloorQuarter

/-! ## The collar in the WEIGHT chart: the sharp criterion, division-free -/

/-- **THE COLLAR, READ IN THE RAW WEIGHT.**  `Gtz.posDef_insertCompletion_of_planeMargin`
asks `coupling < marginRatio * lev * (lev - 1)`; with `lev = mass / weight` that is
the DIVISION-FREE quadratic

    weight^2 * coupling  <  marginRatio * mass * (mass - weight),

whose left side vanishes and whose right side tends to `marginRatio * mass^2 > 0`
as the weight falls.  So for a FIXED insert direction and a FIXED kept pair with
a positive plane margin, EVERY sufficiently light weight completes the triple --
this is the collar leg the weight-aware clearance needs, and it is an honest
neighbourhood of the light-weight face because `marginRatio` and `coupling`
depend on the insert only through its DIRECTION.

Note this is `Gtz.posDef_insertCompletion_of_planeMargin` and NOT its corollary
`Gtz.posDef_insertCompletion_of_leverage_gt`.  The corollary weakens
`coupling < marginRatio * (lev - 1)` to `coupling < marginRatio * lev * (lev - 1)`
and, read at a UNIT insert direction, its hypothesis becomes
`lev * (1 - directionCoupling / marginRatio) > 1`, which is UNSATISFIABLE AT
EVERY LEVERAGE -- hence at every weight -- as soon as the direction coupling
reaches the plane margin.  At `Gtz.minimaxRefuterDesign` that happens at all six
inserts and all fifteen pairs. -/
theorem posDef_insertCompletion_of_lightRawWeight {size rank : ℕ}
    (design : WeightedDesign size rank)
    {keptOne keptTwo insertLabel : Fin size}
    (hneKepts : keptOne ≠ keptTwo) (hneOneInsert : keptOne ≠ insertLabel)
    (hneTwoInsert : keptTwo ≠ insertLabel)
    {marginRatio : ℝ} (hmarginPos : 0 < marginRatio)
    (hmargin : ∀ planar : Fin rank → ℝ, design.atom insertLabel ⬝ᵥ planar = 0 →
      (1 + marginRatio) * (planar ⬝ᵥ planar)
        ≤ (design.atom keptOne ⬝ᵥ planar) ^ 2
          + (design.atom keptTwo ⬝ᵥ planar) ^ 2)
    (hlight : design.weight insertLabel ^ 2
          * ((design.atom keptOne ⬝ᵥ design.atom insertLabel) ^ 2
            + (design.atom keptTwo ⬝ᵥ design.atom insertLabel) ^ 2)
        < marginRatio
          * (design.weight insertLabel * leverageOf (design.atom insertLabel))
          * (design.weight insertLabel * leverageOf (design.atom insertLabel)
              - design.weight insertLabel)) :
    (subsetSum design ({keptOne, keptTwo, insertLabel} : Finset (Fin size))
        - 1).PosDef := by
  have hweightPos : 0 < design.weight insertLabel := design.weight_pos insertLabel
  have hleverageEq : design.atom insertLabel ⬝ᵥ design.atom insertLabel
      = leverageOf (design.atom insertLabel) :=
    (leverageOf_eq_dotProduct (design.atom insertLabel)).symm
  set leverage : ℝ := leverageOf (design.atom insertLabel) with hleverageDef
  set coupling : ℝ := (design.atom keptOne ⬝ᵥ design.atom insertLabel) ^ 2
      + (design.atom keptTwo ⬝ᵥ design.atom insertLabel) ^ 2 with hcouplingDef
  have hcouplingNonneg : 0 ≤ coupling := by positivity
  have hweightSqPos : 0 < design.weight insertLabel ^ 2 := by positivity
  have hleverageNonneg : 0 ≤ leverage := by
    rw [hleverageDef, leverageOf]
    exact Finset.sum_nonneg fun index _ => sq_nonneg _
  -- the division-free hypothesis IS the plane-margin gate, rescaled by weight^2
  have hgate : coupling < marginRatio * (leverage * (leverage - 1)) := by
    have hexpand : marginRatio * (design.weight insertLabel * leverage)
          * (design.weight insertLabel * leverage - design.weight insertLabel)
        = design.weight insertLabel ^ 2 * (marginRatio * (leverage * (leverage - 1))) := by
      ring
    rw [hexpand] at hlight
    exact lt_of_mul_lt_mul_left (by linarith [hlight]) hweightSqPos.le
  have hheavy : 1 < leverage := by
    by_contra hnotHeavy
    have hle : leverage ≤ 1 := not_lt.mp hnotHeavy
    have hnonneg : 0 ≤ marginRatio * (leverage * (1 - leverage)) :=
      mul_nonneg hmarginPos.le (mul_nonneg hleverageNonneg (by linarith))
    have hflip : marginRatio * (leverage * (leverage - 1))
        = -(marginRatio * (leverage * (1 - leverage))) := by ring
    rw [hflip] at hgate
    linarith
  refine posDef_insertCompletion_of_planeMargin design hneKepts hneOneInsert
    hneTwoInsert (by rw [hleverageEq]; exact hheavy) hmarginPos hmargin ?_
  rw [hleverageEq]
  exact hgate

end Gtz

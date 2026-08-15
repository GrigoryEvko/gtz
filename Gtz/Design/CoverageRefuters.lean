import Gtz.Design.UnsignedCycleCells

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The coverage refuters and the pendant-family cells

Two exact chart points refute the two candidate dichotomies for the knife-band
existence statement.  The module also lands the four pendant cells of the
matching `{2, 3}`, the rescuers of the second refuter.

The first refuter has unit masses and weights `(1/4, 1/8, 1/8, 1/8, 1/8, 1/4)`.
Every admissible floor at a matching edge is at most `3`, and the Gershgorin
row needs more than `4`: no star row-dominates.  The four paths of the
complementary square read their cleared traces at exact equality.  But the
gauge-star cell fires with minors `5`, `24`, `12`: the point is covered.  A
selection law through row dominance or through a strict trace cannot exist.

The second refuter has masses `(2/5, 11/15, 29/30, 1, 11/15, 2/5)` and weights
`(2/15, 7/30, 7/30, 1/30, 7/30, 2/15)`.  All four star gaps carry explicit
directions of negative energy: no star selection is positive definite.  The
sixteen cleared trace readings all sit at or past their floor products (the
probe holds the exact table; the smallest trace is `113606/110055`).  But the
pendant tree `{1, 2, 3}` fires its cell with minors `92/105`, `5573/11025`,
`3012229/330750`: the point is covered.  The star-or-trace dichotomy also
cannot exist.  The knife-band residual is the full minor atlas.
-/

namespace Gtz

open Matrix Finset

/-! ## The pendant-family expansions at the matching `{2, 3}` -/

/-- Edge `1 = ac` in the pendant tree `{0, 2, 3}`. -/
theorem kFour_expansion_zeroTwoThree_one :
    (1 : ℝ) • kFourDirection 1
      = (1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 2
        + (0 : ℝ) • kFourDirection 3 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `4 = bd` in the pendant tree `{0, 2, 3}`. -/
theorem kFour_expansion_zeroTwoThree_four :
    (1 : ℝ) • kFourDirection 4
      = (-1 : ℝ) • kFourDirection 0 + (0 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 3 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `5 = cd` in the pendant tree `{0, 2, 3}`. -/
theorem kFour_expansion_zeroTwoThree_five :
    (1 : ℝ) • kFourDirection 5
      = (-1 : ℝ) • kFourDirection 0 + (-1 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 3 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `0 = ab` in the pendant tree `{1, 2, 3}`. -/
theorem kFour_expansion_oneTwoThree_zero :
    (1 : ℝ) • kFourDirection 0
      = (1 : ℝ) • kFourDirection 1 + (-1 : ℝ) • kFourDirection 2
        + (0 : ℝ) • kFourDirection 3 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `4 = bd` in the pendant tree `{1, 2, 3}`. -/
theorem kFour_expansion_oneTwoThree_four :
    (1 : ℝ) • kFourDirection 4
      = (-1 : ℝ) • kFourDirection 1 + (1 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 3 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `5 = cd` in the pendant tree `{1, 2, 3}`. -/
theorem kFour_expansion_oneTwoThree_five :
    (1 : ℝ) • kFourDirection 5
      = (-1 : ℝ) • kFourDirection 1 + (0 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 3 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `0 = ab` in the pendant tree `{2, 3, 4}`. -/
theorem kFour_expansion_twoThreeFour_zero :
    (1 : ℝ) • kFourDirection 0
      = (0 : ℝ) • kFourDirection 2 + (1 : ℝ) • kFourDirection 3
        + (-1 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `1 = ac` in the pendant tree `{2, 3, 4}`. -/
theorem kFour_expansion_twoThreeFour_one :
    (1 : ℝ) • kFourDirection 1
      = (1 : ℝ) • kFourDirection 2 + (1 : ℝ) • kFourDirection 3
        + (-1 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `5 = cd` in the pendant tree `{2, 3, 4}`. -/
theorem kFour_expansion_twoThreeFour_five :
    (1 : ℝ) • kFourDirection 5
      = (-1 : ℝ) • kFourDirection 2 + (0 : ℝ) • kFourDirection 3
        + (1 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `0 = ab` in the pendant tree `{2, 3, 5}`. -/
theorem kFour_expansion_twoThreeFive_zero :
    (1 : ℝ) • kFourDirection 0
      = (-1 : ℝ) • kFourDirection 2 + (1 : ℝ) • kFourDirection 3
        + (-1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `1 = ac` in the pendant tree `{2, 3, 5}`. -/
theorem kFour_expansion_twoThreeFive_one :
    (1 : ℝ) • kFourDirection 1
      = (0 : ℝ) • kFourDirection 2 + (1 : ℝ) • kFourDirection 3
        + (-1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `4 = bd` in the pendant tree `{2, 3, 5}`. -/
theorem kFour_expansion_twoThreeFive_four :
    (1 : ℝ) • kFourDirection 4
      = (1 : ℝ) • kFourDirection 2 + (0 : ℝ) • kFourDirection 3
        + (1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-! ## The four pendant cells -/

/-- **The pendant cell at `{0, 2, 3}`.** -/
theorem posDef_kFour_pendantCell_zeroTwoThree (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorZero floorTwo floorThree : ℝ}
    (hfloorZero : floorZero * weight 0 ≤ mass 0 * (1 - weight 0))
    (hfloorTwo : floorTwo * weight 2 ≤ mass 2 * (1 - weight 2))
    (hfloorThree : floorThree * weight 3 ≤ mass 3 * (1 - weight 3))
    (hcorner : 0 < floorZero - (mass 1 + mass 4 + mass 5))
    (hminorTwo : 0 < (floorZero - (mass 1 + mass 4 + mass 5))
      * (floorTwo - (mass 1 + mass 5)) - (mass 1 + mass 5) ^ 2)
    (hminorDet : 0 < (floorZero - (mass 1 + mass 4 + mass 5))
        * (floorTwo - (mass 1 + mass 5)) * (floorThree - (mass 4 + mass 5))
      - (floorZero - (mass 1 + mass 4 + mass 5)) * mass 5 ^ 2
      - (mass 1 + mass 5) ^ 2 * (floorThree - (mass 4 + mass 5))
      + 2 * (-(mass 1 + mass 5)) * (-(mass 4 + mass 5)) * (-(mass 5))
      - (mass 4 + mass 5) ^ 2 * (floorTwo - (mass 1 + mass 5))) :
    (directionChartGap kFourDirection mass weight
      ({0, 2, 3} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 0) (selB := 2) (selC := 3) (outA := 1) (outB := 4) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_zeroTwoThree_one kFour_expansion_zeroTwoThree_four
    kFour_expansion_zeroTwoThree_five
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 1) (fBB := 0) (fBC := 1)
    (fCA := 1) (fCB := 1) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 1) (demandB := mass 4) (demandC := mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorTwo hfloorThree
    (entryAA := floorZero - (mass 1 + mass 4 + mass 5))
    (entryBB := floorTwo - (mass 1 + mass 5))
    (entryCC := floorThree - (mass 4 + mass 5))
    (entryAB := -(mass 1 + mass 5)) (entryAC := -(mass 4 + mass 5))
    (entryBC := -(mass 5))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The pendant cell at `{1, 2, 3}`**, the rescuer tree of the second
refuter. -/
theorem posDef_kFour_pendantCell_oneTwoThree (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorOne floorTwo floorThree : ℝ}
    (hfloorOne : floorOne * weight 1 ≤ mass 1 * (1 - weight 1))
    (hfloorTwo : floorTwo * weight 2 ≤ mass 2 * (1 - weight 2))
    (hfloorThree : floorThree * weight 3 ≤ mass 3 * (1 - weight 3))
    (hcorner : 0 < floorOne - (mass 0 + mass 4 + mass 5))
    (hminorTwo : 0 < (floorOne - (mass 0 + mass 4 + mass 5))
      * (floorTwo - (mass 0 + mass 4)) - (mass 0 + mass 4) ^ 2)
    (hminorDet : 0 < (floorOne - (mass 0 + mass 4 + mass 5))
        * (floorTwo - (mass 0 + mass 4)) * (floorThree - (mass 4 + mass 5))
      - (floorOne - (mass 0 + mass 4 + mass 5)) * mass 4 ^ 2
      - (mass 0 + mass 4) ^ 2 * (floorThree - (mass 4 + mass 5))
      + 2 * (-(mass 0 + mass 4)) * (-(mass 4 + mass 5)) * (-(mass 4))
      - (mass 4 + mass 5) ^ 2 * (floorTwo - (mass 0 + mass 4))) :
    (directionChartGap kFourDirection mass weight
      ({1, 2, 3} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 1) (selB := 2) (selC := 3) (outA := 0) (outB := 4) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_oneTwoThree_zero kFour_expansion_oneTwoThree_four
    kFour_expansion_oneTwoThree_five
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 1) (fBB := 1) (fBC := 1)
    (fCA := 1) (fCB := 0) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 0) (demandB := mass 4) (demandC := mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorOne hfloorTwo hfloorThree
    (entryAA := floorOne - (mass 0 + mass 4 + mass 5))
    (entryBB := floorTwo - (mass 0 + mass 4))
    (entryCC := floorThree - (mass 4 + mass 5))
    (entryAB := -(mass 0 + mass 4)) (entryAC := -(mass 4 + mass 5))
    (entryBC := -(mass 4))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The pendant cell at `{2, 3, 4}`.** -/
theorem posDef_kFour_pendantCell_twoThreeFour (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorTwo floorThree floorFour : ℝ}
    (hfloorTwo : floorTwo * weight 2 ≤ mass 2 * (1 - weight 2))
    (hfloorThree : floorThree * weight 3 ≤ mass 3 * (1 - weight 3))
    (hfloorFour : floorFour * weight 4 ≤ mass 4 * (1 - weight 4))
    (hcorner : 0 < floorTwo - (mass 1 + mass 5))
    (hminorTwo : 0 < (floorTwo - (mass 1 + mass 5))
      * (floorThree - (mass 0 + mass 1)) - mass 1 ^ 2)
    (hminorDet : 0 < (floorTwo - (mass 1 + mass 5))
        * (floorThree - (mass 0 + mass 1)) * (floorFour - (mass 0 + mass 1 + mass 5))
      - (floorTwo - (mass 1 + mass 5)) * (mass 0 + mass 1) ^ 2
      - mass 1 ^ 2 * (floorFour - (mass 0 + mass 1 + mass 5))
      + 2 * (-(mass 1)) * (-(mass 1 + mass 5)) * (-(mass 0 + mass 1))
      - (mass 1 + mass 5) ^ 2 * (floorThree - (mass 0 + mass 1))) :
    (directionChartGap kFourDirection mass weight
      ({2, 3, 4} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 2) (selB := 3) (selC := 4) (outA := 0) (outB := 1) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_twoThreeFour_zero kFour_expansion_twoThreeFour_one
    kFour_expansion_twoThreeFour_five
    (fAA := 0) (fAB := 1) (fAC := 1) (fBA := 1) (fBB := 1) (fBC := 1)
    (fCA := 1) (fCB := 0) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 0) (demandB := mass 1) (demandC := mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorTwo hfloorThree hfloorFour
    (entryAA := floorTwo - (mass 1 + mass 5))
    (entryBB := floorThree - (mass 0 + mass 1))
    (entryCC := floorFour - (mass 0 + mass 1 + mass 5))
    (entryAB := -(mass 1)) (entryAC := -(mass 1 + mass 5))
    (entryBC := -(mass 0 + mass 1))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The pendant cell at `{2, 3, 5}`.** -/
theorem posDef_kFour_pendantCell_twoThreeFive (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorTwo floorThree floorFive : ℝ}
    (hfloorTwo : floorTwo * weight 2 ≤ mass 2 * (1 - weight 2))
    (hfloorThree : floorThree * weight 3 ≤ mass 3 * (1 - weight 3))
    (hfloorFive : floorFive * weight 5 ≤ mass 5 * (1 - weight 5))
    (hcorner : 0 < floorTwo - (mass 0 + mass 4))
    (hminorTwo : 0 < (floorTwo - (mass 0 + mass 4))
      * (floorThree - (mass 0 + mass 1)) - mass 0 ^ 2)
    (hminorDet : 0 < (floorTwo - (mass 0 + mass 4))
        * (floorThree - (mass 0 + mass 1)) * (floorFive - (mass 0 + mass 1 + mass 4))
      - (floorTwo - (mass 0 + mass 4)) * (mass 0 + mass 1) ^ 2
      - mass 0 ^ 2 * (floorFive - (mass 0 + mass 1 + mass 4))
      + 2 * (-(mass 0)) * (-(mass 0 + mass 4)) * (-(mass 0 + mass 1))
      - (mass 0 + mass 4) ^ 2 * (floorThree - (mass 0 + mass 1))) :
    (directionChartGap kFourDirection mass weight
      ({2, 3, 5} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 2) (selB := 3) (selC := 5) (outA := 0) (outB := 1) (outC := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_twoThreeFive_zero kFour_expansion_twoThreeFive_one
    kFour_expansion_twoThreeFive_four
    (fAA := 1) (fAB := 1) (fAC := 1) (fBA := 0) (fBB := 1) (fBC := 1)
    (fCA := 1) (fCB := 0) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 0) (demandB := mass 1) (demandC := mass 4)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorTwo hfloorThree hfloorFive
    (entryAA := floorTwo - (mass 0 + mass 4))
    (entryBB := floorThree - (mass 0 + mass 1))
    (entryCC := floorFive - (mass 0 + mass 1 + mass 4))
    (entryAB := -(mass 0)) (entryAC := -(mass 0 + mass 4))
    (entryBC := -(mass 0 + mass 1))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- The four pendant trees are spanning trees. -/
theorem pendantTrees_mem_kFourSpanningTreeList :
    ({0, 2, 3} : Finset (Fin 6)) ∈ kFourSpanningTreeList
      ∧ ({1, 2, 3} : Finset (Fin 6)) ∈ kFourSpanningTreeList
      ∧ ({2, 3, 4} : Finset (Fin 6)) ∈ kFourSpanningTreeList
      ∧ ({2, 3, 5} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## The first refuter: row dominance and strict traces both fail, the
gauge-star cell fires -/

/-- The first refuter: unit masses. -/
noncomputable def coverageRefuterOneMass : Fin 6 → ℝ := fun _ => 1

/-- The first refuter: the matching `{0, 5}` carries weight `1/4` each, the
complementary square `1/8` each. -/
noncomputable def coverageRefuterOneWeight : Fin 6 → ℝ
  | 0 => 1 / 4
  | 1 => 1 / 8
  | 2 => 1 / 8
  | 3 => 1 / 8
  | 4 => 1 / 8
  | 5 => 1 / 4

/-- The first refuter is a mass-one chart weight vector. -/
theorem coverageRefuterOneWeight_sum :
    (∑ label, coverageRefuterOneWeight label) = 1 := by
  rw [Fin.sum_univ_six]
  norm_num [coverageRefuterOneWeight]

/-- **The matching-row cap.**  At the first refuter, every admissible floor at
a matching edge is at most `3`, and strict Gershgorin row dominance at that
row needs more than `2 * (1 + 1) = 4`.  Each of the four stars contains a
matching edge, so no star is strictly row-dominant. -/
theorem coverageRefuterOne_matchingRow_capped (floor : ℝ)
    (hfloor : floor * (1 / 4 : ℝ) ≤ 1 * (1 - 1 / 4)) :
    ¬ (2 * ((1 : ℝ) + 1) < floor - (1 + 1)) := by
  intro hdominant
  nlinarith

/-- **The cleared trace boundary.**  At the first refuter, each of the four
paths of the complementary square reads its cleared trace at exact equality
with the floor product: the strict trace hypothesis fails on all four.  The
reading below is the tree `{1, 2, 3}`; the other three permute the same
numbers. -/
theorem coverageRefuterOne_traceBoundary :
    (1 : ℝ) * (1 ^ 2 * (7 * 7) + 1 ^ 2 * (7 * 7) + 0 ^ 2 * (7 * 7))
      + 1 * (1 ^ 2 * (7 * 7) + 1 ^ 2 * (7 * 7) + 1 ^ 2 * (7 * 7))
      + 1 * (1 ^ 2 * (7 * 7) + 0 ^ 2 * (7 * 7) + 1 ^ 2 * (7 * 7))
      = 7 * (7 * 7) := by
  norm_num

/-- **The rescue.**  The gauge-star cell fires at the first refuter with
floors `(7, 7, 3)` and minors `5`, `24`, `12`: the point is covered even
though no star row-dominates and no tree has a strict trace. -/
theorem coverageRefuterOne_gaugeStar_posDef :
    (directionChartGap kFourDirection coverageRefuterOneMass
      coverageRefuterOneWeight ({3, 4, 5} : Finset (Fin 6))).PosDef := by
  refine posDef_kFour_starCell coverageRefuterOneMass coverageRefuterOneWeight
    (fun label => by fin_cases label <;> norm_num [coverageRefuterOneMass])
    (fun label => by fin_cases label <;> norm_num [coverageRefuterOneWeight])
    (floorThree := 7) (floorFour := 7) (floorFive := 3)
    ?_ ?_ ?_ ?_ ?_ ?_ <;>
  norm_num [coverageRefuterOneMass, coverageRefuterOneWeight]

/-! ## The second refuter: no star gap is positive definite, all cleared
traces sit at or past their floors, the pendant cell fires -/

/-- The second refuter: masses. -/
noncomputable def coverageRefuterTwoMass : Fin 6 → ℝ
  | 0 => 2 / 5
  | 1 => 11 / 15
  | 2 => 29 / 30
  | 3 => 1
  | 4 => 11 / 15
  | 5 => 2 / 5

/-- The second refuter: weights. -/
noncomputable def coverageRefuterTwoWeight : Fin 6 → ℝ
  | 0 => 2 / 15
  | 1 => 7 / 30
  | 2 => 7 / 30
  | 3 => 1 / 30
  | 4 => 7 / 30
  | 5 => 2 / 15

/-- The second refuter is a mass-one chart weight vector. -/
theorem coverageRefuterTwoWeight_sum :
    (∑ label, coverageRefuterTwoWeight label) = 1 := by
  rw [Fin.sum_univ_six]
  norm_num [coverageRefuterTwoWeight]

/-- The energy reading of a selection at a probe, unfolded to the six labels.
This is the scalar shape every negative-direction witness evaluates. -/
theorem coverageRefuterTwo_reading (selected : Finset (Fin 6)) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (directionChartGap kFourDirection coverageRefuterTwoMass
        coverageRefuterTwoWeight selected *ᵥ probe)
      = (∑ label ∈ selected,
          coverageRefuterTwoMass label / coverageRefuterTwoWeight label
            * (kFourDirection label ⬝ᵥ probe) ^ 2)
        - ∑ label, coverageRefuterTwoMass label
            * (kFourDirection label ⬝ᵥ probe) ^ 2 :=
  dotProduct_directionChartGap_mulVec_eq kFourDirection coverageRefuterTwoMass
    coverageRefuterTwoWeight selected probe

/-- **Star `a` is not positive definite** at the second refuter: the probe
`(-1086, -83825, 75123)` reads the negative energy `-26868993/5`. -/
theorem coverageRefuterTwo_starA_not_posDef :
    ¬ (directionChartGap kFourDirection coverageRefuterTwoMass
      coverageRefuterTwoWeight ({0, 1, 3} : Finset (Fin 6))).PosDef := by
  intro hpd
  have hne : (![(-1086 : ℝ), -83825, 75123] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hread := congrFun hzero 0
    norm_num at hread
  have hq := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hne
  rw [star_trivial, coverageRefuterTwo_reading] at hq
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six] at hq
  norm_num [kFourDirection_zero, kFourDirection_one, kFourDirection_two,
    kFourDirection_three, kFourDirection_four, kFourDirection_five,
    coverageRefuterTwoMass, coverageRefuterTwoWeight, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hq

/-- **Star `b` is not positive definite** at the second refuter: the probe
`(2, 1, 1)` reads the negative energy `-13/105`. -/
theorem coverageRefuterTwo_starB_not_posDef :
    ¬ (directionChartGap kFourDirection coverageRefuterTwoMass
      coverageRefuterTwoWeight ({0, 2, 4} : Finset (Fin 6))).PosDef := by
  intro hpd
  have hne : (![(2 : ℝ), 1, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hread := congrFun hzero 0
    norm_num at hread
  have hq := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hne
  rw [star_trivial, coverageRefuterTwo_reading] at hq
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six] at hq
  norm_num [kFourDirection_zero, kFourDirection_one, kFourDirection_two,
    kFourDirection_three, kFourDirection_four, kFourDirection_five,
    coverageRefuterTwoMass, coverageRefuterTwoWeight, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hq

/-- **Star `c` is not positive definite** at the second refuter: the probe
`(5, 4, 3)` reads the negative energy `-193/210`. -/
theorem coverageRefuterTwo_starC_not_posDef :
    ¬ (directionChartGap kFourDirection coverageRefuterTwoMass
      coverageRefuterTwoWeight ({1, 2, 5} : Finset (Fin 6))).PosDef := by
  intro hpd
  have hne : (![(5 : ℝ), 4, 3] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hread := congrFun hzero 0
    norm_num at hread
  have hq := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hne
  rw [star_trivial, coverageRefuterTwo_reading] at hq
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six] at hq
  norm_num [kFourDirection_zero, kFourDirection_one, kFourDirection_two,
    kFourDirection_three, kFourDirection_four, kFourDirection_five,
    coverageRefuterTwoMass, coverageRefuterTwoWeight, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hq

/-- **Star `d` is not positive definite** at the second refuter: the probe
`(-1191, -83930, 91038)` reads the negative energy `-32561258/5`. -/
theorem coverageRefuterTwo_starD_not_posDef :
    ¬ (directionChartGap kFourDirection coverageRefuterTwoMass
      coverageRefuterTwoWeight ({3, 4, 5} : Finset (Fin 6))).PosDef := by
  intro hpd
  have hne : (![(-1191 : ℝ), -83930, 91038] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hread := congrFun hzero 0
    norm_num at hread
  have hq := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hne
  rw [star_trivial, coverageRefuterTwo_reading] at hq
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six] at hq
  norm_num [kFourDirection_zero, kFourDirection_one, kFourDirection_two,
    kFourDirection_three, kFourDirection_four, kFourDirection_five,
    coverageRefuterTwoMass, coverageRefuterTwoWeight, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hq

/-- **The rescue.**  The pendant cell at `{1, 2, 3}` fires at the second
refuter with floors `(253/105, 667/210, 29)`, all three at exact budget
equality, and minors `92/105`, `5573/11025`, `3012229/330750`.  The point is
covered while every star selection has a negative direction. -/
theorem coverageRefuterTwo_pendant_posDef :
    (directionChartGap kFourDirection coverageRefuterTwoMass
      coverageRefuterTwoWeight ({1, 2, 3} : Finset (Fin 6))).PosDef := by
  refine posDef_kFour_pendantCell_oneTwoThree coverageRefuterTwoMass
    coverageRefuterTwoWeight
    (fun label => by fin_cases label <;> norm_num [coverageRefuterTwoMass])
    (fun label => by fin_cases label <;> norm_num [coverageRefuterTwoWeight])
    (floorOne := 253 / 105) (floorTwo := 667 / 210) (floorThree := 29)
    ?_ ?_ ?_ ?_ ?_ ?_ <;>
  norm_num [coverageRefuterTwoMass, coverageRefuterTwoWeight]

end Gtz

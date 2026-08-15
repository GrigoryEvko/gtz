import Gtz.Design.UnsignedTraceCell
import Gtz.Design.ThreeLinesAtlas
import Gtz.Wave.ThreeLinesUnsignedTraceWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The five moved three-lines trace orbits

The two rotation-fixed triples do not cover the three-lines chart.  The exact
`Z/3` action leaves five further orbits of independent triples.  This module
gives every moved orbit an unsigned trace certificate without pretending that
the certificate predicate is invariant under rotation:

* fifteen division-free basis expansions, three for each representative;
* five exact one-inequality trace cells;
* a generic transport theorem that checks the cell on the original, once-
  rotated, or twice-rotated chart point and pulls the strict gap back;
* one seven-orbit atlas combining these cells with the two fixed cells; and
* an exact A2 formula sharpening that removes the whole atlas.

The transformed chart masses are load-bearing.  Only positive definiteness is
transported by congruence.  No mass-invariance shortcut is used.
-/

namespace Gtz

open Matrix Finset

/-! Exact basis expansions for one representative of each moved `Z/3` orbit. -/

theorem threeLines_expansion_014_two (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 2
      = (1 : ℝ) • threeLinesDirection slide 0 + (1 : ℝ) • threeLinesDirection slide 1
        + (0 : ℝ) • threeLinesDirection slide 4 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_014_three (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 3
      = (-1 : ℝ) • threeLinesDirection slide 0 + (0 : ℝ) • threeLinesDirection slide 1
        + (1 : ℝ) • threeLinesDirection slide 4 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_014_five (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 5
      = (-slide) • threeLinesDirection slide 0 + (1 : ℝ) • threeLinesDirection slide 1
        + slide • threeLinesDirection slide 4 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_015_two (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 2
      = (1 : ℝ) • threeLinesDirection slide 0 + (1 : ℝ) • threeLinesDirection slide 1
        + (0 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_015_three (slide : ℝ) :
    slide • threeLinesDirection slide 3
      = (0 : ℝ) • threeLinesDirection slide 0 + (-1 : ℝ) • threeLinesDirection slide 1
        + (1 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_015_four (slide : ℝ) :
    slide • threeLinesDirection slide 4
      = slide • threeLinesDirection slide 0 + (-1 : ℝ) • threeLinesDirection slide 1
        + (1 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_024_one (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 1
      = (-1 : ℝ) • threeLinesDirection slide 0 + (1 : ℝ) • threeLinesDirection slide 2
        + (0 : ℝ) • threeLinesDirection slide 4 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_024_three (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 3
      = (-1 : ℝ) • threeLinesDirection slide 0 + (0 : ℝ) • threeLinesDirection slide 2
        + (1 : ℝ) • threeLinesDirection slide 4 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_024_five (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 5
      = (-(1 + slide)) • threeLinesDirection slide 0
        + (1 : ℝ) • threeLinesDirection slide 2
        + slide • threeLinesDirection slide 4 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_025_one (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 1
      = (-1 : ℝ) • threeLinesDirection slide 0 + (1 : ℝ) • threeLinesDirection slide 2
        + (0 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_025_three (slide : ℝ) :
    slide • threeLinesDirection slide 3
      = (1 : ℝ) • threeLinesDirection slide 0 + (-1 : ℝ) • threeLinesDirection slide 2
        + (1 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_025_four (slide : ℝ) :
    slide • threeLinesDirection slide 4
      = (1 + slide) • threeLinesDirection slide 0
        + (-1 : ℝ) • threeLinesDirection slide 2
        + (1 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_045_one (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 1
      = slide • threeLinesDirection slide 0 + (-slide) • threeLinesDirection slide 4
        + (1 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_045_two (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 2
      = (1 + slide) • threeLinesDirection slide 0
        + (-slide) • threeLinesDirection slide 4
        + (1 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

theorem threeLines_expansion_045_three (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 3
      = (-1 : ℝ) • threeLinesDirection slide 0 + (1 : ℝ) • threeLinesDirection slide 4
        + (0 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

/-! One exact unsigned-trace cell for each representative.  The demand
variables occur only when a basis expansion was cleared by `slide`; all other
demands are the actual outside masses. -/

def ThreeLinesTraceCell014 (slide : ℝ) (point : DirectionChartPoint 6) : Prop :=
  ∃ floorZero floorOne floorFour : ℝ,
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    0 < floorZero ∧ 0 < floorOne ∧ 0 < floorFour ∧
    point.mass 2 * (floorOne * floorFour + floorZero * floorFour)
      + point.mass 3 * (floorOne * floorFour + floorZero * floorOne)
      + point.mass 5 * (|slide| ^ 2 * (floorOne * floorFour)
          + floorZero * floorFour + |slide| ^ 2 * (floorZero * floorOne))
        < floorZero * (floorOne * floorFour)

def ThreeLinesTraceCell015 (slide : ℝ) (point : DirectionChartPoint 6) : Prop :=
  ∃ demandThree demandFour floorZero floorOne floorFive : ℝ,
    point.mass 3 ≤ demandThree * slide ^ 2 ∧
    point.mass 4 ≤ demandFour * slide ^ 2 ∧
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorZero ∧ 0 < floorOne ∧ 0 < floorFive ∧
    point.mass 2 * (floorOne * floorFive + floorZero * floorFive)
      + demandThree * (floorZero * floorFive + floorZero * floorOne)
      + demandFour * (|slide| ^ 2 * (floorOne * floorFive)
          + floorZero * floorFive + floorZero * floorOne)
        < floorZero * (floorOne * floorFive)

def ThreeLinesTraceCell024 (slide : ℝ) (point : DirectionChartPoint 6) : Prop :=
  ∃ floorZero floorTwo floorFour : ℝ,
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    0 < floorZero ∧ 0 < floorTwo ∧ 0 < floorFour ∧
    point.mass 1 * (floorTwo * floorFour + floorZero * floorFour)
      + point.mass 3 * (floorTwo * floorFour + floorZero * floorTwo)
      + point.mass 5 * (|1 + slide| ^ 2 * (floorTwo * floorFour)
          + floorZero * floorFour + |slide| ^ 2 * (floorZero * floorTwo))
        < floorZero * (floorTwo * floorFour)

def ThreeLinesTraceCell025 (slide : ℝ) (point : DirectionChartPoint 6) : Prop :=
  ∃ demandThree demandFour floorZero floorTwo floorFive : ℝ,
    point.mass 3 ≤ demandThree * slide ^ 2 ∧
    point.mass 4 ≤ demandFour * slide ^ 2 ∧
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorZero ∧ 0 < floorTwo ∧ 0 < floorFive ∧
    point.mass 1 * (floorTwo * floorFive + floorZero * floorFive)
      + demandThree * (floorTwo * floorFive + floorZero * floorFive
          + floorZero * floorTwo)
      + demandFour * (|1 + slide| ^ 2 * (floorTwo * floorFive)
          + floorZero * floorFive + floorZero * floorTwo)
        < floorZero * (floorTwo * floorFive)

def ThreeLinesTraceCell045 (slide : ℝ) (point : DirectionChartPoint 6) : Prop :=
  ∃ floorZero floorFour floorFive : ℝ,
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorZero ∧ 0 < floorFour ∧ 0 < floorFive ∧
    point.mass 1 * (|slide| ^ 2 * (floorFour * floorFive)
          + |slide| ^ 2 * (floorZero * floorFive) + floorZero * floorFour)
      + point.mass 2 * (|1 + slide| ^ 2 * (floorFour * floorFive)
          + |slide| ^ 2 * (floorZero * floorFive) + floorZero * floorFour)
      + point.mass 3 * (floorFour * floorFive + floorZero * floorFive)
        < floorZero * (floorFour * floorFive)

theorem posDef_threeLines_014_of_traceCell (slide : ℝ) (point : DirectionChartPoint 6)
    (hcell : ThreeLinesTraceCell014 slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({0, 1, 4} : Finset (Fin 6))).PosDef := by
  obtain ⟨floorZero, floorOne, floorFour, hfloorZero, hfloorOne, hfloorFour,
    hposZero, hposOne, hposFour, htrace⟩ := hcell
  refine posDef_directionChartGap_of_unsignedCycleTrace (threeLinesDirection slide)
    point.mass point.weight point.mass_pos point.weight_pos
    (selA := 0) (selB := 1) (selC := 4) (outA := 2) (outB := 3) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (threeLinesDirection_span slide)
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    (threeLines_expansion_014_two slide) (threeLines_expansion_014_three slide)
    (threeLines_expansion_014_five slide)
    (fAA := 1) (fAB := 1) (fAC := 0)
    (fBA := 1) (fBB := 0) (fBC := 1)
    (fCA := |slide|) (fCB := 1) (fCC := |slide|)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simp) (by norm_num) (by simp)
    (demandA := point.mass 2) (demandB := point.mass 3) (demandC := point.mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorOne hfloorFour hposZero hposOne hposFour ?_
  simpa using htrace

theorem posDef_threeLines_015_of_traceCell (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide) (point : DirectionChartPoint 6)
    (hcell : ThreeLinesTraceCell015 slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({0, 1, 5} : Finset (Fin 6))).PosDef := by
  obtain ⟨demandThree, demandFour, floorZero, floorOne, floorFive,
    hdemandThree, hdemandFour, hfloorZero, hfloorOne, hfloorFive,
    hposZero, hposOne, hposFive, htrace⟩ := hcell
  refine posDef_directionChartGap_of_unsignedCycleTrace (threeLinesDirection slide)
    point.mass point.weight point.mass_pos point.weight_pos
    (selA := 0) (selB := 1) (selC := 5) (outA := 2) (outB := 3) (outC := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (threeLinesDirection_span slide)
    (scaleA := 1) (scaleB := slide) (scaleC := slide)
    one_ne_zero hadmissible.1 hadmissible.1
    (threeLines_expansion_015_two slide) (threeLines_expansion_015_three slide)
    (threeLines_expansion_015_four slide)
    (fAA := 1) (fAB := 1) (fAC := 0)
    (fBA := 0) (fBB := 1) (fBC := 1)
    (fCA := |slide|) (fCB := 1) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simp) (by norm_num) (by norm_num)
    (demandA := point.mass 2) (demandB := demandThree) (demandC := demandFour)
    (le_of_eq (by ring)) hdemandThree hdemandFour
    hfloorZero hfloorOne hfloorFive hposZero hposOne hposFive ?_
  simpa using htrace

theorem posDef_threeLines_024_of_traceCell (slide : ℝ) (point : DirectionChartPoint 6)
    (hcell : ThreeLinesTraceCell024 slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({0, 2, 4} : Finset (Fin 6))).PosDef := by
  obtain ⟨floorZero, floorTwo, floorFour, hfloorZero, hfloorTwo, hfloorFour,
    hposZero, hposTwo, hposFour, htrace⟩ := hcell
  refine posDef_directionChartGap_of_unsignedCycleTrace (threeLinesDirection slide)
    point.mass point.weight point.mass_pos point.weight_pos
    (selA := 0) (selB := 2) (selC := 4) (outA := 1) (outB := 3) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (threeLinesDirection_span slide)
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    (threeLines_expansion_024_one slide) (threeLines_expansion_024_three slide)
    (threeLines_expansion_024_five slide)
    (fAA := 1) (fAB := 1) (fAC := 0)
    (fBA := 1) (fBB := 0) (fBC := 1)
    (fCA := |1 + slide|) (fCB := 1) (fCC := |slide|)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by exact (abs_neg (1 + slide)).le)
    (by norm_num) (by simp)
    (demandA := point.mass 1) (demandB := point.mass 3) (demandC := point.mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorTwo hfloorFour hposZero hposTwo hposFour ?_
  simpa using htrace

theorem posDef_threeLines_025_of_traceCell (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide) (point : DirectionChartPoint 6)
    (hcell : ThreeLinesTraceCell025 slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({0, 2, 5} : Finset (Fin 6))).PosDef := by
  obtain ⟨demandThree, demandFour, floorZero, floorTwo, floorFive,
    hdemandThree, hdemandFour, hfloorZero, hfloorTwo, hfloorFive,
    hposZero, hposTwo, hposFive, htrace⟩ := hcell
  refine posDef_directionChartGap_of_unsignedCycleTrace (threeLinesDirection slide)
    point.mass point.weight point.mass_pos point.weight_pos
    (selA := 0) (selB := 2) (selC := 5) (outA := 1) (outB := 3) (outC := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (threeLinesDirection_span slide)
    (scaleA := 1) (scaleB := slide) (scaleC := slide)
    one_ne_zero hadmissible.1 hadmissible.1
    (threeLines_expansion_025_one slide) (threeLines_expansion_025_three slide)
    (threeLines_expansion_025_four slide)
    (fAA := 1) (fAB := 1) (fAC := 0)
    (fBA := 1) (fBB := 1) (fBC := 1)
    (fCA := |1 + slide|) (fCB := 1) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simp) (by norm_num) (by norm_num)
    (demandA := point.mass 1) (demandB := demandThree) (demandC := demandFour)
    (le_of_eq (by ring)) hdemandThree hdemandFour
    hfloorZero hfloorTwo hfloorFive hposZero hposTwo hposFive ?_
  simpa using htrace

theorem posDef_threeLines_045_of_traceCell (slide : ℝ) (point : DirectionChartPoint 6)
    (hcell : ThreeLinesTraceCell045 slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({0, 4, 5} : Finset (Fin 6))).PosDef := by
  obtain ⟨floorZero, floorFour, floorFive, hfloorZero, hfloorFour, hfloorFive,
    hposZero, hposFour, hposFive, htrace⟩ := hcell
  refine posDef_directionChartGap_of_unsignedCycleTrace (threeLinesDirection slide)
    point.mass point.weight point.mass_pos point.weight_pos
    (selA := 0) (selB := 4) (selC := 5) (outA := 1) (outB := 2) (outC := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (threeLinesDirection_span slide)
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    (threeLines_expansion_045_one slide) (threeLines_expansion_045_two slide)
    (threeLines_expansion_045_three slide)
    (fAA := |slide|) (fAB := |slide|) (fAC := 1)
    (fBA := |1 + slide|) (fBB := |slide|) (fBC := 1)
    (fCA := 1) (fCB := 1) (fCC := 0)
    (by simp) (by simp) (by norm_num) (by simp) (by simp)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := point.mass 1) (demandB := point.mass 2) (demandC := point.mass 3)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorFour hfloorFive hposZero hposFour hposFive ?_
  simpa using htrace

/-- The moved-orbit atlas is nonempty: the chart point that refutes the two
fixed triples lies deeply inside the `{0,1,5}` trace cell. -/
theorem canonicalPairFailure_traceCell015 :
    ThreeLinesTraceCell015 2 canonicalPairFailurePoint := by
  refine ⟨1 / 4, 1 / 40, 98, 98, 98, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [canonicalPairFailurePoint, canonicalPairFailureMass,
      canonicalPairFailureWeight]

/-! The five moved orbits. -/

theorem threeLinesRotation_map_zeroOneFour :
    ({0, 1, 4} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {1, 2, 3} := by decide

theorem threeLinesRotation_map_oneTwoThree :
    ({1, 2, 3} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {0, 3, 5} := by decide

theorem threeLinesRotation_map_zeroThreeFive :
    ({0, 3, 5} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {0, 1, 4} := by decide

theorem threeLinesRotation_map_zeroTwoFour :
    ({0, 2, 4} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {1, 2, 5} := by decide

theorem threeLinesRotation_map_oneTwoFive :
    ({1, 2, 5} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {3, 4, 5} := by decide

theorem threeLinesRotation_map_threeFourFive :
    ({3, 4, 5} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {0, 2, 4} := by decide

theorem threeLinesRotation_map_zeroTwoFive :
    ({0, 2, 5} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {1, 4, 5} := by decide

theorem threeLinesRotation_map_oneFourFive :
    ({1, 4, 5} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {2, 3, 4} := by decide

theorem threeLinesRotation_map_twoThreeFour :
    ({2, 3, 4} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {0, 2, 5} := by decide

theorem threeLinesRotation_map_zeroFourFive :
    ({0, 4, 5} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {1, 2, 4} := by decide

theorem threeLinesRotation_map_oneTwoFour :
    ({1, 2, 4} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {2, 3, 5} := by decide

theorem threeLinesRotation_map_twoThreeFive :
    ({2, 3, 5} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {0, 4, 5} := by decide

/-! ## Orbit packaging and transport -/

noncomputable def twiceRotatedThreeLinesChartPoint (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) : DirectionChartPoint 6 :=
  rotatedThreeLinesChartPoint slide hslideNe
    (rotatedThreeLinesChartPoint slide hslideNe point)

def ThreeLinesRotatedTraceOrbitCell (slide : ℝ) (hslideNe : slide ≠ 0)
    (cell : DirectionChartPoint 6 → Prop) (point : DirectionChartPoint 6) : Prop :=
  cell point ∨
    cell (rotatedThreeLinesChartPoint slide hslideNe point) ∨
    cell (twiceRotatedThreeLinesChartPoint slide hslideNe point)

theorem exists_posDef_threeLines_of_rotatedTraceOrbitCell
    (slide : ℝ) (hslideNe : slide ≠ 0)
    (cell : DirectionChartPoint 6 → Prop)
    (representative next last : Finset (Fin 6))
    (hcardRepresentative : representative.card = 3)
    (hcardNext : next.card = 3) (hcardLast : last.card = 3)
    (hmapNext : next.map threeLinesRotation.toEmbedding = last)
    (hmapLast : last.map threeLinesRotation.toEmbedding = representative)
    (hcertificate : ∀ point : DirectionChartPoint 6, cell point →
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        representative).PosDef)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesRotatedTraceOrbitCell slide hslideNe cell point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef := by
  rcases hcell with hhere | honce | htwice
  · exact ⟨representative, hcardRepresentative, hcertificate point hhere⟩
  · have hstrictRepresentative := hcertificate
      (rotatedThreeLinesChartPoint slide hslideNe point) honce
    have htransport := posDef_directionChartGap_threeLines_rotate_iff
      slide hslideNe point last
    rw [hmapLast] at htransport
    exact ⟨last, hcardLast, htransport.mpr hstrictRepresentative⟩
  · have hstrictRepresentative := hcertificate
      (twiceRotatedThreeLinesChartPoint slide hslideNe point) htwice
    have htransportOnce := posDef_directionChartGap_threeLines_rotate_iff
      slide hslideNe (rotatedThreeLinesChartPoint slide hslideNe point) last
    rw [hmapLast] at htransportOnce
    have hstrictLast := htransportOnce.mpr hstrictRepresentative
    have htransportBack := posDef_directionChartGap_threeLines_rotate_iff
      slide hslideNe point next
    rw [hmapNext] at htransportBack
    exact ⟨next, hcardNext, htransportBack.mpr hstrictLast⟩

def ThreeLinesTraceOrbit014 (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) : Prop :=
  ThreeLinesRotatedTraceOrbitCell slide hslideNe (ThreeLinesTraceCell014 slide) point

def ThreeLinesTraceOrbit015 (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) : Prop :=
  ThreeLinesRotatedTraceOrbitCell slide hslideNe (ThreeLinesTraceCell015 slide) point

def ThreeLinesTraceOrbit024 (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) : Prop :=
  ThreeLinesRotatedTraceOrbitCell slide hslideNe (ThreeLinesTraceCell024 slide) point

def ThreeLinesTraceOrbit025 (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) : Prop :=
  ThreeLinesRotatedTraceOrbitCell slide hslideNe (ThreeLinesTraceCell025 slide) point

def ThreeLinesTraceOrbit045 (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) : Prop :=
  ThreeLinesRotatedTraceOrbitCell slide hslideNe (ThreeLinesTraceCell045 slide) point

def ThreeLinesMovedTraceOrbitCellFires (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) : Prop :=
  ThreeLinesTraceOrbit014 slide hslideNe point ∨
    ThreeLinesTraceOrbit015 slide hslideNe point ∨
    ThreeLinesTraceOrbit024 slide hslideNe point ∨
    ThreeLinesTraceOrbit025 slide hslideNe point ∨
    ThreeLinesTraceOrbit045 slide hslideNe point

theorem exists_posDef_threeLines_of_traceOrbit014 (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) (hcell : ThreeLinesTraceOrbit014 slide hslideNe point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef :=
  exists_posDef_threeLines_of_rotatedTraceOrbitCell slide hslideNe
    (ThreeLinesTraceCell014 slide) {0, 1, 4} {1, 2, 3} {0, 3, 5}
    (by decide) (by decide) (by decide)
    threeLinesRotation_map_oneTwoThree threeLinesRotation_map_zeroThreeFive
    (posDef_threeLines_014_of_traceCell slide) point hcell

theorem exists_posDef_threeLines_of_traceOrbit015 (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6) (hcell : ThreeLinesTraceOrbit015 slide hadmissible.1 point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef :=
  exists_posDef_threeLines_of_rotatedTraceOrbitCell slide hadmissible.1
    (ThreeLinesTraceCell015 slide) {0, 1, 5} {1, 3, 4} {0, 2, 3}
    (by decide) (by decide) (by decide)
    threeLinesRotation_map_oneThreeFour threeLinesRotation_map_zeroTwoThree
    (posDef_threeLines_015_of_traceCell slide hadmissible) point hcell

theorem exists_posDef_threeLines_of_traceOrbit024 (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) (hcell : ThreeLinesTraceOrbit024 slide hslideNe point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef :=
  exists_posDef_threeLines_of_rotatedTraceOrbitCell slide hslideNe
    (ThreeLinesTraceCell024 slide) {0, 2, 4} {1, 2, 5} {3, 4, 5}
    (by decide) (by decide) (by decide)
    threeLinesRotation_map_oneTwoFive threeLinesRotation_map_threeFourFive
    (posDef_threeLines_024_of_traceCell slide) point hcell

theorem exists_posDef_threeLines_of_traceOrbit025 (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6) (hcell : ThreeLinesTraceOrbit025 slide hadmissible.1 point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef :=
  exists_posDef_threeLines_of_rotatedTraceOrbitCell slide hadmissible.1
    (ThreeLinesTraceCell025 slide) {0, 2, 5} {1, 4, 5} {2, 3, 4}
    (by decide) (by decide) (by decide)
    threeLinesRotation_map_oneFourFive threeLinesRotation_map_twoThreeFour
    (posDef_threeLines_025_of_traceCell slide hadmissible) point hcell

theorem exists_posDef_threeLines_of_traceOrbit045 (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) (hcell : ThreeLinesTraceOrbit045 slide hslideNe point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef :=
  exists_posDef_threeLines_of_rotatedTraceOrbitCell slide hslideNe
    (ThreeLinesTraceCell045 slide) {0, 4, 5} {1, 2, 4} {2, 3, 5}
    (by decide) (by decide) (by decide)
    threeLinesRotation_map_oneTwoFour threeLinesRotation_map_twoThreeFive
    (posDef_threeLines_045_of_traceCell slide) point hcell

theorem exists_posDef_threeLines_of_movedTraceOrbitCellFires (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesMovedTraceOrbitCellFires slide hadmissible.1 point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef := by
  rcases hcell with h014 | h015 | h024 | h025 | h045
  · exact exists_posDef_threeLines_of_traceOrbit014 slide hadmissible.1 point h014
  · exact exists_posDef_threeLines_of_traceOrbit015 slide hadmissible point h015
  · exact exists_posDef_threeLines_of_traceOrbit024 slide hadmissible.1 point h024
  · exact exists_posDef_threeLines_of_traceOrbit025 slide hadmissible point h025
  · exact exists_posDef_threeLines_of_traceOrbit045 slide hadmissible.1 point h045

/-! ## Spend the moved-orbit atlas in A2 -/

def ThreeLinesSevenOrbitTraceAtlasCellFires (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) : Prop :=
  ThreeLinesExpandedUnsignedCellFires slide point ∨
    ThreeLinesMovedTraceOrbitCellFires slide hslideNe point

theorem exists_posDef_threeLines_of_sevenOrbitTraceAtlasCellFires (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesSevenOrbitTraceAtlasCellFires slide hadmissible.1 point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef := by
  rcases hcell with hfixed | hmoved
  · exact exists_posDef_threeLines_of_expandedUnsignedCellFires
      slide hadmissible point hfixed
  · exact exists_posDef_threeLines_of_movedTraceOrbitCellFires
      slide hadmissible point hmoved

def ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines : Prop :=
  ∀ slide : ℝ, ∀ hadmissible : IsAdmissibleThreeLinesParameter slide, 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      ¬ ThreeLinesBudgetCellFires slide point →
      ¬ ThreeLinesReadingCoverCellFires slide point →
      ¬ ThreeLinesSevenOrbitTraceAtlasCellFires slide hadmissible.1 point →
      (∃ selected : Finset (Fin 6), ThreeLinesOffLinesWeakTriple slide point selected) →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef

theorem traceBlindThreeLinesFundamentalDomain_of_sevenOrbitTraceBlind
    (hblind :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines := by
  intro slide hadmissible hfundamental point hbudgetBlind hreadingBlind
    hfixedBlind hweak
  rcases Classical.em
      (ThreeLinesMovedTraceOrbitCellFires slide hadmissible.1 point) with hmoved | hmoved
  · exact exists_posDef_threeLines_of_movedTraceOrbitCellFires
      slide hadmissible point hmoved
  · apply hblind slide hadmissible hfundamental point hbudgetBlind hreadingBlind
    · intro hcell
      rcases hcell with hfixed | hnew
      · exact hfixedBlind hfixed
      · exact hmoved hnew
    · exact hweak

theorem sevenOrbitTraceBlindThreeLinesFundamentalDomain_of_traceBlind
    (hblind : ChartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines := by
  intro slide hadmissible hfundamental point hbudgetBlind hreadingBlind
    hatlasBlind hweak
  have hfixedBlind : ¬ ThreeLinesExpandedUnsignedCellFires slide point := by
    intro hfixed
    exact hatlasBlind (Or.inl hfixed)
  exact hblind slide hadmissible hfundamental point hbudgetBlind hreadingBlind
    hfixedBlind hweak

theorem
    chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff_traceBlind :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ↔
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines :=
  ⟨traceBlindThreeLinesFundamentalDomain_of_sevenOrbitTraceBlind,
    sevenOrbitTraceBlindThreeLinesFundamentalDomain_of_traceBlind⟩

theorem chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ↔
      ChartTieFreeThreeLinesFundamentalDomain :=
  chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff_traceBlind.trans
    chartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines_iff

end Gtz

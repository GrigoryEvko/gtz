import Gtz.Wave.ThreeLinesStallEscapeWiring
import Gtz.Wave.ThreeLinesDominanceNoGo
import Gtz.Design.ThreeLinesAtlas
import Gtz.Design.PivotStallPropagation
import Gtz.Design.CardFourStallEquivalence
import Gtz.LinAlg.BernsteinPositivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The three-lines backlog: card-four residual, slide elimination, dominance no-go

This module wires landed three-lines mathematics.  It adds no axiom and it opens
no new route.  Five blocks:

1. The uniform chart point, the refutation of the dominance cover, and explicit
   inhabitants of the class antecedents.
2. The card-four residual of the class target, in closed-form minor signs.
3. Three generic pivot laws instantiated at the three-lines direction family.
4. The Bernstein bridge.  The determinant minor is degree two in the slide, so a
   Moebius substitution turns fundamental-domain positivity into FIVE
   slide-free coefficient inequalities.  The real parameter disappears.
5. The mass homogeneity of the three minors.  Positive definiteness is invariant
   under a positive rescaling of all six masses, so the eleven-real chart cell
   carries one exact scaling freedom.

Each statement below is labelled EQUIVALENCE, STRICT REDUCTION, WIRING or
KERNEL REFUTATION in its docstring.  An equivalence buys a checkable shape, not
strength.
-/

namespace Gtz

open Finset Matrix

/-! ## Part 1.  The uniform chart point, and the dominance no-go

`Gtz.ThreeLinesDominanceNoGo` owns the uniform mass, the uniform weight and the
three field facts, but never packages them as a `Gtz.DirectionChartPoint`.  The
package closes the refutation and inhabits every antecedent of the class. -/

/-- The uniform three-lines chart point: mass one and weight one sixth at every
label. -/
noncomputable def threeLinesUniformPoint : DirectionChartPoint 6 where
  mass := uniformSixMass
  weight := threeLinesUniformWeight
  mass_pos := uniformSixMass_pos
  weight_pos := threeLinesUniformWeight_pos
  weight_sum_one := threeLinesUniformWeight_sum

theorem mass_threeLinesUniformPoint (label : Fin 6) :
    threeLinesUniformPoint.mass label = 1 := rfl

theorem chartExcess_threeLinesUniformPoint (label : Fin 6) :
    chartExcess threeLinesUniformPoint.mass threeLinesUniformPoint.weight label = 5 :=
  chartExcess_uniformSix label

/-- **KERNEL REFUTATION.**  The dominance family is not a cover.  The uniform
chart point at slide three defeats it. -/
theorem not_threeLinesDominanceCovers : ¬ ThreeLinesDominanceCovers := by
  refine not_threeLinesDominanceCovers_of_witness threeLinesUniformPoint 3 ?_ ?_ ?_ ?_
  · rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]; norm_num
  · rw [chartExcess_threeLinesUniformPoint]; norm_num
  · rw [chartExcess_threeLinesUniformPoint, mass_threeLinesUniformPoint]; norm_num
  · rw [chartExcess_threeLinesUniformPoint, chartExcess_threeLinesUniformPoint,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
    norm_num

/-! ### Inhabitants of the class antecedents

The class target quantifies over admissible slides in the fundamental domain,
over chart points, and over chart points that carry a weakly dominating triple.
All three antecedents are inhabited, so the obligation is not vacuous. -/

theorem isAdmissibleThreeLinesParameter_one : IsAdmissibleThreeLinesParameter 1 :=
  ⟨one_ne_zero, by norm_num⟩

theorem one_le_abs_one : (1:ℝ) ≤ |(1:ℝ)| := by rw [abs_one]

theorem threeLinesChartCoefficient_uniform_mem {label : Fin 6}
    (hmem : label ∈ ({0, 1, 3} : Finset (Fin 6))) :
    threeLinesChartCoefficient threeLinesUniformPoint.mass threeLinesUniformPoint.weight
      ({0, 1, 3} : Finset (Fin 6)) label = 5 := by
  rw [threeLinesChartCoefficient_of_mem _ _ hmem]
  exact chartExcess_threeLinesUniformPoint label

theorem threeLinesChartCoefficient_uniform_notMem {label : Fin 6}
    (hmem : label ∉ ({0, 1, 3} : Finset (Fin 6))) :
    threeLinesChartCoefficient threeLinesUniformPoint.mass threeLinesUniformPoint.weight
      ({0, 1, 3} : Finset (Fin 6)) label = -1 := by
  rw [threeLinesChartCoefficient_of_notMem _ _ hmem, mass_threeLinesUniformPoint]

/-- **The class antecedent is inhabited.**  At slide one the coordinate triple
of the uniform chart point dominates STRICTLY.  Its three closed-form minors are
`3`, `8` and `16`. -/
theorem posDef_directionChartGap_threeLinesUniform_slideOne :
    (directionChartGap (threeLinesDirection 1) threeLinesUniformPoint.mass
      threeLinesUniformPoint.weight ({0, 1, 3} : Finset (Fin 6))).PosDef := by
  have h0 := threeLinesChartCoefficient_uniform_mem (label := 0) (by decide)
  have h1 := threeLinesChartCoefficient_uniform_mem (label := 1) (by decide)
  have h3 := threeLinesChartCoefficient_uniform_mem (label := 3) (by decide)
  have h2 := threeLinesChartCoefficient_uniform_notMem (label := 2) (by decide)
  have h4 := threeLinesChartCoefficient_uniform_notMem (label := 4) (by decide)
  have h5 := threeLinesChartCoefficient_uniform_notMem (label := 5) (by decide)
  refine (posDef_directionChartGap_iff_hasPositiveThreeLinesMinors 1 threeLinesUniformPoint
    ({0, 1, 3} : Finset (Fin 6))).mpr ⟨?_, ?_, ?_⟩
  · rw [threeLinesCornerMinor, h0, h2, h4]; norm_num
  · rw [threeLinesBlockMinor, h0, h1, h2, h4, h5]; norm_num
  · rw [threeLinesBasisDeterminant, h0, h1, h2, h3, h4, h5]; norm_num

/-- **The weak antecedent is inhabited.**  The uniform chart point at slide one
carries a weakly dominating triple. -/
theorem exists_weakTriple_threeLinesUniform_slideOne :
    ∃ weakSet : Finset (Fin 6), weakSet.card = 3 ∧
      (directionChartGap (threeLinesDirection 1) threeLinesUniformPoint.mass
        threeLinesUniformPoint.weight weakSet).PosSemidef :=
  ⟨{0, 1, 3}, by decide, posDef_directionChartGap_threeLinesUniform_slideOne.posSemidef⟩

/-! ## Part 2.  The card-four residual of the class target

Four landed unconditional theorems compose here:
`Gtz.threeLines_cardThree_or_cardFour_stall` (a dichotomy with no hypothesis),
`Gtz.exists_cardThree_posDef_iff_exists_nonStalledCardFour` (generic),
`Gtz.threeLinesFundamentalStallEscape_iff_chartTieFree` (an `Iff` with the
target) and `Gtz.chartTieFreeThreeLinesFundamentalDomain_iff_minorSigns` (the
target as closed-form minor signs). -/

/-- The class residual in card-four minor form.  At every admissible slide of the
fundamental domain, at every chart point that carries a weakly dominating triple,
every stalled positive-definite four-set is accompanied by a card-three subset
whose three closed-form minors are positive. -/
def ThreeLinesStalledCardFourMinorEscape : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      (∃ weakSet : Finset (Fin 6), weakSet.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          weakSet).PosSemidef) →
      ∀ stalled : Finset (Fin 6), stalled.card = 4 →
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          stalled).PosDef →
        (∀ label ∈ stalled, 1 ≤ chartLadderPivot (threeLinesDirection slide)
          point.mass point.weight stalled label) →
        ∃ selected : Finset (Fin 6), selected.card = 3 ∧
          HasPositiveThreeLinesMinors slide point selected

/-- **EQUIVALENCE, NOT PROGRESS IN STRENGTH.**  The class target is exactly the
card-four minor escape.  The forward direction ignores the stall data.  The
reverse direction spends the unconditional dichotomy on the strict branch and the
escape on the stalled branch.

What this buys is a FINITE, CHECKABLE SHAPE: the demand is now three polynomial
signs at one of twenty card-three subsets, under a card-four antecedent that
hands the prover a positive-definite matrix and four pivot inequalities. -/
theorem chartTieFreeThreeLinesFundamentalDomain_iff_stalledCardFourMinorEscape :
    ChartTieFreeThreeLinesFundamentalDomain ↔ ThreeLinesStalledCardFourMinorEscape := by
  constructor
  · intro hdomain slide hadmissible hbound point hweak _stalled _hcard _hpd _hstall
    exact chartTieFreeThreeLinesFundamentalDomain_iff_minorSigns.mp hdomain slide
      hadmissible hbound point hweak
  · intro hescape
    refine chartTieFreeThreeLinesFundamentalDomain_iff_minorSigns.mpr ?_
    intro slide hadmissible hbound point hweak
    rcases threeLines_cardThree_or_cardFour_stall slide point with
      ⟨selected, hcard, hpd⟩ | ⟨stalled, hcard, hpd, hstall⟩
    · exact ⟨selected, hcard,
        (posDef_directionChartGap_iff_hasPositiveThreeLinesMinors slide point selected).mp hpd⟩
    · exact hescape slide hadmissible hbound point hweak stalled hcard hpd hstall

/-- **EQUIVALENCE.**  The four-way joint of the ring: the stall-escape
restatement, the class target and the card-four minor escape are one statement. -/
theorem threeLinesFundamentalStallEscape_iff_stalledCardFourMinorEscape :
    ThreeLinesFundamentalStallEscape ↔ ThreeLinesStalledCardFourMinorEscape := by
  rw [threeLinesFundamentalStallEscape_iff_chartTieFree,
    chartTieFreeThreeLinesFundamentalDomain_iff_stalledCardFourMinorEscape]

/-- **EQUIVALENCE, UNCONDITIONAL AND POINTWISE.**  A three-lines chart point
carries a card-three subset with three positive closed-form minors exactly when
it carries a non-stalled positive-definite four-set.  This is the generic
card-four equivalence read through the Cauchy-Binet minors. -/
theorem exists_positiveThreeLinesMinors_iff_exists_nonStalledCardFour (slide : ℝ)
    (point : DirectionChartPoint 6) :
    (∃ selected : Finset (Fin 6), selected.card = 3 ∧
        HasPositiveThreeLinesMinors slide point selected)
      ↔ ∃ selected : Finset (Fin 6), selected.card = 4 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef ∧
        ∃ label ∈ selected, chartLadderPivot (threeLinesDirection slide) point.mass
          point.weight selected label < 1 := by
  refine Iff.trans ?_ (exists_cardThree_posDef_iff_exists_nonStalledCardFour
    (threeLinesDirection slide) point)
  constructor
  · rintro ⟨selected, hcard, hsigns⟩
    exact ⟨selected, hcard,
      (posDef_directionChartGap_iff_hasPositiveThreeLinesMinors slide point selected).mpr hsigns⟩
  · rintro ⟨selected, hcard, hpd⟩
    exact ⟨selected, hcard,
      (posDef_directionChartGap_iff_hasPositiveThreeLinesMinors slide point selected).mp hpd⟩

/-- **STRICT REDUCTION, NOT AN EQUIVALENCE.**  If no stalled positive-definite
card-four selection exists at any admissible slide of the fundamental domain,
the class target holds.  The weak antecedent is never used, so this hypothesis is
strictly stronger than the target: the target permits a stalled four-set to sit
beside a strict triple, and this hypothesis forbids it. -/
theorem chartTieFreeThreeLinesFundamentalDomain_of_no_stalled_cardFour
    (hno : ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
      ∀ point : DirectionChartPoint 6, ∀ selected : Finset (Fin 6), selected.card = 4 →
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef →
        ∃ label ∈ selected, chartLadderPivot (threeLinesDirection slide) point.mass
          point.weight selected label < 1) :
    ChartTieFreeThreeLinesFundamentalDomain := by
  intro slide hadmissible hbound point _hweak
  rcases threeLines_cardThree_or_cardFour_stall slide point with
    hstrict | ⟨stalled, hcard, hpd, hstall⟩
  · exact hstrict
  · obtain ⟨label, hmem, hlt⟩ := hno slide hadmissible hbound point stalled hcard hpd
    exact absurd (hstall label hmem) (not_le.mpr hlt)

/-! ## Part 3.  Three generic pivot laws at the three-lines direction

The first two engines already carry `direction` as an argument, so each
instantiation is one application.  The third is hard-coded to the K4 chart
although its proof uses the K4 configuration only through the full-selection
positivity.  A direction-generic restatement is landed here, with the
full-selection positivity taken as a hypothesis. -/

/-- **WIRING.**  A stalled positive-definite four-set of the three-lines chart
admits an outside label whose deletion pivot is at least one. -/
theorem threeLines_card_four_stall_exists_outside_pivot_ge_one (slide : ℝ)
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)} (hcard : selected.card = 4)
    (hpd : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot (threeLinesDirection slide) point.mass point.weight
        selected label) :
    ∃ added ∉ selected,
      1 ≤ chartLadderPivot (threeLinesDirection slide) point.mass point.weight
        selected added :=
  card_four_stall_exists_outside_pivot_ge_one (threeLinesDirection slide) point hcard hpd hstall

/-- **WIRING.**  The four-set propagation dichotomy at the three-lines chart. -/
theorem threeLines_card_four_stall_exchange_or_priced_endpoint (slide : ℝ)
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)} (hcard : selected.card = 4)
    (hpd : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot (threeLinesDirection slide) point.mass point.weight
        selected label) :
    ∃ added : Fin 6, added ∉ selected ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        (insert added selected)).PosDef ∧
      1 / 2 ≤ chartLadderPivot (threeLinesDirection slide) point.mass point.weight
        (insert added selected) added ∧
      chartLadderPivot (threeLinesDirection slide) point.mass point.weight
        (insert added selected) added < 1 ∧
      ((∃ dropped ∈ selected,
          chartLadderPivot (threeLinesDirection slide) point.mass point.weight
              (insert added selected) dropped < 1 ∧
          (directionChartGap (threeLinesDirection slide) point.mass point.weight
            ((insert added selected).erase dropped)).PosDef)
        ∨ ((∀ dropped ∈ selected,
              1 ≤ chartLadderPivot (threeLinesDirection slide) point.mass point.weight
                (insert added selected) dropped) ∧
            ∀ missing ∉ insert added selected,
              1 + 1 / (2 * point.weight missing)
                < chartLadderPivot (threeLinesDirection slide) point.mass point.weight
                    (insert added selected) missing)) :=
  card_four_stall_exchange_or_priced_endpoint (threeLinesDirection slide) point hcard hpd hstall

/-- **THE UNIV-DESCENT LAW, DIRECTION-GENERIC.**  Every four-element set of
labels holds a label that is droppable from the full selection.  The landed K4
copy hard-codes the chart, but the only K4 input is the full-selection
positivity, which is a hypothesis here.

At the full selection the balance spends exactly three units, while four labels
alone would already spend `4` minus their weight, which is more than three
because the two remaining weights are positive. -/
theorem exists_mem_pivot_univ_lt_one_of_card_four_of_posDef_univ
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (hunivPD : (directionChartGap direction point.mass point.weight Finset.univ).PosDef)
    {sel : Finset (Fin 6)} (hcard : sel.card = 4) :
    ∃ label ∈ sel, chartLadderPivot direction point.mass point.weight
      Finset.univ label < 1 := by
  by_contra hall
  push Not at hall
  have hbal := pivot_balance direction point Finset.univ hunivPD
  rw [Finset.compl_univ, Finset.sum_empty, add_zero] at hbal
  rw [← Finset.sum_add_sum_compl sel] at hbal
  have hinside : ((sel.card : ℝ) - ∑ label ∈ sel, point.weight label)
      ≤ ∑ label ∈ sel, (1 - point.weight label)
        * chartLadderPivot direction point.mass point.weight Finset.univ label := by
    have hterm : ∀ label ∈ sel, (1 - point.weight label)
        ≤ (1 - point.weight label)
          * chartLadderPivot direction point.mass point.weight Finset.univ label := by
      intro label hmem
      have hw1 := directionChartPoint_weight_lt_one point label
      exact le_mul_of_one_le_right (by linarith) (hall label hmem)
    have hsum := Finset.sum_le_sum hterm
    have hleft : ∑ label ∈ sel, (1 - point.weight label)
        = (sel.card : ℝ) - ∑ label ∈ sel, point.weight label := by
      rw [Finset.sum_sub_distrib, Finset.sum_const]
      simp
    rwa [hleft] at hsum
  have houtside : 0 ≤ ∑ label ∈ selᶜ, (1 - point.weight label)
      * chartLadderPivot direction point.mass point.weight Finset.univ label := by
    refine Finset.sum_nonneg fun label _ => ?_
    have hw1 := directionChartPoint_weight_lt_one point label
    exact mul_nonneg (by linarith)
      (chartLadderPivot_nonneg_of_posDef direction point.mass point.weight
        point.mass_pos point.weight_pos Finset.univ hunivPD label)
  have hsplit : ∑ label ∈ sel, point.weight label
      + ∑ label ∈ selᶜ, point.weight label = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact point.weight_sum_one
  have hcompl : selᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, hcard]
    simp
  have houtPos : 0 < ∑ label ∈ selᶜ, point.weight label :=
    Finset.sum_pos (fun label _ => point.weight_pos label) hcompl
  rw [hcard] at hinside
  norm_num at hinside
  linarith

/-- **WIRING.**  The univ-descent law at the three-lines chart, at every slide.
The full-selection positivity is landed and unconditional here. -/
theorem threeLines_exists_mem_pivot_univ_lt_one_of_card_four (slide : ℝ)
    (point : DirectionChartPoint 6) {sel : Finset (Fin 6)} (hcard : sel.card = 4) :
    ∃ label ∈ sel, chartLadderPivot (threeLinesDirection slide) point.mass point.weight
      Finset.univ label < 1 :=
  exists_mem_pivot_univ_lt_one_of_card_four_of_posDef_univ (threeLinesDirection slide) point
    (posDef_directionChartGap_univ_threeLines slide point) hcard

/-! ## Part 4.  The Bernstein bridge, and the elimination of the slide

`Gtz.chartTieFreeThreeLinesFundamentalDomain_iff_minorSigns` reduces the class to
three polynomial signs.  Two of the three carry no slide at all.  The third,
`Gtz.threeLinesBasisDeterminant`, is degree TWO in the slide, on the UNBOUNDED
domain `1 <= |slide|`.

`Gtz.bernstein_coeff_pos` covers the COMPACT interval `[0,1]` only.  The
Moebius substitution `slide = 1 / u` repairs the mismatch and costs nothing,
because a quadratic stays a quadratic: for `slide` at least one,

  `leading * slide ^ 2 + linear * slide + const
     = slide ^ 2 * (leading + linear * u + const * u ^ 2)`  with `u = 1 / slide`.

The reversed polynomial has degree two, so its Bernstein form has exactly THREE
coefficients.  A mirror at `slide = -slide` covers the negative half line.  The
outcome is five coefficient inequalities with NO slide in them. -/

section Bernstein

open Polynomial

/-- The three degree-two Bernstein basis polynomials, evaluated. -/
private theorem bernsteinTwo_eval (u : ℝ) :
    (bernsteinPolynomial ℝ 2 0).eval u = (1 - u) ^ 2
      ∧ (bernsteinPolynomial ℝ 2 1).eval u = 2 * u * (1 - u)
      ∧ (bernsteinPolynomial ℝ 2 2).eval u = u ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [bernsteinPolynomial]
      simp only [eval_mul, eval_pow, eval_sub, eval_one, eval_X, eval_natCast,
        Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self]
      norm_num

/-- The three Bernstein coefficients of a quadratic on `[0,1]`. -/
noncomputable def quadraticBernsteinCoeff (leading linear const : ℝ) (index : ℕ) : ℝ :=
  if index = 0 then leading
  else if index = 1 then leading + linear / 2
  else leading + linear + const

/-- The Bernstein form of a quadratic reproduces the quadratic. -/
private theorem sum_quadraticBernstein (leading linear const u : ℝ) :
    ∑ index ∈ Finset.range (2 + 1), quadraticBernsteinCoeff leading linear const index
        * (bernsteinPolynomial ℝ 2 index).eval u
      = leading + linear * u + const * u ^ 2 := by
  obtain ⟨hzero, hone, htwo⟩ := bernsteinTwo_eval u
  have ezero : quadraticBernsteinCoeff leading linear const 0 = leading := by
    simp [quadraticBernsteinCoeff]
  have eone : quadraticBernsteinCoeff leading linear const 1 = leading + linear / 2 := by
    simp [quadraticBernsteinCoeff]
  have etwo : quadraticBernsteinCoeff leading linear const 2 = leading + linear + const := by
    simp [quadraticBernsteinCoeff]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, ezero, eone, etwo, hzero, hone, htwo]
  ring

/-- **THE MOEBIUS BERNSTEIN LAW, POSITIVE HALF LINE.**  Three slide-free
coefficient signs prove a quadratic positive on the whole ray `1 <= slide`. -/
theorem quadratic_pos_of_bernstein_ge_one {leading linear const : ℝ}
    (hzero : 0 < leading) (hone : 0 < leading + linear / 2)
    (htwo : 0 < leading + linear + const)
    {slide : ℝ} (hslide : 1 ≤ slide) :
    0 < leading * slide ^ 2 + linear * slide + const := by
  have hpos : (0:ℝ) < slide := lt_of_lt_of_le one_pos hslide
  have hne : slide ≠ 0 := ne_of_gt hpos
  have hulow : (0:ℝ) ≤ 1 / slide := le_of_lt (div_pos one_pos hpos)
  have huhigh : 1 / slide ≤ 1 := by rw [div_le_one hpos]; exact hslide
  have hkey : 0 < leading + linear * (1 / slide) + const * (1 / slide) ^ 2 := by
    rw [← sum_quadraticBernstein]
    refine bernstein_coeff_pos 2 _ ?_ hulow huhigh
    intro index hindex
    rw [Finset.mem_range] at hindex
    interval_cases index
    · simpa [quadraticBernsteinCoeff] using hzero
    · simpa [quadraticBernsteinCoeff] using hone
    · simpa [quadraticBernsteinCoeff] using htwo
  have hfactor : leading * slide ^ 2 + linear * slide + const
      = slide ^ 2 * (leading + linear * (1 / slide) + const * (1 / slide) ^ 2) := by
    field_simp
  rw [hfactor]
  exact mul_pos (pow_pos hpos 2) hkey

/-- **THE MOEBIUS BERNSTEIN LAW, NEGATIVE HALF LINE.**  The mirror of the
positive law at `slide` replaced by its negative. -/
theorem quadratic_pos_of_bernstein_le_neg_one {leading linear const : ℝ}
    (hzero : 0 < leading) (hone : 0 < leading - linear / 2)
    (htwo : 0 < leading - linear + const)
    {slide : ℝ} (hslide : slide ≤ -1) :
    0 < leading * slide ^ 2 + linear * slide + const := by
  have hmirror : (1:ℝ) ≤ -slide := by linarith
  have hexpand : leading * slide ^ 2 + linear * slide + const
      = leading * (-slide) ^ 2 + -linear * (-slide) + const := by ring
  rw [hexpand]
  exact quadratic_pos_of_bernstein_ge_one hzero (by linarith) (by linarith) hmirror

/-- **THE FUNDAMENTAL-DOMAIN BERNSTEIN LAW.**  Five slide-free coefficient signs
prove a quadratic positive on the whole domain `1 <= |slide|`. -/
theorem quadratic_pos_of_bernstein_fundamental {leading linear const : ℝ}
    (hlead : 0 < leading)
    (hplus : 0 < leading + linear / 2) (hminus : 0 < leading - linear / 2)
    (hone : 0 < leading + linear + const) (hnegOne : 0 < leading - linear + const)
    {slide : ℝ} (hslide : 1 ≤ |slide|) :
    0 < leading * slide ^ 2 + linear * slide + const := by
  rcases le_abs.mp hslide with hright | hleft
  · exact quadratic_pos_of_bernstein_ge_one hlead hplus hone hright
  · exact quadratic_pos_of_bernstein_le_neg_one hlead hminus hnegOne (by linarith)

end Bernstein

/-! ### The three Cauchy-Binet bracket aggregates

`Gtz.threeLinesBasisDeterminant` weights each of the seventeen independent
triples by its squared bracket.  The bracket takes three values only, so the
determinant splits into three aggregates and the slide sits outside them. -/

/-- The twelve triples of unit squared bracket. -/
def threeLinesUnitBracketSum (coefficient : Fin 6 → ℝ) : ℝ :=
  coefficient 0 * coefficient 1 * coefficient 3
    + coefficient 0 * coefficient 1 * coefficient 4
    + coefficient 0 * coefficient 2 * coefficient 3
    + coefficient 0 * coefficient 2 * coefficient 4
    + coefficient 0 * coefficient 3 * coefficient 5
    + coefficient 0 * coefficient 4 * coefficient 5
    + coefficient 1 * coefficient 2 * coefficient 3
    + coefficient 1 * coefficient 2 * coefficient 4
    + coefficient 1 * coefficient 3 * coefficient 4
    + coefficient 2 * coefficient 3 * coefficient 4
    + coefficient 2 * coefficient 3 * coefficient 5
    + coefficient 3 * coefficient 4 * coefficient 5

/-- The four triples of squared bracket `slide ^ 2`. -/
def threeLinesSlideBracketSum (coefficient : Fin 6 → ℝ) : ℝ :=
  coefficient 0 * coefficient 1 * coefficient 5
    + coefficient 0 * coefficient 2 * coefficient 5
    + coefficient 1 * coefficient 2 * coefficient 5
    + coefficient 1 * coefficient 4 * coefficient 5

/-- The free triple `{2,4,5}`, of squared bracket `(1 + slide) ^ 2`. -/
def threeLinesFreeBracketProduct (coefficient : Fin 6 → ℝ) : ℝ :=
  coefficient 2 * coefficient 4 * coefficient 5

/-- **THE BRACKET SPLIT.**  The determinant is the unit aggregate, plus the slide
aggregate at weight `slide ^ 2`, plus the free triple at weight
`(1 + slide) ^ 2`. -/
theorem threeLinesBasisDeterminant_eq_bracketSplit (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    threeLinesBasisDeterminant slide coefficient
      = threeLinesUnitBracketSum coefficient
        + slide ^ 2 * threeLinesSlideBracketSum coefficient
        + (1 + slide) ^ 2 * threeLinesFreeBracketProduct coefficient := by
  rw [threeLinesBasisDeterminant, threeLinesUnitBracketSum, threeLinesSlideBracketSum,
    threeLinesFreeBracketProduct]
  ring

/-- **THE DETERMINANT AS A QUADRATIC IN THE SLIDE.**  The three coefficients are
the slide aggregate plus the free triple, twice the free triple, and the unit
aggregate plus the free triple. -/
theorem threeLinesBasisDeterminant_eq_slideQuadratic (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    threeLinesBasisDeterminant slide coefficient
      = (threeLinesSlideBracketSum coefficient + threeLinesFreeBracketProduct coefficient)
          * slide ^ 2
        + (2 * threeLinesFreeBracketProduct coefficient) * slide
        + (threeLinesUnitBracketSum coefficient + threeLinesFreeBracketProduct coefficient) := by
  rw [threeLinesBasisDeterminant_eq_bracketSplit]
  ring

/-- The five slide-free bracket signs that certify a card-three subset over the
whole fundamental domain at once.  Read in order: the corner minor, the block
minor, the leading determinant coefficient, the two Bernstein middle
coefficients, and the determinant values at `slide = 1` and `slide = -1`. -/
def HasSlideFreeThreeLinesBrackets (coefficient : Fin 6 → ℝ) : Prop :=
  0 < threeLinesCornerMinor coefficient
    ∧ 0 < threeLinesBlockMinor coefficient
    ∧ 0 < threeLinesSlideBracketSum coefficient + threeLinesFreeBracketProduct coefficient
    ∧ 0 < threeLinesSlideBracketSum coefficient + 2 * threeLinesFreeBracketProduct coefficient
    ∧ 0 < threeLinesSlideBracketSum coefficient
    ∧ 0 < threeLinesUnitBracketSum coefficient + threeLinesSlideBracketSum coefficient
        + 4 * threeLinesFreeBracketProduct coefficient
    ∧ 0 < threeLinesUnitBracketSum coefficient + threeLinesSlideBracketSum coefficient

/-- **THE SLIDE LEAVES THE DETERMINANT.**  Five inequalities in the six
coefficients alone prove the basis determinant positive at EVERY slide of the
fundamental domain. -/
theorem threeLinesBasisDeterminant_pos_of_bracketCertificate (coefficient : Fin 6 → ℝ)
    (hlead : 0 < threeLinesSlideBracketSum coefficient + threeLinesFreeBracketProduct coefficient)
    (hplus : 0 < threeLinesSlideBracketSum coefficient
      + 2 * threeLinesFreeBracketProduct coefficient)
    (hminus : 0 < threeLinesSlideBracketSum coefficient)
    (hone : 0 < threeLinesUnitBracketSum coefficient + threeLinesSlideBracketSum coefficient
      + 4 * threeLinesFreeBracketProduct coefficient)
    (hnegOne : 0 < threeLinesUnitBracketSum coefficient + threeLinesSlideBracketSum coefficient)
    {slide : ℝ} (hslide : 1 ≤ |slide|) :
    0 < threeLinesBasisDeterminant slide coefficient := by
  rw [threeLinesBasisDeterminant_eq_slideQuadratic]
  exact quadratic_pos_of_bernstein_fundamental (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hslide

/-- **STRICT REDUCTION.**  The slide-free bracket certificate implies the
closed-form minor positivity at every slide of the fundamental domain. -/
theorem hasPositiveThreeLinesMinors_of_slideFreeBrackets (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hbrackets : HasSlideFreeThreeLinesBrackets
      (threeLinesChartCoefficient point.mass point.weight selected))
    {slide : ℝ} (hslide : 1 ≤ |slide|) :
    HasPositiveThreeLinesMinors slide point selected := by
  obtain ⟨hcorner, hblock, hlead, hplus, hminus, hone, hnegOne⟩ := hbrackets
  exact ⟨hcorner, hblock, threeLinesBasisDeterminant_pos_of_bracketCertificate _ hlead
    hplus hminus hone hnegOne hslide⟩

/-- The slide-free certificate demand, still under the weak antecedent. -/
def ThreeLinesSlideFreeBracketCertificate : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      (∃ weakSet : Finset (Fin 6), weakSet.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          weakSet).PosSemidef) →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        HasSlideFreeThreeLinesBrackets
          (threeLinesChartCoefficient point.mass point.weight selected)

/-- The fully slide-free certificate demand.  No slide occurs anywhere in the
statement, so the chart cell is eleven reals and nothing more. -/
def ThreeLinesUniformBracketCertificate : Prop :=
  ∀ point : DirectionChartPoint 6, ∃ selected : Finset (Fin 6), selected.card = 3 ∧
    HasSlideFreeThreeLinesBrackets
      (threeLinesChartCoefficient point.mass point.weight selected)

/-- **STRICT REDUCTION, THE BERNSTEIN CONSUMER.**  The slide-free bracket
certificate discharges the class target.  This is the first consumer of
`Gtz.bernstein_coeff_pos` in the repository. -/
theorem chartTieFreeThreeLinesFundamentalDomain_of_slideFreeBrackets
    (hcert : ThreeLinesSlideFreeBracketCertificate) :
    ChartTieFreeThreeLinesFundamentalDomain := by
  refine chartTieFreeThreeLinesFundamentalDomain_iff_minorSigns.mpr ?_
  intro slide hadmissible hbound point hweak
  obtain ⟨selected, hcard, hbrackets⟩ := hcert slide hadmissible hbound point hweak
  exact ⟨selected, hcard,
    hasPositiveThreeLinesMinors_of_slideFreeBrackets point selected hbrackets hbound⟩

/-- **STRICT REDUCTION, WITH THE SLIDE FULLY REMOVED.**  A certificate that
mentions no slide at all discharges the class target on the whole fundamental
domain.  The one direction parameter of this class is eliminated. -/
theorem chartTieFreeThreeLinesFundamentalDomain_of_uniformBrackets
    (hcert : ThreeLinesUniformBracketCertificate) :
    ChartTieFreeThreeLinesFundamentalDomain :=
  chartTieFreeThreeLinesFundamentalDomain_of_slideFreeBrackets
    (fun _slide _hadmissible _hbound point _hweak => hcert point)

/-! ## Part 5.  Mass homogeneity, and one exact dimension of the chart cell

The chart coefficient is homogeneous of degree one in the mass.  The corner
minor, the block minor and the basis determinant are homogeneous of degrees one,
two and three in the coefficient.  Positivity of all three is therefore invariant
under a positive rescaling of the six masses. -/

theorem threeLinesChartCoefficient_smul_mass (scale : ℝ) (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) (label : Fin 6) :
    threeLinesChartCoefficient (fun index => scale * mass index) weight selected label
      = scale * threeLinesChartCoefficient mass weight selected label := by
  by_cases hmem : label ∈ selected
  · rw [threeLinesChartCoefficient_of_mem _ _ hmem, threeLinesChartCoefficient_of_mem _ _ hmem,
      chartExcess, chartExcess]
    ring
  · rw [threeLinesChartCoefficient_of_notMem _ _ hmem,
      threeLinesChartCoefficient_of_notMem _ _ hmem]
    ring

theorem threeLinesCornerMinor_smul (scale : ℝ) (coefficient : Fin 6 → ℝ) :
    threeLinesCornerMinor (fun index => scale * coefficient index)
      = scale * threeLinesCornerMinor coefficient := by
  rw [threeLinesCornerMinor, threeLinesCornerMinor]; ring

theorem threeLinesBlockMinor_smul (scale : ℝ) (coefficient : Fin 6 → ℝ) :
    threeLinesBlockMinor (fun index => scale * coefficient index)
      = scale ^ 2 * threeLinesBlockMinor coefficient := by
  rw [threeLinesBlockMinor, threeLinesBlockMinor]; ring

theorem threeLinesBasisDeterminant_smul (slide scale : ℝ) (coefficient : Fin 6 → ℝ) :
    threeLinesBasisDeterminant slide (fun index => scale * coefficient index)
      = scale ^ 3 * threeLinesBasisDeterminant slide coefficient := by
  rw [threeLinesBasisDeterminant, threeLinesBasisDeterminant]; ring

/-- The chart point with all six masses rescaled by a positive factor. -/
noncomputable def scaleMassChartPoint (point : DirectionChartPoint 6) {scale : ℝ}
    (hscale : 0 < scale) : DirectionChartPoint 6 where
  mass := fun label => scale * point.mass label
  weight := point.weight
  mass_pos := fun label => mul_pos hscale (point.mass_pos label)
  weight_pos := point.weight_pos
  weight_sum_one := point.weight_sum_one

private theorem pos_of_smul_pos {scale value : ℝ} (hscale : 0 < scale)
    (hpos : 0 < scale * value) : 0 < value := by
  have hne : scale ≠ 0 := ne_of_gt hscale
  have hrewrite : value = scale * value / scale := by field_simp
  rw [hrewrite]
  exact div_pos hpos hscale

/-- **THE MASS SCALING FREEDOM, KERNEL.**  The three closed-form minors of a
card-three subset are positive at a chart point exactly when they are positive at
every positive mass rescaling of that point.  The eleven-real chart cell carries
one exact scaling direction, so the effective cell is ten reals plus the
slide. -/
theorem hasPositiveThreeLinesMinors_scaleMassChartPoint (point : DirectionChartPoint 6)
    {scale : ℝ} (hscale : 0 < scale) (slide : ℝ) (selected : Finset (Fin 6)) :
    HasPositiveThreeLinesMinors slide (scaleMassChartPoint point hscale) selected
      ↔ HasPositiveThreeLinesMinors slide point selected := by
  have hcoeff : threeLinesChartCoefficient (scaleMassChartPoint point hscale).mass
      (scaleMassChartPoint point hscale).weight selected
      = fun index => scale * threeLinesChartCoefficient point.mass point.weight selected index := by
    funext label
    exact threeLinesChartCoefficient_smul_mass scale point.mass point.weight selected label
  unfold HasPositiveThreeLinesMinors
  rw [hcoeff, threeLinesCornerMinor_smul, threeLinesBlockMinor_smul,
    threeLinesBasisDeterminant_smul]
  constructor
  · rintro ⟨hcorner, hblock, hdet⟩
    exact ⟨pos_of_smul_pos hscale hcorner, pos_of_smul_pos (pow_pos hscale 2) hblock,
      pos_of_smul_pos (pow_pos hscale 3) hdet⟩
  · rintro ⟨hcorner, hblock, hdet⟩
    exact ⟨mul_pos hscale hcorner, mul_pos (pow_pos hscale 2) hblock,
      mul_pos (pow_pos hscale 3) hdet⟩

/-! ## Part 6.  A NEW CERTIFICATE: the selection leverage bound

Every part above rearranges landed statements.  This part adds a theorem the
repository does not carry, in any class.

The chart gap of a selection is `A - M`.  Here `A` is the boosted selection sum
`sum over the selection of (mass / weight) * atom`, and `M` is the raw mass
moment `sum over all labels of mass * atom`.  The corpus decides
`A - M` positive definite only through Sylvester minors, which need the whole
determinant, or through the ladder pivot, which needs a positive definite base
BEFORE the question is settled.  Both routes are circular for a first
certificate.

The bound below is not circular.  Write `dual c` for a solution of
`A * dual c = direction c`.  The number

  `leverage = sum over all labels of mass c * (direction c . dual c)`

is the total mass leverage of the configuration against the selection.
Cauchy-Schwarz in the `A` inner product prices every squared reading by its own
leverage,

  `(direction c . probe) ^ 2 <= (direction c . dual c) * (probe . A probe)`,

and summation against the masses gives `probe . M probe <= leverage * (probe . A
probe)`.  A leverage below one therefore forces `A - M` positive definite.

The certificate reads ONE scalar.  It needs no determinant, no minor, no
eigenvalue and no prior positive definiteness.  It also has an exact reading at a
card-three basis: a selected label contributes its own weight, so the criterion
says that the three labels OUTSIDE the selection carry less leverage than the
weight they leave behind.

LEVEL WARNING.  Part 6 is direction-generic machinery.  No `slide` and no
three-lines pattern occurs in it, so no statement here is a class residual.  The
three-lines residual is Part 7. -/

private theorem hermitian_of_transpose {mat : Matrix (Fin 3) (Fin 3) ℝ} (htrans : matᵀ = mat) :
    mat.IsHermitian := by
  show matᴴ = mat
  ext rowIndex colIndex
  rw [Matrix.conjTranspose_apply, star_trivial]
  exact congrFun (congrFun htrans rowIndex) colIndex

/-- The bilinear reading of one rank-one atom. -/
private theorem atomBilinear (atomVec left right : Fin 3 → ℝ) :
    left ⬝ᵥ (atomMatrix atomVec *ᵥ right) = (atomVec ⬝ᵥ left) * (atomVec ⬝ᵥ right) := by
  simp only [atomMatrix, Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun leftCoord _ =>
    Finset.sum_congr rfl fun rightCoord _ => by ring

/-- The bilinear reading of a weighted atom sum. -/
private theorem sumAtomBilinear {size : ℕ} (coefficient : Fin size → ℝ)
    (vectors : Fin size → (Fin 3 → ℝ)) (support : Finset (Fin size))
    (left right : Fin 3 → ℝ) :
    left ⬝ᵥ ((∑ label ∈ support, coefficient label • atomMatrix (vectors label)) *ᵥ right)
      = ∑ label ∈ support, coefficient label
          * ((vectors label ⬝ᵥ left) * (vectors label ⬝ᵥ right)) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomBilinear]

/-- **THE WEIGHTED CAUCHY-SCHWARZ INEQUALITY.**  The discriminant of the
nonnegative quadratic in the shift. -/
private theorem weighted_cauchy_schwarz {size : ℕ} (support : Finset (Fin size))
    (coeff first second : Fin size → ℝ) (hcoeff : ∀ index ∈ support, 0 ≤ coeff index) :
    (∑ index ∈ support, coeff index * (first index * second index)) ^ 2
      ≤ (∑ index ∈ support, coeff index * first index ^ 2)
        * (∑ index ∈ support, coeff index * second index ^ 2) := by
  have hquad : ∀ step : ℝ,
      0 ≤ (∑ index ∈ support, coeff index * first index ^ 2) * (step * step)
        + (2 * ∑ index ∈ support, coeff index * (first index * second index)) * step
        + ∑ index ∈ support, coeff index * second index ^ 2 := by
    intro step
    have hnonneg : 0 ≤ ∑ index ∈ support,
        coeff index * (step * first index + second index) ^ 2 :=
      Finset.sum_nonneg fun index hindex => mul_nonneg (hcoeff index hindex) (sq_nonneg _)
    have hexpand : ∑ index ∈ support, coeff index * (step * first index + second index) ^ 2
        = (∑ index ∈ support, coeff index * first index ^ 2) * (step * step)
          + (2 * ∑ index ∈ support, coeff index * (first index * second index)) * step
          + ∑ index ∈ support, coeff index * second index ^ 2 := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun index _ => by ring
    linarith [hexpand ▸ hnonneg]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- The arithmetic core of the certificate. -/
private theorem pos_sub_of_leverage_lt_one {selectionForm massForm leverage : ℝ}
    (hselection : 0 < selectionForm) (hbound : massForm ≤ leverage * selectionForm)
    (hleverage : leverage < 1) : 0 < selectionForm - massForm := by
  nlinarith

/-- **THE BOOSTED SELECTION MATRIX.**  The positive half of the chart gap. -/
noncomputable def chartSelectionMatrix {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ label ∈ selected, (mass label / weight label) • atomMatrix (direction label)

theorem chartSelectionMatrix_eq {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) :
    chartSelectionMatrix direction mass weight selected
      = ∑ label ∈ selected, (mass label / weight label) • atomMatrix (direction label) := rfl

/-- The quadratic reading of the chart gap: the boosted selection energy minus
the raw mass energy. -/
theorem dotProduct_directionChartGap_mulVec_split {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe)
      = (∑ label ∈ selected, (mass label / weight label) * (direction label ⬝ᵥ probe) ^ 2)
        - ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2 := by
  unfold directionChartGap
  rw [Matrix.sub_mulVec, dotProduct_sub, sumAtomBilinear, sumAtomBilinear]
  congr 1
  · exact Finset.sum_congr rfl fun label _ => by ring
  · exact Finset.sum_congr rfl fun label _ => by ring

/-- **THE LEVERAGE CERTIFICATE.**  If the total mass leverage against the
boosted selection matrix is less than one, the chart gap of that selection is
positive definite.

The hypothesis is a dual vector for every direction, which exists exactly when
the selected directions span, and one scalar inequality.  Neither a determinant
nor a minor nor a pivot appears. -/
theorem posDef_directionChartGap_of_dualLeverage_lt_one {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) (dual : Fin size → (Fin 3 → ℝ))
    (hdual : ∀ label,
      chartSelectionMatrix direction mass weight selected *ᵥ dual label = direction label)
    (hspan : ∀ probe : Fin 3 → ℝ,
      (∀ label ∈ selected, direction label ⬝ᵥ probe = 0) → probe = 0)
    (hleverage : ∑ label, mass label * (direction label ⬝ᵥ dual label) < 1) :
    (directionChartGap direction mass weight selected).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨hermitian_of_transpose (directionChartGap_transpose direction mass weight selected),
      fun probe hprobe => ?_⟩
  rw [star_trivial, dotProduct_directionChartGap_mulVec_split]
  have hcoeffNonneg : ∀ label ∈ selected, 0 ≤ mass label / weight label :=
    fun label _ => (div_pos (hmass label) (hweight label)).le
  have htermNonneg : ∀ label ∈ selected,
      0 ≤ (mass label / weight label) * (direction label ⬝ᵥ probe) ^ 2 :=
    fun label hlabel => mul_nonneg (hcoeffNonneg label hlabel) (sq_nonneg _)
  have hselection : 0 < ∑ label ∈ selected,
      (mass label / weight label) * (direction label ⬝ᵥ probe) ^ 2 := by
    rcases (Finset.sum_nonneg htermNonneg).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hall := (Finset.sum_eq_zero_iff_of_nonneg htermNonneg).mp heq.symm
      refine hprobe (hspan probe fun label hlabel => ?_)
      have hterm := hall label hlabel
      have hne : (mass label / weight label) ≠ 0 :=
        ne_of_gt (div_pos (hmass label) (hweight label))
      have hsq : (direction label ⬝ᵥ probe) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hterm with hzero | hzero
        · exact absurd hzero hne
        · exact hzero
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  have hkey : ∀ label : Fin size, (direction label ⬝ᵥ probe) ^ 2
      ≤ (direction label ⬝ᵥ dual label)
        * ∑ inner ∈ selected, (mass inner / weight inner)
            * (direction inner ⬝ᵥ probe) ^ 2 := by
    intro label
    have hcross : (direction label ⬝ᵥ probe)
        = ∑ inner ∈ selected, (mass inner / weight inner)
            * ((direction inner ⬝ᵥ dual label) * (direction inner ⬝ᵥ probe)) := by
      have hstep : probe
            ⬝ᵥ (chartSelectionMatrix direction mass weight selected *ᵥ dual label)
          = ∑ inner ∈ selected, (mass inner / weight inner)
              * ((direction inner ⬝ᵥ probe) * (direction inner ⬝ᵥ dual label)) := by
        rw [chartSelectionMatrix_eq]
        exact sumAtomBilinear _ _ _ _ _
      rw [hdual label, dotProduct_comm] at hstep
      rw [hstep]
      exact Finset.sum_congr rfl fun inner _ => by ring
    have hself : (direction label ⬝ᵥ dual label)
        = ∑ inner ∈ selected, (mass inner / weight inner)
            * (direction inner ⬝ᵥ dual label) ^ 2 := by
      have hstep : dual label
            ⬝ᵥ (chartSelectionMatrix direction mass weight selected *ᵥ dual label)
          = ∑ inner ∈ selected, (mass inner / weight inner)
              * ((direction inner ⬝ᵥ dual label) * (direction inner ⬝ᵥ dual label)) := by
        rw [chartSelectionMatrix_eq]
        exact sumAtomBilinear _ _ _ _ _
      rw [hdual label, dotProduct_comm] at hstep
      rw [hstep]
      exact Finset.sum_congr rfl fun inner _ => by ring
    have hcs := weighted_cauchy_schwarz selected (fun inner => mass inner / weight inner)
      (fun inner => direction inner ⬝ᵥ dual label)
      (fun inner => direction inner ⬝ᵥ probe) hcoeffNonneg
    rw [← hcross, ← hself] at hcs
    exact hcs
  have hbound : ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2
      ≤ (∑ label, mass label * (direction label ⬝ᵥ dual label))
        * ∑ inner ∈ selected, (mass inner / weight inner)
            * (direction inner ⬝ᵥ probe) ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun label _ => ?_
    have hstep := mul_le_mul_of_nonneg_left (hkey label) (hmass label).le
    linarith [hstep]
  exact pos_sub_of_leverage_lt_one hselection hbound hleverage

/-! ## Part 7.  The leverage certificate at the three-lines chart

`slide` appears in every statement below, so these are genuine three-lines
residuals.  The certificate demands, at every chart point that carries a weakly
dominating triple, one card-three selection that spans, one dual family, and one
scalar inequality. -/

/-- The three-lines leverage demand. -/
def ThreeLinesLeverageCertificate : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      (∃ weakSet : Finset (Fin 6), weakSet.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          weakSet).PosSemidef) →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (∀ probe : Fin 3 → ℝ,
          (∀ label ∈ selected, threeLinesDirection slide label ⬝ᵥ probe = 0) → probe = 0) ∧
        ∃ dual : Fin 6 → (Fin 3 → ℝ),
          (∀ label, chartSelectionMatrix (threeLinesDirection slide) point.mass
            point.weight selected *ᵥ dual label = threeLinesDirection slide label) ∧
          ∑ label, point.mass label
            * (threeLinesDirection slide label ⬝ᵥ dual label) < 1

/-- **STRICT REDUCTION.**  The leverage certificate discharges the class target.
The demand it replaces is a determinant sign at twenty subsets.  The demand it
makes is one scalar inequality at one subset. -/
theorem chartTieFreeThreeLinesFundamentalDomain_of_leverageCertificate
    (hcert : ThreeLinesLeverageCertificate) :
    ChartTieFreeThreeLinesFundamentalDomain := by
  intro slide hadmissible hbound point hweak
  obtain ⟨selected, hcard, hspan, dual, hdual, hleverage⟩ :=
    hcert slide hadmissible hbound point hweak
  exact ⟨selected, hcard, posDef_directionChartGap_of_dualLeverage_lt_one
    (threeLinesDirection slide) point.mass point.weight point.mass_pos point.weight_pos
    selected dual hdual hspan hleverage⟩

end Gtz

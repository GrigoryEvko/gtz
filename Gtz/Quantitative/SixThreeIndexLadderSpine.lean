import Gtz.Quantitative.StrongStationarityIndexFloor
import Gtz.Quantitative.SixThreeExclusionFrontier
import Gtz.Reduction.StressWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The `(6,3)` index ladder, stated as one chain with named open rungs

The chart-side attack on `Gtz.GtzWeighted 6 3` runs through `Gtz.SixThreeCrux`, and
everything it has produced so far is a statement about ONE natural number: the number of
active blocks, `(chartArgmaxFamily (chartPointOfDesign crux.design)).card`.  The floor of
that number has been pushed from two to three to four, each step a separate module, and
two further conditional rungs reach five and six.  What the repository has never recorded
is that the number is BOUNDED ABOVE, and by what.

This file supplies the ceiling, closes the ladder into a finite case analysis, and states
every remaining case as an EXPLICIT NAMED HYPOTHESIS rather than a `sorry`, so that a
later argument discharges a named rung instead of inventing a statement.

## The ceiling, and why it turns the ladder into a countable measure

`Gtz.chartArgmaxFamily` is a `Finset.filter` of `Gtz.chartCandidates size rank`
(`Gtz/Reduction/ChartAttainmentWeld.lean:276`), and `Gtz.chartCandidates size rank` is the
set of `rank`-element subsets of `Fin size` (`Gtz/Reduction/ChartAttainment.lean:414`).
So the active family never has more than `size.choose rank` members --- at `(6,3)`, never
more than TWENTY.  Together with the unconditional floor of four
(`Gtz.SixThreeCrux.four_le_card_chartArgmaxFamily_strong`) this confines the active count
of a counterexample to the seventeen values `4, 5, ..., 20`, and excluding all seventeen
IS the cell.

Progress along this route is therefore a single integer, and the residual is a finite list
of named rungs rather than an open-ended search.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.card_chartCandidates_eq_choose` --- the candidate count at every size and rank.
* `Gtz.card_chartArgmaxFamily_le_choose` --- **THE CEILING**, at every size and rank.
* `Gtz.SixThreeCrux.card_chartArgmaxFamily_le_twenty` and
  `Gtz.SixThreeCrux.card_chartArgmaxFamily_mem_indexWindow` --- the window `[4, 20]`.
* `Gtz.gtzWeighted_six_three_of_forall_isSixThreeActiveCountExcluded` --- **THE SPINE.**
  Excluding the seventeen counts proves the cell.
* `Gtz.forall_isSixThreeActiveCountExcluded_iff_gtzWeighted_six_three` --- and the
  decomposition is LOSSLESS: the conjunction of the seventeen rungs is EQUIVALENT to the
  cell.  See the honesty section; this is what makes the file a reformulation and not a
  reduction.
* `Gtz.SixThreeCrux.five_le_card_chartArgmaxFamily_of_isSixThreeActiveTightSupportFull`
  and `Gtz.isSixThreeActiveCountExcluded_four_of_isSixThreeActiveTightSupportFull` ---
  the support rung closes the count-four case, which demonstrates the intended mode of
  progress on the file itself.  ** READ THE QUANTIFIER: THAT DISCHARGE IS CONDITIONAL ON
  AN OPEN RUNG, AND ZERO OF THE SEVENTEEN IN-WINDOW COUNTS IS EXCLUDED UNCONDITIONALLY. **
  The two unconditional exclusions below,
  `Gtz.isSixThreeActiveCountExcluded_of_lt_four` and `..._of_twenty_lt`, cover counts
  BELOW four and ABOVE twenty --- both outside the window this file defines.  So the
  honest count of in-window rungs standing is seventeen, not sixteen, and it becomes
  sixteen only for whoever discharges the support rung first.
* `Gtz.SixThreeCrux.card_totalTightSupport_eq_two_or_three` --- the bridge between the
  support-two vocabulary of the leak calculus and the full-support vocabulary of the
  landed index floor.  At a card-three block the two are exactly complementary.
* `Gtz.SixThreeCrux.exists_unitTightEigenvectorFamily_and_assemblyMultiplier` --- the
  ambient kit, in one place: a rung-filler needs a unit block-eigenvector family and its
  matching assembly multiplier, and both are unconditional at a crux.
* `Gtz.gtzWeighted_six_three_of_isSixThreeActiveTightSupportFull_of_flatPairSeparated` ---
  **THE SECOND ROUTE THROUGH THE SPINE.**  The support rung together with a separated flat
  pair closes the cell at once, without any case analysis on the active count.  This is the
  concavity leg: a flat weight direction exists whenever the active count is at least two
  short of the atom count (`Gtz.exists_flatDirection_of_card_add_one_lt`,
  `Gtz/Quantitative/ChartSecondOrder.lean:276`), and separating two of them by a pivot
  coordinate is what remains open.
* `Gtz.isSixThreeActiveTightSupportFull_and_flatPairSeparated_iff_gtzWeighted_six_three`
  --- **AND THE SECOND ROUTE IS LOSSLESS TOO.**  Its two rungs are jointly EQUIVALENT to
  the cell, exactly as the seventeen are.  Neither route is a weakening of the target;
  both buy a named residual and nothing more, and a reader must not take the shorter one
  for the cheaper one.
* `Gtz.spineRungsHold_of_isEmpty_sixThreeCrux` --- every Prop in the file is inhabited by
  the cell itself, for one reason, which is what makes the spine's satisfiability a
  single question with a single answer: decided up to the cell and not further.

## THE AMBIENT ARITHMETIC --- what a rung-filler may already assume, and where it lives

Every one of these is landed, unconditional at a crux, and is NOT restated here, because a
second copy of a theorem is a census defect rather than a service.  Each line was opened at
the stated line while this file was written.

* the value window, `-(4/27) ≤ value < 0`:
  `Gtz.SixThreeCrux.neg_four_div_twentySeven_le_chartObjective` and
  `Gtz.SixThreeCrux.chartObjective_mem_window`,
  `Gtz/Quantitative/SixThreeExclusionFrontier.lean:165` and `:173`.
* the two first-order laws, as FIELDS of `Gtz.IsChartStationaryData`:
  `assembly_diagonal` at `Gtz/Quantitative/ChartStationary.lean:384` (the weights) and
  `assembly_commutes` at `:388` (the Grassmannian).  The crux carries the bundle by the
  theorem `Gtz.SixThreeCrux.exists_multiplier_isChartStationaryData`, NOT as a field.
* the trace law `tr(P Xi) = value + 1/size`,
  `Gtz.trace_projection_mul_multiplier_of_isChartStationaryData`, same file `:629`, and the
  sandwich `P Xi = P Xi P` at `:649`.
* the pointwise weight bounds `-value ≤ weight` and `value ≤ 1 - weight`, same file `:679`
  and `:722`, and the summed floor `-1/size ≤ value` at `:697`.
* the flat-direction count `Gtz.exists_flatDirection_of_card_add_one_lt` and the rigidity
  certificate `Gtz.eq_zero_of_flatDirection_of_span_top`,
  `Gtz/Quantitative/ChartSecondOrder.lean:276` and `:571`.

## HONESTY --- what the decomposition does and does not buy

`Gtz.forall_isSixThreeActiveCountExcluded_iff_gtzWeighted_six_three` is an EQUIVALENCE.
The conjunction of the rungs is not weaker than the target, so the split buys no
mathematics by itself; it buys a finite, named, countable residual.  Every individual rung
is VACUOUS IF `Gtz.GtzWeighted 6 3` HOLDS, because it is quantified over a structure that
is then empty --- the same caveat that attaches to every statement about
`Gtz.SixThreeCrux`.  Read a discharged rung as one of seventeen cases closed, never as
evidence about the conjecture.

## NOT PROVED here, and named

The rungs `Gtz.IsSixThreeActiveCountExcluded count` for `count = 5, ..., 20` are open, and
so are the two support rungs that would collapse several of them at once.  The repository
carries two CONDITIONAL ladder steps that bear on the low end ---
`Gtz.SixThreeCrux.five_le_card_chartArgmaxFamily_of_assemblyDiagonal` and
`Gtz.SixThreeCrux.six_le_card_chartArgmaxFamily_of_assemblyDiagonal_of_ne_five` --- and
NOTHING AT ALL above six.  Fourteen of the seventeen cases have never been attacked by any
argument in this repository.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The ceiling of the index ladder -/

/-- The candidate blocks of a chart are the `rank`-element subsets of `Fin size`, so there
are exactly `size.choose rank` of them.  Nothing in the repository counted them before, and
the count is what closes the index ladder from above. -/
theorem card_chartCandidates_eq_choose (chartSize chartRank : ℕ) :
    (chartCandidates chartSize chartRank).card = chartSize.choose chartRank := by
  classical
  have hcandidates : chartCandidates chartSize chartRank
      = Finset.powersetCard chartRank (Finset.univ : Finset (Fin chartSize)) := by
    ext selected
    simp [chartCandidates, Finset.mem_powersetCard]
  rw [hcandidates, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The active family is carved out of the candidate blocks by a filter, so it never
escapes them. -/
theorem chartArgmaxFamily_subset_chartCandidates [Nonempty (Fin rank)]
    (point : ChartPoint size rank) :
    chartArgmaxFamily point ⊆ chartCandidates size rank := by
  intro candidate hmember
  exact (mem_chartCandidates_iff size rank candidate).mpr
    ((mem_chartArgmaxFamily_iff point candidate).mp hmember).1

/-- **THE CEILING.**  However many blocks are active at a chart point, there are at most
`size.choose rank` of them.  This is the upper end the index-floor ladder has always been
climbing towards without anyone writing it down. -/
theorem card_chartArgmaxFamily_le_choose [Nonempty (Fin rank)] (point : ChartPoint size rank) :
    (chartArgmaxFamily point).card ≤ size.choose rank :=
  le_of_le_of_eq (Finset.card_le_card (chartArgmaxFamily_subset_chartCandidates point))
    (card_chartCandidates_eq_choose size rank)

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- The ceiling at the cell: a `(6,3)` counterexample has at most twenty active blocks. -/
theorem card_chartArgmaxFamily_le_twenty :
    (chartArgmaxFamily (chartPointOfDesign crux.design)).card ≤ 20 := by
  have hceiling := card_chartArgmaxFamily_le_choose (chartPointOfDesign crux.design)
  have hchoose : Nat.choose 6 3 = 20 := rfl
  rw [hchoose] at hceiling
  exact hceiling

/-- **THE INDEX WINDOW.**  The active count of a `(6,3)` counterexample lies in `[4, 20]`.
The floor is `Gtz.SixThreeCrux.four_le_card_chartArgmaxFamily_strong` and the ceiling is
the candidate count; both are unconditional. -/
theorem card_chartArgmaxFamily_mem_indexWindow :
    4 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card ∧
      (chartArgmaxFamily (chartPointOfDesign crux.design)).card ≤ 20 :=
  ⟨crux.four_le_card_chartArgmaxFamily_strong, crux.card_chartArgmaxFamily_le_twenty⟩

/-! ## The ambient kit a rung-filler needs -/

/-- **THE AMBIENT KIT.**  Both existence facts every rung of the ladder consumes, gathered
into one statement: a unit least-eigenvector family at every card-three block, and the
assembly multiplier that strong stationarity returns for exactly that family.  Neither
half carries a hypothesis beyond the crux itself. -/
theorem exists_unitTightEigenvectorFamily_and_assemblyMultiplier :
    ∃ (tightVec : Finset (Fin 6) → (Fin 3 → ℝ)) (multiplier : Finset (Fin 6) → ℝ),
      (∀ selected : Finset (Fin 6), selected.card = 3 →
          tightVec selected ⬝ᵥ tightVec selected = 1)
        ∧ (∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
          (chartPointGap (chartPointOfDesign crux.design)).submatrix
              (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
            = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
                (chartPointOfDesign crux.design).weight) :
                (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
        ∧ (∀ atomIndex : Fin 6,
          ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
            multiplier selected * totalEigenSquareRow tightVec selected atomIndex
              = (((6 : ℕ) : ℝ))⁻¹) := by
  obtain ⟨tightVec, hunit, hEigen⟩ :=
    exists_unit_chartBlockEigenvectorFamily (chartPointOfDesign crux.design)
  obtain ⟨multiplier, hassembly⟩ :=
    crux.exists_multiplier_assembly_totalEigenSquareRow tightVec hunit hEigen
  exact ⟨tightVec, multiplier, hunit, hEigen, hassembly⟩

/-- **THE SUPPORT DICHOTOMY.**  At a `(6,3)` counterexample every card-three block's least
eigenvector has support of exactly two or exactly three atoms: at least two because the
chart-gap diagonal is strictly positive while the block value is negative, at most three
because the support lives inside the block.  So the support-two case of the leak calculus
and the full-support hypothesis of the landed index floor are complementary, not merely
related. -/
theorem card_totalTightSupport_eq_two_or_three
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    (totalTightSupport tightVec selected).card = 2 ∨
      (totalTightSupport tightVec selected).card = 3 := by
  have hlower := crux.two_le_card_totalTightSupport tightVec hunit hEigen selected hcard
  have hupper : (totalTightSupport tightVec selected).card ≤ 3 := by
    have hsubset := Finset.card_le_card (totalTightSupport_subset tightVec hcard)
    rw [hcard] at hsubset
    exact hsubset
  omega

end SixThreeCrux

/-! ## The named rungs -/

/-- **A RUNG OF THE INDEX LADDER.**  No `(6,3)` counterexample has exactly `count` active
blocks.  The seventeen instances `count = 4, ..., 20` are the whole residual of this route,
by `Gtz.SixThreeCrux.card_chartArgmaxFamily_mem_indexWindow`.

VACUOUS if `Gtz.GtzWeighted 6 3` holds --- see
`Gtz.forall_isSixThreeActiveCountExcluded_iff_gtzWeighted_six_three`. -/
def IsSixThreeActiveCountExcluded (count : ℕ) : Prop :=
  ∀ crux : SixThreeCrux,
    (chartArgmaxFamily (chartPointOfDesign crux.design)).card ≠ count

/-- Every count below the floor is excluded outright, with no hypothesis.  Together with
the next theorem this pins the residual of the rung family to exactly the seventeen values
`4, ..., 20` and shows the family is not a degenerate predicate. -/
theorem isSixThreeActiveCountExcluded_of_lt_four (count : ℕ) (hcount : count < 4) :
    IsSixThreeActiveCountExcluded count := by
  intro crux hequal
  have hfloor := crux.four_le_card_chartArgmaxFamily_strong
  omega

/-- Every count above the ceiling is excluded outright, with no hypothesis.  This is the
first consequence of the ceiling and it is what makes the ladder terminate. -/
theorem isSixThreeActiveCountExcluded_of_twenty_lt (count : ℕ) (hcount : 20 < count) :
    IsSixThreeActiveCountExcluded count := by
  intro crux hequal
  have hceiling := crux.card_chartArgmaxFamily_le_twenty
  omega

/-- **THE SUPPORT RUNG, AT ACTIVE BLOCKS.**  At every `(6,3)` counterexample, every unit
least eigenvector of every ACTIVE block has all three coordinates nonzero.

WHAT WOULD DISCHARGE IT.  By `Gtz.SixThreeCrux.card_totalTightSupport_eq_two_or_three` the
alternative is a support of exactly two atoms, which is the support-two case of the leak
calculus: a two-supported tight direction whose leak vanishes yields a two-supported kernel
vector of the Gram projection, hence a parallel pair, contradicting
`Gtz.SixThreeCrux.hasNoParallelPair`.  What is NOT covered by that argument is a
two-supported tight direction with NONZERO leak, and that is the whole content of this
rung.

WHAT IS KNOWN.  `Gtz.SixThreeCrux.not_forall_exists_fullSupport_activeEigenvector_of_card_eq_four`
proves the rung FAILS when the active count is exactly four, so the rung is not a theorem
about all chart points --- it is a statement about counterexamples, and it excludes the
count-four case precisely because the two cannot coexist. -/
def IsSixThreeActiveTightSupportFull : Prop :=
  ∀ (crux : SixThreeCrux) (selected : Finset (Fin 6)),
    selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design) →
    ∀ (hcard : selected.card = 3) (vec : Fin 3 → ℝ),
      vec ⬝ᵥ vec = 1 →
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ vec
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • vec →
      ∀ blockIndex : Fin 3, vec blockIndex ≠ 0

/-- **THE SUPPORT RUNG, AT EVERY BLOCK.**  The same statement without the restriction to
active blocks.  Strictly stronger than `Gtz.IsSixThreeActiveTightSupportFull`, and it is
the form the five-to-six step
`Gtz.SixThreeCrux.six_le_card_chartArgmaxFamily_of_assemblyDiagonal_of_ne_five` consumes.
An inactive block's coordinate support is irrelevant to the four-to-five step, which is
why the two are separated. -/
def IsSixThreeTightSupportFull : Prop :=
  ∀ (crux : SixThreeCrux) (selected : Finset (Fin 6)) (hcard : selected.card = 3)
      (vec : Fin 3 → ℝ),
    vec ⬝ᵥ vec = 1 →
    (chartPointGap (chartPointOfDesign crux.design)).submatrix
        (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ vec
      = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
          (chartPointOfDesign crux.design).weight) :
          (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • vec →
    ∀ blockIndex : Fin 3, vec blockIndex ≠ 0

/-- The unrestricted support rung implies the active one. -/
theorem isSixThreeActiveTightSupportFull_of_isSixThreeTightSupportFull
    (hrung : IsSixThreeTightSupportFull) : IsSixThreeActiveTightSupportFull :=
  fun crux selected _ hcard vec hunit hEigen => hrung crux selected hcard vec hunit hEigen

/-- The support rung says exactly that no active block sits at the support-two end of
`Gtz.SixThreeCrux.card_totalTightSupport_eq_two_or_three`. -/
theorem card_totalTightSupport_eq_three_of_isSixThreeActiveTightSupportFull
    (hrung : IsSixThreeActiveTightSupportFull) (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (selected : Finset (Fin 6))
    (hmember : selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design)) :
    (totalTightSupport tightVec selected).card = 3 := by
  have hcard : selected.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
  have hfull : ∀ blockIndex : Fin 3, tightVec selected blockIndex ≠ 0 :=
    hrung crux selected hmember hcard (tightVec selected) (hunit selected hcard)
      (hEigen selected hcard)
  rw [totalTightSupport_eq_self_of_fullSupport tightVec hcard hfull, hcard]

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- **THE RUNG DISCHARGES A STEP OF THE LADDER.**  Granted the support rung, the landed
active-full-support floor fires with its multiplier supplied by strong stationarity, and
the active count of a counterexample is at least five. -/
theorem five_le_card_chartArgmaxFamily_of_isSixThreeActiveTightSupportFull
    (hrung : IsSixThreeActiveTightSupportFull) :
    5 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  obtain ⟨tightVec, multiplier, hunit, hEigen, hassembly⟩ :=
    crux.exists_unitTightEigenvectorFamily_and_assemblyMultiplier
  refine crux.five_le_card_chartArgmaxFamily_of_activeFullSupport tightVec hunit hEigen
    ?_ multiplier hassembly
  intro selected hmember blockIndex
  have hcard : selected.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
  exact hrung crux selected hmember hcard (tightVec selected) (hunit selected hcard)
    (hEigen selected hcard) blockIndex

end SixThreeCrux

/-- **SEVENTEEN BECOME SIXTEEN.**  The support rung closes the count-four case of the
ladder outright. -/
theorem isSixThreeActiveCountExcluded_four_of_isSixThreeActiveTightSupportFull
    (hrung : IsSixThreeActiveTightSupportFull) : IsSixThreeActiveCountExcluded 4 := by
  intro crux hfour
  have hfive := crux.five_le_card_chartArgmaxFamily_of_isSixThreeActiveTightSupportFull hrung
  omega

/-- **THE CONCAVITY RUNG.**  At every `(6,3)` counterexample, and for every unit
least-eigenvector family, the flat directions of the eigen-square rows contain a pair
SEPARATED BY A PIVOT COORDINATE: one direction nonzero there, a second nonzero direction
vanishing there.

WHY THIS SHAPE.  `Gtz.SixThreeCrux.false_of_flatPair_of_activeFullSupport` turns exactly
that configuration into a contradiction, so the rung is the last missing input of the
second-order argument and not a reformulation of it.

WHAT IS KNOWN.  A single flat direction is free whenever the active count falls two short
of six, by `Gtz.exists_flatDirection_of_card_add_one_lt`; the rigidity certificate
`Gtz.eq_zero_of_flatDirection_of_span_top` says there is none at all once the eigen-square
rows span, which is the measured behaviour at every landed tie.  So the rung is a genuine
statement about the crux stratum and is FALSE off it --- it must not be tested against a
tie. -/
def IsSixThreeFlatPairSeparated : Prop :=
  ∀ (crux : SixThreeCrux) (tightVec : Finset (Fin 6) → (Fin 3 → ℝ)),
    (∀ selected : Finset (Fin 6), selected.card = 3 →
        tightVec selected ⬝ᵥ tightVec selected = 1) →
    (∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        (chartPointGap (chartPointOfDesign crux.design)).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
          = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected) →
    ∃ (first second : Fin 6 → ℝ) (pivot : Fin 6),
      first ∈ flatSumZeroSubmodule (chartArgmaxFamily (chartPointOfDesign crux.design))
          (totalEigenSquareRow tightVec) ∧
        second ∈ flatSumZeroSubmodule (chartArgmaxFamily (chartPointOfDesign crux.design))
          (totalEigenSquareRow tightVec) ∧
        second ≠ 0 ∧ first pivot ≠ 0 ∧ second pivot = 0

/-- **THE SECOND ROUTE, ASSEMBLED.**  Support at the active blocks plus a separated flat
pair contradict each other at a counterexample, with no case analysis on the active count
anywhere in the argument. -/
theorem false_of_sixThreeCrux_of_isSixThreeActiveTightSupportFull_of_flatPairSeparated
    (hsupport : IsSixThreeActiveTightSupportFull) (hflat : IsSixThreeFlatPairSeparated)
    (crux : SixThreeCrux) : False := by
  obtain ⟨tightVec, multiplier, hunit, hEigen, hassembly⟩ :=
    crux.exists_unitTightEigenvectorFamily_and_assemblyMultiplier
  obtain ⟨first, second, pivot, hfirstMem, hsecondMem, hsecondNe, hpivotFirst,
    hpivotSecond⟩ := hflat crux tightVec hunit hEigen
  refine crux.false_of_flatPair_of_activeFullSupport tightVec hunit hEigen ?_ hfirstMem
    hsecondMem hsecondNe hpivotFirst hpivotSecond
  intro selected hmember blockIndex
  have hcard : selected.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
  exact hsupport crux selected hmember hcard (tightVec selected) (hunit selected hcard)
    (hEigen selected hcard) blockIndex

/-! ## The capstone -/

/-- Excluding every admissible active count leaves a counterexample with nowhere to sit. -/
theorem false_of_sixThreeCrux_of_forall_isSixThreeActiveCountExcluded
    (hladder : ∀ count : ℕ, 4 ≤ count → count ≤ 20 → IsSixThreeActiveCountExcluded count)
    (crux : SixThreeCrux) : False := by
  obtain ⟨hfloor, hceiling⟩ := crux.card_chartArgmaxFamily_mem_indexWindow
  exact hladder (chartArgmaxFamily (chartPointOfDesign crux.design)).card hfloor hceiling
    crux rfl

/-- **THE SPINE.**  The seventeen rungs `4, ..., 20` prove the cell.  Every one of them is
a statement about `Gtz.SixThreeCrux` alone, so a later argument discharges a named
hypothesis of this theorem rather than inventing a statement. -/
theorem gtzWeighted_six_three_of_forall_isSixThreeActiveCountExcluded
    (hladder : ∀ count : ℕ, 4 ≤ count → count ≤ 20 → IsSixThreeActiveCountExcluded count) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_isEmpty_sixThreeCrux
    ⟨false_of_sixThreeCrux_of_forall_isSixThreeActiveCountExcluded hladder⟩

/-- **THE DECOMPOSITION IS LOSSLESS, AND THEREFORE BUYS NOTHING BY ITSELF.**  The
conjunction of the seventeen rungs is EQUIVALENT to the cell, so no rung can be easier than
the cell in the aggregate, and each individual rung is vacuous once the cell is proved.
What the split buys is a finite, named residual: sixteen open cases after the support rung,
against one unnamed one before. -/
theorem forall_isSixThreeActiveCountExcluded_iff_gtzWeighted_six_three :
    (∀ count : ℕ, 4 ≤ count → count ≤ 20 → IsSixThreeActiveCountExcluded count)
      ↔ GtzWeighted 6 3 := by
  constructor
  · exact gtzWeighted_six_three_of_forall_isSixThreeActiveCountExcluded
  · intro hcell count _ _ crux
    exact absurd hcell (not_gtzWeighted_six_three_of_sixThreeCrux crux)

/-- The unrestricted form of the equivalence: the rung family is exactly the cell, and the
counts outside `[4, 20]` contribute nothing because they are theorems already. -/
theorem forall_isSixThreeActiveCountExcluded_unrestricted_iff_gtzWeighted_six_three :
    (∀ count : ℕ, IsSixThreeActiveCountExcluded count) ↔ GtzWeighted 6 3 := by
  rw [← forall_isSixThreeActiveCountExcluded_iff_gtzWeighted_six_three]
  exact ⟨fun hall count _ _ => hall count, fun hwindow count => by
    rcases Nat.lt_or_ge count 4 with hsmall | hfloor
    · exact isSixThreeActiveCountExcluded_of_lt_four count hsmall
    · rcases Nat.lt_or_ge 20 count with hbig | hceiling
      · exact isSixThreeActiveCountExcluded_of_twenty_lt count hbig
      · exact hwindow count hfloor hceiling⟩

/-- **THE SPINE WITH THE FIRST RUNG DISCHARGED.**  Sixteen cases, `5, ..., 20`, and the
support rung. -/
theorem gtzWeighted_six_three_of_isSixThreeActiveTightSupportFull_of_forall_excluded
    (hsupport : IsSixThreeActiveTightSupportFull)
    (hladder : ∀ count : ℕ, 5 ≤ count → count ≤ 20 → IsSixThreeActiveCountExcluded count) :
    GtzWeighted 6 3 := by
  refine gtzWeighted_six_three_of_forall_isSixThreeActiveCountExcluded ?_
  intro count hfloor hceiling
  rcases Nat.eq_or_lt_of_le hfloor with hfour | hfive
  · exact hfour ▸ isSixThreeActiveCountExcluded_four_of_isSixThreeActiveTightSupportFull
      hsupport
  · exact hladder count hfive hceiling

/-- **THE SECOND ROUTE, AS A CLOSURE OF THE CELL.**  Two named rungs, no case analysis. -/
theorem gtzWeighted_six_three_of_isSixThreeActiveTightSupportFull_of_flatPairSeparated
    (hsupport : IsSixThreeActiveTightSupportFull) (hflat : IsSixThreeFlatPairSeparated) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_isEmpty_sixThreeCrux
    ⟨false_of_sixThreeCrux_of_isSixThreeActiveTightSupportFull_of_flatPairSeparated hsupport
      hflat⟩

/-- **THE RANK-THREE PAYOFF.**  The ladder closes rank three at every size, through the
landed `Gtz.gtzWeightedAll_three_of_six_three`. -/
theorem gtzWeightedAll_three_of_forall_isSixThreeActiveCountExcluded
    (hladder : ∀ count : ℕ, 4 ≤ count → count ≤ 20 → IsSixThreeActiveCountExcluded count) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_forall_isSixThreeActiveCountExcluded hladder)

/-! ## Both routes are lossless, and the file says so about both -/

/-- **EVERY RUNG OF THE SPINE HOLDS IF NO COUNTEREXAMPLE EXISTS.**  All four of the
Props above are `∀ crux : SixThreeCrux, ...`, so an empty crux type inhabits every one
of them at once, for one reason.  This is what makes the satisfiability question for the
whole spine a single question, and its answer is "decided up to the cell and not
further": a crux-quantified Prop cannot be shown inhabited by any means short of
settling `Gtz.GtzWeighted 6 3`, and cannot be shown empty without exhibiting a
counterexample. -/
theorem spineRungsHold_of_isEmpty_sixThreeCrux (hempty : IsEmpty SixThreeCrux) :
    (∀ count : ℕ, IsSixThreeActiveCountExcluded count)
      ∧ IsSixThreeActiveTightSupportFull
      ∧ IsSixThreeTightSupportFull
      ∧ IsSixThreeFlatPairSeparated :=
  ⟨fun _ crux => (hempty.false crux).elim,
   fun crux => (hempty.false crux).elim,
   fun crux => (hempty.false crux).elim,
   fun crux => (hempty.false crux).elim⟩

/-- **THE TWO-RUNG ROUTE IS AN EQUIVALENCE TOO.**  The seventeen-rung decomposition is
stated above as an `iff` with the cell, and the reader is warned there that it therefore
buys no mathematics.  ** THE SHORTER ROUTE DESERVES THE SAME WARNING AND THIS IS IT. **
The two named rungs of
`Gtz.gtzWeighted_six_three_of_isSixThreeActiveTightSupportFull_of_flatPairSeparated`
are jointly EQUIVALENT to `Gtz.GtzWeighted 6 3`, so that route asserts neither more nor
less than the target either.  Both routes are lossless reformulations; what they buy is
a finite named residual in place of an unnamed one, and nothing else. -/
theorem isSixThreeActiveTightSupportFull_and_flatPairSeparated_iff_gtzWeighted_six_three :
    (IsSixThreeActiveTightSupportFull ∧ IsSixThreeFlatPairSeparated)
      ↔ GtzWeighted 6 3 := by
  constructor
  · rintro ⟨hsupport, hflat⟩
    exact gtzWeighted_six_three_of_isSixThreeActiveTightSupportFull_of_flatPairSeparated
      hsupport hflat
  · intro hcell
    have hempty : IsEmpty SixThreeCrux :=
      not_nonempty_iff.mp fun hnonempty =>
        (nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three.mp hnonempty) hcell
    obtain ⟨_, hsupport, _, hflat⟩ := spineRungsHold_of_isEmpty_sixThreeCrux hempty
    exact ⟨hsupport, hflat⟩

end Gtz

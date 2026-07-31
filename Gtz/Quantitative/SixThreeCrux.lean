/-
# The `(6,3)` counterexample normal form

A failure of `Gtz.GtzWeighted 6 3` is not merely realised at *some* design.  It is
realised at a design carrying eight simultaneous structural constraints, every one of
them a theorem of this repository with NO open hypothesis.  This file bundles them into
one structure and proves the bundle EQUIVALENT to the failure, so the crux cell has a
normal form rather than a description.

`(6,3)` and not `(7,3)`: at `(6,3)` both smaller rungs are the shipped
`Gtz.gtzWeighted_of_le_five`, a light atom deflates onto `(5,3)`, a parallel pair merges
onto `(5,3)`, and the Naimark dual of a `(6,3)` design is again `(6,3)` so the dual
deflation lands on `(5,3)`.  Corank two closes all three.  At `(7,3)` the same three
routes land on `(6,3)`, `(6,3)` and `(6,4)` respectively — two of them open — which is
why the `(7,3)` analogue in the last section carries `Gtz.GtzWeighted 6 3` explicitly.

## The carrier is the DESIGN, and the bundle is derived on its CHART POINT

The choice matters and is not free.  `Gtz.Reduction.CompactnessReduction`'s "THE
OBJECTIVE MISMATCH" note records that the design-side margin and the chart objective do
NOT share their minimisers, because the congruence `diagonal (sqrt t_C)` rescales
non-uniformly.  So a first-order bundle derived from minimality of one objective is not
available at a minimiser of the other, and `Gtz.exists_collared_allHeavy_minimiser_sevenThree`
(design margin, weight-floored class, no first-order data) must not be confused with
`Gtz.exists_allHeavy_minimiser_sixThree` (chart objective, closed chart domain).

This file takes the CHART side.  The field `isChartMinimiser` says that
`Gtz.chartPointOfDesign design` minimises `Gtz.chartObjective` globally, which is exactly
the hypothesis `Gtz.isChartStrongStationaryData_of_isMin_of_weightPos` consumes.  The
whole first-order layer is therefore DERIVED here, never assumed: it appears as theorems
in the `SixThreeCrux` namespace and NOT as fields.  Nothing in the structure is a
first-order hypothesis in disguise.

Strict weight positivity is likewise not a field: it is `WeightedDesign.weight_pos`,
free from the carrier.  That is the whole reason the carrier is a design and not a bare
chart point — `Gtz.chartPointHasDesign` was already spent, upstream, to convert the
strictly interior minimiser into one.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `SixThreeCrux` — eight fields: the design, global chart minimality, strictly negative
  chart value, no dominating triple, all-heaviness, strictly dominating co-singletons,
  no parallel pair, and avoidance of the equal-share stratum.
* `nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three` — **the normal form.**  The
  structure is inhabited if and only if `Gtz.GtzWeighted 6 3` fails.  UNCONDITIONAL in
  both directions; nothing is assumed on either side.
* The derived layer, all in the `SixThreeCrux` namespace and all free:
  `isChartStrongStationaryData`, `isChartArgmaxValue`,
  `exists_multiplier_isChartStationaryData`, `isChartTightCovering`, `chartArgmaxFamily_nonempty` — the first-order system;
  `hasNoAtMostFiveLines`, `deflationLevel_lt_one`, `neg_inv_six_le_chartObjective`,
  `exists_dominates_at_three_fifths`, `exists_naimarkDual_allHeavy_not_dominating` — the
  quantitative and dual readings.
* The chart-side coverage combinatorics, stated at general `(size, rank)` and cashed at
  `(6,3)`: `exists_mem_chartArgmaxFamily_of_isMin`,
  `size_le_rank_mul_card_chartArgmaxFamily_of_isMin`,
  `two_le_card_chartArgmaxFamily_sixThree_of_isMin`, and the two-block classification
  `disjoint_partition_of_card_chartArgmaxFamily_eq_two_sixThree`.
* `SevenThreeCrux` and `nonempty_sevenThreeCrux_of_not_gtzWeighted_seven_three` — the
  `(7,3)` analogue, whose production theorem CARRIES `Gtz.GtzWeighted 6 3`.  The
  structure has SEVEN fields, one fewer than the `(6,3)` one; see the honesty section.
* `gtzWeightedAll_three_of_isEmpty_cruxes` — emptying both structures proves rank-three
  GTZ at every size, so the normal form is a complete reformulation and not a filter.

## NOT PROVED here, and named

**THE DISJOINT TWO-BLOCK BRANCH IS OPEN ON THE CHART SIDE.**  The coverage
combinatorics above stops at: the argmax family of the crux has at least TWO members,
and if it has exactly two they are disjoint triples partitioning the six atoms.  The
third step — killing that partition — is shipped, but on the OTHER side of the campaign:
`Gtz.three_le_card_activeSubsetImage_sixThree`
(`Gtz/Quantitative/IsolatedBlockExclusion.lean`) proves it, via
`Gtz.rank_le_value_of_disjointPair_activeSubsetImage`, from
`Gtz.IsQuadricStationaryData`.  That datum is NOT reachable from a crux.  Every
inhabitant of `Gtz.IsQuadricStationaryData` in this repository is a named concrete
witness; no theorem produces one from minimality, and the only chart-to-quadric bridge,
`Gtz/Quantitative/ChartMultiplierSplit.lean`, holds at chart value ZERO, whereas a crux
has `hasNegativeChartValue`.  So the classification here genuinely stops one step short
of the quadric-side one, and closing the gap needs either a chart-side
isolated-block theorem (the repository has none — no chart file mentions isolation
or disjointness) or a bridge valid off the extremal locus.  Neither is attempted here.

**NO EQUAL-SHARE FIELD AT `(7,3)`.**  `avoidsEqualShareStratum` rests on
`Gtz.gtzWeighted_six_three_of_isEqualShare`, which is unconditional at `(6,3)`.  The
`(7,3)` equal-share stratum is NOT closed: `Gtz.exists_isCompatibleTriangle_of_isEqualShare_sevenThree`
discharges only the EDGE half of `Gtz.dominates_triple_iff_isElliptopeGoodTriangle`
there, and the cubic tie leg is untouched.  The field is therefore absent from
`SevenThreeCrux` rather than assumed into it.

**THIS PROVES NOTHING ABOUT THE TARGET.**  A normal form is a reformulation.
`nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three` is an equivalence, so it can no
more decide `Gtz.GtzWeighted 6 3` than the cell can decide itself.  What it buys is that
an attack may now assume all eight constraints at once without re-deriving any of them.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.EqualShareSixThree
import Gtz.Reduction.AllHeavyMinimiser
import Gtz.Reduction.ChartAttainmentWeld
import Gtz.Reduction.LineCountReduction
import Gtz.Reduction.NaimarkLeverage

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Coverage of the argmax family, on the chart side

Everything in this section is derived from interiority plus global minimality alone, by
routing the shipped weak-bundle consequences through
`Gtz.isChartStrongStationaryData_of_isMin_of_weightPos`.  On the chart side the active
subsets ARE the argmax blocks (`activeSubset = id`), so the family is its own image and
the counting bounds land directly on the number of distinct argmax blocks — one
projection sharper than the quadric-side statements, which must take an image first. -/

/-- **COVERAGE.**  At a strictly interior global minimiser of the chart objective, every
atom lies in some argmax block.  The chart-side reading of the first clause of the
campaign's coverage combinatorics. -/
theorem exists_mem_chartArgmaxFamily_of_isMin [Nonempty (Fin rank)]
    (minimiser : ChartPoint size rank)
    (hweightPos : ∀ atomIndex : Fin size, 0 < minimiser.weight atomIndex)
    (hmin : ∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point)
    (atomIndex : Fin size) :
    ∃ block ∈ chartArgmaxFamily minimiser, atomIndex ∈ block :=
  exists_mem_activeSubset_of_isChartStrongStationaryData
    (isChartStrongStationaryData_of_isMin_of_weightPos minimiser hweightPos hmin) atomIndex

/-- **THE COUNTING BOUND.**  Coverage plus "every argmax block has exactly `rank` atoms"
gives `size ≤ rank * (number of argmax blocks)`.  The chart-side twin of
`Gtz.size_le_rank_mul_card_activeSubsetImage`, and free of any `value ≠ 0` hypothesis. -/
theorem size_le_rank_mul_card_chartArgmaxFamily_of_isMin [Nonempty (Fin rank)]
    (minimiser : ChartPoint size rank)
    (hweightPos : ∀ atomIndex : Fin size, 0 < minimiser.weight atomIndex)
    (hmin : ∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point) :
    size ≤ rank * (chartArgmaxFamily minimiser).card := by
  obtain ⟨multiplier, selection, hweak⟩ :=
    exists_isChartStationaryData_of_isChartStrongStationaryData
      (isChartStrongStationaryData_of_isMin_of_weightPos minimiser hweightPos hmin)
  exact size_le_rank_mul_card_activeSet_of_isChartStationaryData hweak

/-- **AT `(6,3)`: AT LEAST TWO ARGMAX TRIPLES.**  Six atoms covered by triples cannot use
fewer than two of them.  This is the honest chart-side floor; the quadric-side
`Gtz.three_le_card_activeSubsetImage_sixThree` reaches three, but from a datum a crux
does not carry — see this file's header. -/
theorem two_le_card_chartArgmaxFamily_sixThree_of_isMin (minimiser : ChartPoint 6 3)
    (hweightPos : ∀ atomIndex : Fin 6, 0 < minimiser.weight atomIndex)
    (hmin : ∀ point : ChartPoint 6 3, chartObjective minimiser ≤ chartObjective point) :
    2 ≤ (chartArgmaxFamily minimiser).card := by
  have hbound := size_le_rank_mul_card_chartArgmaxFamily_of_isMin minimiser hweightPos hmin
  omega

/-- **THE TWO-BLOCK CASE IS A PARTITION.**  If the argmax family of a `(6,3)` interior
minimiser has exactly two members, they are disjoint triples whose union is everything.
Pure counting from coverage: two blocks of three covering six atoms leave no room to
overlap.

This is the exact shape the quadric-side `Gtz.rank_le_value_of_disjointPair_activeSubsetImage`
excludes, and the point at which the chart-side classification stops. -/
theorem disjoint_partition_of_card_chartArgmaxFamily_eq_two_sixThree
    (minimiser : ChartPoint 6 3)
    (hweightPos : ∀ atomIndex : Fin 6, 0 < minimiser.weight atomIndex)
    (hmin : ∀ point : ChartPoint 6 3, chartObjective minimiser ≤ chartObjective point)
    (hcard : (chartArgmaxFamily minimiser).card = 2) :
    ∃ firstBlock secondBlock : Finset (Fin 6),
      chartArgmaxFamily minimiser = {firstBlock, secondBlock}
        ∧ firstBlock.card = 3 ∧ secondBlock.card = 3
        ∧ Disjoint firstBlock secondBlock
        ∧ firstBlock ∪ secondBlock = Finset.univ := by
  classical
  obtain ⟨firstBlock, secondBlock, -, hpair⟩ := Finset.card_eq_two.mp hcard
  have hfirstMem : firstBlock ∈ chartArgmaxFamily minimiser := by
    rw [hpair]; exact Finset.mem_insert_self _ _
  have hsecondMem : secondBlock ∈ chartArgmaxFamily minimiser := by
    rw [hpair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hfirstCard : firstBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff minimiser firstBlock).mp hfirstMem).1
  have hsecondCard : secondBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff minimiser secondBlock).mp hsecondMem).1
  have hcovered : (Finset.univ : Finset (Fin 6)) ⊆ firstBlock ∪ secondBlock := by
    intro atomIndex _
    obtain ⟨block, hblockMem, hatomMem⟩ :=
      exists_mem_chartArgmaxFamily_of_isMin minimiser hweightPos hmin atomIndex
    rw [hpair] at hblockMem
    rcases Finset.mem_insert.mp hblockMem with hfirst | hsecond
    · exact Finset.mem_union_left _ (hfirst ▸ hatomMem)
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mp hsecond ▸ hatomMem)
  have hunion : firstBlock ∪ secondBlock = Finset.univ :=
    Finset.Subset.antisymm (Finset.subset_univ _) hcovered
  have hunionCard : (firstBlock ∪ secondBlock).card = 6 := by
    rw [hunion, Finset.card_univ, Fintype.card_fin]
  have hdisjoint : Disjoint firstBlock secondBlock := by
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
    have hinclusionExclusion := Finset.card_union_add_card_inter firstBlock secondBlock
    omega
  exact ⟨firstBlock, secondBlock, hpair, hfirstCard, hsecondCard, hdisjoint, hunion⟩

/-! ## The normal form -/

/-- **THE `(6,3)` COUNTEREXAMPLE NORMAL FORM.**  Eight simultaneous constraints on a
single weighted design, each of them forced at a failure of `Gtz.GtzWeighted 6 3` with no
open hypothesis, and jointly equivalent to that failure
(`nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three`).

Read the field list as the answer to "what must a `(6,3)` counterexample look like".
Every field is PRIMITIVE data or a constraint that cannot be recovered from the others;
the entire first-order layer is absent from this list precisely because it IS recoverable,
and appears as theorems in the `SixThreeCrux` namespace below. -/
structure SixThreeCrux where
  /-- The counterexample itself. -/
  design : WeightedDesign 6 3
  /-- Its chart point globally minimises the chart objective over the CLOSED chart
  domain.  This is the field the whole first-order layer is derived from. -/
  isChartMinimiser : ∀ point : ChartPoint 6 3,
    chartObjective (chartPointOfDesign design) ≤ chartObjective point
  /-- And at a strictly negative value, so no triple even comes close. -/
  hasNegativeChartValue : chartObjective (chartPointOfDesign design) < 0
  /-- No triple dominates — the failure itself. -/
  hasNoDominatingTriple : ∀ selected : Finset (Fin 6), selected.card = 3 →
    ¬ Dominates design selected
  /-- Every leverage is STRICTLY above one.  Free at a counterexample: a light atom
  deflates onto `(5,3)`, which is corank two. -/
  isAllHeavy : AllHeavy design
  /-- Deleting any single atom leaves the unweighted sum STRICTLY above the identity.
  Free at a counterexample by the Naimark dual, which at `(6,3)` is again `(6,3)`, so the
  dual deflation lands on `(5,3)`. -/
  hasStrictlyDominatingCoSingletons : HasStrictlyDominatingCoSingletons design
  /-- No two atoms are parallel.  Free at a counterexample: a parallel pair merges onto
  `(5,3)`.  Strictly stronger than failing `Gtz.HasAtMostLines design 5`, which is
  derived below. -/
  hasNoParallelPair : ¬ HasParallelPair design
  /-- The design is not the equal-share point — uniform weights together with isotropic
  leverage.  Free at a counterexample by `Gtz.gtzWeighted_six_three_of_isEqualShare`. -/
  avoidsEqualShareStratum : ¬ IsEqualShare design

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- Strict interiority, free from the carrier: a `Gtz.WeightedDesign` has positive
weights by construction.  This is what `Gtz.chartPointHasDesign` was spent on upstream,
and it is the hypothesis every theorem below shares. -/
theorem weight_pos (atomIndex : Fin 6) :
    0 < (chartPointOfDesign crux.design).weight atomIndex :=
  crux.design.weight_pos atomIndex

/-! ### The first-order layer, DERIVED -/

/-- **THE STRONG STATIONARITY BUNDLE, DERIVED.**  Not a field: interiority plus global
minimality already give the whole strong first-order system at the argmax family, by
`Gtz.isChartStrongStationaryData_of_isMin_of_weightPos`, whose spectral leg discharges
the tight-direction obligation. -/
theorem isChartStrongStationaryData :
    IsChartStrongStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) :=
  isChartStrongStationaryData_of_isMin_of_weightPos _ crux.weight_pos crux.isChartMinimiser

/-- **THE ARGMAX FIELD, DERIVED.**  Every triple admits a supported unit probe at or
below the value — the admissibility hypothesis the exclusions of
`Gtz.Quantitative.ChartStationary` and its successors consume alongside the bundle. -/
theorem isChartArgmaxValue :
    IsChartArgmaxValue 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) :=
  (exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin _ crux.weight_pos
    crux.isChartMinimiser).2

/-- The weak bundle, with its multiplier and selection, for consumers stated against
`Gtz.IsChartStationaryData` rather than the strong form. -/
theorem exists_multiplier_isChartStationaryData :
    ∃ (multiplier : Finset (Fin 6) → ℝ) (selection : Finset (Fin 6) → (Fin 6 → ℝ)),
      IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design))
        (chartArgmaxFamily (chartPointOfDesign crux.design))
        (id : Finset (Fin 6) → Finset (Fin 6)) multiplier selection :=
  (exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin _ crux.weight_pos
    crux.isChartMinimiser).1

/-- The first-order covering condition at the argmax family. -/
theorem isChartTightCovering :
    IsChartTightCovering (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) :=
  isChartTightCovering_of_isMin _ crux.weight_pos crux.isChartMinimiser

/-- The argmax family is nonempty, so none of the above is a statement about an empty
family. -/
theorem chartArgmaxFamily_nonempty :
    (chartArgmaxFamily (chartPointOfDesign crux.design)).Nonempty :=
  Gtz.chartArgmaxFamily_nonempty _

/-! ### The coverage combinatorics at the crux -/

/-- Every atom of a crux lies in some argmax triple. -/
theorem exists_mem_chartArgmaxFamily (atomIndex : Fin 6) :
    ∃ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design), atomIndex ∈ block :=
  exists_mem_chartArgmaxFamily_of_isMin _ crux.weight_pos crux.isChartMinimiser atomIndex

/-- A crux carries at least two distinct argmax triples. -/
theorem two_le_card_chartArgmaxFamily :
    2 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card :=
  two_le_card_chartArgmaxFamily_sixThree_of_isMin _ crux.weight_pos crux.isChartMinimiser

/-- **THE CLASSIFICATION, AND WHERE IT STOPS.**  A crux either carries three or more
distinct argmax triples, or exactly two, and then they are disjoint and partition the six
atoms.  The second branch is what
`Gtz.rank_le_value_of_disjointPair_activeSubsetImage` excludes on the quadric side; this
file's header records why that exclusion is not reachable from chart data, so the
disjunction is left standing rather than collapsed. -/
theorem three_le_card_chartArgmaxFamily_or_disjoint_partition :
    3 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card
      ∨ ∃ firstBlock secondBlock : Finset (Fin 6),
          chartArgmaxFamily (chartPointOfDesign crux.design) = {firstBlock, secondBlock}
            ∧ firstBlock.card = 3 ∧ secondBlock.card = 3
            ∧ Disjoint firstBlock secondBlock
            ∧ firstBlock ∪ secondBlock = Finset.univ := by
  rcases Nat.lt_or_ge (chartArgmaxFamily (chartPointOfDesign crux.design)).card 3 with
    hsmall | hlarge
  · refine Or.inr (disjoint_partition_of_card_chartArgmaxFamily_eq_two_sixThree _
      crux.weight_pos crux.isChartMinimiser ?_)
    have htwo := crux.two_le_card_chartArgmaxFamily
    omega
  · exact Or.inl hlarge

/-! ### The quantitative and dual readings -/

/-- The chart value is pinned into a bounded window: strictly negative by the field, and
at least `-1/6` by the one-sided bound the strong bundle carries. -/
theorem neg_inv_six_le_chartObjective :
    -(1 / (6 : ℝ)) ≤ chartObjective (chartPointOfDesign crux.design) := by
  simpa using neg_inv_size_le_value_of_isChartStrongStationaryData crux.isChartStrongStationaryData

/-- Five lines are already too few.  Weaker than `hasNoParallelPair`: six atoms on five
lines force a parallel pair by pigeonhole, so the field implies this and not conversely. -/
theorem hasNoAtMostFiveLines : ¬ HasAtMostLines crux.design 5 := by
  rintro ⟨lineOf, hparallelOnLine⟩
  have hnotInjective : ¬ Function.Injective lineOf := by
    intro hinjective
    have hcard := Fintype.card_le_of_injective lineOf hinjective
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨keptLabel, dropLabel, hsameLine, hdistinct⟩ :=
    Function.not_injective_iff.mp hnotInjective
  obtain ⟨ratio, hparallel⟩ := hparallelOnLine keptLabel dropLabel hsameLine
  exact crux.hasNoParallelPair ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩

/-- **THE DEFLATION LANE IS SPENT AT A CRUX.**  Every deflation level is strictly below
one, so no choice of pivot inside the light-atom transport closes the remaining gap. -/
theorem deflationLevel_lt_one (atomIndex : Fin 6) :
    deflationLevel crux.design atomIndex < 1 :=
  deflationLevel_lt_one_of_allHeavy (m := 5) crux.design (by norm_num) crux.isAllHeavy atomIndex

/-- **THE QUANTITATIVE SQUEEZE.**  A crux dominates at level `3/5` — unconditionally, by
the universal share floor — and fails at level `1` by its own field.  The gap between
those two numbers is exactly what `Gtz.GtzWeighted 6 3` asks to close. -/
theorem exists_dominates_at_three_fifths :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum crux.design selected - ((3 : ℝ) / 5) • 1).PosSemidef :=
  gtzWeightedFloor_six_three_three_fifths crux.design

/-- **THE DUAL IS A COUNTEREXAMPLE TOO.**  `(6,3)` is its own Naimark dual, and at a crux
the dual is all-heavy (that is what `hasStrictlyDominatingCoSingletons` says) and has no
dominating triple either, because domination flips across complements and a complement of
a triple in six atoms is a triple.  So the crux locus is closed under Naimark duality:
whatever kills a crux must survive that involution.  The dual carries the crux's own
weights, so the involution fixes the weight vector and moves only the atoms. -/
theorem exists_naimarkDual_allHeavy_not_dominating :
    ∃ dual : WeightedDesign 6 3,
      (∀ atomIndex : Fin 6, dual.weight atomIndex = crux.design.weight atomIndex)
      ∧ AllHeavy dual
      ∧ ∀ selected : Finset (Fin 6), selected.card = 3 → ¬ Dominates dual selected := by
  obtain ⟨dual, hweights, hdictionary, hflip⟩ :=
    exists_naimarkDual_allHeavy_iff (m := 6) (k := 3) (by norm_num) (by norm_num) crux.design
  refine ⟨dual, hweights, hdictionary.mpr crux.hasStrictlyDominatingCoSingletons,
    fun selected hcard hdominates => ?_⟩
  have hcompCard : (selectedᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  exact crux.hasNoDominatingTriple selectedᶜ hcompCard
    ((hflip selectedᶜ hcompCard).mpr (by rwa [compl_compl]))

end SixThreeCrux

/-! ## The normal form is exactly the failure -/

/-- One direction, immediate: a crux refutes the cell. -/
theorem not_gtzWeighted_six_three_of_sixThreeCrux (crux : SixThreeCrux) :
    ¬ GtzWeighted 6 3 := by
  intro hgtz
  obtain ⟨selected, hcard, hdominates⟩ := hgtz crux.design
  exact crux.hasNoDominatingTriple selected hcard hdominates

/-- **THE ASSEMBLY.**  A failure of `Gtz.GtzWeighted 6 3` is realised at a crux — all
eight constraints at once, with NO open hypothesis anywhere.

Five shipped results compose and nothing else is used.
`Gtz.exists_allHeavy_minimiser_sixThree` supplies the design, its all-heaviness, its
minimality and the negative value; `Gtz.dominating_of_coSingleton_not_posDef_sixThree`
supplies the co-singleton condition through the dual deflation onto `(5,3)`;
`Gtz.dominating_of_parallel_pair` against `Gtz.gtzWeighted_of_le_five` supplies
primitivity through the merge onto `(5,3)`; and
`Gtz.gtzWeighted_six_three_of_isEqualShare` supplies the equal-share avoidance.  Each of
the last three is a contrapositive: the constraint holds because its failure would
already produce the dominating triple the design does not have. -/
theorem nonempty_sixThreeCrux_of_not_gtzWeighted_six_three (hfail : ¬ GtzWeighted 6 3) :
    Nonempty SixThreeCrux := by
  obtain ⟨design, hheavy, hnotDominates, hmin, hnegative⟩ :=
    exists_allHeavy_minimiser_sixThree hfail
  refine ⟨⟨design, hmin, hnegative, hnotDominates, hheavy, ?_, ?_, ?_⟩⟩
  · intro atomIndex
    by_contra hnotPosDef
    obtain ⟨selected, hcard, hdominates⟩ :=
      dominating_of_coSingleton_not_posDef_sixThree design atomIndex hnotPosDef
    exact hnotDominates selected hcard hdominates
  · rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
    obtain ⟨selected, hcard, hdominates⟩ :=
      dominating_of_parallel_pair (m := 5) design
        (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) hdistinct hparallel
    exact hnotDominates selected hcard hdominates
  · intro hequal
    obtain ⟨selected, hcard, hdominates⟩ := gtzWeighted_six_three_of_isEqualShare design hequal
    exact hnotDominates selected hcard hdominates

/-- **THE NORMAL FORM.**  The crux structure is inhabited if and only if the crux cell
fails.  Unconditional in both directions.

This is a reformulation and not a step toward a proof — see the header.  Its use is that
an attack on `Gtz.GtzWeighted 6 3` may now assume all eight constraints, plus the whole
derived first-order layer, without re-deriving any of them, and may equally prove the
cell by showing the structure UNINHABITED. -/
theorem nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three :
    Nonempty SixThreeCrux ↔ ¬ GtzWeighted 6 3 :=
  ⟨fun ⟨crux⟩ => not_gtzWeighted_six_three_of_sixThreeCrux crux,
    nonempty_sixThreeCrux_of_not_gtzWeighted_six_three⟩

/-- The contrapositive reading, which is the one a prover would target.  Emptying
the structure IS the cell. -/
theorem gtzWeighted_six_three_of_isEmpty_sixThreeCrux (hempty : IsEmpty SixThreeCrux) :
    GtzWeighted 6 3 :=
  not_not.mp fun hfail =>
    hempty.elim (nonempty_sixThreeCrux_of_not_gtzWeighted_six_three hfail).some

/-! ## The `(7,3)` analogue — CONDITIONAL

The structure below is unconditional as a bundle of properties, and
`not_gtzWeighted_seven_three_of_sevenThreeCrux` is unconditional.  What carries
`Gtz.GtzWeighted 6 3` is the PRODUCTION theorem, and it does so irreducibly: at `(7,3)`
the light-atom deflation and the parallel merge both land on `(6,3)`.  Only the
co-singleton route is free there, because the Naimark dual of a `(7,3)` design is
`(7,4)`, whose deflation lands on `(6,4)` — corank two.

The equal-share field is ABSENT, not assumed; see the header. -/

/-- **THE `(7,3)` COUNTEREXAMPLE NORMAL FORM**, seven fields.  Same shape as
`SixThreeCrux` minus `avoidsEqualShareStratum`, which has no `(7,3)` source. -/
structure SevenThreeCrux where
  /-- The counterexample itself. -/
  design : WeightedDesign 7 3
  /-- Its chart point globally minimises the chart objective. -/
  isChartMinimiser : ∀ point : ChartPoint 7 3,
    chartObjective (chartPointOfDesign design) ≤ chartObjective point
  /-- At a strictly negative value. -/
  hasNegativeChartValue : chartObjective (chartPointOfDesign design) < 0
  /-- No triple dominates. -/
  hasNoDominatingTriple : ∀ selected : Finset (Fin 7), selected.card = 3 →
    ¬ Dominates design selected
  /-- Every leverage strictly above one. -/
  isAllHeavy : AllHeavy design
  /-- Every co-singleton strictly dominates.  This one is free even at `(7,3)`: the dual
  deflation lands on `(6,4)`, which is corank two. -/
  hasStrictlyDominatingCoSingletons : HasStrictlyDominatingCoSingletons design
  /-- No two atoms are parallel. -/
  hasNoParallelPair : ¬ HasParallelPair design

namespace SevenThreeCrux

variable (crux : SevenThreeCrux)

/-- Strict interiority, free from the carrier. -/
theorem weight_pos (atomIndex : Fin 7) :
    0 < (chartPointOfDesign crux.design).weight atomIndex :=
  crux.design.weight_pos atomIndex

/-- The strong stationarity bundle, derived exactly as at `(6,3)`. -/
theorem isChartStrongStationaryData :
    IsChartStrongStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 7) → Finset (Fin 7)) :=
  isChartStrongStationaryData_of_isMin_of_weightPos _ crux.weight_pos crux.isChartMinimiser

/-- The argmax field, derived. -/
theorem isChartArgmaxValue :
    IsChartArgmaxValue 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) :=
  (exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin _ crux.weight_pos
    crux.isChartMinimiser).2

/-- Every atom lies in some argmax triple, and seven atoms need at least three of them —
one better than the `(6,3)` floor, because seven is not divisible by three. -/
theorem three_le_card_chartArgmaxFamily :
    3 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  have hbound := size_le_rank_mul_card_chartArgmaxFamily_of_isMin _ crux.weight_pos
    crux.isChartMinimiser
  omega

/-- Five lines are already too few, by pigeonhole from `hasNoParallelPair`. -/
theorem hasNoAtMostFiveLines : ¬ HasAtMostLines crux.design 5 := by
  rintro ⟨lineOf, hparallelOnLine⟩
  have hnotInjective : ¬ Function.Injective lineOf := by
    intro hinjective
    have hcard := Fintype.card_le_of_injective lineOf hinjective
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨keptLabel, dropLabel, hsameLine, hdistinct⟩ :=
    Function.not_injective_iff.mp hnotInjective
  obtain ⟨ratio, hparallel⟩ := hparallelOnLine keptLabel dropLabel hsameLine
  exact crux.hasNoParallelPair ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩

/-- Every deflation level is strictly below one. -/
theorem deflationLevel_lt_one (atomIndex : Fin 7) :
    deflationLevel crux.design atomIndex < 1 :=
  deflationLevel_lt_one_of_allHeavy (m := 6) crux.design (by norm_num) crux.isAllHeavy atomIndex

end SevenThreeCrux

/-- Unconditional: a `(7,3)` crux refutes the frontier cell. -/
theorem not_gtzWeighted_seven_three_of_sevenThreeCrux (crux : SevenThreeCrux) :
    ¬ GtzWeighted 7 3 := by
  intro hgtz
  obtain ⟨selected, hcard, hdominates⟩ := hgtz crux.design
  exact crux.hasNoDominatingTriple selected hcard hdominates

/-- **THE `(7,3)` ASSEMBLY, CONDITIONAL ON THE OPEN CELL.**  Granted
`Gtz.GtzWeighted 6 3`, a failure at `(7,3)` is realised at a seven-field crux.  The
hypothesis is irreducible on two of the three routes: the light-atom deflation of
`Gtz.exists_allHeavy_minimiser_sevenThree` and the parallel merge both land on `(6,3)`.
Only `Gtz.dominating_of_coSingleton_not_posDef_sevenThree` is free of it. -/
theorem nonempty_sevenThreeCrux_of_not_gtzWeighted_seven_three (hsixThree : GtzWeighted 6 3)
    (hfail : ¬ GtzWeighted 7 3) : Nonempty SevenThreeCrux := by
  obtain ⟨design, hheavy, hnotDominates, hmin, hnegative⟩ :=
    exists_allHeavy_minimiser_sevenThree hsixThree hfail
  refine ⟨⟨design, hmin, hnegative, hnotDominates, hheavy, ?_, ?_⟩⟩
  · intro atomIndex
    by_contra hnotPosDef
    obtain ⟨selected, hcard, hdominates⟩ :=
      dominating_of_coSingleton_not_posDef_sevenThree design atomIndex hnotPosDef
    exact hnotDominates selected hcard hdominates
  · rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
    obtain ⟨selected, hcard, hdominates⟩ :=
      dominating_of_parallel_pair (m := 6) design hsixThree hdistinct hparallel
    exact hnotDominates selected hcard hdominates

/-- **RANK THREE FROM THE TWO NORMAL FORMS.**  Emptying both structures proves weighted
GTZ at rank three for EVERY size, with nothing left over.  So the pair of normal forms is
a complete reformulation of the rank-three conjecture, not a filter on it: no
counterexample of any size escapes them.

The route is the shipped size induction — `Gtz.gtzWeightedAll_three_of_seven_three`
converts the frontier cell into all sizes — with the crux cell supplied first, exactly as
the conditionality of the `(7,3)` production requires. -/
theorem gtzWeightedAll_three_of_isEmpty_cruxes (hsixEmpty : IsEmpty SixThreeCrux)
    (hsevenEmpty : IsEmpty SevenThreeCrux) : GtzWeightedAll 3 := by
  have hsixThree : GtzWeighted 6 3 := gtzWeighted_six_three_of_isEmpty_sixThreeCrux hsixEmpty
  refine gtzWeightedAll_three_of_seven_three (not_not.mp fun hfail => hsevenEmpty.elim ?_)
  exact (nonempty_sevenThreeCrux_of_not_gtzWeighted_seven_three hsixThree hfail).some

end Gtz

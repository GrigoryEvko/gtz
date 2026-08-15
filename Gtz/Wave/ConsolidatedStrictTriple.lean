/-
# One statement for five obligations: the consolidated strict card-three
# selection

The rank-three campaign carries seven registry axioms.  Five of them are on the
path to `Gtz.GtzWeighted 6 3`:

* `Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual` (A1),
* `Gtz.OneLineTenthHeavyJointBlindLineSparse` (the one-line survivor),
* `Gtz.TwoMeetingLinesTenthHeavyJointBlindTransversal` (the tenth-heavy line),
* `Gtz.ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines`
  (A2),
* `Gtz.KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict` (A3).

Each was cut to a different stratum with a different blind spot, a different
candidate list and a different conclusion.  This file shows that **all five are
consequences of one statement**, and that the statement mentions no stratum, no
blind spot and no candidate list.

## What this file does NOT do

It does not prove anything about `Gtz.GtzWeighted 6 3`.  A consolidation
concentrates debt, it does not discharge it.  Five axioms whose truth is
supported by separate arguments become one axiom whose truth is supported by
one argument, and the surviving argument is a **measurement**, not a proof.  The
registry count is unchanged by this file, deliberately: nothing here is wired
into `Skeleton.Obligations`, and the count still reads seven.

## PROVED here, kernel-checked, unconditional

* `Gtz.ConsolidatedStrictTriple` — the statement, at the chart level.
* `Gtz.ConsolidatedStrictTripleDesign` — the same statement at the design level,
  and `Gtz.consolidatedStrictTripleDesign_of_consolidatedStrictTriple`, the
  specialization.  A design is a chart point of its own atom family, and
  `Gtz.directionChartGap_designChartPoint` is the per-selection dictionary.
* `Gtz.threeLinesDirection_pairwise_independent` — the A2 chart family has no
  parallel pair at a nonzero slide.  The K4 family already had
  `Gtz.kFourDirection_pair_independent`.
* Five wiring theorems, one for each on-path obligation, each named
  `..._of_consolidatedStrictTriple`.

## Why the non-degeneracy hypothesis costs nothing

The consolidated statement assumes the directions span and have no parallel
pair.  Both are free at every consumer.  Spanning is Parseval at a design
(`Gtz.designAtom_span`) and a landed lemma at each chart
(`Gtz.threeLinesDirection_span`, `Gtz.kFourDirection_span`).  The absence of a
parallel pair is supplied at the three design strata by the line pattern itself
(`Gtz.Design.LinePatternPrimitivity`), and at the two chart strata by the
explicit direction family.

## Why the hypothesis is stated at the chart level

A1, the one-line survivor and the tenth-heavy line quantify over
`Gtz.WeightedDesign 6 3`.  A2 and A3 quantify over `Gtz.DirectionChartPoint 6`,
which carries no Parseval condition and separates mass from weight.  The chart
is the larger object, so the chart statement implies the design statement and
not the other way around.  A design-level consolidation would reach three of the
five obligations.  The chart-level one reaches all five, and it is
correspondingly stronger and correspondingly harder to believe.

## What the measurement says, and a trap in it

`Gtz.ConsolidatedStrictTriple` is measured, not proved.  Two searches ran
against it.

The reliable one is exact.  Write the weights as `W_c / D` with integer `W_c`
and `D = ∑ W_c`, and the ratios `mass / weight` as integers `R_c`.  Then
`D * directionChartGap` is an integer matrix, and the twenty leading-minor tests
are exact integer arithmetic.  That search covered **1.2 billion samples** over
integer direction families and over `R` and `W` up to one million, and found
**zero** counterexamples.  A second exact search at the design level, in the
congruence coordinates that need no matrix square root, covered **160 million**
samples over twelve decades of weight spread and found **zero**.

A third search, in a different language and in unbounded exact rational
arithmetic, covered **205,324** accepted samples over fifteen configurations,
out to eighteen decades of spread in both the weights and the ratios.  It found
**zero** counterexamples and **zero** control failures.  The control is that the
full selection is always strictly dominating, which is the landed theorem
`Gtz.posDef_subsetSum_univ_sub_one`.

The trap is that a naive double-precision search reports counterexamples that do
not exist.  At six decades of ratio spread it reported 1,677 in forty million
samples.  Every one of them is cancellation: the selected sum and the subtracted
moment agree to many digits, so the third leading minor of a genuinely positive
definite gap comes out nonpositive.  Re-testing at 64-bit mantissa rescued
1,964 of 1,966, and re-testing at 113-bit mantissa rescued the rest, leaving
**zero** survivors at six and at nine decades.  At eighteen decades even 113-bit
arithmetic still reports false counterexamples, and only the exact rational run
clears them.  **Do not use floating point on this criterion at any precision.**
Use the integer form or exact rationals.
-/
import Gtz.Design.LinePatternPrimitivity
import Gtz.Design.DesignDescentPort
import Gtz.Design.KFourChartClosure
import Gtz.Design.TwoMeetingLinesTransversal
import Gtz.Wave.TwoOutsideMomentLaw
import Gtz.Wave.A1NeedleWiring
import Gtz.Wave.OneLineSurvivorWiring
import Gtz.Wave.TenthHeavyLineResidualWiring
import Gtz.Wave.ThreeLinesMovedOrbitTraceWiring
import Gtz.Wave.KFourStarAllMaxHeavyWiring

namespace Gtz

open Finset Matrix

/-! ## The statement -/

/-- **A direction family is pair-independent** when no direction is a multiple
of another.  This is `Gtz.IsPrimitiveDesign` with the atom family named
directly, so a design satisfies it exactly when it is primitive. -/
def DirectionsArePairIndependent {size : ℕ} (direction : Fin size → (Fin 3 → ℝ)) : Prop :=
  ∀ (keptLabel dropLabel : Fin size) (ratio : ℝ),
    keptLabel ≠ dropLabel → direction dropLabel ≠ ratio • direction keptLabel

/-- **THE CONSOLIDATED STATEMENT.**  Every chart point of a spanning,
pair-independent direction family at size six and rank three carries a strictly
dominating card-three selection.

No stratum, no line pattern, no blind spot, no heavy label, no candidate list,
no weak antecedent.  The two hypotheses are non-degeneracy of the directions,
and nothing else. -/
def ConsolidatedStrictTriple : Prop :=
  ∀ direction : Fin 6 → (Fin 3 → ℝ),
    (∀ probe : Fin 3 → ℝ, (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0) →
    DirectionsArePairIndependent direction →
    ∀ point : DirectionChartPoint 6,
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap direction point.mass point.weight selected).PosDef

/-- **The design-level reading.**  Every primitive weighted design at `(6,3)`
carries a strictly dominating card-three subset. -/
def ConsolidatedStrictTripleDesign : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - 1).PosDef

/-- **The chart statement implies the design statement.**  A design is the chart
point of its own atom family with mass equal to weight, spanning is Parseval,
and the gap dictionary is an equality at every selection. -/
theorem consolidatedStrictTripleDesign_of_consolidatedStrictTriple
    (hconsolidated : ConsolidatedStrictTriple) : ConsolidatedStrictTripleDesign := by
  intro design hprimitive
  obtain ⟨selected, hcard, hposDef⟩ :=
    hconsolidated design.atom (fun probe hprobe => designAtom_span design probe hprobe)
      hprimitive (designChartPoint design)
  refine ⟨selected, hcard, ?_⟩
  rwa [directionChartGap_designChartPoint design selected] at hposDef

/-! ## The pair independence of the two chart families

The K4 family already carries `Gtz.kFourDirection_pair_independent` in the
coefficient phrasing.  The three-lines family carries no such lemma, and it
genuinely fails at slide zero, where label five reads `![0, 1, 0]` and coincides
with label one.  Admissibility excludes exactly that value.
-/

/-- **The K4 family has no parallel pair.**  Read off the landed coefficient
form: a multiple relation is a vanishing combination with a unit coefficient. -/
theorem directionsArePairIndependent_kFourDirection :
    DirectionsArePairIndependent kFourDirection := by
  intro keptLabel dropLabel ratio hdistinct hparallel
  have hcombination :
      (-ratio) • kFourDirection keptLabel + (1 : ℝ) • kFourDirection dropLabel = 0 := by
    rw [hparallel, one_smul, neg_smul]
    exact neg_add_cancel _
  have hcoeff := kFourDirection_pair_independent hdistinct (-ratio) 1 hcombination
  exact one_ne_zero hcoeff.2

/-- **The three-lines family has no parallel pair at a nonzero slide.**  Thirty
ordered pairs of distinct labels, each closed on its coordinates.  Two pairs need
the slide.  At `(1, 5)` the reading `![0, 1, slide]` is a multiple of `![0, 1, 0]`
exactly when the slide vanishes, and the third coordinate says so directly.  At
`(5, 1)` the second coordinate pins the ratio to one first, and the third
coordinate then reads the slide. -/
theorem threeLinesDirection_pairwise_independent (slide : ℝ) (hslide : slide ≠ 0) :
    DirectionsArePairIndependent (threeLinesDirection slide) := by
  intro keptLabel dropLabel ratio hdistinct hparallel
  have hzeroth := congrFun hparallel 0
  have hfirst := congrFun hparallel 1
  have hsecond := congrFun hparallel 2
  clear hparallel
  simp only [Pi.smul_apply, smul_eq_mul] at hzeroth hfirst hsecond
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    simp only [threeLinesDirection, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, mul_zero,
      mul_one] at hzeroth hfirst hsecond ⊢ <;>
    first
      | exact hdistinct rfl
      | linarith
      | exact hslide (by linarith)
      | exact hslide (by subst_vars; linarith)

/-! ## The five wirings

Each theorem below spends the consolidated statement once and then one landed
restriction: the strict triple has to land inside that stratum's candidate list.
Every stratum hypothesis of the obligation that is not needed is discarded, which
is the point of a consolidation.
-/

/-- **A1 follows.**  The A1 residual is a counterexample: it lists eighteen
hypotheses and concludes `False`.  One of the eighteen says no card-three
selection is strictly dominating, and the empty line pattern makes the design
primitive, so the consolidated statement contradicts it directly.  The other
seventeen hypotheses are never read. -/
theorem baseTripleTightLineFreeOffConicHeavyNeedleResidual_of_consolidatedStrictTriple
    (hconsolidated : ConsolidatedStrictTriple) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual := by
  intro design _tightDir _weakDir hlineFree _hoffConic _hdominates _htightNe _htight
    _hweakNe _hweak _htightSeparated _hheavyBase _hbaseUpper _hdiscriminant
    _hbaseNotStrict _hbaseResidual _hnoLight _hheavy hnoStrict _hcapLower _hcapUpper
    _hprobe
  obtain ⟨selected, hcard, hposDef⟩ :=
    consolidatedStrictTripleDesign_of_consolidatedStrictTriple hconsolidated design
      (isPrimitiveDesign_of_emptyPattern design hlineFree)
  exact hnoStrict selected hcard hposDef

/-- **The one-line survivor follows.**  The one line makes the design primitive,
the consolidated statement supplies a strict card-three subset, and the landed
normal-blind restriction puts that subset in the ten-candidate list. -/
theorem oneLineTenthHeavyJointBlindLineSparse_of_consolidatedStrictTriple
    (hconsolidated : ConsolidatedStrictTriple) :
    OneLineTenthHeavyJointBlindLineSparse := by
  intro design hpattern _hheavy _hweightHeavy _hcapBlind hlineBlind _hweak
  obtain ⟨selected, hcard, hposDef⟩ :=
    consolidatedStrictTripleDesign_of_consolidatedStrictTriple hconsolidated design
      (isPrimitiveDesign_of_oneLinePattern design hpattern)
  exact planeBranchTenCandidate_of_oneLine_strictTriple_of_normalBlind design hpattern
    hlineBlind selected hcard hposDef

/-- **The tenth-heavy two meeting lines follows.**  The two lines make the design
primitive, the consolidated statement supplies a strict card-three subset, and
the landed two-normal restriction puts that subset on one of the four
transversals through the open label. -/
theorem twoMeetingLinesTenthHeavyJointBlindTransversal_of_consolidatedStrictTriple
    (hconsolidated : ConsolidatedStrictTriple) :
    TwoMeetingLinesTenthHeavyJointBlindTransversal := by
  intro design hpattern _hheavy _hweightHeavy _hcapBlind _hweak
    normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
    hblindFirst hblindSecond
  obtain ⟨selected, hcard, hposDef⟩ :=
    consolidatedStrictTripleDesign_of_consolidatedStrictTriple hconsolidated design
      (isPrimitiveDesign_of_twoMeetingLinesPattern design hpattern)
  have hshape := twoMeetingLines_strictTriple_eq_transversal_of_bothLineNormalBlind
    design normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
    hblindFirst hblindSecond selected hcard hposDef
  rcases hshape with h135 | h145 | h235 | h245
  · exact Or.inl (by simpa only [h135] using hposDef)
  · exact Or.inr (Or.inl (by simpa only [h145] using hposDef))
  · exact Or.inr (Or.inr (Or.inl (by simpa only [h235] using hposDef)))
  · exact Or.inr (Or.inr (Or.inr (by simpa only [h245] using hposDef)))

/-- **A2 follows.**  The three-lines chart spans at every slide and has no
parallel pair at an admissible one, so the consolidated statement applies with no
restriction step: A2 already asks only for a strict card-three selection.  The
budget cell, the reading cover, the orbit trace and the weak antecedent are all
discarded. -/
theorem chartTieFreeThreeLines_of_consolidatedStrictTriple
    (hconsolidated : ConsolidatedStrictTriple) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines := by
  intro slide hadmissible _hslideBound point _hbudget _hreading _horbit _hweak
  exact hconsolidated (threeLinesDirection slide) (threeLinesDirection_span slide)
    (threeLinesDirection_pairwise_independent slide hadmissible.1) point

/-- **A3 follows.**  The K4 chart spans and has no parallel pair, so the
consolidated statement supplies a strict card-three selection.  A card-three
subset of the six K4 edges is a spanning tree or one of the four dependent
triples, and a dependent triple is not even weakly dominating, so the selection
is a spanning tree. -/
theorem kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_of_consolidatedStrictTriple
    (hconsolidated : ConsolidatedStrictTriple) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  intro point _hlayerA _hstar _hatlas _hledger _hresidual
  obtain ⟨selected, hcard, hposDef⟩ :=
    hconsolidated kFourDirection kFourDirection_span
      directionsArePairIndependent_kFourDirection point
  rcases cardThreeSubset_isSpanningTreeOrDependentTriple selected hcard with
    htree | htriangle
  · exact ⟨selected, htree, hposDef⟩
  · exact absurd hposDef.posSemidef
      (kFourDependentTriple_gap_not_posSemidef point selected htriangle)

end Gtz

/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Quantitative.ChartDisjointBlockExclusion
import Gtz.Quantitative.SixThreeFrontierSharp

/-!
# The MINIMALITY layer of the `(6,3)` refutation box

`Gtz.isSixThreeRefutationCandidateSharp_iff` proved the sharp box EQUAL to the shipped
box, because every conjunct it added was a consequence of the box's own no-domination
clause.  This file adds conjuncts that are NOT: they are consequences of
`Gtz.SixThreeCrux.isChartMinimiser`, and no derivation of them from
`Gtz.SixThreeCrux.hasNoDominatingTriple` is known.

## The four conjuncts

* `Gtz.HasThreeArgmaxBlocks` -- the argmax family has at least three members.  At a
  crux this is `Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily`, which spends
  `isChartMinimiser` and `hasNegativeChartValue`.  It is ALREADY a component of
  `Gtz.SixThreeCrux.frontier`, and `Gtz.isSixThreeRefutationCandidate_of_sixThreeCrux`
  discards it (its `obtain` pattern binds the second component to `_`): the box did not
  fail to prove it, the box threw it away.
* `Gtz.HasChartValueAboveSharpFloor` -- `-4/27 <= chartObjective`, the frontier's other
  discarded component.
* `Gtz.HasCoveringArgmaxFamily` -- every atom lies in some argmax triple.  At a crux
  this is the shipped `Gtz.SixThreeCrux.exists_mem_chartArgmaxFamily`, whose proof runs
  through the constant assembly diagonal `1/size > 0` of `Gtz.IsChartStationaryData`;
  the value never appears, so no `value != 0` hypothesis is consumed.
* `Gtz.HasSupportedCoveringArgmaxFamily` -- STRICTLY STRONGER than coverage: the
  covering block can be chosen with a tight direction whose coordinate at the atom does
  NOT vanish.  Coverage only needs the assembly diagonal to be nonzero; the diagonal
  says `sum over active C containing c of mu_C (u_C)_c^2 = 1/size`, and one positive
  summand is exactly a block with a positive multiplier and a nonvanishing coordinate.
  The general form is
  `Gtz.exists_mem_activeSubset_pos_activeWeight_tightDir_ne_zero_of_isChartStationaryData`,
  which sharpens the shipped `Gtz.exists_mem_activeSubset_of_isChartStationaryData` at
  every size and rank.

All four are DESIGN-LEVEL: `Gtz.chartPointOfDesign` is a function of the design, and
each of the twenty block values is the least eigenvalue of an explicit `3 x 3` matrix
built from the atoms and the weights.  A search evaluates the first three by twenty
eigenvalue extractions and one comparison, and the fourth by reading the least
eigenspace of each argmax block.

## Why these are not the sharp box again

The sharp box's four conjuncts were each derived from `hasNoDominatingTriple`
(`Gtz.isSixThreeRefutationCandidateSharp_of_candidate`).  These are derived from
`isChartMinimiser`, and they constrain the design in a way non-domination cannot: they
ask for an exact TIE among block values, a closed condition with EMPTY INTERIOR, while
non-domination is an OPEN condition.  A closed condition with empty interior is not
implied by an open one unless the open one is empty.  That paragraph is an ARGUMENT, not
a theorem of this file.

## What "shrinks" can mean here -- the adjudication

`Gtz.not_gtzWeighted_six_three_of_isSixThreeRefutationCandidate` says every member of
the shipped box refutes the cell.  So:

**A design witnessing that this layer strictly shrinks the box is itself a refutation
of `Gtz.GtzWeighted 6 3`.**  That is
`Gtz.not_gtzWeighted_six_three_of_exists_strictShrink`, and
`Gtz.not_gtzWeighted_six_three_of_exists_candidate_not_satisfying` says the same for an
ARBITRARY extra conjunct.  Strict properness is therefore not merely unproved: it is a
refutation of the cell, and no honest run can exhibit it while the cell stands.  The
previous campaign's iff-trap was NOT that its box failed to shrink -- it was that its
conjuncts were PROVABLY IMPLIED by the box.  The distinction is exactly this one, and it
is a theorem here rather than a slogan.

**NOTHING IN THIS FILE ASSERTS THAT THE BOX GOT SMALLER.**  The only honest properness
is RELATIVE, against the box with its one globally expensive conjunct removed:

* `Gtz.IsSixThreeShapeCandidate` -- the shipped box minus `hasNoDominatingTriple`.
* `Gtz.MinimalityLayerIsProperOverShape` -- a design satisfying all ten shape conjuncts
  whose argmax family does not cover.  Its witness is exact and is recorded in that
  declaration's docstring; it is MEASURED OUTSIDE LEAN AND NOT MECHANIZED HERE, which is
  why it is a `Prop` and not a theorem.
* `Gtz.exists_shapeCandidate_not_isSixThreeRefutationCandidateMinimal_of_properOverShape`
  is what that `Prop` buys once someone supplies it, so it is a hypothesis with a
  consumer rather than an inert assertion.

The corresponding statement over the FIRST of those ten conjuncts alone IS mechanized, in
`Gtz/Quantitative/SixThreeMinimalityWitness.lean`: `Gtz.minimalityLayerIsProperOverAllHeavy`
exhibits an ALL-HEAVY design whose argmax family is a single block.  All-heaviness is the
conjunct that carries rank three on its own, by `Gtz.rank_three_of_heavy_six_three`, so
that is the sharpest properness available without the full shape box.

## What is NOT here

No claim that the minimal box is strictly smaller than the shipped one (see above).  No
properness witness over the full ten-conjunct shape box -- only over all-heaviness, and
that in the companion file.  Nothing that approaches `Gtz.GtzWeighted 6 3`: the whole
layer is a restatement of minimality at the design level, and its conjuncts are
conjecturally vacuous exactly when the cell holds.

NO SORRY, NO AXIOM, NO `native_decide`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

open scoped BigOperators

/-! ## Two laws at every size and rank

The shipped `Gtz.exists_mem_activeSubset_of_isChartStationaryData` uses only that the
constant assembly diagonal is NONZERO.  The same two lines give the positive summand
itself, which carries a positive multiplier and a nonvanishing tight coordinate; and
reading the diagonal in the other direction caps every multiplier. -/

section GeneralSize

variable {size : ℕ} {activeIndex : Type*}

/-- **THE SUPPORTED COVERAGE LAW.**  Every atom lies in an active subset whose
multiplier is STRICTLY POSITIVE and whose tight direction does not vanish at that atom.
Sharpens `Gtz.exists_mem_activeSubset_of_isChartStationaryData`, whose conclusion is the
membership alone. -/
theorem exists_mem_activeSubset_pos_activeWeight_tightDir_ne_zero_of_isChartStationaryData
    {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    ∃ activeLabel ∈ activeSet, atomIndex ∈ activeSubset activeLabel
      ∧ 0 < activeWeight activeLabel ∧ tightDir activeLabel atomIndex ≠ 0 := by
  by_contra hnone
  simp only [not_exists, not_and, not_ne_iff] at hnone
  have hvanish : ∑ activeLabel ∈ activeSet,
      activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun activeLabel hmem => ?_
    by_cases hmember : atomIndex ∈ activeSubset activeLabel
    · rcases le_or_gt (activeWeight activeLabel) 0 with hnonpositive | hpositive
      · rw [le_antisymm hnonpositive (hdata.activeWeight_nonneg activeLabel hmem)]
        ring
      · rw [hnone activeLabel hmem hmember hpositive]
        ring
    · rw [hdata.tightDir_support activeLabel hmem atomIndex hmember]
      ring
  have hdiagonal := hdata.assembly_diagonal atomIndex
  rw [chartMultiplierAssembly_diagonal, hvanish] at hdiagonal
  exact absurd hdiagonal.symm
    (ne_of_gt (inv_pos.mpr (size_cast_pos_of_isChartStationaryData hdata)))

/-- **THE MULTIPLIER CAP.**  No active multiplier exceeds `rank / size`.  The tight
direction is a unit vector supported on its own `rank`-element subset, so its multiplier
splits into `rank` summands of the assembly diagonal, each at most `1/size`.  Both the
constant-diagonal field and the cardinality field are spent; nothing about the value or
the chart is used, so the bound holds at EVERY chart-stationary datum, at every size and
rank.  At `(6,3)` it reads `mu_C <= 1/2`. -/
theorem activeWeight_le_rank_div_size_of_isChartStationaryData
    {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet) :
    activeWeight activeLabel ≤ (rank : ℝ) / (size : ℝ) := by
  have hunit : ∑ atomIndex ∈ activeSubset activeLabel,
      tightDir activeLabel atomIndex ^ 2 = 1 := by
    have hall : ∑ atomIndex : Fin size, tightDir activeLabel atomIndex ^ 2 = 1 := by
      have hdot := hdata.tightDir_unit activeLabel hmem
      rw [dotProduct] at hdot
      simpa [sq] using hdot
    rw [← hall]
    refine Finset.sum_subset (Finset.subset_univ (activeSubset activeLabel)) ?_
    intro atomIndex _ hnot
    rw [hdata.tightDir_support activeLabel hmem atomIndex hnot]
    ring
  calc activeWeight activeLabel
      = ∑ atomIndex ∈ activeSubset activeLabel,
          activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2 := by
        rw [← Finset.mul_sum, hunit, mul_one]
    _ ≤ ∑ _atomIndex ∈ activeSubset activeLabel, ((size : ℝ))⁻¹ := by
        refine Finset.sum_le_sum fun atomIndex _ => ?_
        have hdiag := hdata.assembly_diagonal atomIndex
        rw [chartMultiplierAssembly_diagonal] at hdiag
        rw [← hdiag]
        exact Finset.single_le_sum
          (f := fun label => activeWeight label * tightDir label atomIndex ^ 2)
          (fun label hlabel =>
            mul_nonneg (hdata.activeWeight_nonneg label hlabel) (sq_nonneg _)) hmem
    _ = (rank : ℝ) / (size : ℝ) := by
        rw [Finset.sum_const, hdata.activeSubset_card activeLabel hmem, nsmul_eq_mul,
          div_eq_mul_inv]

end GeneralSize

/-! ## The four design-level minimality conjuncts -/

/-- **THE ARGMAX FAMILY CARRIES THREE TRIPLES.** -/
def HasThreeArgmaxBlocks (design : WeightedDesign 6 3) : Prop :=
  3 ≤ (chartArgmaxFamily (chartPointOfDesign design)).card

/-- **THE CHART VALUE SITS ABOVE THE SHARP FLOOR.**  The other dropped conjunct:
`Gtz.SixThreeCrux.frontier` proves `-4/27 <= value` and the box discarded it along with
the argmax cardinality, because both are stated in chart vocabulary.  Unlike the other
two this one is NOT exhibitably proper over the shape box -- a shape design violating it
has every block value below `-4/27 < 0`, hence no dominating triple at all, hence IS a
refutation.  It is carried here because it is a genuine minimality consequence, it costs
one line, and it is the hook the value lane needs: the shipped box contains no statement
about `chartObjective` whatever. -/
def HasChartValueAboveSharpFloor (design : WeightedDesign 6 3) : Prop :=
  -(4 / 27 : ℝ) ≤ chartObjective (chartPointOfDesign design)

/-- **THE ARGMAX FAMILY COVERS EVERY ATOM.**  `chartArgmaxFamily` of a design's chart
point is the set of triples whose block attains the maximum of the twenty least
eigenvalues; this asks that their union be everything. -/
def HasCoveringArgmaxFamily (design : WeightedDesign 6 3) : Prop :=
  ∀ atomIndex : Fin 6,
    ∃ block ∈ chartArgmaxFamily (chartPointOfDesign design), atomIndex ∈ block

/-- **THE SUPPORTED COVERING LAW, AT THE DESIGN.**  Strictly stronger than
`Gtz.HasCoveringArgmaxFamily`, and still design-level: the tight direction is a least
eigenvector of an explicit block, so a searcher reads it off the same eigendecomposition
that produced the block value. -/
def HasSupportedCoveringArgmaxFamily (design : WeightedDesign 6 3) : Prop :=
  ∀ atomIndex : Fin 6, ∃ block ∈ chartArgmaxFamily (chartPointOfDesign design),
    atomIndex ∈ block ∧ ∃ tightVec : Fin 6 → ℝ,
      IsChartTightDirection (chartPointOfDesign design).chart
          (chartPointOfDesign design).weight
          (chartObjective (chartPointOfDesign design)) block tightVec
        ∧ tightVec atomIndex ≠ 0

/-- Support implies coverage: forget the tight direction. -/
theorem hasCoveringArgmaxFamily_of_hasSupportedCoveringArgmaxFamily
    {design : WeightedDesign 6 3} (hsupported : HasSupportedCoveringArgmaxFamily design) :
    HasCoveringArgmaxFamily design := fun atomIndex =>
  let witness := hsupported atomIndex
  ⟨witness.choose, witness.choose_spec.1, witness.choose_spec.2.1⟩

/-- Coverage forces at least two argmax triples: three atoms per triple, six atoms.  The
count is the shipped `Gtz.sum_activeFamilyDegree_eq_rank_mul_card`, applied to the argmax
family, whose members have cardinality three by `Gtz.mem_chartArgmaxFamily_iff`.
`Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily` improves this to three at a crux, at
the cost of the negative-value field. -/
theorem two_le_card_chartArgmaxFamily_of_hasCoveringArgmaxFamily
    {design : WeightedDesign 6 3} (hcovering : HasCoveringArgmaxFamily design) :
    2 ≤ (chartArgmaxFamily (chartPointOfDesign design)).card := by
  classical
  have hmemberCard : ∀ block ∈ chartArgmaxFamily (chartPointOfDesign design),
      block.card = 3 := fun block hmem =>
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign design) block).mp hmem).1
  have hdouble := sum_activeFamilyDegree_eq_rank_mul_card (rank := 3)
    (chartArgmaxFamily (chartPointOfDesign design)) hmemberCard
  have hpositive : ∀ atomIndex : Fin 6,
      1 ≤ activeFamilyDegree (chartArgmaxFamily (chartPointOfDesign design)) atomIndex := by
    intro atomIndex
    obtain ⟨block, hblock, hatom⟩ := hcovering atomIndex
    rw [activeFamilyDegree]
    exact Finset.card_pos.mpr ⟨block, Finset.mem_filter.mpr ⟨hblock, hatom⟩⟩
  have hsix : (6 : ℕ)
      ≤ ∑ atomIndex : Fin 6,
          activeFamilyDegree (chartArgmaxFamily (chartPointOfDesign design)) atomIndex := by
    calc (6 : ℕ) = ∑ _atomIndex : Fin 6, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun atomIndex _ => hpositive atomIndex
  omega

/-! ## All four hold at a crux, and all four spend minimality -/

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- **THREE ARGMAX TRIPLES AT A CRUX.**  `Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily`,
read at the design.  Consumes `isChartMinimiser` and `hasNegativeChartValue`. -/
theorem hasThreeArgmaxBlocks : HasThreeArgmaxBlocks crux.design :=
  crux.three_le_card_chartArgmaxFamily

/-- **THE SHARP VALUE FLOOR AT A CRUX.**
`Gtz.SixThreeCrux.neg_four_div_twentySeven_le_chartObjective`, read as a box conjunct. -/
theorem hasChartValueAboveSharpFloor : HasChartValueAboveSharpFloor crux.design :=
  crux.neg_four_div_twentySeven_le_chartObjective

/-- **COVERAGE AT A CRUX.**  The shipped `Gtz.SixThreeCrux.exists_mem_chartArgmaxFamily`,
read as a box conjunct.  The only crux fields it consumes are `isChartMinimiser` and the
carrier's own weight positivity -- `hasNoDominatingTriple` is not used. -/
theorem hasCoveringArgmaxFamily : HasCoveringArgmaxFamily crux.design :=
  crux.exists_mem_chartArgmaxFamily

/-- **SUPPORTED COVERAGE AT A CRUX**, through the weak stationarity bundle. -/
theorem hasSupportedCoveringArgmaxFamily :
    HasSupportedCoveringArgmaxFamily crux.design := by
  intro atomIndex
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  obtain ⟨activeLabel, hmem, hatom, -, hnonzero⟩ :=
    exists_mem_activeSubset_pos_activeWeight_tightDir_ne_zero_of_isChartStationaryData
      hdata atomIndex
  exact ⟨activeLabel, hmem, hatom, selection activeLabel,
    ⟨hdata.tightDir_unit activeLabel hmem, hdata.tightDir_support activeLabel hmem,
      hdata.tightDir_isTight activeLabel hmem⟩, hnonzero⟩

/-- **THE MULTIPLIER CAP AT A CRUX**: every active multiplier of the crux's own
stationarity bundle is at most one half.  `(6,3)` instance of
`Gtz.activeWeight_le_rank_div_size_of_isChartStationaryData`. -/
theorem activeWeight_le_half_of_isChartStationaryData
    {multiplier : Finset (Fin 6) → ℝ} {selection : Finset (Fin 6) → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier selection)
    {block : Finset (Fin 6)}
    (hmem : block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)) :
    multiplier block ≤ 1 / 2 := by
  have hbound := activeWeight_le_rank_div_size_of_isChartStationaryData hdata hmem
  norm_num at hbound
  linarith

end SixThreeCrux

/-! ## The enlarged box -/

/-- **THE `(6,3)` REFUTATION TARGET WITH THE MINIMALITY LAYER.**  The sharp box plus the
argmax cardinality floor, the supported covering law and the sharp value floor.  Unlike
the sharp layer, these are NOT consequences of the box's no-domination clause -- see the
honesty section.  They are also NOT proved to shrink it. -/
def IsSixThreeRefutationCandidateMinimal (design : WeightedDesign 6 3) : Prop :=
  IsSixThreeRefutationCandidateSharp design
    ∧ HasThreeArgmaxBlocks design
    ∧ HasSupportedCoveringArgmaxFamily design
    ∧ HasChartValueAboveSharpFloor design

/-- The minimal box sits inside the sharp one, hence inside the shipped one. -/
theorem isSixThreeRefutationCandidateSharp_of_minimal {design : WeightedDesign 6 3}
    (hminimal : IsSixThreeRefutationCandidateMinimal design) :
    IsSixThreeRefutationCandidateSharp design := hminimal.1

theorem isSixThreeRefutationCandidate_of_minimal {design : WeightedDesign 6 3}
    (hminimal : IsSixThreeRefutationCandidateMinimal design) :
    IsSixThreeRefutationCandidate design :=
  isSixThreeRefutationCandidate_of_sharp hminimal.1

/-- The cheap covering conjunct, free from the box. -/
theorem hasCoveringArgmaxFamily_of_minimal {design : WeightedDesign 6 3}
    (hminimal : IsSixThreeRefutationCandidateMinimal design) :
    HasCoveringArgmaxFamily design :=
  hasCoveringArgmaxFamily_of_hasSupportedCoveringArgmaxFamily hminimal.2.2.1

/-- Every crux's design is a MINIMAL refutation candidate. -/
theorem isSixThreeRefutationCandidateMinimal_of_sixThreeCrux (crux : SixThreeCrux) :
    IsSixThreeRefutationCandidateMinimal crux.design :=
  ⟨isSixThreeRefutationCandidateSharp_of_sixThreeCrux crux, crux.hasThreeArgmaxBlocks,
    crux.hasSupportedCoveringArgmaxFamily, crux.hasChartValueAboveSharpFloor⟩

/-- **THE MINIMAL TARGET IS REACHED BY EVERY FAILURE.** -/
theorem exists_isSixThreeRefutationCandidateMinimal_of_not_gtzWeighted_six_three
    (hfail : ¬ GtzWeighted 6 3) :
    ∃ design : WeightedDesign 6 3, IsSixThreeRefutationCandidateMinimal design := by
  obtain ⟨crux⟩ := nonempty_sixThreeCrux_of_not_gtzWeighted_six_three hfail
  exact ⟨crux.design, isSixThreeRefutationCandidateMinimal_of_sixThreeCrux crux⟩

/-- **THE MINIMAL SEARCH CRITERION.**  Emptying the smaller box still suffices. -/
theorem gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidateMinimal
    (hnone : ∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidateMinimal design) :
    GtzWeighted 6 3 := by
  by_contra hfail
  obtain ⟨design, hcandidate⟩ :=
    exists_isSixThreeRefutationCandidateMinimal_of_not_gtzWeighted_six_three hfail
  exact hnone design hcandidate

/-- **THE WHOLE RANK, ON THE MINIMAL BOX ALONE.** -/
theorem gtzWeightedAll_three_of_forall_not_isSixThreeRefutationCandidateMinimal
    (hnone : ∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidateMinimal design) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidateMinimal hnone)

/-- **THE ONE-ANTECEDENT TERMINUS, ON THE SMALLER BOX.**  Same shape as
`Gtz.gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidateSharp`, with
four more conjuncts available at every point of the search. -/
theorem gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidateMinimal
    (hnone : ∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidateMinimal design)
    (atomCount : ℕ) (hpos : 0 < atomCount) : GtzOriginal atomCount 3 :=
  gtz_original_rank_three_of_six_three
    (gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidateMinimal hnone)
    atomCount hpos

/-! ## The honesty layer: what "shrinks" can mean

The box's no-domination clause makes every box member a refutation, so a strict shrink
IS a refutation.  Both statements below are one line; they exist so that no later reader
mistakes an UNEXHIBITABLE properness for an unproved one. -/

/-- **EVERY BOX MEMBER REFUTES THE CELL.**  Immediate from the no-domination clause. -/
theorem not_gtzWeighted_six_three_of_isSixThreeRefutationCandidate
    {design : WeightedDesign 6 3} (hcandidate : IsSixThreeRefutationCandidate design) :
    ¬ GtzWeighted 6 3 := by
  intro hweighted
  obtain ⟨selected, hcard, hdominates⟩ := hweighted design
  exact hcandidate.2.2.2.2.1 selected hcard hdominates

/-- **A STRICT SHRINK IS A REFUTATION.**  If some design satisfies the shipped box but
NOT the minimality layer then `Gtz.GtzWeighted 6 3` is false.  So "the minimality layer
strictly shrinks the box" cannot be exhibited unless the cell falls, and its absence is
no evidence that the layer is vacuous. -/
theorem not_gtzWeighted_six_three_of_exists_strictShrink
    (hshrink : ∃ design : WeightedDesign 6 3, IsSixThreeRefutationCandidate design
      ∧ ¬ IsSixThreeRefutationCandidateMinimal design) :
    ¬ GtzWeighted 6 3 := by
  obtain ⟨design, hcandidate, -⟩ := hshrink
  exact not_gtzWeighted_six_three_of_isSixThreeRefutationCandidate hcandidate

/-- **AND THE SAME FOR ANY CONJUNCT WHATEVER.**  The obstruction is the box, not the
candidate: NO conjunct can be shown to shrink the shipped box while the cell stands.
Stated at an arbitrary predicate so that no future run re-attempts the impossible. -/
theorem not_gtzWeighted_six_three_of_exists_candidate_not_satisfying
    (extra : WeightedDesign 6 3 → Prop)
    (hshrink : ∃ design : WeightedDesign 6 3,
      IsSixThreeRefutationCandidate design ∧ ¬ extra design) :
    ¬ GtzWeighted 6 3 := by
  obtain ⟨design, hcandidate, -⟩ := hshrink
  exact not_gtzWeighted_six_three_of_isSixThreeRefutationCandidate hcandidate

/-! ## The exhibitable relative notion -/

/-- **THE SHIPPED BOX MINUS ITS ONE GLOBAL CONJUNCT.**  Everything in
`Gtz.IsSixThreeRefutationCandidate` except `hasNoDominatingTriple`.  This set is NOT
conjecturally empty, so properness against it is exhibitable. -/
def IsSixThreeShapeCandidate (design : WeightedDesign 6 3) : Prop :=
  AllHeavy design
    ∧ HasStrictlyDominatingCoSingletons design
    ∧ ¬ HasParallelPair design
    ∧ ¬ IsEqualShare design
    ∧ (∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - (3 / 5 : ℝ) • 1).PosSemidef)
    ∧ (∀ atomIndex : Fin 6, ¬ (subsetSum design {atomIndex}ᶜ - (5 : ℝ) • 1).PosSemidef)
    ∧ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
        ¬ (atomPairing design first second = 0 ∧ atomPairing design first third = 0
          ∧ atomPairing design second third = 0))
    ∧ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
        excessGap design first second third
          < heavyExcess design first * heavyExcess design second * heavyExcess design third / 4)
    ∧ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
        0 ≤ excessGap design first second third → tripleParity design first second third = -1)
    ∧ ((∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
      → linkWordOf design ∈ residualSectors)

/-- The shipped box implies the shape box: drop the no-domination clause. -/
theorem isSixThreeShapeCandidate_of_candidate {design : WeightedDesign 6 3}
    (hcandidate : IsSixThreeRefutationCandidate design) : IsSixThreeShapeCandidate design :=
  ⟨hcandidate.1, hcandidate.2.1, hcandidate.2.2.1, hcandidate.2.2.2.1,
    hcandidate.2.2.2.2.2.1, hcandidate.2.2.2.2.2.2.1, hcandidate.2.2.2.2.2.2.2.1,
    hcandidate.2.2.2.2.2.2.2.2.1, hcandidate.2.2.2.2.2.2.2.2.2.1,
    hcandidate.2.2.2.2.2.2.2.2.2.2⟩

/-- **RELATIVE PROPERNESS, THE EXHIBITABLE STATEMENT.**  Some design satisfies all ten
shape conjuncts and fails the covering law.  Since the shape box is not conjecturally
empty this IS exhibitable, and it says exactly that the covering law is not implied by
the box's cheap layer.

MEASURED EXACTLY OUTSIDE LEAN, AND NOT MECHANIZED HERE -- which is why this is a `Prop`
and not a theorem.  The witness is carried by six INTEGER directions in `Z^3`,

    g0 ~ (-6,-1,3)   g1 ~ (3,4,-2)   g2 ~ (5,-4,5)
    g3 ~ (-3,2,-1)   g4 ~ (0,1,1)    g5 ~ (-1,-1,2),

whose Parseval weights are the exact rationals
`(87/3554, 185/5331, 45/1777, 58/5331, 3185/3554, 15/1777)`, summing to one, with Gram
entries over the denominators `3435` and `1145`.  All ten shape conjuncts hold in exact
rational arithmetic; NINETEEN of the twenty triples fail to dominate; the argmax family
is the SINGLE triple `{0,1,2}`, separated from the runner-up by `0.0396`, so it covers
only three of the six atoms and both `Gtz.HasThreeArgmaxBlocks` and
`Gtz.HasCoveringArgmaxFamily` fail on it. -/
def MinimalityLayerIsProperOverShape : Prop :=
  ∃ design : WeightedDesign 6 3, IsSixThreeShapeCandidate design
    ∧ ¬ (HasThreeArgmaxBlocks design ∧ HasCoveringArgmaxFamily design)

/-- **WHAT THE PROPERNESS `Prop` BUYS**, once someone supplies it: the minimality layer
really does cut the shape box, i.e. some shape design is not a minimal candidate.  This
is the consumer that keeps `Gtz.MinimalityLayerIsProperOverShape` a hypothesis with a
conclusion rather than an inert assertion; it is NOT a proof of that hypothesis. -/
theorem exists_shapeCandidate_not_isSixThreeRefutationCandidateMinimal_of_properOverShape
    (hproper : MinimalityLayerIsProperOverShape) :
    ∃ design : WeightedDesign 6 3, IsSixThreeShapeCandidate design
      ∧ ¬ IsSixThreeRefutationCandidateMinimal design := by
  obtain ⟨design, hshape, hfail⟩ := hproper
  refine ⟨design, hshape, fun hminimal => hfail ⟨hminimal.2.1, ?_⟩⟩
  exact hasCoveringArgmaxFamily_of_hasSupportedCoveringArgmaxFamily hminimal.2.2.1

end Gtz

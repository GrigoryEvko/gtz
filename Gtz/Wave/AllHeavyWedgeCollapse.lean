/-
# The all-heavy collapse: the wedge balance alone decides, and the light branch is paid

`Gtz.posDef_iff_normalSurplus_and_wedgeBalance` decides strict domination by TWO
data at a unit normal: a NORMAL SURPLUS and the WEDGE BALANCE at every in-plane
probe.  `Gtz.posDef_iff_traceTest_and_wedgeBalance` replaces the surplus by the
STRICT trace test `3 < sum of the leverages`.  Every wedge selector in the tree
carries one of those two conjuncts, and no producer of either exists.

This file removes that conjunct, and then removes the whole light branch of the
`(6, 3)` problem.  Four independent results.

**ONE, the sharp trace threshold.**  `Gtz.forall_wedgeBalanceAt_iff_definite`
says the balance alone is DEFINITENESS OF EITHER SIGN, and
`Gtz.sum_leverage_lt_three_of_posDef_neg` says the negative branch forces the
leverage total STRICTLY BELOW three.  So the balance plus `3 <= sum` already
gives a positive definite gap.  The landed criterion asks for `3 < sum`.  The
non-strict threshold is sharp, and it is exactly what an all-heavy triple
supplies for free: three members of leverage at least one total at least three.

Four of the five on-path obligations hand over `1 <= leverageOf` at every label.
On that stratum the surplus conjunct, the trace conjunct and the leak are all
discharged, and the ENTIRE content of strict domination is the wedge balance.

**TWO, the strict-heaviness count.**  A weighted design of rank `k` has at least
`k` atoms of leverage STRICTLY above one.  No primitivity, no all-heavy, no
pattern.  The proof is one line of Parseval bookkeeping against the per-atom
leverage cap: the weighted gap excess totals `k - 1`, every term is at most
`1 - w`, and the light atoms only subtract.  Since a strict dominator has every
member strictly heavy, the search for a strict triple is confined to that set.
When the set has exactly three members it IS the only candidate, and the whole
`(6, 3)` question becomes ONE wedge balance with no selection left in it.

**THREE, the light branch is already paid.**  `Gtz.gtzWeighted_of_le_five` is an
unconditional theorem, so `Gtz.GtzWeighted 5 3` holds, and
`Gtz.posDef_of_strictly_light_atom` turns one atom of leverage strictly below one
into a strict card-three witness at size six.  So `(6, 3)` splits with no
hypothesis into a discharged light branch and an all-heavy branch.
`Gtz.AllHeavyWedgeSelector` is the residual, and it retires all five on-path
obligations.  The equivalence with `Gtz.ConsolidatedStrictTripleDesign` certifies
that the residual is neither weaker nor stronger than the target.

**FOUR, the general-rank hinge, consolidated.**  Both hinge obligations take the
predecessor cell and conclude a parallel pair out of a tie.
`Gtz.hinge_of_predecessor_on_strictlyLightBranch` closes their strictly light
branch at every rank.  `Gtz.AllHeavyHingeResidual` is what is left of the two
together, and this file proves each of the two axiom shapes from it.

## A weak-to-strict upgrade that costs nothing

`Gtz.planePair_sq_of_dominates` runs from `Gtz.Dominates`, which is only positive
SEMIdefinite, and gives `0 <= pairGapExcessOf` at the flat pair of a weak
card-three dominator.  Section 6 pairs that floor with the ceiling inside
`Gtz.IsCapBlindSpot`, a hypothesis of the two line obligations, and reads one
consequence off the floor alone: if the two flat atoms are not orthogonal, BOTH
are strictly heavy.  A weak dominator therefore upgrades `1 <= leverageOf` to
`1 < leverageOf` at two labels at once, and those two labels enter the strictly
heavy set of section 2.

## What this file does NOT claim

It does not prove `Gtz.AllHeavyWedgeSelector`, and it does not prove
`Gtz.AllHeavyHingeResidual`.  It proves that each is exactly what is left.

## #ZERO-CONSUMER — over a thousand lines, ONE consumed declaration

Outside this file and the two umbrellas, the only declaration here that any
module cites is `Gtz.sum_weight_mul_gapExcess`
(Gtz/Wave/TieStratumClassification.lean).  Every other theorem and definition,
including `Gtz.strictlyHeavySet` and its whole counting layer, has no outward
consumer.  Two forks have since re-derived pieces of this file elsewhere.

## #DUP — three names for one set, in three coordinate systems

* `Gtz.strictlyHeavySet design = {c : 1 < leverageOf (atom c)}` (:189), design
  coordinates.
* `Finset.univ.filter (fun c => weight c < chartMassLeverage direction mass c)`,
  chart coordinates, counted by `Gtz.three_le_card_overLevered`
  (Gtz/Wave/ThreeLinesSlideElimination.lean:283) and vetoed by
  `Gtz.weight_lt_chartMassLeverage_of_posDef_gap` (:341).  At a design point
  mass equals weight and the moment is the identity, so the two filters read the
  same labels.  NO KERNEL LEMMA LINKS THEM.
* `Finset.univ.filter (fun c => pivot D Finset.univ c < 1)` in
  `Gtz.compl_subset_lowPivot_of_posDef`
  (Gtz/Design/SharedAtomPivotExclusion.lean).  This one is a DIFFERENT scalar:
  `pivot` inverts the UNWEIGHTED `subsetSum D univ - 1`.  Do not merge it with
  the first two.

The base lemma `Gtz.one_lt_leverage_of_mem_of_posDef`
(Gtz/Design/SelectorEquivalences.lean:197) is spent in three places, but the
packaged counting layer of section 2 and section 3 is spent nowhere.
-/
import Gtz.Wave.WedgeBalanceAdjugate
import Gtz.Wave.OneLineWedgeFlatSplit
import Gtz.Wave.WiringDoorLedger
import Gtz.Wave.OnPathRegistryCollapse
import Gtz.Design.SelectorEquivalences
import Gtz.Design.PairCapEngine
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.Reductions
import Gtz.Reduction.ParallelFreeReach
import Gtz.Reduction.StressWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Finset Matrix

/-! ## 1. The sharp trace threshold

`Gtz.posDef_iff_traceTest_and_wedgeBalance` pairs the balance with `3 < sum`.
The negative branch of `Gtz.forall_wedgeBalanceAt_iff_definite` forces
`sum < 3`, so the balance already rules it out at `3 <= sum`.  The gain is the
difference between a strict and a non-strict inequality, and that difference is
the whole gap between what the on-path residuals supply and what the landed
criterion asks for. -/

/-- **THE BALANCE DECIDES AT A NON-STRICT TRACE THRESHOLD.**  A leverage total of
at least three, together with the wedge balance at every in-plane probe of one
unit normal, gives a positive definite gap.  The landed
`Gtz.posDef_iff_traceTest_and_wedgeBalance` asks for a STRICT total.  The
threshold here is sharp, because a negative definite gap forces the total
strictly below three. -/
theorem posDef_of_three_le_sum_leverage_of_wedgeBalance {size : ℕ}
    (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (hheavy : (3 : ℝ) ≤ ∑ label ∈ selected, leverageOf (design.atom label))
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hbalance : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      WedgeBalanceAt design selected unitNormal probeVec) :
    (subsetSum design selected - 1).PosDef := by
  rcases (forall_wedgeBalanceAt_iff_definite design selected unitNormal hunit).mp hbalance with
    hposDef | hnegDef
  · exact hposDef
  · exact absurd (sum_leverage_lt_three_of_posDef_neg design selected hnegDef)
      (not_lt.mpr hheavy)

/-- **A HEAVY TRIPLE TOTALS AT LEAST THREE.**  Card three and leverage at least
one at every member.  Nothing else. -/
theorem three_le_sum_leverage_of_allHeavy {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hcard : selected.card = 3)
    (hheavy : ∀ label ∈ selected, 1 ≤ leverageOf (design.atom label)) :
    (3 : ℝ) ≤ ∑ label ∈ selected, leverageOf (design.atom label) := by
  have hbound : ∑ _label ∈ selected, (1 : ℝ)
      ≤ ∑ label ∈ selected, leverageOf (design.atom label) := Finset.sum_le_sum hheavy
  have hconst : ∑ _label ∈ selected, (1 : ℝ) = 3 := by
    rw [Finset.sum_const, hcard]
    norm_num
  linarith [hbound, hconst]

/-- **THE ALL-HEAVY COLLAPSE.**  At a card-three subset whose every member has
leverage at least one, strict domination IS the wedge balance.  No normal
surplus, no trace test, no leak and no leverage cap survive on either side.  The
normal is arbitrary, and by `Gtz.forall_wedgeBalanceAt_normal_free` the right
side does not depend on which one is chosen. -/
theorem posDef_iff_wedgeBalance_of_allHeavy {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hcard : selected.card = 3)
    (hheavy : ∀ label ∈ selected, 1 ≤ leverageOf (design.atom label))
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    (subsetSum design selected - 1).PosDef
      ↔ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
          WedgeBalanceAt design selected unitNormal probeVec := by
  constructor
  · intro hposDef
    exact (forall_wedgeBalanceAt_iff_definite design selected unitNormal hunit).mpr
      (Or.inl hposDef)
  · exact posDef_of_three_le_sum_leverage_of_wedgeBalance design selected
      (three_le_sum_leverage_of_allHeavy design selected hcard hheavy) unitNormal hunit

/-- **THE CONSUMER SHAPE.**  One wedge balance at one heavy triple kills a tie. -/
theorem not_isTie_of_allHeavy_of_wedgeBalance {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hcard : selected.card = 3)
    (hheavy : ∀ label ∈ selected, 1 ≤ leverageOf (design.atom label))
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hbalance : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      WedgeBalanceAt design selected unitNormal probeVec) :
    ¬ IsTie design := fun htie =>
  htie.2 selected hcard
    ((posDef_iff_wedgeBalance_of_allHeavy design selected hcard hheavy unitNormal hunit).mpr
      hbalance)

/-- **THE PRUNING LAW.**  On the all-heavy stratum a member of leverage EXACTLY
one refuses the balance at every triple through it.  So the unit-leverage labels
are dead weight for the selector, and only the strictly heavy ones can appear. -/
theorem not_forall_wedgeBalanceAt_of_leverage_eq_one {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hcard : selected.card = 3)
    (hheavy : ∀ label ∈ selected, 1 ≤ leverageOf (design.atom label))
    {unitLabel : Fin size} (hmem : unitLabel ∈ selected)
    (hunitLeverage : leverageOf (design.atom unitLabel) = 1)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    ¬ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
        WedgeBalanceAt design selected unitNormal probeVec := by
  intro hbalance
  have hposDef :=
    (posDef_iff_wedgeBalance_of_allHeavy design selected hcard hheavy unitNormal hunit).mpr
      hbalance
  have hstrict := one_lt_leverage_of_mem_of_posDef design selected hcard hmem hposDef
  rw [hunitLeverage] at hstrict
  exact absurd hstrict (lt_irrefl 1)

/-! ## 2. Every design has at least `rank` strictly heavy atoms

Parseval's trace gives `sum of w * leverage = rank`, and the weights total one,
so the WEIGHTED GAP EXCESS totals `rank - 1`.  The per-atom leverage cap
`Gtz.weighted_leverage_le_one` bounds each term by `1 - w`.  The atoms of
leverage at most one contribute nothing positive, so `rank - 1` is beaten by the
count of the strictly heavy atoms minus their weight, and the count is at least
`rank`.

No hypothesis is used beyond the design axioms.  This is a structural law of
every weighted design at every rank. -/

/-- The atoms of leverage strictly above one.  A strict dominator lives inside
this set, by `Gtz.one_lt_leverage_of_mem_of_posDef`. -/
noncomputable def strictlyHeavySet {m k : ℕ} (design : WeightedDesign m k) : Finset (Fin m) :=
  Finset.univ.filter fun label => 1 < leverageOf (design.atom label)

theorem mem_strictlyHeavySet_iff {m k : ℕ} (design : WeightedDesign m k) (label : Fin m) :
    label ∈ strictlyHeavySet design ↔ 1 < leverageOf (design.atom label) := by
  unfold strictlyHeavySet
  rw [Finset.mem_filter]
  exact ⟨fun hmem => hmem.2, fun hlt => ⟨Finset.mem_univ label, hlt⟩⟩

/-- **THE WEIGHTED GAP EXCESS TOTALS `rank - 1`.**  Parseval's trace minus the
weight total.  No hypothesis. -/
theorem sum_weight_mul_gapExcess {m k : ℕ} (design : WeightedDesign m k) :
    ∑ label : Fin m, design.weight label * (leverageOf (design.atom label) - 1)
      = (k : ℝ) - 1 := by
  have hsplit : ∑ label : Fin m, design.weight label * (leverageOf (design.atom label) - 1)
      = (∑ label : Fin m, design.weight label * leverageOf (design.atom label))
        - ∑ label : Fin m, design.weight label := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by ring
  rw [hsplit, sum_weight_mul_leverage design, design.weight_sum_one]

/-- Each weighted gap excess is at most the atom's weight deficit.  This is the
per-atom leverage cap, moved by one. -/
theorem weight_mul_gapExcess_le_one_sub_weight {m k : ℕ} (design : WeightedDesign m k)
    (label : Fin m) :
    design.weight label * (leverageOf (design.atom label) - 1) ≤ 1 - design.weight label := by
  have hcap := weighted_leverage_le_one design label
  have hexpand : design.weight label * (leverageOf (design.atom label) - 1)
      = design.weight label * leverageOf (design.atom label) - design.weight label := by ring
  rw [hexpand]
  linarith [hcap]

/-- **THE COUNTING BOUND.**  The rank minus one is at most the count of the
strictly heavy atoms minus their total weight.  Hypothesis free, at every rank
and every size. -/
theorem rank_sub_one_le_card_strictlyHeavySet_sub_weight {m k : ℕ}
    (design : WeightedDesign m k) :
    (k : ℝ) - 1
      ≤ ((strictlyHeavySet design).card : ℝ)
        - ∑ label ∈ strictlyHeavySet design, design.weight label := by
  classical
  have htotal := sum_weight_mul_gapExcess design
  have hsplit := Finset.sum_add_sum_compl (strictlyHeavySet design)
    (fun label => design.weight label * (leverageOf (design.atom label) - 1))
  have hcomplNonpos : ∑ label ∈ (strictlyHeavySet design)ᶜ,
      design.weight label * (leverageOf (design.atom label) - 1) ≤ 0 := by
    refine Finset.sum_nonpos fun label hlabel => ?_
    have hnotMem : label ∉ strictlyHeavySet design := Finset.mem_compl.mp hlabel
    have hle : leverageOf (design.atom label) ≤ 1 := by
      by_contra hgt
      exact hnotMem ((mem_strictlyHeavySet_iff design label).mpr (not_le.mp hgt))
    have hprod : 0 ≤ design.weight label * (1 - leverageOf (design.atom label)) :=
      mul_nonneg (design.weight_pos label).le (by linarith)
    linarith [hprod]
  have hheavyBound : ∑ label ∈ strictlyHeavySet design,
        design.weight label * (leverageOf (design.atom label) - 1)
      ≤ ∑ label ∈ strictlyHeavySet design, (1 - design.weight label) :=
    Finset.sum_le_sum fun label _ => weight_mul_gapExcess_le_one_sub_weight design label
  have hrhs : ∑ label ∈ strictlyHeavySet design, (1 - design.weight label)
      = ((strictlyHeavySet design).card : ℝ)
        - ∑ label ∈ strictlyHeavySet design, design.weight label := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith [htotal, hsplit, hcomplNonpos, hheavyBound, hrhs]

/-- **EVERY DESIGN CARRIES AT LEAST `rank` STRICTLY HEAVY ATOMS.**  At rank two
and up, with no primitivity, no all-heavy hypothesis and no pattern.  The mirror
of `Gtz.exists_leverage_le_rank`, and strictly finer than
`Gtz.exists_leverage_ge_rank`, which names ONE long atom. -/
-- AUDIT-DUPLICATE (2026-08-17): this law and the two that follow it (:291, :300)
-- are the DESIGN-COORDINATE twin of the chart-coordinate leverage laws in
-- Gtz/Wave/ThreeLinesSlideElimination.lean, namely `Gtz.three_le_card_overLevered`,
-- `Gtz.weight_lt_chartMassLeverage_of_posDef_gap` and
-- `Gtz.exists_posDef_threeLines_of_overLevered_triple`.  Same structure, two
-- coordinate systems, and NO bridging lemma between `strictlyHeavySet` and the
-- over-levered filter.  Measured: those are the only two copies in the tree.
-- AUDIT-ORPHAN (2026-08-17): this module scores ONE outward consumer across 61
-- declarations and 1027 lines.  The three laws named here have none.
theorem rank_le_card_strictlyHeavySet {m k : ℕ} (design : WeightedDesign m k) (hk : 2 ≤ k) :
    k ≤ (strictlyHeavySet design).card := by
  classical
  by_contra hsmall
  push Not at hsmall
  have hbound := rank_sub_one_le_card_strictlyHeavySet_sub_weight design
  have hstep : (strictlyHeavySet design).card + 1 ≤ k := hsmall
  have hcardReal : ((strictlyHeavySet design).card : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hstep
  have hweightNonpos : ∑ label ∈ strictlyHeavySet design, design.weight label ≤ 0 := by
    linarith [hbound, hcardReal]
  have hempty : strictlyHeavySet design = ∅ := by
    by_contra hne
    obtain ⟨label, hlabel⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hpos : 0 < ∑ other ∈ strictlyHeavySet design, design.weight other :=
      Finset.sum_pos (fun other _ => design.weight_pos other) ⟨label, hlabel⟩
    linarith [hpos, hweightNonpos]
  rw [hempty] at hbound
  simp only [Finset.card_empty, Nat.cast_zero, Finset.sum_empty, sub_zero] at hbound
  have hkReal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith [hbound, hkReal]

/-- Three of the six atoms of a `(6, 3)` design are strictly heavy. -/
theorem three_le_card_strictlyHeavySet_sixThree (design : WeightedDesign 6 3) :
    3 ≤ (strictlyHeavySet design).card :=
  rank_le_card_strictlyHeavySet design (by norm_num)

/-! ## 3. The strict dominator lives in the strictly heavy set

`Gtz.one_lt_leverage_of_mem_of_posDef` says every member of a strict card-three
dominator has leverage strictly above one.  Section 2 says at least three labels
qualify.  Together they confine the search, and at exactly three they remove it
entirely. -/

/-- **THE STRICT DOMINATOR IS STRICTLY HEAVY, MEMBER BY MEMBER.** -/
theorem subset_strictlyHeavySet_of_posDef {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hcard : selected.card = 3)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    selected ⊆ strictlyHeavySet design := fun label hlabel =>
  (mem_strictlyHeavySet_iff design label).mpr
    (one_lt_leverage_of_mem_of_posDef design selected hcard hlabel hposDef)

/-- **THREE STRICTLY HEAVY ATOMS LEAVE NO CHOICE.**  When exactly three labels
are strictly heavy, a strict card-three dominator IS that set. -/
theorem eq_strictlyHeavySet_of_posDef_of_card_eq_three {size : ℕ}
    (design : WeightedDesign size 3) (selected : Finset (Fin size)) (hcard : selected.card = 3)
    (hheavyCard : (strictlyHeavySet design).card = 3)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    selected = strictlyHeavySet design :=
  Finset.eq_of_subset_of_card_le (subset_strictlyHeavySet_of_posDef design selected hcard hposDef)
    (by rw [hcard, hheavyCard])

/-- **THE SELECTION IS GONE AT THREE.**  When exactly three atoms are strictly
heavy the existence of a strict card-three witness is the strict domination of
that one named triple.  No quantifier over subsets survives. -/
theorem exists_posDef_cardThree_iff_posDef_strictlyHeavySet {size : ℕ}
    (design : WeightedDesign size 3) (hheavyCard : (strictlyHeavySet design).card = 3) :
    (∃ selected : Finset (Fin size), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef)
      ↔ (subsetSum design (strictlyHeavySet design) - 1).PosDef := by
  constructor
  · rintro ⟨selected, hcard, hposDef⟩
    rwa [eq_strictlyHeavySet_of_posDef_of_card_eq_three design selected hcard hheavyCard hposDef]
      at hposDef
  · intro hposDef
    exact ⟨strictlyHeavySet design, hheavyCard, hposDef⟩

/-- The strictly heavy set is all-heavy, trivially. -/
theorem one_le_leverage_of_mem_strictlyHeavySet {m k : ℕ} (design : WeightedDesign m k)
    {label : Fin m} (hmem : label ∈ strictlyHeavySet design) :
    1 ≤ leverageOf (design.atom label) :=
  ((mem_strictlyHeavySet_iff design label).mp hmem).le

/-- **THE WHOLE QUESTION, AT ONE TRIPLE AND ONE BALANCE.**  When exactly three
atoms are strictly heavy, a design carries a strict card-three witness exactly
when the wedge balance holds at that triple, at every probe orthogonal to one
fixed unit normal.  Both the selection and the surplus are gone. -/
theorem exists_posDef_cardThree_iff_wedgeBalance_strictlyHeavySet {size : ℕ}
    (design : WeightedDesign size 3) (hheavyCard : (strictlyHeavySet design).card = 3)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    (∃ selected : Finset (Fin size), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef)
      ↔ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
          WedgeBalanceAt design (strictlyHeavySet design) unitNormal probeVec := by
  rw [exists_posDef_cardThree_iff_posDef_strictlyHeavySet design hheavyCard]
  exact posDef_iff_wedgeBalance_of_allHeavy design (strictlyHeavySet design) hheavyCard
    (fun label hlabel => one_le_leverage_of_mem_strictlyHeavySet design hlabel) unitNormal hunit

/-! ## 4. The light branch of `(6, 3)` is already paid

`Gtz.gtzWeighted_of_le_five` is unconditional, so the predecessor cell
`Gtz.GtzWeighted 5 3` is a THEOREM, and `Gtz.posDef_of_strictly_light_atom`
converts one strictly light atom into a strict card-three witness at size six.
The `(6, 3)` problem therefore splits with no hypothesis at all. -/

/-- The predecessor cell of `(6, 3)`, unconditional. -/
theorem gtzWeighted_five_three : GtzWeighted 5 3 :=
  gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)

/-- **THE LIGHT BRANCH, DISCHARGED.**  One atom of leverage strictly below one
hands back a strictly dominating triple at size six, with no further hypothesis.
The predecessor cell is spent here and never appears again. -/
theorem exists_posDef_cardThree_of_light (design : WeightedDesign 6 3)
    {lightLabel : Fin 6} (hlight : leverageOf (design.atom lightLabel) < 1) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef :=
  posDef_of_strictly_light_atom (m := 5) (k := 3) design (by norm_num) gtzWeighted_five_three
    lightLabel hlight

/-- **THE DICHOTOMY.**  Every `(6, 3)` design is all-heavy or already settled. -/
theorem allHeavy_or_exists_posDef_cardThree (design : WeightedDesign 6 3) :
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
      ∨ ∃ selected : Finset (Fin 6), selected.card = 3
          ∧ (subsetSum design selected - 1).PosDef := by
  by_cases hall : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)
  · exact Or.inl hall
  · refine Or.inr ?_
    obtain ⟨lightLabel, hlabel⟩ : ∃ lightLabel : Fin 6,
        leverageOf (design.atom lightLabel) < 1 := by
      by_contra hnone
      refine hall fun label => ?_
      by_contra hlt
      exact hnone ⟨label, not_le.mp hlt⟩
    exact exists_posDef_cardThree_of_light design hlabel

/-! ## 5. The residual, and the door

The residual of `(6, 3)` after sections 1 and 4 asks for ONE thing: a card-three
subset whose wedge balance holds at every probe orthogonal to the first
coordinate axis, at every PRIMITIVE ALL-HEAVY design.  It carries no surplus, no
trace test, no leak, no normal and no light branch. -/

/-- **THE ALL-HEAVY WEDGE SELECTOR.**  The residual of the whole rank-three
frontier, in one line. -/
def AllHeavyWedgeSelector : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ ![1, 0, 0] = 0 → probeVec ≠ 0 →
            WedgeBalanceAt design selected ![1, 0, 0] probeVec

/-- **THE RESIDUAL IS THE TARGET.**  An equivalence, so the selector is neither a
strengthening nor a weakening of `Gtz.ConsolidatedStrictTripleDesign`.  What it
removes is the surplus conjunct and the light branch, and those are removed
because they are proved, not because they are assumed away. -/
theorem allHeavyWedgeSelector_iff_consolidatedStrictTripleDesign :
    AllHeavyWedgeSelector ↔ ConsolidatedStrictTripleDesign := by
  constructor
  · intro hselector design hprimitive
    rcases allHeavy_or_exists_posDef_cardThree design with hall | hwitness
    · obtain ⟨selected, hcard, hbalance⟩ := hselector design hprimitive hall
      exact ⟨selected, hcard,
        posDef_of_three_le_sum_leverage_of_wedgeBalance design selected
          (three_le_sum_leverage_of_allHeavy design selected hcard fun label _ => hall label)
          ![1, 0, 0] dotProduct_firstAxis hbalance⟩
    · exact hwitness
  · intro hconsolidated design hprimitive _hall
    obtain ⟨selected, hcard, hposDef⟩ := hconsolidated design hprimitive
    exact ⟨selected, hcard,
      (forall_wedgeBalanceAt_iff_definite design selected ![1, 0, 0] dotProduct_firstAxis).mpr
        (Or.inl hposDef)⟩

/-- **THE DOOR.**  The all-heavy wedge selector retires all five on-path
obligations. -/
theorem allFiveOnPath_of_allHeavyWedgeSelector (hselector : AllHeavyWedgeSelector) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  allFiveOnPath_of_consolidatedStrictTripleDesign
    (allHeavyWedgeSelector_iff_consolidatedStrictTripleDesign.mp hselector)

/-- **THE SELECTOR, PINNED TO THE STRICTLY HEAVY SET.**  Section 2 confines the
witness, so the selector may quantify over subsets of the strictly heavy set
alone.  At six labels that set holds at least three, and when it holds exactly
three the selector has no choice left to make. -/
theorem allHeavyWedgeSelector_of_strictlyHeavyBalance
    (hproducer : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
        ∃ selected ⊆ strictlyHeavySet design, selected.card = 3
          ∧ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ ![1, 0, 0] = 0 → probeVec ≠ 0 →
              WedgeBalanceAt design selected ![1, 0, 0] probeVec) :
    AllHeavyWedgeSelector := by
  intro design hprimitive hall
  obtain ⟨selected, _hsubset, hcard, hbalance⟩ := hproducer design hprimitive hall
  exact ⟨selected, hcard, hbalance⟩

/-! ## 6. The general-rank hinge, consolidated

`Skeleton.obligationSubThresholdBandHinge` and
`Skeleton.obligationThresholdCellHingeRankFourAndUp` have the same shape: the
predecessor cell, then a tie, then a parallel pair.
`Gtz.hinge_of_predecessor_on_strictlyLightBranch` closes the strictly light
branch of both at every rank.  What is left of the two together is ONE all-heavy
statement, and this section proves each axiom shape from it. -/

/-- **THE ALL-HEAVY HINGE RESIDUAL.**  What both general-rank hinge obligations
still ask for, once the strictly light branch is spent. -/
def AllHeavyHingeResidual : Prop :=
  ∀ rank size : ℕ, 2 ≤ size → ∀ design : WeightedDesign size rank,
    (∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) →
      IsTie design → HasParallelPair design

/-- **THE HINGE, FROM THE ALL-HEAVY RESIDUAL ALONE.**  Exactly the shape both
obligations carry, with the light branch discharged by the predecessor cell. -/
theorem hasParallelPair_of_isTie_of_allHeavyHingeResidual (hresidual : AllHeavyHingeResidual)
    {size rank : ℕ} (hsize : 2 ≤ size) (hpredecessor : GtzWeighted (size - 1) rank)
    (design : WeightedDesign size rank) (htie : IsTie design) : HasParallelPair design := by
  by_cases hall : ∀ label : Fin size, 1 ≤ leverageOf (design.atom label)
  · exact hresidual rank size hsize design hall htie
  · obtain ⟨lightLabel, hlabel⟩ : ∃ lightLabel : Fin size,
        leverageOf (design.atom lightLabel) < 1 := by
      by_contra hnone
      refine hall fun label => ?_
      by_contra hlt
      exact hnone ⟨label, not_le.mp hlt⟩
    exact hinge_of_predecessor_on_strictlyLightBranch hsize hpredecessor design
      ⟨lightLabel, hlabel⟩ htie

/-- **THE SUB-THRESHOLD BAND HINGE, FROM THE ALL-HEAVY RESIDUAL.**  Written with
the size and rank bounds exactly as `Skeleton.obligationSubThresholdBandHinge`
carries them.  The registry records that axiom as having no live producer. -/
theorem subThresholdBandHinge_of_allHeavyHingeResidual (hresidual : AllHeavyHingeResidual) :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank, IsTie design → HasParallelPair design := by
  intro rank hrank size hlow _hhigh hpredecessor design htie
  exact hasParallelPair_of_isTie_of_allHeavyHingeResidual hresidual (by omega) hpredecessor
    design htie

/-- **THE THRESHOLD CELL HINGE AT RANK FOUR AND UP, FROM THE ALL-HEAVY
RESIDUAL.**  Written exactly as
`Skeleton.obligationThresholdCellHingeRankFourAndUp` carries it. -/
theorem thresholdCellHingeRankFourAndUp_of_allHeavyHingeResidual
    (hresidual : AllHeavyHingeResidual) :
    ∀ rank : ℕ, 4 ≤ rank →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor design htie
  refine hasParallelPair_of_isTie_of_allHeavyHingeResidual hresidual ?_ hpredecessor design htie
  have hfour : 2 * 2 ≤ rank * (rank + 1) := by
    have hstep : 4 * 1 ≤ rank * (rank + 1) := Nat.mul_le_mul hrank (by omega)
    simpa using hstep
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr hfour

/-! ## 7. The weak dominator upgrades two leverages at once

`Gtz.pairGapExcessOf_nonneg_of_dominates_flatPair` gives `0 <= pairGapExcessOf`
at the flat pair of a WEAK card-three dominator.  That is the product of two gap
excesses minus a squared pairing.  On the all-heavy stratum both excesses are
nonnegative, so a nonzero pairing forces both to be strictly positive.  A weak
dominator therefore upgrades `1 <= leverageOf` to `1 < leverageOf` at two labels
at once, and section 3 then places both inside the strictly heavy set. -/

/-- The pair gap excess of a rank-three design, in pair-cap vocabulary. -/
theorem pairGapExcessOf_eq_heavyExcess_minor {m : ℕ} (design : WeightedDesign m 3)
    (firstLabel secondLabel : Fin m) :
    pairGapExcessOf design firstLabel secondLabel
      = heavyExcess design firstLabel * heavyExcess design secondLabel
        - atomPairing design firstLabel secondLabel ^ 2 := rfl

/-- **THE WEAK-TO-STRICT UPGRADE.**  A nonnegative pair minor, two nonnegative
gap excesses and a nonzero pairing force both excesses strictly positive. -/
theorem gapExcess_pos_of_pairGapExcessOf_nonneg {m k : ℕ} (design : WeightedDesign m k)
    {firstLabel secondLabel : Fin m}
    (hfirst : 1 ≤ leverageOf (design.atom firstLabel))
    (hsecond : 1 ≤ leverageOf (design.atom secondLabel))
    (hpairing : design.atom firstLabel ⬝ᵥ design.atom secondLabel ≠ 0)
    (hminor : 0 ≤ pairGapExcessOf design firstLabel secondLabel) :
    1 < leverageOf (design.atom firstLabel) ∧ 1 < leverageOf (design.atom secondLabel) := by
  have hexpand : pairGapExcessOf design firstLabel secondLabel
      = (leverageOf (design.atom firstLabel) - 1) * (leverageOf (design.atom secondLabel) - 1)
        - (design.atom firstLabel ⬝ᵥ design.atom secondLabel) ^ 2 := rfl
  rw [hexpand] at hminor
  have hsquarePos : 0 < (design.atom firstLabel ⬝ᵥ design.atom secondLabel) ^ 2 :=
    (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hpairing))
  have hproductPos : 0 < (leverageOf (design.atom firstLabel) - 1)
      * (leverageOf (design.atom secondLabel) - 1) := by linarith [hminor, hsquarePos]
  constructor
  · by_contra hnot
    have hzero : leverageOf (design.atom firstLabel) - 1 = 0 := by
      have := not_lt.mp hnot
      linarith [hfirst, this]
    rw [hzero, zero_mul] at hproductPos
    exact absurd hproductPos (lt_irrefl 0)
  · by_contra hnot
    have hzero : leverageOf (design.atom secondLabel) - 1 = 0 := by
      have := not_lt.mp hnot
      linarith [hsecond, this]
    rw [hzero, mul_zero] at hproductPos
    exact absurd hproductPos (lt_irrefl 0)

/-- **THE FLAT PAIR OF A WEAK DOMINATOR IS STRICTLY HEAVY.**  On the all-heavy
stratum, with the two flat atoms independent and not orthogonal, both members of
the flat pair enter the strictly heavy set.  Every hypothesis is supplied by the
one-line and two-meeting-lines residuals, and the dominator is only WEAK. -/
theorem flatPair_mem_strictlyHeavySet_of_dominates {size rank : ℕ}
    (design : WeightedDesign size rank) {flatFirst flatSecond freeLabel : Fin size}
    (hFirstSecond : flatFirst ≠ flatSecond) (hFirstFree : flatFirst ≠ freeLabel)
    (hSecondFree : flatSecond ≠ freeLabel)
    (unitNormal : Fin rank → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hFirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hSecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hheavy : ∀ label : Fin size, 1 ≤ leverageOf (design.atom label))
    (hindependent : 0 < leverageOf (design.atom flatFirst) * leverageOf (design.atom flatSecond)
      - gapPairingOf design flatFirst flatSecond ^ 2)
    (hpairing : design.atom flatFirst ⬝ᵥ design.atom flatSecond ≠ 0)
    (hdominates : Dominates design {flatFirst, flatSecond, freeLabel}) :
    flatFirst ∈ strictlyHeavySet design ∧ flatSecond ∈ strictlyHeavySet design := by
  have hminor := pairGapExcessOf_nonneg_of_dominates_flatPair design hFirstSecond hFirstFree
    hSecondFree unitNormal hunit hFirstFlat hSecondFlat hindependent hdominates
  obtain ⟨hfirst, hsecond⟩ := gapExcess_pos_of_pairGapExcessOf_nonneg design
    (hheavy flatFirst) (hheavy flatSecond) hpairing hminor
  exact ⟨(mem_strictlyHeavySet_iff design flatFirst).mpr hfirst,
    (mem_strictlyHeavySet_iff design flatSecond).mpr hsecond⟩

/-! ## 8. The two line obligations, balance only

`Gtz.oneLine_and_twoMeetingLines_of_lineFlatSplitSelector` retires both line
axioms from one flat-split selector.  Section 1 supplies that selector from the
wedge balance alone, because both axioms hand over `1 <= leverageOf` at every
label.  So the two line residuals lose their surplus conjunct and their leak. -/

/-- **THE FLAT-SPLIT SELECTOR, FROM THE BALANCE ALONE.**  All-heavy plus one
balanced card-three subset. -/
theorem lineFlatSplitSelectorAt_of_allHeavy_of_wedgeBalance (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hbalance : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      WedgeBalanceAt design selected unitNormal probeVec) :
    LineFlatSplitSelectorAt design unitNormal :=
  lineFlatSplitSelectorAt_of_exists_posDef_cardThree design hunit hlineFlat
    ⟨selected, hcard,
      posDef_of_three_le_sum_leverage_of_wedgeBalance design selected
        (three_le_sum_leverage_of_allHeavy design selected hcard fun label _ => hheavy label)
        unitNormal hunit hbalance⟩

/-- **BOTH LINE OBLIGATIONS FROM ONE BALANCE.**  A design-level choice of a
card-three subset whose wedge balance holds at the line normal retires the
one-line residual and the two-meeting-lines residual together.  No surplus, no
lead, no leak and no sharp balance appear in the hypothesis. -/
theorem oneLine_and_twoMeetingLines_of_allHeavyLineBalance
    (hproducer : ∀ design : WeightedDesign 6 3, ∀ unitNormal : Fin 3 → ℝ,
      unitNormal ⬝ᵥ unitNormal = 1 →
      (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ unitNormal = 0) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
            WedgeBalanceAt design selected unitNormal probeVec) :
    OneLineTenthHeavyJointBlindLineSparse
      ∧ TwoMeetingLinesTenthHeavyJointBlindTransversal := by
  refine oneLine_and_twoMeetingLines_of_lineFlatSplitSelector ?_
  intro design unitNormal hunit hlineFlat hheavy hcapBlind hweak
  obtain ⟨selected, hcard, hbalance⟩ :=
    hproducer design unitNormal hunit hlineFlat hheavy hcapBlind hweak
  exact lineFlatSplitSelectorAt_of_allHeavy_of_wedgeBalance design hunit hlineFlat hheavy
    hcard hbalance

/-! ## 9. A WEAK dominator already pays the trace threshold

Section 1 asks for a leverage total of at least three.  A weak dominator supplies
it with nothing else: the gap of a dominating subset is positive SEMIdefinite, so
its value at each coordinate axis is nonnegative, and the three axis readings
total the leverage of the subset minus the rank.

So the threshold is free wherever a weak dominator is handed over, and it is
handed over by four of the five on-path obligations and by the definition of a
tie.  No all-heavy hypothesis, no primitivity and no pattern are used. -/

/-- **A WEAK DOMINATOR TOTALS AT LEAST THREE.**  The rank-three reading of the
landed general-rank trace test `Gtz.rank_le_sum_leverage_of_dominates`, which had
no consumer in the wedge lane.  The trace of a positive semidefinite gap is
nonnegative, and the gap of a subset has trace `sum of the leverages - rank`. -/
theorem three_le_sum_leverage_of_dominates {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hdominates : Dominates design selected) :
    (3 : ℝ) ≤ ∑ label ∈ selected, leverageOf (design.atom label) := by
  exact_mod_cast rank_le_sum_leverage_of_dominates design selected hdominates

/-- **THE WEAK-TO-STRICT ENGINE.**  A WEAK dominator whose wedge balance holds at
every in-plane probe of one unit normal is a STRICT dominator.

This is the shape four of the five on-path obligations ask for.  Each hands over
a card-three subset with `Gtz.Dominates` and asks for a positive definite gap.
The only thing still missing is one strict inequality per in-plane direction, and
neither a surplus, nor a trace test, nor a leak, nor a leverage floor appears
anywhere in the hypothesis. -/
theorem posDef_of_dominates_of_wedgeBalance {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hdominates : Dominates design selected)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hbalance : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      WedgeBalanceAt design selected unitNormal probeVec) :
    (subsetSum design selected - 1).PosDef :=
  posDef_of_three_le_sum_leverage_of_wedgeBalance design selected
    (three_le_sum_leverage_of_dominates design selected hdominates) unitNormal hunit hbalance

/-- **THE WEAK-TO-STRICT ENGINE IS AN EQUIVALENCE.**  At a weak dominator, strict
domination IS the wedge balance.  Nothing is lost in either direction. -/
theorem posDef_iff_wedgeBalance_of_dominates {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hdominates : Dominates design selected)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    (subsetSum design selected - 1).PosDef
      ↔ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
          WedgeBalanceAt design selected unitNormal probeVec := by
  constructor
  · intro hposDef
    exact (forall_wedgeBalanceAt_iff_definite design selected unitNormal hunit).mpr
      (Or.inl hposDef)
  · exact posDef_of_dominates_of_wedgeBalance design selected hdominates unitNormal hunit

/-- **ONE BALANCED WEAK DOMINATOR KILLS A TIE.** -/
theorem not_isTie_of_dominates_of_wedgeBalance {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hcard : selected.card = 3)
    (hdominates : Dominates design selected)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hbalance : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      WedgeBalanceAt design selected unitNormal probeVec) :
    ¬ IsTie design := fun htie =>
  htie.2 selected hcard
    (posDef_of_dominates_of_wedgeBalance design selected hdominates unitNormal hunit hbalance)

/-! ## 10. The tie side of `(6, 3)`, unconditional

`Gtz.forall_one_le_leverage_of_isTie` needs the predecessor cell.  Section 4
supplies it at size six from `Gtz.gtzWeighted_of_le_five`, so the whole tie side
of `(6, 3)` becomes unconditional. -/

/-- **EVERY `(6, 3)` TIE IS ALL-HEAVY.**  Unconditional.  The predecessor cell is
a theorem, so a tie cannot hold an atom of leverage strictly below one. -/
theorem forall_one_le_leverage_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label) :=
  forall_one_le_leverage_of_isTie (predSize := 5) (rank := 3) design (by norm_num)
    gtzWeighted_five_three htie

/-- **A `(6, 3)` TIE REFUSES THE BALANCE EVERYWHERE.**  At every card-three
subset and every unit normal.  This is the exact refusal the tie locus carries,
and it needs no hypothesis at all. -/
theorem not_forall_wedgeBalanceAt_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    ¬ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
        WedgeBalanceAt design selected unitNormal probeVec := by
  intro hbalance
  exact htie.2 selected hcard
    ((posDef_iff_wedgeBalance_of_allHeavy design selected hcard
        (fun label _ => forall_one_le_leverage_of_isTie_sixThree design htie label)
        unitNormal hunit).mpr hbalance)

/-- **A `(6, 3)` TIE HAS AT LEAST THREE STRICTLY HEAVY ATOMS, AND EVERY ONE OF ITS
BALANCED CANDIDATES IS INSIDE THEM.**  Section 2 counts, section 3 confines. -/
theorem three_le_card_strictlyHeavySet_of_isTie (design : WeightedDesign 6 3)
    (_htie : IsTie design) : 3 ≤ (strictlyHeavySet design).card :=
  three_le_card_strictlyHeavySet_sixThree design

/-! ## 11. The residual of the deciding cell, and the capstone

`Gtz.HingeHoldsAtSize 6 3` is the deciding cell of rank three:
`Gtz.gtzWeightedAll_three_of_hinge` turns it into all of rank three, and
`Gtz.consolidatedStrictTripleDesign_iff_hingeHoldsAtSize_six_three` says the
design selector IS that cell.

Section 9 reduces the cell to ONE statement about ties: a primitive tie has a
BALANCED weak dominating triple.  The `Gtz.IsTie` antecedent is what makes the
reduction an equivalence, and it is recorded here rather than hidden: a version
without that antecedent would be strictly stronger, because a primitive design
may carry an unbalanced weak dominator alongside a strict triple elsewhere. -/

/-- **THE RESIDUAL OF THE DECIDING CELL.**  A primitive tie has a weak dominating
triple whose wedge balance holds at every probe orthogonal to the first
coordinate axis.  No surplus, no trace test, no leak, no leverage floor, no
pattern, no chart and no selection: the triple is handed over by the tie. -/
def TieDominatorBalanceResidual : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design → IsTie design →
    ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected →
      ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ ![1, 0, 0] = 0 → probeVec ≠ 0 →
        WedgeBalanceAt design selected ![1, 0, 0] probeVec

/-- **THE RESIDUAL DECIDES RANK THREE.** -/
theorem hingeHoldsAtSize_six_three_of_tieDominatorBalanceResidual
    (hresidual : TieDominatorBalanceResidual) : HingeHoldsAtSize 6 3 := by
  intro design htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  obtain ⟨weakDominator, hcard, hdominates⟩ := htie.1
  exact htie.2 weakDominator hcard
    (posDef_of_dominates_of_wedgeBalance design weakDominator hdominates ![1, 0, 0]
      dotProduct_firstAxis
      (hresidual design hprimitive htie weakDominator hcard hdominates))

/-- **AND IT IS EXACTLY THE DECIDING CELL.**  The converse is vacuous, and that
is the honest content: the cell asserts the primitive tie locus is empty, so the
residual quantifies over an empty family exactly when the cell holds. -/
theorem tieDominatorBalanceResidual_of_hinge (hhinge : HingeHoldsAtSize 6 3) :
    TieDominatorBalanceResidual := by
  intro design hprimitive htie _selected _hcard _hdominates _probeVec _hperp _hne
  exact absurd (hhinge design htie)
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)

theorem tieDominatorBalanceResidual_iff_hingeHoldsAtSize_six_three :
    TieDominatorBalanceResidual ↔ HingeHoldsAtSize 6 3 :=
  ⟨hingeHoldsAtSize_six_three_of_tieDominatorBalanceResidual,
    tieDominatorBalanceResidual_of_hinge⟩

/-- **THE `(6, 3)` CELL FROM THE RESIDUAL.** -/
theorem gtzWeighted_six_three_of_tieDominatorBalanceResidual
    (hresidual : TieDominatorBalanceResidual) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_hinge
    (hingeHoldsAtSize_six_three_of_tieDominatorBalanceResidual hresidual)

/-- **ALL OF RANK THREE FROM THE RESIDUAL.** -/
theorem gtzWeightedAll_three_of_tieDominatorBalanceResidual
    (hresidual : TieDominatorBalanceResidual) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_hinge
    (hingeHoldsAtSize_six_three_of_tieDominatorBalanceResidual hresidual)

/-- **THE 1997 STATEMENT AT RANK THREE, FROM ONE WEDGE BALANCE.**  Root A of the
campaign, reached from a single strict inequality per in-plane direction at the
weak dominating triple of a primitive tie. -/
theorem forall_gtzOriginal_rank_three_of_tieDominatorBalanceResidual
    (hresidual : TieDominatorBalanceResidual) : ∀ size : ℕ, 0 < size → GtzOriginal size 3 :=
  gtz_original_rank_three_of_six_three
    (gtzWeighted_six_three_of_tieDominatorBalanceResidual hresidual)

/-! ## 12. The all-heavy selector reaches the same capstone

Section 5 built `Gtz.AllHeavyWedgeSelector` out of the light-heavy dichotomy.
It is equivalent to the design selector, so it is equivalent to the deciding
cell, and it reaches rank three at every size by the same three landed bridges. -/

theorem hingeHoldsAtSize_six_three_of_allHeavyWedgeSelector
    (hselector : AllHeavyWedgeSelector) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_six_three_of_consolidatedStrictTripleDesign
    (allHeavyWedgeSelector_iff_consolidatedStrictTripleDesign.mp hselector)

/-- **THE ALL-HEAVY SELECTOR IS THE DECIDING CELL.** -/
theorem allHeavyWedgeSelector_iff_hingeHoldsAtSize_six_three :
    AllHeavyWedgeSelector ↔ HingeHoldsAtSize 6 3 :=
  allHeavyWedgeSelector_iff_consolidatedStrictTripleDesign.trans
    consolidatedStrictTripleDesign_iff_hingeHoldsAtSize_six_three

theorem gtzWeighted_six_three_of_allHeavyWedgeSelector
    (hselector : AllHeavyWedgeSelector) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_hinge (hingeHoldsAtSize_six_three_of_allHeavyWedgeSelector hselector)

theorem gtzWeightedAll_three_of_allHeavyWedgeSelector
    (hselector : AllHeavyWedgeSelector) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_hinge (hingeHoldsAtSize_six_three_of_allHeavyWedgeSelector hselector)

/-- **THE 1997 STATEMENT AT RANK THREE, FROM THE ALL-HEAVY SELECTOR.** -/
theorem forall_gtzOriginal_rank_three_of_allHeavyWedgeSelector
    (hselector : AllHeavyWedgeSelector) : ∀ size : ℕ, 0 < size → GtzOriginal size 3 :=
  gtz_original_rank_three_of_six_three (gtzWeighted_six_three_of_allHeavyWedgeSelector hselector)

/-- **THE TWO RESIDUALS ARE THE SAME STATEMENT.**  Both are the deciding cell, so
neither is a weakening of the other, and a proof of either closes rank three. -/
theorem allHeavyWedgeSelector_iff_tieDominatorBalanceResidual :
    AllHeavyWedgeSelector ↔ TieDominatorBalanceResidual :=
  allHeavyWedgeSelector_iff_hingeHoldsAtSize_six_three.trans
    tieDominatorBalanceResidual_iff_hingeHoldsAtSize_six_three.symm

/-! ## 13. The line-free obligation, closed by one balance at the pinned triple

`Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual` hands over
`Gtz.Dominates design {0, 1, 2}` and, three hypotheses later, the refusal
`¬ (subsetSum design {0, 1, 2} - 1).PosDef`.  Section 9 turns the first into the
second's negation as soon as the base triple is balanced.  So the whole
obligation reduces to ONE wedge balance at ONE named triple. -/

/-- **THE LINE-FREE OBLIGATION FROM ONE WEDGE BALANCE.**  A design whose base
triple weakly dominates and which carries no strict card-three witness at all
has a balanced base triple, and that alone retires the obligation.  The producer
receives the weak domination and the no-strict ledger, which are two of the
obligation's own hypotheses. -/
theorem baseTripleTightLineFreeOffConicHeavyNeedleResidual_of_baseTripleWedgeBalance
    (hbalance : ∀ design : WeightedDesign 6 3,
      Dominates design ({0, 1, 2} : Finset (Fin 6)) →
      (∀ selected : Finset (Fin 6), selected.card = 3 →
        ¬ (subsetSum design selected - 1).PosDef) →
      ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ ![1, 0, 0] = 0 → probeVec ≠ 0 →
        WedgeBalanceAt design ({0, 1, 2} : Finset (Fin 6)) ![1, 0, 0] probeVec) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual := by
  intro design _tightDir _weakDir _hpattern _hquadric hdominates _htightNe _htightNull
    _hweakNe _hweakBound _htightBound _hshareLow _hshareHigh _hdiscriminant hnotPosDef
    _hbaseResidual _hlightTriple _hheavyLabel hnoStrict _hcapLow _hcapHigh _hprobeBudget
  exact hnotPosDef
    (posDef_of_dominates_of_wedgeBalance design ({0, 1, 2} : Finset (Fin 6)) hdominates
      ![1, 0, 0] dotProduct_firstAxis (hbalance design hdominates hnoStrict))

/-! ## 15. The two line obligations, closed by the weak dominator's own balance

Section 8 asked for a balanced card-three subset and used the all-heavy
hypothesis to reach strict domination.  Section 9 removes even that: the two
line obligations hand over a WEAK dominator, and its balance alone is enough.
The residual of both is now one strict inequality per in-plane direction, read
at the subset the obligation itself supplies. -/

/-- **BOTH LINE OBLIGATIONS FROM THE WEAK DOMINATOR'S BALANCE.**  The sharpest
form available: no surplus, no trace test, no leak, no leverage floor and no
selection.  The triple is the one the obligation already carries. -/
theorem oneLine_and_twoMeetingLines_of_dominatorWedgeBalance
    (hproducer : ∀ design : WeightedDesign 6 3, ∀ unitNormal : Fin 3 → ℝ,
      unitNormal ⬝ᵥ unitNormal = 1 →
      (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ unitNormal = 0) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      ∀ dominator : Finset (Fin 6), dominator.card = 3 → Dominates design dominator →
        ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
          WedgeBalanceAt design dominator unitNormal probeVec) :
    OneLineTenthHeavyJointBlindLineSparse
      ∧ TwoMeetingLinesTenthHeavyJointBlindTransversal := by
  refine oneLine_and_twoMeetingLines_of_lineFlatSplitSelector ?_
  intro design unitNormal hunit hlineFlat hheavy hcapBlind hweak
  obtain ⟨dominator, hcard, hdominates⟩ := hweak
  exact lineFlatSplitSelectorAt_of_exists_posDef_cardThree design hunit hlineFlat
    ⟨dominator, hcard,
      posDef_of_dominates_of_wedgeBalance design dominator hdominates unitNormal hunit
        (hproducer design unitNormal hunit hlineFlat hheavy hcapBlind dominator hcard
          hdominates)⟩

/-! ## 15. Primitivity supplies the independence, and kills the unit atom

Section 7 asked the two flat atoms to be independent.  At rank three primitivity
gives that for free, because a nonzero wedge has positive energy and that energy
IS the pair Gram determinant.  With independence free, the weak dominator law
reads two ways.

Positively, a non-orthogonal flat pair inside a weak card-three dominator is
strictly heavy at both members.  Negatively, such a pair can hold no atom of
leverage exactly one.  So on the all-heavy stratum a UNIT atom is barred from
every weak dominator that carries it in a non-orthogonal flat pair, and the
one-line and two-meeting-lines obligations both present exactly that shape. -/

/-- **PRIMITIVITY IS PAIR INDEPENDENCE.**  At rank three the pair Gram
determinant of two distinct atoms of a primitive design is strictly positive,
because it is the energy of their nonzero wedge. -/
theorem pairGramDet_pos_of_primitive {size : ℕ} (design : WeightedDesign size 3)
    (hprimitive : IsPrimitiveDesign design) {leftLabel rightLabel : Fin size}
    (hne : leftLabel ≠ rightLabel) :
    0 < leverageOf (design.atom leftLabel) * leverageOf (design.atom rightLabel)
      - gapPairingOf design leftLabel rightLabel ^ 2 := by
  have hwedgeNe : atomWedge (design.atom leftLabel) (design.atom rightLabel) ≠ 0 :=
    atomWedge_ne_zero_of_primitive design hprimitive hne
  have hpositive : 0 < atomWedge (design.atom leftLabel) (design.atom rightLabel)
      ⬝ᵥ atomWedge (design.atom leftLabel) (design.atom rightLabel) :=
    dotProduct_self_pos hwedgeNe
  rw [atomWedge_energy] at hpositive
  have hleft : leverageOf (design.atom leftLabel)
      = design.atom leftLabel ⬝ᵥ design.atom leftLabel :=
    leverageOf_eq_dotProduct (design.atom leftLabel)
  have hright : leverageOf (design.atom rightLabel)
      = design.atom rightLabel ⬝ᵥ design.atom rightLabel :=
    leverageOf_eq_dotProduct (design.atom rightLabel)
  have hpair : gapPairingOf design leftLabel rightLabel
      = design.atom leftLabel ⬝ᵥ design.atom rightLabel := rfl
  rw [hleft, hright, hpair]
  linarith [hpositive]

/-- **THE PAIR MINOR OF A PRIMITIVE WEAK DOMINATOR'S FLAT PAIR IS NONNEGATIVE.**
The landed `Gtz.pairGapExcessOf_nonneg_of_dominates_flatPair` with its
independence hypothesis discharged. -/
theorem pairGapExcessOf_nonneg_of_dominates_flatPair_of_primitive {size : ℕ}
    (design : WeightedDesign size 3) (hprimitive : IsPrimitiveDesign design)
    {flatFirst flatSecond freeLabel : Fin size}
    (hFirstSecond : flatFirst ≠ flatSecond) (hFirstFree : flatFirst ≠ freeLabel)
    (hSecondFree : flatSecond ≠ freeLabel)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hFirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hSecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hdominates : Dominates design {flatFirst, flatSecond, freeLabel}) :
    0 ≤ pairGapExcessOf design flatFirst flatSecond :=
  pairGapExcessOf_nonneg_of_dominates_flatPair design hFirstSecond hFirstFree hSecondFree
    unitNormal hunit hFirstFlat hSecondFlat
    (pairGramDet_pos_of_primitive design hprimitive hFirstSecond) hdominates

/-- **THE WEAK-TO-STRICT UPGRADE, WITH EVERY SIDE CONDITION DISCHARGED.**  On the
all-heavy stratum of a primitive design, a non-orthogonal flat pair inside a weak
card-three dominator has BOTH members strictly heavy.  Every hypothesis except
the nonzero pairing is handed over by the two line obligations. -/
theorem flatPair_strictlyHeavy_of_dominates_of_primitive {size : ℕ}
    (design : WeightedDesign size 3) (hprimitive : IsPrimitiveDesign design)
    {flatFirst flatSecond freeLabel : Fin size}
    (hFirstSecond : flatFirst ≠ flatSecond) (hFirstFree : flatFirst ≠ freeLabel)
    (hSecondFree : flatSecond ≠ freeLabel)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hFirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hSecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hheavy : ∀ label : Fin size, 1 ≤ leverageOf (design.atom label))
    (hpairing : design.atom flatFirst ⬝ᵥ design.atom flatSecond ≠ 0)
    (hdominates : Dominates design {flatFirst, flatSecond, freeLabel}) :
    flatFirst ∈ strictlyHeavySet design ∧ flatSecond ∈ strictlyHeavySet design :=
  flatPair_mem_strictlyHeavySet_of_dominates design hFirstSecond hFirstFree hSecondFree
    unitNormal hunit hFirstFlat hSecondFlat hheavy
    (pairGramDet_pos_of_primitive design hprimitive hFirstSecond) hpairing hdominates

/-- **A UNIT ATOM CANNOT SIT IN A NON-ORTHOGONAL FLAT PAIR OF A WEAK DOMINATOR.**
The negative reading, and it needs no all-heavy hypothesis: a member of leverage
exactly one forces the pair minor to be minus a positive square, which the weak
domination law forbids. -/
theorem not_dominates_of_flat_unitAtom_of_primitive {size : ℕ}
    (design : WeightedDesign size 3) (hprimitive : IsPrimitiveDesign design)
    {flatFirst flatSecond freeLabel : Fin size}
    (hFirstSecond : flatFirst ≠ flatSecond) (hFirstFree : flatFirst ≠ freeLabel)
    (hSecondFree : flatSecond ≠ freeLabel)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hFirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hSecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hunitLeverage : leverageOf (design.atom flatFirst) = 1)
    (hpairing : design.atom flatFirst ⬝ᵥ design.atom flatSecond ≠ 0) :
    ¬ Dominates design {flatFirst, flatSecond, freeLabel} := by
  intro hdominates
  have hminor := pairGapExcessOf_nonneg_of_dominates_flatPair_of_primitive design hprimitive
    hFirstSecond hFirstFree hSecondFree unitNormal hunit hFirstFlat hSecondFlat hdominates
  have hexpand : pairGapExcessOf design flatFirst flatSecond
      = (leverageOf (design.atom flatFirst) - 1) * (leverageOf (design.atom flatSecond) - 1)
        - (design.atom flatFirst ⬝ᵥ design.atom flatSecond) ^ 2 := rfl
  rw [hexpand, hunitLeverage] at hminor
  have hsquarePos : 0 < (design.atom flatFirst ⬝ᵥ design.atom flatSecond) ^ 2 :=
    (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hpairing))
  simp only [sub_self, zero_mul, zero_sub, neg_nonneg] at hminor
  linarith [hminor, hsquarePos]

/-! ## 16. The pair-cap sandwich

`Gtz.IsCapBlindSpot` is a hypothesis of both line obligations, and it caps the
pair minor of every pair from ABOVE.  Section 7 floors the same minor at the flat
pair of the weak dominator.  The two bounds are recorded together here: they read
the SAME scalar, in two vocabularies that the tree keeps apart. -/

/-- The pair gap excess of a rank-three design, in pair-cap vocabulary. -/
theorem pairGapExcessOf_eq_heavyExcess_pairMinor {m : ℕ} (design : WeightedDesign m 3)
    (firstLabel secondLabel : Fin m) :
    pairGapExcessOf design firstLabel secondLabel
      = heavyExcess design firstLabel * heavyExcess design secondLabel
        - atomPairing design firstLabel secondLabel ^ 2 := rfl

/-- **THE SANDWICH.**  Inside the joint blind spot of the two line obligations,
the pair minor of the weak dominator's flat pair is nonnegative and capped.  Both
sides are landed and neither had a consumer. -/
theorem pairGapExcessOf_sandwich_of_dominates_flatPair {size : ℕ}
    (design : WeightedDesign size 3) (hprimitive : IsPrimitiveDesign design)
    (hcapBlind : IsCapBlindSpot design)
    {flatFirst flatSecond freeLabel : Fin size}
    (hFirstSecond : flatFirst ≠ flatSecond) (hFirstFree : flatFirst ≠ freeLabel)
    (hSecondFree : flatSecond ≠ freeLabel)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hFirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hSecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hdominates : Dominates design {flatFirst, flatSecond, freeLabel}) :
    0 ≤ pairGapExcessOf design flatFirst flatSecond
      ∧ 2 * (design.weight flatFirst + design.weight flatSecond)
            * pairGapExcessOf design flatFirst flatSecond
          ≤ (1 - design.weight flatSecond) * heavyExcess design flatFirst
            + (1 - design.weight flatSecond) * heavyExcess design flatSecond
              + (design.weight flatSecond - design.weight flatFirst)
                * heavyExcess design flatSecond := by
  refine ⟨pairGapExcessOf_nonneg_of_dominates_flatPair_of_primitive design hprimitive
    hFirstSecond hFirstFree hSecondFree unitNormal hunit hFirstFlat hSecondFlat hdominates, ?_⟩
  have hcap := hcapBlind flatFirst flatSecond hFirstSecond
  rw [pairGapExcessOf_eq_heavyExcess_pairMinor]
  linarith [hcap]

end Gtz

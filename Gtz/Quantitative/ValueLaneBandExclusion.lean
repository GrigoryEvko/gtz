/-
# The value lane at `(6,3)`: the slogan is free, the all-floors covering IS the cell,
# and what remains is a band exclusion at ONE explicit width

Gap 4 of the campaign ledger reads "quantitative bridge, value lane -- ABSENT.  The
`C eps^2` law is Tier-E only; neither the law nor a consumer exists in Lean; the
precise closing implication has never been stated."  This file states it, and in
doing so retires the slogan the lane was built on.

## 1.  The slogan is a theorem, and therefore closes nothing

`Gtz/Quantitative/SixThreeExclusionFrontier.lean:126-135` names "a LOWER BOUND ON
`|chartObjective|` at a crux" as the single highest-value missing inequality, the
chain being that `Gtz.weight_ge_neg_value_of_isChartStationaryData` turns any such
bound into a weight floor at every atom, after which a floored covering fires.

The field `isChartMinimiser` makes every crux a GLOBAL minimiser of ONE objective
over ONE domain, so all cruxes carry the SAME chart value
(`SixThreeCrux.chartObjective_eq`), and `hasNegativeChartValue` already makes that
shared value strictly negative.  Hence
`SixThreeCrux.exists_pos_forall_le_neg_chartObjective`: a positive lower bound valid
at every crux exists the moment one crux does.  What the chain consumes is not the
EXISTENCE of the bound but an EXPLICIT value for it, and section 2 says why.

## 2.  Quantified over all floors, the floored covering IS the open cell

The crux supplies its own floor at the unknown height `-chartObjective`
(`SixThreeCrux.hasWeightFloor_neg_chartObjective`), so a floored covering usable
there must hold at EVERY positive floor -- and
`forall_weightFlooredCovering_iff_gtzWeighted_six_three` proves the all-floors
statement is LOGICALLY EQUIVALENT to `Gtz.GtzWeighted 6 3`.  The forward direction
is the only content: a design's own minimum weight is a positive floor it satisfies.

The same collapse holds for the tree's OWN floored predicate.
`forall_flooredSpreadCovering_iff_gtzWeighted_six_three` proves that
`Gtz.FlooredSpreadCovering 0 floor` at every positive floor is again equivalent to
the cell, through `Gtz.rank_three_of_heavy_six_three`.  So the collapse is a
property of the all-floors quantifier, not of the particular covering notion.

## 3.  The shape that does close, at ONE explicit band

`isEmpty_sixThreeCrux_of_bandExclusion_of_flooredSpreadCovering` is the honest
assembly.  At one explicit rational `band` it needs

  * `ChartValueBandExclusion band` -- no crux has chart value above `-band`; this is
    the a-priori form of gap 2, and the landed
    `Gtz.SixThreeCrux.neg_four_div_twentySeven_le_chartObjective` bounds the value
    from BELOW, which is the other direction; and
  * `Gtz.FlooredSpreadCovering 0 band` -- the tree's own shipped predicate at zero
    spread, which by `hasSpreadAtLeast_zero` is no restriction at all.

Neither implies the other, and each is strictly weaker than the cell.

## 4.  The band range is exactly `(0, 4/27]`, and there the covering is TIGHT

`isEmpty_sixThreeCrux_of_bandExclusion_of_four_div_twentySeven_lt` shows a band
exclusion above `4/27` contradicts the shipped value window on its own, so it is not
a sub-goal but the whole cell.  On the surviving range the second ingredient carries
no margin: `Gtz.splitTetraDesign_balanced_hasWeightFloor` puts the balanced split
tetrahedron -- an exact tie -- inside the `1/8`-floored family, and
`Gtz/Quantitative/FlooredSpreadRegion.lean:411-414` already records in the tree's own
words that "the floor alone does NOT remove it ... the spread parameter is doing work
the floor cannot do".  Since `4/27 < 1/6` and a `(6,3)` tie is known at uniform
weights `1/6`, no floor at or below the useful range gives the covering slack.

WHAT THIS DOES NOT DO.  It does not close `Gtz.GtzWeighted 6 3`, it supplies neither
ingredient, and it deliberately states NO `C eps^2` margin law: that law is measured
FALSE, the floored chart minimum being zero on the whole feasible floor range.  What
the file adds is that the lane's target is now a single explicit number with a known
admissible range, and that the two ways of reading the old slogan are both settled --
one as a theorem, one as the cell.
-/
import Mathlib
import Gtz.Quantitative.ChartStationary
import Gtz.Quantitative.FlooredSpreadRegion
import Gtz.Quantitative.PositivstellensatzRankThree
import Gtz.Quantitative.SixThreeExclusionFrontier
import Gtz.Quantitative.SpreadCertificateSixThree
import Gtz.Reduction.StressWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

/-! ## 1.  The slogan is free, because all cruxes carry one value -/

/-- **ALL CRUXES CARRY THE SAME CHART VALUE.**  Each is a global minimiser of the same
objective over the same closed domain, so the two minimisers bound each other.  This is
why "there is a positive lower bound on `|chartObjective|` at a crux" is not an open
inequality: with `hasNegativeChartValue` it is discharged by the shared value itself. -/
theorem SixThreeCrux.chartObjective_eq (first second : SixThreeCrux) :
    chartObjective (chartPointOfDesign first.design)
      = chartObjective (chartPointOfDesign second.design) :=
  le_antisymm (first.isChartMinimiser _) (second.isChartMinimiser _)

/-- The shared value is strictly negative, so `-chartObjective` is a positive number --
the "`eps`" of the slogan, available at once. -/
theorem SixThreeCrux.pos_neg_chartObjective (crux : SixThreeCrux) :
    0 < -chartObjective (chartPointOfDesign crux.design) :=
  neg_pos.mpr crux.hasNegativeChartValue

/-- **THE SLOGAN, DISCHARGED.**  A positive lower bound on `|chartObjective|` valid at
EVERY crux exists as soon as one crux does.  Compare
`Gtz/Quantitative/SixThreeExclusionFrontier.lean:126-135`, which names such a bound as the
highest-value missing inequality: the missing thing is not the bound, it is an EXPLICIT
value for it. -/
theorem SixThreeCrux.exists_pos_forall_le_neg_chartObjective (crux : SixThreeCrux) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ other : SixThreeCrux,
      bound ≤ -chartObjective (chartPointOfDesign other.design) :=
  ⟨-chartObjective (chartPointOfDesign crux.design), crux.pos_neg_chartObjective,
    fun other => le_of_eq (congrArg Neg.neg (crux.chartObjective_eq other))⟩

/-! ## 2.  The crux supplies its own weight floor -/

/-- **THE SELF-REFERENTIAL FLOOR.**  The shipped
`Gtz.weight_ge_neg_value_of_isChartStationaryData`, read at the crux's own stationarity
bundle: every weight is at least `-chartObjective`.  The floor is therefore not something
a lower bound has to CREATE -- it is already there, at the unknown height
`-chartObjective`, which is exactly why a floored covering has to be available at an
unknown floor, and section 3 shows what that costs. -/
theorem SixThreeCrux.hasWeightFloor_neg_chartObjective (crux : SixThreeCrux) :
    HasWeightFloor crux.design (-chartObjective (chartPointOfDesign crux.design)) := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  exact fun atomIndex => weight_ge_neg_value_of_isChartStationaryData hdata atomIndex

/-! ## 3.  The floored covering, and the theorem that it is not a lever -/

/-- **THE FLOORED COVERING AT ONE EXPLICIT FLOOR.**  Every `(6,3)` design all of whose
weights are at least `floor` has a dominating triple.

This is `Gtz.GtzWeighted 6 3` restricted to the `floor`-floored family.  It is STRICTLY
STRONGER than the tree's shipped `Gtz.FlooredSpreadCovering spread floor`, which asks the
same of designs that are additionally all-heavy and spread-bounded, and phrases the
conclusion through the two `S_3`-invariant legs; `flooredSpreadCovering_of_weightFlooredCovering`
is that implication.  The weaker shipped predicate is the better ingredient, and the
assembly in section 4 uses it. -/
def WeightFlooredCovering (floor : ℝ) : Prop :=
  ∀ D : WeightedDesign 6 3, HasWeightFloor D floor →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates D selected

/-- Raising the floor shrinks the family, so the covering at the higher floor is the
weaker statement. -/
theorem weightFlooredCovering_mono {floor higherFloor : ℝ} (hle : floor ≤ higherFloor)
    (hcovering : WeightFlooredCovering floor) : WeightFlooredCovering higherFloor :=
  fun D hfloor => hcovering D (hasWeightFloor_mono hle hfloor)

/-- The unrestricted cell implies the covering at every floor -- the trivial direction. -/
theorem weightFlooredCovering_of_gtzWeighted (floor : ℝ) (hcell : GtzWeighted 6 3) :
    WeightFlooredCovering floor :=
  fun D _ => hcell D

/-- **THE TRIVIALITY THEOREM.**  Quantified over all positive floors, the floored covering
is LOGICALLY EQUIVALENT to the open cell.  The forward direction is the only content: a
design's own minimum weight is a positive floor it satisfies, so the all-floors law applies
to every design.

Consequence for the lane: no proof of a floored covering "for all `eps > 0`" can be easier
than the cell, and a self-referential floor -- which is what
`SixThreeCrux.hasWeightFloor_neg_chartObjective` supplies -- needs exactly that.  A usable
floored covering must be stated at an EXPLICIT floor. -/
theorem forall_weightFlooredCovering_iff_gtzWeighted_six_three :
    (∀ floor : ℝ, 0 < floor → WeightFlooredCovering floor) ↔ GtzWeighted 6 3 := by
  constructor
  · intro hall D
    have hnonempty : (Finset.univ : Finset (Fin 6)).Nonempty := Finset.univ_nonempty
    set ownFloor : ℝ := Finset.univ.inf' hnonempty D.weight with hownFloor
    have hpos : 0 < ownFloor := by
      rw [hownFloor, Finset.lt_inf'_iff]
      exact fun atomIndex _ => D.weight_pos atomIndex
    have hfloor : HasWeightFloor D ownFloor :=
      fun atomIndex => Finset.inf'_le _ (Finset.mem_univ atomIndex)
    obtain ⟨selected, hcard, hdominates⟩ := hall ownFloor hpos D hfloor
    exact ⟨selected, hcard, hdominates⟩
  · intro hcell floor _
    exact weightFlooredCovering_of_gtzWeighted floor hcell

/-! ### The same collapse, at the tree's own floored predicate -/

/-- **ZERO SPREAD IS NO RESTRICTION.**  `Gtz.HasSpreadAtLeast D 0` is Cauchy-Schwarz, which
the tree already proves as `Gtz.atomPairing_sq_le_leverage_product`.  So
`Gtz.IsFlooredSpreadDesign D 0 floor` is exactly "all-heavy with weight floor `floor`", and
`Gtz.FlooredSpreadCovering 0 floor` is the shipped covering predicate carrying no spread
hypothesis at all. -/
theorem hasSpreadAtLeast_zero {m : ℕ} (D : WeightedDesign m 3) : HasSpreadAtLeast D 0 := by
  intro atomFirst atomSecond _
  have hcauchy := atomPairing_sq_le_leverage_product D atomFirst atomSecond
  linarith

/-- **THE BRIDGE: the new predicate is the stronger one.**  A covering that asks only for a
weight floor implies the shipped covering, which additionally assumes all-heaviness and a
spread bound.  The conclusions match through `Gtz.dominates_triple_iff_symmetricLegs`,
whose strict-heaviness hypotheses come from the region's own `Gtz.AllHeavy` conjunct. -/
theorem flooredSpreadCovering_of_weightFlooredCovering {spread floor : ℝ}
    (hcovering : WeightFlooredCovering floor) : FlooredSpreadCovering spread floor := by
  intro D hregion
  obtain ⟨selected, hcard, hdominates⟩ := hcovering D hregion.2.2
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hset⟩ :=
    Finset.card_eq_three.mp hcard
  subst hset
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    ((dominates_triple_iff_symmetricLegs D hfirstSecond hfirstThird hsecondThird
      (hregion.1 first) (hregion.1 second) (hregion.1 third)).mp hdominates).1,
    ((dominates_triple_iff_symmetricLegs D hfirstSecond hfirstThird hsecondThird
      (hregion.1 first) (hregion.1 second) (hregion.1 third)).mp hdominates).2⟩

/-- **THE COLLAPSE IS A PROPERTY OF THE QUANTIFIER, NOT OF THE PREDICATE.**  The tree's own
`Gtz.FlooredSpreadCovering`, at zero spread and quantified over all positive floors, is
also equivalent to the open cell.  The forward direction runs through all-heavy weighted
GTZ and the shipped `Gtz.rank_three_of_heavy_six_three`, so the equivalence costs the
Naimark-dual rank-three machinery rather than being immediate. -/
theorem forall_flooredSpreadCovering_iff_gtzWeighted_six_three :
    (∀ floor : ℝ, 0 < floor → FlooredSpreadCovering 0 floor) ↔ GtzWeighted 6 3 := by
  constructor
  · intro hall
    refine rank_three_of_heavy_six_three (fun D hheavy => ?_) 6
    have hnonempty : (Finset.univ : Finset (Fin 6)).Nonempty := Finset.univ_nonempty
    set ownFloor : ℝ := Finset.univ.inf' hnonempty D.weight with hownFloor
    have hpos : 0 < ownFloor := by
      rw [hownFloor, Finset.lt_inf'_iff]
      exact fun atomIndex _ => D.weight_pos atomIndex
    obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hminor, htie⟩ :=
      hall ownFloor hpos D ⟨hheavy, hasSpreadAtLeast_zero D,
        fun atomIndex => Finset.inf'_le _ (Finset.mem_univ atomIndex)⟩
    refine ⟨{first, second, third},
      Finset.card_eq_three.mpr ⟨first, second, third, hfirstSecond, hfirstThird,
        hsecondThird, rfl⟩, ?_⟩
    exact (dominates_triple_iff_symmetricLegs D hfirstSecond hfirstThird hsecondThird
      (hheavy first) (hheavy second) (hheavy third)).mpr ⟨hminor, htie⟩
  · intro hcell floor _
    exact flooredSpreadCovering_of_weightFlooredCovering
      (weightFlooredCovering_of_gtzWeighted floor hcell)

/-! ## 4.  The band exclusion, and the assembly -/

/-- **THE A-PRIORI BAND (gap 2, in the shape the lane consumes).**  No crux has chart value
inside `(-band, 0)`; since a crux's value is negative, this reads as
`chartObjective <= -band`.

The landed `Gtz.SixThreeCrux.neg_four_div_twentySeven_le_chartObjective` bounds the value
from BELOW by `-4/27`, so it constrains the band from the other side: only `band <= 4/27`
is consistent with a crux existing, which is
`isEmpty_sixThreeCrux_of_bandExclusion_of_four_div_twentySeven_lt`. -/
def ChartValueBandExclusion (band : ℝ) : Prop :=
  ∀ crux : SixThreeCrux, chartObjective (chartPointOfDesign crux.design) ≤ -band

/-- **THE BAND IS USEFUL ONLY ON `(0, 4/27]`.**  Above `4/27` the exclusion contradicts the
shipped value window by itself, so it is not a sub-goal on the way to the cell -- it IS the
cell, and proving it must consume everything a proof of the cell consumes.  This is what
pins the lane's target to an explicit finite range. -/
theorem isEmpty_sixThreeCrux_of_bandExclusion_of_four_div_twentySeven_lt {band : ℝ}
    (hwide : (4 : ℝ) / 27 < band) (hband : ChartValueBandExclusion band) :
    IsEmpty SixThreeCrux := by
  refine ⟨fun crux => ?_⟩
  have hwindow := crux.neg_four_div_twentySeven_le_chartObjective
  have hexcluded := hband crux
  linarith

/-- **THE ASSEMBLY -- THE VALUE LANE IN ONE THEOREM.**  At one explicit `band`, an a-priori
band exclusion plus the tree's own floored covering at the SAME `band` empties the crux
structure.

The proof is the whole lane: the band pushes the crux's value down to `-band`, the shipped
weight floor turns that into `band <= weight` at every atom, the crux's own all-heaviness
and free zero spread put its design in the floored spread region, the covering produces a
triple with both symmetric legs nonnegative, `Gtz.dominates_triple_iff_symmetricLegs` reads
that back as domination, and `hasNoDominatingTriple` refuses it.  No step needs `band` to
be small, and no step needs a margin. -/
theorem isEmpty_sixThreeCrux_of_bandExclusion_of_flooredSpreadCovering {band : ℝ}
    (hband : ChartValueBandExclusion band) (hcovering : FlooredSpreadCovering 0 band) :
    IsEmpty SixThreeCrux := by
  refine ⟨fun crux => ?_⟩
  have hfloor : HasWeightFloor crux.design band := by
    intro atomIndex
    refine le_trans ?_ (crux.hasWeightFloor_neg_chartObjective atomIndex)
    have := hband crux
    linarith
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hminor, htie⟩ :=
    hcovering crux.design ⟨crux.isAllHeavy, hasSpreadAtLeast_zero crux.design, hfloor⟩
  refine crux.hasNoDominatingTriple {first, second, third}
    (Finset.card_eq_three.mpr ⟨first, second, third, hfirstSecond, hfirstThird,
      hsecondThird, rfl⟩) ?_
  exact (dominates_triple_iff_symmetricLegs crux.design hfirstSecond hfirstThird hsecondThird
    (crux.isAllHeavy first) (crux.isAllHeavy second) (crux.isAllHeavy third)).mpr ⟨hminor, htie⟩

/-- The same assembly at the stronger ingredient, for a consumer that has it. -/
theorem isEmpty_sixThreeCrux_of_bandExclusion_of_weightFlooredCovering {band : ℝ}
    (hband : ChartValueBandExclusion band) (hcovering : WeightFlooredCovering band) :
    IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_bandExclusion_of_flooredSpreadCovering hband
    (flooredSpreadCovering_of_weightFlooredCovering hcovering)

/-- **THE CELL, from the two explicit ingredients.** -/
theorem gtzWeighted_six_three_of_bandExclusion_of_flooredSpreadCovering {band : ℝ}
    (hband : ChartValueBandExclusion band) (hcovering : FlooredSpreadCovering 0 band) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_isEmpty_sixThreeCrux
    (isEmpty_sixThreeCrux_of_bandExclusion_of_flooredSpreadCovering hband hcovering)

theorem gtzWeighted_six_three_of_bandExclusion_of_weightFlooredCovering {band : ℝ}
    (hband : ChartValueBandExclusion band) (hcovering : WeightFlooredCovering band) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_bandExclusion_of_flooredSpreadCovering hband
    (flooredSpreadCovering_of_weightFlooredCovering hcovering)

/-- **RANK THREE, from the two explicit ingredients.**  Composing with the shipped
`Gtz.gtz_original_rank_three_of_six_three`, so the two named quantitative inputs decide the
literal 1997 statement at rank three. -/
theorem gtzOriginal_rank_three_of_bandExclusion_of_flooredSpreadCovering {band : ℝ}
    (hband : ChartValueBandExclusion band) (hcovering : FlooredSpreadCovering 0 band) :
    ∀ atoms : ℕ, 0 < atoms → GtzOriginal atoms 3 :=
  gtz_original_rank_three_of_six_three
    (gtzWeighted_six_three_of_bandExclusion_of_flooredSpreadCovering hband hcovering)

theorem gtzOriginal_rank_three_of_bandExclusion_of_weightFlooredCovering {band : ℝ}
    (hband : ChartValueBandExclusion band) (hcovering : WeightFlooredCovering band) :
    ∀ atoms : ℕ, 0 < atoms → GtzOriginal atoms 3 :=
  gtzOriginal_rank_three_of_bandExclusion_of_flooredSpreadCovering hband
    (flooredSpreadCovering_of_weightFlooredCovering hcovering)

end Gtz

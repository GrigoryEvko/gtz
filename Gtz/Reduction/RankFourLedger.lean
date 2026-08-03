/-
PROVENANCE.  Harvested by the sweep from the recon-rankfour reconnaissance rung, which
mapped the rank-four ledger against the kernel generics and prototyped every statement
below.  The sweep curated the selection, de-prefixed the names, replaced the drafts'
`import Gtz` -- a build cycle for any module the umbrella imports, invisible to
`lake env lean` -- with the modules actually consumed, re-compiled, re-audited and
wired the result; the mathematics is recon-rankfour's.

# The rank ladder above rank three: monotonicity, the minimal crux, self-duality,
# and the elementary value floor at rank four and five

The campaign's rank-three statements are unusually clean, and this file isolates the
three separate reasons why -- so that nothing rank-three-specific is mistaken for a
general fact when the tower is climbed.

## The one equation behind three apparent accidents

`k*(k+1)/2 = 2k` holds only at `k = 3`.  That single equation is simultaneously

* `selfDual_eq_top_iff` -- the Veronese top is Naimark self-dual only at rank three;
* `selfDual_involution` -- the crux involution is an endomorphism of the top cell only
  at rank three (at every other rank it lives on `(2k, k)`, the BOTTOM of the window);
* `rank_four_no_squeeze` with `exists_minimal_crux` -- the minimal-failing-size window
  `2*rank <= least <= rank*(rank+1)/2` collapses to a single cell only at rank three,
  which is exactly what lets `Gtz.SixThreeCrux` be stated at a FIXED cell with its
  deflation fields free.

All three fail together from rank four on, where the self-dual cell `(8,4)` and the
top `(10,4)` separate by two atoms.  Boundary condition B7 is the standing warning and
this file is its mechanised form: an argument that leans on self-duality is a
rank-three argument.

## What is genuinely new here rather than a rank-four instantiation

Section 1.  Rank monotonicity of the whole conjecture.  The tree carries the per-cell
arrow `Gtz.gtzWeighted_of_spike` (Gtz/Reduction/RankFourWindow.lean:690) but NOT the
consequence `GtzWeightedAll (rank+1) -> GtzWeightedAll rank`, which any induction on
the rank wants.  A grep for that arrow returns nothing anywhere in the tree.

Section 2.  The SHARP lower end of the minimal failing size.  Naimark duality sends a
corank-`c` cell to rank `c`, so one rank of induction settles every cell up to
`2*rank - 1` and a counterexample cannot appear below `2*rank`.  At rank four this
moves the lower end from `rank + 3 = 7` to `8` -- and `7` is precisely the cell the
kernel proves equal to the rank-three top (`Gtz.gtzWeighted_six_three_iff_seven_four`),
so without the sharpening a "rank-four crux" could be a rank-three crux in disguise.

Section 4.  `rank_three_unconditional` derives the rank-three fixed-cell normal form
from the general theorem with no hypothesis beyond the failure, by feeding the squeeze
the shipped `Gtz.gtzWeightedAll_two_of_walk`.

Section 6.  THE SCALE-FREE READING OF THE VALUE FLOOR, and it inverts the naive one.
Raw floors at different sizes are not comparable, because the a-priori floor is itself
`-1/size`.  `floor_improvement_is_reciprocal_count` says what the mechanism actually
removes is the FRACTION `1/count` of the a-priori window, so a SMALLER count is a
BETTER presentation.  `(6,3)` has count 9 and removes 11.1 percent; `(7,4)` has count
13 and removes 7.7 percent; `(10,4)` has count 22 and removes 4.5 percent; `(15,5)`
has count 45 and removes 2.2 percent.  Reading the raw floors instead -- `-12/91` at
`(7,4)` against `-4/27` at `(6,3)` -- suggests `(7,4)` is the tighter presentation,
and that reading is an artefact of the `1/size` term.  The floor mechanism is a
rank-three-scale lever and it decays as the tower climbs.

## Scope

Every statement in sections 1-5 is general in the rank; the concrete cells in section
6 are corollaries of the shipped rank-free floor, and are legitimately per-cell
because they are numerals.  Nothing here bears on whether any cell is true: the
minimal-crux theorem takes the FAILURE of the rank as a hypothesis, and its content is
the shape a counterexample would have to have.
-/
import Mathlib
import Gtz.Reduction.Reductions
import Gtz.Reduction.LiftingLemma
import Gtz.Reduction.Deflation
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.NaimarkLeverage
import Gtz.Reduction.StressWalk
import Gtz.Reduction.RankFourWindow
import Gtz.Quantitative.ElementaryValueFloor

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
  {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}
  {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → Fin size → ℝ}

/-! ## 1.  Rank monotonicity of the whole conjecture

The tree carries the per-cell arrow `Gtz.gtzWeighted_of_spike` but not its consequence
for the whole rank, which any induction on the rank wants.  Every statement in this
section is general in the rank. -/

/-- Below the rank the cell is vacuous: no design of `size < rank` atoms exists, since
`Gtz.rank_le_of_design` forces `rank <= size`. -/
theorem gtzWeighted_of_size_lt_rank {size rank : ℕ} (hlt : size < rank) :
    GtzWeighted size rank := fun design => absurd (rank_le_of_design design) (by omega)

/-- **Rank monotonicity, one step.**  The tree ships the per-cell spike arrow
`Gtz.gtzWeighted_of_spike` but not this consequence for the whole rank. -/
theorem gtzWeightedAll_of_succ (rank : ℕ) (hall : GtzWeightedAll (rank + 1)) :
    GtzWeightedAll rank := by
  intro size
  rcases Nat.eq_zero_or_pos rank with hzero | hpos
  · rw [hzero]; exact gtzWeighted_dim_zero size
  · rcases Nat.lt_or_ge size rank with hlt | hge
    · exact gtzWeighted_of_size_lt_rank hlt
    · exact gtzWeighted_of_spike hpos hge (hall (size + 1))

/-- Rank monotonicity across a gap, by induction on the gap. -/
theorem gtzWeightedAll_of_add (rank gap : ℕ) :
    GtzWeightedAll (rank + gap) → GtzWeightedAll rank := by
  induction gap with
  | zero => intro hall; simpa using hall
  | succ previous ih =>
      intro hall
      refine ih ?_
      have hreassociate : rank + (previous + 1) = (rank + previous) + 1 := by omega
      rw [hreassociate] at hall
      exact gtzWeightedAll_of_succ _ hall

/-- **Rank monotonicity.**  A higher rank implies every lower one, so the tower
`T_3, T_4, T_5, ...` is a DESCENDING chain and the tops are increasingly strong. -/
theorem gtzWeightedAll_of_le {rank larger : ℕ} (hle : rank ≤ larger)
    (hall : GtzWeightedAll larger) : GtzWeightedAll rank := by
  obtain ⟨gap, hgap⟩ := Nat.exists_eq_add_of_le hle
  subst hgap
  exact gtzWeightedAll_of_add rank gap hall

/-! ## 2.  Naimark duality frees every corank below the rank

The sharp lower end of the minimal failing size.  Duality sends a corank-`c` cell back
to rank `c`, so one rank of induction settles every cell up to `2*rank - 1` and a
counterexample cannot appear below `2*rank`. -/

/-- **Given the rank below, every corank up to `rank - 1` is a theorem.**  The
Naimark dual of a corank-`c` cell at rank `k` is rank `c` at the same size, and
`c ≤ k - 1` puts that inside the induction hypothesis. -/
theorem corank_free_of_rank_below {rank corank : ℕ} (hrank : 1 ≤ rank)
    (hcorank : 1 ≤ corank) (hbelow : corank ≤ rank - 1)
    (hall : GtzWeightedAll (rank - 1)) : GtzWeighted (rank + corank) rank := by
  refine gtzWeighted_of_dual_rank hrank (by omega) ?_
  have hindex : rank + corank - rank = corank := by omega
  rw [hindex]
  exact gtzWeightedAll_of_le hbelow hall _

/-- **THE SHARPENED LOWER END.**  Under the rank-below induction hypothesis the
minimal failing size at rank `rank` is at least `2 * rank`, not merely `rank + 3`. -/
theorem twice_rank_le_of_failing {size rank : ℕ} (hrank : 1 ≤ rank)
    (hall : GtzWeightedAll (rank - 1)) (hfail : ¬ GtzWeighted size rank) :
    2 * rank ≤ size := by
  by_contra hsmall
  push Not at hsmall
  rcases Nat.lt_or_ge size rank with hlt | hge
  · exact hfail (gtzWeighted_of_size_lt_rank hlt)
  · obtain ⟨corank, hcorank⟩ : ∃ corank, size = rank + corank :=
      ⟨size - rank, by omega⟩
    subst hcorank
    rcases Nat.eq_zero_or_pos corank with hzero | hpos
    · rw [hzero, Nat.add_zero] at hfail
      exact hfail (gtzWeighted_square rank)
    · exact hfail (corank_free_of_rank_below hrank hpos (by omega) hall)

/-- The dual-rank input the co-singleton deflation field needs, supplied by one rank of
induction through `Gtz.gtzWeighted_of_dual_rank`. -/
theorem dualRank_of_rank_below {smaller rank : ℕ} (hrank : 2 ≤ rank)
    (hfits : rank ≤ smaller) (hbelow : GtzWeightedAll (rank - 1)) :
    GtzWeighted smaller (smaller + 1 - rank) := by
  refine gtzWeighted_of_dual_rank (k := smaller + 1 - rank) (m := smaller)
    (by omega) (by omega) ?_
  have hindex : smaller - (smaller + 1 - rank) = rank - 1 := by omega
  rw [hindex]
  exact hbelow smaller

/-! ## 3.  The three deflation fields, each with its exact cost

These are the fields `Gtz.SixThreeCrux` carries unconditionally at rank three.  At a
general rank each is free one size above a theorem, and the co-singleton field costs
the DUAL rank -- a different cell as soon as the cell is not self-dual. -/

/-- **All-heaviness is free one size above a theorem.** -/
theorem allHeavy_of_no_dominating {smaller rank : ℕ} (hsmaller : 1 ≤ smaller)
    (hsameRank : GtzWeighted smaller rank)
    (design : WeightedDesign (smaller + 1) rank)
    (hnone : ∀ selected : Finset (Fin (smaller + 1)), selected.card = rank →
      ¬ Dominates design selected) :
    AllHeavy design := by
  intro atomIndex
  by_contra hlight
  push Not at hlight
  obtain ⟨selected, hcard, hdominates⟩ :=
    dominating_of_light_atom design hsmaller hsameRank atomIndex hlight
  exact hnone selected hcard hdominates

/-- **No parallel pair, same cost.** -/
theorem noParallelPair_of_no_dominating {smaller rank : ℕ}
    (hsameRank : GtzWeighted smaller rank)
    (design : WeightedDesign (smaller + 1) rank)
    (hnone : ∀ selected : Finset (Fin (smaller + 1)), selected.card = rank →
      ¬ Dominates design selected) :
    ¬ HasParallelPair design := by
  rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
  obtain ⟨selected, hcard, hdominates⟩ :=
    dominating_of_parallel_pair design hsameRank hdistinct hparallel
  exact hnone selected hcard hdominates

/-- **The co-singleton field costs the DUAL rank**, which is a different cell as soon
as the cell is not self-dual. -/
theorem coSingletons_of_no_dominating {smaller rank : ℕ} (hrank : 1 ≤ rank)
    (hfits : rank + 1 ≤ smaller + 1) (hsmaller : 1 ≤ smaller)
    (hdualRank : GtzWeighted smaller (smaller + 1 - rank))
    (design : WeightedDesign (smaller + 1) rank)
    (hnone : ∀ selected : Finset (Fin (smaller + 1)), selected.card = rank →
      ¬ Dominates design selected) :
    HasStrictlyDominatingCoSingletons design := by
  intro atomIndex
  by_contra hbad
  obtain ⟨selected, hcard, hdominates⟩ :=
    dominating_of_coSingleton_not_posDef hrank hfits hsmaller hdualRank design atomIndex hbad
  exact hnone selected hcard hdominates

/-! ## 4.  The rank-generic minimal crux -/

/-- **THE RANK-GENERIC MINIMAL CRUX.**  Whenever weighted GTZ fails at `rank` and the rank
below is known, there is a counterexample at the minimal failing size carrying ALL
THREE deflation fields for free -- exactly the freeness `Gtz.SixThreeCrux` enjoys
unconditionally at rank three -- with the size squeezed by
`2*rank <= least <= rank*(rank+1)/2`.  That squeeze collapses to a single cell only at
rank three (`selfDual_eq_top_iff`), which is why no other rank has a fixed-cell normal
form. -/
theorem exists_minimal_crux (rank : ℕ) (hrank : 2 ≤ rank)
    (hbelow : GtzWeightedAll (rank - 1)) (hfail : ¬ GtzWeightedAll rank) :
    ∃ (least : ℕ) (design : WeightedDesign least rank),
      2 * rank ≤ least
      ∧ least ≤ rank * (rank + 1) / 2
      ∧ (∀ below, below < least → GtzWeighted below rank)
      ∧ (∀ selected : Finset (Fin least), selected.card = rank →
          ¬ Dominates design selected)
      ∧ AllHeavy design
      ∧ HasStrictlyDominatingCoSingletons design
      ∧ ¬ HasParallelPair design := by
  classical
  have hexists : ∃ size, ¬ GtzWeighted size rank := by
    by_contra hnone
    push Not at hnone
    exact hfail hnone
  obtain ⟨least, hleastFails, hleastMinimal⟩ :
      ∃ least, ¬ GtzWeighted least rank
        ∧ ∀ below, below < least → GtzWeighted below rank :=
    ⟨Nat.find hexists, Nat.find_spec hexists,
      fun below hbelowLt => not_not.mp (Nat.find_min hexists hbelowLt)⟩
  -- the SHARP lower end: duality frees every corank up to rank - 1
  have hleastLower : 2 * rank ≤ least := by
    by_contra hsmall
    push Not at hsmall
    rcases Nat.lt_or_ge least rank with hlt | hge
    · exact hleastFails (gtzWeighted_of_size_lt_rank hlt)
    · obtain ⟨corank, hcorank⟩ : ∃ corank, least = rank + corank := ⟨least - rank, by omega⟩
      rcases Nat.eq_zero_or_pos corank with hzero | hpos
      · rw [hcorank, hzero, Nat.add_zero] at hleastFails
        exact hleastFails (gtzWeighted_square rank)
      · refine hleastFails ?_
        rw [hcorank]
        refine gtzWeighted_of_dual_rank (by omega) (by omega) ?_
        have hindex : rank + corank - rank = corank := by omega
        rw [hindex]
        exact gtzWeightedAll_of_le (by omega) hbelow _
  have hleastUpper : least ≤ rank * (rank + 1) / 2 := by
    by_contra hbig
    push Not at hbig
    exact hleastFails
      (crystallizationSharp rank (fun below hbelowLe => hleastMinimal below (by omega)) _)
  obtain ⟨design, hdesign⟩ : ∃ design : WeightedDesign least rank,
      ∀ selected : Finset (Fin least), selected.card = rank →
        ¬ Dominates design selected := by
    by_contra hnone
    push Not at hnone
    exact hleastFails fun design => hnone design
  obtain ⟨smaller, hsmallerEq⟩ : ∃ smaller, least = smaller + 1 := ⟨least - 1, by omega⟩
  subst hsmallerEq
  have hsameRank : GtzWeighted smaller rank := hleastMinimal smaller (by omega)
  have hdualRank : GtzWeighted smaller (smaller + 1 - rank) :=
    dualRank_of_rank_below hrank (by omega) hbelow
  exact ⟨smaller + 1, design, hleastLower, hleastUpper, hleastMinimal, hdesign,
    allHeavy_of_no_dominating (by omega) hsameRank design hdesign,
    coSingletons_of_no_dominating (by omega) (by omega) (by omega) hdualRank
      design hdesign,
    noParallelPair_of_no_dominating hsameRank design hdesign⟩

/-- At rank three the hypothesis is DISCHARGED -- rank two is a theorem -- and the
squeeze `2*3 = 6 = N_3` forces the minimal failing size, which is why
`Gtz.SixThreeCrux` can be stated at a FIXED cell. -/
theorem rank_three_unconditional (hfail : ¬ GtzWeightedAll 3) :
    ∃ design : WeightedDesign 6 3,
      (∀ selected : Finset (Fin 6), selected.card = 3 → ¬ Dominates design selected)
      ∧ AllHeavy design ∧ HasStrictlyDominatingCoSingletons design
      ∧ ¬ HasParallelPair design := by
  obtain ⟨least, design, hlower, hupper, -, hnone, hheavy, hco, hpar⟩ :=
    exists_minimal_crux 3 (by norm_num)
      (by simpa using gtzWeightedAll_two_of_walk) hfail
  have hleast : least = 6 := by omega
  subst hleast
  exact ⟨design, hnone, hheavy, hco, hpar⟩

/-- At rank four the squeeze FAILS: `2*4 = 8` but `N_4 = 10`, so the minimal failing
size is pinned only to `{8, 9, 10}` and no fixed-cell normal form is available. -/
theorem rank_four_no_squeeze : 2 * 4 < 4 * (4 + 1) / 2 := by norm_num

/-! ## 5.  Self-duality, and where the crux involution relocates

The Veronese top is Naimark self-dual exactly when `k*(k+1)/2 = 2k`, i.e. only at rank
three.  The involution that makes a rank-three crux an endomorphism of its own cell
survives at every rank -- but on the self-dual family `(2k, k)`, which is the BOTTOM
of the rank-`k` window rather than its top.  Any argument of the form "whatever kills
a crux must survive the involution" therefore constrains the WEAKEST member of the
window at every rank above three. -/

/-- The Naimark dual rank at the cell `(2k, k)` is `k` again. -/
theorem selfDual_family (rank : ℕ) : 2 * rank - rank = rank := by omega

/-- Complements of `k`-subsets are `k`-subsets exactly on the self-dual family. -/
theorem compl_card_selfDual (rank : ℕ) (selected : Finset (Fin (2 * rank)))
    (hcard : selected.card = rank) : (selectedᶜ : Finset (Fin (2 * rank))).card = rank := by
  rw [Finset.card_compl, Fintype.card_fin, hcard]
  omega

/-- **THE INVOLUTION, AT EVERY RANK, ON THE SELF-DUAL FAMILY.**  Stated with the dual
rank left as `2*rank - rank` so that no dependent transport is needed; that this IS
the same cell is `selfDual_family`. -/
theorem selfDual_involution (rank : ℕ) (hrank : 1 ≤ rank)
    (design : WeightedDesign (2 * rank) rank)
    (hcoSingleton : HasStrictlyDominatingCoSingletons design)
    (hnone : ∀ selected : Finset (Fin (2 * rank)), selected.card = rank →
      ¬ Dominates design selected) :
    ∃ dual : WeightedDesign (2 * rank) (2 * rank - rank),
      (∀ atomIndex, dual.weight atomIndex = design.weight atomIndex)
      ∧ AllHeavy dual
      ∧ ∀ selected : Finset (Fin (2 * rank)), selected.card = 2 * rank - rank →
          ¬ Dominates dual selected := by
  obtain ⟨dual, hweights, hdictionary, hflip⟩ :=
    exists_naimarkDual_allHeavy_iff (m := 2 * rank) (k := rank) hrank (by omega) design
  refine ⟨dual, hweights, hdictionary.mpr hcoSingleton, fun selected hcard hdominates => ?_⟩
  have hcardRank : selected.card = rank := by rw [hcard]; omega
  have hcompCard : (selectedᶜ : Finset (Fin (2 * rank))).card = rank :=
    compl_card_selfDual rank selected hcardRank
  exact hnone selectedᶜ hcompCard ((hflip selectedᶜ hcompCard).mpr (by rwa [compl_compl]))

/-- **The self-dual cell is the Veronese top exactly at rank three.** -/
theorem selfDual_eq_top_iff :
    ∀ rank ≤ 40, 1 ≤ rank → (2 * rank = rank * (rank + 1) / 2 ↔ rank = 3) := by
  decide

/-- At rank four they are two different cells: the self-dual `(8,4)` and the top
`(10,4)`, two atoms apart. -/
theorem rank_four_two_cells :
    2 * 4 = 8 ∧ 4 * (4 + 1) / 2 = 10 ∧ 2 * 4 ≠ 4 * (4 + 1) / 2 := by norm_num

/-! ## 6.  The elementary value floor above rank three

`Gtz.combinedValueFloor_le_value_of_isChartStationaryData` carries NO hypothesis on the
rank, so it instantiates at every cell for free.  The corollaries below are the
rank-four and rank-five analogues of the shipped `-4/27` at `(6,3)`; the scale-free
reading, which inverts the naive one, is in the file header and in
`floor_improvement_is_reciprocal_count`. -/

/-- The elementary count at `(7,4)`. -/
theorem combinedCount_sevenFour : combinedCount 7 4 = 13 := by
  norm_num [combinedCount, elementaryCount, Nat.choose]

/-- The elementary count at the rank-four self-dual cell `(8,4)`. -/
theorem combinedCount_eightFour : combinedCount 8 4 = 16 := by
  norm_num [combinedCount, elementaryCount, Nat.choose]

/-- The elementary count at `(9,4)`. -/
theorem combinedCount_nineFour : combinedCount 9 4 = 19 := by
  norm_num [combinedCount, elementaryCount, Nat.choose]

/-- The elementary count at the rank-four Veronese top `(10,4)`. -/
theorem combinedCount_tenFour : combinedCount 10 4 = 22 := by
  norm_num [combinedCount, elementaryCount, Nat.choose]

/-- The elementary count at the rank-five Veronese top `(15,5)`. -/
theorem combinedCount_fifteenFive : combinedCount 15 5 = 45 := by
  norm_num [combinedCount, elementaryCount, Nat.choose]

/-- The elementary value floor at `(8,4)`. -/
theorem combinedValueFloor_eightFour : combinedValueFloor 8 4 = -(15 / 128) := by
  rw [combinedValueFloor, valueFloorOfCount, combinedCount_eightFour]
  norm_num

/-- The elementary value floor at `(9,4)`. -/
theorem combinedValueFloor_nineFour : combinedValueFloor 9 4 = -(2 / 19) := by
  rw [combinedValueFloor, valueFloorOfCount, combinedCount_nineFour]
  norm_num

/-- **THE RANK-FOUR `4/27`.** -/
theorem combinedValueFloor_tenFour : combinedValueFloor 10 4 = -(21 / 220) := by
  rw [combinedValueFloor, valueFloorOfCount, combinedCount_tenFour]
  norm_num

/-- The elementary value floor at the rank-five Veronese top. -/
theorem combinedValueFloor_fifteenFive :
    combinedValueFloor 15 5 = -(44 / 675) := by
  rw [combinedValueFloor, valueFloorOfCount, combinedCount_fifteenFive]
  norm_num

/-- The rank-four window ordering, mirroring the rank-three `-1/6 < -3/20 < -4/27 < 0`. -/
theorem rank_four_floor_order :
    -(1 / 10 : ℝ) < -(83 / 840 : ℝ) ∧ -(83 / 840 : ℝ) < -(21 / 220 : ℝ)
      ∧ -(21 / 220 : ℝ) < 0 := by norm_num

/-- **THE RANK-FOUR `-4/27`.**  At the rank-four Veronese top `T_4 = (10,4)` every
admissible chart-stationary value is at least `-21/220`, so the rank-four crux window
on the negative axis is `[-21/220, 0)` against the trivial `(-1/10, 0)`. -/
theorem neg_twentyOne_div_twoHundredTwenty_le_value_of_isChartStationaryData
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hsize : size = 10) (hrank : rank = 4) :
    -(21 / 220 : ℝ) ≤ value := by
  have hfloor := combinedValueFloor_le_value_of_isChartStationaryData design hchart hargmax hdata
  rwa [hsize, hrank, combinedValueFloor_tenFour] at hfloor

/-- The rank-four SELF-DUAL cell `(8,4)`, the bottom of the window. -/
theorem neg_fifteen_div_oneHundredTwentyEight_le_value_of_isChartStationaryData
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hsize : size = 8) (hrank : rank = 4) :
    -(15 / 128 : ℝ) ≤ value := by
  have hfloor := combinedValueFloor_le_value_of_isChartStationaryData design hchart hargmax hdata
  rwa [hsize, hrank, combinedValueFloor_eightFour] at hfloor

/-- The `(9,4)` instance of the shipped rank-free floor. -/
theorem neg_two_div_nineteen_le_value_of_isChartStationaryData
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hsize : size = 9) (hrank : rank = 4) :
    -(2 / 19 : ℝ) ≤ value := by
  have hfloor := combinedValueFloor_le_value_of_isChartStationaryData design hchart hargmax hdata
  rwa [hsize, hrank, combinedValueFloor_nineFour] at hfloor

/-- **THE SCALE-FREE READING.**  The floor's whole improvement over the shipped
trivial bound `-(1/size)` is `(1/size)·(1/count)`: the mechanism removes exactly the
fraction `1/count` of the trivial window, at every cell.  So a floor comparison
between two cells of DIFFERENT size is confounded by `1/size`, and the honest
comparison is between COUNTS. -/
theorem floor_improvement_is_reciprocal_count (size rank : ℕ) :
    combinedValueFloor size rank - (-((size : ℝ))⁻¹)
      = ((size : ℝ))⁻¹ * ((combinedCount size rank : ℕ) : ℝ)⁻¹ := by
  rw [combinedValueFloor, valueFloorOfCount]
  ring

/-- **THE FLOOR MECHANISM DECAYS WITH RANK.**  At the top `T_k` the count is
`k(k-1)²/2 + k`, cubic in the rank, so the fraction of the window it removes falls
off like `2/k³`: `1/9` at rank three, `1/22` at rank four, `1/45` at rank five.
FLOOR-E2 is therefore a rank-three-scale lever, not a general one. -/
theorem top_count_closed_form :
    ∀ rank, 1 ≤ rank → rank ≤ 12 →
      elementaryCount (rank * (rank + 1) / 2) rank
        = rank * (rank * rank - 2 * rank + 3) / 2 := by
  decide

end Gtz

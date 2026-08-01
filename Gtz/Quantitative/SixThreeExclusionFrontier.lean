/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Quantitative.TwoGraphCollision
import Gtz.Quantitative.ExcessGapCensus
import Gtz.Quantitative.ActiveOverlapPatternsSixThree
import Gtz.Quantitative.ChartDisjointBlockExclusion
import Gtz.Quantitative.ElementaryValueFloor
import Gtz.Reduction.ChartAttainmentWeld

/-!
# The `(6,3)` exclusion frontier

`Gtz.GtzWeighted 6 3` is the wall cell of the rank-three conjecture:
`Gtz.nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three` makes it EQUIVALENT to
`IsEmpty Gtz.SixThreeCrux`, and `Gtz.gtzWeightedAll_three_of_isEmpty_cruxes` then carries
rank three entirely.  This file is the terminal module of a campaign that attacked that
emptiness and did NOT achieve it.  It contracts the crux as far as the landed material
allows, and it names precisely what survives.

## THE FRONTIER LEDGER

Rung by rung, what landed and what walled.  Read the WALLS first: three of them are
theorems in this repository rather than reports, so the routes they close are closed
for good.

* **Coherence forcing.**  LANDED, and sharper than a disjunction.
  `Gtz.SixThreeCrux.discriminantTie_neg_of_excessGap_nonneg` squeezes every triple:
  a nonnegative sign-blind gap forces incoherence, all three pairings nonzero, and
  `excessGap < 2 |p p p|`.  The zero-pairing escape clause the rung was scoped with is
  VACUOUS -- `Gtz.dominates_of_coherent_of_excessGap_nonneg` carries no nonvanishing
  hypothesis -- and the vanishing case is a SECOND kill,
  `Gtz.dominates_of_excessGap_nonneg_of_exists_atomPairing_eq_zero`.

* **Chart-side two-block kill.**  LANDED as a weld, not a port.
  `Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily`: the argmax family has at least
  three members.  The exclusion already existed under other vocabulary
  (`Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_design_of_negativeValue`);
  what was missing was the observation that at `size = 2 * rank` a two-member argmax
  family IS a complementary pair.

* **Sharp coherent count.**  LANDED at general size.
  `Gtz.card_coherentPairsThroughBase_ge` gives `m - 4` coherent triangles through every
  atom, and `Gtz.card_coherentTripleSets_ge` gives `m (m - 4) / 3` globally -- FOUR of
  the twenty at `m = 6`, SEVEN of the thirty-five at `m = 7`.  Both need pairwise
  nonvanishing pairings; the hypothesis-free statement is the dichotomy
  `Gtz.SixThreeCrux.two_le_card_coherentPairsThroughBase_or_exists_orthogonalPair`.

* **Excess-gap census.**  WALLED, and the wall is a theorem.
  `Gtz.censusTripleSets_icosaDesign_eq_empty`: `Gtz.icosaDesign` is all-heavy, has no
  parallel pair, and every one of its twenty triples has sign-blind gap `-14/5`, so its
  census is EMPTY.  Since `Gtz.excessGap` reads only the three heavy excesses and the
  three squared pairings, NO hypothesis expressible in sign-blind data can force a
  census triple to exist.  What survives is a per-triple window
  (`Gtz.SixThreeCrux.excessGap_lt_quarter_mul_heavyExcess_prod`, sharp at the
  tetrahedral tie), two ceilings, and the two-sided sign band.

* **Two-graph collision.**  LANDED IN FULL, AND THE RESIDUE IS NOT EMPTY.
  All three known levers are now proved -- the obtuse cap at a base
  (`Gtz.card_le_three_of_forall_incoherent_through_base`), its complement
  (`Gtz.card_le_three_of_forall_coherent_through_base`), and the saturated-matching
  law resting on the edge identity `Gtz.sum_erasePair_weight_mul_atomPairing`.  They
  leave `Gtz.card_residualSectors = 842` of the 1024 two-graphs, in eight of the
  sixteen isomorphism classes.  The residue is SHARP: each of the eight is realised by
  an explicit `(6,3)` design with positive rational Parseval coefficients (measured
  exactly outside Lean, by two independent methods), so no correct sign-only argument
  cuts any of them.  THE SIGN LANE IS CLOSED, IN BOTH DIRECTIONS.

* **Self-duality.**  LANDED, and it REFUTED the band it was commissioned to supply.
  `Gtz.IsChartDual` carries D1 (`Gtz.dotProduct_chartDual_of_ne`, pairings exactly
  negated with the same zero set), D2, D3 (`Gtz.tripleParity_chartDual`, the dual
  two-graph is the complement) and D5.  But it is NOT the Naimark dual:
  `Gtz.exists_naimarkDual_dominates_and_chartDual_not_dominates` separates them at
  `Gtz.orthoSplitDesign`.  The anti-parity law lives on the chart dual and the
  domination transport lives on the Naimark dual, and NO SINGLE OBJECT CARRIES BOTH --
  so the ledger's per-vertex band does not follow by field transport.  It is a theorem
  anyway, by the partner route: `Gtz.card_coherentPairsThroughBase_mem_band_sixThree`.

* **Overlap patterns.**  LANDED as a three-way disjunction, not the hoped-for two.
  `Gtz.SixThreeCrux.exists_overlapPattern_of_card_chartArgmaxFamily_eq_three`: a
  three-member covering argmax family is a TRIANGLE, a CHAIN or a STAR.  The star is
  the saturated case and dies on the QUADRIC side
  (`Gtz.one_le_value_of_hasSaturatedAtom_of_isActiveFamily`), which a crux cannot
  reach; no chart-side saturation exclusion exists and two agents failed to build one.
  The chain is exactly a complementary pair plus a third block meeting both, the shape
  nothing shipped excludes.

## WHAT THIS FILE ADDS

1. THE SHARP WINDOW, still unlanded after three agents flagged it:
   `Gtz.SixThreeCrux.neg_four_div_twentySeven_le_chartObjective` narrows the crux's
   chart value from the shipped `[-1/6, 0)` to `[-4/27, 0)`, free from data the crux
   already carries.  The `(7,3)` sibling reads `-10/77` against `-1/7`.

2. THE UNIFIED STAR LAW.  `Gtz.atomShare_add_ne_one_of_saturatedStar`: an edge whose
   four triples all carry the SAME parity has its own pairing nonzero AND its two
   shares off one, in the direction the sign names -- under STAR-nonvanishing alone,
   where the shipped saturated-edge lemmas asked for GLOBAL nonvanishing and the
   shipped orthogonal-edge lemmas covered only the vanishing case.  One statement
   subsumes all four, and it is the lemma the zero-pairing branch runs on.

3. THE ZERO-PAIRING BRANCH, given real content.  At a crux an orthogonal edge with
   nonvanishing star carries BOTH parities among its four triples
   (`Gtz.SixThreeCrux.exists_coherent_and_exists_incoherent_through_orthogonalEdge`).
   Measured outside Lean on the sector table: this constraint MORE THAN COMPENSATES
   for the loss of the two obtuse levers, which genuinely fail at a vanishing pairing
   because `Gtz.IsPairwiseObtuse` is strict and the non-strict cap in `R^3` is six.
   One orthogonal edge leaves 840 of the 1024 two-graphs against 958 without it, and
   842 in the nonvanishing branch.  THE ZERO-PAIRING BRANCH IS NOT A BLACK HOLE.
   It is also not empty, and it is not closed.

4. THE FRONTIER, hypothesis-free: `Gtz.SixThreeCrux.frontier` collects the window, the
   active-family floor, the per-triple sign-blind window, the co-singleton window, the
   domination window, triangle-freeness of the orthogonality graph, and the sign
   dichotomy with BOTH branches carrying their content.

5. THE REFUTATION TARGET: `Gtz.IsSixThreeRefutationCandidate`, a design-level predicate
   with no chart data in it, together with
   `Gtz.gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidate` -- so
   emptying an explicitly checkable semialgebraic box now SUFFICES for the wall cell,
   and a failed search is evidence rather than silence.

## WHAT IS NOT CLOSED, NAMED

`IsEmpty Gtz.SixThreeCrux` is OPEN and nothing here approaches it.  The single
highest-value missing inequality, identified independently by two lanes, is a LOWER
BOUND ON `|chartObjective|` at a crux: the shipped
`Gtz.weight_ge_neg_value_of_isChartStationaryData` turns any such bound `eps` into a
weight floor at every atom, and the domination margin was measured to grow like
`C eps^2` with `C` between `0.60` and `3.75` across the eight surviving sign classes
(margins from `7.5e-3` to `1.0e-1` at `eps = 4/27`).  Without it the constrained
infimum of that margin is exactly one in every surviving class -- approached to
`5.05e-11`, re-verified at eighty digits -- so there is NO per-sector magnitude
inequality to mechanize, and the sector decomposition does not localise the problem.

Two smaller named openings.  (a) The chart-side saturated-atom exclusion: the law
`Gtz.SixThreeCrux.weight_eq_neg_chartObjective_of_saturatedAtom` is an EQUATION, not a
bound, and combining it with the shipped weight floor and the weight sum reproduces
only `value >= -1/6`; the star pattern therefore survives.  (b) An atom orthogonal to
all five others forces its share to one, its five partners into a plane, and a
dominating triple through `Gtz.gtzWeighted_corank_two 2` -- a genuine kill of a
degenerate sub-case that needs the rank-two sub-design built, and is not attempted
here.

NO SORRY, NO AXIOM, NO `native_decide`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open scoped BigOperators

/-! ## The sharp window

The shipped `Gtz.SixThreeCrux.neg_inv_six_le_chartObjective` reads `-1/6 <= value` off
the strong stationarity bundle alone.  The crux also carries `Gtz.IsChartArgmaxValue`
AND a design, which is exactly what the combined floor consumes, so the negative axis
narrows by `1/54` for free. -/

/-- **THE SHARP CRUX WINDOW, LOWER END.**  A `(6,3)` crux has chart value at least
`-4/27 = -0.148148...`, against the shipped `-1/6 = -0.166666...`. -/
theorem SixThreeCrux.neg_four_div_twentySeven_le_chartObjective (crux : SixThreeCrux) :
    -(4 / 27 : ℝ) ≤ chartObjective (chartPointOfDesign crux.design) := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  exact neg_four_div_twentySeven_le_value_of_isChartStationaryData crux.design rfl
    crux.isChartArgmaxValue hdata rfl rfl

/-- **THE CRUX WINDOW, BOTH ENDS.**  That the lower end is a genuine upgrade is the
shipped `Gtz.neg_inv_six_lt_neg_four_div_twentySeven`. -/
theorem SixThreeCrux.chartObjective_mem_window (crux : SixThreeCrux) :
    -(4 / 27 : ℝ) ≤ chartObjective (chartPointOfDesign crux.design)
      ∧ chartObjective (chartPointOfDesign crux.design) < 0 :=
  ⟨crux.neg_four_div_twentySeven_le_chartObjective, crux.hasNegativeChartValue⟩

/-- **THE SAME UPGRADE AT `(7,3)`:** `-10/77` against the shipped `-1/7`.  The `(7,3)`
crux exposes its minimiser rather than a packaged stationarity datum, so the bundle is
produced here through the attainment weld. -/
theorem SevenThreeCrux.neg_ten_div_seventySeven_le_chartObjective (crux : SevenThreeCrux) :
    -(10 / 77 : ℝ) ≤ chartObjective (chartPointOfDesign crux.design) := by
  obtain ⟨⟨multiplier, selection, hdata⟩, _⟩ :=
    exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin _ crux.weight_pos
      crux.isChartMinimiser
  exact neg_ten_div_seventySeven_le_value_of_isChartStationaryData crux.design rfl
    crux.isChartArgmaxValue hdata rfl rfl

/-! ## The unified star law

Call an edge SIGN-SATURATED when all four triples through it carry the same parity.
The shipped saturated-edge lemmas price a saturated edge in shares but ask for global
nonvanishing; the shipped orthogonal-edge lemmas ask only for a nonvanishing star but
cover only the vanishing edge.  Both halves need exactly the star, and the edge law
`Gtz.sum_erasePair_weight_mul_atomPairing` supplies both at once: multiplying it by the
edge pairing turns every summand into the oriented triple product of the corresponding
star member, whose sign IS the parity. -/

/-- **THE STAR LAW, COHERENT SIDE.**  A coherent-saturated edge has its own pairing
nonzero and its two shares summing to strictly less than one -- under nonvanishing of
the STAR only. -/
theorem atomShare_add_lt_one_of_coherentStar (design : WeightedDesign 6 3)
    {edgeFirst edgeSecond : Fin 6} (hedge : edgeFirst ≠ edgeSecond)
    (hstarFirst : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeFirst other ≠ 0)
    (hstarSecond : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeSecond other ≠ 0)
    (hcoherent : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      tripleParity design edgeFirst edgeSecond other = 1) :
    atomPairing design edgeFirst edgeSecond ≠ 0
      ∧ atomShare design edgeFirst + atomShare design edgeSecond < 1 := by
  have hpairNe : atomPairing design edgeFirst edgeSecond ≠ 0 := fun hzero =>
    not_forall_coherent_of_orthogonalEdge design hedge hzero hstarFirst hstarSecond hcoherent
  refine ⟨hpairNe, ?_⟩
  have hlaw := sum_erasePair_weight_mul_atomPairing design hedge
  have hnonempty :
      ((Finset.univ.erase edgeFirst).erase edgeSecond : Finset (Fin 6)).Nonempty := by
    rw [← Finset.card_pos,
      Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hedge, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    norm_num
  have htermPos : ∀ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      0 < atomPairing design edgeFirst edgeSecond * (design.weight other
        * (atomPairing design edgeFirst other * atomPairing design other edgeSecond)) := by
    intro other hother
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hother
    obtain ⟨hotherSecond, hotherFirst⟩ := hother
    have hprodNe : atomPairing design edgeFirst edgeSecond * atomPairing design edgeFirst other
        * atomPairing design edgeSecond other ≠ 0 :=
      mul_ne_zero (mul_ne_zero hpairNe (hstarFirst other hotherFirst hotherSecond))
        (hstarSecond other hotherFirst hotherSecond)
    have hprod := pos_atomPairingProduct_of_tripleParity_eq_one design
      (hcoherent other hotherFirst hotherSecond) hprodNe
    have hswap : atomPairing design other edgeSecond = atomPairing design edgeSecond other :=
      atomPairing_comm design other edgeSecond
    have hweight := design.weight_pos other
    rw [hswap]
    nlinarith [hprod, hweight]
  have hsumPos : 0 < ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      atomPairing design edgeFirst edgeSecond * (design.weight other
        * (atomPairing design edgeFirst other * atomPairing design other edgeSecond)) :=
    Finset.sum_pos htermPos hnonempty
  rw [← Finset.mul_sum, hlaw] at hsumPos
  have hsq : 0 < atomPairing design edgeFirst edgeSecond ^ 2 := by positivity
  nlinarith [hsumPos, hsq]

/-- **THE STAR LAW, INCOHERENT SIDE.**  An incoherent-saturated edge has its own
pairing nonzero and its two shares summing to strictly more than one. -/
theorem one_lt_atomShare_add_of_incoherentStar (design : WeightedDesign 6 3)
    {edgeFirst edgeSecond : Fin 6} (hedge : edgeFirst ≠ edgeSecond)
    (hstarFirst : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeFirst other ≠ 0)
    (hstarSecond : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeSecond other ≠ 0)
    (hincoherent : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      tripleParity design edgeFirst edgeSecond other = -1) :
    atomPairing design edgeFirst edgeSecond ≠ 0
      ∧ 1 < atomShare design edgeFirst + atomShare design edgeSecond := by
  have hpairNe : atomPairing design edgeFirst edgeSecond ≠ 0 := fun hzero =>
    not_forall_incoherent_of_orthogonalEdge design hedge hzero hstarFirst hstarSecond hincoherent
  refine ⟨hpairNe, ?_⟩
  have hlaw := sum_erasePair_weight_mul_atomPairing design hedge
  have hnonempty :
      ((Finset.univ.erase edgeFirst).erase edgeSecond : Finset (Fin 6)).Nonempty := by
    rw [← Finset.card_pos,
      Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hedge, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    norm_num
  have htermNeg : ∀ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      atomPairing design edgeFirst edgeSecond * (design.weight other
        * (atomPairing design edgeFirst other * atomPairing design other edgeSecond)) < 0 := by
    intro other hother
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hother
    obtain ⟨hotherSecond, hotherFirst⟩ := hother
    have hprodNe : atomPairing design edgeFirst edgeSecond * atomPairing design edgeFirst other
        * atomPairing design edgeSecond other ≠ 0 :=
      mul_ne_zero (mul_ne_zero hpairNe (hstarFirst other hotherFirst hotherSecond))
        (hstarSecond other hotherFirst hotherSecond)
    have hprod := neg_atomPairingProduct_of_tripleParity_eq_neg_one design
      (hincoherent other hotherFirst hotherSecond) hprodNe
    have hswap : atomPairing design other edgeSecond = atomPairing design edgeSecond other :=
      atomPairing_comm design other edgeSecond
    have hweight := design.weight_pos other
    rw [hswap]
    nlinarith [hprod, hweight]
  have hsumNeg : ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      atomPairing design edgeFirst edgeSecond * (design.weight other
        * (atomPairing design edgeFirst other * atomPairing design other edgeSecond)) < 0 :=
    Finset.sum_neg htermNeg hnonempty
  rw [← Finset.mul_sum, hlaw] at hsumNeg
  have hsq : 0 < atomPairing design edgeFirst edgeSecond ^ 2 := by positivity
  nlinarith [hsumNeg, hsq]

/-- **THE UNIFIED STAR LAW.**  A sign-saturated edge with nonvanishing star has its own
pairing nonzero and its two shares OFF one.  Every one of the four shipped lemmas it
replaces is the specialisation of this to one parity and one vanishing regime. -/
theorem atomShare_add_ne_one_of_saturatedStar (design : WeightedDesign 6 3)
    {edgeFirst edgeSecond : Fin 6} (hedge : edgeFirst ≠ edgeSecond)
    (hstarFirst : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeFirst other ≠ 0)
    (hstarSecond : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeSecond other ≠ 0)
    (hsaturated : (∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
        tripleParity design edgeFirst edgeSecond other = 1)
      ∨ ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
        tripleParity design edgeFirst edgeSecond other = -1) :
    atomPairing design edgeFirst edgeSecond ≠ 0
      ∧ atomShare design edgeFirst + atomShare design edgeSecond ≠ 1 := by
  rcases hsaturated with hcoherent | hincoherent
  · obtain ⟨hpair, hshare⟩ :=
      atomShare_add_lt_one_of_coherentStar design hedge hstarFirst hstarSecond hcoherent
    exact ⟨hpair, ne_of_lt hshare⟩
  · obtain ⟨hpair, hshare⟩ :=
      one_lt_atomShare_add_of_incoherentStar design hedge hstarFirst hstarSecond hincoherent
    exact ⟨hpair, (ne_of_lt hshare).symm⟩

/-- **THE CONTRAPOSITIVE, READ AT THE SHARES.**  An edge whose two shares sum to
exactly one has BOTH parities among its four triples.  The orthogonal-edge law is the
case where the edge pairing vanishes and the right-hand side of the edge law dies for
that reason instead. -/
theorem not_saturatedStar_of_atomShare_add_eq_one (design : WeightedDesign 6 3)
    {edgeFirst edgeSecond : Fin 6} (hedge : edgeFirst ≠ edgeSecond)
    (hstarFirst : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeFirst other ≠ 0)
    (hstarSecond : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeSecond other ≠ 0)
    (hshare : atomShare design edgeFirst + atomShare design edgeSecond = 1) :
    ¬ ((∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
        tripleParity design edgeFirst edgeSecond other = 1)
      ∨ ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
        tripleParity design edgeFirst edgeSecond other = -1) := fun hsaturated =>
  (atomShare_add_ne_one_of_saturatedStar design hedge hstarFirst hstarSecond hsaturated).2 hshare

/-! ## The zero-pairing branch

`Gtz.SixThreeCrux.linkWord_mem_residualSectors` and the sign band both carry a GLOBAL
nonvanishing hypothesis, and a crux is not known to supply it: the honest entry point is
`Gtz.SixThreeCrux.two_le_card_coherentPairsThroughBase_or_exists_orthogonalPair`.  The
two obtuse levers genuinely FAIL in the vanishing branch rather than merely resisting
proof -- `Gtz.IsPairwiseObtuse` demands strict negativity and the non-strict cap in
`R^3` is six, not four.  What survives there is the star law, and it is strong. -/

/-- **BOTH PARITIES THROUGH AN ORTHOGONAL EDGE.**  At a crux, an orthogonal edge whose
star does not vanish carries a coherent triple AND an incoherent triple among its four.
Measured on the sector table outside Lean, this constraint outweighs the loss of the two
obtuse levers: one orthogonal edge leaves 840 of the 1024 two-graphs with it against 958
without, and the nonvanishing branch leaves 842. -/
theorem SixThreeCrux.exists_coherent_and_exists_incoherent_through_orthogonalEdge
    (crux : SixThreeCrux) {edgeFirst edgeSecond : Fin 6} (hedge : edgeFirst ≠ edgeSecond)
    (hzero : atomPairing crux.design edgeFirst edgeSecond = 0)
    (hstarFirst : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing crux.design edgeFirst other ≠ 0)
    (hstarSecond : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing crux.design edgeSecond other ≠ 0) :
    (∃ other : Fin 6, other ≠ edgeFirst ∧ other ≠ edgeSecond
        ∧ tripleParity crux.design edgeFirst edgeSecond other = 1)
      ∧ ∃ other : Fin 6, other ≠ edgeFirst ∧ other ≠ edgeSecond
        ∧ tripleParity crux.design edgeFirst edgeSecond other = -1 := by
  constructor
  · by_contra hnone
    refine not_forall_incoherent_of_orthogonalEdge crux.design hedge hzero hstarFirst
      hstarSecond ?_
    intro other hotherFirst hotherSecond
    rcases eq_or_ne (tripleParity crux.design edgeFirst edgeSecond other) 1 with hvalue | hvalue
    · exact absurd ⟨other, hotherFirst, hotherSecond, hvalue⟩ hnone
    · rcases tripleParity_eq_one_or_neg_one crux.design edgeFirst edgeSecond other with
        hcase | hcase
      · exact absurd hcase hvalue
      · exact hcase
  · by_contra hnone
    refine not_forall_coherent_of_orthogonalEdge crux.design hedge hzero hstarFirst
      hstarSecond ?_
    intro other hotherFirst hotherSecond
    rcases eq_or_ne (tripleParity crux.design edgeFirst edgeSecond other) (-1) with hvalue | hvalue
    · exact absurd ⟨other, hotherFirst, hotherSecond, hvalue⟩ hnone
    · exact tripleParity_eq_one_of_ne_neg_one crux.design hvalue

/-- **THE ORTHOGONALITY GRAPH OF A CRUX IS TRIANGLE-FREE**, read as a statement about
edges rather than about triples: two atoms orthogonal to a common third are not
orthogonal to each other.  This is `Gtz.SixThreeCrux.hasNoOrthogonalTriple` in the shape
a graph argument consumes, and it is what keeps the vanishing branch from collapsing. -/
theorem SixThreeCrux.atomPairing_ne_zero_of_common_orthogonalPartner (crux : SixThreeCrux)
    {base edgeFirst edgeSecond : Fin 6} (hbaseFirst : base ≠ edgeFirst)
    (hbaseSecond : base ≠ edgeSecond) (hedge : edgeFirst ≠ edgeSecond)
    (hfirst : atomPairing crux.design base edgeFirst = 0)
    (hsecond : atomPairing crux.design base edgeSecond = 0) :
    atomPairing crux.design edgeFirst edgeSecond ≠ 0 := fun hzero =>
  crux.hasNoOrthogonalTriple base edgeFirst edgeSecond hbaseFirst hbaseSecond hedge
    ⟨hfirst, hsecond, hzero⟩

/-! ## The residual sector set under two-graph complement

`Gtz.IsChartDual` gives every `(6,3)` design a partner with the SAME weights and the
COMPLEMENT two-graph, and the partner is again a design, so the three levers apply to it
verbatim.  The sector filter is therefore complement-symmetric, and that is decidable.
This is the LICENSED reading of the duality filter: what is NOT licensed, and what the
campaign brief asked for, is that the complement pattern be carried by another CRUX --
the chart dual is not one, and `Gtz.exists_naimarkDual_dominates_and_chartDual_not_dominates`
shows it is not the Naimark dual either. -/

/-- **THE RESIDUE IS COMPLEMENT-SYMMETRIC.**  Complementing every parity of a two-graph
complements its link at atom zero, which on ten bits is exclusive-or with `1023`; the
residue is closed under it, because the two obtuse levers exchange and the
saturated-matching law forbids both signs. -/
theorem sectorSurvives_xor_of_sectorSurvives :
    ((List.range 1024).all fun link =>
      !sectorSurvives link || sectorSurvives (link ^^^ 1023)) = true := by decide +kernel

/-- The `Finset` reading of the same fact. -/
theorem xor_mem_residualSectors_of_mem_residualSectors {link : ℕ}
    (hmem : link ∈ residualSectors) : link ^^^ 1023 ∈ residualSectors := by
  rw [mem_residualSectors_iff] at hmem ⊢
  obtain ⟨hlt, hsurvives⟩ := hmem
  refine ⟨Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 10) hlt (by norm_num)) (by norm_num), ?_⟩
  have hall := sectorSurvives_xor_of_sectorSurvives
  rw [List.all_eq_true] at hall
  have := hall link (List.mem_range.2 hlt)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with hfalse | htrue
  · exact absurd hsurvives (by rw [hfalse]; simp)
  · exact htrue

/-! ## The frontier

Everything the campaign landed about a `(6,3)` crux, in one hypothesis-free statement.
The sign layer necessarily appears as a dichotomy: both of its branches carry content,
and neither is empty. -/

/-- **THE `(6,3)` EXCLUSION FRONTIER.**  Every `Gtz.SixThreeCrux` satisfies all of this,
with no hypothesis whatever.  Nothing in the conjunction is contradictory -- that is the
honest state of the wall cell, and the sign dichotomy is where the remaining work is. -/
theorem SixThreeCrux.frontier (crux : SixThreeCrux) :
    -- the chart window, both ends
    (-(4 / 27 : ℝ) ≤ chartObjective (chartPointOfDesign crux.design)
        ∧ chartObjective (chartPointOfDesign crux.design) < 0)
    -- the active family carries at least three blocks
    ∧ 3 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card
    -- the per-triple sign-blind window, and the squeeze that reads it as a parity
    ∧ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
        excessGap crux.design first second third
            < heavyExcess crux.design first * heavyExcess crux.design second
              * heavyExcess crux.design third / 4
          ∧ (0 ≤ excessGap crux.design first second third →
            tripleParity crux.design first second third = -1))
    -- the co-singleton window, both ends
    ∧ (∀ atomIndex : Fin 6, (subsetSum crux.design {atomIndex}ᶜ - 1).PosDef
        ∧ ¬ (subsetSum crux.design {atomIndex}ᶜ - (5 : ℝ) • 1).PosSemidef)
    -- the domination window: a triple at three fifths, and none at one
    ∧ (∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum crux.design selected - (3 / 5 : ℝ) • 1).PosSemidef)
    ∧ (∀ selected : Finset (Fin 6), selected.card = 3 → ¬ Dominates crux.design selected)
    -- the orthogonality graph is triangle-free
    ∧ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
        ¬ (atomPairing crux.design first second = 0 ∧ atomPairing crux.design first third = 0
          ∧ atomPairing crux.design second third = 0))
    -- THE SIGN DICHOTOMY, both branches with their content
    ∧ (((∀ first second : Fin 6, first ≠ second → atomPairing crux.design first second ≠ 0)
          ∧ linkWordOf crux.design ∈ residualSectors
          ∧ (4 ≤ (coherentTripleSets crux.design).card
            ∧ (coherentTripleSets crux.design).card ≤ 16)
          ∧ ∀ base : Fin 6, 2 ≤ (coherentPairsThroughBase crux.design base).card
            ∧ (coherentPairsThroughBase crux.design base).card ≤ 8)
      ∨ (∃ first second : Fin 6, first ≠ second ∧ atomPairing crux.design first second = 0)
          ∧ ∀ edgeFirst edgeSecond : Fin 6, edgeFirst ≠ edgeSecond →
              atomPairing crux.design edgeFirst edgeSecond = 0 →
              (∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
                atomPairing crux.design edgeFirst other ≠ 0) →
              (∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
                atomPairing crux.design edgeSecond other ≠ 0) →
              (∃ other : Fin 6, other ≠ edgeFirst ∧ other ≠ edgeSecond
                  ∧ tripleParity crux.design edgeFirst edgeSecond other = 1)
                ∧ ∃ other : Fin 6, other ≠ edgeFirst ∧ other ≠ edgeSecond
                  ∧ tripleParity crux.design edgeFirst edgeSecond other = -1) := by
  refine ⟨crux.chartObjective_mem_window, crux.three_le_card_chartArgmaxFamily,
    fun first second third hfirstSecond hfirstThird hsecondThird =>
      ⟨crux.excessGap_lt_quarter_mul_heavyExcess_prod hfirstSecond hfirstThird hsecondThird,
        fun hgap => crux.tripleParity_eq_neg_one_of_excessGap_nonneg hfirstSecond hfirstThird
          hsecondThird hgap⟩,
    crux.coSingletonWindow, crux.exists_dominates_at_three_fifths, crux.hasNoDominatingTriple,
    crux.hasNoOrthogonalTriple, ?_⟩
  by_cases hnonzero : ∀ first second : Fin 6, first ≠ second →
      atomPairing crux.design first second ≠ 0
  · obtain ⟨hglobal, hperBase, _, _, _⟩ := crux.signBandAndCensusCeiling hnonzero
    exact Or.inl ⟨hnonzero, crux.linkWord_mem_residualSectors hnonzero, hglobal, hperBase⟩
  · refine Or.inr ⟨?_, fun edgeFirst edgeSecond hedge hzero hstarFirst hstarSecond =>
      crux.exists_coherent_and_exists_incoherent_through_orthogonalEdge hedge hzero
        hstarFirst hstarSecond⟩
    by_contra hnone
    refine hnonzero fun first second hne hzero => hnone ⟨first, second, hne, hzero⟩

/-! ## The refutation target

The frontier is a statement about a `Gtz.SixThreeCrux`, which carries chart data no
search can evaluate.  Projecting it onto the design gives a predicate with no chart in
it, so a counterexample hunt has an explicit semialgebraic box to dig in -- and, by the
contrapositive below, emptying that box SUFFICES for the wall cell. -/

/-- **THE `(6,3)` REFUTATION TARGET.**  A design-level predicate, every conjunct
checkable from the atoms and weights alone.  Any failure of `Gtz.GtzWeighted 6 3`
produces a design satisfying it. -/
def IsSixThreeRefutationCandidate (design : WeightedDesign 6 3) : Prop :=
  AllHeavy design
    ∧ HasStrictlyDominatingCoSingletons design
    ∧ ¬ HasParallelPair design
    ∧ ¬ IsEqualShare design
    ∧ (∀ selected : Finset (Fin 6), selected.card = 3 → ¬ Dominates design selected)
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

/-- Every crux's design is a refutation candidate. -/
theorem isSixThreeRefutationCandidate_of_sixThreeCrux (crux : SixThreeCrux) :
    IsSixThreeRefutationCandidate crux.design := by
  obtain ⟨_, _, _, hcoSingleton, hdominates, hnoTriple, hsign⟩ := crux.frontier
  exact ⟨crux.isAllHeavy, crux.hasStrictlyDominatingCoSingletons, crux.hasNoParallelPair,
    crux.avoidsEqualShareStratum, crux.hasNoDominatingTriple,
    crux.exists_dominates_at_three_fifths, fun atomIndex => (crux.coSingletonWindow atomIndex).2,
    crux.hasNoOrthogonalTriple,
    fun first second third hfirstSecond hfirstThird hsecondThird =>
      crux.excessGap_lt_quarter_mul_heavyExcess_prod hfirstSecond hfirstThird hsecondThird,
    fun first second third hfirstSecond hfirstThird hsecondThird hgap =>
      crux.tripleParity_eq_neg_one_of_excessGap_nonneg hfirstSecond hfirstThird hsecondThird hgap,
    fun hnonzero => crux.linkWord_mem_residualSectors hnonzero⟩

/-- **THE REFUTATION TARGET IS REACHED BY EVERY FAILURE.** -/
theorem exists_isSixThreeRefutationCandidate_of_not_gtzWeighted_six_three
    (hfail : ¬ GtzWeighted 6 3) :
    ∃ design : WeightedDesign 6 3, IsSixThreeRefutationCandidate design := by
  obtain ⟨crux⟩ := nonempty_sixThreeCrux_of_not_gtzWeighted_six_three hfail
  exact ⟨crux.design, isSixThreeRefutationCandidate_of_sixThreeCrux crux⟩

/-- **THE SEARCH CRITERION.**  Emptying the box SUFFICES for the wall cell. -/
theorem gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidate
    (hnone : ∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidate design) :
    GtzWeighted 6 3 := by
  by_contra hfail
  obtain ⟨design, hcandidate⟩ :=
    exists_isSixThreeRefutationCandidate_of_not_gtzWeighted_six_three hfail
  exact hnone design hcandidate

/-- The wall cell in the shape `Gtz.gtzWeightedAll_three_of_isEmpty_cruxes` consumes. -/
theorem isEmpty_sixThreeCrux_of_gtzWeighted_six_three (hweighted : GtzWeighted 6 3) :
    IsEmpty SixThreeCrux :=
  not_nonempty_iff.1 fun hnonempty =>
    nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three.1 hnonempty hweighted

/-- **WHAT EMPTYING THE BOX BUYS, AT RANK THREE.**  Together with the `(7,3)` half it
carries `Gtz.GtzWeightedAll 3` outright. -/
theorem gtzWeightedAll_three_of_forall_not_isSixThreeRefutationCandidate
    (hnone : ∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidate design)
    (hsevenEmpty : IsEmpty SevenThreeCrux) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_isEmpty_cruxes
    (isEmpty_sixThreeCrux_of_gtzWeighted_six_three
      (gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidate hnone)) hsevenEmpty

/-- **AND THE 1997 STATEMENT ITSELF**, for every positive `n`, through
`Gtz.original_of_weighted`.  This is the terminus of the reduction: a `(6,3)` search
that empties the box, plus `(7,3)`, settles rank three of the Goreinov-Tyrtyshnikov-
Zamarashkin conjecture. -/
theorem gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidate
    (hnone : ∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidate design)
    (hsevenEmpty : IsEmpty SevenThreeCrux) (atomCount : ℕ) (hpos : 0 < atomCount) :
    GtzOriginal atomCount 3 :=
  original_of_weighted 3
    (gtzWeightedAll_three_of_forall_not_isSixThreeRefutationCandidate hnone hsevenEmpty)
    atomCount hpos

end Gtz

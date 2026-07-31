/-
# The lifted (disjunction-free) presentation of `DiscriminantCovering 7`, and the
# two obstructions that survive it

`Gtz/Certificates/PositivstellensatzObstruction.lean` kills the Putinar/Schmuedgen
half of the Positivstellensatz for the TIE system at every degree, and
`Gtz/Quantitative/PositivstellensatzRankThree.lean` proves a cardinality floor of
four on the multiplier support of the surviving strict Stengle form.  Both carry
an explicit scope caveat:

  (i)  they quantify over designs at which every TIE leg is `<= 0`, which
       `Gtz.exists_tieNonneg_notDominates_seven` shows is strictly weaker than the
       covering, so neither statement is about `Gtz.DiscriminantCovering 7` itself;
  (ii) the degree reading is presentation dependent, and that file offers an
       explicit escape: LIFT the two-leg disjunction by one auxiliary variable
       `u_T` per triple, with ideal generator `(e_2(T) - u_T)(e_3(T) - u_T) = 0`,
       cone generators `e_2(T) - u_T >= 0` and `e_3(T) - u_T >= 0`, and strict
       generator `-u_T > 0`.  On that system `u_T = min(e_2(T), e_3(T))`, the
       failure set is BASIC, and the strict generators have degree one.

This file works in the lifted presentation and shows both obstructions survive it.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `minimumLeg` — the value the lifted variable is forced to take.
* `closedCoveringFailure_min_inhabited_seven` — the closed lifted failure system
  is INHABITED, at the split tetrahedron, through its rainbow triples where the
  minimum leg is exactly `0`.  An inhabited closed basic system has no emptiness
  certificate of any kind, so the lifting does not restore the Putinar half.
  NOT to be confused with the shipped
  `Gtz.closedCoveringFailure_inhabited_seven`, which is the DISJUNCTION reading
  (`trace <= 0 OR tie <= 0`); the `_min_` infix distinguishes them.
* `not_hasUniformCoveringAggregateSeven` — the degree-free form: no strictly
  positive floor is cleared by any nonnegatively weighted aggregate of the
  minimum legs, weights being arbitrary real functions of the design.  This
  removes scope caveat (i) from the shipped
  `Gtz.not_hasUniformTieAggregateSeven`.
* `isStengleCoveringSupportSeven_increasing_iff` — the CALIBRATION, and the point
  of the whole file: at FULL support the lifted support condition is EXACTLY
  `Gtz.GtzWeightedAll 3`, rank three GTZ for every `n`.  Contrast the shipped
  `Gtz.isStengleTieSupportSeven_increasing_iff`, which calibrates the tie-system
  notion to "some triple has tie leg `>= 0`": that is a CONSEQUENCE of rank three
  and not equivalent to it, which is exactly the gap
  `Gtz.exists_tieNonneg_notDominates_seven` exhibits.  The lifted notion has no
  such gap, so the floor below is a floor on a certificate for the covering.
* `four_le_card_of_isStengleCoveringSupportSeven` — the cardinality floor
  transports verbatim, because at a THIN block design the minimum leg is
  `min(1, -8) = -8` on a direction-repeating triple and `min(9, 0) = 0` on a
  rainbow one, so it has the SAME vanishing set as the tie leg.

## NOT proved here

No DEGREE floor.  In the lifted presentation the strict generators have degree
one, so four generators give degree four, and the `12`/`24` reading of the tie
presentation does not transport.  Only the cardinality floor does; scope caveat
(ii) is therefore NOT recovered, only caveat (i).

The floor is FOUR, not five.  The scratch report proposed raising it to five by
splitting the diamond `M(K4-e)` tie primitive `Gtz.diamondTieDesign` into `(7,3)`;
that upgrade is NOT mechanized anywhere and must not be cited as if it were.  A
diamond-split all-heavy `(7,3)` design with all thirty-five legs `<= 0` would make
`four_le_card_of_isStengleCoveringSupportSeven` immediately strengthenable.

Provenance: scratch report 17 (`sos-agent`).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.DecisionAtlasSevenThree
import Gtz.Quantitative.PositivstellensatzRankThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Gtz

/-! ## The lifted variable -/

/-- **The value the lifted variable is forced to take at a triple**: the minimum
of the two `S_3`-invariant legs.  The lifted system's cone generators
`e_2 - u >= 0`, `e_3 - u >= 0` together with the ideal generator
`(e_2 - u)(e_3 - u) = 0` say exactly `u = min(e_2, e_3)`, and the strict
generator `-u > 0` then says the triple fails to dominate. -/
noncomputable def minimumLeg (design : WeightedDesign 7 3)
    (triple : Fin 7 × Fin 7 × Fin 7) : ℝ :=
  min (discriminantMinorSum design triple.1 triple.2.1 triple.2.2)
    (discriminantTie design triple.1 triple.2.1 triple.2.2)

theorem minimumLeg_le_tie (design : WeightedDesign 7 3) (triple : Fin 7 × Fin 7 × Fin 7) :
    minimumLeg design triple ≤ discriminantTie design triple.1 triple.2.1 triple.2.2 :=
  min_le_right _ _

theorem minimumLeg_nonneg_iff (design : WeightedDesign 7 3)
    (triple : Fin 7 × Fin 7 × Fin 7) :
    0 ≤ minimumLeg design triple ↔
      0 ≤ discriminantMinorSum design triple.1 triple.2.1 triple.2.2
        ∧ 0 ≤ discriminantTie design triple.1 triple.2.1 triple.2.2 :=
  le_min_iff

theorem minimumLeg_of_legs (design : WeightedDesign 7 3)
    (triple : Fin 7 × Fin 7 × Fin 7) {minorValue tieValue : ℝ}
    (hminor : discriminantMinorSum design triple.1 triple.2.1 triple.2.2 = minorValue)
    (htie : discriminantTie design triple.1 triple.2.1 triple.2.2 = tieValue) :
    minimumLeg design triple = min minorValue tieValue := by
  rw [minimumLeg, hminor, htie]

/-! ## The Putinar half is unavailable in the lifted presentation too -/

/-- **The closed LIFTED failure system is inhabited.**  Relaxing the strict
generators `-u_T > 0` to `-u_T >= 0` produces a basic closed semialgebraic system
that the split tetrahedron satisfies, through its rainbow triples where the
minimum leg is exactly `0` and its direction-repeating triples where it is `-8`.
An inhabited closed basic system has no emptiness certificate of any kind, so the
lifting offered as an escape from the degree reading does not restore the Putinar
half. -/
theorem closedCoveringFailure_min_inhabited_seven :
    ∃ design : WeightedDesign 7 3, AllHeavy design ∧
      ∀ triple ∈ increasingTriplesSeven, minimumLeg design triple ≤ 0 := by
  refine ⟨splitSevenDesign, splitSevenDesign_allHeavy, fun triple hmem => ?_⟩
  obtain ⟨hpivotFirst, hpivotSecond, hpairDistinct⟩ := increasingTriplesSeven_distinct hmem
  exact (minimumLeg_le_tie splitSevenDesign triple).trans
    (splitSevenDesign_discriminantTie_nonpos hpivotFirst hpivotSecond hpairDistinct)

/-- **A uniformly positive nonnegatively weighted MINIMUM-LEG aggregate**: what a
Putinar or Schmuedgen certificate for the emptiness of the closed lifted system
delivers after rearranging its certifying identity.  The weights are arbitrary
real-valued functions of the design — no degree bound, no polynomiality, no
equivariance. -/
def HasUniformCoveringAggregateSeven : Prop :=
  ∃ floor : ℝ, 0 < floor ∧
    ∀ design : WeightedDesign 7 3, AllHeavy design →
      ∃ weight : Fin 7 × Fin 7 × Fin 7 → ℝ, (∀ triple, 0 ≤ weight triple) ∧
        floor ≤ ∑ triple ∈ increasingTriplesSeven, weight triple * minimumLeg design triple

theorem splitSevenDesign_weightedMinimumLegAggregate_nonpos
    (weight : Fin 7 × Fin 7 × Fin 7 → ℝ) (hweightNonneg : ∀ triple, 0 ≤ weight triple) :
    ∑ triple ∈ increasingTriplesSeven,
        weight triple * minimumLeg splitSevenDesign triple ≤ 0 := by
  refine Finset.sum_nonpos fun triple hmem => ?_
  obtain ⟨hpivotFirst, hpivotSecond, hpairDistinct⟩ := increasingTriplesSeven_distinct hmem
  exact mul_nonpos_of_nonneg_of_nonpos (hweightNonneg triple)
    ((minimumLeg_le_tie splitSevenDesign triple).trans
      (splitSevenDesign_discriminantTie_nonpos hpivotFirst hpivotSecond hpairDistinct))

/-- **THE DEGREE-FREE OBSTRUCTION, IN THE LIFTED PRESENTATION.**  No uniformly
positive nonnegatively weighted minimum-leg aggregate exists at `(7,3)`, so no
Putinar and no Schmuedgen certificate for the LIFTED covering system exists at any
degree.  This closes the escape route: the lifting removes the disjunction and
drops the strict generators to degree one, but it does not make the closed system
empty, and emptiness of the closed system is exactly what the Putinar half needs. -/
theorem not_hasUniformCoveringAggregateSeven : ¬ HasUniformCoveringAggregateSeven := by
  rintro ⟨floor, hfloorPos, hcertificate⟩
  obtain ⟨weight, hweightNonneg, hfloorLe⟩ :=
    hcertificate splitSevenDesign splitSevenDesign_allHeavy
  exact absurd (hfloorLe.trans
    (splitSevenDesign_weightedMinimumLegAggregate_nonpos weight hweightNonneg))
    (not_le.mpr hfloorPos)

/-! ## The multiplier-support floor, now for the COVERING and not for the tie leg -/

/-- **The strict-generator support of a Stengle monoid multiplier, in the lifted
presentation.**  A strict Stengle certificate for the emptiness of the lifted
failure system carries a factor `prod over a support of (-u_T)^(e_T)` with every
`e_T >= 1`.  At every point of the CLOSED system the monoid part must vanish while
the region's own strict generators `t_c` and `heavyExcess c` do not, and a product
of reals vanishes exactly when one factor does — so the support must contain, at
every such point, a triple whose lifted variable is exactly `0`, i.e. whose two
symmetric legs have minimum `0`. -/
def IsStengleCoveringSupportSeven (support : Finset (Fin 7 × Fin 7 × Fin 7)) : Prop :=
  ∀ design : WeightedDesign 7 3, AllHeavy design →
    (∀ triple ∈ increasingTriplesSeven, minimumLeg design triple ≤ 0) →
      ∃ triple ∈ support, minimumLeg design triple = 0

/-- **THE CALIBRATION, and the reason the lifted notion is the right one.**  At
FULL support the lifted support condition is EXACTLY `Gtz.GtzWeightedAll 3` — rank
three GTZ for every `n`.  Contrast `Gtz.isStengleTieSupportSeven_increasing_iff`,
which calibrates the tie-system notion to "the tie leg alone covers": that is a
CONSEQUENCE of rank three and not equivalent to it, which is exactly the scope
gap `Gtz.exists_tieNonneg_notDominates_seven` exhibits.  The lifted notion has no
such gap, so the floor below is a floor on a certificate for the covering. -/
theorem isStengleCoveringSupportSeven_increasing_iff :
    IsStengleCoveringSupportSeven increasingTriplesSeven ↔ GtzWeightedAll 3 := by
  rw [← symmetricCoveringSeven_iff_rank_three, symmetricCoveringSeven_iff_increasingTriples]
  constructor
  · intro hsupport design hheavy
    by_cases hnonpos : ∀ triple ∈ increasingTriplesSeven, minimumLeg design triple ≤ 0
    · obtain ⟨triple, hmem, hzero⟩ := hsupport design hheavy hnonpos
      exact ⟨triple, hmem, (minimumLeg_nonneg_iff design triple).mp (le_of_eq hzero.symm)⟩
    · push Not at hnonpos
      obtain ⟨triple, hmem, hpositive⟩ := hnonpos
      exact ⟨triple, hmem, (minimumLeg_nonneg_iff design triple).mp hpositive.le⟩
  · intro hcover design hheavy hnonpos
    obtain ⟨triple, hmem, hminor, htie⟩ := hcover design hheavy
    exact ⟨triple, hmem, le_antisymm (hnonpos triple hmem)
      ((minimumLeg_nonneg_iff design triple).mpr ⟨hminor, htie⟩)⟩

/-- At a THIN block design the minimum leg has the SAME vanishing set as the tie
leg: `min(9, 0) = 0` on a rainbow triple and `min(1, -8) = -8` on a triple
repeating a direction.  The `e_2` leg never binds on this family
(`Gtz.tetraBlockDesign_symmetricSignature`), which is precisely why the tie-system
floor transports to the lifted presentation unchanged. -/
theorem tetraBlockDesign_minimumLeg_of_repeated {blocks : Fin 7 → Fin 4}
    (hthin : IsThinBlockMap blocks) {triple : Fin 7 × Fin 7 × Fin 7}
    (hmem : triple ∈ increasingTriplesSeven)
    (hshares : isBlockSharedInTriple blocks triple = true) :
    minimumLeg (tetraBlockDesign blocks hthin.1) triple = -8 := by
  obtain ⟨hpivotFirst, hpivotSecond, hpairDistinct⟩ := increasingTriplesSeven_distinct hmem
  have hrepeat := blocksAgreeSomewhere_of_isBlockSharedInTriple hshares
  rw [minimumLeg_of_legs _ triple
    (tetraBlockDesign_discriminantMinorSum_of_repeated hthin hpivotFirst hpivotSecond
      hpairDistinct hrepeat)
    (tetraBlockDesign_discriminantTie_of_repeated hthin hpivotFirst hpivotSecond
      hpairDistinct hrepeat)]
  norm_num

theorem tetraBlockDesign_minimumLeg_nonpos {blocks : Fin 7 → Fin 4}
    (hthin : IsThinBlockMap blocks) {triple : Fin 7 × Fin 7 × Fin 7}
    (hmem : triple ∈ increasingTriplesSeven) :
    minimumLeg (tetraBlockDesign blocks hthin.1) triple ≤ 0 := by
  obtain ⟨hpivotFirst, hpivotSecond, hpairDistinct⟩ := increasingTriplesSeven_distinct hmem
  exact (minimumLeg_le_tie _ triple).trans
    (tetraBlockDesign_discriminantTie_nonpos hthin hpivotFirst hpivotSecond hpairDistinct)

/-- **THE SUPPORT FLOOR FOR THE COVERING.**  No set of at most three triples is
the strict-generator support of a Stengle certificate for the LIFTED covering
system at `(7,3)`.  Same witness and same kernel search as the tie-system floor —
`Gtz.hasSharedBlockForEveryTrio_true` — because the minimum leg vanishes exactly
where the tie leg does on the tetrahedral block family. -/
theorem not_isStengleCoveringSupportSeven_of_card_le_three
    {support : Finset (Fin 7 × Fin 7 × Fin 7)} (hsubset : support ⊆ increasingTriplesSeven)
    (hcard : support.card ≤ 3) : ¬ IsStengleCoveringSupportSeven support := by
  obtain ⟨enlarged, hsupportSub, hEnlargedSub, hcardThree⟩ :=
    Finset.exists_subsuperset_card_eq hsubset hcard
      (by rw [increasingTriplesSeven_card]; norm_num)
  obtain ⟨first, second, third, -, -, -, hEnlarged⟩ := Finset.card_eq_three.mp hcardThree
  have hfirstMem : first ∈ increasingTriplesSeven := hEnlargedSub (by rw [hEnlarged]; simp)
  have hsecondMem : second ∈ increasingTriplesSeven := hEnlargedSub (by rw [hEnlarged]; simp)
  have hthirdMem : third ∈ increasingTriplesSeven := hEnlargedSub (by rw [hEnlarged]; simp)
  obtain ⟨blocks, hblocksMem, hfirstShares, hsecondShares, hthirdShares⟩ :=
    exists_blockMap_sharing (mem_triplesSevenList_of_mem_increasing hfirstMem)
      (mem_triplesSevenList_of_mem_increasing hsecondMem)
      (mem_triplesSevenList_of_mem_increasing hthirdMem)
  have hthin : IsThinBlockMap blocks := blockMapsSeven_thin blocks hblocksMem
  intro hstengle
  obtain ⟨triple, hmem, hzero⟩ := hstengle (tetraBlockDesign blocks hthin.1)
    (tetraBlockDesign_allHeavy blocks hthin.1)
    (fun triple hmem => tetraBlockDesign_minimumLeg_nonpos hthin hmem)
  have hinEnlarged : triple ∈ ({first, second, third} : Finset (Fin 7 × Fin 7 × Fin 7)) := by
    rw [← hEnlarged]; exact hsupportSub hmem
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hinEnlarged
  rcases hinEnlarged with hchoice | hchoice | hchoice
  · rw [hchoice, tetraBlockDesign_minimumLeg_of_repeated hthin hfirstMem hfirstShares] at hzero
    norm_num at hzero
  · rw [hchoice, tetraBlockDesign_minimumLeg_of_repeated hthin hsecondMem hsecondShares] at hzero
    norm_num at hzero
  · rw [hchoice, tetraBlockDesign_minimumLeg_of_repeated hthin hthirdMem hthirdShares] at hzero
    norm_num at hzero

/-- **The floor, as a cardinality statement, for a notion that is exactly rank
three at full support.**  Every strict-generator support of a Stengle certificate
for the lifted covering system at `(7,3)` has at least four triples.  Four, not
five: the diamond upgrade proposed alongside this result is not mechanized. -/
theorem four_le_card_of_isStengleCoveringSupportSeven
    {support : Finset (Fin 7 × Fin 7 × Fin 7)} (hsubset : support ⊆ increasingTriplesSeven)
    (hstengle : IsStengleCoveringSupportSeven support) : 4 ≤ support.card := by
  by_contra hsmall
  exact not_isStengleCoveringSupportSeven_of_card_le_three hsubset (by omega) hstengle

/-- **The lifted support notion is at least as strong as the tie one.**  Any
support that works for the lifted covering system also works for the all-tie
system, because at an all-tie design the minimum leg is at most the tie leg.  The
hypothesis is exactly the situation on the whole tetrahedral block family. -/
theorem isStengleCoveringSupportSeven_of_tie_hypotheses
    {support : Finset (Fin 7 × Fin 7 × Fin 7)}
    (hstengle : IsStengleCoveringSupportSeven support)
    (design : WeightedDesign 7 3) (hheavy : AllHeavy design)
    (htie : ∀ triple ∈ increasingTriplesSeven,
      discriminantTie design triple.1 triple.2.1 triple.2.2 ≤ 0) :
    ∃ triple ∈ support, minimumLeg design triple = 0 :=
  hstengle design hheavy fun triple hmem =>
    (minimumLeg_le_tie design triple).trans (htie triple hmem)

end Gtz

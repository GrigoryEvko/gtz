/-
# The on-path registry collapses onto the `(6,3)` hinge

The rank-three campaign carries seven registry axioms.  Five of them are ON
PATH: the line-free `U(3,6)` residual, the one-line residual, the two-meeting-
lines residual, the three-lines chart residual and the `K4` knife band.  This
module proves that those five, taken together, are EXACTLY the `(6,3)` hinge —
not a decomposition of it, not a narrowing of it, and not a sufficient
condition for it.

## What was missing

The tree already carried every forward arrow.  The five class statements
assemble into `Gtz.StressFreeHingeHoldsSixThree`
(`Gtz.stressFreeHingeHoldsSixThree_of_residualFamilies`), that assembles into
`Gtz.HingeHoldsAtSize 6 3` (`Gtz.hingeHoldsAtSize_sixThree_of_stressFreeHinge`,
whose two other inputs are unconditional theorems), and the design selector
`Gtz.ConsolidatedStrictTripleDesign` reaches all five at once
(`Gtz.allFiveOnPath_of_consolidatedStrictTripleDesign`).

Every BACKWARD arrow was absent.  Three of them are one line each, and this
module lands all three:

* `Gtz.residualFamiliesTieFree_of_hinge` — a stress-free design is primitive, so
  the hinge kills its ties directly.
* `Gtz.stressFreeHingeHoldsSixThree_of_hinge` — restriction.
* `Gtz.consolidatedStrictTripleDesign_of_hinge` — the hinge supplies weak
  domination through `Gtz.gtzWeighted_six_three_of_hinge`, and a primitive
  design with a weak dominator and no strict one IS a tie.

The third is the load-bearing one, and it is the reason the campaign stalled.

## The consequence

`Gtz.onPathRegistryCollapse` states the four equivalences in one theorem.  Read
it as a cost statement.  A proof of any one of

* the five class obligations together,
* `Gtz.StressFreeHingeHoldsSixThree`,
* `Gtz.ConsolidatedStrictTripleDesign`, or
* any of the eighteen `Gtz.allFiveOnPath_of_*` door hypotheses,

is a proof of `Gtz.HingeHoldsAtSize 6 3`, hence of `Gtz.GtzWeightedAll 3` —
the whole rank-three conjecture at every size.  None of them is cheaper than
any other, and no rewriting between them can make one cheaper.  Thirty-one
forks moved between these names.

## The vacuity law that explains the rest

Section 1 states the general fact behind the collapse.  A Prop of the shape

  `∀ design, IsPrimitiveDesign design → IsTie design → <anything>`

is IMPLIED BY the hinge at its own size and rank, because the hinge makes the
two antecedents contradictory.  Forty named Props in the tree have that shape,
including twenty in `Gtz/Reduction/Polar*.lean`, each shipped with a
`hingeHoldsAtSize_of_*` producer.  Every one of them is therefore equivalent to
the hinge, and the chain of "narrowings" between them narrows nothing.
`Gtz.polarTiltSelection_of_hinge` closes the first one; the others are the same
line with a different binder count.
-/
import Gtz.Wave.ChartDesignGauge
import Gtz.Wave.WiringDoorLedger
import Gtz.Wave.A1NeedleCollapse
import Gtz.Reduction.TrichotomyLedger
import Gtz.Reduction.BalancedStratumClosure
import Gtz.Reduction.PolarCoverDescent
import Gtz.Reduction.ParallelFreeReach
import Gtz.Design.CompanionConstruction
import Gtz.Design.StressFreeMatroidStratification
import Gtz.Design.LinePatternSixCasesTwo
import Gtz.Design.StratumEmptinessLedger
import Gtz.Uniform.SpectralWhitening

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

variable {size rank : ℕ}

/-! ## 1. The primitive-tie vacuity law

The hinge says a tie carries a parallel pair.  Primitivity says it does not.
So under the hinge no design satisfies both antecedents, and a Prop that
quantifies over exactly those designs is free.  This is stated at `Sort*` so it
applies under any number of further binders and at any conclusion. -/

/-- **UNDER THE HINGE, `IsPrimitiveDesign` AND `IsTie` ARE CONTRADICTORY.**  This
is the whole reason a residual of the shape
`∀ design, IsPrimitiveDesign design → IsTie design → …` records nothing beyond
`Gtz.HingeHoldsAtSize`. -/
theorem elim_primitive_isTie_of_hinge {motive : Prop} (hhinge : HingeHoldsAtSize size rank)
    {design : WeightedDesign size rank} (hprimitive : IsPrimitiveDesign design)
    (htie : IsTie design) : motive :=
  absurd (hhinge design htie) ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)

/-- **NO PRIMITIVE TIE SURVIVES THE HINGE.**  The same law in the form a reader
of a residual definition needs. -/
theorem not_isTie_of_isPrimitiveDesign_of_hinge (hhinge : HingeHoldsAtSize size rank)
    {design : WeightedDesign size rank} (hprimitive : IsPrimitiveDesign design) :
    ¬ IsTie design :=
  fun htie => elim_primitive_isTie_of_hinge hhinge hprimitive htie

/-- **THE POLAR TILT RESIDUAL IS FREE UNDER THE HINGE.**  Together with the
landed `Gtz.hingeHoldsAtSize_of_polarTilt` this makes the residual EQUAL to the
hinge, so the polar lane is a renaming rather than a reduction.  The other
nineteen polar residuals share the antecedent pair and close the same way. -/
theorem polarTiltSelection_of_hinge (hhinge : HingeHoldsAtSize size rank) :
    PolarTiltSelection size rank :=
  fun _design _pole _covering _margin hprimitive htie _hlong _hmargin _hcard _hmem _hcover =>
    elim_primitive_isTie_of_hinge hhinge hprimitive htie

/-- **THE POLAR RESIDUAL IS THE HINGE.**  Both directions, at every rank at
least two, granted the predecessor rank the landed producer already asks for. -/
theorem polarTiltSelection_iff_hingeHoldsAtSize (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) :
    PolarTiltSelection size rank ↔ HingeHoldsAtSize size rank :=
  ⟨hingeHoldsAtSize_of_polarTilt hrank hpredecessor, polarTiltSelection_of_hinge⟩

/-! ## 2. The stress-free arm is the whole hinge

One direction is the landed trichotomy assembly, whose other two inputs are
unconditional theorems.  The other direction is restriction. -/

/-- The hinge restricted to the stress-free stratum. -/
theorem stressFreeHingeHoldsSixThree_of_hinge (hhinge : HingeHoldsAtSize 6 3) :
    StressFreeHingeHoldsSixThree :=
  fun design _hstressFree htie => hhinge design htie

/-- **THE STRESS-FREE ARM CARRIES THE WHOLE `(6,3)` HINGE.**  Branch (ii) is
`Gtz.balancedStratumSelection_six_holds` and branch (iii) is
`Gtz.twoPoleStratumSelection_six_unconditional`, both unconditional, so the
trichotomy leaves exactly the stress-free arm. -/
theorem hingeHoldsAtSize_six_three_of_stressFreeHinge
    (hstressFree : StressFreeHingeHoldsSixThree) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_sixThree_of_stressFreeHinge twoPoleStratumSelection_six_unconditional
    (balancedStratumCapstone_of_balancedStratumSelection balancedStratumSelection_six_holds)
    hstressFree

/-- **THE STRESS-FREE HINGE IS THE HINGE.**  No information is lost by
restricting to the stress-free stratum at `(6,3)`. -/
theorem stressFreeHingeHoldsSixThree_iff_hingeHoldsAtSize_six_three :
    StressFreeHingeHoldsSixThree ↔ HingeHoldsAtSize 6 3 :=
  ⟨hingeHoldsAtSize_six_three_of_stressFreeHinge, stressFreeHingeHoldsSixThree_of_hinge⟩

/-! ## 3. The five class statements are the hinge

`Gtz.stressFreeResidualFamiliesSix` is the five-entry list of surviving matroid
classes: the line-free family, one line, two meeting lines, three lines, and the
`K4` family.  The five registry axioms are exactly the tie-freeness of these
five strata, reached through the landed per-class wiring. -/

/-- **THE FIVE ON-PATH CLASS STATEMENTS, AS ONE PROP.**  This is the exact
`hresidual` argument of `Gtz.stressFreeHingeHoldsSixThree_of_residualFamilies`,
and it is what the five registry axioms are spent on. -/
def StressFreeResidualFamiliesTieFree : Prop :=
  ∀ lines ∈ stressFreeResidualFamiliesSix, StressFreeStratumIsTieFree (lineFamilyPattern lines)

/-- The landed assembly, with the enumeration premise discharged. -/
theorem stressFreeHingeHoldsSixThree_of_residualFamiliesTieFree
    (hresidual : StressFreeResidualFamiliesTieFree) : StressFreeHingeHoldsSixThree :=
  stressFreeHingeHoldsSixThree_of_residualFamilies linearSpaceListIsComplete_six hresidual

/-- **THE HINGE EMPTIES EVERY STRESS-FREE STRATUM, AT EVERY PATTERN.**  A
stress-free design is primitive (`Gtz.isPrimitiveDesign_of_stressFree`), so the
hinge forbids it a tie.  No pattern data, no chart, no selector and no
matroid enumeration is used, and the pattern is arbitrary — the five residual
families are not special. -/
theorem stressFreeStratumIsTieFree_of_hinge (hhinge : HingeHoldsAtSize 6 3)
    (pattern : LinePattern 6) : StressFreeStratumIsTieFree pattern := by
  intro design _relabel hstressFree _hpattern htie
  exact elim_primitive_isTie_of_hinge hhinge (isPrimitiveDesign_of_stressFree design hstressFree)
    htie

/-- **THE HINGE GIVES ALL FIVE CLASS STATEMENTS AT ONCE.**  The five-pattern
instance of the previous theorem. -/
theorem residualFamiliesTieFree_of_hinge (hhinge : HingeHoldsAtSize 6 3) :
    StressFreeResidualFamiliesTieFree :=
  fun lines _hmem => stressFreeStratumIsTieFree_of_hinge hhinge (lineFamilyPattern lines)

/-- **THE FIVE CLASS STATEMENTS ARE THE `(6,3)` HINGE.** -/
theorem residualFamiliesTieFree_iff_hingeHoldsAtSize_six_three :
    StressFreeResidualFamiliesTieFree ↔ HingeHoldsAtSize 6 3 :=
  ⟨fun hresidual => hingeHoldsAtSize_six_three_of_stressFreeHinge
      (stressFreeHingeHoldsSixThree_of_residualFamiliesTieFree hresidual),
    residualFamiliesTieFree_of_hinge⟩

/-! ## 4. The consolidated selector is the hinge

This is the missing arrow.  The tree carried
`Gtz.hingeHoldsAtSize_six_three_of_consolidatedStrictTripleDesign` and read the
selector lane as a door WORTH the conjecture.  It is not worth more: it IS the
hinge. -/

/-- **THE HINGE PRODUCES A STRICT TRIPLE AT EVERY PRIMITIVE `(6,3)` DESIGN.**
The hinge supplies weak domination through `Gtz.gtzWeighted_six_three_of_hinge`.
A primitive design with a weak dominator and no strict one is a tie by
definition, and the hinge then hands it a parallel pair, which primitivity
forbids. -/
theorem consolidatedStrictTripleDesign_of_hinge (hhinge : HingeHoldsAtSize 6 3) :
    ConsolidatedStrictTripleDesign := by
  intro design hprimitive
  by_contra hnone
  have hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef :=
    fun selected hcard hposDef => hnone ⟨selected, hcard, hposDef⟩
  obtain ⟨weakDominator, hcard, hdominates⟩ :=
    gtzWeighted_six_three_of_hinge hhinge design
  exact elim_primitive_isTie_of_hinge hhinge hprimitive
    ⟨⟨weakDominator, hcard, hdominates⟩, hnoStrict⟩

/-- **THE DESIGN SELECTOR IS THE `(6,3)` HINGE.**  Every one of the eighteen
`Gtz.allFiveOnPath_of_*` doors funnels through the left side, so every one of
them is the hinge as well. -/
theorem consolidatedStrictTripleDesign_iff_hingeHoldsAtSize_six_three :
    ConsolidatedStrictTripleDesign ↔ HingeHoldsAtSize 6 3 :=
  ⟨hingeHoldsAtSize_six_three_of_consolidatedStrictTripleDesign,
    consolidatedStrictTripleDesign_of_hinge⟩

/-- The chart-side selector is the hinge too, through the landed whitening
gauge. -/
theorem consolidatedStrictTriple_iff_hingeHoldsAtSize_six_three :
    ConsolidatedStrictTriple ↔ HingeHoldsAtSize 6 3 :=
  consolidatedStrictTriple_iff_consolidatedStrictTripleDesign.trans
    consolidatedStrictTripleDesign_iff_hingeHoldsAtSize_six_three

/-! ## 5. The five registry Props, and the capstone -/

/-- **THE CONJUNCTION OF THE FIVE ON-PATH REGISTRY PROPS.**  These are the exact
Props asserted by `Skeleton.obligationBaseTripleTightUThreeSix`,
`Skeleton.obligationHeavyWeakToStrictOneLine`,
`Skeleton.obligationHeavyWeakToStrictTwoMeetingLines`,
`Skeleton.obligationChartTieFreeThreeLinesFundamentalDomain` and
`Skeleton.obligationKnifeBandRefinedKFour`. -/
def OnPathRegistryConjunction : Prop :=
  BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
    OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
        ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
          KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict

/-- **THE HINGE DISCHARGES ALL FIVE REGISTRY PROPS.**  So the five axioms are
not independent assumptions above the hinge: they are consequences of it. -/
theorem onPathRegistryConjunction_of_hinge (hhinge : HingeHoldsAtSize 6 3) :
    OnPathRegistryConjunction :=
  allFiveOnPath_of_consolidatedStrictTripleDesign (consolidatedStrictTripleDesign_of_hinge hhinge)

/-- **THE FIRST REGISTRY AXIOM, DIRECTLY FROM THE HINGE.**  `Skeleton.obligationBaseTripleTightUThreeSix`
is the line-free `U(3,6)` residual, and `Gtz.heavyNeedleResidual_iff_stressFreeStratumIsTieFree`
proves it EQUAL to the tie-freeness of the line-free stress-free stratum.  So it
needs neither the chart gauge nor the consolidated selector: the pattern
instance of `Gtz.stressFreeStratumIsTieFree_of_hinge` delivers it in one step,
with the empty line family as the pattern. -/
theorem baseTripleTightHeavyNeedleResidual_of_hinge (hhinge : HingeHoldsAtSize 6 3) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual :=
  heavyNeedleResidual_iff_stressFreeStratumIsTieFree.mpr
    (stressFreeStratumIsTieFree_of_hinge hhinge (lineFamilyPattern ([] : List (List (Fin 6)))))

/-- **NO LINE-FREE OFF-CONIC TIE, FROM THE HINGE.**  The counterexample shape of
the first registry axiom, closed.  `Gtz.exists_lineFreeOffConicTie_of_not_heavyNeedleResidual`
says this is the ONLY object that can refute that axiom. -/
theorem lineFreeOffConic_tieFree_of_hinge (hhinge : HingeHoldsAtSize 6 3)
    (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom) : ¬ IsTie design :=
  heavyNeedleResidual_iff_lineFreeOffConicTieFree.mp
    (baseTripleTightHeavyNeedleResidual_of_hinge hhinge) design hlineFree hoffConic

/-- **THE ON-PATH REGISTRY COLLAPSE.**

Four Props that thirty-one forks treated as successive narrowings are one Prop,
and it is `Gtz.HingeHoldsAtSize 6 3`.  The fifth line prices that Prop: it is
the whole rank-three conjecture at every size.

Read the theorem as a ledger.  Nothing between the five class obligations and
the design selector can be cheaper than anything else, because they are equal.
A campaign that moves between them buys formula size and nothing else. -/
theorem onPathRegistryCollapse :
    (StressFreeResidualFamiliesTieFree ↔ HingeHoldsAtSize 6 3)
      ∧ (StressFreeHingeHoldsSixThree ↔ HingeHoldsAtSize 6 3)
        ∧ (ConsolidatedStrictTripleDesign ↔ HingeHoldsAtSize 6 3)
          ∧ (ConsolidatedStrictTriple ↔ HingeHoldsAtSize 6 3)
            ∧ (HingeHoldsAtSize 6 3 → OnPathRegistryConjunction)
              ∧ (HingeHoldsAtSize 6 3 → GtzWeightedAll 3) :=
  ⟨residualFamiliesTieFree_iff_hingeHoldsAtSize_six_three,
    stressFreeHingeHoldsSixThree_iff_hingeHoldsAtSize_six_three,
      consolidatedStrictTripleDesign_iff_hingeHoldsAtSize_six_three,
        consolidatedStrictTriple_iff_hingeHoldsAtSize_six_three,
          onPathRegistryConjunction_of_hinge,
            gtzWeightedAll_three_of_hinge⟩

/-- **THE PRICE OF ANY ONE OF THE FIVE CLASS OBLIGATIONS.**  Proving the five
class statements proves rank three at every size.  This is the same content as
the capstone, stated as the number a planner needs. -/
theorem gtzWeightedAll_three_of_residualFamiliesTieFree
    (hresidual : StressFreeResidualFamiliesTieFree) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_hinge (residualFamiliesTieFree_iff_hingeHoldsAtSize_six_three.mp hresidual)

/-- The same for the design selector, without going through the class list. -/
theorem gtzWeightedAll_three_of_consolidated (hselector : ConsolidatedStrictTripleDesign) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_hinge (hingeHoldsAtSize_six_three_of_consolidatedStrictTripleDesign
    hselector)

/-! ## 6. The frontier, as one object

Composing the section-2 equivalence with the landed
`Gtz.stressFreeHingeHoldsSixThree_iff_no_stressFree_tie` prices the whole
rank-three conjecture against the existence of a SINGLE object. -/

/-- **THE `(6,3)` HINGE IS THE NON-EXISTENCE OF A STRESS-FREE `(6,3)` TIE.**  The
parallel branch, the stressed branches and the matroid stratification are all
already paid for, so nothing else remains on the rank-three frontier. -/
theorem hingeHoldsAtSize_six_three_iff_no_stressFree_tie :
    HingeHoldsAtSize 6 3 ↔
      ∀ design : WeightedDesign 6 3,
        (∀ stress : Fin 6 → ℝ,
          (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0) →
          ¬ IsTie design :=
  stressFreeHingeHoldsSixThree_iff_hingeHoldsAtSize_six_three.symm.trans
    stressFreeHingeHoldsSixThree_iff_no_stressFree_tie

/-- **RANK THREE AT EVERY SIZE, FROM ONE EMPTINESS.**  The 1997 conjecture at
rank three follows from the non-existence of a stress-free `(6,3)` tie, and by
`Gtz.onPathRegistryCollapse` nothing in the on-path registry asks for less.

This is the whole remaining cost of rank three, in one hypothesis, with no
chart, no selector, no pattern list and no residual vocabulary. -/
theorem gtzWeightedAll_three_of_no_stressFree_tie
    (hnone : ∀ design : WeightedDesign 6 3,
      (∀ stress : Fin 6 → ℝ, (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0) →
        ¬ IsTie design) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_hinge (hingeHoldsAtSize_six_three_iff_no_stressFree_tie.mpr hnone)

/-- **THE FRONTIER IS ONE OBJECT.**  Six named Props, the five registry Props and
the whole rank-three conjecture, all priced against the emptiness of a single
locus. -/
theorem rankThreeFrontier_is_one_emptiness :
    (StressFreeResidualFamiliesTieFree ↔ HingeHoldsAtSize 6 3)
      ∧ (ConsolidatedStrictTripleDesign ↔ HingeHoldsAtSize 6 3)
        ∧ (HingeHoldsAtSize 6 3 ↔
            ∀ design : WeightedDesign 6 3,
              (∀ stress : Fin 6 → ℝ,
                (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0) →
                ¬ IsTie design)
          ∧ (HingeHoldsAtSize 6 3 → OnPathRegistryConjunction ∧ GtzWeightedAll 3) :=
  ⟨residualFamiliesTieFree_iff_hingeHoldsAtSize_six_three,
    consolidatedStrictTripleDesign_iff_hingeHoldsAtSize_six_three,
      hingeHoldsAtSize_six_three_iff_no_stressFree_tie,
        fun hhinge => ⟨onPathRegistryConjunction_of_hinge hhinge,
          gtzWeightedAll_three_of_hinge hhinge⟩⟩

end Gtz

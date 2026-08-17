import Skeleton.Obligations

/-!
# What the tree proves ABOUT the frontier

This module adds NO axiom and touches NO ledger.  Every declaration here is a
theorem that rides a `Gtz` theorem, so nothing below reaches an obligation.  It
exists because the registry's prose and the kernel had drifted apart, and the
kernel facts had no Skeleton-side name.

## Why this module is separate from `Skeleton.Frontier`

`Skeleton.Frontier` and `Skeleton.RankThree` carry the CHAIN: the assembly that
takes the obligations to the capstone.  This module carries the SHAPE: what the
obligations are worth, how they relate to each other, and which strata the tree
has closed outright.  A reader who wants to know what is left reads the chain.
A reader who wants to know what the campaign has learned reads this.

## The one sentence

`Skeleton.skeletonFrontierIsOneEmptiness` states it.  Rank three at every size
follows from the non-existence of ONE object, a stress-free `(6,3)` tie.  No
chart, no selector, no pattern list and no residual vocabulary survives in the
hypothesis.

## The correction this module records

The five on-path obligations read as five independent problems, and the registry
gives each its own STATUS, CONSUMERS, WHY OPEN and ATTACK field.  They are not
independent.  `Skeleton.skeletonRegistryCollapse` shows that their conjunction,
the stress-free hinge, the residual-families reading and the consolidated
selector are ONE statement.  A fork that moves between those spellings makes no
progress, and this campaign spent thirty-one forks discovering that.

The count of open obligations is unchanged and this module does not touch it.
What changes is the PRICE the registry records: no route to any one of the five
is cheaper than the whole rank-three conjecture.
-/

namespace Skeleton

open Matrix

/-! ### 1.  The frontier is one statement -/

/-- **THE ON-PATH REGISTRY COLLAPSES.**  Four named Props sit in one equivalence
class with the hinge at the deciding cell, and the hinge delivers the five
registry Props together with rank-three GTZ at every size. -/
theorem skeletonRegistryCollapse :
    (Gtz.StressFreeResidualFamiliesTieFree ↔ Gtz.HingeHoldsAtSize 6 3)
      ∧ (Gtz.StressFreeHingeHoldsSixThree ↔ Gtz.HingeHoldsAtSize 6 3)
        ∧ (Gtz.ConsolidatedStrictTripleDesign ↔ Gtz.HingeHoldsAtSize 6 3)
          ∧ (Gtz.ConsolidatedStrictTriple ↔ Gtz.HingeHoldsAtSize 6 3)
            ∧ (Gtz.HingeHoldsAtSize 6 3 → Gtz.OnPathRegistryConjunction)
              ∧ (Gtz.HingeHoldsAtSize 6 3 → Gtz.GtzWeightedAll 3) :=
  Gtz.onPathRegistryCollapse

/-- **THE TWO ROUTES CARRY THE SAME PRICE.**  The conjunction of the five
on-path Props and the single Prop of the second route are one statement.  The
registry mentions the second route nowhere. -/
theorem skeletonRouteAgreement :
    Gtz.AllFiveOnPath ↔ Gtz.NoStressResidual 6 :=
  Gtz.allFiveOnPath_iff_noStressResidual_six

/-- **THE FRONTIER AS ONE EMPTINESS.**  Rank three at every size follows from
the non-existence of a stress-free `(6,3)` tie. -/
theorem skeletonFrontierIsOneEmptiness :
    (Gtz.StressFreeResidualFamiliesTieFree ↔ Gtz.HingeHoldsAtSize 6 3)
      ∧ (Gtz.ConsolidatedStrictTripleDesign ↔ Gtz.HingeHoldsAtSize 6 3)
        ∧ (Gtz.HingeHoldsAtSize 6 3 ↔
            ∀ design : Gtz.WeightedDesign 6 3,
              (∀ stress : Fin 6 → ℝ,
                (∑ c, stress c • Gtz.atomMatrix (design.atom c)) = 0 → stress = 0) →
                ¬ Gtz.IsTie design)
          ∧ (Gtz.HingeHoldsAtSize 6 3 →
              Gtz.OnPathRegistryConjunction ∧ Gtz.GtzWeightedAll 3) :=
  Gtz.rankThreeFrontier_is_one_emptiness

/-- The five-Prop conjunction reaches the capstone inside `Gtz`, so every door
that concludes it reaches rank three at every size. -/
theorem skeletonAllFiveOnPathReachesCapstone
    (hall : Gtz.AllFiveOnPath) : Gtz.GtzWeightedAll 3 :=
  Gtz.gtzWeightedAll_three_of_allFiveOnPath hall

/-! ### 2.  Why rank three is the deciding rank

At rank three, and at no other rank, the two thresholds coincide:
`2 * rank = 6 = rank * (rank + 1) / 2`.  The complement of a triple is itself a
triple, so it competes.  And six atom matrices can span the symmetric space, so
Parseval determines the shares.  The sub-threshold band is empty at rank three
for exactly this reason. -/

/-- **THE SIZE GAP.**  Five directions in three-space always share a conic.
Seven always carry a stress.  Every primitive `(6,3)` tie is stress-free and off
every conic.  So the stratum is empty at five, empty at seven, and inhabited
only at six. -/
theorem skeletonSizeGapRankThree :
    (∀ atoms : Fin 5 → (Fin 3 → ℝ), ∃ form : Matrix (Fin 3) (Fin 3) ℝ,
        formᵀ = form ∧ form ≠ 0 ∧ ∀ index, atoms index ⬝ᵥ (form *ᵥ atoms index) = 0)
      ∧ (∀ atoms : Fin 7 → (Fin 3 → ℝ), ∃ stress : Fin 7 → ℝ,
          stress ≠ 0 ∧ (∑ label, stress label • Gtz.atomMatrix (atoms label)) = 0)
        ∧ (∀ design : Gtz.WeightedDesign 6 3, Gtz.IsPrimitiveDesign design →
            Gtz.IsTie design →
              Gtz.IsStressFreeDesign design ∧ Gtz.HasNoCommonQuadric design.atom) :=
  Gtz.sizeGap_at_rank_three

/-! ### 3.  Strata the tree has closed outright

Each theorem below is unconditional.  None reaches an obligation.  They record
what a counterexample can no longer look like. -/

/-- **THE STRESSED ARM IS CLOSED.**  Every primitive `(6,3)` tie is stress-free,
so the six atom matrices form a basis of the symmetric space. -/
theorem skeletonPrimitiveTieIsStressFree (design : Gtz.WeightedDesign 6 3)
    (hprimitive : Gtz.IsPrimitiveDesign design) (htie : Gtz.IsTie design) :
    Gtz.IsStressFreeDesign design :=
  Gtz.isStressFreeDesign_of_isPrimitiveDesign_of_isTie design hprimitive htie

/-- **THE CONIC STRATUM IS CLOSED.**  Every primitive `(6,3)` tie lies off every
conic, so the off-conic antecedent of the line-free obligation is free. -/
theorem skeletonPrimitiveTieIsOffConic (design : Gtz.WeightedDesign 6 3)
    (hprimitive : Gtz.IsPrimitiveDesign design) (htie : Gtz.IsTie design) :
    Gtz.HasNoCommonQuadric design.atom :=
  Gtz.hasNoCommonQuadric_of_isPrimitiveDesign_of_isTie design hprimitive htie

/-- **THE CORANK-THREE STRATUM IS EMPTY.**  No triple of a `(6,3)` tie has a gap
matrix that vanishes.  No primitivity and no stratum hypothesis appear. -/
theorem skeletonCorankThreeEmpty (design : Gtz.WeightedDesign 6 3)
    (htie : Gtz.IsTie design) (selected : Finset (Fin 6))
    (hcard : selected.card = 3) :
    Gtz.subsetSum design selected ≠ 1 :=
  Gtz.subsetSum_ne_one_of_isTie_sixThree design htie selected hcard

/-! ### 4.  A no-go that bounds every future attempt

The scalar data of a tie is CONSISTENT.  Positivity, unit weight total, the
leverage floor, the share cap, the trace, the harmonic law and the second-moment
bound all hold at uniform weight and leverage three.  So no contradiction lives
in the weights and the leverages alone, and every future argument must read the
pairings, the brackets or the stress. -/

/-- **THE SCALAR LANE IS CLOSED, BY AN EXPLICIT WITNESS.** -/
theorem skeletonScalarArithmeticIsConsistent :
    ∃ weight leverage : Fin 6 → ℝ,
      (∀ label, 0 < weight label)
        ∧ (∑ label, weight label) = 1
        ∧ (∀ label, 1 ≤ leverage label)
        ∧ (∀ label, weight label * leverage label < 1)
        ∧ (∑ label, weight label * leverage label) = 3
        ∧ (∑ label, (leverage label)⁻¹) < 4
        ∧ (∑ label, (weight label * leverage label) ^ 2) ≤ 3 :=
  Gtz.shareArithmetic_is_consistent

end Skeleton

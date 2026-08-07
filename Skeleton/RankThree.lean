import Skeleton.Frontier

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Rank-three GTZ, assembled as a chain

This module proves rank three of the Gruber-Todd-Zhang conjecture in all three
of its canonical shapes, from the tree's own theorems plus exactly ONE open
obligation, `Skeleton.obligationStressFreeHingeSixThree`.

## The shape of the argument

Rank three collapses onto the single cell `(6,3)`: `Gtz.rank_three_iff_six_three`
and `Gtz.gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three` are both
unconditional, so `Gtz.GtzWeighted 6 3`, `Gtz.GtzWeightedAll 3` and
`forall n > 0, Gtz.GtzOriginal n 3` are one statement in three coordinates.
Section 6 states that collapse as its own unconditional theorem, so it is a
kernel fact here and not three separate coincidences.

The cell is reached through the hinge.  `Gtz.HingeHoldsAtSize 6 3` says every
`(6,3)` tie carries a parallel pair; `Gtz.sixThree_stress_trichotomy` splits
every `(6,3)` design three ways by its stress, and the hinge is assembled one
branch at a time:

* branch (iii), coplanar-support stress  -- CLOSED, `Gtz.twoPoleStratumSelection_six_unconditional`
* branch (ii), balanced full-support stress -- CLOSED, `Gtz.balancedStratumSelection_six_holds`
* branch (i), stress-free -- **OPEN**, and it is the only thing this file assumes

So the file reads: two branches the tree has already closed (section 1), the
branch it has not (section 2), the assembly (section 3), the connectedness
ingredient that the funnel needs and that rank three gets for free (section 4),
and the funnel down to the three shapes (section 5).

## Why branch (i) is harder than it looks

`Gtz.isPrimitiveDesign_of_stressFree` gives that a stress-free `(6,3)` design has
NO parallel pair, so on branch (i) the hinge's conclusion is unreachable.  The
arm cannot be discharged by producing a parallel pair; it can only be discharged
by proving the tie set empty.  Section 2 states both forms, and the tie-emptiness
form is the honest content of what this file assumes.

## An honesty note carried into the code

The hinge family is STRICTLY STRONGER than the value it is used to prove.
`Gtz.gtzWeighted_of_le_five` gives `Gtz.GtzWeighted 5 3` while
`Gtz.not_hingeHoldsAtSize_five_three` refutes the hinge at that size, so the
hinge is not a restatement of GTZ and this route assumes more than the
conjecture asserts.  Section 6 proves that conjunction rather than asserting it.
The refutation is at size five, strictly below six, so it does not touch the
obligation; and the separately refuted `0 <= weight` relaxation cannot touch it
either, because `Gtz.WeightedDesign` carries `weight_pos : 0 < weight`, strict.

## What this file must never do

No `sorry`, no new axiom, and no second rank-three obligation: the six spellings
`Gtz.HingeHoldsAtSize 6 3`, `Gtz.TightDropOnPlaneSixThree`,
`Gtz.TightDropWithinBudgetSixThree`, `Gtz.StressFreeHingeHoldsAtCorankThree 3`,
the residual-families obligation and the not-plane-pair-covered obligation are
all the same sentence as `obligationStressFreeHingeSixThree`, which since the
five-class split is itself a theorem assembled from the five registered class
obligations.
-/

namespace Skeleton

/-! ### 1. The two trichotomy branches the tree has already closed

Both are stated over `Gtz.WeightedDesign 6 3` and both are zero-binder theorems
in the tree, so neither contributes to the frontier. -/

/-- Branch (iii) of `Gtz.sixThree_stress_trichotomy`, the coplanar-support
stratum: closed outright by `Gtz.twoPoleStratumSelection_six_unconditional`. -/
theorem skeletonTwoPoleBranchSixThree : Gtz.TwoPoleStratumSelection 6 :=
  Gtz.twoPoleStratumSelection_six_unconditional

/-- Branch (ii), the balanced full-support stratum: closed by
`Gtz.balancedStratumSelection_six_holds`, repackaged into the capstone form the
assembly consumes via `Gtz.balancedStratumCapstone_of_balancedStratumSelection`. -/
theorem skeletonBalancedBranchSixThree : Gtz.BalancedStratumCapstone :=
  Gtz.balancedStratumCapstone_of_balancedStratumSelection
    Gtz.balancedStratumSelection_six_holds

/-! ### 2. Branch (i), the stress-free stratum: the one open obligation

This is the only place in the file where anything is assumed. -/

/-- **Why branch (i) must be attacked as tie-emptiness.**  A stress-free `(6,3)`
design has no parallel pair at all, so the hinge's conclusion is unreachable on
this branch.  Unconditional: rides `Gtz.isPrimitiveDesign_of_stressFree` through
the bridge `Gtz.isPrimitiveDesign_iff_not_hasParallelPair`. -/
theorem skeletonStressFreeDesignHasNoParallelPairSixThree :
    ∀ design : Gtz.WeightedDesign 6 3,
      (∀ stress : Fin 6 → ℝ,
          ∑ label, stress label • Gtz.atomMatrix (design.atom label) = 0 → stress = 0) →
        ¬ Gtz.HasParallelPair design :=
  fun design hStressFree =>
    (Gtz.isPrimitiveDesign_iff_not_hasParallelPair design).mp
      (Gtz.isPrimitiveDesign_of_stressFree design hStressFree)

/-- **THE OPEN OBLIGATION**, written out rather than named, so the mathematics is
visible at the point of assumption: every stress-free `(6,3)` tie carries a
parallel pair.  This is `Skeleton.obligationStressFreeHingeSixThree` unfolded. -/
theorem skeletonStressFreeBranchSixThree :
    ∀ design : Gtz.WeightedDesign 6 3,
      (∀ stress : Fin 6 → ℝ,
          ∑ label, stress label • Gtz.atomMatrix (design.atom label) = 0 → stress = 0) →
        Gtz.IsTie design → Gtz.HasParallelPair design :=
  Skeleton.obligationStressFreeHingeSixThree

/-- **The honest content of that obligation.**  Combining the previous two, the
parallel pair the obligation produces cannot exist, so what is really being
assumed is that no stress-free `(6,3)` design is a tie.  Rides the tree's own
`Gtz.stressFreeHingeHoldsSixThree_iff_no_stressFree_tie`. -/
theorem skeletonNoStressFreeTieSixThree :
    ∀ design : Gtz.WeightedDesign 6 3,
      (∀ stress : Fin 6 → ℝ,
          ∑ label, stress label • Gtz.atomMatrix (design.atom label) = 0 → stress = 0) →
        ¬ Gtz.IsTie design :=
  Gtz.stressFreeHingeHoldsSixThree_iff_no_stressFree_tie.mp
    Skeleton.obligationStressFreeHingeSixThree

/-! ### 3. The trichotomy assembly

`Gtz.sixThree_stress_trichotomy` exhausts the three branches; the assembly
theorem consumes one input per branch and returns the hinge. -/

/-- **The hinge at `(6,3)`**: every `(6,3)` tie carries a parallel pair.  Rides
`Gtz.hingeHoldsAtSize_sixThree_of_stressFreeHinge`, fed branch (iii), branch (ii)
and branch (i) in that order.  Only branch (i) is open. -/
theorem skeletonHingeHoldsSixThree : Gtz.HingeHoldsAtSize 6 3 :=
  Gtz.hingeHoldsAtSize_sixThree_of_stressFreeHinge
    skeletonTwoPoleBranchSixThree
    skeletonBalancedBranchSixThree
    skeletonStressFreeBranchSixThree

/-! ### 4. The connectedness ingredient, free at rank three

The hinge alone does not give the cell: the funnel walks the parallel-free locus
to an anchor that strictly dominates.  At rank three that walk is a theorem. -/

/-- **The general-rank reach obligation, discharged at rank three.**  This is the
rank-three instance of `Skeleton.obligationSharpWindowAnchorReach`, and it is
unconditional: the sharp window `2 * 3 <= size <= 3 * (3 + 1) / 2` is the single
cell `size = 6`, witnessed by `Gtz.icosaDesign` through
`Gtz.icosaDesign_hasStrictlyDominatingSubset` and
`Gtz.parallelFreeReachesAnchor_six_three`. -/
theorem skeletonSharpWindowAnchorReachAtRankThree :
    ∀ size : ℕ, 2 * 3 ≤ size → size ≤ 3 * (3 + 1) / 2 →
      ∃ anchor : Gtz.WeightedDesign size 3,
        Gtz.HasStrictlyDominatingSubset anchor
          ∧ Gtz.ParallelFreeReachesAnchor size 3 anchor := by
  intro size hlow hhigh
  have hsize : size = 6 := by omega
  subst hsize
  exact ⟨Gtz.icosaDesign, Gtz.icosaDesign_hasStrictlyDominatingSubset,
    Gtz.parallelFreeReachesAnchor_six_three⟩

/-- Kernel check that the statement above really is the rank-three slice of
`Skeleton.obligationSharpWindowAnchorReach`, rather than a hand-copied lookalike:
the axiom applied at rank three elaborates against exactly that type.  Anonymous
and off the chain -- it reaches the axiom and exists only to keep the claim in
the previous docstring honest. -/
example :
    ∀ size : ℕ, 2 * 3 ≤ size → size ≤ 3 * (3 + 1) / 2 →
      ∃ anchor : Gtz.WeightedDesign size 3,
        Gtz.HasStrictlyDominatingSubset anchor
          ∧ Gtz.ParallelFreeReachesAnchor size 3 anchor :=
  Skeleton.obligationSharpWindowAnchorReach 3 (by norm_num)

/-! ### 5. The funnel, and the three canonical shapes of the result -/

/-- **The cell.**  Rides `Gtz.gtzWeighted_six_three_of_hinge_of_reach`, which
takes the hinge together with the reach witness of section 4.  The tree also
packages these as `Gtz.gtzWeighted_six_three_of_hinge`; the two-argument form is
used here so the connectedness ingredient stays visible in the chain. -/
theorem skeletonGtzWeightedSixThree : Gtz.GtzWeighted 6 3 :=
  Gtz.gtzWeighted_six_three_of_hinge_of_reach
    skeletonHingeHoldsSixThree
    Gtz.parallelFreeReachesAnchor_six_three

/-- **The rank.**  Rides `Gtz.rank_three_iff_six_three`, the unconditional
equivalence that makes the single cell carry all of rank three. -/
theorem skeletonGtzWeightedAllThree : Gtz.GtzWeightedAll 3 :=
  Gtz.rank_three_iff_six_three.mpr skeletonGtzWeightedSixThree

/-- **The capstone: rank three of GTZ in its 1997 form.**  Rides
`Gtz.original_of_weighted`, which converts the weighted conjecture at a rank into
the original conjecture at every size. -/
theorem skeletonGtzOriginalRankThree : ∀ n : ℕ, 0 < n → Gtz.GtzOriginal n 3 :=
  Gtz.original_of_weighted 3 skeletonGtzWeightedAllThree

/-! ### 6. Cross-checks and honesty notes

None of these is on the chain above; they exist so that claims made in prose
elsewhere are kernel facts here. -/

/-- **The three shapes are one statement.**  Unconditional, so it reaches no
obligation: all the content of rank three sits in section 2, none of it in the
translation between coordinates.  Rides `Gtz.rank_three_iff_six_three` and
`Gtz.gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three`. -/
theorem skeletonRankThreeShapesAgree :
    (Gtz.GtzWeightedAll 3 ↔ Gtz.GtzWeighted 6 3)
      ∧ (Gtz.GtzWeighted 6 3 ↔ ∀ n : ℕ, 0 < n → Gtz.GtzOriginal n 3) :=
  ⟨Gtz.rank_three_iff_six_three,
   Gtz.gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three⟩

/-- **A second route to the capstone, from a different module.**  The tree ships
`Gtz.forall_gtzOriginal_rank_three_of_stressFreeHingeAlone` in
Gtz/Reduction/BalancedStratumClosure.lean, which reaches the same conclusion from
the same single obligation without going through the hinge explicitly.  Module
provenance differs from the chain above; no claim is made about proof-term
independence. -/
theorem skeletonGtzOriginalRankThreeViaTreeCapstone :
    ∀ n : ℕ, 0 < n → Gtz.GtzOriginal n 3 :=
  Gtz.forall_gtzOriginal_rank_three_of_stressFreeHingeAlone
    Skeleton.obligationStressFreeHingeSixThree

/-- **A third route, through the general-rank registry instead.**  Rides
`Skeleton.stressFreeHingeSixThree_of_thresholdCellHinge`, so it reaches
`Skeleton.obligationThresholdCellHinge` and NOT the rank-three obligation.  This
is why the merged frontier count over both roots is three and not four: whoever
assumes the general-rank threshold-cell hinge already has rank three. -/
theorem skeletonGtzOriginalRankThreeViaThresholdHinge :
    ∀ n : ℕ, 0 < n → Gtz.GtzOriginal n 3 :=
  Gtz.forall_gtzOriginal_rank_three_of_stressFreeHingeAlone
    (Skeleton.stressFreeHingeSixThree_of_thresholdCellHinge
      Skeleton.obligationThresholdCellHinge)

/-- **The route assumes strictly more than it proves.**  Unconditional: the value
holds at `(5,3)` by `Gtz.gtzWeighted_of_le_five` while the hinge is refuted there
by `Gtz.not_hingeHoldsAtSize_five_three`.  So the hinge family is provably not a
restatement of GTZ, and the obligation of section 2 is a sufficient condition
that is not known to be necessary: the stage-two producer census over the whole
tree found eight producers of that obligation and no converse, so nothing here
derives it back from `Gtz.GtzWeighted 6 3`.  That last part is a census result,
not something this file checks. -/
theorem skeletonHingeIsStrictlyStrongerThanRankThree :
    Gtz.GtzWeighted 5 3 ∧ ¬ Gtz.HingeHoldsAtSize 5 3 :=
  ⟨Gtz.gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num),
   Gtz.not_hingeHoldsAtSize_five_three⟩

/-! ### 7. The frontier

`skeletonRankThreeShapesAgree` must report zero obligations, confirming the
coordinate changes are free.  `skeletonGtzOriginalRankThreeViaThresholdHinge`
must report the threshold-cell hinge, confirming the subsumption.  The capstone
must report exactly the five class obligations of the split parent
`obligationStressFreeHingeSixThree`. -/

#gtz_frontier skeletonRankThreeShapesAgree

#gtz_frontier skeletonGtzOriginalRankThreeViaThresholdHinge

#gtz_frontier skeletonGtzOriginalRankThree

end Skeleton

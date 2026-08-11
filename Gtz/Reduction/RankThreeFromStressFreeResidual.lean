import Gtz.Design.FreeMassBudgetDischarge
import Gtz.Design.StressFreeClassSplit
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.HingeFunnel
import Gtz.Reduction.StressWalk
import Gtz.Reduction.BalancedStratumClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Rank-three GTZ from the one surviving stress-free hypothesis

`Gtz/Design/FreeMassBudgetDischarge.lean` removes the free-mass budget hypothesis
from the stress-free arm of the `(6,3)` hinge, leaving `Gtz.NoStressResidual 6` as
its only open Prop.  This module carries that all the way up, because the other
two hypotheses of the hinge assembly are already landed and unconditional:

* `Gtz.twoPoleStratumSelection_six_unconditional`, and
* `Gtz.balancedStratumCapstone_of_balancedStratumSelection` applied to
  `Gtz.balancedStratumSelection_six_holds`.

Composing them with `Gtz.gtzWeightedAll_three_of_hinge` gives

    `NoStressResidual 6  ->  GtzWeightedAll 3` ,

rank-three GTZ at every size from ONE Prop.

## This is a repackaging, not a reduction, and the file proves it

`gtzWeightedAll_three_of_noStressResidual` is not a cheaper target than the
tree's five class obligations, and it must not be read as one.
`exists_dominating_of_noStressResidual` is the reason: `NoStressResidual 6`
concludes a STRICTLY dominating triple with no hypothesis that any triple
dominates at all, so it already yields weighted domination on its own hypothesis
stratum -- a piece of the open cell -- while the arm it reduces needs only the
weak-to-strict upgrade.  The single Prop is STRICTLY STRONGER than the five it
replaces, and the honest reading of the pair is that the frontier has two
descriptions, five goals on the tree's route and one on a strictly stronger one.

## And the stratum it quantifies over is inhabited

The hypothesis set of `NoStressResidual 6` -- primitive, stress-free, and no
triple carrying either strict certificate -- is NOT empty: the tree's own landed
stress-free witness `Gtz.coordinateDiagonalDesign` is primitive and stress-free
and carries zero strict certificates at all twenty triples, because the isotropy
leg never fires and the free-mass budget totals `6/5` or `7/5` at the sixteen
triples where its inner matrix is positive definite at all.  So the Prop is not
vacuously true and the route "prove the hypothesis set empty and the arm is done"
is closed.  That measurement is exact rational arithmetic outside the kernel and
is recorded here rather than proved.
-/

namespace Gtz

/-- **The surviving hypothesis is an inflation.**  `NoStressResidual 6` produces a
weakly dominating triple at every certificate-free stress-free design, with no
hypothesis that any triple dominates -- so it entails a piece of `GtzWeighted 6 3`
on its own stratum, which the weak-to-strict arm it reduces does not ask for. -/
theorem exists_dominating_of_noStressResidual
    (hresidual : NoStressResidual 6) (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0)
    (hnoCertificate : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ HasStrictCertificate design selected) :
    ∃ dominatingTriple : Finset (Fin 6),
      dominatingTriple.card = 3 ∧ Dominates design dominatingTriple := by
  obtain ⟨triple, hcard, hposDef⟩ :=
    hresidual design (isPrimitiveDesign_of_stressFree design hstressFree)
      hstressFree hnoCertificate
  exact ⟨triple, hcard, hposDef.posSemidef⟩

/-- The stress-free arm of the `(6,3)` hinge, packaged onto the named Prop with
the discharged budget hypothesis gone. -/
theorem stressFreeHingeHoldsSixThree_of_noStressResidual
    (hresidual : NoStressResidual 6) : StressFreeHingeHoldsSixThree := by
  intro design hstressFree htie
  exact sixThree_hasParallelPair_of_isTie_of_stressFree_ofResidual hresidual design htie
    hstressFree

/-- The whole `(6,3)` hinge from one open Prop: the assembly's other two
hypotheses are landed and unconditional. -/
theorem hingeHoldsAtSize_sixThree_of_noStressResidual
    (hresidual : NoStressResidual 6) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_sixThree_of_stressFreeHinge
    twoPoleStratumSelection_six_unconditional
    (balancedStratumCapstone_of_balancedStratumSelection balancedStratumSelection_six_holds)
    (stressFreeHingeHoldsSixThree_of_noStressResidual hresidual)

/-- **Rank-three GTZ at every size, from `NoStressResidual 6` alone.**  Read it
with `exists_dominating_of_noStressResidual` beside it: the single Prop is
strictly stronger than the five class obligations it stands in for. -/
theorem gtzWeightedAll_three_of_noStressResidual
    (hresidual : NoStressResidual 6) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_hinge (hingeHoldsAtSize_sixThree_of_noStressResidual hresidual)

end Gtz

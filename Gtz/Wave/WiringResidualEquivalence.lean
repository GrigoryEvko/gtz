/-
# The second route and the stress-free hinge are ONE Prop

## What this file settles

`Gtz.gtzWeightedAll_three_of_noStressResidual` (Gtz/Reduction/RankThreeFromStressFreeResidual.lean:94)
reaches rank-three GTZ from the single Prop `Gtz.NoStressResidual 6`.  That module
claims, in prose, that the single Prop is STRICTLY STRONGER than the five class
obligations it stands in for.  **The claim is false, and this file refutes it in
kernel.**

`Gtz.noStressResidual_six_of_stressFreeHinge` is the converse nobody composed.
Its four ingredients were all landed and all unconditional:

* `Gtz.hingeHoldsAtSize_sixThree_of_stressFreeHinge` (Gtz/Reduction/TrichotomyLedger.lean:689),
* `Gtz.twoPoleStratumSelection_six_unconditional` (Gtz/Design/CompanionConstruction.lean:1443),
* `Gtz.balancedStratumSelection_six_holds` (Gtz/Reduction/BalancedStratumClosure.lean:37),
* `Gtz.gtzWeighted_six_three_of_hinge` (Gtz/Reduction/ParallelFreeReach.lean:1105).

The hinge supplies `Gtz.GtzWeighted 6 3`, which hands every design the FIRST
conjunct of `Gtz.IsTie`.  The hinge also refutes the conjunction on the
stress-free locus.  The second conjunct must fail, and that is exactly the
conclusion of `Gtz.NoStressResidual 6`.

## The proof spends neither side hypothesis

`Gtz.noStressResidual_six_of_stressFreeHinge` uses neither `IsPrimitiveDesign`
nor certificate-freeness.  Both hypotheses of `Gtz.NoStressResidual` are free
weight.  `Gtz.exists_posDef_triple_of_stressFreeHinge` states the stronger form
that drops them.

## Why the earlier strictness argument fails

`Gtz.exists_dominating_of_noStressResidual` concludes `Gtz.Dominates`, the WEAK
form, through `PosSemidef`.  Weak domination on that stratum follows from
`Gtz.GtzWeighted 6 3`, which the hinge already delivers everywhere.  The theorem
exhibits no gap.  `Gtz.exists_dominating_of_stressFreeHinge` below proves the
same conclusion from the hinge alone.

## The sixth equivalence

Five sharpened forms of this campaign were already proved equivalent to what
they reduce.  `Gtz.NoStressResidual 6` is the sixth.  An intermediate that is
iff-equivalent to its target records nothing, and this one is.

## The registry consequence

`Gtz.noStressResidual_six_iff_residualFamiliesTieFree` puts the second route and
the five-class split in one equivalence class.  Adding `Gtz.NoStressResidual 6`
to the registry would add no strength and would remove no obligation.
-/
import Gtz.Reduction.RankThreeFromStressFreeResidual
import Gtz.Reduction.ParallelFreeReach
import Gtz.Design.StressFreeClassSplit
import Gtz.Wave.LightAtomTieFloor
import Gtz.Wave.A1NeedleCollapse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ### 1.  The hinge alone gives weighted GTZ at the single cell -/

/-- The `(6,3)` cell from the stress-free arm alone.  Branches (ii) and (iii) of
`Gtz.sixThree_stress_trichotomy` are landed and carry no hypothesis. -/
theorem gtzWeighted_six_three_of_stressFreeHinge
    (hinge : StressFreeHingeHoldsSixThree) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_hinge
    (hingeHoldsAtSize_sixThree_of_stressFreeHinge
      twoPoleStratumSelection_six_unconditional
      (balancedStratumCapstone_of_balancedStratumSelection balancedStratumSelection_six_holds)
      hinge)

/-! ### 2.  The converse nobody composed -/

/-- **EVERY STRESS-FREE `(6,3)` DESIGN HAS A STRICTLY DOMINATING TRIPLE, FROM THE
HINGE ALONE.**  No primitivity hypothesis and no certificate hypothesis appear.
The hinge gives a weakly dominating triple through `Gtz.GtzWeighted 6 3`, and it
refutes `Gtz.IsTie` on the stress-free locus.  A design with a weak dominator
that is not a tie has a strict one. -/
theorem exists_posDef_triple_of_stressFreeHinge
    (hinge : StressFreeHingeHoldsSixThree) (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) :
    ∃ dominatingTriple : Finset (Fin 6), dominatingTriple.card = 3
      ∧ (subsetSum design dominatingTriple - 1).PosDef := by
  classical
  have hnotTie : ¬ IsTie design :=
    stressFreeHingeHoldsSixThree_iff_no_stressFree_tie.mp hinge design hstressFree
  obtain ⟨weakTriple, hcard, hdominates⟩ :=
    gtzWeighted_six_three_of_stressFreeHinge hinge design
  by_contra hnone
  push Not at hnone
  exact hnotTie ⟨⟨weakTriple, hcard, hdominates⟩, fun triple hcardTriple => hnone triple hcardTriple⟩

/-- **THE MISSING CONVERSE.**  The stress-free hinge produces the named residual.
Both hypotheses of `Gtz.NoStressResidual` stay unused, so the residual is not
stronger than the arm it reduces. -/
theorem noStressResidual_six_of_stressFreeHinge
    (hinge : StressFreeHingeHoldsSixThree) : NoStressResidual 6 :=
  fun design _hprimitive hstressFree _hcertificateFree =>
    exists_posDef_triple_of_stressFreeHinge hinge design hstressFree

/-! ### 3.  The equivalence, and what it costs the record -/

/-- **THE SIXTH EQUIVALENCE TRAP OF THIS CAMPAIGN.**  The single Prop of the
second route and the stress-free arm of the `(6,3)` hinge are one statement. -/
theorem noStressResidual_six_iff_stressFreeHingeHoldsSixThree :
    NoStressResidual 6 ↔ StressFreeHingeHoldsSixThree :=
  ⟨stressFreeHingeHoldsSixThree_of_noStressResidual, noStressResidual_six_of_stressFreeHinge⟩

/-- The second route and the five-class split sit in one equivalence class.  A
registry entry for the residual would add no strength. -/
theorem noStressResidual_six_iff_residualFamiliesTieFree :
    NoStressResidual 6 ↔
      ∀ lines ∈ stressFreeResidualFamiliesSix,
        StressFreeStratumIsTieFree (lineFamilyPattern lines) :=
  noStressResidual_six_iff_stressFreeHingeHoldsSixThree.trans
    stressFreeResidualFamilies_tieFree_iff_stressFreeHinge.symm

/-- The residual is equivalent to tie-emptiness of the stress-free locus, with
no certificate quantifier and no primitivity quantifier left in it. -/
theorem noStressResidual_six_iff_no_stressFree_tie :
    NoStressResidual 6 ↔
      ∀ design : WeightedDesign 6 3,
        (∀ stressCoeff : Fin 6 → ℝ,
          (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
            stressCoeff = 0) →
          ¬ IsTie design :=
  noStressResidual_six_iff_stressFreeHingeHoldsSixThree.trans
    stressFreeHingeHoldsSixThree_iff_no_stressFree_tie

/-- **THE STRICTNESS ARGUMENT, REFUTED AT ITS OWN CONCLUSION.**  The weak
dominator that `Gtz.exists_dominating_of_noStressResidual` produces already
follows from the hinge, with the certificate hypothesis dropped. -/
theorem exists_dominating_of_stressFreeHinge
    (hinge : StressFreeHingeHoldsSixThree) (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) :
    ∃ dominatingTriple : Finset (Fin 6),
      dominatingTriple.card = 3 ∧ Dominates design dominatingTriple := by
  obtain ⟨triple, hcard, hposDef⟩ := exists_posDef_triple_of_stressFreeHinge hinge design hstressFree
  exact ⟨triple, hcard, hposDef.posSemidef⟩

/-! ### 4.  The A1 class Prop joins the same class

`Gtz.heavyNeedleResidual_iff_stressFreeStratumIsTieFree` (Gtz/Wave/A1NeedleCollapse.lean:179)
already proves the first on-path registry Prop equivalent to its class
statement.  The residual therefore implies that class Prop directly. -/

/-- The second route delivers the first on-path registry Prop. -/
theorem baseTripleTightLineFreeOffConicHeavyNeedleResidual_of_noStressResidual
    (hresidual : NoStressResidual 6) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual :=
  heavyNeedleResidual_iff_stressFreeStratumIsTieFree.mpr
    (noStressResidual_six_iff_residualFamiliesTieFree.mp hresidual _
      (by simp [stressFreeResidualFamiliesSix]))

/-! ### 5.  A door of the off-path lane that records nothing

`Gtz.hingeConclusion_sixThree_of_heavyTie` (Gtz/Wave/LightAtomTieFloor.lean:127)
reduces the `(6,3)` hinge to the same statement on the all-heavy stratum.  The
heaviness is FREE at `(6,3)`, because `Gtz.leverage_one_le_of_isTie_sixThree`
carries no hypothesis.  The reduction is an equivalence. -/

/-- **THE ALL-HEAVY REDUCTION AT `(6,3)` IS AN EQUIVALENCE.**  It hands a prover
a hypothesis that the tie already supplies, and it records no progress. -/
theorem heavyTie_hingeConclusion_iff_hingeHoldsAtSize_six_three :
    (∀ design : WeightedDesign 6 3,
        (∀ label, 1 ≤ leverageOf (design.atom label)) →
          IsTie design → HasParallelPair design)
      ↔ HingeHoldsAtSize 6 3 :=
  ⟨hingeConclusion_sixThree_of_heavyTie,
    fun hhinge design _hheavy htie => hhinge design htie⟩

end Gtz

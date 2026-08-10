import Gtz.Design.LineBranchOneSlotDeterminant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6000000

namespace Gtz

/-- The exact remaining line-branch claim: the Parseval-normalized rank-two
hidden form cannot satisfy all 39 candidate refusals under the original
line-free and off-conic hypotheses. -/
def UThreeSixUnitAxisPolynomialExclusion : Prop :=
  ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    tightDir ≠ 0 →
    IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir →
    HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir →
    ¬ UnitAxisHiddenPolynomialFailure design

/-- The tight-line branch is neither weakened nor strengthened by the
normal-form reduction: it is exactly exclusion of the finite sign witness. -/
theorem uThreeSixTightLineBranch_iff_unitAxisPolynomialExclusion :
    UThreeSixTightLineBranch ↔ UThreeSixUnitAxisPolynomialExclusion := by
  constructor
  · intro hline design tightDir hlineFree hoffConic hdominates htightNe htight hkernel hfailure
    have hcandidates : UnitAxisHiddenNineteenCandidate design :=
      (exists_posDef_cardThree_iff_unitAxisHiddenNineteenCandidate
        design tightDir hlineFree htightNe htight).mp
          (hline design tightDir hlineFree hoffConic hdominates htightNe htight hkernel)
    exact (not_unitAxisHiddenNineteenCandidate_iff_polynomialFailure design
      hlineFree (unitAxisHiddenForm_posSemidef design hlineFree hdominates)).mpr
        hfailure hcandidates
  · intro hexclusion design tightDir hlineFree hoffConic hdominates htightNe htight hkernel
    apply (exists_posDef_cardThree_iff_unitAxisHiddenNineteenCandidate
      design tightDir hlineFree htightNe htight).mpr
    by_contra hnoCandidate
    exact hexclusion design tightDir hlineFree hoffConic hdominates htightNe htight
      hkernel ((not_unitAxisHiddenNineteenCandidate_iff_polynomialFailure design
        hlineFree (unitAxisHiddenForm_posSemidef design hlineFree hdominates)).mp
          hnoCandidate)

/-- The current U(3,6) Skeleton proposition in its fully explicit two-branch
form. The line half is now a finite polynomial exclusion; the plane half is
the already-landed ten-candidate problem. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_iff_explicitAxisBranches :
    BaseTripleTightLineFreeOffConicWeakToStrict ↔
      UThreeSixUnitAxisPolynomialExclusion ∧ UThreeSixPlaneTenCandidateBranch := by
  rw [baseTripleTightLineFreeOffConicWeakToStrict_iff_tightSpaceBranches,
    uThreeSixTightLineBranch_iff_unitAxisPolynomialExclusion]

end Gtz

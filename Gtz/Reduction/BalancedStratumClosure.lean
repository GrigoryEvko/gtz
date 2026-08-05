/-
# The balanced stratum is closed: rank 3 rests on the stress-free hinge alone

Branches (ii) and (iii) of the (6,3) stress trichotomy are closed.  Branch
(iii) closed in `Gtz.Design.CompanionConstruction`
(`twoPoleStratumSelection_six_unconditional`).  Branch (ii) closes here by
composing its two unconditional halves through the endpoint-gauge chain:

* the (5,3) spiked tie exclusion
  (`EndpointSpike.endpointBottomTieExclusionFiveThree_holds`,
  `Gtz.Ties.SpikeMatroidObstruction`), and
* the two-vanished (4,3) boundary domination
  (`twoVanishedRigidBottomDomination_holds`,
  `Gtz.Reduction.TwoVanishedBoundary`).

`balancedStratumSelection_six_holds` makes `BalancedStratumSelection 6` a
theorem, and `forall_gtzOriginal_rank_three_of_stressFreeHinge` states the
campaign's position exactly: the 1997 conjecture at rank three, for every
size, follows from `StressFreeHingeHoldsSixThree` -- no stress-free (6,3)
tie exists -- and from nothing else.
-/
import Mathlib
import Gtz.Reduction.EndpointGaugeDescent
import Gtz.Reduction.TwoVanishedBoundary
import Gtz.Ties.SpikeMatroidObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

/-- **The balanced stratum is closed.**  Branch (ii) of the stress trichotomy
holds unconditionally: the endpoint-gauge descent reduces it to the
one-vanished and two-vanished boundary strata, the one-vanished stratum
closes through the (5,3) spiked tie exclusion, and the two-vanished stratum
closes outright. -/
theorem balancedStratumSelection_six_holds : BalancedStratumSelection 6 :=
  balancedStratumSelection_six_of_vanishedCases
    (oneVanished_of_spikedBottomDomination
      (spikedBottomDomination_of_tieExclusion
        EndpointSpike.endpointBottomTieExclusionFiveThree_holds))
    twoVanishedRigidBottomDomination_holds

/-- **Rank three rests on the stress-free hinge alone.**  With branches (ii)
and (iii) closed, the full 1997 statement at rank three -- every size --
follows from the single remaining branch of the trichotomy: no stress-free
(6,3) tie exists.  (`forall_gtzOriginal_rank_three_of_stressFreeHinge` in
`Gtz.Reduction.TrichotomyLedger` is the earlier three-hypothesis form; here
the other two hypotheses are theorems.) -/
theorem forall_gtzOriginal_rank_three_of_stressFreeHingeAlone
    (hstressFreeHinge : StressFreeHingeHoldsSixThree) :
    ∀ sizeParam : ℕ, 0 < sizeParam → GtzOriginal sizeParam 3 :=
  forall_gtzOriginal_rank_three_of_tieExclusion_twoVanished_stressFreeHinge
    EndpointSpike.endpointBottomTieExclusionFiveThree_holds
    twoVanishedRigidBottomDomination_holds hstressFreeHinge

end Gtz

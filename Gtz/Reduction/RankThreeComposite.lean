/-
# The rank-three composite: the 1997 conjecture from two Props

Branch (iii) is supplied by `twoPoleStratumSelection_six_unconditional`, so the
whole of `GtzOriginal n 3` at every size rests on exactly two remaining Props:
branch (ii)'s `BalancedStratumSelection 6` and branch (i)'s
`StressFreeHingeHoldsSixThree`.
-/
import Mathlib
import Gtz.Reduction.TrichotomyLedger
import Gtz.Design.CompanionConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

/-- **THE COMPOSITE.**  Every real `n`-by-three matrix with orthonormal columns has
a three-row submatrix of smallest singular value at least `1 / sqrt n`, as soon as
the balanced-stratum selection and the stress-free hinge hold at size six. -/
theorem forall_gtzOriginal_rank_three_of_balancedSelection_and_stressFreeHinge
    (hBalanced : BalancedStratumSelection 6)
    (hstressFreeHinge : StressFreeHingeHoldsSixThree) :
    ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  forall_gtzOriginal_rank_three_of_twoSelections_and_stressFreeHinge
    twoPoleStratumSelection_six_unconditional hBalanced hstressFreeHinge

end Gtz

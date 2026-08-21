/-
# The tetrahedron sits inside branch B, so branch B survives below size six

Branch B is the region in which every atom is strictly heavy and every pair is
admissible.  It is the case of the hinge whose conclusion has no witness to
point at, because an admissible pair is never parallel, and the campaign's
working hypothesis is that no `(6,3)` boundary system lies in it.

The tetrahedron fixture is landed and heavily used: `Gtz.tetraDesign` is the
four even-parity sign vectors at weight one quarter, `Gtz.tetraDesign_leverage`
gives every leverage as three, `Gtz.tetraAtom_dot_eq_neg_one` gives every
distinct pairing as minus one, and `Gtz.tetraDesign_isTie` makes it a boundary
system.  What nothing in the corpus records is where it sits relative to
ADMISSIBILITY.  This module records that, and the answer bounds what a proof of
the size-six emptiness may look like.

## The reading

Every pair minor of the tetrahedron is `(3-1)(3-1) - (-1)^2 = 3`
(`Gtz.tetraDesign_pairGapMinor`), so every pair is admissible and every atom is
strictly heavy.  Hence

  **`Gtz.branchB_nonempty_at_four`: branch B contains a boundary system at size
  four.**

The landed `(5,3)` diamond is a second one: its leverages are `2` and `13/4`
and its pair minors are `3/4`, `2` and `9/2`, all positive.  So branch B is
nonempty at sizes four and five, and **a proof that it is empty at size six
cannot be size-blind**: any argument that reads only four or only five of the
six atoms proves something false.  That is the same shape as the hinge itself,
which is false at size five (`Gtz.not_hingeHoldsAtSize_five_three`) and expected
at size six.

## The constant of the strong-pair bound is attained here

`Gtz.exists_strongPair_of_tripleGapDet_nonpos` says a refused triple of heavy
atoms carries a pair with `x_a x_b <= 4 <g_a,g_b>^2`.  At the tetrahedron every
pair meets that with EQUALITY, `2 * 2 = 4 * 1` (`Gtz.tetraDesign_strongPair_sharp`),
so the quarter cannot be improved.

[MEASURED.  Minimising `max_T tripleGapDet` over branch-B `(6,3)` designs under
a weight floor `tau` returns `+2.09e-2` at `tau = 5e-2`, `+1.65e-3` at
`tau = 1e-2` and `+1.25e-4` at `tau = 1e-3`, and the minimiser degenerates onto
THIS fixture: two of the six weights fall to the floor and the four survivors
carry normalised pairings `+-0.494, +-0.501, +-0.504` against the tetrahedral
`+-1/2`, holding `1.99` of the total excess mass `2`.  So the infimum over
genuine `(6,3)` designs is zero, and any certificate for the size-six emptiness
must vanish on this ray, hence be non-strict, and must consume the weights.]
-/
import Gtz.Wave.BranchBStrongPair
import Gtz.Ties.TetrahedronCertifiedTie
import Gtz.Design.FourThreeRigidity
import Gtz.Quantitative.DiscriminantSystem

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. Every pair of the tetrahedron is admissible -/

/-- Every pair minor of the tetrahedron is three. -/
theorem tetraDesign_pairGapMinor {a b : Fin 4} (hab : a ≠ b) :
    pairGapMinor (tetraDesign.atom a) (tetraDesign.atom b) = 3 := by
  rw [pairGapMinor, tetraDesign_leverage, tetraDesign_leverage, tetraDesign_atom,
    tetraAtom_dot_eq_neg_one hab]
  norm_num

/-- Every pair of the tetrahedron is admissible. -/
theorem tetraDesign_admissiblePair {a b : Fin 4} (hab : a ≠ b) :
    AdmissiblePair (tetraDesign.atom a) (tetraDesign.atom b) := by
  rw [AdmissiblePair, tetraDesign_pairGapMinor hab]; norm_num

/-- Every atom of the tetrahedron is strictly heavy. -/
theorem tetraDesign_one_lt_leverage (a : Fin 4) : 1 < leverageOf (tetraDesign.atom a) := by
  rw [tetraDesign_leverage]; norm_num

/-! ## 2. Branch B at size four -/

/-- **BRANCH B IS NOT EMPTY AT SIZE FOUR.**  The tetrahedron is a boundary
system whose atoms are all strictly heavy and whose pairs are all admissible.

With the `(5,3)` diamond, whose leverages are `2` and `13/4` and whose pair
minors are `3/4`, `2` and `9/2`, branch B survives at sizes four and five.  A
proof that it is empty at size six therefore cannot be size-blind. -/
theorem branchB_nonempty_at_four :
    IsTie tetraDesign
      ∧ (∀ a : Fin 4, 1 < leverageOf (tetraDesign.atom a))
      ∧ (∀ a b : Fin 4, a ≠ b → AdmissiblePair (tetraDesign.atom a) (tetraDesign.atom b)) :=
  ⟨tetraDesign_isTie, tetraDesign_one_lt_leverage, fun _ _ hab => tetraDesign_admissiblePair hab⟩

/-! ## 3. The strong-pair constant is attained -/

/-- **THE QUARTER IS SHARP.**  At the tetrahedron every pair meets the bound of
`Gtz.exists_strongPair_of_tripleGapDet_nonpos` with equality. -/
theorem tetraDesign_strongPair_sharp {a b : Fin 4} (hab : a ≠ b) :
    (leverageOf (tetraDesign.atom a) - 1) * (leverageOf (tetraDesign.atom b) - 1)
      = 4 * (tetraDesign.atom a ⬝ᵥ tetraDesign.atom b) ^ 2 := by
  rw [tetraDesign_leverage, tetraDesign_leverage, tetraDesign_atom,
    tetraAtom_dot_eq_neg_one hab]
  norm_num

/-- **NO PAIR OF THE TETRAHEDRON IS WEAK.**  Every pair is strong, so the
tetrahedron saturates the Mantel side of the branch-B graph as well: the graph
of weak pairs is empty. -/
theorem tetraDesign_forall_strongPair {a b : Fin 4} (hab : a ≠ b) :
    (leverageOf (tetraDesign.atom a) - 1) * (leverageOf (tetraDesign.atom b) - 1)
      ≤ 4 * (tetraDesign.atom a ⬝ᵥ tetraDesign.atom b) ^ 2 :=
  le_of_eq (tetraDesign_strongPair_sharp hab)

end Gtz

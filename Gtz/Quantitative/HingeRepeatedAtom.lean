/-
# The hinge at `(6,3)`, as an equivalence about a REPEATED atom

`Gtz.HingeHoldsAtSize 6 3` asks every `(6,3)` tie for a parallel pair with an
UNCONSTRAINED ratio.  Composing the shipped
`Gtz.sq_eq_one_of_parallel_of_isTie_sixThree` with the trivial converse sharpens
that to an equivalence: every `(6,3)` tie REPEATS AN ATOM UP TO SIGN.

Two consequences worth stating in one place.  A design refuting the hinge is a
`(6,3)` tie whose six atoms are six pairwise-distinct points of the projective
plane.  And a design carrying two atoms of the same direction but DIFFERENT
lengths cannot be a tie at all (`Gtz.not_isTie_of_parallel_ratio_ne_sixThree`).

R6 DISCLOSURE.  The `ratio ^ 2 = 1` step is NOT re-derived here — it is the
shipped `Gtz.sq_eq_one_of_parallel_of_isTie_sixThree`, whose own module header
already states the sharpening in prose.  What is new is only the EQUIVALENCE: no
`↔` statement over `Gtz.HingeHoldsAtSize` exists anywhere else in the tree.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Certificates.ResidueDissolution
import Gtz.Quantitative.HingeStressNarrowing
import Gtz.Reduction.SplitTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz


/-- **A `(6,3)` TIE CANNOT CARRY A RESCALED REPEAT.**  Contrapositive of the shipped
`Gtz.sq_eq_one_of_parallel_of_isTie_sixThree`. -/
theorem not_isTie_of_parallel_ratio_ne_sixThree (design : WeightedDesign 6 3)
    {keptLabel dropLabel : Fin 6} (hdistinct : keptLabel ≠ dropLabel) {ratio : ℝ}
    (hparallel : design.atom dropLabel = ratio • design.atom keptLabel)
    (hnotOne : ratio ≠ 1) (hnotNegOne : ratio ≠ -1) : ¬ IsTie design := by
  intro htie
  have hsq := sq_eq_one_of_parallel_of_isTie_sixThree design htie hdistinct hparallel
  rcases mul_eq_zero.mp (show (ratio - 1) * (ratio + 1) = 0 by linear_combination hsq) with h | h
  · exact hnotOne (by linarith)
  · exact hnotNegOne (by linarith)

/-- **THE HINGE AT `(6,3)`, SHARPENED TO AN EQUIVALENCE.**  No enumeration, no
strata, and strictly more informative than the parallel-pair form: the pair the
hinge asks for is automatically a REPEATED ATOM up to sign. -/
theorem hingeHoldsAtSize_six_three_iff_repeatedAtom :
    HingeHoldsAtSize 6 3 ↔ ∀ design : WeightedDesign 6 3, IsTie design →
      ∃ keptLabel dropLabel : Fin 6, keptLabel ≠ dropLabel ∧
        (design.atom dropLabel = design.atom keptLabel
          ∨ design.atom dropLabel = -design.atom keptLabel) := by
  constructor
  · intro hhinge design htie
    obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩ := hhinge design htie
    refine ⟨keptLabel, dropLabel, hdistinct, ?_⟩
    have hsq := sq_eq_one_of_parallel_of_isTie_sixThree design htie hdistinct hparallel
    rcases mul_eq_zero.mp (show (ratio - 1) * (ratio + 1) = 0 by linear_combination hsq)
      with h | h
    · exact Or.inl (by rw [hparallel, show ratio = 1 by linarith, one_smul])
    · exact Or.inr (by rw [hparallel, show ratio = -1 by linarith, neg_one_smul])
  · intro hrepeat design htie
    obtain ⟨keptLabel, dropLabel, hdistinct, hcase⟩ := hrepeat design htie
    rcases hcase with h | h
    · exact ⟨keptLabel, dropLabel, 1, hdistinct, by rw [h, one_smul]⟩
    · exact ⟨keptLabel, dropLabel, -1, hdistinct, by rw [h, neg_one_smul]⟩

end Gtz

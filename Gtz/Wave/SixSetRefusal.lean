import Gtz.Wave.SixSetDowndate
import Gtz.LinAlg.DepthThreeDowndate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The refusal-consumption dictionary of the six-set metric

`Gtz.not_isTie_of_sixSet_combination_reading` produces strictness: a triple
whose combination readings stay below their square norms exhibits a strict
dominator and refutes the tie.  This module lands the CONSUMPTION direction:
at a tie, every triple's readings must reach the threshold.

Two forms.  The contrapositive form (`Gtz.tie_forces_sixSet_reading`)
exhibits, for every card-3 subset of a `(6,3)` tie, a nonzero combination
`ξ` of its atoms whose six-set reading `gᵀW⁻¹g` reaches `|ξ|²` — the
eigen-free statement that every complementary 3×3 block of the pivot matrix
has `λ_max ≥ 1`.  The scalarized form (`Gtz.tie_refusal_sylvester`) reads the
same refusal through the depth-three downdate dictionary
(`Gtz.not_posDef_sub_three_vecMulVec_iff`): one of the three Sylvester
minors of `I₃ − P_R` gives way, where `P_R` is the 3×3 block of six-set
pivots at the subset.  The scalar form is the input format of the corner
certificates: refusals arrive as polynomial inequalities in the pivots.

Both need the complement of a triple to be a triple, so nothing here can be
stated at `(5,3)`: there is no diamond hazard, by construction.
-/

namespace Gtz

open Matrix Finset

/-- **A tie forces every combination threshold.**  At a `(6,3)` tie whose
six-set gap is positive definite, every card-3 subset carries a nonzero
combination of its atoms whose six-set reading reaches its square norm. -/
theorem tie_forces_sixSet_reading (D : WeightedDesign 6 3) (htie : IsTie D)
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    {r1 r2 r3 : Fin 6} (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) :
    ∃ r s q : ℝ, ¬(r = 0 ∧ s = 0 ∧ q = 0) ∧
      r ^ 2 + s ^ 2 + q ^ 2
        ≤ (r • D.atom r1 + s • D.atom r2 + q • D.atom r3)
            ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹
              *ᵥ (r • D.atom r1 + s • D.atom r2 + q • D.atom r3)) := by
  by_contra hcon
  push_neg at hcon
  exact not_isTie_of_sixSet_combination_reading D hPD h12 h13 h23
    (fun r s q hne => hcon r s q fun hr hs hq => hne ⟨hr, hs, hq⟩) htie

/-- **The scalarized refusal.**  At a `(6,3)` tie whose six-set gap is
positive definite, every card-3 subset's 3×3 block of six-set pivots
breaks one of the three Sylvester minors of `I₃ − P_R`: the first pivot
reaches one, or the pair determinant gives way, or the full determinant
does. -/
theorem tie_refusal_sylvester (D : WeightedDesign 6 3) (htie : IsTie D)
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    {r1 r2 r3 : Fin 6} (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) :
    1 ≤ D.atom r1 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r1)
      ∨ (1 - D.atom r1 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r1))
            * (1 - D.atom r2 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r2))
          ≤ (D.atom r1 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r2)) ^ 2
      ∨ (1 - D.atom r1 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r1))
            * (1 - D.atom r2 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r2))
            * (1 - D.atom r3 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r3))
          ≤ (1 - D.atom r1 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r1))
              * (D.atom r2 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r3)) ^ 2
            + (1 - D.atom r2 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r2))
              * (D.atom r1 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r3)) ^ 2
            + (1 - D.atom r3 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r3))
              * (D.atom r1 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r2)) ^ 2
            + 2 * ((D.atom r1 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r2))
              * (D.atom r1 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r3))
              * (D.atom r2 ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom r3))) := by
  classical
  set R : Finset (Fin 6) := {r1, r2, r3} with hR
  have hcardR : R.card = 3 := by
    rw [hR, Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  have hcardRc : Rᶜ.card = 3 := card_compl_eq_three_of_card_eq_three R hcardR
  have hsum : ∑ r ∈ R, atomMatrix (D.atom r)
      = Matrix.vecMulVec (D.atom r1) (D.atom r1)
        + Matrix.vecMulVec (D.atom r2) (D.atom r2)
        + Matrix.vecMulVec (D.atom r3) (D.atom r3) := by
    rw [hR, Finset.sum_insert (by simp [h12, h13]),
      Finset.sum_insert (by simp [h23]), Finset.sum_singleton, atomMatrix,
      atomMatrix, atomMatrix]
    abel
  have hgapEq := tripleGap_eq_sixSet_downdate D R
  rw [hsum] at hgapEq
  have hrefused : ¬ (subsetSum D Rᶜ - 1).PosDef := htie.2 Rᶜ hcardRc
  have hshape : (subsetSum D Finset.univ - 1)
        - (Matrix.vecMulVec (D.atom r1) (D.atom r1)
          + Matrix.vecMulVec (D.atom r2) (D.atom r2)
          + Matrix.vecMulVec (D.atom r3) (D.atom r3))
      = (subsetSum D Finset.univ - 1)
        - Matrix.vecMulVec (D.atom r1) (D.atom r1)
        - Matrix.vecMulVec (D.atom r2) (D.atom r2)
        - Matrix.vecMulVec (D.atom r3) (D.atom r3) := by
    abel
  rw [hgapEq, hshape] at hrefused
  exact (not_posDef_sub_three_vecMulVec_iff (subsetSum D Finset.univ - 1) hPD
    (D.atom r1) (D.atom r2) (D.atom r3)).mp hrefused

end Gtz

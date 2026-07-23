/-
# The deflation engine: coisometries push weighted designs forward

The all-k induction (the Lifting-Lemma route) deflates dimension: fix a
pivot atom, project the others onto its orthocomplement, and the
projections satisfy the SAME-weight Parseval identity in dimension `k−1`.
The engine underneath is coordinate-free and unconditional: ANY coisometry
`B` (`B·Bᵀ = 1`) pushes a weighted design forward to a weighted design —
same weights, atoms `B·g_c`. The orthocomplement projection is the
instance where `B`'s rows are an orthonormal completion basis.

This is the first kernel footprint of the all-k frontier: the induction's
Parseval step is now a theorem, independent of the (open) pivot-selection
content of the Lifting Lemma itself.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

open Matrix Finset

variable {m k j : ℕ}

/-- **Rectangular conjugation of a rank-one square**:
`(B·g)(B·g)ᵀ = B·(g gᵀ)·Bᵀ` for any rectangular `B`. -/
theorem atomMatrix_mulVec_conj (rectangular : Matrix (Fin j) (Fin k) ℝ)
    (direction : Fin k → ℝ) :
    atomMatrix (rectangular *ᵥ direction)
      = rectangular * atomMatrix direction * rectangularᵀ := by
  ext row col
  simp only [atomMatrix, Matrix.vecMulVec_apply, Matrix.mulVec,
    Matrix.mul_apply, Matrix.transpose_apply, dotProduct]
  rw [Finset.sum_mul_sum]
  conv_rhs => simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun innerLeft _ => ?_
  refine Finset.sum_congr rfl fun innerRight _ => ?_
  ring

/-- **The coisometry pushforward**: a weighted design in dimension `k`
pushes forward along any coisometry `B : ℝᵏ → ℝʲ` (`B·Bᵀ = 1`) to a
weighted design in dimension `j` with the SAME weights — the deflation
induction's Parseval step, unconditional. -/
def coisometryPushforward (D : WeightedDesign m k)
    (rectangular : Matrix (Fin j) (Fin k) ℝ)
    (hcoisometry : rectangular * rectangularᵀ = 1) : WeightedDesign m j where
  atom index := rectangular *ᵥ D.atom index
  weight := D.weight
  weight_pos := D.weight_pos
  weight_sum_one := D.weight_sum_one
  isParseval := by
    have hconjugated : ∑ index, D.weight index
        • atomMatrix (rectangular *ᵥ D.atom index)
        = rectangular * (∑ index, D.weight index
            • atomMatrix (D.atom index)) * rectangularᵀ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun index _ => ?_
      rw [atomMatrix_mulVec_conj, Matrix.mul_smul, Matrix.smul_mul]
    rw [hconjugated, D.isParseval, Matrix.mul_one, hcoisometry]

/-- The pushforward keeps every weight (definitional reading). -/
theorem coisometryPushforward_weight (D : WeightedDesign m k)
    (rectangular : Matrix (Fin j) (Fin k) ℝ)
    (hcoisometry : rectangular * rectangularᵀ = 1) (index : Fin m) :
    (coisometryPushforward D rectangular hcoisometry).weight index
      = D.weight index := rfl

/-- The pushforward's atoms are the projected atoms (definitional
reading). -/
theorem coisometryPushforward_atom (D : WeightedDesign m k)
    (rectangular : Matrix (Fin j) (Fin k) ℝ)
    (hcoisometry : rectangular * rectangularᵀ = 1) (index : Fin m) :
    (coisometryPushforward D rectangular hcoisometry).atom index
      = rectangular *ᵥ D.atom index := rfl

end Gtz

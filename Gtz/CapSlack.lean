/-
# Theorem D: the cap–slack determinant identities

The determinant form of the certificate's two branches, at every rank. The
engine is the matrix determinant lemma specialized to rank-one atom updates of
a symmetric invertible base:

  `det(N ± g gᵀ) = det N · (1 ± gᵀ N⁻¹ g)` — symmetry of the base is not even
needed, because the update vector appears on both sides.

Read at the pigeonhole base `N = S_Q − 1 ≻ 0` this says the erased subset's
excess determinant is `det(S_Q − 1)·(1 − q_d)` — the depth IS the determinant
ratio — and since a rank-one downdate of a positive definite matrix has at most
one negative eigenvalue, the erased subset dominates exactly when that
determinant is nonnegative. Read at a cap base of signature `(k−1,1)`
(negative determinant) the same lemma flips the inequality: the cap fires,
`gᵀN⁻¹g ≤ −1`, exactly when `det(N + g gᵀ) ≥ 0`. One identity, both branches,
no eigenvalues computed anywhere — this is the k-uniform content behind the
planar wall law `ℓ_e·P* = det(H−I)`.
-/
import Mathlib
import Gtz.Basic
import Gtz.TraceIdentity
import Gtz.SchurRankOne

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### The matrix determinant lemma for atoms -/

/-- Splitting off a subtracted atom as a column–row product. -/
theorem sub_atomMatrix_eq_add_replicate (N : Matrix (Fin k) (Fin k) ℝ)
    (g : Fin k → ℝ) :
    N - atomMatrix g
      = N + Matrix.replicateCol Unit g * Matrix.replicateRow Unit (-g) := by
  ext firstIndex secondIndex
  simp [atomMatrix, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.replicateCol_apply, Matrix.replicateRow_apply, sub_eq_add_neg,
    mul_comm]

/-- Splitting off an added atom as a column–row product. -/
theorem add_atomMatrix_eq_add_replicate (N : Matrix (Fin k) (Fin k) ℝ)
    (g : Fin k → ℝ) :
    N + atomMatrix g
      = N + Matrix.replicateCol Unit g * Matrix.replicateRow Unit g := by
  ext firstIndex secondIndex
  simp [atomMatrix, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.replicateCol_apply, Matrix.replicateRow_apply, mul_comm]

/-- The one-by-one determinant appearing in the update formula, evaluated. -/
theorem det_one_add_row_inv_col (N : Matrix (Fin k) (Fin k) ℝ)
    (leftVec rightVec : Fin k → ℝ) :
    (1 + Matrix.replicateRow Unit leftVec * N
        * Matrix.replicateCol Unit rightVec).det
      = 1 + leftVec ⬝ᵥ (N *ᵥ rightVec) := by
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- **The determinant lemma, subtracted atom**: for invertible `N`,
`det(N − g gᵀ) = det N · (1 − gᵀN⁻¹g)`. -/
theorem det_sub_atomMatrix {N : Matrix (Fin k) (Fin k) ℝ}
    (hdet : IsUnit N.det) (g : Fin k → ℝ) :
    (N - atomMatrix g).det = N.det * (1 - g ⬝ᵥ (N⁻¹ *ᵥ g)) := by
  rw [sub_atomMatrix_eq_add_replicate,
    Matrix.det_add_replicateCol_mul_replicateRow hdet,
    det_one_add_row_inv_col]
  have hflip : (-g) ⬝ᵥ (N⁻¹ *ᵥ g) = -(g ⬝ᵥ (N⁻¹ *ᵥ g)) := by
    rw [neg_dotProduct]
  rw [hflip]
  ring

/-- **The determinant lemma, added atom**: `det(N + g gᵀ) = det N·(1 + gᵀN⁻¹g)`. -/
theorem det_add_atomMatrix {N : Matrix (Fin k) (Fin k) ℝ}
    (hdet : IsUnit N.det) (g : Fin k → ℝ) :
    (N + atomMatrix g).det = N.det * (1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) := by
  rw [add_atomMatrix_eq_add_replicate,
    Matrix.det_add_replicateCol_mul_replicateRow hdet,
    det_one_add_row_inv_col]

/-! ### The pigeonhole branch in determinant form -/

/-- **The depth is the determinant ratio**: erasing an insider scales the excess
determinant by exactly `1 − q_d`. This is Theorem D's identity at the
pigeonhole base, every rank, every size. -/
theorem det_erase_eq_det_mul_pivot_gap (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hQ : (subsetSum D Q - 1).PosDef) {d : Fin m}
    (hd : d ∈ Q) :
    (subsetSum D (Q.erase d) - 1).det
      = (subsetSum D Q - 1).det * (1 - pivot D Q d) := by
  have hdet : IsUnit (subsetSum D Q - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hQ.det_pos)
  have herase : subsetSum D (Q.erase d) - 1
      = (subsetSum D Q - 1) - atomMatrix (D.atom d) := by
    have hsum := Finset.sum_erase_add Q (fun c => atomMatrix (D.atom c)) hd
    rw [subsetSum, subsetSum, ← hsum]
    abel
  rw [herase, det_sub_atomMatrix hdet, pivot_eq_dot]

/-- **The fire test is a determinant sign**: under a positive definite base,
the erased subset dominates exactly when its own excess determinant is
nonnegative. One scalar decides the branch — no spectrum, no minors. -/
theorem erase_dominates_iff_det_nonneg (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hQ : (subsetSum D Q - 1).PosDef) {d : Fin m}
    (hd : d ∈ Q) :
    Dominates D (Q.erase d) ↔ 0 ≤ (subsetSum D (Q.erase d) - 1).det := by
  rw [erase_dominates_iff_pivot_le_one D Q hQ hd,
    det_erase_eq_det_mul_pivot_gap D Q hQ hd]
  constructor
  · intro hpivot
    exact mul_nonneg hQ.det_pos.le (by linarith)
  · intro hdetNonneg
    nlinarith [hQ.det_pos, hdetNonneg]

/-! ### The cap branch in determinant form -/

/-- **The cap fire is the opposite determinant sign**: against a base of
negative determinant (the signature-(k−1,1) cap), the depth condition
`gᵀN⁻¹g ≤ −1` holds exactly when `det(N + g gᵀ) ≥ 0`. The same determinant
lemma decides both branches with the inequality flipped by the base's sign —
this is the k-uniform root of the planar wall law. -/
theorem cap_fires_iff_det_nonneg {N : Matrix (Fin k) (Fin k) ℝ}
    (hdetNeg : N.det < 0) (g : Fin k → ℝ) :
    g ⬝ᵥ (N⁻¹ *ᵥ g) ≤ -1 ↔ 0 ≤ (N + atomMatrix g).det := by
  have hdet : IsUnit N.det := isUnit_iff_ne_zero.mpr (ne_of_lt hdetNeg)
  rw [det_add_atomMatrix hdet]
  constructor
  · intro hdepth
    nlinarith [hdetNeg]
  · intro hdetNonneg
    nlinarith [hdetNeg, hdetNonneg]

end Gtz

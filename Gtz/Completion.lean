/-
# Orthonormal completion: [A | B] square orthogonal from AᵀA = I

Any m×k real matrix with orthonormal columns completes to a square orthogonal
matrix. Route: the columns are an orthonormal family in Euclidean m-space; the
orthogonal complement of their span has dimension m−k and carries
`stdOrthonormalBasis`; the juxtaposition [A | B] then has orthonormal columns,
and `Matrix.fromCols_mul_fromRows_eq_one_comm` (one-sided inverses of square
matrices commute) upgrades column orthonormality to row completeness
A·Aᵀ + B·Bᵀ = I. This is the only ingredient of Theorem N that touches
inner-product-space machinery; everything downstream is congruence algebra.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

open Matrix

open scoped RealInnerProductSpace

/-- The j-th column of a matrix as a Euclidean vector. -/
def columnVec {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (j : Fin k) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun c => A c j)

/-- Euclidean inner products of columns are Gram entries. -/
theorem inner_columnVec {m k l : ℕ} (A : Matrix (Fin m) (Fin k) ℝ)
    (B : Matrix (Fin m) (Fin l) ℝ) (i : Fin k) (j : Fin l) :
    ⟪columnVec A i, columnVec B j⟫ = (Aᵀ * B) i j := by
  rw [columnVec, columnVec, EuclideanSpace.inner_toLp_toLp, Matrix.mul_apply]
  simp [dotProduct, Matrix.transpose_apply, mul_comm]

/-- **Orthonormal completion.** Any m×k matrix with orthonormal columns
completes to a square orthogonal matrix: some B has orthonormal columns
orthogonal to A's, and jointly they resolve the identity. -/
theorem exists_orthonormal_completion {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ) (hA : Aᵀ * A = 1) :
    ∃ B : Matrix (Fin m) (Fin (m - k)) ℝ,
      Bᵀ * B = 1 ∧ Aᵀ * B = 0 ∧ A * Aᵀ + B * Bᵀ = 1 := by
  classical
  -- the columns of A are orthonormal, so their span has dimension k ≤ m
  have honA : Orthonormal ℝ (columnVec A) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_columnVec, hA, Matrix.one_apply]
  set spanA : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
    Submodule.span ℝ (Set.range (columnVec A)) with hspanA
  have hrankA : Module.finrank ℝ spanA = k := by
    rw [hspanA, finrank_span_eq_card honA.linearIndependent, Fintype.card_fin]
  have hkm : k ≤ m := by
    have hle := Submodule.finrank_le spanA
    rwa [hrankA, finrank_euclideanSpace_fin] at hle
  have hrankPerp : Module.finrank ℝ spanAᗮ = m - k := by
    have htotal := spanA.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin, hrankA] at htotal
    omega
  -- the perpendicular orthonormal basis, as the columns of B
  set perpBasis :=
    (stdOrthonormalBasis ℝ (↥spanAᗮ)).reindex (finCongr hrankPerp) with hperpBasis
  set B : Matrix (Fin m) (Fin (m - k)) ℝ :=
    Matrix.of (fun c j =>
      WithLp.ofLp ((perpBasis j : EuclideanSpace ℝ (Fin m))) c) with hB
  have hcolB : ∀ j, columnVec B j = (perpBasis j : EuclideanSpace ℝ (Fin m)) := by
    intro j
    simp only [columnVec, hB, Matrix.of_apply]
  -- the three Gram identities
  have hBB : Bᵀ * B = 1 := by
    ext i j
    have hon := perpBasis.orthonormal
    rw [orthonormal_iff_ite] at hon
    have hij := hon i j
    rw [Submodule.coe_inner, ← hcolB, ← hcolB, inner_columnVec] at hij
    rw [hij, Matrix.one_apply]
  have hAB : Aᵀ * B = 0 := by
    ext i j
    have hmem : (perpBasis j : EuclideanSpace ℝ (Fin m)) ∈ spanAᗮ := (perpBasis j).2
    have hzero := Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self i)) hmem
    rw [← hcolB, inner_columnVec] at hzero
    rw [hzero, Matrix.zero_apply]
  have hBA : Bᵀ * A = 0 := by
    have htr := congrArg Matrix.transpose hAB
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] at htr
  -- column orthonormality of the square [A | B] flips to row completeness
  have hsquare : Matrix.fromRows Aᵀ Bᵀ * Matrix.fromCols A B = 1 := by
    rw [Matrix.fromRows_mul_fromCols, hA, hAB, hBA, hBB, Matrix.fromBlocks_one]
  have hindex : Fin m ≃ Fin k ⊕ Fin (m - k) :=
    (finCongr (by omega : m = k + (m - k))).trans finSumFinEquiv.symm
  have hflip := (Matrix.fromCols_mul_fromRows_eq_one_comm hindex A B Aᵀ Bᵀ).mpr hsquare
  rw [Matrix.fromCols_mul_fromRows] at hflip
  exact ⟨B, hBB, hAB, hflip⟩

end Gtz

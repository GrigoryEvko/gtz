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
import Gtz.Completion

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

/-- **The deflation coisometry exists**: every unit pivot direction in
`ℝ^(k+1)` admits a coisometry `B : ℝ^(k+1) → ℝᵏ` whose rows are orthonormal
and orthogonal to the pivot, with the completeness split
`Bᵀ·B + u·uᵀ = 1` — the orthonormal basis of `u^⊥` packaged as the matrix
the pushforward consumes. Instantiates `exists_orthonormal_completion` at
one column and transposes. -/
theorem exists_deflation_coisometry {k : ℕ} {pivotDir : Fin (k + 1) → ℝ}
    (hpivotUnit : pivotDir ⬝ᵥ pivotDir = 1) :
    ∃ deflator : Matrix (Fin k) (Fin (k + 1)) ℝ,
      deflator * deflatorᵀ = 1
        ∧ deflator *ᵥ pivotDir = 0
        ∧ deflatorᵀ * deflator + atomMatrix pivotDir = 1 := by
  set pivotColumn : Matrix (Fin (k + 1)) (Fin 1) ℝ :=
    fun rowIndex _ => pivotDir rowIndex with hpivotColumn
  have hcolumnOrtho : pivotColumnᵀ * pivotColumn = 1 := by
    ext firstIndex secondIndex
    fin_cases firstIndex
    fin_cases secondIndex
    simpa [hpivotColumn, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.one_apply, dotProduct] using hpivotUnit
  obtain ⟨completion, hcompletionOrtho, hcrossZero, hcomplete⟩ :=
    exists_orthonormal_completion pivotColumn hcolumnOrtho
  refine ⟨completionᵀ, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_transpose]
    exact hcompletionOrtho
  · funext rowIndex
    have hcrossEntry := congrFun (congrFun hcrossZero 0) rowIndex
    simp only [Matrix.mul_apply, Matrix.transpose_apply,
      hpivotColumn] at hcrossEntry
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Pi.zero_apply]
    rw [Finset.sum_congr rfl fun index _ =>
      mul_comm (completion index rowIndex) (pivotDir index)]
    exact hcrossEntry
  · have hpivotSquare : pivotColumn * pivotColumnᵀ = atomMatrix pivotDir := by
      ext firstIndex secondIndex
      simp [hpivotColumn, Matrix.mul_apply, Matrix.transpose_apply,
        atomMatrix, Matrix.vecMulVec_apply]
    rw [Matrix.transpose_transpose]
    rw [hpivotSquare] at hcomplete
    rw [← hcomplete]
    exact add_comm (completion * completionᵀ) (atomMatrix pivotDir)

/-- **Pivot deflation, end-to-end**: every NONZERO atom of a weighted design
in dimension `k+1` yields a positive normalizing scale and a deflation
coisometry — rows orthonormal, annihilating the atom itself, with the
completeness split at the normalized direction. Feeding `deflator` to
`coisometryPushforward` gives the projected design of the SS15 induction
step; no unit-norm hypothesis survives, only `atom ≠ 0`. -/
theorem exists_pivot_deflation {m k : ℕ} (D : WeightedDesign m (k + 1))
    (pivot : Fin m) (hpivotNonzero : D.atom pivot ≠ 0) :
    ∃ (scale : ℝ) (deflator : Matrix (Fin k) (Fin (k + 1)) ℝ),
      0 < scale
        ∧ deflator * deflatorᵀ = 1
        ∧ deflator *ᵥ D.atom pivot = 0
        ∧ deflatorᵀ * deflator + atomMatrix (scale • D.atom pivot) = 1 := by
  set lev := D.atom pivot ⬝ᵥ D.atom pivot with hlev
  have hlevNonneg : 0 ≤ lev := by
    rw [hlev]
    simp only [dotProduct]
    exact Finset.sum_nonneg fun index _ => mul_self_nonneg _
  have hlevPos : 0 < lev := by
    rcases eq_or_lt_of_le hlevNonneg with hzero | hpos
    · exact absurd (dotProduct_self_eq_zero.mp hzero.symm) hpivotNonzero
    · exact hpos
  have hsqrtPos : 0 < Real.sqrt lev := Real.sqrt_pos.mpr hlevPos
  have hunit : ((Real.sqrt lev)⁻¹ • D.atom pivot)
      ⬝ᵥ ((Real.sqrt lev)⁻¹ • D.atom pivot) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hlevPos.le]
    exact inv_mul_cancel₀ (ne_of_gt hlevPos)
  obtain ⟨deflator, hcoisometry, hkillScaled, hsplit⟩ :=
    exists_deflation_coisometry hunit
  refine ⟨(Real.sqrt lev)⁻¹, deflator, inv_pos.mpr hsqrtPos, hcoisometry,
    ?_, hsplit⟩
  have hkillSmul : (Real.sqrt lev)⁻¹ • (deflator *ᵥ D.atom pivot) = 0 := by
    rw [← Matrix.mulVec_smul]
    exact hkillScaled
  rcases smul_eq_zero.mp hkillSmul with hscaleZero | hvecZero
  · exact absurd hscaleZero (inv_ne_zero (ne_of_gt hsqrtPos))
  · exact hvecZero

end Gtz

import Mathlib
import Gtz.Quantitative.MarginContinuity
import Gtz.Reduction.ChartAttainment

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Reindexing invariance of the least Rayleigh value

`lambdaMinMat` is the infimum of Rayleigh quotients over nonzero vectors, and a
permutation of the index set is a bijection of nonzero vectors preserving both
the quadratic form and the norm.  So the least Rayleigh value of a permuted
submatrix is the least Rayleigh value of the matrix — and, downstream, the least
eigenvalue of a principal block depends only on the SET of selected indices, not
on the enumeration used to cut the block.  These are the two analytic bricks
under the relabelling equivariance of the chart objective.
-/

namespace Gtz

open Matrix

/-- Composing with a permutation preserves the dot product. -/
theorem dotProduct_comp_equiv {k : ℕ} (reindex : Equiv.Perm (Fin k))
    (leftVec rightVec : Fin k → ℝ) :
    (fun index => leftVec (reindex index)) ⬝ᵥ (fun index => rightVec (reindex index))
      = leftVec ⬝ᵥ rightVec := by
  simp only [dotProduct]
  exact Equiv.sum_comp reindex fun index => leftVec index * rightVec index

/-- A permuted submatrix acts on a probe as the matrix acts on the transported
probe, read back through the permutation. -/
theorem submatrix_equiv_mulVec_apply {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (reindex : Equiv.Perm (Fin k)) (probe : Fin k → ℝ) (rowIndex : Fin k) :
    (M.submatrix reindex reindex *ᵥ probe) rowIndex
      = (M *ᵥ fun index => probe (reindex.symm index)) (reindex rowIndex) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  calc ∑ colIndex, M (reindex rowIndex) (reindex colIndex) * probe colIndex
      = ∑ colIndex, M (reindex rowIndex) (reindex colIndex)
          * probe (reindex.symm (reindex colIndex)) := by
        refine Finset.sum_congr rfl fun colIndex _ => ?_
        rw [Equiv.symm_apply_apply]
    _ = ∑ colIndex, M (reindex rowIndex) colIndex * probe (reindex.symm colIndex) :=
        Equiv.sum_comp reindex fun colIndex =>
          M (reindex rowIndex) colIndex * probe (reindex.symm colIndex)

/-- The quadratic form of a permuted submatrix is the quadratic form of the
matrix at the transported probe. -/
theorem dotProduct_submatrix_equiv_mulVec {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (reindex : Equiv.Perm (Fin k)) (probe : Fin k → ℝ) :
    probe ⬝ᵥ (M.submatrix reindex reindex *ᵥ probe)
      = (fun index => probe (reindex.symm index))
          ⬝ᵥ (M *ᵥ fun index => probe (reindex.symm index)) := by
  have htransport : probe ⬝ᵥ (M.submatrix reindex reindex *ᵥ probe)
      = (fun index => probe (reindex.symm (reindex index)))
          ⬝ᵥ (fun index =>
              (M *ᵥ fun inner => probe (reindex.symm inner)) (reindex index)) := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun rowIndex _ => ?_
    rw [Equiv.symm_apply_apply, submatrix_equiv_mulVec_apply]
  rw [htransport]
  exact dotProduct_comp_equiv reindex (fun index => probe (reindex.symm index))
    (M *ᵥ fun index => probe (reindex.symm index))

/-- **The least Rayleigh value is invariant under permutation reindexing.** -/
theorem lambdaMinMat_submatrix_equiv {k : ℕ} [Nonempty (Fin k)]
    (M : Matrix (Fin k) (Fin k) ℝ) (reindex : Equiv.Perm (Fin k)) :
    lambdaMinMat (M.submatrix reindex reindex) = lambdaMinMat M := by
  classical
  have htoLpNe : ∀ (transport : Equiv.Perm (Fin k)) (probe : EuclideanSpace ℝ (Fin k)),
      probe ≠ 0 →
        (WithLp.toLp 2 fun index => probe (transport index) :
          EuclideanSpace ℝ (Fin k)) ≠ 0 := by
    intro transport probe hne hzero
    apply hne
    ext atomIndex
    have hplain := congrArg (WithLp.ofLp (p := 2)) hzero
    have hcoordinate := congrFun hplain (transport.symm atomIndex)
    simpa using hcoordinate
  have hrayleigh : ∀ probe : EuclideanSpace ℝ (Fin k),
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (M.submatrix reindex reindex)).rayleighQuotient probe
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) M).rayleighQuotient
            (WithLp.toLp 2 fun index => probe (reindex.symm index)) := by
    intro probe
    rw [rayleigh_toEuclideanCLM_eq, rayleigh_toEuclideanCLM_eq,
      euclid_norm_sq_eq_dotProduct, euclid_norm_sq_eq_dotProduct]
    have hquad := dotProduct_submatrix_equiv_mulVec M reindex (WithLp.ofLp probe)
    have hnorm := dotProduct_comp_equiv reindex.symm (WithLp.ofLp probe) (WithLp.ofLp probe)
    rw [hquad, ← hnorm]
  have hpull : ∀ probe : EuclideanSpace ℝ (Fin k),
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (M.submatrix reindex reindex)).rayleighQuotient
          (WithLp.toLp 2 fun index => probe (reindex index))
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) M).rayleighQuotient probe := by
    intro probe
    rw [hrayleigh]
    congr 1
    ext atomIndex
    simp
  apply le_antisymm
  · rw [lambdaMinMat, lambdaMinMat, lambdaMinCLM, lambdaMinCLM]
    refine le_ciInf fun probe => ?_
    calc (⨅ x : {x : EuclideanSpace ℝ (Fin k) // x ≠ 0},
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (M.submatrix reindex reindex)).rayleighQuotient x)
        ≤ (Matrix.toEuclideanCLM (𝕜 := ℝ) (M.submatrix reindex reindex)).rayleighQuotient
            (WithLp.toLp 2 fun index => (probe : EuclideanSpace ℝ (Fin k)) (reindex index)) :=
          ciInf_le (rayleigh_bddBelow _)
            ⟨WithLp.toLp 2 fun index => (probe : EuclideanSpace ℝ (Fin k)) (reindex index),
              htoLpNe reindex probe probe.2⟩
      _ = (Matrix.toEuclideanCLM (𝕜 := ℝ) M).rayleighQuotient
            (probe : EuclideanSpace ℝ (Fin k)) := hpull probe
  · rw [lambdaMinMat, lambdaMinMat, lambdaMinCLM, lambdaMinCLM]
    refine le_ciInf fun probe => ?_
    calc (⨅ x : {x : EuclideanSpace ℝ (Fin k) // x ≠ 0},
          (Matrix.toEuclideanCLM (𝕜 := ℝ) M).rayleighQuotient x)
        ≤ (Matrix.toEuclideanCLM (𝕜 := ℝ) M).rayleighQuotient
            (WithLp.toLp 2 fun index =>
              (probe : EuclideanSpace ℝ (Fin k)) (reindex.symm index)) :=
          ciInf_le (rayleigh_bddBelow _)
            ⟨WithLp.toLp 2 fun index =>
              (probe : EuclideanSpace ℝ (Fin k)) (reindex.symm index),
              htoLpNe reindex.symm probe probe.2⟩
      _ = (Matrix.toEuclideanCLM (𝕜 := ℝ)
            (M.submatrix reindex reindex)).rayleighQuotient
              (probe : EuclideanSpace ℝ (Fin k)) := (hrayleigh probe).symm

/-- **The least block eigenvalue depends only on the selected index set**: two
injective enumerations with the same range cut congruent blocks. -/
theorem lambdaMinMat_submatrix_eq_of_range_eq {k size : ℕ} [Nonempty (Fin k)]
    (gap : Matrix (Fin size) (Fin size) ℝ)
    (firstEnum secondEnum : Fin k → Fin size)
    (hfirstInjective : Function.Injective firstEnum)
    (hsecondInjective : Function.Injective secondEnum)
    (hrange : Set.range firstEnum = Set.range secondEnum) :
    lambdaMinMat (gap.submatrix firstEnum firstEnum)
      = lambdaMinMat (gap.submatrix secondEnum secondEnum) := by
  classical
  let transport : Fin k ≃ Fin k :=
    (Equiv.ofInjective firstEnum hfirstInjective).trans
      ((Equiv.setCongr hrange).trans (Equiv.ofInjective secondEnum hsecondInjective).symm)
  have hcompose : ∀ index : Fin k, secondEnum (transport index) = firstEnum index := by
    intro index
    dsimp only [transport, Equiv.trans_apply]
    rw [Equiv.apply_ofInjective_symm hsecondInjective]
    rfl
  have hsubmatrix : gap.submatrix firstEnum firstEnum
      = (gap.submatrix secondEnum secondEnum).submatrix transport transport := by
    ext rowIndex colIndex
    simp only [Matrix.submatrix_apply, hcompose]
  rw [hsubmatrix, lambdaMinMat_submatrix_equiv]

end Gtz

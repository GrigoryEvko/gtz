import Gtz.Wave.IsolatedRowProjectionKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! **KERNEL DEPENDENCIES ARE PARALLEL PAIRS.**  The chart of a design is the
Gram projection of its scaled atom rows, so a kernel vector of the chart is a
linear dependency among the scaled atoms.  A dependency supported on two atoms
makes them parallel, and two non-proportional dependencies supported inside a
triple combine into one supported on a pair.  This is the exit the disconnected
triangle-plus-full profiles feed after the projection annihilates their full
row and block-diagonalises the chart. -/

/-- A chart kernel vector is a dependency among the scaled atom rows. -/
theorem scaledAtomRows_transpose_mulVec_eq_zero_of_projection_mulVec_eq_zero
    {atoms rankValue : ℕ} (design : WeightedDesign atoms rankValue)
    {kernelVec : Fin atoms → ℝ}
    (hkernel : projectionOfDesign design *ᵥ kernelVec = 0) :
    (scaledAtomRows design)ᵀ *ᵥ kernelVec = 0 := by
  have hquad : kernelVec ⬝ᵥ (projectionOfDesign design *ᵥ kernelVec) = 0 := by
    rw [hkernel]
    exact dotProduct_zero kernelVec
  rw [projectionOfDesign, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
    ← Matrix.transpose_transpose (scaledAtomRows design), Matrix.vecMul_transpose,
    Matrix.transpose_transpose] at hquad
  exact dotProduct_self_eq_zero.mp hquad

/-- The coordinate reading of a scaled-atom dependency supported on two atoms. -/
theorem pairSupported_dependency_combination
    {atoms rankValue : ℕ} (design : WeightedDesign atoms rankValue)
    {kernelVec : Fin atoms → ℝ} {firstAtom secondAtom : Fin atoms}
    (hatomsNe : firstAtom ≠ secondAtom)
    (hdependency : (scaledAtomRows design)ᵀ *ᵥ kernelVec = 0)
    (hsupport : ∀ atomIndex : Fin atoms,
      atomIndex ∉ ({firstAtom, secondAtom} : Finset (Fin atoms)) →
        kernelVec atomIndex = 0) :
    (kernelVec firstAtom * Real.sqrt (design.weight firstAtom))
        • design.atom firstAtom
      + (kernelVec secondAtom * Real.sqrt (design.weight secondAtom))
        • design.atom secondAtom = 0 := by
  classical
  funext coordIndex
  have hcolumn := congrFun hdependency coordIndex
  simp only [Pi.zero_apply] at hcolumn
  have hexpand : ((scaledAtomRows design)ᵀ *ᵥ kernelVec) coordIndex
      = ∑ atomIndex : Fin atoms, kernelVec atomIndex
          * (Real.sqrt (design.weight atomIndex) * design.atom atomIndex coordIndex) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, scaledAtomRows,
      Matrix.of_apply]
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  rw [hexpand] at hcolumn
  have hrestrict : ∑ atomIndex : Fin atoms, kernelVec atomIndex
      * (Real.sqrt (design.weight atomIndex) * design.atom atomIndex coordIndex)
      = ∑ atomIndex ∈ ({firstAtom, secondAtom} : Finset (Fin atoms)),
          kernelVec atomIndex
            * (Real.sqrt (design.weight atomIndex) * design.atom atomIndex coordIndex) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro atomIndex _ hnotPair
    rw [hsupport atomIndex hnotPair, zero_mul]
  rw [hrestrict, Finset.sum_pair hatomsNe] at hcolumn
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  linear_combination hcolumn

/-- **A PAIR-SUPPORTED DEPENDENCY IS A PARALLEL PAIR.**  Either both
coefficients are nonzero and one atom is a scalar multiple of the other, or a
lone coefficient survives and its atom vanishes — a ratio-zero parallel pair. -/
theorem hasParallelPair_of_pairSupported_dependency
    {atoms rankValue : ℕ} (design : WeightedDesign atoms rankValue)
    {kernelVec : Fin atoms → ℝ} {firstAtom secondAtom : Fin atoms}
    (hatomsNe : firstAtom ≠ secondAtom)
    (hdependency : (scaledAtomRows design)ᵀ *ᵥ kernelVec = 0)
    (hsupport : ∀ atomIndex : Fin atoms,
      atomIndex ∉ ({firstAtom, secondAtom} : Finset (Fin atoms)) →
        kernelVec atomIndex = 0)
    (hnonzero : kernelVec ≠ 0) :
    HasParallelPair design := by
  classical
  have hcombination := pairSupported_dependency_combination design hatomsNe
    hdependency hsupport
  have hsqrtFirst : Real.sqrt (design.weight firstAtom) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (design.weight_pos firstAtom))
  have hsqrtSecond : Real.sqrt (design.weight secondAtom) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (design.weight_pos secondAtom))
  by_cases hsecondCoeff : kernelVec secondAtom = 0
  · have hfirstCoeff : kernelVec firstAtom ≠ 0 := by
      intro hfirstZero
      apply hnonzero
      funext atomIndex
      by_cases hpairMem : atomIndex ∈ ({firstAtom, secondAtom} : Finset (Fin atoms))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hpairMem
        rcases hpairMem with rfl | rfl
        · exact hfirstZero
        · exact hsecondCoeff
      · exact hsupport atomIndex hpairMem
    have hfirstAtomZero : design.atom firstAtom = 0 := by
      have hlone : (kernelVec firstAtom * Real.sqrt (design.weight firstAtom))
          • design.atom firstAtom = 0 := by
        rw [hsecondCoeff, zero_mul, zero_smul, add_zero] at hcombination
        exact hcombination
      rcases smul_eq_zero.mp hlone with hcoeff | hatom
      · exact absurd hcoeff (mul_ne_zero hfirstCoeff hsqrtFirst)
      · exact hatom
    exact ⟨secondAtom, firstAtom, 0, hatomsNe.symm, by rw [hfirstAtomZero, zero_smul]⟩
  · refine ⟨firstAtom, secondAtom,
      -(kernelVec firstAtom * Real.sqrt (design.weight firstAtom))
        / (kernelVec secondAtom * Real.sqrt (design.weight secondAtom)),
      hatomsNe, ?_⟩
    have hsecondNe : kernelVec secondAtom * Real.sqrt (design.weight secondAtom) ≠ 0 :=
      mul_ne_zero hsecondCoeff hsqrtSecond
    have hisolate : (kernelVec secondAtom * Real.sqrt (design.weight secondAtom))
        • design.atom secondAtom
        = -((kernelVec firstAtom * Real.sqrt (design.weight firstAtom))
            • design.atom firstAtom) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hcombination
    funext coordIndex
    have hcoord := congrFun hisolate coordIndex
    simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at hcoord ⊢
    field_simp
    linarith [hcoord]

/-- **TWO NON-PROPORTIONAL DEPENDENCIES COMBINE TO A PAIR.**  Two chart kernel
vectors supported inside a listed triple of atoms, not proportional to one
another, cross-combine into a nonzero kernel vector supported on a pair of the
triple, and the pair-supported exit fires. -/
theorem hasParallelPair_of_two_kernel_vectors_in_triple
    {atoms rankValue : ℕ} (design : WeightedDesign atoms rankValue)
    {firstVec secondVec : Fin atoms → ℝ} {atomA atomB atomC : Fin atoms}
    (_hneAB : atomA ≠ atomB) (_hneAC : atomA ≠ atomC) (hneBC : atomB ≠ atomC)
    (hfirstKernel : projectionOfDesign design *ᵥ firstVec = 0)
    (hsecondKernel : projectionOfDesign design *ᵥ secondVec = 0)
    (hfirstSupport : ∀ atomIndex : Fin atoms,
      atomIndex ∉ ({atomA, atomB, atomC} : Finset (Fin atoms)) → firstVec atomIndex = 0)
    (hsecondSupport : ∀ atomIndex : Fin atoms,
      atomIndex ∉ ({atomA, atomB, atomC} : Finset (Fin atoms)) → secondVec atomIndex = 0)
    (hfirstAtomA : firstVec atomA ≠ 0)
    (hnotProportional : ∀ scale : ℝ, secondVec ≠ scale • firstVec) :
    HasParallelPair design := by
  classical
  set crossVec : Fin atoms → ℝ :=
    fun atomIndex => firstVec atomA * secondVec atomIndex
      - secondVec atomA * firstVec atomIndex with hcrossDef
  have hcrossKernel : projectionOfDesign design *ᵥ crossVec = 0 := by
    have hcrossEq : crossVec = firstVec atomA • secondVec
        - secondVec atomA • firstVec := by
      funext atomIndex
      simp [hcrossDef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcrossEq, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hfirstKernel, hsecondKernel, smul_zero, smul_zero, sub_zero]
  have hcrossAtomA : crossVec atomA = 0 := by
    simp [hcrossDef]
    ring
  have hcrossSupport : ∀ atomIndex : Fin atoms,
      atomIndex ∉ ({atomB, atomC} : Finset (Fin atoms)) → crossVec atomIndex = 0 := by
    intro atomIndex hnotPair
    by_cases hatomA : atomIndex = atomA
    · rw [hatomA]
      exact hcrossAtomA
    · have hnotTriple : atomIndex ∉ ({atomA, atomB, atomC} : Finset (Fin atoms)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hnotPair ⊢
        tauto
      simp [hcrossDef, hfirstSupport atomIndex hnotTriple,
        hsecondSupport atomIndex hnotTriple]
  have hcrossNonzero : crossVec ≠ 0 := by
    intro hcrossZero
    apply hnotProportional (secondVec atomA / firstVec atomA)
    funext atomIndex
    have hentry := congrFun hcrossZero atomIndex
    simp only [hcrossDef, Pi.zero_apply] at hentry
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith [hentry]
  exact hasParallelPair_of_pairSupported_dependency design hneBC
    (scaledAtomRows_transpose_mulVec_eq_zero_of_projection_mulVec_eq_zero design
      hcrossKernel)
    hcrossSupport hcrossNonzero

end Gtz

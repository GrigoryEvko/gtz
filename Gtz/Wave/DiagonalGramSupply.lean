import Gtz.Wave.CycleQuadKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The diagonal Gram supply — a basis-only positive set makes the Gram diagonal

When every label with a nonzero weight is a basis label, the Gram sum
collapses: each basis coefficient vector is a coordinate axis, and the
Gram core is the diagonal of the basis weights.  This supplies the
diagonal-Gram hypothesis of the corner kills whenever the reduced datum
has no positive label beyond the basis.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.coefficientGram_diagonal_of_positive_basis` — **THE SUPPLY.**

## Vacuity

Nothing here quantifies over a crux.  The statement holds at every
stationary datum with a chosen basis.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- **THE DIAGONAL GRAM SUPPLY.**  If every label with a nonzero weight is
a basis label, the Gram core is the diagonal of the basis weights. -/
theorem coefficientGram_diagonal_of_positive_basis
    (basisLabel : Fin basisCount → activeIndex)
    (hinjective : Function.Injective basisLabel)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hmemAll : ∀ columnIndex, basisLabel columnIndex ∈ activeSet)
    (honly : ∀ label ∈ activeSet, activeWeight label ≠ 0 →
      ∃ columnIndex, basisLabel columnIndex = label) :
    H = Matrix.diagonal
      (fun columnIndex => activeWeight (basisLabel columnIndex)) := by
  classical
  rw [coefficientGram_eq_sum_of_Hform basisLabel L hleft hHform]
  have himage : ∑ label ∈ activeSet,
      activeWeight label • atomMatrix (L *ᵥ tightDir label)
      = ∑ label ∈ Finset.univ.image basisLabel,
          activeWeight label • atomMatrix (L *ᵥ tightDir label) := by
    symm
    apply Finset.sum_subset
    · intro label hmem
      obtain ⟨columnIndex, -, rfl⟩ := Finset.mem_image.mp hmem
      exact hmemAll columnIndex
    · intro label hmem hnotMem
      have hzero : activeWeight label = 0 := by
        by_contra hnonzero
        obtain ⟨columnIndex, hcol⟩ := honly label hmem hnonzero
        exact hnotMem (Finset.mem_image.mpr ⟨columnIndex, Finset.mem_univ _, hcol⟩)
      rw [hzero, zero_smul]
  have hreindex : ∑ label ∈ Finset.univ.image basisLabel,
      activeWeight label • atomMatrix (L *ᵥ tightDir label)
      = ∑ columnIndex : Fin basisCount,
          activeWeight (basisLabel columnIndex)
            • atomMatrix (L *ᵥ tightDir (basisLabel columnIndex)) :=
    Finset.sum_image fun firstIndex _ secondIndex _ heq => hinjective heq
  rw [himage, hreindex]
  have haxis : ∀ columnIndex : Fin basisCount,
      atomMatrix (L *ᵥ tightDir (basisLabel columnIndex))
      = atomMatrix (Pi.single columnIndex 1) := by
    intro columnIndex
    rw [leftInverse_mulVec_tightDir_basisLabel basisLabel L hleft]
  refine Finset.sum_congr rfl (fun columnIndex _ => by rw [haxis]) |>.trans ?_
  ext rowIndex colIndex
  rw [Matrix.sum_apply]
  by_cases hcase : rowIndex = colIndex
  · subst hcase
    rw [Matrix.diagonal_apply_eq]
    rw [Finset.sum_eq_single rowIndex
      (fun columnIndex _ hne => by
        simp [atomMatrix, Matrix.vecMulVec_apply, Pi.single_eq_of_ne (Ne.symm hne)])
      (fun hnotMem => absurd (Finset.mem_univ _) hnotMem)]
    simp [atomMatrix, Matrix.vecMulVec_apply]
  · rw [Matrix.diagonal_apply_ne _ hcase]
    refine Finset.sum_eq_zero fun columnIndex _ => ?_
    by_cases hrow : columnIndex = rowIndex
    · subst hrow
      simp [atomMatrix, Matrix.vecMulVec_apply,
        Pi.single_eq_of_ne (fun hcontra => hcase hcontra.symm)]
    · simp [atomMatrix, Matrix.vecMulVec_apply,
        Pi.single_eq_of_ne (fun hcontra => hrow hcontra.symm)]

end Gtz

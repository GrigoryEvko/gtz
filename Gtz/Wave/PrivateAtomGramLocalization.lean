import Gtz.Wave.CoefficientProjectionWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Gram localization at a private atom

The Gram sum splits over the carriers of a private atom.  Every active
label whose block misses the private atom contributes nothing to the
private slot's Gram row: a positive label dies by the circuit kill, and a
zero-multiplier label dies outright.  Thus the private row of `H` reads
only the labels that carry the private atom.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.coefficientGram_entry_localized_of_private_atom` — **THE
  LOCALIZATION.**  The private Gram row is the carrier sum.

## Vacuity

Nothing here quantifies over a crux.  The statement holds at every
stationary datum with a chosen basis and left inverse.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- **THE LOCALIZATION.**  The private slot's Gram row reads only the
carriers of the private atom. -/
theorem coefficientGram_entry_localized_of_private_atom
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    {privateSlot : Fin basisCount} {privateAtom : Fin size}
    (hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) privateAtom = 0)
    (hslotNe : tightDir (basisLabel privateSlot) privateAtom ≠ 0)
    (colIndex : Fin basisCount) :
    H privateSlot colIndex
      = ∑ label ∈ activeSet.filter (fun label => privateAtom ∈ activeSubset label),
          activeWeight label * ((L *ᵥ tightDir label) privateSlot
            * (L *ᵥ tightDir label) colIndex) := by
  classical
  rw [coefficientGram_eq_sum_of_Hform basisLabel L hleft hHform, Matrix.sum_apply]
  simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [← Finset.sum_filter_add_sum_filter_not activeSet
    (fun label => privateAtom ∈ activeSubset label)
    (fun label => activeWeight label * ((L *ᵥ tightDir label) privateSlot
      * (L *ᵥ tightDir label) colIndex))]
  have hdead : ∑ label ∈ activeSet.filter
      (fun label => ¬ privateAtom ∈ activeSubset label),
      activeWeight label * ((L *ᵥ tightDir label) privateSlot
        * (L *ᵥ tightDir label) colIndex) = 0 := by
    refine Finset.sum_eq_zero fun label hmem => ?_
    obtain ⟨hactive, hnotMem⟩ := Finset.mem_filter.mp hmem
    by_cases hpos : 0 < activeWeight label
    · have hkill := coefficientReading_eq_zero_of_private_atom hdata basisLabel
        hbasisSpan L hleft hprivate hslotNe
        (mem_positiveActiveSet.mpr ⟨hactive, hpos⟩) hnotMem
      rw [hkill, zero_mul, mul_zero]
    · have hzero : activeWeight label = 0 :=
        le_antisymm (not_lt.mp hpos) (hdata.activeWeight_nonneg label hactive)
      rw [hzero, zero_mul]
  rw [hdead, add_zero]

end Gtz

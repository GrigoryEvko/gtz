import Gtz.Wave.PrivateAtomCaptureTightness

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The two-carrier dictionary — conjugated diagonals at a shared atom

The census gives atoms of multiplicity one and atoms of multiplicity two.
The private reading handles multiplicity one.  This file lands the
multiplicity-two reading: the ambient diagonal of a conjugated form at an
atom that only two basis columns carry collapses to the four entries of
the conjugating core on the two slots.  The two instantiations follow:
the Gram core reads the constant assembly diagonal, and the captured core
reads the forced diagonal.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.conjugated_diagonal_eq_of_two_carriers` — **THE DICTIONARY.**
* `Gtz.two_carrier_gram_eq_inv_size` — the Gram instantiation.
* `Gtz.two_carrier_capture_eq_forced_diagonal` — the capture
  instantiation.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every
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

/-- **THE TWO-CARRIER DICTIONARY.**  At an atom that only two basis columns
carry, the ambient diagonal of a conjugated form collapses to the four
core entries on the two slots. -/
theorem conjugated_diagonal_eq_of_two_carriers
    (basisLabel : Fin basisCount → activeIndex)
    {K : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    {X : Matrix (Fin size) (Fin size) ℝ}
    (hform : tightBasisColumns tightDir basisLabel * K
        * (tightBasisColumns tightDir basisLabel)ᵀ = X)
    {firstSlot secondSlot : Fin basisCount} (hne : firstSlot ≠ secondSlot)
    {sharedAtom : Fin size}
    (hcarriers : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) sharedAtom = 0) :
    X sharedAtom sharedAtom
      = (tightDir (basisLabel firstSlot) sharedAtom * K firstSlot firstSlot
          + tightDir (basisLabel secondSlot) sharedAtom * K secondSlot firstSlot)
          * tightDir (basisLabel firstSlot) sharedAtom
        + (tightDir (basisLabel firstSlot) sharedAtom * K firstSlot secondSlot
          + tightDir (basisLabel secondSlot) sharedAtom * K secondSlot secondSlot)
          * tightDir (basisLabel secondSlot) sharedAtom := by
  classical
  have hinner : ∀ colIndex : Fin basisCount,
      (tightBasisColumns tightDir basisLabel * K) sharedAtom colIndex
        = tightDir (basisLabel firstSlot) sharedAtom * K firstSlot colIndex
          + tightDir (basisLabel secondSlot) sharedAtom * K secondSlot colIndex := by
    intro colIndex
    rw [Matrix.mul_apply]
    have hrestrict : ∑ innerIndex,
        tightBasisColumns tightDir basisLabel sharedAtom innerIndex
          * K innerIndex colIndex
        = ∑ innerIndex ∈ ({firstSlot, secondSlot} : Finset (Fin basisCount)),
            tightBasisColumns tightDir basisLabel sharedAtom innerIndex
              * K innerIndex colIndex := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro innerIndex _ hnotMem
      have hfirst : innerIndex ≠ firstSlot := fun hcontra =>
        hnotMem (hcontra ▸ Finset.mem_insert_self _ _)
      have hsecond : innerIndex ≠ secondSlot := fun hcontra =>
        hnotMem (hcontra ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hzero : tightBasisColumns tightDir basisLabel sharedAtom innerIndex = 0 :=
        hcarriers innerIndex hfirst hsecond
      rw [hzero, zero_mul]
    rw [hrestrict, Finset.sum_pair hne]
    rfl
  rw [← hform, Matrix.mul_apply]
  have hrestrictOuter : ∑ colIndex,
      (tightBasisColumns tightDir basisLabel * K) sharedAtom colIndex
        * (tightBasisColumns tightDir basisLabel)ᵀ colIndex sharedAtom
      = ∑ colIndex ∈ ({firstSlot, secondSlot} : Finset (Fin basisCount)),
          (tightBasisColumns tightDir basisLabel * K) sharedAtom colIndex
            * (tightBasisColumns tightDir basisLabel)ᵀ colIndex sharedAtom := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro colIndex _ hnotMem
    have hfirst : colIndex ≠ firstSlot := fun hcontra =>
      hnotMem (hcontra ▸ Finset.mem_insert_self _ _)
    have hsecond : colIndex ≠ secondSlot := fun hcontra =>
      hnotMem (hcontra ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hzero : (tightBasisColumns tightDir basisLabel)ᵀ colIndex sharedAtom = 0 := by
      rw [Matrix.transpose_apply]
      exact hcarriers colIndex hfirst hsecond
    rw [hzero, mul_zero]
  rw [hrestrictOuter, Finset.sum_pair hne, hinner firstSlot, hinner secondSlot,
    Matrix.transpose_apply, Matrix.transpose_apply]
  rfl

/-- The Gram instantiation of the dictionary: at a two-carrier atom, the
four Gram entries on the two slots read the constant assembly diagonal. -/
theorem two_carrier_gram_eq_inv_size
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    {firstSlot secondSlot : Fin basisCount} (hne : firstSlot ≠ secondSlot)
    {sharedAtom : Fin size}
    (hcarriers : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) sharedAtom = 0) :
    (tightDir (basisLabel firstSlot) sharedAtom * H firstSlot firstSlot
        + tightDir (basisLabel secondSlot) sharedAtom * H secondSlot firstSlot)
        * tightDir (basisLabel firstSlot) sharedAtom
      + (tightDir (basisLabel firstSlot) sharedAtom * H firstSlot secondSlot
        + tightDir (basisLabel secondSlot) sharedAtom * H secondSlot secondSlot)
        * tightDir (basisLabel secondSlot) sharedAtom
      = ((size : ℝ))⁻¹ :=
  (conjugated_diagonal_eq_of_two_carriers basisLabel hHform hne hcarriers).symm.trans
    (hdata.assembly_diagonal sharedAtom)

/-- The capture instantiation of the dictionary: at a two-carrier atom, the
four captured entries on the two slots read the forced diagonal
`(value + weight) / size`. -/
theorem two_carrier_capture_eq_forced_diagonal
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    {firstSlot secondSlot : Fin basisCount} (hne : firstSlot ≠ secondSlot)
    {sharedAtom : Fin size}
    (hcarriers : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) sharedAtom = 0) :
    (tightDir (basisLabel firstSlot) sharedAtom * (M * H) firstSlot firstSlot
        + tightDir (basisLabel secondSlot) sharedAtom * (M * H) secondSlot firstSlot)
        * tightDir (basisLabel firstSlot) sharedAtom
      + (tightDir (basisLabel firstSlot) sharedAtom * (M * H) firstSlot secondSlot
        + tightDir (basisLabel secondSlot) sharedAtom * (M * H) secondSlot secondSlot)
        * tightDir (basisLabel secondSlot) sharedAtom
      = (value + weight sharedAtom) * ((size : ℝ))⁻¹ :=
  (conjugated_diagonal_eq_of_two_carriers basisLabel
      (capture_Hform basisLabel hrepresentation hHform) hne hcarriers).symm.trans
    (diagonal_projection_mul_multiplier_of_isChartStationaryData hdata sharedAtom)

end Gtz

import Gtz.Wave.CaptureSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The carried row reading — the pointwise coefficient law at a block atom

The representation `P B = B M` and the tight equation give one linear law
for each pair of a slot and an atom of its block: the basis coordinates at
the atom contract the coefficient column to the shifted weight times the
slot coordinate.  Every pin and every eigen relation of the pattern kills
is an instance of this law.  The two-carrier collapse turns the law into a
two-by-two eigen equation on the carrier pair.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.carried_row_reading` — **THE MASTER LAW.**
* `Gtz.two_carrier_row_reading` — the two-carrier collapse.

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

/-- **THE MASTER LAW.**  At an atom of a slot's block, the basis
coordinates contract the coefficient column to the shifted weight times
the slot coordinate. -/
theorem carried_row_reading
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {slotIndex : Fin basisCount} (hmem : basisLabel slotIndex ∈ activeSet)
    {atomIndex : Fin size}
    (hatomMem : atomIndex ∈ activeSubset (basisLabel slotIndex)) :
    ∑ columnIndex : Fin basisCount,
        tightDir (basisLabel columnIndex) atomIndex * M columnIndex slotIndex
      = (value + weight atomIndex) * tightDir (basisLabel slotIndex) atomIndex := by
  have hentry : ∑ columnIndex : Fin basisCount,
      tightDir (basisLabel columnIndex) atomIndex * M columnIndex slotIndex
      = (tightBasisColumns tightDir basisLabel * M) atomIndex slotIndex := by
    rw [Matrix.mul_apply]
    rfl
  have hcolumnEntry : (projection * tightBasisColumns tightDir basisLabel)
      atomIndex slotIndex
      = (projection *ᵥ tightDir (basisLabel slotIndex)) atomIndex := by
    rw [Matrix.mul_apply]
    rfl
  rw [hentry, ← hrepresentation, hcolumnEntry,
    projection_mulVec_tightDir_of_mem hdata hmem hatomMem]

/-- **THE TWO-CARRIER COLLAPSE.**  If only two basis columns carry the
atom, the master law collapses to the carrier pair. -/
theorem two_carrier_row_reading
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {firstSlot secondSlot readSlot : Fin basisCount}
    (hne : firstSlot ≠ secondSlot)
    (hmem : basisLabel readSlot ∈ activeSet)
    {atomIndex : Fin size}
    (hatomMem : atomIndex ∈ activeSubset (basisLabel readSlot))
    (hcarriers : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) atomIndex = 0) :
    tightDir (basisLabel firstSlot) atomIndex * M firstSlot readSlot
        + tightDir (basisLabel secondSlot) atomIndex * M secondSlot readSlot
      = (value + weight atomIndex) * tightDir (basisLabel readSlot) atomIndex := by
  classical
  have hmaster := carried_row_reading hdata basisLabel hrepresentation hmem hatomMem
  have hpair : ∑ columnIndex : Fin basisCount,
      tightDir (basisLabel columnIndex) atomIndex * M columnIndex readSlot
      = ∑ columnIndex ∈ ({firstSlot, secondSlot} : Finset (Fin basisCount)),
          tightDir (basisLabel columnIndex) atomIndex * M columnIndex readSlot := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro columnIndex _ hnotMem
    have hfirst : columnIndex ≠ firstSlot := fun hcontra =>
      hnotMem (hcontra ▸ Finset.mem_insert_self _ _)
    have hsecond : columnIndex ≠ secondSlot := fun hcontra =>
      hnotMem (hcontra ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hcarriers columnIndex hfirst hsecond, zero_mul]
  rw [hpair, Finset.sum_pair hne] at hmaster
  exact hmaster

end Gtz

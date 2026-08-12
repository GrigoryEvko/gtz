import Gtz.Wave.AllPrivateSlotsKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The private slot extraction — from the census clause to the pin

The census hands branch two a multiplicity-one atom.  The pin and the
circuit kill consume a private SLOT: the unique basis column whose
direction is nonzero at the atom, with the atom inside its block.  This
file extracts the slot from the multiplicity clause.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.exists_private_slot_of_multiplicity_one` — **THE EXTRACTION.**

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

/-- **THE EXTRACTION.**  A multiplicity-one atom yields its private slot:
the atom sits in the slot's block, the slot's direction is nonzero there,
and every other basis direction vanishes there. -/
theorem exists_private_slot_of_multiplicity_one
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hmem : ∀ columnIndex, basisLabel columnIndex ∈ activeSet)
    {atomIndex : Fin size}
    (hmult : basisSupportMultiplicity tightDir basisLabel atomIndex = 1) :
    ∃ privateSlot : Fin basisCount,
      atomIndex ∈ activeSubset (basisLabel privateSlot)
        ∧ tightDir (basisLabel privateSlot) atomIndex ≠ 0
        ∧ ∀ columnIndex, columnIndex ≠ privateSlot →
            tightDir (basisLabel columnIndex) atomIndex = 0 := by
  classical
  rw [basisSupportMultiplicity] at hmult
  obtain ⟨privateSlot, hfilter⟩ := Finset.card_eq_one.mp hmult
  have hslotMem : privateSlot ∈ Finset.univ.filter (fun columnIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex)) := by
    rw [hfilter]
    exact Finset.mem_singleton_self _
  have hslotSupport := (Finset.mem_filter.mp hslotMem).2
  refine ⟨privateSlot, ?_, mem_datumTightSupport.mp hslotSupport, ?_⟩
  · exact datumTightSupport_subset hdata (hmem privateSlot) hslotSupport
  · intro columnIndex hne
    by_contra hnonzero
    have hcolMem : columnIndex ∈ Finset.univ.filter (fun innerIndex =>
        atomIndex ∈ datumTightSupport tightDir (basisLabel innerIndex)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_datumTightSupport.mpr hnonzero⟩
    rw [hfilter, Finset.mem_singleton] at hcolMem
    exact hne hcolMem

end Gtz

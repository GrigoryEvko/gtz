import Gtz.Wave.TriplePairSectorKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The carrier-pair extraction — from multiplicity two to the dense pair

The census hands the dense branch atoms of multiplicity two.  The corner
kills consume a carrier PAIR: two distinct slots dense at the atom, with
every other basis column vanishing there.  This file extracts the pair
from the multiplicity clause.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.exists_carrier_pair_of_multiplicity_two` — **THE EXTRACTION.**

## Vacuity

The statement is unconditional.
-/

namespace Gtz

variable {size : ℕ} {activeIndex : Type*}
variable {tightDir : activeIndex → (Fin size → ℝ)} {basisCount : ℕ}

/-- **THE EXTRACTION.**  A multiplicity-two atom yields its dense carrier
pair: two distinct slots with nonzero coordinates, and every other basis
column vanishes at the atom. -/
theorem exists_carrier_pair_of_multiplicity_two
    (basisLabel : Fin basisCount → activeIndex) {atomIndex : Fin size}
    (hmult : basisSupportMultiplicity tightDir basisLabel atomIndex = 2) :
    ∃ firstSlot secondSlot : Fin basisCount, firstSlot ≠ secondSlot
      ∧ tightDir (basisLabel firstSlot) atomIndex ≠ 0
      ∧ tightDir (basisLabel secondSlot) atomIndex ≠ 0
      ∧ ∀ columnIndex, columnIndex ≠ firstSlot → columnIndex ≠ secondSlot →
          tightDir (basisLabel columnIndex) atomIndex = 0 := by
  classical
  rw [basisSupportMultiplicity] at hmult
  obtain ⟨firstSlot, secondSlot, hne, hfilter⟩ := Finset.card_eq_two.mp hmult
  have hfirstMem : firstSlot ∈ Finset.univ.filter (fun columnIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex)) := by
    rw [hfilter]
    exact Finset.mem_insert_self _ _
  have hsecondMem : secondSlot ∈ Finset.univ.filter (fun columnIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex)) := by
    rw [hfilter]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  refine ⟨firstSlot, secondSlot, hne,
    mem_datumTightSupport.mp (Finset.mem_filter.mp hfirstMem).2,
    mem_datumTightSupport.mp (Finset.mem_filter.mp hsecondMem).2, ?_⟩
  intro columnIndex hneFirst hneSecond
  by_contra hnonzero
  have hcolMem : columnIndex ∈ Finset.univ.filter (fun innerIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel innerIndex)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_datumTightSupport.mpr hnonzero⟩
  rw [hfilter, Finset.mem_insert, Finset.mem_singleton] at hcolMem
  rcases hcolMem with h | h
  · exact hneFirst h
  · exact hneSecond h

end Gtz

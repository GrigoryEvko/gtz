import Gtz.Wave.AllPrivateSupportKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The private-support split — full privacy or a shared atom

Branch two of the census gives one multiplicity-one atom on a slot.  The
slot's support then splits: either every support atom has multiplicity
one (the all-private-support kill closes this side), or some support atom
sits in at least two basis supports.  The split is the router of the
branch-two closure.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.all_private_or_exists_shared_atom` — **THE SPLIT.**

## Vacuity

The statement is unconditional.
-/

namespace Gtz

variable {size : ℕ} {activeIndex : Type*}
variable {tightDir : activeIndex → (Fin size → ℝ)} {basisCount : ℕ}

/-- **THE PRIVATE-SUPPORT SPLIT.**  Every slot's support is fully
multiplicity-one, or it carries an atom in at least two basis supports.
A support atom always has multiplicity at least one, because its own slot
carries it. -/
theorem all_private_or_exists_shared_atom
    (basisLabel : Fin basisCount → activeIndex) (privateSlot : Fin basisCount) :
    (∀ atomIndex ∈ datumTightSupport tightDir (basisLabel privateSlot),
        basisSupportMultiplicity tightDir basisLabel atomIndex = 1)
      ∨ ∃ atomIndex ∈ datumTightSupport tightDir (basisLabel privateSlot),
          2 ≤ basisSupportMultiplicity tightDir basisLabel atomIndex := by
  classical
  by_cases hall : ∀ atomIndex ∈ datumTightSupport tightDir (basisLabel privateSlot),
      basisSupportMultiplicity tightDir basisLabel atomIndex = 1
  · exact Or.inl hall
  push Not at hall
  obtain ⟨atomIndex, hmem, hne⟩ := hall
  have hpos : 0 < basisSupportMultiplicity tightDir basisLabel atomIndex := by
    rw [basisSupportMultiplicity, Finset.card_pos]
    exact ⟨privateSlot, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩⟩
  exact Or.inr ⟨atomIndex, hmem, by omega⟩

end Gtz

import Gtz.Wave.SharedPrivateCornerDefect
import Gtz.Wave.CaptureLinePairKill

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

/-!
# The leak budget — the stationary leak law on the shared-private lattice

The stationary leak law prices the multiplier-weighted squared leaks at
every atom: their total is exactly `d (1 - d) / 6`, with `d` the
captured diagonal.  This module reads that law at a shared-private
datum, keeps the basis family's part, and collapses the pin instance.

## The consumable forms

Every basis label carries a positive multiplier, thus the law caps each
basis leak and the whole basis family at every atom.  Through the
coefficient representation the basis leak at an atom is the coefficient
combination of the basis values minus the captured read.  Thus the cap
is a COEFFICIENT inequality: the first pointwise bound that ties the
off-diagonal coefficient entries to the captured diagonals.

At the pin atom only the pinned slot is live, thus the leak of a basis
slot collapses to one product: the pinned value times one entry of the
pinned coefficient row.  The whole pinned row away from the diagonal is
then priced by `d (1 - d) / 6` at the pin.  The level-two feasibility
probe of this session shows that the counted identical residue at basis
count five and six needs exactly this mixture layer: the slot and
coefficient machinery alone admits exact stationary relaxation points.

## Vacuity

The statements quantify over shared-private data, and no shared-private
datum exists if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-! ## Layer 1 — the datum leak law -/

/-- **THE DATUM LEAK LAW.**  The multiplier-weighted squared leaks of a
shared-private datum total `d (1 - d) / 6` at every atom. -/
theorem leak_sq_sum (data : SharedPrivateData crux) (atomIndex : Fin 6) :
    ∑ label ∈ data.activeSet, data.reducedWeight label
        * (((chartPointOfDesign crux.design).chart *ᵥ data.tightDir label) atomIndex
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomIndex)
            * data.tightDir label atomIndex) ^ 2
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)) / 6 := by
  have hlaw := stationary_leak_sq_sum data.hdata atomIndex
  rw [hlaw]
  push_cast
  ring

/-- Every leak term of the law is nonnegative. -/
theorem leak_term_nonneg (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet) (atomIndex : Fin 6) :
    0 ≤ data.reducedWeight label
        * (((chartPointOfDesign crux.design).chart *ᵥ data.tightDir label) atomIndex
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomIndex)
            * data.tightDir label atomIndex) ^ 2 :=
  mul_nonneg (data.hdata.activeWeight_nonneg label hmem) (sq_nonneg _)

/-! ## Layer 2 — the basis family part of the law -/

/-- **THE BASIS FAMILY LEAK CAP.**  The basis labels are distinct members
of the active family, thus their weighted squared leaks stay below the
full budget at every atom. -/
theorem basis_family_leak_sq_le (data : SharedPrivateData crux) (atomIndex : Fin 6) :
    ∑ slot : Fin data.basisCount, data.reducedWeight (data.basisLabel slot)
        * (((chartPointOfDesign crux.design).chart
              *ᵥ data.tightDir (data.basisLabel slot)) atomIndex
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomIndex)
            * data.tightDir (data.basisLabel slot) atomIndex) ^ 2
      ≤ (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)) / 6 := by
  classical
  rw [← data.leak_sq_sum atomIndex]
  have himage : ∑ label ∈ Finset.image data.basisLabel Finset.univ,
      data.reducedWeight label
        * (((chartPointOfDesign crux.design).chart
              *ᵥ data.tightDir label) atomIndex
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomIndex)
            * data.tightDir label atomIndex) ^ 2
      = ∑ slot : Fin data.basisCount,
          data.reducedWeight (data.basisLabel slot)
            * (((chartPointOfDesign crux.design).chart
                  *ᵥ data.tightDir (data.basisLabel slot)) atomIndex
              - (chartObjective (chartPointOfDesign crux.design)
                  + (chartPointOfDesign crux.design).weight atomIndex)
                * data.tightDir (data.basisLabel slot) atomIndex) ^ 2 :=
    Finset.sum_image fun slotOne _ slotTwo _ hsame => data.hinjective hsame
  rw [← himage]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    fun label hmem _ => data.leak_term_nonneg hmem atomIndex
  intro label hmem
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp hmem
  exact data.basisLabel_mem_activeSet slot

/-- **THE SINGLE BASIS LEAK CAP.** -/
theorem basis_leak_sq_le (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) (atomIndex : Fin 6) :
    data.reducedWeight (data.basisLabel slot)
        * (((chartPointOfDesign crux.design).chart
              *ᵥ data.tightDir (data.basisLabel slot)) atomIndex
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomIndex)
            * data.tightDir (data.basisLabel slot) atomIndex) ^ 2
      ≤ (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)) / 6 := by
  rw [← data.leak_sq_sum atomIndex]
  exact Finset.single_le_sum
    (fun label hmem => data.leak_term_nonneg hmem atomIndex)
    (data.basisLabel_mem_activeSet slot)

/-! ## Layer 3 — the coefficient form of the basis leak -/

/-- The captured image of a basis column at any atom is the coefficient
combination of the basis values.  This is one entry of the coefficient
representation, at every atom of every column. -/
theorem chart_mulVec_basis_eq_coeff_sum (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) (atomIndex : Fin 6) :
    ((chartPointOfDesign crux.design).chart
        *ᵥ data.tightDir (data.basisLabel slot)) atomIndex
      = ∑ other : Fin data.basisCount,
          data.tightDir (data.basisLabel other) atomIndex * data.coeff other slot := by
  have hentry := congrFun (congrFun data.hrepresentation atomIndex) slot
  simp only [Matrix.mul_apply, tightBasisColumns] at hentry
  simp only [Matrix.mulVec, dotProduct]
  exact hentry

/-- **THE COEFFICIENT LEAK CAP.**  The pointwise inequality that ties the
coefficient entries to the captured diagonals: at every atom, the
weighted squared coefficient leak of a basis slot is at most
`d (1 - d) / 6`. -/
theorem coeffRow_leak_sq_le (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) (atomIndex : Fin 6) :
    data.reducedWeight (data.basisLabel slot)
        * ((∑ other : Fin data.basisCount,
              data.tightDir (data.basisLabel other) atomIndex
                * data.coeff other slot)
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomIndex)
            * data.tightDir (data.basisLabel slot) atomIndex) ^ 2
      ≤ (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)) / 6 := by
  have hcap := data.basis_leak_sq_le slot atomIndex
  rwa [data.chart_mulVec_basis_eq_coeff_sum slot atomIndex] at hcap

/-! ## Layer 4 — the pinned row budget -/

/-- The coefficient leak of a foreign slot at the pin atom is one
product: the pinned value times one pinned-row coefficient entry. -/
theorem coeff_sum_pinAtom_collapse (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) :
    ∑ other : Fin data.basisCount,
        data.tightDir (data.basisLabel other) data.pinAtom * data.coeff other slot
      = data.tightDir (data.basisLabel data.privateSlot) data.pinAtom
        * data.coeff data.privateSlot slot := by
  classical
  refine Finset.sum_eq_single data.privateSlot
    (fun other _ hother => by rw [data.hprivate other hother, zero_mul])
    (fun habs => absurd (Finset.mem_univ _) habs)

/-- **THE PINNED ROW BUDGET.**  At the pin atom every foreign basis slot
leaks exactly through the pinned coefficient row, thus each entry of
that row pays the leak budget of the pin: `w (v c)² ≤ d (1 - d) / 6`.
This is the first sign-carrying bound on the off-diagonal coefficient
entries of the pinned slot, and the mixture layer that the basis-count
five and six identical residues need enters exactly here. -/
theorem pinRow_coeff_sq_le (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} (hne : slot ≠ data.privateSlot) :
    data.reducedWeight (data.basisLabel slot)
        * (data.tightDir (data.basisLabel data.privateSlot) data.pinAtom
            * data.coeff data.privateSlot slot) ^ 2
      ≤ (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight data.pinAtom)
        * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight data.pinAtom)) / 6 := by
  have hcap := data.coeffRow_leak_sq_le slot data.pinAtom
  rw [data.coeff_sum_pinAtom_collapse slot] at hcap
  have hdead : data.tightDir (data.basisLabel slot) data.pinAtom = 0 :=
    data.hprivate slot hne
  rw [hdead, mul_zero, sub_zero] at hcap
  exact hcap

/-- **THE PINNED ROW FAMILY BUDGET.**  The whole pinned coefficient row
away from the diagonal, weighted by the basis multipliers and scaled by
the squared pinned value, stays below the pin budget. -/
theorem pinRow_family_sq_le (data : SharedPrivateData crux) :
    ∑ slot ∈ Finset.univ.erase data.privateSlot,
        data.reducedWeight (data.basisLabel slot)
          * (data.tightDir (data.basisLabel data.privateSlot) data.pinAtom
              * data.coeff data.privateSlot slot) ^ 2
      ≤ (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight data.pinAtom)
        * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight data.pinAtom)) / 6 := by
  classical
  have hfamily := data.basis_family_leak_sq_le data.pinAtom
  have hterm : ∀ slot ∈ Finset.univ.erase data.privateSlot,
      data.reducedWeight (data.basisLabel slot)
        * (data.tightDir (data.basisLabel data.privateSlot) data.pinAtom
            * data.coeff data.privateSlot slot) ^ 2
      = data.reducedWeight (data.basisLabel slot)
        * (((chartPointOfDesign crux.design).chart
              *ᵥ data.tightDir (data.basisLabel slot)) data.pinAtom
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight data.pinAtom)
            * data.tightDir (data.basisLabel slot) data.pinAtom) ^ 2 := by
    intro slot hslot
    have hne : slot ≠ data.privateSlot := (Finset.mem_erase.mp hslot).1
    rw [data.chart_mulVec_basis_eq_coeff_sum slot data.pinAtom,
      data.coeff_sum_pinAtom_collapse slot, data.hprivate slot hne, mul_zero,
      sub_zero]
  rw [Finset.sum_congr rfl hterm]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.erase_subset _ _) fun slot _ _ => ?_) hfamily
  exact mul_nonneg
    (data.hdata.activeWeight_nonneg _ (data.basisLabel_mem_activeSet slot))
    (sq_nonneg _)

end SharedPrivateData

end Gtz

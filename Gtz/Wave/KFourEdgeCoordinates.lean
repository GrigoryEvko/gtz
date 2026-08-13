import Gtz.Wave.GramExchangeLayer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The K4 edge coordinates — the polynomial frame of the tetrahedral kill

The labeled K4 pattern puts one shared atom on each pair of basis slots.
Each atom carries exactly two slots, thus each carried row collapses to
the two-carrier form, and each Gram entry collapses to one product of
two coordinates at the shared edge.  The exchange symmetry of the Gram
layer then reads as four-term polynomial equations in the edge
coordinates.  The eventual K4 certificate combines exactly these laws.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.not_mem_support_of_multiplicity_two` — the third-slot exclusion.
* `Gtz.tightDir_vanish_of_multiplicity_two` — the off-carrier vanish.
* `Gtz.edge_ne_of_third_slot` — the distinctness of the edge atoms.
* `Gtz.kfour_corner_read_first`, `Gtz.kfour_corner_read_second` — **THE
  CORNER READS** at a share singleton.
* `Gtz.kfour_gram_offdiag` — the Gram entry at a share singleton.
* `Gtz.kfour_unit_norm_expand` — the unit norm in edge coordinates.
* `Gtz.matrix_mul_apply_four`, `Gtz.kfour_exchange_symm_four` — the
  four-term entry expansions of the exchange symmetry.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every
stationary datum with a chosen basis and the stated share structure.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the multiplicity-two combinatorics

Each atom of the K4 pattern is in exactly two basis supports.  Thus a
third slot cannot carry the atom, the off-carrier coordinates vanish,
and two edge atoms with a separated slot pair are distinct. -/

/-- **THE THIRD-SLOT EXCLUSION.**  When an atom is in two basis
supports and the multiplicity is two, the atom is in no third support. -/
theorem not_mem_support_of_multiplicity_two
    (basisLabel : Fin basisCount → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {atomIndex : Fin size} {slotA slotB slotC : Fin basisCount}
    (hAB : slotA ≠ slotB) (hAC : slotA ≠ slotC) (hBC : slotB ≠ slotC)
    (hmemA : atomIndex ∈ datumTightSupport tightDir (basisLabel slotA))
    (hmemB : atomIndex ∈ datumTightSupport tightDir (basisLabel slotB)) :
    atomIndex ∉ datumTightSupport tightDir (basisLabel slotC) := by
  intro hmemC
  have hsubset : ({slotA, slotB, slotC} : Finset (Fin basisCount))
      ⊆ Finset.univ.filter fun columnIndex =>
          atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex) := by
    intro slot hslot
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hslot with hA | hslot
    · exact hA ▸ hmemA
    rcases Finset.mem_insert.mp hslot with hB | hslot
    · exact hB ▸ hmemB
    · exact (Finset.mem_singleton.mp hslot) ▸ hmemC
  have hthree : ({slotA, slotB, slotC} : Finset (Fin basisCount)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Finset.mem_insert,
        Finset.mem_singleton, hAB, hAC]),
      Finset.card_insert_of_notMem (by simp [Finset.mem_singleton, hBC]),
      Finset.card_singleton]
  have hbound : (3 : ℕ) ≤ basisSupportMultiplicity tightDir basisLabel atomIndex := by
    rw [basisSupportMultiplicity, ← hthree]
    exact Finset.card_le_card hsubset
  rw [hmult atomIndex] at hbound
  omega

/-- **THE OFF-CARRIER VANISH.**  When an atom is in two basis supports
and the multiplicity is two, the coordinate of a third slot at the atom
is zero. -/
theorem tightDir_vanish_of_multiplicity_two
    (basisLabel : Fin basisCount → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {atomIndex : Fin size} {slotA slotB slotC : Fin basisCount}
    (hAB : slotA ≠ slotB) (hAC : slotA ≠ slotC) (hBC : slotB ≠ slotC)
    (hmemA : atomIndex ∈ datumTightSupport tightDir (basisLabel slotA))
    (hmemB : atomIndex ∈ datumTightSupport tightDir (basisLabel slotB)) :
    tightDir (basisLabel slotC) atomIndex = 0 := by
  by_contra hne
  exact not_mem_support_of_multiplicity_two basisLabel hmult hAB hAC hBC
    hmemA hmemB (mem_datumTightSupport.mpr hne)

/-- **THE EDGE DISTINCTNESS.**  Two edge atoms are distinct when the
second one is in a support that is not one of the first one's two
carriers. -/
theorem edge_ne_of_third_slot
    (basisLabel : Fin basisCount → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {edgeA edgeB : Fin size} {slotA slotB slotC : Fin basisCount}
    (hAB : slotA ≠ slotB) (hAC : slotA ≠ slotC) (hBC : slotB ≠ slotC)
    (hmemA : edgeA ∈ datumTightSupport tightDir (basisLabel slotA))
    (hmemB : edgeA ∈ datumTightSupport tightDir (basisLabel slotB))
    (hmemC : edgeB ∈ datumTightSupport tightDir (basisLabel slotC)) :
    edgeA ≠ edgeB := by
  intro heq
  exact not_mem_support_of_multiplicity_two basisLabel hmult hAB hAC hBC
    hmemA hmemB (heq ▸ hmemC)

/-! ## Layer 2 — the share singleton vocabulary

The labeled bridge gives each slot pair one shared atom.  The singleton
equation gives the two memberships, and it kills every product of the
two coordinates away from the shared atom. -/

/-- The shared atom is in the first support. -/
theorem shareSet_singleton_mem_left
    (basisLabel : Fin basisCount → activeIndex)
    {slotI slotJ : Fin basisCount} {edge : Fin size}
    (hshare : shareSet tightDir basisLabel slotI slotJ = {edge}) :
    edge ∈ datumTightSupport tightDir (basisLabel slotI) := by
  have hmem : edge ∈ shareSet tightDir basisLabel slotI slotJ := by
    rw [hshare]
    exact Finset.mem_singleton_self _
  exact ((Finset.mem_filter.mp hmem).2).1

/-- The shared atom is in the second support. -/
theorem shareSet_singleton_mem_right
    (basisLabel : Fin basisCount → activeIndex)
    {slotI slotJ : Fin basisCount} {edge : Fin size}
    (hshare : shareSet tightDir basisLabel slotI slotJ = {edge}) :
    edge ∈ datumTightSupport tightDir (basisLabel slotJ) := by
  have hmem : edge ∈ shareSet tightDir basisLabel slotI slotJ := by
    rw [hshare]
    exact Finset.mem_singleton_self _
  exact ((Finset.mem_filter.mp hmem).2).2

/-- Away from the shared atom, the product of the two slot coordinates
is zero. -/
theorem coordinate_product_vanish_of_shareSet_singleton
    (basisLabel : Fin basisCount → activeIndex)
    {slotI slotJ : Fin basisCount} {edge : Fin size}
    (hshare : shareSet tightDir basisLabel slotI slotJ = {edge})
    {atomIndex : Fin size} (hne : atomIndex ≠ edge) :
    tightDir (basisLabel slotI) atomIndex
      * tightDir (basisLabel slotJ) atomIndex = 0 := by
  have hnotShare : atomIndex ∉ shareSet tightDir basisLabel slotI slotJ := by
    rw [hshare]
    exact fun hmem => hne (Finset.mem_singleton.mp hmem)
  by_cases hmemI : atomIndex ∈ datumTightSupport tightDir (basisLabel slotI)
  · have hzero : tightDir (basisLabel slotJ) atomIndex = 0 := by
      by_contra hne'
      exact hnotShare (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hmemI, mem_datumTightSupport.mpr hne'⟩)
    rw [hzero, mul_zero]
  · have hzero : tightDir (basisLabel slotI) atomIndex = 0 := by
      by_contra hne'
      exact hmemI (mem_datumTightSupport.mpr hne')
    rw [hzero, zero_mul]

/-! ## Layer 3 — the corner reads

At a share singleton with multiplicity two, the carried row collapses
to the two carriers.  The two reads give the four corner entries of the
coefficient matrix on the slot pair. -/

/-- **THE FIRST CORNER READ.**  The two-carrier row at the shared atom,
read at the first slot. -/
theorem kfour_corner_read_first
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {slotI slotJ : Fin basisCount} (hne : slotI ≠ slotJ)
    (hmemI : basisLabel slotI ∈ activeSet)
    {edge : Fin size}
    (hshare : shareSet tightDir basisLabel slotI slotJ = {edge}) :
    tightDir (basisLabel slotI) edge * M slotI slotI
        + tightDir (basisLabel slotJ) edge * M slotJ slotI
      = (value + weight edge) * tightDir (basisLabel slotI) edge := by
  have hmemSuppI := shareSet_singleton_mem_left basisLabel hshare
  have hmemSuppJ := shareSet_singleton_mem_right basisLabel hshare
  refine two_carrier_row_reading hdata basisLabel hrepresentation hne hmemI
    (datumTightSupport_subset hdata hmemI hmemSuppI) ?_
  intro slotK hneI hneJ
  exact tightDir_vanish_of_multiplicity_two basisLabel hmult hne
    (Ne.symm hneI) (Ne.symm hneJ) hmemSuppI hmemSuppJ

/-- **THE SECOND CORNER READ.**  The two-carrier row at the shared
atom, read at the second slot. -/
theorem kfour_corner_read_second
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {slotI slotJ : Fin basisCount} (hne : slotI ≠ slotJ)
    (hmemJ : basisLabel slotJ ∈ activeSet)
    {edge : Fin size}
    (hshare : shareSet tightDir basisLabel slotI slotJ = {edge}) :
    tightDir (basisLabel slotI) edge * M slotI slotJ
        + tightDir (basisLabel slotJ) edge * M slotJ slotJ
      = (value + weight edge) * tightDir (basisLabel slotJ) edge := by
  have hmemSuppI := shareSet_singleton_mem_left basisLabel hshare
  have hmemSuppJ := shareSet_singleton_mem_right basisLabel hshare
  refine two_carrier_row_reading hdata basisLabel hrepresentation hne hmemJ
    (datumTightSupport_subset hdata hmemJ hmemSuppJ) ?_
  intro slotK hneI hneJ
  exact tightDir_vanish_of_multiplicity_two basisLabel hmult hne
    (Ne.symm hneI) (Ne.symm hneJ) hmemSuppI hmemSuppJ

/-! ## Layer 4 — the Gram entries in edge coordinates

The Gram entry of a slot pair collapses to the coordinate product at
the shared atom.  The unit norm of a slot expands over its three star
edges. -/

/-- **THE GRAM EDGE ENTRY.**  The Gram entry of a slot pair is the
coordinate product at the shared atom. -/
theorem kfour_gram_offdiag (basisLabel : Fin basisCount → activeIndex)
    {slotI slotJ : Fin basisCount} {edge : Fin size}
    (hshare : shareSet tightDir basisLabel slotI slotJ = {edge}) :
    basisGram tightDir basisLabel slotI slotJ
      = tightDir (basisLabel slotI) edge * tightDir (basisLabel slotJ) edge := by
  rw [basisGram_apply_sum]
  apply Finset.sum_eq_single_of_mem edge (Finset.mem_univ edge)
  intro atomIndex _ hne
  exact coordinate_product_vanish_of_shareSet_singleton basisLabel hshare hne

/-- **THE UNIT NORM IN EDGE COORDINATES.**  When the support of a slot
is three distinct atoms, the unit norm is the three-term square sum. -/
theorem kfour_unit_norm_expand
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {slotIndex : Fin basisCount} (hmem : basisLabel slotIndex ∈ activeSet)
    {edgeA edgeB edgeC : Fin size}
    (hsupport : datumTightSupport tightDir (basisLabel slotIndex)
      = {edgeA, edgeB, edgeC})
    (hneAB : edgeA ≠ edgeB) (hneAC : edgeA ≠ edgeC) (hneBC : edgeB ≠ edgeC) :
    tightDir (basisLabel slotIndex) edgeA ^ 2
        + tightDir (basisLabel slotIndex) edgeB ^ 2
        + tightDir (basisLabel slotIndex) edgeC ^ 2 = 1 := by
  have hunit := hdata.tightDir_unit (basisLabel slotIndex) hmem
  have hsum : tightDir (basisLabel slotIndex) ⬝ᵥ tightDir (basisLabel slotIndex)
      = ∑ atomIndex ∈ ({edgeA, edgeB, edgeC} : Finset (Fin size)),
          tightDir (basisLabel slotIndex) atomIndex
            * tightDir (basisLabel slotIndex) atomIndex := by
    rw [dotProduct]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnotMem
    have hzero : tightDir (basisLabel slotIndex) atomIndex = 0 := by
      by_contra hne
      exact hnotMem (hsupport ▸ mem_datumTightSupport.mpr hne)
    rw [hzero, zero_mul]
  rw [hsum] at hunit
  rw [Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton,
      hneAB, hneAC]),
    Finset.sum_insert (by simp [Finset.mem_singleton, hneBC]),
    Finset.sum_singleton] at hunit
  calc tightDir (basisLabel slotIndex) edgeA ^ 2
        + tightDir (basisLabel slotIndex) edgeB ^ 2
        + tightDir (basisLabel slotIndex) edgeC ^ 2
      = tightDir (basisLabel slotIndex) edgeA
            * tightDir (basisLabel slotIndex) edgeA
          + (tightDir (basisLabel slotIndex) edgeB
            * tightDir (basisLabel slotIndex) edgeB
          + tightDir (basisLabel slotIndex) edgeC
            * tightDir (basisLabel slotIndex) edgeC) := by ring
    _ = 1 := hunit

/-! ## Layer 5 — the four-term entry expansions

The exchange symmetry of the Gram layer, expanded on four slots.  Each
instance is one polynomial equation of the certificate system. -/

/-- The entry of a four-by-four product, expanded. -/
theorem matrix_mul_apply_four (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (rowIndex colIndex : Fin 4) :
    (A * B) rowIndex colIndex
      = A rowIndex 0 * B 0 colIndex + A rowIndex 1 * B 1 colIndex
        + A rowIndex 2 * B 2 colIndex + A rowIndex 3 * B 3 colIndex := by
  rw [Matrix.mul_apply, Fin.sum_univ_four]

/-- **THE EXPANDED EXCHANGE SYMMETRY.**  The four-term polynomial form
of the second exchange law at a slot pair. -/
theorem kfour_exchange_symm_four
    (basisLabel : Fin 4 → activeIndex)
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (rowSlot colSlot : Fin 4) :
    basisGram tightDir basisLabel rowSlot 0 * M 0 colSlot
        + basisGram tightDir basisLabel rowSlot 1 * M 1 colSlot
        + basisGram tightDir basisLabel rowSlot 2 * M 2 colSlot
        + basisGram tightDir basisLabel rowSlot 3 * M 3 colSlot
      = basisGram tightDir basisLabel colSlot 0 * M 0 rowSlot
        + basisGram tightDir basisLabel colSlot 1 * M 1 rowSlot
        + basisGram tightDir basisLabel colSlot 2 * M 2 rowSlot
        + basisGram tightDir basisLabel colSlot 3 * M 3 rowSlot := by
  have hsymm :=
    gram_exchange_apply_symm basisLabel hsym hidem hrepresentation rowSlot colSlot
  rwa [matrix_mul_apply_four, matrix_mul_apply_four] at hsymm

/-- **THE EXPANDED DIAGONAL READ.**  The four-term polynomial form of
the exchange diagonal read at a slot. -/
theorem kfour_diag_read_four
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin 4 → activeIndex)
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {slotIndex : Fin 4} (hmem : basisLabel slotIndex ∈ activeSet) :
    basisGram tightDir basisLabel slotIndex 0 * M 0 slotIndex
        + basisGram tightDir basisLabel slotIndex 1 * M 1 slotIndex
        + basisGram tightDir basisLabel slotIndex 2 * M 2 slotIndex
        + basisGram tightDir basisLabel slotIndex 3 * M 3 slotIndex
      = value + ∑ atomIndex : Fin size,
          weight atomIndex * tightDir (basisLabel slotIndex) atomIndex ^ 2 := by
  have hread := gram_exchange_diag_read hdata basisLabel hrepresentation hmem
  rwa [matrix_mul_apply_four] at hread

end Gtz

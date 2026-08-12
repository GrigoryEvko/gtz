import Gtz.Wave.FullyPrivateBlockKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The all-private-support kill — the census clause meets the block kill

The fully-private-block kill consumes abstract enumerations.  This file
assembles the enumerations from census-shaped data on the (6, 3) shape:
four basis slots, six atoms, all supports of cardinality three, and every
atom of one slot's support with multiplicity one.  The complement of the
private support has cardinality three, each off support avoids the private
support and thus EQUALS the complement, and the order isomorphisms of the
two finite sets supply the enumerations.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.false_of_all_private_support` — **THE KILL.**  No stationary datum
  with a negative value and the trace budget two carries a four-slot basis
  with all supports of cardinality three and one fully private support.

## Vacuity

The statement takes the negative value as a hypothesis, and a crux
supplies it.  It is vacuous if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

variable {rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin 6)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)}

/-- **THE ALL-PRIVATE-SUPPORT KILL.**  On the (6, 3) shape, a four-slot
basis with all supports of cardinality three and one fully private support
dies against the trace budget. -/
theorem false_of_all_private_support
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hvalueNeg : value < 0)
    (basisLabel : Fin 4 → activeIndex)
    {L : Matrix (Fin 4) (Fin 6) ℝ}
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (htrace : Matrix.trace M = 2)
    {privateSlot : Fin 4}
    (hmemAll : ∀ columnIndex, basisLabel columnIndex ∈ activeSet)
    (hsupportCard : (datumTightSupport tightDir (basisLabel privateSlot)).card = 3)
    (hcardOff : ∀ columnIndex, columnIndex ≠ privateSlot →
      (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
    (hallPrivate : ∀ atomIndex ∈ datumTightSupport tightDir (basisLabel privateSlot),
      basisSupportMultiplicity tightDir basisLabel atomIndex = 1) :
    False := by
  classical
  have hprivateBlock : ∀ atomIndex : Fin 6,
      tightDir (basisLabel privateSlot) atomIndex ≠ 0 →
      ∀ columnIndex, columnIndex ≠ privateSlot →
        tightDir (basisLabel columnIndex) atomIndex = 0 := by
    intro atomIndex hne columnIndex hneCol
    by_contra hnonzero
    have hmult := hallPrivate atomIndex (mem_datumTightSupport.mpr hne)
    rw [basisSupportMultiplicity] at hmult
    have heq := Finset.card_le_one.mp hmult.le columnIndex
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_datumTightSupport.mpr hnonzero⟩)
      privateSlot
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_datumTightSupport.mpr hne⟩)
    exact hneCol heq
  obtain ⟨privateAtom, hprivMem⟩ :=
    Finset.card_pos.mp (by rw [hsupportCard]; norm_num)
  have hslotNe : tightDir (basisLabel privateSlot) privateAtom ≠ 0 :=
    mem_datumTightSupport.mp hprivMem
  have hatomMem : privateAtom ∈ activeSubset (basisLabel privateSlot) :=
    datumTightSupport_subset hdata (hmemAll privateSlot) hprivMem
  have hslotCard : (Finset.univ.erase privateSlot).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hfilterEq : Finset.univ.filter
      (fun atomIndex => ¬ tightDir (basisLabel privateSlot) atomIndex = 0)
      = datumTightSupport tightDir (basisLabel privateSlot) := by
    simp [datumTightSupport]
  have hcount := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 6)))
    (p := fun atomIndex => tightDir (basisLabel privateSlot) atomIndex = 0)
  rw [hfilterEq, hsupportCard] at hcount
  have hunivCard : (Finset.univ : Finset (Fin 6)).card = 6 := by simp
  have hcompCard : (Finset.univ.filter
      (fun atomIndex => tightDir (basisLabel privateSlot) atomIndex = 0)).card = 3 := by
    omega
  obtain ⟨slotEnum, hslotInjective, hslotOff, hslotSurj⟩ :
      ∃ slotEnum : Fin 3 → Fin 4, Function.Injective slotEnum
        ∧ (∀ offIndex, slotEnum offIndex ≠ privateSlot)
        ∧ ∀ columnIndex, columnIndex ≠ privateSlot →
            ∃ offIndex, slotEnum offIndex = columnIndex := by
    refine ⟨fun offIndex =>
      ((Finset.univ.erase privateSlot).orderIsoOfFin hslotCard offIndex : Fin 4),
      ?_, ?_, ?_⟩
    · intro firstIndex secondIndex heq
      exact ((Finset.univ.erase privateSlot).orderIsoOfFin hslotCard).injective
        (Subtype.ext heq)
    · intro offIndex
      exact (Finset.mem_erase.mp
        ((Finset.univ.erase privateSlot).orderIsoOfFin hslotCard offIndex).2).1
    · intro columnIndex hne
      refine ⟨((Finset.univ.erase privateSlot).orderIsoOfFin hslotCard).symm
        ⟨columnIndex, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩⟩, ?_⟩
      exact congrArg Subtype.val (OrderIso.apply_symm_apply _ _)
  obtain ⟨atomEnum, hatomInjective, hatomOff, hatomSurj⟩ :
      ∃ atomEnum : Fin 3 → Fin 6, Function.Injective atomEnum
        ∧ (∀ offIndex, tightDir (basisLabel privateSlot) (atomEnum offIndex) = 0)
        ∧ ∀ atomIndex, tightDir (basisLabel privateSlot) atomIndex = 0 →
            ∃ offIndex, atomEnum offIndex = atomIndex := by
    refine ⟨fun offIndex =>
      ((Finset.univ.filter (fun atomIndex =>
          tightDir (basisLabel privateSlot) atomIndex = 0)).orderIsoOfFin
        hcompCard offIndex : Fin 6), ?_, ?_, ?_⟩
    · intro firstIndex secondIndex heq
      exact ((Finset.univ.filter _).orderIsoOfFin hcompCard).injective
        (Subtype.ext heq)
    · intro offIndex
      exact (Finset.mem_filter.mp
        ((Finset.univ.filter _).orderIsoOfFin hcompCard offIndex).2).2
    · intro atomIndex hzero
      refine ⟨((Finset.univ.filter _).orderIsoOfFin hcompCard).symm
        ⟨atomIndex, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩⟩, ?_⟩
      exact congrArg Subtype.val (OrderIso.apply_symm_apply _ _)
  have hoffSupport : ∀ offIndex : Fin 3,
      datumTightSupport tightDir (basisLabel (slotEnum offIndex))
        = Finset.univ.filter fun atomIndex =>
            tightDir (basisLabel privateSlot) atomIndex = 0 := by
    intro offIndex
    apply Finset.eq_of_subset_of_card_le
    · intro atomIndex hmem
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      by_contra hnonzero
      exact (mem_datumTightSupport.mp hmem)
        (hprivateBlock atomIndex hnonzero (slotEnum offIndex) (hslotOff offIndex))
    · rw [hcompCard, hcardOff (slotEnum offIndex) (hslotOff offIndex)]
  have hcoverBlock : ∀ offIndex : Fin 3, ∀ atomIndex : Fin 6,
      atomIndex ∈ activeSubset (basisLabel (slotEnum offIndex))
        ∨ tightDir (basisLabel privateSlot) atomIndex ≠ 0 := by
    intro offIndex atomIndex
    by_cases hzero : tightDir (basisLabel privateSlot) atomIndex = 0
    · refine Or.inl ?_
      have hmemSupp : atomIndex
          ∈ datumTightSupport tightDir (basisLabel (slotEnum offIndex)) := by
        rw [hoffSupport offIndex]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩
      exact datumTightSupport_subset hdata (hmemAll _) hmemSupp
    · exact Or.inr hzero
  exact false_of_fully_private_block hdata hvalueNeg basisLabel hleft
    hrepresentation htrace hmemAll hprivateBlock hatomMem hslotNe
    slotEnum hslotInjective hslotOff hslotSurj
    atomEnum hatomInjective hatomOff hatomSurj hcoverBlock

end Gtz

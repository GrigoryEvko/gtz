import Gtz.Wave.DiagonalGramSupply

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The triple-pair sector kill — three atoms on one pair force two shared supports

On the six-atom shape, three distinct atoms dense on one slot pair and
carried only by that pair force the pair's supports to coincide with the
atom triple.  The remaining two slots then share the complementary
triple, and every complementary atom is carried only by the remaining
pair.  The two-shared-pair kill closes the sector without any Gram
hypothesis.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.false_of_triple_pair_sector` — **THE KILL.**

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

/-- **THE TRIPLE-PAIR SECTOR KILL.**  Three distinct atoms dense on one
slot pair and carried only by that pair die against the trace budget on
the six-atom shape. -/
theorem false_of_triple_pair_sector
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
    (hmemAll : ∀ columnIndex, basisLabel columnIndex ∈ activeSet)
    (hcardAll : ∀ columnIndex,
      (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
    {slotA slotB slotC slotD : Fin 4}
    (hAB : slotA ≠ slotB) (hCD : slotC ≠ slotD)
    (hAC : slotA ≠ slotC) (hAD : slotA ≠ slotD)
    (hBC : slotB ≠ slotC) (hBD : slotB ≠ slotD)
    {tripleOne tripleTwo tripleThree : Fin 6}
    (h12 : tripleOne ≠ tripleTwo) (h13 : tripleOne ≠ tripleThree)
    (h23 : tripleTwo ≠ tripleThree)
    (hOneDenseA : tightDir (basisLabel slotA) tripleOne ≠ 0)
    (hTwoDenseA : tightDir (basisLabel slotA) tripleTwo ≠ 0)
    (hThreeDenseA : tightDir (basisLabel slotA) tripleThree ≠ 0)
    (hOneDenseB : tightDir (basisLabel slotB) tripleOne ≠ 0)
    (hTwoDenseB : tightDir (basisLabel slotB) tripleTwo ≠ 0)
    (hThreeDenseB : tightDir (basisLabel slotB) tripleThree ≠ 0)
    (hOneCarriers : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) tripleOne = 0)
    (hTwoCarriers : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) tripleTwo = 0)
    (hThreeCarriers : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) tripleThree = 0) :
    False := by
  classical
  have hslotUniv : ∀ columnIndex : Fin 4, columnIndex = slotA ∨ columnIndex = slotB
      ∨ columnIndex = slotC ∨ columnIndex = slotD := by
    intro columnIndex
    have hBnotMem : slotB ∉ ({slotC, slotD} : Finset (Fin 4)) := by
      simp [hBC, hBD]
    have hAnotMem : slotA ∉ ({slotB, slotC, slotD} : Finset (Fin 4)) := by
      simp [hAB, hAC, hAD]
    have hCnotMem : slotC ∉ ({slotD} : Finset (Fin 4)) := by
      simp [hCD]
    have hslotCard : ({slotA, slotB, slotC, slotD} : Finset (Fin 4)).card = 4 := by
      rw [Finset.card_insert_of_notMem hAnotMem,
        Finset.card_insert_of_notMem hBnotMem,
        Finset.card_insert_of_notMem hCnotMem, Finset.card_singleton]
    have huniv : ({slotA, slotB, slotC, slotD} : Finset (Fin 4)) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_univ, Fintype.card_fin, hslotCard]
    have hmem : columnIndex ∈ ({slotA, slotB, slotC, slotD} : Finset (Fin 4)) := by
      rw [huniv]
      exact Finset.mem_univ _
    simpa using hmem
  -- the triple set
  have hTwoNotMem : tripleTwo ∉ ({tripleThree} : Finset (Fin 6)) := by
    simp [h23]
  have hOneNotMem : tripleOne ∉ ({tripleTwo, tripleThree} : Finset (Fin 6)) := by
    simp [h12, h13]
  have htripleCard : ({tripleOne, tripleTwo, tripleThree} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem hOneNotMem,
      Finset.card_insert_of_notMem hTwoNotMem, Finset.card_singleton]
  -- the pair supports both equal the triple
  have hsuppA : ({tripleOne, tripleTwo, tripleThree} : Finset (Fin 6))
      = datumTightSupport tightDir (basisLabel slotA) := by
    apply Finset.eq_of_subset_of_card_le
    · intro atomIndex hmem
      rcases Finset.mem_insert.mp hmem with h | hrest
      · exact h ▸ mem_datumTightSupport.mpr hOneDenseA
      rcases Finset.mem_insert.mp hrest with h | h
      · exact h ▸ mem_datumTightSupport.mpr hTwoDenseA
      · exact (Finset.mem_singleton.mp h) ▸ mem_datumTightSupport.mpr hThreeDenseA
    · rw [hcardAll slotA, htripleCard]
  have hsuppB : ({tripleOne, tripleTwo, tripleThree} : Finset (Fin 6))
      = datumTightSupport tightDir (basisLabel slotB) := by
    apply Finset.eq_of_subset_of_card_le
    · intro atomIndex hmem
      rcases Finset.mem_insert.mp hmem with h | hrest
      · exact h ▸ mem_datumTightSupport.mpr hOneDenseB
      rcases Finset.mem_insert.mp hrest with h | h
      · exact h ▸ mem_datumTightSupport.mpr hTwoDenseB
      · exact (Finset.mem_singleton.mp h) ▸ mem_datumTightSupport.mpr hThreeDenseB
    · rw [hcardAll slotB, htripleCard]
  have hsharedAB : datumTightSupport tightDir (basisLabel slotA)
      = datumTightSupport tightDir (basisLabel slotB) := hsuppA ▸ hsuppB
  -- every triple atom is carried only by the pair
  have hcarriersAB : ∀ atomIndex : Fin 6,
      tightDir (basisLabel slotA) atomIndex ≠ 0 →
      ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
        tightDir (basisLabel columnIndex) atomIndex = 0 := by
    intro atomIndex hdense columnIndex hneA hneB
    have hmem : atomIndex ∈ ({tripleOne, tripleTwo, tripleThree} : Finset (Fin 6)) := by
      rw [hsuppA]
      exact mem_datumTightSupport.mpr hdense
    rcases Finset.mem_insert.mp hmem with h | hrest
    · exact h ▸ hOneCarriers columnIndex hneA hneB
    rcases Finset.mem_insert.mp hrest with h | h
    · exact h ▸ hTwoCarriers columnIndex hneA hneB
    · exact (Finset.mem_singleton.mp h) ▸ hThreeCarriers columnIndex hneA hneB
  -- the complementary supports coincide
  have hcompCard : ((Finset.univ : Finset (Fin 6))
      \ ({tripleOne, tripleTwo, tripleThree} : Finset (Fin 6))).card = 3 := by
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
      Finset.inter_univ, htripleCard]
  have hsuppComp : ∀ offSlot : Fin 4, offSlot ≠ slotA → offSlot ≠ slotB →
      datumTightSupport tightDir (basisLabel offSlot)
        = (Finset.univ : Finset (Fin 6))
          \ ({tripleOne, tripleTwo, tripleThree} : Finset (Fin 6)) := by
    intro offSlot hneA hneB
    apply Finset.eq_of_subset_of_card_le
    · intro atomIndex hmem
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hcontra
      have hzero : tightDir (basisLabel offSlot) atomIndex = 0 := by
        rcases Finset.mem_insert.mp hcontra with h | hrest
        · exact h ▸ hOneCarriers offSlot hneA hneB
        rcases Finset.mem_insert.mp hrest with h | h
        · exact h ▸ hTwoCarriers offSlot hneA hneB
        · exact (Finset.mem_singleton.mp h) ▸ hThreeCarriers offSlot hneA hneB
      exact (mem_datumTightSupport.mp hmem) hzero
    · rw [hcompCard, hcardAll offSlot]
  have hsharedCD : datumTightSupport tightDir (basisLabel slotC)
      = datumTightSupport tightDir (basisLabel slotD) := by
    rw [hsuppComp slotC (Ne.symm hAC) (Ne.symm hBC),
      hsuppComp slotD (Ne.symm hAD) (Ne.symm hBD)]
  -- every complementary atom is carried only by the remaining pair
  have hcarriersCD : ∀ atomIndex : Fin 6,
      tightDir (basisLabel slotC) atomIndex ≠ 0 →
      ∀ columnIndex, columnIndex ≠ slotC → columnIndex ≠ slotD →
        tightDir (basisLabel columnIndex) atomIndex = 0 := by
    intro atomIndex hdense columnIndex hneC hneD
    have hmemComp : atomIndex ∈ (Finset.univ : Finset (Fin 6))
        \ ({tripleOne, tripleTwo, tripleThree} : Finset (Fin 6)) := by
      rw [← hsuppComp slotC (Ne.symm hAC) (Ne.symm hBC)]
      exact mem_datumTightSupport.mpr hdense
    have hnotTriple := (Finset.mem_sdiff.mp hmemComp).2
    rcases hslotUniv columnIndex with h | h | h | h
    · subst h
      by_contra hnonzero
      have hmemA : atomIndex ∈ ({tripleOne, tripleTwo, tripleThree}
          : Finset (Fin 6)) := by
        rw [hsuppA]
        exact mem_datumTightSupport.mpr hnonzero
      exact hnotTriple hmemA
    · subst h
      by_contra hnonzero
      have hmemB : atomIndex ∈ ({tripleOne, tripleTwo, tripleThree}
          : Finset (Fin 6)) := by
        rw [hsuppB]
        exact mem_datumTightSupport.mpr hnonzero
      exact hnotTriple hmemB
    · exact absurd h hneC
    · exact absurd h hneD
  -- the nonempty supports
  have hnonemptyAB : (datumTightSupport tightDir (basisLabel slotA)).Nonempty := by
    rw [← hsuppA]
    exact ⟨tripleOne, Finset.mem_insert_self _ _⟩
  have hnonemptyCD : (datumTightSupport tightDir (basisLabel slotC)).Nonempty := by
    rw [← Finset.card_pos, hcardAll slotC]
    norm_num
  exact false_of_two_shared_support_pairs hdata hvalueNeg basisLabel hleft
    hrepresentation htrace hAB hCD hAC hAD hBC hBD
    (hmemAll slotA) (hmemAll slotB) (hmemAll slotC) (hmemAll slotD)
    hsharedAB hsharedCD hnonemptyAB hnonemptyCD hcarriersAB hcarriersCD

end Gtz

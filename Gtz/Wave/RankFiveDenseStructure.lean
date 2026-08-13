import Gtz.Wave.RankFiveClosureSupply

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The rank-five dense structure — the block laws of the dense branch

The dense branch of the rank-five census carries all supports at
cardinality three, every atom in at least two supports, and a heavy atom
in at least three.  This file lands the structure laws that the dense
kills consume.  A full support IS its block.  A heavy atom yields three
distinct carrier slots.  Two doubled supports are complementary triples:
an atom outside the two doubled supports has at most one carrier, and
the dense floor refuses it.  The doubled-cover law is the rank-five
analog of the rank-four cycle normalization, and with the shared-block
cap it pins the doubled sub-branch to one shape: two complementary
doubled triples plus one crossing fifth block.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.RankFiveFrame.dense_support_eq_block` — a full support is its
  block.
* `Gtz.exists_three_carriers_of_heavy_atom` — the heavy atom yields
  three distinct carrier slots.
* `Gtz.RankFiveFrame.dense_doubled_covers` — **THE DOUBLED-COVER LAW.**
  Two doubled supports are disjoint and cover the six atoms.

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds.  The
carrier extraction is unconditional.
-/

namespace Gtz

open Matrix

/-- A full support of a rank-five frame is its block. -/
theorem RankFiveFrame.dense_support_eq_block {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {columnIndex : Fin 5}
    (hcard : (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) :
    datumTightSupport frame.tightDir (frame.basisLabel columnIndex)
      = frame.activeSubset (frame.basisLabel columnIndex) :=
  datumTightSupport_eq_activeSubset_of_card_eq_rank frame.hdata
    (frame.hmemAll columnIndex) hcard

/-- **THE CARRIER TRIPLE.**  An atom of multiplicity at least three
yields three distinct carrier slots. -/
theorem exists_three_carriers_of_heavy_atom {size basisCount : ℕ}
    {activeIndex : Type*} {tightDir : activeIndex → (Fin size → ℝ)}
    {basisLabel : Fin basisCount → activeIndex} {heavyAtom : Fin size}
    (hheavy : 3 ≤ basisSupportMultiplicity tightDir basisLabel heavyAtom) :
    ∃ slotOne slotTwo slotThree : Fin basisCount,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
      ∧ heavyAtom ∈ datumTightSupport tightDir (basisLabel slotOne)
      ∧ heavyAtom ∈ datumTightSupport tightDir (basisLabel slotTwo)
      ∧ heavyAtom ∈ datumTightSupport tightDir (basisLabel slotThree) := by
  classical
  rw [basisSupportMultiplicity] at hheavy
  obtain ⟨carrierTriple, hsubset, hcardTriple⟩ :=
    Finset.exists_subset_card_eq hheavy
  obtain ⟨slotOne, slotTwo, slotThree, h12, h13, h23, hset⟩ :=
    Finset.card_eq_three.mp hcardTriple
  have hmemOf : ∀ slotIndex ∈ carrierTriple,
      heavyAtom ∈ datumTightSupport tightDir (basisLabel slotIndex) :=
    fun slotIndex hmem => (Finset.mem_filter.mp (hsubset hmem)).2
  refine ⟨slotOne, slotTwo, slotThree, h12, h13, h23, ?_, ?_, ?_⟩
  · exact hmemOf slotOne (by rw [hset]; exact Finset.mem_insert_self _ _)
  · exact hmemOf slotTwo (by
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  · exact hmemOf slotThree (by
      rw [hset]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

/-- **THE DOUBLED-COVER LAW.**  At a dense rank-five frame, two doubled
supports are disjoint and cover the six atoms.  An atom outside the two
doubled supports has at most one carrier — only the fifth slot — and
the dense floor refuses it.  The cardinality count then kills the
intersection. -/
theorem RankFiveFrame.dense_doubled_covers {crux : SixThreeCrux}
    (frame : RankFiveFrame crux)
    (hmultTwo : ∀ atomIndex, 2 ≤ basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex)
    {slotA slotB slotC slotD : Fin 5}
    (hAB : slotA ≠ slotB) (hAC : slotA ≠ slotC) (hAD : slotA ≠ slotD)
    (hBC : slotB ≠ slotC) (hBD : slotB ≠ slotD) (hCD : slotC ≠ slotD)
    (hcardA : (datumTightSupport frame.tightDir
      (frame.basisLabel slotA)).card = 3)
    (hcardC : (datumTightSupport frame.tightDir
      (frame.basisLabel slotC)).card = 3)
    (hdoubledAB : datumTightSupport frame.tightDir (frame.basisLabel slotB)
      = datumTightSupport frame.tightDir (frame.basisLabel slotA))
    (hdoubledCD : datumTightSupport frame.tightDir (frame.basisLabel slotD)
      = datumTightSupport frame.tightDir (frame.basisLabel slotC)) :
    datumTightSupport frame.tightDir (frame.basisLabel slotA)
        ∩ datumTightSupport frame.tightDir (frame.basisLabel slotC) = ∅
      ∧ datumTightSupport frame.tightDir (frame.basisLabel slotA)
        ∪ datumTightSupport frame.tightDir (frame.basisLabel slotC)
        = Finset.univ := by
  classical
  have hcardQuad : ({slotA, slotB, slotC, slotD} : Finset (Fin 5)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hAB, hAC, hAD]),
      Finset.card_insert_of_notMem (by simp [hBC, hBD]),
      Finset.card_insert_of_notMem (by simp [hCD]), Finset.card_singleton]
  have hunion : datumTightSupport frame.tightDir (frame.basisLabel slotA)
      ∪ datumTightSupport frame.tightDir (frame.basisLabel slotC)
      = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro atomIndex
    by_contra houtside
    rw [Finset.mem_union] at houtside
    push Not at houtside
    have hsubFilter : Finset.univ.filter (fun columnIndex =>
        atomIndex ∈ datumTightSupport frame.tightDir
          (frame.basisLabel columnIndex))
        ⊆ Finset.univ \ ({slotA, slotB, slotC, slotD} : Finset (Fin 5)) := by
      intro columnIndex hmemFilter
      have hcarry := (Finset.mem_filter.mp hmemFilter).2
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hmemQuad => ?_⟩
      rcases Finset.mem_insert.mp hmemQuad with hA | hrest
      · rw [hA] at hcarry
        exact houtside.1 hcarry
      rcases Finset.mem_insert.mp hrest with hB | hrest'
      · rw [hB, hdoubledAB] at hcarry
        exact houtside.1 hcarry
      rcases Finset.mem_insert.mp hrest' with hC | hD
      · rw [hC] at hcarry
        exact houtside.2 hcarry
      · rw [Finset.mem_singleton.mp hD, hdoubledCD] at hcarry
        exact houtside.2 hcarry
    have hcap := Finset.card_le_card hsubFilter
    rw [Finset.card_univ_sdiff, hcardQuad, Fintype.card_fin] at hcap
    have hfloor := hmultTwo atomIndex
    rw [basisSupportMultiplicity] at hfloor
    omega
  refine ⟨?_, hunion⟩
  have hcount := Finset.card_union_add_card_inter
    (datumTightSupport frame.tightDir (frame.basisLabel slotA))
    (datumTightSupport frame.tightDir (frame.basisLabel slotC))
  rw [hunion, Finset.card_univ, Fintype.card_fin, hcardA, hcardC] at hcount
  rw [← Finset.card_eq_zero]
  omega

end Gtz

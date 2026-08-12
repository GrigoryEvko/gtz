import Mathlib
import Gtz.Quantitative.ThreeTripleDoorReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The all-double door: profile (0,0,6,0) closed end to end

Every atom doubly covered admits exactly two shapes, read off the dual
multigraph on the four blocks (three-regular with six edges): the simple
K4 — atoms biject with block pairs, giving the TETRAHEDRON M(K4) — or one
doubled edge forcing a complementary doubled edge, giving the DOUBLE-DOUBLE.
The driver: the three atoms of the first block each name one other block;
an injective assignment yields the tetrahedron, a repeated target yields the
double-double, and a triple target collides two blocks.  Explicit
permutations land the shapes on `{{0,1,2},{0,3,4},{1,3,5},{2,4,5}}` and
`{{0,1,2},{0,1,3},{2,4,5},{3,4,5}}`.  Sixth and seventh census
representatives pinned; one profile door remains open on each side of the
count spectrum.
-/

namespace Gtz

/-- Swapping the first two listed elements of a three-element set. -/
theorem tripleSet_swap_first_second {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α) = {b, a, c} :=
  Finset.insert_comm a b {c}

/-- Swapping the last two listed elements of a three-element set. -/
theorem tripleSet_swap_second_third {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α) = {a, c, b} :=
  congrArg (insert a) (Finset.pair_comm b c)

/-- A full double class makes every atom doubly covered. -/
theorem count_eq_two_of_doubleClassCard_six
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hclass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2 = 6)
    (atomIndex : Fin 6) :
    fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 2 := by
  rw [fourBlockCountClass] at hclass
  have hfilterEq : (Finset.univ.filter fun atom =>
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom = 2)
        = Finset.univ :=
    Finset.eq_univ_of_card _ (hclass.trans (Fintype.card_fin 6).symm)
  have hmem : atomIndex ∈ Finset.univ.filter fun atom =>
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom = 2 := by
    rw [hfilterEq]
    exact Finset.mem_univ atomIndex
  exact (Finset.mem_filter.mp hmem).2

/-- **The companion-target normalization.**  The three atoms of the first
block each name one other block; an injective assignment is the tetrahedron
seed, a repeated target the double-double seed, and a triple target collides
two blocks. -/
theorem exists_companionAssignment_of_all_count_two
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock)
    (hcardTwo : secondBlock.card = 3) (hcardThree : thirdBlock.card = 3)
    (hcardFour : fourthBlock.card = 3)
    {atomU atomV atomW : Fin 6}
    (hneUV : atomU ≠ atomV) (hneUW : atomU ≠ atomW) (hneVW : atomV ≠ atomW)
    (hAtomEq : firstBlock = {atomU, atomV, atomW})
    (hcountU : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomU
      = 2)
    (hcountV : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomV
      = 2)
    (hcountW : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomW
      = 2) :
    (∃ blockU blockV blockW : Finset (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} : Finset (Finset (Fin 6)))
          = {firstBlock, blockU, blockV, blockW}
        ∧ (∀ atom : Fin 6, fourBlockCoverCount firstBlock blockU blockV blockW atom
            = fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom)
        ∧ blockU.card = 3 ∧ blockV.card = 3 ∧ blockW.card = 3
        ∧ atomU ∈ blockU ∧ atomU ∉ blockV ∧ atomU ∉ blockW
        ∧ atomV ∉ blockU ∧ atomV ∈ blockV ∧ atomV ∉ blockW
        ∧ atomW ∉ blockU ∧ atomW ∉ blockV ∧ atomW ∈ blockW)
      ∨ (∃ pairFirst pairSecond lonerAtom : Fin 6,
        ∃ blockShared blockLoner blockLast : Finset (Fin 6),
        firstBlock = {pairFirst, pairSecond, lonerAtom}
          ∧ pairFirst ≠ pairSecond ∧ pairFirst ≠ lonerAtom ∧ pairSecond ≠ lonerAtom
          ∧ ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
              Finset (Finset (Fin 6)))
            = {firstBlock, blockShared, blockLoner, blockLast}
          ∧ (∀ atom : Fin 6, fourBlockCoverCount firstBlock blockShared blockLoner
              blockLast atom
                = fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
                    atom)
          ∧ blockShared.card = 3 ∧ blockLoner.card = 3 ∧ blockLast.card = 3
          ∧ pairFirst ∈ blockShared ∧ pairSecond ∈ blockShared
          ∧ lonerAtom ∉ blockShared
          ∧ pairFirst ∉ blockLoner ∧ pairSecond ∉ blockLoner ∧ lonerAtom ∈ blockLoner
          ∧ pairFirst ∉ blockLast ∧ pairSecond ∉ blockLast ∧ lonerAtom ∉ blockLast) := by
  have hmemUFirst : atomU ∈ firstBlock := by
    rw [hAtomEq]
    exact Finset.mem_insert_self _ _
  have hmemVFirst : atomV ∈ firstBlock := by
    rw [hAtomEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
  have hmemWFirst : atomW ∈ firstBlock := by
    rw [hAtomEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self _))))
  rcases fourBlockCoverCount_eq_two_inversion hcountU with
      ⟨huFirst, huSecond, huThird, huFourth⟩ | ⟨huFirst, huSecond, huThird, huFourth⟩
    | ⟨huFirst, huSecond, huThird, huFourth⟩ | ⟨huFirst, huSecond, huThird, huFourth⟩
    | ⟨huFirst, huSecond, huThird, huFourth⟩
    | ⟨huFirst, huSecond, huThird, huFourth⟩ <;>
    rcases fourBlockCoverCount_eq_two_inversion hcountV with
        ⟨hvFirst, hvSecond, hvThird, hvFourth⟩ | ⟨hvFirst, hvSecond, hvThird, hvFourth⟩
      | ⟨hvFirst, hvSecond, hvThird, hvFourth⟩ | ⟨hvFirst, hvSecond, hvThird, hvFourth⟩
      | ⟨hvFirst, hvSecond, hvThird, hvFourth⟩
      | ⟨hvFirst, hvSecond, hvThird, hvFourth⟩ <;>
    rcases fourBlockCoverCount_eq_two_inversion hcountW with
        ⟨hwFirst, hwSecond, hwThird, hwFourth⟩ | ⟨hwFirst, hwSecond, hwThird, hwFourth⟩
      | ⟨hwFirst, hwSecond, hwThird, hwFourth⟩ | ⟨hwFirst, hwSecond, hwThird, hwFourth⟩
      | ⟨hwFirst, hwSecond, hwThird, hwFourth⟩
      | ⟨hwFirst, hwSecond, hwThird, hwFourth⟩ <;>
    first
    | exact absurd hmemUFirst huFirst
    | exact absurd hmemVFirst hvFirst
    | exact absurd hmemWFirst hwFirst
    | exact absurd ((eq_triple_of_mem_mem_mem_card_three hcardTwo hneUV hneUW hneVW
        huSecond hvSecond hwSecond).trans hAtomEq.symm) hneOneTwo.symm
    | exact absurd ((eq_triple_of_mem_mem_mem_card_three hcardThree hneUV hneUW hneVW
        huThird hvThird hwThird).trans hAtomEq.symm) hneOneThree.symm
    | exact absurd ((eq_triple_of_mem_mem_mem_card_three hcardFour hneUV hneUW hneVW
        huFourth hvFourth hwFourth).trans hAtomEq.symm) hneOneFour.symm
    | exact Or.inr ⟨atomU, atomV, atomW, secondBlock, thirdBlock, fourthBlock,
        hAtomEq,
        hneUV, hneUW, hneVW, rfl, fun atom => rfl, hcardTwo, hcardThree, hcardFour,
        huSecond, hvSecond, hwSecond, huThird, hvThird, hwThird, huFourth, hvFourth, hwFourth⟩
    | (refine Or.inr ⟨atomU, atomV, atomW, secondBlock, fourthBlock, thirdBlock,
        hAtomEq,
        hneUV, hneUW, hneVW, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardFour, hcardThree,
        huSecond, hvSecond, hwSecond, huFourth, hvFourth, hwFourth, huThird, hvThird, hwThird⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock])
    | exact Or.inr ⟨atomU, atomW, atomV, secondBlock, thirdBlock, fourthBlock,
        hAtomEq.trans (tripleSet_swap_second_third atomU atomV atomW),
        hneUW, hneUV, hneVW.symm, rfl, fun atom => rfl, hcardTwo, hcardThree, hcardFour,
        huSecond, hwSecond, hvSecond, huThird, hwThird, hvThird, huFourth, hwFourth, hvFourth⟩
    | (refine Or.inr ⟨atomV, atomW, atomU, thirdBlock, secondBlock, fourthBlock,
        hAtomEq.trans ((tripleSet_swap_first_second atomU atomV atomW).trans
          (tripleSet_swap_second_third atomV atomU atomW)),
        hneVW, hneUV.symm, hneUW.symm, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardTwo, hcardFour,
        hvThird, hwThird, huThird, hvSecond, hwSecond, huSecond, hvFourth, hwFourth, huFourth⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock])
    | exact Or.inl ⟨secondBlock, thirdBlock, fourthBlock, rfl,
        fun atom => rfl, hcardTwo, hcardThree, hcardFour,
        huSecond, huThird, huFourth, hvSecond, hvThird, hvFourth, hwSecond, hwThird, hwFourth⟩
    | (refine Or.inr ⟨atomU, atomW, atomV, secondBlock, fourthBlock, thirdBlock,
        hAtomEq.trans (tripleSet_swap_second_third atomU atomV atomW),
        hneUW, hneUV, hneVW.symm, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardFour, hcardThree,
        huSecond, hwSecond, hvSecond, huFourth, hwFourth, hvFourth, huThird, hwThird, hvThird⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock])
    | (refine Or.inl ⟨secondBlock, fourthBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardFour, hcardThree,
        huSecond, huFourth, huThird, hvSecond, hvFourth, hvThird, hwSecond, hwFourth, hwThird⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock])
    | (refine Or.inr ⟨atomV, atomW, atomU, fourthBlock, secondBlock, thirdBlock,
        hAtomEq.trans ((tripleSet_swap_first_second atomU atomV atomW).trans
          (tripleSet_swap_second_third atomV atomU atomW)),
        hneVW, hneUV.symm, hneUW.symm, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardTwo, hcardThree,
        hvFourth, hwFourth, huFourth, hvSecond, hwSecond, huSecond, hvThird, hwThird, huThird⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock])
    | exact Or.inr ⟨atomV, atomW, atomU, secondBlock, thirdBlock, fourthBlock,
        hAtomEq.trans ((tripleSet_swap_first_second atomU atomV atomW).trans
          (tripleSet_swap_second_third atomV atomU atomW)),
        hneVW, hneUV.symm, hneUW.symm, rfl, fun atom => rfl, hcardTwo, hcardThree, hcardFour,
        hvSecond, hwSecond, huSecond, hvThird, hwThird, huThird, hvFourth, hwFourth, huFourth⟩
    | (refine Or.inr ⟨atomU, atomW, atomV, thirdBlock, secondBlock, fourthBlock,
        hAtomEq.trans (tripleSet_swap_second_third atomU atomV atomW),
        hneUW, hneUV, hneVW.symm, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardTwo, hcardFour,
        huThird, hwThird, hvThird, huSecond, hwSecond, hvSecond, huFourth, hwFourth, hvFourth⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock])
    | (refine Or.inl ⟨thirdBlock, secondBlock, fourthBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardTwo, hcardFour,
        huThird, huSecond, huFourth, hvThird, hvSecond, hvFourth, hwThird, hwSecond, hwFourth⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock])
    | (refine Or.inr ⟨atomU, atomV, atomW, thirdBlock, secondBlock, fourthBlock,
        hAtomEq,
        hneUV, hneUW, hneVW, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardTwo, hcardFour,
        huThird, hvThird, hwThird, huSecond, hvSecond, hwSecond, huFourth, hvFourth, hwFourth⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock])
    | (refine Or.inr ⟨atomU, atomV, atomW, thirdBlock, fourthBlock, secondBlock,
        hAtomEq,
        hneUV, hneUW, hneVW, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardFour, hcardTwo,
        huThird, hvThird, hwThird, huFourth, hvFourth, hwFourth, huSecond, hvSecond, hwSecond⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock])
    | (refine Or.inl ⟨thirdBlock, fourthBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardFour, hcardTwo,
        huThird, huFourth, huSecond, hvThird, hvFourth, hvSecond, hwThird, hwFourth, hwSecond⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock])
    | (refine Or.inr ⟨atomU, atomW, atomV, thirdBlock, fourthBlock, secondBlock,
        hAtomEq.trans (tripleSet_swap_second_third atomU atomV atomW),
        hneUW, hneUV, hneVW.symm, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardFour, hcardTwo,
        huThird, hwThird, hvThird, huFourth, hwFourth, hvFourth, huSecond, hwSecond, hvSecond⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock])
    | (refine Or.inr ⟨atomV, atomW, atomU, fourthBlock, thirdBlock, secondBlock,
        hAtomEq.trans ((tripleSet_swap_first_second atomU atomV atomW).trans
          (tripleSet_swap_second_third atomV atomU atomW)),
        hneVW, hneUV.symm, hneUW.symm, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardThree, hcardTwo,
        hvFourth, hwFourth, huFourth, hvThird, hwThird, huThird, hvSecond, hwSecond, huSecond⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_third_fourth firstBlock fourthBlock secondBlock thirdBlock])
    | (refine Or.inr ⟨atomV, atomW, atomU, secondBlock, fourthBlock, thirdBlock,
        hAtomEq.trans ((tripleSet_swap_first_second atomU atomV atomW).trans
          (tripleSet_swap_second_third atomV atomU atomW)),
        hneVW, hneUV.symm, hneUW.symm, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardFour, hcardThree,
        hvSecond, hwSecond, huSecond, hvFourth, hwFourth, huFourth, hvThird, hwThird, huThird⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock])
    | (refine Or.inl ⟨fourthBlock, secondBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardTwo, hcardThree,
        huFourth, huSecond, huThird, hvFourth, hvSecond, hvThird, hwFourth, hwSecond, hwThird⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock])
    | (refine Or.inr ⟨atomU, atomW, atomV, fourthBlock, secondBlock, thirdBlock,
        hAtomEq.trans (tripleSet_swap_second_third atomU atomV atomW),
        hneUW, hneUV, hneVW.symm, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardTwo, hcardThree,
        huFourth, hwFourth, hvFourth, huSecond, hwSecond, hvSecond, huThird, hwThird, hvThird⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock])
    | (refine Or.inl ⟨fourthBlock, thirdBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardThree, hcardTwo,
        huFourth, huThird, huSecond, hvFourth, hvThird, hvSecond, hwFourth, hwThird, hwSecond⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_third_fourth firstBlock fourthBlock secondBlock thirdBlock])
    | (refine Or.inr ⟨atomV, atomW, atomU, thirdBlock, fourthBlock, secondBlock,
        hAtomEq.trans ((tripleSet_swap_first_second atomU atomV atomW).trans
          (tripleSet_swap_second_third atomV atomU atomW)),
        hneVW, hneUV.symm, hneUW.symm, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardFour, hcardTwo,
        hvThird, hwThird, huThird, hvFourth, hwFourth, huFourth, hvSecond, hwSecond, huSecond⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock])
    | (refine Or.inr ⟨atomU, atomW, atomV, fourthBlock, thirdBlock, secondBlock,
        hAtomEq.trans (tripleSet_swap_second_third atomU atomV atomW),
        hneUW, hneUV, hneVW.symm, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardThree, hcardTwo,
        huFourth, hwFourth, hvFourth, huThird, hwThird, hvThird, huSecond, hwSecond, hvSecond⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_third_fourth firstBlock fourthBlock secondBlock thirdBlock])
    | (refine Or.inr ⟨atomU, atomV, atomW, fourthBlock, secondBlock, thirdBlock,
        hAtomEq,
        hneUV, hneUW, hneVW, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardTwo, hcardThree,
        huFourth, hvFourth, hwFourth, huSecond, hvSecond, hwSecond, huThird, hvThird, hwThird⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock])
    | (refine Or.inr ⟨atomU, atomV, atomW, fourthBlock, thirdBlock, secondBlock,
        hAtomEq,
        hneUV, hneUW, hneVW, ?_, fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardThree, hcardTwo,
        huFourth, hvFourth, hwFourth, huThird, hvThird, hwThird, huSecond, hvSecond, hwSecond⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_third_fourth firstBlock fourthBlock secondBlock thirdBlock])

/-- **The tetrahedron extraction.**  An injective companion assignment forces
the K4 shape: the companions of the first block's atoms pair up through three
further atoms, one per block pair. -/
theorem family_eq_tetrahedronForm_of_assignment
    {firstBlock blockU blockV blockW : Finset (Fin 6)}
    {atomU atomV atomW : Fin 6}
    (hneUV : atomU ≠ atomV) (hneUW : atomU ≠ atomW) (hneVW : atomV ≠ atomW)
    (hAtomEq : firstBlock = {atomU, atomV, atomW})
    (hcardU : blockU.card = 3) (hcardV : blockV.card = 3) (hcardW : blockW.card = 3)
    (hmemUU : atomU ∈ blockU) (hnotUV : atomU ∉ blockV) (hnotUW : atomU ∉ blockW)
    (hnotVU : atomV ∉ blockU) (hmemVV : atomV ∈ blockV) (hnotVW : atomV ∉ blockW)
    (hnotWU : atomW ∉ blockU) (hnotWV : atomW ∉ blockV) (hmemWW : atomW ∈ blockW)
    (hAllTwo : ∀ atom : Fin 6,
      fourBlockCoverCount firstBlock blockU blockV blockW atom = 2) :
    ∃ edgeUV edgeUW edgeVW : Fin 6,
      edgeUV ≠ atomU ∧ edgeUV ≠ atomV ∧ edgeUV ≠ atomW
        ∧ edgeUW ≠ atomU ∧ edgeUW ≠ atomV ∧ edgeUW ≠ atomW
        ∧ edgeVW ≠ atomU ∧ edgeVW ≠ atomV ∧ edgeVW ≠ atomW
        ∧ edgeUV ≠ edgeUW ∧ edgeUV ≠ edgeVW ∧ edgeUW ≠ edgeVW
        ∧ blockU = {atomU, edgeUV, edgeUW}
        ∧ blockV = {atomV, edgeUV, edgeVW}
        ∧ blockW = {atomW, edgeUW, edgeVW} := by
  have heraseCard : (blockU.erase atomU).card = 2 := by
    rw [Finset.card_erase_of_mem hmemUU, hcardU]
  obtain ⟨xAtom, yAtom, hneXY, heraseEq⟩ := Finset.card_eq_two.mp heraseCard
  have hxErase : xAtom ∈ blockU.erase atomU := by
    rw [heraseEq]
    exact Finset.mem_insert_self _ _
  have hyErase : yAtom ∈ blockU.erase atomU := by
    rw [heraseEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hxNeU : xAtom ≠ atomU := (Finset.mem_erase.mp hxErase).1
  have hyNeU : yAtom ≠ atomU := (Finset.mem_erase.mp hyErase).1
  have hxU : xAtom ∈ blockU := (Finset.mem_erase.mp hxErase).2
  have hyU : yAtom ∈ blockU := (Finset.mem_erase.mp hyErase).2
  have hUEq : blockU = {atomU, xAtom, yAtom} := by
    rw [← Finset.insert_erase hmemUU, heraseEq]
  have hxNeV : xAtom ≠ atomV := fun hcontra => hnotVU (hcontra ▸ hxU)
  have hxNeW : xAtom ≠ atomW := fun hcontra => hnotWU (hcontra ▸ hxU)
  have hyNeV : yAtom ≠ atomV := fun hcontra => hnotVU (hcontra ▸ hyU)
  have hyNeW : yAtom ≠ atomW := fun hcontra => hnotWU (hcontra ▸ hyU)
  have hxNotFirst : xAtom ∉ firstBlock := by
    rw [hAtomEq]
    simp [hxNeU, hxNeV, hxNeW]
  have hyNotFirst : yAtom ∉ firstBlock := by
    rw [hAtomEq]
    simp [hyNeU, hyNeV, hyNeW]
  have hxVW : (xAtom ∈ blockV ∧ xAtom ∉ blockW)
      ∨ (xAtom ∉ blockV ∧ xAtom ∈ blockW) := by
    rcases fourBlockCoverCount_eq_two_inversion (hAllTwo xAtom) with
        ⟨hf, _, _, _⟩ | ⟨hf, _, _, _⟩ | ⟨hf, _, _, _⟩ | ⟨_, _, hc, hd⟩
      | ⟨_, _, hc, hd⟩ | ⟨_, hb, _, _⟩
    exacts [absurd hf hxNotFirst, absurd hf hxNotFirst, absurd hf hxNotFirst,
      Or.inl ⟨hc, hd⟩, Or.inr ⟨hc, hd⟩, absurd hxU hb]
  have hyVW : (yAtom ∈ blockV ∧ yAtom ∉ blockW)
      ∨ (yAtom ∉ blockV ∧ yAtom ∈ blockW) := by
    rcases fourBlockCoverCount_eq_two_inversion (hAllTwo yAtom) with
        ⟨hf, _, _, _⟩ | ⟨hf, _, _, _⟩ | ⟨hf, _, _, _⟩ | ⟨_, _, hc, hd⟩
      | ⟨_, _, hc, hd⟩ | ⟨_, hb, _, _⟩
    exacts [absurd hf hyNotFirst, absurd hf hyNotFirst, absurd hf hyNotFirst,
      Or.inl ⟨hc, hd⟩, Or.inr ⟨hc, hd⟩, absurd hyU hb]
  have hmain : ∀ candUV candUW : Fin 6, blockU = {atomU, candUV, candUW}
      → candUV ≠ atomU → candUV ≠ atomV → candUV ≠ atomW
      → candUW ≠ atomU → candUW ≠ atomV → candUW ≠ atomW
      → candUV ≠ candUW
      → candUV ∈ blockV → candUW ∉ blockV → candUW ∈ blockW
      → ∃ edgeUV edgeUW edgeVW : Fin 6,
          edgeUV ≠ atomU ∧ edgeUV ≠ atomV ∧ edgeUV ≠ atomW
            ∧ edgeUW ≠ atomU ∧ edgeUW ≠ atomV ∧ edgeUW ≠ atomW
            ∧ edgeVW ≠ atomU ∧ edgeVW ≠ atomV ∧ edgeVW ≠ atomW
            ∧ edgeUV ≠ edgeUW ∧ edgeUV ≠ edgeVW ∧ edgeUW ≠ edgeVW
            ∧ blockU = {atomU, edgeUV, edgeUW}
            ∧ blockV = {atomV, edgeUV, edgeVW}
            ∧ blockW = {atomW, edgeUW, edgeVW} := by
    intro candUV candUW hUEqCand hc1NeU hc1NeV hc1NeW hc2NeU hc2NeV hc2NeW hneCands
      hc1V hc2NotV hc2W
    obtain ⟨thirdAtom, hthirdNeV, hthirdNeCand, hVEq⟩ :=
      exists_third_of_pair_mem_card_three hcardV hc1NeV.symm hmemVV hc1V
    have hthirdV : thirdAtom ∈ blockV := by
      rw [hVEq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton_self _))))
    have hthirdNeU : thirdAtom ≠ atomU := fun hcontra => hnotUV (hcontra ▸ hthirdV)
    have hthirdNeW : thirdAtom ≠ atomW := fun hcontra => hnotWV (hcontra ▸ hthirdV)
    have hthirdNeCand2 : thirdAtom ≠ candUW := fun hcontra =>
      hc2NotV (hcontra ▸ hthirdV)
    have hthirdNotFirst : thirdAtom ∉ firstBlock := by
      rw [hAtomEq]
      simp [hthirdNeU, hthirdNeV, hthirdNeW]
    have hthirdNotU : thirdAtom ∉ blockU := by
      intro hcontra
      rw [hUEqCand] at hcontra
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcontra
      rcases hcontra with rfl | rfl | rfl
      exacts [hthirdNeU rfl, hthirdNeCand rfl, hthirdNeCand2 rfl]
    have hthirdW : thirdAtom ∈ blockW := by
      rcases fourBlockCoverCount_eq_two_inversion (hAllTwo thirdAtom) with
          ⟨hf, _, _, _⟩ | ⟨hf, _, _, _⟩ | ⟨hf, _, _, _⟩ | ⟨_, hb, _, _⟩
        | ⟨_, _, hc, _⟩ | ⟨_, _, _, hd⟩
      exacts [absurd hf hthirdNotFirst, absurd hf hthirdNotFirst,
        absurd hf hthirdNotFirst, absurd hb hthirdNotU,
        absurd hthirdV hc, hd]
    have hWEq : blockW = {atomW, candUW, thirdAtom} :=
      eq_triple_of_mem_mem_mem_card_three hcardW hc2NeW.symm hthirdNeW.symm
        hthirdNeCand2.symm hmemWW hc2W hthirdW
    exact ⟨candUV, candUW, thirdAtom, hc1NeU, hc1NeV, hc1NeW, hc2NeU, hc2NeV, hc2NeW,
      hthirdNeU, hthirdNeV, hthirdNeW, hneCands, hthirdNeCand.symm,
      hthirdNeCand2.symm, hUEqCand, hVEq, hWEq⟩
  rcases hxVW with ⟨hxV, hxNotW⟩ | ⟨hxNotV, hxW⟩ <;>
    rcases hyVW with ⟨hyV, hyNotW⟩ | ⟨hyNotV, hyW⟩
  · -- both companions in blockV: blockW starves
    have heraseW : (blockW.erase atomW).card = 2 := by
      rw [Finset.card_erase_of_mem hmemWW, hcardW]
    obtain ⟨sAtom, tAtom, hneST, heraseWEq⟩ := Finset.card_eq_two.mp heraseW
    have hsErase : sAtom ∈ blockW.erase atomW := by
      rw [heraseWEq]
      exact Finset.mem_insert_self _ _
    have htErase : tAtom ∈ blockW.erase atomW := by
      rw [heraseWEq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have hsub : ({sAtom, tAtom} : Finset (Fin 6))
        ⊆ ({atomU, atomV, atomW, xAtom, yAtom} : Finset (Fin 6))ᶜ := by
      intro atom hmem
      have hmemW : atom ∈ blockW := by
        rcases Finset.mem_insert.mp hmem with rfl | hmem2
        · exact (Finset.mem_erase.mp hsErase).2
        · rw [Finset.mem_singleton] at hmem2
          exact hmem2 ▸ (Finset.mem_erase.mp htErase).2
      have hneAnchor : atom ≠ atomW := by
        rcases Finset.mem_insert.mp hmem with rfl | hmem2
        · exact (Finset.mem_erase.mp hsErase).1
        · rw [Finset.mem_singleton] at hmem2
          exact hmem2 ▸ (Finset.mem_erase.mp htErase).1
      rw [Finset.mem_compl]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl | rfl | rfl)
      exacts [hnotUW hmemW, hnotVW hmemW, hneAnchor rfl, hxNotW hmemW, hyNotW hmemW]
    have hfiveCard : ({atomU, atomV, atomW, xAtom, yAtom} : Finset (Fin 6)).card
        = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [hneUV, hneUW, hxNeU.symm, hyNeU.symm]),
        Finset.card_insert_of_notMem (by simp [hneVW, hxNeV.symm, hyNeV.symm]),
        Finset.card_insert_of_notMem (by simp [hxNeW.symm, hyNeW.symm]),
        Finset.card_insert_of_notMem (by simpa using hneXY), Finset.card_singleton]
    have hpairCard : ({sAtom, tAtom} : Finset (Fin 6)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hneST), Finset.card_singleton]
    have hcompl := Finset.card_le_card hsub
    rw [hpairCard, Finset.card_compl, hfiveCard, Fintype.card_fin] at hcompl
    exact absurd hcompl (by omega)
  · exact hmain xAtom yAtom hUEq hxNeU hxNeV hxNeW hyNeU hyNeV hyNeW hneXY hxV
      hyNotV hyW
  · exact hmain yAtom xAtom (hUEq.trans (congrArg (insert atomU)
      (Finset.pair_comm xAtom yAtom))) hyNeU hyNeV hyNeW hxNeU hxNeV hxNeW hneXY.symm
      hyV hxNotV hxW
  · -- both companions in blockW: blockV starves
    have heraseV : (blockV.erase atomV).card = 2 := by
      rw [Finset.card_erase_of_mem hmemVV, hcardV]
    obtain ⟨sAtom, tAtom, hneST, heraseVEq⟩ := Finset.card_eq_two.mp heraseV
    have hsErase : sAtom ∈ blockV.erase atomV := by
      rw [heraseVEq]
      exact Finset.mem_insert_self _ _
    have htErase : tAtom ∈ blockV.erase atomV := by
      rw [heraseVEq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have hsub : ({sAtom, tAtom} : Finset (Fin 6))
        ⊆ ({atomU, atomV, atomW, xAtom, yAtom} : Finset (Fin 6))ᶜ := by
      intro atom hmem
      have hmemV : atom ∈ blockV := by
        rcases Finset.mem_insert.mp hmem with rfl | hmem2
        · exact (Finset.mem_erase.mp hsErase).2
        · rw [Finset.mem_singleton] at hmem2
          exact hmem2 ▸ (Finset.mem_erase.mp htErase).2
      have hneAnchor : atom ≠ atomV := by
        rcases Finset.mem_insert.mp hmem with rfl | hmem2
        · exact (Finset.mem_erase.mp hsErase).1
        · rw [Finset.mem_singleton] at hmem2
          exact hmem2 ▸ (Finset.mem_erase.mp htErase).1
      rw [Finset.mem_compl]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl | rfl | rfl)
      exacts [hnotUV hmemV, hneAnchor rfl, hnotWV hmemV, hxNotV hmemV, hyNotV hmemV]
    have hfiveCard : ({atomU, atomV, atomW, xAtom, yAtom} : Finset (Fin 6)).card
        = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [hneUV, hneUW, hxNeU.symm, hyNeU.symm]),
        Finset.card_insert_of_notMem (by simp [hneVW, hxNeV.symm, hyNeV.symm]),
        Finset.card_insert_of_notMem (by simp [hxNeW.symm, hyNeW.symm]),
        Finset.card_insert_of_notMem (by simpa using hneXY), Finset.card_singleton]
    have hpairCard : ({sAtom, tAtom} : Finset (Fin 6)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hneST), Finset.card_singleton]
    have hcompl := Finset.card_le_card hsub
    rw [hpairCard, Finset.card_compl, hfiveCard, Fintype.card_fin] at hcompl
    exact absurd hcompl (by omega)

/-- **The double-double extraction.**  A repeated companion target forces the
complementary doubled edge: the shared block completes the pair by one fresh
atom, the loner block by two, and the last block is exactly the three fresh
atoms. -/
theorem family_eq_doubleDoubleForm_of_assignment
    {firstBlock blockShared blockLoner blockLast : Finset (Fin 6)}
    {pairFirst pairSecond lonerAtom : Fin 6}
    (hneP12 : pairFirst ≠ pairSecond) (hneP1L : pairFirst ≠ lonerAtom)
    (hneP2L : pairSecond ≠ lonerAtom)
    (hAtomEq : firstBlock = {pairFirst, pairSecond, lonerAtom})
    (hcardShared : blockShared.card = 3) (hcardLoner : blockLoner.card = 3)
    (hcardLast : blockLast.card = 3)
    (hmemP1S : pairFirst ∈ blockShared) (hmemP2S : pairSecond ∈ blockShared)
    (hnotLS : lonerAtom ∉ blockShared)
    (hnotP1L : pairFirst ∉ blockLoner) (hnotP2L : pairSecond ∉ blockLoner)
    (hmemLL : lonerAtom ∈ blockLoner)
    (hnotP1Last : pairFirst ∉ blockLast) (hnotP2Last : pairSecond ∉ blockLast)
    (hnotLLast : lonerAtom ∉ blockLast)
    (hAllTwo : ∀ atom : Fin 6,
      fourBlockCoverCount firstBlock blockShared blockLoner blockLast atom = 2) :
    ∃ sharedThird lonerSecond lonerThird : Fin 6,
      sharedThird ≠ pairFirst ∧ sharedThird ≠ pairSecond ∧ sharedThird ≠ lonerAtom
        ∧ lonerSecond ≠ pairFirst ∧ lonerSecond ≠ pairSecond
        ∧ lonerSecond ≠ lonerAtom
        ∧ lonerThird ≠ pairFirst ∧ lonerThird ≠ pairSecond ∧ lonerThird ≠ lonerAtom
        ∧ sharedThird ≠ lonerSecond ∧ sharedThird ≠ lonerThird
        ∧ lonerSecond ≠ lonerThird
        ∧ blockShared = {pairFirst, pairSecond, sharedThird}
        ∧ blockLoner = {lonerAtom, lonerSecond, lonerThird}
        ∧ blockLast = {sharedThird, lonerSecond, lonerThird} := by
  obtain ⟨sharedThird, hpNeP1, hpNeP2, hSharedEq⟩ :=
    exists_third_of_pair_mem_card_three hcardShared hneP12 hmemP1S hmemP2S
  have hpShared : sharedThird ∈ blockShared := by
    rw [hSharedEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self _))))
  have hpNeL : sharedThird ≠ lonerAtom := fun hcontra => hnotLS (hcontra ▸ hpShared)
  have hpNotFirst : sharedThird ∉ firstBlock := by
    rw [hAtomEq]
    simp [hpNeP1, hpNeP2, hpNeL]
  have heraseL : (blockLoner.erase lonerAtom).card = 2 := by
    rw [Finset.card_erase_of_mem hmemLL, hcardLoner]
  obtain ⟨lonerSecond, lonerThird, hneQR, heraseLEq⟩ := Finset.card_eq_two.mp heraseL
  have hqErase : lonerSecond ∈ blockLoner.erase lonerAtom := by
    rw [heraseLEq]
    exact Finset.mem_insert_self _ _
  have hrErase : lonerThird ∈ blockLoner.erase lonerAtom := by
    rw [heraseLEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hqNeL : lonerSecond ≠ lonerAtom := (Finset.mem_erase.mp hqErase).1
  have hrNeL : lonerThird ≠ lonerAtom := (Finset.mem_erase.mp hrErase).1
  have hqLoner : lonerSecond ∈ blockLoner := (Finset.mem_erase.mp hqErase).2
  have hrLoner : lonerThird ∈ blockLoner := (Finset.mem_erase.mp hrErase).2
  have hLonerEq : blockLoner = {lonerAtom, lonerSecond, lonerThird} := by
    rw [← Finset.insert_erase hmemLL, heraseLEq]
  have hqNeP1 : lonerSecond ≠ pairFirst := fun hcontra => hnotP1L (hcontra ▸ hqLoner)
  have hqNeP2 : lonerSecond ≠ pairSecond := fun hcontra => hnotP2L (hcontra ▸ hqLoner)
  have hrNeP1 : lonerThird ≠ pairFirst := fun hcontra => hnotP1L (hcontra ▸ hrLoner)
  have hrNeP2 : lonerThird ≠ pairSecond := fun hcontra => hnotP2L (hcontra ▸ hrLoner)
  have hqNotFirst : lonerSecond ∉ firstBlock := by
    rw [hAtomEq]
    simp [hqNeP1, hqNeP2, hqNeL]
  have hrNotFirst : lonerThird ∉ firstBlock := by
    rw [hAtomEq]
    simp [hrNeP1, hrNeP2, hrNeL]
  have hLastEq : blockLast = ({pairFirst, pairSecond, lonerAtom} :
      Finset (Fin 6))ᶜ := by
    have hsub : blockLast ⊆ ({pairFirst, pairSecond, lonerAtom} :
        Finset (Fin 6))ᶜ := by
      intro atom hmem
      rw [Finset.mem_compl]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl)
      exacts [hnotP1Last hmem, hnotP2Last hmem, hnotLLast hmem]
    have htripleCard : ({pairFirst, pairSecond, lonerAtom} : Finset (Fin 6)).card
        = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hneP12, hneP1L]),
        Finset.card_insert_of_notMem (by simp [hneP2L]), Finset.card_singleton]
    exact Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_compl, htripleCard, Fintype.card_fin, hcardLast])
  have hpLast : sharedThird ∈ blockLast := by
    rw [hLastEq, Finset.mem_compl]
    simp [hpNeP1, hpNeP2, hpNeL]
  have hqLast : lonerSecond ∈ blockLast := by
    rw [hLastEq, Finset.mem_compl]
    simp [hqNeP1, hqNeP2, hqNeL]
  have hrLast : lonerThird ∈ blockLast := by
    rw [hLastEq, Finset.mem_compl]
    simp [hrNeP1, hrNeP2, hrNeL]
  have hqNotShared : lonerSecond ∉ blockShared := by
    rcases fourBlockCoverCount_eq_two_inversion (hAllTwo lonerSecond) with
        ⟨hf, _, _, _⟩ | ⟨hf, _, _, _⟩ | ⟨hf, _, _, _⟩ | ⟨_, _, _, hd⟩
      | ⟨_, _, hc, _⟩ | ⟨_, hb, _, _⟩
    exacts [absurd hf hqNotFirst, absurd hf hqNotFirst, absurd hf hqNotFirst,
      absurd hqLast hd, absurd hqLoner hc, hb]
  have hrNotShared : lonerThird ∉ blockShared := by
    rcases fourBlockCoverCount_eq_two_inversion (hAllTwo lonerThird) with
        ⟨hf, _, _, _⟩ | ⟨hf, _, _, _⟩ | ⟨hf, _, _, _⟩ | ⟨_, _, _, hd⟩
      | ⟨_, _, hc, _⟩ | ⟨_, hb, _, _⟩
    exacts [absurd hf hrNotFirst, absurd hf hrNotFirst, absurd hf hrNotFirst,
      absurd hrLast hd, absurd hrLoner hc, hb]
  have hpNeQ : sharedThird ≠ lonerSecond := fun hcontra =>
    hqNotShared (hcontra ▸ hpShared)
  have hpNeR : sharedThird ≠ lonerThird := fun hcontra =>
    hrNotShared (hcontra ▸ hpShared)
  have hLastTripleEq : blockLast = {sharedThird, lonerSecond, lonerThird} :=
    eq_triple_of_mem_mem_mem_card_three hcardLast hpNeQ hpNeR hneQR hpLast hqLast
      hrLast
  exact ⟨sharedThird, lonerSecond, lonerThird, hpNeP1, hpNeP2, hpNeL, hqNeP1, hqNeP2,
    hqNeL, hrNeP1, hrNeP2, hrNeL, hpNeQ, hpNeR, hneQR, hSharedEq, hLonerEq,
    hLastTripleEq⟩

/-- The canonical tetrahedron family: atoms are the six edges of `K4`, blocks
the four vertex stars. -/
def canonicalTetrahedronFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}}

/-- The canonical double-double family: two block pairs each sharing two
atoms. -/
def canonicalDoubleDoubleFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {2, 4, 5}, {3, 4, 5}}

/-- **THE ALL-DOUBLE CAPSTONE.**  Any four-block family with profile
`(0,0,6,0)` relabels onto the canonical tetrahedron or the canonical
double-double. -/
theorem exists_map_family_eq_canonicalTetrahedron_or_doubleDouble_of_profile
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock)
    (hcardOne : firstBlock.card = 3) (hcardTwo : secondBlock.card = 3)
    (hcardThree : thirdBlock.card = 3) (hcardFour : fourthBlock.card = 3)
    (hdoubleClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2
      = 6) :
    ∃ relabelPerm : Equiv.Perm (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalTetrahedronFamily
        ∨ ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalDoubleDoubleFamily := by
  classical
  have hAllTwo := count_eq_two_of_doubleClassCard_six hdoubleClass
  obtain ⟨atomU, atomV, atomW, hneUV, hneUW, hneVW, hAtomEq⟩ :=
    Finset.card_eq_three.mp hcardOne
  rcases exists_companionAssignment_of_all_count_two hneOneTwo hneOneThree hneOneFour
      hcardTwo hcardThree hcardFour hneUV hneUW hneVW hAtomEq (hAllTwo atomU)
      (hAllTwo atomV) (hAllTwo atomW) with
    ⟨blockU, blockV, blockW, hSetEq, hCountEq, hcardU, hcardV, hcardW, hmemUU, hnotUV,
        hnotUW, hnotVU, hmemVV, hnotVW, hnotWU, hnotWV, hmemWW⟩
    | ⟨pairFirst, pairSecond, lonerAtom, blockShared, blockLoner, blockLast,
        hAtomEqPerm, hneP12, hneP1L, hneP2L, hSetEq, hCountEq, hcardShared, hcardLoner,
        hcardLast, hmemP1S, hmemP2S, hnotLS, hnotP1L, hnotP2L, hmemLL, hnotP1Last,
        hnotP2Last, hnotLLast⟩
  · obtain ⟨edgeUV, edgeUW, edgeVW, heUVNeU, heUVNeV, heUVNeW, heUWNeU, heUWNeV,
        heUWNeW, heVWNeU, heVWNeV, heVWNeW, heUVNeUW, heUVNeVW, heUWNeVW, hUEq, hVEq,
        hWEq⟩ :=
      family_eq_tetrahedronForm_of_assignment hneUV hneUW hneVW hAtomEq hcardU hcardV
        hcardW hmemUU hnotUV hnotUW hnotVU hmemVV hnotVW hnotWU hnotWV hmemWW
        (fun atom => (hCountEq atom).trans (hAllTwo atom))
    have hinj : Function.Injective
        ![atomU, atomV, atomW, edgeUV, edgeUW, edgeVW] :=
      injective_sixAtomAssignment hneUV hneUW heUVNeU.symm heUWNeU.symm heVWNeU.symm
        hneVW heUVNeV.symm heUWNeV.symm heVWNeV.symm heUVNeW.symm heUWNeW.symm
        heVWNeW.symm heUVNeUW heUVNeVW heUWNeVW
    let atomAssignment : Equiv.Perm (Fin 6) :=
      Equiv.ofBijective ![atomU, atomV, atomW, edgeUV, edgeUW, edgeVW]
        (Finite.injective_iff_bijective.mp hinj)
    have hpiU : atomAssignment.symm atomU = 0 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiV : atomAssignment.symm atomV = 1 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiW : atomAssignment.symm atomW = 2 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiUV : atomAssignment.symm edgeUV = 3 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiUW : atomAssignment.symm edgeUW = 4 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiVW : atomAssignment.symm edgeVW = 5 := by
      rw [Equiv.symm_apply_eq]; rfl
    refine ⟨atomAssignment.symm, Or.inl ?_⟩
    rw [hSetEq, hAtomEq, hUEq, hVEq, hWEq]
    simp only [Finset.image_insert, Finset.image_singleton]
    rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
      map_triple_toEmbedding, hpiU, hpiV, hpiW, hpiUV, hpiUW, hpiVW]
    rfl
  · obtain ⟨sharedThird, lonerSecond, lonerThird, hpNeP1, hpNeP2, hpNeL, hqNeP1,
        hqNeP2, hqNeL, hrNeP1, hrNeP2, hrNeL, hpNeQ, hpNeR, hneQR, hSharedEq, hLonerEq,
        hLastEq⟩ :=
      family_eq_doubleDoubleForm_of_assignment hneP12 hneP1L hneP2L hAtomEqPerm
        hcardShared hcardLoner hcardLast hmemP1S hmemP2S hnotLS hnotP1L hnotP2L hmemLL
        hnotP1Last hnotP2Last hnotLLast
        (fun atom => (hCountEq atom).trans (hAllTwo atom))
    have hinj : Function.Injective
        ![pairFirst, pairSecond, lonerAtom, sharedThird, lonerSecond, lonerThird] :=
      injective_sixAtomAssignment hneP12 hneP1L hpNeP1.symm hqNeP1.symm hrNeP1.symm
        hneP2L hpNeP2.symm hqNeP2.symm hrNeP2.symm hpNeL.symm hqNeL.symm hrNeL.symm
        hpNeQ hpNeR hneQR
    let atomAssignment : Equiv.Perm (Fin 6) :=
      Equiv.ofBijective
        ![pairFirst, pairSecond, lonerAtom, sharedThird, lonerSecond, lonerThird]
        (Finite.injective_iff_bijective.mp hinj)
    have hpiP1 : atomAssignment.symm pairFirst = 0 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiP2 : atomAssignment.symm pairSecond = 1 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiL : atomAssignment.symm lonerAtom = 2 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiP : atomAssignment.symm sharedThird = 3 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiQ : atomAssignment.symm lonerSecond = 4 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiR : atomAssignment.symm lonerThird = 5 := by
      rw [Equiv.symm_apply_eq]; rfl
    refine ⟨atomAssignment.symm, Or.inr ?_⟩
    rw [hSetEq, hAtomEqPerm, hSharedEq, hLonerEq, hLastEq]
    simp only [Finset.image_insert, Finset.image_singleton]
    rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
      map_triple_toEmbedding, hpiP1, hpiP2, hpiL, hpiP, hpiQ, hpiR]
    rfl

end Gtz

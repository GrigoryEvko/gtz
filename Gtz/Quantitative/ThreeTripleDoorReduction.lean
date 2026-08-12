import Mathlib
import Gtz.Quantitative.QuadDoorDispatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The three-triple door: profile (0,3,0,3) closed end to end

Three triply-covered atoms and three singly-covered atoms admit exactly one
shape: each triple atom misses exactly one block, two coinciding misses would
force a second all-triple block colliding with the first, so the misses
biject with the three mixed blocks -- one block holds all three triple atoms
and each mixed block is a triple-atom pair completed by its own single atom.
An explicit permutation carries the family onto the canonical
`{{0,1,2},{1,2,5},{0,2,4},{0,1,3}}`.  Fifth census door closed end to end,
the first without a quadruple atom.
-/

namespace Gtz

/-- A card-three block through three distinct named atoms is exactly their
triple. -/
theorem eq_triple_of_mem_mem_mem_card_three {block : Finset (Fin 6)}
    (hcard : block.card = 3) {firstAtom secondAtom thirdAtom : Fin 6}
    (hneOneTwo : firstAtom ≠ secondAtom) (hneOneThree : firstAtom ≠ thirdAtom)
    (hneTwoThree : secondAtom ≠ thirdAtom) (hfirst : firstAtom ∈ block)
    (hsecond : secondAtom ∈ block) (hthird : thirdAtom ∈ block) :
    block = {firstAtom, secondAtom, thirdAtom} := by
  have hsubset : ({firstAtom, secondAtom, thirdAtom} : Finset (Fin 6)) ⊆ block := by
    intro atom hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem
    · exact hfirst
    · rcases Finset.mem_insert.mp hmem with rfl | hmem
      · exact hsecond
      · rw [Finset.mem_singleton] at hmem
        exact hmem ▸ hthird
  have htripleCard : ({firstAtom, secondAtom, thirdAtom} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hneOneTwo, hneOneThree]),
      Finset.card_insert_of_notMem (by simp [hneTwoThree]), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsubset (by rw [hcard, htripleCard])).symm

/-- Membership in any of the four blocks puts the cover count at one or
more. -/
theorem one_le_fourBlockCoverCount_of_mem
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)} {atomIndex : Fin 6}
    (hmem : atomIndex ∈ firstBlock ∨ atomIndex ∈ secondBlock
      ∨ atomIndex ∈ thirdBlock ∨ atomIndex ∈ fourthBlock) :
    1 ≤ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex := by
  unfold fourBlockCoverCount
  split_ifs <;> first | omega | tauto

/-- An empty count class forbids its count value everywhere. -/
theorem count_ne_of_classCard_zero
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)} {countValue : ℕ}
    (hclass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock countValue
      = 0) (atomIndex : Fin 6) :
    fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
      ≠ countValue := by
  intro hcontra
  rw [fourBlockCountClass, Finset.card_eq_zero] at hclass
  have hmem : atomIndex ∈ Finset.univ.filter fun atom =>
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom
        = countValue :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ atomIndex, hcontra⟩
  rw [hclass] at hmem
  exact absurd hmem (Finset.notMem_empty atomIndex)

/-- **The miss-assignment normalization.**  Three triply-covered atoms miss
pairwise-distinct blocks -- coinciding misses collide two all-triple blocks --
so the family renormalizes as one all-triple block and three one-miss blocks,
with cover counts carried verbatim. -/
theorem exists_missAssignment_of_three_count_three
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock) (hneTwoThree : secondBlock ≠ thirdBlock)
    (hneTwoFour : secondBlock ≠ fourthBlock) (hneThreeFour : thirdBlock ≠ fourthBlock)
    (hcardOne : firstBlock.card = 3) (hcardTwo : secondBlock.card = 3)
    (hcardThree : thirdBlock.card = 3) (hcardFour : fourthBlock.card = 3)
    {tripleFirst tripleSecond tripleThird : Fin 6}
    (hneT12 : tripleFirst ≠ tripleSecond) (hneT13 : tripleFirst ≠ tripleThird)
    (hneT23 : tripleSecond ≠ tripleThird)
    (hcount1 : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
      tripleFirst = 3)
    (hcount2 : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
      tripleSecond = 3)
    (hcount3 : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
      tripleThird = 3) :
    ∃ allTripleBlock missFirstBlock missSecondBlock missThirdBlock : Finset (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} : Finset (Finset (Fin 6)))
          = {allTripleBlock, missFirstBlock, missSecondBlock, missThirdBlock}
        ∧ (∀ atom : Fin 6, fourBlockCoverCount allTripleBlock missFirstBlock
            missSecondBlock missThirdBlock atom
              = fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom)
        ∧ allTripleBlock.card = 3 ∧ missFirstBlock.card = 3 ∧ missSecondBlock.card = 3
        ∧ missThirdBlock.card = 3
        ∧ missFirstBlock ≠ missSecondBlock ∧ missFirstBlock ≠ missThirdBlock
        ∧ missSecondBlock ≠ missThirdBlock
        ∧ tripleFirst ∈ allTripleBlock ∧ tripleSecond ∈ allTripleBlock
        ∧ tripleThird ∈ allTripleBlock
        ∧ tripleFirst ∉ missFirstBlock ∧ tripleSecond ∈ missFirstBlock
        ∧ tripleThird ∈ missFirstBlock
        ∧ tripleFirst ∈ missSecondBlock ∧ tripleSecond ∉ missSecondBlock
        ∧ tripleThird ∈ missSecondBlock
        ∧ tripleFirst ∈ missThirdBlock ∧ tripleSecond ∈ missThirdBlock
        ∧ tripleThird ∉ missThirdBlock := by
  rcases fourBlockCoverCount_eq_three_inversion hcount1 with
      ⟨ht1First, ht1Second, ht1Third, ht1Fourth⟩
    | ⟨ht1First, ht1Second, ht1Third, ht1Fourth⟩
    | ⟨ht1First, ht1Second, ht1Third, ht1Fourth⟩
    | ⟨ht1First, ht1Second, ht1Third, ht1Fourth⟩ <;>
    rcases fourBlockCoverCount_eq_three_inversion hcount2 with
        ⟨ht2First, ht2Second, ht2Third, ht2Fourth⟩
      | ⟨ht2First, ht2Second, ht2Third, ht2Fourth⟩
      | ⟨ht2First, ht2Second, ht2Third, ht2Fourth⟩
      | ⟨ht2First, ht2Second, ht2Third, ht2Fourth⟩ <;>
    rcases fourBlockCoverCount_eq_three_inversion hcount3 with
        ⟨ht3First, ht3Second, ht3Third, ht3Fourth⟩
      | ⟨ht3First, ht3Second, ht3Third, ht3Fourth⟩
      | ⟨ht3First, ht3Second, ht3Third, ht3Fourth⟩
      | ⟨ht3First, ht3Second, ht3Third, ht3Fourth⟩ <;>
    first
    | exact absurd ((eq_triple_of_mem_mem_mem_card_three hcardOne hneT12 hneT13 hneT23
        ht1First ht2First ht3First).trans
        (eq_triple_of_mem_mem_mem_card_three hcardTwo hneT12 hneT13 hneT23
          ht1Second ht2Second ht3Second).symm) hneOneTwo
    | exact absurd ((eq_triple_of_mem_mem_mem_card_three hcardOne hneT12 hneT13 hneT23
        ht1First ht2First ht3First).trans
        (eq_triple_of_mem_mem_mem_card_three hcardThree hneT12 hneT13 hneT23
          ht1Third ht2Third ht3Third).symm) hneOneThree
    | exact absurd ((eq_triple_of_mem_mem_mem_card_three hcardOne hneT12 hneT13 hneT23
        ht1First ht2First ht3First).trans
        (eq_triple_of_mem_mem_mem_card_three hcardFour hneT12 hneT13 hneT23
          ht1Fourth ht2Fourth ht3Fourth).symm) hneOneFour
    | exact absurd ((eq_triple_of_mem_mem_mem_card_three hcardTwo hneT12 hneT13 hneT23
        ht1Second ht2Second ht3Second).trans
        (eq_triple_of_mem_mem_mem_card_three hcardThree hneT12 hneT13 hneT23
          ht1Third ht2Third ht3Third).symm) hneTwoThree
    | exact absurd ((eq_triple_of_mem_mem_mem_card_three hcardTwo hneT12 hneT13 hneT23
        ht1Second ht2Second ht3Second).trans
        (eq_triple_of_mem_mem_mem_card_three hcardFour hneT12 hneT13 hneT23
          ht1Fourth ht2Fourth ht3Fourth).symm) hneTwoFour
    | exact absurd ((eq_triple_of_mem_mem_mem_card_three hcardThree hneT12 hneT13 hneT23
        ht1Third ht2Third ht3Third).trans
        (eq_triple_of_mem_mem_mem_card_three hcardFour hneT12 hneT13 hneT23
          ht1Fourth ht2Fourth ht3Fourth).symm) hneThreeFour
    | (refine ⟨fourthBlock, firstBlock, secondBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardOne, hcardTwo, hcardThree,
        hneOneTwo, hneOneThree, hneTwoThree, ht1Fourth, ht2Fourth, ht3Fourth, ht1First, ht2First, ht3First, ht1Second, ht2Second, ht3Second, ht1Third, ht2Third, ht3Third⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_first_second firstBlock fourthBlock secondBlock thirdBlock])
    | (refine ⟨thirdBlock, firstBlock, secondBlock, fourthBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardOne, hcardTwo, hcardFour,
        hneOneTwo, hneOneFour, hneTwoFour, ht1Third, ht2Third, ht3Third, ht1First, ht2First, ht3First, ht1Second, ht2Second, ht3Second, ht1Fourth, ht2Fourth, ht3Fourth⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock])
    | (refine ⟨fourthBlock, firstBlock, thirdBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardOne, hcardThree, hcardTwo,
        hneOneThree, hneOneTwo, hneTwoThree.symm, ht1Fourth, ht2Fourth, ht3Fourth, ht1First, ht2First, ht3First, ht1Third, ht2Third, ht3Third, ht1Second, ht2Second, ht3Second⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_first_second firstBlock fourthBlock secondBlock thirdBlock,
         quadSet_swap_third_fourth fourthBlock firstBlock secondBlock thirdBlock])
    | (refine ⟨secondBlock, firstBlock, thirdBlock, fourthBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardOne, hcardThree, hcardFour,
        hneOneThree, hneOneFour, hneThreeFour, ht1Second, ht2Second, ht3Second, ht1First, ht2First, ht3First, ht1Third, ht2Third, ht3Third, ht1Fourth, ht2Fourth, ht3Fourth⟩
       rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock])
    | (refine ⟨thirdBlock, firstBlock, fourthBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardOne, hcardFour, hcardTwo,
        hneOneFour, hneOneTwo, hneTwoFour.symm, ht1Third, ht2Third, ht3Third, ht1First, ht2First, ht3First, ht1Fourth, ht2Fourth, ht3Fourth, ht1Second, ht2Second, ht3Second⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock,
         quadSet_swap_third_fourth thirdBlock firstBlock secondBlock fourthBlock])
    | (refine ⟨secondBlock, firstBlock, fourthBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardOne, hcardFour, hcardThree,
        hneOneFour, hneOneThree, hneThreeFour.symm, ht1Second, ht2Second, ht3Second, ht1First, ht2First, ht3First, ht1Fourth, ht2Fourth, ht3Fourth, ht1Third, ht2Third, ht3Third⟩
       rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth secondBlock firstBlock thirdBlock fourthBlock])
    | (refine ⟨fourthBlock, secondBlock, firstBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardTwo, hcardOne, hcardThree,
        hneOneTwo.symm, hneTwoThree, hneOneThree, ht1Fourth, ht2Fourth, ht3Fourth, ht1Second, ht2Second, ht3Second, ht1First, ht2First, ht3First, ht1Third, ht2Third, ht3Third⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_first_second firstBlock fourthBlock secondBlock thirdBlock,
         quadSet_swap_second_third fourthBlock firstBlock secondBlock thirdBlock])
    | (refine ⟨thirdBlock, secondBlock, firstBlock, fourthBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardTwo, hcardOne, hcardFour,
        hneOneTwo.symm, hneTwoFour, hneOneFour, ht1Third, ht2Third, ht3Third, ht1Second, ht2Second, ht3Second, ht1First, ht2First, ht3First, ht1Fourth, ht2Fourth, ht3Fourth⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock,
         quadSet_swap_second_third thirdBlock firstBlock secondBlock fourthBlock])
    | (refine ⟨fourthBlock, secondBlock, thirdBlock, firstBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardTwo, hcardThree, hcardOne,
        hneTwoThree, hneOneTwo.symm, hneOneThree.symm, ht1Fourth, ht2Fourth, ht3Fourth, ht1Second, ht2Second, ht3Second, ht1Third, ht2Third, ht3Third, ht1First, ht2First, ht3First⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_first_second firstBlock fourthBlock secondBlock thirdBlock,
         quadSet_swap_second_third fourthBlock firstBlock secondBlock thirdBlock,
         quadSet_swap_third_fourth fourthBlock secondBlock firstBlock thirdBlock])
    | exact ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, rfl,
        fun atom => rfl, hcardOne, hcardTwo, hcardThree, hcardFour,
        hneTwoThree, hneTwoFour, hneThreeFour, ht1First, ht2First, ht3First, ht1Second, ht2Second, ht3Second, ht1Third, ht2Third, ht3Third, ht1Fourth, ht2Fourth, ht3Fourth⟩
    | (refine ⟨thirdBlock, secondBlock, fourthBlock, firstBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardTwo, hcardFour, hcardOne,
        hneTwoFour, hneOneTwo.symm, hneOneFour.symm, ht1Third, ht2Third, ht3Third, ht1Second, ht2Second, ht3Second, ht1Fourth, ht2Fourth, ht3Fourth, ht1First, ht2First, ht3First⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock,
         quadSet_swap_second_third thirdBlock firstBlock secondBlock fourthBlock,
         quadSet_swap_third_fourth thirdBlock secondBlock firstBlock fourthBlock])
    | (refine ⟨firstBlock, secondBlock, fourthBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardTwo, hcardFour, hcardThree,
        hneTwoFour, hneTwoThree, hneThreeFour.symm, ht1First, ht2First, ht3First, ht1Second, ht2Second, ht3Second, ht1Fourth, ht2Fourth, ht3Fourth, ht1Third, ht2Third, ht3Third⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock])
    | (refine ⟨fourthBlock, thirdBlock, firstBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardThree, hcardOne, hcardTwo,
        hneOneThree.symm, hneTwoThree.symm, hneOneTwo, ht1Fourth, ht2Fourth, ht3Fourth, ht1Third, ht2Third, ht3Third, ht1First, ht2First, ht3First, ht1Second, ht2Second, ht3Second⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_first_second firstBlock fourthBlock secondBlock thirdBlock,
         quadSet_swap_third_fourth fourthBlock firstBlock secondBlock thirdBlock,
         quadSet_swap_second_third fourthBlock firstBlock thirdBlock secondBlock])
    | (refine ⟨secondBlock, thirdBlock, firstBlock, fourthBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardThree, hcardOne, hcardFour,
        hneOneThree.symm, hneThreeFour, hneOneFour, ht1Second, ht2Second, ht3Second, ht1Third, ht2Third, ht3Third, ht1First, ht2First, ht3First, ht1Fourth, ht2Fourth, ht3Fourth⟩
       rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third secondBlock firstBlock thirdBlock fourthBlock])
    | (refine ⟨fourthBlock, thirdBlock, secondBlock, firstBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardThree, hcardTwo, hcardOne,
        hneTwoThree.symm, hneOneThree.symm, hneOneTwo.symm, ht1Fourth, ht2Fourth, ht3Fourth, ht1Third, ht2Third, ht3Third, ht1Second, ht2Second, ht3Second, ht1First, ht2First, ht3First⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_first_second firstBlock fourthBlock secondBlock thirdBlock,
         quadSet_swap_third_fourth fourthBlock firstBlock secondBlock thirdBlock,
         quadSet_swap_second_third fourthBlock firstBlock thirdBlock secondBlock,
         quadSet_swap_third_fourth fourthBlock thirdBlock firstBlock secondBlock])
    | (refine ⟨firstBlock, thirdBlock, secondBlock, fourthBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardThree, hcardTwo, hcardFour,
        hneTwoThree.symm, hneThreeFour, hneTwoFour, ht1First, ht2First, ht3First, ht1Third, ht2Third, ht3Third, ht1Second, ht2Second, ht3Second, ht1Fourth, ht2Fourth, ht3Fourth⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock])
    | (refine ⟨secondBlock, thirdBlock, fourthBlock, firstBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardThree, hcardFour, hcardOne,
        hneThreeFour, hneOneThree.symm, hneOneFour.symm, ht1Second, ht2Second, ht3Second, ht1Third, ht2Third, ht3Third, ht1Fourth, ht2Fourth, ht3Fourth, ht1First, ht2First, ht3First⟩
       rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third secondBlock firstBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth secondBlock thirdBlock firstBlock fourthBlock])
    | (refine ⟨firstBlock, thirdBlock, fourthBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardThree, hcardFour, hcardTwo,
        hneThreeFour, hneTwoThree.symm, hneTwoFour.symm, ht1First, ht2First, ht3First, ht1Third, ht2Third, ht3Third, ht1Fourth, ht2Fourth, ht3Fourth, ht1Second, ht2Second, ht3Second⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock])
    | (refine ⟨thirdBlock, fourthBlock, firstBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardFour, hcardOne, hcardTwo,
        hneOneFour.symm, hneTwoFour.symm, hneOneTwo, ht1Third, ht2Third, ht3Third, ht1Fourth, ht2Fourth, ht3Fourth, ht1First, ht2First, ht3First, ht1Second, ht2Second, ht3Second⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock,
         quadSet_swap_third_fourth thirdBlock firstBlock secondBlock fourthBlock,
         quadSet_swap_second_third thirdBlock firstBlock fourthBlock secondBlock])
    | (refine ⟨secondBlock, fourthBlock, firstBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardFour, hcardOne, hcardThree,
        hneOneFour.symm, hneThreeFour.symm, hneOneThree, ht1Second, ht2Second, ht3Second, ht1Fourth, ht2Fourth, ht3Fourth, ht1First, ht2First, ht3First, ht1Third, ht2Third, ht3Third⟩
       rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth secondBlock firstBlock thirdBlock fourthBlock,
         quadSet_swap_second_third secondBlock firstBlock fourthBlock thirdBlock])
    | (refine ⟨thirdBlock, fourthBlock, secondBlock, firstBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardFour, hcardTwo, hcardOne,
        hneTwoFour.symm, hneOneFour.symm, hneOneTwo.symm, ht1Third, ht2Third, ht3Third, ht1Fourth, ht2Fourth, ht3Fourth, ht1Second, ht2Second, ht3Second, ht1First, ht2First, ht3First⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock,
         quadSet_swap_third_fourth thirdBlock firstBlock secondBlock fourthBlock,
         quadSet_swap_second_third thirdBlock firstBlock fourthBlock secondBlock,
         quadSet_swap_third_fourth thirdBlock fourthBlock firstBlock secondBlock])
    | (refine ⟨firstBlock, fourthBlock, secondBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardFour, hcardTwo, hcardThree,
        hneTwoFour.symm, hneThreeFour.symm, hneTwoThree, ht1First, ht2First, ht3First, ht1Fourth, ht2Fourth, ht3Fourth, ht1Second, ht2Second, ht3Second, ht1Third, ht2Third, ht3Third⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock])
    | (refine ⟨secondBlock, fourthBlock, thirdBlock, firstBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardFour, hcardThree, hcardOne,
        hneThreeFour.symm, hneOneFour.symm, hneOneThree.symm, ht1Second, ht2Second, ht3Second, ht1Fourth, ht2Fourth, ht3Fourth, ht1Third, ht2Third, ht3Third, ht1First, ht2First, ht3First⟩
       rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth secondBlock firstBlock thirdBlock fourthBlock,
         quadSet_swap_second_third secondBlock firstBlock fourthBlock thirdBlock,
         quadSet_swap_third_fourth secondBlock fourthBlock firstBlock thirdBlock])
    | (refine ⟨firstBlock, fourthBlock, thirdBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardFour, hcardThree, hcardTwo,
        hneThreeFour.symm, hneTwoFour.symm, hneTwoThree.symm, ht1First, ht2First, ht3First, ht1Fourth, ht2Fourth, ht3Fourth, ht1Third, ht2Third, ht3Third, ht1Second, ht2Second, ht3Second⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_third_fourth firstBlock fourthBlock secondBlock thirdBlock])

/-- **The three-triple extraction.**  A miss-assigned family IS the
three-triple shape: the all-triple block plus each triple pair completed by
its own singly-covered atom. -/
theorem family_eq_threeTripleForm_of_missAssignment
    {allTripleBlock missFirstBlock missSecondBlock missThirdBlock : Finset (Fin 6)}
    (hcardAll : allTripleBlock.card = 3) (hcardMissFirst : missFirstBlock.card = 3)
    (hcardMissSecond : missSecondBlock.card = 3) (hcardMissThird : missThirdBlock.card = 3)
    {tripleFirst tripleSecond tripleThird : Fin 6}
    (hneT12 : tripleFirst ≠ tripleSecond) (hneT13 : tripleFirst ≠ tripleThird)
    (hneT23 : tripleSecond ≠ tripleThird)
    (hmemAll1 : tripleFirst ∈ allTripleBlock) (hmemAll2 : tripleSecond ∈ allTripleBlock)
    (hmemAll3 : tripleThird ∈ allTripleBlock)
    (hmiss11 : tripleFirst ∉ missFirstBlock) (hmem12 : tripleSecond ∈ missFirstBlock)
    (hmem13 : tripleThird ∈ missFirstBlock)
    (hmem21 : tripleFirst ∈ missSecondBlock) (hmiss22 : tripleSecond ∉ missSecondBlock)
    (hmem23 : tripleThird ∈ missSecondBlock)
    (hmem31 : tripleFirst ∈ missThirdBlock) (hmem32 : tripleSecond ∈ missThirdBlock)
    (hmiss33 : tripleThird ∉ missThirdBlock)
    (hthreeOnly : ∀ atom : Fin 6, fourBlockCoverCount allTripleBlock missFirstBlock
        missSecondBlock missThirdBlock atom = 3
      → atom = tripleFirst ∨ atom = tripleSecond ∨ atom = tripleThird)
    (hTwoNone : ∀ atom : Fin 6, fourBlockCoverCount allTripleBlock missFirstBlock
      missSecondBlock missThirdBlock atom ≠ 2)
    (hFourNone : ∀ atom : Fin 6, fourBlockCoverCount allTripleBlock missFirstBlock
      missSecondBlock missThirdBlock atom ≠ 4) :
    ∃ singleFirst singleSecond singleThird : Fin 6,
      singleFirst ≠ singleSecond ∧ singleFirst ≠ singleThird
        ∧ singleSecond ≠ singleThird
        ∧ singleFirst ≠ tripleFirst ∧ singleFirst ≠ tripleSecond
        ∧ singleFirst ≠ tripleThird
        ∧ singleSecond ≠ tripleFirst ∧ singleSecond ≠ tripleSecond
        ∧ singleSecond ≠ tripleThird
        ∧ singleThird ≠ tripleFirst ∧ singleThird ≠ tripleSecond
        ∧ singleThird ≠ tripleThird
        ∧ ({allTripleBlock, missFirstBlock, missSecondBlock, missThirdBlock} :
              Finset (Finset (Fin 6)))
            = {{tripleFirst, tripleSecond, tripleThird},
               {tripleSecond, tripleThird, singleFirst},
               {tripleFirst, tripleThird, singleSecond},
               {tripleFirst, tripleSecond, singleThird}} := by
  have hAllEq : allTripleBlock = {tripleFirst, tripleSecond, tripleThird} :=
    eq_triple_of_mem_mem_mem_card_three hcardAll hneT12 hneT13 hneT23 hmemAll1
      hmemAll2 hmemAll3
  obtain ⟨singleFirst, hs1Ne2, hs1Ne3, hMissFirstEq⟩ :=
    exists_third_of_pair_mem_card_three hcardMissFirst hneT23 hmem12 hmem13
  obtain ⟨singleSecond, hs2Ne1, hs2Ne3, hMissSecondEq⟩ :=
    exists_third_of_pair_mem_card_three hcardMissSecond hneT13 hmem21 hmem23
  obtain ⟨singleThird, hs3Ne1, hs3Ne2, hMissThirdEq⟩ :=
    exists_third_of_pair_mem_card_three hcardMissThird hneT12 hmem31 hmem32
  have hs1Mem : singleFirst ∈ missFirstBlock := by
    rw [hMissFirstEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self _))))
  have hs2Mem : singleSecond ∈ missSecondBlock := by
    rw [hMissSecondEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self _))))
  have hs3Mem : singleThird ∈ missThirdBlock := by
    rw [hMissThirdEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self _))))
  have hs1Ne1 : singleFirst ≠ tripleFirst := by
    intro hcontra
    exact hmiss11 (hcontra ▸ hs1Mem)
  have hs2Ne2 : singleSecond ≠ tripleSecond := by
    intro hcontra
    exact hmiss22 (hcontra ▸ hs2Mem)
  have hs3Ne3 : singleThird ≠ tripleThird := by
    intro hcontra
    exact hmiss33 (hcontra ▸ hs3Mem)
  have hcountOne : ∀ single : Fin 6, single ≠ tripleFirst → single ≠ tripleSecond
      → single ≠ tripleThird
      → (single ∈ allTripleBlock ∨ single ∈ missFirstBlock
        ∨ single ∈ missSecondBlock ∨ single ∈ missThirdBlock)
      → fourBlockCoverCount allTripleBlock missFirstBlock missSecondBlock
          missThirdBlock single = 1 := by
    intro single hne1 hne2 hne3 hmem
    have hge := one_le_fourBlockCoverCount_of_mem hmem
    have hle := fourBlockCoverCount_le_four allTripleBlock missFirstBlock
      missSecondBlock missThirdBlock single
    have hneThree : fourBlockCoverCount allTripleBlock missFirstBlock missSecondBlock
        missThirdBlock single ≠ 3 := by
      intro hcontra
      rcases hthreeOnly single hcontra with rfl | rfl | rfl
      exacts [hne1 rfl, hne2 rfl, hne3 rfl]
    have hneTwo := hTwoNone single
    have hneFour := hFourNone single
    omega
  have hs1Count : fourBlockCoverCount allTripleBlock missFirstBlock missSecondBlock
      missThirdBlock singleFirst = 1 :=
    hcountOne singleFirst hs1Ne1 hs1Ne2.symm.symm hs1Ne3 (Or.inr (Or.inl hs1Mem))
  have hs2Count : fourBlockCoverCount allTripleBlock missFirstBlock missSecondBlock
      missThirdBlock singleSecond = 1 :=
    hcountOne singleSecond hs2Ne1 hs2Ne2 hs2Ne3 (Or.inr (Or.inr (Or.inl hs2Mem)))
  have hs3Count : fourBlockCoverCount allTripleBlock missFirstBlock missSecondBlock
      missThirdBlock singleThird = 1 :=
    hcountOne singleThird hs3Ne1 hs3Ne2 hs3Ne3 (Or.inr (Or.inr (Or.inr hs3Mem)))
  have hs1Pairwise := pairwise_notMem_of_fourBlockCoverCount_le_one hs1Count.le
  have hs2Pairwise := pairwise_notMem_of_fourBlockCoverCount_le_one hs2Count.le
  have hsNe12 : singleFirst ≠ singleSecond := by
    intro hcontra
    exact hs1Pairwise.2.2.2.1 ⟨hs1Mem, hcontra ▸ hs2Mem⟩
  have hsNe13 : singleFirst ≠ singleThird := by
    intro hcontra
    exact hs1Pairwise.2.2.2.2.1 ⟨hs1Mem, hcontra ▸ hs3Mem⟩
  have hsNe23 : singleSecond ≠ singleThird := by
    intro hcontra
    exact hs2Pairwise.2.2.2.2.2 ⟨hs2Mem, hcontra ▸ hs3Mem⟩
  refine ⟨singleFirst, singleSecond, singleThird, hsNe12, hsNe13, hsNe23, hs1Ne1,
    hs1Ne2, hs1Ne3, hs2Ne1, hs2Ne2, hs2Ne3, hs3Ne1, hs3Ne2, hs3Ne3, ?_⟩
  rw [hAllEq, hMissFirstEq, hMissSecondEq, hMissThirdEq]

/-- The canonical three-triple family: triple atoms `0,1,2`, single atoms
`3,4,5` completing the pairs `{0,1}`, `{0,2}`, `{1,2}` respectively. -/
def canonicalThreeTripleFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {1, 2, 5}, {0, 2, 4}, {0, 1, 3}}

/-- **THE THREE-TRIPLE CAPSTONE.**  Any four-block family with profile
`(0, 3, 0, 3)` relabels onto the canonical three-triple family. -/
theorem exists_map_family_eq_canonicalThreeTriple_of_profile
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock) (hneTwoThree : secondBlock ≠ thirdBlock)
    (hneTwoFour : secondBlock ≠ fourthBlock) (hneThreeFour : thirdBlock ≠ fourthBlock)
    (hcardOne : firstBlock.card = 3) (hcardTwo : secondBlock.card = 3)
    (hcardThree : thirdBlock.card = 3) (hcardFour : fourthBlock.card = 3)
    (hquadClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4
      = 0)
    (htripleClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3
      = 3)
    (hdoubleClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2
      = 0) :
    ∃ relabelPerm : Equiv.Perm (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
          Finset (Finset (Fin 6))).image
          (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
        = canonicalThreeTripleFamily := by
  classical
  obtain ⟨tripleFirst, tripleSecond, tripleThird, hneT12, hneT13, hneT23, hcount1,
      hcount2, hcount3⟩ := exists_three_atoms_of_classCard_three htripleClass
  have hthreeOnly : ∀ atom : Fin 6,
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom = 3
        → atom = tripleFirst ∨ atom = tripleSecond ∨ atom = tripleThird := by
    intro atom hcontra
    have hsubset : ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 6))
        ⊆ Finset.univ.filter fun atomIndex =>
          fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
            = 3 := by
      intro triple hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      exacts [Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcount1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcount2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcount3⟩]
    have htripleCard : ({tripleFirst, tripleSecond, tripleThird} :
        Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hneT12, hneT13]),
        Finset.card_insert_of_notMem (by simp [hneT23]), Finset.card_singleton]
    have hfilterCard : (Finset.univ.filter fun atomIndex =>
        fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
          = 3).card = 3 := by
      rw [← fourBlockCountClass]
      exact htripleClass
    have hfilterEq := Finset.eq_of_subset_of_card_le hsubset
      (by rw [hfilterCard, htripleCard])
    have hmemFilter : atom ∈ Finset.univ.filter fun atomIndex =>
        fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
          = 3 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ atom, hcontra⟩
    rw [← hfilterEq] at hmemFilter
    simpa using hmemFilter
  obtain ⟨allTripleBlock, missFirstBlock, missSecondBlock, missThirdBlock, hSetEq,
      hCountEq, hcardAll, hcardMissFirst, hcardMissSecond, hcardMissThird, hneMiss12,
      hneMiss13, hneMiss23, hmemAll1, hmemAll2, hmemAll3, hmiss11, hmem12, hmem13,
      hmem21, hmiss22, hmem23, hmem31, hmem32, hmiss33⟩ :=
    exists_missAssignment_of_three_count_three hneOneTwo hneOneThree hneOneFour
      hneTwoThree hneTwoFour hneThreeFour hcardOne hcardTwo hcardThree hcardFour
      hneT12 hneT13 hneT23 hcount1 hcount2 hcount3
  obtain ⟨singleFirst, singleSecond, singleThird, hsNe12, hsNe13, hsNe23, hs1Ne1,
      hs1Ne2, hs1Ne3, hs2Ne1, hs2Ne2, hs2Ne3, hs3Ne1, hs3Ne2, hs3Ne3, hFormEq⟩ :=
    family_eq_threeTripleForm_of_missAssignment hcardAll hcardMissFirst hcardMissSecond
      hcardMissThird hneT12 hneT13 hneT23 hmemAll1 hmemAll2 hmemAll3 hmiss11 hmem12
      hmem13 hmem21 hmiss22 hmem23 hmem31 hmem32 hmiss33
      (fun atom hcount => hthreeOnly atom ((hCountEq atom).symm.trans hcount))
      (fun atom hcount => count_ne_of_classCard_zero hdoubleClass atom
        ((hCountEq atom).symm.trans hcount))
      (fun atom hcount => count_ne_of_classCard_zero hquadClass atom
        ((hCountEq atom).symm.trans hcount))
  have hinj : Function.Injective
      ![tripleFirst, tripleSecond, tripleThird, singleThird, singleSecond,
        singleFirst] :=
    injective_sixAtomAssignment hneT12 hneT13 hs3Ne1.symm hs2Ne1.symm hs1Ne1.symm
      hneT23 hs3Ne2.symm hs2Ne2.symm hs1Ne2.symm hs3Ne3.symm hs2Ne3.symm hs1Ne3.symm
      hsNe23.symm hsNe13.symm hsNe12.symm
  let atomAssignment : Equiv.Perm (Fin 6) :=
    Equiv.ofBijective
      ![tripleFirst, tripleSecond, tripleThird, singleThird, singleSecond, singleFirst]
      (Finite.injective_iff_bijective.mp hinj)
  have hpiT1 : atomAssignment.symm tripleFirst = 0 := by
    rw [Equiv.symm_apply_eq]; rfl
  have hpiT2 : atomAssignment.symm tripleSecond = 1 := by
    rw [Equiv.symm_apply_eq]; rfl
  have hpiT3 : atomAssignment.symm tripleThird = 2 := by
    rw [Equiv.symm_apply_eq]; rfl
  have hpiS3 : atomAssignment.symm singleThird = 3 := by
    rw [Equiv.symm_apply_eq]; rfl
  have hpiS2 : atomAssignment.symm singleSecond = 4 := by
    rw [Equiv.symm_apply_eq]; rfl
  have hpiS1 : atomAssignment.symm singleFirst = 5 := by
    rw [Equiv.symm_apply_eq]; rfl
  refine ⟨atomAssignment.symm, ?_⟩
  rw [hSetEq, hFormEq]
  simp only [Finset.image_insert, Finset.image_singleton]
  rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
    map_triple_toEmbedding, hpiT1, hpiT2, hpiT3, hpiS3, hpiS2, hpiS1]
  rfl

end Gtz

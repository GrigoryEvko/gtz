import Mathlib
import Gtz.Quantitative.AllDoubleDoorReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The two-two-two door: profile (0,2,2,2) closed end to end

Two triple atoms, two double atoms, two single atoms admit exactly five
shapes, split by whether the two triple atoms miss the same block.  A shared
miss gives the TRIDENT: three blocks through the triple pair, the miss block
pairing the two doubles with the leftover atom.  Split misses leave two
blocks through the pair and sort by where the two pair-completing atoms
land: the TWIN-PAIRS (both miss blocks share the double pair), the ZIGZAG
(each miss block picks up its own both-block double), the HOOK (one
both-block double chains through a shared fresh double), and the NESTED
(one miss block swallows both both-block thirds).  Explicit permutations
land all five on canonical representatives; twelve of the fifteen census
representatives are now pinned.
-/

namespace Gtz

/-- A positive cover count names a block. -/
theorem exists_mem_of_one_le_fourBlockCoverCount
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)} {atomIndex : Fin 6}
    (hcount : 1 ≤ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
      atomIndex) :
    atomIndex ∈ firstBlock ∨ atomIndex ∈ secondBlock ∨ atomIndex ∈ thirdBlock
      ∨ atomIndex ∈ fourthBlock := by
  unfold fourBlockCoverCount at hcount
  split_ifs at hcount <;> first | omega | tauto

/-- **The miss-split normalization.**  The two triple atoms miss one block
each; the family renormalizes around a shared miss or a split pair of
misses, with cover counts carried verbatim. -/
theorem exists_missSplit_of_two_count_three
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock) (hneTwoThree : secondBlock ≠ thirdBlock)
    (hneTwoFour : secondBlock ≠ fourthBlock) (hneThreeFour : thirdBlock ≠ fourthBlock)
    (hcardOne : firstBlock.card = 3) (hcardTwo : secondBlock.card = 3)
    (hcardThree : thirdBlock.card = 3) (hcardFour : fourthBlock.card = 3)
    {tripleFirst tripleSecond : Fin 6}
    (hcount1 : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
      tripleFirst = 3)
    (hcount2 : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
      tripleSecond = 3) :
    (∃ tBlockA tBlockB tBlockC missBlock : Finset (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} : Finset (Finset (Fin 6)))
          = {tBlockA, tBlockB, tBlockC, missBlock}
        ∧ (∀ atom : Fin 6, fourBlockCoverCount tBlockA tBlockB tBlockC missBlock atom
            = fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom)
        ∧ tBlockA.card = 3 ∧ tBlockB.card = 3 ∧ tBlockC.card = 3 ∧ missBlock.card = 3
        ∧ tBlockA ≠ tBlockB ∧ tBlockA ≠ tBlockC ∧ tBlockB ≠ tBlockC
        ∧ tripleFirst ∈ tBlockA ∧ tripleFirst ∈ tBlockB ∧ tripleFirst ∈ tBlockC
        ∧ tripleFirst ∉ missBlock
        ∧ tripleSecond ∈ tBlockA ∧ tripleSecond ∈ tBlockB ∧ tripleSecond ∈ tBlockC
        ∧ tripleSecond ∉ missBlock)
      ∨ (∃ bothBlockA bothBlockB missFirstBlock missSecondBlock : Finset (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} : Finset (Finset (Fin 6)))
          = {bothBlockA, bothBlockB, missFirstBlock, missSecondBlock}
        ∧ (∀ atom : Fin 6, fourBlockCoverCount bothBlockA bothBlockB missFirstBlock
            missSecondBlock atom
              = fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom)
        ∧ bothBlockA.card = 3 ∧ bothBlockB.card = 3 ∧ missFirstBlock.card = 3
        ∧ missSecondBlock.card = 3
        ∧ bothBlockA ≠ bothBlockB
        ∧ tripleFirst ∈ bothBlockA ∧ tripleFirst ∈ bothBlockB
        ∧ tripleFirst ∉ missFirstBlock ∧ tripleFirst ∈ missSecondBlock
        ∧ tripleSecond ∈ bothBlockA ∧ tripleSecond ∈ bothBlockB
        ∧ tripleSecond ∈ missFirstBlock ∧ tripleSecond ∉ missSecondBlock) := by
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
    first
    | (refine Or.inl ⟨secondBlock, thirdBlock, fourthBlock, firstBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardThree, hcardFour, hcardOne,
        hneTwoThree, hneTwoFour, hneThreeFour, ht1Second, ht1Third, ht1Fourth, ht1First, ht2Second, ht2Third, ht2Fourth, ht2First⟩
       rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third secondBlock firstBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth secondBlock thirdBlock firstBlock fourthBlock])
    | (refine Or.inr ⟨thirdBlock, fourthBlock, firstBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardFour, hcardOne, hcardTwo,
        hneThreeFour, ht1Third, ht1Fourth, ht1First, ht1Second, ht2Third, ht2Fourth, ht2First, ht2Second⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock,
         quadSet_swap_third_fourth thirdBlock firstBlock secondBlock fourthBlock,
         quadSet_swap_second_third thirdBlock firstBlock fourthBlock secondBlock])
    | (refine Or.inr ⟨secondBlock, fourthBlock, firstBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardFour, hcardOne, hcardThree,
        hneTwoFour, ht1Second, ht1Fourth, ht1First, ht1Third, ht2Second, ht2Fourth, ht2First, ht2Third⟩
       rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth secondBlock firstBlock thirdBlock fourthBlock,
         quadSet_swap_second_third secondBlock firstBlock fourthBlock thirdBlock])
    | (refine Or.inr ⟨secondBlock, thirdBlock, firstBlock, fourthBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardThree, hcardOne, hcardFour,
        hneTwoThree, ht1Second, ht1Third, ht1First, ht1Fourth, ht2Second, ht2Third, ht2First, ht2Fourth⟩
       rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third secondBlock firstBlock thirdBlock fourthBlock])
    | (refine Or.inr ⟨thirdBlock, fourthBlock, secondBlock, firstBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardFour, hcardTwo, hcardOne,
        hneThreeFour, ht1Third, ht1Fourth, ht1Second, ht1First, ht2Third, ht2Fourth, ht2Second, ht2First⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock,
         quadSet_swap_third_fourth thirdBlock firstBlock secondBlock fourthBlock,
         quadSet_swap_second_third thirdBlock firstBlock fourthBlock secondBlock,
         quadSet_swap_third_fourth thirdBlock fourthBlock firstBlock secondBlock])
    | (refine Or.inl ⟨firstBlock, thirdBlock, fourthBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardThree, hcardFour, hcardTwo,
        hneOneThree, hneOneFour, hneThreeFour, ht1First, ht1Third, ht1Fourth, ht1Second, ht2First, ht2Third, ht2Fourth, ht2Second⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock])
    | (refine Or.inr ⟨firstBlock, fourthBlock, secondBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardFour, hcardTwo, hcardThree,
        hneOneFour, ht1First, ht1Fourth, ht1Second, ht1Third, ht2First, ht2Fourth, ht2Second, ht2Third⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock])
    | (refine Or.inr ⟨firstBlock, thirdBlock, secondBlock, fourthBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardThree, hcardTwo, hcardFour,
        hneOneThree, ht1First, ht1Third, ht1Second, ht1Fourth, ht2First, ht2Third, ht2Second, ht2Fourth⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock])
    | (refine Or.inr ⟨secondBlock, fourthBlock, thirdBlock, firstBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardFour, hcardThree, hcardOne,
        hneTwoFour, ht1Second, ht1Fourth, ht1Third, ht1First, ht2Second, ht2Fourth, ht2Third, ht2First⟩
       rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth secondBlock firstBlock thirdBlock fourthBlock,
         quadSet_swap_second_third secondBlock firstBlock fourthBlock thirdBlock,
         quadSet_swap_third_fourth secondBlock fourthBlock firstBlock thirdBlock])
    | (refine Or.inr ⟨firstBlock, fourthBlock, thirdBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardFour, hcardThree, hcardTwo,
        hneOneFour, ht1First, ht1Fourth, ht1Third, ht1Second, ht2First, ht2Fourth, ht2Third, ht2Second⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
         quadSet_swap_third_fourth firstBlock fourthBlock secondBlock thirdBlock])
    | (refine Or.inl ⟨firstBlock, secondBlock, fourthBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardTwo, hcardFour, hcardThree,
        hneOneTwo, hneOneFour, hneTwoFour, ht1First, ht1Second, ht1Fourth, ht1Third, ht2First, ht2Second, ht2Fourth, ht2Third⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock])
    | exact Or.inr ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, rfl,
        fun atom => rfl, hcardOne, hcardTwo, hcardThree, hcardFour,
        hneOneTwo, ht1First, ht1Second, ht1Third, ht1Fourth, ht2First, ht2Second, ht2Third, ht2Fourth⟩
    | (refine Or.inr ⟨secondBlock, thirdBlock, fourthBlock, firstBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardThree, hcardFour, hcardOne,
        hneTwoThree, ht1Second, ht1Third, ht1Fourth, ht1First, ht2Second, ht2Third, ht2Fourth, ht2First⟩
       rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_second_third secondBlock firstBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth secondBlock thirdBlock firstBlock fourthBlock])
    | (refine Or.inr ⟨firstBlock, thirdBlock, fourthBlock, secondBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardThree, hcardFour, hcardTwo,
        hneOneThree, ht1First, ht1Third, ht1Fourth, ht1Second, ht2First, ht2Third, ht2Fourth, ht2Second⟩
       rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
         quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock])
    | (refine Or.inr ⟨firstBlock, secondBlock, fourthBlock, thirdBlock, ?_,
        fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardTwo, hcardFour, hcardThree,
        hneOneTwo, ht1First, ht1Second, ht1Fourth, ht1Third, ht2First, ht2Second, ht2Fourth, ht2Third⟩
       rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock])
    | exact Or.inl ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, rfl,
        fun atom => rfl, hcardOne, hcardTwo, hcardThree, hcardFour,
        hneOneTwo, hneOneThree, hneTwoThree, ht1First, ht1Second, ht1Third, ht1Fourth, ht2First, ht2Second, ht2Third, ht2Fourth⟩

/-- **The trident extraction.**  A shared miss puts three blocks through the
triple pair; coverage parks the leftover atom in the miss block, whose other
two atoms are the doubles. -/
theorem family_eq_tridentForm_of_sharedMiss
    {tBlockA tBlockB tBlockC missBlock : Finset (Fin 6)}
    (hcardA : tBlockA.card = 3) (hcardB : tBlockB.card = 3) (hcardC : tBlockC.card = 3)
    (hcardMiss : missBlock.card = 3)
    (hneAB : tBlockA ≠ tBlockB) (hneAC : tBlockA ≠ tBlockC) (hneBC : tBlockB ≠ tBlockC)
    {tripleFirst tripleSecond : Fin 6} (hneT12 : tripleFirst ≠ tripleSecond)
    (hmem1A : tripleFirst ∈ tBlockA) (hmem1B : tripleFirst ∈ tBlockB)
    (hmem1C : tripleFirst ∈ tBlockC) (hmiss1 : tripleFirst ∉ missBlock)
    (hmem2A : tripleSecond ∈ tBlockA) (hmem2B : tripleSecond ∈ tBlockB)
    (hmem2C : tripleSecond ∈ tBlockC) (hmiss2 : tripleSecond ∉ missBlock)
    (hcovered : ∀ atom : Fin 6,
      1 ≤ fourBlockCoverCount tBlockA tBlockB tBlockC missBlock atom) :
    ∃ doubleFirst doubleSecond singleThird lastAtom : Fin 6,
      doubleFirst ≠ tripleFirst ∧ doubleFirst ≠ tripleSecond
        ∧ doubleSecond ≠ tripleFirst ∧ doubleSecond ≠ tripleSecond
        ∧ singleThird ≠ tripleFirst ∧ singleThird ≠ tripleSecond
        ∧ lastAtom ≠ tripleFirst ∧ lastAtom ≠ tripleSecond
        ∧ doubleFirst ≠ doubleSecond ∧ doubleFirst ≠ singleThird
        ∧ doubleFirst ≠ lastAtom ∧ doubleSecond ≠ singleThird
        ∧ doubleSecond ≠ lastAtom ∧ singleThird ≠ lastAtom
        ∧ ({tBlockA, tBlockB, tBlockC, missBlock} : Finset (Finset (Fin 6)))
            = {{tripleFirst, tripleSecond, doubleFirst},
               {tripleFirst, tripleSecond, doubleSecond},
               {tripleFirst, tripleSecond, singleThird},
               {doubleFirst, doubleSecond, lastAtom}} := by
  obtain ⟨thirdA, hxaNe1, hxaNe2, hAEq⟩ :=
    exists_third_of_pair_mem_card_three hcardA hneT12 hmem1A hmem2A
  obtain ⟨thirdB, hxbNe1, hxbNe2, hBEq⟩ :=
    exists_third_of_pair_mem_card_three hcardB hneT12 hmem1B hmem2B
  obtain ⟨thirdC, hxcNe1, hxcNe2, hCEq⟩ :=
    exists_third_of_pair_mem_card_three hcardC hneT12 hmem1C hmem2C
  have hneXab : thirdA ≠ thirdB := fun hcontra => hneAB (by rw [hAEq, hBEq, hcontra])
  have hneXac : thirdA ≠ thirdC := fun hcontra => hneAC (by rw [hAEq, hCEq, hcontra])
  have hneXbc : thirdB ≠ thirdC := fun hcontra => hneBC (by rw [hBEq, hCEq, hcontra])
  have hFiveCard : ({tripleFirst, tripleSecond, thirdA, thirdB, thirdC} :
      Finset (Fin 6)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by
        simp [hneT12, hxaNe1.symm, hxbNe1.symm, hxcNe1.symm]),
      Finset.card_insert_of_notMem (by simp [hxaNe2.symm, hxbNe2.symm, hxcNe2.symm]),
      Finset.card_insert_of_notMem (by simp [hneXab, hneXac]),
      Finset.card_insert_of_notMem (by simp [hneXbc]), Finset.card_singleton]
  have hcomplCard : (({tripleFirst, tripleSecond, thirdA, thirdB, thirdC} :
      Finset (Fin 6))ᶜ).card = 1 := by
    rw [Finset.card_compl, hFiveCard, Fintype.card_fin]
  obtain ⟨lastAtom, hcomplEq⟩ := Finset.card_eq_one.mp hcomplCard
  have hwNot : lastAtom ∉ ({tripleFirst, tripleSecond, thirdA, thirdB, thirdC} :
      Finset (Fin 6)) := by
    rw [← Finset.mem_compl, hcomplEq]
    exact Finset.mem_singleton_self _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwNot
  push Not at hwNot
  obtain ⟨hwNe1, hwNe2, hwNeXa, hwNeXb, hwNeXc⟩ := hwNot
  have hwMiss : lastAtom ∈ missBlock := by
    rcases exists_mem_of_one_le_fourBlockCoverCount (hcovered lastAtom) with
        hmem | hmem | hmem | hmem
    · rw [hAEq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      exacts [absurd rfl hwNe1, absurd rfl hwNe2, absurd rfl hwNeXa]
    · rw [hBEq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      exacts [absurd rfl hwNe1, absurd rfl hwNe2, absurd rfl hwNeXb]
    · rw [hCEq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      exacts [absurd rfl hwNe1, absurd rfl hwNe2, absurd rfl hwNeXc]
    · exact hmem
  have heraseMiss : (missBlock.erase lastAtom).card = 2 := by
    rw [Finset.card_erase_of_mem hwMiss, hcardMiss]
  obtain ⟨inFirst, inSecond, hneIn, heraseEq⟩ := Finset.card_eq_two.mp heraseMiss
  have hinFirstErase : inFirst ∈ missBlock.erase lastAtom := by
    rw [heraseEq]
    exact Finset.mem_insert_self _ _
  have hinSecondErase : inSecond ∈ missBlock.erase lastAtom := by
    rw [heraseEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hinFirstMiss : inFirst ∈ missBlock := (Finset.mem_erase.mp hinFirstErase).2
  have hinSecondMiss : inSecond ∈ missBlock := (Finset.mem_erase.mp hinSecondErase).2
  have hMissEq : missBlock = {lastAtom, inFirst, inSecond} := by
    rw [← Finset.insert_erase hwMiss, heraseEq]
  have hSixEq : ({tripleFirst, tripleSecond, thirdA, thirdB, thirdC, lastAtom} :
      Finset (Fin 6)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by
        simp [hneT12, hxaNe1.symm, hxbNe1.symm, hxcNe1.symm, hwNe1.symm]),
      Finset.card_insert_of_notMem (by
        simp [hxaNe2.symm, hxbNe2.symm, hxcNe2.symm, hwNe2.symm]),
      Finset.card_insert_of_notMem (by simp [hneXab, hneXac, hwNeXa.symm]),
      Finset.card_insert_of_notMem (by simp [hneXbc, hwNeXb.symm]),
      Finset.card_insert_of_notMem (by simp [hwNeXc.symm]), Finset.card_singleton,
      Fintype.card_fin]
  have hinId : ∀ atom : Fin 6, atom ∈ missBlock.erase lastAtom
      → atom = thirdA ∨ atom = thirdB ∨ atom = thirdC := by
    intro atom hmemErase
    have hneW : atom ≠ lastAtom := (Finset.mem_erase.mp hmemErase).1
    have hmemMiss : atom ∈ missBlock := (Finset.mem_erase.mp hmemErase).2
    have hmemSix : atom ∈ ({tripleFirst, tripleSecond, thirdA, thirdB, thirdC,
        lastAtom} : Finset (Fin 6)) := by
      rw [hSixEq]
      exact Finset.mem_univ atom
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemSix
    rcases hmemSix with rfl | rfl | h | h | h | rfl
    exacts [absurd hmemMiss hmiss1, absurd hmemMiss hmiss2, Or.inl h,
      Or.inr (Or.inl h), Or.inr (Or.inr h), absurd rfl hneW]
  rcases hinId inFirst hinFirstErase with hidFirst | hidFirst | hidFirst <;>
    rcases hinId inSecond hinSecondErase with hidSecond | hidSecond | hidSecond <;>
    rw [hidFirst, hidSecond] at hMissEq
  · exact absurd (hidFirst.trans hidSecond.symm) hneIn
  -- doubles thirdA, thirdB
  · refine ⟨thirdA, thirdB, thirdC, lastAtom, hxaNe1, hxaNe2, hxbNe1, hxbNe2, hxcNe1,
      hxcNe2, hwNe1, hwNe2, hneXab, hneXac, hwNeXa.symm, hneXbc,
      hwNeXb.symm, hwNeXc.symm, ?_⟩
    rw [hAEq, hBEq, hCEq, hMissEq.trans ((tripleSet_swap_first_second lastAtom thirdA
      thirdB).trans (tripleSet_swap_second_third thirdA lastAtom thirdB))]
  -- doubles thirdA, thirdC
  · refine ⟨thirdA, thirdC, thirdB, lastAtom, hxaNe1, hxaNe2, hxcNe1, hxcNe2, hxbNe1,
      hxbNe2, hwNe1, hwNe2, hneXac, hneXab, hwNeXa.symm, hneXbc.symm, hwNeXc.symm,
      hwNeXb.symm, ?_⟩
    rw [quadSet_swap_second_third tBlockA tBlockB tBlockC missBlock,
      hAEq, hBEq, hCEq, hMissEq.trans ((tripleSet_swap_first_second lastAtom thirdA
      thirdC).trans (tripleSet_swap_second_third thirdA lastAtom thirdC))]
  -- doubles thirdB, thirdA
  · refine ⟨thirdB, thirdA, thirdC, lastAtom, hxbNe1, hxbNe2, hxaNe1, hxaNe2, hxcNe1,
      hxcNe2, hwNe1, hwNe2, hneXab.symm, hneXbc, hwNeXb.symm, hneXac, hwNeXa.symm,
      hwNeXc.symm, ?_⟩
    rw [quadSet_swap_first_second tBlockA tBlockB tBlockC missBlock,
      hAEq, hBEq, hCEq, hMissEq.trans ((tripleSet_swap_first_second lastAtom thirdB
      thirdA).trans (tripleSet_swap_second_third thirdB lastAtom thirdA))]
  · exact absurd (hidFirst.trans hidSecond.symm) hneIn
  -- doubles thirdB, thirdC
  · refine ⟨thirdB, thirdC, thirdA, lastAtom, hxbNe1, hxbNe2, hxcNe1, hxcNe2, hxaNe1,
      hxaNe2, hwNe1, hwNe2, hneXbc, hneXab.symm, hwNeXb.symm, hneXac.symm,
      hwNeXc.symm, hwNeXa.symm, ?_⟩
    rw [quadSet_swap_first_second tBlockA tBlockB tBlockC missBlock,
      quadSet_swap_second_third tBlockB tBlockA tBlockC missBlock,
      hAEq, hBEq, hCEq, hMissEq.trans ((tripleSet_swap_first_second lastAtom thirdB
      thirdC).trans (tripleSet_swap_second_third thirdB lastAtom thirdC))]
  -- doubles thirdC, thirdA
  · refine ⟨thirdC, thirdA, thirdB, lastAtom, hxcNe1, hxcNe2, hxaNe1, hxaNe2, hxbNe1,
      hxbNe2, hwNe1, hwNe2, hneXac.symm, hneXbc.symm, hwNeXc.symm, hneXab,
      hwNeXa.symm, hwNeXb.symm, ?_⟩
    rw [quadSet_swap_second_third tBlockA tBlockB tBlockC missBlock,
      quadSet_swap_first_second tBlockA tBlockC tBlockB missBlock,
      hAEq, hBEq, hCEq, hMissEq.trans ((tripleSet_swap_first_second lastAtom thirdC
      thirdA).trans (tripleSet_swap_second_third thirdC lastAtom thirdA))]
  -- doubles thirdC, thirdB
  · refine ⟨thirdC, thirdB, thirdA, lastAtom, hxcNe1, hxcNe2, hxbNe1, hxbNe2, hxaNe1,
      hxaNe2, hwNe1, hwNe2, hneXbc.symm, hneXac.symm, hwNeXc.symm, hneXab.symm,
      hwNeXb.symm, hwNeXa.symm, ?_⟩
    rw [quadSet_swap_second_third tBlockA tBlockB tBlockC missBlock,
      quadSet_swap_first_second tBlockA tBlockC tBlockB missBlock,
      quadSet_swap_second_third tBlockC tBlockA tBlockB missBlock,
      hAEq, hBEq, hCEq, hMissEq.trans ((tripleSet_swap_first_second lastAtom thirdC
      thirdB).trans (tripleSet_swap_second_third thirdC lastAtom thirdB))]
  · exact absurd (hidFirst.trans hidSecond.symm) hneIn

/-- Pinning a triple from unordered identifications of its two free slots. -/
theorem triple_pin_of_pair_ids {anchor firstEnd secondEnd xTarget yTarget : Fin 6}
    (hfirstId : firstEnd = xTarget ∨ firstEnd = yTarget)
    (hsecondId : secondEnd = xTarget ∨ secondEnd = yTarget)
    (hneEnds : firstEnd ≠ secondEnd) :
    ({anchor, firstEnd, secondEnd} : Finset (Fin 6)) = {anchor, xTarget, yTarget} := by
  rcases hfirstId with rfl | rfl <;> rcases hsecondId with rfl | rfl
  · exact absurd rfl hneEnds
  · rfl
  · exact tripleSet_swap_second_third anchor firstEnd secondEnd
  · exact absurd rfl hneEnds

/-- **The split-miss extraction.**  With the triple atoms missing different
blocks, the two pair-completing atoms sort the family into the zigzag, the
twin-pairs, the hook, or the nested shape. -/
theorem family_eq_splitMissForm_of_splitMiss
    {bothBlockA bothBlockB missFirstBlock missSecondBlock : Finset (Fin 6)}
    (hcardA : bothBlockA.card = 3) (hcardB : bothBlockB.card = 3)
    (hcardM1 : missFirstBlock.card = 3) (hcardM2 : missSecondBlock.card = 3)
    (hneBoth : bothBlockA ≠ bothBlockB)
    {tripleFirst tripleSecond : Fin 6} (hneT12 : tripleFirst ≠ tripleSecond)
    (hmem1A : tripleFirst ∈ bothBlockA) (hmem1B : tripleFirst ∈ bothBlockB)
    (hmiss1M1 : tripleFirst ∉ missFirstBlock) (hmem1M2 : tripleFirst ∈ missSecondBlock)
    (hmem2A : tripleSecond ∈ bothBlockA) (hmem2B : tripleSecond ∈ bothBlockB)
    (hmem2M1 : tripleSecond ∈ missFirstBlock)
    (hmiss2M2 : tripleSecond ∉ missSecondBlock)
    (hcovered : ∀ atom : Fin 6, 1 ≤ fourBlockCoverCount bothBlockA bothBlockB
      missFirstBlock missSecondBlock atom)
    (hthreeOnly : ∀ atom : Fin 6, fourBlockCoverCount bothBlockA bothBlockB
        missFirstBlock missSecondBlock atom = 3
      → atom = tripleFirst ∨ atom = tripleSecond)
    (hquadNone : ∀ atom : Fin 6, fourBlockCoverCount bothBlockA bothBlockB
      missFirstBlock missSecondBlock atom ≠ 4) :
    (∃ atomZero atomOne atomTwo atomThree atomFour atomFive : Fin 6,
      atomZero ≠ atomOne ∧ atomZero ≠ atomTwo ∧ atomZero ≠ atomThree
        ∧ atomZero ≠ atomFour ∧ atomZero ≠ atomFive ∧ atomOne ≠ atomTwo
        ∧ atomOne ≠ atomThree ∧ atomOne ≠ atomFour ∧ atomOne ≠ atomFive
        ∧ atomTwo ≠ atomThree ∧ atomTwo ≠ atomFour ∧ atomTwo ≠ atomFive
        ∧ atomThree ≠ atomFour ∧ atomThree ≠ atomFive ∧ atomFour ≠ atomFive
        ∧ ({bothBlockA, bothBlockB, missFirstBlock, missSecondBlock} :
              Finset (Finset (Fin 6)))
            = {{atomZero, atomOne, atomTwo}, {atomZero, atomOne, atomThree},
               {atomOne, atomTwo, atomFour}, {atomZero, atomThree, atomFive}})
    ∨ (∃ atomZero atomOne atomTwo atomThree atomFour atomFive : Fin 6,
      atomZero ≠ atomOne ∧ atomZero ≠ atomTwo ∧ atomZero ≠ atomThree
        ∧ atomZero ≠ atomFour ∧ atomZero ≠ atomFive ∧ atomOne ≠ atomTwo
        ∧ atomOne ≠ atomThree ∧ atomOne ≠ atomFour ∧ atomOne ≠ atomFive
        ∧ atomTwo ≠ atomThree ∧ atomTwo ≠ atomFour ∧ atomTwo ≠ atomFive
        ∧ atomThree ≠ atomFour ∧ atomThree ≠ atomFive ∧ atomFour ≠ atomFive
        ∧ ({bothBlockA, bothBlockB, missFirstBlock, missSecondBlock} :
              Finset (Finset (Fin 6)))
            = {{atomZero, atomOne, atomFour}, {atomZero, atomOne, atomFive},
               {atomOne, atomTwo, atomThree}, {atomZero, atomTwo, atomThree}})
    ∨ (∃ atomZero atomOne atomTwo atomThree atomFour atomFive : Fin 6,
      atomZero ≠ atomOne ∧ atomZero ≠ atomTwo ∧ atomZero ≠ atomThree
        ∧ atomZero ≠ atomFour ∧ atomZero ≠ atomFive ∧ atomOne ≠ atomTwo
        ∧ atomOne ≠ atomThree ∧ atomOne ≠ atomFour ∧ atomOne ≠ atomFive
        ∧ atomTwo ≠ atomThree ∧ atomTwo ≠ atomFour ∧ atomTwo ≠ atomFive
        ∧ atomThree ≠ atomFour ∧ atomThree ≠ atomFive ∧ atomFour ≠ atomFive
        ∧ ({bothBlockA, bothBlockB, missFirstBlock, missSecondBlock} :
              Finset (Finset (Fin 6)))
            = {{atomZero, atomOne, atomTwo}, {atomZero, atomOne, atomThree},
               {atomOne, atomTwo, atomFour}, {atomZero, atomFour, atomFive}})
    ∨ (∃ atomZero atomOne atomTwo atomThree atomFour atomFive : Fin 6,
      atomZero ≠ atomOne ∧ atomZero ≠ atomTwo ∧ atomZero ≠ atomThree
        ∧ atomZero ≠ atomFour ∧ atomZero ≠ atomFive ∧ atomOne ≠ atomTwo
        ∧ atomOne ≠ atomThree ∧ atomOne ≠ atomFour ∧ atomOne ≠ atomFive
        ∧ atomTwo ≠ atomThree ∧ atomTwo ≠ atomFour ∧ atomTwo ≠ atomFive
        ∧ atomThree ≠ atomFour ∧ atomThree ≠ atomFive ∧ atomFour ≠ atomFive
        ∧ ({bothBlockA, bothBlockB, missFirstBlock, missSecondBlock} :
              Finset (Finset (Fin 6)))
            = {{atomZero, atomOne, atomTwo}, {atomZero, atomOne, atomThree},
               {atomOne, atomTwo, atomThree}, {atomZero, atomFour, atomFive}}) := by
  obtain ⟨aAtom, haNe1, haNe2, hBothAEq⟩ :=
    exists_third_of_pair_mem_card_three hcardA hneT12 hmem1A hmem2A
  obtain ⟨bAtom, hbNe1, hbNe2, hBothBEq⟩ :=
    exists_third_of_pair_mem_card_three hcardB hneT12 hmem1B hmem2B
  have haNeB : aAtom ≠ bAtom := fun hcontra =>
    hneBoth (by rw [hBothAEq, hBothBEq, hcontra])
  have heraseM1 : (missFirstBlock.erase tripleSecond).card = 2 := by
    rw [Finset.card_erase_of_mem hmem2M1, hcardM1]
  obtain ⟨inOneA, inOneB, hneInOne, heraseM1Eq⟩ := Finset.card_eq_two.mp heraseM1
  have hinOneAErase : inOneA ∈ missFirstBlock.erase tripleSecond := by
    rw [heraseM1Eq]
    exact Finset.mem_insert_self _ _
  have hinOneBErase : inOneB ∈ missFirstBlock.erase tripleSecond := by
    rw [heraseM1Eq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hinOneAM1 : inOneA ∈ missFirstBlock := (Finset.mem_erase.mp hinOneAErase).2
  have hinOneBM1 : inOneB ∈ missFirstBlock := (Finset.mem_erase.mp hinOneBErase).2
  have hinOneANe2 : inOneA ≠ tripleSecond := (Finset.mem_erase.mp hinOneAErase).1
  have hinOneBNe2 : inOneB ≠ tripleSecond := (Finset.mem_erase.mp hinOneBErase).1
  have hM1Eq : missFirstBlock = {tripleSecond, inOneA, inOneB} := by
    rw [← Finset.insert_erase hmem2M1, heraseM1Eq]
  have heraseM2 : (missSecondBlock.erase tripleFirst).card = 2 := by
    rw [Finset.card_erase_of_mem hmem1M2, hcardM2]
  obtain ⟨inTwoA, inTwoB, hneInTwo, heraseM2Eq⟩ := Finset.card_eq_two.mp heraseM2
  have hinTwoAErase : inTwoA ∈ missSecondBlock.erase tripleFirst := by
    rw [heraseM2Eq]
    exact Finset.mem_insert_self _ _
  have hinTwoBErase : inTwoB ∈ missSecondBlock.erase tripleFirst := by
    rw [heraseM2Eq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hinTwoAM2 : inTwoA ∈ missSecondBlock := (Finset.mem_erase.mp hinTwoAErase).2
  have hinTwoBM2 : inTwoB ∈ missSecondBlock := (Finset.mem_erase.mp hinTwoBErase).2
  have hinTwoANe1 : inTwoA ≠ tripleFirst := (Finset.mem_erase.mp hinTwoAErase).1
  have hinTwoBNe1 : inTwoB ≠ tripleFirst := (Finset.mem_erase.mp hinTwoBErase).1
  have hM2Eq : missSecondBlock = {tripleFirst, inTwoA, inTwoB} := by
    rw [← Finset.insert_erase hmem1M2, heraseM2Eq]
  have hFourCard : ({tripleFirst, tripleSecond, aAtom, bAtom} :
      Finset (Fin 6)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hneT12, haNe1.symm, hbNe1.symm]),
      Finset.card_insert_of_notMem (by simp [haNe2.symm, hbNe2.symm]),
      Finset.card_insert_of_notMem (by simp [haNeB]), Finset.card_singleton]
  have hcomplCard : (({tripleFirst, tripleSecond, aAtom, bAtom} :
      Finset (Fin 6))ᶜ).card = 2 := by
    rw [Finset.card_compl, hFourCard, Fintype.card_fin]
  obtain ⟨freshP, freshQ, hnePQ, hcomplEq⟩ := Finset.card_eq_two.mp hcomplCard
  have hpNot : freshP ∉ ({tripleFirst, tripleSecond, aAtom, bAtom} :
      Finset (Fin 6)) := by
    rw [← Finset.mem_compl, hcomplEq]
    exact Finset.mem_insert_self _ _
  have hqNot : freshQ ∉ ({tripleFirst, tripleSecond, aAtom, bAtom} :
      Finset (Fin 6)) := by
    rw [← Finset.mem_compl, hcomplEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpNot hqNot
  push Not at hpNot hqNot
  obtain ⟨hpNe1, hpNe2, hpNeA, hpNeB⟩ := hpNot
  obtain ⟨hqNe1, hqNe2, hqNeA, hqNeB⟩ := hqNot
  have hSixEq : ({tripleFirst, tripleSecond, aAtom, bAtom, freshP, freshQ} :
      Finset (Fin 6)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by
        simp [hneT12, haNe1.symm, hbNe1.symm, hpNe1.symm, hqNe1.symm]),
      Finset.card_insert_of_notMem (by
        simp [haNe2.symm, hbNe2.symm, hpNe2.symm, hqNe2.symm]),
      Finset.card_insert_of_notMem (by simp [haNeB, hpNeA.symm, hqNeA.symm]),
      Finset.card_insert_of_notMem (by simp [hpNeB.symm, hqNeB.symm]),
      Finset.card_insert_of_notMem (by simp [hnePQ]), Finset.card_singleton,
      Fintype.card_fin]
  have hatomId : ∀ atom : Fin 6, atom = tripleFirst ∨ atom = tripleSecond
      ∨ atom = aAtom ∨ atom = bAtom ∨ atom = freshP ∨ atom = freshQ := by
    intro atom
    have hmem : atom ∈ ({tripleFirst, tripleSecond, aAtom, bAtom, freshP, freshQ} :
        Finset (Fin 6)) := by
      rw [hSixEq]
      exact Finset.mem_univ atom
    simpa using hmem
  have hM1AtomId : ∀ atom : Fin 6, atom ∈ missFirstBlock → atom ≠ tripleSecond
      → atom = aAtom ∨ atom = bAtom ∨ atom = freshP ∨ atom = freshQ := by
    intro atom hmem hne2
    rcases hatomId atom with rfl | rfl | h | h | h | h
    exacts [absurd hmem hmiss1M1, absurd rfl hne2, Or.inl h, Or.inr (Or.inl h),
      Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]
  have hM2AtomId : ∀ atom : Fin 6, atom ∈ missSecondBlock → atom ≠ tripleFirst
      → atom = aAtom ∨ atom = bAtom ∨ atom = freshP ∨ atom = freshQ := by
    intro atom hmem hne1
    rcases hatomId atom with rfl | rfl | h | h | h | h
    exacts [absurd rfl hne1, absurd hmem hmiss2M2, Or.inl h, Or.inr (Or.inl h),
      Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]
  have haMemA : aAtom ∈ bothBlockA := by
    rw [hBothAEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self _))))
  have hbMemB : bAtom ∈ bothBlockB := by
    rw [hBothBEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self _))))
  have haState : (aAtom ∉ missFirstBlock ∧ aAtom ∉ missSecondBlock)
      ∨ (aAtom ∈ missFirstBlock ∧ aAtom ∉ missSecondBlock)
      ∨ (aAtom ∉ missFirstBlock ∧ aAtom ∈ missSecondBlock) := by
    by_cases hInM1 : aAtom ∈ missFirstBlock <;>
      by_cases hInM2 : aAtom ∈ missSecondBlock
    · exfalso
      have hthreeLe : 3 ≤ fourBlockCoverCount bothBlockA bothBlockB missFirstBlock
          missSecondBlock aAtom := by
        unfold fourBlockCoverCount
        split_ifs <;> omega
      have hle := fourBlockCoverCount_le_four bothBlockA bothBlockB missFirstBlock
        missSecondBlock aAtom
      have hne4 := hquadNone aAtom
      have heq3 : fourBlockCoverCount bothBlockA bothBlockB missFirstBlock
          missSecondBlock aAtom = 3 := by omega
      rcases hthreeOnly aAtom heq3 with hcase | hcase
      exacts [haNe1 hcase, haNe2 hcase]
    · exact Or.inr (Or.inl ⟨hInM1, hInM2⟩)
    · exact Or.inr (Or.inr ⟨hInM1, hInM2⟩)
    · exact Or.inl ⟨hInM1, hInM2⟩
  have hbState : (bAtom ∉ missFirstBlock ∧ bAtom ∉ missSecondBlock)
      ∨ (bAtom ∈ missFirstBlock ∧ bAtom ∉ missSecondBlock)
      ∨ (bAtom ∉ missFirstBlock ∧ bAtom ∈ missSecondBlock) := by
    by_cases hInM1 : bAtom ∈ missFirstBlock <;>
      by_cases hInM2 : bAtom ∈ missSecondBlock
    · exfalso
      have hthreeLe : 3 ≤ fourBlockCoverCount bothBlockA bothBlockB missFirstBlock
          missSecondBlock bAtom := by
        unfold fourBlockCoverCount
        split_ifs <;> omega
      have hle := fourBlockCoverCount_le_four bothBlockA bothBlockB missFirstBlock
        missSecondBlock bAtom
      have hne4 := hquadNone bAtom
      have heq3 : fourBlockCoverCount bothBlockA bothBlockB missFirstBlock
          missSecondBlock bAtom = 3 := by omega
      rcases hthreeOnly bAtom heq3 with hcase | hcase
      exacts [hbNe1 hcase, hbNe2 hcase]
    · exact Or.inr (Or.inl ⟨hInM1, hInM2⟩)
    · exact Or.inr (Or.inr ⟨hInM1, hInM2⟩)
    · exact Or.inl ⟨hInM1, hInM2⟩
  have hInOneIdOf : aAtom ∉ missFirstBlock → bAtom ∉ missFirstBlock
      → missFirstBlock = {tripleSecond, freshP, freshQ} := by
    intro haNot hbNot
    have hidA : inOneA = freshP ∨ inOneA = freshQ := by
      rcases hM1AtomId inOneA hinOneAM1 hinOneANe2 with h | h | h | h
      exacts [absurd (h ▸ hinOneAM1) haNot, absurd (h ▸ hinOneAM1) hbNot,
        Or.inl h, Or.inr h]
    have hidB : inOneB = freshP ∨ inOneB = freshQ := by
      rcases hM1AtomId inOneB hinOneBM1 hinOneBNe2 with h | h | h | h
      exacts [absurd (h ▸ hinOneBM1) haNot, absurd (h ▸ hinOneBM1) hbNot,
        Or.inl h, Or.inr h]
    exact hM1Eq.trans (triple_pin_of_pair_ids hidA hidB hneInOne)
  have hInTwoIdOf : aAtom ∉ missSecondBlock → bAtom ∉ missSecondBlock
      → missSecondBlock = {tripleFirst, freshP, freshQ} := by
    intro haNot hbNot
    have hidA : inTwoA = freshP ∨ inTwoA = freshQ := by
      rcases hM2AtomId inTwoA hinTwoAM2 hinTwoANe1 with h | h | h | h
      exacts [absurd (h ▸ hinTwoAM2) haNot, absurd (h ▸ hinTwoAM2) hbNot,
        Or.inl h, Or.inr h]
    have hidB : inTwoB = freshP ∨ inTwoB = freshQ := by
      rcases hM2AtomId inTwoB hinTwoBM2 hinTwoBNe1 with h | h | h | h
      exacts [absurd (h ▸ hinTwoBM2) haNot, absurd (h ▸ hinTwoBM2) hbNot,
        Or.inl h, Or.inr h]
    exact hM2Eq.trans (triple_pin_of_pair_ids hidA hidB hneInTwo)
  rcases haState with ⟨haNotM1, haNotM2⟩ | ⟨haInM1, haNotM2⟩ | ⟨haNotM1, haInM2⟩ <;>
    rcases hbState with ⟨hbNotM1, hbNotM2⟩ | ⟨hbInM1, hbNotM2⟩ | ⟨hbNotM1, hbInM2⟩
  -- (a out, b out): TWIN-PAIRS
  · refine Or.inr (Or.inl ⟨tripleFirst, tripleSecond, freshP, freshQ, aAtom, bAtom,
      hneT12, hpNe1.symm, hqNe1.symm, haNe1.symm, hbNe1.symm, hpNe2.symm, hqNe2.symm,
      haNe2.symm, hbNe2.symm, hnePQ, hpNeA, hpNeB, hqNeA, hqNeB, haNeB, ?_⟩)
    rw [hBothAEq, hBothBEq, hInOneIdOf haNotM1 hbNotM1, hInTwoIdOf haNotM2 hbNotM2]
  -- (a out, b in m1): HOOK with the both-block double bAtom
  · have hidA : inOneA = aAtom ∨ inOneA = bAtom ∨ inOneA = freshP ∨ inOneA = freshQ :=
      hM1AtomId inOneA hinOneAM1 hinOneANe2
    have hidB : inOneB = aAtom ∨ inOneB = bAtom ∨ inOneB = freshP ∨ inOneB = freshQ :=
      hM1AtomId inOneB hinOneBM1 hinOneBNe2
    have hbId : bAtom = inOneA ∨ bAtom = inOneB := by
      rw [hM1Eq] at hbInM1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbInM1
      rcases hbInM1 with h | h | h
      exacts [absurd h hbNe2, Or.inl h, Or.inr h]
    have hM2EqPin := hInTwoIdOf haNotM2 hbNotM2
    have hM1Pin : ∃ freshOther : Fin 6,
        (freshOther = freshP ∨ freshOther = freshQ)
          ∧ missFirstBlock = {tripleSecond, bAtom, freshOther} := by
      rcases hbId with hb | hb
      · have hidOther : inOneB = freshP ∨ inOneB = freshQ := by
          rcases hidB with h | h | h | h
          exacts [absurd (h ▸ hinOneBM1) haNotM1,
            absurd (hb.symm.trans h.symm) hneInOne, Or.inl h, Or.inr h]
        exact ⟨inOneB, hidOther, by rw [hM1Eq, ← hb]⟩
      · have hidOther : inOneA = freshP ∨ inOneA = freshQ := by
          rcases hidA with h | h | h | h
          exacts [absurd (h ▸ hinOneAM1) haNotM1,
            absurd (h.trans hb) hneInOne, Or.inl h, Or.inr h]
        exact ⟨inOneA, hidOther, by
          rw [hM1Eq, ← hb]
          exact tripleSet_swap_second_third tripleSecond inOneA bAtom⟩
    obtain ⟨freshOther, hfreshOtherId, hM1EqPin⟩ := hM1Pin
    rcases hfreshOtherId with rfl | rfl
    · refine Or.inr (Or.inr (Or.inl ⟨tripleFirst, tripleSecond, bAtom, aAtom,
        freshOther, freshQ, hneT12, hbNe1.symm, haNe1.symm, hpNe1.symm, hqNe1.symm,
        hbNe2.symm, haNe2.symm, hpNe2.symm, hqNe2.symm, haNeB.symm, hpNeB.symm,
        hqNeB.symm, hpNeA.symm, hqNeA.symm, hnePQ, ?_⟩))
      rw [quadSet_swap_first_second bothBlockA bothBlockB missFirstBlock
        missSecondBlock, hBothAEq, hBothBEq, hM1EqPin, hM2EqPin]
    · refine Or.inr (Or.inr (Or.inl ⟨tripleFirst, tripleSecond, bAtom, aAtom,
        freshOther, freshP, hneT12, hbNe1.symm, haNe1.symm, hqNe1.symm, hpNe1.symm,
        hbNe2.symm, haNe2.symm, hqNe2.symm, hpNe2.symm, haNeB.symm, hqNeB.symm,
        hpNeB.symm, hqNeA.symm, hpNeA.symm, hnePQ.symm, ?_⟩))
      rw [quadSet_swap_first_second bothBlockA bothBlockB missFirstBlock
        missSecondBlock, hBothAEq, hBothBEq, hM1EqPin,
        hM2EqPin.trans (tripleSet_swap_second_third tripleFirst freshP freshOther)]
  -- (a out, b in m2): NESTED-mirror or hook-mirror? b completes its own miss pair
  · have hM1EqPin := hInOneIdOf haNotM1 hbNotM1
    have hbId : bAtom = inTwoA ∨ bAtom = inTwoB := by
      rw [hM2Eq] at hbInM2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbInM2
      rcases hbInM2 with h | h | h
      exacts [absurd h hbNe1, Or.inl h, Or.inr h]
    have hM2Pin : ∃ freshOther : Fin 6,
        (freshOther = freshP ∨ freshOther = freshQ)
          ∧ missSecondBlock = {tripleFirst, bAtom, freshOther} := by
      rcases hbId with hb | hb
      · have hidOther : inTwoB = freshP ∨ inTwoB = freshQ := by
          rcases hM2AtomId inTwoB hinTwoBM2 hinTwoBNe1 with h | h | h | h
          exacts [absurd (h ▸ hinTwoBM2) haNotM2,
            absurd (hb.symm.trans h.symm) hneInTwo, Or.inl h, Or.inr h]
        exact ⟨inTwoB, hidOther, by rw [hM2Eq, ← hb]⟩
      · have hidOther : inTwoA = freshP ∨ inTwoA = freshQ := by
          rcases hM2AtomId inTwoA hinTwoAM2 hinTwoANe1 with h | h | h | h
          exacts [absurd (h ▸ hinTwoAM2) haNotM2,
            absurd (h.trans hb) hneInTwo, Or.inl h, Or.inr h]
        exact ⟨inTwoA, hidOther, by
          rw [hM2Eq, ← hb]
          exact tripleSet_swap_second_third tripleFirst inTwoA bAtom⟩
    obtain ⟨freshOther, hfreshOtherId, hM2EqPin⟩ := hM2Pin
    rcases hfreshOtherId with rfl | rfl
    · refine Or.inr (Or.inr (Or.inl ⟨tripleSecond, tripleFirst, bAtom, aAtom,
        freshOther, freshQ, hneT12.symm, hbNe2.symm, haNe2.symm, hpNe2.symm,
        hqNe2.symm, hbNe1.symm, haNe1.symm, hpNe1.symm, hqNe1.symm, haNeB.symm,
        hpNeB.symm, hqNeB.symm, hpNeA.symm, hqNeA.symm, hnePQ, ?_⟩))
      rw [quadSet_swap_first_second bothBlockA bothBlockB missFirstBlock
          missSecondBlock,
        quadSet_swap_third_fourth bothBlockB bothBlockA missFirstBlock
          missSecondBlock,
        hBothAEq.trans (tripleSet_swap_first_second tripleFirst tripleSecond aAtom),
        hBothBEq.trans (tripleSet_swap_first_second tripleFirst tripleSecond bAtom),
        hM1EqPin, hM2EqPin]
    · refine Or.inr (Or.inr (Or.inl ⟨tripleSecond, tripleFirst, bAtom, aAtom,
        freshOther, freshP, hneT12.symm, hbNe2.symm, haNe2.symm, hqNe2.symm,
        hpNe2.symm, hbNe1.symm, haNe1.symm, hqNe1.symm, hpNe1.symm, haNeB.symm,
        hqNeB.symm, hpNeB.symm, hqNeA.symm, hpNeA.symm, hnePQ.symm, ?_⟩))
      rw [quadSet_swap_first_second bothBlockA bothBlockB missFirstBlock
          missSecondBlock,
        quadSet_swap_third_fourth bothBlockB bothBlockA missFirstBlock
          missSecondBlock,
        hBothAEq.trans (tripleSet_swap_first_second tripleFirst tripleSecond aAtom),
        hBothBEq.trans (tripleSet_swap_first_second tripleFirst tripleSecond bAtom),
        hM1EqPin.trans (tripleSet_swap_second_third tripleSecond freshP freshOther),
        hM2EqPin]
  -- (a in m1, b out): HOOK with the both-block double aAtom
  · have haId : aAtom = inOneA ∨ aAtom = inOneB := by
      rw [hM1Eq] at haInM1
      simp only [Finset.mem_insert, Finset.mem_singleton] at haInM1
      rcases haInM1 with h | h | h
      exacts [absurd h haNe2, Or.inl h, Or.inr h]
    have hM2EqPin := hInTwoIdOf haNotM2 hbNotM2
    have hM1Pin : ∃ freshOther : Fin 6,
        (freshOther = freshP ∨ freshOther = freshQ)
          ∧ missFirstBlock = {tripleSecond, aAtom, freshOther} := by
      rcases haId with ha | ha
      · have hidOther : inOneB = freshP ∨ inOneB = freshQ := by
          rcases hM1AtomId inOneB hinOneBM1 hinOneBNe2 with h | h | h | h
          exacts [absurd (ha.symm.trans h.symm) hneInOne,
            absurd (h ▸ hinOneBM1) hbNotM1, Or.inl h, Or.inr h]
        exact ⟨inOneB, hidOther, by rw [hM1Eq, ← ha]⟩
      · have hidOther : inOneA = freshP ∨ inOneA = freshQ := by
          rcases hM1AtomId inOneA hinOneAM1 hinOneANe2 with h | h | h | h
          exacts [absurd (h.trans ha) hneInOne,
            absurd (h ▸ hinOneAM1) hbNotM1, Or.inl h, Or.inr h]
        exact ⟨inOneA, hidOther, by
          rw [hM1Eq, ← ha]
          exact tripleSet_swap_second_third tripleSecond inOneA aAtom⟩
    obtain ⟨freshOther, hfreshOtherId, hM1EqPin⟩ := hM1Pin
    rcases hfreshOtherId with rfl | rfl
    · refine Or.inr (Or.inr (Or.inl ⟨tripleFirst, tripleSecond, aAtom, bAtom,
        freshOther, freshQ, hneT12, haNe1.symm, hbNe1.symm, hpNe1.symm, hqNe1.symm,
        haNe2.symm, hbNe2.symm, hpNe2.symm, hqNe2.symm, haNeB, hpNeA.symm,
        hqNeA.symm, hpNeB.symm, hqNeB.symm, hnePQ, ?_⟩))
      rw [hBothAEq, hBothBEq, hM1EqPin, hM2EqPin]
    · refine Or.inr (Or.inr (Or.inl ⟨tripleFirst, tripleSecond, aAtom, bAtom,
        freshOther, freshP, hneT12, haNe1.symm, hbNe1.symm, hqNe1.symm, hpNe1.symm,
        haNe2.symm, hbNe2.symm, hqNe2.symm, hpNe2.symm, haNeB, hqNeA.symm,
        hpNeA.symm, hqNeB.symm, hpNeB.symm, hnePQ.symm, ?_⟩))
      rw [hBothAEq, hBothBEq, hM1EqPin,
        hM2EqPin.trans (tripleSet_swap_second_third tripleFirst freshP freshOther)]
  -- (a in m1, b in m1): NESTED
  · have haId : aAtom = inOneA ∨ aAtom = inOneB := by
      rw [hM1Eq] at haInM1
      simp only [Finset.mem_insert, Finset.mem_singleton] at haInM1
      rcases haInM1 with h | h | h
      exacts [absurd h haNe2, Or.inl h, Or.inr h]
    have hbId : bAtom = inOneA ∨ bAtom = inOneB := by
      rw [hM1Eq] at hbInM1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbInM1
      rcases hbInM1 with h | h | h
      exacts [absurd h hbNe2, Or.inl h, Or.inr h]
    have hM1EqPin : missFirstBlock = {tripleSecond, aAtom, bAtom} := by
      rcases haId with ha | ha <;> rcases hbId with hb | hb
      · exact absurd (ha.trans hb.symm) haNeB
      · rw [hM1Eq, ← ha, ← hb]
      · rw [hM1Eq, ← ha, ← hb]
        exact tripleSet_swap_second_third tripleSecond bAtom aAtom
      · exact absurd (ha.trans hb.symm) haNeB
    have hM2EqPin := hInTwoIdOf haNotM2 hbNotM2
    refine Or.inr (Or.inr (Or.inr ⟨tripleFirst, tripleSecond, aAtom, bAtom, freshP,
      freshQ, hneT12, haNe1.symm, hbNe1.symm, hpNe1.symm, hqNe1.symm, haNe2.symm,
      hbNe2.symm, hpNe2.symm, hqNe2.symm, haNeB, hpNeA.symm, hqNeA.symm, hpNeB.symm,
      hqNeB.symm, hnePQ, ?_⟩))
    rw [hBothAEq, hBothBEq, hM1EqPin, hM2EqPin]
  -- (a in m1, b in m2): ZIGZAG
  · have haId : aAtom = inOneA ∨ aAtom = inOneB := by
      rw [hM1Eq] at haInM1
      simp only [Finset.mem_insert, Finset.mem_singleton] at haInM1
      rcases haInM1 with h | h | h
      exacts [absurd h haNe2, Or.inl h, Or.inr h]
    have hbId : bAtom = inTwoA ∨ bAtom = inTwoB := by
      rw [hM2Eq] at hbInM2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbInM2
      rcases hbInM2 with h | h | h
      exacts [absurd h hbNe1, Or.inl h, Or.inr h]
    have hM1Pin : ∃ singleOne : Fin 6,
        (singleOne = freshP ∨ singleOne = freshQ)
          ∧ missFirstBlock = {tripleSecond, aAtom, singleOne} := by
      rcases haId with ha | ha
      · have hidOther : inOneB = freshP ∨ inOneB = freshQ := by
          rcases hM1AtomId inOneB hinOneBM1 hinOneBNe2 with h | h | h | h
          exacts [absurd (ha.symm.trans h.symm) hneInOne,
            absurd (h ▸ hinOneBM1) hbNotM1, Or.inl h, Or.inr h]
        exact ⟨inOneB, hidOther, by rw [hM1Eq, ← ha]⟩
      · have hidOther : inOneA = freshP ∨ inOneA = freshQ := by
          rcases hM1AtomId inOneA hinOneAM1 hinOneANe2 with h | h | h | h
          exacts [absurd (h.trans ha) hneInOne,
            absurd (h ▸ hinOneAM1) hbNotM1, Or.inl h, Or.inr h]
        exact ⟨inOneA, hidOther, by
          rw [hM1Eq, ← ha]
          exact tripleSet_swap_second_third tripleSecond inOneA aAtom⟩
    have hM2Pin : ∃ singleTwo : Fin 6,
        (singleTwo = freshP ∨ singleTwo = freshQ)
          ∧ missSecondBlock = {tripleFirst, bAtom, singleTwo} := by
      rcases hbId with hb | hb
      · have hidOther : inTwoB = freshP ∨ inTwoB = freshQ := by
          rcases hM2AtomId inTwoB hinTwoBM2 hinTwoBNe1 with h | h | h | h
          exacts [absurd (h ▸ hinTwoBM2) haNotM2,
            absurd (hb.symm.trans h.symm) hneInTwo, Or.inl h, Or.inr h]
        exact ⟨inTwoB, hidOther, by rw [hM2Eq, ← hb]⟩
      · have hidOther : inTwoA = freshP ∨ inTwoA = freshQ := by
          rcases hM2AtomId inTwoA hinTwoAM2 hinTwoANe1 with h | h | h | h
          exacts [absurd (h ▸ hinTwoAM2) haNotM2,
            absurd (h.trans hb) hneInTwo, Or.inl h, Or.inr h]
        exact ⟨inTwoA, hidOther, by
          rw [hM2Eq, ← hb]
          exact tripleSet_swap_second_third tripleFirst inTwoA bAtom⟩
    obtain ⟨singleOne, hsOneId, hM1EqPin⟩ := hM1Pin
    obtain ⟨singleTwo, hsTwoId, hM2EqPin⟩ := hM2Pin
    have hneSingles : singleOne ≠ singleTwo := by
      intro hcontra
      have hsOneM1 : singleOne ∈ missFirstBlock := by
        rw [hM1EqPin]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton_self _))))
      have hsOneM2 : singleOne ∈ missSecondBlock := by
        rw [hM2EqPin, hcontra]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton_self _))))
      have hlonely : ∀ other : Fin 6, (other = freshP ∨ other = freshQ)
          → other ≠ singleOne → False := by
        intro other hotherId hneOther
        rcases exists_mem_of_one_le_fourBlockCoverCount (hcovered other) with
            hmem | hmem | hmem | hmem
        · rw [hBothAEq] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hotherId with rfl | rfl <;> rcases hmem with h | h | h
          exacts [absurd h hpNe1, absurd h hpNe2, absurd h hpNeA,
            absurd h hqNe1, absurd h hqNe2, absurd h hqNeA]
        · rw [hBothBEq] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hotherId with rfl | rfl <;> rcases hmem with h | h | h
          exacts [absurd h hpNe1, absurd h hpNe2, absurd h hpNeB,
            absurd h hqNe1, absurd h hqNe2, absurd h hqNeB]
        · rw [hM1EqPin] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h
          · rcases hotherId with rfl | rfl
            exacts [absurd h hpNe2, absurd h hqNe2]
          · rcases hotherId with rfl | rfl
            exacts [absurd h hpNeA, absurd h hqNeA]
          · exact hneOther h
        · rw [hM2EqPin, ← hcontra] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h
          · rcases hotherId with rfl | rfl
            exacts [absurd h hpNe1, absurd h hqNe1]
          · rcases hotherId with rfl | rfl
            exacts [absurd h hpNeB, absurd h hqNeB]
          · exact hneOther h
      rcases hsOneId with rfl | rfl
      · exact hlonely freshQ (Or.inr rfl) hnePQ.symm
      · exact hlonely freshP (Or.inl rfl) hnePQ
    rcases hsOneId with rfl | rfl <;> rcases hsTwoId with rfl | rfl
    · exact absurd rfl hneSingles
    · refine Or.inl ⟨tripleFirst, tripleSecond, aAtom, bAtom, singleOne, singleTwo,
        hneT12, haNe1.symm, hbNe1.symm, hpNe1.symm, hqNe1.symm, haNe2.symm,
        hbNe2.symm, hpNe2.symm, hqNe2.symm, haNeB, hpNeA.symm, hqNeA.symm,
        hpNeB.symm, hqNeB.symm, hnePQ, ?_⟩
      rw [hBothAEq, hBothBEq, hM1EqPin, hM2EqPin]
    · refine Or.inl ⟨tripleFirst, tripleSecond, aAtom, bAtom, singleOne, singleTwo,
        hneT12, haNe1.symm, hbNe1.symm, hqNe1.symm, hpNe1.symm, haNe2.symm,
        hbNe2.symm, hqNe2.symm, hpNe2.symm, haNeB, hqNeA.symm, hpNeA.symm,
        hqNeB.symm, hpNeB.symm, hnePQ.symm, ?_⟩
      rw [hBothAEq, hBothBEq, hM1EqPin, hM2EqPin]
    · exact absurd rfl hneSingles
  -- (a in m2, b out): HOOK mirror through the second miss
  · have haId : aAtom = inTwoA ∨ aAtom = inTwoB := by
      rw [hM2Eq] at haInM2
      simp only [Finset.mem_insert, Finset.mem_singleton] at haInM2
      rcases haInM2 with h | h | h
      exacts [absurd h haNe1, Or.inl h, Or.inr h]
    have hM1EqPin := hInOneIdOf haNotM1 hbNotM1
    have hM2Pin : ∃ freshOther : Fin 6,
        (freshOther = freshP ∨ freshOther = freshQ)
          ∧ missSecondBlock = {tripleFirst, aAtom, freshOther} := by
      rcases haId with ha | ha
      · have hidOther : inTwoB = freshP ∨ inTwoB = freshQ := by
          rcases hM2AtomId inTwoB hinTwoBM2 hinTwoBNe1 with h | h | h | h
          exacts [absurd (ha.symm.trans h.symm) hneInTwo,
            absurd (h ▸ hinTwoBM2) hbNotM2, Or.inl h, Or.inr h]
        exact ⟨inTwoB, hidOther, by rw [hM2Eq, ← ha]⟩
      · have hidOther : inTwoA = freshP ∨ inTwoA = freshQ := by
          rcases hM2AtomId inTwoA hinTwoAM2 hinTwoANe1 with h | h | h | h
          exacts [absurd (h.trans ha) hneInTwo,
            absurd (h ▸ hinTwoAM2) hbNotM2, Or.inl h, Or.inr h]
        exact ⟨inTwoA, hidOther, by
          rw [hM2Eq, ← ha]
          exact tripleSet_swap_second_third tripleFirst inTwoA aAtom⟩
    obtain ⟨freshOther, hfreshOtherId, hM2EqPin⟩ := hM2Pin
    rcases hfreshOtherId with rfl | rfl
    · refine Or.inr (Or.inr (Or.inl ⟨tripleSecond, tripleFirst, aAtom, bAtom,
        freshOther, freshQ, hneT12.symm, haNe2.symm, hbNe2.symm, hpNe2.symm,
        hqNe2.symm, haNe1.symm, hbNe1.symm, hpNe1.symm, hqNe1.symm, haNeB,
        hpNeA.symm, hqNeA.symm, hpNeB.symm, hqNeB.symm, hnePQ, ?_⟩))
      rw [quadSet_swap_third_fourth bothBlockA bothBlockB missFirstBlock
          missSecondBlock,
        hBothAEq.trans (tripleSet_swap_first_second tripleFirst tripleSecond aAtom),
        hBothBEq.trans (tripleSet_swap_first_second tripleFirst tripleSecond bAtom),
        hM2EqPin, hM1EqPin]
    · refine Or.inr (Or.inr (Or.inl ⟨tripleSecond, tripleFirst, aAtom, bAtom,
        freshOther, freshP, hneT12.symm, haNe2.symm, hbNe2.symm, hqNe2.symm,
        hpNe2.symm, haNe1.symm, hbNe1.symm, hqNe1.symm, hpNe1.symm, haNeB,
        hqNeA.symm, hpNeA.symm, hqNeB.symm, hpNeB.symm, hnePQ.symm, ?_⟩))
      rw [quadSet_swap_third_fourth bothBlockA bothBlockB missFirstBlock
          missSecondBlock,
        hBothAEq.trans (tripleSet_swap_first_second tripleFirst tripleSecond aAtom),
        hBothBEq.trans (tripleSet_swap_first_second tripleFirst tripleSecond bAtom),
        hM2EqPin, hM1EqPin.trans (tripleSet_swap_second_third tripleSecond freshP
          freshOther)]
  -- (a in m2, b in m1): ZIGZAG mirror
  · have haId : aAtom = inTwoA ∨ aAtom = inTwoB := by
      rw [hM2Eq] at haInM2
      simp only [Finset.mem_insert, Finset.mem_singleton] at haInM2
      rcases haInM2 with h | h | h
      exacts [absurd h haNe1, Or.inl h, Or.inr h]
    have hbId : bAtom = inOneA ∨ bAtom = inOneB := by
      rw [hM1Eq] at hbInM1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbInM1
      rcases hbInM1 with h | h | h
      exacts [absurd h hbNe2, Or.inl h, Or.inr h]
    have hM1Pin : ∃ singleOne : Fin 6,
        (singleOne = freshP ∨ singleOne = freshQ)
          ∧ missFirstBlock = {tripleSecond, bAtom, singleOne} := by
      rcases hbId with hb | hb
      · have hidOther : inOneB = freshP ∨ inOneB = freshQ := by
          rcases hM1AtomId inOneB hinOneBM1 hinOneBNe2 with h | h | h | h
          exacts [absurd (h ▸ hinOneBM1) haNotM1,
            absurd (hb.symm.trans h.symm) hneInOne, Or.inl h, Or.inr h]
        exact ⟨inOneB, hidOther, by rw [hM1Eq, ← hb]⟩
      · have hidOther : inOneA = freshP ∨ inOneA = freshQ := by
          rcases hM1AtomId inOneA hinOneAM1 hinOneANe2 with h | h | h | h
          exacts [absurd (h ▸ hinOneAM1) haNotM1,
            absurd (h.trans hb) hneInOne, Or.inl h, Or.inr h]
        exact ⟨inOneA, hidOther, by
          rw [hM1Eq, ← hb]
          exact tripleSet_swap_second_third tripleSecond inOneA bAtom⟩
    have hM2Pin : ∃ singleTwo : Fin 6,
        (singleTwo = freshP ∨ singleTwo = freshQ)
          ∧ missSecondBlock = {tripleFirst, aAtom, singleTwo} := by
      rcases haId with ha | ha
      · have hidOther : inTwoB = freshP ∨ inTwoB = freshQ := by
          rcases hM2AtomId inTwoB hinTwoBM2 hinTwoBNe1 with h | h | h | h
          exacts [absurd (ha.symm.trans h.symm) hneInTwo,
            absurd (h ▸ hinTwoBM2) hbNotM2, Or.inl h, Or.inr h]
        exact ⟨inTwoB, hidOther, by rw [hM2Eq, ← ha]⟩
      · have hidOther : inTwoA = freshP ∨ inTwoA = freshQ := by
          rcases hM2AtomId inTwoA hinTwoAM2 hinTwoANe1 with h | h | h | h
          exacts [absurd (h.trans ha) hneInTwo,
            absurd (h ▸ hinTwoAM2) hbNotM2, Or.inl h, Or.inr h]
        exact ⟨inTwoA, hidOther, by
          rw [hM2Eq, ← ha]
          exact tripleSet_swap_second_third tripleFirst inTwoA aAtom⟩
    obtain ⟨singleOne, hsOneId, hM1EqPin⟩ := hM1Pin
    obtain ⟨singleTwo, hsTwoId, hM2EqPin⟩ := hM2Pin
    have hneSingles : singleOne ≠ singleTwo := by
      intro hcontra
      have hlonely : ∀ other : Fin 6, (other = freshP ∨ other = freshQ)
          → other ≠ singleOne → False := by
        intro other hotherId hneOther
        rcases exists_mem_of_one_le_fourBlockCoverCount (hcovered other) with
            hmem | hmem | hmem | hmem
        · rw [hBothAEq] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hotherId with rfl | rfl <;> rcases hmem with h | h | h
          exacts [absurd h hpNe1, absurd h hpNe2, absurd h hpNeA,
            absurd h hqNe1, absurd h hqNe2, absurd h hqNeA]
        · rw [hBothBEq] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hotherId with rfl | rfl <;> rcases hmem with h | h | h
          exacts [absurd h hpNe1, absurd h hpNe2, absurd h hpNeB,
            absurd h hqNe1, absurd h hqNe2, absurd h hqNeB]
        · rw [hM1EqPin] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h
          · rcases hotherId with rfl | rfl
            exacts [absurd h hpNe2, absurd h hqNe2]
          · rcases hotherId with rfl | rfl
            exacts [absurd h hpNeB, absurd h hqNeB]
          · exact hneOther h
        · rw [hM2EqPin, ← hcontra] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h
          · rcases hotherId with rfl | rfl
            exacts [absurd h hpNe1, absurd h hqNe1]
          · rcases hotherId with rfl | rfl
            exacts [absurd h hpNeA, absurd h hqNeA]
          · exact hneOther h
      rcases hsOneId with rfl | rfl
      · exact hlonely freshQ (Or.inr rfl) hnePQ.symm
      · exact hlonely freshP (Or.inl rfl) hnePQ
    rcases hsOneId with rfl | rfl <;> rcases hsTwoId with rfl | rfl
    · exact absurd rfl hneSingles
    · refine Or.inl ⟨tripleFirst, tripleSecond, bAtom, aAtom, singleOne, singleTwo,
        hneT12, hbNe1.symm, haNe1.symm, hpNe1.symm, hqNe1.symm, hbNe2.symm,
        haNe2.symm, hpNe2.symm, hqNe2.symm, haNeB.symm, hpNeB.symm, hqNeB.symm,
        hpNeA.symm, hqNeA.symm, hnePQ, ?_⟩
      rw [quadSet_swap_first_second bothBlockA bothBlockB missFirstBlock
        missSecondBlock, hBothAEq, hBothBEq, hM1EqPin, hM2EqPin]
    · refine Or.inl ⟨tripleFirst, tripleSecond, bAtom, aAtom, singleOne, singleTwo,
        hneT12, hbNe1.symm, haNe1.symm, hqNe1.symm, hpNe1.symm, hbNe2.symm,
        haNe2.symm, hqNe2.symm, hpNe2.symm, haNeB.symm, hqNeB.symm, hpNeB.symm,
        hqNeA.symm, hpNeA.symm, hnePQ.symm, ?_⟩
      rw [quadSet_swap_first_second bothBlockA bothBlockB missFirstBlock
        missSecondBlock, hBothAEq, hBothBEq, hM1EqPin, hM2EqPin]
    · exact absurd rfl hneSingles
  -- (a in m2, b in m2): NESTED mirror
  · have haId : aAtom = inTwoA ∨ aAtom = inTwoB := by
      rw [hM2Eq] at haInM2
      simp only [Finset.mem_insert, Finset.mem_singleton] at haInM2
      rcases haInM2 with h | h | h
      exacts [absurd h haNe1, Or.inl h, Or.inr h]
    have hbId : bAtom = inTwoA ∨ bAtom = inTwoB := by
      rw [hM2Eq] at hbInM2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbInM2
      rcases hbInM2 with h | h | h
      exacts [absurd h hbNe1, Or.inl h, Or.inr h]
    have hM2EqPin : missSecondBlock = {tripleFirst, aAtom, bAtom} := by
      rcases haId with ha | ha <;> rcases hbId with hb | hb
      · exact absurd (ha.trans hb.symm) haNeB
      · rw [hM2Eq, ← ha, ← hb]
      · rw [hM2Eq, ← ha, ← hb]
        exact tripleSet_swap_second_third tripleFirst bAtom aAtom
      · exact absurd (ha.trans hb.symm) haNeB
    have hM1EqPin := hInOneIdOf haNotM1 hbNotM1
    refine Or.inr (Or.inr (Or.inr ⟨tripleSecond, tripleFirst, aAtom, bAtom, freshP,
      freshQ, hneT12.symm, haNe2.symm, hbNe2.symm, hpNe2.symm, hqNe2.symm,
      haNe1.symm, hbNe1.symm, hpNe1.symm, hqNe1.symm, haNeB, hpNeA.symm, hqNeA.symm,
      hpNeB.symm, hqNeB.symm, hnePQ, ?_⟩))
    rw [quadSet_swap_third_fourth bothBlockA bothBlockB missFirstBlock
        missSecondBlock,
      hBothAEq.trans (tripleSet_swap_first_second tripleFirst tripleSecond aAtom),
      hBothBEq.trans (tripleSet_swap_first_second tripleFirst tripleSecond bAtom),
      hM2EqPin, hM1EqPin]

/-- The canonical trident family: three blocks through the pair `{0,1}`, the
doubles `2,3` closing with the leftover `5`. -/
def canonicalTridentFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {2, 3, 5}}

/-- The canonical zigzag family: each miss block picks up its own
pair-completing double. -/
def canonicalZigzagFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {1, 2, 4}, {0, 3, 5}}

/-- The canonical twin-pairs family: both miss blocks share the double
pair. -/
def canonicalTwinPairsFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 4}, {0, 1, 5}, {1, 2, 3}, {0, 2, 3}}

/-- The canonical hook family: one pair-completing double chains through a
shared fresh double. -/
def canonicalHookFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {1, 2, 4}, {0, 4, 5}}

/-- The canonical nested family: one miss block swallows both
pair-completing atoms. -/
def canonicalNestedFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {1, 2, 3}, {0, 4, 5}}

/-- **THE TWO-TWO-TWO CAPSTONE.**  Any four-block covering family with
profile `(0,2,2,2)` relabels onto one of the five canonical shapes. -/
theorem exists_map_family_eq_canonical_of_profile0222
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock) (hneTwoThree : secondBlock ≠ thirdBlock)
    (hneTwoFour : secondBlock ≠ fourthBlock) (hneThreeFour : thirdBlock ≠ fourthBlock)
    (hcardOne : firstBlock.card = 3) (hcardTwo : secondBlock.card = 3)
    (hcardThree : thirdBlock.card = 3) (hcardFour : fourthBlock.card = 3)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock = Finset.univ)
    (hquadClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4
      = 0)
    (htripleClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3
      = 2) :
    ∃ relabelPerm : Equiv.Perm (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalTridentFamily
        ∨ ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalZigzagFamily
        ∨ ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalTwinPairsFamily
        ∨ ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalHookFamily
        ∨ ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalNestedFamily := by
  classical
  obtain ⟨tripleFirst, tripleSecond, hneT12, hcount1, hcount2⟩ :=
    exists_two_atoms_of_classCard_two htripleClass
  have hthreeOnly : ∀ atom : Fin 6,
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom = 3
        → atom = tripleFirst ∨ atom = tripleSecond := by
    intro atom hcontra
    have hsubset : ({tripleFirst, tripleSecond} : Finset (Fin 6))
        ⊆ Finset.univ.filter fun atomIndex =>
          fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
            = 3 := by
      intro triple hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      exacts [Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcount1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcount2⟩]
    have hpairCard : ({tripleFirst, tripleSecond} : Finset (Fin 6)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hneT12),
        Finset.card_singleton]
    have hfilterCard : (Finset.univ.filter fun atomIndex =>
        fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
          = 3).card = 2 := by
      rw [← fourBlockCountClass]
      exact htripleClass
    have hfilterEq := Finset.eq_of_subset_of_card_le hsubset
      (by rw [hfilterCard, hpairCard])
    have hmemFilter : atom ∈ Finset.univ.filter fun atomIndex =>
        fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
          = 3 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ atom, hcontra⟩
    rw [← hfilterEq] at hmemFilter
    simpa using hmemFilter
  have hcovOrig : ∀ atom : Fin 6,
      1 ≤ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom := by
    intro atom
    have hmem : atom ∈ firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock := by
      rw [hcover]
      exact Finset.mem_univ atom
    simp only [Finset.mem_union] at hmem
    exact one_le_fourBlockCoverCount_of_mem (by tauto)
  rcases exists_missSplit_of_two_count_three hneOneTwo hneOneThree hneOneFour
      hneTwoThree hneTwoFour hneThreeFour hcardOne hcardTwo hcardThree hcardFour
      hcount1 hcount2 with
    ⟨tBlockA, tBlockB, tBlockC, missBlock, hSetEq, hCountEq, hcardA, hcardB, hcardC,
        hcardMiss, hneAB, hneAC, hneBC, hmem1A, hmem1B, hmem1C, hmiss1, hmem2A,
        hmem2B, hmem2C, hmiss2⟩
    | ⟨bothBlockA, bothBlockB, missFirstBlock, missSecondBlock, hSetEq, hCountEq,
        hcardBA, hcardBB, hcardM1, hcardM2, hneBoth, hmem1A, hmem1B, hmiss1M1,
        hmem1M2, hmem2A, hmem2B, hmem2M1, hmiss2M2⟩
  -- shared miss: the TRIDENT
  · obtain ⟨doubleFirst, doubleSecond, singleThird, lastAtom, hdF1, hdF2, hdS1, hdS2,
        hsT1, hsT2, hlast1, hlast2, hdFdS, hdFsT, hdFlast, hdSsT, hdSlast, hsTlast,
        hFormEq⟩ :=
      family_eq_tridentForm_of_sharedMiss hcardA hcardB hcardC hcardMiss hneAB hneAC
        hneBC hneT12 hmem1A hmem1B hmem1C hmiss1 hmem2A hmem2B hmem2C hmiss2
        (fun atom => by rw [hCountEq atom]; exact hcovOrig atom)
    have hinj : Function.Injective
        ![tripleFirst, tripleSecond, doubleFirst, doubleSecond, singleThird,
          lastAtom] :=
      injective_sixAtomAssignment hneT12 hdF1.symm hdS1.symm hsT1.symm hlast1.symm
        hdF2.symm hdS2.symm hsT2.symm hlast2.symm hdFdS hdFsT hdFlast hdSsT hdSlast
        hsTlast
    let atomAssignment : Equiv.Perm (Fin 6) :=
      Equiv.ofBijective
        ![tripleFirst, tripleSecond, doubleFirst, doubleSecond, singleThird, lastAtom]
        (Finite.injective_iff_bijective.mp hinj)
    have hpi0 : atomAssignment.symm tripleFirst = 0 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpi1 : atomAssignment.symm tripleSecond = 1 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpi2 : atomAssignment.symm doubleFirst = 2 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpi3 : atomAssignment.symm doubleSecond = 3 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpi4 : atomAssignment.symm singleThird = 4 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpi5 : atomAssignment.symm lastAtom = 5 := by
      rw [Equiv.symm_apply_eq]; rfl
    refine ⟨atomAssignment.symm, Or.inl ?_⟩
    rw [hSetEq, hFormEq]
    simp only [Finset.image_insert, Finset.image_singleton]
    rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
      map_triple_toEmbedding, hpi0, hpi1, hpi2, hpi3, hpi4, hpi5]
    rfl
  -- split miss: the ZIGZAG, TWIN-PAIRS, HOOK, or NESTED
  · have hcoveredTuple : ∀ atom : Fin 6, 1 ≤ fourBlockCoverCount bothBlockA bothBlockB
        missFirstBlock missSecondBlock atom := by
      intro atom
      rw [hCountEq atom]
      exact hcovOrig atom
    have hthreeOnlyTuple : ∀ atom : Fin 6, fourBlockCoverCount bothBlockA bothBlockB
        missFirstBlock missSecondBlock atom = 3
        → atom = tripleFirst ∨ atom = tripleSecond :=
      fun atom h => hthreeOnly atom ((hCountEq atom).symm.trans h)
    have hquadNoneTuple : ∀ atom : Fin 6, fourBlockCoverCount bothBlockA bothBlockB
        missFirstBlock missSecondBlock atom ≠ 4 :=
      fun atom h => count_ne_of_classCard_zero hquadClass atom
        ((hCountEq atom).symm.trans h)
    rcases family_eq_splitMissForm_of_splitMiss hcardBA hcardBB hcardM1 hcardM2
        hneBoth hneT12 hmem1A hmem1B hmiss1M1 hmem1M2 hmem2A hmem2B hmem2M1 hmiss2M2
        hcoveredTuple hthreeOnlyTuple hquadNoneTuple with
      ⟨atomZero, atomOne, atomTwo, atomThree, atomFour, atomFive, hne01, hne02, hne03,
          hne04, hne05, hne12, hne13, hne14, hne15, hne23, hne24, hne25, hne34, hne35,
          hne45, hFormEq⟩
      | ⟨atomZero, atomOne, atomTwo, atomThree, atomFour, atomFive, hne01, hne02,
          hne03, hne04, hne05, hne12, hne13, hne14, hne15, hne23, hne24, hne25, hne34,
          hne35, hne45, hFormEq⟩
      | ⟨atomZero, atomOne, atomTwo, atomThree, atomFour, atomFive, hne01, hne02,
          hne03, hne04, hne05, hne12, hne13, hne14, hne15, hne23, hne24, hne25, hne34,
          hne35, hne45, hFormEq⟩
      | ⟨atomZero, atomOne, atomTwo, atomThree, atomFour, atomFive, hne01, hne02,
          hne03, hne04, hne05, hne12, hne13, hne14, hne15, hne23, hne24, hne25, hne34,
          hne35, hne45, hFormEq⟩
    all_goals
      have hinj : Function.Injective
          ![atomZero, atomOne, atomTwo, atomThree, atomFour, atomFive] :=
        injective_sixAtomAssignment hne01 hne02 hne03 hne04 hne05 hne12 hne13 hne14
          hne15 hne23 hne24 hne25 hne34 hne35 hne45
    all_goals
      let atomAssignment : Equiv.Perm (Fin 6) :=
        Equiv.ofBijective ![atomZero, atomOne, atomTwo, atomThree, atomFour, atomFive]
          (Finite.injective_iff_bijective.mp hinj)
    all_goals
      have hpi0 : atomAssignment.symm atomZero = 0 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi1 : atomAssignment.symm atomOne = 1 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi2 : atomAssignment.symm atomTwo = 2 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi3 : atomAssignment.symm atomThree = 3 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi4 : atomAssignment.symm atomFour = 4 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi5 : atomAssignment.symm atomFive = 5 := by
        rw [Equiv.symm_apply_eq]; rfl
    · refine ⟨atomAssignment.symm, Or.inr (Or.inl ?_)⟩
      rw [hSetEq, hFormEq]
      simp only [Finset.image_insert, Finset.image_singleton]
      rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
        map_triple_toEmbedding, hpi0, hpi1, hpi2, hpi3, hpi4, hpi5]
      rfl
    · refine ⟨atomAssignment.symm, Or.inr (Or.inr (Or.inl ?_))⟩
      rw [hSetEq, hFormEq]
      simp only [Finset.image_insert, Finset.image_singleton]
      rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
        map_triple_toEmbedding, hpi0, hpi1, hpi2, hpi3, hpi4, hpi5]
      rfl
    · refine ⟨atomAssignment.symm, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
      rw [hSetEq, hFormEq]
      simp only [Finset.image_insert, Finset.image_singleton]
      rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
        map_triple_toEmbedding, hpi0, hpi1, hpi2, hpi3, hpi4, hpi5]
      rfl
    · refine ⟨atomAssignment.symm, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
      rw [hSetEq, hFormEq]
      simp only [Finset.image_insert, Finset.image_singleton]
      rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
        map_triple_toEmbedding, hpi0, hpi1, hpi2, hpi3, hpi4, hpi5]
      rfl

end Gtz

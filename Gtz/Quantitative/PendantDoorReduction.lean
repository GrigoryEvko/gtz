import Mathlib
import Gtz.Quantitative.TwoTwoTwoDoorReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The pendant door: profile (0,1,4,1) closed end to end

One triple atom, four double atoms, one single atom admit exactly three
shapes.  The triple atom threads three blocks and misses one; the single
atom either sits in the miss block — the DOUBLE-PATH, whose four doubles
chain end-to-end through the triple blocks — or completes one triple block
beside a partner double, which either avoids the miss block (the
PENDANT-SPLIT: the partner chains into one further triple block and the
miss block is the remaining double triple) or sits in it (the PENDANT-FORK:
a fresh double forks through both remaining triple blocks).  Explicit
permutations land all three on canonical representatives, completing the
fifteen-representative census of covering four-families.
-/

namespace Gtz

/-- **The single-miss normalization.**  The triple atom's miss reorders the
family, cover counts carried verbatim. -/
theorem exists_missOne_of_count_three
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock) (hneTwoThree : secondBlock ≠ thirdBlock)
    (hneTwoFour : secondBlock ≠ fourthBlock) (hneThreeFour : thirdBlock ≠ fourthBlock)
    (hcardOne : firstBlock.card = 3) (hcardTwo : secondBlock.card = 3)
    (hcardThree : thirdBlock.card = 3) (hcardFour : fourthBlock.card = 3)
    {tripleAtom : Fin 6}
    (hcount : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
      tripleAtom = 3) :
    ∃ threadA threadB threadC missBlock : Finset (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} : Finset (Finset (Fin 6)))
          = {threadA, threadB, threadC, missBlock}
        ∧ (∀ atom : Fin 6, fourBlockCoverCount threadA threadB threadC missBlock atom
            = fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom)
        ∧ threadA.card = 3 ∧ threadB.card = 3 ∧ threadC.card = 3 ∧ missBlock.card = 3
        ∧ threadA ≠ threadB ∧ threadA ≠ threadC ∧ threadB ≠ threadC
        ∧ tripleAtom ∈ threadA ∧ tripleAtom ∈ threadB ∧ tripleAtom ∈ threadC
        ∧ tripleAtom ∉ missBlock := by
  rcases fourBlockCoverCount_eq_three_inversion hcount with
      ⟨htFirst, htSecond, htThird, htFourth⟩ | ⟨htFirst, htSecond, htThird, htFourth⟩
    | ⟨htFirst, htSecond, htThird, htFourth⟩ | ⟨htFirst, htSecond, htThird, htFourth⟩
  · refine ⟨secondBlock, thirdBlock, fourthBlock, firstBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardThree, hcardFour,
      hcardOne, hneTwoThree, hneTwoFour, hneThreeFour, htSecond, htThird, htFourth,
      htFirst⟩
    rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_second_third secondBlock firstBlock thirdBlock fourthBlock,
      quadSet_swap_third_fourth secondBlock thirdBlock firstBlock fourthBlock]
  · refine ⟨firstBlock, thirdBlock, fourthBlock, secondBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardThree, hcardFour,
      hcardTwo, hneOneThree, hneOneFour, hneThreeFour, htFirst, htThird, htFourth,
      htSecond⟩
    rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock]
  · refine ⟨firstBlock, secondBlock, fourthBlock, thirdBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardTwo, hcardFour,
      hcardThree, hneOneTwo, hneOneFour, hneTwoFour, htFirst, htSecond, htFourth,
      htThird⟩
    rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock]
  · exact ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, rfl, fun atom => rfl,
      hcardOne, hcardTwo, hcardThree, hcardFour, hneOneTwo, hneOneThree, hneTwoThree,
      htFirst, htSecond, htThird, htFourth⟩

/-- **The thread-first normalization.**  A named atom in one of the three
thread blocks reorders them so its block leads, all data carried along. -/
theorem exists_threadFirst_of_mem
    {threadA threadB threadC missBlock : Finset (Fin 6)}
    (hcardA : threadA.card = 3) (hcardB : threadB.card = 3) (hcardC : threadC.card = 3)
    (hneAB : threadA ≠ threadB) (hneAC : threadA ≠ threadC) (hneBC : threadB ≠ threadC)
    {tripleAtom : Fin 6}
    (hmemA : tripleAtom ∈ threadA) (hmemB : tripleAtom ∈ threadB)
    (hmemC : tripleAtom ∈ threadC)
    {namedAtom : Fin 6}
    (hnamed : namedAtom ∈ threadA ∨ namedAtom ∈ threadB ∨ namedAtom ∈ threadC) :
    ∃ leadBlock otherBlockA otherBlockB : Finset (Fin 6),
      ({threadA, threadB, threadC, missBlock} : Finset (Finset (Fin 6)))
          = {leadBlock, otherBlockA, otherBlockB, missBlock}
        ∧ (∀ atom : Fin 6, fourBlockCoverCount leadBlock otherBlockA otherBlockB
            missBlock atom
              = fourBlockCoverCount threadA threadB threadC missBlock atom)
        ∧ leadBlock.card = 3 ∧ otherBlockA.card = 3 ∧ otherBlockB.card = 3
        ∧ leadBlock ≠ otherBlockA ∧ leadBlock ≠ otherBlockB
        ∧ otherBlockA ≠ otherBlockB
        ∧ tripleAtom ∈ leadBlock ∧ tripleAtom ∈ otherBlockA
        ∧ tripleAtom ∈ otherBlockB
        ∧ namedAtom ∈ leadBlock := by
  rcases hnamed with hnamed | hnamed | hnamed
  · exact ⟨threadA, threadB, threadC, rfl, fun atom => rfl, hcardA, hcardB, hcardC,
      hneAB, hneAC, hneBC, hmemA, hmemB, hmemC, hnamed⟩
  · refine ⟨threadB, threadA, threadC, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardB, hcardA, hcardC,
      hneAB.symm, hneBC, hneAC, hmemB, hmemA, hmemC, hnamed⟩
    rw [quadSet_swap_first_second threadA threadB threadC missBlock]
  · refine ⟨threadC, threadA, threadB, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardC, hcardA, hcardB,
      hneAC.symm, hneBC.symm, hneAB, hmemC, hmemA, hmemB, hnamed⟩
    rw [quadSet_swap_second_third threadA threadB threadC missBlock,
      quadSet_swap_first_second threadA threadC threadB missBlock]

/-- **The double-path extraction.**  The single atom in the miss block chains
the four doubles end-to-end through the thread blocks. -/
theorem family_eq_doublePathForm_of_sMemMiss
    {threadA threadB threadC missBlock : Finset (Fin 6)}
    (hcardA : threadA.card = 3) (hcardB : threadB.card = 3) (hcardC : threadC.card = 3)
    (hcardMiss : missBlock.card = 3)
    (hneAB : threadA ≠ threadB) (hneAC : threadA ≠ threadC) (hneBC : threadB ≠ threadC)
    {tripleAtom singleAtom : Fin 6} (hneTs : tripleAtom ≠ singleAtom)
    (hmemTA : tripleAtom ∈ threadA) (hmemTB : tripleAtom ∈ threadB)
    (hmemTC : tripleAtom ∈ threadC) (hmissT : tripleAtom ∉ missBlock)
    (hsMemMiss : singleAtom ∈ missBlock)
    (hsCount : fourBlockCoverCount threadA threadB threadC missBlock singleAtom = 1)
    (hthreeOnly : ∀ atom : Fin 6, fourBlockCoverCount threadA threadB threadC missBlock
      atom = 3 → atom = tripleAtom)
    (hsingleOnly : ∀ atom : Fin 6, fourBlockCoverCount threadA threadB threadC
      missBlock atom = 1 → atom = singleAtom)
    (hquadNone : ∀ atom : Fin 6, fourBlockCoverCount threadA threadB threadC missBlock
      atom ≠ 4)
    (hcovered : ∀ atom : Fin 6,
      1 ≤ fourBlockCoverCount threadA threadB threadC missBlock atom) :
    ∃ edgeFirst nearDouble farDouble edgeSecond : Fin 6,
      tripleAtom ≠ edgeFirst ∧ tripleAtom ≠ nearDouble ∧ tripleAtom ≠ farDouble
        ∧ tripleAtom ≠ edgeSecond ∧ tripleAtom ≠ singleAtom
        ∧ edgeFirst ≠ nearDouble ∧ edgeFirst ≠ farDouble ∧ edgeFirst ≠ edgeSecond
        ∧ edgeFirst ≠ singleAtom ∧ nearDouble ≠ farDouble ∧ nearDouble ≠ edgeSecond
        ∧ nearDouble ≠ singleAtom ∧ farDouble ≠ edgeSecond ∧ farDouble ≠ singleAtom
        ∧ edgeSecond ≠ singleAtom
        ∧ ({threadA, threadB, threadC, missBlock} : Finset (Finset (Fin 6)))
            = {{tripleAtom, edgeFirst, nearDouble},
               {tripleAtom, nearDouble, farDouble},
               {tripleAtom, farDouble, edgeSecond},
               {edgeFirst, edgeSecond, singleAtom}} := by
  have hsPair := pairwise_notMem_of_fourBlockCoverCount_le_one hsCount.le
  have hsNotA : singleAtom ∉ threadA := fun h => hsPair.2.2.1 ⟨h, hsMemMiss⟩
  have hsNotB : singleAtom ∉ threadB := fun h => hsPair.2.2.2.2.1 ⟨h, hsMemMiss⟩
  have hsNotC : singleAtom ∉ threadC := fun h => hsPair.2.2.2.2.2 ⟨h, hsMemMiss⟩
  have heraseMiss : (missBlock.erase singleAtom).card = 2 := by
    rw [Finset.card_erase_of_mem hsMemMiss, hcardMiss]
  obtain ⟨endOne, endTwo, hneEnds, heraseEq⟩ := Finset.card_eq_two.mp heraseMiss
  have hEndOneErase : endOne ∈ missBlock.erase singleAtom := by
    rw [heraseEq]
    exact Finset.mem_insert_self _ _
  have hEndTwoErase : endTwo ∈ missBlock.erase singleAtom := by
    rw [heraseEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hEndOneMiss : endOne ∈ missBlock := (Finset.mem_erase.mp hEndOneErase).2
  have hEndTwoMiss : endTwo ∈ missBlock := (Finset.mem_erase.mp hEndTwoErase).2
  have hEndOneNeS : endOne ≠ singleAtom := (Finset.mem_erase.mp hEndOneErase).1
  have hEndTwoNeS : endTwo ≠ singleAtom := (Finset.mem_erase.mp hEndTwoErase).1
  have hEndOneNeT : endOne ≠ tripleAtom := fun h => hmissT (h ▸ hEndOneMiss)
  have hEndTwoNeT : endTwo ≠ tripleAtom := fun h => hmissT (h ▸ hEndTwoMiss)
  have hMissEq : missBlock = {singleAtom, endOne, endTwo} := by
    rw [← Finset.insert_erase hsMemMiss, heraseEq]
  have hdoubleOf : ∀ atom : Fin 6, atom ≠ tripleAtom → atom ≠ singleAtom
      → 1 ≤ fourBlockCoverCount threadA threadB threadC missBlock atom
      → fourBlockCoverCount threadA threadB threadC missBlock atom = 2 := by
    intro atom hneT hneS hge
    have hle := fourBlockCoverCount_le_four threadA threadB threadC missBlock atom
    have hne3 : fourBlockCoverCount threadA threadB threadC missBlock atom ≠ 3 :=
      fun h => hneT (hthreeOnly atom h)
    have hne1 : fourBlockCoverCount threadA threadB threadC missBlock atom ≠ 1 :=
      fun h => hneS (hsingleOnly atom h)
    have hne4 := hquadNone atom
    omega
  have hEndOneCount := hdoubleOf endOne hEndOneNeT hEndOneNeS
    (one_le_fourBlockCoverCount_of_mem (Or.inr (Or.inr (Or.inr hEndOneMiss))))
  have hEndOneThread : endOne ∈ threadA ∨ endOne ∈ threadB ∨ endOne ∈ threadC := by
    rcases fourBlockCoverCount_eq_two_inversion hEndOneCount with
        ⟨ha, hb, _, hd⟩ | ⟨ha, _, hc, hd⟩ | ⟨ha, _, _, _⟩ | ⟨_, hb, hc, hd⟩
      | ⟨_, hb, _, _⟩ | ⟨_, _, hc, _⟩
    exacts [absurd hEndOneMiss hd, absurd hEndOneMiss hd, Or.inl ha,
      absurd hEndOneMiss hd, Or.inr (Or.inl hb), Or.inr (Or.inr hc)]
  obtain ⟨leadBlock, otherBlockA, otherBlockB, hReorderEq, hCountEq2, hcardLead,
      hcardOA, hcardOB, hneLeadOA, hneLeadOB, hneOAOB, hmemTLead, hmemTOA, hmemTOB,
      hEndOneLead⟩ :=
    exists_threadFirst_of_mem hcardA hcardB hcardC hneAB hneAC hneBC hmemTA hmemTB
      hmemTC hEndOneThread
  have hmissTupleEq : ∀ atom : Fin 6, fourBlockCoverCount leadBlock otherBlockA
      otherBlockB missBlock atom
        = fourBlockCoverCount threadA threadB threadC missBlock atom := hCountEq2
  obtain ⟨nearAtom, hnearNeT, hnearNeEndOne, hLeadEq⟩ :=
    exists_third_of_pair_mem_card_three hcardLead hEndOneNeT.symm hmemTLead
      hEndOneLead
  have hnearLead : nearAtom ∈ leadBlock := by
    rw [hLeadEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self _))))
  have hsNotLead : singleAtom ∉ leadBlock := by
    intro h
    have hs2 : 1 ≤ fourBlockCoverCount leadBlock otherBlockA otherBlockB missBlock
        singleAtom := one_le_fourBlockCoverCount_of_mem (Or.inl h)
    have hsPair2 := pairwise_notMem_of_fourBlockCoverCount_le_one
      (le_of_eq ((hmissTupleEq singleAtom).trans hsCount))
    exact hsPair2.2.2.1 ⟨h, hsMemMiss⟩
  have hnearNeS : nearAtom ≠ singleAtom := fun h => hsNotLead (h ▸ hnearLead)
  have hEndOnePattern : endOne ∉ otherBlockA ∧ endOne ∉ otherBlockB := by
    rcases fourBlockCoverCount_eq_two_inversion
        ((hmissTupleEq endOne).trans hEndOneCount) with
        ⟨_, _, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨_, hb, hc, _⟩ | ⟨ha, _, _, _⟩
      | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩
    exacts [absurd hEndOneMiss hd, absurd hEndOneMiss hd, ⟨hb, hc⟩,
      absurd hEndOneLead ha, absurd hEndOneLead ha, absurd hEndOneLead ha]
  have hEndTwoCount := hdoubleOf endTwo hEndTwoNeT hEndTwoNeS
    (one_le_fourBlockCoverCount_of_mem (Or.inr (Or.inr (Or.inr hEndTwoMiss))))
  have hFourCard : ({tripleAtom, singleAtom, endOne, endTwo} :
      Finset (Fin 6)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp [hneTs, hEndOneNeT.symm, hEndTwoNeT.symm]),
      Finset.card_insert_of_notMem (by simp [hEndOneNeS.symm, hEndTwoNeS.symm]),
      Finset.card_insert_of_notMem (by simp [hneEnds]), Finset.card_singleton]
  have hcomplCard : (({tripleAtom, singleAtom, endOne, endTwo} :
      Finset (Fin 6))ᶜ).card = 2 := by
    rw [Finset.card_compl, hFourCard, Fintype.card_fin]
  obtain ⟨freshP, freshQ, hnePQ, hcomplEq⟩ := Finset.card_eq_two.mp hcomplCard
  have hpNot : freshP ∉ ({tripleAtom, singleAtom, endOne, endTwo} :
      Finset (Fin 6)) := by
    rw [← Finset.mem_compl, hcomplEq]
    exact Finset.mem_insert_self _ _
  have hqNot : freshQ ∉ ({tripleAtom, singleAtom, endOne, endTwo} :
      Finset (Fin 6)) := by
    rw [← Finset.mem_compl, hcomplEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpNot hqNot
  push Not at hpNot hqNot
  obtain ⟨hpNeT, hpNeS, hpNeEndOne, hpNeEndTwo⟩ := hpNot
  obtain ⟨hqNeT, hqNeS, hqNeEndOne, hqNeEndTwo⟩ := hqNot
  have hSixEq : ({tripleAtom, singleAtom, endOne, endTwo, freshP, freshQ} :
      Finset (Fin 6)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by
        simp [hneTs, hEndOneNeT.symm, hEndTwoNeT.symm, hpNeT.symm, hqNeT.symm]),
      Finset.card_insert_of_notMem (by
        simp [hEndOneNeS.symm, hEndTwoNeS.symm, hpNeS.symm, hqNeS.symm]),
      Finset.card_insert_of_notMem (by simp [hneEnds, hpNeEndOne.symm,
        hqNeEndOne.symm]),
      Finset.card_insert_of_notMem (by simp [hpNeEndTwo.symm, hqNeEndTwo.symm]),
      Finset.card_insert_of_notMem (by simp [hnePQ]), Finset.card_singleton,
      Fintype.card_fin]
  have hnearNeEndTwo : nearAtom ≠ endTwo := by
    intro hcontra
    have hLeadPin : leadBlock = {tripleAtom, endOne, endTwo} := by
      rw [hLeadEq, hcontra]
    have hEndTwoPattern : endTwo ∉ otherBlockA ∧ endTwo ∉ otherBlockB := by
      have hEndTwoLead : endTwo ∈ leadBlock := by
        rw [hLeadPin]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton_self _))))
      rcases fourBlockCoverCount_eq_two_inversion
          ((hmissTupleEq endTwo).trans hEndTwoCount) with
          ⟨_, _, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨_, hb, hc, _⟩ | ⟨ha, _, _, _⟩
        | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩
      exacts [absurd hEndTwoMiss hd, absurd hEndTwoMiss hd, ⟨hb, hc⟩,
        absurd hEndTwoLead ha, absurd hEndTwoLead ha, absurd hEndTwoLead ha]
    have hpinOf : ∀ block : Finset (Fin 6), block.card = 3 → tripleAtom ∈ block
        → singleAtom ∉ block → endOne ∉ block → endTwo ∉ block
        → block = {tripleAtom, freshP, freshQ} := by
      intro block hcardBlock hTmem hsNot hOneNot hTwoNot
      have heraseBlock : (block.erase tripleAtom).card = 2 := by
        rw [Finset.card_erase_of_mem hTmem, hcardBlock]
      obtain ⟨uAtom, vAtom, hneUV, heraseBlockEq⟩ :=
        Finset.card_eq_two.mp heraseBlock
      have hIdOf : ∀ atom, atom ∈ block.erase tripleAtom
          → atom = freshP ∨ atom = freshQ := by
        intro atom hmemErase
        have hmemBlock : atom ∈ block := (Finset.mem_erase.mp hmemErase).2
        have hneTa : atom ≠ tripleAtom := (Finset.mem_erase.mp hmemErase).1
        have hmemSix : atom ∈ ({tripleAtom, singleAtom, endOne, endTwo, freshP,
            freshQ} : Finset (Fin 6)) := by
          rw [hSixEq]
          exact Finset.mem_univ atom
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmemSix
        rcases hmemSix with rfl | rfl | rfl | rfl | h | h
        exacts [absurd rfl hneTa, absurd hmemBlock hsNot, absurd hmemBlock hOneNot,
          absurd hmemBlock hTwoNot, Or.inl h, Or.inr h]
      have hBlockEq : block = {tripleAtom, uAtom, vAtom} := by
        rw [← Finset.insert_erase hTmem, heraseBlockEq]
      have hidU : uAtom = freshP ∨ uAtom = freshQ := by
        apply hIdOf
        rw [heraseBlockEq]
        exact Finset.mem_insert_self _ _
      have hidV : vAtom = freshP ∨ vAtom = freshQ := by
        apply hIdOf
        rw [heraseBlockEq]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
      exact hBlockEq.trans (triple_pin_of_pair_ids hidU hidV hneUV)
    have hsNotOA : singleAtom ∉ otherBlockA := fun h =>
      (pairwise_notMem_of_fourBlockCoverCount_le_one
        (le_of_eq ((hmissTupleEq singleAtom).trans hsCount))).2.2.2.2.1
        ⟨h, hsMemMiss⟩
    have hsNotOB : singleAtom ∉ otherBlockB := fun h =>
      (pairwise_notMem_of_fourBlockCoverCount_le_one
        (le_of_eq ((hmissTupleEq singleAtom).trans hsCount))).2.2.2.2.2
        ⟨h, hsMemMiss⟩
    have hOAPin := hpinOf otherBlockA hcardOA hmemTOA hsNotOA hEndOnePattern.1
      hEndTwoPattern.1
    have hOBPin := hpinOf otherBlockB hcardOB hmemTOB hsNotOB hEndOnePattern.2
      hEndTwoPattern.2
    exact hneOAOB (hOAPin.trans hOBPin.symm)
  have hnearId : nearAtom = freshP ∨ nearAtom = freshQ := by
    have hmemSix : nearAtom ∈ ({tripleAtom, singleAtom, endOne, endTwo, freshP,
        freshQ} : Finset (Fin 6)) := by
      rw [hSixEq]
      exact Finset.mem_univ nearAtom
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemSix
    rcases hmemSix with rfl | rfl | rfl | rfl | h | h
    exacts [absurd rfl hnearNeT, absurd rfl hnearNeS, absurd rfl hnearNeEndOne,
      absurd rfl hnearNeEndTwo, Or.inl h, Or.inr h]
  have hMissRelist : missBlock = {endOne, endTwo, singleAtom} :=
    eq_triple_of_mem_mem_mem_card_three hcardMiss hneEnds hEndOneNeS hEndTwoNeS
      hEndOneMiss hEndTwoMiss hsMemMiss
  have hmain : ∀ farAtom : Fin 6, farAtom ≠ tripleAtom → farAtom ≠ singleAtom
      → farAtom ≠ endOne → farAtom ≠ endTwo → farAtom ≠ nearAtom
      → ∃ edgeFirst nearDouble farDouble edgeSecond : Fin 6,
        tripleAtom ≠ edgeFirst ∧ tripleAtom ≠ nearDouble ∧ tripleAtom ≠ farDouble
          ∧ tripleAtom ≠ edgeSecond ∧ tripleAtom ≠ singleAtom
          ∧ edgeFirst ≠ nearDouble ∧ edgeFirst ≠ farDouble ∧ edgeFirst ≠ edgeSecond
          ∧ edgeFirst ≠ singleAtom ∧ nearDouble ≠ farDouble
          ∧ nearDouble ≠ edgeSecond ∧ nearDouble ≠ singleAtom
          ∧ farDouble ≠ edgeSecond ∧ farDouble ≠ singleAtom
          ∧ edgeSecond ≠ singleAtom
          ∧ ({threadA, threadB, threadC, missBlock} : Finset (Finset (Fin 6)))
              = {{tripleAtom, edgeFirst, nearDouble},
                 {tripleAtom, nearDouble, farDouble},
                 {tripleAtom, farDouble, edgeSecond},
                 {edgeFirst, edgeSecond, singleAtom}} := by
    intro farAtom hfarNeT hfarNeS hfarNeEndOne hfarNeEndTwo hfarNeNear
    have hfarNotMiss : farAtom ∉ missBlock := by
      rw [hMissEq]
      simp [hfarNeS, hfarNeEndOne, hfarNeEndTwo]
    have hfarNotLead : farAtom ∉ leadBlock := by
      rw [hLeadEq]
      simp [hfarNeT, hfarNeEndOne, hfarNeNear]
    have hfarCount := hdoubleOf farAtom hfarNeT hfarNeS (hcovered farAtom)
    have hfarBoth : farAtom ∈ otherBlockA ∧ farAtom ∈ otherBlockB := by
      rcases fourBlockCoverCount_eq_two_inversion
          ((hmissTupleEq farAtom).trans hfarCount) with
          ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨_, hb, hc, _⟩
        | ⟨_, _, _, hd⟩ | ⟨_, _, _, hd⟩
      exacts [absurd ha hfarNotLead, absurd ha hfarNotLead, absurd ha hfarNotLead,
        ⟨hb, hc⟩, absurd hd hfarNotMiss, absurd hd hfarNotMiss]
    have hnearCountCore : fourBlockCoverCount threadA threadB threadC missBlock
        nearAtom = 2 := by
      apply hdoubleOf nearAtom hnearNeT hnearNeS
      rw [← hmissTupleEq nearAtom]
      exact one_le_fourBlockCoverCount_of_mem (Or.inl hnearLead)
    have hEndTwoSecond : endTwo ∈ otherBlockA ∨ endTwo ∈ otherBlockB := by
      have hEndTwoNotLead : endTwo ∉ leadBlock := by
        rw [hLeadEq]
        simp [hEndTwoNeT, Ne.symm hneEnds, Ne.symm hnearNeEndTwo]
      rcases fourBlockCoverCount_eq_two_inversion
          ((hmissTupleEq endTwo).trans hEndTwoCount) with
          ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨_, hb, _, hd⟩
        | ⟨_, hb, _, hd⟩ | ⟨_, _, hc, hd⟩
      exacts [absurd ha hEndTwoNotLead, absurd ha hEndTwoNotLead,
        absurd ha hEndTwoNotLead, Or.inl hb, Or.inl hb, Or.inr hc]
    rcases fourBlockCoverCount_eq_two_inversion
        ((hmissTupleEq nearAtom).trans hnearCountCore) with
        ⟨_, hnearOA, hnearNotOB, _⟩ | ⟨_, hnearNotOA, hnearOB, _⟩
      | ⟨_, _, _, hnearMiss⟩ | ⟨hnearNotLead, _, _, _⟩ | ⟨hnearNotLead, _, _, _⟩
      | ⟨hnearNotLead, _, _, _⟩
    · -- nearAtom continues into otherBlockA
      have hOAEq : otherBlockA = {tripleAtom, nearAtom, farAtom} :=
        eq_triple_of_mem_mem_mem_card_three hcardOA hnearNeT.symm hfarNeT.symm
          (fun h => hfarNeNear h.symm) hmemTOA hnearOA hfarBoth.1
      have hEndTwoOB : endTwo ∈ otherBlockB := by
        rcases hEndTwoSecond with h | h
        · rw [hOAEq] at h
          simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with h | h | h
          exacts [absurd h hEndTwoNeT, absurd h (Ne.symm hnearNeEndTwo),
            absurd h (Ne.symm hfarNeEndTwo)]
        · exact h
      have hOBEq : otherBlockB = {tripleAtom, farAtom, endTwo} :=
        eq_triple_of_mem_mem_mem_card_three hcardOB hfarNeT.symm hEndTwoNeT.symm
          hfarNeEndTwo hmemTOB hfarBoth.2 hEndTwoOB
      refine ⟨endOne, nearAtom, farAtom, endTwo, hEndOneNeT.symm, hnearNeT.symm,
        hfarNeT.symm, hEndTwoNeT.symm, hneTs, Ne.symm hnearNeEndOne,
        Ne.symm hfarNeEndOne, hneEnds, hEndOneNeS, Ne.symm hfarNeNear,
        hnearNeEndTwo, hnearNeS, hfarNeEndTwo, hfarNeS, hEndTwoNeS, ?_⟩
      rw [hReorderEq, hLeadEq, hOAEq, hOBEq, hMissRelist]
    · -- nearAtom continues into otherBlockB
      have hOBEq : otherBlockB = {tripleAtom, nearAtom, farAtom} :=
        eq_triple_of_mem_mem_mem_card_three hcardOB hnearNeT.symm hfarNeT.symm
          (fun h => hfarNeNear h.symm) hmemTOB hnearOB hfarBoth.2
      have hEndTwoOA : endTwo ∈ otherBlockA := by
        rcases hEndTwoSecond with h | h
        · exact h
        · rw [hOBEq] at h
          simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with h | h | h
          exacts [absurd h hEndTwoNeT, absurd h (Ne.symm hnearNeEndTwo),
            absurd h (Ne.symm hfarNeEndTwo)]
      have hOAEq : otherBlockA = {tripleAtom, farAtom, endTwo} :=
        eq_triple_of_mem_mem_mem_card_three hcardOA hfarNeT.symm hEndTwoNeT.symm
          hfarNeEndTwo hmemTOA hfarBoth.1 hEndTwoOA
      refine ⟨endOne, nearAtom, farAtom, endTwo, hEndOneNeT.symm, hnearNeT.symm,
        hfarNeT.symm, hEndTwoNeT.symm, hneTs, Ne.symm hnearNeEndOne,
        Ne.symm hfarNeEndOne, hneEnds, hEndOneNeS, Ne.symm hfarNeNear,
        hnearNeEndTwo, hnearNeS, hfarNeEndTwo, hfarNeS, hEndTwoNeS, ?_⟩
      rw [hReorderEq, quadSet_swap_second_third leadBlock otherBlockA otherBlockB
        missBlock, hLeadEq, hOAEq, hOBEq, hMissRelist]
    · exact absurd hnearMiss (by
        rw [hMissEq]
        simp [hnearNeS, hnearNeEndOne, hnearNeEndTwo])
    · exact absurd hnearLead hnearNotLead
    · exact absurd hnearLead hnearNotLead
    · exact absurd hnearLead hnearNotLead
  rcases hnearId with rfl | rfl
  · exact hmain freshQ hqNeT hqNeS hqNeEndOne hqNeEndTwo hnePQ.symm
  · exact hmain freshP hpNeT hpNeS hpNeEndOne hpNeEndTwo hnePQ

/-- **The pendant extraction.**  The single atom inside a thread block sits
beside a partner double, which either avoids the miss block — the
pendant-split — or sits in it — the pendant-fork. -/
theorem family_eq_pendantForms_of_sMemLead
    {leadBlock otherBlockA otherBlockB missBlock : Finset (Fin 6)}
    (hcardLead : leadBlock.card = 3) (hcardOA : otherBlockA.card = 3)
    (hcardOB : otherBlockB.card = 3) (hcardMiss : missBlock.card = 3)
    (hneOAOB : otherBlockA ≠ otherBlockB)
    {tripleAtom singleAtom : Fin 6} (hneTs : tripleAtom ≠ singleAtom)
    (hmemTLead : tripleAtom ∈ leadBlock) (hmemTOA : tripleAtom ∈ otherBlockA)
    (hmemTOB : tripleAtom ∈ otherBlockB) (hmissT : tripleAtom ∉ missBlock)
    (hsLead : singleAtom ∈ leadBlock)
    (hsCount : fourBlockCoverCount leadBlock otherBlockA otherBlockB missBlock
      singleAtom = 1)
    (hthreeOnly : ∀ atom : Fin 6, fourBlockCoverCount leadBlock otherBlockA
      otherBlockB missBlock atom = 3 → atom = tripleAtom)
    (hsingleOnly : ∀ atom : Fin 6, fourBlockCoverCount leadBlock otherBlockA
      otherBlockB missBlock atom = 1 → atom = singleAtom)
    (hquadNone : ∀ atom : Fin 6, fourBlockCoverCount leadBlock otherBlockA
      otherBlockB missBlock atom ≠ 4)
    (hcovered : ∀ atom : Fin 6,
      1 ≤ fourBlockCoverCount leadBlock otherBlockA otherBlockB missBlock atom) :
    (∃ partnerAtom secondAtom forkFirst forkSecond : Fin 6,
      tripleAtom ≠ partnerAtom ∧ tripleAtom ≠ secondAtom ∧ tripleAtom ≠ forkFirst
        ∧ tripleAtom ≠ forkSecond ∧ tripleAtom ≠ singleAtom
        ∧ partnerAtom ≠ secondAtom ∧ partnerAtom ≠ forkFirst
        ∧ partnerAtom ≠ forkSecond ∧ partnerAtom ≠ singleAtom
        ∧ secondAtom ≠ forkFirst ∧ secondAtom ≠ forkSecond
        ∧ secondAtom ≠ singleAtom ∧ forkFirst ≠ forkSecond
        ∧ forkFirst ≠ singleAtom ∧ forkSecond ≠ singleAtom
        ∧ ({leadBlock, otherBlockA, otherBlockB, missBlock} :
              Finset (Finset (Fin 6)))
            = {{tripleAtom, partnerAtom, singleAtom},
               {tripleAtom, partnerAtom, secondAtom},
               {tripleAtom, forkFirst, forkSecond},
               {secondAtom, forkFirst, forkSecond}})
    ∨ (∃ partnerAtom forkAtom branchFirst branchSecond : Fin 6,
      tripleAtom ≠ partnerAtom ∧ tripleAtom ≠ forkAtom ∧ tripleAtom ≠ branchFirst
        ∧ tripleAtom ≠ branchSecond ∧ tripleAtom ≠ singleAtom
        ∧ partnerAtom ≠ forkAtom ∧ partnerAtom ≠ branchFirst
        ∧ partnerAtom ≠ branchSecond ∧ partnerAtom ≠ singleAtom
        ∧ forkAtom ≠ branchFirst ∧ forkAtom ≠ branchSecond
        ∧ forkAtom ≠ singleAtom ∧ branchFirst ≠ branchSecond
        ∧ branchFirst ≠ singleAtom ∧ branchSecond ≠ singleAtom
        ∧ ({leadBlock, otherBlockA, otherBlockB, missBlock} :
              Finset (Finset (Fin 6)))
            = {{tripleAtom, partnerAtom, singleAtom},
               {tripleAtom, forkAtom, branchFirst},
               {tripleAtom, forkAtom, branchSecond},
               {partnerAtom, branchFirst, branchSecond}}) := by
  have hsPair := pairwise_notMem_of_fourBlockCoverCount_le_one hsCount.le
  have hsNotOA : singleAtom ∉ otherBlockA := fun h => hsPair.1 ⟨hsLead, h⟩
  have hsNotOB : singleAtom ∉ otherBlockB := fun h => hsPair.2.1 ⟨hsLead, h⟩
  have hsNotMiss : singleAtom ∉ missBlock := fun h => hsPair.2.2.1 ⟨hsLead, h⟩
  obtain ⟨partnerAtom, hpNeT, hpNeS, hLeadEq⟩ :=
    exists_third_of_pair_mem_card_three hcardLead hneTs hmemTLead hsLead
  have hpLead : partnerAtom ∈ leadBlock := by
    rw [hLeadEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self _))))
  have hdoubleOf : ∀ atom : Fin 6, atom ≠ tripleAtom → atom ≠ singleAtom
      → fourBlockCoverCount leadBlock otherBlockA otherBlockB missBlock atom = 2 := by
    intro atom hneT hneS
    have hge := hcovered atom
    have hle := fourBlockCoverCount_le_four leadBlock otherBlockA otherBlockB
      missBlock atom
    have hne3 : fourBlockCoverCount leadBlock otherBlockA otherBlockB missBlock atom
        ≠ 3 := fun h => hneT (hthreeOnly atom h)
    have hne1 : fourBlockCoverCount leadBlock otherBlockA otherBlockB missBlock atom
        ≠ 1 := fun h => hneS (hsingleOnly atom h)
    have hne4 := hquadNone atom
    omega
  have hpCount := hdoubleOf partnerAtom hpNeT hpNeS
  have hLeadRelist : leadBlock = {tripleAtom, partnerAtom, singleAtom} :=
    eq_triple_of_mem_mem_mem_card_three hcardLead hpNeT.symm hneTs hpNeS hmemTLead
      hpLead hsLead
  by_cases hpMiss : partnerAtom ∈ missBlock
  · -- the pendant-fork
    have hpPattern : partnerAtom ∉ otherBlockA ∧ partnerAtom ∉ otherBlockB := by
      rcases fourBlockCoverCount_eq_two_inversion hpCount with
          ⟨_, _, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨_, hb, hc, _⟩ | ⟨ha, _, _, _⟩
        | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩
      exacts [absurd hpMiss hd, absurd hpMiss hd, ⟨hb, hc⟩, absurd hpLead ha,
        absurd hpLead ha, absurd hpLead ha]
    have heraseMiss : (missBlock.erase partnerAtom).card = 2 := by
      rw [Finset.card_erase_of_mem hpMiss, hcardMiss]
    obtain ⟨branchFirst, branchSecond, hneBranches, heraseMissEq⟩ :=
      Finset.card_eq_two.mp heraseMiss
    have hbFErase : branchFirst ∈ missBlock.erase partnerAtom := by
      rw [heraseMissEq]
      exact Finset.mem_insert_self _ _
    have hbSErase : branchSecond ∈ missBlock.erase partnerAtom := by
      rw [heraseMissEq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have hbFMiss : branchFirst ∈ missBlock := (Finset.mem_erase.mp hbFErase).2
    have hbSMiss : branchSecond ∈ missBlock := (Finset.mem_erase.mp hbSErase).2
    have hbFNeP : branchFirst ≠ partnerAtom := (Finset.mem_erase.mp hbFErase).1
    have hbSNeP : branchSecond ≠ partnerAtom := (Finset.mem_erase.mp hbSErase).1
    have hbFNeT : branchFirst ≠ tripleAtom := fun h => hmissT (h ▸ hbFMiss)
    have hbSNeT : branchSecond ≠ tripleAtom := fun h => hmissT (h ▸ hbSMiss)
    have hbFNeS : branchFirst ≠ singleAtom := fun h => hsNotMiss (h ▸ hbFMiss)
    have hbSNeS : branchSecond ≠ singleAtom := fun h => hsNotMiss (h ▸ hbSMiss)
    have hFiveCard : ({tripleAtom, singleAtom, partnerAtom, branchFirst,
        branchSecond} : Finset (Fin 6)).card = 5 := by
      rw [Finset.card_insert_of_notMem (by
          simp [hneTs, hpNeT.symm, hbFNeT.symm, hbSNeT.symm]),
        Finset.card_insert_of_notMem (by
          simp [hpNeS.symm, hbFNeS.symm, hbSNeS.symm]),
        Finset.card_insert_of_notMem (by simp [hbFNeP.symm, hbSNeP.symm]),
        Finset.card_insert_of_notMem (by simpa using hneBranches),
        Finset.card_singleton]
    have hcomplCard : (({tripleAtom, singleAtom, partnerAtom, branchFirst,
        branchSecond} : Finset (Fin 6))ᶜ).card = 1 := by
      rw [Finset.card_compl, hFiveCard, Fintype.card_fin]
    obtain ⟨forkAtom, hcomplEq⟩ := Finset.card_eq_one.mp hcomplCard
    have hforkNot : forkAtom ∉ ({tripleAtom, singleAtom, partnerAtom, branchFirst,
        branchSecond} : Finset (Fin 6)) := by
      rw [← Finset.mem_compl, hcomplEq]
      exact Finset.mem_singleton_self _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hforkNot
    push Not at hforkNot
    obtain ⟨hforkNeT, hforkNeS, hforkNeP, hforkNeBF, hforkNeBS⟩ := hforkNot
    have hforkCount := hdoubleOf forkAtom hforkNeT hforkNeS
    have hforkNotLead : forkAtom ∉ leadBlock := by
      rw [hLeadRelist]
      simp [hforkNeT, hforkNeP, hforkNeS]
    have hMissEq : missBlock = {partnerAtom, branchFirst, branchSecond} := by
      rw [← Finset.insert_erase hpMiss, heraseMissEq]
    have hforkNotMiss : forkAtom ∉ missBlock := by
      rw [hMissEq]
      simp [hforkNeP, hforkNeBF, hforkNeBS]
    have hforkBoth : forkAtom ∈ otherBlockA ∧ forkAtom ∈ otherBlockB := by
      rcases fourBlockCoverCount_eq_two_inversion hforkCount with
          ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨_, hb, hc, _⟩
        | ⟨_, _, _, hd⟩ | ⟨_, _, _, hd⟩
      exacts [absurd ha hforkNotLead, absurd ha hforkNotLead,
        absurd ha hforkNotLead, ⟨hb, hc⟩, absurd hd hforkNotMiss,
        absurd hd hforkNotMiss]
    obtain ⟨branchOA, hbOANeT, hbOANeFork, hOAEq⟩ :=
      exists_third_of_pair_mem_card_three hcardOA hforkNeT.symm hmemTOA hforkBoth.1
    obtain ⟨branchOB, hbOBNeT, hbOBNeFork, hOBEq⟩ :=
      exists_third_of_pair_mem_card_three hcardOB hforkNeT.symm hmemTOB hforkBoth.2
    have hbOAMem : branchOA ∈ otherBlockA := by
      rw [hOAEq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton_self _))))
    have hbOBMem : branchOB ∈ otherBlockB := by
      rw [hOBEq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton_self _))))
    have hbOAId : branchOA = branchFirst ∨ branchOA = branchSecond := by
      have hmemSix : branchOA ∈ ({tripleAtom, singleAtom, partnerAtom, branchFirst,
          branchSecond, forkAtom} : Finset (Fin 6)) := by
        have hSixEq : ({tripleAtom, singleAtom, partnerAtom, branchFirst,
            branchSecond, forkAtom} : Finset (Fin 6)) = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [Finset.card_insert_of_notMem (by
              simp [hneTs, hpNeT.symm, hbFNeT.symm, hbSNeT.symm, hforkNeT.symm]),
            Finset.card_insert_of_notMem (by
              simp [hpNeS.symm, hbFNeS.symm, hbSNeS.symm, hforkNeS.symm]),
            Finset.card_insert_of_notMem (by
              simp [hbFNeP.symm, hbSNeP.symm, hforkNeP.symm]),
            Finset.card_insert_of_notMem (by simp [hneBranches, hforkNeBF.symm]),
            Finset.card_insert_of_notMem (by simp [hforkNeBS.symm]),
            Finset.card_singleton, Fintype.card_fin]
        rw [hSixEq]
        exact Finset.mem_univ branchOA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemSix
      rcases hmemSix with rfl | rfl | rfl | h | h | rfl
      exacts [absurd rfl hbOANeT, absurd hbOAMem hsNotOA,
        absurd hbOAMem hpPattern.1, Or.inl h, Or.inr h, absurd rfl hbOANeFork]
    have hbOBId : branchOB = branchFirst ∨ branchOB = branchSecond := by
      have hmemSix : branchOB ∈ ({tripleAtom, singleAtom, partnerAtom, branchFirst,
          branchSecond, forkAtom} : Finset (Fin 6)) := by
        have hSixEq : ({tripleAtom, singleAtom, partnerAtom, branchFirst,
            branchSecond, forkAtom} : Finset (Fin 6)) = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [Finset.card_insert_of_notMem (by
              simp [hneTs, hpNeT.symm, hbFNeT.symm, hbSNeT.symm, hforkNeT.symm]),
            Finset.card_insert_of_notMem (by
              simp [hpNeS.symm, hbFNeS.symm, hbSNeS.symm, hforkNeS.symm]),
            Finset.card_insert_of_notMem (by
              simp [hbFNeP.symm, hbSNeP.symm, hforkNeP.symm]),
            Finset.card_insert_of_notMem (by simp [hneBranches, hforkNeBF.symm]),
            Finset.card_insert_of_notMem (by simp [hforkNeBS.symm]),
            Finset.card_singleton, Fintype.card_fin]
        rw [hSixEq]
        exact Finset.mem_univ branchOB
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemSix
      rcases hmemSix with rfl | rfl | rfl | h | h | rfl
      exacts [absurd rfl hbOBNeT, absurd hbOBMem hsNotOB,
        absurd hbOBMem hpPattern.2, Or.inl h, Or.inr h, absurd rfl hbOBNeFork]
    have hneOAOBthirds : branchOA ≠ branchOB := by
      intro hcontra
      apply hneOAOB
      rw [hOAEq, hOBEq, hcontra]
    have hMissRelist : missBlock = {partnerAtom, branchOA, branchOB} := by
      rcases hbOAId with rfl | rfl <;> rcases hbOBId with rfl | rfl
      · exact absurd rfl hneOAOBthirds
      · exact hMissEq
      · exact hMissEq.trans (tripleSet_swap_second_third partnerAtom branchOB
          branchOA)
      · exact absurd rfl hneOAOBthirds
    refine Or.inr ⟨partnerAtom, forkAtom, branchOA, branchOB, hpNeT.symm,
      hforkNeT.symm, hbOANeT.symm, hbOBNeT.symm, hneTs, hforkNeP.symm, ?_, ?_,
      hpNeS, hbOANeFork.symm, hbOBNeFork.symm, hforkNeS, hneOAOBthirds, ?_, ?_,
      ?_⟩
    · rcases hbOAId with rfl | rfl
      exacts [hbFNeP.symm, hbSNeP.symm]
    · rcases hbOBId with rfl | rfl
      exacts [hbFNeP.symm, hbSNeP.symm]
    · rcases hbOAId with rfl | rfl
      exacts [hbFNeS, hbSNeS]
    · rcases hbOBId with rfl | rfl
      exacts [hbFNeS, hbSNeS]
    · rw [hLeadRelist, hOAEq, hOBEq, hMissRelist]
  · -- the pendant-split
    have hpSecond : (partnerAtom ∈ otherBlockA ∧ partnerAtom ∉ otherBlockB)
        ∨ (partnerAtom ∉ otherBlockA ∧ partnerAtom ∈ otherBlockB) := by
      rcases fourBlockCoverCount_eq_two_inversion hpCount with
          ⟨_, hb, hc, _⟩ | ⟨_, hb, hc, _⟩ | ⟨_, _, _, hd⟩ | ⟨ha, _, _, _⟩
        | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩
      exacts [Or.inl ⟨hb, hc⟩, Or.inr ⟨hb, hc⟩, absurd hd hpMiss,
        absurd hpLead ha, absurd hpLead ha, absurd hpLead ha]
    have hMissCompl : missBlock = ({tripleAtom, singleAtom, partnerAtom} :
        Finset (Fin 6))ᶜ := by
      have hsub : missBlock ⊆ ({tripleAtom, singleAtom, partnerAtom} :
          Finset (Fin 6))ᶜ := by
        intro atom hmem
        rw [Finset.mem_compl]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (rfl | rfl | rfl)
        exacts [hmissT hmem, hsNotMiss hmem, hpMiss hmem]
      have htripleCard : ({tripleAtom, singleAtom, partnerAtom} :
          Finset (Fin 6)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hneTs, hpNeT.symm]),
          Finset.card_insert_of_notMem (by simp [hpNeS.symm]),
          Finset.card_singleton]
      exact Finset.eq_of_subset_of_card_le hsub
        (by rw [Finset.card_compl, htripleCard, Fintype.card_fin, hcardMiss])
    have hsplitBranch : ∀ hpOA : partnerAtom ∈ otherBlockA,
        ∀ hpNotOB : partnerAtom ∉ otherBlockB,
        ∃ secondAtom forkFirst forkSecond : Fin 6,
          tripleAtom ≠ secondAtom ∧ tripleAtom ≠ forkFirst ∧ tripleAtom ≠ forkSecond
            ∧ partnerAtom ≠ secondAtom ∧ partnerAtom ≠ forkFirst
            ∧ partnerAtom ≠ forkSecond ∧ secondAtom ≠ forkFirst
            ∧ secondAtom ≠ forkSecond ∧ secondAtom ≠ singleAtom
            ∧ forkFirst ≠ forkSecond ∧ forkFirst ≠ singleAtom
            ∧ forkSecond ≠ singleAtom
            ∧ otherBlockA = {tripleAtom, partnerAtom, secondAtom}
            ∧ otherBlockB = {tripleAtom, forkFirst, forkSecond}
            ∧ missBlock = {secondAtom, forkFirst, forkSecond} := by
      intro hpOA hpNotOB
      obtain ⟨secondAtom, hsecNeT, hsecNeP, hOAEq⟩ :=
        exists_third_of_pair_mem_card_three hcardOA hpNeT.symm hmemTOA hpOA
      have hsecOA : secondAtom ∈ otherBlockA := by
        rw [hOAEq]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton_self _))))
      have hsecNeS : secondAtom ≠ singleAtom := fun h => hsNotOA (h ▸ hsecOA)
      have hsecMiss : secondAtom ∈ missBlock := by
        rw [hMissCompl, Finset.mem_compl]
        simp [hsecNeT, hsecNeS, hsecNeP]
      have heraseOB : (otherBlockB.erase tripleAtom).card = 2 := by
        rw [Finset.card_erase_of_mem hmemTOB, hcardOB]
      obtain ⟨forkFirst, forkSecond, hneForks, heraseOBEq⟩ :=
        Finset.card_eq_two.mp heraseOB
      have hfFErase : forkFirst ∈ otherBlockB.erase tripleAtom := by
        rw [heraseOBEq]
        exact Finset.mem_insert_self _ _
      have hfSErase : forkSecond ∈ otherBlockB.erase tripleAtom := by
        rw [heraseOBEq]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
      have hfFOB : forkFirst ∈ otherBlockB := (Finset.mem_erase.mp hfFErase).2
      have hfSOB : forkSecond ∈ otherBlockB := (Finset.mem_erase.mp hfSErase).2
      have hfFNeT : forkFirst ≠ tripleAtom := (Finset.mem_erase.mp hfFErase).1
      have hfSNeT : forkSecond ≠ tripleAtom := (Finset.mem_erase.mp hfSErase).1
      have hfFNeS : forkFirst ≠ singleAtom := fun h => hsNotOB (h ▸ hfFOB)
      have hfSNeS : forkSecond ≠ singleAtom := fun h => hsNotOB (h ▸ hfSOB)
      have hfFNeP : forkFirst ≠ partnerAtom := fun h => hpNotOB (h ▸ hfFOB)
      have hfSNeP : forkSecond ≠ partnerAtom := fun h => hpNotOB (h ▸ hfSOB)
      have hOBEq : otherBlockB = {tripleAtom, forkFirst, forkSecond} := by
        rw [← Finset.insert_erase hmemTOB, heraseOBEq]
      have hfFMiss : forkFirst ∈ missBlock := by
        rw [hMissCompl, Finset.mem_compl]
        simp [hfFNeT, hfFNeS, hfFNeP]
      have hfSMiss : forkSecond ∈ missBlock := by
        rw [hMissCompl, Finset.mem_compl]
        simp [hfSNeT, hfSNeS, hfSNeP]
      have hsecNotLead : secondAtom ∉ leadBlock := by
        rw [hLeadRelist]
        simp [hsecNeT, hsecNeP, hsecNeS]
      have hsecNotOB : secondAtom ∉ otherBlockB := by
        rcases fourBlockCoverCount_eq_two_inversion
            (hdoubleOf secondAtom hsecNeT hsecNeS) with
            ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨_, _, _, hd⟩
          | ⟨_, _, hc, _⟩ | ⟨_, hb, _, _⟩
        exacts [absurd ha hsecNotLead, absurd ha hsecNotLead,
          absurd ha hsecNotLead, absurd hsecMiss hd, hc, absurd hsecOA hb]
      have hsecNeFF : secondAtom ≠ forkFirst := fun h => hsecNotOB (h ▸ hfFOB)
      have hsecNeFS : secondAtom ≠ forkSecond := fun h => hsecNotOB (h ▸ hfSOB)
      have hMissRelist : missBlock = {secondAtom, forkFirst, forkSecond} :=
        eq_triple_of_mem_mem_mem_card_three hcardMiss hsecNeFF hsecNeFS hneForks
          hsecMiss hfFMiss hfSMiss
      exact ⟨secondAtom, forkFirst, forkSecond, hsecNeT.symm, hfFNeT.symm,
        hfSNeT.symm, hsecNeP.symm, hfFNeP.symm, hfSNeP.symm, hsecNeFF, hsecNeFS,
        hsecNeS, hneForks, hfFNeS, hfSNeS, hOAEq, hOBEq, hMissRelist⟩
    rcases hpSecond with ⟨hpOA, hpNotOB⟩ | ⟨hpNotOA, hpOB⟩
    · obtain ⟨secondAtom, forkFirst, forkSecond, h1, h2, h3, h4, h5, h6, h7, h8, h9,
          h10, h11, h12, hOAEq, hOBEq, hMissRelist⟩ := hsplitBranch hpOA hpNotOB
      refine Or.inl ⟨partnerAtom, secondAtom, forkFirst, forkSecond, hpNeT.symm, h1,
        h2, h3, hneTs, h4, h5, h6, hpNeS, h7, h8, h9, h10, h11, h12, ?_⟩
      rw [hLeadRelist, hOAEq, hOBEq, hMissRelist]
    · -- partner threads through the second other block: swap the pair
      have hsplitBranchB :
          ∃ secondAtom forkFirst forkSecond : Fin 6,
            tripleAtom ≠ secondAtom ∧ tripleAtom ≠ forkFirst
              ∧ tripleAtom ≠ forkSecond ∧ partnerAtom ≠ secondAtom
              ∧ partnerAtom ≠ forkFirst ∧ partnerAtom ≠ forkSecond
              ∧ secondAtom ≠ forkFirst ∧ secondAtom ≠ forkSecond
              ∧ secondAtom ≠ singleAtom ∧ forkFirst ≠ forkSecond
              ∧ forkFirst ≠ singleAtom ∧ forkSecond ≠ singleAtom
              ∧ otherBlockB = {tripleAtom, partnerAtom, secondAtom}
              ∧ otherBlockA = {tripleAtom, forkFirst, forkSecond}
              ∧ missBlock = {secondAtom, forkFirst, forkSecond} := by
        obtain ⟨secondAtom, hsecNeT, hsecNeP, hOBEq⟩ :=
          exists_third_of_pair_mem_card_three hcardOB hpNeT.symm hmemTOB hpOB
        have hsecOB : secondAtom ∈ otherBlockB := by
          rw [hOBEq]
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton_self _))))
        have hsecNeS : secondAtom ≠ singleAtom := fun h => hsNotOB (h ▸ hsecOB)
        have hsecMiss : secondAtom ∈ missBlock := by
          rw [hMissCompl, Finset.mem_compl]
          simp [hsecNeT, hsecNeS, hsecNeP]
        have heraseOA : (otherBlockA.erase tripleAtom).card = 2 := by
          rw [Finset.card_erase_of_mem hmemTOA, hcardOA]
        obtain ⟨forkFirst, forkSecond, hneForks, heraseOAEq⟩ :=
          Finset.card_eq_two.mp heraseOA
        have hfFErase : forkFirst ∈ otherBlockA.erase tripleAtom := by
          rw [heraseOAEq]
          exact Finset.mem_insert_self _ _
        have hfSErase : forkSecond ∈ otherBlockA.erase tripleAtom := by
          rw [heraseOAEq]
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
        have hfFOA : forkFirst ∈ otherBlockA := (Finset.mem_erase.mp hfFErase).2
        have hfSOA : forkSecond ∈ otherBlockA := (Finset.mem_erase.mp hfSErase).2
        have hfFNeT : forkFirst ≠ tripleAtom := (Finset.mem_erase.mp hfFErase).1
        have hfSNeT : forkSecond ≠ tripleAtom := (Finset.mem_erase.mp hfSErase).1
        have hfFNeS : forkFirst ≠ singleAtom := fun h => hsNotOA (h ▸ hfFOA)
        have hfSNeS : forkSecond ≠ singleAtom := fun h => hsNotOA (h ▸ hfSOA)
        have hfFNeP : forkFirst ≠ partnerAtom := fun h => hpNotOA (h ▸ hfFOA)
        have hfSNeP : forkSecond ≠ partnerAtom := fun h => hpNotOA (h ▸ hfSOA)
        have hOAEq : otherBlockA = {tripleAtom, forkFirst, forkSecond} := by
          rw [← Finset.insert_erase hmemTOA, heraseOAEq]
        have hfFMiss : forkFirst ∈ missBlock := by
          rw [hMissCompl, Finset.mem_compl]
          simp [hfFNeT, hfFNeS, hfFNeP]
        have hfSMiss : forkSecond ∈ missBlock := by
          rw [hMissCompl, Finset.mem_compl]
          simp [hfSNeT, hfSNeS, hfSNeP]
        have hsecNotLead : secondAtom ∉ leadBlock := by
          rw [hLeadRelist]
          simp [hsecNeT, hsecNeP, hsecNeS]
        have hsecNotOA : secondAtom ∉ otherBlockA := by
          rcases fourBlockCoverCount_eq_two_inversion
              (hdoubleOf secondAtom hsecNeT hsecNeS) with
              ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨_, _, _, hd⟩
            | ⟨_, _, hc, _⟩ | ⟨_, hb, _, _⟩
          exacts [absurd ha hsecNotLead, absurd ha hsecNotLead,
            absurd ha hsecNotLead, absurd hsecMiss hd, absurd hsecOB hc, hb]
        have hsecNeFF : secondAtom ≠ forkFirst := fun h => hsecNotOA (h ▸ hfFOA)
        have hsecNeFS : secondAtom ≠ forkSecond := fun h => hsecNotOA (h ▸ hfSOA)
        have hMissRelist : missBlock = {secondAtom, forkFirst, forkSecond} :=
          eq_triple_of_mem_mem_mem_card_three hcardMiss hsecNeFF hsecNeFS hneForks
            hsecMiss hfFMiss hfSMiss
        exact ⟨secondAtom, forkFirst, forkSecond, hsecNeT.symm, hfFNeT.symm,
          hfSNeT.symm, hsecNeP.symm, hfFNeP.symm, hfSNeP.symm, hsecNeFF, hsecNeFS,
          hsecNeS, hneForks, hfFNeS, hfSNeS, hOBEq, hOAEq, hMissRelist⟩
      obtain ⟨secondAtom, forkFirst, forkSecond, h1, h2, h3, h4, h5, h6, h7, h8, h9,
          h10, h11, h12, hOBEq, hOAEq, hMissRelist⟩ := hsplitBranchB
      refine Or.inl ⟨partnerAtom, secondAtom, forkFirst, forkSecond, hpNeT.symm, h1,
        h2, h3, hneTs, h4, h5, h6, hpNeS, h7, h8, h9, h10, h11, h12, ?_⟩
      rw [quadSet_swap_second_third leadBlock otherBlockA otherBlockB missBlock,
        hLeadRelist, hOAEq, hOBEq, hMissRelist]

/-- The canonical double-path family: the four doubles chain `1-2-3-4`
through the triple atom `0`, the single `5` closing the ends. -/
def canonicalDoublePathFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 2, 3}, {0, 3, 4}, {1, 4, 5}}

/-- The canonical pendant-split family: the single `5` beside partner `1`,
which chains once more; the miss block is the remaining double triple. -/
def canonicalPendantSplitFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 5}, {0, 1, 2}, {0, 3, 4}, {2, 3, 4}}

/-- The canonical pendant-fork family: the single `5` beside partner `1`,
a fresh double `2` forking through both remaining thread blocks. -/
def canonicalPendantForkFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 5}, {0, 2, 3}, {0, 2, 4}, {1, 3, 4}}

/-- **THE PENDANT CAPSTONE.**  Any four-block covering family with profile
`(0,1,4,1)` relabels onto the double-path, the pendant-split, or the
pendant-fork — completing the fifteen-representative census. -/
theorem exists_map_family_eq_canonical_of_profile0141
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
      = 1)
    (hsingleClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1
      = 1) :
    ∃ relabelPerm : Equiv.Perm (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalDoublePathFamily
        ∨ ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalPendantSplitFamily
        ∨ ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalPendantForkFamily := by
  classical
  obtain ⟨tripleAtom, htCount, htUnique⟩ :=
    exists_unique_atom_of_classCard_one htripleClass
  obtain ⟨singleAtom, hsCountOrig, hsUnique⟩ :=
    exists_unique_atom_of_classCard_one hsingleClass
  have hneTs : tripleAtom ≠ singleAtom := by
    intro hcontra
    rw [hcontra, hsCountOrig] at htCount
    omega
  have hcovOrig : ∀ atom : Fin 6,
      1 ≤ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom := by
    intro atom
    have hmem : atom ∈ firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock := by
      rw [hcover]
      exact Finset.mem_univ atom
    simp only [Finset.mem_union] at hmem
    exact one_le_fourBlockCoverCount_of_mem (by tauto)
  obtain ⟨threadA, threadB, threadC, missBlock, hSetEq, hCountEq, hcardA, hcardB,
      hcardC, hcardMiss, hneAB, hneAC, hneBC, hmemTA, hmemTB, hmemTC, hmissT⟩ :=
    exists_missOne_of_count_three hneOneTwo hneOneThree hneOneFour hneTwoThree
      hneTwoFour hneThreeFour hcardOne hcardTwo hcardThree hcardFour htCount
  have hsPos : singleAtom ∈ threadA ∨ singleAtom ∈ threadB ∨ singleAtom ∈ threadC
      ∨ singleAtom ∈ missBlock := by
    apply exists_mem_of_one_le_fourBlockCoverCount
    rw [hCountEq singleAtom]
    exact hcovOrig singleAtom
  have hthreeOnlyTuple : ∀ atom : Fin 6, fourBlockCoverCount threadA threadB threadC
      missBlock atom = 3 → atom = tripleAtom :=
    fun atom h => htUnique atom ((hCountEq atom).symm.trans h)
  have hsingleOnlyTuple : ∀ atom : Fin 6, fourBlockCoverCount threadA threadB threadC
      missBlock atom = 1 → atom = singleAtom :=
    fun atom h => hsUnique atom ((hCountEq atom).symm.trans h)
  have hquadNoneTuple : ∀ atom : Fin 6, fourBlockCoverCount threadA threadB threadC
      missBlock atom ≠ 4 :=
    fun atom h => count_ne_of_classCard_zero hquadClass atom
      ((hCountEq atom).symm.trans h)
  have hcoveredTuple : ∀ atom : Fin 6, 1 ≤ fourBlockCoverCount threadA threadB
      threadC missBlock atom := by
    intro atom
    rw [hCountEq atom]
    exact hcovOrig atom
  have hsCountTuple : fourBlockCoverCount threadA threadB threadC missBlock
      singleAtom = 1 := (hCountEq singleAtom).trans hsCountOrig
  rcases hsPos with hsThread | hsThread | hsThread | hsMiss
  rotate_right
  · -- the single atom sits in the miss block: the double-path
    obtain ⟨edgeFirst, nearDouble, farDouble, edgeSecond, hne01, hne02, hne03, hne04,
        hne05, hne12, hne13, hne14, hne15, hne23, hne24, hne25, hne34, hne35, hne45,
        hFormEq⟩ :=
      family_eq_doublePathForm_of_sMemMiss hcardA hcardB hcardC hcardMiss hneAB hneAC
        hneBC hneTs hmemTA hmemTB hmemTC hmissT hsMiss hsCountTuple hthreeOnlyTuple
        hsingleOnlyTuple hquadNoneTuple hcoveredTuple
    have hinj : Function.Injective
        ![tripleAtom, edgeFirst, nearDouble, farDouble, edgeSecond, singleAtom] :=
      injective_sixAtomAssignment hne01 hne02 hne03 hne04 hne05 hne12 hne13 hne14
        hne15 hne23 hne24 hne25 hne34 hne35 hne45
    let atomAssignment : Equiv.Perm (Fin 6) :=
      Equiv.ofBijective
        ![tripleAtom, edgeFirst, nearDouble, farDouble, edgeSecond, singleAtom]
        (Finite.injective_iff_bijective.mp hinj)
    have hpi0 : atomAssignment.symm tripleAtom = 0 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpi1 : atomAssignment.symm edgeFirst = 1 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpi2 : atomAssignment.symm nearDouble = 2 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpi3 : atomAssignment.symm farDouble = 3 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpi4 : atomAssignment.symm edgeSecond = 4 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpi5 : atomAssignment.symm singleAtom = 5 := by
      rw [Equiv.symm_apply_eq]; rfl
    refine ⟨atomAssignment.symm, Or.inl ?_⟩
    rw [hSetEq, hFormEq]
    simp only [Finset.image_insert, Finset.image_singleton]
    rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
      map_triple_toEmbedding, hpi0, hpi1, hpi2, hpi3, hpi4, hpi5]
    rfl
  all_goals {
    obtain ⟨leadBlock, otherBlockA, otherBlockB, hReorderEq, hCountEq2, hcardLead,
        hcardOA, hcardOB, hneLeadOA, hneLeadOB, hneOAOB, hmemTLead, hmemTOA, hmemTOB,
        hsLead⟩ :=
      exists_threadFirst_of_mem (namedAtom := singleAtom) hcardA hcardB hcardC hneAB
        hneAC hneBC hmemTA hmemTB hmemTC (by tauto)
    have hCountEqLead : ∀ atom : Fin 6, fourBlockCoverCount leadBlock otherBlockA
        otherBlockB missBlock atom
          = fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom :=
      fun atom => (hCountEq2 atom).trans (hCountEq atom)
    rcases family_eq_pendantForms_of_sMemLead hcardLead hcardOA hcardOB hcardMiss
        hneOAOB hneTs hmemTLead hmemTOA hmemTOB hmissT hsLead
        ((hCountEqLead singleAtom).trans hsCountOrig)
        (fun atom h => htUnique atom ((hCountEqLead atom).symm.trans h))
        (fun atom h => hsUnique atom ((hCountEqLead atom).symm.trans h))
        (fun atom h => count_ne_of_classCard_zero hquadClass atom
          ((hCountEqLead atom).symm.trans h))
        (fun atom => by rw [hCountEqLead atom]; exact hcovOrig atom) with
      ⟨partnerAtom, secondAtom, forkFirst, forkSecond, hne01, hne02, hne03, hne04,
          hne05, hne12, hne13, hne14, hne15, hne23, hne24, hne25, hne34, hne35, hne45,
          hFormEq⟩
      | ⟨partnerAtom, forkAtom, branchFirst, branchSecond, hne01, hne02, hne03, hne04,
          hne05, hne12, hne13, hne14, hne15, hne23, hne24, hne25, hne34, hne35, hne45,
          hFormEq⟩
    · -- the pendant-split
      have hinj : Function.Injective
          ![tripleAtom, partnerAtom, secondAtom, forkFirst, forkSecond, singleAtom] :=
        injective_sixAtomAssignment hne01 hne02 hne03 hne04 hne05 hne12 hne13 hne14
          hne15 hne23 hne24 hne25 hne34 hne35 hne45
      let atomAssignment : Equiv.Perm (Fin 6) :=
        Equiv.ofBijective
          ![tripleAtom, partnerAtom, secondAtom, forkFirst, forkSecond, singleAtom]
          (Finite.injective_iff_bijective.mp hinj)
      have hpi0 : atomAssignment.symm tripleAtom = 0 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi1 : atomAssignment.symm partnerAtom = 1 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi2 : atomAssignment.symm secondAtom = 2 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi3 : atomAssignment.symm forkFirst = 3 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi4 : atomAssignment.symm forkSecond = 4 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi5 : atomAssignment.symm singleAtom = 5 := by
        rw [Equiv.symm_apply_eq]; rfl
      refine ⟨atomAssignment.symm, Or.inr (Or.inl ?_)⟩
      rw [hSetEq, hReorderEq, hFormEq]
      simp only [Finset.image_insert, Finset.image_singleton]
      rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
        map_triple_toEmbedding, hpi0, hpi1, hpi2, hpi3, hpi4, hpi5]
      rfl
    · -- the pendant-fork
      have hinj : Function.Injective
          ![tripleAtom, partnerAtom, forkAtom, branchFirst, branchSecond,
            singleAtom] :=
        injective_sixAtomAssignment hne01 hne02 hne03 hne04 hne05 hne12 hne13 hne14
          hne15 hne23 hne24 hne25 hne34 hne35 hne45
      let atomAssignment : Equiv.Perm (Fin 6) :=
        Equiv.ofBijective
          ![tripleAtom, partnerAtom, forkAtom, branchFirst, branchSecond, singleAtom]
          (Finite.injective_iff_bijective.mp hinj)
      have hpi0 : atomAssignment.symm tripleAtom = 0 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi1 : atomAssignment.symm partnerAtom = 1 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi2 : atomAssignment.symm forkAtom = 2 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi3 : atomAssignment.symm branchFirst = 3 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi4 : atomAssignment.symm branchSecond = 4 := by
        rw [Equiv.symm_apply_eq]; rfl
      have hpi5 : atomAssignment.symm singleAtom = 5 := by
        rw [Equiv.symm_apply_eq]; rfl
      refine ⟨atomAssignment.symm, Or.inr (Or.inr ?_)⟩
      rw [hSetEq, hReorderEq, hFormEq]
      simp only [Finset.image_insert, Finset.image_singleton]
      rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
        map_triple_toEmbedding, hpi0, hpi1, hpi2, hpi3, hpi4, hpi5]
      rfl
  }

end Gtz

import Mathlib
import Gtz.Quantitative.QuadrupleAtomDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The pencil door: two quadruple atoms force the edge pencil

At profile `(2,0,0,4)` two atoms lie in all four blocks, so every block is the
shared edge completed by a third, the four thirds are pairwise distinct because
the blocks are, and four distinct thirds exhaust the four atoms off the edge.
The family IS the edge pencil — one orbit, one representative.
-/

namespace Gtz

/-- **THE PENCIL NORMAL FORM.**  Four pairwise-distinct card-three blocks all
containing two fixed atoms are exactly the completions of that edge by the four
atoms off it. -/
theorem family_eq_edgePencil_of_pair_mem_all
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hfirstCard : firstBlock.card = 3) (hsecondCard : secondBlock.card = 3)
    (hthirdCard : thirdBlock.card = 3) (hfourthCard : fourthBlock.card = 3)
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock) (hneTwoThree : secondBlock ≠ thirdBlock)
    (hneTwoFour : secondBlock ≠ fourthBlock) (hneThreeFour : thirdBlock ≠ fourthBlock)
    {edgeFirst edgeSecond : Fin 6} (hedgeNe : edgeFirst ≠ edgeSecond)
    (hfirstPair : edgeFirst ∈ firstBlock ∧ edgeSecond ∈ firstBlock)
    (hsecondPair : edgeFirst ∈ secondBlock ∧ edgeSecond ∈ secondBlock)
    (hthirdPair : edgeFirst ∈ thirdBlock ∧ edgeSecond ∈ thirdBlock)
    (hfourthPair : edgeFirst ∈ fourthBlock ∧ edgeSecond ∈ fourthBlock) :
    ({firstBlock, secondBlock, thirdBlock, fourthBlock} : Finset (Finset (Fin 6)))
      = ({edgeFirst, edgeSecond}ᶜ : Finset (Fin 6)).image
          (fun thirdAtom => {edgeFirst, edgeSecond, thirdAtom}) := by
  classical
  obtain ⟨firstThird, hfirstThirdNeA, hfirstThirdNeB, hfirstEq⟩ :=
    exists_third_of_pair_mem_card_three hfirstCard hedgeNe hfirstPair.1 hfirstPair.2
  obtain ⟨secondThird, hsecondThirdNeA, hsecondThirdNeB, hsecondEq⟩ :=
    exists_third_of_pair_mem_card_three hsecondCard hedgeNe hsecondPair.1 hsecondPair.2
  obtain ⟨thirdThird, hthirdThirdNeA, hthirdThirdNeB, hthirdEq⟩ :=
    exists_third_of_pair_mem_card_three hthirdCard hedgeNe hthirdPair.1 hthirdPair.2
  obtain ⟨fourthThird, hfourthThirdNeA, hfourthThirdNeB, hfourthEq⟩ :=
    exists_third_of_pair_mem_card_three hfourthCard hedgeNe hfourthPair.1 hfourthPair.2
  have hthirdsNe : ∀ {leftThird rightThird : Fin 6},
      ({edgeFirst, edgeSecond, leftThird} : Finset (Fin 6))
          ≠ ({edgeFirst, edgeSecond, rightThird} : Finset (Fin 6)) →
        leftThird ≠ rightThird := by
    intro leftThird rightThird hblocksNe hcontra
    exact hblocksNe (hcontra ▸ rfl)
  have hne12 : firstThird ≠ secondThird :=
    hthirdsNe (hfirstEq ▸ hsecondEq ▸ hneOneTwo)
  have hne13 : firstThird ≠ thirdThird :=
    hthirdsNe (hfirstEq ▸ hthirdEq ▸ hneOneThree)
  have hne14 : firstThird ≠ fourthThird :=
    hthirdsNe (hfirstEq ▸ hfourthEq ▸ hneOneFour)
  have hne23 : secondThird ≠ thirdThird :=
    hthirdsNe (hsecondEq ▸ hthirdEq ▸ hneTwoThree)
  have hne24 : secondThird ≠ fourthThird :=
    hthirdsNe (hsecondEq ▸ hfourthEq ▸ hneTwoFour)
  have hne34 : thirdThird ≠ fourthThird :=
    hthirdsNe (hthirdEq ▸ hfourthEq ▸ hneThreeFour)
  have hthirdsSubset : ({firstThird, secondThird, thirdThird, fourthThird} : Finset (Fin 6))
      ⊆ ({edgeFirst, edgeSecond}ᶜ : Finset (Fin 6)) := by
    intro atom hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    rcases hmem with rfl | rfl | rfl | rfl <;>
      rintro (rfl | rfl) <;>
      first
      | exact hfirstThirdNeA rfl
      | exact hfirstThirdNeB rfl
      | exact hsecondThirdNeA rfl
      | exact hsecondThirdNeB rfl
      | exact hthirdThirdNeA rfl
      | exact hthirdThirdNeB rfl
      | exact hfourthThirdNeA rfl
      | exact hfourthThirdNeB rfl
  have hthirdsCard : ({firstThird, secondThird, thirdThird, fourthThird} :
      Finset (Fin 6)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact hne34
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hcontra | hcontra)
      · exact hne23 hcontra
      · exact hne24 hcontra
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hcontra | hcontra | hcontra)
      · exact hne12 hcontra
      · exact hne13 hcontra
      · exact hne14 hcontra
  have hcomplCard : (({edgeFirst, edgeSecond}ᶜ : Finset (Fin 6))).card = 4 := by
    rw [Finset.card_compl]
    have hpairCard : ({edgeFirst, edgeSecond} : Finset (Fin 6)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hedgeNe), Finset.card_singleton]
    rw [hpairCard]
    rfl
  have hthirdsEq : ({firstThird, secondThird, thirdThird, fourthThird} : Finset (Fin 6))
      = ({edgeFirst, edgeSecond}ᶜ : Finset (Fin 6)) :=
    Finset.eq_of_subset_of_card_le hthirdsSubset (by rw [hthirdsCard, hcomplCard])
  rw [← hthirdsEq, hfirstEq, hsecondEq, hthirdEq, hfourthEq]
  ext block
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨firstThird, Or.inl rfl, rfl⟩
    · exact ⟨secondThird, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨thirdThird, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨fourthThird, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
  · rintro ⟨thirdAtom, hthirdMem, rfl⟩
    rcases hthirdMem with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- The canonical edge pencil: the four completions of the edge `{0, 1}`. -/
def canonicalEdgePencil : Finset (Finset (Fin 6)) :=
  ({0, 1}ᶜ : Finset (Fin 6)).image fun thirdAtom => {0, 1, thirdAtom}

/-- An explicit permutation carrying an ordered pair of distinct atoms to
`(0, 1)`: swap the first to zero, then swap the displaced second to one. -/
noncomputable def pairToZeroOne (edgeFirst edgeSecond : Fin 6) : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 edgeFirst).trans
    (Equiv.swap 1 ((Equiv.swap 0 edgeFirst) edgeSecond))

theorem pairToZeroOne_first {edgeFirst edgeSecond : Fin 6} (hne : edgeFirst ≠ edgeSecond) :
    pairToZeroOne edgeFirst edgeSecond edgeFirst = 0 := by
  have hdisplacedNe : (Equiv.swap 0 edgeFirst) edgeSecond ≠ 0 := by
    intro hcontra
    have hback := congrArg (Equiv.swap 0 edgeFirst) hcontra
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at hback
    exact hne hback.symm
  rw [pairToZeroOne, Equiv.trans_apply, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by norm_num) (Ne.symm hdisplacedNe)]

theorem pairToZeroOne_second {edgeFirst edgeSecond : Fin 6} (_hne : edgeFirst ≠ edgeSecond) :
    pairToZeroOne edgeFirst edgeSecond edgeSecond = 1 := by
  rw [pairToZeroOne, Equiv.trans_apply, Equiv.swap_apply_right]

/-- A triple maps to the triple of images. -/
theorem map_triple_toEmbedding (relabel : Equiv.Perm (Fin 6))
    (firstAtom secondAtom thirdAtom : Fin 6) :
    ({firstAtom, secondAtom, thirdAtom} : Finset (Fin 6)).map relabel.toEmbedding
      = {relabel firstAtom, relabel secondAtom, relabel thirdAtom} := by
  rw [Finset.map_insert, Finset.map_insert, Finset.map_singleton]
  rfl

/-- A permutation transports the complement of a pair to the complement of the
image pair. -/
theorem image_compl_pair (relabel : Equiv.Perm (Fin 6)) (firstAtom secondAtom : Fin 6) :
    (({firstAtom, secondAtom}ᶜ : Finset (Fin 6))).image relabel
      = ({relabel firstAtom, relabel secondAtom}ᶜ : Finset (Fin 6)) := by
  ext targetAtom
  simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨sourceAtom, hsourceNot, rfl⟩
    rintro (hcontra | hcontra) <;> exact hsourceNot (by
      first
      | exact Or.inl (relabel.injective hcontra)
      | exact Or.inr (relabel.injective hcontra))
  · intro htargetNot
    refine ⟨relabel.symm targetAtom, ?_, relabel.apply_symm_apply targetAtom⟩
    rintro (hcontra | hcontra) <;> apply htargetNot
    · exact Or.inl (by rw [← hcontra, Equiv.apply_symm_apply])
    · exact Or.inr (by rw [← hcontra, Equiv.apply_symm_apply])

/-- **THE PENCIL TRANSPORT.**  The image of an edge pencil under any
permutation is the pencil of the image edge. -/
theorem image_map_edgePencil (relabel : Equiv.Perm (Fin 6))
    (edgeFirst edgeSecond : Fin 6) :
    ((({edgeFirst, edgeSecond}ᶜ : Finset (Fin 6)).image
        fun thirdAtom => ({edgeFirst, edgeSecond, thirdAtom} : Finset (Fin 6))).image
      fun block : Finset (Fin 6) => block.map relabel.toEmbedding)
      = ({relabel edgeFirst, relabel edgeSecond}ᶜ : Finset (Fin 6)).image
          fun thirdAtom => {relabel edgeFirst, relabel edgeSecond, thirdAtom} := by
  rw [Finset.image_image, ← image_compl_pair relabel, Finset.image_image]
  refine Finset.image_congr fun thirdAtom _ => ?_
  exact map_triple_toEmbedding relabel edgeFirst edgeSecond thirdAtom

/-- **THE PENCIL-DOOR REDUCTION.**  A covering four-family with two
quadruply-covered atoms relabels to the canonical edge pencil: the two
quadruple atoms sit in every block, the normal form makes the family the edge
pencil, and the explicit pair permutation carries it to the edge `{0, 1}`. -/
theorem exists_map_family_eq_canonicalEdgePencil_of_two_quadruple_atoms
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hfirstCard : firstBlock.card = 3) (hsecondCard : secondBlock.card = 3)
    (hthirdCard : thirdBlock.card = 3) (hfourthCard : fourthBlock.card = 3)
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock) (hneTwoThree : secondBlock ≠ thirdBlock)
    (hneTwoFour : secondBlock ≠ fourthBlock) (hneThreeFour : thirdBlock ≠ fourthBlock)
    {edgeFirst edgeSecond : Fin 6} (hedgeNe : edgeFirst ≠ edgeSecond)
    (hfirstCount : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
      edgeFirst = 4)
    (hsecondCount : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
      edgeSecond = 4) :
    ∃ relabelPerm : Equiv.Perm (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} : Finset (Finset (Fin 6))).image
          (fun block => block.map relabelPerm.toEmbedding)
        = canonicalEdgePencil := by
  obtain ⟨hfirstMemA, hsecondMemA, hthirdMemA, hfourthMemA⟩ :=
    mem_all_of_fourBlockCoverCount_eq_four hfirstCount
  obtain ⟨hfirstMemB, hsecondMemB, hthirdMemB, hfourthMemB⟩ :=
    mem_all_of_fourBlockCoverCount_eq_four hsecondCount
  have hpencil := family_eq_edgePencil_of_pair_mem_all hfirstCard hsecondCard hthirdCard
    hfourthCard hneOneTwo hneOneThree hneOneFour hneTwoThree hneTwoFour hneThreeFour
    hedgeNe ⟨hfirstMemA, hfirstMemB⟩ ⟨hsecondMemA, hsecondMemB⟩
    ⟨hthirdMemA, hthirdMemB⟩ ⟨hfourthMemA, hfourthMemB⟩
  refine ⟨pairToZeroOne edgeFirst edgeSecond, ?_⟩
  rw [hpencil, image_map_edgePencil, pairToZeroOne_first hedgeNe,
    pairToZeroOne_second hedgeNe]
  rfl

end Gtz

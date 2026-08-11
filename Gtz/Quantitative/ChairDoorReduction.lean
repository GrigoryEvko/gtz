import Mathlib
import Gtz.Quantitative.HubFamilyNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

/-!
# The chair-door reduction: profile (1,1,1,3) closed end to end

A single quadruply-covered hub, one triple atom, and one double atom force the
erased edge graph into the CHAIR: the triple atom (the apex) and the double
atom (the wrist) share an edge, the apex carries two further leaf edges, the
wrist one further tail edge, and these four edges exhaust the family.  An
explicit permutation built from the six pinned atoms carries the block family
onto the canonical chair `{{0,1,2},{0,1,3},{0,1,4},{0,2,5}}` — the second
census door closed end to end: count inversions, normal form, witness
permutation, canonical transport.
-/

namespace Gtz

/-- A cover count of three names the unique block the atom misses. -/
theorem fourBlockCoverCount_eq_three_inversion
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)} {atomIndex : Fin 6}
    (hcount : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
      = 3) :
    (atomIndex ∉ firstBlock ∧ atomIndex ∈ secondBlock ∧ atomIndex ∈ thirdBlock
        ∧ atomIndex ∈ fourthBlock)
      ∨ (atomIndex ∈ firstBlock ∧ atomIndex ∉ secondBlock ∧ atomIndex ∈ thirdBlock
        ∧ atomIndex ∈ fourthBlock)
      ∨ (atomIndex ∈ firstBlock ∧ atomIndex ∈ secondBlock ∧ atomIndex ∉ thirdBlock
        ∧ atomIndex ∈ fourthBlock)
      ∨ (atomIndex ∈ firstBlock ∧ atomIndex ∈ secondBlock ∧ atomIndex ∈ thirdBlock
        ∧ atomIndex ∉ fourthBlock) := by
  unfold fourBlockCoverCount at hcount
  split_ifs at hcount <;> first | omega | tauto

/-- A cover count of two names the unique pair of blocks holding the atom. -/
theorem fourBlockCoverCount_eq_two_inversion
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)} {atomIndex : Fin 6}
    (hcount : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
      = 2) :
    (atomIndex ∈ firstBlock ∧ atomIndex ∈ secondBlock ∧ atomIndex ∉ thirdBlock
        ∧ atomIndex ∉ fourthBlock)
      ∨ (atomIndex ∈ firstBlock ∧ atomIndex ∉ secondBlock ∧ atomIndex ∈ thirdBlock
        ∧ atomIndex ∉ fourthBlock)
      ∨ (atomIndex ∈ firstBlock ∧ atomIndex ∉ secondBlock ∧ atomIndex ∉ thirdBlock
        ∧ atomIndex ∈ fourthBlock)
      ∨ (atomIndex ∉ firstBlock ∧ atomIndex ∈ secondBlock ∧ atomIndex ∈ thirdBlock
        ∧ atomIndex ∉ fourthBlock)
      ∨ (atomIndex ∉ firstBlock ∧ atomIndex ∈ secondBlock ∧ atomIndex ∉ thirdBlock
        ∧ atomIndex ∈ fourthBlock)
      ∨ (atomIndex ∉ firstBlock ∧ atomIndex ∉ secondBlock ∧ atomIndex ∈ thirdBlock
        ∧ atomIndex ∈ fourthBlock) := by
  unfold fourBlockCoverCount at hcount
  split_ifs at hcount <;> first | omega | tauto

/-- A cover count of at most one forbids membership in two blocks at once. -/
theorem pairwise_notMem_of_fourBlockCoverCount_le_one
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)} {atomIndex : Fin 6}
    (hcount : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
      ≤ 1) :
    ¬(atomIndex ∈ firstBlock ∧ atomIndex ∈ secondBlock)
      ∧ ¬(atomIndex ∈ firstBlock ∧ atomIndex ∈ thirdBlock)
      ∧ ¬(atomIndex ∈ firstBlock ∧ atomIndex ∈ fourthBlock)
      ∧ ¬(atomIndex ∈ secondBlock ∧ atomIndex ∈ thirdBlock)
      ∧ ¬(atomIndex ∈ secondBlock ∧ atomIndex ∈ fourthBlock)
      ∧ ¬(atomIndex ∈ thirdBlock ∧ atomIndex ∈ fourthBlock) := by
  unfold fourBlockCoverCount at hcount
  split_ifs at hcount <;> first | omega | tauto

/-- An edge through a named atom is that atom and one other. -/
theorem exists_other_of_mem_card_two {edge : Finset (Fin 6)} (hcard : edge.card = 2)
    {atom : Fin 6} (hmem : atom ∈ edge) :
    ∃ otherAtom : Fin 6, otherAtom ≠ atom ∧ edge = {atom, otherAtom} := by
  obtain ⟨firstEnd, secondEnd, hne, rfl⟩ := Finset.card_eq_two.mp hcard
  rcases Finset.mem_insert.mp hmem with rfl | hmem
  · exact ⟨secondEnd, hne.symm, rfl⟩
  · rw [Finset.mem_singleton] at hmem
    subst hmem
    exact ⟨firstEnd, hne, Finset.pair_comm firstEnd atom⟩

/-- An edge through two distinct named atoms is exactly their pair. -/
theorem eq_pair_of_mem_mem_card_two {edge : Finset (Fin 6)} (hcard : edge.card = 2)
    {firstAtom secondAtom : Fin 6} (hne : firstAtom ≠ secondAtom)
    (hfirst : firstAtom ∈ edge) (hsecond : secondAtom ∈ edge) :
    edge = {firstAtom, secondAtom} := by
  have hsubset : ({firstAtom, secondAtom} : Finset (Fin 6)) ⊆ edge := by
    intro atom hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem
    · exact hfirst
    · rw [Finset.mem_singleton] at hmem
      exact hmem ▸ hsecond
  have hpairCard : ({firstAtom, secondAtom} : Finset (Fin 6)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsubset (by rw [hcard, hpairCard])).symm

/-- A singleton count class names its unique atom. -/
theorem exists_unique_atom_of_classCard_one
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)} {countValue : ℕ}
    (hclass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock countValue
      = 1) :
    ∃ atom : Fin 6,
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom = countValue
        ∧ ∀ other : Fin 6,
            fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock other
                = countValue
              → other = atom := by
  rw [fourBlockCountClass] at hclass
  obtain ⟨atom, hfilter⟩ := Finset.card_eq_one.mp hclass
  have hmem : atom ∈ Finset.univ.filter fun atomIndex =>
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
        = countValue := by
    rw [hfilter]
    exact Finset.mem_singleton_self atom
  refine ⟨atom, (Finset.mem_filter.mp hmem).2, fun other hother => ?_⟩
  have hotherMem : other ∈ Finset.univ.filter fun atomIndex =>
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
        = countValue :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ other, hother⟩
  rw [hfilter] at hotherMem
  exact Finset.mem_singleton.mp hotherMem

/-- Swapping the first two listed elements of a four-element set. -/
theorem quadSet_swap_first_second {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α) = {b, a, c, d} :=
  Finset.insert_comm a b {c, d}

/-- Swapping the middle two listed elements of a four-element set. -/
theorem quadSet_swap_second_third {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α) = {a, c, b, d} :=
  congrArg (insert a) (Finset.insert_comm b c {d})

/-- Swapping the last two listed elements of a four-element set. -/
theorem quadSet_swap_third_fourth {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α) = {a, b, d, c} :=
  congrArg (insert a) (congrArg (insert b) (Finset.pair_comm c d))

/-- **Normalizing around an apex of degree three and a wrist of degree two.**
The apex and the wrist share one edge (twice would collide two blocks), the
apex carries two further edges free of the wrist, and the wrist one further
edge free of the apex — an ordered relabelling of the four edges. -/
theorem exists_normalized_of_count_three_two
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock) (hneTwoThree : secondBlock ≠ thirdBlock)
    (hneTwoFour : secondBlock ≠ fourthBlock) (hneThreeFour : thirdBlock ≠ fourthBlock)
    (hcardOne : firstBlock.card = 2) (hcardTwo : secondBlock.card = 2)
    (hcardThree : thirdBlock.card = 2) (hcardFour : fourthBlock.card = 2)
    {apexAtom wristAtom : Fin 6} (hneAtoms : apexAtom ≠ wristAtom)
    (hapex : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock apexAtom
      = 3)
    (hwrist : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock wristAtom
      = 2)
    (hothers : ∀ atom : Fin 6, atom ≠ apexAtom → atom ≠ wristAtom →
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom ≤ 1) :
    ∃ sharedEdge firstApexEdge secondApexEdge wristEdge : Finset (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} : Finset (Finset (Fin 6)))
          = {sharedEdge, firstApexEdge, secondApexEdge, wristEdge}
        ∧ sharedEdge.card = 2 ∧ firstApexEdge.card = 2 ∧ secondApexEdge.card = 2
        ∧ wristEdge.card = 2
        ∧ firstApexEdge ≠ secondApexEdge
        ∧ apexAtom ∈ sharedEdge ∧ wristAtom ∈ sharedEdge
        ∧ apexAtom ∈ firstApexEdge ∧ wristAtom ∉ firstApexEdge
        ∧ apexAtom ∈ secondApexEdge ∧ wristAtom ∉ secondApexEdge
        ∧ apexAtom ∉ wristEdge ∧ wristAtom ∈ wristEdge
        ∧ ∀ atom : Fin 6, atom ≠ apexAtom → atom ≠ wristAtom →
            ¬(atom ∈ firstApexEdge ∧ atom ∈ wristEdge)
              ∧ ¬(atom ∈ secondApexEdge ∧ atom ∈ wristEdge) := by
  rcases fourBlockCoverCount_eq_three_inversion hapex with
      ⟨hvFirst, hvSecond, hvThird, hvFourth⟩ | ⟨hvFirst, hvSecond, hvThird, hvFourth⟩
    | ⟨hvFirst, hvSecond, hvThird, hvFourth⟩ | ⟨hvFirst, hvSecond, hvThird, hvFourth⟩ <;>
    rcases fourBlockCoverCount_eq_two_inversion hwrist with
        ⟨hwFirst, hwSecond, hwThird, hwFourth⟩ | ⟨hwFirst, hwSecond, hwThird, hwFourth⟩
      | ⟨hwFirst, hwSecond, hwThird, hwFourth⟩ | ⟨hwFirst, hwSecond, hwThird, hwFourth⟩
      | ⟨hwFirst, hwSecond, hwThird, hwFourth⟩ | ⟨hwFirst, hwSecond, hwThird, hwFourth⟩
  -- apex misses the first block; wrist on {1,2}: shared E2, apex E3 E4, wrist E1
  · refine ⟨secondBlock, thirdBlock, fourthBlock, firstBlock, ?_, hcardTwo, hcardThree,
      hcardFour, hcardOne, hneThreeFour, hvSecond, hwSecond, hvThird, hwThird, hvFourth,
      hwFourth, hvFirst, hwFirst, fun atom hva hwa => ?_⟩
    · rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
        quadSet_swap_second_third secondBlock firstBlock thirdBlock fourthBlock,
        quadSet_swap_third_fourth secondBlock thirdBlock firstBlock fourthBlock]
    · have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
      exact ⟨fun hcontra => hpair.2.1 ⟨hcontra.2, hcontra.1⟩,
        fun hcontra => hpair.2.2.1 ⟨hcontra.2, hcontra.1⟩⟩
  -- apex misses the first block; wrist on {1,3}: shared E3, apex E2 E4, wrist E1
  · refine ⟨thirdBlock, secondBlock, fourthBlock, firstBlock, ?_, hcardThree, hcardTwo,
      hcardFour, hcardOne, hneTwoFour, hvThird, hwThird, hvSecond, hwSecond, hvFourth,
      hwFourth, hvFirst, hwFirst, fun atom hva hwa => ?_⟩
    · rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
        quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock,
        quadSet_swap_second_third thirdBlock firstBlock secondBlock fourthBlock,
        quadSet_swap_third_fourth thirdBlock secondBlock firstBlock fourthBlock]
    · have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
      exact ⟨fun hcontra => hpair.1 ⟨hcontra.2, hcontra.1⟩,
        fun hcontra => hpair.2.2.1 ⟨hcontra.2, hcontra.1⟩⟩
  -- apex misses the first block; wrist on {1,4}: shared E4, apex E2 E3, wrist E1
  · refine ⟨fourthBlock, secondBlock, thirdBlock, firstBlock, ?_, hcardFour, hcardTwo,
      hcardThree, hcardOne, hneTwoThree, hvFourth, hwFourth, hvSecond, hwSecond, hvThird,
      hwThird, hvFirst, hwFirst, fun atom hva hwa => ?_⟩
    · rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
        quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
        quadSet_swap_first_second firstBlock fourthBlock secondBlock thirdBlock,
        quadSet_swap_second_third fourthBlock firstBlock secondBlock thirdBlock,
        quadSet_swap_third_fourth fourthBlock secondBlock firstBlock thirdBlock]
    · have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
      exact ⟨fun hcontra => hpair.1 ⟨hcontra.2, hcontra.1⟩,
        fun hcontra => hpair.2.1 ⟨hcontra.2, hcontra.1⟩⟩
  -- apex misses the first block; wrist on {2,3}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardTwo hneAtoms hvSecond hwSecond).trans
      (eq_pair_of_mem_mem_card_two hcardThree hneAtoms hvThird hwThird).symm) hneTwoThree
  -- apex misses the first block; wrist on {2,4}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardTwo hneAtoms hvSecond hwSecond).trans
      (eq_pair_of_mem_mem_card_two hcardFour hneAtoms hvFourth hwFourth).symm) hneTwoFour
  -- apex misses the first block; wrist on {3,4}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardThree hneAtoms hvThird hwThird).trans
      (eq_pair_of_mem_mem_card_two hcardFour hneAtoms hvFourth hwFourth).symm)
      hneThreeFour
  -- apex misses the second block; wrist on {1,2}: shared E1, apex E3 E4, wrist E2
  · refine ⟨firstBlock, thirdBlock, fourthBlock, secondBlock, ?_, hcardOne, hcardThree,
      hcardFour, hcardTwo, hneThreeFour, hvFirst, hwFirst, hvThird, hwThird, hvFourth,
      hwFourth, hvSecond, hwSecond, fun atom hva hwa => ?_⟩
    · rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
        quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock]
    · have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
      exact ⟨fun hcontra => hpair.2.2.2.1 ⟨hcontra.2, hcontra.1⟩,
        fun hcontra => hpair.2.2.2.2.1 ⟨hcontra.2, hcontra.1⟩⟩
  -- apex misses the second block; wrist on {1,3}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardOne hneAtoms hvFirst hwFirst).trans
      (eq_pair_of_mem_mem_card_two hcardThree hneAtoms hvThird hwThird).symm) hneOneThree
  -- apex misses the second block; wrist on {1,4}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardOne hneAtoms hvFirst hwFirst).trans
      (eq_pair_of_mem_mem_card_two hcardFour hneAtoms hvFourth hwFourth).symm) hneOneFour
  -- apex misses the second block; wrist on {2,3}: shared E3, apex E1 E4, wrist E2
  · refine ⟨thirdBlock, firstBlock, fourthBlock, secondBlock, ?_, hcardThree, hcardOne,
      hcardFour, hcardTwo, hneOneFour, hvThird, hwThird, hvFirst, hwFirst, hvFourth,
      hwFourth, hvSecond, hwSecond, fun atom hva hwa => ?_⟩
    · rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
        quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock,
        quadSet_swap_first_second firstBlock thirdBlock fourthBlock secondBlock]
    · have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
      exact ⟨fun hcontra => hpair.1 hcontra,
        fun hcontra => hpair.2.2.2.2.1 ⟨hcontra.2, hcontra.1⟩⟩
  -- apex misses the second block; wrist on {2,4}: shared E4, apex E1 E3, wrist E2
  · refine ⟨fourthBlock, firstBlock, thirdBlock, secondBlock, ?_, hcardFour, hcardOne,
      hcardThree, hcardTwo, hneOneThree, hvFourth, hwFourth, hvFirst, hwFirst, hvThird,
      hwThird, hvSecond, hwSecond, fun atom hva hwa => ?_⟩
    · rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
        quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
        quadSet_swap_first_second firstBlock fourthBlock secondBlock thirdBlock,
        quadSet_swap_third_fourth fourthBlock firstBlock secondBlock thirdBlock]
    · have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
      exact ⟨fun hcontra => hpair.1 hcontra,
        fun hcontra => hpair.2.2.2.1 ⟨hcontra.2, hcontra.1⟩⟩
  -- apex misses the second block; wrist on {3,4}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardThree hneAtoms hvThird hwThird).trans
      (eq_pair_of_mem_mem_card_two hcardFour hneAtoms hvFourth hwFourth).symm)
      hneThreeFour
  -- apex misses the third block; wrist on {1,2}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardOne hneAtoms hvFirst hwFirst).trans
      (eq_pair_of_mem_mem_card_two hcardTwo hneAtoms hvSecond hwSecond).symm) hneOneTwo
  -- apex misses the third block; wrist on {1,3}: shared E1, apex E2 E4, wrist E3
  · refine ⟨firstBlock, secondBlock, fourthBlock, thirdBlock, ?_, hcardOne, hcardTwo,
      hcardFour, hcardThree, hneTwoFour, hvFirst, hwFirst, hvSecond, hwSecond, hvFourth,
      hwFourth, hvThird, hwThird, fun atom hva hwa => ?_⟩
    · rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock]
    · have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
      exact ⟨fun hcontra => hpair.2.2.2.1 hcontra,
        fun hcontra => hpair.2.2.2.2.2 ⟨hcontra.2, hcontra.1⟩⟩
  -- apex misses the third block; wrist on {1,4}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardOne hneAtoms hvFirst hwFirst).trans
      (eq_pair_of_mem_mem_card_two hcardFour hneAtoms hvFourth hwFourth).symm) hneOneFour
  -- apex misses the third block; wrist on {2,3}: shared E2, apex E1 E4, wrist E3
  · refine ⟨secondBlock, firstBlock, fourthBlock, thirdBlock, ?_, hcardTwo, hcardOne,
      hcardFour, hcardThree, hneOneFour, hvSecond, hwSecond, hvFirst, hwFirst, hvFourth,
      hwFourth, hvThird, hwThird, fun atom hva hwa => ?_⟩
    · rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
        quadSet_swap_third_fourth secondBlock firstBlock thirdBlock fourthBlock]
    · have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
      exact ⟨fun hcontra => hpair.2.1 hcontra,
        fun hcontra => hpair.2.2.2.2.2 ⟨hcontra.2, hcontra.1⟩⟩
  -- apex misses the third block; wrist on {2,4}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardTwo hneAtoms hvSecond hwSecond).trans
      (eq_pair_of_mem_mem_card_two hcardFour hneAtoms hvFourth hwFourth).symm) hneTwoFour
  -- apex misses the third block; wrist on {3,4}: shared E4, apex E1 E2, wrist E3
  · refine ⟨fourthBlock, firstBlock, secondBlock, thirdBlock, ?_, hcardFour, hcardOne,
      hcardTwo, hcardThree, hneOneTwo, hvFourth, hwFourth, hvFirst, hwFirst, hvSecond,
      hwSecond, hvThird, hwThird, fun atom hva hwa => ?_⟩
    · rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
        quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
        quadSet_swap_first_second firstBlock fourthBlock secondBlock thirdBlock]
    · have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
      exact ⟨fun hcontra => hpair.2.1 hcontra,
        fun hcontra => hpair.2.2.2.1 hcontra⟩
  -- apex misses the fourth block; wrist on {1,2}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardOne hneAtoms hvFirst hwFirst).trans
      (eq_pair_of_mem_mem_card_two hcardTwo hneAtoms hvSecond hwSecond).symm) hneOneTwo
  -- apex misses the fourth block; wrist on {1,3}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardOne hneAtoms hvFirst hwFirst).trans
      (eq_pair_of_mem_mem_card_two hcardThree hneAtoms hvThird hwThird).symm) hneOneThree
  -- apex misses the fourth block; wrist on {1,4}: shared E1, apex E2 E3, wrist E4
  · refine ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, rfl, hcardOne, hcardTwo,
      hcardThree, hcardFour, hneTwoThree, hvFirst, hwFirst, hvSecond, hwSecond, hvThird,
      hwThird, hvFourth, hwFourth, fun atom hva hwa => ?_⟩
    have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
    exact ⟨fun hcontra => hpair.2.2.2.2.1 hcontra,
      fun hcontra => hpair.2.2.2.2.2 hcontra⟩
  -- apex misses the fourth block; wrist on {2,3}: both shared edges collide
  · exact absurd ((eq_pair_of_mem_mem_card_two hcardTwo hneAtoms hvSecond hwSecond).trans
      (eq_pair_of_mem_mem_card_two hcardThree hneAtoms hvThird hwThird).symm) hneTwoThree
  -- apex misses the fourth block; wrist on {2,4}: shared E2, apex E1 E3, wrist E4
  · refine ⟨secondBlock, firstBlock, thirdBlock, fourthBlock, ?_, hcardTwo, hcardOne,
      hcardThree, hcardFour, hneOneThree, hvSecond, hwSecond, hvFirst, hwFirst, hvThird,
      hwThird, hvFourth, hwFourth, fun atom hva hwa => ?_⟩
    · rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock]
    · have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
      exact ⟨fun hcontra => hpair.2.2.1 hcontra,
        fun hcontra => hpair.2.2.2.2.2 hcontra⟩
  -- apex misses the fourth block; wrist on {3,4}: shared E3, apex E1 E2, wrist E4
  · refine ⟨thirdBlock, firstBlock, secondBlock, fourthBlock, ?_, hcardThree, hcardOne,
      hcardTwo, hcardFour, hneOneTwo, hvThird, hwThird, hvFirst, hwFirst, hvSecond,
      hwSecond, hvFourth, hwFourth, fun atom hva hwa => ?_⟩
    · rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
        quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock]
    · have hpair := pairwise_notMem_of_fourBlockCoverCount_le_one (hothers atom hva hwa)
      exact ⟨fun hcontra => hpair.2.2.1 hcontra,
        fun hcontra => hpair.2.2.2.2.1 hcontra⟩

/-- **The chair extraction.**  A normalized apex-wrist family IS the chair:
shared edge, two apex-leaf edges, one wrist-tail edge, with all five off-hub
atoms pinned pairwise distinct. -/
theorem edgeSet_eq_chair_of_normalized
    {sharedEdge firstApexEdge secondApexEdge wristEdge : Finset (Fin 6)}
    (hcardShared : sharedEdge.card = 2) (hcardFirst : firstApexEdge.card = 2)
    (hcardSecond : secondApexEdge.card = 2) (hcardWrist : wristEdge.card = 2)
    (hneApexEdges : firstApexEdge ≠ secondApexEdge)
    {apexAtom wristAtom : Fin 6} (hneAtoms : apexAtom ≠ wristAtom)
    (hsharedApex : apexAtom ∈ sharedEdge) (hsharedWrist : wristAtom ∈ sharedEdge)
    (hfirstApex : apexAtom ∈ firstApexEdge) (hfirstNoWrist : wristAtom ∉ firstApexEdge)
    (hsecondApex : apexAtom ∈ secondApexEdge) (hsecondNoWrist : wristAtom ∉ secondApexEdge)
    (hwristNoApex : apexAtom ∉ wristEdge) (hwristMem : wristAtom ∈ wristEdge)
    (hdisjointOthers : ∀ atom : Fin 6, atom ≠ apexAtom → atom ≠ wristAtom →
      ¬(atom ∈ firstApexEdge ∧ atom ∈ wristEdge)
        ∧ ¬(atom ∈ secondApexEdge ∧ atom ∈ wristEdge)) :
    ∃ firstLeaf secondLeaf tailAtom : Fin 6,
      firstLeaf ≠ secondLeaf ∧ firstLeaf ≠ tailAtom ∧ secondLeaf ≠ tailAtom
        ∧ firstLeaf ≠ apexAtom ∧ firstLeaf ≠ wristAtom
        ∧ secondLeaf ≠ apexAtom ∧ secondLeaf ≠ wristAtom
        ∧ tailAtom ≠ apexAtom ∧ tailAtom ≠ wristAtom
        ∧ ({sharedEdge, firstApexEdge, secondApexEdge, wristEdge} :
              Finset (Finset (Fin 6)))
            = {{apexAtom, wristAtom}, {apexAtom, firstLeaf}, {apexAtom, secondLeaf},
               {wristAtom, tailAtom}} := by
  obtain ⟨firstLeaf, hfirstLeafNeApex, hfirstEdgeEq⟩ :=
    exists_other_of_mem_card_two hcardFirst hfirstApex
  obtain ⟨secondLeaf, hsecondLeafNeApex, hsecondEdgeEq⟩ :=
    exists_other_of_mem_card_two hcardSecond hsecondApex
  obtain ⟨tailAtom, htailNeWrist, hwristEdgeEq⟩ :=
    exists_other_of_mem_card_two hcardWrist hwristMem
  have hfirstLeafMem : firstLeaf ∈ firstApexEdge := by
    rw [hfirstEdgeEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self firstLeaf))
  have hsecondLeafMem : secondLeaf ∈ secondApexEdge := by
    rw [hsecondEdgeEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self secondLeaf))
  have htailMem : tailAtom ∈ wristEdge := by
    rw [hwristEdgeEq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self tailAtom))
  have hfirstLeafNeWrist : firstLeaf ≠ wristAtom := by
    intro hcontra
    exact hfirstNoWrist (hcontra ▸ hfirstLeafMem)
  have hsecondLeafNeWrist : secondLeaf ≠ wristAtom := by
    intro hcontra
    exact hsecondNoWrist (hcontra ▸ hsecondLeafMem)
  have htailNeApex : tailAtom ≠ apexAtom := by
    intro hcontra
    exact hwristNoApex (hcontra ▸ htailMem)
  have hleavesNe : firstLeaf ≠ secondLeaf := by
    intro hcontra
    apply hneApexEdges
    rw [hfirstEdgeEq, hsecondEdgeEq, hcontra]
  have hfirstLeafNeTail : firstLeaf ≠ tailAtom := by
    intro hcontra
    exact (hdisjointOthers firstLeaf hfirstLeafNeApex hfirstLeafNeWrist).1
      ⟨hfirstLeafMem, hcontra ▸ htailMem⟩
  have hsecondLeafNeTail : secondLeaf ≠ tailAtom := by
    intro hcontra
    exact (hdisjointOthers secondLeaf hsecondLeafNeApex hsecondLeafNeWrist).2
      ⟨hsecondLeafMem, hcontra ▸ htailMem⟩
  have hsharedEq : sharedEdge = {apexAtom, wristAtom} :=
    eq_pair_of_mem_mem_card_two hcardShared hneAtoms hsharedApex hsharedWrist
  refine ⟨firstLeaf, secondLeaf, tailAtom, hleavesNe, hfirstLeafNeTail,
    hsecondLeafNeTail, hfirstLeafNeApex, hfirstLeafNeWrist, hsecondLeafNeApex,
    hsecondLeafNeWrist, htailNeApex, htailNeWrist, ?_⟩
  rw [hsharedEq, hfirstEdgeEq, hsecondEdgeEq, hwristEdgeEq]

/-- Six pairwise-distinct atoms make the slot-to-atom vector injective. -/
theorem injective_sixAtomAssignment
    {hubAtom apexAtom wristAtom firstLeaf secondLeaf tailAtom : Fin 6}
    (hHubApex : hubAtom ≠ apexAtom) (hHubWrist : hubAtom ≠ wristAtom)
    (hHubFirst : hubAtom ≠ firstLeaf) (hHubSecond : hubAtom ≠ secondLeaf)
    (hHubTail : hubAtom ≠ tailAtom) (hApexWrist : apexAtom ≠ wristAtom)
    (hApexFirst : apexAtom ≠ firstLeaf) (hApexSecond : apexAtom ≠ secondLeaf)
    (hApexTail : apexAtom ≠ tailAtom) (hWristFirst : wristAtom ≠ firstLeaf)
    (hWristSecond : wristAtom ≠ secondLeaf) (hWristTail : wristAtom ≠ tailAtom)
    (hFirstSecond : firstLeaf ≠ secondLeaf) (hFirstTail : firstLeaf ≠ tailAtom)
    (hSecondTail : secondLeaf ≠ tailAtom) :
    Function.Injective
      ![hubAtom, apexAtom, wristAtom, firstLeaf, secondLeaf, tailAtom] := by
  intro slotFirst slotSecond hslots
  fin_cases slotFirst <;> fin_cases slotSecond <;>
    first
      | rfl
      | exact absurd hslots hHubApex | exact absurd hslots hHubApex.symm
      | exact absurd hslots hHubWrist | exact absurd hslots hHubWrist.symm
      | exact absurd hslots hHubFirst | exact absurd hslots hHubFirst.symm
      | exact absurd hslots hHubSecond | exact absurd hslots hHubSecond.symm
      | exact absurd hslots hHubTail | exact absurd hslots hHubTail.symm
      | exact absurd hslots hApexWrist | exact absurd hslots hApexWrist.symm
      | exact absurd hslots hApexFirst | exact absurd hslots hApexFirst.symm
      | exact absurd hslots hApexSecond | exact absurd hslots hApexSecond.symm
      | exact absurd hslots hApexTail | exact absurd hslots hApexTail.symm
      | exact absurd hslots hWristFirst | exact absurd hslots hWristFirst.symm
      | exact absurd hslots hWristSecond | exact absurd hslots hWristSecond.symm
      | exact absurd hslots hWristTail | exact absurd hslots hWristTail.symm
      | exact absurd hslots hFirstSecond | exact absurd hslots hFirstSecond.symm
      | exact absurd hslots hFirstTail | exact absurd hslots hFirstTail.symm
      | exact absurd hslots hSecondTail | exact absurd hslots hSecondTail.symm

/-- The canonical chair family: hub `0`, apex `1`, wrist `2`, leaves `3`, `4`,
tail `5`. -/
def canonicalChairFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 5}}

/-- **THE CHAIR-DOOR CAPSTONE.**  Any four-block family with profile counts
`(quadruple, triple, double) = (1, 1, 1)` relabels onto the canonical chair. -/
theorem exists_map_family_eq_canonicalChair_of_profile
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock) (hneTwoThree : secondBlock ≠ thirdBlock)
    (hneTwoFour : secondBlock ≠ fourthBlock) (hneThreeFour : thirdBlock ≠ fourthBlock)
    (hcardOne : firstBlock.card = 3) (hcardTwo : secondBlock.card = 3)
    (hcardThree : thirdBlock.card = 3) (hcardFour : fourthBlock.card = 3)
    (hquadClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4 = 1)
    (htripleClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3
      = 1)
    (hdoubleClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2
      = 1) :
    ∃ relabelPerm : Equiv.Perm (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
          Finset (Finset (Fin 6))).image
          (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
        = canonicalChairFamily := by
  classical
  obtain ⟨hubAtom, hhubCount, hhubUnique⟩ := exists_unique_atom_of_classCard_one hquadClass
  obtain ⟨apexAtom, hapexCount, hapexUnique⟩ :=
    exists_unique_atom_of_classCard_one htripleClass
  obtain ⟨wristAtom, hwristCount, hwristUnique⟩ :=
    exists_unique_atom_of_classCard_one hdoubleClass
  obtain ⟨hhubOne, hhubTwo, hhubThree, hhubFour⟩ :=
    mem_all_of_fourBlockCoverCount_eq_four hhubCount
  have hApexNeHub : apexAtom ≠ hubAtom := by
    intro hcontra
    rw [hcontra, hhubCount] at hapexCount
    omega
  have hWristNeHub : wristAtom ≠ hubAtom := by
    intro hcontra
    rw [hcontra, hhubCount] at hwristCount
    omega
  have hApexNeWrist : apexAtom ≠ wristAtom := by
    intro hcontra
    rw [hcontra, hwristCount] at hapexCount
    omega
  have hothersEdge : ∀ atom : Fin 6, atom ≠ apexAtom → atom ≠ wristAtom →
      fourBlockCoverCount (firstBlock.erase hubAtom) (secondBlock.erase hubAtom)
        (thirdBlock.erase hubAtom) (fourthBlock.erase hubAtom) atom ≤ 1 := by
    intro atom hva hwa
    by_cases hhub : atom = hubAtom
    · subst hhub
      unfold fourBlockCoverCount
      simp
    · rw [fourBlockCoverCount_erase_hub hhub]
      have hle := fourBlockCoverCount_le_four firstBlock secondBlock thirdBlock
        fourthBlock atom
      have hneFour : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
          atom ≠ 4 := fun hcontra => hhub (hhubUnique atom hcontra)
      have hneThree : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
          atom ≠ 3 := fun hcontra => hva (hapexUnique atom hcontra)
      have hneTwo : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
          atom ≠ 2 := fun hcontra => hwa (hwristUnique atom hcontra)
      omega
  obtain ⟨sharedEdge, firstApexEdge, secondApexEdge, wristEdge, hEdgeSetEq, hcardShared,
      hcardFirstEdge, hcardSecondEdge, hcardWristEdge, hneApexEdges, hsharedApex,
      hsharedWrist, hfirstApex, hfirstNoWrist, hsecondApex, hsecondNoWrist, hwristNoApex,
      hwristMemEdge, hdisjointOthers⟩ :=
    exists_normalized_of_count_three_two
      (erase_hub_ne_of_ne hneOneTwo hhubOne hhubTwo)
      (erase_hub_ne_of_ne hneOneThree hhubOne hhubThree)
      (erase_hub_ne_of_ne hneOneFour hhubOne hhubFour)
      (erase_hub_ne_of_ne hneTwoThree hhubTwo hhubThree)
      (erase_hub_ne_of_ne hneTwoFour hhubTwo hhubFour)
      (erase_hub_ne_of_ne hneThreeFour hhubThree hhubFour)
      (card_erase_hub_eq_two hcardOne hhubOne) (card_erase_hub_eq_two hcardTwo hhubTwo)
      (card_erase_hub_eq_two hcardThree hhubThree)
      (card_erase_hub_eq_two hcardFour hhubFour)
      hApexNeWrist
      ((fourBlockCoverCount_erase_hub hApexNeHub).trans hapexCount)
      ((fourBlockCoverCount_erase_hub hWristNeHub).trans hwristCount)
      hothersEdge
  obtain ⟨firstLeaf, secondLeaf, tailAtom, hleavesNe, hfirstLeafNeTail,
      hsecondLeafNeTail, hfirstLeafNeApex, hfirstLeafNeWrist, hsecondLeafNeApex,
      hsecondLeafNeWrist, htailNeApex, htailNeWrist, hChairEq⟩ :=
    edgeSet_eq_chair_of_normalized hcardShared hcardFirstEdge hcardSecondEdge
      hcardWristEdge hneApexEdges hApexNeWrist hsharedApex hsharedWrist hfirstApex
      hfirstNoWrist hsecondApex hsecondNoWrist hwristNoApex hwristMemEdge
      hdisjointOthers
  have hCombinedEq : ({firstBlock.erase hubAtom, secondBlock.erase hubAtom,
        thirdBlock.erase hubAtom, fourthBlock.erase hubAtom} : Finset (Finset (Fin 6)))
      = {{apexAtom, wristAtom}, {apexAtom, firstLeaf}, {apexAtom, secondLeaf},
         {wristAtom, tailAtom}} := hEdgeSetEq.trans hChairEq
  have hHubNotInChairEdge : ∀ edge ∈ ({{apexAtom, wristAtom}, {apexAtom, firstLeaf},
        {apexAtom, secondLeaf}, {wristAtom, tailAtom}} : Finset (Finset (Fin 6))),
      hubAtom ∉ edge := by
    intro edge hedge
    rw [← hCombinedEq] at hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl | rfl <;> exact Finset.notMem_erase hubAtom _
  have hHubNeFirstLeaf : hubAtom ≠ firstLeaf := by
    intro hcontra
    refine hHubNotInChairEdge {apexAtom, firstLeaf} ?_ ?_
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
    · rw [hcontra]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self firstLeaf))
  have hHubNeSecondLeaf : hubAtom ≠ secondLeaf := by
    intro hcontra
    refine hHubNotInChairEdge {apexAtom, secondLeaf} ?_ ?_
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert_self _ _))))
    · rw [hcontra]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self secondLeaf))
  have hHubNeTail : hubAtom ≠ tailAtom := by
    intro hcontra
    refine hHubNotInChairEdge {wristAtom, tailAtom} ?_ ?_
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))))))
    · rw [hcontra]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self tailAtom))
  have hinj : Function.Injective
      ![hubAtom, apexAtom, wristAtom, firstLeaf, secondLeaf, tailAtom] :=
    injective_sixAtomAssignment hApexNeHub.symm hWristNeHub.symm hHubNeFirstLeaf
      hHubNeSecondLeaf hHubNeTail hApexNeWrist hfirstLeafNeApex.symm
      hsecondLeafNeApex.symm htailNeApex.symm hfirstLeafNeWrist.symm
      hsecondLeafNeWrist.symm htailNeWrist.symm hleavesNe hfirstLeafNeTail
      hsecondLeafNeTail
  let atomAssignment : Equiv.Perm (Fin 6) :=
    Equiv.ofBijective ![hubAtom, apexAtom, wristAtom, firstLeaf, secondLeaf, tailAtom]
      (Finite.injective_iff_bijective.mp hinj)
  have hpiHub : atomAssignment.symm hubAtom = 0 := by
    rw [Equiv.symm_apply_eq]; rfl
  have hpiApex : atomAssignment.symm apexAtom = 1 := by
    rw [Equiv.symm_apply_eq]; rfl
  have hpiWrist : atomAssignment.symm wristAtom = 2 := by
    rw [Equiv.symm_apply_eq]; rfl
  have hpiFirstLeaf : atomAssignment.symm firstLeaf = 3 := by
    rw [Equiv.symm_apply_eq]; rfl
  have hpiSecondLeaf : atomAssignment.symm secondLeaf = 4 := by
    rw [Equiv.symm_apply_eq]; rfl
  have hpiTail : atomAssignment.symm tailAtom = 5 := by
    rw [Equiv.symm_apply_eq]; rfl
  refine ⟨atomAssignment.symm, ?_⟩
  rw [family_eq_image_insert_erase_of_hub_mem_all hhubOne hhubTwo hhubThree hhubFour,
    hCombinedEq]
  simp only [Finset.image_insert, Finset.image_singleton]
  rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
    map_triple_toEmbedding]
  rw [hpiHub, hpiApex, hpiWrist, hpiFirstLeaf, hpiSecondLeaf, hpiTail]
  rfl

end Gtz

import Mathlib
import Gtz.Quantitative.ChairDoorReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The path-and-triangle door: profile (1,0,3,2) closed end to end

A single quadruply-covered hub with three double atoms and two single atoms
forces the erased edge graph into exactly two shapes.  The two single atoms
(the leaves) either share their sole edge — then the remaining three edges
are card-two subsets of the three double atoms and form the TRIANGLE — or
they hang off two distinct double atoms whose remaining slots thread through
the third: the FIVE-PATH.  Explicit permutations carry the block family onto
`{{0,1,2},{0,2,3},{0,1,4},{0,3,5}}` (path: hub 0, spine 1-2-3, leaves 4, 5)
or `{{0,1,2},{0,1,3},{0,2,3},{0,4,5}}` (triangle: hub 0, triangle 1,2,3,
pendant edge 4-5).  Third and fourth census doors closed end to end; the
quadruple-atom half of the census is complete.
-/

namespace Gtz

/-- A cover count of one names the unique block holding the atom. -/
theorem fourBlockCoverCount_eq_one_inversion
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)} {atomIndex : Fin 6}
    (hcount : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
      = 1) :
    (atomIndex ∈ firstBlock ∧ atomIndex ∉ secondBlock ∧ atomIndex ∉ thirdBlock
        ∧ atomIndex ∉ fourthBlock)
      ∨ (atomIndex ∉ firstBlock ∧ atomIndex ∈ secondBlock ∧ atomIndex ∉ thirdBlock
        ∧ atomIndex ∉ fourthBlock)
      ∨ (atomIndex ∉ firstBlock ∧ atomIndex ∉ secondBlock ∧ atomIndex ∈ thirdBlock
        ∧ atomIndex ∉ fourthBlock)
      ∨ (atomIndex ∉ firstBlock ∧ atomIndex ∉ secondBlock ∧ atomIndex ∉ thirdBlock
        ∧ atomIndex ∈ fourthBlock) := by
  unfold fourBlockCoverCount at hcount
  split_ifs at hcount <;> first | omega | tauto

/-- A doubleton count class names its two atoms. -/
theorem exists_two_atoms_of_classCard_two
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)} {countValue : ℕ}
    (hclass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock countValue
      = 2) :
    ∃ firstAtom secondAtom : Fin 6, firstAtom ≠ secondAtom
      ∧ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock firstAtom
          = countValue
      ∧ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock secondAtom
          = countValue := by
  rw [fourBlockCountClass] at hclass
  obtain ⟨firstAtom, secondAtom, hne, hfilter⟩ := Finset.card_eq_two.mp hclass
  have hfirstMem : firstAtom ∈ Finset.univ.filter fun atomIndex =>
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
        = countValue := by
    rw [hfilter]
    exact Finset.mem_insert_self firstAtom {secondAtom}
  have hsecondMem : secondAtom ∈ Finset.univ.filter fun atomIndex =>
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
        = countValue := by
    rw [hfilter]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self secondAtom))
  exact ⟨firstAtom, secondAtom, hne, (Finset.mem_filter.mp hfirstMem).2,
    (Finset.mem_filter.mp hsecondMem).2⟩

/-- A tripleton count class names its three atoms. -/
theorem exists_three_atoms_of_classCard_three
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)} {countValue : ℕ}
    (hclass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock countValue
      = 3) :
    ∃ firstAtom secondAtom thirdAtom : Fin 6,
      firstAtom ≠ secondAtom ∧ firstAtom ≠ thirdAtom ∧ secondAtom ≠ thirdAtom
        ∧ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock firstAtom
            = countValue
        ∧ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock secondAtom
            = countValue
        ∧ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock thirdAtom
            = countValue := by
  rw [fourBlockCountClass] at hclass
  obtain ⟨firstAtom, secondAtom, thirdAtom, hneOneTwo, hneOneThree, hneTwoThree,
      hfilter⟩ := Finset.card_eq_three.mp hclass
  have hmemOf : ∀ atom ∈ ({firstAtom, secondAtom, thirdAtom} : Finset (Fin 6)),
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom
        = countValue := by
    intro atom hmem
    rw [← hfilter] at hmem
    exact (Finset.mem_filter.mp hmem).2
  exact ⟨firstAtom, secondAtom, thirdAtom, hneOneTwo, hneOneThree, hneTwoThree,
    hmemOf firstAtom (Finset.mem_insert_self _ _),
    hmemOf secondAtom (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))),
    hmemOf thirdAtom (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self _)))))⟩

/-- A four-element listed set splits as its first three elements union the
last. -/
theorem quadSet_eq_tripleSet_union {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α) = {a, b, c} ∪ {d} := by
  rw [Finset.insert_union, Finset.insert_union, Finset.singleton_union]

/-- A two-element edge inside a listed triple is one of its three pairs. -/
theorem eq_pair_of_subset_triple {edge : Finset (Fin 6)} (hcard : edge.card = 2)
    {firstAtom secondAtom thirdAtom : Fin 6}
    (hneOneTwo : firstAtom ≠ secondAtom) (hneOneThree : firstAtom ≠ thirdAtom)
    (hneTwoThree : secondAtom ≠ thirdAtom)
    (hsub : ∀ atom ∈ edge, atom = firstAtom ∨ atom = secondAtom ∨ atom = thirdAtom) :
    edge = {firstAtom, secondAtom} ∨ edge = {firstAtom, thirdAtom}
      ∨ edge = {secondAtom, thirdAtom} := by
  obtain ⟨leftEnd, rightEnd, hneEnds, rfl⟩ := Finset.card_eq_two.mp hcard
  have hleft := hsub leftEnd (Finset.mem_insert_self _ _)
  have hright := hsub rightEnd
    (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
  rcases hleft with rfl | rfl | rfl <;> rcases hright with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hneEnds
      | exact Or.inl rfl
      | exact Or.inl (Finset.pair_comm leftEnd rightEnd)
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inl (Finset.pair_comm leftEnd rightEnd))
      | exact Or.inr (Or.inr rfl)
      | exact Or.inr (Or.inr (Finset.pair_comm leftEnd rightEnd))

/-- **The leaf dispatcher.**  Two single atoms either share their sole edge or
name two distinct edges; either way the four edges renormalize around them,
with cover counts carried along verbatim. -/
theorem exists_leaf_normalization_of_count_one_one
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock) (hneTwoThree : secondBlock ≠ thirdBlock)
    (hneTwoFour : secondBlock ≠ fourthBlock) (hneThreeFour : thirdBlock ≠ fourthBlock)
    (hcardOne : firstBlock.card = 2) (hcardTwo : secondBlock.card = 2)
    (hcardThree : thirdBlock.card = 2) (hcardFour : fourthBlock.card = 2)
    {leafFirst leafSecond : Fin 6}
    (hleafFirst : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
      leafFirst = 1)
    (hleafSecond : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock
      leafSecond = 1) :
    (∃ insideA insideB insideC leafEdge : Finset (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} : Finset (Finset (Fin 6)))
          = {insideA, insideB, insideC, leafEdge}
        ∧ (∀ atom : Fin 6, fourBlockCoverCount insideA insideB insideC leafEdge atom
            = fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom)
        ∧ insideA.card = 2 ∧ insideB.card = 2 ∧ insideC.card = 2 ∧ leafEdge.card = 2
        ∧ insideA ≠ insideB ∧ insideA ≠ insideC ∧ insideB ≠ insideC
        ∧ leafFirst ∈ leafEdge ∧ leafFirst ∉ insideA ∧ leafFirst ∉ insideB
        ∧ leafFirst ∉ insideC
        ∧ leafSecond ∈ leafEdge ∧ leafSecond ∉ insideA ∧ leafSecond ∉ insideB
        ∧ leafSecond ∉ insideC)
    ∨ (∃ aEdge bEdge insideC insideD : Finset (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} : Finset (Finset (Fin 6)))
          = {aEdge, bEdge, insideC, insideD}
        ∧ (∀ atom : Fin 6, fourBlockCoverCount aEdge bEdge insideC insideD atom
            = fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom)
        ∧ aEdge.card = 2 ∧ bEdge.card = 2 ∧ insideC.card = 2 ∧ insideD.card = 2
        ∧ insideC ≠ insideD
        ∧ leafFirst ∈ aEdge ∧ leafFirst ∉ bEdge ∧ leafFirst ∉ insideC
        ∧ leafFirst ∉ insideD
        ∧ leafSecond ∈ bEdge ∧ leafSecond ∉ aEdge ∧ leafSecond ∉ insideC
        ∧ leafSecond ∉ insideD) := by
  rcases fourBlockCoverCount_eq_one_inversion hleafFirst with
      ⟨haFirst, haSecond, haThird, haFourth⟩ | ⟨haFirst, haSecond, haThird, haFourth⟩
    | ⟨haFirst, haSecond, haThird, haFourth⟩ | ⟨haFirst, haSecond, haThird, haFourth⟩ <;>
    rcases fourBlockCoverCount_eq_one_inversion hleafSecond with
        ⟨hbFirst, hbSecond, hbThird, hbFourth⟩ | ⟨hbFirst, hbSecond, hbThird, hbFourth⟩
      | ⟨hbFirst, hbSecond, hbThird, hbFourth⟩ | ⟨hbFirst, hbSecond, hbThird, hbFourth⟩
  -- both leaves on the first edge: leaf edge E1, insides E2 E3 E4
  · refine Or.inl ⟨secondBlock, thirdBlock, fourthBlock, firstBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardThree, hcardFour,
      hcardOne, hneTwoThree, hneTwoFour, hneThreeFour, haFirst, haSecond, haThird,
      haFourth, hbFirst, hbSecond, hbThird, hbFourth⟩
    rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_second_third secondBlock firstBlock thirdBlock fourthBlock,
      quadSet_swap_third_fourth secondBlock thirdBlock firstBlock fourthBlock]
  -- first leaf on E1, second leaf on E2
  · exact Or.inr ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, rfl,
      fun atom => rfl, hcardOne, hcardTwo, hcardThree, hcardFour, hneThreeFour,
      haFirst, haSecond, haThird, haFourth, hbSecond, hbFirst, hbThird, hbFourth⟩
  -- first leaf on E1, second leaf on E3
  · refine Or.inr ⟨firstBlock, thirdBlock, secondBlock, fourthBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardThree, hcardTwo,
      hcardFour, hneTwoFour, haFirst, haThird, haSecond, haFourth, hbThird, hbFirst,
      hbSecond, hbFourth⟩
    rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock]
  -- first leaf on E1, second leaf on E4
  · refine Or.inr ⟨firstBlock, fourthBlock, secondBlock, thirdBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardFour, hcardTwo,
      hcardThree, hneTwoThree, haFirst, haFourth, haSecond, haThird, hbFourth, hbFirst,
      hbSecond, hbThird⟩
    rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock]
  -- first leaf on E2, second leaf on E1
  · refine Or.inr ⟨secondBlock, firstBlock, thirdBlock, fourthBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardOne, hcardThree,
      hcardFour, hneThreeFour, haSecond, haFirst, haThird, haFourth, hbFirst, hbSecond,
      hbThird, hbFourth⟩
    rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock]
  -- both leaves on the second edge: leaf edge E2, insides E1 E3 E4
  · refine Or.inl ⟨firstBlock, thirdBlock, fourthBlock, secondBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardThree, hcardFour,
      hcardTwo, hneOneThree, hneOneFour, hneThreeFour, haSecond, haFirst, haThird,
      haFourth, hbSecond, hbFirst, hbThird, hbFourth⟩
    rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock]
  -- first leaf on E2, second leaf on E3
  · refine Or.inr ⟨secondBlock, thirdBlock, firstBlock, fourthBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardThree, hcardOne,
      hcardFour, hneOneFour, haSecond, haThird, haFirst, haFourth, hbThird, hbSecond,
      hbFirst, hbFourth⟩
    rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_second_third secondBlock firstBlock thirdBlock fourthBlock]
  -- first leaf on E2, second leaf on E4
  · refine Or.inr ⟨secondBlock, fourthBlock, firstBlock, thirdBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardTwo, hcardFour, hcardOne,
      hcardThree, hneOneThree, haSecond, haFourth, haFirst, haThird, hbFourth, hbSecond,
      hbFirst, hbThird⟩
    rw [quadSet_swap_first_second firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_third_fourth secondBlock firstBlock thirdBlock fourthBlock,
      quadSet_swap_second_third secondBlock firstBlock fourthBlock thirdBlock]
  -- first leaf on E3, second leaf on E1
  · refine Or.inr ⟨thirdBlock, firstBlock, secondBlock, fourthBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardOne, hcardTwo,
      hcardFour, hneTwoFour, haThird, haFirst, haSecond, haFourth, hbFirst, hbThird,
      hbSecond, hbFourth⟩
    rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock]
  -- first leaf on E3, second leaf on E2
  · refine Or.inr ⟨thirdBlock, secondBlock, firstBlock, fourthBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardTwo, hcardOne,
      hcardFour, hneOneFour, haThird, haSecond, haFirst, haFourth, hbSecond, hbThird,
      hbFirst, hbFourth⟩
    rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock,
      quadSet_swap_second_third thirdBlock firstBlock secondBlock fourthBlock]
  -- both leaves on the third edge: leaf edge E3, insides E1 E2 E4
  · refine Or.inl ⟨firstBlock, secondBlock, fourthBlock, thirdBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardOne, hcardTwo, hcardFour,
      hcardThree, hneOneTwo, hneOneFour, hneTwoFour, haThird, haFirst, haSecond,
      haFourth, hbThird, hbFirst, hbSecond, hbFourth⟩
    rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock]
  -- first leaf on E3, second leaf on E4
  · refine Or.inr ⟨thirdBlock, fourthBlock, firstBlock, secondBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardThree, hcardFour, hcardOne,
      hcardTwo, hneOneTwo, haThird, haFourth, haFirst, haSecond, hbFourth, hbThird,
      hbFirst, hbSecond⟩
    rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_first_second firstBlock thirdBlock secondBlock fourthBlock,
      quadSet_swap_third_fourth thirdBlock firstBlock secondBlock fourthBlock,
      quadSet_swap_second_third thirdBlock firstBlock fourthBlock secondBlock]
  -- first leaf on E4, second leaf on E1
  · refine Or.inr ⟨fourthBlock, firstBlock, secondBlock, thirdBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardOne, hcardTwo,
      hcardThree, hneTwoThree, haFourth, haFirst, haSecond, haThird, hbFirst, hbFourth,
      hbSecond, hbThird⟩
    rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
      quadSet_swap_first_second firstBlock fourthBlock secondBlock thirdBlock]
  -- first leaf on E4, second leaf on E2
  · refine Or.inr ⟨fourthBlock, secondBlock, firstBlock, thirdBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardTwo, hcardOne,
      hcardThree, hneOneThree, haFourth, haSecond, haFirst, haThird, hbSecond, hbFourth,
      hbFirst, hbThird⟩
    rw [quadSet_swap_third_fourth firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_second_third firstBlock secondBlock fourthBlock thirdBlock,
      quadSet_swap_first_second firstBlock fourthBlock secondBlock thirdBlock,
      quadSet_swap_second_third fourthBlock firstBlock secondBlock thirdBlock]
  -- first leaf on E4, second leaf on E3
  · refine Or.inr ⟨fourthBlock, thirdBlock, firstBlock, secondBlock, ?_,
      fun atom => by unfold fourBlockCoverCount; ring, hcardFour, hcardThree, hcardOne,
      hcardTwo, hneOneTwo, haFourth, haThird, haFirst, haSecond, hbThird, hbFourth,
      hbFirst, hbSecond⟩
    rw [quadSet_swap_second_third firstBlock secondBlock thirdBlock fourthBlock,
      quadSet_swap_third_fourth firstBlock thirdBlock secondBlock fourthBlock,
      quadSet_swap_first_second firstBlock thirdBlock fourthBlock secondBlock,
      quadSet_swap_second_third thirdBlock firstBlock fourthBlock secondBlock,
      quadSet_swap_first_second thirdBlock fourthBlock firstBlock secondBlock]
  -- both leaves on the fourth edge: leaf edge E4, insides E1 E2 E3
  · exact Or.inl ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, rfl,
      fun atom => rfl, hcardOne, hcardTwo, hcardThree, hcardFour, hneOneTwo,
      hneOneThree, hneTwoThree, haFourth, haFirst, haSecond, haThird, hbFourth,
      hbFirst, hbSecond, hbThird⟩

/-- **The triangle extraction.**  Three edges avoiding both leaves live on the
three double atoms and are exactly the three pairs. -/
theorem edgeSet_eq_triangle_of_leaf_edge
    {insideA insideB insideC : Finset (Fin 6)}
    (hcardA : insideA.card = 2) (hcardB : insideB.card = 2) (hcardC : insideC.card = 2)
    (hneAB : insideA ≠ insideB) (hneAC : insideA ≠ insideC) (hneBC : insideB ≠ insideC)
    {xAtom yAtom zAtom : Fin 6}
    (hneXY : xAtom ≠ yAtom) (hneXZ : xAtom ≠ zAtom) (hneYZ : yAtom ≠ zAtom)
    (hInsideAtoms : ∀ atom : Fin 6,
      (atom ∈ insideA ∨ atom ∈ insideB ∨ atom ∈ insideC)
        → atom = xAtom ∨ atom = yAtom ∨ atom = zAtom) :
    ({insideA, insideB, insideC} : Finset (Finset (Fin 6)))
      = {{xAtom, yAtom}, {xAtom, zAtom}, {yAtom, zAtom}} := by
  have hApair := eq_pair_of_subset_triple hcardA hneXY hneXZ hneYZ
    fun atom hmem => hInsideAtoms atom (Or.inl hmem)
  have hBpair := eq_pair_of_subset_triple hcardB hneXY hneXZ hneYZ
    fun atom hmem => hInsideAtoms atom (Or.inr (Or.inl hmem))
  have hCpair := eq_pair_of_subset_triple hcardC hneXY hneXZ hneYZ
    fun atom hmem => hInsideAtoms atom (Or.inr (Or.inr hmem))
  have hsubset : ({insideA, insideB, insideC} : Finset (Finset (Fin 6)))
      ⊆ {{xAtom, yAtom}, {xAtom, zAtom}, {yAtom, zAtom}} := by
    intro block hblock
    simp only [Finset.mem_insert, Finset.mem_singleton] at hblock ⊢
    rcases hblock with rfl | rfl | rfl
    · exact hApair
    · exact hBpair
    · exact hCpair
  have hleftCard : ({insideA, insideB, insideC} : Finset (Finset (Fin 6))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hneAB, hneAC]),
      Finset.card_insert_of_notMem (by simp [hneBC]), Finset.card_singleton]
  have hrightCard : ({{xAtom, yAtom}, {xAtom, zAtom}, {yAtom, zAtom}} :
      Finset (Finset (Fin 6))).card ≤ 3 := by
    apply le_trans (Finset.card_insert_le _ _)
    apply Nat.succ_le_succ
    apply le_trans (Finset.card_insert_le _ _)
    exact Nat.succ_le_succ (Finset.card_singleton _).le
  exact Finset.eq_of_subset_of_card_le hsubset (le_trans hrightCard hleftCard.ge)

/-- **The five-path extraction.**  Two leaves on distinct edges hang off two
distinct double atoms, and the two remaining edges thread through the third
double atom: the family is the path leaf-end-mid-end-leaf. -/
theorem edgeSet_eq_path_of_leaf_edges
    {aEdge bEdge insideC insideD : Finset (Fin 6)}
    (hcardA : aEdge.card = 2) (hcardB : bEdge.card = 2)
    (hcardC : insideC.card = 2) (hcardD : insideD.card = 2)
    (hneCD : insideC ≠ insideD)
    {xAtom yAtom zAtom leafFirst leafSecond : Fin 6}
    (hneXY : xAtom ≠ yAtom) (hneXZ : xAtom ≠ zAtom) (hneYZ : yAtom ≠ zAtom)
    (haNeX : leafFirst ≠ xAtom) (haNeY : leafFirst ≠ yAtom) (haNeZ : leafFirst ≠ zAtom)
    (hbNeX : leafSecond ≠ xAtom) (hbNeY : leafSecond ≠ yAtom)
    (hbNeZ : leafSecond ≠ zAtom)
    (haMemA : leafFirst ∈ aEdge) (haNotB : leafFirst ∉ bEdge)
    (haNotC : leafFirst ∉ insideC) (haNotD : leafFirst ∉ insideD)
    (hbMemB : leafSecond ∈ bEdge) (hbNotA : leafSecond ∉ aEdge)
    (hbNotC : leafSecond ∉ insideC) (hbNotD : leafSecond ∉ insideD)
    (hxyzCount : ∀ atom : Fin 6, atom = xAtom ∨ atom = yAtom ∨ atom = zAtom →
      fourBlockCoverCount aEdge bEdge insideC insideD atom = 2)
    (hedgeAtoms : ∀ atom : Fin 6,
      (atom ∈ aEdge ∨ atom ∈ bEdge ∨ atom ∈ insideC ∨ atom ∈ insideD)
        → atom = xAtom ∨ atom = yAtom ∨ atom = zAtom ∨ atom = leafFirst
          ∨ atom = leafSecond) :
    ∃ endFirst midAtom endSecond : Fin 6,
      ({endFirst, midAtom, endSecond} : Finset (Fin 6)) = {xAtom, yAtom, zAtom}
        ∧ endFirst ≠ midAtom ∧ endFirst ≠ endSecond ∧ midAtom ≠ endSecond
        ∧ ({aEdge, bEdge, insideC, insideD} : Finset (Finset (Fin 6)))
            = {{endFirst, midAtom}, {midAtom, endSecond}, {endFirst, leafFirst},
               {endSecond, leafSecond}} := by
  have hNotLeafFirst : ∀ atom : Fin 6,
      atom = xAtom ∨ atom = yAtom ∨ atom = zAtom → atom ≠ leafFirst := by
    rintro atom (rfl | rfl | rfl)
    exacts [haNeX.symm, haNeY.symm, haNeZ.symm]
  have hNotLeafSecond : ∀ atom : Fin 6,
      atom = xAtom ∨ atom = yAtom ∨ atom = zAtom → atom ≠ leafSecond := by
    rintro atom (rfl | rfl | rfl)
    exacts [hbNeX.symm, hbNeY.symm, hbNeZ.symm]
  have hmemTriple : ∀ atom : Fin 6, atom = xAtom ∨ atom = yAtom ∨ atom = zAtom →
      atom ∈ ({xAtom, yAtom, zAtom} : Finset (Fin 6)) := by
    rintro atom (rfl | rfl | rfl) <;> simp
  have hCsub : ∀ atom ∈ insideC, atom = xAtom ∨ atom = yAtom ∨ atom = zAtom := by
    intro atom hmem
    rcases hedgeAtoms atom (Or.inr (Or.inr (Or.inl hmem))) with h | h | h | rfl | rfl
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h),
      absurd hmem haNotC, absurd hmem hbNotC]
  have hDsub : ∀ atom ∈ insideD, atom = xAtom ∨ atom = yAtom ∨ atom = zAtom := by
    intro atom hmem
    rcases hedgeAtoms atom (Or.inr (Or.inr (Or.inr hmem))) with h | h | h | rfl | rfl
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h),
      absurd hmem haNotD, absurd hmem hbNotD]
  have hTripleCard : ({xAtom, yAtom, zAtom} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hneXY, hneXZ]),
      Finset.card_insert_of_notMem (by simp [hneYZ]), Finset.card_singleton]
  obtain ⟨endFirst, hendFirstNeLeaf, hAeq⟩ := exists_other_of_mem_card_two hcardA haMemA
  have hendFirstMemA : endFirst ∈ aEdge := by
    rw [hAeq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hendFirstXYZ : endFirst = xAtom ∨ endFirst = yAtom ∨ endFirst = zAtom := by
    rcases hedgeAtoms endFirst (Or.inl hendFirstMemA) with h | h | h | rfl | rfl
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h),
      absurd rfl hendFirstNeLeaf, absurd hendFirstMemA hbNotA]
  obtain ⟨endSecond, hendSecondNeLeaf, hBeq⟩ := exists_other_of_mem_card_two hcardB hbMemB
  have hendSecondMemB : endSecond ∈ bEdge := by
    rw [hBeq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hendSecondXYZ : endSecond = xAtom ∨ endSecond = yAtom ∨ endSecond = zAtom := by
    rcases hedgeAtoms endSecond (Or.inr (Or.inl hendSecondMemB)) with h | h | h | rfl | rfl
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h),
      absurd hendSecondMemB haNotB, absurd rfl hendSecondNeLeaf]
  have hendFirstMemTriple := hmemTriple endFirst hendFirstXYZ
  have hendSecondMemTriple := hmemTriple endSecond hendSecondXYZ
  have hEndsNe : endFirst ≠ endSecond := by
    intro hcontra
    have hvB : endFirst ∈ bEdge := hcontra ▸ hendSecondMemB
    have hvNotCD : endFirst ∉ insideC ∧ endFirst ∉ insideD := by
      rcases fourBlockCoverCount_eq_two_inversion (hxyzCount endFirst hendFirstXYZ) with
          ⟨_, _, hc, hd⟩ | ⟨_, hb, _, _⟩ | ⟨_, hb, _, _⟩ | ⟨ha, _, _, _⟩
        | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩
      exacts [⟨hc, hd⟩, absurd hvB hb, absurd hvB hb, absurd hendFirstMemA ha,
        absurd hendFirstMemA ha, absurd hendFirstMemA ha]
    have hEraseCard : (({xAtom, yAtom, zAtom} : Finset (Fin 6)).erase endFirst).card
        = 2 := by
      rw [Finset.card_erase_of_mem hendFirstMemTriple, hTripleCard]
    have hCpairSub : insideC ⊆ ({xAtom, yAtom, zAtom} : Finset (Fin 6)).erase
        endFirst := by
      intro atom hmem
      rw [Finset.mem_erase]
      exact ⟨fun hcontra2 => hvNotCD.1 (hcontra2 ▸ hmem),
        hmemTriple atom (hCsub atom hmem)⟩
    have hDpairSub : insideD ⊆ ({xAtom, yAtom, zAtom} : Finset (Fin 6)).erase
        endFirst := by
      intro atom hmem
      rw [Finset.mem_erase]
      exact ⟨fun hcontra2 => hvNotCD.2 (hcontra2 ▸ hmem),
        hmemTriple atom (hDsub atom hmem)⟩
    have hCeq := Finset.eq_of_subset_of_card_le hCpairSub (by rw [hcardC, hEraseCard])
    have hDeq := Finset.eq_of_subset_of_card_le hDpairSub (by rw [hcardD, hEraseCard])
    exact hneCD (hCeq.trans hDeq.symm)
  have hendFirstNotB : endFirst ∉ bEdge := by
    intro hcontra
    rw [hBeq] at hcontra
    rcases Finset.mem_insert.mp hcontra with hcontra2 | hcontra2
    · exact hNotLeafSecond endFirst hendFirstXYZ hcontra2
    · exact hEndsNe (Finset.mem_singleton.mp hcontra2)
  have hendSecondNotA : endSecond ∉ aEdge := by
    intro hcontra
    rw [hAeq] at hcontra
    rcases Finset.mem_insert.mp hcontra with hcontra2 | hcontra2
    · exact hNotLeafFirst endSecond hendSecondXYZ hcontra2
    · exact hEndsNe (Finset.mem_singleton.mp hcontra2).symm
  have hCDBoth : ∀ atom : Fin 6, atom = xAtom ∨ atom = yAtom ∨ atom = zAtom →
      atom ∉ aEdge → atom ∉ bEdge → atom ∈ insideC ∧ atom ∈ insideD := by
    intro atom hxyz hna hnb
    rcases fourBlockCoverCount_eq_two_inversion (hxyzCount atom hxyz) with
        ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩ | ⟨_, hb, _, _⟩
      | ⟨_, hb, _, _⟩ | ⟨_, _, hc, hd⟩
    exacts [absurd ha hna, absurd ha hna, absurd ha hna, absurd hb hnb,
      absurd hb hnb, ⟨hc, hd⟩]
  rcases fourBlockCoverCount_eq_two_inversion (hxyzCount endFirst hendFirstXYZ) with
      ⟨_, hb, _, _⟩ | ⟨_, _, hendFirstMemC, hendFirstNotD⟩
    | ⟨_, _, hendFirstNotC, hendFirstMemD⟩ | ⟨ha, _, _, _⟩ | ⟨ha, _, _, _⟩
    | ⟨ha, _, _, _⟩
  · exact absurd hb hendFirstNotB
  -- endFirst threads through insideC
  · obtain ⟨midAtom, hmidNeEndFirst, hCeq⟩ :=
      exists_other_of_mem_card_two hcardC hendFirstMemC
    have hmidMemC : midAtom ∈ insideC := by
      rw [hCeq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have hmidXYZ := hCsub midAtom hmidMemC
    have hmidNotA : midAtom ∉ aEdge := by
      intro hcontra
      rw [hAeq] at hcontra
      rcases Finset.mem_insert.mp hcontra with hcontra2 | hcontra2
      · exact hNotLeafFirst midAtom hmidXYZ hcontra2
      · exact hmidNeEndFirst (Finset.mem_singleton.mp hcontra2)
    have hmidNeEndSecond : midAtom ≠ endSecond := by
      intro hcontra
      have hendSecondMemC : endSecond ∈ insideC := hcontra ▸ hmidMemC
      have hendSecondNotD : endSecond ∉ insideD := by
        rcases fourBlockCoverCount_eq_two_inversion
            (hxyzCount endSecond hendSecondXYZ) with
            ⟨ha2, _, _, _⟩ | ⟨ha2, _, _, _⟩ | ⟨ha2, _, _, _⟩ | ⟨_, _, _, hd2⟩
          | ⟨_, _, hc2, _⟩ | ⟨_, hb2, _, _⟩
        exacts [absurd ha2 hendSecondNotA, absurd ha2 hendSecondNotA,
          absurd ha2 hendSecondNotA, hd2, absurd hendSecondMemC hc2,
          absurd hendSecondMemB hb2]
      have hDsubPair : insideD ⊆ (({xAtom, yAtom, zAtom} : Finset (Fin 6)).erase
          endFirst).erase endSecond := by
        intro atom hmem
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨fun hcontra2 => hendSecondNotD (hcontra2 ▸ hmem),
          fun hcontra2 => hendFirstNotD (hcontra2 ▸ hmem),
          hmemTriple atom (hDsub atom hmem)⟩
      have hEraseCard : ((({xAtom, yAtom, zAtom} : Finset (Fin 6)).erase
          endFirst).erase endSecond).card = 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr
          ⟨hEndsNe.symm, hendSecondMemTriple⟩),
          Finset.card_erase_of_mem hendFirstMemTriple, hTripleCard]
      have hle := Finset.card_le_card hDsubPair
      rw [hcardD, hEraseCard] at hle
      omega
    have hmidNotB : midAtom ∉ bEdge := by
      intro hcontra
      rw [hBeq] at hcontra
      rcases Finset.mem_insert.mp hcontra with hcontra2 | hcontra2
      · exact hNotLeafSecond midAtom hmidXYZ hcontra2
      · exact hmidNeEndSecond (Finset.mem_singleton.mp hcontra2)
    have hmidMemD : midAtom ∈ insideD := (hCDBoth midAtom hmidXYZ hmidNotA hmidNotB).2
    obtain ⟨dOther, hdOtherNeMid, hDeq⟩ :=
      exists_other_of_mem_card_two hcardD hmidMemD
    have hdOtherMemD : dOther ∈ insideD := by
      rw [hDeq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have hSpineCard : ({endFirst, midAtom, endSecond} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp [Ne.symm hmidNeEndFirst, hEndsNe]),
        Finset.card_insert_of_notMem (by simp [hmidNeEndSecond]),
        Finset.card_singleton]
    have hSpineSub : ({endFirst, midAtom, endSecond} : Finset (Fin 6))
        ⊆ {xAtom, yAtom, zAtom} := by
      intro atom hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hendFirstMemTriple
      · exact hmemTriple _ hmidXYZ
      · exact hendSecondMemTriple
    have hSpineEq : ({endFirst, midAtom, endSecond} : Finset (Fin 6))
        = {xAtom, yAtom, zAtom} :=
      Finset.eq_of_subset_of_card_le hSpineSub (by rw [hTripleCard, hSpineCard])
    have hdOtherEnd : dOther = endSecond := by
      have hdOtherMemSpine : dOther ∈ ({endFirst, midAtom, endSecond} :
          Finset (Fin 6)) := by
        rw [hSpineEq]
        exact hmemTriple dOther (hDsub dOther hdOtherMemD)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hdOtherMemSpine
      rcases hdOtherMemSpine with hcase | hcase | hcase
      · exact absurd (hcase ▸ hdOtherMemD) hendFirstNotD
      · exact absurd hcase hdOtherNeMid
      · exact hcase
    have hDeqEnd : insideD = {midAtom, endSecond} := hdOtherEnd ▸ hDeq
    have hAeqFlipped : aEdge = {endFirst, leafFirst} :=
      hAeq.trans (Finset.pair_comm leafFirst endFirst)
    have hBeqFlipped : bEdge = {endSecond, leafSecond} :=
      hBeq.trans (Finset.pair_comm leafSecond endSecond)
    refine ⟨endFirst, midAtom, endSecond, hSpineEq, Ne.symm hmidNeEndFirst, hEndsNe,
      hmidNeEndSecond, ?_⟩
    rw [quadSet_swap_second_third aEdge bEdge insideC insideD,
      quadSet_swap_first_second aEdge insideC bEdge insideD,
      quadSet_swap_third_fourth insideC aEdge bEdge insideD,
      quadSet_swap_second_third insideC aEdge insideD bEdge,
      hCeq, hDeqEnd, hAeqFlipped, hBeqFlipped]
  -- endFirst threads through insideD
  · obtain ⟨midAtom, hmidNeEndFirst, hDeq⟩ :=
      exists_other_of_mem_card_two hcardD hendFirstMemD
    have hmidMemD : midAtom ∈ insideD := by
      rw [hDeq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have hmidXYZ := hDsub midAtom hmidMemD
    have hmidNotA : midAtom ∉ aEdge := by
      intro hcontra
      rw [hAeq] at hcontra
      rcases Finset.mem_insert.mp hcontra with hcontra2 | hcontra2
      · exact hNotLeafFirst midAtom hmidXYZ hcontra2
      · exact hmidNeEndFirst (Finset.mem_singleton.mp hcontra2)
    have hmidNeEndSecond : midAtom ≠ endSecond := by
      intro hcontra
      have hendSecondMemD : endSecond ∈ insideD := hcontra ▸ hmidMemD
      have hendSecondNotC : endSecond ∉ insideC := by
        rcases fourBlockCoverCount_eq_two_inversion
            (hxyzCount endSecond hendSecondXYZ) with
            ⟨ha2, _, _, _⟩ | ⟨ha2, _, _, _⟩ | ⟨ha2, _, _, _⟩ | ⟨_, _, _, hd2⟩
          | ⟨_, _, hc2, _⟩ | ⟨_, hb2, _, _⟩
        exacts [absurd ha2 hendSecondNotA, absurd ha2 hendSecondNotA,
          absurd ha2 hendSecondNotA, absurd hendSecondMemD hd2, hc2,
          absurd hendSecondMemB hb2]
      have hCsubPair : insideC ⊆ (({xAtom, yAtom, zAtom} : Finset (Fin 6)).erase
          endFirst).erase endSecond := by
        intro atom hmem
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨fun hcontra2 => hendSecondNotC (hcontra2 ▸ hmem),
          fun hcontra2 => hendFirstNotC (hcontra2 ▸ hmem),
          hmemTriple atom (hCsub atom hmem)⟩
      have hEraseCard : ((({xAtom, yAtom, zAtom} : Finset (Fin 6)).erase
          endFirst).erase endSecond).card = 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr
          ⟨hEndsNe.symm, hendSecondMemTriple⟩),
          Finset.card_erase_of_mem hendFirstMemTriple, hTripleCard]
      have hle := Finset.card_le_card hCsubPair
      rw [hcardC, hEraseCard] at hle
      omega
    have hmidNotB : midAtom ∉ bEdge := by
      intro hcontra
      rw [hBeq] at hcontra
      rcases Finset.mem_insert.mp hcontra with hcontra2 | hcontra2
      · exact hNotLeafSecond midAtom hmidXYZ hcontra2
      · exact hmidNeEndSecond (Finset.mem_singleton.mp hcontra2)
    have hmidMemC : midAtom ∈ insideC := (hCDBoth midAtom hmidXYZ hmidNotA hmidNotB).1
    obtain ⟨cOther, hcOtherNeMid, hCeq⟩ :=
      exists_other_of_mem_card_two hcardC hmidMemC
    have hcOtherMemC : cOther ∈ insideC := by
      rw [hCeq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have hSpineCard : ({endFirst, midAtom, endSecond} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp [Ne.symm hmidNeEndFirst, hEndsNe]),
        Finset.card_insert_of_notMem (by simp [hmidNeEndSecond]),
        Finset.card_singleton]
    have hSpineSub : ({endFirst, midAtom, endSecond} : Finset (Fin 6))
        ⊆ {xAtom, yAtom, zAtom} := by
      intro atom hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hendFirstMemTriple
      · exact hmemTriple _ hmidXYZ
      · exact hendSecondMemTriple
    have hSpineEq : ({endFirst, midAtom, endSecond} : Finset (Fin 6))
        = {xAtom, yAtom, zAtom} :=
      Finset.eq_of_subset_of_card_le hSpineSub (by rw [hTripleCard, hSpineCard])
    have hcOtherEnd : cOther = endSecond := by
      have hcOtherMemSpine : cOther ∈ ({endFirst, midAtom, endSecond} :
          Finset (Fin 6)) := by
        rw [hSpineEq]
        exact hmemTriple cOther (hCsub cOther hcOtherMemC)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcOtherMemSpine
      rcases hcOtherMemSpine with hcase | hcase | hcase
      · exact absurd (hcase ▸ hcOtherMemC) hendFirstNotC
      · exact absurd hcase hcOtherNeMid
      · exact hcase
    have hCeqEnd : insideC = {midAtom, endSecond} := hcOtherEnd ▸ hCeq
    have hAeqFlipped : aEdge = {endFirst, leafFirst} :=
      hAeq.trans (Finset.pair_comm leafFirst endFirst)
    have hBeqFlipped : bEdge = {endSecond, leafSecond} :=
      hBeq.trans (Finset.pair_comm leafSecond endSecond)
    refine ⟨endFirst, midAtom, endSecond, hSpineEq, Ne.symm hmidNeEndFirst, hEndsNe,
      hmidNeEndSecond, ?_⟩
    rw [quadSet_swap_second_third aEdge bEdge insideC insideD,
      quadSet_swap_third_fourth aEdge insideC bEdge insideD,
      quadSet_swap_first_second aEdge insideC insideD bEdge,
      quadSet_swap_second_third insideC aEdge insideD bEdge,
      quadSet_swap_first_second insideC insideD aEdge bEdge,
      hDeq, hCeqEnd, hAeqFlipped, hBeqFlipped]
  · exact absurd hendFirstMemA ha
  · exact absurd hendFirstMemA ha
  · exact absurd hendFirstMemA ha

/-- The canonical five-path family: hub `0`, spine `1-2-3`, leaves `4` on the
first end and `5` on the second. -/
def canonicalFivePathFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 2, 3}, {0, 1, 4}, {0, 3, 5}}

/-- The canonical triangle-plus-edge family: hub `0`, triangle `1,2,3`,
pendant edge `4-5`. -/
def canonicalTriangleEdgeFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {0, 4, 5}}

/-- **THE PATH-AND-TRIANGLE CAPSTONE.**  Any four-block family with profile
counts `(quadruple, double, single) = (1, 3, 2)` relabels onto the canonical
five-path or the canonical triangle-plus-edge. -/
theorem exists_map_family_eq_canonicalPath_or_triangle_of_profile
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hneOneTwo : firstBlock ≠ secondBlock) (hneOneThree : firstBlock ≠ thirdBlock)
    (hneOneFour : firstBlock ≠ fourthBlock) (hneTwoThree : secondBlock ≠ thirdBlock)
    (hneTwoFour : secondBlock ≠ fourthBlock) (hneThreeFour : thirdBlock ≠ fourthBlock)
    (hcardOne : firstBlock.card = 3) (hcardTwo : secondBlock.card = 3)
    (hcardThree : thirdBlock.card = 3) (hcardFour : fourthBlock.card = 3)
    (hquadClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4 = 1)
    (hdoubleClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2
      = 3)
    (hsingleClass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1
      = 2) :
    ∃ relabelPerm : Equiv.Perm (Fin 6),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalFivePathFamily
        ∨ ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map relabelPerm.toEmbedding)
          = canonicalTriangleEdgeFamily := by
  classical
  obtain ⟨hubAtom, hhubCount, hhubUnique⟩ := exists_unique_atom_of_classCard_one hquadClass
  obtain ⟨xAtom, yAtom, zAtom, hneXY, hneXZ, hneYZ, hxCount, hyCount, hzCount⟩ :=
    exists_three_atoms_of_classCard_three hdoubleClass
  obtain ⟨leafFirst, leafSecond, hneLeaves, haCount, hbCount⟩ :=
    exists_two_atoms_of_classCard_two hsingleClass
  obtain ⟨hhubOne, hhubTwo, hhubThree, hhubFour⟩ :=
    mem_all_of_fourBlockCoverCount_eq_four hhubCount
  have hXNeHub : xAtom ≠ hubAtom := by
    intro hcontra; rw [hcontra, hhubCount] at hxCount; omega
  have hYNeHub : yAtom ≠ hubAtom := by
    intro hcontra; rw [hcontra, hhubCount] at hyCount; omega
  have hZNeHub : zAtom ≠ hubAtom := by
    intro hcontra; rw [hcontra, hhubCount] at hzCount; omega
  have hANeHub : leafFirst ≠ hubAtom := by
    intro hcontra; rw [hcontra, hhubCount] at haCount; omega
  have hBNeHub : leafSecond ≠ hubAtom := by
    intro hcontra; rw [hcontra, hhubCount] at hbCount; omega
  have hANeX : leafFirst ≠ xAtom := by
    intro hcontra; rw [hcontra, hxCount] at haCount; omega
  have hANeY : leafFirst ≠ yAtom := by
    intro hcontra; rw [hcontra, hyCount] at haCount; omega
  have hANeZ : leafFirst ≠ zAtom := by
    intro hcontra; rw [hcontra, hzCount] at haCount; omega
  have hBNeX : leafSecond ≠ xAtom := by
    intro hcontra; rw [hcontra, hxCount] at hbCount; omega
  have hBNeY : leafSecond ≠ yAtom := by
    intro hcontra; rw [hcontra, hyCount] at hbCount; omega
  have hBNeZ : leafSecond ≠ zAtom := by
    intro hcontra; rw [hcontra, hzCount] at hbCount; omega
  have hUnivEq : ({hubAtom, xAtom, yAtom, zAtom, leafFirst, leafSecond} :
      Finset (Fin 6)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by
        simp [hXNeHub.symm, hYNeHub.symm, hZNeHub.symm, hANeHub.symm, hBNeHub.symm]),
      Finset.card_insert_of_notMem (by simp [hneXY, hneXZ, hANeX.symm, hBNeX.symm]),
      Finset.card_insert_of_notMem (by simp [hneYZ, hANeY.symm, hBNeY.symm]),
      Finset.card_insert_of_notMem (by simp [hANeZ.symm, hBNeZ.symm]),
      Finset.card_insert_of_notMem (by simp [hneLeaves]), Finset.card_singleton,
      Fintype.card_fin]
  have hedgeAtomsAll : ∀ atom : Fin 6,
      (atom ∈ firstBlock.erase hubAtom ∨ atom ∈ secondBlock.erase hubAtom
        ∨ atom ∈ thirdBlock.erase hubAtom ∨ atom ∈ fourthBlock.erase hubAtom)
      → atom = xAtom ∨ atom = yAtom ∨ atom = zAtom ∨ atom = leafFirst
        ∨ atom = leafSecond := by
    intro atom hmem
    have hneAtomHub : atom ≠ hubAtom := by
      rcases hmem with h | h | h | h <;>
        exact fun hcontra => Finset.notMem_erase hubAtom _ (hcontra ▸ h)
    have hmemSix : atom ∈ ({hubAtom, xAtom, yAtom, zAtom, leafFirst, leafSecond} :
        Finset (Fin 6)) := by
      rw [hUnivEq]
      exact Finset.mem_univ atom
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemSix
    rcases hmemSix with hcase | hcase | hcase | hcase | hcase | hcase
    exacts [absurd hcase hneAtomHub, Or.inl hcase, Or.inr (Or.inl hcase),
      Or.inr (Or.inr (Or.inl hcase)), Or.inr (Or.inr (Or.inr (Or.inl hcase))),
      Or.inr (Or.inr (Or.inr (Or.inr hcase)))]
  rcases exists_leaf_normalization_of_count_one_one
      (erase_hub_ne_of_ne hneOneTwo hhubOne hhubTwo)
      (erase_hub_ne_of_ne hneOneThree hhubOne hhubThree)
      (erase_hub_ne_of_ne hneOneFour hhubOne hhubFour)
      (erase_hub_ne_of_ne hneTwoThree hhubTwo hhubThree)
      (erase_hub_ne_of_ne hneTwoFour hhubTwo hhubFour)
      (erase_hub_ne_of_ne hneThreeFour hhubThree hhubFour)
      (card_erase_hub_eq_two hcardOne hhubOne) (card_erase_hub_eq_two hcardTwo hhubTwo)
      (card_erase_hub_eq_two hcardThree hhubThree)
      (card_erase_hub_eq_two hcardFour hhubFour)
      ((fourBlockCoverCount_erase_hub hANeHub).trans haCount)
      ((fourBlockCoverCount_erase_hub hBNeHub).trans hbCount) with
    ⟨insideA, insideB, insideC, leafEdge, hSetEq, hCountEq, hcardInA, hcardInB,
        hcardInC, hcardLeaf, hneInAB, hneInAC, hneInBC, haMemLeaf, haNotInA, haNotInB,
        haNotInC, hbMemLeaf, hbNotInA, hbNotInB, hbNotInC⟩
    | ⟨aEdge, bEdge, insideC, insideD, hSetEq, hCountEq, hcardAE, hcardBE, hcardInC,
        hcardInD, hneInCD, haMemAE, haNotBE, haNotInC, haNotInD, hbMemBE, hbNotAE,
        hbNotInC, hbNotInD⟩
  -- the two leaves share one edge: the TRIANGLE door
  · have hTupleAtoms : ∀ atom : Fin 6,
        (atom ∈ insideA ∨ atom ∈ insideB ∨ atom ∈ insideC ∨ atom ∈ leafEdge)
          → atom = xAtom ∨ atom = yAtom ∨ atom = zAtom ∨ atom = leafFirst
            ∨ atom = leafSecond := by
      intro atom hmem
      have hedgeMem : ∀ edge : Finset (Fin 6),
          edge ∈ ({insideA, insideB, insideC, leafEdge} : Finset (Finset (Fin 6)))
            → atom ∈ edge
            → atom ∈ firstBlock.erase hubAtom ∨ atom ∈ secondBlock.erase hubAtom
              ∨ atom ∈ thirdBlock.erase hubAtom ∨ atom ∈ fourthBlock.erase hubAtom := by
        intro edge hedge hatomMem
        rw [← hSetEq] at hedge
        simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
        rcases hedge with rfl | rfl | rfl | rfl
        exacts [Or.inl hatomMem, Or.inr (Or.inl hatomMem),
          Or.inr (Or.inr (Or.inl hatomMem)), Or.inr (Or.inr (Or.inr hatomMem))]
      rcases hmem with h | h | h | h
      · exact hedgeAtomsAll atom (hedgeMem insideA (by simp) h)
      · exact hedgeAtomsAll atom (hedgeMem insideB (by simp) h)
      · exact hedgeAtomsAll atom (hedgeMem insideC (by simp) h)
      · exact hedgeAtomsAll atom (hedgeMem leafEdge (by simp) h)
    have hInsideAtoms : ∀ atom : Fin 6,
        (atom ∈ insideA ∨ atom ∈ insideB ∨ atom ∈ insideC)
          → atom = xAtom ∨ atom = yAtom ∨ atom = zAtom := by
      intro atom hmem
      rcases hTupleAtoms atom (by tauto) with h | h | h | rfl | rfl
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · rcases hmem with h | h | h
        exacts [absurd h haNotInA, absurd h haNotInB, absurd h haNotInC]
      · rcases hmem with h | h | h
        exacts [absurd h hbNotInA, absurd h hbNotInB, absurd h hbNotInC]
    have hTriEq := edgeSet_eq_triangle_of_leaf_edge hcardInA hcardInB hcardInC hneInAB
      hneInAC hneInBC hneXY hneXZ hneYZ hInsideAtoms
    have hLeafEq : leafEdge = {leafFirst, leafSecond} :=
      eq_pair_of_mem_mem_card_two hcardLeaf hneLeaves haMemLeaf hbMemLeaf
    have hQuadEq : ({insideA, insideB, insideC, leafEdge} : Finset (Finset (Fin 6)))
        = {{xAtom, yAtom}, {xAtom, zAtom}, {yAtom, zAtom},
           {leafFirst, leafSecond}} := by
      rw [quadSet_eq_tripleSet_union insideA insideB insideC leafEdge, hTriEq, hLeafEq,
        ← quadSet_eq_tripleSet_union]
    have hinj : Function.Injective
        ![hubAtom, xAtom, yAtom, zAtom, leafFirst, leafSecond] :=
      injective_sixAtomAssignment hXNeHub.symm hYNeHub.symm hZNeHub.symm hANeHub.symm
        hBNeHub.symm hneXY hneXZ hANeX.symm hBNeX.symm hneYZ hANeY.symm hBNeY.symm
        hANeZ.symm hBNeZ.symm hneLeaves
    let atomAssignment : Equiv.Perm (Fin 6) :=
      Equiv.ofBijective ![hubAtom, xAtom, yAtom, zAtom, leafFirst, leafSecond]
        (Finite.injective_iff_bijective.mp hinj)
    have hpiHub : atomAssignment.symm hubAtom = 0 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiX : atomAssignment.symm xAtom = 1 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiY : atomAssignment.symm yAtom = 2 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiZ : atomAssignment.symm zAtom = 3 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiA : atomAssignment.symm leafFirst = 4 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiB : atomAssignment.symm leafSecond = 5 := by
      rw [Equiv.symm_apply_eq]; rfl
    refine ⟨atomAssignment.symm, Or.inr ?_⟩
    rw [family_eq_image_insert_erase_of_hub_mem_all hhubOne hhubTwo hhubThree hhubFour,
      hSetEq, hQuadEq]
    simp only [Finset.image_insert, Finset.image_singleton]
    rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
      map_triple_toEmbedding, hpiHub, hpiX, hpiY, hpiZ, hpiA, hpiB]
    rfl
  -- the two leaves hang on distinct edges: the FIVE-PATH door
  · have hTupleAtoms : ∀ atom : Fin 6,
        (atom ∈ aEdge ∨ atom ∈ bEdge ∨ atom ∈ insideC ∨ atom ∈ insideD)
          → atom = xAtom ∨ atom = yAtom ∨ atom = zAtom ∨ atom = leafFirst
            ∨ atom = leafSecond := by
      intro atom hmem
      have hedgeMem : ∀ edge : Finset (Fin 6),
          edge ∈ ({aEdge, bEdge, insideC, insideD} : Finset (Finset (Fin 6)))
            → atom ∈ edge
            → atom ∈ firstBlock.erase hubAtom ∨ atom ∈ secondBlock.erase hubAtom
              ∨ atom ∈ thirdBlock.erase hubAtom ∨ atom ∈ fourthBlock.erase hubAtom := by
        intro edge hedge hatomMem
        rw [← hSetEq] at hedge
        simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
        rcases hedge with rfl | rfl | rfl | rfl
        exacts [Or.inl hatomMem, Or.inr (Or.inl hatomMem),
          Or.inr (Or.inr (Or.inl hatomMem)), Or.inr (Or.inr (Or.inr hatomMem))]
      rcases hmem with h | h | h | h
      · exact hedgeAtomsAll atom (hedgeMem aEdge (by simp) h)
      · exact hedgeAtomsAll atom (hedgeMem bEdge (by simp) h)
      · exact hedgeAtomsAll atom (hedgeMem insideC (by simp) h)
      · exact hedgeAtomsAll atom (hedgeMem insideD (by simp) h)
    have hxyzCountTuple : ∀ atom : Fin 6,
        atom = xAtom ∨ atom = yAtom ∨ atom = zAtom →
        fourBlockCoverCount aEdge bEdge insideC insideD atom = 2 := by
      rintro atom (rfl | rfl | rfl)
      · exact (hCountEq atom).trans
          ((fourBlockCoverCount_erase_hub hXNeHub).trans hxCount)
      · exact (hCountEq atom).trans
          ((fourBlockCoverCount_erase_hub hYNeHub).trans hyCount)
      · exact (hCountEq atom).trans
          ((fourBlockCoverCount_erase_hub hZNeHub).trans hzCount)
    obtain ⟨endFirst, midAtom, endSecond, hSpineEq, hneEndMid, hneEnds, hneMidEnd,
        hPathEq⟩ :=
      edgeSet_eq_path_of_leaf_edges hcardAE hcardBE hcardInC hcardInD hneInCD hneXY
        hneXZ hneYZ hANeX hANeY hANeZ hBNeX hBNeY hBNeZ haMemAE haNotBE haNotInC
        haNotInD hbMemBE hbNotAE hbNotInC hbNotInD hxyzCountTuple hTupleAtoms
    have hspineFacts : ∀ atom : Fin 6,
        atom ∈ ({xAtom, yAtom, zAtom} : Finset (Fin 6))
          → atom ≠ hubAtom ∧ atom ≠ leafFirst ∧ atom ≠ leafSecond := by
      intro atom hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      exacts [⟨hXNeHub, hANeX.symm, hBNeX.symm⟩, ⟨hYNeHub, hANeY.symm, hBNeY.symm⟩,
        ⟨hZNeHub, hANeZ.symm, hBNeZ.symm⟩]
    have hEndFNe := hspineFacts endFirst (by rw [← hSpineEq]; simp)
    have hMidNe := hspineFacts midAtom (by rw [← hSpineEq]; simp)
    have hEndSNe := hspineFacts endSecond (by rw [← hSpineEq]; simp)
    have hinj : Function.Injective
        ![hubAtom, endFirst, midAtom, endSecond, leafFirst, leafSecond] :=
      injective_sixAtomAssignment hEndFNe.1.symm hMidNe.1.symm hEndSNe.1.symm
        hANeHub.symm hBNeHub.symm hneEndMid hneEnds hEndFNe.2.1 hEndFNe.2.2
        hneMidEnd hMidNe.2.1 hMidNe.2.2 hEndSNe.2.1 hEndSNe.2.2 hneLeaves
    let atomAssignment : Equiv.Perm (Fin 6) :=
      Equiv.ofBijective ![hubAtom, endFirst, midAtom, endSecond, leafFirst, leafSecond]
        (Finite.injective_iff_bijective.mp hinj)
    have hpiHub : atomAssignment.symm hubAtom = 0 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiEndF : atomAssignment.symm endFirst = 1 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiMid : atomAssignment.symm midAtom = 2 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiEndS : atomAssignment.symm endSecond = 3 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiA : atomAssignment.symm leafFirst = 4 := by
      rw [Equiv.symm_apply_eq]; rfl
    have hpiB : atomAssignment.symm leafSecond = 5 := by
      rw [Equiv.symm_apply_eq]; rfl
    refine ⟨atomAssignment.symm, Or.inl ?_⟩
    rw [family_eq_image_insert_erase_of_hub_mem_all hhubOne hhubTwo hhubThree hhubFour,
      hSetEq, hPathEq]
    simp only [Finset.image_insert, Finset.image_singleton]
    rw [map_triple_toEmbedding, map_triple_toEmbedding, map_triple_toEmbedding,
      map_triple_toEmbedding, hpiHub, hpiEndF, hpiMid, hpiEndS, hpiA, hpiB]
    rfl

end Gtz

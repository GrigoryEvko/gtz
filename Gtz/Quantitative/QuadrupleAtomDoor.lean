import Mathlib
import Gtz.Quantitative.FourFamilyCoverProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The quadruple-atom door of the four-family census

A cover count of four names an atom lying in all four blocks, and a card-three
block through two named atoms is those two plus a third.  Together these open
the three profile doors carrying a quadruply-covered atom: every block of such
a family is the shared atom pair (or atom) completed by thirds, which is the
edge-pencil normal form the orbit reduction sends to its representative.
-/

namespace Gtz

/-- A cover count of four puts the atom in all four blocks. -/
theorem mem_all_of_fourBlockCoverCount_eq_four
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    {atomIndex : Fin 6}
    (hcount : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
      = 4) :
    atomIndex ∈ firstBlock ∧ atomIndex ∈ secondBlock
      ∧ atomIndex ∈ thirdBlock ∧ atomIndex ∈ fourthBlock := by
  unfold fourBlockCoverCount at hcount
  split_ifs at hcount <;>
    first
    | omega
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;> assumption)

/-- A card-three block through two distinct named atoms is those two atoms and
a third. -/
theorem exists_third_of_pair_mem_card_three
    {block : Finset (Fin 6)} (hcard : block.card = 3)
    {firstAtom secondAtom : Fin 6} (hne : firstAtom ≠ secondAtom)
    (hfirst : firstAtom ∈ block) (hsecond : secondAtom ∈ block) :
    ∃ thirdAtom : Fin 6, thirdAtom ≠ firstAtom ∧ thirdAtom ≠ secondAtom
      ∧ block = {firstAtom, secondAtom, thirdAtom} := by
  classical
  have hpairSubset : ({firstAtom, secondAtom} : Finset (Fin 6)) ⊆ block := by
    intro atom hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem
    · exact hfirst
    · rw [Finset.mem_singleton] at hmem
      exact hmem ▸ hsecond
  have hpairCard : ({firstAtom, secondAtom} : Finset (Fin 6)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hdiffCard : (block \ {firstAtom, secondAtom}).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hpairSubset, hcard, hpairCard]
  obtain ⟨thirdAtom, hthird⟩ := Finset.card_eq_one.mp hdiffCard
  have hthirdMem : thirdAtom ∈ block \ ({firstAtom, secondAtom} : Finset (Fin 6)) := by
    rw [hthird]
    exact Finset.mem_singleton_self thirdAtom
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hthirdMem
  have hthirdNeFirst : thirdAtom ≠ firstAtom := fun hcontra => hthirdMem.2 (Or.inl hcontra)
  have hthirdNeSecond : thirdAtom ≠ secondAtom := fun hcontra => hthirdMem.2 (Or.inr hcontra)
  refine ⟨thirdAtom, hthirdNeFirst, hthirdNeSecond, ?_⟩
  have hsubset : ({firstAtom, secondAtom, thirdAtom} : Finset (Fin 6)) ⊆ block := by
    intro atom hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem
    · exact hfirst
    · rcases Finset.mem_insert.mp hmem with rfl | hmem
      · exact hsecond
      · rw [Finset.mem_singleton] at hmem
        exact hmem ▸ hthirdMem.1
  have hfirstNot : firstAtom ∉ ({secondAtom, thirdAtom} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (hcontra | hcontra)
    · exact hne hcontra
    · exact hthirdNeFirst hcontra.symm
  have hsecondNot : secondAtom ∉ ({thirdAtom} : Finset (Fin 6)) := by
    simp only [Finset.mem_singleton]
    intro hcontra
    exact hthirdNeSecond hcontra.symm
  have hthirdCard : ({firstAtom, secondAtom, thirdAtom} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem hfirstNot, Finset.card_insert_of_notMem hsecondNot,
      Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsubset (by rw [hcard, hthirdCard])).symm

end Gtz

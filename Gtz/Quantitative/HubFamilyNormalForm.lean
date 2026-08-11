import Mathlib
import Gtz.Quantitative.PencilDoorReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The hub normal form: one quadruple atom turns the family into a graph

A single quadruply-covered hub sits in every block, so erasing it leaves four
pairwise-distinct EDGES on the five off-hub atoms, the family is the image of
that edge set under insertion of the hub, off-hub cover counts become edge
degrees, and covering makes the edge set span the off-hub atoms.  The two
single-hub profile doors are thereby exactly the 4-edge graphs on five
vertices with degree sequences `(2,2,2,1,1)` and `(3,2,1,1,1)` — the object
the graph classification consumes.
-/

namespace Gtz

/-- Erasing the hub from a card-three block through it leaves an edge. -/
theorem card_erase_hub_eq_two {block : Finset (Fin 6)} (hcard : block.card = 3)
    {hubAtom : Fin 6} (hmem : hubAtom ∈ block) :
    (block.erase hubAtom).card = 2 := by
  rw [Finset.card_erase_of_mem hmem, hcard]

/-- Distinct blocks through a common hub erase to distinct edges. -/
theorem erase_hub_ne_of_ne {firstBlock secondBlock : Finset (Fin 6)}
    (hne : firstBlock ≠ secondBlock) {hubAtom : Fin 6}
    (hfirstMem : hubAtom ∈ firstBlock) (hsecondMem : hubAtom ∈ secondBlock) :
    firstBlock.erase hubAtom ≠ secondBlock.erase hubAtom := by
  intro hcontra
  apply hne
  rw [← Finset.insert_erase hfirstMem, ← Finset.insert_erase hsecondMem, hcontra]

/-- Off the hub, the cover counts of the blocks and of their erased edges
agree: cover counts are edge degrees. -/
theorem fourBlockCoverCount_erase_hub {firstBlock secondBlock thirdBlock fourthBlock :
      Finset (Fin 6)} {hubAtom atomIndex : Fin 6} (hne : atomIndex ≠ hubAtom) :
    fourBlockCoverCount (firstBlock.erase hubAtom) (secondBlock.erase hubAtom)
        (thirdBlock.erase hubAtom) (fourthBlock.erase hubAtom) atomIndex
      = fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex := by
  simp only [fourBlockCoverCount, Finset.mem_erase, ne_eq, hne, not_false_eq_true, true_and]

/-- **THE HUB NORMAL FORM.**  A four-block family through a common hub is the
image of its erased edge set under insertion of the hub. -/
theorem family_eq_image_insert_erase_of_hub_mem_all
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)} {hubAtom : Fin 6}
    (hfirstMem : hubAtom ∈ firstBlock) (hsecondMem : hubAtom ∈ secondBlock)
    (hthirdMem : hubAtom ∈ thirdBlock) (hfourthMem : hubAtom ∈ fourthBlock) :
    ({firstBlock, secondBlock, thirdBlock, fourthBlock} : Finset (Finset (Fin 6)))
      = ({firstBlock.erase hubAtom, secondBlock.erase hubAtom, thirdBlock.erase hubAtom,
          fourthBlock.erase hubAtom} : Finset (Finset (Fin 6))).image
            (insert hubAtom) := by
  ext block
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨block.erase hubAtom, Or.inl rfl, Finset.insert_erase hfirstMem⟩
    · exact ⟨block.erase hubAtom, Or.inr (Or.inl rfl), Finset.insert_erase hsecondMem⟩
    · exact ⟨block.erase hubAtom, Or.inr (Or.inr (Or.inl rfl)),
        Finset.insert_erase hthirdMem⟩
    · exact ⟨block.erase hubAtom, Or.inr (Or.inr (Or.inr rfl)),
        Finset.insert_erase hfourthMem⟩
  · rintro ⟨edge, (rfl | rfl | rfl | rfl), rfl⟩
    · exact Or.inl (Finset.insert_erase hfirstMem)
    · exact Or.inr (Or.inl (Finset.insert_erase hsecondMem))
    · exact Or.inr (Or.inr (Or.inl (Finset.insert_erase hthirdMem)))
    · exact Or.inr (Or.inr (Or.inr (Finset.insert_erase hfourthMem)))

/-- Under covering, every off-hub atom lies on some erased edge: the edge set
spans the five off-hub atoms. -/
theorem exists_mem_erase_of_cover_of_ne_hub
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock = Finset.univ)
    {hubAtom atomIndex : Fin 6} (hne : atomIndex ≠ hubAtom) :
    atomIndex ∈ firstBlock.erase hubAtom ∨ atomIndex ∈ secondBlock.erase hubAtom
      ∨ atomIndex ∈ thirdBlock.erase hubAtom ∨ atomIndex ∈ fourthBlock.erase hubAtom := by
  have hmem : atomIndex ∈ firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock := by
    rw [hcover]
    exact Finset.mem_univ atomIndex
  simp only [Finset.mem_union] at hmem
  simp only [Finset.mem_erase]
  tauto

/-- The hub cannot lie on its own erased edges, so every erased edge is a
two-element subset of the off-hub atoms. -/
theorem erase_hub_subset_compl {block : Finset (Fin 6)} (hubAtom : Fin 6) :
    block.erase hubAtom ⊆ ({hubAtom} : Finset (Fin 6))ᶜ := by
  intro atom hmem
  rw [Finset.mem_compl, Finset.mem_singleton]
  exact (Finset.mem_erase.mp hmem).1

/-- A singleton quadruple class makes the hub unique: off the hub, no atom is
quadruply covered, so every erased edge degree is at most three. -/
theorem count_ne_four_of_ne_hub_of_classCard_one
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hclass : fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4 = 1)
    {hubAtom atomIndex : Fin 6}
    (hhub : fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock hubAtom = 4)
    (hne : atomIndex ≠ hubAtom) :
    fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex ≠ 4 := by
  intro hcontra
  have hpairSubset : ({hubAtom, atomIndex} : Finset (Fin 6)) ⊆
      Finset.univ.filter (fun atom =>
        fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atom = 4) := by
    intro atom hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ atom, hhub⟩
    · rw [Finset.mem_singleton] at hmem
      subst hmem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ atom, hcontra⟩
  have hpairCard : ({hubAtom, atomIndex} : Finset (Fin 6)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne.symm), Finset.card_singleton]
  have hclassBound := Finset.card_le_card hpairSubset
  rw [hpairCard] at hclassBound
  rw [fourBlockCountClass] at hclass
  omega

end Gtz

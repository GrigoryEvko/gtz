import Mathlib
import Gtz.Quantitative.PathTriangleDoorReduction
import Gtz.Quantitative.CruxRelabel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

/-!
# The quadruple-door dispatch: card-four crux families hit their canonicals

A crux whose argmax family has four blocks names four pairwise-distinct
card-three triples covering the six atoms, so the landed profile census
applies: seven count profiles, of which the three carrying a quadruple atom
are now CLOSED doors.  The dispatch composes the family extraction, the
coverage law, the profile census, the three door capstones, and the crux
relabelling transport into one statement: every card-four crux either
relabels to a crux whose argmax family IS one of the four canonical
quadruple representatives (pencil, chair, five-path, triangle-plus-edge), or
its family realizes one of the four quadruple-free profiles — the exact
interface the remaining census doors consume.
-/

namespace Gtz

/-- Union form of a four-set covering union. -/
theorem union_four_eq_univ_of_biUnion
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hbiUnion : ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
      Finset (Finset (Fin 6))).biUnion id = Finset.univ) :
    firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro atomIndex
  have hmem := Finset.eq_univ_iff_forall.mp hbiUnion atomIndex
  rw [Finset.mem_biUnion] at hmem
  obtain ⟨block, hblockMem, hatomMem⟩ := hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hblockMem
  simp only [Finset.mem_union]
  rcases hblockMem with rfl | rfl | rfl | rfl
  exacts [Or.inl (Or.inl (Or.inl hatomMem)), Or.inl (Or.inl (Or.inr hatomMem)),
    Or.inl (Or.inr hatomMem), Or.inr hatomMem]

/-- Coverage in union-of-family form: the argmax blocks exhaust the atoms. -/
theorem SixThreeCrux.biUnion_chartArgmaxFamily_eq_univ (crux : SixThreeCrux) :
    (chartArgmaxFamily (chartPointOfDesign crux.design)).biUnion id
      = (Finset.univ : Finset (Fin 6)) := by
  apply Finset.eq_univ_iff_forall.mpr
  intro atomIndex
  obtain ⟨block, hblockMem, hatomMem⟩ := crux.exists_mem_chartArgmaxFamily atomIndex
  exact Finset.mem_biUnion.mpr ⟨block, hblockMem, hatomMem⟩

/-- **THE QUADRUPLE-DOOR DISPATCH.**  A card-four crux either relabels onto a
canonical quadruple-door representative or realizes a quadruple-free
profile. -/
theorem SixThreeCrux.relabel_canonical_or_noQuadProfile_of_card_four
    (crux : SixThreeCrux)
    (hcardFour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    (∃ relabelPerm : Equiv.Perm (Fin 6),
      chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
          = canonicalEdgePencil
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
          = canonicalChairFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
          = canonicalFivePathFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
          = canonicalTriangleEdgeFamily)
      ∨ (∃ firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6),
        chartArgmaxFamily (chartPointOfDesign crux.design)
            = {firstBlock, secondBlock, thirdBlock, fourthBlock}
          ∧ firstBlock ≠ secondBlock ∧ firstBlock ≠ thirdBlock
          ∧ firstBlock ≠ fourthBlock ∧ secondBlock ≠ thirdBlock
          ∧ secondBlock ≠ fourthBlock ∧ thirdBlock ≠ fourthBlock
          ∧ firstBlock.card = 3 ∧ secondBlock.card = 3 ∧ thirdBlock.card = 3
          ∧ fourthBlock.card = 3
          ∧ firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock = Finset.univ
          ∧ ((fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4,
                fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3,
                fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2,
                fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1)
                  = (0, 0, 6, 0)
              ∨ (fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4,
                  fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3,
                  fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2,
                  fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1)
                  = (0, 1, 4, 1)
              ∨ (fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4,
                  fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3,
                  fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2,
                  fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1)
                  = (0, 2, 2, 2)
              ∨ (fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4,
                  fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3,
                  fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2,
                  fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1)
                  = (0, 3, 0, 3))) := by
  classical
  obtain ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, hneOneTwo, hneOneThree,
      hneOneFour, hneTwoThree, hneTwoFour, hneThreeFour, hfamEq⟩ :=
    Finset.card_eq_four.mp hcardFour
  have hmemCard : ∀ block ∈ ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
      Finset (Finset (Fin 6))), block.card = 3 := by
    intro block hmem
    rw [← hfamEq] at hmem
    exact ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) block).mp hmem).1
  have hcardOne : firstBlock.card = 3 := hmemCard firstBlock (by simp)
  have hcardTwo : secondBlock.card = 3 := hmemCard secondBlock (by simp)
  have hcardThree : thirdBlock.card = 3 := hmemCard thirdBlock (by simp)
  have hcardFourth : fourthBlock.card = 3 := hmemCard fourthBlock (by simp)
  have hcover : firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock = Finset.univ := by
    apply union_four_eq_univ_of_biUnion
    rw [← hfamEq]
    exact crux.biUnion_chartArgmaxFamily_eq_univ
  have hrelabelOf : ∀ relabelPerm : Equiv.Perm (Fin 6),
      ∀ target : Finset (Finset (Fin 6)),
      ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
          Finset (Finset (Fin 6))).image
          (fun block => block.map relabelPerm.toEmbedding) = target
        → chartArgmaxFamily (chartPointOfDesign
            ((crux.relabel relabelPerm.symm).design)) = target := by
    intro relabelPerm target hdoor
    have hfamRelabel := chartArgmaxFamily_relabelDesign crux.design relabelPerm.symm
    rw [Equiv.symm_symm, hfamEq] at hfamRelabel
    exact hfamRelabel.trans hdoor
  rcases fourBlockCountClass_profile_of_cover hcardOne hcardTwo hcardThree hcardFourth
      hcover with hprof | hprof | hprof | hprof | hprof | hprof | hprof
  · exact Or.inr ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, hfamEq, hneOneTwo,
      hneOneThree, hneOneFour, hneTwoThree, hneTwoFour, hneThreeFour, hcardOne,
      hcardTwo, hcardThree, hcardFourth, hcover, Or.inl hprof⟩
  · exact Or.inr ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, hfamEq, hneOneTwo,
      hneOneThree, hneOneFour, hneTwoThree, hneTwoFour, hneThreeFour, hcardOne,
      hcardTwo, hcardThree, hcardFourth, hcover, Or.inr (Or.inl hprof)⟩
  · exact Or.inr ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, hfamEq, hneOneTwo,
      hneOneThree, hneOneFour, hneTwoThree, hneTwoFour, hneThreeFour, hcardOne,
      hcardTwo, hcardThree, hcardFourth, hcover, Or.inr (Or.inr (Or.inl hprof))⟩
  · exact Or.inr ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, hfamEq, hneOneTwo,
      hneOneThree, hneOneFour, hneTwoThree, hneTwoFour, hneThreeFour, hcardOne,
      hcardTwo, hcardThree, hcardFourth, hcover, Or.inr (Or.inr (Or.inr hprof))⟩
  -- profile (1,0,3,2): the five-path or the triangle-plus-edge
  · simp only [Prod.mk.injEq] at hprof
    obtain ⟨hquadClass, _, hdoubleClass, hsingleClass⟩ := hprof
    obtain ⟨relabelPerm, hdoor⟩ :=
      exists_map_family_eq_canonicalPath_or_triangle_of_profile hneOneTwo hneOneThree
        hneOneFour hneTwoThree hneTwoFour hneThreeFour hcardOne hcardTwo hcardThree
        hcardFourth hquadClass hdoubleClass hsingleClass
    rcases hdoor with hdoor | hdoor
    · exact Or.inl ⟨relabelPerm.symm, Or.inr (Or.inr (Or.inl
        (hrelabelOf relabelPerm canonicalFivePathFamily hdoor)))⟩
    · exact Or.inl ⟨relabelPerm.symm, Or.inr (Or.inr (Or.inr
        (hrelabelOf relabelPerm canonicalTriangleEdgeFamily hdoor)))⟩
  -- profile (1,1,1,3): the chair
  · simp only [Prod.mk.injEq] at hprof
    obtain ⟨hquadClass, htripleClass, hdoubleClass, _⟩ := hprof
    obtain ⟨relabelPerm, hdoor⟩ :=
      exists_map_family_eq_canonicalChair_of_profile hneOneTwo hneOneThree hneOneFour
        hneTwoThree hneTwoFour hneThreeFour hcardOne hcardTwo hcardThree hcardFourth
        hquadClass htripleClass hdoubleClass
    exact Or.inl ⟨relabelPerm.symm, Or.inr (Or.inl
      (hrelabelOf relabelPerm canonicalChairFamily hdoor))⟩
  -- profile (2,0,0,4): the edge pencil
  · simp only [Prod.mk.injEq] at hprof
    obtain ⟨hquadClass, _, _, _⟩ := hprof
    obtain ⟨edgeFirst, edgeSecond, hedgeNe, hfirstCount, hsecondCount⟩ :=
      exists_two_atoms_of_classCard_two hquadClass
    obtain ⟨relabelPerm, hdoor⟩ :=
      exists_map_family_eq_canonicalEdgePencil_of_two_quadruple_atoms hcardOne hcardTwo
        hcardThree hcardFourth hneOneTwo hneOneThree hneOneFour hneTwoThree hneTwoFour
        hneThreeFour hedgeNe hfirstCount hsecondCount
    exact Or.inl ⟨relabelPerm.symm, Or.inl
      (hrelabelOf relabelPerm canonicalEdgePencil hdoor)⟩

end Gtz

import Mathlib
import Gtz.Quantitative.PendantDoorReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

/-!
# The fifteen-family dispatch: every card-four crux hits a canonical

The census is wired end to end: a crux whose argmax family has four blocks
relabels to a crux whose argmax family IS one of the fifteen canonical
covering four-families.  The quadruple-door dispatch resolves the three
quadruple profiles; the four quadruple-free profiles route through their
door capstones with the same relabelling transport.  This is the complete
rung-4 classifier: the leaf-exit wave now has fifteen concrete targets.
-/

namespace Gtz

/-- **THE FIFTEEN-FAMILY DISPATCH.**  Every card-four crux relabels onto one
of the fifteen canonical covering four-families. -/
theorem SixThreeCrux.exists_relabel_family_canonical_of_card_four
    (crux : SixThreeCrux)
    (hcardFour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ∃ relabelPerm : Equiv.Perm (Fin 6),
      chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalEdgePencil
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalChairFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalFivePathFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalTriangleEdgeFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalThreeTripleFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalTetrahedronFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalDoubleDoubleFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalTridentFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalZigzagFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalTwinPairsFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalHookFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalNestedFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalDoublePathFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalPendantSplitFamily
        ∨ chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))
            = canonicalPendantForkFamily := by
  rcases crux.relabel_canonical_or_noQuadProfile_of_card_four hcardFour with
    ⟨relabelPerm, hdoor⟩ | ⟨firstBlock, secondBlock, thirdBlock, fourthBlock, hfamEq,
        hneOneTwo, hneOneThree, hneOneFour, hneTwoThree, hneTwoFour, hneThreeFour,
        hcardOne, hcardTwo, hcardThree, hcardFourth, hcover, hprofile⟩
  · refine ⟨relabelPerm, ?_⟩
    rcases hdoor with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · have hrelabelOf : ∀ innerPerm : Equiv.Perm (Fin 6),
        ∀ target : Finset (Finset (Fin 6)),
        ({firstBlock, secondBlock, thirdBlock, fourthBlock} :
            Finset (Finset (Fin 6))).image
            (fun block : Finset (Fin 6) => block.map innerPerm.toEmbedding) = target
          → chartArgmaxFamily (chartPointOfDesign
              ((crux.relabel innerPerm.symm).design)) = target := by
      intro innerPerm target hdoor
      have hfamRelabel := chartArgmaxFamily_relabelDesign crux.design innerPerm.symm
      rw [Equiv.symm_symm, hfamEq] at hfamRelabel
      exact hfamRelabel.trans hdoor
    rcases hprofile with hprof | hprof | hprof | hprof <;>
      simp only [Prod.mk.injEq] at hprof
    · obtain ⟨_, _, hdoubleClass, _⟩ := hprof
      obtain ⟨innerPerm, hdoor⟩ :=
        exists_map_family_eq_canonicalTetrahedron_or_doubleDouble_of_profile
          hneOneTwo hneOneThree hneOneFour hcardOne hcardTwo hcardThree hcardFourth
          hdoubleClass
      refine ⟨innerPerm.symm, ?_⟩
      rcases hdoor with h | h <;> have htransported := hrelabelOf innerPerm _ h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htransported)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htransported))))))
    · obtain ⟨hquadClass, htripleClass, _, hsingleClass⟩ := hprof
      obtain ⟨innerPerm, hdoor⟩ :=
        exists_map_family_eq_canonical_of_profile0141 hneOneTwo hneOneThree hneOneFour
          hneTwoThree hneTwoFour hneThreeFour hcardOne hcardTwo hcardThree hcardFourth
          hcover hquadClass htripleClass hsingleClass
      refine ⟨innerPerm.symm, ?_⟩
      rcases hdoor with h | h | h <;> have htransported := hrelabelOf innerPerm _ h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htransported))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htransported)))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (htransported))))))))))))))
    · obtain ⟨hquadClass, htripleClass, _, _⟩ := hprof
      obtain ⟨innerPerm, hdoor⟩ :=
        exists_map_family_eq_canonical_of_profile0222 hneOneTwo hneOneThree hneOneFour
          hneTwoThree hneTwoFour hneThreeFour hcardOne hcardTwo hcardThree hcardFourth
          hcover hquadClass htripleClass
      refine ⟨innerPerm.symm, ?_⟩
      rcases hdoor with h | h | h | h | h <;>
        have htransported := hrelabelOf innerPerm _ h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htransported)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htransported))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htransported)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htransported))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htransported)))))))))))
    · obtain ⟨hquadClass, htripleClass, hdoubleClass, _⟩ := hprof
      obtain ⟨innerPerm, hdoor⟩ :=
        exists_map_family_eq_canonicalThreeTriple_of_profile hneOneTwo hneOneThree
          hneOneFour hneTwoThree hneTwoFour hneThreeFour hcardOne hcardTwo hcardThree
          hcardFourth hquadClass htripleClass hdoubleClass
      refine ⟨innerPerm.symm, ?_⟩
      have htransported := hrelabelOf innerPerm _ hdoor
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htransported))))

end Gtz

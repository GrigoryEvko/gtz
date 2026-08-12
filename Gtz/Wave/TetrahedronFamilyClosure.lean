import Gtz.Quantitative.FifteenFamilyDispatch
import Gtz.Wave.CrossSupportedTightExit
import Gtz.Wave.FullRowTriangleKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The Tetrahedron family, listed. -/
theorem canonicalTetrahedronFamily_eq_literal :
    canonicalTetrahedronFamily
      = ({{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE TETRAHEDRON KILL.**  No crux selects this family. -/
theorem SixThreeCrux.false_of_family_canonicalTetrahedronFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalTetrahedronFamily) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 2} ∨ block = {0, 3, 4} ∨ block = {1, 3, 5} ∨ block = {2, 4, 5} := by
    have hmem := hblockMem
    rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  obtain ⟨pairFirst, pairSecond, hpairDistinct, hpairEq⟩ :=
    Finset.card_eq_two.mp hsupportTwo
  have hpairSubset : ({pairFirst, pairSecond} : Finset (Fin 6)) ⊆ block := by
    rw [← hpairEq]
    exact totalTightSupport_subset tightVec hblockCard
  obtain ⟨coefficient, hremainingCard, hcoefficientNonzero, hcombinationNonzero,
    hcancel⟩ :=
    exists_threeActiveEigenSquareRow_cancellation_of_support_pair tightVec hfour
      hblockMem hblockCard hpairDistinct hpairEq
      (haxes pairFirst (by rw [hpairEq]; exact Finset.mem_insert_self _ _))
  rcases hblockCases with rfl | rfl | rfl | rfl
  · -- selected {0, 1, 2}
    have heraseEq : canonicalTetrahedronFamily.erase {0, 1, 2}
        = ({{0, 3, 4}, {1, 3, 5}, {2, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 1}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 1} :=
        hpairEq.symm.trans hpairPin
      have hcov1 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
      by_cases hmemSplit2 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4}
      ·
        by_cases hmemSplit3 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5}
        ·
          have hcancelAt4 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt5 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt6 := hcancel 3 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt4 hcancelAt5 hcancelAt6
          have hcoeff7 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt4
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
          have hcoeff8 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt5
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff7)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit3))
          have hcoeff9 : coefficient {0, 3, 4} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt6
              (Or.inl hcoeff8)
              (Or.inl hcoeff7)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit2))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff9
          · exact hbadNe hcoeff8
          · exact hbadNe hcoeff7
        ·
          have hpin10 : totalTightSupport tightVec {1, 3, 5} = {1, 3} :=
            eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 5} (by decide)) hmemSplit3 (by decide)
          have hcov11 : (5 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpin10] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact hcoverAtom
          by_cases hmemSplit12 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4}
          ·
            have hcancelAt13 := hcancel 2 (by rw [hpairSetEq]; decide)
            have hcancelAt14 := hcancel 4 (by rw [hpairSetEq]; decide)
            have hcancelAt15 := hcancel 3 (by rw [hpairSetEq]; decide)
            rw [hfamily, heraseEq, Finset.sum_insert (by decide),
              Finset.sum_insert (by decide), Finset.sum_singleton]
              at hcancelAt13 hcancelAt14 hcancelAt15
            have hcoeff16 : coefficient {2, 4, 5} = 0 :=
              thirdCoeff_eq_zero_of_sum_three hcancelAt13
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
            have hcoeff17 : coefficient {0, 3, 4} = 0 :=
              firstCoeff_eq_zero_of_sum_three hcancelAt14
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (Or.inl hcoeff16)
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit12))
            have hcoeff18 : coefficient {1, 3, 5} = 0 :=
              secondCoeff_eq_zero_of_sum_three hcancelAt15
                (Or.inl hcoeff17)
                (Or.inl hcoeff16)
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin10]; decide)))
            obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
            rw [hfamily, heraseEq] at hbadMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
            rcases hbadMem with rfl | rfl | rfl
            · exact hbadNe hcoeff17
            · exact hbadNe hcoeff18
            · exact hbadNe hcoeff16
          ·
            have hpin19 : totalTightSupport tightVec {0, 3, 4} = {0, 3} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 3, 4} (by decide)) hmemSplit12 (by decide)
            have hcov20 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
              obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
              rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
              rcases hcoverMem with rfl | rfl | rfl | rfl
              · rw [hpairPin] at hcoverAtom
                exact absurd hcoverAtom (by decide)
              · rw [hpin19] at hcoverAtom
                exact absurd hcoverAtom (by decide)
              · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
              · exact hcoverAtom
            have hfullEq : totalTightSupport tightVec {2, 4, 5} = {2, 4, 5} := by
              refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
              intro atom hatom
              simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
              rcases hatom with rfl | rfl | rfl
              · exact hcov1
              · exact hcov20
              · exact hcov11
            have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                otherBlock ≠ ({2, 4, 5} : Finset (Fin 6)) →
                ∀ atomIndex ∈ ({2, 4, 5} : Finset (Fin 6)),
                  totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
              intro other hother hne atomIndex hatomIndex
              simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
              rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
              simp only [Finset.mem_insert, Finset.mem_singleton] at hother
              rcases hatomIndex with rfl | rfl | rfl <;>
                rcases hother with rfl | rfl | rfl | rfl
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact absurd rfl hne
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => by rw [hpin19] at hmem; exact absurd hmem (by decide))
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact absurd rfl hne
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => by rw [hpin10] at hmem; exact absurd hmem (by decide))
              · exact absurd rfl hne
            exact crux.false_of_fullRow_isolated_from_residual hfour hdata
              (by rw [hfamily]; decide) hfullEq hothersOff
      ·
        have hpin21 : totalTightSupport tightVec {0, 3, 4} = {0, 4} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 3, 4} (by decide)) hmemSplit2 (by decide)
        have hcov22 : (3 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpin21] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        have hcancelAt23 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt24 := hcancel 2 (by rw [hpairSetEq]; decide)
        have hcancelAt25 := hcancel 4 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt23 hcancelAt24 hcancelAt25
        have hcoeff26 : coefficient {1, 3, 5} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt23
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin21] at hmem; exact absurd hmem (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov22))
        have hcoeff27 : coefficient {2, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt24
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff26)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
        have hcoeff28 : coefficient {0, 3, 4} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt25
            (Or.inl hcoeff26)
            (Or.inl hcoeff27)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin21]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff28
        · exact hbadNe hcoeff26
        · exact hbadNe hcoeff27
    · -- pair {0, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 2} :=
        hpairEq.symm.trans hpairPin
      have hcov29 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit30 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4}
      ·
        by_cases hmemSplit31 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt32 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt33 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt34 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt32 hcancelAt33 hcancelAt34
          have hcoeff35 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt32
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov29))
          have hcoeff36 : coefficient {0, 3, 4} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt33
              (Or.inl hcoeff35)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit30))
          have hcoeff37 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt34
              (Or.inl hcoeff36)
              (Or.inl hcoeff35)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit31))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff36
          · exact hbadNe hcoeff35
          · exact hbadNe hcoeff37
        ·
          have hpin38 : totalTightSupport tightVec {2, 4, 5} = {2, 5} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit31 (by decide)
          have hcancelAt39 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt40 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt41 := hcancel 3 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt39 hcancelAt40 hcancelAt41
          have hcoeff42 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt39
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov29))
          have hcoeff43 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt40
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff42)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin38]; decide)))
          have hcoeff44 : coefficient {0, 3, 4} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt41
              (Or.inl hcoeff42)
              (Or.inl hcoeff43)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit30))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff44
          · exact hbadNe hcoeff42
          · exact hbadNe hcoeff43
      ·
        have hpin45 : totalTightSupport tightVec {0, 3, 4} = {0, 4} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 3, 4} (by decide)) hmemSplit30 (by decide)
        have hcov46 : (3 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpin45] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        by_cases hmemSplit47 : (5 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt48 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt49 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt50 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt48 hcancelAt49 hcancelAt50
          have hcoeff51 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt48
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov29))
          have hcoeff52 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt49
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff51)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit47))
          have hcoeff53 : coefficient {0, 3, 4} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt50
              (Or.inl hcoeff51)
              (Or.inl hcoeff52)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin45]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff53
          · exact hbadNe hcoeff51
          · exact hbadNe hcoeff52
        ·
          have hpin54 : totalTightSupport tightVec {2, 4, 5} = {2, 4} :=
            eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit47 (by decide)
          have hcov55 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · exact hcoverAtom
            · rw [hpin54] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hfullEq : totalTightSupport tightVec {1, 3, 5} = {1, 3, 5} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov29
            · exact hcov46
            · exact hcov55
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({1, 3, 5} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({1, 3, 5} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin45] at hmem; exact absurd hmem (by decide))
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin54] at hmem; exact absurd hmem (by decide))
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- pair {1, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 2} :=
        hpairEq.symm.trans hpairPin
      have hcov56 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit57 : (3 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5}
      ·
        by_cases hmemSplit58 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt59 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt60 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt61 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt59 hcancelAt60 hcancelAt61
          have hcoeff62 : coefficient {0, 3, 4} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt59
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov56))
          have hcoeff63 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt60
              (Or.inl hcoeff62)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit57))
          have hcoeff64 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt61
              (Or.inl hcoeff62)
              (Or.inl hcoeff63)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit58))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff62
          · exact hbadNe hcoeff63
          · exact hbadNe hcoeff64
        ·
          have hpin65 : totalTightSupport tightVec {2, 4, 5} = {2, 5} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit58 (by decide)
          have hcancelAt66 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt67 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt68 := hcancel 5 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt66 hcancelAt67 hcancelAt68
          have hcoeff69 : coefficient {0, 3, 4} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt66
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov56))
          have hcoeff70 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt67
              (Or.inl hcoeff69)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit57))
          have hcoeff71 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt68
              (Or.inl hcoeff69)
              (Or.inl hcoeff70)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin65]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff69
          · exact hbadNe hcoeff70
          · exact hbadNe hcoeff71
      ·
        have hpin72 : totalTightSupport tightVec {1, 3, 5} = {1, 5} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 5} (by decide)) hmemSplit57 (by decide)
        have hcov73 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · rw [hpin72] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        by_cases hmemSplit74 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt75 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt76 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt77 := hcancel 5 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt75 hcancelAt76 hcancelAt77
          have hcoeff78 : coefficient {0, 3, 4} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt75
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov56))
          have hcoeff79 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt76
              (Or.inl hcoeff78)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit74))
          have hcoeff80 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt77
              (Or.inl hcoeff78)
              (Or.inl hcoeff79)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin72]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff78
          · exact hbadNe hcoeff80
          · exact hbadNe hcoeff79
        ·
          have hpin81 : totalTightSupport tightVec {2, 4, 5} = {2, 5} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit74 (by decide)
          have hcov82 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact hcoverAtom
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpin81] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hfullEq : totalTightSupport tightVec {0, 3, 4} = {0, 3, 4} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov56
            · exact hcov73
            · exact hcov82
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 3, 4} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 3, 4} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin72] at hmem; exact absurd hmem (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin81] at hmem; exact absurd hmem (by decide))
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 3, 4}
    have heraseEq : canonicalTetrahedronFamily.erase {0, 3, 4}
        = ({{0, 1, 2}, {1, 3, 5}, {2, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov83 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
      by_cases hmemSplit84 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit85 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5}
        ·
          have hcancelAt86 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt87 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt88 := hcancel 1 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt86 hcancelAt87 hcancelAt88
          have hcoeff89 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt86
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov83))
          have hcoeff90 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt87
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff89)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit85))
          have hcoeff91 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt88
              (Or.inl hcoeff90)
              (Or.inl hcoeff89)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit84))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff91
          · exact hbadNe hcoeff90
          · exact hbadNe hcoeff89
        ·
          have hpin92 : totalTightSupport tightVec {1, 3, 5} = {1, 3} :=
            eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 5} (by decide)) hmemSplit85 (by decide)
          have hcov93 : (5 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpin92] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact hcoverAtom
          by_cases hmemSplit94 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
          ·
            have hcancelAt95 := hcancel 4 (by rw [hpairSetEq]; decide)
            have hcancelAt96 := hcancel 2 (by rw [hpairSetEq]; decide)
            have hcancelAt97 := hcancel 1 (by rw [hpairSetEq]; decide)
            rw [hfamily, heraseEq, Finset.sum_insert (by decide),
              Finset.sum_insert (by decide), Finset.sum_singleton]
              at hcancelAt95 hcancelAt96 hcancelAt97
            have hcoeff98 : coefficient {2, 4, 5} = 0 :=
              thirdCoeff_eq_zero_of_sum_three hcancelAt95
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov83))
            have hcoeff99 : coefficient {0, 1, 2} = 0 :=
              firstCoeff_eq_zero_of_sum_three hcancelAt96
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (Or.inl hcoeff98)
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit94))
            have hcoeff100 : coefficient {1, 3, 5} = 0 :=
              secondCoeff_eq_zero_of_sum_three hcancelAt97
                (Or.inl hcoeff99)
                (Or.inl hcoeff98)
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin92]; decide)))
            obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
            rw [hfamily, heraseEq] at hbadMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
            rcases hbadMem with rfl | rfl | rfl
            · exact hbadNe hcoeff99
            · exact hbadNe hcoeff100
            · exact hbadNe hcoeff98
          ·
            have hpin101 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit94 (by decide)
            have hcov102 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
              obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
              rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
              rcases hcoverMem with rfl | rfl | rfl | rfl
              · rw [hpin101] at hcoverAtom
                exact absurd hcoverAtom (by decide)
              · rw [hpairPin] at hcoverAtom
                exact absurd hcoverAtom (by decide)
              · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
              · exact hcoverAtom
            have hfullEq : totalTightSupport tightVec {2, 4, 5} = {2, 4, 5} := by
              refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
              intro atom hatom
              simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
              rcases hatom with rfl | rfl | rfl
              · exact hcov102
              · exact hcov83
              · exact hcov93
            have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                otherBlock ≠ ({2, 4, 5} : Finset (Fin 6)) →
                ∀ atomIndex ∈ ({2, 4, 5} : Finset (Fin 6)),
                  totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
              intro other hother hne atomIndex hatomIndex
              simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
              rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
              simp only [Finset.mem_insert, Finset.mem_singleton] at hother
              rcases hatomIndex with rfl | rfl | rfl <;>
                rcases hother with rfl | rfl | rfl | rfl
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => by rw [hpin101] at hmem; exact absurd hmem (by decide))
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact absurd rfl hne
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact absurd rfl hne
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => by rw [hpin92] at hmem; exact absurd hmem (by decide))
              · exact absurd rfl hne
            exact crux.false_of_fullRow_isolated_from_residual hfour hdata
              (by rw [hfamily]; decide) hfullEq hothersOff
      ·
        have hpin103 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit84 (by decide)
        have hcov104 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpin103] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        have hcancelAt105 := hcancel 1 (by rw [hpairSetEq]; decide)
        have hcancelAt106 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt107 := hcancel 2 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt105 hcancelAt106 hcancelAt107
        have hcoeff108 : coefficient {1, 3, 5} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt105
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin103] at hmem; exact absurd hmem (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov104))
        have hcoeff109 : coefficient {2, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt106
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff108)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov83))
        have hcoeff110 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt107
            (Or.inl hcoeff108)
            (Or.inl hcoeff109)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin103]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff110
        · exact hbadNe hcoeff108
        · exact hbadNe hcoeff109
    · -- pair {0, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov111 : (3 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit112 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit113 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt114 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt115 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt116 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt114 hcancelAt115 hcancelAt116
          have hcoeff117 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt114
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov111))
          have hcoeff118 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt115
              (Or.inl hcoeff117)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit112))
          have hcoeff119 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt116
              (Or.inl hcoeff118)
              (Or.inl hcoeff117)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit113))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff118
          · exact hbadNe hcoeff117
          · exact hbadNe hcoeff119
        ·
          have hpin120 : totalTightSupport tightVec {2, 4, 5} = {4, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit113 (by decide)
          have hcancelAt121 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt122 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt123 := hcancel 1 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt121 hcancelAt122 hcancelAt123
          have hcoeff124 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt121
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov111))
          have hcoeff125 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt122
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff124)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin120]; decide)))
          have hcoeff126 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt123
              (Or.inl hcoeff124)
              (Or.inl hcoeff125)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit112))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff126
          · exact hbadNe hcoeff124
          · exact hbadNe hcoeff125
      ·
        have hpin127 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit112 (by decide)
        have hcov128 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpin127] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        by_cases hmemSplit129 : (5 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt130 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt131 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt132 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt130 hcancelAt131 hcancelAt132
          have hcoeff133 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt130
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin127] at hmem; exact absurd hmem (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov128))
          have hcoeff134 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt131
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff133)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit129))
          have hcoeff135 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt132
              (Or.inl hcoeff133)
              (Or.inl hcoeff134)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin127]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff135
          · exact hbadNe hcoeff133
          · exact hbadNe hcoeff134
        ·
          have hpin136 : totalTightSupport tightVec {2, 4, 5} = {2, 4} :=
            eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit129 (by decide)
          have hcov137 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact hcoverAtom
            · rw [hpin136] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hfullEq : totalTightSupport tightVec {1, 3, 5} = {1, 3, 5} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov128
            · exact hcov111
            · exact hcov137
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({1, 3, 5} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({1, 3, 5} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin127] at hmem; exact absurd hmem (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin136] at hmem; exact absurd hmem (by decide))
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- pair {3, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {3, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov138 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit139 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5}
      ·
        by_cases hmemSplit140 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt141 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt142 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt143 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt141 hcancelAt142 hcancelAt143
          have hcoeff144 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt141
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov138))
          have hcoeff145 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt142
              (Or.inl hcoeff144)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit139))
          have hcoeff146 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt143
              (Or.inl hcoeff144)
              (Or.inl hcoeff145)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit140))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff144
          · exact hbadNe hcoeff145
          · exact hbadNe hcoeff146
        ·
          have hpin147 : totalTightSupport tightVec {2, 4, 5} = {4, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit140 (by decide)
          have hcancelAt148 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt149 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt150 := hcancel 5 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt148 hcancelAt149 hcancelAt150
          have hcoeff151 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt148
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov138))
          have hcoeff152 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt149
              (Or.inl hcoeff151)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit139))
          have hcoeff153 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt150
              (Or.inl hcoeff151)
              (Or.inl hcoeff152)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin147]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff151
          · exact hbadNe hcoeff152
          · exact hbadNe hcoeff153
      ·
        have hpin154 : totalTightSupport tightVec {1, 3, 5} = {3, 5} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 5} (by decide)) hmemSplit139 (by decide)
        have hcov155 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · exact hcoverAtom
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpin154] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        by_cases hmemSplit156 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt157 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt158 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt159 := hcancel 5 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt157 hcancelAt158 hcancelAt159
          have hcoeff160 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt157
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov138))
          have hcoeff161 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt158
              (Or.inl hcoeff160)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit156))
          have hcoeff162 : coefficient {1, 3, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt159
              (Or.inl hcoeff160)
              (Or.inl hcoeff161)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin154]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff160
          · exact hbadNe hcoeff162
          · exact hbadNe hcoeff161
        ·
          have hpin163 : totalTightSupport tightVec {2, 4, 5} = {4, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit156 (by decide)
          have hcov164 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact hcoverAtom
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpin163] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hfullEq : totalTightSupport tightVec {0, 1, 2} = {0, 1, 2} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov138
            · exact hcov155
            · exact hcov164
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 1, 2} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 1, 2} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · exact absurd rfl hne
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin154] at hmem; exact absurd hmem (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin163] at hmem; exact absurd hmem (by decide))
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {1, 3, 5}
    have heraseEq : canonicalTetrahedronFamily.erase {1, 3, 5}
        = ({{0, 1, 2}, {0, 3, 4}, {2, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {1, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov165 : (5 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
      by_cases hmemSplit166 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit167 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4}
        ·
          have hcancelAt168 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt169 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt170 := hcancel 0 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt168 hcancelAt169 hcancelAt170
          have hcoeff171 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt168
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov165))
          have hcoeff172 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt169
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff171)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit167))
          have hcoeff173 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt170
              (Or.inl hcoeff172)
              (Or.inl hcoeff171)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit166))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff173
          · exact hbadNe hcoeff172
          · exact hbadNe hcoeff171
        ·
          have hpin174 : totalTightSupport tightVec {0, 3, 4} = {0, 3} :=
            eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 3, 4} (by decide)) hmemSplit167 (by decide)
          have hcov175 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpin174] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact hcoverAtom
          by_cases hmemSplit176 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
          ·
            have hcancelAt177 := hcancel 4 (by rw [hpairSetEq]; decide)
            have hcancelAt178 := hcancel 2 (by rw [hpairSetEq]; decide)
            have hcancelAt179 := hcancel 0 (by rw [hpairSetEq]; decide)
            rw [hfamily, heraseEq, Finset.sum_insert (by decide),
              Finset.sum_insert (by decide), Finset.sum_singleton]
              at hcancelAt177 hcancelAt178 hcancelAt179
            have hcoeff180 : coefficient {2, 4, 5} = 0 :=
              thirdCoeff_eq_zero_of_sum_three hcancelAt177
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin174] at hmem; exact absurd hmem (by decide))))
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov175))
            have hcoeff181 : coefficient {0, 1, 2} = 0 :=
              firstCoeff_eq_zero_of_sum_three hcancelAt178
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (Or.inl hcoeff180)
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit176))
            have hcoeff182 : coefficient {0, 3, 4} = 0 :=
              secondCoeff_eq_zero_of_sum_three hcancelAt179
                (Or.inl hcoeff181)
                (Or.inl hcoeff180)
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin174]; decide)))
            obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
            rw [hfamily, heraseEq] at hbadMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
            rcases hbadMem with rfl | rfl | rfl
            · exact hbadNe hcoeff181
            · exact hbadNe hcoeff182
            · exact hbadNe hcoeff180
          ·
            have hpin183 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit176 (by decide)
            have hcov184 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
              obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
              rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
              rcases hcoverMem with rfl | rfl | rfl | rfl
              · rw [hpin183] at hcoverAtom
                exact absurd hcoverAtom (by decide)
              · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
              · rw [hpairPin] at hcoverAtom
                exact absurd hcoverAtom (by decide)
              · exact hcoverAtom
            have hfullEq : totalTightSupport tightVec {2, 4, 5} = {2, 4, 5} := by
              refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
              intro atom hatom
              simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
              rcases hatom with rfl | rfl | rfl
              · exact hcov184
              · exact hcov175
              · exact hcov165
            have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                otherBlock ≠ ({2, 4, 5} : Finset (Fin 6)) →
                ∀ atomIndex ∈ ({2, 4, 5} : Finset (Fin 6)),
                  totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
              intro other hother hne atomIndex hatomIndex
              simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
              rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
              simp only [Finset.mem_insert, Finset.mem_singleton] at hother
              rcases hatomIndex with rfl | rfl | rfl <;>
                rcases hother with rfl | rfl | rfl | rfl
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => by rw [hpin183] at hmem; exact absurd hmem (by decide))
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
              · exact absurd rfl hne
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => by rw [hpin174] at hmem; exact absurd hmem (by decide))
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
              · exact absurd rfl hne
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
              · exact absurd rfl hne
            exact crux.false_of_fullRow_isolated_from_residual hfour hdata
              (by rw [hfamily]; decide) hfullEq hothersOff
      ·
        have hpin185 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit166 (by decide)
        have hcov186 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpin185] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        have hcancelAt187 := hcancel 0 (by rw [hpairSetEq]; decide)
        have hcancelAt188 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt189 := hcancel 2 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt187 hcancelAt188 hcancelAt189
        have hcoeff190 : coefficient {0, 3, 4} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt187
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin185] at hmem; exact absurd hmem (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov186))
        have hcoeff191 : coefficient {2, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt188
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff190)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov165))
        have hcoeff192 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt189
            (Or.inl hcoeff190)
            (Or.inl hcoeff191)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin185]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff192
        · exact hbadNe hcoeff190
        · exact hbadNe hcoeff191
    · -- pair {1, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov193 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit194 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit195 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt196 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt197 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt198 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt196 hcancelAt197 hcancelAt198
          have hcoeff199 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt196
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov193))
          have hcoeff200 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt197
              (Or.inl hcoeff199)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit194))
          have hcoeff201 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt198
              (Or.inl hcoeff200)
              (Or.inl hcoeff199)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit195))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff200
          · exact hbadNe hcoeff199
          · exact hbadNe hcoeff201
        ·
          have hpin202 : totalTightSupport tightVec {2, 4, 5} = {4, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit195 (by decide)
          have hcancelAt203 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt204 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt205 := hcancel 0 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt203 hcancelAt204 hcancelAt205
          have hcoeff206 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt203
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov193))
          have hcoeff207 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt204
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff206)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin202]; decide)))
          have hcoeff208 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt205
              (Or.inl hcoeff206)
              (Or.inl hcoeff207)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit194))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff208
          · exact hbadNe hcoeff206
          · exact hbadNe hcoeff207
      ·
        have hpin209 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit194 (by decide)
        have hcov210 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpin209] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        by_cases hmemSplit211 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt212 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt213 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt214 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt212 hcancelAt213 hcancelAt214
          have hcoeff215 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt212
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin209] at hmem; exact absurd hmem (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov210))
          have hcoeff216 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt213
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff215)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit211))
          have hcoeff217 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt214
              (Or.inl hcoeff215)
              (Or.inl hcoeff216)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin209]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff217
          · exact hbadNe hcoeff215
          · exact hbadNe hcoeff216
        ·
          have hpin218 : totalTightSupport tightVec {2, 4, 5} = {2, 5} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit211 (by decide)
          have hcov219 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · exact hcoverAtom
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpin218] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hfullEq : totalTightSupport tightVec {0, 3, 4} = {0, 3, 4} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov210
            · exact hcov193
            · exact hcov219
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 3, 4} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 3, 4} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin209] at hmem; exact absurd hmem (by decide))
            · exact absurd rfl hne
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin218] at hmem; exact absurd hmem (by decide))
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- pair {3, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {3, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov220 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit221 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4}
      ·
        by_cases hmemSplit222 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt223 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt224 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt225 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt223 hcancelAt224 hcancelAt225
          have hcoeff226 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt223
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov220))
          have hcoeff227 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt224
              (Or.inl hcoeff226)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit221))
          have hcoeff228 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt225
              (Or.inl hcoeff226)
              (Or.inl hcoeff227)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit222))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff226
          · exact hbadNe hcoeff227
          · exact hbadNe hcoeff228
        ·
          have hpin229 : totalTightSupport tightVec {2, 4, 5} = {4, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit222 (by decide)
          have hcancelAt230 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt231 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt232 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt230 hcancelAt231 hcancelAt232
          have hcoeff233 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt230
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov220))
          have hcoeff234 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt231
              (Or.inl hcoeff233)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit221))
          have hcoeff235 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt232
              (Or.inl hcoeff233)
              (Or.inl hcoeff234)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin229]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff233
          · exact hbadNe hcoeff234
          · exact hbadNe hcoeff235
      ·
        have hpin236 : totalTightSupport tightVec {0, 3, 4} = {3, 4} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 3, 4} (by decide)) hmemSplit221 (by decide)
        have hcov237 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · exact hcoverAtom
          · rw [hpin236] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        by_cases hmemSplit238 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt239 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt240 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt241 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt239 hcancelAt240 hcancelAt241
          have hcoeff242 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt239
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin236] at hmem; exact absurd hmem (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov237))
          have hcoeff243 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt240
              (Or.inl hcoeff242)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit238))
          have hcoeff244 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt241
              (Or.inl hcoeff242)
              (Or.inl hcoeff243)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin236]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff242
          · exact hbadNe hcoeff244
          · exact hbadNe hcoeff243
        ·
          have hpin245 : totalTightSupport tightVec {2, 4, 5} = {4, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit238 (by decide)
          have hcov246 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact hcoverAtom
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpin245] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hfullEq : totalTightSupport tightVec {0, 1, 2} = {0, 1, 2} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov237
            · exact hcov220
            · exact hcov246
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 1, 2} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 1, 2} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin236] at hmem; exact absurd hmem (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin245] at hmem; exact absurd hmem (by decide))
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {2, 4, 5}
    have heraseEq : canonicalTetrahedronFamily.erase {2, 4, 5}
        = ({{0, 1, 2}, {0, 3, 4}, {1, 3, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {2, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {2, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov247 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit248 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit249 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4}
        ·
          have hcancelAt250 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt251 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt252 := hcancel 0 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt250 hcancelAt251 hcancelAt252
          have hcoeff253 : coefficient {1, 3, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt250
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov247))
          have hcoeff254 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt251
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff253)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit249))
          have hcoeff255 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt252
              (Or.inl hcoeff254)
              (Or.inl hcoeff253)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit248))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff255
          · exact hbadNe hcoeff254
          · exact hbadNe hcoeff253
        ·
          have hpin256 : totalTightSupport tightVec {0, 3, 4} = {0, 4} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 3, 4} (by decide)) hmemSplit249 (by decide)
          have hcov257 : (3 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpin256] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact hcoverAtom
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          by_cases hmemSplit258 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
          ·
            have hcancelAt259 := hcancel 3 (by rw [hpairSetEq]; decide)
            have hcancelAt260 := hcancel 1 (by rw [hpairSetEq]; decide)
            have hcancelAt261 := hcancel 0 (by rw [hpairSetEq]; decide)
            rw [hfamily, heraseEq, Finset.sum_insert (by decide),
              Finset.sum_insert (by decide), Finset.sum_singleton]
              at hcancelAt259 hcancelAt260 hcancelAt261
            have hcoeff262 : coefficient {1, 3, 5} = 0 :=
              thirdCoeff_eq_zero_of_sum_three hcancelAt259
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin256] at hmem; exact absurd hmem (by decide))))
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov257))
            have hcoeff263 : coefficient {0, 1, 2} = 0 :=
              firstCoeff_eq_zero_of_sum_three hcancelAt260
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (Or.inl hcoeff262)
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit258))
            have hcoeff264 : coefficient {0, 3, 4} = 0 :=
              secondCoeff_eq_zero_of_sum_three hcancelAt261
                (Or.inl hcoeff263)
                (Or.inl hcoeff262)
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin256]; decide)))
            obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
            rw [hfamily, heraseEq] at hbadMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
            rcases hbadMem with rfl | rfl | rfl
            · exact hbadNe hcoeff263
            · exact hbadNe hcoeff264
            · exact hbadNe hcoeff262
          ·
            have hpin265 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
              eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit258 (by decide)
            have hcov266 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5} := by
              obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
              rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
              rcases hcoverMem with rfl | rfl | rfl | rfl
              · rw [hpin265] at hcoverAtom
                exact absurd hcoverAtom (by decide)
              · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
              · exact hcoverAtom
              · rw [hpairPin] at hcoverAtom
                exact absurd hcoverAtom (by decide)
            have hfullEq : totalTightSupport tightVec {1, 3, 5} = {1, 3, 5} := by
              refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
              intro atom hatom
              simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
              rcases hatom with rfl | rfl | rfl
              · exact hcov266
              · exact hcov257
              · exact hcov247
            have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                otherBlock ≠ ({1, 3, 5} : Finset (Fin 6)) →
                ∀ atomIndex ∈ ({1, 3, 5} : Finset (Fin 6)),
                  totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
              intro other hother hne atomIndex hatomIndex
              simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
              rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
              simp only [Finset.mem_insert, Finset.mem_singleton] at hother
              rcases hatomIndex with rfl | rfl | rfl <;>
                rcases hother with rfl | rfl | rfl | rfl
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => by rw [hpin265] at hmem; exact absurd hmem (by decide))
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact absurd rfl hne
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => by rw [hpin256] at hmem; exact absurd hmem (by decide))
              · exact absurd rfl hne
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                  (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
              · exact absurd rfl hne
              · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                rw [hpairPin]
                decide
            exact crux.false_of_fullRow_isolated_from_residual hfour hdata
              (by rw [hfamily]; decide) hfullEq hothersOff
      ·
        have hpin267 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit248 (by decide)
        have hcov268 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpin267] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
        have hcancelAt269 := hcancel 0 (by rw [hpairSetEq]; decide)
        have hcancelAt270 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt271 := hcancel 1 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt269 hcancelAt270 hcancelAt271
        have hcoeff272 : coefficient {0, 3, 4} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt269
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin267] at hmem; exact absurd hmem (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov268))
        have hcoeff273 : coefficient {1, 3, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt270
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff272)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov247))
        have hcoeff274 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt271
            (Or.inl hcoeff272)
            (Or.inl hcoeff273)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin267]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff274
        · exact hbadNe hcoeff272
        · exact hbadNe hcoeff273
    · -- pair {2, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {2, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov275 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit276 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit277 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5}
        ·
          have hcancelAt278 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt279 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt280 := hcancel 1 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt278 hcancelAt279 hcancelAt280
          have hcoeff281 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt278
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov275))
          have hcoeff282 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt279
              (Or.inl hcoeff281)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit276))
          have hcoeff283 : coefficient {1, 3, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt280
              (Or.inl hcoeff282)
              (Or.inl hcoeff281)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit277))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff282
          · exact hbadNe hcoeff281
          · exact hbadNe hcoeff283
        ·
          have hpin284 : totalTightSupport tightVec {1, 3, 5} = {3, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 5} (by decide)) hmemSplit277 (by decide)
          have hcancelAt285 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt286 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt287 := hcancel 0 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt285 hcancelAt286 hcancelAt287
          have hcoeff288 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt285
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov275))
          have hcoeff289 : coefficient {1, 3, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt286
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff288)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin284]; decide)))
          have hcoeff290 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt287
              (Or.inl hcoeff288)
              (Or.inl hcoeff289)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit276))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff290
          · exact hbadNe hcoeff288
          · exact hbadNe hcoeff289
      ·
        have hpin291 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit276 (by decide)
        have hcov292 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpin291] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
        by_cases hmemSplit293 : (3 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5}
        ·
          have hcancelAt294 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt295 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt296 := hcancel 1 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt294 hcancelAt295 hcancelAt296
          have hcoeff297 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt294
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin291] at hmem; exact absurd hmem (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov292))
          have hcoeff298 : coefficient {1, 3, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt295
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff297)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit293))
          have hcoeff299 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt296
              (Or.inl hcoeff297)
              (Or.inl hcoeff298)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin291]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff299
          · exact hbadNe hcoeff297
          · exact hbadNe hcoeff298
        ·
          have hpin300 : totalTightSupport tightVec {1, 3, 5} = {1, 5} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 5} (by decide)) hmemSplit293 (by decide)
          have hcov301 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · exact hcoverAtom
            · rw [hpin300] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hfullEq : totalTightSupport tightVec {0, 3, 4} = {0, 3, 4} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov292
            · exact hcov301
            · exact hcov275
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 3, 4} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 3, 4} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin291] at hmem; exact absurd hmem (by decide))
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin300] at hmem; exact absurd hmem (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- pair {4, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {4, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov302 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
        rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit303 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4}
      ·
        by_cases hmemSplit304 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5}
        ·
          have hcancelAt305 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt306 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt307 := hcancel 1 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt305 hcancelAt306 hcancelAt307
          have hcoeff308 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt305
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov302))
          have hcoeff309 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt306
              (Or.inl hcoeff308)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit303))
          have hcoeff310 : coefficient {1, 3, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt307
              (Or.inl hcoeff308)
              (Or.inl hcoeff309)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit304))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff308
          · exact hbadNe hcoeff309
          · exact hbadNe hcoeff310
        ·
          have hpin311 : totalTightSupport tightVec {1, 3, 5} = {3, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 5} (by decide)) hmemSplit304 (by decide)
          have hcancelAt312 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt313 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt314 := hcancel 3 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt312 hcancelAt313 hcancelAt314
          have hcoeff315 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt312
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov302))
          have hcoeff316 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt313
              (Or.inl hcoeff315)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit303))
          have hcoeff317 : coefficient {1, 3, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt314
              (Or.inl hcoeff315)
              (Or.inl hcoeff316)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin311]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff315
          · exact hbadNe hcoeff316
          · exact hbadNe hcoeff317
      ·
        have hpin318 : totalTightSupport tightVec {0, 3, 4} = {3, 4} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 3, 4} (by decide)) hmemSplit303 (by decide)
        have hcov319 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · exact hcoverAtom
          · rw [hpin318] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
        by_cases hmemSplit320 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 5}
        ·
          have hcancelAt321 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt322 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt323 := hcancel 3 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt321 hcancelAt322 hcancelAt323
          have hcoeff324 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt321
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin318] at hmem; exact absurd hmem (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov319))
          have hcoeff325 : coefficient {1, 3, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt322
              (Or.inl hcoeff324)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit320))
          have hcoeff326 : coefficient {0, 3, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt323
              (Or.inl hcoeff324)
              (Or.inl hcoeff325)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin318]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff324
          · exact hbadNe hcoeff326
          · exact hbadNe hcoeff325
        ·
          have hpin327 : totalTightSupport tightVec {1, 3, 5} = {3, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 5} (by decide)) hmemSplit320 (by decide)
          have hcov328 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact hcoverAtom
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpin327] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hfullEq : totalTightSupport tightVec {0, 1, 2} = {0, 1, 2} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov319
            · exact hcov328
            · exact hcov302
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 1, 2} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 1, 2} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalTetrahedronFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin318] at hmem; exact absurd hmem (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin327] at hmem; exact absurd hmem (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)

end Gtz

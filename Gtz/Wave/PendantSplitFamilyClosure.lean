import Gtz.Quantitative.FifteenFamilyDispatch
import Gtz.Wave.CrossSupportedTightExit
import Gtz.Wave.FullRowTriangleKill
import Gtz.Wave.FourFamilyTypeEightExit
import Gtz.Wave.WeightedColumnSupportBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The indexFortySix family, listed. -/
theorem indexFortySixFamily_eq_literal :
    indexFortySixFamily
      = ({{0, 1, 2}, {0, 1, 3}, {0, 4, 5}, {2, 4, 5}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE INDEXFORTYSIX KILL.**  No crux selects this family. -/
theorem SixThreeCrux.false_of_family_indexFortySixFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = indexFortySixFamily) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 2} ∨ block = {0, 1, 3} ∨ block = {0, 4, 5} ∨ block = {2, 4, 5} := by
    have hmem := hblockMem
    rw [hfamily, indexFortySixFamily_eq_literal] at hmem
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
    have heraseEq : indexFortySixFamily.erase {0, 1, 2}
        = ({{0, 1, 3}, {0, 4, 5}, {2, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 1}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 1} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 1, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {0, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 2} :=
        hpairEq.symm.trans hpairPin
      have hcov1 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      have hcov2 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit3 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5}
      ·
        by_cases hmemSplit4 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5}
        ·
          by_cases hmemSplit5 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5}
          ·
            by_cases hmemSplit6 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
            ·
              by_cases hmemSplit7 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
              ·
                by_cases hmemSplit8 : (5 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
                ·
                  by_cases hmemSplit9 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
                  ·
                    have hfullPin10 : totalTightSupport tightVec {0, 1, 3} = {0, 1, 3} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit9
                      · exact hcov1
                      · exact hcov2
                    have hfullPin11 : totalTightSupport tightVec {0, 4, 5} = {0, 4, 5} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit3
                      · exact hmemSplit4
                      · exact hmemSplit5
                    have hfullPin12 : totalTightSupport tightVec {2, 4, 5} = {2, 4, 5} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit6
                      · exact hmemSplit7
                      · exact hmemSplit8
                    refine crux.false_of_indexFortySix_totalSupports hfamily hdata ?_ ?_ ?_ ?_
                    · show totalTightSupport tightVec {0, 1, 2} = _
                      rw [hpairPin]
                    · show totalTightSupport tightVec {0, 1, 3} = _
                      rw [hfullPin10]
                    · show totalTightSupport tightVec {0, 4, 5} = _
                      rw [hfullPin11]
                    · show totalTightSupport tightVec {2, 4, 5} = _
                      rw [hfullPin12]
                  ·
                    have hpin13 : totalTightSupport tightVec {0, 1, 3} = {1, 3} :=
                      eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                      (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit9 (by decide)
                    have hisoA14 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({0, 1, 3} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 1 = 0 := by
                      intro other hother hne
                      rw [hfamily, indexFortySixFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact absurd rfl hne
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                    have hisoB15 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({0, 1, 3} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 3 = 0 := by
                      intro other hother hne
                      rw [hfamily, indexFortySixFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact absurd rfl hne
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                    exact crux.false_of_isolated_pair_row (by decide) hdata
                      (by rw [hfamily]; decide)
                      hpin13
                      hisoA14 hisoB15
                ·
                  have hpin16 : totalTightSupport tightVec {2, 4, 5} = {2, 4} :=
                    eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                    (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit8 (by decide)
                  have hcancelAt17 := hcancel 1 (by rw [hpairSetEq]; decide)
                  have hcancelAt18 := hcancel 5 (by rw [hpairSetEq]; decide)
                  have hcancelAt19 := hcancel 4 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton]
                    at hcancelAt17 hcancelAt18 hcancelAt19
                  have hcoeff20 : coefficient {0, 1, 3} = 0 :=
                    firstCoeff_eq_zero_of_sum_three hcancelAt17
                      (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                      (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                      (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
                  have hcoeff21 : coefficient {0, 4, 5} = 0 :=
                    secondCoeff_eq_zero_of_sum_three hcancelAt18
                      (Or.inl hcoeff20)
                      (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin16] at hmem; exact absurd hmem (by decide))))
                      (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit5))
                  have hcoeff22 : coefficient {2, 4, 5} = 0 :=
                    thirdCoeff_eq_zero_of_sum_three hcancelAt19
                      (Or.inl hcoeff20)
                      (Or.inl hcoeff21)
                      (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit7))
                  obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
                  rw [hfamily, heraseEq] at hbadMem
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
                  rcases hbadMem with rfl | rfl | rfl
                  · exact hbadNe hcoeff20
                  · exact hbadNe hcoeff21
                  · exact hbadNe hcoeff22
              ·
                have hpin23 : totalTightSupport tightVec {2, 4, 5} = {2, 5} :=
                  eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit7 (by decide)
                have hcancelAt24 := hcancel 1 (by rw [hpairSetEq]; decide)
                have hcancelAt25 := hcancel 4 (by rw [hpairSetEq]; decide)
                have hcancelAt26 := hcancel 5 (by rw [hpairSetEq]; decide)
                rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                  Finset.sum_insert (by decide), Finset.sum_singleton]
                  at hcancelAt24 hcancelAt25 hcancelAt26
                have hcoeff27 : coefficient {0, 1, 3} = 0 :=
                  firstCoeff_eq_zero_of_sum_three hcancelAt24
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
                have hcoeff28 : coefficient {0, 4, 5} = 0 :=
                  secondCoeff_eq_zero_of_sum_three hcancelAt25
                    (Or.inl hcoeff27)
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin23] at hmem; exact absurd hmem (by decide))))
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit4))
                have hcoeff29 : coefficient {2, 4, 5} = 0 :=
                  thirdCoeff_eq_zero_of_sum_three hcancelAt26
                    (Or.inl hcoeff27)
                    (Or.inl hcoeff28)
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin23]; decide)))
                obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
                rw [hfamily, heraseEq] at hbadMem
                simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
                rcases hbadMem with rfl | rfl | rfl
                · exact hbadNe hcoeff27
                · exact hbadNe hcoeff28
                · exact hbadNe hcoeff29
            ·
              have hpin30 : totalTightSupport tightVec {2, 4, 5} = {4, 5} :=
                eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit6 (by decide)
              exact crux.false_of_totalTightSupport_subset_neighbor
                (hostBlock := {2, 4, 5})
                (neighborBlock := {0, 4, 5})
                hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                (by decide) hdata (by rw [hpin30]; decide)
          ·
            have hpin31 : totalTightSupport tightVec {0, 4, 5} = {0, 4} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 4, 5} (by decide)) hmemSplit5 (by decide)
            have hcov32 : (5 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
              obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
              rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
              rcases hcoverMem with rfl | rfl | rfl | rfl
              · rw [hpairPin] at hcoverAtom
                exact absurd hcoverAtom (by decide)
              · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
              · rw [hpin31] at hcoverAtom
                exact absurd hcoverAtom (by decide)
              · exact hcoverAtom
            have hcancelAt33 := hcancel 1 (by rw [hpairSetEq]; decide)
            have hcancelAt34 := hcancel 5 (by rw [hpairSetEq]; decide)
            have hcancelAt35 := hcancel 4 (by rw [hpairSetEq]; decide)
            rw [hfamily, heraseEq, Finset.sum_insert (by decide),
              Finset.sum_insert (by decide), Finset.sum_singleton]
              at hcancelAt33 hcancelAt34 hcancelAt35
            have hcoeff36 : coefficient {0, 1, 3} = 0 :=
              firstCoeff_eq_zero_of_sum_three hcancelAt33
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
            have hcoeff37 : coefficient {2, 4, 5} = 0 :=
              thirdCoeff_eq_zero_of_sum_three hcancelAt34
                (Or.inl hcoeff36)
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin31] at hmem; exact absurd hmem (by decide))))
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov32))
            have hcoeff38 : coefficient {0, 4, 5} = 0 :=
              secondCoeff_eq_zero_of_sum_three hcancelAt35
                (Or.inl hcoeff36)
                (Or.inl hcoeff37)
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit4))
            obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
            rw [hfamily, heraseEq] at hbadMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
            rcases hbadMem with rfl | rfl | rfl
            · exact hbadNe hcoeff36
            · exact hbadNe hcoeff38
            · exact hbadNe hcoeff37
        ·
          have hpin39 : totalTightSupport tightVec {0, 4, 5} = {0, 5} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 4, 5} (by decide)) hmemSplit4 (by decide)
          have hcov40 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
            rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpin39] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact hcoverAtom
          have hcancelAt41 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt42 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt43 := hcancel 5 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt41 hcancelAt42 hcancelAt43
          have hcoeff44 : coefficient {0, 1, 3} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt41
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
          have hcoeff45 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt42
              (Or.inl hcoeff44)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin39] at hmem; exact absurd hmem (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov40))
          have hcoeff46 : coefficient {0, 4, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt43
              (Or.inl hcoeff44)
              (Or.inl hcoeff45)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin39]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff44
          · exact hbadNe hcoeff46
          · exact hbadNe hcoeff45
      ·
        have hpin47 : totalTightSupport tightVec {0, 4, 5} = {4, 5} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 4, 5} (by decide)) hmemSplit3 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 4, 5})
          (neighborBlock := {2, 4, 5})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin47]; decide)
    · -- pair {1, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 2} :=
        hpairEq.symm.trans hpairPin
      have hcov48 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit49 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5}
      ·
        by_cases hmemSplit50 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt51 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt52 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt53 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt51 hcancelAt52 hcancelAt53
          have hcoeff54 : coefficient {0, 1, 3} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt51
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov48))
          have hcoeff55 : coefficient {0, 4, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt52
              (Or.inl hcoeff54)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit49))
          have hcoeff56 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt53
              (Or.inl hcoeff54)
              (Or.inl hcoeff55)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit50))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff54
          · exact hbadNe hcoeff55
          · exact hbadNe hcoeff56
        ·
          have hpin57 : totalTightSupport tightVec {2, 4, 5} = {2, 5} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit50 (by decide)
          have hcancelAt58 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt59 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt60 := hcancel 5 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt58 hcancelAt59 hcancelAt60
          have hcoeff61 : coefficient {0, 1, 3} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt58
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov48))
          have hcoeff62 : coefficient {0, 4, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt59
              (Or.inl hcoeff61)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit49))
          have hcoeff63 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt60
              (Or.inl hcoeff61)
              (Or.inl hcoeff62)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin57]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff61
          · exact hbadNe hcoeff62
          · exact hbadNe hcoeff63
      ·
        have hpin64 : totalTightSupport tightVec {0, 4, 5} = {4, 5} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 4, 5} (by decide)) hmemSplit49 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 4, 5})
          (neighborBlock := {2, 4, 5})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin64]; decide)
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 1, 3}
    have heraseEq : indexFortySixFamily.erase {0, 1, 3}
        = ({{0, 1, 2}, {0, 4, 5}, {2, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 1}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 1} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 3})
        (neighborBlock := {0, 1, 2})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {0, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov65 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit66 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5}
      ·
        by_cases hmemSplit67 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
        ·
          have hcancelAt68 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt69 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt70 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt68 hcancelAt69 hcancelAt70
          have hcoeff71 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt68
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov65))
          have hcoeff72 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt69
              (Or.inl hcoeff71)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit67))
          have hcoeff73 : coefficient {0, 4, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt70
              (Or.inl hcoeff71)
              (Or.inl hcoeff72)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit66))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff71
          · exact hbadNe hcoeff73
          · exact hbadNe hcoeff72
        ·
          have hpin74 : totalTightSupport tightVec {2, 4, 5} = {4, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit67 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {2, 4, 5})
            (neighborBlock := {0, 4, 5})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin74]; decide)
      ·
        have hpin75 : totalTightSupport tightVec {0, 4, 5} = {0, 5} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 4, 5} (by decide)) hmemSplit66 (by decide)
        have hcov76 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
          rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpin75] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
        have hcancelAt77 := hcancel 1 (by rw [hpairSetEq]; decide)
        have hcancelAt78 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt79 := hcancel 5 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt77 hcancelAt78 hcancelAt79
        have hcoeff80 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt77
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov65))
        have hcoeff81 : coefficient {2, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt78
            (Or.inl hcoeff80)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin75] at hmem; exact absurd hmem (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov76))
        have hcoeff82 : coefficient {0, 4, 5} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt79
            (Or.inl hcoeff80)
            (Or.inl hcoeff81)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin75]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff80
        · exact hbadNe hcoeff82
        · exact hbadNe hcoeff81
    · -- pair {1, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 3} :=
        hpairEq.symm.trans hpairPin
      by_cases hmemSplit83 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit84 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5}
        ·
          by_cases hmemSplit85 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5}
          ·
            by_cases hmemSplit86 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
            ·
              by_cases hmemSplit87 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
              ·
                by_cases hmemSplit88 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
                ·
                  have hcancelAt89 := hcancel 0 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt89
                  have hrowZero90 : totalEigenSquareRow tightVec {2, 4, 5} 0 = 0 :=
                    totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                  have hdeadTerm91 : coefficient {2, 4, 5} * totalEigenSquareRow tightVec {2, 4, 5} 0 = 0 := by
                    rw [hrowZero90]; ring
                  have hmeet92 : coefficient {0, 1, 2} * totalEigenSquareRow tightVec {0, 1, 2} 0
                      + coefficient {0, 4, 5} * totalEigenSquareRow tightVec {0, 4, 5} 0 = 0 := by
                    linarith [hcancelAt89, hdeadTerm91]
                  have hcancelAt93 := hcancel 4 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt93
                  have hrowZero94 : totalEigenSquareRow tightVec {0, 1, 2} 4 = 0 :=
                    totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                  have hdeadTerm95 : coefficient {0, 1, 2} * totalEigenSquareRow tightVec {0, 1, 2} 4 = 0 := by
                    rw [hrowZero94]; ring
                  have hmeet96 : coefficient {0, 4, 5} * totalEigenSquareRow tightVec {0, 4, 5} 4
                      + coefficient {2, 4, 5} * totalEigenSquareRow tightVec {2, 4, 5} 4 = 0 := by
                    linarith [hcancelAt93, hdeadTerm95]
                  have hcancelAt97 := hcancel 2 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt97
                  have hrowZero98 : totalEigenSquareRow tightVec {0, 4, 5} 2 = 0 :=
                    totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                  have hdeadTerm99 : coefficient {0, 4, 5} * totalEigenSquareRow tightVec {0, 4, 5} 2 = 0 := by
                    rw [hrowZero98]; ring
                  have hmeet100 : coefficient {0, 1, 2} * totalEigenSquareRow tightVec {0, 1, 2} 2
                      + coefficient {2, 4, 5} * totalEigenSquareRow tightVec {2, 4, 5} 2 = 0 := by
                    linarith [hcancelAt97, hdeadTerm99]
                  refine false_of_oppositeSign_triangle hmeet92 hmeet96 hmeet100
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit88)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit84)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit85)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit87)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit83)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit86) ?_
                  obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
                  rw [hfamily, heraseEq] at hbadMem
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
                  rcases hbadMem with rfl | rfl | rfl
                  · exact Or.inl hbadNe
                  · exact Or.inr (Or.inl hbadNe)
                  · exact Or.inr (Or.inr hbadNe)
                ·
                  have hpin101 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
                    eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                    (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit88 (by decide)
                  have hcancelAt102 := hcancel 0 (by rw [hpairSetEq]; decide)
                  have hcancelAt103 := hcancel 4 (by rw [hpairSetEq]; decide)
                  have hcancelAt104 := hcancel 2 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton]
                    at hcancelAt102 hcancelAt103 hcancelAt104
                  have hcoeff105 : coefficient {0, 4, 5} = 0 :=
                    secondCoeff_eq_zero_of_sum_three hcancelAt102
                      (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin101] at hmem; exact absurd hmem (by decide))))
                      (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                      (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit84))
                  have hcoeff106 : coefficient {2, 4, 5} = 0 :=
                    thirdCoeff_eq_zero_of_sum_three hcancelAt103
                      (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                      (Or.inl hcoeff105)
                      (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit87))
                  have hcoeff107 : coefficient {0, 1, 2} = 0 :=
                    firstCoeff_eq_zero_of_sum_three hcancelAt104
                      (Or.inl hcoeff105)
                      (Or.inl hcoeff106)
                      (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit83))
                  obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
                  rw [hfamily, heraseEq] at hbadMem
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
                  rcases hbadMem with rfl | rfl | rfl
                  · exact hbadNe hcoeff107
                  · exact hbadNe hcoeff105
                  · exact hbadNe hcoeff106
              ·
                have hpin108 : totalTightSupport tightVec {2, 4, 5} = {2, 5} :=
                  eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit87 (by decide)
                have hcancelAt109 := hcancel 4 (by rw [hpairSetEq]; decide)
                have hcancelAt110 := hcancel 5 (by rw [hpairSetEq]; decide)
                have hcancelAt111 := hcancel 2 (by rw [hpairSetEq]; decide)
                rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                  Finset.sum_insert (by decide), Finset.sum_singleton]
                  at hcancelAt109 hcancelAt110 hcancelAt111
                have hcoeff112 : coefficient {0, 4, 5} = 0 :=
                  secondCoeff_eq_zero_of_sum_three hcancelAt109
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin108] at hmem; exact absurd hmem (by decide))))
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit85))
                have hcoeff113 : coefficient {2, 4, 5} = 0 :=
                  thirdCoeff_eq_zero_of_sum_three hcancelAt110
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                    (Or.inl hcoeff112)
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin108]; decide)))
                have hcoeff114 : coefficient {0, 1, 2} = 0 :=
                  firstCoeff_eq_zero_of_sum_three hcancelAt111
                    (Or.inl hcoeff112)
                    (Or.inl hcoeff113)
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit83))
                obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
                rw [hfamily, heraseEq] at hbadMem
                simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
                rcases hbadMem with rfl | rfl | rfl
                · exact hbadNe hcoeff114
                · exact hbadNe hcoeff112
                · exact hbadNe hcoeff113
            ·
              have hpin115 : totalTightSupport tightVec {2, 4, 5} = {4, 5} :=
                eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit86 (by decide)
              exact crux.false_of_totalTightSupport_subset_neighbor
                (hostBlock := {2, 4, 5})
                (neighborBlock := {0, 4, 5})
                hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                (by decide) hdata (by rw [hpin115]; decide)
          ·
            have hpin116 : totalTightSupport tightVec {0, 4, 5} = {0, 5} :=
              eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 4, 5} (by decide)) hmemSplit85 (by decide)
            have hcov117 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
              obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
              rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
              rcases hcoverMem with rfl | rfl | rfl | rfl
              · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
              · rw [hpairPin] at hcoverAtom
                exact absurd hcoverAtom (by decide)
              · rw [hpin116] at hcoverAtom
                exact absurd hcoverAtom (by decide)
              · exact hcoverAtom
            have hcancelAt118 := hcancel 4 (by rw [hpairSetEq]; decide)
            have hcancelAt119 := hcancel 2 (by rw [hpairSetEq]; decide)
            have hcancelAt120 := hcancel 0 (by rw [hpairSetEq]; decide)
            rw [hfamily, heraseEq, Finset.sum_insert (by decide),
              Finset.sum_insert (by decide), Finset.sum_singleton]
              at hcancelAt118 hcancelAt119 hcancelAt120
            have hcoeff121 : coefficient {2, 4, 5} = 0 :=
              thirdCoeff_eq_zero_of_sum_three hcancelAt118
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin116] at hmem; exact absurd hmem (by decide))))
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov117))
            have hcoeff122 : coefficient {0, 1, 2} = 0 :=
              firstCoeff_eq_zero_of_sum_three hcancelAt119
                (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                (Or.inl hcoeff121)
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit83))
            have hcoeff123 : coefficient {0, 4, 5} = 0 :=
              secondCoeff_eq_zero_of_sum_three hcancelAt120
                (Or.inl hcoeff122)
                (Or.inl hcoeff121)
                (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit84))
            obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
            rw [hfamily, heraseEq] at hbadMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
            rcases hbadMem with rfl | rfl | rfl
            · exact hbadNe hcoeff122
            · exact hbadNe hcoeff123
            · exact hbadNe hcoeff121
        ·
          have hpin124 : totalTightSupport tightVec {0, 4, 5} = {4, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 4, 5} (by decide)) hmemSplit84 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 4, 5})
            (neighborBlock := {2, 4, 5})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin124]; decide)
      ·
        have hpin125 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
          eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit83 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 1, 2})
          (neighborBlock := {0, 1, 3})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin125]; decide)
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 4, 5}
    have heraseEq : indexFortySixFamily.erase {0, 4, 5}
        = ({{0, 1, 2}, {0, 1, 3}, {2, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov126 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      have hcov127 : (5 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
      by_cases hmemSplit128 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        have hcancelAt129 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt130 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt131 := hcancel 1 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt129 hcancelAt130 hcancelAt131
        have hcoeff132 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt129
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov126))
        have hcoeff133 : coefficient {2, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt130
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff132)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov127))
        have hcoeff134 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt131
            (Or.inl hcoeff132)
            (Or.inl hcoeff133)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit128))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff134
        · exact hbadNe hcoeff132
        · exact hbadNe hcoeff133
      ·
        have hpin135 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit128 (by decide)
        have hcancelAt136 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt137 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt138 := hcancel 2 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt136 hcancelAt137 hcancelAt138
        have hcoeff139 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt136
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov126))
        have hcoeff140 : coefficient {2, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt137
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff139)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov127))
        have hcoeff141 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt138
            (Or.inl hcoeff139)
            (Or.inl hcoeff140)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin135]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff141
        · exact hbadNe hcoeff139
        · exact hbadNe hcoeff140
    · -- pair {0, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov142 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      have hcov143 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
      by_cases hmemSplit144 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        have hcancelAt145 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt146 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt147 := hcancel 1 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt145 hcancelAt146 hcancelAt147
        have hcoeff148 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt145
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov142))
        have hcoeff149 : coefficient {2, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt146
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff148)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov143))
        have hcoeff150 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt147
            (Or.inl hcoeff148)
            (Or.inl hcoeff149)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit144))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff150
        · exact hbadNe hcoeff148
        · exact hbadNe hcoeff149
      ·
        have hpin151 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit144 (by decide)
        have hcancelAt152 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt153 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt154 := hcancel 2 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt152 hcancelAt153 hcancelAt154
        have hcoeff155 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt152
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov142))
        have hcoeff156 : coefficient {2, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt153
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff155)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov143))
        have hcoeff157 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt154
            (Or.inl hcoeff155)
            (Or.inl hcoeff156)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin151]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff157
        · exact hbadNe hcoeff155
        · exact hbadNe hcoeff156
    · -- pair {4, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {4, 5} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 4, 5})
        (neighborBlock := {2, 4, 5})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {2, 4, 5}
    have heraseEq : indexFortySixFamily.erase {2, 4, 5}
        = ({{0, 1, 2}, {0, 1, 3}, {0, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {2, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {2, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov158 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      have hcov159 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit160 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        have hcancelAt161 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt162 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt163 := hcancel 0 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt161 hcancelAt162 hcancelAt163
        have hcoeff164 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt161
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov158))
        have hcoeff165 : coefficient {0, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt162
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff164)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov159))
        have hcoeff166 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt163
            (Or.inl hcoeff164)
            (Or.inl hcoeff165)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit160))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff166
        · exact hbadNe hcoeff164
        · exact hbadNe hcoeff165
      ·
        have hpin167 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit160 (by decide)
        have hcancelAt168 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt169 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt170 := hcancel 1 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt168 hcancelAt169 hcancelAt170
        have hcoeff171 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt168
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov158))
        have hcoeff172 : coefficient {0, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt169
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff171)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov159))
        have hcoeff173 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt170
            (Or.inl hcoeff171)
            (Or.inl hcoeff172)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin167]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff173
        · exact hbadNe hcoeff171
        · exact hbadNe hcoeff172
    · -- pair {2, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {2, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov174 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      have hcov175 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, indexFortySixFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit176 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        have hcancelAt177 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt178 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt179 := hcancel 0 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt177 hcancelAt178 hcancelAt179
        have hcoeff180 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt177
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov174))
        have hcoeff181 : coefficient {0, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt178
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff180)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov175))
        have hcoeff182 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt179
            (Or.inl hcoeff180)
            (Or.inl hcoeff181)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit176))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff182
        · exact hbadNe hcoeff180
        · exact hbadNe hcoeff181
      ·
        have hpin183 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit176 (by decide)
        have hcancelAt184 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt185 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt186 := hcancel 1 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt184 hcancelAt185 hcancelAt186
        have hcoeff187 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt184
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov174))
        have hcoeff188 : coefficient {0, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt185
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff187)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov175))
        have hcoeff189 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt186
            (Or.inl hcoeff187)
            (Or.inl hcoeff188)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin183]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff189
        · exact hbadNe hcoeff187
        · exact hbadNe hcoeff188
    · -- pair {4, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {4, 5} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {2, 4, 5})
        (neighborBlock := {0, 4, 5})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)

end Gtz

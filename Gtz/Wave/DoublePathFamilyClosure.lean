import Gtz.Quantitative.FifteenFamilyDispatch
import Gtz.Wave.CrossSupportedTightExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The DoublePath family, listed. -/
theorem canonicalDoublePathFamily_eq_literal :
    canonicalDoublePathFamily
      = ({{0, 1, 2}, {0, 2, 3}, {0, 3, 4}, {1, 4, 5}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE DOUBLEPATH KILL.**  No crux selects this family. -/
theorem SixThreeCrux.false_of_family_canonicalDoublePathFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalDoublePathFamily) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 2} ∨ block = {0, 2, 3} ∨ block = {0, 3, 4} ∨ block = {1, 4, 5} := by
    have hmem := hblockMem
    rw [hfamily, canonicalDoublePathFamily_eq_literal] at hmem
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
    have heraseEq : canonicalDoublePathFamily.erase {0, 1, 2}
        = ({{0, 2, 3}, {0, 3, 4}, {1, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov1 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalDoublePathFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
    by_cases hmemSplit2 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
    ·
      by_cases hmemSplit3 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4}
      ·
        have hcancelAt4 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt5 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt6 := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt4 hcancelAt5 hcancelAt6
        have hcoeff7 : coefficient {1, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt4
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
        have hcoeff8 : coefficient {0, 3, 4} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt5
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff7)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit3))
        have hcoeff9 : coefficient {0, 2, 3} = 0 :=
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
        have hpin10 : totalTightSupport tightVec {0, 3, 4} = {0, 3} :=
          eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 3, 4} (by decide)) hmemSplit3 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 3, 4})
          (neighborBlock := {0, 2, 3})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin10]; decide)
    ·
      have hpin11 : totalTightSupport tightVec {0, 2, 3} = {0, 2} :=
        eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit2 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 2, 3})
        (neighborBlock := {0, 1, 2})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin11]; decide)
  · -- selected {0, 2, 3}
    have heraseEq : canonicalDoublePathFamily.erase {0, 2, 3}
        = ({{0, 1, 2}, {0, 3, 4}, {1, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov12 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalDoublePathFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
    by_cases hmemSplit13 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
    ·
      by_cases hmemSplit14 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4}
      ·
        have hcancelAt15 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt16 := hcancel 1 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt17 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt15 hcancelAt16 hcancelAt17
        have hcoeff18 : coefficient {1, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt15
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov12))
        have hcoeff19 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt16
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff18)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit13))
        have hcoeff20 : coefficient {0, 3, 4} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt17
            (Or.inl hcoeff19)
            (Or.inl hcoeff18)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit14))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff19
        · exact hbadNe hcoeff20
        · exact hbadNe hcoeff18
      ·
        have hpin21 : totalTightSupport tightVec {0, 3, 4} = {0, 3} :=
          eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 3, 4} (by decide)) hmemSplit14 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 3, 4})
          (neighborBlock := {0, 2, 3})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin21]; decide)
    ·
      have hpin22 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
        eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit13 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 2, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin22]; decide)
  · -- selected {0, 3, 4}
    have heraseEq : canonicalDoublePathFamily.erase {0, 3, 4}
        = ({{0, 1, 2}, {0, 2, 3}, {1, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov23 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalDoublePathFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact hcoverAtom
    by_cases hmemSplit24 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
    ·
      by_cases hmemSplit25 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
      ·
        have hcancelAt26 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt27 := hcancel 1 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt28 := hcancel 2 (fun hmem => absurd (hpairSubset hmem) (by decide))
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt26 hcancelAt27 hcancelAt28
        have hcoeff29 : coefficient {1, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt26
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov23))
        have hcoeff30 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt27
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff29)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit24))
        have hcoeff31 : coefficient {0, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt28
            (Or.inl hcoeff30)
            (Or.inl hcoeff29)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit25))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff30
        · exact hbadNe hcoeff31
        · exact hbadNe hcoeff29
      ·
        have hpin32 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit25 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 2, 3})
          (neighborBlock := {0, 3, 4})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin32]; decide)
    ·
      have hpin33 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
        eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit24 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 2, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin33]; decide)
  · -- selected {1, 4, 5}
    have heraseEq : canonicalDoublePathFamily.erase {1, 4, 5}
        = ({{0, 1, 2}, {0, 2, 3}, {0, 3, 4}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {1, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 4} :=
        hpairEq.symm.trans hpairPin
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalDoublePathFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairPin] at hcoverAtom
        exact absurd hcoverAtom (by decide)
    · -- pair {1, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov34 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalDoublePathFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit35 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit36 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
        ·
          have hcancelAt37 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt38 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt39 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt37 hcancelAt38 hcancelAt39
          have hcoeff40 : coefficient {0, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt37
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov34))
          have hcoeff41 : coefficient {0, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt38
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff40)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit36))
          have hcoeff42 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt39
              (Or.inl hcoeff41)
              (Or.inl hcoeff40)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit35))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff42
          · exact hbadNe hcoeff41
          · exact hbadNe hcoeff40
        ·
          have hpin43 : totalTightSupport tightVec {0, 2, 3} = {0, 2} :=
            eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit36 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 2, 3})
            (neighborBlock := {0, 1, 2})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin43]; decide)
      ·
        have hpin44 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
          eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit35 (by decide)
        have hcov45 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
          rw [hfamily, canonicalDoublePathFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpin44] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
        have hcancelAt46 := hcancel 2 (by rw [hpairSetEq]; decide)
        have hcancelAt47 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt48 := hcancel 0 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt46 hcancelAt47 hcancelAt48
        have hcoeff49 : coefficient {0, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt46
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin44] at hmem; exact absurd hmem (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov45))
        have hcoeff50 : coefficient {0, 3, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt47
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff49)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov34))
        have hcoeff51 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt48
            (Or.inl hcoeff49)
            (Or.inl hcoeff50)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin44]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff51
        · exact hbadNe hcoeff49
        · exact hbadNe hcoeff50
    · -- pair {4, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {4, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov52 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
        rw [hfamily, canonicalDoublePathFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit53 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
      ·
        by_cases hmemSplit54 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 4}
        ·
          have hcancelAt55 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt56 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt57 := hcancel 0 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt55 hcancelAt56 hcancelAt57
          have hcoeff58 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt55
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov52))
          have hcoeff59 : coefficient {0, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt56
              (Or.inl hcoeff58)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit53))
          have hcoeff60 : coefficient {0, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt57
              (Or.inl hcoeff58)
              (Or.inl hcoeff59)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit54))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff58
          · exact hbadNe hcoeff59
          · exact hbadNe hcoeff60
        ·
          have hpin61 : totalTightSupport tightVec {0, 3, 4} = {3, 4} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 3, 4} (by decide)) hmemSplit54 (by decide)
          have hcancelAt62 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt63 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt64 := hcancel 3 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt62 hcancelAt63 hcancelAt64
          have hcoeff65 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt62
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov52))
          have hcoeff66 : coefficient {0, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt63
              (Or.inl hcoeff65)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit53))
          have hcoeff67 : coefficient {0, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt64
              (Or.inl hcoeff65)
              (Or.inl hcoeff66)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin61]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff65
          · exact hbadNe hcoeff66
          · exact hbadNe hcoeff67
      ·
        have hpin68 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit53 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 2, 3})
          (neighborBlock := {0, 3, 4})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin68]; decide)
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)

end Gtz

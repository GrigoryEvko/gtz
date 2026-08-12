import Gtz.Quantitative.FifteenFamilyDispatch
import Gtz.Wave.CrossSupportedTightExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The Zigzag family, listed. -/
theorem canonicalZigzagFamily_eq_literal :
    canonicalZigzagFamily
      = ({{0, 1, 2}, {0, 1, 3}, {1, 2, 4}, {0, 3, 5}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE ZIGZAG KILL.**  No crux selects this family. -/
theorem SixThreeCrux.false_of_family_canonicalZigzagFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalZigzagFamily) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 2} ∨ block = {0, 1, 3} ∨ block = {1, 2, 4} ∨ block = {0, 3, 5} := by
    have hmem := hblockMem
    rw [hfamily, canonicalZigzagFamily_eq_literal] at hmem
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
    have heraseEq : canonicalZigzagFamily.erase {0, 1, 2}
        = ({{0, 1, 3}, {1, 2, 4}, {0, 3, 5}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov1 : (4 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 4} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, canonicalZigzagFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
    have hcov2 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalZigzagFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
    by_cases hmemSplit3 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
    ·
      have hcancelAt4 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt5 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt6 := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
      rw [hfamily, heraseEq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
        at hcancelAt4 hcancelAt5 hcancelAt6
      have hcoeff7 : coefficient {1, 2, 4} = 0 :=
        secondCoeff_eq_zero_of_sum_three hcancelAt4
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
      have hcoeff8 : coefficient {0, 3, 5} = 0 :=
        thirdCoeff_eq_zero_of_sum_three hcancelAt5
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inl hcoeff7)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov2))
      have hcoeff9 : coefficient {0, 1, 3} = 0 :=
        firstCoeff_eq_zero_of_sum_three hcancelAt6
          (Or.inl hcoeff7)
          (Or.inl hcoeff8)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit3))
      obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
      rw [hfamily, heraseEq] at hbadMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
      rcases hbadMem with rfl | rfl | rfl
      · exact hbadNe hcoeff9
      · exact hbadNe hcoeff7
      · exact hbadNe hcoeff8
    ·
      have hpin10 : totalTightSupport tightVec {0, 1, 3} = {0, 1} :=
        eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit3 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 3})
        (neighborBlock := {0, 1, 2})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin10]; decide)
  · -- selected {0, 1, 3}
    have heraseEq : canonicalZigzagFamily.erase {0, 1, 3}
        = ({{0, 1, 2}, {1, 2, 4}, {0, 3, 5}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov11 : (4 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 4} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, canonicalZigzagFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
    have hcov12 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalZigzagFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
    by_cases hmemSplit13 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
    ·
      have hcancelAt14 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt15 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt16 := hcancel 2 (fun hmem => absurd (hpairSubset hmem) (by decide))
      rw [hfamily, heraseEq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
        at hcancelAt14 hcancelAt15 hcancelAt16
      have hcoeff17 : coefficient {1, 2, 4} = 0 :=
        secondCoeff_eq_zero_of_sum_three hcancelAt14
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov11))
      have hcoeff18 : coefficient {0, 3, 5} = 0 :=
        thirdCoeff_eq_zero_of_sum_three hcancelAt15
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inl hcoeff17)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov12))
      have hcoeff19 : coefficient {0, 1, 2} = 0 :=
        firstCoeff_eq_zero_of_sum_three hcancelAt16
          (Or.inl hcoeff17)
          (Or.inl hcoeff18)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit13))
      obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
      rw [hfamily, heraseEq] at hbadMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
      rcases hbadMem with rfl | rfl | rfl
      · exact hbadNe hcoeff19
      · exact hbadNe hcoeff17
      · exact hbadNe hcoeff18
    ·
      have hpin20 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
        eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit13 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 1, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin20]; decide)
  · -- selected {1, 2, 4}
    have heraseEq : canonicalZigzagFamily.erase {1, 2, 4}
        = ({{0, 1, 2}, {0, 1, 3}, {0, 3, 5}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov21 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 3, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalZigzagFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact hcoverAtom
    by_cases hmemSplit22 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
    ·
      by_cases hmemSplit23 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
      ·
        have hcancelAt24 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt25 := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt26 := hcancel 0 (fun hmem => absurd (hpairSubset hmem) (by decide))
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt24 hcancelAt25 hcancelAt26
        have hcoeff27 : coefficient {0, 3, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt24
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov21))
        have hcoeff28 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt25
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff27)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit23))
        have hcoeff29 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt26
            (Or.inl hcoeff28)
            (Or.inl hcoeff27)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit22))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff29
        · exact hbadNe hcoeff28
        · exact hbadNe hcoeff27
      ·
        have hpin30 : totalTightSupport tightVec {0, 1, 3} = {0, 1} :=
          eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit23 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 1, 3})
          (neighborBlock := {0, 1, 2})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin30]; decide)
    ·
      have hpin31 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
        eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit22 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {1, 2, 4})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin31]; decide)
  · -- selected {0, 3, 5}
    have heraseEq : canonicalZigzagFamily.erase {0, 3, 5}
        = ({{0, 1, 2}, {0, 1, 3}, {1, 2, 4}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov32 : (4 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 4} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, canonicalZigzagFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
    by_cases hmemSplit33 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
    ·
      by_cases hmemSplit34 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
      ·
        have hcancelAt35 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt36 := hcancel 2 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt37 := hcancel 1 (fun hmem => absurd (hpairSubset hmem) (by decide))
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt35 hcancelAt36 hcancelAt37
        have hcoeff38 : coefficient {1, 2, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt35
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov32))
        have hcoeff39 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt36
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff38)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit33))
        have hcoeff40 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt37
            (Or.inl hcoeff39)
            (Or.inl hcoeff38)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit34))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff39
        · exact hbadNe hcoeff40
        · exact hbadNe hcoeff38
      ·
        have hpin41 : totalTightSupport tightVec {0, 1, 3} = {0, 3} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit34 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 1, 3})
          (neighborBlock := {0, 3, 5})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin41]; decide)
    ·
      have hpin42 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
        eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit33 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 1, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin42]; decide)

end Gtz

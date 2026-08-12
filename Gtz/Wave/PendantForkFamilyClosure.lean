import Gtz.Quantitative.FifteenFamilyDispatch
import Gtz.Wave.CrossSupportedTightExit
import Gtz.Wave.FullRowTriangleKill
import Gtz.Wave.FourFamilyTypeEightExit
import Gtz.Wave.WeightedColumnSupportBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The PendantFork family, listed. -/
theorem canonicalPendantForkFamily_eq_literal :
    canonicalPendantForkFamily
      = ({{0, 1, 5}, {0, 2, 3}, {0, 2, 4}, {1, 3, 4}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE PENDANTFORK KILL.**  No crux selects this family. -/
theorem SixThreeCrux.false_of_family_canonicalPendantForkFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalPendantForkFamily) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 5} ∨ block = {0, 2, 3} ∨ block = {0, 2, 4} ∨ block = {1, 3, 4} := by
    have hmem := hblockMem
    rw [hfamily, canonicalPendantForkFamily_eq_literal] at hmem
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
  · -- selected {0, 1, 5}
    have heraseEq : canonicalPendantForkFamily.erase {0, 1, 5}
        = ({{0, 2, 3}, {0, 2, 4}, {1, 3, 4}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 1}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 1} :=
        hpairEq.symm.trans hpairPin
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairPin] at hcoverAtom
        exact absurd hcoverAtom (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
    · -- pair {0, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov1 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 4} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
      by_cases hmemSplit2 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
      ·
        by_cases hmemSplit3 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4}
        ·
          have hcancelAt4 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt5 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt6 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt4 hcancelAt5 hcancelAt6
          have hcoeff7 : coefficient {1, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt4
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
          have hcoeff8 : coefficient {0, 2, 4} = 0 :=
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
          have hpin10 : totalTightSupport tightVec {0, 2, 4} = {0, 2} :=
            eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 4} (by decide)) hmemSplit3 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 2, 4})
            (neighborBlock := {0, 2, 3})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin10]; decide)
      ·
        have hpin11 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit2 (by decide)
        have hcov12 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
          rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpin11] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        have hcancelAt13 := hcancel 2 (by rw [hpairSetEq]; decide)
        have hcancelAt14 := hcancel 1 (by rw [hpairSetEq]; decide)
        have hcancelAt15 := hcancel 3 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt13 hcancelAt14 hcancelAt15
        have hcoeff16 : coefficient {0, 2, 4} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt13
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin11] at hmem; exact absurd hmem (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov12))
        have hcoeff17 : coefficient {1, 3, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt14
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff16)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
        have hcoeff18 : coefficient {0, 2, 3} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt15
            (Or.inl hcoeff16)
            (Or.inl hcoeff17)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin11]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff18
        · exact hbadNe hcoeff16
        · exact hbadNe hcoeff17
    · -- pair {1, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 5} :=
        hpairEq.symm.trans hpairPin
      by_cases hmemSplit19 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
      ·
        by_cases hmemSplit20 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
        ·
          by_cases hmemSplit21 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4}
          ·
            by_cases hmemSplit22 : (4 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 4}
            ·
              by_cases hmemSplit23 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4}
              ·
                by_cases hmemSplit24 : (3 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 4}
                ·
                  have hcancelAt25 := hcancel 0 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt25
                  have hrowZero26 : totalEigenSquareRow tightVec {1, 3, 4} 0 = 0 :=
                    totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                  have hdeadTerm27 : coefficient {1, 3, 4} * totalEigenSquareRow tightVec {1, 3, 4} 0 = 0 := by
                    rw [hrowZero26]; ring
                  have hmeet28 : coefficient {0, 2, 3} * totalEigenSquareRow tightVec {0, 2, 3} 0
                      + coefficient {0, 2, 4} * totalEigenSquareRow tightVec {0, 2, 4} 0 = 0 := by
                    linarith [hcancelAt25, hdeadTerm27]
                  have hcancelAt29 := hcancel 4 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt29
                  have hrowZero30 : totalEigenSquareRow tightVec {0, 2, 3} 4 = 0 :=
                    totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                  have hdeadTerm31 : coefficient {0, 2, 3} * totalEigenSquareRow tightVec {0, 2, 3} 4 = 0 := by
                    rw [hrowZero30]; ring
                  have hmeet32 : coefficient {0, 2, 4} * totalEigenSquareRow tightVec {0, 2, 4} 4
                      + coefficient {1, 3, 4} * totalEigenSquareRow tightVec {1, 3, 4} 4 = 0 := by
                    linarith [hcancelAt29, hdeadTerm31]
                  have hcancelAt33 := hcancel 3 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt33
                  have hrowZero34 : totalEigenSquareRow tightVec {0, 2, 4} 3 = 0 :=
                    totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                  have hdeadTerm35 : coefficient {0, 2, 4} * totalEigenSquareRow tightVec {0, 2, 4} 3 = 0 := by
                    rw [hrowZero34]; ring
                  have hmeet36 : coefficient {0, 2, 3} * totalEigenSquareRow tightVec {0, 2, 3} 3
                      + coefficient {1, 3, 4} * totalEigenSquareRow tightVec {1, 3, 4} 3 = 0 := by
                    linarith [hcancelAt33, hdeadTerm35]
                  refine false_of_oppositeSign_triangle hmeet28 hmeet32 hmeet36
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit19)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit23)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit21)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit22)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit20)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit24) ?_
                  obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
                  rw [hfamily, heraseEq] at hbadMem
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
                  rcases hbadMem with rfl | rfl | rfl
                  · exact Or.inl hbadNe
                  · exact Or.inr (Or.inl hbadNe)
                  · exact Or.inr (Or.inr hbadNe)
                ·
                  have hpin37 : totalTightSupport tightVec {1, 3, 4} = {1, 4} :=
                    eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                    (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 4} (by decide)) hmemSplit24 (by decide)
                  have hcancelAt38 := hcancel 3 (by rw [hpairSetEq]; decide)
                  have hcancelAt39 := hcancel 0 (by rw [hpairSetEq]; decide)
                  have hcancelAt40 := hcancel 4 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton]
                    at hcancelAt38 hcancelAt39 hcancelAt40
                  have hcoeff41 : coefficient {0, 2, 3} = 0 :=
                    firstCoeff_eq_zero_of_sum_three hcancelAt38
                      (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                      (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin37] at hmem; exact absurd hmem (by decide))))
                      (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit20))
                  have hcoeff42 : coefficient {0, 2, 4} = 0 :=
                    secondCoeff_eq_zero_of_sum_three hcancelAt39
                      (Or.inl hcoeff41)
                      (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                      (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit23))
                  have hcoeff43 : coefficient {1, 3, 4} = 0 :=
                    thirdCoeff_eq_zero_of_sum_three hcancelAt40
                      (Or.inl hcoeff41)
                      (Or.inl hcoeff42)
                      (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit22))
                  obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
                  rw [hfamily, heraseEq] at hbadMem
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
                  rcases hbadMem with rfl | rfl | rfl
                  · exact hbadNe hcoeff41
                  · exact hbadNe hcoeff42
                  · exact hbadNe hcoeff43
              ·
                have hpin44 : totalTightSupport tightVec {0, 2, 4} = {2, 4} :=
                  eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 4} (by decide)) hmemSplit23 (by decide)
                have hcancelAt45 := hcancel 0 (by rw [hpairSetEq]; decide)
                have hcancelAt46 := hcancel 2 (by rw [hpairSetEq]; decide)
                have hcancelAt47 := hcancel 4 (by rw [hpairSetEq]; decide)
                rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                  Finset.sum_insert (by decide), Finset.sum_singleton]
                  at hcancelAt45 hcancelAt46 hcancelAt47
                have hcoeff48 : coefficient {0, 2, 3} = 0 :=
                  firstCoeff_eq_zero_of_sum_three hcancelAt45
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin44] at hmem; exact absurd hmem (by decide))))
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit19))
                have hcoeff49 : coefficient {0, 2, 4} = 0 :=
                  secondCoeff_eq_zero_of_sum_three hcancelAt46
                    (Or.inl hcoeff48)
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin44]; decide)))
                have hcoeff50 : coefficient {1, 3, 4} = 0 :=
                  thirdCoeff_eq_zero_of_sum_three hcancelAt47
                    (Or.inl hcoeff48)
                    (Or.inl hcoeff49)
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit22))
                obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
                rw [hfamily, heraseEq] at hbadMem
                simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
                rcases hbadMem with rfl | rfl | rfl
                · exact hbadNe hcoeff48
                · exact hbadNe hcoeff49
                · exact hbadNe hcoeff50
            ·
              have hpin51 : totalTightSupport tightVec {1, 3, 4} = {1, 3} :=
                eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 4} (by decide)) hmemSplit22 (by decide)
              have hcancelAt52 := hcancel 4 (by rw [hpairSetEq]; decide)
              have hcancelAt53 := hcancel 0 (by rw [hpairSetEq]; decide)
              have hcancelAt54 := hcancel 3 (by rw [hpairSetEq]; decide)
              rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                Finset.sum_insert (by decide), Finset.sum_singleton]
                at hcancelAt52 hcancelAt53 hcancelAt54
              have hcoeff55 : coefficient {0, 2, 4} = 0 :=
                secondCoeff_eq_zero_of_sum_three hcancelAt52
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin51] at hmem; exact absurd hmem (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit21))
              have hcoeff56 : coefficient {0, 2, 3} = 0 :=
                firstCoeff_eq_zero_of_sum_three hcancelAt53
                  (Or.inl hcoeff55)
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit19))
              have hcoeff57 : coefficient {1, 3, 4} = 0 :=
                thirdCoeff_eq_zero_of_sum_three hcancelAt54
                  (Or.inl hcoeff56)
                  (Or.inl hcoeff55)
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin51]; decide)))
              obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
              rw [hfamily, heraseEq] at hbadMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
              rcases hbadMem with rfl | rfl | rfl
              · exact hbadNe hcoeff56
              · exact hbadNe hcoeff55
              · exact hbadNe hcoeff57
          ·
            have hpin58 : totalTightSupport tightVec {0, 2, 4} = {0, 2} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 4} (by decide)) hmemSplit21 (by decide)
            exact crux.false_of_totalTightSupport_subset_neighbor
              (hostBlock := {0, 2, 4})
              (neighborBlock := {0, 2, 3})
              hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
              (by decide) hdata (by rw [hpin58]; decide)
        ·
          have hpin59 : totalTightSupport tightVec {0, 2, 3} = {0, 2} :=
            eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit20 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 2, 3})
            (neighborBlock := {0, 2, 4})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin59]; decide)
      ·
        have hpin60 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit19 (by decide)
        have hcov61 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpin60] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        by_cases hmemSplit62 : (3 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 4}
        ·
          have hcancelAt63 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt64 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt65 := hcancel 3 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt63 hcancelAt64 hcancelAt65
          have hcoeff66 : coefficient {0, 2, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt63
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin60] at hmem; exact absurd hmem (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov61))
          have hcoeff67 : coefficient {0, 2, 3} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt64
              (Or.inl hcoeff66)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin60]; decide)))
          have hcoeff68 : coefficient {1, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt65
              (Or.inl hcoeff67)
              (Or.inl hcoeff66)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit62))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff67
          · exact hbadNe hcoeff66
          · exact hbadNe hcoeff68
        ·
          have hpin69 : totalTightSupport tightVec {1, 3, 4} = {1, 4} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 4} (by decide)) hmemSplit62 (by decide)
          have hcancelAt70 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt71 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt72 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt70 hcancelAt71 hcancelAt72
          have hcoeff73 : coefficient {0, 2, 3} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt70
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin69] at hmem; exact absurd hmem (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin60]; decide)))
          have hcoeff74 : coefficient {0, 2, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt71
              (Or.inl hcoeff73)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov61))
          have hcoeff75 : coefficient {1, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt72
              (Or.inl hcoeff73)
              (Or.inl hcoeff74)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin69]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff73
          · exact hbadNe hcoeff74
          · exact hbadNe hcoeff75
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 2, 3}
    have heraseEq : canonicalPendantForkFamily.erase {0, 2, 3}
        = ({{0, 1, 5}, {0, 2, 4}, {1, 3, 4}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 2} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 2, 3})
        (neighborBlock := {0, 2, 4})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {0, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov76 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      have hcov77 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit78 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 4}
      ·
        have hcancelAt79 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt80 := hcancel 2 (by rw [hpairSetEq]; decide)
        have hcancelAt81 := hcancel 1 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt79 hcancelAt80 hcancelAt81
        have hcoeff82 : coefficient {0, 1, 5} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt79
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov77))
        have hcoeff83 : coefficient {0, 2, 4} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt80
            (Or.inl hcoeff82)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov76))
        have hcoeff84 : coefficient {1, 3, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt81
            (Or.inl hcoeff82)
            (Or.inl hcoeff83)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit78))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff82
        · exact hbadNe hcoeff83
        · exact hbadNe hcoeff84
      ·
        have hpin85 : totalTightSupport tightVec {1, 3, 4} = {3, 4} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 4} (by decide)) hmemSplit78 (by decide)
        have hcancelAt86 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt87 := hcancel 2 (by rw [hpairSetEq]; decide)
        have hcancelAt88 := hcancel 4 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt86 hcancelAt87 hcancelAt88
        have hcoeff89 : coefficient {0, 1, 5} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt86
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov77))
        have hcoeff90 : coefficient {0, 2, 4} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt87
            (Or.inl hcoeff89)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov76))
        have hcoeff91 : coefficient {1, 3, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt88
            (Or.inl hcoeff89)
            (Or.inl hcoeff90)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin85]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff89
        · exact hbadNe hcoeff90
        · exact hbadNe hcoeff91
    · -- pair {2, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {2, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov92 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit93 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4}
      ·
        by_cases hmemSplit94 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 4}
        ·
          have hcancelAt95 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt96 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt97 := hcancel 1 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt95 hcancelAt96 hcancelAt97
          have hcoeff98 : coefficient {0, 1, 5} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt95
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov92))
          have hcoeff99 : coefficient {0, 2, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt96
              (Or.inl hcoeff98)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit93))
          have hcoeff100 : coefficient {1, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt97
              (Or.inl hcoeff98)
              (Or.inl hcoeff99)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit94))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff98
          · exact hbadNe hcoeff99
          · exact hbadNe hcoeff100
        ·
          have hpin101 : totalTightSupport tightVec {1, 3, 4} = {3, 4} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 4} (by decide)) hmemSplit94 (by decide)
          have hcancelAt102 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt103 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt104 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt102 hcancelAt103 hcancelAt104
          have hcoeff105 : coefficient {0, 1, 5} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt102
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov92))
          have hcoeff106 : coefficient {0, 2, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt103
              (Or.inl hcoeff105)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit93))
          have hcoeff107 : coefficient {1, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt104
              (Or.inl hcoeff105)
              (Or.inl hcoeff106)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin101]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff105
          · exact hbadNe hcoeff106
          · exact hbadNe hcoeff107
      ·
        have hpin108 : totalTightSupport tightVec {0, 2, 4} = {2, 4} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 4} (by decide)) hmemSplit93 (by decide)
        have hcov109 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · exact hcoverAtom
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpin108] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        by_cases hmemSplit110 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 4}
        ·
          have hcancelAt111 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt112 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt113 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt111 hcancelAt112 hcancelAt113
          have hcoeff114 : coefficient {0, 1, 5} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt111
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin108] at hmem; exact absurd hmem (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov109))
          have hcoeff115 : coefficient {1, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt112
              (Or.inl hcoeff114)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit110))
          have hcoeff116 : coefficient {0, 2, 4} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt113
              (Or.inl hcoeff114)
              (Or.inl hcoeff115)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin108]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff114
          · exact hbadNe hcoeff116
          · exact hbadNe hcoeff115
        ·
          have hpin117 : totalTightSupport tightVec {1, 3, 4} = {3, 4} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 4} (by decide)) hmemSplit110 (by decide)
          have hcov118 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
            rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact hcoverAtom
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpin117] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hfullEq : totalTightSupport tightVec {0, 1, 5} = {0, 1, 5} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov109
            · exact hcov118
            · exact hcov92
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 1, 5} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 1, 5} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalPendantForkFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · exact absurd rfl hne
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin108] at hmem; exact absurd hmem (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin117] at hmem; exact absurd hmem (by decide))
            · exact absurd rfl hne
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 2, 4}
    have heraseEq : canonicalPendantForkFamily.erase {0, 2, 4}
        = ({{0, 1, 5}, {0, 2, 3}, {1, 3, 4}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 2} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 2, 4})
        (neighborBlock := {0, 2, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {0, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov119 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      have hcov120 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit121 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 4}
      ·
        have hcancelAt122 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt123 := hcancel 2 (by rw [hpairSetEq]; decide)
        have hcancelAt124 := hcancel 1 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt122 hcancelAt123 hcancelAt124
        have hcoeff125 : coefficient {0, 1, 5} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt122
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov120))
        have hcoeff126 : coefficient {0, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt123
            (Or.inl hcoeff125)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov119))
        have hcoeff127 : coefficient {1, 3, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt124
            (Or.inl hcoeff125)
            (Or.inl hcoeff126)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit121))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff125
        · exact hbadNe hcoeff126
        · exact hbadNe hcoeff127
      ·
        have hpin128 : totalTightSupport tightVec {1, 3, 4} = {3, 4} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 4} (by decide)) hmemSplit121 (by decide)
        have hcancelAt129 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt130 := hcancel 2 (by rw [hpairSetEq]; decide)
        have hcancelAt131 := hcancel 3 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt129 hcancelAt130 hcancelAt131
        have hcoeff132 : coefficient {0, 1, 5} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt129
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov120))
        have hcoeff133 : coefficient {0, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt130
            (Or.inl hcoeff132)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov119))
        have hcoeff134 : coefficient {1, 3, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt131
            (Or.inl hcoeff132)
            (Or.inl hcoeff133)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin128]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff132
        · exact hbadNe hcoeff133
        · exact hbadNe hcoeff134
    · -- pair {2, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {2, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov135 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit136 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
      ·
        by_cases hmemSplit137 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 4}
        ·
          have hcancelAt138 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt139 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt140 := hcancel 1 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt138 hcancelAt139 hcancelAt140
          have hcoeff141 : coefficient {0, 1, 5} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt138
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov135))
          have hcoeff142 : coefficient {0, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt139
              (Or.inl hcoeff141)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit136))
          have hcoeff143 : coefficient {1, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt140
              (Or.inl hcoeff141)
              (Or.inl hcoeff142)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit137))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff141
          · exact hbadNe hcoeff142
          · exact hbadNe hcoeff143
        ·
          have hpin144 : totalTightSupport tightVec {1, 3, 4} = {3, 4} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 4} (by decide)) hmemSplit137 (by decide)
          have hcancelAt145 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt146 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt147 := hcancel 3 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt145 hcancelAt146 hcancelAt147
          have hcoeff148 : coefficient {0, 1, 5} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt145
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov135))
          have hcoeff149 : coefficient {0, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt146
              (Or.inl hcoeff148)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit136))
          have hcoeff150 : coefficient {1, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt147
              (Or.inl hcoeff148)
              (Or.inl hcoeff149)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin144]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff148
          · exact hbadNe hcoeff149
          · exact hbadNe hcoeff150
      ·
        have hpin151 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit136 (by decide)
        have hcov152 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · exact hcoverAtom
          · rw [hpin151] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        by_cases hmemSplit153 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 3, 4}
        ·
          have hcancelAt154 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt155 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt156 := hcancel 3 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt154 hcancelAt155 hcancelAt156
          have hcoeff157 : coefficient {0, 1, 5} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt154
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin151] at hmem; exact absurd hmem (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov152))
          have hcoeff158 : coefficient {1, 3, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt155
              (Or.inl hcoeff157)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit153))
          have hcoeff159 : coefficient {0, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt156
              (Or.inl hcoeff157)
              (Or.inl hcoeff158)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin151]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff157
          · exact hbadNe hcoeff159
          · exact hbadNe hcoeff158
        ·
          have hpin160 : totalTightSupport tightVec {1, 3, 4} = {3, 4} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 3, 4} (by decide)) hmemSplit153 (by decide)
          have hcov161 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
            rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact hcoverAtom
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpin160] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hfullEq : totalTightSupport tightVec {0, 1, 5} = {0, 1, 5} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov152
            · exact hcov161
            · exact hcov135
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 1, 5} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 1, 5} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalPendantForkFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin151] at hmem; exact absurd hmem (by decide))
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
                (fun hmem => by rw [hpin160] at hmem; exact absurd hmem (by decide))
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {1, 3, 4}
    have heraseEq : canonicalPendantForkFamily.erase {1, 3, 4}
        = ({{0, 1, 5}, {0, 2, 3}, {0, 2, 4}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {1, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov162 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      have hcov163 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit164 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
      ·
        have hcancelAt165 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt166 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt167 := hcancel 0 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt165 hcancelAt166 hcancelAt167
        have hcoeff168 : coefficient {0, 1, 5} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt165
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov163))
        have hcoeff169 : coefficient {0, 2, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt166
            (Or.inl hcoeff168)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov162))
        have hcoeff170 : coefficient {0, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt167
            (Or.inl hcoeff168)
            (Or.inl hcoeff169)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit164))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff168
        · exact hbadNe hcoeff170
        · exact hbadNe hcoeff169
      ·
        have hpin171 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit164 (by decide)
        have hcancelAt172 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt173 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt174 := hcancel 2 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt172 hcancelAt173 hcancelAt174
        have hcoeff175 : coefficient {0, 1, 5} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt172
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov163))
        have hcoeff176 : coefficient {0, 2, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt173
            (Or.inl hcoeff175)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov162))
        have hcoeff177 : coefficient {0, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt174
            (Or.inl hcoeff175)
            (Or.inl hcoeff176)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin171]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff175
        · exact hbadNe hcoeff177
        · exact hbadNe hcoeff176
    · -- pair {1, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov178 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      have hcov179 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit180 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4}
      ·
        have hcancelAt181 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt182 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt183 := hcancel 0 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt181 hcancelAt182 hcancelAt183
        have hcoeff184 : coefficient {0, 1, 5} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt181
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov179))
        have hcoeff185 : coefficient {0, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt182
            (Or.inl hcoeff184)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov178))
        have hcoeff186 : coefficient {0, 2, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt183
            (Or.inl hcoeff184)
            (Or.inl hcoeff185)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit180))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff184
        · exact hbadNe hcoeff185
        · exact hbadNe hcoeff186
      ·
        have hpin187 : totalTightSupport tightVec {0, 2, 4} = {2, 4} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 4} (by decide)) hmemSplit180 (by decide)
        have hcancelAt188 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt189 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt190 := hcancel 2 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt188 hcancelAt189 hcancelAt190
        have hcoeff191 : coefficient {0, 1, 5} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt188
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov179))
        have hcoeff192 : coefficient {0, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt189
            (Or.inl hcoeff191)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov178))
        have hcoeff193 : coefficient {0, 2, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt190
            (Or.inl hcoeff191)
            (Or.inl hcoeff192)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin187]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff191
        · exact hbadNe hcoeff192
        · exact hbadNe hcoeff193
    · -- pair {3, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {3, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov194 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      have hcov195 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit196 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
      ·
        by_cases hmemSplit197 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
        ·
          by_cases hmemSplit198 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
          ·
            by_cases hmemSplit199 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4}
            ·
              by_cases hmemSplit200 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4}
              ·
                by_cases hmemSplit201 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4}
                ·
                  by_cases hmemSplit202 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5}
                  ·
                    have hfullPin203 : totalTightSupport tightVec {0, 2, 3} = {0, 2, 3} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit196
                      · exact hmemSplit197
                      · exact hmemSplit198
                    have hfullPin204 : totalTightSupport tightVec {0, 2, 4} = {0, 2, 4} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit199
                      · exact hmemSplit200
                      · exact hmemSplit201
                    have hfullPin205 : totalTightSupport tightVec {0, 1, 5} = {0, 1, 5} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit202
                      · exact hcov194
                      · exact hcov195
                    have hrangeT8 : Finset.univ.image
                        (![{1, 3, 4}, {0, 2, 3}, {0, 2, 4}, {0, 1, 5}] : Fin 4 → Finset (Fin 6))
                        = canonicalPendantForkFamily := by decide
                    have hfamilyT8 : chartArgmaxFamily (chartPointOfDesign crux.design) = Finset.univ.image
                        (![{1, 3, 4}, {0, 2, 3}, {0, 2, 4}, {0, 1, 5}] : Fin 4 → Finset (Fin 6)) := by
                      rw [hfamily, hrangeT8]
                    refine crux.false_of_fourFamily_typeEightSupports
                      (chartArgmaxFamily (chartPointOfDesign crux.design))
                      (![{1, 3, 4}, {0, 2, 3}, {0, 2, 4}, {0, 1, 5}] : Fin 4 → Finset (Fin 6))
                      hfamilyT8.symm (by decide)
                      (⟨![0, 3, 4, 2, 1, 5], ![0, 4, 3, 1, 2, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)) rfl hdata ?_ ?_ ?_ ?_
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 0 (by decide)]
                      show totalTightSupport tightVec {1, 3, 4} = _
                      rw [hpairPin]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 1 (by decide)]
                      show totalTightSupport tightVec {0, 2, 3} = _
                      rw [hfullPin203]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 2 (by decide)]
                      show totalTightSupport tightVec {0, 2, 4} = _
                      rw [hfullPin204]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 3 (by decide)]
                      show totalTightSupport tightVec {0, 1, 5} = _
                      rw [hfullPin205]
                      decide
                  ·
                    have hpin206 : totalTightSupport tightVec {0, 1, 5} = {1, 5} :=
                      eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                      (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 5} (by decide)) hmemSplit202 (by decide)
                    have hisoA207 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({0, 1, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 1 = 0 := by
                      intro other hother hne
                      rw [hfamily, canonicalPendantForkFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · exact absurd rfl hne
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                    have hisoB208 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({0, 1, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 5 = 0 := by
                      intro other hother hne
                      rw [hfamily, canonicalPendantForkFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · exact absurd rfl hne
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                    exact crux.false_of_isolated_pair_row (by decide) hdata
                      (by rw [hfamily]; decide)
                      hpin206
                      hisoA207 hisoB208
                ·
                  have hpin209 : totalTightSupport tightVec {0, 2, 4} = {0, 2} :=
                    eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                    (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 4} (by decide)) hmemSplit201 (by decide)
                  exact crux.false_of_totalTightSupport_subset_neighbor
                    (hostBlock := {0, 2, 4})
                    (neighborBlock := {0, 2, 3})
                    hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                    (by decide) hdata (by rw [hpin209]; decide)
              ·
                have hpin210 : totalTightSupport tightVec {0, 2, 4} = {0, 4} :=
                  eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 4} (by decide)) hmemSplit200 (by decide)
                have hcancelAt211 := hcancel 1 (by rw [hpairSetEq]; decide)
                have hcancelAt212 := hcancel 2 (by rw [hpairSetEq]; decide)
                have hcancelAt213 := hcancel 0 (by rw [hpairSetEq]; decide)
                rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                  Finset.sum_insert (by decide), Finset.sum_singleton]
                  at hcancelAt211 hcancelAt212 hcancelAt213
                have hcoeff214 : coefficient {0, 1, 5} = 0 :=
                  firstCoeff_eq_zero_of_sum_three hcancelAt211
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov194))
                have hcoeff215 : coefficient {0, 2, 3} = 0 :=
                  secondCoeff_eq_zero_of_sum_three hcancelAt212
                    (Or.inl hcoeff214)
                    (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin210] at hmem; exact absurd hmem (by decide))))
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit197))
                have hcoeff216 : coefficient {0, 2, 4} = 0 :=
                  thirdCoeff_eq_zero_of_sum_three hcancelAt213
                    (Or.inl hcoeff214)
                    (Or.inl hcoeff215)
                    (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit199))
                obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
                rw [hfamily, heraseEq] at hbadMem
                simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
                rcases hbadMem with rfl | rfl | rfl
                · exact hbadNe hcoeff214
                · exact hbadNe hcoeff215
                · exact hbadNe hcoeff216
            ·
              have hpin217 : totalTightSupport tightVec {0, 2, 4} = {2, 4} :=
                eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 4} (by decide)) hmemSplit199 (by decide)
              have hcancelAt218 := hcancel 1 (by rw [hpairSetEq]; decide)
              have hcancelAt219 := hcancel 0 (by rw [hpairSetEq]; decide)
              have hcancelAt220 := hcancel 2 (by rw [hpairSetEq]; decide)
              rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                Finset.sum_insert (by decide), Finset.sum_singleton]
                at hcancelAt218 hcancelAt219 hcancelAt220
              have hcoeff221 : coefficient {0, 1, 5} = 0 :=
                firstCoeff_eq_zero_of_sum_three hcancelAt218
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov194))
              have hcoeff222 : coefficient {0, 2, 3} = 0 :=
                secondCoeff_eq_zero_of_sum_three hcancelAt219
                  (Or.inl hcoeff221)
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin217] at hmem; exact absurd hmem (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit196))
              have hcoeff223 : coefficient {0, 2, 4} = 0 :=
                thirdCoeff_eq_zero_of_sum_three hcancelAt220
                  (Or.inl hcoeff221)
                  (Or.inl hcoeff222)
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin217]; decide)))
              obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
              rw [hfamily, heraseEq] at hbadMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
              rcases hbadMem with rfl | rfl | rfl
              · exact hbadNe hcoeff221
              · exact hbadNe hcoeff222
              · exact hbadNe hcoeff223
          ·
            have hpin224 : totalTightSupport tightVec {0, 2, 3} = {0, 2} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit198 (by decide)
            exact crux.false_of_totalTightSupport_subset_neighbor
              (hostBlock := {0, 2, 3})
              (neighborBlock := {0, 2, 4})
              hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
              (by decide) hdata (by rw [hpin224]; decide)
        ·
          have hpin225 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit197 (by decide)
          have hcov226 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
            rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
            · rw [hpin225] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact hcoverAtom
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hcancelAt227 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt228 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt229 := hcancel 0 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt227 hcancelAt228 hcancelAt229
          have hcoeff230 : coefficient {0, 1, 5} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt227
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov194))
          have hcoeff231 : coefficient {0, 2, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt228
              (Or.inl hcoeff230)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin225] at hmem; exact absurd hmem (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov226))
          have hcoeff232 : coefficient {0, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt229
              (Or.inl hcoeff230)
              (Or.inl hcoeff231)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit196))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff230
          · exact hbadNe hcoeff232
          · exact hbadNe hcoeff231
      ·
        have hpin233 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit196 (by decide)
        by_cases hmemSplit234 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4}
        ·
          have hcancelAt235 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt236 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt237 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt235 hcancelAt236 hcancelAt237
          have hcoeff238 : coefficient {0, 1, 5} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt235
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov194))
          have hcoeff239 : coefficient {0, 2, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt236
              (Or.inl hcoeff238)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin233] at hmem; exact absurd hmem (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit234))
          have hcoeff240 : coefficient {0, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt237
              (Or.inl hcoeff238)
              (Or.inl hcoeff239)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin233]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff238
          · exact hbadNe hcoeff240
          · exact hbadNe hcoeff239
        ·
          have hpin241 : totalTightSupport tightVec {0, 2, 4} = {2, 4} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 4} (by decide)) hmemSplit234 (by decide)
          have hcov242 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
            rw [hfamily, canonicalPendantForkFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · exact hcoverAtom
            · rw [hpin233] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpin241] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
          have hfullEq : totalTightSupport tightVec {0, 1, 5} = {0, 1, 5} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov242
            · exact hcov194
            · exact hcov195
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 1, 5} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 1, 5} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalPendantForkFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · exact absurd rfl hne
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin233] at hmem; exact absurd hmem (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin241] at hmem; exact absurd hmem (by decide))
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
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)

end Gtz

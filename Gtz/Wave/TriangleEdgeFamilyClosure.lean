import Gtz.Quantitative.FifteenFamilyDispatch
import Gtz.Wave.CrossSupportedTightExit
import Gtz.Wave.FullRowTriangleKill
import Gtz.Wave.FourFamilyTypeEightExit
import Gtz.Wave.WeightedColumnSupportBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The TriangleEdge family, listed. -/
theorem canonicalTriangleEdgeFamily_eq_literal :
    canonicalTriangleEdgeFamily
      = ({{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {0, 4, 5}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE TRIANGLEEDGE KILL.**  No crux selects this family. -/
theorem SixThreeCrux.false_of_family_canonicalTriangleEdgeFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalTriangleEdgeFamily) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 2} ∨ block = {0, 1, 3} ∨ block = {0, 2, 3} ∨ block = {0, 4, 5} := by
    have hmem := hblockMem
    rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hmem
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
    have heraseEq : canonicalTriangleEdgeFamily.erase {0, 1, 2}
        = ({{0, 1, 3}, {0, 2, 3}, {0, 4, 5}} :
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
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 2, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {1, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 2} :=
        hpairEq.symm.trans hpairPin
      have hcov1 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
      have hcov2 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
      by_cases hmemSplit3 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
      ·
        by_cases hmemSplit4 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
        ·
          by_cases hmemSplit5 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
          ·
            by_cases hmemSplit6 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
            ·
              by_cases hmemSplit7 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
              ·
                by_cases hmemSplit8 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
                ·
                  by_cases hmemSplit9 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5}
                  ·
                    have hfullPin10 : totalTightSupport tightVec {0, 1, 3} = {0, 1, 3} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit3
                      · exact hmemSplit4
                      · exact hmemSplit5
                    have hfullPin11 : totalTightSupport tightVec {0, 2, 3} = {0, 2, 3} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit6
                      · exact hmemSplit7
                      · exact hmemSplit8
                    have hfullPin12 : totalTightSupport tightVec {0, 4, 5} = {0, 4, 5} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit9
                      · exact hcov1
                      · exact hcov2
                    have hrangeT8 : Finset.univ.image
                        (![{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {0, 4, 5}] : Fin 4 → Finset (Fin 6))
                        = canonicalTriangleEdgeFamily := by decide
                    have hfamilyT8 : chartArgmaxFamily (chartPointOfDesign crux.design) = Finset.univ.image
                        (![{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {0, 4, 5}] : Fin 4 → Finset (Fin 6)) := by
                      rw [hfamily, hrangeT8]
                    refine crux.false_of_fourFamily_typeEightSupports
                      (chartArgmaxFamily (chartPointOfDesign crux.design))
                      (![{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {0, 4, 5}] : Fin 4 → Finset (Fin 6))
                      hfamilyT8.symm (by decide)
                      (⟨![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)) rfl hdata ?_ ?_ ?_ ?_
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 0 (by decide)]
                      show totalTightSupport tightVec {0, 1, 2} = _
                      rw [hpairPin]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 1 (by decide)]
                      show totalTightSupport tightVec {0, 1, 3} = _
                      rw [hfullPin10]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 2 (by decide)]
                      show totalTightSupport tightVec {0, 2, 3} = _
                      rw [hfullPin11]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 3 (by decide)]
                      show totalTightSupport tightVec {0, 4, 5} = _
                      rw [hfullPin12]
                      decide
                  ·
                    have hpin13 : totalTightSupport tightVec {0, 4, 5} = {4, 5} :=
                      eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                      (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 4, 5} (by decide)) hmemSplit9 (by decide)
                    have hisoA14 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({0, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 4 = 0 := by
                      intro other hother hne
                      rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact absurd rfl hne
                    have hisoB15 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({0, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 5 = 0 := by
                      intro other hother hne
                      rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact absurd rfl hne
                    exact crux.false_of_isolated_pair_row (by decide) hdata
                      (by rw [hfamily]; decide)
                      hpin13
                      hisoA14 hisoB15
                ·
                  have hpin16 : totalTightSupport tightVec {0, 2, 3} = {0, 2} :=
                    eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                    (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit8 (by decide)
                  exact crux.false_of_totalTightSupport_subset_neighbor
                    (hostBlock := {0, 2, 3})
                    (neighborBlock := {0, 1, 2})
                    hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                    (by decide) hdata (by rw [hpin16]; decide)
              ·
                have hpin17 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
                  eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit7 (by decide)
                exact crux.false_of_totalTightSupport_subset_neighbor
                  (hostBlock := {0, 2, 3})
                  (neighborBlock := {0, 1, 3})
                  hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                  (by decide) hdata (by rw [hpin17]; decide)
            ·
              have hpin18 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
                eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit6 (by decide)
              have hcancelAt19 := hcancel 4 (by rw [hpairSetEq]; decide)
              have hcancelAt20 := hcancel 0 (by rw [hpairSetEq]; decide)
              have hcancelAt21 := hcancel 3 (by rw [hpairSetEq]; decide)
              rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                Finset.sum_insert (by decide), Finset.sum_singleton]
                at hcancelAt19 hcancelAt20 hcancelAt21
              have hcoeff22 : coefficient {0, 4, 5} = 0 :=
                thirdCoeff_eq_zero_of_sum_three hcancelAt19
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
              have hcoeff23 : coefficient {0, 1, 3} = 0 :=
                firstCoeff_eq_zero_of_sum_three hcancelAt20
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin18] at hmem; exact absurd hmem (by decide))))
                  (Or.inl hcoeff22)
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit3))
              have hcoeff24 : coefficient {0, 2, 3} = 0 :=
                secondCoeff_eq_zero_of_sum_three hcancelAt21
                  (Or.inl hcoeff23)
                  (Or.inl hcoeff22)
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin18]; decide)))
              obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
              rw [hfamily, heraseEq] at hbadMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
              rcases hbadMem with rfl | rfl | rfl
              · exact hbadNe hcoeff23
              · exact hbadNe hcoeff24
              · exact hbadNe hcoeff22
          ·
            have hpin25 : totalTightSupport tightVec {0, 1, 3} = {0, 1} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit5 (by decide)
            exact crux.false_of_totalTightSupport_subset_neighbor
              (hostBlock := {0, 1, 3})
              (neighborBlock := {0, 1, 2})
              hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
              (by decide) hdata (by rw [hpin25]; decide)
        ·
          have hpin26 : totalTightSupport tightVec {0, 1, 3} = {0, 3} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit4 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 1, 3})
            (neighborBlock := {0, 2, 3})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin26]; decide)
      ·
        have hpin27 : totalTightSupport tightVec {0, 1, 3} = {1, 3} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit3 (by decide)
        by_cases hmemSplit28 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
        ·
          have hcancelAt29 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt30 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt31 := hcancel 3 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt29 hcancelAt30 hcancelAt31
          have hcoeff32 : coefficient {0, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt29
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
          have hcoeff33 : coefficient {0, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt30
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin27] at hmem; exact absurd hmem (by decide))))
              (Or.inl hcoeff32)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit28))
          have hcoeff34 : coefficient {0, 1, 3} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt31
              (Or.inl hcoeff33)
              (Or.inl hcoeff32)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin27]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff34
          · exact hbadNe hcoeff33
          · exact hbadNe hcoeff32
        ·
          have hpin35 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit28 (by decide)
          have hcov36 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
            rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpin27] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpin35] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact hcoverAtom
          have hfullEq : totalTightSupport tightVec {0, 4, 5} = {0, 4, 5} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov36
            · exact hcov1
            · exact hcov2
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 4, 5} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 4, 5} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin27] at hmem; exact absurd hmem (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin35] at hmem; exact absurd hmem (by decide))
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
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 1, 3}
    have heraseEq : canonicalTriangleEdgeFamily.erase {0, 1, 3}
        = ({{0, 1, 2}, {0, 2, 3}, {0, 4, 5}} :
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
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 3})
        (neighborBlock := {0, 2, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {1, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov37 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
      have hcov38 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
      by_cases hmemSplit39 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit40 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
        ·
          by_cases hmemSplit41 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
          ·
            by_cases hmemSplit42 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
            ·
              by_cases hmemSplit43 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
              ·
                by_cases hmemSplit44 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
                ·
                  by_cases hmemSplit45 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5}
                  ·
                    have hfullPin46 : totalTightSupport tightVec {0, 1, 2} = {0, 1, 2} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit39
                      · exact hmemSplit40
                      · exact hmemSplit41
                    have hfullPin47 : totalTightSupport tightVec {0, 2, 3} = {0, 2, 3} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit42
                      · exact hmemSplit43
                      · exact hmemSplit44
                    have hfullPin48 : totalTightSupport tightVec {0, 4, 5} = {0, 4, 5} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit45
                      · exact hcov37
                      · exact hcov38
                    have hrangeT8 : Finset.univ.image
                        (![{0, 1, 3}, {0, 1, 2}, {0, 2, 3}, {0, 4, 5}] : Fin 4 → Finset (Fin 6))
                        = canonicalTriangleEdgeFamily := by decide
                    have hfamilyT8 : chartArgmaxFamily (chartPointOfDesign crux.design) = Finset.univ.image
                        (![{0, 1, 3}, {0, 1, 2}, {0, 2, 3}, {0, 4, 5}] : Fin 4 → Finset (Fin 6)) := by
                      rw [hfamily, hrangeT8]
                    refine crux.false_of_fourFamily_typeEightSupports
                      (chartArgmaxFamily (chartPointOfDesign crux.design))
                      (![{0, 1, 3}, {0, 1, 2}, {0, 2, 3}, {0, 4, 5}] : Fin 4 → Finset (Fin 6))
                      hfamilyT8.symm (by decide)
                      (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)) rfl hdata ?_ ?_ ?_ ?_
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 0 (by decide)]
                      show totalTightSupport tightVec {0, 1, 3} = _
                      rw [hpairPin]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 1 (by decide)]
                      show totalTightSupport tightVec {0, 1, 2} = _
                      rw [hfullPin46]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 2 (by decide)]
                      show totalTightSupport tightVec {0, 2, 3} = _
                      rw [hfullPin47]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 3 (by decide)]
                      show totalTightSupport tightVec {0, 4, 5} = _
                      rw [hfullPin48]
                      decide
                  ·
                    have hpin49 : totalTightSupport tightVec {0, 4, 5} = {4, 5} :=
                      eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                      (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 4, 5} (by decide)) hmemSplit45 (by decide)
                    have hisoA50 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({0, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 4 = 0 := by
                      intro other hother hne
                      rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact absurd rfl hne
                    have hisoB51 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({0, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 5 = 0 := by
                      intro other hother hne
                      rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact absurd rfl hne
                    exact crux.false_of_isolated_pair_row (by decide) hdata
                      (by rw [hfamily]; decide)
                      hpin49
                      hisoA50 hisoB51
                ·
                  have hpin52 : totalTightSupport tightVec {0, 2, 3} = {0, 2} :=
                    eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                    (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit44 (by decide)
                  exact crux.false_of_totalTightSupport_subset_neighbor
                    (hostBlock := {0, 2, 3})
                    (neighborBlock := {0, 1, 2})
                    hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                    (by decide) hdata (by rw [hpin52]; decide)
              ·
                have hpin53 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
                  eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit43 (by decide)
                exact crux.false_of_totalTightSupport_subset_neighbor
                  (hostBlock := {0, 2, 3})
                  (neighborBlock := {0, 1, 3})
                  hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                  (by decide) hdata (by rw [hpin53]; decide)
            ·
              have hpin54 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
                eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit42 (by decide)
              have hcancelAt55 := hcancel 4 (by rw [hpairSetEq]; decide)
              have hcancelAt56 := hcancel 0 (by rw [hpairSetEq]; decide)
              have hcancelAt57 := hcancel 2 (by rw [hpairSetEq]; decide)
              rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                Finset.sum_insert (by decide), Finset.sum_singleton]
                at hcancelAt55 hcancelAt56 hcancelAt57
              have hcoeff58 : coefficient {0, 4, 5} = 0 :=
                thirdCoeff_eq_zero_of_sum_three hcancelAt55
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov37))
              have hcoeff59 : coefficient {0, 1, 2} = 0 :=
                firstCoeff_eq_zero_of_sum_three hcancelAt56
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin54] at hmem; exact absurd hmem (by decide))))
                  (Or.inl hcoeff58)
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit39))
              have hcoeff60 : coefficient {0, 2, 3} = 0 :=
                secondCoeff_eq_zero_of_sum_three hcancelAt57
                  (Or.inl hcoeff59)
                  (Or.inl hcoeff58)
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin54]; decide)))
              obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
              rw [hfamily, heraseEq] at hbadMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
              rcases hbadMem with rfl | rfl | rfl
              · exact hbadNe hcoeff59
              · exact hbadNe hcoeff60
              · exact hbadNe hcoeff58
          ·
            have hpin61 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit41 (by decide)
            exact crux.false_of_totalTightSupport_subset_neighbor
              (hostBlock := {0, 1, 2})
              (neighborBlock := {0, 1, 3})
              hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
              (by decide) hdata (by rw [hpin61]; decide)
        ·
          have hpin62 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit40 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 1, 2})
            (neighborBlock := {0, 2, 3})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin62]; decide)
      ·
        have hpin63 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit39 (by decide)
        by_cases hmemSplit64 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
        ·
          have hcancelAt65 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt66 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt67 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt65 hcancelAt66 hcancelAt67
          have hcoeff68 : coefficient {0, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt65
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov37))
          have hcoeff69 : coefficient {0, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt66
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin63] at hmem; exact absurd hmem (by decide))))
              (Or.inl hcoeff68)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit64))
          have hcoeff70 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt67
              (Or.inl hcoeff69)
              (Or.inl hcoeff68)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin63]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff70
          · exact hbadNe hcoeff69
          · exact hbadNe hcoeff68
        ·
          have hpin71 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit64 (by decide)
          have hcov72 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
            rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · rw [hpin63] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpin71] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact hcoverAtom
          have hfullEq : totalTightSupport tightVec {0, 4, 5} = {0, 4, 5} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov72
            · exact hcov37
            · exact hcov38
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 4, 5} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 4, 5} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin63] at hmem; exact absurd hmem (by decide))
            · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
              rw [hpairPin]
              decide
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin71] at hmem; exact absurd hmem (by decide))
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
                (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
            · exact absurd rfl hne
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 2, 3}
    have heraseEq : canonicalTriangleEdgeFamily.erase {0, 2, 3}
        = ({{0, 1, 2}, {0, 1, 3}, {0, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 2} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 2, 3})
        (neighborBlock := {0, 1, 2})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {0, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 3} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 2, 3})
        (neighborBlock := {0, 1, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {2, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {2, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov73 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
      have hcov74 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
      by_cases hmemSplit75 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit76 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
        ·
          by_cases hmemSplit77 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
          ·
            by_cases hmemSplit78 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
            ·
              by_cases hmemSplit79 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
              ·
                by_cases hmemSplit80 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
                ·
                  by_cases hmemSplit81 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5}
                  ·
                    have hfullPin82 : totalTightSupport tightVec {0, 1, 2} = {0, 1, 2} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit75
                      · exact hmemSplit76
                      · exact hmemSplit77
                    have hfullPin83 : totalTightSupport tightVec {0, 1, 3} = {0, 1, 3} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit78
                      · exact hmemSplit79
                      · exact hmemSplit80
                    have hfullPin84 : totalTightSupport tightVec {0, 4, 5} = {0, 4, 5} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit81
                      · exact hcov73
                      · exact hcov74
                    have hrangeT8 : Finset.univ.image
                        (![{0, 2, 3}, {0, 1, 2}, {0, 1, 3}, {0, 4, 5}] : Fin 4 → Finset (Fin 6))
                        = canonicalTriangleEdgeFamily := by decide
                    have hfamilyT8 : chartArgmaxFamily (chartPointOfDesign crux.design) = Finset.univ.image
                        (![{0, 2, 3}, {0, 1, 2}, {0, 1, 3}, {0, 4, 5}] : Fin 4 → Finset (Fin 6)) := by
                      rw [hfamily, hrangeT8]
                    refine crux.false_of_fourFamily_typeEightSupports
                      (chartArgmaxFamily (chartPointOfDesign crux.design))
                      (![{0, 2, 3}, {0, 1, 2}, {0, 1, 3}, {0, 4, 5}] : Fin 4 → Finset (Fin 6))
                      hfamilyT8.symm (by decide)
                      (⟨![0, 2, 3, 1, 4, 5], ![0, 3, 1, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)) rfl hdata ?_ ?_ ?_ ?_
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 0 (by decide)]
                      show totalTightSupport tightVec {0, 2, 3} = _
                      rw [hpairPin]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 1 (by decide)]
                      show totalTightSupport tightVec {0, 1, 2} = _
                      rw [hfullPin82]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 2 (by decide)]
                      show totalTightSupport tightVec {0, 1, 3} = _
                      rw [hfullPin83]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 3 (by decide)]
                      show totalTightSupport tightVec {0, 4, 5} = _
                      rw [hfullPin84]
                      decide
                  ·
                    have hpin85 : totalTightSupport tightVec {0, 4, 5} = {4, 5} :=
                      eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                      (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 4, 5} (by decide)) hmemSplit81 (by decide)
                    have hisoA86 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({0, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 4 = 0 := by
                      intro other hother hne
                      rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact absurd rfl hne
                    have hisoB87 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({0, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 5 = 0 := by
                      intro other hother hne
                      rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact absurd rfl hne
                    exact crux.false_of_isolated_pair_row (by decide) hdata
                      (by rw [hfamily]; decide)
                      hpin85
                      hisoA86 hisoB87
                ·
                  have hpin88 : totalTightSupport tightVec {0, 1, 3} = {0, 1} :=
                    eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                    (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit80 (by decide)
                  exact crux.false_of_totalTightSupport_subset_neighbor
                    (hostBlock := {0, 1, 3})
                    (neighborBlock := {0, 1, 2})
                    hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                    (by decide) hdata (by rw [hpin88]; decide)
              ·
                have hpin89 : totalTightSupport tightVec {0, 1, 3} = {0, 3} :=
                  eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit79 (by decide)
                exact crux.false_of_totalTightSupport_subset_neighbor
                  (hostBlock := {0, 1, 3})
                  (neighborBlock := {0, 2, 3})
                  hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                  (by decide) hdata (by rw [hpin89]; decide)
            ·
              have hpin90 : totalTightSupport tightVec {0, 1, 3} = {1, 3} :=
                eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit78 (by decide)
              have hcancelAt91 := hcancel 4 (by rw [hpairSetEq]; decide)
              have hcancelAt92 := hcancel 0 (by rw [hpairSetEq]; decide)
              have hcancelAt93 := hcancel 1 (by rw [hpairSetEq]; decide)
              rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                Finset.sum_insert (by decide), Finset.sum_singleton]
                at hcancelAt91 hcancelAt92 hcancelAt93
              have hcoeff94 : coefficient {0, 4, 5} = 0 :=
                thirdCoeff_eq_zero_of_sum_three hcancelAt91
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov73))
              have hcoeff95 : coefficient {0, 1, 2} = 0 :=
                firstCoeff_eq_zero_of_sum_three hcancelAt92
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin90] at hmem; exact absurd hmem (by decide))))
                  (Or.inl hcoeff94)
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit75))
              have hcoeff96 : coefficient {0, 1, 3} = 0 :=
                secondCoeff_eq_zero_of_sum_three hcancelAt93
                  (Or.inl hcoeff95)
                  (Or.inl hcoeff94)
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin90]; decide)))
              obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
              rw [hfamily, heraseEq] at hbadMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
              rcases hbadMem with rfl | rfl | rfl
              · exact hbadNe hcoeff95
              · exact hbadNe hcoeff96
              · exact hbadNe hcoeff94
          ·
            have hpin97 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit77 (by decide)
            exact crux.false_of_totalTightSupport_subset_neighbor
              (hostBlock := {0, 1, 2})
              (neighborBlock := {0, 1, 3})
              hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
              (by decide) hdata (by rw [hpin97]; decide)
        ·
          have hpin98 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit76 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 1, 2})
            (neighborBlock := {0, 2, 3})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin98]; decide)
      ·
        have hpin99 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit75 (by decide)
        by_cases hmemSplit100 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
        ·
          have hcancelAt101 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt102 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt103 := hcancel 1 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt101 hcancelAt102 hcancelAt103
          have hcoeff104 : coefficient {0, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt101
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov73))
          have hcoeff105 : coefficient {0, 1, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt102
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin99] at hmem; exact absurd hmem (by decide))))
              (Or.inl hcoeff104)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit100))
          have hcoeff106 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt103
              (Or.inl hcoeff105)
              (Or.inl hcoeff104)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin99]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff106
          · exact hbadNe hcoeff105
          · exact hbadNe hcoeff104
        ·
          have hpin107 : totalTightSupport tightVec {0, 1, 3} = {1, 3} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit100 (by decide)
          have hcov108 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
            obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
            rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hcoverMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
            rcases hcoverMem with rfl | rfl | rfl | rfl
            · rw [hpin99] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpin107] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · rw [hpairPin] at hcoverAtom
              exact absurd hcoverAtom (by decide)
            · exact hcoverAtom
          have hfullEq : totalTightSupport tightVec {0, 4, 5} = {0, 4, 5} := by
            refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
            intro atom hatom
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
            rcases hatom with rfl | rfl | rfl
            · exact hcov108
            · exact hcov73
            · exact hcov74
          have hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
              otherBlock ≠ ({0, 4, 5} : Finset (Fin 6)) →
              ∀ atomIndex ∈ ({0, 4, 5} : Finset (Fin 6)),
                totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
            intro other hother hne atomIndex hatomIndex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hatomIndex
            rw [hfamily, canonicalTriangleEdgeFamily_eq_literal] at hother
            simp only [Finset.mem_insert, Finset.mem_singleton] at hother
            rcases hatomIndex with rfl | rfl | rfl <;>
              rcases hother with rfl | rfl | rfl | rfl
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin99] at hmem; exact absurd hmem (by decide))
            · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                (fun hmem => by rw [hpin107] at hmem; exact absurd hmem (by decide))
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
          exact crux.false_of_fullRow_isolated_from_residual hfour hdata
            (by rw [hfamily]; decide) hfullEq hothersOff
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 4, 5}
    have heraseEq : canonicalTriangleEdgeFamily.erase {0, 4, 5}
        = ({{0, 1, 2}, {0, 1, 3}, {0, 2, 3}} :
            Finset (Finset (Fin 6))) := by decide
    by_cases hmemSplit109 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
    ·
      by_cases hmemSplit110 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit111 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
        ·
          by_cases hmemSplit112 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
          ·
            by_cases hmemSplit113 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
            ·
              by_cases hmemSplit114 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
              ·
                have hcancelAt115 := hcancel 1 (fun hmem => absurd (hpairSubset hmem) (by decide))
                rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                  Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt115
                have hrowZero116 : totalEigenSquareRow tightVec {0, 2, 3} 1 = 0 :=
                  totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                have hdeadTerm117 : coefficient {0, 2, 3} * totalEigenSquareRow tightVec {0, 2, 3} 1 = 0 := by
                  rw [hrowZero116]; ring
                have hmeet118 : coefficient {0, 1, 2} * totalEigenSquareRow tightVec {0, 1, 2} 1
                    + coefficient {0, 1, 3} * totalEigenSquareRow tightVec {0, 1, 3} 1 = 0 := by
                  linarith [hcancelAt115, hdeadTerm117]
                have hcancelAt119 := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
                rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                  Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt119
                have hrowZero120 : totalEigenSquareRow tightVec {0, 1, 2} 3 = 0 :=
                  totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                have hdeadTerm121 : coefficient {0, 1, 2} * totalEigenSquareRow tightVec {0, 1, 2} 3 = 0 := by
                  rw [hrowZero120]; ring
                have hmeet122 : coefficient {0, 1, 3} * totalEigenSquareRow tightVec {0, 1, 3} 3
                    + coefficient {0, 2, 3} * totalEigenSquareRow tightVec {0, 2, 3} 3 = 0 := by
                  linarith [hcancelAt119, hdeadTerm121]
                have hcancelAt123 := hcancel 2 (fun hmem => absurd (hpairSubset hmem) (by decide))
                rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                  Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt123
                have hrowZero124 : totalEigenSquareRow tightVec {0, 1, 3} 2 = 0 :=
                  totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                have hdeadTerm125 : coefficient {0, 1, 3} * totalEigenSquareRow tightVec {0, 1, 3} 2 = 0 := by
                  rw [hrowZero124]; ring
                have hmeet126 : coefficient {0, 1, 2} * totalEigenSquareRow tightVec {0, 1, 2} 2
                    + coefficient {0, 2, 3} * totalEigenSquareRow tightVec {0, 2, 3} 2 = 0 := by
                  linarith [hcancelAt123, hdeadTerm125]
                refine false_of_oppositeSign_triangle hmeet118 hmeet122 hmeet126
                  (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit109)
                  (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit111)
                  (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit112)
                  (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit114)
                  (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit110)
                  (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit113) ?_
                obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
                rw [hfamily, heraseEq] at hbadMem
                simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
                rcases hbadMem with rfl | rfl | rfl
                · exact Or.inl hbadNe
                · exact Or.inr (Or.inl hbadNe)
                · exact Or.inr (Or.inr hbadNe)
              ·
                have hpin127 : totalTightSupport tightVec {0, 2, 3} = {0, 2} :=
                  eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit114 (by decide)
                exact crux.false_of_totalTightSupport_subset_neighbor
                  (hostBlock := {0, 2, 3})
                  (neighborBlock := {0, 1, 2})
                  hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                  (by decide) hdata (by rw [hpin127]; decide)
            ·
              have hpin128 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
                eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit113 (by decide)
              exact crux.false_of_totalTightSupport_subset_neighbor
                (hostBlock := {0, 2, 3})
                (neighborBlock := {0, 1, 3})
                hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                (by decide) hdata (by rw [hpin128]; decide)
          ·
            have hpin129 : totalTightSupport tightVec {0, 1, 3} = {0, 1} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit112 (by decide)
            exact crux.false_of_totalTightSupport_subset_neighbor
              (hostBlock := {0, 1, 3})
              (neighborBlock := {0, 1, 2})
              hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
              (by decide) hdata (by rw [hpin129]; decide)
        ·
          have hpin130 : totalTightSupport tightVec {0, 1, 3} = {0, 3} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit111 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 1, 3})
            (neighborBlock := {0, 2, 3})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin130]; decide)
      ·
        have hpin131 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
          eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit110 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 1, 2})
          (neighborBlock := {0, 1, 3})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin131]; decide)
    ·
      have hpin132 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
        eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit109 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 2, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin132]; decide)

end Gtz

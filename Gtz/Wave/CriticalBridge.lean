import Gtz.Quantitative.StrongStationarityIndexFloor
import Gtz.Wave.ZeroLeakPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

/-- Convert membership in the scratch finite row span into coefficients indexed by the
ambient active family. -/
theorem exists_family_linearCombination_eq_of_mem_finiteRowSpan
    {size : ℕ} {family : Finset (Finset (Fin size))}
    {row : Finset (Fin size) → (Fin size → ℝ)} {target : Fin size → ℝ}
    (hmem : target ∈ finiteRowSpan family row) :
    ∃ coefficient : Finset (Fin size) → ℝ,
      ∑ selected ∈ family, coefficient selected • row selected = target := by
  classical
  obtain ⟨subtypeCoefficient, hcombination⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  let coefficient : Finset (Fin size) → ℝ := fun selected ↦
    if hselected : selected ∈ family then subtypeCoefficient ⟨selected, hselected⟩ else 0
  refine ⟨coefficient, ?_⟩
  calc
    ∑ selected ∈ family, coefficient selected • row selected
        = ∑ selected : {selected // selected ∈ family},
            coefficient selected.1 • row selected.1 := by
              exact (Finset.sum_coe_sort family
                (fun selected ↦ coefficient selected • row selected)).symm
    _ = ∑ selected : {selected // selected ∈ family},
          subtypeCoefficient selected • row selected.1 := by
            apply Finset.sum_congr rfl
            intro selected _
            simp only [coefficient, dif_pos selected.2]
    _ = target := hcombination

/-- The actual four-active-family reading of the second-order row-span witness.  Once
the selected squared row is known to have pair support, the other three active rows
must admit a nonzero cancellation at every coordinate outside that pair. -/
theorem exists_threeActiveRow_cancellation_of_mem_finiteRowSpan
    {size : ℕ} {family : Finset (Finset (Fin size))}
    (hfour : family.card = 4)
    (row : Finset (Fin size) → (Fin size → ℝ))
    {selected : Finset (Fin size)} (hselected : selected ∈ family)
    {pairFirst pairSecond : Fin size} (hpairDistinct : pairFirst ≠ pairSecond)
    (hselectedFirst : row selected pairFirst ≠ 0)
    (hselectedSecond : row selected pairSecond ≠ 0)
    (hselectedSupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)) →
        row selected atomIndex = 0)
    (hcoordinate : Pi.single pairFirst (1 : ℝ) ∈ finiteRowSpan family row) :
    ∃ coefficient : Finset (Fin size) → ℝ,
      (family.erase selected).card = 3
        ∧ (∃ activeBlock ∈ family.erase selected, coefficient activeBlock ≠ 0)
        ∧ (∑ activeBlock ∈ family.erase selected,
            coefficient activeBlock • row activeBlock) ≠ 0
        ∧ ∀ atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)),
          ∑ activeBlock ∈ family.erase selected,
            coefficient activeBlock * row activeBlock atomIndex = 0 := by
  obtain ⟨coefficient, hcombination⟩ :=
    exists_family_linearCombination_eq_of_mem_finiteRowSpan hcoordinate
  exact exists_nontrivial_threeRow_cancellation_off_pair family hfour row hselected
    hpairDistinct hselectedFirst hselectedSecond hselectedSupport
    ⟨coefficient, hcombination⟩

/-- The total squared row is nonzero exactly on the total tight support. -/
theorem totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport
    {size rank : ℕ} (tightVec : Finset (Fin size) → (Fin rank → ℝ))
    {selected : Finset (Fin size)} (hcard : selected.card = rank)
    {atomIndex : Fin size} :
    totalEigenSquareRow tightVec selected atomIndex ≠ 0
      ↔ atomIndex ∈ totalTightSupport tightVec selected := by
  classical
  rw [totalEigenSquareRow_of_card tightVec hcard,
    totalTightSupport_of_card tightVec hcard]
  constructor
  · intro hrow
    have hmemSelected : atomIndex ∈ selected := by
      by_contra hnotMem
      exact hrow (eigenSquareRow_eq_zero_of_notMem hcard (tightVec selected) hnotMem)
    have hrange : atomIndex ∈ Set.range (selected.orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin selected hcard]
      exact hmemSelected
    obtain ⟨blockIndex, hblockIndex⟩ := hrange
    have hentry := eigenSquareRow_eq_sq hcard (tightVec selected) hblockIndex
    rw [hentry] at hrow
    have hvecNonzero : tightVec selected blockIndex ≠ 0 := by
      intro hzero
      apply hrow
      simp [hzero]
    exact Finset.mem_image.mpr ⟨blockIndex,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvecNonzero⟩, hblockIndex⟩
  · intro hsupport
    obtain ⟨blockIndex, hblockIndex, hindex⟩ := Finset.mem_image.mp hsupport
    rw [eigenSquareRow_eq_sq hcard (tightVec selected) hindex]
    exact pow_ne_zero 2 (Finset.mem_filter.mp hblockIndex).2

/-- Fully instantiated support-two residue for the rows used by the strong-stationarity
index-floor file.  Under four active triples and exact pair support, the remaining three
squared tight rows satisfy a nontrivial outside-pair cancellation. -/
theorem exists_threeActiveEigenSquareRow_cancellation_of_support_pair
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    {family : Finset (Finset (Fin 6))} (hfour : family.card = 4)
    {selected : Finset (Fin 6)} (hselected : selected ∈ family)
    (hselectedCard : selected.card = 3)
    {pairFirst pairSecond : Fin 6} (hpairDistinct : pairFirst ≠ pairSecond)
    (hsupport : totalTightSupport tightVec selected
      = ({pairFirst, pairSecond} : Finset (Fin 6)))
    (hcoordinate : Pi.single pairFirst (1 : ℝ) ∈
      finiteRowSpan family (totalEigenSquareRow tightVec)) :
    ∃ coefficient : Finset (Fin 6) → ℝ,
      (family.erase selected).card = 3
        ∧ (∃ activeBlock ∈ family.erase selected, coefficient activeBlock ≠ 0)
        ∧ (∑ activeBlock ∈ family.erase selected,
            coefficient activeBlock • totalEigenSquareRow tightVec activeBlock) ≠ 0
        ∧ ∀ atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin 6)),
          ∑ activeBlock ∈ family.erase selected,
            coefficient activeBlock
              * totalEigenSquareRow tightVec activeBlock atomIndex = 0 := by
  have hfirstMem : pairFirst ∈ totalTightSupport tightVec selected := by
    rw [hsupport]
    simp
  have hsecondMem : pairSecond ∈ totalTightSupport tightVec selected := by
    rw [hsupport]
    simp
  have hfirstRow : totalEigenSquareRow tightVec selected pairFirst ≠ 0 :=
    (totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport tightVec hselectedCard).mpr
      hfirstMem
  have hsecondRow : totalEigenSquareRow tightVec selected pairSecond ≠ 0 :=
    (totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport tightVec hselectedCard).mpr
      hsecondMem
  have hrowSupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin 6)) →
        totalEigenSquareRow tightVec selected atomIndex = 0 := by
    intro atomIndex hnotPair
    by_contra hrow
    have hmem :=
      (totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport tightVec hselectedCard).mp hrow
    rw [hsupport] at hmem
    exact hnotPair hmem
  exact exists_threeActiveRow_cancellation_of_mem_finiteRowSpan hfour
    (totalEigenSquareRow tightVec) hselected hpairDistinct hfirstRow hsecondRow
    hrowSupport hcoordinate

/-- Strong stationarity specialized to the ambient spreads used by the second-order
eigenvector family, retaining the whole weak datum and therefore commutation. -/
theorem SixThreeCrux.exists_multiplier_ambientTightSelection_isChartStationaryData
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected) :
    ∃ multiplier : Finset (Fin 6) → ℝ,
      IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design))
        (chartArgmaxFamily (chartPointOfDesign crux.design))
        (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
        (ambientTightSelection tightVec) := by
  let selection : Finset (Fin 6) → (Fin 6 → ℝ) := ambientTightSelection tightVec
  have hselection : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      IsChartTightDirection (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) selected (selection selected) := by
    intro selected hmember
    exact isChartTightDirection_ambientTightSelection crux tightVec hunit hEigen hmember
  simpa only [selection] using
    exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData
      crux.isChartStrongStationaryData selection hselection

/-- The second-order witness packaged with its full stationary assembly. -/
theorem SixThreeCrux.exists_rowSpanWitness_with_commutingAssembly
    (crux : SixThreeCrux) :
    ∃ (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
      (multiplier : Finset (Fin 6) → ℝ)
      (block : Finset (Fin 6)),
      (∀ selected : Finset (Fin 6), selected.card = 3 →
        tightVec selected ⬝ᵥ tightVec selected = 1)
      ∧ (∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        (chartPointGap (chartPointOfDesign crux.design)).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
          = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
      ∧ IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          (chartArgmaxFamily (chartPointOfDesign crux.design))
          (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
          (ambientTightSelection tightVec)
      ∧ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
      ∧ 2 ≤ (totalTightSupport tightVec block).card
      ∧ ∀ atomIndex ∈ totalTightSupport tightVec block,
        Pi.single atomIndex (1 : ℝ) ∈ finiteRowSpan
          (chartArgmaxFamily (chartPointOfDesign crux.design))
          (totalEigenSquareRow tightVec) := by
  classical
  obtain ⟨tightVec, hunit, hEigen⟩ :=
    exists_unit_chartBlockEigenvectorFamily (chartPointOfDesign crux.design)
  obtain ⟨multiplier, hdata⟩ :=
    crux.exists_multiplier_ambientTightSelection_isChartStationaryData tightVec hunit hEigen
  obtain ⟨block, hblock, hflatLe⟩ :=
    crux.exists_argmax_le_vanishingSubmodule_totalTightSupport tightVec hunit hEigen
  have hrowEq : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      ∀ atomIndex : Fin 6,
        totalEigenSquareRow tightVec selected atomIndex
          = ambientTightSelection tightVec selected atomIndex
              * ambientTightSelection tightVec selected atomIndex := by
    intro selected hmember atomIndex
    have hcard : selected.card = 3 :=
      ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
    have hrestriction : tightVec selected = fun blockIndex ↦
        ambientTightSelection tightVec selected (selected.orderEmbOfFin hcard blockIndex) := by
      funext blockIndex
      rw [ambientTightSelection, dif_pos hcard,
        selectionInjection_mulVec_apply (selected.orderEmbOfFin hcard).injective]
    rw [totalEigenSquareRow_of_card tightVec hcard, hrestriction]
    exact eigenSquareRow_eq_mul_self_of_support hcard
      (ambientTightSelection tightVec selected)
      (hdata.tightDir_support selected hmember) atomIndex
  have hassembly : ∀ atomIndex : Fin 6,
      ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
        multiplier selected * totalEigenSquareRow tightVec selected atomIndex
          = (((6 : ℕ) : ℝ))⁻¹ :=
    assemblyDiagonal_of_isChartStationaryData_of_rowEq hdata
      (totalEigenSquareRow tightVec) hrowEq
  refine ⟨tightVec, multiplier, block, hunit, hEigen, hdata, hblock,
    crux.two_le_card_totalTightSupport tightVec hunit hEigen block ?_, ?_⟩
  · exact ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) block).mp hblock).1
  · intro atomIndex hatom
    exact coordinateSingle_mem_finiteRowSpan_of_flat_le_vanishing (by norm_num)
      (chartArgmaxFamily (chartPointOfDesign crux.design)) (totalEigenSquareRow tightVec)
      multiplier hassembly (totalTightSupport tightVec block) hflatLe hatom

/-- **THE CRITICAL FOUR-ACTIVE REDUCTION.**  The full commutation-bearing stationary
datum and the second-order row-span witness leave exactly two possibilities: the selected
direction has full three-atom support, or its pair support forces a nontrivial cancellation
of the other three active squared rows off that pair. -/
theorem SixThreeCrux.exists_fullSupport_or_threeRowCancellation_of_card_eq_four
    (crux : SixThreeCrux)
    (hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ∃ (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
      (multiplier : Finset (Fin 6) → ℝ)
      (block : Finset (Fin 6)),
      IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          (chartArgmaxFamily (chartPointOfDesign crux.design))
          (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
          (ambientTightSelection tightVec)
      ∧ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
      ∧ ((totalTightSupport tightVec block).card = 3
        ∨ ∃ (pairFirst pairSecond : Fin 6)
            (coefficient : Finset (Fin 6) → ℝ),
          pairFirst ≠ pairSecond
            ∧ totalTightSupport tightVec block
                = ({pairFirst, pairSecond} : Finset (Fin 6))
            ∧ ((chartArgmaxFamily (chartPointOfDesign crux.design)).erase block).card = 3
            ∧ (∃ activeBlock ∈
                (chartArgmaxFamily (chartPointOfDesign crux.design)).erase block,
                coefficient activeBlock ≠ 0)
            ∧ (∑ activeBlock ∈
                (chartArgmaxFamily (chartPointOfDesign crux.design)).erase block,
                coefficient activeBlock • totalEigenSquareRow tightVec activeBlock) ≠ 0
            ∧ ∀ atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin 6)),
              ∑ activeBlock ∈
                  (chartArgmaxFamily (chartPointOfDesign crux.design)).erase block,
                coefficient activeBlock
                  * totalEigenSquareRow tightVec activeBlock atomIndex = 0) := by
  classical
  obtain ⟨tightVec, multiplier, block, hunit, hEigen, hdata, hblock,
    hsupportLower, hrowSpan⟩ := crux.exists_rowSpanWitness_with_commutingAssembly
  refine ⟨tightVec, multiplier, block, hdata, hblock, ?_⟩
  have hblockCard : block.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) block).mp hblock).1
  have hsupportUpper : (totalTightSupport tightVec block).card ≤ 3 := by
    calc
      (totalTightSupport tightVec block).card ≤ block.card :=
        Finset.card_le_card (totalTightSupport_subset tightVec hblockCard)
      _ = 3 := hblockCard
  have hsupportCases : (totalTightSupport tightVec block).card = 2
      ∨ (totalTightSupport tightVec block).card = 3 := by
    omega
  rcases hsupportCases with hpairSupport | hfullSupport
  · right
    obtain ⟨pairFirst, pairSecond, hpairDistinct, hsupport⟩ :=
      Finset.card_eq_two.mp hpairSupport
    have hfirstMem : pairFirst ∈ totalTightSupport tightVec block := by
      rw [hsupport]
      simp
    have hcoordinate := hrowSpan pairFirst hfirstMem
    obtain ⟨coefficient, hremainingCard, hcoefficientNonzero,
      hcombinationNonzero, hcancellation⟩ :=
      exists_threeActiveEigenSquareRow_cancellation_of_support_pair tightVec hfour
        hblock hblockCard hpairDistinct hsupport hcoordinate
    exact ⟨pairFirst, pairSecond, coefficient, hpairDistinct, hsupport,
      hremainingCard, hcoefficientNonzero, hcombinationNonzero, hcancellation⟩
  · exact Or.inl hfullSupport

end Gtz

import Gtz.Wave.ThreeBlockStationaryClosure
import Gtz.Wave.FourActiveSpine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- **ALL FOUR MULTIPLIERS ARE POSITIVE.**  On the identity-labelled argmax
family of cardinality four, the positive support is a subset of a four-element
set.  The new simple-support floor says it has at least four elements, hence it
is the whole family. -/
theorem SixThreeCrux.activeWeight_pos_of_identity_family_card_four
    (crux : SixThreeCrux)
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    (hfamilyCard :
      (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      0 < multiplier selected := by
  let family := chartArgmaxFamily (chartPointOfDesign crux.design)
  have hsimple : HasSimpleActiveSubsets family
      (id : Finset (Fin 6) → Finset (Fin 6)) := by
    intro firstLabel _ secondLabel _ heq
    exact heq
  have hcardLower := crux.four_le_positiveActiveSet_card_of_simple hdata hsimple
  have hsubset : positiveActiveSet family multiplier ⊆ family :=
    Finset.filter_subset _ _
  have hfamilyLe : family.card ≤ (positiveActiveSet family multiplier).card := by
    rw [hfamilyCard]
    exact hcardLower
  have hpositiveEq : positiveActiveSet family multiplier = family :=
    Finset.eq_of_subset_of_card_le hsubset hfamilyLe
  intro selected hselected
  have hpositiveMem : selected ∈ positiveActiveSet family multiplier := by
    rw [hpositiveEq]
    exact hselected
  exact (Finset.mem_filter.mp hpositiveMem).2

/-- The four-active spine with its previously implicit positivity conclusion
made explicit for downstream support-two elimination. -/
theorem SixThreeCrux.exists_positive_stationary_supportTwo_of_four
    (crux : SixThreeCrux)
    (hfamilyCard :
      (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ∃ (tightVec : Finset (Fin 6) → Fin 3 → ℝ)
      (multiplier : Finset (Fin 6) → ℝ)
      (block : Finset (Fin 6)), block.card = 3
      ∧ (∀ selected : Finset (Fin 6), selected.card = 3 →
        tightVec selected ⬝ᵥ tightVec selected = 1)
      ∧ (∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        Matrix.mulVec ((chartPointGap (chartPointOfDesign crux.design)).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard))
            (tightVec selected) =
          chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
      ∧ IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          (chartArgmaxFamily (chartPointOfDesign crux.design))
          (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
          (ambientTightSelection tightVec)
      ∧ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
      ∧ (∀ atomIndex ∈ totalTightSupport tightVec block,
          Pi.single atomIndex (1 : ℝ) ∈ finiteRowSpan
            (chartArgmaxFamily (chartPointOfDesign crux.design))
            (totalEigenSquareRow tightVec))
      ∧ (totalTightSupport tightVec block).card = 2
      ∧ (∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
          0 < multiplier selected) := by
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata,
    hblockMem, haxes, hsupportTwo⟩ := crux.exists_stationary_supportTwo_of_four hfamilyCard
  exact ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata,
    hblockMem, haxes, hsupportTwo,
    crux.activeWeight_pos_of_identity_family_card_four hdata hfamilyCard⟩


end Gtz

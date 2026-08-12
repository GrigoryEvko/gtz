import Gtz.Wave.StationaryPositiveSupport
import Gtz.Quantitative.TwoBlockEliminationCertificate
import Gtz.Quantitative.SixThreeCrux
import Gtz.Quantitative.ChartDisjointBlockExclusion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- A negative stationary datum carried by a crux cannot have its strictly positive
multiplier support confined to two complementary blocks.  Zero-multiplier active
blocks are discarded before applying the landed two-block exclusion. -/
theorem SixThreeCrux.false_of_positiveActiveSet_twoBlock
    (crux : SixThreeCrux) {activeIndex : Type*}
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (block : Finset (Fin 6))
    (hfamily : IsChartTwoBlockFamily
      (positiveActiveSet activeSet activeWeight) activeSubset block) :
    False := by
  have hrestricted := hdata.restrict_positiveActiveSet
  exact
    (not_isChartStationaryData_of_isChartTwoBlockFamily_of_design_of_negativeValue
      crux.design rfl crux.isChartArgmaxValue hfamily crux.hasNegativeChartValue)
      hrestricted

/-- In particular, the positive multiplier support of a crux stationary datum cannot
have cardinality two.  Coverage makes two active triples complementary, after which
the preceding theorem applies. -/
theorem SixThreeCrux.positiveActiveSet_card_ne_two
    (crux : SixThreeCrux) {activeIndex : Type*}
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir) :
    (positiveActiveSet activeSet activeWeight).card ≠ 2 := by
  classical
  intro hcard
  let positiveSet := positiveActiveSet activeSet activeWeight
  have hrestricted := hdata.restrict_positiveActiveSet
  obtain ⟨first, second, hdistinct, hpair⟩ := Finset.card_eq_two.mp hcard
  have hfirstMem : first ∈ positiveSet := by
    change first ∈ positiveActiveSet activeSet activeWeight
    rw [hpair]
    exact Finset.mem_insert_self _ _
  have hsecondMem : second ∈ positiveSet := by
    change second ∈ positiveActiveSet activeSet activeWeight
    rw [hpair]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hfirstCard : (activeSubset first).card = 3 :=
    hrestricted.activeSubset_card first hfirstMem
  have hsecondCard : (activeSubset second).card = 3 :=
    hrestricted.activeSubset_card second hsecondMem
  have hcovered : (Finset.univ : Finset (Fin 6)) ⊆
      activeSubset first ∪ activeSubset second := by
    intro atomIndex _
    obtain ⟨label, hlabel, hatom⟩ :=
      exists_mem_activeSubset_of_isChartStationaryData hrestricted atomIndex
    rw [hpair] at hlabel
    rcases Finset.mem_insert.mp hlabel with hfirst | hsecond
    · exact Finset.mem_union_left _ (hfirst ▸ hatom)
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mp hsecond ▸ hatom)
  have hunion : activeSubset first ∪ activeSubset second = Finset.univ :=
    Finset.Subset.antisymm (Finset.subset_univ _) hcovered
  have hunionCard : (activeSubset first ∪ activeSubset second).card = 6 := by
    rw [hunion, Finset.card_univ, Fintype.card_fin]
  have hdisjoint : Disjoint (activeSubset first) (activeSubset second) := by
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
    have hinclusionExclusion :=
      Finset.card_union_add_card_inter (activeSubset first) (activeSubset second)
    omega
  have hcomplement : activeSubset second = (activeSubset first)ᶜ :=
    eq_compl_of_disjoint_of_card_add_card_eq_size hdisjoint (by omega)
  have hfamily : IsChartTwoBlockFamily positiveSet activeSubset (activeSubset first) := by
    intro label hlabel
    change label ∈ positiveActiveSet activeSet activeWeight at hlabel
    rw [hpair] at hlabel
    rcases Finset.mem_insert.mp hlabel with hfirst | hsecond
    · exact Or.inl (congrArg activeSubset hfirst)
    · exact Or.inr ((congrArg activeSubset (Finset.mem_singleton.mp hsecond)).trans
        hcomplement)
  exact crux.false_of_positiveActiveSet_twoBlock hdata (activeSubset first) hfamily

/-- Every stationary assembly at a crux uses at least three strictly positive
multipliers.  Coverage gives the lower bound two; the two-block exclusion makes it
strict. -/
theorem SixThreeCrux.three_le_positiveActiveSet_card
    (crux : SixThreeCrux) {activeIndex : Type*}
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir) :
    3 ≤ (positiveActiveSet activeSet activeWeight).card := by
  have hrestricted := hdata.restrict_positiveActiveSet
  have hcoverage := size_le_rank_mul_card_activeSet_of_isChartStationaryData hrestricted
  have hnotTwo := crux.positiveActiveSet_card_ne_two hdata
  omega


end Gtz

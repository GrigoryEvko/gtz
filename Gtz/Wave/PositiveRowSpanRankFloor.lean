import Gtz.Wave.ComplementRankOneCapture
import Gtz.Wave.StationaryPositiveSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace Gtz

open Matrix Finset

/-- At a negative `(6,3)` crux, the tight directions carrying positive
stationary multiplier span a space of dimension at least four.

The primal and Naimark-complement captured assemblies both have rank at least
two.  Their ranges are disjoint, and both ranges lie in the positive tight-row
span. -/
theorem SixThreeCrux.four_le_positiveTightRowSpan_finrank
    (crux : SixThreeCrux)
    {activeIndex : Type*}
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir) :
    4 ≤ Module.finrank ℝ (Submodule.span ℝ
      (↑((positiveActiveSet activeSet activeWeight).image tightDir) : Set (Fin 6 → ℝ))) := by
  classical
  let positiveSet := positiveActiveSet activeSet activeWeight
  let projection := (chartPointOfDesign crux.design).chart
  let assembly := chartMultiplierAssembly positiveSet activeWeight tightDir
  let rows := positiveSet.image tightDir
  let rowSpan := Submodule.span ℝ (↑rows : Set (Fin 6 → ℝ))
  let primalRange := LinearMap.range (Matrix.toLin' (projection * assembly))
  let complementRange := LinearMap.range (Matrix.toLin' ((1 - projection) * assembly))
  have hpositiveData : IsChartStationaryData 3 projection
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      positiveSet activeSubset activeWeight tightDir := by
    simpa only [positiveSet, projection] using hdata.restrict_positiveActiveSet
  have hpositive : ∀ activeLabel ∈ positiveSet, 0 < activeWeight activeLabel := by
    intro activeLabel hmem
    have hmem' : activeLabel ∈ activeSet ∧ 0 < activeWeight activeLabel := by
      simpa only [positiveSet, positiveActiveSet, Finset.mem_filter] using hmem
    exact hmem'.2
  have hcommutes : projection * assembly = assembly * projection := by
    simpa only [projection, assembly] using hpositiveData.assembly_commutes
  have hassemblyRange : LinearMap.range (Matrix.toLin' assembly) ≤ rowSpan := by
    intro vector hvector
    rcases hvector with ⟨preimage, hpreimage⟩
    rw [Matrix.toLin'_apply] at hpreimage
    rw [← hpreimage]
    dsimp only [assembly]
    rw [chartMultiplierAssembly, Matrix.sum_mulVec]
    apply Submodule.sum_mem
    intro activeLabel hmem
    rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul, smul_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp only [rows, Finset.mem_coe, Finset.mem_image]
    exact ⟨activeLabel, hmem, rfl⟩
  have hprimalRange : primalRange ≤ rowSpan := by
    intro vector hvector
    rcases hvector with ⟨preimage, hpreimage⟩
    rw [Matrix.toLin'_apply] at hpreimage
    apply hassemblyRange
    refine ⟨projection *ᵥ preimage, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hcommutes]
    exact hpreimage
  have hcomplementCommutes :
      (1 - projection) * assembly = assembly * (1 - projection) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hcommutes]
  have hcomplementRange : complementRange ≤ rowSpan := by
    intro vector hvector
    rcases hvector with ⟨preimage, hpreimage⟩
    rw [Matrix.toLin'_apply] at hpreimage
    apply hassemblyRange
    refine ⟨(1 - projection) *ᵥ preimage, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hcomplementCommutes]
    exact hpreimage
  have hprojectionComplement :
      projection * (1 - projection) = (0 : Matrix (Fin 6) (Fin 6) ℝ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hpositiveData.isIdempotent, sub_self]
  have hdisjoint : Disjoint primalRange complementRange := by
    rw [Submodule.disjoint_def]
    intro vector hprimal hcomplement
    rcases hprimal with ⟨primalPreimage, hprimalEq⟩
    rcases hcomplement with ⟨complementPreimage, hcomplementEq⟩
    rw [Matrix.toLin'_apply] at hprimalEq hcomplementEq
    have hfixed : projection *ᵥ vector = vector := by
      rw [← hprimalEq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
        hpositiveData.isIdempotent]
    have hkilled : projection *ᵥ vector = 0 := by
      rw [← hcomplementEq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
        hprojectionComplement, Matrix.zero_mul, Matrix.zero_mulVec]
    exact hfixed.symm.trans hkilled
  have hprimalDim : 2 ≤ Module.finrank ℝ primalRange := by
    have hnot := crux.not_projectedMultiplier_range_finrank_le_one hpositiveData
    change ¬ Module.finrank ℝ primalRange ≤ 1 at hnot
    omega
  have hcomplementDim : 2 ≤ Module.finrank ℝ complementRange := by
    have hnot := crux.not_complementProjectedMultiplier_range_finrank_le_one
      hpositiveData
    change ¬ Module.finrank ℝ complementRange ≤ 1 at hnot
    omega
  have hsupLe : primalRange ⊔ complementRange ≤ rowSpan :=
    sup_le hprimalRange hcomplementRange
  have hdimension :=
    Submodule.finrank_sup_add_finrank_inf_eq primalRange complementRange
  rw [hdisjoint.eq_bot, finrank_bot, add_zero] at hdimension
  have hfourLeSup : 4 ≤ Module.finrank ℝ
      (primalRange ⊔ complementRange : Submodule ℝ (Fin 6 → ℝ)) := by
    omega
  have hfourLeRowSpan : 4 ≤ Module.finrank ℝ rowSpan :=
    hfourLeSup.trans (Submodule.finrank_mono hsupLe)
  simpa only [rowSpan, rows, positiveSet] using hfourLeRowSpan


end Gtz

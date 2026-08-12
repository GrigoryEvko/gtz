import Gtz.Wave.ComplementRankOneCapture
import Gtz.Wave.FourActivePositiveMultipliers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace Gtz

open Matrix Finset
open scoped BigOperators

/-- **THE FOUR-ROW RANK SPLIT.**  At a negative `(6,3)` crux, a stationary
assembly supported by exactly four positive tight rows has four-dimensional row
span, and its two commuting corners have ranks exactly two and two.

The proof is dimension bookkeeping with two nontrivial inputs: primal rank one
is excluded by the captured mass transport, and complementary rank one is
excluded by its Naimark-dual transport. -/
theorem SixThreeCrux.fourRowSpan_and_capturedRanks
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
      activeSet activeSubset activeWeight tightDir)
    (hactiveCard : activeSet.card = 4)
    (_hactiveWeightPositive : ∀ activeLabel ∈ activeSet,
      0 < activeWeight activeLabel) :
    let assembly := chartMultiplierAssembly activeSet activeWeight tightDir
    let rowSpan := Submodule.span ℝ
      (↑(activeSet.image tightDir) : Set (Fin 6 → ℝ))
    Module.finrank ℝ rowSpan = 4
      ∧ Module.finrank ℝ (LinearMap.range
        (Matrix.toLin' ((chartPointOfDesign crux.design).chart * assembly))) = 2
      ∧ Module.finrank ℝ (LinearMap.range
        (Matrix.toLin' ((1 - (chartPointOfDesign crux.design).chart) * assembly))) = 2 := by
  classical
  let projection := (chartPointOfDesign crux.design).chart
  let assembly := chartMultiplierAssembly activeSet activeWeight tightDir
  let rows := activeSet.image tightDir
  let rowSpan := Submodule.span ℝ (↑rows : Set (Fin 6 → ℝ))
  let primalRange := LinearMap.range (Matrix.toLin' (projection * assembly))
  let kernelRange := LinearMap.range (Matrix.toLin' ((1 - projection) * assembly))
  have hprojectionIdempotent : projection * projection = projection := by
    simpa only [projection] using hdata.isIdempotent
  have hcommutes : projection * assembly = assembly * projection := by
    simpa only [projection, assembly] using hdata.assembly_commutes
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
    dsimp only [projection, assembly]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      hdata.assembly_commutes]
  have hkernelRange : kernelRange ≤ rowSpan := by
    intro vector hvector
    rcases hvector with ⟨preimage, hpreimage⟩
    rw [Matrix.toLin'_apply] at hpreimage
    apply hassemblyRange
    refine ⟨(1 - projection) *ᵥ preimage, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hcomplementCommutes]
    exact hpreimage
  have hprojectionComplement :
      projection * (1 - projection) = (0 : Matrix (Fin 6) (Fin 6) ℝ) := by
    dsimp only [projection]
    rw [Matrix.mul_sub, Matrix.mul_one, hdata.isIdempotent, sub_self]
  have hdisjoint : Disjoint primalRange kernelRange := by
    rw [Submodule.disjoint_def]
    intro vector hprimal hkernel
    rcases hprimal with ⟨primalPreimage, hprimalEq⟩
    rcases hkernel with ⟨kernelPreimage, hkernelEq⟩
    rw [Matrix.toLin'_apply] at hprimalEq hkernelEq
    have hfixed : projection *ᵥ vector = vector := by
      rw [← hprimalEq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
        hprojectionIdempotent]
    have hkilled : projection *ᵥ vector = 0 := by
      rw [← hkernelEq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
        hprojectionComplement, Matrix.zero_mul, Matrix.zero_mulVec]
    exact hfixed.symm.trans hkilled
  have hrowSpanDimLe : Module.finrank ℝ rowSpan ≤ 4 := by
    have hspanCard := finrank_span_finset_le_card (R := ℝ) rows
    have hrowsCard : rows.card ≤ 4 := by
      exact (Finset.card_image_le).trans_eq hactiveCard
    exact hspanCard.trans hrowsCard
  have hprimalDimGe : 2 ≤ Module.finrank ℝ primalRange := by
    have hnot := crux.not_projectedMultiplier_range_finrank_le_one hdata
    change ¬ Module.finrank ℝ primalRange ≤ 1 at hnot
    omega
  have hkernelDimGe : 2 ≤ Module.finrank ℝ kernelRange := by
    have hnot := crux.not_complementProjectedMultiplier_range_finrank_le_one hdata
    change ¬ Module.finrank ℝ kernelRange ≤ 1 at hnot
    omega
  have hsupLe : primalRange ⊔ kernelRange ≤ rowSpan :=
    sup_le hprimalRange hkernelRange
  have hsupDimLe : Module.finrank ℝ
      (primalRange ⊔ kernelRange : Submodule ℝ (Fin 6 → ℝ)) ≤ 4 :=
    (Submodule.finrank_mono hsupLe).trans hrowSpanDimLe
  have hdimension :=
    Submodule.finrank_sup_add_finrank_inf_eq primalRange kernelRange
  rw [hdisjoint.eq_bot, finrank_bot, add_zero] at hdimension
  have hprimalDim : Module.finrank ℝ primalRange = 2 := by omega
  have hkernelDim : Module.finrank ℝ kernelRange = 2 := by omega
  have hsupDim : Module.finrank ℝ
      (primalRange ⊔ kernelRange : Submodule ℝ (Fin 6 → ℝ)) = 4 := by omega
  have hrowSpanDimGe : 4 ≤ Module.finrank ℝ rowSpan := by
    rw [← hsupDim]
    exact Submodule.finrank_mono hsupLe
  have hrowSpanDim : Module.finrank ℝ rowSpan = 4 := by omega
  simpa only [assembly, rowSpan, rows, primalRange, kernelRange, projection] using
    ⟨hrowSpanDim, hprimalDim, hkernelDim⟩


end Gtz

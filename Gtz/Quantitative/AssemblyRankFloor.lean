import Mathlib
import Gtz.Quantitative.CapturedRankFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The assembly rank floor — every crux assembly has rank at least four

The two captured corners of a stationary assembly live inside the assembly's own
range, they meet trivially (one is chart-fixed, the other chart-annihilated), and
at a `(6,3)` crux neither has rank at most one (`Gtz.Quantitative.CapturedRankFloor`).
So the assembly's range has dimension at least four — at EVERY stationary datum a
crux produces, at every active count, with no multiplier positivity anywhere.

At exactly four active blocks the floor saturates everything at once: the
assembly is a sum of four rank-one terms, so the floor forces ALL FOUR multipliers
positive and the four tight directions independent, and the corner dimensions
pinch to exactly `(2, 2)` — the coefficient projection of the four-active leaf
census has trace two.  These four-active corollaries subsume the earlier
positive-support and rank-split routes in one dimension count.
-/

namespace Gtz

open Matrix

variable {activeIndex : Type*}
variable {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin 6)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)}

/-- The assembly's range lies in the span of the active tight directions. -/
theorem range_multiplier_le_span_tightDir {size : ℕ} {activeIndex : Type*}
    (activeSet : Finset activeIndex) (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → (Fin size → ℝ)) :
    LinearMap.range (Matrix.toLin' (chartMultiplierAssembly activeSet activeWeight tightDir))
      ≤ Submodule.span ℝ (↑(activeSet.image tightDir) : Set (Fin size → ℝ)) := by
  classical
  intro vector hvector
  rcases hvector with ⟨preimage, hpreimage⟩
  rw [Matrix.toLin'_apply] at hpreimage
  rw [← hpreimage, chartMultiplierAssembly, Matrix.sum_mulVec]
  apply Submodule.sum_mem
  intro activeLabel hmem
  rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul, smul_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨activeLabel, hmem, rfl⟩

/-- The assembly's range lies in the span of the POSITIVELY WEIGHTED tight
directions: zero-multiplier terms contribute the zero matrix. -/
theorem range_multiplier_le_span_positive_tightDir {size : ℕ} {activeIndex : Type*}
    (activeSet : Finset activeIndex) (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → (Fin size → ℝ)) :
    LinearMap.range (Matrix.toLin' (chartMultiplierAssembly activeSet activeWeight tightDir))
      ≤ Submodule.span ℝ
          (↑((activeSet.filter (fun activeLabel => activeWeight activeLabel ≠ 0)).image
            tightDir) : Set (Fin size → ℝ)) := by
  classical
  intro vector hvector
  rcases hvector with ⟨preimage, hpreimage⟩
  rw [Matrix.toLin'_apply] at hpreimage
  rw [← hpreimage, chartMultiplierAssembly, Matrix.sum_mulVec]
  apply Submodule.sum_mem
  intro activeLabel hmem
  by_cases hzero : activeWeight activeLabel = 0
  · rw [hzero, zero_smul, Matrix.zero_mulVec]
    exact Submodule.zero_mem _
  · rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul, smul_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
    exact ⟨activeLabel, ⟨hmem, hzero⟩, rfl⟩

/-- Both captured corners live inside the assembly's range, because the corner
factors as the assembly times the projection on the other side. -/
theorem range_projection_mul_multiplier_le_range_multiplier {size : ℕ} {activeIndex : Type*}
    {projection : Matrix (Fin size) (Fin size) ℝ}
    {activeSet : Finset activeIndex} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hcommutes : projection * chartMultiplierAssembly activeSet activeWeight tightDir
      = chartMultiplierAssembly activeSet activeWeight tightDir * projection) :
    LinearMap.range (Matrix.toLin'
        (projection * chartMultiplierAssembly activeSet activeWeight tightDir))
      ≤ LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)) := by
  rw [hcommutes, Matrix.toLin'_mul]
  exact LinearMap.range_comp_le_range _ _

/-- **THE ASSEMBLY RANK FLOOR.**  At a `(6,3)` crux every stationary assembly has
range dimension at least four — at every active count and every multiplier
support, with no positivity hypothesis. -/
theorem SixThreeCrux.four_le_finrank_range_multiplier
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir) :
    4 ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      (chartMultiplierAssembly activeSet activeWeight tightDir))) := by
  classical
  set projection := (chartPointOfDesign crux.design).chart with hprojectionDef
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir with hassemblyDef
  have hcommutes : projection * assembly = assembly * projection := hdata.assembly_commutes
  have hcomplementCommutes : (1 - projection) * assembly = assembly * (1 - projection) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hcommutes]
  have hprimalLe : LinearMap.range (Matrix.toLin' (projection * assembly))
      ≤ LinearMap.range (Matrix.toLin' assembly) :=
    range_projection_mul_multiplier_le_range_multiplier hcommutes
  have hkernelLe : LinearMap.range (Matrix.toLin' ((1 - projection) * assembly))
      ≤ LinearMap.range (Matrix.toLin' assembly) :=
    range_projection_mul_multiplier_le_range_multiplier hcomplementCommutes
  have hprojectionComplement :
      projection * (1 - projection) = (0 : Matrix (Fin 6) (Fin 6) ℝ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hdata.isIdempotent, sub_self]
  have hdisjoint : Disjoint
      (LinearMap.range (Matrix.toLin' (projection * assembly)))
      (LinearMap.range (Matrix.toLin' ((1 - projection) * assembly))) := by
    rw [Submodule.disjoint_def]
    intro vector hprimal hkernel
    rcases hprimal with ⟨primalPreimage, hprimalEq⟩
    rcases hkernel with ⟨kernelPreimage, hkernelEq⟩
    rw [Matrix.toLin'_apply] at hprimalEq hkernelEq
    have hfixed : projection *ᵥ vector = vector := by
      rw [← hprimalEq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hdata.isIdempotent]
    have hkilled : projection *ᵥ vector = 0 := by
      rw [← hkernelEq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hprojectionComplement,
        Matrix.zero_mul, Matrix.zero_mulVec]
    exact hfixed.symm.trans hkilled
  have hprimalGe : 2 ≤ Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' (projection * assembly))) := by
    have hnot := crux.not_projectedMultiplier_range_finrank_le_one hdata
    rw [← hprojectionDef, ← hassemblyDef] at hnot
    omega
  have hkernelGe : 2 ≤ Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' ((1 - projection) * assembly))) := by
    have hnot := crux.not_complementProjectedMultiplier_range_finrank_le_one hdata
    rw [← hprojectionDef, ← hassemblyDef] at hnot
    omega
  have hsupLe : LinearMap.range (Matrix.toLin' (projection * assembly))
        ⊔ LinearMap.range (Matrix.toLin' ((1 - projection) * assembly))
      ≤ LinearMap.range (Matrix.toLin' assembly) := sup_le hprimalLe hkernelLe
  have hdimension := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (Matrix.toLin' (projection * assembly)))
    (LinearMap.range (Matrix.toLin' ((1 - projection) * assembly)))
  rw [hdisjoint.eq_bot, finrank_bot, add_zero] at hdimension
  have hmono := Submodule.finrank_mono hsupLe
  omega

/-- **ALL MULTIPLIERS ARE POSITIVE AT FOUR ACTIVE BLOCKS.**  A vanishing
multiplier would leave at most three rank-one terms, capping the assembly's rank
at three below the floor. -/
theorem SixThreeCrux.activeWeight_pos_of_card_eq_four
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hactiveCard : activeSet.card = 4) :
    ∀ activeLabel ∈ activeSet, 0 < activeWeight activeLabel := by
  classical
  intro selectedLabel hselectedMem
  rcases lt_or_eq_of_le (hdata.activeWeight_nonneg selectedLabel hselectedMem) with
    hpositive | hzero
  · exact hpositive
  have hfloor := crux.four_le_finrank_range_multiplier hdata
  have hspanLe := range_multiplier_le_span_positive_tightDir activeSet activeWeight tightDir
  have hfilterSubset : activeSet.filter (fun activeLabel => activeWeight activeLabel ≠ 0)
      ⊆ activeSet.erase selectedLabel := by
    intro activeLabel hmem
    rcases Finset.mem_filter.mp hmem with ⟨hmemActive, hnonzero⟩
    refine Finset.mem_erase.mpr ⟨?_, hmemActive⟩
    intro hcontra
    apply hnonzero
    rw [hcontra]
    exact hzero.symm
  have hfilterCard : (activeSet.filter
      (fun activeLabel => activeWeight activeLabel ≠ 0)).card ≤ 3 := by
    have hcardErase := Finset.card_erase_of_mem hselectedMem
    have hle := Finset.card_le_card hfilterSubset
    omega
  have hspanCard := finrank_span_finset_le_card (R := ℝ)
    ((activeSet.filter (fun activeLabel => activeWeight activeLabel ≠ 0)).image tightDir)
  have himageCard : ((activeSet.filter
        (fun activeLabel => activeWeight activeLabel ≠ 0)).image tightDir).card ≤ 3 :=
    Finset.card_image_le.trans hfilterCard
  have hrankLe := (Submodule.finrank_mono hspanLe).trans (hspanCard.trans himageCard)
  omega

/-- **THE FOUR-ACTIVE ROW SPAN AND THE CAPTURED RANKS.**  At exactly four active
blocks the four tight directions span a four-dimensional space and the two
captured corners have ranks exactly two and two — with positivity DERIVED, not
hypothesised. -/
theorem SixThreeCrux.fourRowSpan_and_capturedRanks_of_card_eq_four
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hactiveCard : activeSet.card = 4) :
    Module.finrank ℝ (Submodule.span ℝ
        (↑(activeSet.image tightDir) : Set (Fin 6 → ℝ))) = 4
      ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
          ((chartPointOfDesign crux.design).chart
            * chartMultiplierAssembly activeSet activeWeight tightDir))) = 2
      ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
          ((1 - (chartPointOfDesign crux.design).chart)
            * chartMultiplierAssembly activeSet activeWeight tightDir))) = 2 := by
  classical
  set projection := (chartPointOfDesign crux.design).chart with hprojectionDef
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir with hassemblyDef
  have hfloor := crux.four_le_finrank_range_multiplier hdata
  rw [← hassemblyDef] at hfloor
  have hcommutes : projection * assembly = assembly * projection := hdata.assembly_commutes
  have hcomplementCommutes : (1 - projection) * assembly = assembly * (1 - projection) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hcommutes]
  have hprimalLe : LinearMap.range (Matrix.toLin' (projection * assembly))
      ≤ LinearMap.range (Matrix.toLin' assembly) :=
    range_projection_mul_multiplier_le_range_multiplier hcommutes
  have hkernelLe : LinearMap.range (Matrix.toLin' ((1 - projection) * assembly))
      ≤ LinearMap.range (Matrix.toLin' assembly) :=
    range_projection_mul_multiplier_le_range_multiplier hcomplementCommutes
  have hspanLe := range_multiplier_le_span_tightDir activeSet activeWeight tightDir
  rw [← hassemblyDef] at hspanLe
  have hspanCardLe : Module.finrank ℝ (Submodule.span ℝ
      (↑(activeSet.image tightDir) : Set (Fin 6 → ℝ))) ≤ 4 := by
    have hspanCard := finrank_span_finset_le_card (R := ℝ) (activeSet.image tightDir)
    have himageCard : (activeSet.image tightDir).card ≤ 4 :=
      Finset.card_image_le.trans_eq hactiveCard
    exact hspanCard.trans himageCard
  have hrangeLeSpan : Module.finrank ℝ (LinearMap.range (Matrix.toLin' assembly))
      ≤ Module.finrank ℝ (Submodule.span ℝ
          (↑(activeSet.image tightDir) : Set (Fin 6 → ℝ))) :=
    Submodule.finrank_mono hspanLe
  have hprojectionComplement :
      projection * (1 - projection) = (0 : Matrix (Fin 6) (Fin 6) ℝ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hdata.isIdempotent, sub_self]
  have hdisjoint : Disjoint
      (LinearMap.range (Matrix.toLin' (projection * assembly)))
      (LinearMap.range (Matrix.toLin' ((1 - projection) * assembly))) := by
    rw [Submodule.disjoint_def]
    intro vector hprimal hkernel
    rcases hprimal with ⟨primalPreimage, hprimalEq⟩
    rcases hkernel with ⟨kernelPreimage, hkernelEq⟩
    rw [Matrix.toLin'_apply] at hprimalEq hkernelEq
    have hfixed : projection *ᵥ vector = vector := by
      rw [← hprimalEq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hdata.isIdempotent]
    have hkilled : projection *ᵥ vector = 0 := by
      rw [← hkernelEq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hprojectionComplement,
        Matrix.zero_mul, Matrix.zero_mulVec]
    exact hfixed.symm.trans hkilled
  have hprimalGe : 2 ≤ Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' (projection * assembly))) := by
    have hnot := crux.not_projectedMultiplier_range_finrank_le_one hdata
    rw [← hprojectionDef, ← hassemblyDef] at hnot
    omega
  have hkernelGe : 2 ≤ Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' ((1 - projection) * assembly))) := by
    have hnot := crux.not_complementProjectedMultiplier_range_finrank_le_one hdata
    rw [← hprojectionDef, ← hassemblyDef] at hnot
    omega
  have hsupLe : LinearMap.range (Matrix.toLin' (projection * assembly))
        ⊔ LinearMap.range (Matrix.toLin' ((1 - projection) * assembly))
      ≤ LinearMap.range (Matrix.toLin' assembly) := sup_le hprimalLe hkernelLe
  have hdimension := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (Matrix.toLin' (projection * assembly)))
    (LinearMap.range (Matrix.toLin' ((1 - projection) * assembly)))
  rw [hdisjoint.eq_bot, finrank_bot, add_zero] at hdimension
  have hsupMono := Submodule.finrank_mono hsupLe
  refine ⟨?_, ?_, ?_⟩ <;> omega

end Gtz

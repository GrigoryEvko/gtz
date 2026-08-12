import Gtz.Wave.KernelDependencyParallelPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! **THE RESIDUAL ROWS INHERIT A THREE-DIMENSIONAL FLOOR.**  Removing one
block from a card-four crux family costs the four-dimensional positive-row-span
floor at most one dimension, so the remaining three tight rows span at least
three dimensions.  In the triangle-plus-full disconnected profiles the three
residual rows live inside the three off-block coordinates, so they span that
coordinate space exactly — the input both to the cross-block vanishing step and
to the coefficient-independence step of the full-row driver. -/

/-- Erasing one block leaves a three-dimensional row span. -/
theorem SixThreeCrux.three_le_finrank_span_erase_of_card_four
    (crux : SixThreeCrux)
    {multiplier : Finset (Fin 6) → ℝ} {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    {hostBlock : Finset (Fin 6)}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    (hhostMem : hostBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design)) :
    3 ≤ Module.finrank ℝ (Submodule.span ℝ
      (((chartArgmaxFamily (chartPointOfDesign crux.design)).erase hostBlock).image
          tightDir : Set (Fin 6 → ℝ))) := by
  classical
  set family := chartArgmaxFamily (chartPointOfDesign crux.design)
  have hfloor := crux.four_le_positiveTightRowSpan_finrank hdata
  have hposSubset : positiveActiveSet family multiplier ⊆ family :=
    Finset.filter_subset _ _
  have hspanMono : Submodule.span ℝ
      (((positiveActiveSet family multiplier).image tightDir : Finset (Fin 6 → ℝ))
        : Set (Fin 6 → ℝ))
      ≤ Submodule.span ℝ ((family.image tightDir : Finset (Fin 6 → ℝ))
        : Set (Fin 6 → ℝ)) :=
    Submodule.span_mono (by
      intro row hrow
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hrow ⊢
      obtain ⟨block, hblockPos, rfl⟩ := hrow
      exact ⟨block, hposSubset hblockPos, rfl⟩)
  have hfamilyFloor : 4 ≤ Module.finrank ℝ (Submodule.span ℝ
      ((family.image tightDir : Finset (Fin 6 → ℝ)) : Set (Fin 6 → ℝ))) :=
    le_trans hfloor (Submodule.finrank_mono hspanMono)
  have hfamilyEq : family = insert hostBlock (family.erase hostBlock) :=
    (Finset.insert_erase hhostMem).symm
  have himageEq : (family.image tightDir : Finset (Fin 6 → ℝ))
      = insert (tightDir hostBlock) ((family.erase hostBlock).image tightDir) := by
    have hcongr := congrArg (Finset.image tightDir) hfamilyEq
    rw [Finset.image_insert] at hcongr
    exact hcongr
  rw [himageEq, Finset.coe_insert, Submodule.span_insert] at hfamilyFloor
  have hadditive := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ ({tightDir hostBlock} : Set (Fin 6 → ℝ)))
    (Submodule.span ℝ (((family.erase hostBlock).image tightDir
      : Finset (Fin 6 → ℝ)) : Set (Fin 6 → ℝ)))
  have hsingletonRank : Module.finrank ℝ (Submodule.span ℝ
      ({tightDir hostBlock} : Set (Fin 6 → ℝ))) ≤ 1 := by
    rcases eq_or_ne (tightDir hostBlock) 0 with hzero | hnonzero
    · rw [hzero, Submodule.span_zero_singleton]
      rw [finrank_bot]
      omega
    · rw [finrank_span_singleton hnonzero]
  omega

end Gtz

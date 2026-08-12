import Gtz.Wave.AssemblyBasisEnumeration

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The rank-four normal form — the interface of the first rank rung

A `(6,3)` crux datum whose assembly has rank FOUR reduces to one package:
a support-minimal multiplier with the same assembly, four positive labels
whose directions are a basis of `range Ξ`, and the coefficient coordinates
`L`, `M`, `H` with every landed law — including `tr M = 2`, the rank-four
read of the survivor list.  The per-pattern work of the rank-four rung
consumes THIS statement and nothing upstream of it.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.SixThreeCrux.exists_rankFour_coefficient_normalForm` — **THE NORMAL
  FORM.**  Fourteen simultaneous facts at every rank-four crux datum,
  with the basis span law that feeds the reconstruction and the circuit
  equations.

## Vacuity

The statement is quantified over a crux and is vacuous if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

variable {activeIndex : Type*}

/-- **THE RANK-FOUR NORMAL FORM.**  Every rank-four crux datum carries a
support-minimal multiplier with the same assembly, an injective four-label
basis inside its positive support, and coefficient coordinates `L`, `M`, `H`
with

    `L B = 1`,  `P B = B M`,  `M² = M`,  `B H Bᵀ = Ξ`,  `Hᵀ = H`,
    `H ⪰ 0`,  `ker H = 0`,  `M H = H Mᵀ`,  `tr M = 2`. -/
theorem SixThreeCrux.exists_rankFour_coefficient_normalForm
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
    (hrankFour : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir))) = 4) :
    ∃ (reducedWeight : activeIndex → ℝ)
      (basisLabel : Fin 4 → activeIndex)
      (L : Matrix (Fin 4) (Fin 6) ℝ) (M H : Matrix (Fin 4) (Fin 4) ℝ),
      IsChartStationaryData 3
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          activeSet activeSubset reducedWeight tightDir
        ∧ chartMultiplierAssembly activeSet reducedWeight tightDir
            = chartMultiplierAssembly activeSet activeWeight tightDir
        ∧ Function.Injective basisLabel
        ∧ (∀ columnIndex, basisLabel columnIndex
            ∈ positiveActiveSet activeSet reducedWeight)
        ∧ Submodule.span ℝ
              (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
            = LinearMap.range (Matrix.toLin'
                (chartMultiplierAssembly activeSet reducedWeight tightDir))
        ∧ L * tightBasisColumns tightDir basisLabel = 1
        ∧ (chartPointOfDesign crux.design).chart * tightBasisColumns tightDir basisLabel
            = tightBasisColumns tightDir basisLabel * M
        ∧ M * M = M
        ∧ tightBasisColumns tightDir basisLabel * H
              * (tightBasisColumns tightDir basisLabel)ᵀ
            = chartMultiplierAssembly activeSet reducedWeight tightDir
        ∧ Hᵀ = H
        ∧ H.PosSemidef
        ∧ (∀ coeffVec : Fin 4 → ℝ, H *ᵥ coeffVec = 0 → coeffVec = 0)
        ∧ M * H = H * Mᵀ
        ∧ Matrix.trace M = 2 := by
  classical
  -- the support-minimal reduction, assembly unchanged
  obtain ⟨reducedWeight, hreducedData, hassemblyEq, -⟩ :=
    exists_isChartStationaryData_independent_positive_support hdata
  have hrankReduced : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      (chartMultiplierAssembly activeSet reducedWeight tightDir))) = 4 := by
    rw [hassemblyEq]
    exact hrankFour
  -- the enumerated basis of the reduced assembly's range
  obtain ⟨basisLabelEnum, hinjectiveEnum, hmemEnum, hindepEnum, hspanEnum⟩ :=
    exists_enumerated_basis_of_isChartStationaryData hreducedData
  -- transport the index type along the rank-four equation
  obtain ⟨basisLabel, hbasisLabelDef⟩ :
      ∃ basisLabel : Fin 4 → activeIndex,
        basisLabel = fun columnIndex =>
          basisLabelEnum (Fin.cast hrankReduced.symm columnIndex) := ⟨_, rfl⟩
  have hinjective : Function.Injective basisLabel := by
    intro firstIndex secondIndex hcollide
    rw [hbasisLabelDef] at hcollide
    exact Fin.cast_injective hrankReduced.symm (hinjectiveEnum hcollide)
  have hmem : ∀ columnIndex, basisLabel columnIndex
      ∈ positiveActiveSet activeSet reducedWeight := by
    intro columnIndex
    rw [hbasisLabelDef]
    exact hmemEnum _
  have hindep : LinearIndependent ℝ
      (fun columnIndex => tightDir (basisLabel columnIndex)) := by
    have hcomposed := hindepEnum.comp (Fin.cast hrankReduced.symm)
      (Fin.cast_injective hrankReduced.symm)
    have hfamilyEq : (fun columnIndex => tightDir (basisLabel columnIndex))
        = (fun columnIndex => tightDir (basisLabelEnum columnIndex))
          ∘ (Fin.cast hrankReduced.symm) := by
      funext columnIndex
      rw [hbasisLabelDef]
      rfl
    rw [hfamilyEq]
    exact hcomposed
  have hspan : Submodule.span ℝ
      (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet reducedWeight tightDir)) := by
    have hrangeEq : (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
        = Set.range fun columnIndex => tightDir (basisLabelEnum columnIndex) := by
      have hcastSurjective : Function.Surjective (Fin.cast hrankReduced.symm) :=
        fun columnIndex => ⟨Fin.cast hrankReduced columnIndex, rfl⟩
      have hfamilyEq : (fun columnIndex => tightDir (basisLabel columnIndex))
          = (fun columnIndex => tightDir (basisLabelEnum columnIndex))
            ∘ (Fin.cast hrankReduced.symm) := by
        funext columnIndex
        rw [hbasisLabelDef]
        rfl
      rw [hfamilyEq]
      exact hcastSurjective.range_comp _
    rw [hrangeEq]
    exact hspanEnum
  -- the coefficient coordinates
  set B := tightBasisColumns tightDir basisLabel with hBdef
  set assembly := chartMultiplierAssembly activeSet reducedWeight tightDir with hassemblyDef
  have hsymmAssembly : assemblyᵀ = assembly :=
    transpose_chartMultiplierAssembly_of_isChartStationaryData hreducedData
  have hrangeB : LinearMap.range (Matrix.toLin' B)
      = LinearMap.range (Matrix.toLin' assembly) :=
    range_tightBasisColumns_eq basisLabel hspan
  obtain ⟨L, hleft⟩ := exists_leftInverse_tightBasisColumns basisLabel hindep hspan
  have hrepresentation : (chartPointOfDesign crux.design).chart * B
      = B * (L * ((chartPointOfDesign crux.design).chart * B)) :=
    (mul_leftInverse_mul_eq_of_range_le B L
      ((chartPointOfDesign crux.design).chart * B) hleft
      (range_mul_le_of_commutes_of_range_eq hreducedData basisLabel hrangeB)).symm
  have hidempotent : (L * ((chartPointOfDesign crux.design).chart * B))
      * (L * ((chartPointOfDesign crux.design).chart * B))
      = L * ((chartPointOfDesign crux.design).chart * B) :=
    coefficient_idempotent_of_leftInverse (chartPointOfDesign crux.design).chart B L
      (L * ((chartPointOfDesign crux.design).chart * B))
      hleft hreducedData.isIdempotent hrepresentation
  -- the H-form
  have habsorbAssembly : B * (L * assembly) = assembly := by
    refine mul_leftInverse_mul_eq_of_range_le B L assembly hleft ?_
    rw [hrangeB]
  have habsorbAssemblyL : B * (L * (assembly * Lᵀ)) = assembly * Lᵀ := by
    refine mul_leftInverse_mul_eq_of_range_le B L (assembly * Lᵀ) hleft ?_
    rw [hrangeB, Matrix.toLin'_mul]
    exact LinearMap.range_comp_le_range _ _
  have habsorbRight : assembly * Lᵀ * Bᵀ = assembly := by
    have htransposed := congrArg Matrix.transpose habsorbAssembly
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hsymmAssembly] at htransposed
    exact htransposed
  have hHform : B * (L * assembly * Lᵀ) * Bᵀ = assembly := by
    calc B * (L * assembly * Lᵀ) * Bᵀ
        = B * (L * (assembly * Lᵀ)) * Bᵀ := by rw [Matrix.mul_assoc L assembly Lᵀ]
      _ = assembly * Lᵀ * Bᵀ := by rw [habsorbAssemblyL]
      _ = assembly := habsorbRight
  have hsymmH : (L * assembly * Lᵀ)ᵀ = L * assembly * Lᵀ := by
    calc (L * assembly * Lᵀ)ᵀ
        = Lᵀᵀ * (L * assembly)ᵀ := Matrix.transpose_mul _ _
      _ = L * assembly * Lᵀ := by
          rw [Matrix.transpose_transpose, Matrix.transpose_mul, hsymmAssembly,
            Matrix.mul_assoc]
  -- the trace at rank four
  have htrace : Matrix.trace (L * ((chartPointOfDesign crux.design).chart * B)) = 2 := by
    rw [coefficient_trace_eq_capturedRank hreducedData basisLabel hspan L hleft]
    have hsurvivors := crux.multiplierAssembly_rankSplit_survivors hreducedData
    rcases hsurvivors with ⟨-, hcaptured, -⟩ | ⟨htotal, -, -⟩ | ⟨htotal, -, -⟩
      | ⟨htotal, -, -⟩
    · rw [hcaptured]
      norm_num
    · rw [hrankReduced] at htotal
      omega
    · rw [hrankReduced] at htotal
      omega
    · rw [hrankReduced] at htotal
      omega
  exact ⟨reducedWeight, basisLabel, L,
    L * ((chartPointOfDesign crux.design).chart * B), L * assembly * Lᵀ,
    hreducedData, hassemblyEq, hinjective, hmem, hspan, hleft, hrepresentation,
    hidempotent, hHform, hsymmH,
    coefficientGram_posSemidef hreducedData L,
    coefficientGram_mulVec_eq_zero_imp_of_Hform basisLabel (L * assembly * Lᵀ)
      hindep hspan hHform,
    coefficient_exchange_of_leftInverse hreducedData basisLabel hspan L hleft,
    htrace⟩

end Gtz

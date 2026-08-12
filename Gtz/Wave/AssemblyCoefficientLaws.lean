import Gtz.Wave.AssemblyCoefficientForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The coefficient laws — `H ⪰ 0`, `ker H = 0`, `M H = H Mᵀ`

The second half of the H-form.  The coordinate Gram `H = L Ξ Lᵀ` inherits
positive semidefiniteness from the assembly by congruence, and its kernel is
trivial by a rank chain: `B H Bᵀ = Ξ` forces `rank H ≥ rank Ξ = r`, and `H`
is `r × r`.  The exchange law `M H = H Mᵀ` is the chart commutation read in
coefficient coordinates: both sides collapse to `L (Ξ (P Lᵀ))` through the
absorption identities.

`H` is symmetric, positive semidefinite, and has trivial kernel — that is
positive definiteness, packaged in the three separate facts a consumer can
take one at a time without a `PosDef` bridge.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.coefficientGram_posSemidef` — `L Ξ Lᵀ ⪰ 0`, for EVERY `L`.
* `Gtz.coefficientGram_mulVec_eq_zero_imp_of_Hform` — **KERNEL TRIVIALITY.**
  Any `H` with `B H Bᵀ = Ξ` over an independent spanning basis has trivial
  kernel.
* `Gtz.coefficient_exchange_of_leftInverse` — **THE EXCHANGE LAW.**
  `M H = H Mᵀ` for `M = L (P B)` and `H = L Ξ Lᵀ`.

## NOT PROVED here, and named

The trace law `tr M = rank(P Ξ)` is the last piece of the campaign's step
twelve and follows separately.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every stationary
datum with a chosen basis and left inverse.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- **THE COORDINATE GRAM IS POSITIVE SEMIDEFINITE.**  Congruence transports
the assembly's positivity, for every coefficient-reading matrix `L`. -/
theorem coefficientGram_posSemidef
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (L : Matrix (Fin basisCount) (Fin size) ℝ) :
    (L * chartMultiplierAssembly activeSet activeWeight tightDir * Lᵀ).PosSemidef := by
  have hpsd := posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata
  have hcongruence := hpsd.mul_mul_conjTranspose_same L
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hcongruence

/-- **KERNEL TRIVIALITY.**  Any coordinate Gram that reproduces the assembly
over an independent spanning basis has trivial kernel: the rank chain
`r = rank Ξ = rank (B H Bᵀ) ≤ rank H ≤ r` pins the rank, and rank-nullity
empties the kernel. -/
theorem coefficientGram_mulVec_eq_zero_imp_of_Hform
    (basisLabel : Fin basisCount → activeIndex)
    (H : Matrix (Fin basisCount) (Fin basisCount) ℝ)
    (hbasisIndep : LinearIndependent ℝ
      (fun columnIndex => tightDir (basisLabel columnIndex)))
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir) :
    ∀ coeffVec : Fin basisCount → ℝ, H *ᵥ coeffVec = 0 → coeffVec = 0 := by
  classical
  have hrankAssembly : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      (chartMultiplierAssembly activeSet activeWeight tightDir))) = basisCount := by
    rw [← hbasisSpan, finrank_span_eq_card hbasisIndep, Fintype.card_fin]
  have hchain : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      (chartMultiplierAssembly activeSet activeWeight tightDir)))
      ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin' H)) := by
    rw [← hHform]
    have hstepOne : LinearMap.range (Matrix.toLin'
        (tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ))
        ≤ LinearMap.range (Matrix.toLin'
            (tightBasisColumns tightDir basisLabel * H)) := by
      rw [Matrix.toLin'_mul]
      exact LinearMap.range_comp_le_range _ _
    have hstepTwo : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (tightBasisColumns tightDir basisLabel * H)))
        ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin' H)) := by
      rw [Matrix.toLin'_mul, LinearMap.range_comp]
      exact Submodule.finrank_map_le _ _
    exact le_trans (Submodule.finrank_mono hstepOne) hstepTwo
  have hfloor : basisCount ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin' H)) := by
    omega
  have hceiling : Module.finrank ℝ (LinearMap.range (Matrix.toLin' H)) ≤ basisCount := by
    have hwhole := Submodule.finrank_le (LinearMap.range (Matrix.toLin' H))
    have hdomain : Module.finrank ℝ (Fin basisCount → ℝ) = basisCount := by
      simp
    omega
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' H)
  have hdomain : Module.finrank ℝ (Fin basisCount → ℝ) = basisCount := by
    simp
  have hkernelRank : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' H)) = 0 := by
    omega
  have hkernel : LinearMap.ker (Matrix.toLin' H) = ⊥ :=
    Submodule.finrank_eq_zero.mp hkernelRank
  intro coeffVec hvanish
  have hmem : coeffVec ∈ LinearMap.ker (Matrix.toLin' H) := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    exact hvanish
  rw [hkernel, Submodule.mem_bot] at hmem
  exact hmem

/-- **THE EXCHANGE LAW.**  `M H = H Mᵀ`: the chart commutation, read in
coefficient coordinates.  Both sides collapse to `L (Ξ (P Lᵀ))` through the
absorption identities of the left inverse. -/
theorem coefficient_exchange_of_leftInverse
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1) :
    (L * (projection * tightBasisColumns tightDir basisLabel))
        * (L * chartMultiplierAssembly activeSet activeWeight tightDir * Lᵀ)
      = (L * chartMultiplierAssembly activeSet activeWeight tightDir * Lᵀ)
        * (L * (projection * tightBasisColumns tightDir basisLabel))ᵀ := by
  classical
  set B := tightBasisColumns tightDir basisLabel with hBdef
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir with hassemblyDef
  have hcommute : projection * assembly = assembly * projection := hdata.assembly_commutes
  have hsymmAssembly : assemblyᵀ = assembly :=
    transpose_chartMultiplierAssembly_of_isChartStationaryData hdata
  have hrangeB : LinearMap.range (Matrix.toLin' B)
      = LinearMap.range (Matrix.toLin' assembly) :=
    range_tightBasisColumns_eq basisLabel hbasisSpan
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
  have hMt : (L * (projection * B))ᵀ = Bᵀ * (projection * Lᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc, hdata.isSymmetric]
  rw [hMt]
  simp only [Matrix.mul_assoc]
  rw [habsorbAssemblyL]
  rw [show projection * (assembly * Lᵀ) = assembly * (projection * Lᵀ) from by
    rw [← Matrix.mul_assoc, hcommute, Matrix.mul_assoc]]
  rw [show Lᵀ * (Bᵀ * (projection * Lᵀ)) = Lᵀ * Bᵀ * (projection * Lᵀ) from
    (Matrix.mul_assoc _ _ _).symm]
  rw [show assembly * (Lᵀ * Bᵀ * (projection * Lᵀ))
      = assembly * (Lᵀ * Bᵀ) * (projection * Lᵀ) from (Matrix.mul_assoc _ _ _).symm]
  rw [show assembly * (Lᵀ * Bᵀ) = assembly from by
    rw [← Matrix.mul_assoc]
    exact habsorbRight]

end Gtz

import Gtz.Wave.CapturedAmbientTraceGap
import Gtz.Quantitative.CapturedRankFloor
import Gtz.Quantitative.ComplexVeroneseDichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators Matrix

variable {size rank : ℕ}
variable {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}
variable {activeSubset : Fin 3 → Finset (Fin size)}
variable {activeWeight : Fin 3 → ℝ}
variable {tightDir : Fin 3 → Fin size → ℝ}

theorem linearIndependent_fin_two_of_unit_orthogonal
    {first second : Fin size → ℝ}
    (hfirstUnit : first ⬝ᵥ first = 1)
    (hsecondUnit : second ⬝ᵥ second = 1)
    (horthogonal : first ⬝ᵥ second = 0) :
    LinearIndependent ℝ ![first, second] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hsecondZero
    have hsecondZero' : second = 0 := by simpa using hsecondZero
    rw [hsecondZero', dotProduct_zero] at hsecondUnit
    exact one_ne_zero hsecondUnit.symm
  · intro coefficient heq
    have heq' : coefficient • second = first := by simpa using heq
    have hpair := congrArg (fun vector => first ⬝ᵥ vector) heq'
    rw [dotProduct_smul, smul_eq_mul, horthogonal, mul_zero, hfirstUnit] at hpair
    exact zero_ne_one hpair

/-- The range of a multiplier assembly lies in the span of its tight rows. -/
theorem range_chartMultiplierAssembly_le_span_tightDir
    (activeSet : Finset (Fin 3)) :
    LinearMap.range
        (Matrix.toLin' (chartMultiplierAssembly activeSet activeWeight tightDir)) ≤
      Submodule.span ℝ (Set.range tightDir) := by
  intro vector hvector
  rcases hvector with ⟨preimage, hpreimage⟩
  rw [Matrix.toLin'_apply] at hpreimage
  rw [← hpreimage, chartMultiplierAssembly, Matrix.sum_mulVec]
  apply Submodule.sum_mem
  intro activeLabel hmem
  rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul, smul_smul]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self activeLabel))

/-- Two orthogonal unit rows whose multipliers are at least `level` give a
Rayleigh floor `level` on their two-dimensional span. -/
theorem two_row_span_floor_of_chartStationaryData
    (hdata : IsChartStationaryData rank projection weight value
      (Finset.univ : Finset (Fin 3)) activeSubset activeWeight tightDir)
    (level : ℝ)
    (hfirstFloor : level ≤ activeWeight 1)
    (hsecondFloor : level ≤ activeWeight 2)
    (horthogonal : tightDir 1 ⬝ᵥ tightDir 2 = 0) :
    ∀ vector ∈ Submodule.span ℝ (Set.range ![tightDir 1, tightDir 2]),
      level * (vector ⬝ᵥ vector) ≤
        vector ⬝ᵥ
          (chartMultiplierAssembly (Finset.univ : Finset (Fin 3))
            activeWeight tightDir *ᵥ vector) := by
  intro vector hvector
  obtain ⟨coefficient, hcoefficient⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp hvector
  rw [Fin.sum_univ_two] at hcoefficient
  have hcoefficient' :
      coefficient 0 • tightDir 1 + coefficient 1 • tightDir 2 = vector := by
    simpa using hcoefficient
  rw [← hcoefficient',
    dotProduct_mulVec_chartMultiplierAssembly]
  rw [Fin.sum_univ_three]
  have hfirstUnit := hdata.tightDir_unit 1 (Finset.mem_univ _)
  have hsecondUnit := hdata.tightDir_unit 2 (Finset.mem_univ _)
  have hfirstSecond : tightDir 2 ⬝ᵥ tightDir 1 = 0 := by
    rw [dotProduct_comm, horthogonal]
  have hzeroNonneg : 0 ≤ activeWeight 0 :=
    hdata.activeWeight_nonneg 0 (Finset.mem_univ _)
  have hzeroTerm : 0 ≤ activeWeight 0 *
      (tightDir 0 ⬝ᵥ
        (coefficient 0 • tightDir 1 + coefficient 1 • tightDir 2)) ^ 2 :=
    mul_nonneg hzeroNonneg (sq_nonneg _)
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, hfirstUnit, hsecondUnit, horthogonal, hfirstSecond,
    mul_zero, mul_one, add_zero, zero_add]
  nlinarith [sq_nonneg (coefficient 0), sq_nonneg (coefficient 1)]

/-- **THREE-ROW CAPTURE DICHOTOMY.**  For a stationary assembly supported on
three positive rows, two orthogonal rows with multiplier floor `1/size`
already exclude negative value.  Captured rank at least two meets their floor
plane; captured rank at most one factors as a positive rank-one form and the
rank-one mass transport excludes negativity. -/
theorem value_nonneg_of_three_active_rows_of_two_orthogonal_floored_rows
    (hdata : IsChartStationaryData rank projection weight value
      (Finset.univ : Finset (Fin 3)) activeSubset activeWeight tightDir)
    (htracePositive : 0 < value + ((size : ℝ))⁻¹)
    (hactiveWeightPositive : ∀ activeLabel : Fin 3, 0 < activeWeight activeLabel)
    (hfirstFloor : ((size : ℝ))⁻¹ ≤ activeWeight 1)
    (hsecondFloor : ((size : ℝ))⁻¹ ≤ activeWeight 2)
    (horthogonal : tightDir 1 ⬝ᵥ tightDir 2 = 0) :
    0 ≤ value := by
  let assembly := chartMultiplierAssembly (Finset.univ : Finset (Fin 3))
    activeWeight tightDir
  let product := projection * assembly
  let rowSpan := Submodule.span ℝ (Set.range tightDir)
  let floorPlane :=
    Submodule.span ℝ (Set.range ![tightDir 1, tightDir 2])
  have hproductPsd : product.PosSemidef := by
    exact posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata
  have hproductTrace : Matrix.trace product = value + ((size : ℝ))⁻¹ := by
    exact trace_projection_mul_multiplier_of_isChartStationaryData hdata
  by_cases hrankOne :
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' product)) ≤ 1
  · have hproductSymmetric : productᵀ = product :=
      transpose_eq_of_isHermitian hproductPsd.1
    obtain ⟨direction, hdirectionUnit, hfactor⟩ :=
      exists_unit_eq_trace_smul_atomMatrix_of_symmetric_of_range_finrank_le_one
        product hproductSymmetric hrankOne (by rw [hproductTrace]; exact htracePositive)
    apply value_nonneg_of_projectedMultiplier_rankOne_of_activeWeight_pos
      hdata direction hdirectionUnit
    · simpa only [product, assembly, hproductTrace] using hfactor
    · exact htracePositive
    · intro activeLabel _
      exact hactiveWeightPositive activeLabel
  · have hrankTwo :
        2 ≤ Module.finrank ℝ
          (LinearMap.range (Matrix.toLin' product)) := by
      omega
    have hfloorDim : Module.finrank ℝ floorPlane = 2 := by
      have hindependent : LinearIndependent ℝ ![tightDir 1, tightDir 2] :=
        linearIndependent_fin_two_of_unit_orthogonal
          (hdata.tightDir_unit 1 (Finset.mem_univ _))
          (hdata.tightDir_unit 2 (Finset.mem_univ _)) horthogonal
      dsimp only [floorPlane]
      rw [finrank_span_eq_card hindependent, Fintype.card_fin]
    have hrowSpanDim : Module.finrank ℝ rowSpan ≤ 3 := by
      exact finrank_span_range_le tightDir
    have hassemblyRange :
        LinearMap.range (Matrix.toLin' assembly) ≤ rowSpan := by
      exact range_chartMultiplierAssembly_le_span_tightDir Finset.univ
    have hproductRange :
        LinearMap.range (Matrix.toLin' product) ≤ rowSpan := by
      intro vector hvector
      rcases hvector with ⟨preimage, hpreimage⟩
      rw [Matrix.toLin'_apply] at hpreimage
      have hcommutes : projection * assembly = assembly * projection := by
        exact hdata.assembly_commutes
      dsimp only [product] at hpreimage
      rw [hcommutes] at hpreimage
      apply hassemblyRange
      refine ⟨projection *ᵥ preimage, ?_⟩
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      exact hpreimage
    have hfloorRowSpan : floorPlane ≤ rowSpan := by
      apply Submodule.span_mono
      rintro vector ⟨index, rfl⟩
      fin_cases index
      · simp
      · simp
    have hfloor := two_row_span_floor_of_chartStationaryData hdata
      ((size : ℝ))⁻¹ hfirstFloor hsecondFloor horthogonal
    have htraceFloor :=
      level_le_trace_projection_mul_of_twoDimensional_floor_in_ambient
        projection assembly ((size : ℝ))⁻¹ floorPlane rowSpan
        hdata.isSymmetric hdata.isIdempotent hproductPsd hfloorDim hrowSpanDim
        hrankTwo hproductRange hfloorRowSpan hfloor
    rw [hproductTrace] at htraceFloor
    linarith


end Gtz

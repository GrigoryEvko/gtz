import Gtz.Wave.RankOneCapturedRangeFloor
import Gtz.Quantitative.PrivateAtomQuantization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- A vector obtained by applying an idempotent is fixed by that idempotent. -/
theorem projection_mulVec_fixed_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (vector : Fin size → ℝ) :
    projection *ᵥ (projection *ᵥ vector) = projection *ᵥ vector := by
  rw [Matrix.mulVec_mulVec, hdata.isIdempotent]

/-- The orthogonal residual from a unit direction is perpendicular to that
direction. -/
theorem dotProduct_sub_projection_unit
    (direction vector : Fin size → ℝ)
    (hdirectionUnit : direction ⬝ᵥ direction = 1) :
    direction ⬝ᵥ (vector - (direction ⬝ᵥ vector) • direction) = 0 := by
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hdirectionUnit]
  ring

/-- The residual from orthogonal projection onto a unit line pairs with the
original vector by its own squared norm. -/
theorem dotProduct_residual_eq_self
    (direction vector : Fin size → ℝ)
    (hdirectionUnit : direction ⬝ᵥ direction = 1) :
    vector ⬝ᵥ (vector - (direction ⬝ᵥ vector) • direction) =
      (vector - (direction ⬝ᵥ vector) • direction) ⬝ᵥ
        (vector - (direction ⬝ᵥ vector) • direction) := by
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, hdirectionUnit]
  rw [dotProduct_comm vector direction]
  ring

/-- A nonzero rank-one projected assembly is supported inside the range of the
chart projection. -/
theorem direction_fixed_of_projectedMultiplier_rankOne
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (direction : Fin size → ℝ)
    (hdirectionUnit : direction ⬝ᵥ direction = 1)
    (hproduct : projection * chartMultiplierAssembly activeSet activeWeight tightDir =
      (value + ((size : ℝ))⁻¹) • atomMatrix direction)
    (htracePositive : 0 < value + ((size : ℝ))⁻¹) :
    projection *ᵥ direction = direction := by
  let assembly := chartMultiplierAssembly activeSet activeWeight tightDir
  let scale := value + ((size : ℝ))⁻¹
  have hinvariant : projection * (projection * assembly) = projection * assembly := by
    rw [← Matrix.mul_assoc, hdata.isIdempotent]
  have hproduct' : projection * assembly = scale • atomMatrix direction := by
    simpa only [assembly, scale] using hproduct
  change scale > 0 at htracePositive
  rw [hproduct'] at hinvariant
  have happly' := congrArg (fun form : Matrix (Fin size) (Fin size) ℝ =>
      form *ᵥ direction) hinvariant
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul,
    hdirectionUnit, one_smul, Matrix.mulVec_smul] at happly'
  apply funext
  intro atomIndex
  have hcoordinate := congrFun happly' atomIndex
  simp only [Pi.smul_apply, smul_eq_mul] at hcoordinate
  nlinarith

/-- If a projected stationary assembly is a positive rank-one form, every
positively weighted projected tight row lies on that line.  This supplies the
collinearity input that `value_nonneg_of_projectedMultiplier_rankOne` should not
have to assume at applications. -/
theorem projected_tightDir_eq_smul_of_projectedMultiplier_rankOne
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (direction : Fin size → ℝ)
    (hdirectionUnit : direction ⬝ᵥ direction = 1)
    (hdirectionFixed : projection *ᵥ direction = direction)
    (hproduct : projection * chartMultiplierAssembly activeSet activeWeight tightDir =
      (value + ((size : ℝ))⁻¹) • atomMatrix direction)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hweightPositive : 0 < activeWeight activeLabel) :
    projection *ᵥ tightDir activeLabel =
      (direction ⬝ᵥ (projection *ᵥ tightDir activeLabel)) • direction := by
  let projected := projection *ᵥ tightDir activeLabel
  let coefficient := direction ⬝ᵥ projected
  let residual := projected - coefficient • direction
  have hprojectedFixed : projection *ᵥ projected = projected := by
    exact projection_mulVec_fixed_of_isChartStationaryData hdata _
  have hresidualFixed : projection *ᵥ residual = residual := by
    dsimp only [residual]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hprojectedFixed, hdirectionFixed]
  have hresidualOrthogonal : direction ⬝ᵥ residual = 0 := by
    exact dotProduct_sub_projection_unit direction projected hdirectionUnit
  have hrankOneZero : residual ⬝ᵥ
      ((projection * chartMultiplierAssembly activeSet activeWeight tightDir) *ᵥ residual)
        = 0 := by
    rw [hproduct, Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul]
    simp [hresidualOrthogonal]
  have hassemblyZero : residual ⬝ᵥ
      (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ residual) = 0 := by
    calc
      residual ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ residual) =
          (projectionᵀ *ᵥ residual) ⬝ᵥ
            (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ residual) := by
              rw [hdata.isSymmetric, hresidualFixed]
      _ = residual ⬝ᵥ
          (projection *ᵥ
            (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ residual)) :=
        dotProduct_mulVec_transpose projection residual _
      _ = residual ⬝ᵥ
          ((projection * chartMultiplierAssembly activeSet activeWeight tightDir) *ᵥ
            residual) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := hrankOneZero
  have hsumZero :
      ∑ label ∈ activeSet,
          activeWeight label * (tightDir label ⬝ᵥ residual) ^ 2 = 0 := by
    rw [← dotProduct_mulVec_chartMultiplierAssembly]
    exact hassemblyZero
  have hselectedNonneg : 0 ≤
      activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ residual) ^ 2 :=
    mul_nonneg (le_of_lt hweightPositive) (sq_nonneg _)
  have hselectedLe :
      activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ residual) ^ 2 ≤ 0 := by
    rw [← hsumZero]
    exact Finset.single_le_sum
      (s := activeSet)
      (f := fun label => activeWeight label * (tightDir label ⬝ᵥ residual) ^ 2)
      (fun label hlabel =>
        mul_nonneg (hdata.activeWeight_nonneg label hlabel) (sq_nonneg _)) hmem
  have hselectedZero : tightDir activeLabel ⬝ᵥ residual = 0 := by
    have hproductZero :
        activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ residual) ^ 2 = 0 :=
      le_antisymm hselectedLe hselectedNonneg
    rcases mul_eq_zero.mp hproductZero with hweightZero | hsquareZero
    · exact (ne_of_gt hweightPositive hweightZero).elim
    · exact sq_eq_zero_iff.mp hsquareZero
  have hprojectedPair : projected ⬝ᵥ residual = 0 := by
    calc
      projected ⬝ᵥ residual =
          (projectionᵀ *ᵥ tightDir activeLabel) ⬝ᵥ residual := by
            rw [hdata.isSymmetric]
      _ = tightDir activeLabel ⬝ᵥ (projection *ᵥ residual) :=
        dotProduct_mulVec_transpose projection (tightDir activeLabel) residual
      _ = tightDir activeLabel ⬝ᵥ residual := by rw [hresidualFixed]
      _ = 0 := hselectedZero
  have hresidualNorm : residual ⬝ᵥ residual = 0 := by
    rw [← hprojectedPair]
    exact (dotProduct_residual_eq_self direction projected hdirectionUnit).symm
  have hresidualZero : residual = 0 := by
    apply funext
    intro atomIndex
    have hsumSquares : ∑ index : Fin size, residual index ^ 2 = 0 := by
      simpa only [dotProduct_self_eq_sum_sq] using hresidualNorm
    have htermNonneg : ∀ index ∈ (Finset.univ : Finset (Fin size)),
        0 ≤ residual index ^ 2 := fun index _ => sq_nonneg _
    have htermZero := Finset.sum_eq_zero_iff_of_nonneg htermNonneg |>.mp hsumSquares atomIndex
      (Finset.mem_univ atomIndex)
    exact sq_eq_zero_iff.mp htermZero
  change projected = coefficient • direction
  dsimp only [residual] at hresidualZero
  exact sub_eq_zero.mp hresidualZero

/-- **RANK-ONE CAPTURE WRAPPER.**  If the projected stationary assembly is a
positive rank-one form and every active multiplier is positive, the rank-one
mass-transport theorem applies automatically; no per-row collinearity
hypothesis remains. -/
theorem value_nonneg_of_projectedMultiplier_rankOne_of_activeWeight_pos
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (direction : Fin size → ℝ)
    (hdirectionUnit : direction ⬝ᵥ direction = 1)
    (hproduct : projection * chartMultiplierAssembly activeSet activeWeight tightDir =
      (value + ((size : ℝ))⁻¹) • atomMatrix direction)
    (htracePositive : 0 < value + ((size : ℝ))⁻¹)
    (hactiveWeightPositive : ∀ activeLabel ∈ activeSet,
      0 < activeWeight activeLabel) :
    0 ≤ value := by
  let coefficient : activeIndex → ℝ := fun activeLabel =>
    direction ⬝ᵥ (projection *ᵥ tightDir activeLabel)
  have hdirectionFixed := direction_fixed_of_projectedMultiplier_rankOne hdata
    direction hdirectionUnit hproduct htracePositive
  have himage : ∀ activeLabel ∈ activeSet,
      projection *ᵥ tightDir activeLabel = coefficient activeLabel • direction := by
    intro activeLabel hmem
    exact projected_tightDir_eq_smul_of_projectedMultiplier_rankOne hdata direction
      hdirectionUnit hdirectionFixed hproduct hmem (hactiveWeightPositive activeLabel hmem)
  exact value_nonneg_of_projectedMultiplier_rankOne hdata direction coefficient
    hdirectionUnit himage hproduct htracePositive


end Gtz

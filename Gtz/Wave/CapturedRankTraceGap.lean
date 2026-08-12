import Gtz.Wave.RankOneCaptureBridge
import Gtz.Reduction.MaximalVolume

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-- **TWO-DIMENSIONAL CAPTURE HAS A TRACE FLOOR.**  Let `assembly` have range
dimension at most three, and suppose a two-dimensional subspace of its range
has Rayleigh floor `level`.  Any commuting orthogonal projection which captures
at least two dimensions of the assembly then has trace at least `level`.

This is the dimension-theoretic core of the shared-edge interlacing argument;
it uses no ordered eigenvalue API.  The captured range and the floored plane
must meet nontrivially inside a space of dimension at most three. -/
theorem level_le_trace_projection_mul_of_twoDimensional_floor
    {size : ℕ}
    (projection assembly : Matrix (Fin size) (Fin size) ℝ)
    (level : ℝ)
    (floorPlane : Submodule ℝ (Fin size → ℝ))
    (hprojectionTranspose : projectionᵀ = projection)
    (hprojectionIdempotent : projection * projection = projection)
    (hcommutes : projection * assembly = assembly * projection)
    (hproductPsd : (projection * assembly).PosSemidef)
    (hfloorPlaneDim : Module.finrank ℝ floorPlane = 2)
    (hassemblyRangeDim :
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' assembly)) ≤ 3)
    (hproductRangeDim :
      2 ≤ Module.finrank ℝ
        (LinearMap.range (Matrix.toLin' (projection * assembly))))
    (hfloorPlaneRange : floorPlane ≤ LinearMap.range (Matrix.toLin' assembly))
    (hfloor : ∀ vector ∈ floorPlane,
      level * (vector ⬝ᵥ vector) ≤ vector ⬝ᵥ (assembly *ᵥ vector)) :
    level ≤ Matrix.trace (projection * assembly) := by
  let capturedRange : Submodule ℝ (Fin size → ℝ) :=
    LinearMap.range (Matrix.toLin' (projection * assembly))
  let assemblyRange : Submodule ℝ (Fin size → ℝ) :=
    LinearMap.range (Matrix.toLin' assembly)
  have hcapturedRangeAssembly : capturedRange ≤ assemblyRange := by
    intro vector hvector
    rcases hvector with ⟨preimage, hpreimage⟩
    rw [Matrix.toLin'_apply] at hpreimage
    rw [hcommutes] at hpreimage
    refine ⟨projection *ᵥ preimage, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    exact hpreimage
  have hsupRange : capturedRange ⊔ floorPlane ≤ assemblyRange :=
    sup_le hcapturedRangeAssembly hfloorPlaneRange
  have hsupDim : Module.finrank ℝ ↥(capturedRange ⊔ floorPlane) ≤ 3 := by
    exact (Submodule.finrank_mono hsupRange).trans hassemblyRangeDim
  have hdimension :=
    Submodule.finrank_sup_add_finrank_inf_eq capturedRange floorPlane
  have hinfDimPositive :
      0 < Module.finrank ℝ ↥(capturedRange ⊓ floorPlane) := by
    change 2 ≤ Module.finrank ℝ capturedRange at hproductRangeDim
    omega
  have hinfNeBot : capturedRange ⊓ floorPlane ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hinfDimPositive
    omega
  obtain ⟨witness, hwitnessInf, hwitnessNe⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hinfNeBot
  have hwitnessCaptured : witness ∈ capturedRange :=
    (Submodule.mem_inf.mp hwitnessInf).1
  have hwitnessFloor : witness ∈ floorPlane :=
    (Submodule.mem_inf.mp hwitnessInf).2
  have hwitnessFixed : projection *ᵥ witness = witness := by
    rcases hwitnessCaptured with ⟨preimage, hpreimage⟩
    rw [Matrix.toLin'_apply] at hpreimage
    rw [← hpreimage, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      hprojectionIdempotent]
  have hformEq :
      witness ⬝ᵥ ((projection * assembly) *ᵥ witness) =
        witness ⬝ᵥ (assembly *ᵥ witness) := by
    calc
      witness ⬝ᵥ ((projection * assembly) *ᵥ witness) =
          witness ⬝ᵥ (projection *ᵥ (assembly *ᵥ witness)) := by
            rw [Matrix.mulVec_mulVec]
      _ = (projectionᵀ *ᵥ witness) ⬝ᵥ (assembly *ᵥ witness) := by
            exact (dotProduct_mulVec_transpose projection witness
              (assembly *ᵥ witness)).symm
      _ = witness ⬝ᵥ (assembly *ᵥ witness) := by
            rw [hprojectionTranspose, hwitnessFixed]
  have hlower := hfloor witness hwitnessFloor
  have hupper := quadForm_le_trace_mul_dotProduct hproductPsd witness
  rw [hformEq] at hupper
  have hwitnessNormPositive : 0 < witness ⬝ᵥ witness :=
    dotProduct_self_pos hwitnessNe
  nlinarith


end Gtz

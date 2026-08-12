import Gtz.Wave.CapturedRankTraceGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-- A two-dimensional Rayleigh floor forces a trace floor whenever the captured
range and the floored plane lie in one ambient space of dimension at most three.
This is the form needed for a three-row stationary assembly: the ambient space
is the span of the rows, even when some row is not separately exhibited in the
matrix range. -/
theorem level_le_trace_projection_mul_of_twoDimensional_floor_in_ambient
    {size : ℕ}
    (projection assembly : Matrix (Fin size) (Fin size) ℝ)
    (level : ℝ)
    (floorPlane ambient : Submodule ℝ (Fin size → ℝ))
    (hprojectionTranspose : projectionᵀ = projection)
    (hprojectionIdempotent : projection * projection = projection)
    (hproductPsd : (projection * assembly).PosSemidef)
    (hfloorPlaneDim : Module.finrank ℝ floorPlane = 2)
    (hambientDim : Module.finrank ℝ ambient ≤ 3)
    (hproductRangeDim :
      2 ≤ Module.finrank ℝ
        (LinearMap.range (Matrix.toLin' (projection * assembly))))
    (hcapturedAmbient :
      LinearMap.range (Matrix.toLin' (projection * assembly)) ≤ ambient)
    (hfloorPlaneAmbient : floorPlane ≤ ambient)
    (hfloor : ∀ vector ∈ floorPlane,
      level * (vector ⬝ᵥ vector) ≤ vector ⬝ᵥ (assembly *ᵥ vector)) :
    level ≤ Matrix.trace (projection * assembly) := by
  let capturedRange : Submodule ℝ (Fin size → ℝ) :=
    LinearMap.range (Matrix.toLin' (projection * assembly))
  have hsupAmbient : capturedRange ⊔ floorPlane ≤ ambient :=
    sup_le hcapturedAmbient hfloorPlaneAmbient
  have hsupDim : Module.finrank ℝ ↥(capturedRange ⊔ floorPlane) ≤ 3 :=
    (Submodule.finrank_mono hsupAmbient).trans hambientDim
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

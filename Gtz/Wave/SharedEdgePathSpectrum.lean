import Gtz.Wave.SharedEdgeSpectralSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

noncomputable def sharedEdgePathMatrix (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, x, 0], ![x, 1, y], ![0, y, 1]]

noncomputable def sharedEdgeSmallVector (x y : ℝ) : Fin 3 → ℝ :=
  ![-y, 0, x]

noncomputable def sharedEdgeLargeVector (x y : ℝ) : Fin 3 → ℝ :=
  ![x, 1, y]

theorem sharedEdgeSmallVector_norm_sq {x y : ℝ} (hcircle : x ^ 2 + y ^ 2 = 1) :
    sharedEdgeSmallVector x y ⬝ᵥ sharedEdgeSmallVector x y = 1 := by
  simp [sharedEdgeSmallVector, dotProduct, Fin.sum_univ_three]
  nlinarith

theorem sharedEdgeLargeVector_norm_sq {x y : ℝ} (hcircle : x ^ 2 + y ^ 2 = 1) :
    sharedEdgeLargeVector x y ⬝ᵥ sharedEdgeLargeVector x y = 2 := by
  simp [sharedEdgeLargeVector, dotProduct, Fin.sum_univ_three]
  nlinarith

theorem sharedEdge_vectors_orthogonal (x y : ℝ) :
    sharedEdgeSmallVector x y ⬝ᵥ sharedEdgeLargeVector x y = 0 := by
  simp [sharedEdgeSmallVector, sharedEdgeLargeVector, dotProduct, Fin.sum_univ_three]
  ring

/-- The constant-diagonal rank-two path block has eigenvalues `0,1,2`,
expressed without eigenvalue APIs as two orthogonal rank-one summands. -/
theorem sharedEdgePathMatrix_eq_rankOne_sum {x y : ℝ} (hcircle : x ^ 2 + y ^ 2 = 1) :
    sharedEdgePathMatrix x y =
      atomMatrix (sharedEdgeSmallVector x y) + atomMatrix (sharedEdgeLargeVector x y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sharedEdgePathMatrix, sharedEdgeSmallVector, sharedEdgeLargeVector, atomMatrix] <;>
    nlinarith

/-- The explicit range projector of the path block. -/
noncomputable def sharedEdgePathRange (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  atomMatrix (sharedEdgeSmallVector x y)
    + (1 / 2 : ℝ) • atomMatrix (sharedEdgeLargeVector x y)

theorem sharedEdgePathRange_mul_self {x y : ℝ} (hcircle : x ^ 2 + y ^ 2 = 1) :
    sharedEdgePathRange x y * sharedEdgePathRange x y = sharedEdgePathRange x y := by
  have hx := congrArg (fun value : ℝ => value * x) hcircle
  have hy := congrArg (fun value : ℝ => value * y) hcircle
  have hxy := congrArg (fun value : ℝ => value * (x * y)) hcircle
  ring_nf at hx hy hxy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sharedEdgePathRange, sharedEdgeSmallVector, sharedEdgeLargeVector,
      atomMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;>
    nlinarith

theorem sharedEdgePathRange_transpose (x y : ℝ) :
    (sharedEdgePathRange x y)ᵀ = sharedEdgePathRange x y := by
  simp [sharedEdgePathRange, atomMatrix, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_vecMulVec]

theorem sharedEdgePathRange_mul_path {x y : ℝ} (hcircle : x ^ 2 + y ^ 2 = 1) :
    sharedEdgePathRange x y * sharedEdgePathMatrix x y = sharedEdgePathMatrix x y := by
  have hx := congrArg (fun value : ℝ => value * x) hcircle
  have hy := congrArg (fun value : ℝ => value * y) hcircle
  ring_nf at hx hy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sharedEdgePathRange, sharedEdgePathMatrix, sharedEdgeSmallVector,
      sharedEdgeLargeVector, atomMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;>
    nlinarith

/-- Exact `1/6` spectral-floor remainder: after subtracting one sixth of the
range projector, only the large eigenline remains. -/
theorem sharedEdgePath_sixth_floor_eq {x y : ℝ} (hcircle : x ^ 2 + y ^ 2 = 1) :
    (1 / 6 : ℝ) • sharedEdgePathMatrix x y
        - (1 / 6 : ℝ) • sharedEdgePathRange x y
      = (1 / 12 : ℝ) • atomMatrix (sharedEdgeLargeVector x y) := by
  rw [sharedEdgePathMatrix_eq_rankOne_sum hcircle, sharedEdgePathRange]
  ext i j
  simp [atomMatrix]
  ring

theorem sharedEdgePath_sixth_floor_posSemidef {x y : ℝ}
    (hcircle : x ^ 2 + y ^ 2 = 1) :
    ((1 / 6 : ℝ) • sharedEdgePathMatrix x y
        - (1 / 6 : ℝ) • sharedEdgePathRange x y).PosSemidef := by
  rw [sharedEdgePath_sixth_floor_eq hcircle]
  exact (posSemidef_atomMatrix (sharedEdgeLargeVector x y)).smul (by norm_num)


end Gtz

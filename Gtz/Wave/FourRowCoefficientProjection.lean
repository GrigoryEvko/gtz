import Gtz.Wave.TypeNineAlignedOperatorExit

import Gtz.Quantitative.FourActiveCoefficientProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {ambient rowCount : Type*}
  [Fintype ambient]
  [Fintype rowCount] [DecidableEq rowCount]

theorem matrix_leftInverse_recovers_range
    (B : Matrix ambient rowCount ℝ)
    (L : Matrix rowCount ambient ℝ)
    (hleft : L * B = 1)
    {vector : ambient → ℝ}
    (hvector : vector ∈ LinearMap.range (Matrix.toLin' B)) :
    B *ᵥ (L *ᵥ vector) = vector := by
  rcases hvector with ⟨preimage, hpreimage⟩
  rw [Matrix.toLin'_apply] at hpreimage
  rw [← hpreimage]
  change B *ᵥ (L *ᵥ (B *ᵥ preimage)) = B *ᵥ preimage
  rw [Matrix.mulVec_mulVec preimage L B, hleft, Matrix.one_mulVec]

/-- An ambient operator preserving the column range has a coefficient matrix
in any chosen left-invertible column frame. -/
theorem exists_coefficientMatrix_of_leftInverse_of_rangeInvariant
    (P : Matrix ambient ambient ℝ)
    (B : Matrix ambient rowCount ℝ)
    (L : Matrix rowCount ambient ℝ)
    (hleft : L * B = 1)
    (hinvariant : ∀ vector : rowCount → ℝ,
      P *ᵥ (B *ᵥ vector) ∈ LinearMap.range (Matrix.toLin' B)) :
    ∃ M : Matrix rowCount rowCount ℝ, P * B = B * M := by
  let M : Matrix rowCount rowCount ℝ := L * P * B
  refine ⟨M, ?_⟩
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro vector
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec vector P B,
    ← Matrix.mulVec_mulVec vector B M]
  dsimp only [M]
  rw [← Matrix.mulVec_mulVec vector (L * P) B,
    ← Matrix.mulVec_mulVec (B *ᵥ vector) L P]
  change P *ᵥ (B *ᵥ vector) =
    B *ᵥ (L *ᵥ (P *ᵥ (B *ᵥ vector)))
  exact (matrix_leftInverse_recovers_range B L hleft (hinvariant vector)).symm

end Gtz

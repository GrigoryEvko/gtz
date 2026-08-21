/-
# The contraction transfer: `1 − MᵀM ⪰ 0` if and only if `1 − MMᵀ ⪰ 0`

The campaign carries the EXPANSION transfer
`Gtz.posSemidef_transpose_mul_sub_one_comm`: for a square matrix,
`MᵀM ⪰ 1` if and only if `MMᵀ ⪰ 1`.  Its proof inverts `M`, which the
expansion hypothesis supplies for free.

The CONTRACTION transfer is the opposite inequality, and it is the step the
resolvent criterion of `Gtz/Wave/ResolventProjectionLaw.lean` needs: there the
selected block is compared with the identity from BELOW, so the expansion
transfer does not apply and no inverse is available — a contraction may be
singular.  This module supplies it.

## The proof is one Cauchy–Schwarz step

Write the two statements as bounds on the two maps:

  `1 − MᵀM ⪰ 0`  means  `‖M u‖² ≤ ‖u‖²`  for every `u`,
  `1 − MMᵀ ⪰ 0`  means  `‖Mᵀ u‖² ≤ ‖u‖²`  for every `u`.

Assume the first.  For any `u`, the transpose is the adjoint of `M`, so

  `‖Mᵀ u‖² = ⟨Mᵀ u, Mᵀ u⟩ = ⟨u, M (Mᵀ u)⟩ ≤ ‖u‖·‖M (Mᵀ u)‖ ≤ ‖u‖·‖Mᵀ u‖` ,

the first estimate by Cauchy–Schwarz and the second by the hypothesis applied
to the vector `Mᵀ u`.  Dividing by `‖Mᵀ u‖`, which is legitimate unless that
number is zero and the claim is trivial, gives `‖Mᵀ u‖ ≤ ‖u‖`.

Nothing is square in the argument, so `Gtz.posSemidef_one_sub_mul_transpose_comm`
holds for a rectangular matrix as well: it exchanges the two sides of a
rectangle rather than the two factors of a square.  That is stronger than the
expansion transfer, which needs a square matrix to invert.
-/
import Gtz.LinAlg.PsdKit
import Gtz.Planar.BallPerturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {a b : ℕ}

/-! ## 1. The two sides, read as bounds on a map -/

/-- The gap form of `1 − MᵀM` at a probe is the probe's square less the square
of its image.  No hypothesis. -/
theorem one_sub_transpose_mul_form (M : Matrix (Fin a) (Fin b) ℝ) (u : Fin b → ℝ) :
    u ⬝ᵥ (((1 : Matrix (Fin b) (Fin b) ℝ) - Mᵀ * M) *ᵥ u)
      = u ⬝ᵥ u - (M *ᵥ u) ⬝ᵥ (M *ᵥ u) := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_comm u (Mᵀ *ᵥ (M *ᵥ u)), dotProduct_mulVec_transpose]

/-- **THE CONTRACTION, AS A BOUND ON THE MAP.**  `1 − MᵀM` is positive
semidefinite exactly when `M` does not increase the length of any vector. -/
theorem posSemidef_one_sub_transpose_mul_iff (M : Matrix (Fin a) (Fin b) ℝ) :
    ((1 : Matrix (Fin b) (Fin b) ℝ) - Mᵀ * M).PosSemidef
      ↔ ∀ u : Fin b → ℝ, (M *ᵥ u) ⬝ᵥ (M *ᵥ u) ≤ u ⬝ᵥ u := by
  constructor
  · intro hpsd u
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 u
    rw [star_trivial, one_sub_transpose_mul_form M u] at h
    linarith
  · intro hbound
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun u => ?_⟩
    · refine Matrix.isHermitian_one.sub ?_
      rw [Matrix.IsHermitian, Matrix.conjTranspose_mul]
      congr 1 <;> ext i j <;> simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    · rw [star_trivial, one_sub_transpose_mul_form M u]
      have := hbound u
      linarith

/-! ## 2. The transfer -/

/-- The square of a vector is the square of its own length, in the form the
Cauchy–Schwarz step below consumes. -/
theorem dotProduct_self_eq_sq_sqrt (v : Fin a → ℝ) :
    v ⬝ᵥ v = Real.sqrt (v ⬝ᵥ v) ^ 2 :=
  (Real.sq_sqrt (dotProduct_self_nonneg v)).symm

/-- **ONE DIRECTION OF THE TRANSFER.**  If `M` does not increase length, then
neither does `Mᵀ`.  The matrix need not be square: this exchanges the two sides
of a rectangle. -/
theorem transpose_contracts_of_contracts {M : Matrix (Fin a) (Fin b) ℝ}
    (hM : ∀ u : Fin b → ℝ, (M *ᵥ u) ⬝ᵥ (M *ᵥ u) ≤ u ⬝ᵥ u) :
    ∀ w : Fin a → ℝ, (Mᵀ *ᵥ w) ⬝ᵥ (Mᵀ *ᵥ w) ≤ w ⬝ᵥ w := by
  intro w
  set y := Mᵀ *ᵥ w with hy
  have hyy : 0 ≤ y ⬝ᵥ y := dotProduct_self_nonneg y
  have hww : 0 ≤ w ⬝ᵥ w := dotProduct_self_nonneg w
  -- the transpose is the adjoint, so the square of `y` is a pairing against `w`
  have hadjoint : y ⬝ᵥ y = w ⬝ᵥ (M *ᵥ y) := by
    rw [hy, dotProduct_mulVec_transpose]
  -- Cauchy–Schwarz on that pairing, then the hypothesis at `y`
  have hchain : y ⬝ᵥ y ≤ Real.sqrt (w ⬝ᵥ w) * Real.sqrt (y ⬝ᵥ y) :=
    calc y ⬝ᵥ y = w ⬝ᵥ (M *ᵥ y) := hadjoint
      _ ≤ Real.sqrt (w ⬝ᵥ w) * Real.sqrt ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) :=
          le_trans (le_abs_self _) (abs_dotProduct_le w (M *ᵥ y))
      _ ≤ Real.sqrt (w ⬝ᵥ w) * Real.sqrt (y ⬝ᵥ y) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hM y)) (Real.sqrt_nonneg _)
  -- divide by the length of `y`, or read the claim off directly when it vanishes
  have hsq : Real.sqrt (y ⬝ᵥ y) ^ 2 ≤ Real.sqrt (w ⬝ᵥ w) * Real.sqrt (y ⬝ᵥ y) := by
    rw [Real.sq_sqrt hyy]; exact hchain
  have hle : Real.sqrt (y ⬝ᵥ y) ≤ Real.sqrt (w ⬝ᵥ w) := by
    rcases eq_or_lt_of_le (Real.sqrt_nonneg (y ⬝ᵥ y)) with hzero | hpos
    · rw [← hzero]; exact Real.sqrt_nonneg _
    · nlinarith [hsq, hpos]
  calc y ⬝ᵥ y = Real.sqrt (y ⬝ᵥ y) ^ 2 := dotProduct_self_eq_sq_sqrt y
    _ ≤ Real.sqrt (w ⬝ᵥ w) ^ 2 := by nlinarith [Real.sqrt_nonneg (y ⬝ᵥ y), hle]
    _ = w ⬝ᵥ w := Real.sq_sqrt hww

/-- **THE CONTRACTION TRANSFER.**  `1 − MᵀM ⪰ 0` if and only if `1 − MMᵀ ⪰ 0`.
The companion of the landed `Gtz.posSemidef_transpose_mul_sub_one_comm`, which
transfers the opposite inequality by inverting the matrix — an inverse this
statement cannot supply, since a contraction may be singular. -/
theorem posSemidef_one_sub_mul_transpose_comm (M : Matrix (Fin a) (Fin b) ℝ) :
    ((1 : Matrix (Fin b) (Fin b) ℝ) - Mᵀ * M).PosSemidef
      ↔ ((1 : Matrix (Fin a) (Fin a) ℝ) - M * Mᵀ).PosSemidef := by
  constructor
  · intro h
    exact (posSemidef_one_sub_transpose_mul_iff Mᵀ).mpr
      (transpose_contracts_of_contracts ((posSemidef_one_sub_transpose_mul_iff M).mp h))
  · intro h
    exact (posSemidef_one_sub_transpose_mul_iff M).mpr
      (transpose_contracts_of_contracts (M := Mᵀ)
        ((posSemidef_one_sub_transpose_mul_iff Mᵀ).mp h))

/-- **THE TRANSFER AGAINST A SCALAR LEVEL.**  The same statement at level
`level ≥ 0`: the two products contract the ball of that radius together. -/
theorem posSemidef_smul_one_sub_mul_transpose_comm (M : Matrix (Fin a) (Fin b) ℝ)
    {level : ℝ} (hlevel : 0 < level) :
    (level • (1 : Matrix (Fin b) (Fin b) ℝ) - Mᵀ * M).PosSemidef
      ↔ (level • (1 : Matrix (Fin a) (Fin a) ℝ) - M * Mᵀ).PosSemidef := by
  have hscale : ∀ {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ),
      (level • (1 : Matrix (Fin n) (Fin n) ℝ) - N).PosSemidef
        ↔ ((1 : Matrix (Fin n) (Fin n) ℝ) - level⁻¹ • N).PosSemidef := by
    intro n N
    constructor
    · intro hpsd
      have := hpsd.smul (le_of_lt (inv_pos.mpr hlevel))
      rwa [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hlevel), one_smul] at this
    · intro hpsd
      have := hpsd.smul (le_of_lt hlevel)
      rwa [smul_sub, smul_smul, mul_inv_cancel₀ (ne_of_gt hlevel), one_smul] at this
  rw [hscale (Mᵀ * M), hscale (M * Mᵀ)]
  have hleft : level⁻¹ • (Mᵀ * M) = (Real.sqrt level⁻¹ • M)ᵀ * (Real.sqrt level⁻¹ • M) := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Real.mul_self_sqrt (le_of_lt (inv_pos.mpr hlevel))]
  have hright : level⁻¹ • (M * Mᵀ)
      = (Real.sqrt level⁻¹ • M) * (Real.sqrt level⁻¹ • M)ᵀ := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Real.mul_self_sqrt (le_of_lt (inv_pos.mpr hlevel))]
  rw [hleft, hright]
  exact posSemidef_one_sub_mul_transpose_comm _

end Gtz

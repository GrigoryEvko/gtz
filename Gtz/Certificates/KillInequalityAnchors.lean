import Mathlib

/-!
# The kill-inequality data at the canonical diamond: exact anchors in kernel

The diamond-rigidity lane's first-order obstruction consists of two dual-ray
ellipsoids on `y = L^{1/2} h₆`; a first-order-feasible tie must satisfy
`yᵀ A_X y ≥ 60` for BOTH.  The five split directions `u_e = √(5c_e)·r_e` sit
on both boundaries with exact equality — the split-tie family is exactly the
flat locus of the obstruction.

This file puts the EXACT anchor identities in kernel: both quadrics evaluate
to exactly `60` on every one of the five (scaled) incidence directions.
Squared scale factors `5·c_e` are attached explicitly, so every statement is
pure rational arithmetic — no square roots.  Conductances
`c = (1, 2/3, 1, 1, 1)` on edges `(ab, ac, cb, ad, dc)`; incidence rows in
the grounded gauge.

These ten identities are the boundary data any future closed-form kill
certificate must reproduce; they pin the certificate's equality locus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

namespace KillAnchors

/-- The first dual-ray ellipsoid `A_A` (times the common denominator 440). -/
def ellipsoidA : Matrix (Fin 3) (Fin 3) ℚ :=
  !![5280, 2200, 1320; 2200, 4400, 2200; 1320, 2200, 5280]

/-- The second dual-ray ellipsoid `A_B` (times the common denominator 440). -/
def ellipsoidB : Matrix (Fin 3) (Fin 3) ℚ :=
  !![5280, 4400, 1320; 4400, 8800, 4400; 1320, 4400, 5280]

/-- The five incidence directions of the canonical diamond, grounded gauge. -/
def incidenceRow : Fin 5 → Fin 3 → ℚ
  | 0 => ![1, -1, 0]   -- edge ab
  | 1 => ![1, 0, -1]   -- edge ac (the shared circuit edge)
  | 2 => ![0, 1, -1]   -- edge cb
  | 3 => ![1, 0, 0]    -- edge ad
  | 4 => ![0, 0, -1]   -- edge dc

/-- The conductances, times five: the squared scales `5·c_e` of the split
anchors `u_e = √(5c_e)·r_e`. -/
def squaredScale : Fin 5 → ℚ
  | 0 => 5
  | 1 => 10/3
  | 2 => 5
  | 3 => 5
  | 4 => 5

/-- The quadratic form of a rational 3×3 matrix at a direction. -/
def quadraticForm (matrix : Matrix (Fin 3) (Fin 3) ℚ)
    (direction : Fin 3 → ℚ) : ℚ :=
  direction ⬝ᵥ Matrix.mulVec matrix direction

/-- **Anchor exactness for the first ellipsoid**: every split direction sits
exactly on the boundary `yᵀ A_A y = 60` (with the 440 denominator cleared:
`5·c_e · rᵀ(440·A_A)r = 440·60 = 26400`). -/
theorem ellipsoidA_anchor_exact (edge : Fin 5) :
    squaredScale edge * quadraticForm ellipsoidA (incidenceRow edge)
      = 26400 := by
  fin_cases edge <;>
    simp only [squaredScale, quadraticForm, ellipsoidA, incidenceRow,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.of_apply,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    norm_num

/-- **Anchor exactness for the second ellipsoid**: the same five directions
sit exactly on the boundary of `A_B` as well — the flat locus is COMMON to
both dual rays. -/
theorem ellipsoidB_anchor_exact (edge : Fin 5) :
    squaredScale edge * quadraticForm ellipsoidB (incidenceRow edge)
      = 26400 := by
  fin_cases edge <;>
    simp only [squaredScale, quadraticForm, ellipsoidB, incidenceRow,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.of_apply,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    norm_num

end KillAnchors

end Gtz

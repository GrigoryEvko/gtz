import Gtz.Wave.OrbitFourAlignedSimilarity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false

namespace Gtz

open Matrix

/-- The orthogonal ambient frame obtained from the aligned orbit-four rows. -/
noncomputable def orbitFourAlignedFrame
    (a c k z : ℝ) : Matrix (Fin 6) (Fin 4) ℝ :=
  !![0, 0, a, 0;
     1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, c, 0;
     0, 0, 0, k;
     0, 0, 0, z]

/-- The four multiplier-weighted tight columns in canonical aligned type-nine
coordinates. -/
noncomputable def orbitFourAlignedColumns
    (x y a b c e h k z scale : ℝ) : Matrix (Fin 6) (Fin 4) ℝ :=
  !![0, a, scale * a, 0;
     x, b, 0, h;
     y, 0, e, 0;
     0, c, scale * c, 0;
     0, 0, 0, k;
     0, 0, 0, z]

/-- The canonical aligned orbit-four columns become the sparse orthogonal
frame after multiplication by the explicit inverse change matrix. -/
theorem orbitFourAlignedColumns_mul_inv_eq_frame
    (B : Matrix (Fin 6) (Fin 4) ℝ)
    {x y a b c e h k z scale : ℝ}
    (hdet : e * x + scale * b * y ≠ 0)
    (hrowZero : B 0 = (![0, a, scale * a, 0] : Fin 4 → ℝ))
    (hrowOne : B 1 = (![x, b, 0, h] : Fin 4 → ℝ))
    (hrowTwo : B 2 = (![y, 0, e, 0] : Fin 4 → ℝ))
    (hrowThree : B 3 = (![0, c, scale * c, 0] : Fin 4 → ℝ))
    (hrowFour : B 4 = (![0, 0, 0, k] : Fin 4 → ℝ))
    (hrowFive : B 5 = (![0, 0, 0, z] : Fin 4 → ℝ)) :
    B * typeNineAlignedChangeInv x y b e h scale
      = orbitFourAlignedFrame a c k z := by
  have hdetOne : x * e + scale * b * y ≠ 0 := by
    convert hdet using 1 <;> ring
  have hdetTwo : y * scale * b + e * x ≠ 0 := by
    convert hdet using 1 <;> ring
  have hcancelTwo :
      y * scale * b * (y * scale * b + e * x)⁻¹
          + e * x * (y * scale * b + e * x)⁻¹ = 1 := by
    calc
      _ = (y * scale * b + e * x) * (y * scale * b + e * x)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hdetTwo
  have hB : B = orbitFourAlignedColumns x y a b c e h k z scale := by
    funext row col
    fin_cases row <;> fin_cases col <;>
      simp [orbitFourAlignedColumns, hrowZero, hrowOne, hrowTwo,
        hrowThree, hrowFour, hrowFive, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.of_apply]
  rw [hB]
  ext row col
  fin_cases row <;> fin_cases col <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four,
      typeNineAlignedChangeInv, orbitFourAlignedFrame,
      orbitFourAlignedColumns,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.of_apply] <;>
    field_simp [hdet, hdetOne, hdetTwo] <;> ring
  all_goals exact hcancelTwo

/-- The sparse aligned frame recovers the original four columns through the
change matrix. -/
theorem orbitFourAlignedFrame_mul_change_eq_columns
    (B : Matrix (Fin 6) (Fin 4) ℝ)
    {x y a b c e h k z scale : ℝ}
    (hdet : e * x + scale * b * y ≠ 0)
    (hframe : B * typeNineAlignedChangeInv x y b e h scale
      = orbitFourAlignedFrame a c k z) :
    orbitFourAlignedFrame a c k z
        * typeNineAlignedChange x y b e h scale = B := by
  rw [← hframe, Matrix.mul_assoc,
    typeNineAlignedChange_inv_mul hdet, Matrix.mul_one]


end Gtz

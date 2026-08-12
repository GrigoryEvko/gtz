import Gtz.Wave.TypeNineAlignedOrthogonalExit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false

namespace Gtz

open Matrix

/-- Coordinates of the four original weighted tight rows in the aligned
orthogonal frame `(e₁,e₂,endpointResidual,privateResidual)`. -/
noncomputable def typeNineAlignedChange
    (x y b e h scale : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![x, b, 0, h;
     y, 0, e, 0;
     0, 1, scale, 0;
     0, 0, 0, 1]

/-- Explicit inverse of `typeNineAlignedChange`.  Its only denominator is the
genuine pair-plane determinant `e*x + scale*b*y`. -/
noncomputable def typeNineAlignedChangeInv
    (x y b e h scale : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let determinant := e * x + scale * b * y
  !![e / determinant, scale * b / determinant,
      -(b * e) / determinant, -(e * h) / determinant;
     scale * y / determinant, -(scale * x) / determinant,
      e * x / determinant, -(scale * h * y) / determinant;
     -y / determinant, x / determinant,
      b * y / determinant, h * y / determinant;
     0, 0, 0, 1]

theorem typeNineAlignedChange_mul_inv
    {x y b e h scale : ℝ}
    (hdet : e * x + scale * b * y ≠ 0) :
    typeNineAlignedChange x y b e h scale
        * typeNineAlignedChangeInv x y b e h scale = 1 := by
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
  ext row col
  fin_cases row <;> fin_cases col <;>
    norm_num [typeNineAlignedChange, typeNineAlignedChangeInv,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.of_apply, Matrix.one_apply, Fin.isValue, if_pos] <;>
    field_simp [hdet, hdetOne, hdetTwo] <;> ring
  all_goals try assumption

theorem typeNineAlignedChange_inv_mul
    {x y b e h scale : ℝ}
    (hdet : e * x + scale * b * y ≠ 0) :
    typeNineAlignedChangeInv x y b e h scale
        * typeNineAlignedChange x y b e h scale = 1 := by
  have hdetOne : x * e + scale * b * y ≠ 0 := by
    convert hdet using 1 <;> ring
  have hdetTwo : scale * y * b + e * x ≠ 0 := by
    convert hdet using 1 <;> ring
  have hcancelTwo :
      scale * y * b * (scale * y * b + e * x)⁻¹
          + e * x * (scale * y * b + e * x)⁻¹ = 1 := by
    calc
      _ = (scale * y * b + e * x) * (scale * y * b + e * x)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hdetTwo
  ext row col
  fin_cases row <;> fin_cases col <;>
    norm_num [typeNineAlignedChange, typeNineAlignedChangeInv,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.of_apply, Matrix.one_apply, Fin.isValue, if_pos] <;>
    field_simp [hdet, hdetOne, hdetTwo] <;> ring
  all_goals try assumption

/-- Similarity transports an idempotent coefficient projection and its trace
to the aligned orthogonal frame. -/
theorem alignedSimilarity_idempotent_trace
    (C T M : Matrix (Fin 4) (Fin 4) ℝ)
    (hTC : T * C = 1)
    (hidem : M * M = M) (htrace : Matrix.trace M = 2) :
    let R := C * M * T
    R * R = R ∧ Matrix.trace R = 2 := by
  dsimp only
  constructor
  · calc
      (C * M * T) * (C * M * T)
          = C * M * (T * C) * M * T := by simp only [Matrix.mul_assoc]
      _ = C * M * M * T := by rw [hTC, Matrix.mul_one]
      _ = C * (M * M) * T := by simp only [Matrix.mul_assoc]
      _ = C * M * T := by rw [hidem]
  · calc
      Matrix.trace (C * M * T) = Matrix.trace (T * (C * M)) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace ((T * C) * M) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace M := by rw [hTC, Matrix.one_mul]
      _ = 2 := htrace

/-- Change of coefficient frame for an invariant ambient operator. -/
theorem alignedSimilarity_representation
    {ambient : Type*} [Fintype ambient]
    (P : Matrix ambient ambient ℝ)
    (B F : Matrix ambient (Fin 4) ℝ)
    (C T M : Matrix (Fin 4) (Fin 4) ℝ)
    (hBT : B * T = F) (hFC : F * C = B)
    (hPB : P * B = B * M) :
    P * F = F * (C * M * T) := by
  calc
    P * F = P * (B * T) := by rw [hBT]
    _ = (P * B) * T := by simp only [Matrix.mul_assoc]
    _ = (B * M) * T := by rw [hPB]
    _ = ((F * C) * M) * T := by rw [hFC]
    _ = F * (C * M * T) := by simp only [Matrix.mul_assoc]

/-- Self-adjointness of the ambient operator becomes self-adjointness with
respect to the Gram matrix of any invariant coefficient frame. -/
theorem gram_mul_coefficient_eq_transpose_mul_gram
    {ambient coefficient : Type*}
    [Fintype ambient] [Fintype coefficient]
    (P : Matrix ambient ambient ℝ)
    (F : Matrix ambient coefficient ℝ)
    (R : Matrix coefficient coefficient ℝ)
    (hsymm : P.transpose = P)
    (hrepresentation : P * F = F * R) :
    (F.transpose * F) * R = R.transpose * (F.transpose * F) := by
  calc
    (F.transpose * F) * R = F.transpose * (F * R) := by
      simp only [Matrix.mul_assoc]
    _ = F.transpose * (P * F) := by rw [← hrepresentation]
    _ = (F.transpose * P) * F := by simp only [Matrix.mul_assoc]
    _ = ((P * F).transpose) * F := by rw [Matrix.transpose_mul, hsymm]
    _ = ((F * R).transpose) * F := by rw [hrepresentation]
    _ = (R.transpose * F.transpose) * F := by rw [Matrix.transpose_mul]
    _ = R.transpose * (F.transpose * F) := by simp only [Matrix.mul_assoc]


end Gtz

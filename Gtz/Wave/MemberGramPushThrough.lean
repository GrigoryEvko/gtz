import Gtz.Wave.HeavyInsideResidualBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The member readings are one Gram inverse

Every reading of a dominating set at its own inverse gap is an entry of the
inverse of the set's own GRAM matrix, shifted by one.  For a matrix `V` whose
columns are the member atoms (`Gtz.matrix_pushThrough_inv`):

  `Vᵀ(VVᵀ − 1)⁻¹V = 1 + (VᵀV − 1)⁻¹` .

The left side is the matrix of readings of the members at the gap
`A = VVᵀ − 1`; the right side is built from the member Gram `B = VᵀV` alone.
So the whole floor system of a four-set — four inequalities about a `3×3`
inverse — becomes the statement that the diagonal of ONE `4×4` inverse is
nonnegative (`Gtz.member_reading_eq_gram_inv`):

  `r_a = 1 + ((B − 1)⁻¹)_{aa}` ,  and the floor `r_a ≥ 1` is
  `((B − 1)⁻¹)_{aa} ≥ 0` .

The identity is dimension-free and needs no positivity: only that both
shifted matrices are invertible.  It is the push-through identity
`C(C−1)⁻¹ = 1 + (C−1)⁻¹` transported across `V`.

## What it buys

The readings of a four-set live on a `3×3` inverse, so they satisfy hidden
relations that are invisible in the reading coordinates: the four member
atoms of a rank-three gap are linearly DEPENDENT, and the dependency is
exactly the kernel vector of `V`.  On the Gram side that dependency is
explicit — `B` is singular on it and `B − 1` has the eigenvalue `−1` there —
so the four readings are constrained by one linear relation that the
`3×3` picture hides.  A certificate written in the Gram coordinates carries
that relation for free.
-/

namespace Gtz

open Matrix

/-- **THE PUSH-THROUGH INVERSE.**  For any rectangular `V` over a commutative
ring, whenever both shifted products are invertible,

  `Vᵀ(VVᵀ − 1)⁻¹V = 1 + (VᵀV − 1)⁻¹` .

No positivity and no square shape: the identity is the transported form of
`C(C−1)⁻¹ = 1 + (C−1)⁻¹`. -/
theorem matrix_pushThrough_inv {m n : ℕ} (V : Matrix (Fin m) (Fin n) ℝ)
    (hC : IsUnit (V * Vᵀ - 1).det) (hB : IsUnit (Vᵀ * V - 1).det) :
    Vᵀ * (V * Vᵀ - 1)⁻¹ * V = 1 + (Vᵀ * V - 1)⁻¹ := by
  set C : Matrix (Fin m) (Fin m) ℝ := V * Vᵀ with hCdef
  set B : Matrix (Fin n) (Fin n) ℝ := Vᵀ * V with hBdef
  -- the key step: C(C−1)⁻¹ = 1 + (C−1)⁻¹
  have hCstep : C * (C - 1)⁻¹ = 1 + (C - 1)⁻¹ := by
    have h1 : C * (C - 1)⁻¹ = ((C - 1) + 1) * (C - 1)⁻¹ := by
      congr 1
      abel
    rw [h1, Matrix.add_mul, Matrix.one_mul, Matrix.mul_nonsing_inv _ hC]
  have hBV : B * Vᵀ = Vᵀ * C := by
    rw [hBdef, hCdef, Matrix.mul_assoc]
  -- the right inverse of B − 1
  have hright : (B - 1) * (Vᵀ * (C - 1)⁻¹ * V - 1) = 1 := by
    have hexp : (B - 1) * (Vᵀ * (C - 1)⁻¹ * V - 1)
        = B * (Vᵀ * (C - 1)⁻¹ * V) - B - Vᵀ * (C - 1)⁻¹ * V + 1 := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      abel
    have hfirst : B * (Vᵀ * (C - 1)⁻¹ * V) = B + Vᵀ * (C - 1)⁻¹ * V := by
      calc B * (Vᵀ * (C - 1)⁻¹ * V)
          = (B * Vᵀ) * ((C - 1)⁻¹ * V) := by
            simp only [Matrix.mul_assoc]
        _ = (Vᵀ * C) * ((C - 1)⁻¹ * V) := by rw [hBV]
        _ = Vᵀ * (C * (C - 1)⁻¹) * V := by
            simp only [Matrix.mul_assoc]
        _ = Vᵀ * (1 + (C - 1)⁻¹) * V := by rw [hCstep]
        _ = B + Vᵀ * (C - 1)⁻¹ * V := by
            rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hBdef]
    rw [hexp, hfirst]
    abel
  have hinv : (B - 1)⁻¹ = Vᵀ * (C - 1)⁻¹ * V - 1 :=
    Matrix.inv_eq_right_inv hright
  rw [hinv]
  abel

/-- **THE MEMBER READING IS A GRAM ENTRY.**  The reading of the member `a` at
the inverse gap — the `(a,a)` entry of `Vᵀ(VVᵀ−1)⁻¹V` — is one plus the
matching diagonal entry of the inverse shifted Gram.  The floor `r_a ≥ 1`
therefore says exactly that that entry is nonnegative. -/
theorem member_reading_eq_gram_inv {m n : ℕ} (V : Matrix (Fin m) (Fin n) ℝ)
    (hC : IsUnit (V * Vᵀ - 1).det) (hB : IsUnit (Vᵀ * V - 1).det)
    (a : Fin n) :
    ((Vᵀ * (V * Vᵀ - 1)⁻¹ * V : Matrix (Fin n) (Fin n) ℝ)) a a
      = 1 + ((Vᵀ * V - 1)⁻¹ : Matrix (Fin n) (Fin n) ℝ) a a := by
  have hentry := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℝ => M a a)
    (matrix_pushThrough_inv V hC hB)
  simpa only [Matrix.add_apply, Matrix.one_apply_eq] using hentry

end Gtz

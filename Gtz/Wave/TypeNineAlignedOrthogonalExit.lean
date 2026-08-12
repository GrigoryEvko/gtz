import Gtz.Wave.OrbitFourCoefficientBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/--
The scalar core of the full-rank aligned type-nine exit.

The coefficient frame is
`(e₁, e₂, endpointResidual, privateResidual)`.  Its Gram matrix is
`diag(1,1,A,K)`.  The displayed equations are precisely local tightness of
the four rows

* `x e₁ + y e₂`,
* `b e₁ + endpointResidual`,
* `e e₂ + scale endpointResidual`, and
* `h e₁ + privateResidual`.

The determinant `e*x + scale*b*y` says that the selected pair row and the
aligned exchange span the full `(e₁,e₂)` plane.  Self-adjointness in the
orthogonal frame then fixes all four diagonal entries of the coefficient
projection. -/
theorem typeNine_aligned_orthogonal_diagonal
    {R : Matrix (Fin 4) (Fin 4) ℝ}
    {A K x y b e h scale d0 d1 d2 d4 : ℝ}
    (hdet : e * x + scale * b * y ≠ 0)
    (hy : y ≠ 0) (hb : b ≠ 0) (he : e ≠ 0) (hK : K ≠ 0)
    (hself01 : R 0 1 = R 1 0)
    (hself02 : R 0 2 = A * R 2 0)
    (hself12 : R 1 2 = A * R 2 1)
    (hself03 : R 0 3 = K * R 3 0)
    (hp0Endpoint : x * R 2 0 + y * R 2 1 = 0)
    (hp0One : x * R 0 0 + y * R 0 1 = d1 * x)
    (hp1Endpoint : b * R 2 0 + R 2 2 = d0)
    (hp1One : b * R 0 0 + R 0 2 = d1 * b)
    (hp2Endpoint : e * R 2 1 + scale * R 2 2 = scale * d0)
    (hp2Two : e * R 1 1 + scale * R 1 2 = d2 * e)
    (hp3One : h * R 0 0 + R 0 3 = d1 * h)
    (hp3Private : h * R 3 0 + R 3 3 = d4) :
    R 0 0 = d1 ∧ R 1 1 = d2 ∧ R 2 2 = d0 ∧ R 3 3 = d4
      ∧ R 0 1 = 0 ∧ R 1 0 = 0 ∧ R 0 2 = 0 ∧ R 1 2 = 0
      ∧ R 2 0 = 0 ∧ R 2 1 = 0 ∧ R 0 3 = 0 ∧ R 3 0 = 0 := by
  have hpairEquation : e * R 2 1 - scale * b * R 2 0 = 0 := by
    calc
      e * R 2 1 - scale * b * R 2 0
          = (e * R 2 1 + scale * R 2 2 - scale * d0)
              - scale * (b * R 2 0 + R 2 2 - d0) := by ring
      _ = 0 := by rw [hp2Endpoint, hp1Endpoint]; ring
  have hfactor : (e * x + scale * b * y) * R 2 0 = 0 := by
    calc
      (e * x + scale * b * y) * R 2 0
          = e * (x * R 2 0 + y * R 2 1)
              - y * (e * R 2 1 - scale * b * R 2 0) := by ring
      _ = 0 := by rw [hp0Endpoint, hpairEquation]; ring
  have h20 : R 2 0 = 0 := (mul_eq_zero.mp hfactor).resolve_left hdet
  have h21 : R 2 1 = 0 := by
    have hy21 : y * R 2 1 = 0 := by
      calc
        y * R 2 1 = x * R 2 0 + y * R 2 1 := by rw [h20]; ring
        _ = 0 := hp0Endpoint
    exact (mul_eq_zero.mp hy21).resolve_left hy
  have h22 : R 2 2 = d0 := by
    calc
      R 2 2 = b * R 2 0 + R 2 2 := by rw [h20]; ring
      _ = d0 := hp1Endpoint
  have h02 : R 0 2 = 0 := by rw [hself02, h20, mul_zero]
  have h12 : R 1 2 = 0 := by rw [hself12, h21, mul_zero]
  have h00 : R 0 0 = d1 := by
    have hb00 : b * R 0 0 = b * d1 := by
      calc
        b * R 0 0 = b * R 0 0 + R 0 2 := by rw [h02]; ring
        _ = d1 * b := hp1One
        _ = b * d1 := by ring
    exact mul_left_cancel₀ hb hb00
  have h11 : R 1 1 = d2 := by
    have he11 : e * R 1 1 = e * d2 := by
      calc
        e * R 1 1 = e * R 1 1 + scale * R 1 2 := by rw [h12]; ring
        _ = d2 * e := hp2Two
        _ = e * d2 := by ring
    exact mul_left_cancel₀ he he11
  have h01 : R 0 1 = 0 := by
    have hy01 : y * R 0 1 = 0 := by
      calc
        y * R 0 1 = (x * R 0 0 + y * R 0 1) - d1 * x := by
          rw [h00]
          ring
        _ = 0 := by rw [hp0One]; ring
    exact (mul_eq_zero.mp hy01).resolve_left hy
  have h10 : R 1 0 = 0 := by rw [← hself01, h01]
  have h03 : R 0 3 = 0 := by
    calc
      R 0 3 = (h * R 0 0 + R 0 3) - d1 * h := by rw [h00]; ring
      _ = 0 := by rw [hp3One]; ring
  have h30 : R 3 0 = 0 := by
    have hK30 : K * R 3 0 = 0 := by linarith only [hself03, h03]
    exact (mul_eq_zero.mp hK30).resolve_left hK
  have h33 : R 3 3 = d4 := by
    calc
      R 3 3 = h * R 3 0 + R 3 3 := by rw [h30]; ring
      _ = d4 := hp3Private
  exact ⟨h00, h11, h22, h33, h01, h10, h02, h12, h20, h21, h03, h30⟩

/-- A rank-two idempotent cannot have the diagonal forced by the aligned
orthogonal frame at a negative chart point. -/
theorem false_of_typeNine_aligned_orthogonal_projection
    {R : Matrix (Fin 4) (Fin 4) ℝ}
    {A K x y b e h scale d0 d1 d2 d4 : ℝ}
    (hdet : e * x + scale * b * y ≠ 0)
    (hy : y ≠ 0) (hb : b ≠ 0) (he : e ≠ 0)
    (hK : K ≠ 0)
    (hself01 : R 0 1 = R 1 0)
    (hself02 : R 0 2 = A * R 2 0)
    (hself12 : R 1 2 = A * R 2 1)
    (hself03 : R 0 3 = K * R 3 0)
    (hp0Endpoint : x * R 2 0 + y * R 2 1 = 0)
    (hp0One : x * R 0 0 + y * R 0 1 = d1 * x)
    (hp1Endpoint : b * R 2 0 + R 2 2 = d0)
    (hp1One : b * R 0 0 + R 0 2 = d1 * b)
    (hp2Endpoint : e * R 2 1 + scale * R 2 2 = scale * d0)
    (hp2Two : e * R 1 1 + scale * R 1 2 = d2 * e)
    (hp3One : h * R 0 0 + R 0 3 = d1 * h)
    (hp3Private : h * R 3 0 + R 3 3 = d4)
    (hidempotent : R * R = R)
    (htrace : Matrix.trace R = 2)
    (hd0 : 0 ≤ d0) (hd4 : 0 ≤ d4) (hd1 : d1 < 1)
    (hshiftedSum : 2 * d0 + d1 + d2 + 2 * d4 < 1) : False := by
  obtain ⟨h00, h11, h22, h33, h01, h10, h02, h12, h20, h21, h03, h30⟩ :=
    typeNine_aligned_orthogonal_diagonal hdet hy hb he hK hself01 hself02
      hself12 hself03 hp0Endpoint hp0One hp1Endpoint hp1One
      hp2Endpoint hp2Two hp3One hp3Private
  have hidem00 := congrFun (congrFun hidempotent (0 : Fin 4)) (0 : Fin 4)
  rw [Matrix.mul_apply, Fin.sum_univ_four, h00, h01, h02, h03, h10] at hidem00
  have hd1poly : d1 * (d1 - 1) = 0 := by nlinarith only [hidem00]
  have hd1zero : d1 = 0 := by
    rcases mul_eq_zero.mp hd1poly with hzero | hone
    · exact hzero
    · linarith only [hone, hd1]
  have htraceEntries : R 0 0 + R 1 1 + R 2 2 + R 3 3 = 2 := by
    simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four] using htrace
  linarith only [htraceEntries, h00, h11, h22, h33, hd1zero,
    hd0, hd4, hshiftedSum]


end Gtz

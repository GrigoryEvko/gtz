import Gtz.Quantitative.ChartArgmaxIndexFloorTwo

import Gtz.Quantitative.FourActiveCoefficientProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

/--
The scalar exit for the aligned, full-row-rank orbit-four operator.

After restricting the chart projection to the four-dimensional positive tight-row
span, self-adjointness puts its matrix in the form calculated in the orbit-four
normal coordinates.  The equations below are the diagonal and two off-diagonal
entries of idempotence, while `htrace` records that the restricted projection has
rank two.  Shifted chart diagonals are strictly below one at a negative chart
point.  These facts are incompatible, independently of all remaining coordinates.
-/
theorem false_of_typeNine_aligned_operator_idempotence
    {K A d0 d1 d2 d5 u v : ℝ}
    (hK : 0 < K) (hA : 0 < A)
    (hd0 : d0 < 1) (hd1 : d1 < 1) (hd2 : d2 < 1) (hd5 : d5 < 1)
    (h00 : d1 * (d1 - 1) = 0)
    (h11 : K * u ^ 2 + d2 ^ 2 - d2 = 0)
    (h12 : K * u * v = 0)
    (h13 : K * u * (d2 + d5 - 1) = 0)
    (h22 : d0 ^ 2 - d0 + (K / A) * v ^ 2 = 0)
    (h23 : (K / A) * v * (d0 + d5 - 1) = 0)
    (h33 : K * u ^ 2 + d5 ^ 2 - d5 + (K / A) * v ^ 2 = 0)
    (htrace : d0 + d1 + d2 + d5 = 2) : False := by
  have hKne : K ≠ 0 := ne_of_gt hK
  have hAne : A ≠ 0 := ne_of_gt hA
  have hKAne : K / A ≠ 0 := div_ne_zero hKne hAne
  have hd1zero : d1 = 0 := by
    rcases mul_eq_zero.mp h00 with hd1zero | hd1one
    · exact hd1zero
    · linarith only [hd1, hd1one]
  by_cases hu : u = 0
  · by_cases hv : v = 0
    · have hd0poly : d0 ^ 2 - d0 = 0 := by simpa [hu, hv] using h22
      have hd2poly : d2 ^ 2 - d2 = 0 := by simpa [hu] using h11
      have hd5poly : d5 ^ 2 - d5 = 0 := by simpa [hu, hv] using h33
      have hd0zero : d0 = 0 := by
        have : d0 * (d0 - 1) = 0 := by nlinarith only [hd0poly]
        rcases mul_eq_zero.mp this with hd0zero | hd0one
        · exact hd0zero
        · linarith only [hd0, hd0one]
      have hd2zero : d2 = 0 := by
        have : d2 * (d2 - 1) = 0 := by nlinarith only [hd2poly]
        rcases mul_eq_zero.mp this with hd2zero | hd2one
        · exact hd2zero
        · linarith only [hd2, hd2one]
      have hd5zero : d5 = 0 := by
        have : d5 * (d5 - 1) = 0 := by nlinarith only [hd5poly]
        rcases mul_eq_zero.mp this with hd5zero | hd5one
        · exact hd5zero
        · linarith only [hd5, hd5one]
      linarith only [htrace, hd0zero, hd1zero, hd2zero, hd5zero]
    · have hvFactor : (K / A) * v ≠ 0 := mul_ne_zero hKAne hv
      have hd0d5 : d0 + d5 - 1 = 0 :=
        (mul_eq_zero.mp h23).resolve_left hvFactor
      have hd2poly : d2 ^ 2 - d2 = 0 := by simpa [hu] using h11
      have hd2zero : d2 = 0 := by
        have : d2 * (d2 - 1) = 0 := by nlinarith only [hd2poly]
        rcases mul_eq_zero.mp this with hd2zero | hd2one
        · exact hd2zero
        · linarith only [hd2, hd2one]
      linarith only [htrace, hd0d5, hd1zero, hd2zero]
  · have hvzero : v = 0 := by
      rcases mul_eq_zero.mp h12 with hKu | hvzero
      · exact (mul_ne_zero hKne hu hKu).elim
      · exact hvzero
    have hKu : K * u ≠ 0 := mul_ne_zero hKne hu
    have hd2d5 : d2 + d5 - 1 = 0 :=
      (mul_eq_zero.mp h13).resolve_left hKu
    have hd0poly : d0 ^ 2 - d0 = 0 := by simpa [hvzero] using h22
    have hd0zero : d0 = 0 := by
      have : d0 * (d0 - 1) = 0 := by nlinarith only [hd0poly]
      rcases mul_eq_zero.mp this with hd0zero | hd0one
      · exact hd0zero
      · linarith only [hd0, hd0one]
    linarith only [htrace, hd2d5, hd1zero, hd0zero]

/-- The four-by-four coordinate matrix whose scalar idempotence entries are used above. -/
noncomputable def typeNineAlignedOperator
    (K A b h d0 d1 d2 d5 u v : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![d1, -h * u, b * (d1 - d0) - h * v,
        h * (d1 - d5) - (K * b / A) * v;
     0, d2, 0, K * u;
     0, 0, d0, (K / A) * v;
     0, u, v, d5]

/-- Matrix-facing wrapper for `false_of_typeNine_aligned_operator_idempotence`.
Only five entries of `M²=M` are needed; the remaining orbit coordinates disappear. -/
theorem false_of_typeNine_aligned_operator_matrix
    {K A b h d0 d1 d2 d5 u v : ℝ}
    (hK : 0 < K) (hA : 0 < A)
    (hd0 : d0 < 1) (hd1 : d1 < 1) (hd2 : d2 < 1) (hd5 : d5 < 1)
    (hidempotent :
      typeNineAlignedOperator K A b h d0 d1 d2 d5 u v
          * typeNineAlignedOperator K A b h d0 d1 d2 d5 u v
        = typeNineAlignedOperator K A b h d0 d1 d2 d5 u v)
    (htrace : d0 + d1 + d2 + d5 = 2) : False := by
  have h00 := congrFun (congrFun hidempotent (0 : Fin 4)) (0 : Fin 4)
  have h11 := congrFun (congrFun hidempotent (1 : Fin 4)) (1 : Fin 4)
  have h12 := congrFun (congrFun hidempotent (1 : Fin 4)) (2 : Fin 4)
  have h13 := congrFun (congrFun hidempotent (1 : Fin 4)) (3 : Fin 4)
  have h22 := congrFun (congrFun hidempotent (2 : Fin 4)) (2 : Fin 4)
  have h23 := congrFun (congrFun hidempotent (2 : Fin 4)) (3 : Fin 4)
  have h33 := congrFun (congrFun hidempotent (3 : Fin 4)) (3 : Fin 4)
  norm_num [typeNineAlignedOperator, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.of_apply] at h00
  norm_num [typeNineAlignedOperator, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.of_apply] at h11
  norm_num [typeNineAlignedOperator, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.of_apply] at h12
  norm_num [typeNineAlignedOperator, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.of_apply] at h13
  norm_num [typeNineAlignedOperator, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.of_apply] at h22
  norm_num [typeNineAlignedOperator, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.of_apply] at h23
  norm_num [typeNineAlignedOperator, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.of_apply] at h33
  have h00' : d1 * (d1 - 1) = 0 := by nlinarith only [h00]
  have h11' : K * u ^ 2 + d2 ^ 2 - d2 = 0 := by nlinarith only [h11]
  have h12' : K * u * v = 0 := by
    rcases h12 with (hKzero | huzero) | hvzero
    · simp [hKzero]
    · simp [huzero]
    · simp [hvzero]
  have h13' : K * u * (d2 + d5 - 1) = 0 := by nlinarith only [h13]
  have h22' : d0 ^ 2 - d0 + (K / A) * v ^ 2 = 0 := by nlinarith only [h22]
  have h23' : (K / A) * v * (d0 + d5 - 1) = 0 := by nlinarith only [h23]
  have h33' : K * u ^ 2 + d5 ^ 2 - d5 + (K / A) * v ^ 2 = 0 := by
    nlinarith only [h33]
  exact false_of_typeNine_aligned_operator_idempotence hK hA hd0 hd1 hd2 hd5
    h00' h11' h12' h13' h22' h23' h33' htrace

/-- The aligned phase also exits at trace level once nonnegative shifted
diagonals are retained.  The longer idempotence theorem above is useful as an
independent check, but is not needed at a crux. -/
theorem false_of_typeNine_aligned_trace
    {d0 d1 d2 d3 d4 d5 : ℝ}
    (hd3 : 0 ≤ d3) (hd4 : 0 ≤ d4)
    (hrestrictedTrace : d0 + d1 + d2 + d5 = 2)
    (hshiftedSum : d0 + d1 + d2 + d3 + d4 + d5 < 1) : False := by
  linarith

/-- Matrix-facing aligned trace exit. -/
theorem false_of_typeNine_aligned_projection_trace
    {M : Matrix (Fin 4) (Fin 4) ℝ} {d0 d1 d2 d3 d4 d5 : ℝ}
    (hd3 : 0 ≤ d3) (hd4 : 0 ≤ d4)
    (hdiagZero : M 0 0 = d1) (hdiagOne : M 1 1 = d2)
    (hdiagTwo : M 2 2 = d0) (hdiagThree : M 3 3 = d5)
    (htrace : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2)
    (hshiftedSum : d0 + d1 + d2 + d3 + d4 + d5 < 1) : False := by
  have hrestrictedTrace : d0 + d1 + d2 + d5 = 2 := by
    rw [hdiagZero, hdiagOne, hdiagTwo, hdiagThree] at htrace
    linarith
  exact false_of_typeNine_aligned_trace hd3 hd4 hrestrictedTrace hshiftedSum

/--
The reflected phase exits already at trace level.  Local tightness fixes the
two shared-row diagonal entries of the restricted projection to
`(d0+d3)/2`, and the private row contributes `d4=d5`.  Rank-two trace then
forces `m00+d0+d3+d4=2`.  Since a projection diagonal is at most one, this
is incompatible with the negative-chart identity `sum d < 1`.
-/
theorem false_of_typeNine_reflected_trace
    {m00 d0 d1 d2 d3 d4 d5 : ℝ}
    (hm00 : m00 ≤ 1)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd5 : 0 ≤ d5)
    (hrestrictedTrace : m00 + d0 + d3 + d4 = 2)
    (hshiftedSum : d0 + d1 + d2 + d3 + d4 + d5 < 1) : False := by
  linarith

/-- Matrix-facing reflected-phase trace exit. -/
theorem false_of_typeNine_reflected_projection
    {M : Matrix (Fin 4) (Fin 4) ℝ} {d0 d1 d2 d3 d4 d5 : ℝ}
    (hsymmetric : Matrix.transpose M = M) (hidempotent : M * M = M)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd5 : 0 ≤ d5)
    (hdiagOne : M 1 1 = (d0 + d3) / 2)
    (hdiagTwo : M 2 2 = (d0 + d3) / 2)
    (hdiagThree : M 3 3 = d4)
    (htrace : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2)
    (hshiftedSum : d0 + d1 + d2 + d3 + d4 + d5 < 1) : False := by
  have hm00 : M 0 0 ≤ 1 :=
    diagonal_le_one_of_symmetricIdempotent hsymmetric hidempotent 0
  have hrestrictedTrace : M 0 0 + d0 + d3 + d4 = 2 := by
    rw [hdiagOne, hdiagTwo, hdiagThree] at htrace
    linarith
  exact false_of_typeNine_reflected_trace hm00 hd1 hd2 hd5
    hrestrictedTrace hshiftedSum

/--
Coordinate interface for the reflected orbit-four exit.  The six displayed
equations are precisely the local tightness equations at the two shared
coordinates and at one private coordinate.  No other entry of the ambient
projection is used.
-/
theorem false_of_typeNine_reflected_weighted_coordinates
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    {a r k d0 d1 d2 d3 d4 d5 : ℝ}
    (hsymmetric : Matrix.transpose M = M) (hidempotent : M * M = M)
    (ha : a ≠ 0) (hr : r ≠ 0) (hk : k ≠ 0)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd5 : 0 ≤ d5)
    (hfirstZero : a * M 1 1 + r * M 2 1 = d0 * a)
    (hfirstThree : a * M 1 1 - r * M 2 1 = d3 * a)
    (hsecondZero : a * M 1 2 + r * M 2 2 = d0 * r)
    (hsecondThree : a * M 1 2 - r * M 2 2 = -(d3 * r))
    (hprivate : k * M 3 3 = d4 * k)
    (htrace : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2)
    (hshiftedSum : d0 + d1 + d2 + d3 + d4 + d5 < 1) : False := by
  have hdiagOne : M 1 1 = (d0 + d3) / 2 := by
    apply (mul_left_cancel₀ ha)
    nlinarith only [hfirstZero, hfirstThree]
  have hdiagTwo : M 2 2 = (d0 + d3) / 2 := by
    apply (mul_left_cancel₀ hr)
    nlinarith only [hsecondZero, hsecondThree]
  have hdiagThree : M 3 3 = d4 := by
    apply (mul_left_cancel₀ hk)
    linarith only [hprivate]
  exact false_of_typeNine_reflected_projection hsymmetric hidempotent
    hd1 hd2 hd5 hdiagOne hdiagTwo hdiagThree htrace hshiftedSum

/-- Trace is invariant under a nonsingular two-by-two intertwining.  This is
the phase-robust form needed by the actual orbit-four endpoint rows; no equal
magnitude normalization is required. -/
theorem twoByTwo_trace_eq_of_diagonal_intertwines
    {a r c f m11 m12 m21 m22 d0 d3 : ℝ}
    (hdet : a * f - r * c ≠ 0)
    (hzeroLeft : a * m11 + r * m21 = d0 * a)
    (hzeroRight : a * m12 + r * m22 = d0 * r)
    (hthreeLeft : c * m11 + f * m21 = d3 * c)
    (hthreeRight : c * m12 + f * m22 = d3 * f) :
    m11 + m22 = d0 + d3 := by
  have hleft : (a * f - r * c) * m11
      = f * (d0 * a) - r * (d3 * c) := by
    calc
      (a * f - r * c) * m11
          = f * (a * m11 + r * m21)
              - r * (c * m11 + f * m21) := by ring
      _ = f * (d0 * a) - r * (d3 * c) := by
        rw [hzeroLeft, hthreeLeft]
  have hright : (a * f - r * c) * m22
      = a * (d3 * f) - c * (d0 * r) := by
    calc
      (a * f - r * c) * m22
          = a * (c * m12 + f * m22)
              - c * (a * m12 + r * m22) := by ring
      _ = a * (d3 * f) - c * (d0 * r) := by
        rw [hthreeRight, hzeroRight]
  have hfactor : (a * f - r * c)
      * (m11 + m22 - d0 - d3) = 0 := by
    rw [mul_sub, mul_sub, mul_add, hleft, hright]
    ring
  have hzero : m11 + m22 - d0 - d3 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hdet
  linarith

/-- Actual-coordinate reflected-phase exit.  The endpoint restriction matrix
need only be nonsingular; its trace contribution is automatically `d0+d3`. -/
theorem false_of_typeNine_reflected_general_coordinates
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    {a r c f k d0 d1 d2 d3 d4 d5 : ℝ}
    (hsymmetric : Matrix.transpose M = M) (hidempotent : M * M = M)
    (hdet : a * f - r * c ≠ 0) (hk : k ≠ 0)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd5 : 0 ≤ d5)
    (hzeroLeft : a * M 1 1 + r * M 2 1 = d0 * a)
    (hzeroRight : a * M 1 2 + r * M 2 2 = d0 * r)
    (hthreeLeft : c * M 1 1 + f * M 2 1 = d3 * c)
    (hthreeRight : c * M 1 2 + f * M 2 2 = d3 * f)
    (hprivate : k * M 3 3 = d4 * k)
    (htrace : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2)
    (hshiftedSum : d0 + d1 + d2 + d3 + d4 + d5 < 1) : False := by
  have hmiddle : M 1 1 + M 2 2 = d0 + d3 :=
    twoByTwo_trace_eq_of_diagonal_intertwines hdet hzeroLeft hzeroRight
      hthreeLeft hthreeRight
  have hdiagThree : M 3 3 = d4 := by
    apply (mul_left_cancel₀ hk)
    linarith only [hprivate]
  have hm00 : M 0 0 ≤ 1 :=
    diagonal_le_one_of_symmetricIdempotent hsymmetric hidempotent 0
  have hrestrictedTrace : M 0 0 + d0 + d3 + d4 = 2 := by
    linarith only [htrace, hmiddle, hdiagThree]
  exact false_of_typeNine_reflected_trace hm00 hd1 hd2 hd5
    hrestrictedTrace hshiftedSum


end Gtz

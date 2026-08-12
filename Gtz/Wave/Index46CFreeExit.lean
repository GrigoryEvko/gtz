import Gtz.Wave.TypeNineAlignedOperatorExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

noncomputable def indexFortySixRowZero (a b : ℝ) : Fin 4 → ℝ :=
  ![1, a, b, 0]

noncomputable def indexFortySixRowOne : Fin 4 → ℝ :=
  ![0, 1, 0, 0]

noncomputable def indexFortySixRowTwo (c : ℝ) : Fin 4 → ℝ :=
  ![1, 0, 0, c]

noncomputable def indexFortySixRowWing (z : ℝ) : Fin 4 → ℝ :=
  ![0, 0, 1, z]

noncomputable def indexFortySixLeakZero (alpha : ℝ) : Fin 4 → ℝ :=
  ![0, 0, 0, alpha]

noncomputable def indexFortySixLeakOne (z h : ℝ) : Fin 4 → ℝ :=
  ![0, 0, -(z * h), h]

noncomputable def indexFortySixLeakOneGeneral
    (z h kappa : ℝ) : Fin 4 → ℝ :=
  ![0, 0, kappa - z * h, h]

noncomputable def indexFortySixLeakTwo (c h nu : ℝ) : Fin 4 → ℝ :=
  ![0, c * h, nu, 0]

noncomputable def indexFortySixLeakWing (rho : ℝ) : Fin 4 → ℝ :=
  ![rho, 0, 0, 0]

noncomputable def indexFortySixLeakWingGeneral
    (rho kappa : ℝ) : Fin 4 → ℝ :=
  ![rho, kappa, 0, 0]

noncomputable def indexFortySixScaledGram (a b c z : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  let n0 := 1 + a ^ 2 + b ^ 2
  let nc := 1 + c ^ 2
  let nw := 1 + z ^ 2
  (nc * nw) • atomMatrix (indexFortySixRowZero a b)
    + (2 * n0 * nc * nw) • atomMatrix indexFortySixRowOne
    + (n0 * nw) • atomMatrix (indexFortySixRowTwo c)
    + (2 * n0 * nc) • atomMatrix (indexFortySixRowWing z)

private theorem indexFortySix_mul_atomMatrix_apply
    (M : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ)
    (i j : Fin 4) :
    (M * atomMatrix v) i j = (M *ᵥ v) i * v j := by
  simp only [Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem indexFortySix_atomMatrix_mul_apply
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hsymmetric : M.transpose = M)
    (v : Fin 4 → ℝ) (i j : Fin 4) :
    (atomMatrix v * M) i j = v i * (M *ᵥ v) j := by
  simp only [Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hentry := congrFun (congrFun hsymmetric k) j
  change M j k = M k j at hentry
  rw [← hentry]
  ring

/-- Idempotence first separates the last support leaf into the budget branch
`p+q=1` and the sparse-leak branch `kappa=0`. -/
theorem indexFortySix_idempotence_factor
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    {z p q h rho kappa : ℝ}
    (hsymmetric : M.transpose = M) (hidempotent : M * M = M)
    (hrowOne : M *ᵥ indexFortySixRowOne =
      p • indexFortySixRowOne + indexFortySixLeakOneGeneral z h kappa)
    (hrowWing : M *ᵥ indexFortySixRowWing z =
      q • indexFortySixRowWing z + indexFortySixLeakWingGeneral rho kappa) :
    (p + q - 1) * kappa = 0 := by
  have h12 := congrFun (congrFun hidempotent (1 : Fin 4)) (2 : Fin 4)
  have h13 := congrFun (congrFun hidempotent (1 : Fin 4)) (3 : Fin 4)
  have hrowOne0 := congrFun hrowOne (0 : Fin 4)
  have hrowOne1 := congrFun hrowOne (1 : Fin 4)
  have hrowOne2 := congrFun hrowOne (2 : Fin 4)
  have hrowOne3 := congrFun hrowOne (3 : Fin 4)
  have hrowWing2 := congrFun hrowWing (2 : Fin 4)
  have hrowWing3 := congrFun hrowWing (3 : Fin 4)
  have h10 := congrFun (congrFun hsymmetric (0 : Fin 4)) (1 : Fin 4)
  have h21 := congrFun (congrFun hsymmetric (1 : Fin 4)) (2 : Fin 4)
  have h31 := congrFun (congrFun hsymmetric (1 : Fin 4)) (3 : Fin 4)
  norm_num [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    indexFortySixRowOne, indexFortySixRowWing,
    indexFortySixLeakOneGeneral, indexFortySixLeakWingGeneral,
    Pi.add_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.tail_cons,
    Matrix.of_apply] at h12 h13 hrowOne0 hrowOne1 hrowOne2 hrowOne3 hrowWing2 hrowWing3 h10 h21 h31
  have hM10 : M 1 0 = 0 := by linarith only [h10, hrowOne0]
  have hM12 : M 1 2 = kappa - z * h := by
    linarith only [h21, hrowOne2]
  have hM13 : M 1 3 = h := by linarith only [h31, hrowOne3]
  rw [hM10, hrowOne1, hM12, hM13] at h12 h13
  linear_combination h12 + z * h13
    - (kappa - z * h) * hrowWing2 - h * hrowWing3

/-- In the zero-`kappa` branch, commutation with the equal-row-norm Gram
eliminates all four remaining leaks.  The fourth coordinate `c` is independent;
no relation such as `c = z*b` is used. -/
theorem indexFortySix_leaks_eq_zero_of_commutes
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    {a b c z d0 p d2 q alpha h nu rho : ℝ}
    (hsymmetric : M.transpose = M)
    (ha : a ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0)
    (hrowZero : M *ᵥ indexFortySixRowZero a b =
      d0 • indexFortySixRowZero a b + indexFortySixLeakZero alpha)
    (hrowOne : M *ᵥ indexFortySixRowOne =
      p • indexFortySixRowOne + indexFortySixLeakOne z h)
    (hrowTwo : M *ᵥ indexFortySixRowTwo c =
      d2 • indexFortySixRowTwo c + indexFortySixLeakTwo c h nu)
    (hrowWing : M *ᵥ indexFortySixRowWing z =
      q • indexFortySixRowWing z + indexFortySixLeakWing rho)
    (hcommutes : M * indexFortySixScaledGram a b c z =
      indexFortySixScaledGram a b c z * M) :
    h = 0 ∧ alpha = 0 ∧ rho = 0 ∧ nu = 0 := by
  have h01 := congrFun (congrFun hcommutes (0 : Fin 4)) (1 : Fin 4)
  have h13 := congrFun (congrFun hcommutes (1 : Fin 4)) (3 : Fin 4)
  have h03 := congrFun (congrFun hcommutes (0 : Fin 4)) (3 : Fin 4)
  have h02 := congrFun (congrFun hcommutes (0 : Fin 4)) (2 : Fin 4)
  simp only [indexFortySixScaledGram, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply, Matrix.smul_apply,
    indexFortySix_mul_atomMatrix_apply,
    indexFortySix_atomMatrix_mul_apply M hsymmetric] at h01 h13 h03 h02
  rw [hrowZero, hrowOne, hrowTwo, hrowWing] at h01 h13 h03 h02
  norm_num [indexFortySixRowZero, indexFortySixRowOne,
    indexFortySixRowTwo, indexFortySixRowWing, indexFortySixLeakZero,
    indexFortySixLeakOne, indexFortySixLeakTwo, indexFortySixLeakWing,
    Pi.add_apply, Pi.smul_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.tail_cons, Matrix.of_apply] at h01 h13 h03 h02
  have hn0 : 0 < 1 + a ^ 2 + b ^ 2 := by positivity
  have hnc : 0 < 1 + c ^ 2 := by positivity
  have hnw : 0 < 1 + z ^ 2 := by positivity
  have hh : h = 0 := by
    rcases h01 with (hn0zero | hnwzero) | hczero | hh
    · nlinarith only [hn0, hn0zero]
    · nlinarith only [hnw, hnwzero]
    · exact (hc hczero).elim
    · exact hh
  have halpha : alpha = 0 := by
    rw [hh] at h13
    have hfactor : ((1 + c ^ 2) * (1 + z ^ 2) * a) * alpha = 0 := by
      nlinarith only [h13]
    exact (mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero (mul_ne_zero (ne_of_gt hnc) (ne_of_gt hnw)) ha)
  have hrho : rho = 0 := by
    rw [halpha] at h03
    have hfactor : (2 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * z) * rho = 0 := by
      nlinarith only [h03]
    exact (mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by norm_num) (ne_of_gt hn0)) (ne_of_gt hnc)) hz)
  have hnu : nu = 0 := by
    rw [hrho] at h02
    have hfactor : ((1 + a ^ 2 + b ^ 2) * (1 + z ^ 2)) * nu = 0 := by
      nlinarith only [h02]
    exact (mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero (ne_of_gt hn0) (ne_of_gt hnw))
  exact ⟨hh, halpha, hrho, hnu⟩

/-- Three mutually nonorthogonal eigenrows already contradict a symmetric
rank-two coefficient projection.  This entrywise proof avoids a separate
finrank argument and remains valid on the exceptional plane `c = -b*z`. -/
theorem false_of_indexFortySix_common_eigenrows
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    {a b z lambda : ℝ}
    (hsymmetric : M.transpose = M) (hidempotent : M * M = M)
    (htrace : Matrix.trace M = 2)
    (hb : b ≠ 0) (hz : z ≠ 0)
    (hrowZero : M *ᵥ indexFortySixRowZero a b =
      lambda • indexFortySixRowZero a b)
    (hrowOne : M *ᵥ indexFortySixRowOne =
      lambda • indexFortySixRowOne)
    (hrowWing : M *ᵥ indexFortySixRowWing z =
      lambda • indexFortySixRowWing z) : False := by
  have hzero0 := congrFun hrowZero (0 : Fin 4)
  have hzero3 := congrFun hrowZero (3 : Fin 4)
  have hone0 := congrFun hrowOne (0 : Fin 4)
  have hone1 := congrFun hrowOne (1 : Fin 4)
  have hone2 := congrFun hrowOne (2 : Fin 4)
  have hone3 := congrFun hrowOne (3 : Fin 4)
  have hwing0 := congrFun hrowWing (0 : Fin 4)
  have hwing2 := congrFun hrowWing (2 : Fin 4)
  have hwing3 := congrFun hrowWing (3 : Fin 4)
  have h03sym := congrFun (congrFun hsymmetric (3 : Fin 4)) (0 : Fin 4)
  have h13sym := congrFun (congrFun hsymmetric (3 : Fin 4)) (1 : Fin 4)
  have h23sym := congrFun (congrFun hsymmetric (3 : Fin 4)) (2 : Fin 4)
  have hidem03 := congrFun (congrFun hidempotent (0 : Fin 4)) (3 : Fin 4)
  have hidem11 := congrFun (congrFun hidempotent (1 : Fin 4)) (1 : Fin 4)
  have htraceEntries : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2 := by
    simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four] using htrace
  norm_num [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    indexFortySixRowZero, indexFortySixRowOne, indexFortySixRowWing,
    Pi.smul_apply, Matrix.transpose_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.tail_cons,
    Matrix.of_apply] at hzero0 hzero3 hone0 hone1 hone2 hone3 hwing0 hwing2 hwing3 h03sym h13sym h23sym hidem03 hidem11
  have he00 : M 0 0 - lambda - b * z * M 0 3 = 0 := by
    linear_combination hzero0 - a * hone0 - b * hwing0
  have he11 : M 1 1 - lambda = 0 := by linarith only [hone1]
  have he02 : M 0 2 + z * M 0 3 = 0 := by linarith only [hwing0]
  have hM13 : M 1 3 = 0 := by linarith only [h13sym, hone3]
  have he23 : b * M 2 3 + M 0 3 = 0 := by
    rw [← h03sym, ← h23sym, hone3] at hzero3
    nlinarith only [hzero3]
  have he22 : M 2 2 + z * M 2 3 - lambda = 0 := by
    nlinarith only [hwing2]
  have he33 : M 2 3 + z * M 3 3 - lambda * z = 0 := by
    rw [← h23sym] at hwing3
    nlinarith only [hwing3]
  have hlambdaPoly : lambda ^ 2 - lambda = 0 := by
    rw [hone0, hone1, hone2, hone3] at hidem11
    nlinarith only [hidem11]
  have htracePoly :
      b * z * (4 * lambda - 2)
        + M 0 3 * (b ^ 2 * z ^ 2 + z ^ 2 + 1) = 0 := by
    linear_combination b * z * htraceEntries - b * z * he00
      - b * z * he11 - b * z * he22 - b * he33
      + (z ^ 2 + 1) * he23
  have hidemPoly :
      b * z * M 0 3 * (2 * lambda - 1)
        + (M 0 3) ^ 2 * (b ^ 2 * z ^ 2 + z ^ 2 + 1) = 0 := by
    linear_combination b * z * hidem03 - b * z * M 0 3 * he00
      - b * z * M 2 3 * he02 - b * M 0 3 * he33
      - b * z * M 1 3 * hone0 + M 0 3 * (z ^ 2 + 1) * he23
  have hbz : b * z ≠ 0 := mul_ne_zero hb hz
  have hlambdaHalf : 2 * lambda - 1 = 0 := by
    by_cases hx : M 0 3 = 0
    · rw [hx] at htracePoly
      have hfactor : (b * z) * (4 * lambda - 2) = 0 := by
        nlinarith only [htracePoly]
      have hfour : 4 * lambda - 2 = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left hbz
      nlinarith only [hfour]
    · have hfactor : M 0 3 *
          (b * z * (2 * lambda - 1)
            + M 0 3 * (b ^ 2 * z ^ 2 + z ^ 2 + 1)) = 0 := by
        nlinarith only [hidemPoly]
      have hbracket : b * z * (2 * lambda - 1)
          + M 0 3 * (b ^ 2 * z ^ 2 + z ^ 2 + 1) = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left hx
      have hsmall : b * z * (2 * lambda - 1) = 0 := by
        nlinarith only [htracePoly, hbracket]
      exact (mul_eq_zero.mp hsmall).resolve_left hbz
  nlinarith only [hlambdaPoly, hlambdaHalf]

private theorem eigenvalue_eq_of_symmetric_of_dotProduct_ne_zero
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    {left right : Fin 4 → ℝ} {leftValue rightValue : ℝ}
    (hsymmetric : M.transpose = M)
    (hleft : M *ᵥ left = leftValue • left)
    (hright : M *ᵥ right = rightValue • right)
    (hdot : left ⬝ᵥ right ≠ 0) : leftValue = rightValue := by
  have hbilinear := dot_mulVec_comm hsymmetric left right
  rw [hleft, hright] at hbilinear
  simp only [dotProduct_smul, smul_eq_mul] at hbilinear
  rw [dotProduct_comm right left] at hbilinear
  have hfactor : (rightValue - leftValue) * (left ⬝ᵥ right) = 0 := by
    nlinarith only [hbilinear]
  have hvalue := (mul_eq_zero.mp hfactor).resolve_right hdot
  linarith only [hvalue]

/-- Complete abstract exit for the final reflected four-support leaf.  All
normal-form coefficients remain independent, including `c`. -/
theorem false_of_indexFortySix_cFree
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    {a b c z d0 p d2 q alpha h nu rho kappa : ℝ}
    (hsymmetric : M.transpose = M) (hidempotent : M * M = M)
    (htrace : Matrix.trace M = 2)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0)
    (hd0 : 0 ≤ d0) (hd2 : 0 ≤ d2)
    (hshiftedSum : d0 + 2 * p + d2 + 2 * q < 1)
    (hrowZero : M *ᵥ indexFortySixRowZero a b =
      d0 • indexFortySixRowZero a b + indexFortySixLeakZero alpha)
    (hrowOne : M *ᵥ indexFortySixRowOne =
      p • indexFortySixRowOne + indexFortySixLeakOneGeneral z h kappa)
    (hrowTwo : M *ᵥ indexFortySixRowTwo c =
      d2 • indexFortySixRowTwo c + indexFortySixLeakTwo c h nu)
    (hrowWing : M *ᵥ indexFortySixRowWing z =
      q • indexFortySixRowWing z + indexFortySixLeakWingGeneral rho kappa)
    (hcommutes : M * indexFortySixScaledGram a b c z =
      indexFortySixScaledGram a b c z * M) : False := by
  have hfactor := indexFortySix_idempotence_factor hsymmetric hidempotent
    hrowOne hrowWing
  rcases mul_eq_zero.mp hfactor with hpq | hkappa
  · nlinarith only [hpq, hd0, hd2, hshiftedSum]
  · have hrowOneSparse : M *ᵥ indexFortySixRowOne =
        p • indexFortySixRowOne + indexFortySixLeakOne z h := by
      simpa [indexFortySixLeakOneGeneral, indexFortySixLeakOne, hkappa] using hrowOne
    have hrowWingSparse : M *ᵥ indexFortySixRowWing z =
        q • indexFortySixRowWing z + indexFortySixLeakWing rho := by
      simpa [indexFortySixLeakWingGeneral, indexFortySixLeakWing, hkappa] using hrowWing
    obtain ⟨hh, halpha, hrho, hnu⟩ :=
      indexFortySix_leaks_eq_zero_of_commutes hsymmetric ha hc hz hrowZero
        hrowOneSparse hrowTwo hrowWingSparse hcommutes
    have hrowZeroEigen : M *ᵥ indexFortySixRowZero a b =
        d0 • indexFortySixRowZero a b := by
      rw [hrowZero]
      funext i
      fin_cases i <;> simp [indexFortySixLeakZero, halpha]
    have hrowOneEigen : M *ᵥ indexFortySixRowOne =
        p • indexFortySixRowOne := by
      rw [hrowOneSparse]
      funext i
      fin_cases i <;> simp [indexFortySixLeakOne, hh]
    have hrowWingEigen : M *ᵥ indexFortySixRowWing z =
        q • indexFortySixRowWing z := by
      rw [hrowWingSparse]
      funext i
      fin_cases i <;> simp [indexFortySixLeakWing, hrho]
    have hdotOne : indexFortySixRowZero a b ⬝ᵥ indexFortySixRowOne ≠ 0 := by
      simpa [indexFortySixRowZero, indexFortySixRowOne, dotProduct,
        Fin.sum_univ_four] using ha
    have hdotWing : indexFortySixRowZero a b ⬝ᵥ indexFortySixRowWing z ≠ 0 := by
      simpa [indexFortySixRowZero, indexFortySixRowWing, dotProduct,
        Fin.sum_univ_four] using hb
    have hdp : d0 = p :=
      eigenvalue_eq_of_symmetric_of_dotProduct_ne_zero hsymmetric
        hrowZeroEigen hrowOneEigen hdotOne
    have hdq : d0 = q :=
      eigenvalue_eq_of_symmetric_of_dotProduct_ne_zero hsymmetric
        hrowZeroEigen hrowWingEigen hdotWing
    apply false_of_indexFortySix_common_eigenrows hsymmetric hidempotent htrace hb hz
      hrowZeroEigen
    · simpa [← hdp] using hrowOneEigen
    · simpa [← hdq] using hrowWingEigen



end Gtz

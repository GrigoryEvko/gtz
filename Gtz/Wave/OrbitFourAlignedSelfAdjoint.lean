import Gtz.Wave.OrbitFourAlignedFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unnecessarySeqFocus false

namespace Gtz

open Matrix

/-- Self-adjointness of the ambient chart matrix gives precisely the four
weighted symmetry identities needed by the aligned scalar exit. -/
theorem orbitFourAlignedFrame_selfAdjoint_coordinates
    (P : Matrix (Fin 6) (Fin 6) ℝ)
    (R : Matrix (Fin 4) (Fin 4) ℝ)
    (a c k z : ℝ)
    (hsymm : P.transpose = P)
    (hrepresentation : P * orbitFourAlignedFrame a c k z
      = orbitFourAlignedFrame a c k z * R) :
    R 0 1 = R 1 0
      ∧ R 0 2 = (a ^ 2 + c ^ 2) * R 2 0
      ∧ R 1 2 = (a ^ 2 + c ^ 2) * R 2 1
      ∧ R 0 3 = (k ^ 2 + z ^ 2) * R 3 0 := by
  have hgram := gram_mul_coefficient_eq_transpose_mul_gram
    P (orbitFourAlignedFrame a c k z) R hsymm hrepresentation
  have h01 := congrFun (congrFun hgram (0 : Fin 4)) (1 : Fin 4)
  have h02 := congrFun (congrFun hgram (0 : Fin 4)) (2 : Fin 4)
  have h12 := congrFun (congrFun hgram (1 : Fin 4)) (2 : Fin 4)
  have h03 := congrFun (congrFun hgram (0 : Fin 4)) (3 : Fin 4)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_four, Fin.sum_univ_six] at h01 h02 h12 h03
  have hrowZero : orbitFourAlignedFrame a c k z 0
      = (![0, 0, a, 0] : Fin 4 → ℝ) := by rfl
  have hrowOne : orbitFourAlignedFrame a c k z 1
      = (![1, 0, 0, 0] : Fin 4 → ℝ) := by rfl
  have hrowTwo : orbitFourAlignedFrame a c k z 2
      = (![0, 1, 0, 0] : Fin 4 → ℝ) := by rfl
  have hrowThree : orbitFourAlignedFrame a c k z 3
      = (![0, 0, c, 0] : Fin 4 → ℝ) := by rfl
  have hrowFour : orbitFourAlignedFrame a c k z 4
      = (![0, 0, 0, k] : Fin 4 → ℝ) := by rfl
  have hrowFive : orbitFourAlignedFrame a c k z 5
      = (![0, 0, 0, z] : Fin 4 → ℝ) := by rfl
  norm_num [hrowZero, hrowOne, hrowTwo, hrowThree, hrowFour, hrowFive,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    at h01 h02 h12 h03
  change R 0 1 = R 1 0 at h01
  have h02' : R 0 2 = (a ^ 2 + c ^ 2) * R 2 0 := by
    calc
      R 0 2 = R 2 0 * (a * a + c * c) := h02
      _ = (a ^ 2 + c ^ 2) * R 2 0 := by ring
  have h12' : R 1 2 = (a ^ 2 + c ^ 2) * R 2 1 := by
    calc
      R 1 2 = R 2 1 * (a * a + c * c) := h12
      _ = (a ^ 2 + c ^ 2) * R 2 1 := by ring
  have h03' : R 0 3 = (k ^ 2 + z ^ 2) * R 3 0 := by
    calc
      R 0 3 = R 3 0 * (k * k + z * z) := h03
      _ = (k ^ 2 + z ^ 2) * R 3 0 := by ring
  exact ⟨h01, h02', h12', h03'⟩


end Gtz

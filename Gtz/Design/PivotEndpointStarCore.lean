import Gtz.Design.PivotEndpointContraction
import Gtz.Design.StratumSqueeze

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

theorem posSemidef_pairing_sq_le {rank : ℕ}
    {form : Matrix (Fin rank) (Fin rank) ℝ} (hpsd : form.PosSemidef)
    (left right : Fin rank → ℝ)
    (hleft : 0 < left ⬝ᵥ (form *ᵥ left)) :
    (left ⬝ᵥ (form *ᵥ right)) ^ 2
      ≤ (left ⬝ᵥ (form *ᵥ left)) * (right ⬝ᵥ (form *ᵥ right)) := by
  let a := left ⬝ᵥ (form *ᵥ left)
  let b := left ⬝ᵥ (form *ᵥ right)
  have hcomm : right ⬝ᵥ (form *ᵥ left) = b := by
    exact dotProduct_mulVec_comm_of_transpose_eq hpsd.isHermitian.eq right left
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2
    (b • left - a • right)
  rw [star_trivial] at hnonneg
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
    dotProduct_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul] at hnonneg
  simp only [a, b] at hcomm hnonneg ⊢
  rw [hcomm] at hnonneg
  nlinarith

theorem kFour_coeffSum_diagonal_nonneg
    (coefficient : Fin 6 → ℝ)
    (hpsd : (∑ label, coefficient label • atomMatrix (kFourDirection label)).PosSemidef) :
    0 ≤ coefficient 0 + coefficient 1 + coefficient 3 ∧
    0 ≤ coefficient 0 + coefficient 2 + coefficient 4 ∧
    0 ≤ coefficient 1 + coefficient 2 + coefficient 5 := by
  have h0 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, 0, 0]
  have h1 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, 1, 0]
  have h2 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, 0, 1]
  rw [star_trivial] at h0 h1 h2
  simp [Matrix.mulVec, atomMatrix, kFourDirection, dotProduct,
    Fin.sum_univ_three, Fin.sum_univ_six] at h0 h1 h2
  constructor
  · linarith
  constructor <;> linarith

theorem kFour_coeffSum_principal_minors_nonneg
    (coefficient : Fin 6 → ℝ)
    (hpsd : (∑ label, coefficient label • atomMatrix (kFourDirection label)).PosSemidef) :
    0 ≤ (coefficient 0 + coefficient 1 + coefficient 3)
          * (coefficient 1 + coefficient 2 + coefficient 5) - coefficient 1 ^ 2 ∧
    0 ≤ (coefficient 0 + coefficient 2 + coefficient 4)
          * (coefficient 1 + coefficient 2 + coefficient 5) - coefficient 2 ^ 2 := by
  have h02 := (hpsd.submatrix ![0, 2]).det_nonneg
  have h12 := (hpsd.submatrix ![1, 2]).det_nonneg
  simp [Matrix.det_fin_two, Matrix.submatrix, atomMatrix, kFourDirection,
    Fin.sum_univ_six] at h02 h12
  constructor <;> nlinarith

theorem mul_neg_of_mul_eq_neg_mul_of_coeff_mul_pos
    {a b x y : ℝ} (hab : 0 < a * b) (ha : a ≠ 0) (hx : x ≠ 0)
    (h : a * x = -(b * y)) : x * y < 0 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hscaled := congrArg (fun value : ℝ => value * (a * x)) h
  nlinarith

theorem mul_pos_of_mul_eq_neg_mul_of_coeff_mul_neg
    {a b x y : ℝ} (hab : a * b < 0) (hb : b ≠ 0) (hx : x ≠ 0)
    (h : a * x = -(b * y)) : 0 < x * y := by
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hscaled := congrArg (fun value : ℝ => value * (b * x)) h
  nlinarith

theorem kFour_tree_star_of_addedFive
    (coefficient : Fin 6 → ℝ) (probe : Fin 3 → ℝ)
    (tree : Finset (Fin 6))
    (htree : tree ∈ kFourSpanningTreeList)
    (hfive : (5 : Fin 6) ∉ tree)
    (hpos : ∀ label ∈ tree, 0 < coefficient label)
    (hneg : ∀ label ∉ tree, coefficient label < 0)
    (_hprobe : probe ≠ 0)
    (hkernel : (∑ label, coefficient label • atomMatrix (kFourDirection label))
      *ᵥ probe = 0)
    (hzero : ∀ label, kFourDirection label ⬝ᵥ probe = 0 ↔ label = 5)
    (hpsd : (∑ label, coefficient label • atomMatrix (kFourDirection label)).PosSemidef) :
    tree = {0, 1, 3} ∨ tree = {0, 2, 4} := by
  have hp2 : probe 2 = 0 := by
    have hreading := (hzero 5).mpr rfl
    simpa [kFourDirection, dotProduct, Fin.sum_univ_three] using hreading
  have hp0 : probe 0 ≠ 0 := by
    intro hp0
    have hreading : kFourDirection 3 ⬝ᵥ probe = 0 := by
      simp [kFourDirection, dotProduct, Fin.sum_univ_three, hp0]
    have : (3 : Fin 6) = 5 := (hzero 3).mp hreading
    have := congrArg Fin.val this
    omega
  have hp1 : probe 1 ≠ 0 := by
    intro hp1
    have hreading : kFourDirection 4 ⬝ᵥ probe = 0 := by
      simp [kFourDirection, dotProduct, Fin.sum_univ_three, hp1]
    have : (4 : Fin 6) = 5 := (hzero 4).mp hreading
    have := congrArg Fin.val this
    omega
  have heq := kFour_coeffSum_kernel_equations coefficient probe hkernel
  rw [hp2] at heq
  norm_num at heq
  have h12 : coefficient 1 * probe 0 = -(coefficient 2 * probe 1) := by
    linarith [heq.2.2]
  have h34 : coefficient 3 * probe 0 = -(coefficient 4 * probe 1) := by
    linarith [heq.1, heq.2.1, heq.2.2]
  have hA : (coefficient 0 + coefficient 1 + coefficient 3) * probe 0
      = coefficient 0 * probe 1 := by
    linarith [heq.1]
  have hB : (coefficient 0 + coefficient 2 + coefficient 4) * probe 1
      = coefficient 0 * probe 0 := by
    linarith [heq.2.1]
  simp [kFourSpanningTreeList] at htree
  rcases htree with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp at hfive
  · exact Or.inl rfl
  · exact Or.inr rfl
  · have hc0 : 0 < coefficient 0 := hpos 0 (by simp)
    have hc1 : 0 < coefficient 1 := hpos 1 (by simp)
    have hc2 : coefficient 2 < 0 := hneg 2 (by simp)
    have hc4 : 0 < coefficient 4 := hpos 4 (by simp)
    have hc5 : coefficient 5 < 0 := hneg 5 (by simp)
    have hxy : 0 < probe 0 * probe 1 :=
      mul_pos_of_mul_eq_neg_mul_of_coeff_mul_neg
        (by nlinarith : coefficient 1 * coefficient 2 < 0)
        (ne_of_lt hc2) hp0 h12
    have hminor :=
      (kFour_coeffSum_principal_minors_nonneg coefficient hpsd).1
    have hleft :
        ((coefficient 0 + coefficient 1 + coefficient 3)
            * (coefficient 1 + coefficient 2 + coefficient 5)
              - coefficient 1 ^ 2) * probe 0 ^ 2
          = coefficient 0 * probe 0 * probe 1
              * (coefficient 1 + coefficient 2 + coefficient 5)
              - coefficient 2 ^ 2 * probe 1 ^ 2 := by
      calc
        ((coefficient 0 + coefficient 1 + coefficient 3)
              * (coefficient 1 + coefficient 2 + coefficient 5)
                - coefficient 1 ^ 2) * probe 0 ^ 2
            = ((coefficient 0 + coefficient 1 + coefficient 3) * probe 0)
                * (coefficient 1 + coefficient 2 + coefficient 5) * probe 0
                - (coefficient 1 * probe 0) ^ 2 := by ring
        _ = (coefficient 0 * probe 1)
                * (coefficient 1 + coefficient 2 + coefficient 5) * probe 0
                - (-(coefficient 2 * probe 1)) ^ 2 := by rw [hA, h12]
        _ = coefficient 0 * probe 0 * probe 1
                * (coefficient 1 + coefficient 2 + coefficient 5)
                - coefficient 2 ^ 2 * probe 1 ^ 2 := by ring
    have hscale : 0 < coefficient 0 * probe 0 * probe 1 := by
      nlinarith [mul_pos hc0 hxy]
    have hdrop :
        coefficient 0 * probe 0 * probe 1
              * (coefficient 1 + coefficient 2 + coefficient 5)
              - coefficient 2 ^ 2 * probe 1 ^ 2
          < coefficient 0 * probe 0 * probe 1
              * (coefficient 1 + coefficient 2)
              - coefficient 2 ^ 2 * probe 1 ^ 2 := by
      have := mul_lt_mul_of_pos_left
        (show coefficient 1 + coefficient 2 + coefficient 5
            < coefficient 1 + coefficient 2 by linarith) hscale
      linarith
    have h12y := congrArg (fun value : ℝ => value * probe 1) h12
    have h4 : coefficient 4 * probe 1
        = coefficient 0 * (probe 0 - probe 1) - coefficient 2 * probe 1 := by
      linarith [heq.2.1]
    have h4scaled := congrArg
      (fun value : ℝ => value * (coefficient 2 * probe 1)) h4
    have htail :
        coefficient 0 * probe 0 * probe 1
              * (coefficient 1 + coefficient 2)
              - coefficient 2 ^ 2 * probe 1 ^ 2
          = coefficient 2 * coefficient 4 * probe 1 ^ 2 := by
      ring_nf at h12y h4scaled ⊢
      nlinarith [h12y, h4scaled]
    have htailNeg : coefficient 2 * coefficient 4 * probe 1 ^ 2 < 0 := by
      have hprod : coefficient 2 * coefficient 4 < 0 :=
        mul_neg_of_neg_of_pos hc2 hc4
      exact mul_neg_of_neg_of_pos hprod (sq_pos_of_ne_zero hp1)
    have hnonneg := mul_nonneg hminor (sq_nonneg (probe 0))
    nlinarith [hleft, hdrop, htail, htailNeg]
  · have hc0 : 0 < coefficient 0 := hpos 0 (by simp)
    have hc1 : coefficient 1 < 0 := hneg 1 (by simp)
    have hc2 : 0 < coefficient 2 := hpos 2 (by simp)
    have hc3 : 0 < coefficient 3 := hpos 3 (by simp)
    have hc5 : coefficient 5 < 0 := hneg 5 (by simp)
    have hxy : 0 < probe 0 * probe 1 :=
      mul_pos_of_mul_eq_neg_mul_of_coeff_mul_neg
        (by nlinarith : coefficient 1 * coefficient 2 < 0)
        (ne_of_gt hc2) hp0 h12
    have hminor :=
      (kFour_coeffSum_principal_minors_nonneg coefficient hpsd).2
    have h21 : coefficient 2 * probe 1 = -(coefficient 1 * probe 0) := by
      linarith [h12]
    have hleft :
        ((coefficient 0 + coefficient 2 + coefficient 4)
            * (coefficient 1 + coefficient 2 + coefficient 5)
              - coefficient 2 ^ 2) * probe 1 ^ 2
          = coefficient 0 * probe 0 * probe 1
              * (coefficient 1 + coefficient 2 + coefficient 5)
              - coefficient 1 ^ 2 * probe 0 ^ 2 := by
      calc
        ((coefficient 0 + coefficient 2 + coefficient 4)
              * (coefficient 1 + coefficient 2 + coefficient 5)
                - coefficient 2 ^ 2) * probe 1 ^ 2
            = ((coefficient 0 + coefficient 2 + coefficient 4) * probe 1)
                * (coefficient 1 + coefficient 2 + coefficient 5) * probe 1
                - (coefficient 2 * probe 1) ^ 2 := by ring
        _ = (coefficient 0 * probe 0)
                * (coefficient 1 + coefficient 2 + coefficient 5) * probe 1
                - (-(coefficient 1 * probe 0)) ^ 2 := by rw [hB, h21]
        _ = coefficient 0 * probe 0 * probe 1
                * (coefficient 1 + coefficient 2 + coefficient 5)
                - coefficient 1 ^ 2 * probe 0 ^ 2 := by ring
    have hscale : 0 < coefficient 0 * probe 0 * probe 1 := by
      nlinarith [mul_pos hc0 hxy]
    have hdrop :
        coefficient 0 * probe 0 * probe 1
              * (coefficient 1 + coefficient 2 + coefficient 5)
              - coefficient 1 ^ 2 * probe 0 ^ 2
          < coefficient 0 * probe 0 * probe 1
              * (coefficient 1 + coefficient 2)
              - coefficient 1 ^ 2 * probe 0 ^ 2 := by
      have := mul_lt_mul_of_pos_left
        (show coefficient 1 + coefficient 2 + coefficient 5
            < coefficient 1 + coefficient 2 by linarith) hscale
      linarith
    have h12x := congrArg (fun value : ℝ => value * probe 0) h12
    have h3 : coefficient 3 * probe 0
        = coefficient 0 * (probe 1 - probe 0) - coefficient 1 * probe 0 := by
      linarith [heq.1]
    have h3scaled := congrArg
      (fun value : ℝ => value * (coefficient 1 * probe 0)) h3
    have htail :
        coefficient 0 * probe 0 * probe 1
              * (coefficient 1 + coefficient 2)
              - coefficient 1 ^ 2 * probe 0 ^ 2
          = coefficient 1 * coefficient 3 * probe 0 ^ 2 := by
      ring_nf at h12x h3scaled ⊢
      nlinarith [h12x, h3scaled]
    have htailNeg : coefficient 1 * coefficient 3 * probe 0 ^ 2 < 0 := by
      have hprod : coefficient 1 * coefficient 3 < 0 :=
        mul_neg_of_neg_of_pos hc1 hc3
      exact mul_neg_of_neg_of_pos hprod (sq_pos_of_ne_zero hp0)
    have hnonneg := mul_nonneg hminor (sq_nonneg (probe 1))
    nlinarith [hleft, hdrop, htail, htailNeg]
  · have hc1 : 0 < coefficient 1 := hpos 1 (by simp)
    have hc2 : 0 < coefficient 2 := hpos 2 (by simp)
    have hc3 : 0 < coefficient 3 := hpos 3 (by simp)
    have hc4 : coefficient 4 < 0 := hneg 4 (by simp)
    have hnegxy : probe 0 * probe 1 < 0 :=
      mul_neg_of_mul_eq_neg_mul_of_coeff_mul_pos
        (by positivity) (ne_of_gt hc1) hp0 h12
    have hposxy : 0 < probe 0 * probe 1 :=
      mul_pos_of_mul_eq_neg_mul_of_coeff_mul_neg
        (by nlinarith : coefficient 3 * coefficient 4 < 0)
        (ne_of_lt hc4) hp0 h34
    linarith
  · have hc1 : 0 < coefficient 1 := hpos 1 (by simp)
    have hc2 : 0 < coefficient 2 := hpos 2 (by simp)
    have hc3 : coefficient 3 < 0 := hneg 3 (by simp)
    have hc4 : 0 < coefficient 4 := hpos 4 (by simp)
    have hnegxy : probe 0 * probe 1 < 0 :=
      mul_neg_of_mul_eq_neg_mul_of_coeff_mul_pos
        (by positivity) (ne_of_gt hc1) hp0 h12
    have hposxy : 0 < probe 0 * probe 1 :=
      mul_pos_of_mul_eq_neg_mul_of_coeff_mul_neg
        (by nlinarith : coefficient 3 * coefficient 4 < 0)
        (ne_of_gt hc4) hp0 h34
    linarith
  · have hc1 : 0 < coefficient 1 := hpos 1 (by simp)
    have hc2 : coefficient 2 < 0 := hneg 2 (by simp)
    have hc3 : 0 < coefficient 3 := hpos 3 (by simp)
    have hc4 : 0 < coefficient 4 := hpos 4 (by simp)
    have hposxy : 0 < probe 0 * probe 1 :=
      mul_pos_of_mul_eq_neg_mul_of_coeff_mul_neg
        (by nlinarith : coefficient 1 * coefficient 2 < 0)
        (ne_of_lt hc2) hp0 h12
    have hnegxy : probe 0 * probe 1 < 0 :=
      mul_neg_of_mul_eq_neg_mul_of_coeff_mul_pos
        (by positivity) (ne_of_gt hc3) hp0 h34
    linarith
  · have hc1 : coefficient 1 < 0 := hneg 1 (by simp)
    have hc2 : 0 < coefficient 2 := hpos 2 (by simp)
    have hc3 : 0 < coefficient 3 := hpos 3 (by simp)
    have hc4 : 0 < coefficient 4 := hpos 4 (by simp)
    have hposxy : 0 < probe 0 * probe 1 :=
      mul_pos_of_mul_eq_neg_mul_of_coeff_mul_neg
        (by nlinarith : coefficient 1 * coefficient 2 < 0)
        (ne_of_gt hc2) hp0 h12
    have hnegxy : probe 0 * probe 1 < 0 :=
      mul_neg_of_mul_eq_neg_mul_of_coeff_mul_pos
        (by positivity) (ne_of_gt hc3) hp0 h34
    linarith

end Gtz

import Gtz.Design.DiamondPrimitive
import Gtz.Reduction.RayleighCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Step zero of the adjacency campaign: the diamond is stress-free and lies on a conic

The adjacency brief conjectured "adjacent dominators force a parallel pair or a
STRESS" and mandated a kernel decision at `Gtz.diamondDesign` first.  This module
decides it, and the verdict CORRECTS the brief.

* `Gtz.diamondDesign_stressFree` — the five atom matrices of the diamond are
  linearly independent.  A stress dichotomy would refute the diamond, which is a
  real primitive tie with adjacent dominators.  So the stress clause is the
  WRONG escape hatch at `(5,3)`.
* `Gtz.diamondDesign_on_conic` — the diamond lies on an explicit conic.  In the
  rational edge frame the conic is `![![0,0,1],![0,0,1],![1,1,2]]`.  The correct
  size-generic dichotomy is therefore CONIC-or-parallel.  At `(6,3)` the conic
  clause is equivalent to a stress (`Gtz.exists_stress_of_commonQuadric` and
  `Gtz.isStressFreeDesign_of_isPrimitiveDesign_of_isTie`), so the corrected
  dichotomy still kills equality readings at a primitive `(6,3)` tie.  At
  `(5,3)` the conic clause is free for every design, and the diamond escapes
  through it — as it must.

Both proofs work in the rational edge frame and transport through the whitener
by congruence.  No entry of the whitener is ever computed.
-/

namespace Gtz

open Matrix

/-! ## The rational edge vectors of the diamond, in closed form -/

/-- The five grounded edge vectors of the diamond graph. -/
def diamondEdgeVec : Fin 5 → Fin 3 → ℝ :=
  ![![1, -1, 0], ![1, 0, -1], ![1, 0, 0], ![0, 1, -1], ![0, 1, 0]]

theorem diamondGraph_edgeVector_eq (edge : Fin 5) :
    diamondGraph.edgeVector edge = diamondEdgeVec edge := by
  funext coord
  fin_cases edge <;> fin_cases coord <;>
    simp [MultigraphOnGround.edgeVector, diamondGraph, diamondEdgeVec, Fin.ext_iff]

/-! ## The congruence cancel -/

/-- A congruence by an invertible matrix that lands on zero started at zero. -/
theorem eq_zero_of_conj_eq_zero {k : ℕ} {W X : Matrix (Fin k) (Fin k) ℝ}
    (hunit : IsUnit W.det) (hconj : Wᵀ * X * W = 0) : X = 0 := by
  have hunitT : IsUnit (Wᵀ).det := by rwa [Matrix.det_transpose]
  calc X = (Wᵀ)⁻¹ * (Wᵀ * X * W) * W⁻¹ := by
        rw [Matrix.mul_assoc (Wᵀ) X W, ← Matrix.mul_assoc ((Wᵀ)⁻¹),
          Matrix.nonsing_inv_mul _ hunitT, Matrix.one_mul,
          Matrix.mul_assoc X W, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
    _ = 0 := by rw [hconj, Matrix.mul_zero, Matrix.zero_mul]

/-- The atom-matrix sum of a graphic design, pushed into the rational frame. -/
theorem sum_smul_atomMatrix_graphic (lam : Fin 5 → ℝ) :
    ∑ e, lam e • atomMatrix (diamondDesign.atom e)
      = (diamondData.whitener)ᵀ
          * (∑ e, (lam e * (diamondData.conductance e / diamondData.weight e))
              • atomMatrix (diamondGraph.edgeVector e))
          * diamondData.whitener := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hatom : atomMatrix (diamondDesign.atom e)
      = (diamondData.conductance e / diamondData.weight e) •
        ((diamondData.whitener)ᵀ * atomMatrix (diamondGraph.edgeVector e)
          * diamondData.whitener) :=
    diamondData.atomMatrix_graphicAtom e
  rw [hatom, smul_smul, Matrix.mul_smul, Matrix.smul_mul]

/-! ## The verdict, half one: the diamond is stress-free -/

/-- **THE DIAMOND CARRIES NO STRESS.**  The five atom matrices are linearly
independent: the three off-diagonal entries each appear in exactly one edge
matrix, and the two free diagonal entries finish the rest. -/
theorem diamondDesign_stressFree (stress : Fin 5 → ℝ)
    (hsum : ∑ e, stress e • atomMatrix (diamondDesign.atom e) = 0) :
    stress = 0 := by
  have hconj := hsum
  rw [sum_smul_atomMatrix_graphic stress] at hconj
  have hzero := eq_zero_of_conj_eq_zero diamondData.whitener_isUnit hconj
  have hE : ∀ i j : Fin 3,
      (∑ e, (stress e * (diamondData.conductance e / diamondData.weight e))
        • atomMatrix (diamondGraph.edgeVector e)) i j = 0 := by
    intro i j
    have happ := congrFun (congrFun hzero i) j
    simpa using happ
  have h01 := hE 0 1
  have h02 := hE 0 2
  have h12 := hE 1 2
  have h00 := hE 0 0
  have h11 := hE 1 1
  simp only [Finset.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
    Matrix.vecMulVec_apply, diamondGraph_edgeVector_eq, Fin.sum_univ_five]
    at h01 h02 h12 h00 h11
  norm_num [diamondEdgeVec, diamondData, diamondGraph, Matrix.vecMulVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.tail_cons] at h01 h02 h12 h00 h11
  funext e
  fin_cases e
  · show stress 0 = 0
    linarith
  · show stress 1 = 0
    linarith
  · show stress 2 = 0
    linarith
  · show stress 3 = 0
    linarith
  · show stress 4 = 0
    linarith

/-! ## The verdict, half two: the diamond lies on a conic -/

/-- The conic through the five diamond edges, in the rational frame. -/
def diamondConicRat : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![0, 0, 1], ![0, 0, 1], ![1, 1, 2]]

theorem diamondConicRat_symm : diamondConicRatᵀ = diamondConicRat := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [diamondConicRat, Matrix.transpose_apply]

/-- Every rational edge vector of the diamond is conic-null. -/
theorem diamondEdgeVec_conicNull (edge : Fin 5) :
    diamondGraph.edgeVector edge
      ⬝ᵥ (diamondConicRat *ᵥ diamondGraph.edgeVector edge) = 0 := by
  rw [diamondGraph_edgeVector_eq]
  fin_cases edge <;>
    simp [diamondEdgeVec, diamondConicRat, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;> norm_num

/-- **THE DIAMOND LIES ON A CONIC.**  The witness is the rational conic
transported through the whitener; no whitener entry is computed. -/
theorem diamondDesign_on_conic :
    ∃ form : Matrix (Fin 3) (Fin 3) ℝ, formᵀ = form ∧ form ≠ 0 ∧
      ∀ edge : Fin 5,
        diamondDesign.atom edge ⬝ᵥ (form *ᵥ diamondDesign.atom edge) = 0 := by
  set W := diamondData.whitener with hW
  have hunit : IsUnit W.det := diamondData.whitener_isUnit
  have hunitT : IsUnit (Wᵀ).det := by rwa [Matrix.det_transpose]
  refine ⟨W⁻¹ * diamondConicRat * (Wᵀ)⁻¹, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
      diamondConicRat_symm, Matrix.mul_assoc]
  · intro hzero
    have hback : diamondConicRat = W * (W⁻¹ * diamondConicRat * (Wᵀ)⁻¹) * Wᵀ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hunitT, Matrix.mul_one]
    rw [hzero, Matrix.mul_zero, Matrix.zero_mul] at hback
    have hread := congrFun (congrFun hback 0) 2
    simp [diamondConicRat] at hread
  · intro edge
    have hatom : atomMatrix (diamondDesign.atom edge)
        = (diamondData.conductance edge / diamondData.weight edge) •
          (Wᵀ * atomMatrix (diamondGraph.edgeVector edge) * W) :=
      diamondData.atomMatrix_graphicAtom edge
    have hpair := atomMatrix_trace_pairing
      (M := W⁻¹ * diamondConicRat * (Wᵀ)⁻¹) (w := diamondDesign.atom edge)
    rw [← hpair, hatom, Matrix.smul_mul, Matrix.trace_smul]
    have hcollapse :
        Wᵀ * atomMatrix (diamondGraph.edgeVector edge) * W
            * (W⁻¹ * diamondConicRat * (Wᵀ)⁻¹)
          = Wᵀ * (atomMatrix (diamondGraph.edgeVector edge)
              * (diamondConicRat * (Wᵀ)⁻¹)) := by
      have hWW : W * (W⁻¹ * (diamondConicRat * (Wᵀ)⁻¹))
          = diamondConicRat * (Wᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
      simp only [Matrix.mul_assoc]
      rw [hWW]
    rw [hcollapse, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hunitT, Matrix.mul_one, atomMatrix_trace_pairing,
      diamondEdgeVec_conicNull, smul_zero]

end Gtz

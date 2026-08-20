/-
# The teeth of the projection tax: spectral-free block floors

The tax law of `Gtz.ProjectionTaxLaw` consumes a quadratic floor of the
projection block.  This module produces the floor from polynomial data, with
no spectral theorem:

* `form_le_trace_mul_normSq_of_posSemidef` — a positive semidefinite `3×3`
  form is below its trace: the difference is EXACTLY the sum of the three
  paired compressions of the form, each nonnegative;
* `adjugate_eq_fin_three_cayley` — the Cayley–Hamilton adjugate:
  `adj A = A² − (tr A)·A + e₂·1` with `e₂ = ((tr A)² − tr A²)/2`;
* `e2_mul_form_ge_det_mul_normSq` — THE FLOOR: for a positive semidefinite
  symmetric `A` and every probe,

    `det A·‖ξ‖² ≤ e₂(A)·(ξᵀAξ)` .

  The proof probes `A·adj A = det A·1`, substitutes Cayley–Hamilton, and the
  residue is the trace law at the probe `Aξ`.  Dividing by `e₂ > 0` this is
  `λmin ≥ e₃/e₂`, but no division and no eigenvalue enters;
* the teeth: the LIGHT-TRIPLE PRODUCER in multiplied polynomial form (all
  member weights times `e₂` below `det` force a strict dominator), and THE
  BLOCK TAX OF A TIE — at every triple of a tie,

    `det Π[C] ≤ (max member weight)·e₂(Π[C])` ,

  a polynomial tie-necessary law.  In the invariant arena the block
  determinant is the weighted squared bracket and `e₂` is the weighted wedge
  mass of the pairs, so the law prices brackets by wedges — the currencies
  of primitivity.
-/
import Gtz.Wave.ProjectionTaxLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The trace law -/

/-- **A positive semidefinite `3×3` form is below its trace.**  The gap is
the sum of the three paired compressions of the form, each an instance of
the form itself. -/
theorem form_le_trace_mul_normSq_of_posSemidef
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosSemidef) (ξ : Fin 3 → ℝ) :
    ξ ⬝ᵥ (A *ᵥ ξ) ≤ Matrix.trace A * (ξ ⬝ᵥ ξ) := by
  have h01 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA).2 ![ξ 1, -(ξ 0), 0]
  have h02 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA).2 ![ξ 2, 0, -(ξ 0)]
  have h12 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA).2 ![0, ξ 2, -(ξ 1)]
  rw [star_trivial] at h01 h02 h12
  have hsymm : Aᵀ = A := transpose_eq_of_isHermitian hA.1
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.trace_fin_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h01 h02 h12 ⊢
  have ha01 : A 0 1 = A 1 0 := by
    have := congrFun (congrFun hsymm 0) 1
    simpa [Matrix.transpose_apply] using this.symm
  have ha02 : A 0 2 = A 2 0 := by
    have := congrFun (congrFun hsymm 0) 2
    simpa [Matrix.transpose_apply] using this.symm
  have ha12 : A 1 2 = A 2 1 := by
    have := congrFun (congrFun hsymm 1) 2
    simpa [Matrix.transpose_apply] using this.symm
  nlinarith [h01, h02, h12]

/-! ## 2. The Cayley–Hamilton adjugate -/

set_option linter.unusedSimpArgs false in
/-- **The `3×3` adjugate through Cayley–Hamilton**:
`adj A = A² − (tr A)·A + (((tr A)² − tr A²)/2)·1`. -/
theorem adjugate_eq_fin_three_cayley (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.adjugate = A * A - Matrix.trace A • A
      + (((Matrix.trace A)^2 - Matrix.trace (A * A))/2)
        • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.adjugate_fin_three, Matrix.trace_fin_three, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.one_apply]
      ring

/-! ## 3. The floor -/

/-- **THE SPECTRAL-FREE BLOCK FLOOR.**  For a positive semidefinite `3×3`
matrix, the determinant times the squared probe norm is below the second
invariant times the form:

  `det A·‖ξ‖² ≤ (((tr A)² − tr A²)/2)·(ξᵀAξ)` .

Cayley–Hamilton turns the adjugate probe of `A·adj A = det A·1` into the
trace law at `A ξ`. -/
theorem e2_mul_form_ge_det_mul_normSq
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosSemidef) (ξ : Fin 3 → ℝ) :
    A.det * (ξ ⬝ᵥ ξ)
      ≤ (((Matrix.trace A)^2 - Matrix.trace (A * A))/2) * (ξ ⬝ᵥ (A *ᵥ ξ)) := by
  have hsymm : Aᵀ = A := transpose_eq_of_isHermitian hA.1
  have hdet1 : A.det * (ξ ⬝ᵥ ξ) = ξ ⬝ᵥ ((A * A.adjugate) *ᵥ ξ) := by
    rw [Matrix.mul_adjugate, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      Matrix.one_mulVec]
  have hCH := adjugate_eq_fin_three_cayley A
  have hAξ : ξ ⬝ᵥ ((A * A) *ᵥ ξ) = (A *ᵥ ξ) ⬝ᵥ (A *ᵥ ξ) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      show ξ ᵥ* A = A *ᵥ ξ from by rw [← Matrix.mulVec_transpose, hsymm]]
  have hA3 : ξ ⬝ᵥ ((A * (A * A)) *ᵥ ξ) = (A *ᵥ ξ) ⬝ᵥ (A *ᵥ (A *ᵥ ξ)) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      show ξ ᵥ* A = A *ᵥ ξ from by rw [← Matrix.mulVec_transpose, hsymm],
      Matrix.mulVec_mulVec]
  have htrace := form_le_trace_mul_normSq_of_posSemidef hA (A *ᵥ ξ)
  have hexpand : ξ ⬝ᵥ ((A * A.adjugate) *ᵥ ξ)
      = (A *ᵥ ξ) ⬝ᵥ (A *ᵥ (A *ᵥ ξ))
        - Matrix.trace A * ((A *ᵥ ξ) ⬝ᵥ (A *ᵥ ξ))
        + (((Matrix.trace A)^2 - Matrix.trace (A * A))/2) * (ξ ⬝ᵥ (A *ᵥ ξ)) := by
    rw [show A * A.adjugate
        = A * (A * A) - Matrix.trace A • (A * A)
          + (((Matrix.trace A)^2 - Matrix.trace (A * A))/2) • A from by
      rw [hCH]
      rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
        Matrix.mul_one]]
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, dotProduct_add, dotProduct_sub, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul, hAξ, hA3]
  rw [hdet1, hexpand]
  nlinarith [htrace]

set_option linter.unusedSimpArgs false in
/-- The second invariant of a positive semidefinite `3×3` matrix is
nonnegative: it is the sum of the three principal `2×2` minors, each the
determinant of a positive semidefinite compression. -/
theorem e2_nonneg_of_posSemidef {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.PosSemidef) :
    0 ≤ ((Matrix.trace A)^2 - Matrix.trace (A * A))/2 := by
  have hsymm : Aᵀ = A := transpose_eq_of_isHermitian hA.1
  have h01 : (0:ℝ) ≤ (A.submatrix ![0,1] ![0,1]).det :=
    ((hA.submatrix ![0,1]).det_nonneg)
  have h02 : (0:ℝ) ≤ (A.submatrix ![0,2] ![0,2]).det :=
    ((hA.submatrix ![0,2]).det_nonneg)
  have h12 : (0:ℝ) ≤ (A.submatrix ![1,2] ![1,2]).det :=
    ((hA.submatrix ![1,2]).det_nonneg)
  have ha01 : A 0 1 = A 1 0 := by
    have := congrFun (congrFun hsymm 0) 1
    simpa [Matrix.transpose_apply] using this.symm
  have ha02 : A 0 2 = A 2 0 := by
    have := congrFun (congrFun hsymm 0) 2
    simpa [Matrix.transpose_apply] using this.symm
  have ha12 : A 1 2 = A 2 1 := by
    have := congrFun (congrFun hsymm 1) 2
    simpa [Matrix.transpose_apply] using this.symm
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.trace_fin_three,
    Matrix.mul_apply, Fin.sum_univ_three] at h01 h02 h12 ⊢
  nlinarith [h01, h02, h12]

/-! ## 4. The teeth -/

/-- **THE POLYNOMIAL LIGHT-TRIPLE PRODUCER.**  A triple whose members all
satisfy `t·e₂ < det` on the projection block dominates strictly.  The floor
is manufactured by `e2_mul_form_ge_det_mul_normSq` — no spectral input. -/
theorem posDef_subsetSum_of_invariant_light (D : WeightedDesign m 3)
    (pick : Fin 3 → Fin m) (hinj : Function.Injective pick)
    (he₂ : 0 < ((Matrix.trace ((projectionOfDesign D).submatrix pick pick))^2
        - Matrix.trace ((projectionOfDesign D).submatrix pick pick
          * (projectionOfDesign D).submatrix pick pick))/2)
    (hlight : ∀ slot, D.weight (pick slot)
        * (((Matrix.trace ((projectionOfDesign D).submatrix pick pick))^2
          - Matrix.trace ((projectionOfDesign D).submatrix pick pick
            * (projectionOfDesign D).submatrix pick pick))/2)
      < ((projectionOfDesign D).submatrix pick pick).det) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef := by
  set B : Matrix (Fin 3) (Fin 3) ℝ := (projectionOfDesign D).submatrix pick pick
    with hB
  have hBpsd : B.PosSemidef := (posSemidef_projectionOfDesign D).submatrix pick
  refine posDef_subsetSum_of_projectionFloor_light D pick hinj
    (lam := B.det / (((Matrix.trace B)^2 - Matrix.trace (B * B))/2))
    (fun ξ => ?_) (fun slot => ?_)
  · rw [div_mul_eq_mul_div, div_le_iff₀ he₂]
    calc B.det * (ξ ⬝ᵥ ξ)
        ≤ (((Matrix.trace B)^2 - Matrix.trace (B * B))/2) * (ξ ⬝ᵥ (B *ᵥ ξ)) :=
          e2_mul_form_ge_det_mul_normSq hBpsd ξ
      _ = (ξ ⬝ᵥ (B *ᵥ ξ)) * (((Matrix.trace B)^2 - Matrix.trace (B * B))/2) := by
          ring
  · rw [lt_div_iff₀ he₂]
    exact hlight slot

/-- **THE BLOCK TAX OF A TIE, polynomial form.**  At every triple of a tie
with positive second invariant, the block determinant is below the maximal
member weight times the second invariant:

  `det Π[C] ≤ t_{c*}·e₂(Π[C])`  for some member `c*` .

The invariant translation reads the two sides as the weighted squared
bracket and the weighted wedge mass of the pairs. -/
theorem isTie_block_tax (D : WeightedDesign m 3) (htie : IsTie D)
    (pick : Fin 3 → Fin m) (hinj : Function.Injective pick)
    (he₂ : 0 < ((Matrix.trace ((projectionOfDesign D).submatrix pick pick))^2
        - Matrix.trace ((projectionOfDesign D).submatrix pick pick
          * (projectionOfDesign D).submatrix pick pick))/2) :
    ∃ slot, ((projectionOfDesign D).submatrix pick pick).det
      ≤ D.weight (pick slot)
        * (((Matrix.trace ((projectionOfDesign D).submatrix pick pick))^2
          - Matrix.trace ((projectionOfDesign D).submatrix pick pick
            * (projectionOfDesign D).submatrix pick pick))/2) := by
  by_contra hcon
  push Not at hcon
  have hcard : (Finset.image pick Finset.univ).card = 3 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  exact htie.2 _ hcard
    (posDef_subsetSum_of_invariant_light D pick hinj he₂ fun slot => hcon slot)

end Gtz

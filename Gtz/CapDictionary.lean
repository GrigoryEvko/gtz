/-
# The cap–z-mass dictionary and boundary pivots

The z-mass workflow's exact layer (triple-verified: build sympy, adversarial
audit, orchestrator re-derivation), now in the kernel. Per atom-plane and
gated pair, the cap tie, the wall tie, and the z-mass tie are ONE codim-1
surface read in three coordinate systems:

* **D2**: `det(A_i + A_j − I₃) = −det(H − I₂)` — the 3×3 pair matrix and the
  2×2 pair Gram carry opposite determinant signs (a free polynomial identity);
* **D4, division-free**: `det(A_i + A_j + ℓ·uuᵀ − I₃) = ℓ·det(H′ − I₂)
  − det(H − I₂)` where `H′ − I = (H − I) − y·yᵀ` is the planar downdate by the
  pair's heights `y = (⟨g_i,u⟩, ⟨g_j,u⟩)` — proven `linear_combination` the
  unit constraint with cofactor `ℓ·det(H − I)`;
* **the dictionary**: under a nondegenerate pair Gram and `ℓ ≠ 0`, the cap
  determinant vanishes iff the z-mass form `yᵀ(H−I)⁻¹y` equals `1 − 1/ℓ` —
  the z-mass tie (`TwoByTwo.depth_eq_one_sub_zmass` supplies the depth leg);
* **Z-PIV**: at boundary domination — the erased subset's excess determinant
  vanishes — every insider pivot of a positive definite cover equals one
  EXACTLY (one line from Theorem D's determinant identity). Two of the tied
  variety's four insider ties are automatic at the boundary.
-/
import Mathlib
import Gtz.CapSlack
import Gtz.TwoByTwo

namespace Gtz

open Matrix

/-- The 2×2 Gram matrix of a pair of atoms. -/
def pairGram {k : ℕ} (leftAtom rightAtom : Fin k → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![leftAtom ⬝ᵥ leftAtom, leftAtom ⬝ᵥ rightAtom;
     rightAtom ⬝ᵥ leftAtom, rightAtom ⬝ᵥ rightAtom]

/-- The pair's heights along a direction. -/
def pairHeights {k : ℕ} (leftAtom rightAtom direction : Fin k → ℝ) :
    Fin 2 → ℝ :=
  ![leftAtom ⬝ᵥ direction, rightAtom ⬝ᵥ direction]

/-- **D2**: the 3×3 pair matrix and the 2×2 pair Gram have opposite
determinant signs — `det(A_i + A_j − I₃) = −det(H − I₂)`, freely. -/
theorem det_pair_matrix_eq_neg_pairGram (leftAtom rightAtom : Fin 3 → ℝ) :
    (atomMatrix leftAtom + atomMatrix rightAtom - 1).det
      = -(pairGram leftAtom rightAtom - 1).det := by
  simp only [Matrix.det_fin_three, Matrix.det_fin_two, pairGram, atomMatrix,
    Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.reduceEq, reduceIte]
  ring

/-- **D4, division-free**: adding a scaled unit atom to the pair matrix reads
the planar downdate — `det(A_i + A_j + ℓ·uuᵀ − I₃) = ℓ·det((H−I) − y·yᵀ)
− det(H−I)` with `y` the pair's heights along `u`. -/
theorem cap_det_dictionary (leftAtom rightAtom unitDir : Fin 3 → ℝ)
    (lev : ℝ) (hunit : unitDir ⬝ᵥ unitDir = 1) :
    (atomMatrix leftAtom + atomMatrix rightAtom
        + lev • atomMatrix unitDir - 1).det
      = lev * ((pairGram leftAtom rightAtom - 1)
            - Matrix.vecMulVec (pairHeights leftAtom rightAtom unitDir)
                (pairHeights leftAtom rightAtom unitDir)).det
        - (pairGram leftAtom rightAtom - 1).det := by
  have hunitExpanded : unitDir 0 * unitDir 0 + unitDir 1 * unitDir 1
      + unitDir 2 * unitDir 2 = 1 := by
    have hexpand := hunit
    simp only [dotProduct, Fin.sum_univ_three] at hexpand
    exact hexpand
  simp only [Matrix.det_fin_three, Matrix.det_fin_two, pairGram, pairHeights,
    atomMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Matrix.one_apply, smul_eq_mul, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.reduceEq, reduceIte]
  linear_combination (lev * ((leftAtom 0 * leftAtom 0 + leftAtom 1 * leftAtom 1
      + leftAtom 2 * leftAtom 2 - 1)
    * (rightAtom 0 * rightAtom 0 + rightAtom 1 * rightAtom 1
      + rightAtom 2 * rightAtom 2 - 1)
    - (leftAtom 0 * rightAtom 0 + leftAtom 1 * rightAtom 1
      + leftAtom 2 * rightAtom 2) ^ 2)) * hunitExpanded

/-- **The cap–z-mass dictionary**: under a nondegenerate pair Gram and a
nonzero leverage, the cap determinant at the plane vanishes exactly when the
z-mass form equals `1 − 1/ℓ` — the cap tie, the wall tie, and the z-mass tie
are one surface. -/
theorem cap_tie_iff_zmass (leftAtom rightAtom unitDir : Fin 3 → ℝ)
    {lev : ℝ} (hunit : unitDir ⬝ᵥ unitDir = 1)
    (hgate : (pairGram leftAtom rightAtom - 1).det ≠ 0) (hlev : lev ≠ 0) :
    (atomMatrix leftAtom + atomMatrix rightAtom
        + lev • atomMatrix unitDir - 1).det = 0
      ↔ pairHeights leftAtom rightAtom unitDir
          ⬝ᵥ ((pairGram leftAtom rightAtom - 1)⁻¹
            *ᵥ pairHeights leftAtom rightAtom unitDir)
        = 1 - 1 / lev := by
  rw [cap_det_dictionary leftAtom rightAtom unitDir lev hunit]
  have hdowndate : ((pairGram leftAtom rightAtom - 1)
        - Matrix.vecMulVec (pairHeights leftAtom rightAtom unitDir)
            (pairHeights leftAtom rightAtom unitDir)).det
      = (pairGram leftAtom rightAtom - 1).det
        * (1 - pairHeights leftAtom rightAtom unitDir
            ⬝ᵥ ((pairGram leftAtom rightAtom - 1)⁻¹
              *ᵥ pairHeights leftAtom rightAtom unitDir)) := by
    have hdepth := depth_eq_one_sub_zmass (pairGram leftAtom rightAtom - 1)
      (pairHeights leftAtom rightAtom unitDir) hgate
    field_simp at hdepth
    linarith [hdepth]
  rw [hdowndate]
  constructor
  · intro hzero
    have hfactor : (pairGram leftAtom rightAtom - 1).det
        * (lev * (1 - pairHeights leftAtom rightAtom unitDir
            ⬝ᵥ ((pairGram leftAtom rightAtom - 1)⁻¹
              *ᵥ pairHeights leftAtom rightAtom unitDir)) - 1) = 0 := by
      linarith [hzero]
    rcases mul_eq_zero.mp hfactor with hbad | hgood
    · exact absurd hbad hgate
    · field_simp
      linarith [hgood]
  · intro hzmass
    rw [hzmass]
    field_simp
    ring

/-- **Z-PIV, the boundary pivot tie**: when the erased subset sits exactly on
the domination boundary (its excess determinant vanishes) while the full
subset is positive definite, the erased atom's pivot is EXACTLY one. At
`Φ = 1` every PD quadruple over the best triple carries automatic insider
ties. -/
theorem boundary_pivot_eq_one {m k : ℕ} (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hQ : (subsetSum D Q - 1).PosDef) {d : Fin m}
    (hd : d ∈ Q)
    (hboundary : (subsetSum D (Q.erase d) - 1).det = 0) :
    pivot D Q d = 1 := by
  have hidentity := det_erase_eq_det_mul_pivot_gap D Q hQ hd
  rw [hboundary] at hidentity
  rcases mul_eq_zero.mp hidentity.symm with hbad | hgood
  · exact absurd hbad (ne_of_gt hQ.det_pos)
  · linarith

end Gtz

/-
# Light-atom deflation: an atom of leverage ≤ 1 reduces (m+1, k) to (m, k)

The k-GENERAL Case-A step of Sengupta–Pautov, in weighted form (diary §61):
if some atom d has ℓ_d = |g_d|² ≤ 1 then P := I − t_d·g_dg_dᵀ is positive
definite (Cauchy–Schwarz: the form is ≥ (1 − t_d·ℓ_d)|u|², and
t_d·ℓ_d ≤ t_d < 1), and the remaining atoms whiten into a design on one fewer
atom: atoms √(1−t_d)·(Rᵀg_c), weights t_c/(1−t_d), where RᵀPR = I and the
index drops through `Fin.succAbove`. A dominating k-subset of the deflated
design pulls back through

  S_C − I = (1−t_d)⁻¹·[ ((1−t_d)·S_C − P)  +  t_d·(I − g_dg_dᵀ) ] ,

the first summand PSD by congruence from the deflated domination, the second
PSD exactly because ℓ_d ≤ 1 (rank-one Schur at N = I).
-/
import Mathlib
import Gtz.Basic
import Gtz.Sanity
import Gtz.SchurRankOne
import Gtz.PsdKit
import Gtz.Naimark

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- Subset atom sums are symmetric. -/
theorem subsetSum_transpose (D : WeightedDesign m k) (C : Finset (Fin m)) :
    (subsetSum D C)ᵀ = subsetSum D C := by
  rw [subsetSum, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun c _ =>
    transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom c)).1

/-- The deflated design: drop atom d, whiten the remaining Parseval mass by R,
absorb the mass loss into the atoms and weights. -/
noncomputable def deflatedDesign (D : WeightedDesign (m + 1) k)
    (d : Fin (m + 1)) (R : Matrix (Fin k) (Fin k) ℝ)
    (hs : 0 < 1 - D.weight d)
    (hRPR : Rᵀ * (1 - D.weight d • atomMatrix (D.atom d)) * R = 1) :
    WeightedDesign m k where
  atom i := Real.sqrt (1 - D.weight d) • (Rᵀ *ᵥ D.atom (d.succAbove i))
  weight i := D.weight (d.succAbove i) / (1 - D.weight d)
  weight_pos i := div_pos (D.weight_pos _) hs
  weight_sum_one := by
    rw [← Finset.sum_div]
    have hsplit := Fin.sum_univ_succAbove D.weight d
    rw [D.weight_sum_one] at hsplit
    rw [show ∑ i, D.weight (d.succAbove i) = 1 - D.weight d from by linarith,
      div_self hs.ne']
  isParseval := by
    have hterm : ∀ i : Fin m,
        (D.weight (d.succAbove i) / (1 - D.weight d))
          • atomMatrix (Real.sqrt (1 - D.weight d)
            • (Rᵀ *ᵥ D.atom (d.succAbove i)))
        = D.weight (d.succAbove i)
          • atomMatrix (Rᵀ *ᵥ D.atom (d.succAbove i)) := by
      intro i
      rw [atomMatrix_smul, Real.sq_sqrt hs.le, smul_smul,
        div_mul_cancel₀ _ hs.ne']
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    have hconj : ∑ i, D.weight (d.succAbove i)
          • atomMatrix (Rᵀ *ᵥ D.atom (d.succAbove i))
        = Rᵀ * (∑ i, D.weight (d.succAbove i)
            • atomMatrix (D.atom (d.succAbove i))) * R := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Matrix.mul_smul, Matrix.smul_mul, transpose_mul_atomMatrix_mul]
    have hPsum : ∑ i, D.weight (d.succAbove i)
          • atomMatrix (D.atom (d.succAbove i))
        = 1 - D.weight d • atomMatrix (D.atom d) := by
      have hsplit := Fin.sum_univ_succAbove
        (fun c => D.weight c • atomMatrix (D.atom c)) d
      rw [D.isParseval] at hsplit
      rw [eq_sub_iff_add_eq, add_comm]
      exact hsplit.symm
    rw [hconj, hPsum, hRPR]

/-- **Light-atom deflation.** If an atom has leverage ≤ 1 and weighted GTZ
holds one size down, this design has a dominating k-subset. -/
theorem dominating_of_light_atom (D : WeightedDesign (m + 1) k)
    (hm : 1 ≤ m) (hrec : GtzWeighted m k) (d : Fin (m + 1))
    (hlight : leverageOf (D.atom d) ≤ 1) :
    ∃ C : Finset (Fin (m + 1)), C.card = k ∧ Dominates D C := by
  have htd : D.weight d < 1 := weight_lt_one D (by omega) d
  have htdpos := D.weight_pos d
  have hs : (0 : ℝ) < 1 - D.weight d := by linarith
  -- P = I − t_d·A_d is positive definite
  have hPsymm : (1 - D.weight d • atomMatrix (D.atom d))ᵀ
      = 1 - D.weight d • atomMatrix (D.atom d) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom d)).1]
  have hPpd : (1 - D.weight d • atomMatrix (D.atom d)).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hPsymm, fun u hu => ?_⟩
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm u (D.atom d)]
    have hCS : (D.atom d ⬝ᵥ u) * (D.atom d ⬝ᵥ u)
        ≤ leverageOf (D.atom d) * (u ⬝ᵥ u) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (D.atom d) u
      rw [dotProduct, dotProduct_self_eq_sum_sq, leverageOf]
      nlinarith [h]
    have hupos : 0 < u ⬝ᵥ u := by
      have hne : ∃ s, u s ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hu (funext hall)
      obtain ⟨s, hsu⟩ := hne
      rw [dotProduct]
      exact Finset.sum_pos' (fun i _ => mul_self_nonneg _)
        ⟨s, Finset.mem_univ s, mul_self_pos.mpr hsu⟩
    nlinarith [mul_le_mul_of_nonneg_left hCS htdpos.le,
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right htdpos.le hlight)
        hupos.le,
      mul_pos hs hupos]
  obtain ⟨R, hRdet, hRPR⟩ := exists_congruence_to_one hPpd
  obtain ⟨Cdef, hCdefcard, hCdefdom⟩ := hrec (deflatedDesign D d R hs hRPR)
  have hembinj : Function.Injective d.succAbove := Fin.succAbove_right_injective
  refine ⟨Cdef.image d.succAbove, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hembinj, hCdefcard]
  · -- the deflated domination, in explicit-sum form
    have hdom : ((∑ i ∈ Cdef, atomMatrix (Real.sqrt (1 - D.weight d)
        • (Rᵀ *ᵥ D.atom (d.succAbove i)))) - 1).PosSemidef := hCdefdom
    -- the sum is the conjugated, scaled primal subset sum
    have hSdef : ∑ i ∈ Cdef, atomMatrix (Real.sqrt (1 - D.weight d)
          • (Rᵀ *ᵥ D.atom (d.succAbove i)))
        = Rᵀ * (((1 : ℝ) - D.weight d)
            • subsetSum D (Cdef.image d.succAbove)) * R := by
      rw [subsetSum, Finset.sum_image fun a _ b _ hab => hembinj hab,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
        Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [atomMatrix_smul, Real.sq_sqrt hs.le, transpose_mul_atomMatrix_mul]
    -- congruence back: (1−t_d)·S_C − P is PSD
    have hXsym : ((((1 : ℝ) - D.weight d)
          • subsetSum D (Cdef.image d.succAbove))
          - (1 - D.weight d • atomMatrix (D.atom d)))ᵀ
        = (((1 : ℝ) - D.weight d) • subsetSum D (Cdef.image d.succAbove))
          - (1 - D.weight d • atomMatrix (D.atom d)) := by
      rw [Matrix.transpose_sub, Matrix.transpose_smul, subsetSum_transpose,
        hPsymm]
    have hkey : ((((1 : ℝ) - D.weight d)
        • subsetSum D (Cdef.image d.succAbove))
        - (1 - D.weight d • atomMatrix (D.atom d))).PosSemidef := by
      refine (posSemidef_congr_right hXsym hRdet).mpr ?_
      have hexpand : Rᵀ * ((((1 : ℝ) - D.weight d)
            • subsetSum D (Cdef.image d.succAbove))
            - (1 - D.weight d • atomMatrix (D.atom d))) * R
          = (∑ i ∈ Cdef, atomMatrix (Real.sqrt (1 - D.weight d)
              • (Rᵀ *ᵥ D.atom (d.succAbove i)))) - 1 := by
        rw [Matrix.mul_sub, Matrix.sub_mul, hRPR, ← hSdef]
      rw [hexpand]
      exact hdom
    -- the light atom's own contribution is PSD
    have hlightpsd : (1 - atomMatrix (D.atom d)).PosSemidef :=
      (posSemidef_sub_vecMulVec_iff 1 Matrix.PosDef.one (D.atom d)).mpr
        (by rw [inv_one, Matrix.one_mulVec, dotProduct_self_eq_sum_sq]
            exact hlight)
    -- reassemble
    show (subsetSum D (Cdef.image d.succAbove) - 1).PosSemidef
    have hfinal : subsetSum D (Cdef.image d.succAbove) - 1
        = ((1 : ℝ) - D.weight d)⁻¹
          • (((((1 : ℝ) - D.weight d)
              • subsetSum D (Cdef.image d.succAbove))
              - (1 - D.weight d • atomMatrix (D.atom d)))
            + D.weight d • (1 - atomMatrix (D.atom d))) := by
      have hinner : ((((1 : ℝ) - D.weight d)
            • subsetSum D (Cdef.image d.succAbove))
            - (1 - D.weight d • atomMatrix (D.atom d)))
            + D.weight d • (1 - atomMatrix (D.atom d))
          = ((1 : ℝ) - D.weight d)
            • (subsetSum D (Cdef.image d.succAbove) - 1) := by
        module
      rw [hinner, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    rw [hfinal]
    exact (hkey.add (hlightpsd.smul htdpos.le)).smul (inv_nonneg.mpr hs.le)

end Gtz

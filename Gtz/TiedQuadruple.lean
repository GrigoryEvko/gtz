/-
# Tied quadruples: rank-one excess pins every insider to the boundary

The c5-constant audit's structural fact, generic and pure: when a subset's
excess `S_Q − I` is a rank-one square `hhᵀ` (the whitened tied-quadruple
normal form at any rank), the excess is singular in every ambient rank ≥ 2 —
so EVERY erased insider triple of a tied quadruple sits exactly on the
domination boundary, automatically. The tied variety's whole content is the
mixed structure; the insider ties cost nothing. Combined with the kernel's
`boundary_pivot_eq_one`, every insider pivot of a positive-definite cover
over a tied subset equals one identically.

Two lemmas, spectra-free:

* a rank-one square has determinant zero once the dimension exceeds one
  (two independent directions in the kernel of a rank-one map cannot both
  be avoided);
* under a rank-one excess, subtracting any atom keeps the determinant at
  `det(hhᵀ)·(1 − q) = 0` — the erase stays on the boundary without any
  computation of `q`.
-/
import Mathlib
import Gtz.CapSlack

namespace Gtz

open Matrix

variable {k : ℕ}

/-- **A rank-one square is singular in dimension ≥ 2**: `det(hhᵀ) = 0`. The
column space is at most a line, so the columns are dependent. -/
theorem det_atomMatrix_eq_zero (hk : 2 ≤ k) (h : Fin k → ℝ) :
    (atomMatrix h).det = 0 := by
  have hrank : (atomMatrix h).rank ≤ 1 := by
    rw [atomMatrix]
    exact Matrix.rank_vecMulVec_le h h
  by_contra hdet
  have hunit : IsUnit (atomMatrix h) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hfull : (atomMatrix h).rank = k := by
    rw [Matrix.rank_of_isUnit (atomMatrix h) hunit]
    simp
  omega

/-- **Insider erases of a tied subset stay on the boundary**: when the
excess is the rank-one square `hhᵀ` (the tied normal form), subtracting ANY
atom leaves the determinant at zero — the matrix determinant lemma gives
`det(hhᵀ − ggᵀ) = det(hhᵀ)·(1 − q) = 0` when `hhᵀ` is singular, and in the
singular case directly: the difference of two rank-one squares has rank at
most two, singular in every ambient rank ≥ 3. -/
theorem tied_erase_det_eq_zero (hk : 3 ≤ k) (tieDir atom : Fin k → ℝ) :
    (atomMatrix tieDir - atomMatrix atom).det = 0 := by
  -- the difference factors through a k×2 rectangle: rank ≤ 2
  have hfactor : atomMatrix tieDir - atomMatrix atom
      = (Matrix.of fun (row : Fin k) (col : Fin 2) =>
          if col = 0 then tieDir row else atom row)
        * (Matrix.of fun (col : Fin 2) (colIdx : Fin k) =>
          if col = 0 then tieDir colIdx else -(atom colIdx)) := by
    ext rowIdx colIdx
    simp only [atomMatrix, Matrix.sub_apply, Matrix.vecMulVec_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
    norm_num
    ring
  have hrank : (atomMatrix tieDir - atomMatrix atom).rank ≤ 2 := by
    rw [hfactor]
    refine le_trans (Matrix.rank_mul_le_left _ _) ?_
    refine le_trans (Matrix.rank_le_card_width _) ?_
    simp
  by_contra hdet
  have hunit : IsUnit (atomMatrix tieDir - atomMatrix atom) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hfull : (atomMatrix tieDir - atomMatrix atom).rank = k := by
    rw [Matrix.rank_of_isUnit _ hunit]
    simp
  omega

/-- **The insider-boundary law**: for a design subset whose excess is the
tied rank-one form `S_Q − 1 = hhᵀ` in rank ≥ 3, erasing any insider leaves
the erased excess determinant at zero — every insider triple of a tied
quadruple is boundary-dominated automatically, with no tie condition on the
erased atom. -/
theorem tied_subset_erase_boundary {m : ℕ} (hk : 3 ≤ k)
    (D : WeightedDesign m k) (Q : Finset (Fin m)) (tieDir : Fin k → ℝ)
    (htied : subsetSum D Q - 1 = atomMatrix tieDir) {d : Fin m} (hd : d ∈ Q) :
    (subsetSum D (Q.erase d) - 1).det = 0 := by
  have herase : subsetSum D (Q.erase d) - 1
      = (subsetSum D Q - 1) - atomMatrix (D.atom d) := by
    have hsum := Finset.sum_erase_add Q (fun c => atomMatrix (D.atom c)) hd
    rw [subsetSum, subsetSum, ← hsum]
    abel
  rw [herase, htied]
  exact tied_erase_det_eq_zero hk tieDir (D.atom d)

end Gtz

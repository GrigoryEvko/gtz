/-
# A rank-one downdate of a positive definite matrix is decided by its determinant

The star promotion of `Gtz/Wave/CellHStarPromotion.lean` turns the cell-H trio
into a dominating triple, but it pays for it with two admissibility hypotheses,
and a cell-H inhabitant supplies them only sometimes.  This module removes the
hypotheses entirely, by using the cell's own structure instead.

## The mechanism

Every triple of the cell-H trio is a RANK-ONE DOWNDATE of the four-set `A_y`:

  `S_{y,c,d} − 1 = A_y − g_b g_bᵀ` ,

and cell H carries `A_y ≻ 0` as a hypothesis.  For a positive definite `N` the
matrix determinant lemma reads

  `det(N − ggᵀ) = det N · (1 − gᵀN⁻¹g)` ,

so a positive determinant forces `gᵀN⁻¹g < 1`, which is exactly the landed
rank-one Schur criterion `Gtz.posDef_sub_vecMulVec_iff`.  Hence

  **`N ≻ 0` and `det(N − ggᵀ) > 0` ⟹ `N − ggᵀ ≻ 0`**
  (`Gtz.posDef_sub_vecMulVec_of_det_pos`).

The eigenvalue reading is the same one the cell-H lane already used for `A_z`: a
rank-one downdate moves at most one eigenvalue across zero, so a downdate of a
positive definite matrix has at most one nonpositive eigenvalue, and a positive
determinant then forbids that one.  No interlacing is needed — the determinant
lemma and the Schur criterion do it.

## What it closes

The promotion becomes unconditional on cell H
(`Gtz.cellH_exists_dominating_triple_of_posDef`): the trio's positive gap
determinant is a strictly dominating triple with no admissibility hypothesis at
all, because `A_y ≻ 0` is already part of the cell.

[MEASURED on 32,885 exact cell-H inhabitants: the trio fires at 100.0000%, some
gap determinant is positive at 100.0000%, and that triple is positive definite
at 100.0000% — while the star of the inserted atom is fully admissible at only
40.06% and the two pairs the star promotion needs at 71.97%.  The downdate route
covers the cell; the admissibility route does not.]
-/
import Gtz.Wave.CellHStarPromotion
import Gtz.LinAlg.SchurRankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {k : ℕ}

/-! ## 1. The rank-one form as a column times a row -/

/-- A rank-one operator is a column times a row. -/
theorem vecMulVec_eq_replicate (v w : Fin k → ℝ) :
    Matrix.vecMulVec v w
      = Matrix.replicateCol (Fin 1) v * Matrix.replicateRow (Fin 1) w := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.mul_apply]

/-! ## 2. The matrix determinant lemma at a rank-one downdate -/

/-- **THE DETERMINANT OF A RANK-ONE DOWNDATE.**  For invertible `N`, the
determinant of `N − ggᵀ` is the determinant of `N` scaled by one less the
reading of `g` against the inverse. -/
theorem det_sub_vecMulVec (N : Matrix (Fin k) (Fin k) ℝ) (hN : IsUnit N.det)
    (g : Fin k → ℝ) :
    (N - Matrix.vecMulVec g g).det = N.det * (1 - g ⬝ᵥ (N⁻¹ *ᵥ g)) := by
  have hrewrite : N - Matrix.vecMulVec g g
      = N + Matrix.replicateCol (Fin 1) (-g) * Matrix.replicateRow (Fin 1) g := by
    rw [← vecMulVec_eq_replicate]
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring
  rw [hrewrite, Matrix.det_add_mul (Matrix.replicateCol (Fin 1) (-g))
    (Matrix.replicateRow (Fin 1) g) hN]
  congr 1
  rw [Matrix.det_unique]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  have hswap : (∑ x : Fin k, ∑ y : Fin k, g y * N⁻¹ y x * g x)
      = ∑ y : Fin k, ∑ x : Fin k, g y * N⁻¹ y x * g x := Finset.sum_comm
  have hsum : (∑ x : Fin k, ∑ y : Fin k, g y * N⁻¹ y x * g x)
      = ∑ x : Fin k, ∑ y : Fin k, g x * (N⁻¹ x y * g y) := by
    rw [hswap]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  linarith [hsum]

/-! ## 3. The promotion -/

/-- **A POSITIVE DETERMINANT DECIDES A RANK-ONE DOWNDATE.**  A rank-one downdate
of a positive definite matrix moves at most one eigenvalue across zero, so a
positive determinant leaves none across: the downdate is positive definite.

No admissibility, no Sylvester chain, no interlacing — the determinant lemma
supplies the reading and the landed rank-one Schur criterion converts it. -/
theorem posDef_sub_vecMulVec_of_det_pos {N : Matrix (Fin k) (Fin k) ℝ}
    (hN : N.PosDef) {g : Fin k → ℝ}
    (hdet : 0 < (N - Matrix.vecMulVec g g).det) :
    (N - Matrix.vecMulVec g g).PosDef := by
  have hunit : IsUnit N.det := isUnit_iff_ne_zero.mpr (ne_of_gt hN.det_pos)
  rw [det_sub_vecMulVec N hunit g] at hdet
  have hreading : g ⬝ᵥ (N⁻¹ *ᵥ g) < 1 := by
    by_contra hcon
    push_neg at hcon
    have : N.det * (1 - g ⬝ᵥ (N⁻¹ *ᵥ g)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hN.det_pos.le (by linarith)
    linarith
  exact (posDef_sub_vecMulVec_iff N hN g).mpr hreading

/-- The atom form: a triple obtained by removing one atom from a positive
definite four-set is decided by its own gap determinant. -/
theorem posDef_sub_atomMatrix_of_det_pos {N : Matrix (Fin 3) (Fin 3) ℝ}
    (hN : N.PosDef) {g : Fin 3 → ℝ}
    (hdet : 0 < (N - atomMatrix g).det) :
    (N - atomMatrix g).PosDef :=
  posDef_sub_vecMulVec_of_det_pos hN hdet

/-! ## 4. Cell H, unconditionally -/

/-- **CELL H PRODUCES A DOMINATING TRIPLE WITH NO ADMISSIBILITY HYPOTHESIS.**
Each triple of the trio is the four-set `A_y` less one outside atom, and cell H
carries `A_y ≻ 0`, so the trio's positive gap determinant is strict domination
outright.

This supersedes `Gtz.cellH_exists_dominating_triple`, which paid two
admissibility hypotheses that a cell-H inhabitant supplies only sometimes. -/
theorem cellH_exists_dominating_triple_of_posDef {ay b c d : Fin 3 → ℝ}
    (hAy : (atomMatrix ay + atomMatrix b + atomMatrix c + atomMatrix d - 1).PosDef)
    (hdet : 0 < (atomMatrix ay + atomMatrix c + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix ay + atomMatrix b + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix ay + atomMatrix b + atomMatrix c - 1).det) :
    (atomMatrix ay + atomMatrix c + atomMatrix d - 1).PosDef
      ∨ (atomMatrix ay + atomMatrix b + atomMatrix d - 1).PosDef
      ∨ (atomMatrix ay + atomMatrix b + atomMatrix c - 1).PosDef := by
  have hb : atomMatrix ay + atomMatrix c + atomMatrix d - 1
      = (atomMatrix ay + atomMatrix b + atomMatrix c + atomMatrix d - 1)
        - atomMatrix b := by abel
  have hc : atomMatrix ay + atomMatrix b + atomMatrix d - 1
      = (atomMatrix ay + atomMatrix b + atomMatrix c + atomMatrix d - 1)
        - atomMatrix c := by abel
  have hd : atomMatrix ay + atomMatrix b + atomMatrix c - 1
      = (atomMatrix ay + atomMatrix b + atomMatrix c + atomMatrix d - 1)
        - atomMatrix d := by abel
  rcases hdet with h | h | h
  · rw [hb] at h ⊢; exact Or.inl (posDef_sub_atomMatrix_of_det_pos hAy h)
  · rw [hc] at h ⊢; exact Or.inr (Or.inl (posDef_sub_atomMatrix_of_det_pos hAy h))
  · rw [hd] at h ⊢; exact Or.inr (Or.inr (posDef_sub_atomMatrix_of_det_pos hAy h))

end Gtz

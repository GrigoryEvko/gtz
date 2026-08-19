import Gtz.Wave.CorankTwoDeficitArm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The corner residual of the corank-two arm is false without a tie

`Gtz.NonplanarGhostResidual` asks, at EVERY non-planar corank-two corner of a
`(6,3)` design, for an inside atom whose ghost pair carries a short block of
six-set pivots.  It carries no tie hypothesis.  This module proves that the
statement is false, so `Gtz.corankTwoGap_absurd` can never be discharged as it
stands and the arm has to be rebuilt over a residual that carries the tie —
which `Gtz.corankTwoGap_absurd'` does.

## The foil

The design `Gtz.residualFoil` has the six atoms

  `g₀ = (0,1,0)` , `g₁ = (0,0,1)` , `g₂ = (2,0,0)` ,
  `g₃ = (3/2,2,1/3)` , `g₄ = (3/2,−2,1/3)` , `g₅ = (1/6,0,−4/3)`

and the weights `(253, 173, 367, 360, 360, 1620)/3133`.  The inside triple
`C = {0,1,2}` is orthogonal, so `S_C = diag(4,1,1)` and the gap is

  `S_C − 1 = 3 • u uᵀ` , `u = (1,0,0)` ,

a corank-two corner with `lam = 3`.  The outside atom `g₃` reads `u` at `3/2`,
so the corner is non-planar.  The two outside atoms `g₃` and `g₄` are mirror
images in the second coordinate and `g₅` cancels their cross term, so the
six-set gap is the block matrix

  `W = S_univ − 1 = [[271/36, 0, 7/9], [0, 8, 0], [7/9, 0, 2]]`

whose inverse is exact and rational.  The three inside pivots are

  `P₀₀ = 1/8` , `P₁₁ = 2439/4682` , `P₂₂ = 1296/2341` ,

and the LAST TWO EXCEED ONE HALF.  Every inside atom leaves a ghost pair that
contains `1` or `2`, so every ghost pair carries a pivot above one half and
`Gtz.GhostBlockShort` fails at every selector
(`Gtz.not_nonplanarGhostResidual`).  Every weight of the foil is above `1/20`
(`Gtz.residualFoil_weight_floor`), so no weight degeneration is at work.

## What survives

The weighted surface does survive at this design.  The pivot matrix is block
diagonal in the atom `0`, so `P₀₁ = P₀₂ = 0` and the swap bracket at the small
pivot `P₀₀ = 1/8` is very negative.  The weighted deficit at the selector `1`
therefore holds, although the short block does not.  That is exactly why
`Gtz.NonplanarDeficitResidual` is the correct residual to produce: it is wider
at each corner AND it carries the tie.
-/

namespace Gtz

open Matrix Finset

namespace ResidualFoil

/-- The six atoms of the foil. -/
noncomputable def atomFn : Fin 6 → (Fin 3 → ℝ) :=
  ![![0, 1, 0], ![0, 0, 1], ![2, 0, 0],
    ![3/2, 2, 1/3], ![3/2, -2, 1/3], ![1/6, 0, -4/3]]

/-- The six weights of the foil. -/
noncomputable def weightFn : Fin 6 → ℝ :=
  ![253/3133, 173/3133, 367/3133, 360/3133, 360/3133, 1620/3133]

/-- The corner direction. -/
def axisVec : Fin 3 → ℝ := ![1, 0, 0]

/-- The six-set gap of the foil, in closed form. -/
noncomputable def gapMat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![271/36, 0, 7/9; 0, 8, 0; 7/9, 0, 2]

/-- The inverse of the six-set gap, in closed form. -/
noncomputable def gapInvMat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![324/2341, 0, -126/2341; 0, 1/8, 0; -126/2341, 0, 2439/4682]

end ResidualFoil

open ResidualFoil

/-- **The foil.**  A primitive `(6,3)` design with a non-planar corank-two
corner at `{0,1,2}` and no short ghost block at any selector. -/
noncomputable def residualFoil : WeightedDesign 6 3 where
  atom := atomFn
  weight := weightFn
  weight_pos := by
    intro c
    fin_cases c <;> norm_num [weightFn]
  weight_sum_one := by
    simp [weightFn, Fin.sum_univ_six]
    norm_num
  isParseval := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [atomFn, weightFn, atomMatrix, Matrix.vecMulVec_apply, Fin.sum_univ_six,
        Matrix.one_apply] <;>
      norm_num

/-! ## 1. The closed forms -/

/-- The six-set gap of the foil. -/
theorem residualFoil_gapMat : subsetSum residualFoil Finset.univ - 1 = gapMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [subsetSum, residualFoil, atomFn, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_six, Matrix.one_apply, gapMat] <;>
    norm_num

/-- The inverse of the six-set gap of the foil. -/
theorem residualFoil_gapInv :
    (subsetSum residualFoil Finset.univ - 1)⁻¹ = gapInvMat := by
  rw [residualFoil_gapMat]
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gapMat, gapInvMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    norm_num

/-- **The corner.**  The inside triple is orthogonal, so its gap is a positive
multiple of the atom matrix of the first axis. -/
theorem residualFoil_corner :
    subsetSum residualFoil ({0, 1, 2} : Finset (Fin 6)) - 1
      = (3 : ℝ) • atomMatrix axisVec := by
  have hsum : subsetSum residualFoil ({0, 1, 2} : Finset (Fin 6))
      = atomMatrix (residualFoil.atom 0) + atomMatrix (residualFoil.atom 1)
        + atomMatrix (residualFoil.atom 2) := by
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    abel
  rw [hsum]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [residualFoil, atomFn, axisVec, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.one_apply] <;>
    norm_num

/-! ## 2. The three inside pivots -/

/-- The pivot of the first inside atom. -/
theorem residualFoil_pivot_zero : sixSetPivot residualFoil 0 0 = 1 / 8 := by
  rw [sixSetPivot, residualFoil_gapInv]
  simp only [residualFoil, atomFn, gapInvMat, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.of_apply, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_val']
  norm_num

/-- The pivot of the second inside atom, which exceeds one half. -/
theorem residualFoil_pivot_one : sixSetPivot residualFoil 1 1 = 2439 / 4682 := by
  rw [sixSetPivot, residualFoil_gapInv]
  simp only [residualFoil, atomFn, gapInvMat, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.of_apply, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_val']
  norm_num

/-- The pivot of the third inside atom, which exceeds one half. -/
theorem residualFoil_pivot_two : sixSetPivot residualFoil 2 2 = 1296 / 2341 := by
  rw [sixSetPivot, residualFoil_gapInv]
  simp only [residualFoil, atomFn, gapInvMat, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.of_apply, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_val']
  norm_num

/-! ## 3. The foil carries no dust -/

/-- **Every weight of the foil is above one twentieth.**  The refutation is not
an artifact of a vanishing weight: the design sits well inside the weight
simplex. -/
theorem residualFoil_weight_floor (c : Fin 6) : 1 / 20 < residualFoil.weight c := by
  fin_cases c <;> norm_num [residualFoil, weightFn]

/-! ## 4. The refutation -/

/-- **The corner residual of the corank-two arm is false.**  The foil has a
non-planar corank-two corner at which no inside atom leaves a short ghost pair,
because two of the three inside pivots exceed one half. -/
theorem not_nonplanarGhostResidual : ¬ NonplanarGhostResidual residualFoil := by
  intro hres
  obtain ⟨e, he, f, h, hfh, herase, hshort⟩ :=
    hres ({0, 1, 2} : Finset (Fin 6)) (by decide) 3 (by norm_num) axisVec
      (by simp [axisVec, dotProduct, Fin.sum_univ_three])
      residualFoil_corner
      ⟨3, by decide, by
        simp [residualFoil, atomFn, axisVec, dotProduct, Fin.sum_univ_three]⟩
  obtain ⟨hf2, hh2, -, -⟩ := hshort
  have hpair : ∀ c : Fin 6, c ∈ ({f, h} : Finset (Fin 6)) →
      2 * sixSetPivot residualFoil c c < 1 := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact hf2
    · exact hh2
  have hkey : (1 : Fin 6) ∈ ({0, 1, 2} : Finset (Fin 6)).erase e
      ∨ (2 : Fin 6) ∈ ({0, 1, 2} : Finset (Fin 6)).erase e := by
    fin_cases e <;> revert he <;> decide
  rw [herase] at hkey
  rcases hkey with hone | htwo
  · have := hpair 1 hone
    rw [residualFoil_pivot_one] at this
    norm_num at this
  · have := hpair 2 htwo
    rw [residualFoil_pivot_two] at this
    norm_num at this

/-- **Some design refutes the corner residual.**  Only the tie can rescue the
corner residual of the corank-two arm. -/
theorem exists_not_nonplanarGhostResidual :
    ∃ D : WeightedDesign 6 3, (∀ c, 1 / 20 < D.weight c) ∧ ¬ NonplanarGhostResidual D :=
  ⟨residualFoil, residualFoil_weight_floor, not_nonplanarGhostResidual⟩

end Gtz

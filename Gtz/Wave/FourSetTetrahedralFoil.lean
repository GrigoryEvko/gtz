import Gtz.Wave.CoweightedMemberLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The four-set alone carries no obstruction

The heavy-inside residual asks to refute `{cell H, S ≥ 0, the three outside
floors}`.  This module proves that the FOUR-SET PART of that system — a
positive definite gap with every member floor — is REALIZABLE, so no
certificate can succeed from the four-set data alone.

The witness is the scaled sign tetrahedron `v_a = (9/10)·(±1,±1,±1)` over
the even sign patterns.  Its atom sum is `(81/25)·1`, so the gap is
`(56/25)·1 ≻ 0`, and every reading is

  `r_a = (25/56)·|v_a|² = 243/224 > 1` :

all four floors hold STRICTLY at a positive definite gap
(`Gtz.fourSet_posDef_gap_all_floors_realizable`).  Through
`Gtz.member_floor_iff_gapDet_erase_nonpos` the same witness has every
3-subset failing while the 4-set dominates — the exact sign pattern of the
heavy-inside floor system.

## What this rules out

Every generator of a refuting certificate that is expressible in the member
atoms alone — the member Gram, the member readings, the coweight ledgers of
the four-set — is satisfied by this witness together with the floors.  A
certificate for the residual must therefore consume the corner data: the
frame relations of `Z1`, Parseval over all six atoms with the excluded pair
included, and the failure of the other four-set.  This is the structural
reason every member-side aggregate degenerated at the roof.  The obstruction
was never in the four-set.
-/

namespace Gtz

open Matrix Finset

/-- The scaled sign tetrahedron: the four even sign patterns of
`(9/10)·(±1,±1,±1)`. -/
noncomputable def tetraFoilAtom : Fin 4 → Fin 3 → ℝ :=
  ![![9/10, 9/10, 9/10], ![9/10, -(9/10), -(9/10)],
    ![-(9/10), 9/10, -(9/10)], ![-(9/10), -(9/10), 9/10]]

/-- The atom sum of the tetrahedral foil is a positive multiple of the
identity. -/
theorem tetraFoil_sum_eq :
    ∑ a, atomMatrix (tetraFoilAtom a) = (81 / 25 : ℝ) • 1 := by
  ext i j
  simp only [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply,
    Fin.sum_univ_four, tetraFoilAtom, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      Matrix.head_fin_const]

/-- The gap of the tetrahedral foil. -/
theorem tetraFoil_gap_eq :
    (∑ a, atomMatrix (tetraFoilAtom a)) - 1 = (56 / 25 : ℝ) • 1 := by
  rw [tetraFoil_sum_eq]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases h : i = j <;> simp [h] <;> norm_num

/-- The gap of the tetrahedral foil is positive definite. -/
theorem tetraFoil_gap_posDef :
    ((∑ a, atomMatrix (tetraFoilAtom a)) - 1).PosDef := by
  rw [tetraFoil_gap_eq]
  exact Matrix.PosDef.one.smul (by norm_num)

/-- The inverse gap of the tetrahedral foil. -/
theorem tetraFoil_gap_inv :
    ((∑ a, atomMatrix (tetraFoilAtom a)) - 1)⁻¹ = (25 / 56 : ℝ) • 1 := by
  rw [tetraFoil_gap_eq]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  norm_num

/-- Every member of the tetrahedral foil reads the inverse gap strictly past
one: `r_a = 243/224`. -/
theorem tetraFoil_reading (a : Fin 4) :
    tetraFoilAtom a ⬝ᵥ (((∑ b, atomMatrix (tetraFoilAtom b)) - 1)⁻¹
        *ᵥ tetraFoilAtom a) = 243 / 224 := by
  rw [tetraFoil_gap_inv, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul]
  have hnorm : tetraFoilAtom a ⬝ᵥ tetraFoilAtom a = 243 / 100 := by
    fin_cases a <;>
      norm_num [tetraFoilAtom, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
        Matrix.head_fin_const]
  rw [hnorm]
  norm_num

/-- **THE FOUR-SET FOIL.**  A positive definite four-set gap with all four
member floors STRICT is realizable.  No certificate for the heavy-inside
residual can work from the four-set data alone: the obstruction must come
from the corner, the six-atom Parseval, and the failed four-set. -/
theorem fourSet_posDef_gap_all_floors_realizable :
    ∃ v : Fin 4 → Fin 3 → ℝ,
      ((∑ a, atomMatrix (v a)) - 1).PosDef ∧
      ∀ a, 1 < v a ⬝ᵥ (((∑ b, atomMatrix (v b)) - 1)⁻¹ *ᵥ v a) := by
  refine ⟨tetraFoilAtom, tetraFoil_gap_posDef, fun a => ?_⟩
  rw [tetraFoil_reading a]
  norm_num

end Gtz

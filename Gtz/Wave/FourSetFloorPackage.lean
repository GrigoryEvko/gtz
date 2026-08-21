/-
# The four member floors of a four-set are ONE inverse-free inequality

Both `Z1` cells are stated as floor systems.  Cell H carries four floors of the
surviving four-set, cell B carries eight — four at each of its two surviving
four-sets — and `Gtz.OneAxisZeroBothLightChartSystem` writes them as seven gap
determinant signs, because the two `y`-floors and `z`-floors erase to the same
outside triple.

Those floors are not independent.  The landed
`Gtz.sum_fourSet_gapDet_eq_det_sub_e2` totals the four triple gap determinants
of a four-set at `det − e₂` of its own gap, so four nonpositive determinants
give ONE inequality:

  **`Gtz.fourSet_det_le_secondInvariant_of_floors`: `det A ≤ e₂(A)`.**

For a positive definite `A` with eigenvalues `a, b, c` that reads
`abc ≤ ab + ac + bc`, which is `tr(A⁻¹) ≥ 1`.  The four floors say each member
reads `A⁻¹` at least one, and the four member readings total `3 + tr(A⁻¹)`
because the four atoms rebuild `A + 1`.  So the aggregate of the four floors IS
`tr(A⁻¹) ≥ 1`, and `det A ≤ e₂(A)` is that statement with the inverse cleared.

## The corner pays three free equations

A corner's gap is rank one, so its second invariant vanishes and the four-set
law makes EVERY four-set determinant through the corner vanish
(`Gtz.corner_fourSet_gapDet_eq_zero`).  At `(6,3)` that is three polynomial
EQUATIONS in the atoms, available before any floor is read, and they were not
in the cells' systems.  A certificate search on either cell may use them.

## What it does not do

It does not close either cell.  It replaces four sign conditions by one, and it
adds three equations.  The cells' own residual — that some star fires — is
untouched.
-/
import Gtz.Wave.OutsideReadingFloor
import Gtz.Wave.DiamondNeighborhoodFourSet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. Four floors collapse to one inequality -/

/-- **THE FLOOR PACKAGE.**  Four nonpositive triple gap determinants inside a
four-set put that four-set's determinant under its own second invariant.  The
landed four-set total carries the whole statement. -/
theorem fourSet_det_le_secondInvariant_of_floors {a b c d : Fin 3 → ℝ}
    (hbcd : (atomMatrix b + atomMatrix c + atomMatrix d - 1).det ≤ 0)
    (hacd : (atomMatrix a + atomMatrix c + atomMatrix d - 1).det ≤ 0)
    (habd : (atomMatrix a + atomMatrix b + atomMatrix d - 1).det ≤ 0)
    (habc : (atomMatrix a + atomMatrix b + atomMatrix c - 1).det ≤ 0) :
    (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).det
      ≤ secondInvariantOfThree
          (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1) := by
  have htotal := sum_fourSet_gapDet_eq_det_sub_e2 a b c d
  rw [secondInvariantOfThree_eq_trace_form]
  linarith

/-- **THE PACKAGE IS SHARP AT THE BOUNDARY.**  If the four determinants total
zero the inequality is an equality, so nothing is lost by the collapse. -/
theorem fourSet_det_eq_secondInvariant_of_floors_eq_zero {a b c d : Fin 3 → ℝ}
    (hsum : (atomMatrix b + atomMatrix c + atomMatrix d - 1).det
        + (atomMatrix a + atomMatrix c + atomMatrix d - 1).det
        + (atomMatrix a + atomMatrix b + atomMatrix d - 1).det
        + (atomMatrix a + atomMatrix b + atomMatrix c - 1).det = 0) :
    (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).det
      = secondInvariantOfThree
          (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1) := by
  have htotal := sum_fourSet_gapDet_eq_det_sub_e2 a b c d
  rw [secondInvariantOfThree_eq_trace_form]
  linarith

/-! ## 2. The corner's free equations -/

/-- A rank-one form has a vanishing second invariant. -/
theorem secondInvariantOfThree_smul_atomMatrix (lam : ℝ) (u : Fin 3 → ℝ) :
    secondInvariantOfThree (lam • atomMatrix u) = 0 := by
  simp only [secondInvariantOfThree, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-- **A RANK-ONE FORM UPDATED BY ONE ATOM IS STILL SINGULAR.**  Two rank-one
summands cannot fill three dimensions. -/
theorem det_smul_atomMatrix_add_atomMatrix (lam : ℝ) (u v : Fin 3 → ℝ) :
    (lam • atomMatrix u + atomMatrix v).det = 0 := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply,
    atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-- **THE CORNER PAYS A FREE EQUATION AT EVERY FOUR-SET THROUGH IT.**  A corner
gap is rank one, so adjoining any label leaves a singular gap.  At `(6,3)` this
is three polynomial equations in the atoms, available before any floor is
read. -/
theorem corner_fourSet_gapDet_eq_zero (D : WeightedDesign m 3) {T : Finset (Fin m)}
    {lam : ℝ} {u : Fin 3 → ℝ} (hcorner : subsetSum D T - 1 = lam • atomMatrix u)
    {d : Fin m} (hd : d ∉ T) :
    (subsetSum D (insert d T) - 1).det = 0 := by
  have hins : subsetSum D (insert d T) - 1
      = (subsetSum D T - 1) + atomMatrix (D.atom d) := by
    rw [subsetSum, subsetSum, Finset.sum_insert hd]; abel
  rw [hins, hcorner, det_smul_atomMatrix_add_atomMatrix]

/-- **A CORNER CARRIES NO STRICT FOUR-SET.**  The determinant is zero, so the
gap is never positive definite.  This is the corank-two arm's half of the
Loewner separation. -/
theorem corner_fourSet_not_posDef (D : WeightedDesign m 3) {T : Finset (Fin m)}
    {lam : ℝ} {u : Fin 3 → ℝ} (hcorner : subsetSum D T - 1 = lam • atomMatrix u)
    {d : Fin m} (hd : d ∉ T) :
    ¬ (subsetSum D (insert d T) - 1).PosDef := by
  intro hpd
  exact absurd (corner_fourSet_gapDet_eq_zero D hcorner hd) (ne_of_gt hpd.det_pos)

/-! ## 3. The cells read the package -/

/-- **CELL B'S SEVEN FLOORS PAY TWICE.**  The four triples of the surviving
`y`-four-set are the outside triple together with the three `y`-triples, and the
same holds at `z`.  So the seven sign conditions of
`Gtz.OneAxisZeroBothLightChartSystem` deliver the package at BOTH four-sets. -/
theorem bothLight_det_le_secondInvariant {y z d4 d5 d6 : Fin 3 → ℝ}
    (hout : (atomMatrix d4 + atomMatrix d5 + atomMatrix d6 - 1).det ≤ 0)
    (hy56 : (atomMatrix y + atomMatrix d5 + atomMatrix d6 - 1).det ≤ 0)
    (hy46 : (atomMatrix y + atomMatrix d4 + atomMatrix d6 - 1).det ≤ 0)
    (hy45 : (atomMatrix y + atomMatrix d4 + atomMatrix d5 - 1).det ≤ 0)
    (hz56 : (atomMatrix z + atomMatrix d5 + atomMatrix d6 - 1).det ≤ 0)
    (hz46 : (atomMatrix z + atomMatrix d4 + atomMatrix d6 - 1).det ≤ 0)
    (hz45 : (atomMatrix z + atomMatrix d4 + atomMatrix d5 - 1).det ≤ 0) :
    (atomMatrix y + atomMatrix d4 + atomMatrix d5 + atomMatrix d6 - 1).det
        ≤ secondInvariantOfThree
            (atomMatrix y + atomMatrix d4 + atomMatrix d5 + atomMatrix d6 - 1)
      ∧ (atomMatrix z + atomMatrix d4 + atomMatrix d5 + atomMatrix d6 - 1).det
        ≤ secondInvariantOfThree
            (atomMatrix z + atomMatrix d4 + atomMatrix d5 + atomMatrix d6 - 1) := by
  constructor
  · exact fourSet_det_le_secondInvariant_of_floors hout hy56 hy46 hy45
  · exact fourSet_det_le_secondInvariant_of_floors hout hz56 hz46 hz45

end Gtz

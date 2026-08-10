import Gtz.Design.LineBranchFreePairBracketExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# One-slot determinants as four bracket squares

A one-slot swap replaces one atom of a card-three subset by another, so its
gap determinant is the determinant of `A_f + A_s + A_in - A_out` where each
`A` is a rank-one atom matrix.  Signed Cauchy-Binet collapses that to four
coordinate-bracket squares with one positive and three negative signs.

Both statements below are UNCONDITIONAL in the four vectors: there is no
design, no hidden form, no Parseval identity and, despite the module name
inherited from the scratch lane, no rank-two hypothesis anywhere.  They are
pure determinant algebra, which is what makes them reusable at every
one-slot site rather than only on the line branch.
-/

namespace Gtz

open Matrix

/-- The signed Cauchy-Binet identity for a one-slot gap determinant: the
determinant of three atom matrices minus a fourth is the inserted triple's
bracket square minus the three bracket squares that use the removed vector.
Unconditional in all four vectors. -/
theorem det_threeAtomMatrix_sub_atomMatrix_eq_bracketSquares
    (first second inserted removed : Fin 3 -> Real) :
    (atomMatrix first + atomMatrix second + atomMatrix inserted
        - atomMatrix removed).det
      = tripleBracket first second inserted ^ 2
        - tripleBracket first second removed ^ 2
        - tripleBracket first inserted removed ^ 2
        - tripleBracket second inserted removed ^ 2 := by
  simp [Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply,
    tripleBracket_eq]
  ring

/-- A one-slot swap FAILS to have positive gap determinant exactly when the
inserted triple's bracket square is dominated by the sum of the three bracket
squares through the removed vector.  This is the determinant refusal at a
single removed vector, restated as one scalar inequality with no matrix left
in it. -/
theorem rankTwo_oneSlot_axis_refusal_iff
    (first second inserted : Fin 3 -> Real) (axis : Fin 3 -> Real) :
    (atomMatrix first + atomMatrix second + atomMatrix inserted
        - atomMatrix axis).det <= 0
      <-> tripleBracket first second inserted ^ 2
          <= tripleBracket first second axis ^ 2
            + tripleBracket first inserted axis ^ 2
            + tripleBracket second inserted axis ^ 2 := by
  rw [det_threeAtomMatrix_sub_atomMatrix_eq_bracketSquares]
  constructor <;> intro hrefusal <;> linarith

end Gtz

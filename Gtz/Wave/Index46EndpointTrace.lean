import Gtz.Wave.TypeNineAlignedOperatorExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-- A non-singular endpoint plane in the last two coefficient coordinates
already contradicts the rank-two coefficient trace and the shifted-weight
budget.  This is the scalar exit for the opposite-sign phase of support leaf
46. -/
theorem false_of_indexFortySix_endpointPlane
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    {c k p l q d0 d1 d2 d3 d4 d5 : ℝ}
    (hsymmetric : M.transpose = M) (hidempotent : M * M = M)
    (hc : c ≠ 0) (hdet : k * q - p * l ≠ 0)
    (hd0 : 0 ≤ d0) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (hone : c * M 1 1 = d1 * c)
    (hfourTwo : k * M 2 2 + p * M 3 2 = d4 * k)
    (hfourThree : k * M 2 3 + p * M 3 3 = d4 * p)
    (hfiveTwo : l * M 2 2 + q * M 3 2 = d5 * l)
    (hfiveThree : l * M 2 3 + q * M 3 3 = d5 * q)
    (htrace : Matrix.trace M = 2)
    (hshiftedSum : d0 + d1 + d2 + d3 + d4 + d5 < 1) : False := by
  have hdiagOne : M 1 1 = d1 := by
    apply mul_left_cancel₀ hc
    linarith only [hone]
  have hendpointTrace : M 2 2 + M 3 3 = d4 + d5 :=
    twoByTwo_trace_eq_of_diagonal_intertwines hdet
      hfourTwo hfourThree hfiveTwo hfiveThree
  have htraceEntries : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2 := by
    simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four] using htrace
  have hdiagZero : M 0 0 ≤ 1 :=
    diagonal_le_one_of_symmetricIdempotent hsymmetric hidempotent 0
  linarith only [hdiagOne, hendpointTrace, htraceEntries, hdiagZero,
    hd0, hd2, hd3, hshiftedSum]


end Gtz

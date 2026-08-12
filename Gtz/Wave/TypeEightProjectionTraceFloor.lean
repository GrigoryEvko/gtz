import Gtz.Wave.SupportTypeEightTraceFloor
import Gtz.Quantitative.ChartDescentFromMinimality
import Gtz.Design.StressFreeNormalizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-- The type-eight support frame has trace at least one against every
symmetric rank-two orthogonal projection.  This is the basis-free form used
by the stationary coefficient projection. -/
theorem typeEight_projection_trace_floor
    (planeZeroOne planeZeroTwo planeOneTwo axisFirst axisSecond extra : Fin 4 -> Real)
    (hzeroOneUnit : planeZeroOne ⬝ᵥ planeZeroOne = 1)
    (hzeroTwoUnit : planeZeroTwo ⬝ᵥ planeZeroTwo = 1)
    (honeTwoUnit : planeOneTwo ⬝ᵥ planeOneTwo = 1)
    (haxisFirstUnit : axisFirst ⬝ᵥ axisFirst = 1)
    (haxisSecondUnit : axisSecond ⬝ᵥ axisSecond = 1)
    (hzeroOneTwo : planeZeroOne 2 = 0)
    (hzeroOneThree : planeZeroOne 3 = 0)
    (hzeroTwoOne : planeZeroTwo 1 = 0)
    (hzeroTwoThree : planeZeroTwo 3 = 0)
    (honeTwoZero : planeOneTwo 0 = 0)
    (honeTwoThree : planeOneTwo 3 = 0)
    (haxisFirstZero : axisFirst 0 = 0 ∧ axisFirst 1 = 0 ∧ axisFirst 2 = 0)
    (haxisSecondZero : axisSecond 0 = 0 ∧ axisSecond 1 = 0 ∧ axisSecond 2 = 0)
    (projection : Matrix (Fin 4) (Fin 4) Real)
    (hsymmetric : projection.transpose = projection)
    (hidempotent : projection * projection = projection)
    (htrace : Matrix.trace projection = 2) :
    1 <= Matrix.trace (projection *
      (atomMatrix planeZeroOne + atomMatrix planeZeroTwo + atomMatrix planeOneTwo +
        atomMatrix axisFirst + atomMatrix axisSecond + atomMatrix extra)) := by
  let rotateOne := rotateZeroOne planeZeroOne
  let rotateTwo := rotateZeroTwo planeZeroTwo
  let rotateThree := rotateOneTwo planeOneTwo
  let frame := atomMatrix planeZeroOne + atomMatrix planeZeroTwo + atomMatrix planeOneTwo +
    atomMatrix axisFirst + atomMatrix axisSecond + atomMatrix extra
  let complement := atomMatrix rotateOne + atomMatrix rotateTwo + atomMatrix rotateThree
  have haxisFirst := atomMatrix_eq_fourthAxis axisFirst haxisFirstUnit
    haxisFirstZero.1 haxisFirstZero.2.1 haxisFirstZero.2.2
  have haxisSecond := atomMatrix_eq_fourthAxis axisSecond haxisSecondUnit
    haxisSecondZero.1 haxisSecondZero.2.1 haxisSecondZero.2.2
  have hresolve : frame + complement =
      (2 : Real) • (1 : Matrix (Fin 4) (Fin 4) Real) + atomMatrix extra := by
    have hone := atomMatrix_add_rotateZeroOne planeZeroOne hzeroOneUnit
      hzeroOneTwo hzeroOneThree
    have htwo := atomMatrix_add_rotateZeroTwo planeZeroTwo hzeroTwoUnit
      hzeroTwoOne hzeroTwoThree
    have hthree := atomMatrix_add_rotateOneTwo planeOneTwo honeTwoUnit
      honeTwoZero honeTwoThree
    dsimp only [frame, complement, rotateOne, rotateTwo, rotateThree]
    rw [haxisFirst, haxisSecond]
    calc
      _ = (atomMatrix planeZeroOne + atomMatrix (rotateZeroOne planeZeroOne)) +
          (atomMatrix planeZeroTwo + atomMatrix (rotateZeroTwo planeZeroTwo)) +
          (atomMatrix planeOneTwo + atomMatrix (rotateOneTwo planeOneTwo)) +
          (atomMatrix fourthAxis + atomMatrix fourthAxis) + atomMatrix extra := by
            abel
      _ = Matrix.diagonal ![1, 1, 0, 0] + Matrix.diagonal ![1, 0, 1, 0] +
          Matrix.diagonal ![0, 1, 1, 0] +
          (atomMatrix fourthAxis + atomMatrix fourthAxis) + atomMatrix extra := by
            rw [hone, htwo, hthree]
      _ = (2 : Real) • (1 : Matrix (Fin 4) (Fin 4) Real) + atomMatrix extra := by
            ext row col
            fin_cases row <;> fin_cases col <;>
              norm_num [atomMatrix, Matrix.vecMulVec_apply, fourthAxis]
  have hrotateOneUnit : rotateOne ⬝ᵥ rotateOne = 1 :=
    rotateZeroOne_unit planeZeroOne hzeroOneUnit hzeroOneTwo hzeroOneThree
  have hrotateTwoUnit : rotateTwo ⬝ᵥ rotateTwo = 1 :=
    rotateZeroTwo_unit planeZeroTwo hzeroTwoUnit hzeroTwoOne hzeroTwoThree
  have hrotateThreeUnit : rotateThree ⬝ᵥ rotateThree = 1 :=
    rotateOneTwo_unit planeOneTwo honeTwoUnit honeTwoZero honeTwoThree
  have hrotateOneBound :
      rotateOne ⬝ᵥ (projection *ᵥ rotateOne) <= 1 := by
    simpa [hrotateOneUnit] using
      dotProduct_mulVec_le_self_of_symmetricIdempotent hsymmetric hidempotent rotateOne
  have hrotateTwoBound :
      rotateTwo ⬝ᵥ (projection *ᵥ rotateTwo) <= 1 := by
    simpa [hrotateTwoUnit] using
      dotProduct_mulVec_le_self_of_symmetricIdempotent hsymmetric hidempotent rotateTwo
  have hrotateThreeBound :
      rotateThree ⬝ᵥ (projection *ᵥ rotateThree) <= 1 := by
    simpa [hrotateThreeUnit] using
      dotProduct_mulVec_le_self_of_symmetricIdempotent hsymmetric hidempotent rotateThree
  have hextraNonneg : 0 <= extra ⬝ᵥ (projection *ᵥ extra) :=
    dotProduct_mulVec_nonneg_of_symmetricIdempotent hsymmetric hidempotent extra
  have htraceResolve := congrArg Matrix.trace
    (congrArg (fun matrix => projection * matrix) hresolve)
  have htraceEq :
      Matrix.trace (projection * frame) + Matrix.trace (projection * complement) =
        (2 : Real) * 2 + extra ⬝ᵥ (projection *ᵥ extra) := by
    simpa only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
      Matrix.trace_smul, Matrix.mul_one, htrace, smul_eq_mul,
      trace_mul_atomMatrix] using htraceResolve
  have hcomplementTrace : Matrix.trace (projection * complement) =
      rotateOne ⬝ᵥ (projection *ᵥ rotateOne) +
      rotateTwo ⬝ᵥ (projection *ᵥ rotateTwo) +
      rotateThree ⬝ᵥ (projection *ᵥ rotateThree) := by
    simp only [complement, Matrix.mul_add, Matrix.trace_add,
      trace_mul_atomMatrix]
  change 1 <= Matrix.trace (projection * frame)
  rw [hcomplementTrace] at htraceEq
  linarith


end Gtz

import Gtz.Reduction.TwoVanishedBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! An exact spectral certificate for the four-row support type

    `{1,2}, {0,1,3}, {0,2,3}, {0,4,5}`.

After transposing the scaled tight-row matrix, three of its six unit rows lie
in the `01`, `02`, and `12` coordinate planes of `R^4`, while two more lie on
the fourth axis.  Rotating the three plane rows by ninety degrees completes
their rank-one forms to twice the identity.  Bessel's inequality then forces
trace at least one on every two-dimensional compression of the unscaled frame,
hence at least `1/6` for the stationary assembly.
-/

def rotateZeroOne (vector : Fin 4 -> Real) : Fin 4 -> Real :=
  ![-vector 1, vector 0, 0, 0]

def rotateZeroTwo (vector : Fin 4 -> Real) : Fin 4 -> Real :=
  ![-vector 2, 0, vector 0, 0]

def rotateOneTwo (vector : Fin 4 -> Real) : Fin 4 -> Real :=
  ![0, -vector 2, vector 1, 0]

def fourthAxis : Fin 4 -> Real := ![0, 0, 0, 1]

theorem two_vector_bessel
    (first second probe : Fin 4 -> Real)
    (hfirstUnit : first ⬝ᵥ first = 1)
    (hsecondUnit : second ⬝ᵥ second = 1)
    (horthogonal : first ⬝ᵥ second = 0) :
    (probe ⬝ᵥ first) ^ 2 + (probe ⬝ᵥ second) ^ 2 <= probe ⬝ᵥ probe := by
  let residual :=
    probe - (probe ⬝ᵥ first) • first - (probe ⬝ᵥ second) • second
  have hnonneg := dotProduct_self_nonneg residual
  have hreverse : second ⬝ᵥ first = 0 := by
    rw [dotProduct_comm, horthogonal]
  have hfirstReverse : first ⬝ᵥ probe = probe ⬝ᵥ first := dotProduct_comm _ _
  have hsecondReverse : second ⬝ᵥ probe = probe ⬝ᵥ second := dotProduct_comm _ _
  have hnorm :
      residual ⬝ᵥ residual = probe ⬝ᵥ probe - (probe ⬝ᵥ first) ^ 2 -
        (probe ⬝ᵥ second) ^ 2 := by
    dsimp only [residual]
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, hfirstUnit, hsecondUnit, horthogonal, hreverse,
      hfirstReverse, hsecondReverse, mul_zero, mul_one, sub_zero]
    ring
  rw [hnorm] at hnonneg
  linarith

theorem atomMatrix_add_rotateZeroOne
    (vector : Fin 4 -> Real)
    (hunit : vector ⬝ᵥ vector = 1)
    (hzeroTwo : vector 2 = 0)
    (hzeroThree : vector 3 = 0) :
    atomMatrix vector + atomMatrix (rotateZeroOne vector) =
      Matrix.diagonal ![1, 1, 0, 0] := by
  have hsum : vector 0 ^ 2 + vector 1 ^ 2 = 1 := by
    simp only [dotProduct, Fin.sum_univ_four, hzeroTwo, hzeroThree,
      mul_zero, add_zero] at hunit
    nlinarith
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [atomMatrix, Matrix.vecMulVec_apply, rotateZeroOne, hzeroTwo, hzeroThree] <;>
      nlinarith [hsum]

theorem atomMatrix_add_rotateZeroTwo
    (vector : Fin 4 -> Real)
    (hunit : vector ⬝ᵥ vector = 1)
    (hzeroOne : vector 1 = 0)
    (hzeroThree : vector 3 = 0) :
    atomMatrix vector + atomMatrix (rotateZeroTwo vector) =
      Matrix.diagonal ![1, 0, 1, 0] := by
  have hsum : vector 0 ^ 2 + vector 2 ^ 2 = 1 := by
    simp only [dotProduct, Fin.sum_univ_four, hzeroOne, hzeroThree,
      mul_zero, add_zero] at hunit
    nlinarith
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [atomMatrix, Matrix.vecMulVec_apply, rotateZeroTwo, hzeroOne, hzeroThree] <;>
      nlinarith [hsum]

theorem atomMatrix_add_rotateOneTwo
    (vector : Fin 4 -> Real)
    (hunit : vector ⬝ᵥ vector = 1)
    (hzeroZero : vector 0 = 0)
    (hzeroThree : vector 3 = 0) :
    atomMatrix vector + atomMatrix (rotateOneTwo vector) =
      Matrix.diagonal ![0, 1, 1, 0] := by
  have hsum : vector 1 ^ 2 + vector 2 ^ 2 = 1 := by
    simp only [dotProduct, Fin.sum_univ_four, hzeroZero, hzeroThree,
      mul_zero, zero_add, add_zero] at hunit
    nlinarith
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [atomMatrix, Matrix.vecMulVec_apply, rotateOneTwo, hzeroZero, hzeroThree] <;>
      nlinarith [hsum]

theorem atomMatrix_eq_fourthAxis
    (vector : Fin 4 -> Real)
    (hunit : vector ⬝ᵥ vector = 1)
    (hzeroZero : vector 0 = 0)
    (hzeroOne : vector 1 = 0)
    (hzeroTwo : vector 2 = 0) :
    atomMatrix vector = atomMatrix fourthAxis := by
  have hsquare : vector 3 ^ 2 = 1 := by
    simp only [dotProduct, Fin.sum_univ_four, hzeroZero, hzeroOne, hzeroTwo,
      zero_mul, zero_add] at hunit
    nlinarith
  ext row col
  fin_cases row <;> fin_cases col
  all_goals simp [atomMatrix, Matrix.vecMulVec_apply, fourthAxis, hzeroZero, hzeroOne,
    hzeroTwo]
  all_goals nlinarith [hsquare]

theorem rotateZeroOne_unit
    (vector : Fin 4 -> Real)
    (hunit : vector ⬝ᵥ vector = 1)
    (hzeroTwo : vector 2 = 0)
    (hzeroThree : vector 3 = 0) :
    rotateZeroOne vector ⬝ᵥ rotateZeroOne vector = 1 := by
  simp only [dotProduct, Fin.sum_univ_four, hzeroTwo, hzeroThree,
    mul_zero, add_zero] at hunit
  simp [dotProduct, Fin.sum_univ_four, rotateZeroOne]
  nlinarith

theorem rotateZeroTwo_unit
    (vector : Fin 4 -> Real)
    (hunit : vector ⬝ᵥ vector = 1)
    (hzeroOne : vector 1 = 0)
    (hzeroThree : vector 3 = 0) :
    rotateZeroTwo vector ⬝ᵥ rotateZeroTwo vector = 1 := by
  simp only [dotProduct, Fin.sum_univ_four, hzeroOne, hzeroThree,
    mul_zero, add_zero] at hunit
  simp [dotProduct, Fin.sum_univ_four, rotateZeroTwo]
  nlinarith

theorem rotateOneTwo_unit
    (vector : Fin 4 -> Real)
    (hunit : vector ⬝ᵥ vector = 1)
    (hzeroZero : vector 0 = 0)
    (hzeroThree : vector 3 = 0) :
    rotateOneTwo vector ⬝ᵥ rotateOneTwo vector = 1 := by
  simp only [dotProduct, Fin.sum_univ_four, hzeroZero, hzeroThree,
    zero_add, mul_zero, add_zero] at hunit
  simp [dotProduct, Fin.sum_univ_four, rotateOneTwo]
  nlinarith

/-- The support-type-eight frame has trace at least one on every orthonormal
two-frame.  This is the exact unscaled form of the `1/6` captured-trace floor. -/
theorem typeEight_twoFrame_trace_floor
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
    (first second : Fin 4 -> Real)
    (hfirstUnit : first ⬝ᵥ first = 1)
    (hsecondUnit : second ⬝ᵥ second = 1)
    (horthogonal : first ⬝ᵥ second = 0) :
    1 <=
      first ⬝ᵥ
          ((atomMatrix planeZeroOne + atomMatrix planeZeroTwo + atomMatrix planeOneTwo +
              atomMatrix axisFirst + atomMatrix axisSecond + atomMatrix extra) *ᵥ first) +
        second ⬝ᵥ
          ((atomMatrix planeZeroOne + atomMatrix planeZeroTwo + atomMatrix planeOneTwo +
              atomMatrix axisFirst + atomMatrix axisSecond + atomMatrix extra) *ᵥ second) := by
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
  have hresolve : frame + complement = (2 : Real) • (1 : Matrix (Fin 4) (Fin 4) Real) +
      atomMatrix extra := by
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
  have hfirstResolve := congrArg
    (fun form : Matrix (Fin 4) (Fin 4) Real => first ⬝ᵥ (form *ᵥ first)) hresolve
  have hsecondResolve := congrArg
    (fun form : Matrix (Fin 4) (Fin 4) Real => second ⬝ᵥ (form *ᵥ second)) hresolve
  have hfirstEq :
      first ⬝ᵥ (frame *ᵥ first) + first ⬝ᵥ (complement *ᵥ first) =
        2 + (extra ⬝ᵥ first) ^ 2 := by
    simpa only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, hfirstUnit,
      dotProduct_atomMatrix_mulVec_eq_sq, mul_one] using hfirstResolve
  have hsecondEq :
      second ⬝ᵥ (frame *ᵥ second) + second ⬝ᵥ (complement *ᵥ second) =
        2 + (extra ⬝ᵥ second) ^ 2 := by
    simpa only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, hsecondUnit,
      dotProduct_atomMatrix_mulVec_eq_sq, mul_one] using hsecondResolve
  have hrotateOneUnit : rotateOne ⬝ᵥ rotateOne = 1 :=
    rotateZeroOne_unit planeZeroOne hzeroOneUnit hzeroOneTwo hzeroOneThree
  have hrotateTwoUnit : rotateTwo ⬝ᵥ rotateTwo = 1 :=
    rotateZeroTwo_unit planeZeroTwo hzeroTwoUnit hzeroTwoOne hzeroTwoThree
  have hrotateThreeUnit : rotateThree ⬝ᵥ rotateThree = 1 :=
    rotateOneTwo_unit planeOneTwo honeTwoUnit honeTwoZero honeTwoThree
  have hbesselOne := two_vector_bessel first second rotateOne
    hfirstUnit hsecondUnit horthogonal
  have hbesselTwo := two_vector_bessel first second rotateTwo
    hfirstUnit hsecondUnit horthogonal
  have hbesselThree := two_vector_bessel first second rotateThree
    hfirstUnit hsecondUnit horthogonal
  have hcomplementFirst :
      first ⬝ᵥ (complement *ᵥ first) =
        (rotateOne ⬝ᵥ first) ^ 2 + (rotateTwo ⬝ᵥ first) ^ 2 +
          (rotateThree ⬝ᵥ first) ^ 2 := by
    simp only [complement, Matrix.add_mulVec, dotProduct_add,
      dotProduct_atomMatrix_mulVec_eq_sq]
  have hcomplementSecond :
      second ⬝ᵥ (complement *ᵥ second) =
        (rotateOne ⬝ᵥ second) ^ 2 + (rotateTwo ⬝ᵥ second) ^ 2 +
          (rotateThree ⬝ᵥ second) ^ 2 := by
    simp only [complement, Matrix.add_mulVec, dotProduct_add,
      dotProduct_atomMatrix_mulVec_eq_sq]
  rw [hcomplementFirst] at hfirstEq
  rw [hcomplementSecond] at hsecondEq
  change 1 <= first ⬝ᵥ (frame *ᵥ first) + second ⬝ᵥ (frame *ᵥ second)
  nlinarith [sq_nonneg (extra ⬝ᵥ first), sq_nonneg (extra ⬝ᵥ second),
    hrotateOneUnit, hrotateTwoUnit, hrotateThreeUnit]


end Gtz

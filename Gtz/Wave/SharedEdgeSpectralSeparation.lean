import Gtz.Quantitative.SevenThreeMaxVolume
import Gtz.Quantitative.SevenThreeNoGo
import Gtz.Reduction.CompactnessReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

/-- The trace-complement determinant of two weighted unit rank-one forms in
dimension three. -/
theorem det_traceComplement_two_unit_atomMatrices
    (first second : Fin 3 → ℝ) (firstWeight secondWeight : ℝ)
    (hfirstUnit : first ⬝ᵥ first = 1)
    (hsecondUnit : second ⬝ᵥ second = 1) :
    Matrix.det (((firstWeight + secondWeight) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        - (firstWeight • atomMatrix first + secondWeight • atomMatrix second))
      = (firstWeight + secondWeight) * firstWeight * secondWeight
          * (1 - (first ⬝ᵥ second) ^ 2) := by
  let traceTerm := firstWeight * (first ⬝ᵥ first)
    + secondWeight * (second ⬝ᵥ second)
  have hraw :
      Matrix.det ((traceTerm • (1 : Matrix (Fin 3) (Fin 3) ℝ))
          - (firstWeight • atomMatrix first + secondWeight • atomMatrix second))
        = traceTerm * firstWeight * secondWeight
            * ((first ⬝ᵥ first) * (second ⬝ᵥ second)
              - (first ⬝ᵥ second) ^ 2) := by
    rw [Matrix.det_fin_three]
    simp [traceTerm, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul,
      dotProduct, Fin.sum_univ_three]
    ring
  have htrace : traceTerm = firstWeight + secondWeight := by
    dsimp [traceTerm]
    rw [hfirstUnit, hsecondUnit]
    ring
  rw [← htrace]
  simpa [hfirstUnit, hsecondUnit] using hraw

/-- A unit vector with a nonzero third coordinate cannot be parallel to a unit
vector supported on the first two coordinates.  This is the strict Cauchy
inequality in its elementary two-coordinate form. -/
theorem dotProduct_sq_lt_one_of_unit_of_pairSupport
    (full pair : Fin 3 → ℝ)
    (hfullUnit : full ⬝ᵥ full = 1)
    (hpairUnit : pair ⬝ᵥ pair = 1)
    (hfullThird : full 2 ≠ 0)
    (hpairThird : pair 2 = 0) :
    (full ⬝ᵥ pair) ^ 2 < 1 := by
  simp only [dotProduct, Fin.sum_univ_three] at hfullUnit hpairUnit ⊢
  rw [hpairThird] at hpairUnit ⊢
  simp only [mul_zero, add_zero] at hpairUnit ⊢
  have hfullThirdSq : 0 < full 2 ^ 2 := sq_pos_of_ne_zero hfullThird
  have hlambda : 0 ≤ (full 0 * pair 1 - full 1 * pair 0) ^ 2 := sq_nonneg _
  nlinarith

/-- Coordinate-free version of the strict Cauchy step: it suffices that one
coordinate vanishes on `pair` and not on `full`. -/
theorem dotProduct_sq_lt_one_of_unit_of_missingCoordinate
    (full pair : Fin 3 → ℝ) (missing : Fin 3)
    (hfullUnit : full ⬝ᵥ full = 1)
    (hpairUnit : pair ⬝ᵥ pair = 1)
    (hfullMissing : full missing ≠ 0)
    (hpairMissing : pair missing = 0) :
    (full ⬝ᵥ pair) ^ 2 < 1 := by
  fin_cases missing
  · simp only [dotProduct, Fin.sum_univ_three] at hfullUnit hpairUnit ⊢
    have hpairZero : pair 0 = 0 := by simpa using hpairMissing
    have hfullNe : full 0 ≠ 0 := by simpa using hfullMissing
    rw [hpairZero] at hpairUnit ⊢
    simp only [mul_zero, zero_add] at hpairUnit ⊢
    have hmissingSq : 0 < full 0 ^ 2 := sq_pos_of_ne_zero hfullNe
    have hminor : 0 ≤ (full 1 * pair 2 - full 2 * pair 1) ^ 2 := sq_nonneg _
    nlinarith
  · simp only [dotProduct, Fin.sum_univ_three] at hfullUnit hpairUnit ⊢
    have hpairZero : pair 1 = 0 := by simpa using hpairMissing
    have hfullNe : full 1 ≠ 0 := by simpa using hfullMissing
    rw [hpairZero] at hpairUnit ⊢
    simp only [mul_zero, add_zero] at hpairUnit ⊢
    have hmissingSq : 0 < full 1 ^ 2 := sq_pos_of_ne_zero hfullNe
    have hminor : 0 ≤ (full 0 * pair 2 - full 2 * pair 0) ^ 2 := sq_nonneg _
    nlinarith
  · exact dotProduct_sq_lt_one_of_unit_of_pairSupport full pair hfullUnit hpairUnit
      hfullMissing hpairMissing

/-- The complementary form to a positive combination of two independent unit
rank-one forms is positive definite.  Its three eigenvalues are the two
positive eigenvalues of the rank-two form, exchanged, and their sum; the proof
uses only PSD plus the explicit determinant. -/
theorem posDef_traceComplement_two_unit_atomMatrices_of_pairSupport
    (full pair : Fin 3 → ℝ) (fullWeight pairWeight : ℝ)
    (hfullUnit : full ⬝ᵥ full = 1)
    (hpairUnit : pair ⬝ᵥ pair = 1)
    (hfullThird : full 2 ≠ 0)
    (hpairThird : pair 2 = 0)
    (hfullWeight : 0 < fullWeight)
    (hpairWeight : 0 < pairWeight) :
    (((fullWeight + pairWeight) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        - (fullWeight • atomMatrix full + pairWeight • atomMatrix pair)).PosDef := by
  let assembly : Matrix (Fin 3) (Fin 3) ℝ :=
    fullWeight • atomMatrix full + pairWeight • atomMatrix pair
  have hassemblyPsd : assembly.PosSemidef := by
    exact (posSemidef_atomMatrix full).smul hfullWeight.le |>.add
      ((posSemidef_atomMatrix pair).smul hpairWeight.le)
  have hfullLeverage : leverageOf full = 1 := by
    simpa [leverageOf, dotProduct, pow_two] using hfullUnit
  have hpairLeverage : leverageOf pair = 1 := by
    simpa [leverageOf, dotProduct, pow_two] using hpairUnit
  have htrace : Matrix.trace assembly = fullWeight + pairWeight := by
    dsimp [assembly]
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      trace_atomMatrix, trace_atomMatrix, hfullLeverage, hpairLeverage]
    ring
  have hpsd :
      (((fullWeight + pairWeight) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        - assembly).PosSemidef := by
    rw [← htrace]
    exact posSemidef_trace_smul_one_sub_of_three hassemblyPsd
  refine hpsd.posDef_iff_det_ne_zero.mpr ?_
  rw [show assembly = fullWeight • atomMatrix full
      + pairWeight • atomMatrix pair by rfl,
    det_traceComplement_two_unit_atomMatrices full pair fullWeight pairWeight
      hfullUnit hpairUnit]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (add_pos hfullWeight hpairWeight |>.ne') hfullWeight.ne')
      hpairWeight.ne')
    (sub_ne_zero.mpr (ne_of_gt
      (dotProduct_sq_lt_one_of_unit_of_pairSupport full pair hfullUnit hpairUnit
        hfullThird hpairThird)))

/-- The same spectral gap with an arbitrary missing coordinate. -/
theorem posDef_traceComplement_two_unit_atomMatrices_of_missingCoordinate
    (full pair : Fin 3 → ℝ) (missing : Fin 3)
    (fullWeight pairWeight : ℝ)
    (hfullUnit : full ⬝ᵥ full = 1)
    (hpairUnit : pair ⬝ᵥ pair = 1)
    (hfullMissing : full missing ≠ 0)
    (hpairMissing : pair missing = 0)
    (hfullWeight : 0 < fullWeight)
    (hpairWeight : 0 < pairWeight) :
    (((fullWeight + pairWeight) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        - (fullWeight • atomMatrix full + pairWeight • atomMatrix pair)).PosDef := by
  let assembly : Matrix (Fin 3) (Fin 3) ℝ :=
    fullWeight • atomMatrix full + pairWeight • atomMatrix pair
  have hassemblyPsd : assembly.PosSemidef := by
    exact (posSemidef_atomMatrix full).smul hfullWeight.le |>.add
      ((posSemidef_atomMatrix pair).smul hpairWeight.le)
  have hfullLeverage : leverageOf full = 1 := by
    simpa [leverageOf, dotProduct, pow_two] using hfullUnit
  have hpairLeverage : leverageOf pair = 1 := by
    simpa [leverageOf, dotProduct, pow_two] using hpairUnit
  have htrace : Matrix.trace assembly = fullWeight + pairWeight := by
    dsimp [assembly]
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      trace_atomMatrix, trace_atomMatrix, hfullLeverage, hpairLeverage]
    ring
  have hpsd :
      (((fullWeight + pairWeight) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        - assembly).PosSemidef := by
    rw [← htrace]
    exact posSemidef_trace_smul_one_sub_of_three hassemblyPsd
  refine hpsd.posDef_iff_det_ne_zero.mpr ?_
  rw [show assembly = fullWeight • atomMatrix full
      + pairWeight • atomMatrix pair by rfl,
    det_traceComplement_two_unit_atomMatrices full pair fullWeight pairWeight
      hfullUnit hpairUnit]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (add_pos hfullWeight hpairWeight |>.ne') hfullWeight.ne')
      hpairWeight.ne')
    (sub_ne_zero.mpr (ne_of_gt
      (dotProduct_sq_lt_one_of_unit_of_missingCoordinate full pair missing
        hfullUnit hpairUnit hfullMissing hpairMissing)))

/-- Two independent positive rows already make the trace-complement strict;
an additional nonnegative unit row contributes only a PSD summand.  This is the
spectral collapse behind the all-positive four-active branch. -/
theorem posDef_half_one_sub_three_unit_atomMatrices_of_missingCoordinate
    (full pair extra : Fin 3 → ℝ) (missing : Fin 3)
    (fullWeight pairWeight extraWeight : ℝ)
    (hfullUnit : full ⬝ᵥ full = 1)
    (hpairUnit : pair ⬝ᵥ pair = 1)
    (hextraUnit : extra ⬝ᵥ extra = 1)
    (hfullMissing : full missing ≠ 0)
    (hpairMissing : pair missing = 0)
    (hfullWeight : 0 < fullWeight)
    (hpairWeight : 0 < pairWeight)
    (hextraWeight : 0 ≤ extraWeight)
    (hweightSum : fullWeight + pairWeight + extraWeight = 1 / 2) :
    ((1 / 2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
      (fullWeight • atomMatrix full + pairWeight • atomMatrix pair
        + extraWeight • atomMatrix extra)).PosDef := by
  have hbase :
      ((fullWeight + pairWeight) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
        (fullWeight • atomMatrix full + pairWeight • atomMatrix pair)).PosDef :=
    posDef_traceComplement_two_unit_atomMatrices_of_missingCoordinate
      full pair missing fullWeight pairWeight hfullUnit hpairUnit hfullMissing
        hpairMissing hfullWeight hpairWeight
  have hextraLeverage : leverageOf extra = 1 := by
    simpa only [leverageOf, dotProduct, pow_two] using hextraUnit
  have hextraCap :
      ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix extra).PosSemidef := by
    apply posSemidef_smul_one_sub_atomMatrix_of_leverage_le
    rw [hextraLeverage]
  have hextraPsd :
      (extraWeight • ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - atomMatrix extra)).PosSemidef :=
    hextraCap.smul hextraWeight
  have hdecompose :
      (1 / 2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
          (fullWeight • atomMatrix full + pairWeight • atomMatrix pair
            + extraWeight • atomMatrix extra) =
        ((fullWeight + pairWeight) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
          (fullWeight • atomMatrix full + pairWeight • atomMatrix pair))
          + extraWeight • ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
            - atomMatrix extra) := by
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
    have hentry := congrArg (fun scalar : ℝ => scalar *
      (1 : Matrix (Fin 3) (Fin 3) ℝ) rowIndex colIndex) hweightSum
    ring_nf at hentry ⊢
    linarith
  rw [hdecompose]
  exact hbase.add_posSemidef hextraPsd

/-- A positive-definite matrix has trivial kernel as a linear operator. -/
theorem mulVec_eq_zero_of_posDef_three
    {form : Matrix (Fin 3) (Fin 3) ℝ} {vector : Fin 3 → ℝ}
    (hform : form.PosDef) (hzero : Matrix.mulVec form vector = 0) :
    vector = 0 := by
  apply Matrix.mulVec_injective_of_isUnit hform.isUnit
  simpa using hzero

/-- Spectral separation for an intertwining block.  If `assembly` has no
eigenvalue at its trace and the right block is the trace-scaled projector onto
`vector`, then the cross block kills `vector`. -/
theorem cross_mulVec_eq_zero_of_traceComplement_posDef
    {assembly cross : Matrix (Fin 3) (Fin 3) ℝ} {vector : Fin 3 → ℝ}
    {traceTerm : ℝ}
    (hcomplement :
      (traceTerm • (1 : Matrix (Fin 3) (Fin 3) ℝ) - assembly).PosDef)
    (hunit : vector ⬝ᵥ vector = 1)
    (hintertwines :
      assembly * cross = cross * (traceTerm • atomMatrix vector)) :
    Matrix.mulVec cross vector = 0 := by
  have heigen :
      Matrix.mulVec assembly (Matrix.mulVec cross vector) =
        traceTerm • Matrix.mulVec cross vector := by
    calc
      Matrix.mulVec assembly (Matrix.mulVec cross vector) =
          Matrix.mulVec (assembly * cross) vector := by
            rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (cross * (traceTerm • atomMatrix vector)) vector := by
            rw [hintertwines]
      _ = Matrix.mulVec cross
          (Matrix.mulVec (traceTerm • atomMatrix vector) vector) := by
            rw [Matrix.mulVec_mulVec]
      _ = traceTerm • Matrix.mulVec cross vector := by
            rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_dot_smul, hunit,
              one_smul, Matrix.mulVec_smul]
  apply mulVec_eq_zero_of_posDef_three hcomplement
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heigen, sub_self]

/-- Once the complementary tight vector is killed by the cross block, the
intertwining equation says that the two-atom block kills the whole cross
matrix. -/
theorem twoAtomAssembly_mul_cross_eq_zero_of_intertwines
    {assembly cross : Matrix (Fin 3) (Fin 3) ℝ} {vector : Fin 3 → ℝ}
    {traceTerm : ℝ}
    (hintertwines :
      assembly * cross = cross * (traceTerm • atomMatrix vector))
    (hcrossVector : Matrix.mulVec cross vector = 0) :
    assembly * cross = 0 := by
  rw [hintertwines, Matrix.mul_smul, atomMatrix, matrix_mul_vecMulVec,
    hcrossVector, Matrix.zero_vecMulVec, smul_zero]

/-- If a positive two-atom assembly kills a cross block, then the transpose
cross block kills the full-support atom.  Reading the coordinate missing from
the pair isolates its coefficient without any inverse. -/
theorem transpose_cross_mulVec_full_eq_zero_of_twoAtomAssembly_mul_cross_eq_zero
    (full pair : Fin 3 → ℝ) (cross : Matrix (Fin 3) (Fin 3) ℝ)
    (fullWeight pairWeight : ℝ)
    (hfullThird : full 2 ≠ 0) (hpairThird : pair 2 = 0)
    (hfullWeight : 0 < fullWeight)
    (hzero :
      (fullWeight • atomMatrix full + pairWeight • atomMatrix pair) * cross = 0) :
    Matrix.mulVec cross.transpose full = 0 := by
  funext columnIndex
  have hproduct :
      (fullWeight * full 2) * (∑ rowIndex, full rowIndex * cross rowIndex columnIndex) = 0 := by
    calc
      (fullWeight * full 2) *
          (∑ rowIndex, full rowIndex * cross rowIndex columnIndex) =
          ((fullWeight • atomMatrix full + pairWeight • atomMatrix pair) * cross)
            2 columnIndex := by
              simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, atomMatrix,
                Matrix.vecMulVec_apply, hpairThird, Finset.mul_sum]
              ring
      _ = 0 := by rw [hzero]; rfl
  have hdot : (∑ rowIndex, full rowIndex * cross rowIndex columnIndex) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left
      (mul_ne_zero hfullWeight.ne' hfullThird)
  change (∑ rowIndex, cross rowIndex columnIndex * full rowIndex) = 0
  simpa [mul_comm] using hdot

/-- Arbitrary-missing-coordinate version of the transpose cross-block kill. -/
theorem transpose_cross_mulVec_full_eq_zero_of_twoAtomAssembly_missingCoordinate
    (full pair : Fin 3 → ℝ) (missing : Fin 3)
    (cross : Matrix (Fin 3) (Fin 3) ℝ)
    (fullWeight pairWeight : ℝ)
    (hfullMissing : full missing ≠ 0) (hpairMissing : pair missing = 0)
    (hfullWeight : 0 < fullWeight)
    (hzero :
      (fullWeight • atomMatrix full + pairWeight • atomMatrix pair) * cross = 0) :
    Matrix.mulVec cross.transpose full = 0 := by
  funext columnIndex
  have hproduct :
      (fullWeight * full missing) *
          (∑ rowIndex, full rowIndex * cross rowIndex columnIndex) = 0 := by
    calc
      (fullWeight * full missing) *
          (∑ rowIndex, full rowIndex * cross rowIndex columnIndex) =
          ((fullWeight • atomMatrix full + pairWeight • atomMatrix pair) * cross)
            missing columnIndex := by
              simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, atomMatrix,
                Matrix.vecMulVec_apply, hpairMissing, Finset.mul_sum]
              ring
      _ = 0 := by rw [hzero]; rfl
  have hdot : (∑ rowIndex, full rowIndex * cross rowIndex columnIndex) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left
      (mul_ne_zero hfullWeight.ne' hfullMissing)
  change (∑ rowIndex, cross rowIndex columnIndex * full rowIndex) = 0
  simpa [mul_comm] using hdot

/-- A positive rank-one summand of a PSD assembly also annihilates every vector
killed by the whole assembly.  Applied columnwise, this makes the transpose
cross block kill the full row without coordinate elimination. -/
theorem transpose_cross_mulVec_full_eq_zero_of_threeAtomAssembly_mul_cross_eq_zero
    (full pair extra : Fin 3 → ℝ) (cross : Matrix (Fin 3) (Fin 3) ℝ)
    (fullWeight pairWeight extraWeight : ℝ)
    (hfullWeight : 0 < fullWeight)
    (hpairWeight : 0 ≤ pairWeight)
    (hextraWeight : 0 ≤ extraWeight)
    (hzero :
      (fullWeight • atomMatrix full + pairWeight • atomMatrix pair
        + extraWeight • atomMatrix extra) * cross = 0) :
    Matrix.mulVec cross.transpose full = 0 := by
  funext columnIndex
  let column : Fin 3 → ℝ := fun rowIndex => cross rowIndex columnIndex
  let remainder : Matrix (Fin 3) (Fin 3) ℝ :=
    pairWeight • atomMatrix pair + extraWeight • atomMatrix extra
  have hremainderPsd : remainder.PosSemidef := by
    exact ((posSemidef_atomMatrix pair).smul hpairWeight).add
      ((posSemidef_atomMatrix extra).smul hextraWeight)
  have hcolumnZero :
      Matrix.mulVec
        (fullWeight • atomMatrix full + pairWeight • atomMatrix pair
          + extraWeight • atomMatrix extra) column = 0 := by
    funext rowIndex
    have hentry := congrFun (congrFun hzero rowIndex) columnIndex
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, column,
      Matrix.zero_apply, Pi.zero_apply] using hentry
  have htotal :
      column ⬝ᵥ Matrix.mulVec
        (fullWeight • atomMatrix full + remainder) column = 0 := by
    have hmatrix :
        fullWeight • atomMatrix full + remainder =
          fullWeight • atomMatrix full + pairWeight • atomMatrix pair
            + extraWeight • atomMatrix extra := by
      dsimp only [remainder]
      exact (add_assoc _ _ _).symm
    rw [hmatrix, hcolumnZero, dotProduct_zero]
  have hremainderNonneg :
      0 ≤ column ⬝ᵥ Matrix.mulVec remainder column :=
    (Matrix.posSemidef_iff_dotProduct_mulVec.mp hremainderPsd).2 column
  have hfullTerm :
      column ⬝ᵥ Matrix.mulVec (atomMatrix full) column =
        (full ⬝ᵥ column) ^ 2 := by
    rw [atomMatrix_mulVec_eq_dot_smul, dotProduct_smul, smul_eq_mul,
      dotProduct_comm column full, pow_two]
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, hfullTerm] at htotal
  have hdot : full ⬝ᵥ column = 0 := by
    have hsquare : (full ⬝ᵥ column) ^ 2 = 0 := by
      nlinarith
    exact sq_eq_zero_iff.mp hsquare
  change column ⬝ᵥ full = 0
  rw [dotProduct_comm, hdot]

/-- **SHARED-EDGE SPECTRAL SEPARATION.**  The commuting off-diagonal block
annihilates both the complementary tight vector and, after transposition, the
full tight vector on the shared-edge side. -/
theorem sharedEdge_cross_kills_complement_and_full
    (full pair complement : Fin 3 → ℝ)
    (cross : Matrix (Fin 3) (Fin 3) ℝ)
    (fullWeight pairWeight : ℝ)
    (hfullUnit : full ⬝ᵥ full = 1)
    (hpairUnit : pair ⬝ᵥ pair = 1)
    (hcomplementUnit : complement ⬝ᵥ complement = 1)
    (hfullThird : full 2 ≠ 0) (hpairThird : pair 2 = 0)
    (hfullWeight : 0 < fullWeight) (hpairWeight : 0 < pairWeight)
    (hweightSum : fullWeight + pairWeight = 1 / 2)
    (hintertwines :
      (fullWeight • atomMatrix full + pairWeight • atomMatrix pair) * cross =
        cross * ((1 / 2 : ℝ) • atomMatrix complement)) :
    Matrix.mulVec cross complement = 0 ∧
      Matrix.mulVec cross.transpose full = 0 := by
  have hcomplement :
      ((1 / 2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
        (fullWeight • atomMatrix full + pairWeight • atomMatrix pair)).PosDef := by
    rw [← hweightSum]
    exact posDef_traceComplement_two_unit_atomMatrices_of_pairSupport
      full pair fullWeight pairWeight hfullUnit hpairUnit hfullThird hpairThird
        hfullWeight hpairWeight
  have hcrossComplement : Matrix.mulVec cross complement = 0 := by
    exact cross_mulVec_eq_zero_of_traceComplement_posDef hcomplement
      hcomplementUnit hintertwines
  have hassemblyCross :
      (fullWeight • atomMatrix full + pairWeight • atomMatrix pair) * cross = 0 := by
    exact twoAtomAssembly_mul_cross_eq_zero_of_intertwines hintertwines hcrossComplement
  exact ⟨hcrossComplement,
    transpose_cross_mulVec_full_eq_zero_of_twoAtomAssembly_mul_cross_eq_zero
      full pair cross fullWeight pairWeight hfullThird hpairThird hfullWeight
        hassemblyCross⟩

/-- Coordinate-independent shared-edge spectral separation. -/
theorem sharedEdge_cross_kills_complement_and_full_missingCoordinate
    (full pair complement : Fin 3 → ℝ) (missing : Fin 3)
    (cross : Matrix (Fin 3) (Fin 3) ℝ)
    (fullWeight pairWeight : ℝ)
    (hfullUnit : full ⬝ᵥ full = 1)
    (hpairUnit : pair ⬝ᵥ pair = 1)
    (hcomplementUnit : complement ⬝ᵥ complement = 1)
    (hfullMissing : full missing ≠ 0) (hpairMissing : pair missing = 0)
    (hfullWeight : 0 < fullWeight) (hpairWeight : 0 < pairWeight)
    (hweightSum : fullWeight + pairWeight = 1 / 2)
    (hintertwines :
      (fullWeight • atomMatrix full + pairWeight • atomMatrix pair) * cross =
        cross * ((1 / 2 : ℝ) • atomMatrix complement)) :
    Matrix.mulVec cross complement = 0 ∧
      Matrix.mulVec cross.transpose full = 0 := by
  have hcomplement :
      ((1 / 2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
        (fullWeight • atomMatrix full + pairWeight • atomMatrix pair)).PosDef := by
    rw [← hweightSum]
    exact posDef_traceComplement_two_unit_atomMatrices_of_missingCoordinate
      full pair missing fullWeight pairWeight hfullUnit hpairUnit hfullMissing
        hpairMissing hfullWeight hpairWeight
  have hcrossComplement : Matrix.mulVec cross complement = 0 := by
    exact cross_mulVec_eq_zero_of_traceComplement_posDef hcomplement
      hcomplementUnit hintertwines
  have hassemblyCross :
      (fullWeight • atomMatrix full + pairWeight • atomMatrix pair) * cross = 0 := by
    exact twoAtomAssembly_mul_cross_eq_zero_of_intertwines hintertwines hcrossComplement
  exact ⟨hcrossComplement,
    transpose_cross_mulVec_full_eq_zero_of_twoAtomAssembly_missingCoordinate
      full pair missing cross fullWeight pairWeight hfullMissing hpairMissing
        hfullWeight hassemblyCross⟩

/-- Three-row version of spectral separation.  Two independent positive rows
make the trace-complement strict; an arbitrary third nonnegative row cannot
destroy it. -/
theorem threeAtom_cross_kills_complement_and_full_missingCoordinate
    (full pair extra complement : Fin 3 → ℝ) (missing : Fin 3)
    (cross : Matrix (Fin 3) (Fin 3) ℝ)
    (fullWeight pairWeight extraWeight : ℝ)
    (hfullUnit : full ⬝ᵥ full = 1)
    (hpairUnit : pair ⬝ᵥ pair = 1)
    (hextraUnit : extra ⬝ᵥ extra = 1)
    (hcomplementUnit : complement ⬝ᵥ complement = 1)
    (hfullMissing : full missing ≠ 0) (hpairMissing : pair missing = 0)
    (hfullWeight : 0 < fullWeight) (hpairWeight : 0 < pairWeight)
    (hextraWeight : 0 ≤ extraWeight)
    (hweightSum : fullWeight + pairWeight + extraWeight = 1 / 2)
    (hintertwines :
      (fullWeight • atomMatrix full + pairWeight • atomMatrix pair
        + extraWeight • atomMatrix extra) * cross =
        cross * ((1 / 2 : ℝ) • atomMatrix complement)) :
    Matrix.mulVec cross complement = 0 ∧
      Matrix.mulVec cross.transpose full = 0 := by
  have hcomplement :=
    posDef_half_one_sub_three_unit_atomMatrices_of_missingCoordinate
      full pair extra missing fullWeight pairWeight extraWeight hfullUnit hpairUnit
        hextraUnit hfullMissing hpairMissing hfullWeight hpairWeight hextraWeight
        hweightSum
  have hcrossComplement : Matrix.mulVec cross complement = 0 :=
    cross_mulVec_eq_zero_of_traceComplement_posDef hcomplement
      hcomplementUnit hintertwines
  have hassemblyCross :
      (fullWeight • atomMatrix full + pairWeight • atomMatrix pair
        + extraWeight • atomMatrix extra) * cross = 0 :=
    twoAtomAssembly_mul_cross_eq_zero_of_intertwines hintertwines hcrossComplement
  exact ⟨hcrossComplement,
    transpose_cross_mulVec_full_eq_zero_of_threeAtomAssembly_mul_cross_eq_zero
      full pair extra cross fullWeight pairWeight extraWeight hfullWeight
        hpairWeight.le hextraWeight hassemblyCross⟩


end Gtz

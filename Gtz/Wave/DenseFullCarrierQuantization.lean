import Gtz.Wave.CarriedRowReading
import Gtz.Wave.SupportTwoRayleighKill
import Gtz.Wave.SharedPrivateCertificateReduction
import Gtz.Wave.BothParallelKernelRigidity
import Gtz.Wave.ConjugationTraceTransfer
import Gtz.Wave.RankFiveDenseStructure
import Gtz.Wave.RankSixClosureSupply

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The dense full-carrier quantization — the heavy-atom eigenrow laws

An atom that every basis slot carries makes its coordinate row a left
eigenrow of the WHOLE coefficient matrix.  Idempotency then quantizes
the shifted weight: the square law `d * d = d` with the capture floor
and the weight window forces `d = 0`.  The zero shifted weight collapses
the captured column, and the basis transpose annihilates the projected
axis.  Two endings follow.

At rank six the basis matrix carries a two-sided inverse, thus the
projected axis dies outright and the all-heavy floor refuses the zero
chart diagonal: **no atom sits in all six supports.**  The census
corollary caps every rank-six multiplicity at five.

At rank five the projected axis is a fixed vector of the chart outside
the basis span.  The extension calculus adjoins it as a sixth column,
and the kernel-free conjugation reads the chart trace as the coefficient
trace plus one.  The chart trace is three, thus **a full-carrier atom
pins the coefficient trace at two.**  The trace-three side of the frame
disjunction refuses every multiplicity-five atom, which kills the heavy
profile of the dense census at half of the trace disjunction.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.eigenvalue_idempotent_of_left_row` — **THE EIGENROW SQUARE.**
* `Gtz.full_carrier_diagonal_zero` — **THE QUANTIZATION.**  A
  full-carrier atom has a zero shifted weight.
* `Gtz.extendedBasisColumns`, `Gtz.extendedCoefficient` with the
  representation, kernel, and trace laws — the extension calculus.
* `Gtz.RankSixFrame.false_of_full_carrier_atom` — **THE RANK-SIX
  FULL-CARRIER KILL.**
* `Gtz.RankSixFrame.basisSupportMultiplicity_le_five` — the census cap.
* `Gtz.RankFiveFrame.trace_eq_two_of_full_carrier_atom` — **THE TRACE
  PIN.**
* `Gtz.RankFiveFrame.trace_eq_two_of_multiplicity_five` — the census
  form of the pin.

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds.  The
eigenrow square and the extension calculus are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the eigenrow square -/

/-- **THE EIGENROW SQUARE.**  A row that contracts every column of an
idempotent matrix to `d` times itself satisfies `d * d = d`, when some
row coordinate is nonzero. -/
theorem eigenvalue_idempotent_of_left_row {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hidem : M * M = M)
    {row : Fin n → ℝ} {d : ℝ}
    (hrow : ∀ slotIndex : Fin n,
      ∑ columnIndex : Fin n, row columnIndex * M columnIndex slotIndex
        = d * row slotIndex)
    {witnessIndex : Fin n} (hne : row witnessIndex ≠ 0) :
    d * d = d := by
  have hsquare : ∑ columnIndex : Fin n,
      row columnIndex * (M * M) columnIndex witnessIndex
      = d * (d * row witnessIndex) := by
    calc ∑ columnIndex : Fin n,
        row columnIndex * (M * M) columnIndex witnessIndex
        = ∑ columnIndex : Fin n, ∑ middleIndex : Fin n,
            row columnIndex
              * (M columnIndex middleIndex * M middleIndex witnessIndex) := by
          refine Finset.sum_congr rfl fun columnIndex _ => ?_
          rw [Matrix.mul_apply, Finset.mul_sum]
      _ = ∑ middleIndex : Fin n, (∑ columnIndex : Fin n,
            row columnIndex * M columnIndex middleIndex)
              * M middleIndex witnessIndex := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun middleIndex _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun columnIndex _ => ?_
          ring
      _ = ∑ middleIndex : Fin n,
            (d * row middleIndex) * M middleIndex witnessIndex := by
          refine Finset.sum_congr rfl fun middleIndex _ => ?_
          rw [hrow middleIndex]
      _ = d * ∑ middleIndex : Fin n,
            row middleIndex * M middleIndex witnessIndex := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun middleIndex _ => ?_
          ring
      _ = d * (d * row witnessIndex) := by rw [hrow witnessIndex]
  rw [hidem, hrow witnessIndex] at hsquare
  have hfactor : (d * d - d) * row witnessIndex = 0 := by
    linear_combination -hsquare
  rcases mul_eq_zero.mp hfactor with hcase | hcase
  · linarith
  · exact absurd hcase hne

/-! ## Layer 2 — the quantization of the shifted weight -/

/-- **THE QUANTIZATION.**  At an atom that every basis slot carries, the
shifted weight is an eigenvalue of the idempotent coefficient matrix.
The capture floor and the weight window force the zero branch. -/
theorem full_carrier_diagonal_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hidem : M * M = M)
    (hmemAll : ∀ columnIndex, basisLabel columnIndex ∈ activeSet)
    (hvalueNeg : value < 0)
    {atomIndex : Fin size} (witnessSlot : Fin basisCount)
    (hcarrier : ∀ columnIndex,
      atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex)) :
    value + weight atomIndex = 0 := by
  have hblock : ∀ columnIndex,
      atomIndex ∈ activeSubset (basisLabel columnIndex) := by
    intro columnIndex
    by_contra hout
    exact mem_datumTightSupport.mp (hcarrier columnIndex)
      (hdata.tightDir_support _ (hmemAll columnIndex) atomIndex hout)
  have hrow : ∀ slotIndex : Fin basisCount,
      ∑ columnIndex : Fin basisCount,
        tightDir (basisLabel columnIndex) atomIndex * M columnIndex slotIndex
      = (value + weight atomIndex)
        * tightDir (basisLabel slotIndex) atomIndex :=
    fun slotIndex => carried_row_reading hdata basisLabel hrepresentation
      (hmemAll slotIndex) (hblock slotIndex)
  have hquant := eigenvalue_idempotent_of_left_row hidem hrow
    (mem_datumTightSupport.mp (hcarrier witnessSlot))
  have hfloor := capture_diagonal_nonneg_of_isChartStationaryData hdata
    atomIndex
  have hupper : weight atomIndex ≤ 1 := by
    have hsum := hdata.weight_sum_one
    have hsingle := Finset.single_le_sum (f := weight)
      (fun otherAtom _ => (hdata.weight_pos otherAtom).le)
      (Finset.mem_univ atomIndex)
    linarith
  have hsplit : (value + weight atomIndex)
      * ((value + weight atomIndex) - 1) = 0 := by
    linear_combination hquant
  rcases mul_eq_zero.mp hsplit with hcase | hcase
  · exact hcase
  · exfalso
    linarith

/-! ## Layer 3 — the rank-six full-carrier kill -/

/-- **THE RANK-SIX FULL-CARRIER KILL.**  An atom in all six supports is
impossible: the quantization zeroes the shifted weight, the two-sided
inverse kills the projected axis, and the all-heavy floor refuses the
zero chart diagonal. -/
theorem RankSixFrame.false_of_full_carrier_atom {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {atomIndex : Fin 6}
    (hcarrier : ∀ columnIndex : Fin 6,
      atomIndex ∈ datumTightSupport frame.tightDir
        (frame.basisLabel columnIndex)) :
    False := by
  have hzero := full_carrier_diagonal_zero frame.hdata frame.basisLabel
    frame.hrepresentation frame.hidempotent frame.hmemAll frame.hvalueNeg
    (0 : Fin 6) hcarrier
  have hann := assembly_mulVec_projection_single_of_diagonal_zero frame.hdata
    hzero
  have hBt := basisTranspose_zero_of_assembly_mulVec_zero frame.basisLabel
    frame.hleft frame.hHform frame.hker hann
  have hone : frame.leftInvᵀ
      * (tightBasisColumns frame.tightDir frame.basisLabel)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, frame.hright, Matrix.transpose_one]
  have hx : (chartPointOfDesign crux.design).chart
      *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) = 0 := by
    have hlift := congrArg (fun ambientVec => frame.leftInvᵀ *ᵥ ambientVec) hBt
    simp only [Matrix.mulVec_zero] at hlift
    rw [Matrix.mulVec_mulVec, hone, Matrix.one_mulVec] at hlift
    exact hlift
  have hdiag := single_dotProduct_mulVec_single
    ((chartPointOfDesign crux.design).chart) atomIndex
  rw [hx, dotProduct_zero] at hdiag
  have hfloor := crux.gap_diagonal_pos_of_allHeavy atomIndex
  have hgap : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomIndex atomIndex
      = (chartPointOfDesign crux.design).chart atomIndex atomIndex
        - (chartPointOfDesign crux.design).weight atomIndex := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
  rw [hgap, ← hdiag] at hfloor
  linarith [frame.hdata.weight_pos atomIndex]

/-- **THE RANK-SIX MULTIPLICITY CAP.**  Every atom of a rank-six frame
sits in at most five basis supports. -/
theorem RankSixFrame.basisSupportMultiplicity_le_five {crux : SixThreeCrux}
    (frame : RankSixFrame crux) (atomIndex : Fin 6) :
    basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
      ≤ 5 := by
  classical
  by_contra hgt
  have hle : basisSupportMultiplicity frame.tightDir frame.basisLabel
      atomIndex ≤ 6 := by
    rw [basisSupportMultiplicity]
    have hcap := Finset.card_filter_le (Finset.univ : Finset (Fin 6))
      (fun columnIndex => atomIndex ∈ datumTightSupport frame.tightDir
        (frame.basisLabel columnIndex))
    simpa using hcap
  have hcard : (Finset.univ.filter fun columnIndex =>
      atomIndex ∈ datumTightSupport frame.tightDir
        (frame.basisLabel columnIndex)).card = 6 := by
    rw [basisSupportMultiplicity] at hgt hle
    omega
  have huniv := Finset.eq_univ_of_card _
    (by rw [hcard, Fintype.card_fin])
  refine frame.false_of_full_carrier_atom (atomIndex := atomIndex)
    fun columnIndex => ?_
  have hmem : columnIndex ∈ Finset.univ.filter fun otherColumn =>
      atomIndex ∈ datumTightSupport frame.tightDir
        (frame.basisLabel otherColumn) := by
    rw [huniv]
    exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hmem).2

/-! ## Layer 4 — the extension calculus -/

/-- The basis columns with one more column adjoined at the last slot. -/
noncomputable def extendedBasisColumns (B : Matrix (Fin 6) (Fin 5) ℝ)
    (extraColumn : Fin 6 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun rowIndex =>
    Fin.snoc (fun columnIndex : Fin 5 => B rowIndex columnIndex)
      (extraColumn rowIndex)

/-- The coefficient matrix with a unit last diagonal slot adjoined. -/
noncomputable def extendedCoefficient (M : Matrix (Fin 5) (Fin 5) ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of (Fin.snoc
    (fun rowIndex : Fin 5 =>
      Fin.snoc (fun columnIndex : Fin 5 => M rowIndex columnIndex) 0)
    (Fin.snoc (fun _ : Fin 5 => (0 : ℝ)) 1))

theorem extendedBasisColumns_castSucc (B : Matrix (Fin 6) (Fin 5) ℝ)
    (extraColumn : Fin 6 → ℝ) (rowIndex : Fin 6) (columnIndex : Fin 5) :
    extendedBasisColumns B extraColumn rowIndex columnIndex.castSucc
      = B rowIndex columnIndex := by
  simp only [extendedBasisColumns, Matrix.of_apply, Fin.snoc_castSucc]

theorem extendedBasisColumns_last (B : Matrix (Fin 6) (Fin 5) ℝ)
    (extraColumn : Fin 6 → ℝ) (rowIndex : Fin 6) :
    extendedBasisColumns B extraColumn rowIndex (Fin.last 5)
      = extraColumn rowIndex := by
  simp only [extendedBasisColumns, Matrix.of_apply, Fin.snoc_last]

theorem extendedCoefficient_castSucc_castSucc (M : Matrix (Fin 5) (Fin 5) ℝ)
    (rowIndex columnIndex : Fin 5) :
    extendedCoefficient M rowIndex.castSucc columnIndex.castSucc
      = M rowIndex columnIndex := by
  simp only [extendedCoefficient, Matrix.of_apply, Fin.snoc_castSucc]

theorem extendedCoefficient_castSucc_last (M : Matrix (Fin 5) (Fin 5) ℝ)
    (rowIndex : Fin 5) :
    extendedCoefficient M rowIndex.castSucc (Fin.last 5) = 0 := by
  simp only [extendedCoefficient, Matrix.of_apply, Fin.snoc_castSucc,
    Fin.snoc_last]

theorem extendedCoefficient_last_castSucc (M : Matrix (Fin 5) (Fin 5) ℝ)
    (columnIndex : Fin 5) :
    extendedCoefficient M (Fin.last 5) columnIndex.castSucc = 0 := by
  simp only [extendedCoefficient, Matrix.of_apply, Fin.snoc_last,
    Fin.snoc_castSucc]

theorem extendedCoefficient_last_last (M : Matrix (Fin 5) (Fin 5) ℝ) :
    extendedCoefficient M (Fin.last 5) (Fin.last 5) = 1 := by
  simp only [extendedCoefficient, Matrix.of_apply, Fin.snoc_last]

/-- **THE EXTENDED REPRESENTATION.**  A fixed vector of the projection
extends the representation law to the adjoined column. -/
theorem extended_representation {P : Matrix (Fin 6) (Fin 6) ℝ}
    {B : Matrix (Fin 6) (Fin 5) ℝ} {M : Matrix (Fin 5) (Fin 5) ℝ}
    {extraColumn : Fin 6 → ℝ}
    (hrep : P * B = B * M) (hfix : P *ᵥ extraColumn = extraColumn) :
    P * extendedBasisColumns B extraColumn
      = extendedBasisColumns B extraColumn * extendedCoefficient M := by
  ext rowIndex columnIndex
  refine Fin.lastCases ?_ ?_ columnIndex
  · rw [Matrix.mul_apply, Matrix.mul_apply]
    calc ∑ innerIndex : Fin 6, P rowIndex innerIndex
        * extendedBasisColumns B extraColumn innerIndex (Fin.last 5)
        = ∑ innerIndex : Fin 6,
            P rowIndex innerIndex * extraColumn innerIndex := by
          refine Finset.sum_congr rfl fun innerIndex _ => ?_
          rw [extendedBasisColumns_last]
      _ = (P *ᵥ extraColumn) rowIndex := rfl
      _ = extraColumn rowIndex := by rw [hfix]
      _ = ∑ middleIndex : Fin 6,
            extendedBasisColumns B extraColumn rowIndex middleIndex
              * extendedCoefficient M middleIndex (Fin.last 5) := by
          rw [Fin.sum_univ_castSucc]
          have hbulk : ∑ middleIndex : Fin 5,
              extendedBasisColumns B extraColumn rowIndex
                  middleIndex.castSucc
                * extendedCoefficient M middleIndex.castSucc (Fin.last 5)
              = 0 := by
            refine Finset.sum_eq_zero fun middleIndex _ => ?_
            rw [extendedCoefficient_castSucc_last, mul_zero]
          rw [hbulk, extendedBasisColumns_last,
            extendedCoefficient_last_last, mul_one, zero_add]
  · intro columnIndex
    rw [Matrix.mul_apply, Matrix.mul_apply]
    calc ∑ innerIndex : Fin 6, P rowIndex innerIndex
        * extendedBasisColumns B extraColumn innerIndex
          columnIndex.castSucc
        = ∑ innerIndex : Fin 6,
            P rowIndex innerIndex * B innerIndex columnIndex := by
          refine Finset.sum_congr rfl fun innerIndex _ => ?_
          rw [extendedBasisColumns_castSucc]
      _ = (P * B) rowIndex columnIndex := by rw [Matrix.mul_apply]
      _ = (B * M) rowIndex columnIndex := by rw [hrep]
      _ = ∑ middleIndex : Fin 5,
            B rowIndex middleIndex * M middleIndex columnIndex := by
          rw [Matrix.mul_apply]
      _ = ∑ middleIndex : Fin 6,
            extendedBasisColumns B extraColumn rowIndex middleIndex
              * extendedCoefficient M middleIndex columnIndex.castSucc := by
          conv_rhs => rw [Fin.sum_univ_castSucc]
          rw [extendedBasisColumns_last, extendedCoefficient_last_castSucc,
            mul_zero, add_zero]
          refine Finset.sum_congr rfl fun middleIndex _ => ?_
          rw [extendedBasisColumns_castSucc,
            extendedCoefficient_castSucc_castSucc]

/-- **THE EXTENDED KERNEL LAW.**  With an adjoined nonzero column that
the basis transpose annihilates, the extended matrix stays
kernel-free. -/
theorem extended_kernel_free {B : Matrix (Fin 6) (Fin 5) ℝ}
    {L : Matrix (Fin 5) (Fin 6) ℝ} (hleft : L * B = 1)
    {extraColumn : Fin 6 → ℝ} (hne : extraColumn ≠ 0)
    (horth : Bᵀ *ᵥ extraColumn = 0)
    {coeffVec : Fin 6 → ℝ}
    (hzero : extendedBasisColumns B extraColumn *ᵥ coeffVec = 0) :
    coeffVec = 0 := by
  have hsplit : ∀ rowIndex : Fin 6,
      (B *ᵥ fun columnIndex : Fin 5 => coeffVec columnIndex.castSucc)
        rowIndex
        + extraColumn rowIndex * coeffVec (Fin.last 5) = 0 := by
    intro rowIndex
    have hentry := congrFun hzero rowIndex
    calc (B *ᵥ fun columnIndex : Fin 5 => coeffVec columnIndex.castSucc)
          rowIndex
        + extraColumn rowIndex * coeffVec (Fin.last 5)
        = ∑ columnIndex : Fin 5,
            B rowIndex columnIndex * coeffVec columnIndex.castSucc
          + extraColumn rowIndex * coeffVec (Fin.last 5) := rfl
      _ = ∑ columnIndex : Fin 6,
            extendedBasisColumns B extraColumn rowIndex columnIndex
              * coeffVec columnIndex := by
          conv_rhs => rw [Fin.sum_univ_castSucc]
          rw [extendedBasisColumns_last]
          refine congrArg₂ (· + ·) ?_ rfl
          refine Finset.sum_congr rfl fun columnIndex _ => ?_
          rw [extendedBasisColumns_castSucc]
      _ = (extendedBasisColumns B extraColumn *ᵥ coeffVec) rowIndex := rfl
      _ = 0 := hentry
  have hlast : coeffVec (Fin.last 5) = 0 := by
    have hdot : ∑ rowIndex : Fin 6, extraColumn rowIndex
        * ((B *ᵥ fun columnIndex : Fin 5 => coeffVec columnIndex.castSucc)
            rowIndex
          + extraColumn rowIndex * coeffVec (Fin.last 5)) = 0 := by
      refine Finset.sum_eq_zero fun rowIndex _ => ?_
      rw [hsplit rowIndex, mul_zero]
    have hcross : ∑ rowIndex : Fin 6, extraColumn rowIndex
        * (B *ᵥ fun columnIndex : Fin 5 => coeffVec columnIndex.castSucc)
            rowIndex = 0 := by
      calc ∑ rowIndex : Fin 6, extraColumn rowIndex
          * (B *ᵥ fun columnIndex : Fin 5 =>
              coeffVec columnIndex.castSucc) rowIndex
          = ∑ rowIndex : Fin 6, ∑ columnIndex : Fin 5,
              extraColumn rowIndex
                * (B rowIndex columnIndex
                  * coeffVec columnIndex.castSucc) := by
            refine Finset.sum_congr rfl fun rowIndex _ => ?_
            rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
        _ = ∑ columnIndex : Fin 5, (∑ rowIndex : Fin 6,
              B rowIndex columnIndex * extraColumn rowIndex)
                * coeffVec columnIndex.castSucc := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun columnIndex _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun rowIndex _ => ?_
            ring
        _ = 0 := by
            refine Finset.sum_eq_zero fun columnIndex _ => ?_
            have hcol := congrFun horth columnIndex
            have hform : (Bᵀ *ᵥ extraColumn) columnIndex
                = ∑ rowIndex : Fin 6,
                    B rowIndex columnIndex * extraColumn rowIndex := by
              rw [Matrix.mulVec, dotProduct]
              refine Finset.sum_congr rfl fun rowIndex _ => ?_
              rw [Matrix.transpose_apply]
            rw [hform, Pi.zero_apply] at hcol
            rw [hcol, zero_mul]
    have hnorm : (∑ rowIndex : Fin 6,
        extraColumn rowIndex * extraColumn rowIndex)
        * coeffVec (Fin.last 5) = 0 := by
      calc (∑ rowIndex : Fin 6, extraColumn rowIndex * extraColumn rowIndex)
          * coeffVec (Fin.last 5)
          = ∑ rowIndex : Fin 6, extraColumn rowIndex
              * (extraColumn rowIndex * coeffVec (Fin.last 5)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun rowIndex _ => ?_
            ring
        _ = ∑ rowIndex : Fin 6, extraColumn rowIndex
            * ((B *ᵥ fun columnIndex : Fin 5 =>
                coeffVec columnIndex.castSucc) rowIndex
              + extraColumn rowIndex * coeffVec (Fin.last 5))
            - ∑ rowIndex : Fin 6, extraColumn rowIndex
              * (B *ᵥ fun columnIndex : Fin 5 =>
                  coeffVec columnIndex.castSucc) rowIndex := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun rowIndex _ => ?_
            ring
        _ = 0 := by rw [hdot, hcross, sub_zero]
    have hself : extraColumn ⬝ᵥ extraColumn ≠ 0 :=
      fun hcontra => hne (dotProduct_self_eq_zero.mp hcontra)
    have hselfForm : extraColumn ⬝ᵥ extraColumn
        = ∑ rowIndex : Fin 6, extraColumn rowIndex * extraColumn rowIndex :=
      rfl
    rcases mul_eq_zero.mp hnorm with hcase | hcase
    · exact absurd (hselfForm.trans hcase) hself
    · exact hcase
  have hbulkZero : (B *ᵥ fun columnIndex : Fin 5 =>
      coeffVec columnIndex.castSucc) = 0 := by
    funext rowIndex
    have hrow := hsplit rowIndex
    rw [hlast, mul_zero, add_zero] at hrow
    exact hrow
  have hbulk : (fun columnIndex : Fin 5 => coeffVec columnIndex.castSucc)
      = 0 := by
    calc (fun columnIndex : Fin 5 => coeffVec columnIndex.castSucc)
        = (1 : Matrix (Fin 5) (Fin 5) ℝ)
          *ᵥ fun columnIndex : Fin 5 => coeffVec columnIndex.castSucc := by
          rw [Matrix.one_mulVec]
      _ = (L * B) *ᵥ fun columnIndex : Fin 5 =>
            coeffVec columnIndex.castSucc := by rw [hleft]
      _ = L *ᵥ (B *ᵥ fun columnIndex : Fin 5 =>
            coeffVec columnIndex.castSucc) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hbulkZero, Matrix.mulVec_zero]
  funext slotIndex
  refine Fin.lastCases ?_ ?_ slotIndex
  · exact hlast
  · intro slotIndex
    exact congrFun hbulk slotIndex

/-- **THE EXTENDED TRACE.**  The adjoined unit slot adds one to the
trace. -/
theorem extended_trace (M : Matrix (Fin 5) (Fin 5) ℝ) :
    Matrix.trace (extendedCoefficient M) = Matrix.trace M + 1 := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag]
  rw [Fin.sum_univ_castSucc, extendedCoefficient_last_last]
  refine congrArg₂ (· + ·) ?_ rfl
  refine Finset.sum_congr rfl fun rowIndex _ => ?_
  rw [extendedCoefficient_castSucc_castSucc]

/-! ## Layer 5 — the rank-five trace pin -/

/-- **THE TRACE PIN.**  A full-carrier atom pins the rank-five
coefficient trace at two.  The quantization zeroes the shifted weight,
the projected axis survives outside the basis span, and the extended
conjugation reads the chart trace as the coefficient trace plus one. -/
theorem RankFiveFrame.trace_eq_two_of_full_carrier_atom {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {atomIndex : Fin 6}
    (hcarrier : ∀ columnIndex : Fin 5,
      atomIndex ∈ datumTightSupport frame.tightDir
        (frame.basisLabel columnIndex)) :
    Matrix.trace frame.coeff = 2 := by
  classical
  have hzero := full_carrier_diagonal_zero frame.hdata frame.basisLabel
    frame.hrepresentation frame.hidempotent frame.hmemAll frame.hvalueNeg
    (0 : Fin 5) hcarrier
  have hann := assembly_mulVec_projection_single_of_diagonal_zero frame.hdata
    hzero
  have hBt := basisTranspose_zero_of_assembly_mulVec_zero frame.basisLabel
    frame.hleft frame.hHform frame.hker hann
  by_cases hx : (chartPointOfDesign crux.design).chart
      *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) = 0
  · exfalso
    have hdiag := single_dotProduct_mulVec_single
      ((chartPointOfDesign crux.design).chart) atomIndex
    rw [hx, dotProduct_zero] at hdiag
    have hfloor := crux.gap_diagonal_pos_of_allHeavy atomIndex
    have hgap : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomIndex atomIndex
        = (chartPointOfDesign crux.design).chart atomIndex atomIndex
          - (chartPointOfDesign crux.design).weight atomIndex := by
      rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
    rw [hgap, ← hdiag] at hfloor
    linarith [frame.hdata.weight_pos atomIndex]
  · have hidemP : (chartPointOfDesign crux.design).chart
        * (chartPointOfDesign crux.design).chart
        = (chartPointOfDesign crux.design).chart := by
      show projectionOfDesign crux.design * projectionOfDesign crux.design
        = projectionOfDesign crux.design
      exact projectionOfDesign_mul_self crux.design
    have hsym : ((chartPointOfDesign crux.design).chart)ᵀ
        = (chartPointOfDesign crux.design).chart := by
      show (projectionOfDesign crux.design)ᵀ = projectionOfDesign crux.design
      exact projectionOfDesign_transpose crux.design
    have hfix : (chartPointOfDesign crux.design).chart
        *ᵥ ((chartPointOfDesign crux.design).chart
          *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ))
        = (chartPointOfDesign crux.design).chart
          *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) := by
      rw [Matrix.mulVec_mulVec, hidemP]
    have hrep6 := extended_representation frame.hrepresentation hfix
    have hker6 : ∀ coeffVec : Fin 6 → ℝ,
        extendedBasisColumns (tightBasisColumns frame.tightDir
          frame.basisLabel)
          ((chartPointOfDesign crux.design).chart
            *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) *ᵥ coeffVec = 0 →
        coeffVec = 0 :=
      fun coeffVec hvec =>
        extended_kernel_free frame.hleft hx hBt hvec
  -- the transpose of the extension is kernel-free through the determinant
    have hdet : (extendedBasisColumns (tightBasisColumns frame.tightDir
        frame.basisLabel)
        ((chartPointOfDesign crux.design).chart
          *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ))).det ≠ 0 := by
      intro hdet0
      obtain ⟨probeVec, hprobeNe, hprobeZero⟩ :=
        Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
      exact hprobeNe (hker6 probeVec hprobeZero)
    have hkerT : ∀ coeffVec : Fin 6 → ℝ,
        (extendedBasisColumns (tightBasisColumns frame.tightDir
          frame.basisLabel)
          ((chartPointOfDesign crux.design).chart
            *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)))ᵀ *ᵥ coeffVec = 0 →
        coeffVec = 0 := by
      intro coeffVec hvec
      by_contra hne
      have hdetT : ((extendedBasisColumns (tightBasisColumns frame.tightDir
          frame.basisLabel)
          ((chartPointOfDesign crux.design).chart
            *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)))ᵀ).det = 0 :=
        Matrix.exists_mulVec_eq_zero_iff.mp ⟨coeffVec, hne, hvec⟩
      rw [Matrix.det_transpose] at hdetT
      exact hdet hdetT
    have hconj : (extendedBasisColumns (tightBasisColumns frame.tightDir
        frame.basisLabel)
        ((chartPointOfDesign crux.design).chart
          *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)))ᵀ
        * (chartPointOfDesign crux.design).chart
        = (extendedCoefficient frame.coeff)ᵀ
          * (extendedBasisColumns (tightBasisColumns frame.tightDir
            frame.basisLabel)
            ((chartPointOfDesign crux.design).chart
              *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)))ᵀ := by
      have htrans := congrArg Matrix.transpose hrep6
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hsym] at htrans
      exact htrans
    have htrace := trace_eq_of_kernel_free_conjugation hconj hkerT
    rw [Matrix.trace_transpose, extended_trace] at htrace
    have htrP : Matrix.trace (chartPointOfDesign crux.design).chart
        = (3 : ℝ) := by
      show Matrix.trace (projectionOfDesign crux.design) = (3 : ℝ)
      rw [trace_projectionOfDesign]
      norm_num
    rw [htrP] at htrace
    linarith

/-- **THE TRACE-THREE REFUSAL.**  The trace-three side of the rank-five
disjunction admits no full-carrier atom. -/
theorem RankFiveFrame.false_of_full_carrier_atom_of_trace_three
    {crux : SixThreeCrux} (frame : RankFiveFrame crux) {atomIndex : Fin 6}
    (hcarrier : ∀ columnIndex : Fin 5,
      atomIndex ∈ datumTightSupport frame.tightDir
        (frame.basisLabel columnIndex))
    (htraceThree : Matrix.trace frame.coeff = 3) : False := by
  have htwo := frame.trace_eq_two_of_full_carrier_atom hcarrier
  rw [htwo] at htraceThree
  norm_num at htraceThree

/-- **THE CENSUS FORM OF THE PIN.**  A multiplicity-five atom pins the
rank-five coefficient trace at two. -/
theorem RankFiveFrame.trace_eq_two_of_multiplicity_five {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {atomIndex : Fin 6}
    (hfive : basisSupportMultiplicity frame.tightDir frame.basisLabel
      atomIndex = 5) :
    Matrix.trace frame.coeff = 2 := by
  classical
  have huniv := Finset.eq_univ_of_card
    (Finset.univ.filter fun columnIndex =>
      atomIndex ∈ datumTightSupport frame.tightDir
        (frame.basisLabel columnIndex))
    (by rw [← basisSupportMultiplicity, hfive, Fintype.card_fin])
  refine frame.trace_eq_two_of_full_carrier_atom (atomIndex := atomIndex)
    fun columnIndex => ?_
  have hmem : columnIndex ∈ Finset.univ.filter fun otherColumn =>
      atomIndex ∈ datumTightSupport frame.tightDir
        (frame.basisLabel otherColumn) := by
    rw [huniv]
    exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hmem).2

end Gtz

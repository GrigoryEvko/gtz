import Gtz.Wave.DenseProfileDispatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The dense kernel-line dichotomy — the trace geometry of the fifth rank

The rank-five basis leaves a one-dimensional orthocomplement.  This
module builds that line explicitly and reads its geometry.  A kernel
vector exists through the padded determinant.  Any two kernel vectors
are parallel through the extension calculus.  The chart maps the line
to itself, the scale is idempotent, and the scaled extension conjugation
prices the coefficient trace as three minus the scale.  Thus the frame
trace disjunction IS the kernel-line dichotomy: trace two fixes the
line, trace three kills it.

The module also lands two dense supply laws.  The leak square read
prices the off-block leak mass of every tight direction — a per-label
law, valid for extra labels too.  The heavy kernel column identifies
the projected heavy axis of a multiplicity-five atom as the kernel
line, with the pinned weight and the nonvanishing witness.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.exists_basisTranspose_kernel_vector` — **THE KERNEL LINE
  EXISTS.**
* `Gtz.extendedBasisColumns_mulVec_apply` — the extension split.
* `Gtz.parallel_of_basisTranspose_zero` — **THE LINE IS ONE
  DIMENSIONAL.**
* `Gtz.extendedCoefficientScaled` with the entry, representation, and
  trace laws — the scaled extension calculus.
* `Gtz.RankFiveFrame.trace_sub_of_kernel_scale` — **THE TRACE READ.**
* `Gtz.RankFiveFrame.kernel_line_dichotomy` — **THE DICHOTOMY.**
* `Gtz.tight_leak_square_read` — **THE LEAK SQUARE.**
* `Gtz.RankFiveFrame.heavy_kernel_column` — the profile-A bundle.

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds.  The
extension calculus and the kernel existence are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## Layer 1 — the kernel line exists -/

/-- The basis transpose with an adjoined zero row. -/
noncomputable def basisTransposePadded (B : Matrix (Fin 6) (Fin 5) ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of (Fin.snoc (fun rowIndex : Fin 5 => Bᵀ rowIndex) 0)

theorem basisTransposePadded_castSucc (B : Matrix (Fin 6) (Fin 5) ℝ)
    (rowIndex : Fin 5) (columnIndex : Fin 6) :
    basisTransposePadded B rowIndex.castSucc columnIndex
      = Bᵀ rowIndex columnIndex := by
  simp only [basisTransposePadded, Matrix.of_apply, Fin.snoc_castSucc]

theorem basisTransposePadded_last (B : Matrix (Fin 6) (Fin 5) ℝ)
    (columnIndex : Fin 6) :
    basisTransposePadded B (Fin.last 5) columnIndex = 0 := by
  simp only [basisTransposePadded, Matrix.of_apply, Fin.snoc_last,
    Pi.zero_apply]

/-- **THE KERNEL LINE EXISTS.**  Every six-by-five matrix has a nonzero
vector that its transpose annihilates: the padded square matrix carries
a zero row, thus a vanishing determinant. -/
theorem exists_basisTranspose_kernel_vector (B : Matrix (Fin 6) (Fin 5) ℝ) :
    ∃ kernelVec : Fin 6 → ℝ, kernelVec ≠ 0 ∧ Bᵀ *ᵥ kernelVec = 0 := by
  classical
  have hdet : (basisTransposePadded B).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero (Fin.last 5)
      (fun columnIndex => basisTransposePadded_last B columnIndex)
  obtain ⟨kernelVec, hne, hzero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨kernelVec, hne, ?_⟩
  funext columnIndex
  have hrow := congrFun hzero columnIndex.castSucc
  calc (Bᵀ *ᵥ kernelVec) columnIndex
      = (basisTransposePadded B *ᵥ kernelVec) columnIndex.castSucc := by
        show (fun atomIndex => Bᵀ columnIndex atomIndex) ⬝ᵥ kernelVec
          = (fun atomIndex => basisTransposePadded B columnIndex.castSucc
              atomIndex) ⬝ᵥ kernelVec
        congr 1
        funext atomIndex
        rw [basisTransposePadded_castSucc]
    _ = 0 := by rw [hrow]; rfl

/-! ## Layer 2 — the line is one dimensional -/

/-- The extension split: the extended product reads the bulk part plus
the adjoined column times the last coefficient. -/
theorem extendedBasisColumns_mulVec_apply (B : Matrix (Fin 6) (Fin 5) ℝ)
    (extraColumn : Fin 6 → ℝ) (coeffVec : Fin 6 → ℝ) (rowIndex : Fin 6) :
    (extendedBasisColumns B extraColumn *ᵥ coeffVec) rowIndex
      = (B *ᵥ fun columnIndex : Fin 5 => coeffVec columnIndex.castSucc)
          rowIndex
        + extraColumn rowIndex * coeffVec (Fin.last 5) := by
  calc (extendedBasisColumns B extraColumn *ᵥ coeffVec) rowIndex
      = ∑ columnIndex : Fin 6,
          extendedBasisColumns B extraColumn rowIndex columnIndex
            * coeffVec columnIndex := rfl
    _ = ∑ columnIndex : Fin 5,
          B rowIndex columnIndex * coeffVec columnIndex.castSucc
        + extraColumn rowIndex * coeffVec (Fin.last 5) := by
        rw [Fin.sum_univ_castSucc, extendedBasisColumns_last]
        refine congrArg₂ (· + ·) ?_ rfl
        refine Finset.sum_congr rfl fun columnIndex _ => ?_
        rw [extendedBasisColumns_castSucc]
    _ = (B *ᵥ fun columnIndex : Fin 5 => coeffVec columnIndex.castSucc)
          rowIndex
        + extraColumn rowIndex * coeffVec (Fin.last 5) := rfl

/-- **THE LINE IS ONE DIMENSIONAL.**  Two vectors that the basis
transpose annihilates are parallel, when the basis carries a left
inverse: the extension is invertible, and the Gram core absorbs the
bulk coefficients. -/
theorem parallel_of_basisTranspose_zero {B : Matrix (Fin 6) (Fin 5) ℝ}
    {L : Matrix (Fin 5) (Fin 6) ℝ} (hleft : L * B = 1)
    {baseVec otherVec : Fin 6 → ℝ} (hne : baseVec ≠ 0)
    (horthBase : Bᵀ *ᵥ baseVec = 0) (horthOther : Bᵀ *ᵥ otherVec = 0) :
    ∃ scale : ℝ, otherVec = scale • baseVec := by
  classical
  have hkerE : ∀ coeffVec : Fin 6 → ℝ,
      extendedBasisColumns B baseVec *ᵥ coeffVec = 0 → coeffVec = 0 :=
    fun coeffVec hvec => extended_kernel_free hleft hne horthBase hvec
  have hdet : (extendedBasisColumns B baseVec).det ≠ 0 := by
    intro hdet0
    obtain ⟨probeVec, hprobeNe, hprobeZero⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
    exact hprobeNe (hkerE probeVec hprobeZero)
  have hunit : IsUnit (extendedBasisColumns B baseVec).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hsolve : otherVec = extendedBasisColumns B baseVec
      *ᵥ ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hsplit : ∀ rowIndex : Fin 6, otherVec rowIndex
      = (B *ᵥ fun columnIndex : Fin 5 =>
          ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
            columnIndex.castSucc) rowIndex
        + baseVec rowIndex
          * ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
              (Fin.last 5) := by
    intro rowIndex
    calc otherVec rowIndex
        = (extendedBasisColumns B baseVec
            *ᵥ ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec))
          rowIndex := by rw [← hsolve]
      _ = _ := extendedBasisColumns_mulVec_apply B baseVec _ rowIndex
  have hbulkOrth : Bᵀ *ᵥ (B *ᵥ fun columnIndex : Fin 5 =>
      ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
        columnIndex.castSucc) = 0 := by
    funext slotIndex
    have hother := congrFun horthOther slotIndex
    have hexpand : (Bᵀ *ᵥ otherVec) slotIndex
        = (Bᵀ *ᵥ (B *ᵥ fun columnIndex : Fin 5 =>
            ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
              columnIndex.castSucc)) slotIndex
          + ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec) (Fin.last 5)
            * (Bᵀ *ᵥ baseVec) slotIndex := by
      calc (Bᵀ *ᵥ otherVec) slotIndex
          = ∑ rowIndex : Fin 6, Bᵀ slotIndex rowIndex
              * otherVec rowIndex := rfl
        _ = ∑ rowIndex : Fin 6, (Bᵀ slotIndex rowIndex
              * (B *ᵥ fun columnIndex : Fin 5 =>
                  ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
                    columnIndex.castSucc) rowIndex
            + ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
                  (Fin.last 5)
                * (Bᵀ slotIndex rowIndex * baseVec rowIndex)) := by
            refine Finset.sum_congr rfl fun rowIndex _ => ?_
            rw [hsplit rowIndex]
            ring
        _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            rfl
    rw [hother, congrFun horthBase slotIndex] at hexpand
    have hzero : (0 : ℝ)
        = (Bᵀ *ᵥ (B *ᵥ fun columnIndex : Fin 5 =>
            ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
              columnIndex.castSucc)) slotIndex := by
      have hpi : (0 : Fin 5 → ℝ) slotIndex = 0 := rfl
      rw [hpi] at hexpand
      linarith [hexpand]
    rw [← hzero]
    rfl
  have hbulkZero : (B *ᵥ fun columnIndex : Fin 5 =>
      ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
        columnIndex.castSucc) = 0 := by
    have hself : (B *ᵥ fun columnIndex : Fin 5 =>
        ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
          columnIndex.castSucc)
        ⬝ᵥ (B *ᵥ fun columnIndex : Fin 5 =>
          ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
            columnIndex.castSucc) = 0 := by
      rw [Matrix.dotProduct_mulVec]
      have hswap : (B *ᵥ fun columnIndex : Fin 5 =>
          ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
            columnIndex.castSucc) ᵥ* B
          = Bᵀ *ᵥ (B *ᵥ fun columnIndex : Fin 5 =>
              ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
                columnIndex.castSucc) :=
        (Matrix.mulVec_transpose B _).symm
      rw [hswap, hbulkOrth, zero_dotProduct]
    exact dotProduct_self_eq_zero.mp hself
  have hbulkCoeff : (fun columnIndex : Fin 5 =>
      ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
        columnIndex.castSucc) = 0 := by
    calc (fun columnIndex : Fin 5 =>
        ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
          columnIndex.castSucc)
        = (1 : Matrix (Fin 5) (Fin 5) ℝ)
          *ᵥ fun columnIndex : Fin 5 =>
            ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
              columnIndex.castSucc := by rw [Matrix.one_mulVec]
      _ = (L * B) *ᵥ fun columnIndex : Fin 5 =>
            ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
              columnIndex.castSucc := by rw [hleft]
      _ = L *ᵥ (B *ᵥ fun columnIndex : Fin 5 =>
            ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
              columnIndex.castSucc) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hbulkZero, Matrix.mulVec_zero]
  refine ⟨((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec) (Fin.last 5),
    ?_⟩
  funext rowIndex
  have hrow := hsplit rowIndex
  have hbulkRow : (B *ᵥ fun columnIndex : Fin 5 =>
      ((extendedBasisColumns B baseVec)⁻¹ *ᵥ otherVec)
        columnIndex.castSucc) rowIndex = 0 := by
    rw [hbulkZero]
    rfl
  rw [hbulkRow, zero_add] at hrow
  rw [hrow, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Layer 3 — the scaled extension calculus -/

/-- The coefficient extension with a free last diagonal scale. -/
noncomputable def extendedCoefficientScaled (M : Matrix (Fin 5) (Fin 5) ℝ)
    (lastScale : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of (Fin.snoc
    (fun rowIndex : Fin 5 =>
      Fin.snoc (fun columnIndex : Fin 5 => M rowIndex columnIndex) 0)
    (Fin.snoc (fun _ : Fin 5 => (0 : ℝ)) lastScale))

theorem extendedCoefficientScaled_castSucc_castSucc
    (M : Matrix (Fin 5) (Fin 5) ℝ) (lastScale : ℝ)
    (rowIndex columnIndex : Fin 5) :
    extendedCoefficientScaled M lastScale rowIndex.castSucc
      columnIndex.castSucc = M rowIndex columnIndex := by
  simp only [extendedCoefficientScaled, Matrix.of_apply, Fin.snoc_castSucc]

theorem extendedCoefficientScaled_castSucc_last
    (M : Matrix (Fin 5) (Fin 5) ℝ) (lastScale : ℝ) (rowIndex : Fin 5) :
    extendedCoefficientScaled M lastScale rowIndex.castSucc (Fin.last 5)
      = 0 := by
  simp only [extendedCoefficientScaled, Matrix.of_apply, Fin.snoc_castSucc,
    Fin.snoc_last]

theorem extendedCoefficientScaled_last_castSucc
    (M : Matrix (Fin 5) (Fin 5) ℝ) (lastScale : ℝ) (columnIndex : Fin 5) :
    extendedCoefficientScaled M lastScale (Fin.last 5) columnIndex.castSucc
      = 0 := by
  simp only [extendedCoefficientScaled, Matrix.of_apply, Fin.snoc_last,
    Fin.snoc_castSucc]

theorem extendedCoefficientScaled_last_last
    (M : Matrix (Fin 5) (Fin 5) ℝ) (lastScale : ℝ) :
    extendedCoefficientScaled M lastScale (Fin.last 5) (Fin.last 5)
      = lastScale := by
  simp only [extendedCoefficientScaled, Matrix.of_apply, Fin.snoc_last]

/-- **THE SCALED REPRESENTATION.**  A scaled eigenvector of the
projection extends the representation law with its scale on the last
diagonal slot. -/
theorem extended_representation_scaled {P : Matrix (Fin 6) (Fin 6) ℝ}
    {B : Matrix (Fin 6) (Fin 5) ℝ} {M : Matrix (Fin 5) (Fin 5) ℝ}
    {extraColumn : Fin 6 → ℝ} {lastScale : ℝ}
    (hrep : P * B = B * M)
    (hscale : P *ᵥ extraColumn = lastScale • extraColumn) :
    P * extendedBasisColumns B extraColumn
      = extendedBasisColumns B extraColumn
        * extendedCoefficientScaled M lastScale := by
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
      _ = lastScale * extraColumn rowIndex := by
          rw [hscale, Pi.smul_apply, smul_eq_mul]
      _ = ∑ middleIndex : Fin 6,
            extendedBasisColumns B extraColumn rowIndex middleIndex
              * extendedCoefficientScaled M lastScale middleIndex
                (Fin.last 5) := by
          conv_rhs => rw [Fin.sum_univ_castSucc]
          have hbulk : ∑ middleIndex : Fin 5,
              extendedBasisColumns B extraColumn rowIndex
                  middleIndex.castSucc
                * extendedCoefficientScaled M lastScale
                    middleIndex.castSucc (Fin.last 5)
              = 0 := by
            refine Finset.sum_eq_zero fun middleIndex _ => ?_
            rw [extendedCoefficientScaled_castSucc_last, mul_zero]
          rw [hbulk, extendedBasisColumns_last,
            extendedCoefficientScaled_last_last, zero_add]
          ring
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
              * extendedCoefficientScaled M lastScale middleIndex
                columnIndex.castSucc := by
          conv_rhs => rw [Fin.sum_univ_castSucc]
          rw [extendedBasisColumns_last,
            extendedCoefficientScaled_last_castSucc, mul_zero, add_zero]
          refine Finset.sum_congr rfl fun middleIndex _ => ?_
          rw [extendedBasisColumns_castSucc,
            extendedCoefficientScaled_castSucc_castSucc]

/-- **THE SCALED TRACE.**  The adjoined slot adds its scale to the
trace. -/
theorem extended_trace_scaled (M : Matrix (Fin 5) (Fin 5) ℝ)
    (lastScale : ℝ) :
    Matrix.trace (extendedCoefficientScaled M lastScale)
      = Matrix.trace M + lastScale := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag]
  rw [Fin.sum_univ_castSucc, extendedCoefficientScaled_last_last]
  refine congrArg₂ (· + ·) ?_ rfl
  refine Finset.sum_congr rfl fun rowIndex _ => ?_
  rw [extendedCoefficientScaled_castSucc_castSucc]

/-! ## Layer 4 — the trace read and the dichotomy -/

/-- **THE TRACE READ.**  A nonzero kernel vector that the chart scales
prices the coefficient trace as three minus the scale. -/
theorem RankFiveFrame.trace_sub_of_kernel_scale {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {kernelVec : Fin 6 → ℝ} {lastScale : ℝ}
    (hne : kernelVec ≠ 0)
    (horth : (tightBasisColumns frame.tightDir frame.basisLabel)ᵀ
      *ᵥ kernelVec = 0)
    (hscale : (chartPointOfDesign crux.design).chart *ᵥ kernelVec
      = lastScale • kernelVec) :
    Matrix.trace frame.coeff = 3 - lastScale := by
  classical
  have hsym : ((chartPointOfDesign crux.design).chart)ᵀ
      = (chartPointOfDesign crux.design).chart := by
    show (projectionOfDesign crux.design)ᵀ = projectionOfDesign crux.design
    exact projectionOfDesign_transpose crux.design
  have hrep6 := extended_representation_scaled frame.hrepresentation hscale
  have hker6 : ∀ coeffVec : Fin 6 → ℝ,
      extendedBasisColumns (tightBasisColumns frame.tightDir
        frame.basisLabel) kernelVec *ᵥ coeffVec = 0 → coeffVec = 0 :=
    fun coeffVec hvec => extended_kernel_free frame.hleft hne horth hvec
  have hdet : (extendedBasisColumns (tightBasisColumns frame.tightDir
      frame.basisLabel) kernelVec).det ≠ 0 := by
    intro hdet0
    obtain ⟨probeVec, hprobeNe, hprobeZero⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
    exact hprobeNe (hker6 probeVec hprobeZero)
  have hkerT : ∀ coeffVec : Fin 6 → ℝ,
      (extendedBasisColumns (tightBasisColumns frame.tightDir
        frame.basisLabel) kernelVec)ᵀ *ᵥ coeffVec = 0 → coeffVec = 0 := by
    intro coeffVec hvec
    by_contra hcne
    have hdetT : ((extendedBasisColumns (tightBasisColumns frame.tightDir
        frame.basisLabel) kernelVec)ᵀ).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨coeffVec, hcne, hvec⟩
    rw [Matrix.det_transpose] at hdetT
    exact hdet hdetT
  have hconj : (extendedBasisColumns (tightBasisColumns frame.tightDir
      frame.basisLabel) kernelVec)ᵀ
      * (chartPointOfDesign crux.design).chart
      = (extendedCoefficientScaled frame.coeff lastScale)ᵀ
        * (extendedBasisColumns (tightBasisColumns frame.tightDir
          frame.basisLabel) kernelVec)ᵀ := by
    have htrans := congrArg Matrix.transpose hrep6
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hsym] at htrans
    exact htrans
  have htrace := trace_eq_of_kernel_free_conjugation hconj hkerT
  rw [Matrix.trace_transpose, extended_trace_scaled] at htrace
  have htrP : Matrix.trace (chartPointOfDesign crux.design).chart
      = (3 : ℝ) := by
    show Matrix.trace (projectionOfDesign crux.design) = (3 : ℝ)
    rw [trace_projectionOfDesign]
    norm_num
  rw [htrP] at htrace
  linarith

/-- **THE KERNEL-LINE DICHOTOMY.**  The chart fixes the kernel line at
trace two and kills it at trace three.  The scale is idempotent, and
the trace read excludes the crossed branches. -/
theorem RankFiveFrame.kernel_line_dichotomy {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {kernelVec : Fin 6 → ℝ}
    (hne : kernelVec ≠ 0)
    (horth : (tightBasisColumns frame.tightDir frame.basisLabel)ᵀ
      *ᵥ kernelVec = 0) :
    (Matrix.trace frame.coeff = 2
      ∧ (chartPointOfDesign crux.design).chart *ᵥ kernelVec = kernelVec)
    ∨ (Matrix.trace frame.coeff = 3
      ∧ (chartPointOfDesign crux.design).chart *ᵥ kernelVec = 0) := by
  classical
  have hXiZero : chartMultiplierAssembly frame.activeSet frame.reducedWeight
      frame.tightDir *ᵥ kernelVec = 0 := by
    rw [← frame.hHform, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      horth, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hcomm : chartMultiplierAssembly frame.activeSet frame.reducedWeight
      frame.tightDir
      *ᵥ ((chartPointOfDesign crux.design).chart *ᵥ kernelVec) = 0 := by
    rw [Matrix.mulVec_mulVec, ← frame.hdata.assembly_commutes,
      ← Matrix.mulVec_mulVec, hXiZero, Matrix.mulVec_zero]
  have horthP := basisTranspose_zero_of_assembly_mulVec_zero
    frame.basisLabel frame.hleft frame.hHform frame.hker hcomm
  obtain ⟨lastScale, hscale⟩ := parallel_of_basisTranspose_zero frame.hleft
    hne horth horthP
  have hidemP : (chartPointOfDesign crux.design).chart
      * (chartPointOfDesign crux.design).chart
      = (chartPointOfDesign crux.design).chart := by
    show projectionOfDesign crux.design * projectionOfDesign crux.design
      = projectionOfDesign crux.design
    exact projectionOfDesign_mul_self crux.design
  have hsquare : (lastScale * lastScale - lastScale) • kernelVec = 0 := by
    have hfix : (chartPointOfDesign crux.design).chart
        *ᵥ ((chartPointOfDesign crux.design).chart *ᵥ kernelVec)
        = (chartPointOfDesign crux.design).chart *ᵥ kernelVec := by
      rw [Matrix.mulVec_mulVec, hidemP]
    rw [hscale, Matrix.mulVec_smul, hscale, smul_smul] at hfix
    calc (lastScale * lastScale - lastScale) • kernelVec
        = (lastScale * lastScale) • kernelVec - lastScale • kernelVec := by
          rw [sub_smul]
      _ = 0 := by rw [hfix, sub_self]
  have hquant : lastScale * lastScale = lastScale := by
    obtain ⟨witnessIndex, hwitness⟩ := Function.ne_iff.mp hne
    have hentry := congrFun hsquare witnessIndex
    rw [Pi.smul_apply, smul_eq_mul] at hentry
    have hcoord : kernelVec witnessIndex ≠ 0 := hwitness
    have hfactor : (lastScale * lastScale - lastScale)
        * kernelVec witnessIndex = 0 := hentry
    rcases mul_eq_zero.mp hfactor with hcase | hcase
    · linarith
    · exact absurd hcase hcoord
  have htread := frame.trace_sub_of_kernel_scale hne horth hscale
  have hsplit : lastScale * (lastScale - 1) = 0 := by
    linear_combination hquant
  rcases mul_eq_zero.mp hsplit with hcase | hcase
  · right
    rw [hcase] at hscale
    refine ⟨by rw [htread, hcase]; norm_num, ?_⟩
    rw [hscale, zero_smul]
  · left
    have hone : lastScale = 1 := by linarith
    rw [hone] at hscale
    refine ⟨by rw [htread, hone]; norm_num, ?_⟩
    rw [hscale, one_smul]

/-! ## Layer 5 — the leak square read -/

/-- **THE LEAK SQUARE.**  The square mass of the off-block leak of a
tight direction reads the shifted weights: the projected direction
matches the shifted read on the block, and the leftover square mass is
the shifted weight times its complement, summed with the squares.  The
law holds per label, thus for extra labels too. -/
theorem tight_leak_square_read
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection) :
    ∑ atomIndex : Fin size, ((projection *ᵥ tightDir label) atomIndex
        - (value + weight atomIndex) * tightDir label atomIndex) ^ 2
      = ∑ atomIndex : Fin size, (value + weight atomIndex)
          * (1 - (value + weight atomIndex))
          * tightDir label atomIndex ^ 2 := by
  have hPq : (projection *ᵥ tightDir label)
      ⬝ᵥ (projection *ᵥ tightDir label)
      = tightDir label ⬝ᵥ (projection *ᵥ tightDir label) := by
    conv_lhs => rw [Matrix.dotProduct_mulVec]
    have hswap : (projection *ᵥ tightDir label) ᵥ* projection
        = projection *ᵥ (projection *ᵥ tightDir label) := by
      rw [← Matrix.mulVec_transpose, hsym]
    rw [hswap, Matrix.mulVec_mulVec, hidem]
    exact dotProduct_comm _ _
  have hcross : ∀ atomIndex : Fin size,
      (value + weight atomIndex) * tightDir label atomIndex
        * (projection *ᵥ tightDir label) atomIndex
      = ((value + weight atomIndex) * tightDir label atomIndex) ^ 2 := by
    intro atomIndex
    by_cases hmemBlock : atomIndex ∈ activeSubset label
    · rw [projection_mulVec_tightDir_of_mem hdata hmem hmemBlock]
      ring
    · rw [hdata.tightDir_support label hmem atomIndex hmemBlock]
      ring
  have hunit : ∑ atomIndex : Fin size, tightDir label atomIndex ^ 2 = 1 := by
    have hdot := hdata.tightDir_unit label hmem
    calc ∑ atomIndex : Fin size, tightDir label atomIndex ^ 2
        = ∑ atomIndex : Fin size,
            tightDir label atomIndex * tightDir label atomIndex := by
          refine Finset.sum_congr rfl fun atomIndex _ => ?_
          ring
      _ = 1 := hdot
  have henergy : tightDir label ⬝ᵥ (projection *ᵥ tightDir label)
      = ∑ atomIndex : Fin size, (value + weight atomIndex)
          * tightDir label atomIndex ^ 2 := by
    rw [tight_energy_read hdata hmem]
    calc value + ∑ atomIndex : Fin size,
        weight atomIndex * tightDir label atomIndex ^ 2
        = value * ∑ atomIndex : Fin size, tightDir label atomIndex ^ 2
          + ∑ atomIndex : Fin size,
              weight atomIndex * tightDir label atomIndex ^ 2 := by
          rw [hunit]
          ring
      _ = ∑ atomIndex : Fin size,
            value * tightDir label atomIndex ^ 2
          + ∑ atomIndex : Fin size,
              weight atomIndex * tightDir label atomIndex ^ 2 := by
          rw [Finset.mul_sum]
      _ = ∑ atomIndex : Fin size, (value + weight atomIndex)
            * tightDir label atomIndex ^ 2 := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun atomIndex _ => ?_
          ring
  have hsquareSum : ∑ atomIndex : Fin size,
      ((projection *ᵥ tightDir label) atomIndex) ^ 2
      = ∑ atomIndex : Fin size, (value + weight atomIndex)
          * tightDir label atomIndex ^ 2 := by
    calc ∑ atomIndex : Fin size,
        ((projection *ᵥ tightDir label) atomIndex) ^ 2
        = (projection *ᵥ tightDir label)
          ⬝ᵥ (projection *ᵥ tightDir label) := by
          refine Finset.sum_congr rfl fun atomIndex _ => ?_
          ring
      _ = tightDir label ⬝ᵥ (projection *ᵥ tightDir label) := hPq
      _ = _ := henergy
  calc ∑ atomIndex : Fin size, ((projection *ᵥ tightDir label) atomIndex
      - (value + weight atomIndex) * tightDir label atomIndex) ^ 2
      = ∑ atomIndex : Fin size,
          (((projection *ᵥ tightDir label) atomIndex) ^ 2
            - (2 * ((value + weight atomIndex) * tightDir label atomIndex
                * (projection *ᵥ tightDir label) atomIndex)
              - ((value + weight atomIndex)
                  * tightDir label atomIndex) ^ 2)) := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        ring
    _ = ∑ atomIndex : Fin size,
          ((projection *ᵥ tightDir label) atomIndex) ^ 2
        - ∑ atomIndex : Fin size,
            (2 * ((value + weight atomIndex) * tightDir label atomIndex
              * (projection *ᵥ tightDir label) atomIndex)
            - ((value + weight atomIndex)
                * tightDir label atomIndex) ^ 2) := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ atomIndex : Fin size,
          ((projection *ᵥ tightDir label) atomIndex) ^ 2
        - ∑ atomIndex : Fin size,
            ((value + weight atomIndex) * tightDir label atomIndex) ^ 2 := by
        refine congrArg₂ (· - ·) rfl ?_
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rw [hcross atomIndex]
        ring
    _ = ∑ atomIndex : Fin size, (value + weight atomIndex)
          * tightDir label atomIndex ^ 2
        - ∑ atomIndex : Fin size,
            ((value + weight atomIndex) * tightDir label atomIndex) ^ 2 := by
        rw [hsquareSum]
    _ = ∑ atomIndex : Fin size, (value + weight atomIndex)
          * (1 - (value + weight atomIndex))
          * tightDir label atomIndex ^ 2 := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        ring

/-! ## Layer 6 — the heavy kernel column -/

/-- **THE HEAVY KERNEL COLUMN.**  At a multiplicity-five atom of a
rank-five frame, the projected heavy axis is a nonzero fixed vector of
the chart that the basis transpose annihilates, and the heavy weight is
the negative value.  The projected axis IS the kernel line, and the
whole heavy gap row is readable from it. -/
theorem RankFiveFrame.heavy_kernel_column {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {heavyAtom : Fin 6}
    (hfive : basisSupportMultiplicity frame.tightDir frame.basisLabel
      heavyAtom = 5) :
    (chartPointOfDesign crux.design).weight heavyAtom
        = -(chartObjective (chartPointOfDesign crux.design))
      ∧ (tightBasisColumns frame.tightDir frame.basisLabel)ᵀ
          *ᵥ ((chartPointOfDesign crux.design).chart
            *ᵥ (Pi.single heavyAtom 1 : Fin 6 → ℝ)) = 0
      ∧ (chartPointOfDesign crux.design).chart
          *ᵥ ((chartPointOfDesign crux.design).chart
            *ᵥ (Pi.single heavyAtom 1 : Fin 6 → ℝ))
        = (chartPointOfDesign crux.design).chart
            *ᵥ (Pi.single heavyAtom 1 : Fin 6 → ℝ)
      ∧ (chartPointOfDesign crux.design).chart
          *ᵥ (Pi.single heavyAtom 1 : Fin 6 → ℝ) ≠ 0 := by
  classical
  have hzero := full_carrier_diagonal_zero frame.hdata frame.basisLabel
    frame.hrepresentation frame.hidempotent frame.hmemAll frame.hvalueNeg
    (0 : Fin 5) (forall_carrier_of_multiplicity_eq_card hfive)
  have hann := assembly_mulVec_projection_single_of_diagonal_zero
    frame.hdata hzero
  have hBt := basisTranspose_zero_of_assembly_mulVec_zero frame.basisLabel
    frame.hleft frame.hHform frame.hker hann
  have hidemP : (chartPointOfDesign crux.design).chart
      * (chartPointOfDesign crux.design).chart
      = (chartPointOfDesign crux.design).chart := by
    show projectionOfDesign crux.design * projectionOfDesign crux.design
      = projectionOfDesign crux.design
    exact projectionOfDesign_mul_self crux.design
  have hfix : (chartPointOfDesign crux.design).chart
      *ᵥ ((chartPointOfDesign crux.design).chart
        *ᵥ (Pi.single heavyAtom 1 : Fin 6 → ℝ))
      = (chartPointOfDesign crux.design).chart
        *ᵥ (Pi.single heavyAtom 1 : Fin 6 → ℝ) := by
    rw [Matrix.mulVec_mulVec, hidemP]
  have hne : (chartPointOfDesign crux.design).chart
      *ᵥ (Pi.single heavyAtom 1 : Fin 6 → ℝ) ≠ 0 := by
    intro hcontra
    have hdiag := single_dotProduct_mulVec_single
      ((chartPointOfDesign crux.design).chart) heavyAtom
    rw [hcontra, dotProduct_zero] at hdiag
    have hfloor := crux.gap_diagonal_pos_of_allHeavy heavyAtom
    have hgap : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight heavyAtom heavyAtom
        = (chartPointOfDesign crux.design).chart heavyAtom heavyAtom
          - (chartPointOfDesign crux.design).weight heavyAtom := by
      rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
    rw [hgap, ← hdiag] at hfloor
    linarith [frame.hdata.weight_pos heavyAtom]
  exact ⟨by linarith [hzero], hBt, hfix, hne⟩

end Gtz

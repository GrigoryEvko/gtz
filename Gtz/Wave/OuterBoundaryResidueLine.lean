import Gtz.Wave.OuterComplementNullKill
import Gtz.Wave.SharedPrivateKernelGram
import Gtz.Quantitative.ZeroLeakDependency

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The outer boundary residue line — at most one boundary atom

A stationary datum with a left-invertible basis splits its chart into
the capture frame `B * coeff * (Bᵀ * B)⁻¹ * Bᵀ` and a kernel residue.
The residue is a symmetric idempotent and its trace is the trace gap
`rank - trace coeff`.  This module reads the split at the ATOM AXES.

The reading is a dichotomy.  The shifted weight of an atom vanishes if
and only if the capture frame kills that atom axis.  At such a BOUNDARY
atom the whole chart column is residue, thus it is a nonzero vector
that the residue fixes.  Two boundary atoms thus give two fixed vectors
of a residue of trace one, the trace floor makes them parallel, and a
parallel pair of chart columns is a parallel pair of design atoms.  The
crux carries no parallel pair, thus:

**AT MOST ONE ATOM OF A RANK-FOUR OR A RANK-FIVE FRAME IS A BOUNDARY
ATOM, AND A RANK-SIX FRAME HAS NONE.**

The same split closes the clone half of the rank-four closure-one
lattice with NO interiority hypothesis.  A basis null direction
supported on a pair of atoms is killed by the capture frame, thus the
two capture columns die together.  Two boundary atoms are impossible,
thus both atoms of a clone pair are interior.  A full clone pair
carries a zero shifted weight, thus a full clone pair is dead and
`Gtz.RankFourOuterCloneClosed` reduces to its THIN half alone.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.eq_zero_of_fixed_of_trace_lt_one` — a fixed vector of a
  symmetric idempotent of trace less than one is zero.
* `Gtz.parallel_of_fixed_of_trace_lt_two` — **THE TRACE-ONE PARALLEL
  LAW.**
* `Gtz.captureFrame`, `Gtz.captureResidue` — the split.
* `Gtz.captureResidue_transpose`, `Gtz.captureResidue_mul_self`,
  `Gtz.captureResidue_trace`, `Gtz.transpose_basis_mul_captureResidue`
  — the residue laws.
* `Gtz.captureFrame_mulVec_eq_zero_of_basis_dot` — the null kill.
* `Gtz.captureFrame_mulVec_single_eq_zero_of_boundary` and
  `Gtz.boundary_of_captureFrame_mulVec_single_eq_zero` — **THE
  BOUNDARY DICHOTOMY.**
* `Gtz.SixThreeCrux.false_of_two_capture_kills` and
  `Gtz.SixThreeCrux.false_of_two_boundary_atoms` — **THE BOUNDARY PAIR
  KILL.**
* `Gtz.SixThreeCrux.shifted_weight_pos_of_pair_null` — **THE
  PROPORTIONAL-ROW INTERIOR LAW.**
* `Gtz.SixThreeCrux.shifted_weight_pos_of_capture_trace_rank` — the
  trace-gap interiority.
* `Gtz.RankFourFrame.false_of_two_boundary_atoms`,
  `Gtz.RankFourFrame.shifted_weight_pos_of_pair_null`,
  `Gtz.RankFourFrame.boundary_card_le_one`,
  `Gtz.RankFourFrame.five_le_interior_card` — the rank-four readings.
* `Gtz.RankFiveFrame.false_of_two_boundary_atoms`,
  `Gtz.RankFiveFrame.shifted_weight_pos_of_pair_null`,
  `Gtz.RankFiveFrame.boundary_card_le_one`,
  `Gtz.RankSixFrame.shifted_weight_pos_of_residue` — the two other
  rungs.
* `Gtz.RankFourOuterData.shifted_weight_pos_of_clone` — the datum
  reading.
* `Gtz.rankFourOuterCloneClosed_of_thin` — **THE CLONE CLOSURE WITH NO
  INTERIORITY.**
* `Gtz.rankFourSupportTwoClosed_of_thin_triple_interior` — the
  sharpened rank-four discharge.

## Vacuity

Layers one thru three hold at every stationary datum with a chosen
basis.  The crux-facing statements are vacuous if `Gtz.GtzWeighted 6 3`
holds: no crux exists, thus no frame and no datum exists.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the fixed vectors of a low-trace idempotent -/

section FixedFamily

variable {dim : ℕ} {idem : Matrix (Fin dim) (Fin dim) ℝ}

/-- **THE TRACE-ZERO FIXED LAW.**  A symmetric idempotent of trace less
than one fixes no nonzero vector: one fixed vector already forces a
trace of at least one. -/
theorem eq_zero_of_fixed_of_trace_lt_one (hsymm : idemᵀ = idem)
    (hidem : idem * idem = idem) (htrace : Matrix.trace idem < 1)
    {vec : Fin dim → ℝ} (hfix : idem *ᵥ vec = vec) :
    vec = 0 := by
  classical
  by_contra hne
  have hpos : 0 < vec ⬝ᵥ vec := dotProduct_self_pos hne
  have hker : ∀ coeffVec : Fin 1 → ℝ,
      (Matrix.of fun rowIndex colIndex : Fin 1 =>
          (fun _ : Fin 1 => vec) rowIndex ⬝ᵥ (fun _ : Fin 1 => vec) colIndex)
        *ᵥ coeffVec = 0 → coeffVec = 0 := by
    intro coeffVec hzero
    have hentry := congrFun hzero 0
    have hexpand : ((Matrix.of fun rowIndex colIndex : Fin 1 =>
          (fun _ : Fin 1 => vec) rowIndex ⬝ᵥ (fun _ : Fin 1 => vec) colIndex)
        *ᵥ coeffVec) 0 = (vec ⬝ᵥ vec) * coeffVec 0 := by
      simp [Matrix.mulVec, dotProduct]
    rw [hexpand] at hentry
    have hzeroEntry : coeffVec 0 = 0 := by
      rcases mul_eq_zero.mp hentry with hcontra | hgood
      · exact absurd hcontra hpos.ne'
      · exact hgood
    funext index
    have hindex : index = 0 := Subsingleton.elim index 0
    rw [hindex, hzeroEntry]
    rfl
  have hfloor := trace_floor_of_fixed_family hsymm hidem
    (fun _ : Fin 1 => vec) (fun _ => hfix) hker
  rw [Nat.cast_one] at hfloor
  linarith

/-- **THE TRACE-ONE PARALLEL LAW.**  A symmetric idempotent of trace
less than two fixes at most one line: two fixed vectors, the first
nonzero, are proportional.  The proof orthogonalizes the second against
the first and reads the trace floor of the resulting pair. -/
theorem parallel_of_fixed_of_trace_lt_two (hsymm : idemᵀ = idem)
    (hidem : idem * idem = idem) (htrace : Matrix.trace idem < 2)
    {first second : Fin dim → ℝ} (hfirst : idem *ᵥ first = first)
    (hsecond : idem *ᵥ second = second) (hne : first ≠ 0) :
    second = ((first ⬝ᵥ second) / (first ⬝ᵥ first)) • first := by
  classical
  have hpos : 0 < first ⬝ᵥ first := dotProduct_self_pos hne
  have hnezero : first ⬝ᵥ first ≠ 0 := ne_of_gt hpos
  set residualVec : Fin dim → ℝ :=
    (first ⬝ᵥ first) • second - (first ⬝ᵥ second) • first with hresidual
  have hfixResidual : idem *ᵥ residualVec = residualVec := by
    rw [hresidual, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hfirst, hsecond]
  have horth : first ⬝ᵥ residualVec = 0 := by
    rw [hresidual, dotProduct_sub, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    ring
  have horthFlip : residualVec ⬝ᵥ first = 0 := by
    rw [dotProduct_comm]; exact horth
  set family : Fin 2 → (Fin dim → ℝ) :=
    fun index => if index = 0 then first else residualVec with hfamily
  have hfamilyZero : family 0 = first := by rw [hfamily]; simp
  have hfamilyOne : family 1 = residualVec := by
    rw [hfamily]
    simp
  have hresidualZero : residualVec = 0 := by
    by_contra hresidualNe
    have hposResidual : 0 < residualVec ⬝ᵥ residualVec :=
      dotProduct_self_pos hresidualNe
    have hfix : ∀ index : Fin 2, idem *ᵥ family index = family index := by
      intro index
      by_cases hzero : index = 0
      · rw [hzero, hfamilyZero]; exact hfirst
      · have hone : index = 1 := by omega
        rw [hone, hfamilyOne]; exact hfixResidual
    have hker : ∀ coeffVec : Fin 2 → ℝ,
        (Matrix.of fun rowIndex colIndex : Fin 2 =>
            family rowIndex ⬝ᵥ family colIndex) *ᵥ coeffVec = 0 →
          coeffVec = 0 := by
      intro coeffVec hzero
      have hfirstEntry := congrFun hzero 0
      have hsecondEntry := congrFun hzero 1
      have hexpandFirst : ((Matrix.of fun rowIndex colIndex : Fin 2 =>
            family rowIndex ⬝ᵥ family colIndex) *ᵥ coeffVec) 0
          = (family 0 ⬝ᵥ family 0) * coeffVec 0
            + (family 0 ⬝ᵥ family 1) * coeffVec 1 := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have hexpandSecond : ((Matrix.of fun rowIndex colIndex : Fin 2 =>
            family rowIndex ⬝ᵥ family colIndex) *ᵥ coeffVec) 1
          = (family 1 ⬝ᵥ family 0) * coeffVec 0
            + (family 1 ⬝ᵥ family 1) * coeffVec 1 := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [hexpandFirst, hfamilyZero, hfamilyOne, horth, zero_mul,
        add_zero] at hfirstEntry
      rw [hexpandSecond, hfamilyZero, hfamilyOne, horthFlip, zero_mul,
        zero_add] at hsecondEntry
      have hzeroFirst : coeffVec 0 = 0 := by
        rcases mul_eq_zero.mp hfirstEntry with hcontra | hgood
        · exact absurd hcontra hnezero
        · exact hgood
      have hzeroSecond : coeffVec 1 = 0 := by
        rcases mul_eq_zero.mp hsecondEntry with hcontra | hgood
        · exact absurd hcontra hposResidual.ne'
        · exact hgood
      funext index
      by_cases hzeroIndex : index = 0
      · rw [hzeroIndex, hzeroFirst]; rfl
      · have hone : index = 1 := by omega
        rw [hone, hzeroSecond]; rfl
    have hfloor := trace_floor_of_fixed_family hsymm hidem family hfix hker
    norm_num at hfloor
    linarith
  have hsolve : (first ⬝ᵥ first) • second = (first ⬝ᵥ second) • first := by
    have hzero := hresidualZero
    rw [hresidual] at hzero
    exact sub_eq_zero.mp hzero
  funext index
  have hentry := congrFun hsolve index
  simp only [Pi.smul_apply, smul_eq_mul] at hentry ⊢
  field_simp
  linarith [hentry]

end FixedFamily

/-! ## Layer 2 — the capture frame and the capture residue -/

section Split

variable {size basisCount : ℕ}

/-- **THE CAPTURE FRAME.**  The part of the chart that the basis span
carries: the chart read through the span projector of the basis
columns. -/
noncomputable def captureFrame (basisColumns : Matrix (Fin size) (Fin basisCount) ℝ)
    (coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ) :
    Matrix (Fin size) (Fin size) ℝ :=
  basisColumns * coeff * (basisColumnsᵀ * basisColumns)⁻¹ * basisColumnsᵀ

/-- **THE CAPTURE RESIDUE.**  The part of the chart that the basis span
does not carry. -/
noncomputable def captureResidue (projection : Matrix (Fin size) (Fin size) ℝ)
    (basisColumns : Matrix (Fin size) (Fin basisCount) ℝ)
    (coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ) :
    Matrix (Fin size) (Fin size) ℝ :=
  projection - captureFrame basisColumns coeff

variable {projection : Matrix (Fin size) (Fin size) ℝ}
variable {basisColumns : Matrix (Fin size) (Fin basisCount) ℝ}
variable {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
variable {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}

/-- The split is a split: the frame plus the residue is the chart. -/
theorem captureFrame_add_captureResidue :
    captureFrame basisColumns coeff + captureResidue projection basisColumns coeff
      = projection := by
  rw [captureResidue, add_sub_cancel]

/-- The residue of the decomposition is the named residue. -/
theorem captureResidue_eq_of_decomposition
    {residue : Matrix (Fin size) (Fin size) ℝ}
    (hdecomp : projection = basisColumns * coeff
      * (basisColumnsᵀ * basisColumns)⁻¹ * basisColumnsᵀ + residue) :
    residue = captureResidue projection basisColumns coeff := by
  rw [captureResidue, captureFrame, hdecomp, add_sub_cancel_left]

/-- **THE RESIDUE LAWS.**  The residue of a symmetric idempotent that
represents on a left-invertible column matrix is a symmetric idempotent
that annihilates the basis columns, and its trace is the trace gap. -/
theorem captureResidue_spec (hPsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hleft : leftInv * basisColumns = 1)
    (hrep : projection * basisColumns = basisColumns * coeff) :
    (captureResidue projection basisColumns coeff)ᵀ
        = captureResidue projection basisColumns coeff
      ∧ captureResidue projection basisColumns coeff
          * captureResidue projection basisColumns coeff
        = captureResidue projection basisColumns coeff
      ∧ captureResidue projection basisColumns coeff * basisColumns = 0
      ∧ basisColumnsᵀ * captureResidue projection basisColumns coeff = 0
      ∧ Matrix.trace (captureResidue projection basisColumns coeff)
        = Matrix.trace projection - Matrix.trace coeff := by
  obtain ⟨residue, hRsymm, hRidem, hRB, hBtR, hRtrace, hdecomp⟩ :=
    projection_residue_decomposition hPsymm hidem hleft hrep
  have hEq : residue = captureResidue projection basisColumns coeff :=
    captureResidue_eq_of_decomposition hdecomp
  rw [hEq] at hRsymm hRidem hRB hBtR hRtrace
  exact ⟨hRsymm, hRidem, hRB, hBtR, hRtrace⟩

/-- The residue is symmetric. -/
theorem captureResidue_transpose (hPsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hleft : leftInv * basisColumns = 1)
    (hrep : projection * basisColumns = basisColumns * coeff) :
    (captureResidue projection basisColumns coeff)ᵀ
      = captureResidue projection basisColumns coeff :=
  (captureResidue_spec hPsymm hidem hleft hrep).1

/-- The residue is idempotent. -/
theorem captureResidue_mul_self (hPsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hleft : leftInv * basisColumns = 1)
    (hrep : projection * basisColumns = basisColumns * coeff) :
    captureResidue projection basisColumns coeff
        * captureResidue projection basisColumns coeff
      = captureResidue projection basisColumns coeff :=
  (captureResidue_spec hPsymm hidem hleft hrep).2.1

/-- The basis columns die on the left of the residue. -/
theorem transpose_basis_mul_captureResidue (hPsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hleft : leftInv * basisColumns = 1)
    (hrep : projection * basisColumns = basisColumns * coeff) :
    basisColumnsᵀ * captureResidue projection basisColumns coeff = 0 :=
  (captureResidue_spec hPsymm hidem hleft hrep).2.2.2.1

/-- **THE TRACE GAP.**  The residue trace is the chart trace minus the
capture trace. -/
theorem captureResidue_trace (hPsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hleft : leftInv * basisColumns = 1)
    (hrep : projection * basisColumns = basisColumns * coeff) :
    Matrix.trace (captureResidue projection basisColumns coeff)
      = Matrix.trace projection - Matrix.trace coeff :=
  (captureResidue_spec hPsymm hidem hleft hrep).2.2.2.2

/-- **THE NULL KILL.**  The capture frame annihilates every direction
that the basis columns annihilate: the frame reads a direction only
through `basisColumnsᵀ`. -/
theorem captureFrame_mulVec_eq_zero_of_basis_dot
    {nullVec : Fin size → ℝ} (hnull : basisColumnsᵀ *ᵥ nullVec = 0) :
    captureFrame basisColumns coeff *ᵥ nullVec = 0 := by
  rw [captureFrame, ← Matrix.mulVec_mulVec, hnull, Matrix.mulVec_zero]

/-- The chart and the residue agree on every basis null direction. -/
theorem captureResidue_mulVec_eq_of_basis_dot
    {nullVec : Fin size → ℝ} (hnull : basisColumnsᵀ *ᵥ nullVec = 0) :
    captureResidue projection basisColumns coeff *ᵥ nullVec
      = projection *ᵥ nullVec := by
  rw [captureResidue, Matrix.sub_mulVec,
    captureFrame_mulVec_eq_zero_of_basis_dot hnull, sub_zero]

/-- The chart and the residue agree on every axis the capture frame
kills. -/
theorem captureResidue_mulVec_single_eq_of_capture_kill
    {atomIndex : Fin size}
    (hkill : captureFrame basisColumns coeff
      *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ) = 0) :
    captureResidue projection basisColumns coeff
        *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ)
      = projection *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ) := by
  rw [captureResidue, Matrix.sub_mulVec, hkill, sub_zero]

end Split

/-! ## Layer 3 — the axis readings of the split -/

section AxisReading

variable {dim : ℕ}

/-- The entry reading of a matrix against a coordinate axis. -/
theorem mulVec_single_one_apply (mat : Matrix (Fin dim) (Fin dim) ℝ)
    (rowIndex colIndex : Fin dim) :
    (mat *ᵥ (Pi.single colIndex 1 : Fin dim → ℝ)) rowIndex
      = mat rowIndex colIndex := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero]

end AxisReading

section Boundary

variable {size rank basisCount : ℕ} {activeIndex : Type}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- The transposed basis columns read a direction slot by slot. -/
theorem transpose_basisColumns_mulVec_apply
    (basisLabel : Fin basisCount → activeIndex) (vec : Fin size → ℝ)
    (slot : Fin basisCount) :
    ((tightBasisColumns tightDir basisLabel)ᵀ *ᵥ vec) slot
      = tightDir (basisLabel slot) ⬝ᵥ vec := by
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, tightBasisColumns]

/-- A direction that every basis column annihilates is a kernel vector
of the transposed basis columns. -/
theorem transpose_basisColumns_mulVec_eq_zero
    {basisLabel : Fin basisCount → activeIndex} {vec : Fin size → ℝ}
    (hnull : ∀ slot : Fin basisCount, tightDir (basisLabel slot) ⬝ᵥ vec = 0) :
    (tightBasisColumns tightDir basisLabel)ᵀ *ᵥ vec = 0 := by
  funext slot
  rw [transpose_basisColumns_mulVec_apply, hnull slot]
  rfl

/-- The pair direction of two atoms with proportional basis rows is a
basis null direction. -/
theorem basis_dot_pairDirection_eq_zero
    {basisLabel : Fin basisCount → activeIndex} {atomOne atomTwo : Fin size}
    {scale : ℝ}
    (hclone : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) atomTwo
        = scale * tightDir (basisLabel slot) atomOne)
    (slot : Fin basisCount) :
    tightDir (basisLabel slot)
        ⬝ᵥ ((Pi.single atomTwo 1 : Fin size → ℝ)
          - scale • (Pi.single atomOne 1 : Fin size → ℝ)) = 0 := by
  have hone : tightDir (basisLabel slot)
      ⬝ᵥ (Pi.single atomOne 1 : Fin size → ℝ)
      = tightDir (basisLabel slot) atomOne := by
    simp [dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero]
  have htwo : tightDir (basisLabel slot)
      ⬝ᵥ (Pi.single atomTwo 1 : Fin size → ℝ)
      = tightDir (basisLabel slot) atomTwo := by
    simp [dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hone, htwo, hclone slot,
    sub_self]

/-- **THE BOUNDARY COLUMN KILL.**  At an atom of zero shifted weight the
capture frame kills the atom axis.  The capture row of the atom dies at
every basis column, and the exchange law moves the coefficient through
the column Gram. -/
theorem captureFrame_mulVec_single_eq_zero_of_boundary
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrep : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {atomIndex : Fin size} (hzero : value + weight atomIndex = 0) :
    captureFrame (tightBasisColumns tightDir basisLabel) coeff
        *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ) = 0 := by
  classical
  have hrow : ∀ columnIndex,
      (tightBasisColumns tightDir basisLabel * coeff) atomIndex columnIndex = 0 :=
    fun columnIndex => basis_capture_column_zero_of_diagonal_zero hdata hspan
      hrep hzero columnIndex
  set basisColumns := tightBasisColumns tightDir basisLabel with hB
  set columnGram := basisColumnsᵀ * basisColumns with hN
  have hPsymm : projectionᵀ = projection := hdata.isSymmetric
  have hdetN : IsUnit columnGram.det :=
    columnGram_isUnit_det_of_leftInverse hleft
  have hNiN : columnGram⁻¹ * columnGram = 1 :=
    Matrix.nonsing_inv_mul columnGram hdetN
  have hNNi : columnGram * columnGram⁻¹ = 1 :=
    Matrix.mul_nonsing_inv columnGram hdetN
  have hexchange : columnGram * coeff = coeffᵀ * columnGram :=
    columnGram_exchange_of_representation hPsymm hrep
  have hMNi : coeff * columnGram⁻¹ = columnGram⁻¹ * coeffᵀ := by
    have h1 : columnGram⁻¹ * (columnGram * coeff) * columnGram⁻¹
        = columnGram⁻¹ * (coeffᵀ * columnGram) * columnGram⁻¹ := by
      rw [hexchange]
    have h2 : columnGram⁻¹ * (columnGram * coeff) * columnGram⁻¹
        = coeff * columnGram⁻¹ := by
      rw [← Matrix.mul_assoc columnGram⁻¹ columnGram coeff, hNiN, Matrix.one_mul]
    have h3 : columnGram⁻¹ * (coeffᵀ * columnGram) * columnGram⁻¹
        = columnGram⁻¹ * coeffᵀ := by
      rw [← Matrix.mul_assoc columnGram⁻¹ coeffᵀ columnGram,
        Matrix.mul_assoc (columnGram⁻¹ * coeffᵀ) columnGram columnGram⁻¹,
        hNNi, Matrix.mul_one]
    rw [← h2, h1, h3]
  have hrowvec : (basisColumns * coeff)ᵀ
      *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ) = 0 := by
    funext columnIndex
    have happly : ((basisColumns * coeff)ᵀ
        *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ)) columnIndex
        = (basisColumns * coeff) atomIndex columnIndex := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply,
        Matrix.transpose_apply, mul_ite, mul_one, mul_zero]
    rw [happly, hrow columnIndex]
    rfl
  have hswap : captureFrame basisColumns coeff
      = basisColumns * columnGram⁻¹ * (basisColumns * coeff)ᵀ := by
    rw [captureFrame, ← hN, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc coeff columnGram⁻¹ basisColumnsᵀ, hMNi,
      Matrix.mul_assoc]
  rw [hswap, ← Matrix.mulVec_mulVec, hrowvec, Matrix.mulVec_zero]

/-- **THE BOUNDARY DICHOTOMY, THE CONVERSE HALF.**  If the capture frame
kills an atom axis, the shifted weight of that atom vanishes.  The chart
column is then pure residue, thus every basis column reads zero at that
atom, and the coverage law names a live basis column whose carried
reading prices the shifted weight. -/
theorem boundary_of_captureFrame_mulVec_single_eq_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemAll : ∀ slot : Fin basisCount, basisLabel slot ∈ activeSet)
    {gram : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * gram
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrep : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hidem : projection * projection = projection)
    {atomIndex : Fin size}
    (hkill : captureFrame (tightBasisColumns tightDir basisLabel) coeff
      *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ) = 0) :
    value + weight atomIndex = 0 := by
  classical
  set basisColumns := tightBasisColumns tightDir basisLabel with hB
  have hPsymm : projectionᵀ = projection := hdata.isSymmetric
  have hcolumn : captureResidue projection basisColumns coeff
      *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ)
      = projection *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ) :=
    captureResidue_mulVec_single_eq_of_capture_kill hkill
  have hBtR : basisColumnsᵀ * captureResidue projection basisColumns coeff = 0 :=
    transpose_basis_mul_captureResidue hPsymm hidem hleft hrep
  have hbasisBlind : ∀ slot : Fin basisCount,
      (projection *ᵥ tightDir (basisLabel slot)) atomIndex = 0 := by
    intro slot
    have hzeroVec : basisColumnsᵀ
        *ᵥ (captureResidue projection basisColumns coeff
          *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ)) = 0 := by
      rw [Matrix.mulVec_mulVec, hBtR, Matrix.zero_mulVec]
    rw [hcolumn] at hzeroVec
    have hslot := congrFun hzeroVec slot
    rw [transpose_basisColumns_mulVec_apply] at hslot
    have hswap : tightDir (basisLabel slot) ᵥ* projection
        = projection *ᵥ tightDir (basisLabel slot) := by
      rw [← Matrix.mulVec_transpose, hPsymm]
    have hmove : tightDir (basisLabel slot)
        ⬝ᵥ (projection *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ))
        = (projection *ᵥ tightDir (basisLabel slot)) atomIndex := by
      rw [Matrix.dotProduct_mulVec, hswap]
      simp [dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [hmove] at hslot
    exact hslot
  obtain ⟨liveSlot, hlive⟩ := exists_live_basis_slot hdata hHform atomIndex
  have hmemBlock : atomIndex ∈ activeSubset (basisLabel liveSlot) := by
    by_contra hnot
    exact hlive (hdata.tightDir_support _ (hmemAll liveSlot) atomIndex hnot)
  have hread := projection_mulVec_tightDir_of_mem hdata (hmemAll liveSlot)
    hmemBlock
  rw [hbasisBlind liveSlot] at hread
  rcases mul_eq_zero.mp hread.symm with hgood | hcontra
  · exact hgood
  · exact absurd hcontra hlive

end Boundary

/-! ## Layer 4 — the boundary pair kill at a crux -/

section CruxBoundary

variable {activeIndex : Type} {basisCount : ℕ}
variable {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin 6)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)}
variable {basisLabel : Fin basisCount → activeIndex}
variable {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
variable {leftInv : Matrix (Fin basisCount) (Fin 6) ℝ}

/-- **THE BOUNDARY PAIR KILL, THE CAPTURE FORM.**  Two distinct atom
axes that the capture frame kills cannot coexist when the residue trace
is less than two.  Both chart columns are nonzero residue-fixed
vectors, thus they are proportional, thus the chart kills a direction
supported on the atom pair, thus the two design atoms are parallel.  The
crux carries no parallel pair. -/
theorem SixThreeCrux.false_of_two_capture_kills (crux : SixThreeCrux)
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hrep : (chartPointOfDesign crux.design).chart
        * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (htrace : 2 ≤ Matrix.trace coeff)
    {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo)
    (hkillOne : captureFrame (tightBasisColumns tightDir basisLabel) coeff
      *ᵥ (Pi.single atomOne 1 : Fin 6 → ℝ) = 0)
    (hkillTwo : captureFrame (tightBasisColumns tightDir basisLabel) coeff
      *ᵥ (Pi.single atomTwo 1 : Fin 6 → ℝ) = 0) :
    False := by
  classical
  set basisColumns := tightBasisColumns tightDir basisLabel with hB
  set residue := captureResidue (chartPointOfDesign crux.design).chart
    basisColumns coeff with hresidue
  have hPsymm : ((chartPointOfDesign crux.design).chart)ᵀ
      = (chartPointOfDesign crux.design).chart := hdata.isSymmetric
  have hidem : (chartPointOfDesign crux.design).chart
      * (chartPointOfDesign crux.design).chart
      = (chartPointOfDesign crux.design).chart :=
    projectionOfDesign_mul_self crux.design
  have hPtrace : Matrix.trace (chartPointOfDesign crux.design).chart = 3 := by
    have h : Matrix.trace (projectionOfDesign crux.design)
        = ((3 : ℕ) : ℝ) := trace_projectionOfDesign crux.design
    norm_num at h
    exact h
  have hRsymm : residueᵀ = residue :=
    captureResidue_transpose hPsymm hidem hleft hrep
  have hRidem : residue * residue = residue :=
    captureResidue_mul_self hPsymm hidem hleft hrep
  have hRtrace : Matrix.trace residue
      = Matrix.trace (chartPointOfDesign crux.design).chart
        - Matrix.trace coeff :=
    captureResidue_trace hPsymm hidem hleft hrep
  have hRtraceLt : Matrix.trace residue < 2 := by
    rw [hRtrace, hPtrace]
    linarith
  have hfixed : ∀ atomIndex : Fin 6,
      captureFrame basisColumns coeff
          *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) = 0 →
      residue *ᵥ ((chartPointOfDesign crux.design).chart
          *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ))
        = (chartPointOfDesign crux.design).chart
          *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) := by
    intro atomIndex hkill
    have hcolumn : residue *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)
        = (chartPointOfDesign crux.design).chart
          *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) :=
      captureResidue_mulVec_single_eq_of_capture_kill hkill
    rw [← hcolumn, Matrix.mulVec_mulVec, hRidem]
  have hnonzero : ∀ atomIndex : Fin 6,
      (chartPointOfDesign crux.design).chart
        *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) ≠ 0 := by
    intro atomIndex hcontra
    have hdiag : (chartPointOfDesign crux.design).chart atomIndex atomIndex = 0 := by
      rw [← mulVec_single_one_apply (chartPointOfDesign crux.design).chart
        atomIndex atomIndex, hcontra]
      rfl
    have hgap := crux.chartGap_diagonal_pos atomIndex
    simp only [chartStationaryGap, Matrix.sub_apply,
      Matrix.diagonal_apply_eq] at hgap
    rw [hdiag] at hgap
    have hweight := hdata.weight_pos atomIndex
    linarith
  have hparallel := parallel_of_fixed_of_trace_lt_two hRsymm hRidem hRtraceLt
    (hfixed atomOne hkillOne) (hfixed atomTwo hkillTwo) (hnonzero atomOne)
  set scale : ℝ := (((chartPointOfDesign crux.design).chart
        *ᵥ (Pi.single atomOne 1 : Fin 6 → ℝ))
      ⬝ᵥ ((chartPointOfDesign crux.design).chart
        *ᵥ (Pi.single atomTwo 1 : Fin 6 → ℝ)))
    / (((chartPointOfDesign crux.design).chart
        *ᵥ (Pi.single atomOne 1 : Fin 6 → ℝ))
      ⬝ᵥ ((chartPointOfDesign crux.design).chart
        *ᵥ (Pi.single atomOne 1 : Fin 6 → ℝ))) with hscale
  set direction : Fin 6 → ℝ := (Pi.single atomTwo 1 : Fin 6 → ℝ)
    - scale • (Pi.single atomOne 1 : Fin 6 → ℝ) with hdirection
  have hkernel : projectionOfDesign crux.design *ᵥ direction = 0 := by
    have hcompute : (chartPointOfDesign crux.design).chart *ᵥ direction = 0 := by
      rw [hdirection, Matrix.mulVec_sub, Matrix.mulVec_smul, hparallel,
        sub_self]
    exact hcompute
  have hsecondNonzero : direction atomTwo ≠ 0 := by
    rw [hdirection]
    simp [Ne.symm hne]
  have hsupport : ∀ atomIndex : Fin 6, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      direction atomIndex = 0 := by
    intro atomIndex hone htwo
    rw [hdirection]
    simp [hone, htwo]
  exact crux.hasNoParallelPair
    (hasParallelPair_of_projectionOfDesign_mulVec_eq_zero_on_support_pair
      crux.design hkernel hne hsecondNonzero hsupport)

/-- **THE BOUNDARY PAIR KILL.**  Two distinct atoms of zero shifted
weight cannot coexist at a capture trace of two or more. -/
theorem SixThreeCrux.false_of_two_boundary_atoms (crux : SixThreeCrux)
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (hrep : (chartPointOfDesign crux.design).chart
        * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (htrace : 2 ≤ Matrix.trace coeff)
    {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo)
    (hboundOne : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne = 0)
    (hboundTwo : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomTwo = 0) :
    False :=
  crux.false_of_two_capture_kills hdata hrep hleft htrace hne
    (captureFrame_mulVec_single_eq_zero_of_boundary hdata hspan hrep hleft
      hboundOne)
    (captureFrame_mulVec_single_eq_zero_of_boundary hdata hspan hrep hleft
      hboundTwo)

/-- **THE TRACE-GAP INTERIORITY.**  When the capture trace reaches the
chart rank the residue has trace zero, thus a boundary chart column is
zero, which the all-heavy floor refuses.  Every shifted weight is then
positive. -/
theorem SixThreeCrux.shifted_weight_pos_of_capture_trace_rank (crux : SixThreeCrux)
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (hrep : (chartPointOfDesign crux.design).chart
        * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (htrace : 3 ≤ Matrix.trace coeff) (atomIndex : Fin 6) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex := by
  classical
  rcases (capture_diagonal_nonneg_of_isChartStationaryData hdata
    atomIndex).lt_or_eq with hpos | heq
  · exact hpos
  exfalso
  set basisColumns := tightBasisColumns tightDir basisLabel with hB
  set residue := captureResidue (chartPointOfDesign crux.design).chart
    basisColumns coeff with hresidue
  have hPsymm : ((chartPointOfDesign crux.design).chart)ᵀ
      = (chartPointOfDesign crux.design).chart := hdata.isSymmetric
  have hidem : (chartPointOfDesign crux.design).chart
      * (chartPointOfDesign crux.design).chart
      = (chartPointOfDesign crux.design).chart :=
    projectionOfDesign_mul_self crux.design
  have hPtrace : Matrix.trace (chartPointOfDesign crux.design).chart = 3 := by
    have h : Matrix.trace (projectionOfDesign crux.design)
        = ((3 : ℕ) : ℝ) := trace_projectionOfDesign crux.design
    norm_num at h
    exact h
  have hRsymm : residueᵀ = residue :=
    captureResidue_transpose hPsymm hidem hleft hrep
  have hRidem : residue * residue = residue :=
    captureResidue_mul_self hPsymm hidem hleft hrep
  have hRtrace : Matrix.trace residue
      = Matrix.trace (chartPointOfDesign crux.design).chart
        - Matrix.trace coeff :=
    captureResidue_trace hPsymm hidem hleft hrep
  have hRtraceLt : Matrix.trace residue < 1 := by
    rw [hRtrace, hPtrace]
    linarith
  have hkill := captureFrame_mulVec_single_eq_zero_of_boundary hdata hspan
    hrep hleft heq.symm
  have hcolumn : residue *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)
      = (chartPointOfDesign crux.design).chart
        *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) :=
    captureResidue_mulVec_single_eq_of_capture_kill hkill
  have hfix : residue *ᵥ ((chartPointOfDesign crux.design).chart
        *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ))
      = (chartPointOfDesign crux.design).chart
        *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) := by
    rw [← hcolumn, Matrix.mulVec_mulVec, hRidem]
  have hzeroColumn : (chartPointOfDesign crux.design).chart
      *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) = 0 :=
    eq_zero_of_fixed_of_trace_lt_one hRsymm hRidem hRtraceLt hfix
  have hdiag : (chartPointOfDesign crux.design).chart atomIndex atomIndex = 0 := by
    rw [← mulVec_single_one_apply (chartPointOfDesign crux.design).chart
      atomIndex atomIndex, hzeroColumn]
    rfl
  have hgap := crux.chartGap_diagonal_pos atomIndex
  simp only [chartStationaryGap, Matrix.sub_apply,
    Matrix.diagonal_apply_eq] at hgap
  rw [hdiag] at hgap
  have hweight := hdata.weight_pos atomIndex
  linarith

/-- **THE PROPORTIONAL-ROW INTERIOR LAW.**  Two distinct atoms whose
basis rows are proportional are BOTH interior.  The pair direction is a
basis null direction, thus the capture frame kills it, thus the capture
frame kills the second atom axis as soon as it kills the first.  A
vanished shifted weight at the first atom would thus make both atoms
boundary atoms, and the boundary pair kill refuses that. -/
theorem SixThreeCrux.shifted_weight_pos_of_pair_null (crux : SixThreeCrux)
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (hrep : (chartPointOfDesign crux.design).chart
        * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (htrace : 2 ≤ Matrix.trace coeff)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hclone : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) atomTwo
        = scale * tightDir (basisLabel slot) atomOne) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne := by
  classical
  rcases (capture_diagonal_nonneg_of_isChartStationaryData hdata
    atomOne).lt_or_eq with hpos | heq
  · exact hpos
  exfalso
  set basisColumns := tightBasisColumns tightDir basisLabel with hB
  have hnull : basisColumnsᵀ
      *ᵥ ((Pi.single atomTwo 1 : Fin 6 → ℝ)
        - scale • (Pi.single atomOne 1 : Fin 6 → ℝ)) = 0 :=
    transpose_basisColumns_mulVec_eq_zero
      (basis_dot_pairDirection_eq_zero hclone)
  have hframeNull : captureFrame basisColumns coeff
      *ᵥ ((Pi.single atomTwo 1 : Fin 6 → ℝ)
        - scale • (Pi.single atomOne 1 : Fin 6 → ℝ)) = 0 :=
    captureFrame_mulVec_eq_zero_of_basis_dot hnull
  have hframeOne : captureFrame basisColumns coeff
      *ᵥ (Pi.single atomOne 1 : Fin 6 → ℝ) = 0 :=
    captureFrame_mulVec_single_eq_zero_of_boundary hdata hspan hrep hleft
      heq.symm
  have hframeTwo : captureFrame basisColumns coeff
      *ᵥ (Pi.single atomTwo 1 : Fin 6 → ℝ) = 0 := by
    have hsplit : (Pi.single atomTwo 1 : Fin 6 → ℝ)
        = ((Pi.single atomTwo 1 : Fin 6 → ℝ)
            - scale • (Pi.single atomOne 1 : Fin 6 → ℝ))
          + scale • (Pi.single atomOne 1 : Fin 6 → ℝ) := by
      abel
    rw [hsplit, Matrix.mulVec_add, Matrix.mulVec_smul, hframeNull, hframeOne,
      smul_zero, add_zero]
  exact crux.false_of_two_capture_kills hdata hrep hleft htrace hne hframeOne
    hframeTwo

/-- The proportional-row interior law at the SECOND atom of the pair. -/
theorem SixThreeCrux.shifted_weight_pos_of_pair_null_right (crux : SixThreeCrux)
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (hrep : (chartPointOfDesign crux.design).chart
        * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (htrace : 2 ≤ Matrix.trace coeff)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hscale : scale ≠ 0)
    (hclone : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) atomTwo
        = scale * tightDir (basisLabel slot) atomOne) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomTwo := by
  refine crux.shifted_weight_pos_of_pair_null hdata hspan hrep hleft htrace
    (scale := scale⁻¹) (Ne.symm hne) ?_
  intro slot
  rw [hclone slot, ← mul_assoc, inv_mul_cancel₀ hscale, one_mul]

end CruxBoundary

/-! ## Layer 5 — the three rung frames -/

section FrameReadings

variable {crux : SixThreeCrux}

/-- **THE RANK-FOUR BOUNDARY PAIR KILL.** -/
theorem RankFourFrame.false_of_two_boundary_atoms (frame : RankFourFrame crux)
    {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo)
    (hboundOne : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne = 0)
    (hboundTwo : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomTwo = 0) :
    False :=
  crux.false_of_two_boundary_atoms frame.hdata frame.hspan
    frame.hrepresentation frame.hleft (le_of_eq frame.htrace.symm) hne
    hboundOne hboundTwo

/-- **THE RANK-FOUR PROPORTIONAL-ROW INTERIOR LAW.** -/
theorem RankFourFrame.shifted_weight_pos_of_pair_null (frame : RankFourFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hclone : ∀ slot : Fin 4,
      frame.tightDir (frame.basisLabel slot) atomTwo
        = scale * frame.tightDir (frame.basisLabel slot) atomOne) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne :=
  crux.shifted_weight_pos_of_pair_null frame.hdata frame.hspan
    frame.hrepresentation frame.hleft (le_of_eq frame.htrace.symm) hne hclone

/-- **AT MOST ONE BOUNDARY ATOM AT A RANK-FOUR FRAME.** -/
theorem RankFourFrame.boundary_card_le_one (frame : RankFourFrame crux) :
    (Finset.univ.filter fun atomIndex : Fin 6 =>
        chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex = 0).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro atomOne hmemOne atomTwo hmemTwo
  rw [Finset.mem_filter] at hmemOne hmemTwo
  by_contra hne
  exact frame.false_of_two_boundary_atoms hne hmemOne.2 hmemTwo.2

/-- **FIVE INTERIOR ATOMS AT A RANK-FOUR FRAME.**  The shifted weights
are nonnegative, thus every atom off the single boundary atom is
interior. -/
theorem RankFourFrame.five_le_interior_card (frame : RankFourFrame crux) :
    5 ≤ (Finset.univ.filter fun atomIndex : Fin 6 =>
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex).card := by
  classical
  have hsplit : (Finset.univ.filter fun atomIndex : Fin 6 =>
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
      = Finset.univ \ (Finset.univ.filter fun atomIndex : Fin 6 =>
        chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex = 0) := by
    ext atomIndex
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hpos hzero
      rw [hzero] at hpos
      exact lt_irrefl _ hpos
    · intro hnot
      rcases (capture_diagonal_nonneg_of_isChartStationaryData frame.hdata
        atomIndex).lt_or_eq with hpos | heq
      · exact hpos
      · exact absurd heq.symm hnot
  rw [hsplit]
  have hcard : (Finset.univ : Finset (Fin 6)).card = 6 := by simp
  have hle := frame.boundary_card_le_one
  have hkey := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (Finset.univ.filter fun atomIndex : Fin 6 =>
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0))
  omega

/-- **THE RANK-FIVE BOUNDARY PAIR KILL.**  The rank-five capture trace
is two or three, thus the residue trace is at most one either way. -/
theorem RankFiveFrame.false_of_two_boundary_atoms (frame : RankFiveFrame crux)
    {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo)
    (hboundOne : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne = 0)
    (hboundTwo : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomTwo = 0) :
    False := by
  have htrace : 2 ≤ Matrix.trace frame.coeff := by
    rcases frame.htrace with h | h
    · exact le_of_eq h.symm
    · have hthree : (2 : ℝ) ≤ 3 := by norm_num
      rw [h]
      exact hthree
  exact crux.false_of_two_boundary_atoms frame.hdata frame.hspan
    frame.hrepresentation frame.hleft htrace hne hboundOne hboundTwo

/-- **THE RANK-FIVE PROPORTIONAL-ROW INTERIOR LAW.** -/
theorem RankFiveFrame.shifted_weight_pos_of_pair_null (frame : RankFiveFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hclone : ∀ slot : Fin 5,
      frame.tightDir (frame.basisLabel slot) atomTwo
        = scale * frame.tightDir (frame.basisLabel slot) atomOne) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne := by
  have htrace : 2 ≤ Matrix.trace frame.coeff := by
    rcases frame.htrace with h | h
    · exact le_of_eq h.symm
    · have hthree : (2 : ℝ) ≤ 3 := by norm_num
      rw [h]
      exact hthree
  exact crux.shifted_weight_pos_of_pair_null frame.hdata frame.hspan
    frame.hrepresentation frame.hleft htrace hne hclone

/-- **AT MOST ONE BOUNDARY ATOM AT A RANK-FIVE FRAME.** -/
theorem RankFiveFrame.boundary_card_le_one (frame : RankFiveFrame crux) :
    (Finset.univ.filter fun atomIndex : Fin 6 =>
        chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex = 0).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro atomOne hmemOne atomTwo hmemTwo
  rw [Finset.mem_filter] at hmemOne hmemTwo
  by_contra hne
  exact frame.false_of_two_boundary_atoms hne hmemOne.2 hmemTwo.2

/-- **THE RANK-SIX INTERIORITY THROUGH THE RESIDUE.**  A rank-six frame
captures the whole chart trace, thus its residue is trace free, thus no
atom sits at the boundary. -/
theorem RankSixFrame.shifted_weight_pos_of_residue (frame : RankSixFrame crux)
    (atomIndex : Fin 6) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex :=
  crux.shifted_weight_pos_of_capture_trace_rank frame.hdata frame.hspan
    frame.hrepresentation frame.hleft (le_of_eq frame.htrace.symm) atomIndex

end FrameReadings

/-! ## Layer 6 — the clone closure with no interiority -/

section CloneClosure

variable {crux : SixThreeCrux}

/-- **THE DATUM CLONE INTERIOR LAW.**  Both atoms of a clone pair of a
rank-four outer datum are interior. -/
theorem RankFourOuterData.shifted_weight_pos_of_clone
    (data : RankFourOuterData crux) {atomOne atomTwo : Fin 6} {scale : ℝ}
    (hne : atomOne ≠ atomTwo)
    (hclone : ∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) atomTwo
        = scale * data.frame.tightDir (data.frame.basisLabel slot) atomOne) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne :=
  data.frame.shifted_weight_pos_of_pair_null hne hclone

/-- **THE CLONE CLOSURE WITH NO INTERIORITY.**  A full clone pair
carries a zero shifted weight through idempotence, while the
proportional-row interior law makes every clone atom interior.  Thus the
clone residue reduces to its THIN half, with no interiority hypothesis
at all. -/
theorem rankFourOuterCloneClosed_of_thin
    (hthin : RankFourOuterThinCloneClosed) :
    RankFourOuterCloneClosed := by
  classical
  intro crux data atomOne atomTwo scale hneAtoms hOneU hOneV hTwoU hTwoV
    hscaleUnit hclone hweight
  by_cases hfree : ∃ freeSlot : Fin 4,
      atomOne ∉ data.frame.activeSubset (data.frame.basisLabel freeSlot)
        ∧ atomTwo ∉ data.frame.activeSubset (data.frame.basisLabel freeSlot)
  · obtain ⟨freeSlot, hone, htwo⟩ := hfree
    exact hthin crux data atomOne atomTwo scale freeSlot hneAtoms hOneU hOneV
      hTwoU hTwoV hscaleUnit hclone hweight hone htwo
  · push Not at hfree
    have hfull : ∀ slot : Fin 4,
        atomOne ∈ data.frame.activeSubset (data.frame.basisLabel slot)
          ∨ atomTwo ∈ data.frame.activeSubset (data.frame.basisLabel slot) := by
      intro slot
      by_cases hone : atomOne ∈ data.frame.activeSubset
        (data.frame.basisLabel slot)
      · exact Or.inl hone
      · exact Or.inr (hfree slot hone)
    have hscaleNe : scale ≠ 0 := by
      rcases hscaleUnit with hEq | hEq
      · rw [hEq]; norm_num
      · rw [hEq]; norm_num
    obtain ⟨liveSlot, hliveSlot⟩ := data.exists_live_slot atomOne
    have hshiftedWeight : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo := by
      rw [hweight]
    have hboundary := clone_shifted_weight_eq_zero_of_full_carrier
      data.frame.hdata data.frame.hvalueNeg data.frame.hmemAll
      data.frame.hrepresentation data.frame.hidempotent hscaleNe hclone
      hshiftedWeight hfull hliveSlot
    have hinterior := data.shifted_weight_pos_of_clone hneAtoms hclone
    linarith

/-- **THE SHARPENED RANK-FOUR DISCHARGE.**  Closure one of the rank-four
rung follows from the off-pair residue, the THIN clone residue, the
triple residue and the interior residue.  The clone half now spends NO
interiority. -/
theorem rankFourSupportTwoClosed_of_thin_triple_interior
    (hoff : RankFourOuterOffPairCircuitClosed)
    (hthin : RankFourOuterThinCloneClosed)
    (htriple : RankFourOuterTripleNullClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
      (atomIndex : Fin 6),
      2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_clone_triple_interior hoff
    (rankFourOuterCloneClosed_of_thin hthin) htriple hinterior

end CloneClosure

/-! ## Layer 7 — the full clone dies at every rung -/

section FullClone

variable {crux : SixThreeCrux}

/-- **THE CLONE BOUNDARY LAW AT THE RANK-FOUR FRAME.**  A clone pair
whose two carriers exhaust the four slots sits at the boundary of the
shifted weight. -/
theorem RankFourFrame.clone_boundary_of_full_carrier (frame : RankFourFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hscaleNe : scale ≠ 0)
    (hclone : ∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne)
    (hweight : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo)
    (hfull : ∀ slot : Fin 4,
      atomOne ∈ frame.activeSubset (frame.basisLabel slot)
        ∨ atomTwo ∈ frame.activeSubset (frame.basisLabel slot)) :
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne = 0 := by
  obtain ⟨liveSlot, hliveSlot⟩ := frame.exists_live_slot atomOne
  exact clone_shifted_weight_eq_zero_of_full_carrier frame.hdata
    frame.hvalueNeg frame.hmemAll frame.hrepresentation frame.hidempotent
    hscaleNe hclone hweight hfull hliveSlot

/-- **THE RANK-FOUR FULL CLONE KILL.**  A full clone pair is a boundary
pair by idempotence and an interior pair by the proportional-row law. -/
theorem RankFourFrame.false_of_full_clone (frame : RankFourFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hscaleNe : scale ≠ 0)
    (hclone : ∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne)
    (hweight : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo)
    (hfull : ∀ slot : Fin 4,
      atomOne ∈ frame.activeSubset (frame.basisLabel slot)
        ∨ atomTwo ∈ frame.activeSubset (frame.basisLabel slot)) :
    False := by
  have hboundary := frame.clone_boundary_of_full_carrier hscaleNe hclone
    hweight hfull
  have hinterior := frame.shifted_weight_pos_of_pair_null hne hclone
  linarith

/-- **THE RANK-FIVE FULL CLONE KILL.** -/
theorem RankFiveFrame.false_of_full_clone (frame : RankFiveFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hscaleNe : scale ≠ 0)
    (hclone : ∀ slot : Fin 5, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne)
    (hweight : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo)
    (hfull : ∀ slot : Fin 5,
      atomOne ∈ frame.activeSubset (frame.basisLabel slot)
        ∨ atomTwo ∈ frame.activeSubset (frame.basisLabel slot)) :
    False := by
  have hboundary := frame.clone_boundary_of_full_carrier hscaleNe hclone
    hweight hfull
  have hinterior := frame.shifted_weight_pos_of_pair_null hne hclone
  linarith

/-- **THE RANK-SIX FULL CLONE KILL.**  The rank-six residue is trace
free, thus no atom sits at the boundary and the kill needs no
distinctness. -/
theorem RankSixFrame.false_of_full_clone (frame : RankSixFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hscaleNe : scale ≠ 0)
    (hclone : ∀ slot : Fin 6, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne)
    (hweight : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo)
    (hfull : ∀ slot : Fin 6,
      atomOne ∈ frame.activeSubset (frame.basisLabel slot)
        ∨ atomTwo ∈ frame.activeSubset (frame.basisLabel slot)) :
    False := by
  have hboundary := frame.clone_boundary_of_full_carrier hscaleNe hclone
    hweight hfull
  have hinterior := frame.shifted_weight_pos_of_residue atomOne
  linarith

/-- **THE INTERIORITY SUPPLY OFF A BOUNDARY ATOM.**  Once one rank-four
atom sits at the boundary, every other atom is interior. -/
theorem RankFourFrame.shifted_weight_pos_of_ne_boundary
    (frame : RankFourFrame crux) {boundaryAtom atomIndex : Fin 6}
    (hbound : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight boundaryAtom = 0)
    (hne : atomIndex ≠ boundaryAtom) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex := by
  rcases (capture_diagonal_nonneg_of_isChartStationaryData frame.hdata
    atomIndex).lt_or_eq with hpos | heq
  · exact hpos
  · exact absurd (frame.false_of_two_boundary_atoms hne heq.symm hbound)
      not_false

/-- **THE INTERIORITY SUPPLY OFF A BOUNDARY ATOM AT RANK FIVE.** -/
theorem RankFiveFrame.shifted_weight_pos_of_ne_boundary
    (frame : RankFiveFrame crux) {boundaryAtom atomIndex : Fin 6}
    (hbound : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight boundaryAtom = 0)
    (hne : atomIndex ≠ boundaryAtom) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex := by
  rcases (capture_diagonal_nonneg_of_isChartStationaryData frame.hdata
    atomIndex).lt_or_eq with hpos | heq
  · exact hpos
  · exact absurd (frame.false_of_two_boundary_atoms hne heq.symm hbound)
      not_false

end FullClone

end Gtz

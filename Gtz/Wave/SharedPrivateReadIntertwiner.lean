import Gtz.Wave.SharedPrivateGramCommutation
import Gtz.Wave.SharedPrivateKernelFactor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The read intertwiner — the slot frame carries the whole ambient calculus

The kernel-minor budget reads the conjugated coefficient matrix through
six supported vectors, one for each atom.  The reads it consumes hold
on the carriers only, thus the frame exports a fragment of the ambient
laws.  This module exports the whole thing.

The intertwiner.  Collect the six read vectors as the columns of one
read matrix `Z`.  The exchange law of the Gram core then gives
`S Z = Z P`, where `S` is the conjugated coefficient matrix on the
slots and `P` is the chart projection on the atoms.  One equation
replaces the six carrier reads, and it holds off the carriers as well.

The two Gram products.  The row Gram `Zᵀ Z` is the multiplier assembly,
thus its diagonal is one sixth and its trace is one.  The column Gram
`W = Z Zᵀ` is the read weight matrix.  The intertwiner makes `W`
commute with `S`, the trace of `W` is one, the diagonal of `W` is the
Gram core diagonal, and `W` has a trivial kernel.  Thus the Gram core
diagonal sums to one.

The faithful assembly.  At basis count six the basis columns are a
square left-invertible matrix, thus the coefficient matrix is conjugate
to the chart projection and its trace is three.  The same squareness
makes the multiplier assembly kernel-free.  A zero shifted weight then
kills the whole chart column at that atom, and the all-heavy gap floor
refuses it.  Thus every shifted weight is positive at basis count six,
with no trace hypothesis.

The narrowed deficit.  The pin atom has multiplicity one, thus the
profile mass is at least two.  A mass of at most three then pins the
multiplicity-one count to one and the multiplicity-two count to at most
one.  Together with the interior window and the support mass, these
facts narrow the two landed deficit residues, and one dispatch carries
the narrowing through to the generic kill.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.columnGram_quadForm`, `Gtz.rowGram_quadForm`,
  `Gtz.selfDot_nonneg`, `Gtz.eq_zero_of_selfDot_eq_zero` — the Gram
  quadratic forms.
* `Gtz.row_eq_zero_of_quadForm_nonneg_of_diag_zero` — **THE PSD
  RIGIDITY.**
* `Gtz.intertwiner_columnGram_commute`,
  `Gtz.intertwiner_transpose_law`, `Gtz.intertwiner_complement`,
  `Gtz.intertwiner_capture_gram` — the intertwiner calculus.
* `Gtz.projector_capture_sandwich`,
  `Gtz.projector_capture_quadForm_nonneg`,
  `Gtz.projector_capture_transpose` — the commuting capture calculus.
* `Gtz.ReadIntertwiner` with
  `Gtz.SharedPrivateData.readIntertwiner` — **THE READ FRAME.**
* `Gtz.ReadIntertwiner.weightMat` with `weightMat_transpose`,
  `weightMat_commute`, `weightMat_apply`, `weightMat_diagonal`,
  `trace_weightMat`, `weightMat_kernelFree`,
  `weightMat_eq_zero_of_disjoint_support`,
  `gramDiag_sum_one` — **THE READ WEIGHT MATRIX.**
* `Gtz.ReadIntertwiner.capture_weightMat_diagonal`,
  `Gtz.ReadIntertwiner.complement_weightMat_diagonal`,
  `Gtz.ReadIntertwiner.trace_capture_weightMat` (the value plus one
  sixth), `Gtz.ReadIntertwiner.trace_complement_weightMat` (five sixths
  minus the value), with the two diagonal floors — **THE CAPTURE
  LEDGER.**
* `Gtz.SharedPrivateData.trace_eq_three_of_basisCount_six` — the trace
  is three at basis count six.
* `Gtz.SharedPrivateData.assembly_kernelFree_of_basisCount_six` and
  `Gtz.SharedPrivateData.shifted_weight_pos_of_basisCount_six` — **THE
  INTERIOR WINDOW AT BASIS COUNT SIX**, with no trace hypothesis.
* `Gtz.SharedPrivateData.deficit_profile_of_mass` — the pin pins the
  profile.
* `Gtz.SharedPrivateDeficitSixInteriorClosed`,
  `Gtz.SharedPrivateDeficitComplementInteriorClosed`,
  `Gtz.sharedPrivateDeficitClosed_of_interior_residues` and
  `Gtz.sharedPrivateKilled_of_interior_strata` — **THE INTERIOR
  DEFICIT DISPATCH.**

## Vacuity

The matrix statements are unconditional.  The data-facing statements
quantify over shared-private data, and no datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the Gram quadratic forms -/

/-- The self dot product is nonnegative. -/
theorem selfDot_nonneg {slotCount : ℕ} (vec : Fin slotCount → ℝ) :
    0 ≤ vec ⬝ᵥ vec := by
  rw [dotProduct]
  exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- A vanished self dot product kills the vector. -/
theorem eq_zero_of_selfDot_eq_zero {slotCount : ℕ} {vec : Fin slotCount → ℝ}
    (hzero : vec ⬝ᵥ vec = 0) : vec = 0 := by
  funext slot
  rw [dotProduct] at hzero
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun probe _ =>
    mul_self_nonneg (vec probe)).mp hzero slot (Finset.mem_univ slot)
  exact mul_self_eq_zero.mp hterm

/-- The quadratic form of a Gram product is the square of the
transposed image. -/
theorem gram_quadForm {rowCount colCount : ℕ}
    (mat : Matrix (Fin colCount) (Fin rowCount) ℝ) (vec : Fin rowCount → ℝ) :
    vec ⬝ᵥ ((matᵀ * mat) *ᵥ vec) = (mat *ᵥ vec) ⬝ᵥ (mat *ᵥ vec) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **THE COLUMN GRAM FORM.**  The quadratic form of `Z Zᵀ` reads the
transposed image. -/
theorem columnGram_quadForm {rowCount colCount : ℕ}
    (readMat : Matrix (Fin rowCount) (Fin colCount) ℝ)
    (vec : Fin rowCount → ℝ) :
    vec ⬝ᵥ ((readMat * readMatᵀ) *ᵥ vec)
      = (readMatᵀ *ᵥ vec) ⬝ᵥ (readMatᵀ *ᵥ vec) := by
  have hform := gram_quadForm readMatᵀ vec
  rwa [Matrix.transpose_transpose] at hform

/-- **THE ROW GRAM FORM.**  The quadratic form of `Zᵀ Z` reads the
plain image. -/
theorem rowGram_quadForm {rowCount colCount : ℕ}
    (readMat : Matrix (Fin rowCount) (Fin colCount) ℝ)
    (vec : Fin colCount → ℝ) :
    vec ⬝ᵥ ((readMatᵀ * readMat) *ᵥ vec)
      = (readMat *ᵥ vec) ⬝ᵥ (readMat *ᵥ vec) :=
  gram_quadForm readMat vec

/-- **THE PSD RIGIDITY.**  A symmetric matrix with a nonnegative
quadratic form and a zero diagonal entry has a zero row.  The two-slot
probe prices the off-diagonal entry against the diagonal, and the
scaled choice of the second coordinate refuses a nonzero entry. -/
theorem row_eq_zero_of_quadForm_nonneg_of_diag_zero {slotCount : ℕ}
    {form : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : formᵀ = form)
    (hquad : ∀ probe : Fin slotCount → ℝ, 0 ≤ probe ⬝ᵥ (form *ᵥ probe))
    {rowSlot : Fin slotCount} (hdiag : form rowSlot rowSlot = 0)
    (colSlot : Fin slotCount) : form rowSlot colSlot = 0 := by
  classical
  rcases eq_or_ne rowSlot colSlot with rfl | hne
  · exact hdiag
  · have hcross : form colSlot rowSlot = form rowSlot colSlot := by
      have hentry := congrFun (congrFun hsymm rowSlot) colSlot
      rwa [Matrix.transpose_apply] at hentry
    have hcolDiag : 0 ≤ form colSlot colSlot := by
      have hprobe := hquad (Pi.single colSlot 1)
      rwa [single_dotProduct_mulVec_single] at hprobe
    have hpos : (0 : ℝ) < 1 + form colSlot colSlot := by linarith
    set scale : ℝ := (1 + form colSlot colSlot)⁻¹ with hscaleDef
    have hscale : scale * (1 + form colSlot colSlot) = 1 :=
      inv_mul_cancel₀ hpos.ne'
    have hscalePos : 0 < scale := inv_pos.mpr hpos
    set gap : ℝ := form rowSlot colSlot with hgapDef
    set probe : Fin slotCount → ℝ := fun slot =>
      if slot = rowSlot then 1 else if slot = colSlot then -(gap * scale) else 0
      with hprobeDef
    have hprobeRow : probe rowSlot = 1 := by simp [hprobeDef]
    have hprobeCol : probe colSlot = -(gap * scale) := by
      simp [hprobeDef, hne.symm]
    have hprobeSupp : ∀ slot, slot ≠ rowSlot → slot ≠ colSlot → probe slot = 0 := by
      intro slot hone htwo
      simp [hprobeDef, hone, htwo]
    have hmul : ∀ slot : Fin slotCount, (form *ᵥ probe) slot
        = form slot rowSlot * 1 + form slot colSlot * -(gap * scale) := by
      intro slot
      rw [pair_mulVec_apply form hne hprobeSupp slot, hprobeRow, hprobeCol]
    have hq := hquad probe
    rw [pair_dotProduct hne hprobeSupp, hmul rowSlot, hmul colSlot,
      hprobeRow, hprobeCol] at hq
    have hexpand : (1 : ℝ) * (form rowSlot rowSlot * 1
          + form rowSlot colSlot * -(gap * scale))
        + -(gap * scale) * (form colSlot rowSlot * 1
          + form colSlot colSlot * -(gap * scale))
        = gap ^ 2 * scale * (scale * form colSlot colSlot - 2) := by
      rw [hdiag, hcross, ← hgapDef]
      ring
    rw [hexpand] at hq
    have hcap : scale * form colSlot colSlot - 2 ≤ -1 := by nlinarith [hscale]
    have hnn : 0 ≤ gap ^ 2 * scale := mul_nonneg (sq_nonneg gap) hscalePos.le
    have hchain : gap ^ 2 * scale * (scale * form colSlot colSlot - 2)
        ≤ gap ^ 2 * scale * (-1) := mul_le_mul_of_nonneg_left hcap hnn
    have hprodZero : gap ^ 2 * scale = 0 := le_antisymm (by linarith) hnn
    have hsquare : gap ^ 2 = 0 := by
      rcases mul_eq_zero.mp hprodZero with hleft | hright
      · exact hleft
      · exact absurd hright hscalePos.ne'
    exact sq_eq_zero_iff.mp hsquare

/-! ## Layer 2 — the intertwiner calculus -/

/-- The transposed intertwiner law. -/
theorem intertwiner_transpose_law {rowCount colCount : ℕ}
    {slotProj : Matrix (Fin rowCount) (Fin rowCount) ℝ}
    {atomProj : Matrix (Fin colCount) (Fin colCount) ℝ}
    {readMat : Matrix (Fin rowCount) (Fin colCount) ℝ}
    (hslotSymm : slotProjᵀ = slotProj) (hatomSymm : atomProjᵀ = atomProj)
    (hinter : slotProj * readMat = readMat * atomProj) :
    readMatᵀ * slotProj = atomProj * readMatᵀ := by
  have htrans := congrArg Matrix.transpose hinter
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, hslotSymm, hatomSymm]
    at htrans

/-- **THE INTERTWINED COMMUTATION.**  An intertwiner between two
symmetric matrices makes the column Gram commute with the left one.
This is the reduced form of the ambient commutation. -/
theorem intertwiner_columnGram_commute {rowCount colCount : ℕ}
    {slotProj : Matrix (Fin rowCount) (Fin rowCount) ℝ}
    {atomProj : Matrix (Fin colCount) (Fin colCount) ℝ}
    {readMat : Matrix (Fin rowCount) (Fin colCount) ℝ}
    (hslotSymm : slotProjᵀ = slotProj) (hatomSymm : atomProjᵀ = atomProj)
    (hinter : slotProj * readMat = readMat * atomProj) :
    slotProj * (readMat * readMatᵀ) = (readMat * readMatᵀ) * slotProj := by
  have hleft : slotProj * (readMat * readMatᵀ)
      = readMat * atomProj * readMatᵀ := by
    rw [← Matrix.mul_assoc, hinter]
  have hright : (readMat * readMatᵀ) * slotProj
      = readMat * atomProj * readMatᵀ := by
    rw [Matrix.mul_assoc,
      intertwiner_transpose_law hslotSymm hatomSymm hinter, ← Matrix.mul_assoc]
  rw [hleft, hright]

/-- The complement inherits the intertwiner. -/
theorem intertwiner_complement {rowCount colCount : ℕ}
    {slotProj : Matrix (Fin rowCount) (Fin rowCount) ℝ}
    {atomProj : Matrix (Fin colCount) (Fin colCount) ℝ}
    {readMat : Matrix (Fin rowCount) (Fin colCount) ℝ}
    (hinter : slotProj * readMat = readMat * atomProj) :
    (1 - slotProj) * readMat = readMat * (1 - atomProj) := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hinter]

/-- **THE CAPTURED GRAM.**  The intertwiner moves the left projector to
the right of the row Gram. -/
theorem intertwiner_capture_gram {rowCount colCount : ℕ}
    {slotProj : Matrix (Fin rowCount) (Fin rowCount) ℝ}
    {atomProj : Matrix (Fin colCount) (Fin colCount) ℝ}
    {readMat : Matrix (Fin rowCount) (Fin colCount) ℝ}
    (hinter : slotProj * readMat = readMat * atomProj) :
    readMatᵀ * (slotProj * readMat) = (readMatᵀ * readMat) * atomProj := by
  rw [hinter, ← Matrix.mul_assoc]

/-- A commuting projector sandwiches the form it commutes with. -/
theorem projector_capture_sandwich {slotCount : ℕ}
    {proj form : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hidem : proj * proj = proj) (hcomm : proj * form = form * proj) :
    proj * form = proj * form * proj := by
  rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hidem]

/-- **THE CAPTURED FORM.**  A symmetric projector times a commuting
nonnegative form is a nonnegative form. -/
theorem projector_capture_quadForm_nonneg {slotCount : ℕ}
    {proj form : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : projᵀ = proj) (hidem : proj * proj = proj)
    (hcomm : proj * form = form * proj)
    (hform : ∀ probe : Fin slotCount → ℝ, 0 ≤ probe ⬝ᵥ (form *ᵥ probe))
    (probe : Fin slotCount → ℝ) :
    0 ≤ probe ⬝ᵥ ((proj * form) *ᵥ probe) := by
  have hsandwich := projector_capture_sandwich hidem hcomm
  have hvec : probe ᵥ* proj = proj *ᵥ probe := by
    conv_lhs => rw [← hsymm]
    rw [Matrix.vecMul_transpose]
  have hsplit : probe ⬝ᵥ ((proj * form) *ᵥ probe)
      = (proj *ᵥ probe) ⬝ᵥ (form *ᵥ (proj *ᵥ probe)) := by
    rw [hsandwich, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, hvec]
  rw [hsplit]
  exact hform _

/-- The captured form is symmetric. -/
theorem projector_capture_transpose {slotCount : ℕ}
    {proj form : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymmProj : projᵀ = proj) (hsymmForm : formᵀ = form)
    (hcomm : proj * form = form * proj) :
    (proj * form)ᵀ = proj * form := by
  rw [Matrix.transpose_mul, hsymmForm, hsymmProj, ← hcomm]

/-! ## Layer 3 — the read frame of a diagonal-Gram datum -/

/-- **THE READ FRAME.**  At a diagonal Gram core the datum carries a
symmetric idempotent on the slots, a read matrix whose columns are the
six read vectors, and the intertwiner law between the two projections.
The row Gram of the read matrix is the multiplier assembly. -/
structure ReadIntertwiner {crux : SixThreeCrux} (data : SharedPrivateData crux) where
  /-- The diagonal of the Gram core. -/
  gramDiag : Fin data.basisCount → ℝ
  /-- The conjugated coefficient matrix on the slots. -/
  slotProj : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ
  /-- The read matrix: column `y` is the read vector of the atom `y`. -/
  readMat : Matrix (Fin data.basisCount) (Fin 6) ℝ
  /-- The Gram core is the diagonal of its diagonal. -/
  hgramDiag : data.gram = Matrix.diagonal gramDiag
  /-- The Gram core diagonal is positive. -/
  hgramPos : ∀ slot, 0 < gramDiag slot
  /-- The slot projection is symmetric. -/
  hsymm : slotProjᵀ = slotProj
  /-- The slot projection is idempotent. -/
  hidem : slotProj * slotProj = slotProj
  /-- The slot projection carries the coefficient trace. -/
  htrace : Matrix.trace slotProj = Matrix.trace data.coeff
  /-- **THE INTERTWINER LAW.** -/
  hintertwine : slotProj * readMat
    = readMat * (chartPointOfDesign crux.design).chart
  /-- The row Gram of the read matrix is the multiplier assembly. -/
  hassembly : readMatᵀ * readMat
    = chartMultiplierAssembly data.activeSet data.reducedWeight data.tightDir
  /-- The read entries are the scaled basis directions. -/
  hscale : ∀ (slot : Fin data.basisCount) (atomIndex : Fin 6),
    readMat slot atomIndex
      = Real.sqrt (gramDiag slot) * data.tightDir (data.basisLabel slot) atomIndex

namespace ReadIntertwiner

variable {crux : SixThreeCrux} {data : SharedPrivateData crux}

/-- **THE READ WEIGHT MATRIX** `W = Z Zᵀ`. -/
def weightMat (frame : ReadIntertwiner data) :
    Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ :=
  frame.readMat * frame.readMatᵀ

/-- The read weight matrix is symmetric. -/
theorem weightMat_transpose (frame : ReadIntertwiner data) :
    frame.weightMatᵀ = frame.weightMat := by
  rw [weightMat, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **THE REDUCED COMMUTATION.**  The read weight matrix commutes with
the slot projection.  This is the reduced form of the ambient
commutation of the chart with the multiplier assembly. -/
theorem weightMat_commute (frame : ReadIntertwiner data) :
    frame.slotProj * frame.weightMat = frame.weightMat * frame.slotProj :=
  intertwiner_columnGram_commute frame.hsymm data.hdata.isSymmetric
    frame.hintertwine

/-- The read weight matrix entries are the scaled direction products. -/
theorem weightMat_apply (frame : ReadIntertwiner data)
    (rowSlot colSlot : Fin data.basisCount) :
    frame.weightMat rowSlot colSlot
      = Real.sqrt (frame.gramDiag rowSlot) * Real.sqrt (frame.gramDiag colSlot)
        * (data.tightDir (data.basisLabel rowSlot)
            ⬝ᵥ data.tightDir (data.basisLabel colSlot)) := by
  rw [weightMat, Matrix.mul_apply, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [Matrix.transpose_apply, frame.hscale rowSlot atomIndex,
    frame.hscale colSlot atomIndex]
  ring

/-- The read weight diagonal is the Gram core diagonal: the tight
directions are unit vectors. -/
theorem weightMat_diagonal (frame : ReadIntertwiner data)
    (slot : Fin data.basisCount) :
    frame.weightMat slot slot = frame.gramDiag slot := by
  have hmemActive : data.basisLabel slot ∈ data.activeSet := by
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  have hunit := data.hdata.tightDir_unit (data.basisLabel slot) hmemActive
  rw [frame.weightMat_apply slot slot, hunit, mul_one,
    Real.mul_self_sqrt (frame.hgramPos slot).le]

/-- **THE UNIT TRACE.**  The read weight matrix has trace one, because
the multiplier assembly has trace one. -/
theorem trace_weightMat (frame : ReadIntertwiner data) :
    Matrix.trace frame.weightMat = 1 := by
  rw [weightMat, Matrix.trace_mul_comm, frame.hassembly]
  exact trace_chartMultiplierAssembly_of_isChartStationaryData data.hdata

/-- **THE GRAM DIAGONAL MASS.**  The Gram core diagonal sums to one. -/
theorem gramDiag_sum_one (frame : ReadIntertwiner data) :
    ∑ slot : Fin data.basisCount, frame.gramDiag slot = 1 := by
  have htrace := frame.trace_weightMat
  rw [Matrix.trace] at htrace
  rw [← htrace]
  exact (Finset.sum_congr rfl fun slot _ => frame.weightMat_diagonal slot).symm

/-- The read weight quadratic form is nonnegative. -/
theorem weightMat_quadForm_nonneg (frame : ReadIntertwiner data)
    (vec : Fin data.basisCount → ℝ) :
    0 ≤ vec ⬝ᵥ (frame.weightMat *ᵥ vec) := by
  rw [weightMat, columnGram_quadForm]
  exact selfDot_nonneg _

/-- **THE FAITHFUL WEIGHT.**  The read weight matrix has a trivial
kernel: the basis columns are independent and the Gram core diagonal is
positive. -/
theorem weightMat_kernelFree (frame : ReadIntertwiner data)
    (vec : Fin data.basisCount → ℝ) (hzero : frame.weightMat *ᵥ vec = 0) :
    vec = 0 := by
  have hquad : vec ⬝ᵥ (frame.weightMat *ᵥ vec) = 0 := by
    rw [hzero, dotProduct_zero]
  rw [weightMat, columnGram_quadForm] at hquad
  have hrow : frame.readMatᵀ *ᵥ vec = 0 := eq_zero_of_selfDot_eq_zero hquad
  -- the transposed read matrix is the basis column matrix, scaled by slot
  have hscaled : tightBasisColumns data.tightDir data.basisLabel
      *ᵥ (fun slot => Real.sqrt (frame.gramDiag slot) * vec slot) = 0 := by
    funext atomIndex
    have hentry : (frame.readMatᵀ *ᵥ vec) atomIndex
        = (tightBasisColumns data.tightDir data.basisLabel
            *ᵥ fun slot => Real.sqrt (frame.gramDiag slot) * vec slot) atomIndex := by
      rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun slot _ => ?_
      rw [Matrix.transpose_apply, frame.hscale slot atomIndex]
      show Real.sqrt (frame.gramDiag slot)
          * data.tightDir (data.basisLabel slot) atomIndex * vec slot
        = data.tightDir (data.basisLabel slot) atomIndex
          * (Real.sqrt (frame.gramDiag slot) * vec slot)
      ring
    rw [← hentry, hrow]
  have hrecover := congrArg (fun probe => data.leftInv *ᵥ probe) hscaled
  simp only [Matrix.mulVec_mulVec, data.hleft, Matrix.one_mulVec,
    Matrix.mulVec_zero] at hrecover
  funext slot
  have hterm := congrFun hrecover slot
  have hsqrtPos : 0 < Real.sqrt (frame.gramDiag slot) :=
    Real.sqrt_pos.mpr (frame.hgramPos slot)
  show vec slot = 0
  rcases mul_eq_zero.mp hterm with hzeroSqrt | hzeroVec
  · exact absurd hzeroSqrt hsqrtPos.ne'
  · exact hzeroVec

/-- The read vector of an atom vanishes off its support carrier. -/
theorem readMat_eq_zero_of_notMem (frame : ReadIntertwiner data)
    {atomIndex : Fin 6} {slot : Fin data.basisCount}
    (hnot : atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot)) :
    frame.readMat slot atomIndex = 0 := by
  rw [frame.hscale slot atomIndex]
  rw [mem_datumTightSupport, not_not] at hnot
  rw [hnot, mul_zero]

/-- The read vector of an atom does not vanish on its support
carrier. -/
theorem readMat_ne_zero_of_mem (frame : ReadIntertwiner data)
    {atomIndex : Fin 6} {slot : Fin data.basisCount}
    (hmem : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)) :
    frame.readMat slot atomIndex ≠ 0 := by
  rw [frame.hscale slot atomIndex]
  exact mul_ne_zero (Real.sqrt_pos.mpr (frame.hgramPos slot)).ne'
    (mem_datumTightSupport.mp hmem)

/-! ### The captured read weight -/

/-- The complement projection also commutes with the read weight
matrix. -/
theorem complement_weightMat_commute (frame : ReadIntertwiner data) :
    (1 - frame.slotProj) * frame.weightMat
      = frame.weightMat * (1 - frame.slotProj) := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    frame.weightMat_commute]

/-- The captured read weight is symmetric. -/
theorem capture_weightMat_transpose (frame : ReadIntertwiner data) :
    (frame.slotProj * frame.weightMat)ᵀ = frame.slotProj * frame.weightMat :=
  projector_capture_transpose frame.hsymm frame.weightMat_transpose
    frame.weightMat_commute

/-- The captured read weight has a nonnegative quadratic form. -/
theorem capture_weightMat_quadForm_nonneg (frame : ReadIntertwiner data)
    (probe : Fin data.basisCount → ℝ) :
    0 ≤ probe ⬝ᵥ ((frame.slotProj * frame.weightMat) *ᵥ probe) :=
  projector_capture_quadForm_nonneg frame.hsymm frame.hidem
    frame.weightMat_commute frame.weightMat_quadForm_nonneg probe

/-- **THE CAPTURED DIAGONAL.**  The captured read weight diagonal is
the Gram core diagonal times the shifted-weight energy of the basis
direction. -/
theorem capture_weightMat_diagonal (frame : ReadIntertwiner data)
    (slot : Fin data.basisCount) :
    (frame.slotProj * frame.weightMat) slot slot
      = frame.gramDiag slot
        * ∑ atomIndex : Fin 6,
            (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomIndex)
              * data.tightDir (data.basisLabel slot) atomIndex ^ 2 := by
  classical
  have hmemActive : data.basisLabel slot ∈ data.activeSet := by
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  have hexpand : (frame.slotProj * frame.weightMat) slot slot
      = ∑ atomIndex : Fin 6, frame.readMat slot atomIndex
          * ((chartPointOfDesign crux.design).chart
              *ᵥ data.tightDir (data.basisLabel slot)) atomIndex
            * Real.sqrt (frame.gramDiag slot) := by
    rw [weightMat, ← Matrix.mul_assoc, frame.hintertwine, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Matrix.transpose_apply, frame.hscale slot atomIndex, Matrix.mul_apply]
    have hrow : ∑ otherAtom, frame.readMat slot otherAtom
          * (chartPointOfDesign crux.design).chart otherAtom atomIndex
        = Real.sqrt (frame.gramDiag slot)
          * ((chartPointOfDesign crux.design).chart
              *ᵥ data.tightDir (data.basisLabel slot)) atomIndex := by
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun otherAtom _ => ?_
      have hsymmP :=
        congrFun (congrFun data.hdata.isSymmetric otherAtom) atomIndex
      rw [Matrix.transpose_apply] at hsymmP
      rw [frame.hscale slot otherAtom, hsymmP]
      ring
    rw [hrow]
    ring
  rw [hexpand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  by_cases hmem : atomIndex ∈ datumTightSupport data.tightDir
    (data.basisLabel slot)
  · have hread := projection_mulVec_tightDir_of_mem data.hdata hmemActive
      (datumTightSupport_subset data.hdata hmemActive hmem)
    rw [hread, frame.hscale slot atomIndex]
    have hsqsq := Real.mul_self_sqrt (frame.hgramPos slot).le
    linear_combination ((chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      * data.tightDir (data.basisLabel slot) atomIndex ^ 2) * hsqsq
  · rw [mem_datumTightSupport, not_not] at hmem
    rw [frame.hscale slot atomIndex, hmem]
    ring

/-- **THE CAPTURED TRACE.**  The captured read weight has trace
`value + 1/6`: the diagonal of the captured assembly is the shifted
weight over six. -/
theorem trace_capture_weightMat (frame : ReadIntertwiner data) :
    Matrix.trace (frame.slotProj * frame.weightMat)
      = chartObjective (chartPointOfDesign crux.design) + (6 : ℝ)⁻¹ := by
  have hmove : frame.slotProj * frame.weightMat
      = (frame.readMat * (chartPointOfDesign crux.design).chart)
        * frame.readMatᵀ := by
    rw [weightMat, ← Matrix.mul_assoc, frame.hintertwine]
  have hcycle : Matrix.trace (frame.slotProj * frame.weightMat)
      = Matrix.trace (chartMultiplierAssembly data.activeSet data.reducedWeight
          data.tightDir * (chartPointOfDesign crux.design).chart) := by
    rw [hmove, Matrix.trace_mul_comm, ← Matrix.mul_assoc, frame.hassembly]
  have hswap : chartMultiplierAssembly data.activeSet data.reducedWeight
        data.tightDir * (chartPointOfDesign crux.design).chart
      = (chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly data.activeSet data.reducedWeight
          data.tightDir := data.hdata.assembly_commutes.symm
  rw [hcycle, hswap, Matrix.trace]
  have hentry : ∀ atomIndex : Fin 6,
      ((chartPointOfDesign crux.design).chart
          * chartMultiplierAssembly data.activeSet data.reducedWeight
            data.tightDir).diag atomIndex
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * (((6 : ℕ) : ℝ))⁻¹ :=
    fun atomIndex =>
      diagonal_projection_mul_multiplier_of_isChartStationaryData data.hdata
        atomIndex
  rw [Finset.sum_congr rfl fun atomIndex _ => hentry atomIndex,
    ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    data.hdata.weight_sum_one]
  push_cast
  ring

/-- **THE KERNEL TRACE.**  The complement of the captured read weight
has trace `5/6 - value`. -/
theorem trace_complement_weightMat (frame : ReadIntertwiner data) :
    Matrix.trace ((1 - frame.slotProj) * frame.weightMat)
      = (5 : ℝ) / 6 - chartObjective (chartPointOfDesign crux.design) := by
  have hsplit : (1 - frame.slotProj) * frame.weightMat
      = frame.weightMat - frame.slotProj * frame.weightMat := by
    rw [Matrix.sub_mul, Matrix.one_mul]
  rw [hsplit, Matrix.trace_sub, frame.trace_weightMat,
    frame.trace_capture_weightMat]
  ring

/-- The basis direction is a unit vector, read as a square total. -/
theorem tightDir_square_sum (_frame : ReadIntertwiner data)
    (slot : Fin data.basisCount) :
    ∑ atomIndex : Fin 6,
        data.tightDir (data.basisLabel slot) atomIndex ^ 2 = 1 := by
  have hmemActive : data.basisLabel slot ∈ data.activeSet := by
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  have hunit := data.hdata.tightDir_unit (data.basisLabel slot) hmemActive
  rw [dotProduct] at hunit
  rw [← hunit]
  exact Finset.sum_congr rfl fun atomIndex _ => sq _

/-- **THE KERNEL DIAGONAL.**  The complement of the captured read
weight reads the complementary shifted-weight energy. -/
theorem complement_weightMat_diagonal (frame : ReadIntertwiner data)
    (slot : Fin data.basisCount) :
    ((1 - frame.slotProj) * frame.weightMat) slot slot
      = frame.gramDiag slot
        * ∑ atomIndex : Fin 6,
            (1 - (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomIndex))
              * data.tightDir (data.basisLabel slot) atomIndex ^ 2 := by
  have hsplit : ((1 - frame.slotProj) * frame.weightMat) slot slot
      = frame.weightMat slot slot
        - (frame.slotProj * frame.weightMat) slot slot := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply]
  have hexpand : ∑ atomIndex : Fin 6,
        (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))
          * data.tightDir (data.basisLabel slot) atomIndex ^ 2
      = (∑ atomIndex : Fin 6,
            data.tightDir (data.basisLabel slot) atomIndex ^ 2)
        - ∑ atomIndex : Fin 6,
            (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomIndex)
              * data.tightDir (data.basisLabel slot) atomIndex ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsplit, frame.weightMat_diagonal, frame.capture_weightMat_diagonal,
    hexpand, frame.tightDir_square_sum]
  ring

/-- **THE CAPTURED FLOOR.**  At an interior shifted-weight window the
captured read weight diagonal is strictly positive. -/
theorem capture_weightMat_diagonal_pos (frame : ReadIntertwiner data)
    (hinterior : ∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
    (slot : Fin data.basisCount) :
    0 < (frame.slotProj * frame.weightMat) slot slot := by
  classical
  obtain ⟨witness, hwitness⟩ := Finset.card_pos.mp
    (by rw [data.hthree slot]; norm_num :
      0 < (datumTightSupport data.tightDir (data.basisLabel slot)).card)
  have hne : data.tightDir (data.basisLabel slot) witness ≠ 0 :=
    mem_datumTightSupport.mp hwitness
  have hterm : 0 < (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight witness)
      * data.tightDir (data.basisLabel slot) witness ^ 2 :=
    mul_pos (hinterior witness) (pow_pos (abs_pos.mpr hne) 2 |>.trans_le
      (le_of_eq (sq_abs _)))
  have hsum : 0 < ∑ atomIndex : Fin 6,
      (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * data.tightDir (data.basisLabel slot) atomIndex ^ 2 :=
    Finset.sum_pos' (fun atomIndex _ => mul_nonneg (hinterior atomIndex).le
      (sq_nonneg _)) ⟨witness, Finset.mem_univ witness, hterm⟩
  rw [frame.capture_weightMat_diagonal]
  exact mul_pos (frame.hgramPos slot) hsum

/-- **THE KERNEL FLOOR.**  The complement of the captured read weight
has a strictly positive diagonal, because the chart value is
negative. -/
theorem complement_weightMat_diagonal_pos (frame : ReadIntertwiner data)
    (slot : Fin data.basisCount) :
    0 < ((1 - frame.slotProj) * frame.weightMat) slot slot := by
  classical
  have hcap : ∀ atomIndex : Fin 6,
      0 < 1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) := by
    intro atomIndex
    have hvalue : chartObjective (chartPointOfDesign crux.design) < 0 :=
      data.hvalueNeg
    have hweight : (chartPointOfDesign crux.design).weight atomIndex ≤ 1 := by
      have hle : (chartPointOfDesign crux.design).weight atomIndex
          ≤ ∑ probe : Fin 6, (chartPointOfDesign crux.design).weight probe :=
        Finset.single_le_sum
          (f := fun probe => (chartPointOfDesign crux.design).weight probe)
          (fun probe _ => (data.hdata.weight_pos probe).le)
          (Finset.mem_univ atomIndex)
      rwa [data.hdata.weight_sum_one] at hle
    linarith
  obtain ⟨witness, hwitness⟩ := Finset.card_pos.mp
    (by rw [data.hthree slot]; norm_num :
      0 < (datumTightSupport data.tightDir (data.basisLabel slot)).card)
  have hne : data.tightDir (data.basisLabel slot) witness ≠ 0 :=
    mem_datumTightSupport.mp hwitness
  have hsqPos : 0 < data.tightDir (data.basisLabel slot) witness ^ 2 :=
    pow_pos (abs_pos.mpr hne) 2 |>.trans_le (le_of_eq (sq_abs _))
  have hsum : 0 < ∑ atomIndex : Fin 6,
      (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex))
        * data.tightDir (data.basisLabel slot) atomIndex ^ 2 :=
    Finset.sum_pos' (fun atomIndex _ => mul_nonneg (hcap atomIndex).le
      (sq_nonneg _))
      ⟨witness, Finset.mem_univ witness, mul_pos (hcap witness) hsqPos⟩
  rw [frame.complement_weightMat_diagonal]
  exact mul_pos (frame.hgramPos slot) hsum

/-- **THE DISJOINT SLOT PAIR.**  Two slots with disjoint supports carry
a zero read weight entry. -/
theorem weightMat_eq_zero_of_disjoint_support (frame : ReadIntertwiner data)
    {rowSlot colSlot : Fin data.basisCount}
    (hdisjoint : ∀ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel rowSlot) →
      atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel colSlot)) :
    frame.weightMat rowSlot colSlot = 0 := by
  classical
  rw [weightMat, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun atomIndex _ => ?_
  rw [Matrix.transpose_apply]
  by_cases hmem : atomIndex ∈ datumTightSupport data.tightDir
    (data.basisLabel rowSlot)
  · rw [frame.readMat_eq_zero_of_notMem (hdisjoint atomIndex hmem), mul_zero]
  · rw [frame.readMat_eq_zero_of_notMem hmem, zero_mul]

end ReadIntertwiner

/-- **THE READ FRAME CONSTRUCTION.**  Every diagonal-Gram
shared-private datum carries a read frame.  The conjugation by the
square roots of the Gram core diagonal makes the coefficient matrix
symmetric through the exchange law, and the coefficient representation
of the chart becomes the intertwiner. -/
noncomputable def SharedPrivateData.readIntertwiner {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) : ReadIntertwiner data := by
  classical
  -- the positive diagonal of the Gram core
  have hpsd := data.hpsd
  have hker := data.hker
  rw [hdiag] at hpsd hker
  have hg : ∀ slot, 0 < gramDiag slot := by
    intro slot
    have hpos := posSemidef_diagonal_pos_of_kernel_free hpsd hker slot
    rwa [Matrix.diagonal_apply_eq] at hpos
  set sq : Fin data.basisCount → ℝ := fun slot => Real.sqrt (gramDiag slot)
    with hsqdef
  have hsq : ∀ slot, 0 < sq slot := fun slot => Real.sqrt_pos.mpr (hg slot)
  have hsqsq : ∀ slot, sq slot * sq slot = gramDiag slot :=
    fun slot => Real.mul_self_sqrt (hg slot).le
  -- the exchange entries under the diagonal core
  have hexchange := data.hexchange
  rw [hdiag] at hexchange
  have hx : ∀ rowSlot colSlot, data.coeff rowSlot colSlot * gramDiag colSlot
      = gramDiag rowSlot * data.coeff colSlot rowSlot := by
    intro rowSlot colSlot
    have hentry := congrFun (congrFun hexchange rowSlot) colSlot
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply] at hentry
  -- the conjugated coefficient matrix
  set slotProj : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ :=
    Matrix.of fun rowSlot colSlot =>
      (sq rowSlot)⁻¹ * (data.coeff rowSlot colSlot * sq colSlot) with hSdef
  have hSapply : ∀ rowSlot colSlot, slotProj rowSlot colSlot
      = (sq rowSlot)⁻¹ * (data.coeff rowSlot colSlot * sq colSlot) :=
    fun _ _ => rfl
  have hSsymm : slotProjᵀ = slotProj := by
    ext rowSlot colSlot
    rw [Matrix.transpose_apply, hSapply, hSapply]
    refine mul_left_cancel₀
      (mul_ne_zero (hsq rowSlot).ne' (hsq colSlot).ne') ?_
    have hci : sq rowSlot * (sq rowSlot)⁻¹ = 1 :=
      mul_inv_cancel₀ (hsq rowSlot).ne'
    have hcj : sq colSlot * (sq colSlot)⁻¹ = 1 :=
      mul_inv_cancel₀ (hsq colSlot).ne'
    have hgi := hsqsq rowSlot
    have hgj := hsqsq colSlot
    have hxi := hx rowSlot colSlot
    linear_combination
      (data.coeff colSlot rowSlot * sq rowSlot * sq rowSlot) * hcj
      - (data.coeff rowSlot colSlot * sq colSlot * sq colSlot) * hci
      + data.coeff colSlot rowSlot * hgi
      - data.coeff rowSlot colSlot * hgj
      - hxi
  have hSidem : slotProj * slotProj = slotProj := by
    ext rowSlot colSlot
    rw [Matrix.mul_apply]
    have hterm : ∀ midSlot, slotProj rowSlot midSlot * slotProj midSlot colSlot
        = (sq rowSlot)⁻¹
          * (data.coeff rowSlot midSlot * data.coeff midSlot colSlot)
          * sq colSlot := by
      intro midSlot
      rw [hSapply, hSapply]
      have hck : sq midSlot * (sq midSlot)⁻¹ = 1 :=
        mul_inv_cancel₀ (hsq midSlot).ne'
      linear_combination ((sq rowSlot)⁻¹ * data.coeff rowSlot midSlot
        * data.coeff midSlot colSlot * sq colSlot) * hck
    rw [Finset.sum_congr rfl fun midSlot _ => hterm midSlot,
      ← Finset.sum_mul, ← Finset.mul_sum]
    have hMM : ∑ midSlot, data.coeff rowSlot midSlot
        * data.coeff midSlot colSlot = data.coeff rowSlot colSlot := by
      have hentry := congrFun (congrFun data.hidempotent rowSlot) colSlot
      rwa [Matrix.mul_apply] at hentry
    rw [hMM, hSapply]
    ring
  have hStrace : Matrix.trace slotProj = Matrix.trace data.coeff := by
    rw [Matrix.trace, Matrix.trace]
    refine Finset.sum_congr rfl fun slot _ => ?_
    have hinv : (sq slot)⁻¹ * sq slot = 1 :=
      inv_mul_cancel₀ (hsq slot).ne'
    show slotProj slot slot = data.coeff slot slot
    rw [hSapply]
    linear_combination data.coeff slot slot * hinv
  -- the read matrix
  set readMat : Matrix (Fin data.basisCount) (Fin 6) ℝ :=
    Matrix.of fun slot atomIndex =>
      sq slot * data.tightDir (data.basisLabel slot) atomIndex with hZdef
  have hZapply : ∀ slot atomIndex, readMat slot atomIndex
      = sq slot * data.tightDir (data.basisLabel slot) atomIndex :=
    fun _ _ => rfl
  -- the intertwiner law: the exchange moves the coefficient across
  have hinter : slotProj * readMat
      = readMat * (chartPointOfDesign crux.design).chart := by
    ext slot atomIndex
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have hleftTerm : ∀ colSlot, slotProj slot colSlot * readMat colSlot atomIndex
        = sq slot * (data.tightDir (data.basisLabel colSlot) atomIndex
            * data.coeff colSlot slot) := by
      intro colSlot
      rw [hSapply, hZapply]
      have hinvSlot : sq slot * (sq slot)⁻¹ = 1 := mul_inv_cancel₀ (hsq slot).ne'
      have hgi := hsqsq slot
      have hgj := hsqsq colSlot
      have hxj := hx slot colSlot
      refine mul_left_cancel₀ (hsq slot).ne' ?_
      linear_combination
        (data.coeff slot colSlot * sq colSlot ^ 2
          * data.tightDir (data.basisLabel colSlot) atomIndex) * hinvSlot
        + (data.coeff slot colSlot
            * data.tightDir (data.basisLabel colSlot) atomIndex) * hgj
        + (data.tightDir (data.basisLabel colSlot) atomIndex) * hxj
        - (data.tightDir (data.basisLabel colSlot) atomIndex
            * data.coeff colSlot slot) * hgi
    have hrightTerm : ∀ otherAtom, readMat slot otherAtom
          * (chartPointOfDesign crux.design).chart otherAtom atomIndex
        = sq slot * ((chartPointOfDesign crux.design).chart atomIndex otherAtom
            * data.tightDir (data.basisLabel slot) otherAtom) := by
      intro otherAtom
      rw [hZapply]
      have hsymmP := congrFun (congrFun data.hdata.isSymmetric otherAtom) atomIndex
      rw [Matrix.transpose_apply] at hsymmP
      rw [hsymmP]
      ring
    rw [Finset.sum_congr rfl fun colSlot _ => hleftTerm colSlot,
      Finset.sum_congr rfl fun otherAtom _ => hrightTerm otherAtom,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have hrep := congrFun (congrFun data.hrepresentation atomIndex) slot
    rw [Matrix.mul_apply, Matrix.mul_apply] at hrep
    have hleftSum : ∑ otherAtom,
        (chartPointOfDesign crux.design).chart atomIndex otherAtom
          * data.tightDir (data.basisLabel slot) otherAtom
        = ∑ otherAtom, (chartPointOfDesign crux.design).chart atomIndex otherAtom
            * tightBasisColumns data.tightDir data.basisLabel otherAtom slot := rfl
    have hrightSum : ∑ colSlot,
        data.tightDir (data.basisLabel colSlot) atomIndex
          * data.coeff colSlot slot
        = ∑ colSlot, tightBasisColumns data.tightDir data.basisLabel
            atomIndex colSlot * data.coeff colSlot slot := rfl
    rw [hrightSum, hleftSum, ← hrep]
  -- the row Gram is the multiplier assembly
  have hassembly : readMatᵀ * readMat
      = chartMultiplierAssembly data.activeSet data.reducedWeight data.tightDir := by
    have hH := data.hHform
    rw [hdiag] at hH
    rw [← hH]
    ext atomIndex otherAtom
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [Matrix.transpose_apply, hZapply, hZapply, Matrix.mul_diagonal,
      Matrix.transpose_apply]
    have hgk := hsqsq slot
    show sq slot * data.tightDir (data.basisLabel slot) atomIndex
        * (sq slot * data.tightDir (data.basisLabel slot) otherAtom)
      = tightBasisColumns data.tightDir data.basisLabel atomIndex slot
        * gramDiag slot
        * tightBasisColumns data.tightDir data.basisLabel otherAtom slot
    show sq slot * data.tightDir (data.basisLabel slot) atomIndex
        * (sq slot * data.tightDir (data.basisLabel slot) otherAtom)
      = data.tightDir (data.basisLabel slot) atomIndex * gramDiag slot
        * data.tightDir (data.basisLabel slot) otherAtom
    linear_combination (data.tightDir (data.basisLabel slot) atomIndex
      * data.tightDir (data.basisLabel slot) otherAtom) * hgk
  exact
    { gramDiag := gramDiag
      slotProj := slotProj
      readMat := readMat
      hgramDiag := hdiag
      hgramPos := hg
      hsymm := hSsymm
      hidem := hSidem
      htrace := hStrace
      hintertwine := hinter
      hassembly := hassembly
      hscale := fun slot atomIndex => hZapply slot atomIndex }

/-! ## Layer 4 — the faithful assembly at basis count six -/

/-- **THE SQUARE BASIS.**  At basis count six the basis columns are a
two-sided inverse pair with the left inverse. -/
theorem SharedPrivateData.basisColumns_mul_leftInv_of_basisCount_six
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    (hsix : data.basisCount = 6) :
    tightBasisColumns data.tightDir data.basisLabel * data.leftInv = 1 := by
  exact (Matrix.mul_eq_one_comm_of_equiv (finCongr hsix)).mp data.hleft

/-- **THE FORCED TRACE.**  At basis count six the coefficient matrix is
conjugate to the chart projection, thus its trace is three.  Only the
trace-three stratum survives at basis count six. -/
theorem SharedPrivateData.trace_eq_three_of_basisCount_six
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    (hsix : data.basisCount = 6) : Matrix.trace data.coeff = 3 := by
  have hright := data.basisColumns_mul_leftInv_of_basisCount_six hsix
  have hchain : Matrix.trace data.coeff
      = Matrix.trace ((chartPointOfDesign crux.design).chart) := by
    calc Matrix.trace data.coeff
        = Matrix.trace ((1 : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ)
            * data.coeff) := by rw [Matrix.one_mul]
      _ = Matrix.trace (data.leftInv
            * (tightBasisColumns data.tightDir data.basisLabel * data.coeff)) := by
          rw [← data.hleft, Matrix.mul_assoc]
      _ = Matrix.trace (data.leftInv
            * ((chartPointOfDesign crux.design).chart
              * tightBasisColumns data.tightDir data.basisLabel)) := by
          rw [data.hrepresentation]
      _ = Matrix.trace ((tightBasisColumns data.tightDir data.basisLabel
            * data.leftInv) * (chartPointOfDesign crux.design).chart) := by
          rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
      _ = Matrix.trace ((chartPointOfDesign crux.design).chart) := by
          rw [hright, Matrix.one_mul]
  have hrank := data.hdata.hasTraceRank
  rw [hchain, hrank]
  norm_num

/-- The assembly kernel sits inside the kernel of the transposed basis
columns: the Gram core is faithful and the left inverse strips the
basis. -/
theorem SharedPrivateData.basisColumns_transpose_mulVec_eq_zero_of_assembly
    {crux : SixThreeCrux} (data : SharedPrivateData crux) {vec : Fin 6 → ℝ}
    (hzero : chartMultiplierAssembly data.activeSet data.reducedWeight
      data.tightDir *ᵥ vec = 0) :
    (tightBasisColumns data.tightDir data.basisLabel)ᵀ *ᵥ vec = 0 := by
  have hH := data.hHform
  rw [← hH] at hzero
  have hstep : tightBasisColumns data.tightDir data.basisLabel
      *ᵥ (data.gram
        *ᵥ ((tightBasisColumns data.tightDir data.basisLabel)ᵀ *ᵥ vec)) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact hzero
  have hstrip : data.leftInv *ᵥ (tightBasisColumns data.tightDir data.basisLabel
        *ᵥ (data.gram
          *ᵥ ((tightBasisColumns data.tightDir data.basisLabel)ᵀ *ᵥ vec)))
      = data.gram
        *ᵥ ((tightBasisColumns data.tightDir data.basisLabel)ᵀ *ᵥ vec) := by
    rw [Matrix.mulVec_mulVec, data.hleft, Matrix.one_mulVec]
  refine data.hker _ ?_
  rw [← hstrip, hstep, Matrix.mulVec_zero]

/-- **THE FAITHFUL ASSEMBLY.**  At basis count six the multiplier
assembly has a trivial kernel. -/
theorem SharedPrivateData.assembly_kernelFree_of_basisCount_six
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    (hsix : data.basisCount = 6) (vec : Fin 6 → ℝ)
    (hzero : chartMultiplierAssembly data.activeSet data.reducedWeight
      data.tightDir *ᵥ vec = 0) : vec = 0 := by
  have hcolumns := data.basisColumns_transpose_mulVec_eq_zero_of_assembly hzero
  have hright := data.basisColumns_mul_leftInv_of_basisCount_six hsix
  have htrans : data.leftInvᵀ
      * (tightBasisColumns data.tightDir data.basisLabel)ᵀ = 1 := by
    have htrace := congrArg Matrix.transpose hright
    rwa [Matrix.transpose_mul, Matrix.transpose_one] at htrace
  calc vec = (1 : Matrix (Fin 6) (Fin 6) ℝ) *ᵥ vec := (Matrix.one_mulVec vec).symm
    _ = (data.leftInvᵀ
          * (tightBasisColumns data.tightDir data.basisLabel)ᵀ) *ᵥ vec := by
        rw [htrans]
    _ = data.leftInvᵀ
          *ᵥ ((tightBasisColumns data.tightDir data.basisLabel)ᵀ *ᵥ vec) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [hcolumns, Matrix.mulVec_zero]

/-- **THE INTERIOR WINDOW AT BASIS COUNT SIX.**  A zero shifted weight
kills the captured assembly row, thus the assembly kills the chart
column at that atom.  A faithful assembly then kills the chart column
itself, and the all-heavy gap floor refuses a zero chart diagonal.  No
trace hypothesis is used. -/
theorem SharedPrivateData.shifted_weight_pos_of_basisCount_six
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    (hsix : data.basisCount = 6) (atomIndex : Fin 6) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex := by
  classical
  rcases (capture_diagonal_nonneg_of_isChartStationaryData data.hdata
      atomIndex).lt_or_eq with hpos | heq
  · exact hpos
  · exfalso
    set assembly := chartMultiplierAssembly data.activeSet data.reducedWeight
      data.tightDir with hassemblyDef
    set chart := (chartPointOfDesign crux.design).chart with hchartDef
    have hchartSymm : chartᵀ = chart := data.hdata.isSymmetric
    have hcommutes : chart * assembly = assembly * chart :=
      data.hdata.assembly_commutes
    have hassemblySymm : assemblyᵀ = assembly := by
      have hherm : assemblyᴴ = assembly :=
        isHermitian_chartMultiplierAssembly_of_isChartStationaryData data.hdata
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hherm
    have hcapDiag : (chart * assembly) atomIndex atomIndex = 0 := by
      have hvalue : (chart * assembly) atomIndex atomIndex
          = (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomIndex)
            * ((6 : ℕ) : ℝ)⁻¹ :=
        diagonal_projection_mul_multiplier_of_isChartStationaryData data.hdata
          atomIndex
      rw [hvalue, ← heq, zero_mul]
    have hcapSymm : (chart * assembly)ᵀ = chart * assembly := by
      rw [Matrix.transpose_mul, hassemblySymm, hchartSymm, ← hcommutes]
    have hcapQuad : ∀ probe : Fin 6 → ℝ,
        0 ≤ probe ⬝ᵥ ((chart * assembly) *ᵥ probe) := by
      intro probe
      have hpsd :=
        posSemidef_projection_mul_multiplier_of_isChartStationaryData data.hdata
      simpa using hpsd.dotProduct_mulVec_nonneg probe
    have hrow : ∀ otherAtom, (chart * assembly) atomIndex otherAtom = 0 :=
      fun otherAtom => row_eq_zero_of_quadForm_nonneg_of_diag_zero hcapSymm
        hcapQuad hcapDiag otherAtom
    have hcolumn : (chart * assembly) *ᵥ (Pi.single atomIndex (1 : ℝ)) = 0 := by
      funext rowAtom
      have hentry : ((chart * assembly) *ᵥ (Pi.single atomIndex (1 : ℝ))) rowAtom
          = (chart * assembly) rowAtom atomIndex := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
          mul_zero]
      have hcross : (chart * assembly) rowAtom atomIndex
          = (chart * assembly) atomIndex rowAtom := by
        have hsym := congrFun (congrFun hcapSymm atomIndex) rowAtom
        rwa [Matrix.transpose_apply] at hsym
      rw [hentry, hcross, hrow rowAtom]
      rfl
    have hswapped : assembly *ᵥ (chart *ᵥ (Pi.single atomIndex (1 : ℝ))) = 0 := by
      rw [Matrix.mulVec_mulVec, ← hcommutes]
      exact hcolumn
    have hchartColumn : chart *ᵥ (Pi.single atomIndex (1 : ℝ)) = 0 :=
      data.assembly_kernelFree_of_basisCount_six hsix _ hswapped
    have hchartDiag : chart atomIndex atomIndex = 0 := by
      have hread := single_dotProduct_mulVec_single chart atomIndex
      rw [hchartColumn, dotProduct_zero] at hread
      exact hread.symm
    have hgap := crux.chartGap_diagonal_pos atomIndex
    simp only [chartStationaryGap, Matrix.sub_apply,
      Matrix.diagonal_apply_eq] at hgap
    rw [← hchartDef, hchartDiag] at hgap
    have hweight := data.hdata.weight_pos atomIndex
    linarith

/-! ## Layer 5 — the narrowed deficit dispatch -/

/-- **THE PINNED PROFILE.**  The pin atom has multiplicity one, thus a
profile mass of at most three carries exactly one multiplicity-one atom
and at most one multiplicity-two atom. -/
theorem SharedPrivateData.deficit_profile_of_mass {crux : SixThreeCrux}
    (data : SharedPrivateData crux)
    (hmass : 2 * (Finset.univ.filter fun atomIndex =>
          basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1).card
        + (Finset.univ.filter fun atomIndex =>
          basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 2).card
      ≤ 3) :
    (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1).card = 1
    ∧ (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 2).card
      ≤ 1 := by
  classical
  have hpinMem : data.pinAtom ∈ Finset.univ.filter fun atomIndex =>
      basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, data.hmultOne⟩
  have hone : 1 ≤ (Finset.univ.filter fun atomIndex =>
      basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1).card :=
    Finset.card_pos.mpr ⟨data.pinAtom, hpinMem⟩
  omega

/-- **THE INTERIOR SIX RESIDUE.**  The trace-three deficit at basis
count six, with the pinned profile, the interior window, and the
support mass.  Every added hypothesis is free at basis count six. -/
def SharedPrivateDeficitSixInteriorClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 3 →
    data.basisCount = 6 →
    (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1).card = 1 →
    (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 2).card ≤ 1 →
    (∀ atomIndex : Fin 6, 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex) →
    ∑ atomIndex : Fin 6,
      basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 18 →
    False

/-- **THE SIX NARROWING.**  The interior six residue closes the six
residue: the profile mass and the pin pin the profile, the faithful
assembly at basis count six supplies the interior window with no trace
hypothesis, and the support cards supply the mass. -/
theorem sharedPrivateDeficitSixClosed_of_interior
    (hnarrow : SharedPrivateDeficitSixInteriorClosed) :
    SharedPrivateDeficitSixClosed := by
  classical
  intro crux data gramDiag hdiag htraceThree hsix hmass
  obtain ⟨hcardOne, hcardTwo⟩ := data.deficit_profile_of_mass hmass
  have hmultTotal :
      ∑ atomIndex : Fin 6,
        basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 18 := by
    rw [sum_basisSupportMultiplicity,
      Finset.sum_congr rfl fun slot _ => data.hthree slot, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, hsix]
  exact hnarrow crux data gramDiag hdiag htraceThree hsix hcardOne hcardTwo
    (fun atomIndex => data.shifted_weight_pos_of_basisCount_six hsix atomIndex)
    hmultTotal

/-- **THE INTERIOR COMPLEMENT RESIDUE.**  The trace-three deficit at
basis count five with a complementary slot pair, the pinned slot named,
the interior window, and the support mass. -/
def SharedPrivateDeficitComplementInteriorClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 3 →
    data.basisCount = 5 →
    (∀ atomIndex : Fin 6, 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex) →
    ∑ atomIndex : Fin 6,
      basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 15 →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      (∀ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) →
        atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo)) →
      (∀ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
        ∨ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo)) →
      (slotOne = data.privateSlot ∨ slotTwo = data.privateSlot) →
      False

/-- **THE COMPLEMENT NARROWING.**  The interior complement residue
closes the complement residue: the trace-split kill supplies the
interior window, the support cards supply the mass, and the pin law of a
disjoint pair names the pinned slot. -/
theorem sharedPrivateDeficitComplementClosed_of_interior
    (hnarrow : SharedPrivateDeficitComplementInteriorClosed) :
    SharedPrivateDeficitComplementClosed := by
  classical
  intro crux data gramDiag hdiag htraceThree hfive slotOne slotTwo hne
    hdisjoint hcover
  have hmultTotal :
      ∑ atomIndex : Fin 6,
        basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 15 := by
    rw [sum_basisSupportMultiplicity,
      Finset.sum_congr rfl fun slot _ => data.hthree slot, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, hfive]
  exact hnarrow crux data gramDiag hdiag htraceThree hfive
    (fun atomIndex => data.shifted_weight_pos_of_trace_three htraceThree atomIndex)
    hmultTotal slotOne slotTwo hne hdisjoint hcover
    (data.privateSlot_mem_of_disjoint_supports hdisjoint)

/-- **THE INTERIOR DEFICIT DISPATCH.**  The two interior residues close
the trace-three deficit.  This supersedes the two coarser dispatches:
every hypothesis that the interior residues add is free. -/
theorem sharedPrivateDeficitClosed_of_interior_residues
    (hsix : SharedPrivateDeficitSixInteriorClosed)
    (hcomplement : SharedPrivateDeficitComplementInteriorClosed) :
    SharedPrivateDeficitClosed :=
  sharedPrivateDeficitClosed_of_complement_residues
    (sharedPrivateDeficitSixClosed_of_interior hsix)
    (sharedPrivateDeficitComplementClosed_of_interior hcomplement)

/-- **THE INTERIOR STRATA DISPATCH.**  The extras residue, the boundary
residue, and the two interior deficit residues close the generic
shared-private kill. -/
theorem sharedPrivateKilled_of_interior_strata
    (hextras : SharedPrivateExtrasClosed)
    (hboundary : SharedPrivateBoundaryClosed)
    (hsix : SharedPrivateDeficitSixInteriorClosed)
    (hcomplement : SharedPrivateDeficitComplementInteriorClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_strata hextras hboundary
    (sharedPrivateDeficitClosed_of_interior_residues hsix hcomplement)

end Gtz

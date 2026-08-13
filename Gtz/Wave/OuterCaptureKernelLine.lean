import Gtz.Wave.OuterBoundaryResidueLine
import Gtz.Wave.PlaneWitnessLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The capture kernel line — the chart minor of a clone pair

A rank-four frame splits its chart into the capture frame and a capture
residue of trace one.  A trace-one symmetric idempotent is a rank-one
projector, thus every two-by-two minor of the residue vanishes.  This
module reads that vanishing at an atom PAIR whose basis rows are
proportional.

The reading is an identity.  Write `P` for the chart, `F` for the
capture frame and `sigma` for the clone scale.  The capture frame kills
the pair direction, thus `F` at the pair is the rank-one block of
`F_{t1t1}` against `(1, sigma)`, and the vanishing residue minor gives

**`P_{t1t1} P_{t2t2} - P_{t1t2}² = F_{t1t1} (P_{t2t2} - 2 sigma P_{t1t2}
+ sigma² P_{t1t1})`.**

The left side is positive because the crux carries no parallel pair, and
the two right factors are nonnegative, thus BOTH are positive.  The
first factor is the interiority of the clone atom.  The second is a new
chart inequality of every clone pair.

The same split carries a LINE.  The residue of trace one fixes a nonzero
vector, that vector is a basis null direction, and the chart fixes it.
Every clone pair thus splits: either the chart fixes the pair direction
itself, or the pair direction minus its residue part is a nonzero
direction that BOTH the basis and the chart annihilate.  A chart null
direction is an atom dependency, thus it is alive at three atoms or
more.  A chart fixed direction is a design coplanarity: one nonzero
direction of the atom space annihilates every atom off the support.

When the capture trace reaches the chart rank the residue is ZERO, thus
every basis null direction is chart null, thus a clone pair is a
parallel pair.  **EVERY CLONE PAIR OF A RANK-SIX FRAME IS DEAD, AND SO
IS EVERY CLONE PAIR OF A RANK-FIVE FRAME OF CAPTURE TRACE THREE.**

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.symmIdem_minor_eq_of_trace_lt_two` — **THE RANK-ONE MINOR LAW.**
* `Gtz.eq_zero_of_symmIdem_trace_lt_one`,
  `Gtz.exists_fixed_of_symmIdem_trace_pos` — the two trace ends.
* `Gtz.captureFrame_transpose`, `Gtz.captureFrame_mul_self`,
  `Gtz.chart_mul_captureFrame`, `Gtz.chart_mul_captureResidue` — the
  frame is a symmetric idempotent that the chart fixes.
* `Gtz.captureFrame_pair_entries_of_clone` — the pair block of the
  frame.
* `Gtz.chart_pair_minor_eq_captureFrame_form` — **THE CHART PAIR MINOR
  IDENTITY.**
* `Gtz.SixThreeCrux.chart_pair_minor_pos`,
  `Gtz.SixThreeCrux.captureFrame_diag_pos_of_pair_null`,
  `Gtz.SixThreeCrux.pair_null_form_pos` — the three positivities.
* `Gtz.SixThreeCrux.false_of_chart_null_pair`,
  `Gtz.SixThreeCrux.false_of_chart_null_singleton` — a chart null
  direction is alive at three atoms or more.
* `Gtz.SixThreeCrux.exists_orthogonal_of_chart_fixed` — **THE
  COPLANARITY READING.**
* `Gtz.SixThreeCrux.false_of_pair_null_of_capture_trace_rank` — **THE
  ZERO RESIDUE KILL.**
* `Gtz.RankFourFrame.exists_capture_line` — **THE RESIDUE LINE.**
* `Gtz.RankFourFrame.clone_chart_dichotomy` — **THE CLONE SPLIT.**
* `Gtz.RankFiveFrame.false_of_clone_pair_of_capture_trace_three`,
  `Gtz.RankSixFrame.false_of_clone_pair` — the two upper rungs.
* `Gtz.rankFourOuterThinCloneClosed_of_fixed_split` and
  `Gtz.rankFourSupportTwoClosed_of_fixedSplit_triple_interior` — the
  narrowed rank-four discharge.

## Vacuity

Layers one thru three hold at every symmetric idempotent and at every
stationary datum with a chosen basis.  The crux-facing statements are
vacuous if `Gtz.GtzWeighted 6 3` holds: no crux exists, thus no frame
and no datum exists.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the low-trace idempotent calculus -/

section LowTrace

variable {dim : ℕ} {idem : Matrix (Fin dim) (Fin dim) ℝ}

/-- Every column of an idempotent is a fixed vector of it. -/
theorem symmIdem_column_fixed (hidem : idem * idem = idem) (colIndex : Fin dim) :
    idem *ᵥ (idem *ᵥ (Pi.single colIndex 1 : Fin dim → ℝ))
      = idem *ᵥ (Pi.single colIndex 1 : Fin dim → ℝ) := by
  rw [Matrix.mulVec_mulVec, hidem]

/-- **THE RANK-ONE MINOR LAW.**  A symmetric idempotent of trace less
than two is a rank-one projector, thus every two-by-two minor of it
vanishes.  The proof reads two columns, which are fixed vectors, through
the trace-one parallel law. -/
theorem symmIdem_minor_eq_of_trace_lt_two (hsymm : idemᵀ = idem)
    (hidem : idem * idem = idem) (htrace : Matrix.trace idem < 2)
    (rowOne rowTwo colOne colTwo : Fin dim) :
    idem rowOne colOne * idem rowTwo colTwo
      = idem rowOne colTwo * idem rowTwo colOne := by
  classical
  set firstColumn : Fin dim → ℝ := idem *ᵥ (Pi.single colOne 1 : Fin dim → ℝ)
    with hfirstColumn
  set secondColumn : Fin dim → ℝ := idem *ᵥ (Pi.single colTwo 1 : Fin dim → ℝ)
    with hsecondColumn
  have hfirstEntry : ∀ rowIndex : Fin dim, firstColumn rowIndex = idem rowIndex colOne := by
    intro rowIndex
    rw [hfirstColumn, mulVec_single_one_apply]
  have hsecondEntry : ∀ rowIndex : Fin dim, secondColumn rowIndex = idem rowIndex colTwo := by
    intro rowIndex
    rw [hsecondColumn, mulVec_single_one_apply]
  by_cases hzero : firstColumn = 0
  · have hone : idem rowOne colOne = 0 := by
      rw [← hfirstEntry rowOne, hzero]
      rfl
    have htwo : idem rowTwo colOne = 0 := by
      rw [← hfirstEntry rowTwo, hzero]
      rfl
    rw [hone, htwo, zero_mul, mul_zero]
  · have hparallel := parallel_of_fixed_of_trace_lt_two hsymm hidem htrace
      (first := firstColumn) (second := secondColumn)
      (by rw [hfirstColumn]; exact symmIdem_column_fixed hidem colOne)
      (by rw [hsecondColumn]; exact symmIdem_column_fixed hidem colTwo) hzero
    set ratio : ℝ := (firstColumn ⬝ᵥ secondColumn) / (firstColumn ⬝ᵥ firstColumn)
      with hratio
    have hrowOne : idem rowOne colTwo = ratio * idem rowOne colOne := by
      have hentry := congrFun hparallel rowOne
      rw [hsecondEntry rowOne] at hentry
      simpa [hfirstEntry rowOne, hratio] using hentry
    have hrowTwo : idem rowTwo colTwo = ratio * idem rowTwo colOne := by
      have hentry := congrFun hparallel rowTwo
      rw [hsecondEntry rowTwo] at hentry
      simpa [hfirstEntry rowTwo, hratio] using hentry
    rw [hrowOne, hrowTwo]
    ring

/-- **THE TRACE-ZERO COLLAPSE.**  A symmetric idempotent of trace less
than one is the zero matrix: every column is a fixed vector, thus every
column vanishes. -/
theorem eq_zero_of_symmIdem_trace_lt_one (hsymm : idemᵀ = idem)
    (hidem : idem * idem = idem) (htrace : Matrix.trace idem < 1) :
    idem = 0 := by
  ext rowIndex colIndex
  have hcolumn : idem *ᵥ (idem *ᵥ (Pi.single colIndex 1 : Fin dim → ℝ))
      = idem *ᵥ (Pi.single colIndex 1 : Fin dim → ℝ) := symmIdem_column_fixed hidem colIndex
  have hzero := eq_zero_of_fixed_of_trace_lt_one hsymm hidem htrace hcolumn
  have hentry := congrFun hzero rowIndex
  rw [mulVec_single_one_apply] at hentry
  simpa using hentry

/-- **THE POSITIVE TRACE END.**  A symmetric idempotent of positive
trace fixes a nonzero vector: some diagonal entry is nonzero, and that
column is fixed and alive. -/
theorem exists_fixed_of_symmIdem_trace_pos (hidem : idem * idem = idem)
    (htrace : 0 < Matrix.trace idem) :
    ∃ fixedVec : Fin dim → ℝ, fixedVec ≠ 0 ∧ idem *ᵥ fixedVec = fixedVec := by
  classical
  have htraceSum : Matrix.trace idem = ∑ index : Fin dim, idem index index := rfl
  have hsum : ∑ index : Fin dim, idem index index ≠ 0 := by
    rw [← htraceSum]
    exact ne_of_gt htrace
  obtain ⟨liveIndex, _, hlive⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨idem *ᵥ (Pi.single liveIndex 1 : Fin dim → ℝ), ?_,
    symmIdem_column_fixed hidem liveIndex⟩
  intro hcontra
  have hentry := congrFun hcontra liveIndex
  rw [mulVec_single_one_apply] at hentry
  exact hlive (by simpa using hentry)

/-- The diagonal of a symmetric idempotent is the energy of its column. -/
theorem symmIdem_diag_eq_column_energy (hsymm : idemᵀ = idem) (hidem : idem * idem = idem)
    (index : Fin dim) : idem index index = ∑ rowIndex : Fin dim, idem rowIndex index ^ 2 := by
  conv_lhs => rw [← hidem]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun rowIndex _ => ?_
  have hflip : idem index rowIndex = idem rowIndex index := by
    conv_lhs => rw [← hsymm]
    rfl
  rw [hflip]
  ring

/-- The diagonal of a symmetric idempotent is nonnegative. -/
theorem symmIdem_diag_nonneg (hsymm : idemᵀ = idem) (hidem : idem * idem = idem)
    (index : Fin dim) : 0 ≤ idem index index := by
  rw [symmIdem_diag_eq_column_energy hsymm hidem index]
  exact Finset.sum_nonneg fun rowIndex _ => sq_nonneg _

/-- **THE ZERO DIAGONAL KILL.**  A symmetric idempotent with a zero
diagonal entry annihilates that coordinate axis: the diagonal entry is
the energy of the column. -/
theorem symmIdem_mulVec_single_eq_zero_of_diag_eq_zero (hsymm : idemᵀ = idem)
    (hidem : idem * idem = idem) {index : Fin dim} (hzero : idem index index = 0) :
    idem *ᵥ (Pi.single index 1 : Fin dim → ℝ) = 0 := by
  classical
  have henergy : ∑ rowIndex : Fin dim, idem rowIndex index ^ 2 = 0 := by
    rw [← symmIdem_diag_eq_column_energy hsymm hidem index]
    exact hzero
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg
    (fun rowIndex _ => sq_nonneg (idem rowIndex index))).mp henergy
  funext rowIndex
  rw [mulVec_single_one_apply]
  have hsquare := hterms rowIndex (Finset.mem_univ rowIndex)
  have hentryZero : idem rowIndex index = 0 := by
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsquare
  rw [hentryZero]
  rfl

end LowTrace

/-! ## Layer 2 — the capture frame is a chart-fixed symmetric idempotent -/

section CaptureLaws

variable {size basisCount : ℕ}
variable {projection : Matrix (Fin size) (Fin size) ℝ}
variable {basisColumns : Matrix (Fin size) (Fin basisCount) ℝ}
variable {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
variable {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}

/-- The capture frame is the chart minus its residue. -/
theorem captureFrame_eq_sub :
    captureFrame basisColumns coeff
      = projection - captureResidue projection basisColumns coeff := by
  rw [captureResidue, sub_sub_cancel]

/-- **THE CHART FIXES THE CAPTURE FRAME.**  The representation law moves
the chart onto the coefficient matrix, and idempotence of the
coefficient matrix absorbs it. -/
theorem chart_mul_captureFrame (hcoeffIdem : coeff * coeff = coeff)
    (hrep : projection * basisColumns = basisColumns * coeff) :
    projection * captureFrame basisColumns coeff = captureFrame basisColumns coeff := by
  have hleftSide : projection * captureFrame basisColumns coeff
      = (projection * basisColumns)
        * (coeff * ((basisColumnsᵀ * basisColumns)⁻¹ * basisColumnsᵀ)) := by
    simp only [captureFrame, Matrix.mul_assoc]
  rw [hleftSide, hrep]
  simp only [captureFrame, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc coeff coeff, hcoeffIdem]

/-- **THE CHART FIXES THE CAPTURE RESIDUE.** -/
theorem chart_mul_captureResidue (hidem : projection * projection = projection)
    (hcoeffIdem : coeff * coeff = coeff)
    (hrep : projection * basisColumns = basisColumns * coeff) :
    projection * captureResidue projection basisColumns coeff
      = captureResidue projection basisColumns coeff := by
  rw [captureResidue, Matrix.mul_sub, hidem, chart_mul_captureFrame hcoeffIdem hrep]

/-- The capture residue fixes the chart on the right too. -/
theorem captureResidue_mul_chart (hPsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hleft : leftInv * basisColumns = 1)
    (hcoeffIdem : coeff * coeff = coeff)
    (hrep : projection * basisColumns = basisColumns * coeff) :
    captureResidue projection basisColumns coeff * projection
      = captureResidue projection basisColumns coeff := by
  have hflip := congrArg Matrix.transpose (chart_mul_captureResidue hidem hcoeffIdem hrep)
  rw [Matrix.transpose_mul, hPsymm,
    captureResidue_transpose hPsymm hidem hleft hrep] at hflip
  exact hflip

/-- The capture frame is symmetric. -/
theorem captureFrame_transpose (hPsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hleft : leftInv * basisColumns = 1)
    (hrep : projection * basisColumns = basisColumns * coeff) :
    (captureFrame basisColumns coeff)ᵀ = captureFrame basisColumns coeff := by
  rw [captureFrame_eq_sub (projection := projection), Matrix.transpose_sub, hPsymm,
    captureResidue_transpose hPsymm hidem hleft hrep]

/-- The capture frame is idempotent. -/
theorem captureFrame_mul_self (hPsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hleft : leftInv * basisColumns = 1)
    (hcoeffIdem : coeff * coeff = coeff)
    (hrep : projection * basisColumns = basisColumns * coeff) :
    captureFrame basisColumns coeff * captureFrame basisColumns coeff
      = captureFrame basisColumns coeff := by
  rw [captureFrame_eq_sub (projection := projection), Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub, hidem, chart_mul_captureResidue hidem hcoeffIdem hrep,
    captureResidue_mul_chart hPsymm hidem hleft hcoeffIdem hrep,
    captureResidue_mul_self hPsymm hidem hleft hrep]
  abel

/-- The capture frame has a nonnegative diagonal. -/
theorem captureFrame_diag_nonneg (hPsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hleft : leftInv * basisColumns = 1)
    (hcoeffIdem : coeff * coeff = coeff)
    (hrep : projection * basisColumns = basisColumns * coeff) (index : Fin size) :
    0 ≤ captureFrame basisColumns coeff index index :=
  symmIdem_diag_nonneg (captureFrame_transpose hPsymm hidem hleft hrep)
    (captureFrame_mul_self hPsymm hidem hleft hcoeffIdem hrep) index

/-- A residue-fixed vector is a chart-fixed vector. -/
theorem chart_mulVec_eq_self_of_captureResidue_fixed
    (hidem : projection * projection = projection)
    (hcoeffIdem : coeff * coeff = coeff)
    (hrep : projection * basisColumns = basisColumns * coeff)
    {fixedVec : Fin size → ℝ}
    (hfix : captureResidue projection basisColumns coeff *ᵥ fixedVec = fixedVec) :
    projection *ᵥ fixedVec = fixedVec := by
  conv_lhs => rw [← hfix]
  rw [Matrix.mulVec_mulVec, chart_mul_captureResidue hidem hcoeffIdem hrep, hfix]

/-- The residue splits the chart action on every vector. -/
theorem chart_mulVec_eq_captureFrame_add_captureResidue (vec : Fin size → ℝ) :
    projection *ᵥ vec
      = captureFrame basisColumns coeff *ᵥ vec
        + captureResidue projection basisColumns coeff *ᵥ vec := by
  rw [← Matrix.add_mulVec, captureFrame_add_captureResidue]

end CaptureLaws

/-! ## Layer 3 — the pair direction and the chart minor identity -/

section PairDirection

variable {size : ℕ}

/-- The pair direction of two atoms at a scale. -/
def pairDirection (atomOne atomTwo : Fin size) (scale : ℝ) : Fin size → ℝ :=
  (Pi.single atomTwo 1 : Fin size → ℝ) - scale • (Pi.single atomOne 1 : Fin size → ℝ)

/-- The pair direction is alive at its right atom. -/
theorem pairDirection_apply_right {atomOne atomTwo : Fin size} (hne : atomOne ≠ atomTwo)
    (scale : ℝ) : pairDirection atomOne atomTwo scale atomTwo = 1 := by
  simp [pairDirection, hne]

/-- The pair direction dies off its pair. -/
theorem pairDirection_apply_off {atomOne atomTwo : Fin size} (scale : ℝ)
    {atomIndex : Fin size} (hone : atomIndex ≠ atomOne) (htwo : atomIndex ≠ atomTwo) :
    pairDirection atomOne atomTwo scale atomIndex = 0 := by
  simp [pairDirection, hone, htwo]

/-- The pair direction is nonzero. -/
theorem pairDirection_ne_zero {atomOne atomTwo : Fin size} (hne : atomOne ≠ atomTwo)
    (scale : ℝ) : pairDirection atomOne atomTwo scale ≠ 0 := by
  intro hcontra
  have hentry := congrFun hcontra atomTwo
  rw [pairDirection_apply_right hne scale] at hentry
  exact one_ne_zero hentry

/-- A matrix reads the pair direction as the difference of two columns. -/
theorem mulVec_pairDirection_apply (mat : Matrix (Fin size) (Fin size) ℝ)
    (atomOne atomTwo : Fin size) (scale : ℝ) (rowIndex : Fin size) :
    (mat *ᵥ pairDirection atomOne atomTwo scale) rowIndex
      = mat rowIndex atomTwo - scale * mat rowIndex atomOne := by
  rw [pairDirection, Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_single_one_apply]

end PairDirection

section PairMinor

variable {size rank basisCount : ℕ} {activeIndex : Type}
variable {projection : Matrix (Fin size) (Fin size) ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisLabel : Fin basisCount → activeIndex}
variable {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
variable {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}

/-- The capture frame kills the pair direction of a clone pair. -/
theorem captureFrame_mulVec_pairDirection_eq_zero {atomOne atomTwo : Fin size} {scale : ℝ}
    (hclone : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) atomTwo = scale * tightDir (basisLabel slot) atomOne) :
    captureFrame (tightBasisColumns tightDir basisLabel) coeff
        *ᵥ pairDirection atomOne atomTwo scale = 0 :=
  captureFrame_mulVec_eq_zero_of_basis_dot
    (transpose_basisColumns_mulVec_eq_zero (basis_dot_pairDirection_eq_zero hclone))

/-- **THE CAPTURE PAIR BLOCK.**  At a clone pair the capture frame is
the rank-one block of its left diagonal entry against the scale. -/
theorem captureFrame_pair_entries_of_clone
    (hPsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hrep : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {atomOne atomTwo : Fin size} {scale : ℝ}
    (hclone : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) atomTwo = scale * tightDir (basisLabel slot) atomOne) :
    captureFrame (tightBasisColumns tightDir basisLabel) coeff atomOne atomTwo
        = scale * captureFrame (tightBasisColumns tightDir basisLabel) coeff atomOne atomOne
      ∧ captureFrame (tightBasisColumns tightDir basisLabel) coeff atomTwo atomTwo
        = scale ^ 2
          * captureFrame (tightBasisColumns tightDir basisLabel) coeff atomOne atomOne := by
  set frame := captureFrame (tightBasisColumns tightDir basisLabel) coeff with hframe
  have hkill : frame *ᵥ pairDirection atomOne atomTwo scale = 0 := by
    rw [hframe]
    exact captureFrame_mulVec_pairDirection_eq_zero hclone
  have hsymmFrame : frameᵀ = frame := by
    rw [hframe]
    exact captureFrame_transpose hPsymm hidem hleft hrep
  have hleftEntry := congrFun hkill atomOne
  have hrightEntry := congrFun hkill atomTwo
  rw [mulVec_pairDirection_apply] at hleftEntry hrightEntry
  have hflip : frame atomTwo atomOne = frame atomOne atomTwo := by
    conv_lhs => rw [← hsymmFrame]
    rfl
  have hfirst : frame atomOne atomTwo = scale * frame atomOne atomOne := by
    have := hleftEntry
    simp only [Pi.zero_apply] at this
    linarith
  refine ⟨hfirst, ?_⟩
  have hsecond := hrightEntry
  simp only [Pi.zero_apply] at hsecond
  rw [hflip, hfirst] at hsecond
  nlinarith [hsecond]

/-- **THE CHART PAIR MINOR IDENTITY.**  At a clone pair the chart minor
factors into the capture diagonal and the pair form of the chart.  The
residue minor vanishes because the residue trace is below two. -/
theorem chart_pair_minor_eq_captureFrame_form
    (hPsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hrep : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (htraceGap : Matrix.trace projection - Matrix.trace coeff < 2)
    {atomOne atomTwo : Fin size} {scale : ℝ}
    (hclone : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) atomTwo = scale * tightDir (basisLabel slot) atomOne) :
    projection atomOne atomOne * projection atomTwo atomTwo
        - projection atomOne atomTwo * projection atomOne atomTwo
      = captureFrame (tightBasisColumns tightDir basisLabel) coeff atomOne atomOne
        * (projection atomTwo atomTwo
            - 2 * scale * projection atomOne atomTwo
            + scale ^ 2 * projection atomOne atomOne) := by
  classical
  set basisCols := tightBasisColumns tightDir basisLabel with hbasisCols
  set frame := captureFrame basisCols coeff with hframe
  set residue := captureResidue projection basisCols coeff with hresidue
  have hRsymm : residueᵀ = residue := by
    rw [hresidue]
    exact captureResidue_transpose hPsymm hidem hleft hrep
  have hRidem : residue * residue = residue := by
    rw [hresidue]
    exact captureResidue_mul_self hPsymm hidem hleft hrep
  have hRtrace : Matrix.trace residue < 2 := by
    rw [hresidue, captureResidue_trace hPsymm hidem hleft hrep]
    exact htraceGap
  have hminor := symmIdem_minor_eq_of_trace_lt_two hRsymm hRidem hRtrace
    atomOne atomTwo atomOne atomTwo
  have hentry : ∀ rowIndex colIndex : Fin size,
      residue rowIndex colIndex = projection rowIndex colIndex - frame rowIndex colIndex := by
    intro rowIndex colIndex
    rw [hresidue, hframe, captureResidue, Matrix.sub_apply]
  obtain ⟨hcross, hright⟩ := captureFrame_pair_entries_of_clone hPsymm hidem hleft hrep hclone
  rw [hbasisCols.symm] at hcross hright
  rw [← hframe] at hcross hright
  have hRflipEntry : residue atomTwo atomOne = residue atomOne atomTwo := by
    conv_lhs => rw [← hRsymm]
    rfl
  rw [hentry atomOne atomOne, hentry atomTwo atomTwo] at hminor
  rw [hentry atomOne atomTwo, hentry atomTwo atomOne] at hminor
  have hPflip : projection atomTwo atomOne = projection atomOne atomTwo := by
    conv_lhs => rw [← hPsymm]
    rfl
  have hFflip : frame atomTwo atomOne = frame atomOne atomTwo := by
    have hsymmFrame : frameᵀ = frame := by
      rw [hframe]
      exact captureFrame_transpose hPsymm hidem hleft hrep
    conv_lhs => rw [← hsymmFrame]
    rfl
  rw [hPflip, hFflip] at hminor
  rw [hright, hcross] at hminor
  clear hRflipEntry
  linear_combination hminor

end PairMinor

/-! ## Layer 4 — the three positivities at a crux -/

section CruxPositivity

variable {crux : SixThreeCrux}

/-- The chart column of an atom is the atom axis read by the chart. -/
theorem chart_column_dotProduct (crux : SixThreeCrux) (rowIndex colIndex : Fin 6) :
    ((chartPointOfDesign crux.design).chart *ᵥ (Pi.single rowIndex 1 : Fin 6 → ℝ))
        ⬝ᵥ ((chartPointOfDesign crux.design).chart
          *ᵥ (Pi.single colIndex 1 : Fin 6 → ℝ))
      = (chartPointOfDesign crux.design).chart rowIndex colIndex := by
  have hsymm : ((chartPointOfDesign crux.design).chart)ᵀ
      = (chartPointOfDesign crux.design).chart := (chartPointOfDesign crux.design).isSymmetric
  have hidem : (chartPointOfDesign crux.design).chart
      * (chartPointOfDesign crux.design).chart
      = (chartPointOfDesign crux.design).chart := projectionOfDesign_mul_self crux.design
  have hexpand : ((chartPointOfDesign crux.design).chart
        *ᵥ (Pi.single rowIndex 1 : Fin 6 → ℝ))
      ⬝ᵥ ((chartPointOfDesign crux.design).chart *ᵥ (Pi.single colIndex 1 : Fin 6 → ℝ))
      = ∑ index : Fin 6, (chartPointOfDesign crux.design).chart index rowIndex
          * (chartPointOfDesign crux.design).chart index colIndex := by
    simp only [dotProduct, mulVec_single_one_apply]
  rw [hexpand]
  have hflip : ∀ index : Fin 6, (chartPointOfDesign crux.design).chart index rowIndex
      = (chartPointOfDesign crux.design).chart rowIndex index := by
    intro index
    conv_lhs => rw [← hsymm]
    rfl
  have hrewrite : ∑ index : Fin 6, (chartPointOfDesign crux.design).chart index rowIndex
        * (chartPointOfDesign crux.design).chart index colIndex
      = ∑ index : Fin 6, (chartPointOfDesign crux.design).chart rowIndex index
        * (chartPointOfDesign crux.design).chart index colIndex :=
    Finset.sum_congr rfl fun index _ => by rw [hflip index]
  rw [hrewrite, ← Matrix.mul_apply, hidem]

/-- **THE CHART PAIR MINOR IS POSITIVE.**  A vanishing minor makes the
two chart columns proportional, thus the chart kills a direction
supported on the atom pair, thus the two design atoms are parallel. -/
theorem SixThreeCrux.chart_pair_minor_pos (crux : SixThreeCrux)
    {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo) :
    0 < (chartPointOfDesign crux.design).chart atomOne atomOne
        * (chartPointOfDesign crux.design).chart atomTwo atomTwo
      - (chartPointOfDesign crux.design).chart atomOne atomTwo
        * (chartPointOfDesign crux.design).chart atomOne atomTwo := by
  classical
  set chart := (chartPointOfDesign crux.design).chart with hchart
  set leftColumn : Fin 6 → ℝ := chart *ᵥ (Pi.single atomOne 1 : Fin 6 → ℝ) with hleftColumn
  set rightColumn : Fin 6 → ℝ := chart *ᵥ (Pi.single atomTwo 1 : Fin 6 → ℝ) with hrightColumn
  have hleftEnergy : leftColumn ⬝ᵥ leftColumn = chart atomOne atomOne := by
    rw [hleftColumn, hchart]
    exact chart_column_dotProduct crux atomOne atomOne
  have hrightEnergy : rightColumn ⬝ᵥ rightColumn = chart atomTwo atomTwo := by
    rw [hrightColumn, hchart]
    exact chart_column_dotProduct crux atomTwo atomTwo
  have hcross : leftColumn ⬝ᵥ rightColumn = chart atomOne atomTwo := by
    rw [hleftColumn, hrightColumn, hchart]
    exact chart_column_dotProduct crux atomOne atomTwo
  have hleftPos : 0 < chart atomOne atomOne := crux.chart_diagonal_pos atomOne
  set gapVec : Fin 6 → ℝ :=
    (leftColumn ⬝ᵥ leftColumn) • rightColumn - (leftColumn ⬝ᵥ rightColumn) • leftColumn
    with hgapVec
  have hgapEnergy : gapVec ⬝ᵥ gapVec
      = (chart atomOne atomOne)
        * (chart atomOne atomOne * chart atomTwo atomTwo
          - chart atomOne atomTwo * chart atomOne atomTwo) := by
    rw [hgapVec]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    rw [hleftEnergy, hrightEnergy, hcross, dotProduct_comm rightColumn leftColumn, hcross]
    ring
  have hgapNe : gapVec ≠ 0 := by
    intro hcontra
    set scale : ℝ := (leftColumn ⬝ᵥ rightColumn) / (leftColumn ⬝ᵥ leftColumn) with hscale
    have hproportional : rightColumn = scale • leftColumn := by
      have hzero : (leftColumn ⬝ᵥ leftColumn) • rightColumn
          = (leftColumn ⬝ᵥ rightColumn) • leftColumn := by
        rw [hgapVec] at hcontra
        exact sub_eq_zero.mp hcontra
      funext index
      have hentry := congrFun hzero index
      simp only [Pi.smul_apply, smul_eq_mul] at hentry ⊢
      rw [hscale, hleftEnergy] at *
      field_simp
      linarith [hentry]
    have hkernel : projectionOfDesign crux.design
        *ᵥ pairDirection atomOne atomTwo scale = 0 := by
      funext index
      rw [mulVec_pairDirection_apply]
      have hleftEntry : chart index atomOne = leftColumn index := by
        rw [hleftColumn, mulVec_single_one_apply]
      have hrightEntry : chart index atomTwo = rightColumn index := by
        rw [hrightColumn, mulVec_single_one_apply]
      have hcompute : (projectionOfDesign crux.design) index atomTwo
          - scale * (projectionOfDesign crux.design) index atomOne = 0 := by
        rw [show (projectionOfDesign crux.design) = chart from rfl, hleftEntry, hrightEntry,
          hproportional]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hcompute]
      rfl
    exact crux.hasNoParallelPair
      (hasParallelPair_of_projectionOfDesign_mulVec_eq_zero_on_support_pair
        crux.design hkernel hne (by rw [pairDirection_apply_right hne]; exact one_ne_zero)
        fun atomIndex hone htwo => pairDirection_apply_off scale hone htwo)
  have hpos : 0 < gapVec ⬝ᵥ gapVec := dotProduct_self_pos hgapNe
  rw [hgapEnergy] at hpos
  nlinarith [hpos, hleftPos]

/-- **THE PAIR FORM OF THE CHART IS POSITIVE.**  A vanishing pair form
would make the chart kill the pair direction. -/
theorem SixThreeCrux.chart_pair_form_pos (crux : SixThreeCrux)
    {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo) (scale : ℝ) :
    0 < (chartPointOfDesign crux.design).chart atomTwo atomTwo
      - 2 * scale * (chartPointOfDesign crux.design).chart atomOne atomTwo
      + scale ^ 2 * (chartPointOfDesign crux.design).chart atomOne atomOne := by
  have hminor := crux.chart_pair_minor_pos hne
  have hleftPos : 0 < (chartPointOfDesign crux.design).chart atomOne atomOne :=
    crux.chart_diagonal_pos atomOne
  nlinarith [hminor, hleftPos, sq_nonneg (scale * (chartPointOfDesign crux.design).chart
    atomOne atomOne - (chartPointOfDesign crux.design).chart atomOne atomTwo)]

end CruxPositivity

/-! ## Layer 5 — the chart of a crux -/

section CruxChart

/-- The chart of a crux is symmetric. -/
theorem SixThreeCrux.chart_transpose (crux : SixThreeCrux) :
    ((chartPointOfDesign crux.design).chart)ᵀ = (chartPointOfDesign crux.design).chart :=
  (chartPointOfDesign crux.design).isSymmetric

/-- The chart of a crux is idempotent. -/
theorem SixThreeCrux.chart_mul_self (crux : SixThreeCrux) :
    (chartPointOfDesign crux.design).chart * (chartPointOfDesign crux.design).chart
      = (chartPointOfDesign crux.design).chart :=
  projectionOfDesign_mul_self crux.design

/-- The chart of a crux has trace three. -/
theorem SixThreeCrux.chart_trace (crux : SixThreeCrux) :
    Matrix.trace (chartPointOfDesign crux.design).chart = 3 := by
  have htraceRank : Matrix.trace (projectionOfDesign crux.design) = ((3 : ℕ) : ℝ) :=
    trace_projectionOfDesign crux.design
  norm_num at htraceRank
  exact htraceRank

end CruxChart

/-! ## Layer 6 — the chart null and chart fixed support laws -/

section SupportLaws

/-- **A CHART NULL DIRECTION IS NOT A SINGLETON.**  A direction that the
chart kills and that lives at one atom alone puts a zero on the chart
diagonal, which the all-heavy floor refuses. -/
theorem SixThreeCrux.false_of_chart_null_singleton (crux : SixThreeCrux)
    {nullVec : Fin 6 → ℝ} {liveAtom : Fin 6} (hlive : nullVec liveAtom ≠ 0)
    (hsupport : ∀ atomIndex, atomIndex ≠ liveAtom → nullVec atomIndex = 0)
    (hnull : (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0) : False := by
  classical
  have hentry := congrFun hnull liveAtom
  have hexpand : ((chartPointOfDesign crux.design).chart *ᵥ nullVec) liveAtom
      = (chartPointOfDesign crux.design).chart liveAtom liveAtom * nullVec liveAtom := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_single liveAtom (fun atomIndex _ hne => ?_) (fun hcontra => ?_)
    · rw [hsupport atomIndex hne, mul_zero]
    · exact absurd (Finset.mem_univ liveAtom) hcontra
  rw [hexpand] at hentry
  have hdiag := crux.chart_diagonal_pos liveAtom
  rcases mul_eq_zero.mp hentry with hzero | hzero
  · exact absurd hzero (ne_of_gt hdiag)
  · exact hlive hzero

/-- **A CHART NULL DIRECTION IS NOT A PAIR.**  A direction that the
chart kills and that lives inside an atom pair is an atom dependency of
two atoms, thus a parallel pair. -/
theorem SixThreeCrux.false_of_chart_null_pair (crux : SixThreeCrux)
    {nullVec : Fin 6 → ℝ} {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo)
    (hlive : nullVec atomTwo ≠ 0)
    (hsupport : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      nullVec atomIndex = 0)
    (hnull : (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0) : False :=
  crux.hasNoParallelPair
    (hasParallelPair_of_projectionOfDesign_mulVec_eq_zero_on_support_pair
      crux.design hnull hne hlive hsupport)

/-- **THE COPLANARITY READING OF A CHART FIXED DIRECTION.**  The chart
is the Gram matrix of the scaled atom rows, thus a fixed vector is the
image of an atom-space direction, thus every atom off the support of the
fixed vector is orthogonal to that direction. -/
theorem SixThreeCrux.exists_orthogonal_of_chart_fixed (crux : SixThreeCrux)
    {fixedVec : Fin 6 → ℝ} (hne : fixedVec ≠ 0)
    (hfix : (chartPointOfDesign crux.design).chart *ᵥ fixedVec = fixedVec) :
    ∃ normalVec : Fin 3 → ℝ, normalVec ≠ 0
      ∧ ∀ atomIndex : Fin 6, fixedVec atomIndex = 0
        → crux.design.atom atomIndex ⬝ᵥ normalVec = 0 := by
  classical
  have hrowEntry : ∀ (vec : Fin 3 → ℝ) (atomIndex : Fin 6),
      (scaledAtomRows crux.design *ᵥ vec) atomIndex
        = Real.sqrt (crux.design.weight atomIndex)
          * (crux.design.atom atomIndex ⬝ᵥ vec) := by
    intro vec atomIndex
    simp only [Matrix.mulVec, dotProduct, scaledAtomRows, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun coord _ => by ring
  have hrecover : scaledAtomRows crux.design
      *ᵥ ((scaledAtomRows crux.design)ᵀ *ᵥ fixedVec) = fixedVec := by
    rw [Matrix.mulVec_mulVec]
    exact hfix
  refine ⟨(scaledAtomRows crux.design)ᵀ *ᵥ fixedVec, ?_, ?_⟩
  · intro hcontra
    rw [hcontra, Matrix.mulVec_zero] at hrecover
    exact hne hrecover.symm
  · intro atomIndex hzero
    have hentry := congrFun hrecover atomIndex
    rw [hrowEntry, hzero] at hentry
    have hweight : 0 < Real.sqrt (crux.design.weight atomIndex) :=
      Real.sqrt_pos.mpr (crux.design.weight_pos atomIndex)
    rcases mul_eq_zero.mp hentry with hcontra | hgood
    · exact absurd hcontra (ne_of_gt hweight)
    · exact hgood

end SupportLaws


/-! ## Layer 7 — the residue line of a rank-four frame -/

section RankFourLine

variable {crux : SixThreeCrux}

/-- The capture residue of a rank-four frame. -/
noncomputable def RankFourFrame.lineResidue (frame : RankFourFrame crux) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  captureResidue (chartPointOfDesign crux.design).chart
    (tightBasisColumns frame.tightDir frame.basisLabel) frame.coeff

/-- The line residue of a rank-four frame is symmetric. -/
theorem RankFourFrame.lineResidue_transpose (frame : RankFourFrame crux) :
    (frame.lineResidue)ᵀ = frame.lineResidue :=
  captureResidue_transpose crux.chart_transpose crux.chart_mul_self frame.hleft
    frame.hrepresentation

/-- The line residue of a rank-four frame is idempotent. -/
theorem RankFourFrame.lineResidue_mul_self (frame : RankFourFrame crux) :
    frame.lineResidue * frame.lineResidue = frame.lineResidue :=
  captureResidue_mul_self crux.chart_transpose crux.chart_mul_self frame.hleft
    frame.hrepresentation

/-- **THE TRACE OF THE RANK-FOUR RESIDUE IS ONE.**  The chart trace is
three and the capture trace is two. -/
theorem RankFourFrame.lineResidue_trace (frame : RankFourFrame crux) :
    Matrix.trace frame.lineResidue = 1 := by
  rw [RankFourFrame.lineResidue,
    captureResidue_trace crux.chart_transpose crux.chart_mul_self frame.hleft
      frame.hrepresentation, crux.chart_trace, frame.htrace]
  norm_num

/-- The basis columns of a rank-four frame die on the line residue. -/
theorem RankFourFrame.basis_dot_lineResidue (frame : RankFourFrame crux)
    {vec : Fin 6 → ℝ} (hfix : frame.lineResidue *ᵥ vec = vec) (slot : Fin 4) :
    frame.tightDir (frame.basisLabel slot) ⬝ᵥ vec = 0 := by
  have hkill : (tightBasisColumns frame.tightDir frame.basisLabel)ᵀ * frame.lineResidue = 0 :=
    transpose_basis_mul_captureResidue crux.chart_transpose crux.chart_mul_self frame.hleft
      frame.hrepresentation
  have hzero : (tightBasisColumns frame.tightDir frame.basisLabel)ᵀ *ᵥ vec = 0 := by
    conv_lhs => rw [← hfix]
    rw [Matrix.mulVec_mulVec, hkill, Matrix.zero_mulVec]
  have hentry := congrFun hzero slot
  rw [transpose_basisColumns_mulVec_apply] at hentry
  exact hentry

/-- **THE RESIDUE LINE OF A RANK-FOUR FRAME.**  The residue has trace
one, thus it fixes a nonzero vector.  Every basis column annihilates
that vector and the chart fixes it. -/
theorem RankFourFrame.exists_capture_line (frame : RankFourFrame crux) :
    ∃ lineVec : Fin 6 → ℝ, lineVec ≠ 0
      ∧ frame.lineResidue *ᵥ lineVec = lineVec
      ∧ (∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) ⬝ᵥ lineVec = 0)
      ∧ (chartPointOfDesign crux.design).chart *ᵥ lineVec = lineVec := by
  obtain ⟨lineVec, hne, hfix⟩ := exists_fixed_of_symmIdem_trace_pos frame.lineResidue_mul_self
    (by rw [frame.lineResidue_trace]; norm_num)
  refine ⟨lineVec, hne, hfix, fun slot => frame.basis_dot_lineResidue hfix slot, ?_⟩
  exact chart_mulVec_eq_self_of_captureResidue_fixed crux.chart_mul_self frame.hidempotent
    frame.hrepresentation hfix

end RankFourLine

/-! ## Layer 8 — the live atoms of a chart null direction -/

section ChartNullLive

variable {crux : SixThreeCrux}

/-- **A CHART NULL DIRECTION LIVES OFF EVERY PAIR.**  A nonzero
direction that the chart kills is alive at some atom outside any named
pair of atoms: two live atoms already give a parallel pair. -/
theorem SixThreeCrux.exists_live_off_pair_of_chart_null (crux : SixThreeCrux)
    {nullVec : Fin 6 → ℝ} (hne : nullVec ≠ 0)
    (hnull : (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0)
    (atomOne atomTwo : Fin 6) :
    ∃ atomIndex : Fin 6, atomIndex ≠ atomOne ∧ atomIndex ≠ atomTwo
      ∧ nullVec atomIndex ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hsupport : ∀ atomIndex : Fin 6, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      nullVec atomIndex = 0 := fun atomIndex hone htwo => hnone atomIndex hone htwo
  by_cases hlive : nullVec atomTwo ≠ 0
  · by_cases hsame : atomOne = atomTwo
    · refine crux.false_of_chart_null_singleton (liveAtom := atomTwo) hlive ?_ hnull
      intro atomIndex hindex
      exact hsupport atomIndex (hsame ▸ hindex) hindex
    · exact crux.false_of_chart_null_pair hsame hlive hsupport hnull
  · rw [not_not] at hlive
    by_cases hleft : nullVec atomOne ≠ 0
    · refine crux.false_of_chart_null_singleton (liveAtom := atomOne) hleft ?_ hnull
      intro atomIndex hindex
      by_cases hcase : atomIndex = atomTwo
      · rw [hcase, hlive]
      · exact hsupport atomIndex hindex hcase
    · rw [not_not] at hleft
      refine hne ?_
      funext atomIndex
      by_cases hcase : atomIndex = atomOne
      · rw [hcase, hleft]; rfl
      · by_cases hcaseTwo : atomIndex = atomTwo
        · rw [hcaseTwo, hlive]; rfl
        · rw [hsupport atomIndex hcase hcaseTwo]; rfl

/-- **A CHART NULL DIRECTION IS ALIVE AT THREE ATOMS.**  The three atoms
come out of the pair law applied three times. -/
theorem SixThreeCrux.exists_three_live_of_chart_null (crux : SixThreeCrux)
    {nullVec : Fin 6 → ℝ} (hne : nullVec ≠ 0)
    (hnull : (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0) :
    ∃ atomOne atomTwo atomThree : Fin 6, atomOne ≠ atomTwo ∧ atomOne ≠ atomThree
      ∧ atomTwo ≠ atomThree ∧ nullVec atomOne ≠ 0 ∧ nullVec atomTwo ≠ 0
      ∧ nullVec atomThree ≠ 0 := by
  obtain ⟨first, _, _, hfirstLive⟩ :=
    crux.exists_live_off_pair_of_chart_null hne hnull 0 0
  obtain ⟨second, hsecondNe, _, hsecondLive⟩ :=
    crux.exists_live_off_pair_of_chart_null hne hnull first first
  obtain ⟨third, hthirdFirst, hthirdSecond, hthirdLive⟩ :=
    crux.exists_live_off_pair_of_chart_null hne hnull first second
  exact ⟨first, second, third, fun hcontra => hsecondNe hcontra.symm,
    fun hcontra => hthirdFirst hcontra.symm, fun hcontra => hthirdSecond hcontra.symm,
    hfirstLive, hsecondLive, hthirdLive⟩

end ChartNullLive

/-! ## Layer 9 — the zero residue kill -/

section ZeroResidue

variable {basisCount : ℕ} {activeIndex : Type}
variable {tightDir : activeIndex → (Fin 6 → ℝ)}
variable {basisLabel : Fin basisCount → activeIndex}
variable {leftInv : Matrix (Fin basisCount) (Fin 6) ℝ}
variable {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}

/-- **THE ZERO RESIDUE.**  When the capture trace reaches the chart rank
the capture residue is the zero matrix. -/
theorem SixThreeCrux.captureResidue_eq_zero_of_capture_trace_rank (crux : SixThreeCrux)
    (hrep : (chartPointOfDesign crux.design).chart
        * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (htrace : 3 ≤ Matrix.trace coeff) :
    captureResidue (chartPointOfDesign crux.design).chart
      (tightBasisColumns tightDir basisLabel) coeff = 0 := by
  refine eq_zero_of_symmIdem_trace_lt_one
    (captureResidue_transpose crux.chart_transpose crux.chart_mul_self hleft hrep)
    (captureResidue_mul_self crux.chart_transpose crux.chart_mul_self hleft hrep) ?_
  rw [captureResidue_trace crux.chart_transpose crux.chart_mul_self hleft hrep,
    crux.chart_trace]
  linarith

/-- **EVERY BASIS NULL DIRECTION IS CHART NULL AT A FULL CAPTURE
TRACE.**  The capture frame reads a direction only through the
transposed basis columns, and the residue is zero. -/
theorem SixThreeCrux.chart_mulVec_eq_zero_of_basis_null_of_capture_trace_rank
    (crux : SixThreeCrux)
    (hrep : (chartPointOfDesign crux.design).chart
        * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (htrace : 3 ≤ Matrix.trace coeff) {nullVec : Fin 6 → ℝ}
    (hnull : ∀ slot : Fin basisCount, tightDir (basisLabel slot) ⬝ᵥ nullVec = 0) :
    (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0 := by
  rw [chart_mulVec_eq_captureFrame_add_captureResidue
    (basisColumns := tightBasisColumns tightDir basisLabel) (coeff := coeff),
    crux.captureResidue_eq_zero_of_capture_trace_rank hrep hleft htrace,
    captureFrame_mulVec_eq_zero_of_basis_dot
      (transpose_basisColumns_mulVec_eq_zero hnull)]
  simp

/-- **THE ZERO RESIDUE KILL.**  A clone pair direction is a basis null
direction supported on an atom pair, thus at a full capture trace the
chart kills it, thus the two design atoms are parallel. -/
theorem SixThreeCrux.false_of_pair_null_of_capture_trace_rank (crux : SixThreeCrux)
    (hrep : (chartPointOfDesign crux.design).chart
        * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (htrace : 3 ≤ Matrix.trace coeff)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hclone : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) atomTwo = scale * tightDir (basisLabel slot) atomOne) :
    False :=
  crux.false_of_chart_null_pair hne
    (by rw [pairDirection_apply_right hne]; exact one_ne_zero)
    (fun atomIndex hone htwo => pairDirection_apply_off scale hone htwo)
    (crux.chart_mulVec_eq_zero_of_basis_null_of_capture_trace_rank hrep hleft htrace
      (basis_dot_pairDirection_eq_zero hclone))

/-- **THREE LIVE ATOMS OF A BASIS NULL DIRECTION AT A FULL CAPTURE
TRACE.**  Every nonzero basis null direction is then chart null, thus it
is alive at three atoms at least. -/
theorem SixThreeCrux.exists_three_live_of_basis_null_of_capture_trace_rank
    (crux : SixThreeCrux)
    (hrep : (chartPointOfDesign crux.design).chart
        * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (htrace : 3 ≤ Matrix.trace coeff) {nullVec : Fin 6 → ℝ} (hne : nullVec ≠ 0)
    (hnull : ∀ slot : Fin basisCount, tightDir (basisLabel slot) ⬝ᵥ nullVec = 0) :
    ∃ atomOne atomTwo atomThree : Fin 6, atomOne ≠ atomTwo ∧ atomOne ≠ atomThree
      ∧ atomTwo ≠ atomThree ∧ nullVec atomOne ≠ 0 ∧ nullVec atomTwo ≠ 0
      ∧ nullVec atomThree ≠ 0 :=
  crux.exists_three_live_of_chart_null hne
    (crux.chart_mulVec_eq_zero_of_basis_null_of_capture_trace_rank hrep hleft htrace hnull)

end ZeroResidue

/-! ## Layer 10 — the clone split at a rank-four frame -/

section CloneSplit

variable {crux : SixThreeCrux}

/-- **THE CLONE CHART SPLIT.**  At a clone pair either the chart fixes
the pair direction, or the pair direction minus its residue part is a
nonzero direction that both the basis and the chart annihilate. -/
theorem RankFourFrame.clone_chart_dichotomy (frame : RankFourFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ}
    (hclone : ∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne) :
    (chartPointOfDesign crux.design).chart *ᵥ pairDirection atomOne atomTwo scale
        = pairDirection atomOne atomTwo scale
      ∨ ∃ nullVec : Fin 6 → ℝ, nullVec ≠ 0
          ∧ (∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) ⬝ᵥ nullVec = 0)
          ∧ (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0 := by
  classical
  obtain ⟨lineVec, hlineNe, hlineFix, hlineBasis, hlineChart⟩ := frame.exists_capture_line
  have hpairBasis : ∀ slot : Fin 4,
      frame.tightDir (frame.basisLabel slot) ⬝ᵥ pairDirection atomOne atomTwo scale = 0 := by
    intro slot
    exact basis_dot_pairDirection_eq_zero hclone slot
  have hframeKill : captureFrame (tightBasisColumns frame.tightDir frame.basisLabel) frame.coeff
      *ᵥ pairDirection atomOne atomTwo scale = 0 :=
    captureFrame_mulVec_pairDirection_eq_zero hclone
  have hlineFrameKill : captureFrame (tightBasisColumns frame.tightDir frame.basisLabel)
      frame.coeff *ᵥ lineVec = 0 :=
    captureFrame_mulVec_eq_zero_of_basis_dot
      (transpose_basisColumns_mulVec_eq_zero hlineBasis)
  have hpairFixed : frame.lineResidue *ᵥ (frame.lineResidue
      *ᵥ pairDirection atomOne atomTwo scale)
      = frame.lineResidue *ᵥ pairDirection atomOne atomTwo scale := by
    rw [Matrix.mulVec_mulVec, frame.lineResidue_mul_self]
  have hparallel := parallel_of_fixed_of_trace_lt_two frame.lineResidue_transpose
    frame.lineResidue_mul_self (by rw [frame.lineResidue_trace]; norm_num)
    hlineFix hpairFixed hlineNe
  set ratio : ℝ := (lineVec ⬝ᵥ (frame.lineResidue *ᵥ pairDirection atomOne atomTwo scale))
    / (lineVec ⬝ᵥ lineVec) with hratio
  set splitVec : Fin 6 → ℝ := pairDirection atomOne atomTwo scale - ratio • lineVec
    with hsplitVec
  have hresidueSplit : frame.lineResidue *ᵥ splitVec = 0 := by
    rw [hsplitVec, Matrix.mulVec_sub, Matrix.mulVec_smul, hlineFix, hparallel, sub_self]
  have hframeSplit : captureFrame (tightBasisColumns frame.tightDir frame.basisLabel)
      frame.coeff *ᵥ splitVec = 0 := by
    rw [hsplitVec, Matrix.mulVec_sub, Matrix.mulVec_smul, hframeKill, hlineFrameKill,
      smul_zero, sub_zero]
  have hchartSplit : (chartPointOfDesign crux.design).chart *ᵥ splitVec = 0 := by
    rw [chart_mulVec_eq_captureFrame_add_captureResidue
      (basisColumns := tightBasisColumns frame.tightDir frame.basisLabel)
      (coeff := frame.coeff), hframeSplit]
    rw [show captureResidue (chartPointOfDesign crux.design).chart
        (tightBasisColumns frame.tightDir frame.basisLabel) frame.coeff
      = frame.lineResidue from rfl, hresidueSplit, add_zero]
  have hbasisSplit : ∀ slot : Fin 4,
      frame.tightDir (frame.basisLabel slot) ⬝ᵥ splitVec = 0 := by
    intro slot
    rw [hsplitVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, hpairBasis slot,
      hlineBasis slot, mul_zero, sub_zero]
  by_cases hzero : splitVec = 0
  · left
    have hpairEq : pairDirection atomOne atomTwo scale = ratio • lineVec := by
      rw [hsplitVec] at hzero
      exact sub_eq_zero.mp hzero
    rw [hpairEq, Matrix.mulVec_smul, hlineChart]
  · right
    exact ⟨splitVec, hzero, hbasisSplit, hchartSplit⟩

end CloneSplit

/-! ## Layer 11 — the rung readings of the pair minor -/

section RungReadings

variable {crux : SixThreeCrux}

/-- **THE PAIR MINOR IDENTITY AT A RANK-FOUR FRAME.** -/
theorem RankFourFrame.chart_pair_minor_eq (frame : RankFourFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ}
    (hclone : ∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne) :
    (chartPointOfDesign crux.design).chart atomOne atomOne
        * (chartPointOfDesign crux.design).chart atomTwo atomTwo
      - (chartPointOfDesign crux.design).chart atomOne atomTwo
        * (chartPointOfDesign crux.design).chart atomOne atomTwo
      = captureFrame (tightBasisColumns frame.tightDir frame.basisLabel) frame.coeff
          atomOne atomOne
        * ((chartPointOfDesign crux.design).chart atomTwo atomTwo
            - 2 * scale * (chartPointOfDesign crux.design).chart atomOne atomTwo
            + scale ^ 2 * (chartPointOfDesign crux.design).chart atomOne atomOne) := by
  refine chart_pair_minor_eq_captureFrame_form crux.chart_transpose crux.chart_mul_self
    frame.hleft frame.hrepresentation ?_ hclone
  rw [crux.chart_trace, frame.htrace]
  norm_num

/-- **THE CAPTURE DIAGONAL IS POSITIVE AT A CLONE PAIR.**  The chart
minor is positive and the pair form is positive, thus the capture
diagonal is their quotient. -/
theorem RankFourFrame.captureFrame_diag_pos_of_clone (frame : RankFourFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hclone : ∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne) :
    0 < captureFrame (tightBasisColumns frame.tightDir frame.basisLabel) frame.coeff
      atomOne atomOne := by
  have hidentity := frame.chart_pair_minor_eq hclone
  have hminor := crux.chart_pair_minor_pos hne
  have hform := crux.chart_pair_form_pos hne scale
  nlinarith [hidentity, hminor, hform]

/-- **THE CLONE PAIR OF A RANK-FIVE FRAME OF CAPTURE TRACE THREE IS
DEAD.**  The residue is zero, thus the chart kills the pair direction. -/
theorem RankFiveFrame.false_of_clone_pair_of_capture_trace_three (frame : RankFiveFrame crux)
    (htraceThree : Matrix.trace frame.coeff = 3)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hclone : ∀ slot : Fin 5, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne) :
    False :=
  crux.false_of_pair_null_of_capture_trace_rank frame.hrepresentation frame.hleft
    (le_of_eq htraceThree.symm) hne hclone

/-- **A CLONE PAIR PUTS A RANK-FIVE FRAME AT CAPTURE TRACE TWO.** -/
theorem RankFiveFrame.capture_trace_eq_two_of_clone (frame : RankFiveFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hclone : ∀ slot : Fin 5, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne) :
    Matrix.trace frame.coeff = 2 :=
  frame.htrace.resolve_right fun htraceThree =>
    frame.false_of_clone_pair_of_capture_trace_three htraceThree hne hclone

/-- **EVERY CLONE PAIR OF A RANK-SIX FRAME IS DEAD.**  The capture trace
is three at every rank-six frame, thus the residue is zero. -/
theorem RankSixFrame.false_of_clone_pair (frame : RankSixFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hclone : ∀ slot : Fin 6, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne) :
    False :=
  crux.false_of_pair_null_of_capture_trace_rank frame.hrepresentation frame.hleft
    (le_of_eq frame.htrace.symm) hne hclone

end RungReadings


/-! ## Layer 12 — the capture diagonal reads interiority -/

section CaptureInteriority

variable {crux : SixThreeCrux}

/-- **THE CAPTURE DIAGONAL READS INTERIORITY.**  At a boundary atom the
capture frame kills the atom axis, thus its diagonal entry vanishes.  A
positive capture diagonal thus forces a positive shifted weight. -/
theorem RankFourFrame.shifted_weight_pos_of_captureFrame_diag_pos (frame : RankFourFrame crux)
    {atomIndex : Fin 6}
    (hpos : 0 < captureFrame (tightBasisColumns frame.tightDir frame.basisLabel) frame.coeff
      atomIndex atomIndex) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex := by
  rcases lt_or_eq_of_le (crux.shifted_weight_nonneg atomIndex) with hlt | heq
  · exact hlt
  · exfalso
    have hkill := captureFrame_mulVec_single_eq_zero_of_boundary frame.hdata frame.hspan
      frame.hrepresentation frame.hleft heq.symm
    have hentry := congrFun hkill atomIndex
    rw [mulVec_single_one_apply] at hentry
    simp only [Pi.zero_apply] at hentry
    exact absurd hentry (ne_of_gt hpos)

/-- **THE CLONE PAIR IS INTERIOR, THROUGH THE CHART MINOR.**  A second
and independent proof of the proportional-row interior law: the chart
minor of the pair is positive, the pair form of the chart is positive,
thus the capture diagonal is positive. -/
theorem RankFourFrame.shifted_weight_pos_of_clone_minor (frame : RankFourFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hne : atomOne ≠ atomTwo)
    (hclone : ∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne :=
  frame.shifted_weight_pos_of_captureFrame_diag_pos
    (frame.captureFrame_diag_pos_of_clone hne hclone)

end CaptureInteriority

/-! ## Layer 13 — the narrowed thin clone residues -/

section NarrowedResidues

/-- **THE FIXED-LINE THIN CLONE RESIDUE.**  A thin clone pair whose pair
direction the chart FIXES dies.  The residue carries the design reading
for free: one nonzero direction of the atom space annihilates all four
atoms off the pair. -/
def RankFourOuterThinCloneFixedClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
    (atomOne atomTwo : Fin 6) (scale : ℝ) (freeSlot : Fin 4) (normalVec : Fin 3 → ℝ),
    atomOne ≠ atomTwo →
    atomOne ≠ data.atomU → atomOne ≠ data.atomV →
    atomTwo ≠ data.atomU → atomTwo ≠ data.atomV →
    (scale = 1 ∨ scale = -1) →
    (∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) atomTwo
        = scale * data.frame.tightDir (data.frame.basisLabel slot) atomOne) →
    (chartPointOfDesign crux.design).weight atomOne
      = (chartPointOfDesign crux.design).weight atomTwo →
    atomOne ∉ data.frame.activeSubset (data.frame.basisLabel freeSlot) →
    atomTwo ∉ data.frame.activeSubset (data.frame.basisLabel freeSlot) →
    (chartPointOfDesign crux.design).chart *ᵥ pairDirection atomOne atomTwo scale
      = pairDirection atomOne atomTwo scale →
    normalVec ≠ 0 →
    (∀ atomIndex : Fin 6, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      crux.design.atom atomIndex ⬝ᵥ normalVec = 0) →
    False

/-- **THE SPLIT THIN CLONE RESIDUE.**  A thin clone pair together with a
nonzero direction that BOTH the basis and the chart annihilate dies.
Such a direction is alive at three atoms or more by
`Gtz.SixThreeCrux.exists_three_live_of_chart_null`. -/
def RankFourOuterThinCloneSplitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
    (atomOne atomTwo : Fin 6) (scale : ℝ) (freeSlot : Fin 4) (nullVec : Fin 6 → ℝ),
    atomOne ≠ atomTwo →
    atomOne ≠ data.atomU → atomOne ≠ data.atomV →
    atomTwo ≠ data.atomU → atomTwo ≠ data.atomV →
    (scale = 1 ∨ scale = -1) →
    (∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) atomTwo
        = scale * data.frame.tightDir (data.frame.basisLabel slot) atomOne) →
    (chartPointOfDesign crux.design).weight atomOne
      = (chartPointOfDesign crux.design).weight atomTwo →
    atomOne ∉ data.frame.activeSubset (data.frame.basisLabel freeSlot) →
    atomTwo ∉ data.frame.activeSubset (data.frame.basisLabel freeSlot) →
    nullVec ≠ 0 →
    (∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) ⬝ᵥ nullVec = 0) →
    (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0 →
    False

/-- **THE THIN CLONE SPLITS IN TWO.**  The clone split of the rank-four
frame sends every thin clone pair to one of the two narrowed residues.
-/
theorem rankFourOuterThinCloneClosed_of_fixed_split
    (hfixed : RankFourOuterThinCloneFixedClosed)
    (hsplit : RankFourOuterThinCloneSplitClosed) :
    RankFourOuterThinCloneClosed := by
  intro crux data atomOne atomTwo scale freeSlot hne hOneU hOneV hTwoU hTwoV hscale
    hclone hweight hfreeOne hfreeTwo
  rcases data.frame.clone_chart_dichotomy hclone with hfix | hsplitVec
  · obtain ⟨normalVec, hnormalNe, hnormal⟩ :=
      crux.exists_orthogonal_of_chart_fixed (pairDirection_ne_zero hne scale) hfix
    exact hfixed crux data atomOne atomTwo scale freeSlot normalVec hne hOneU hOneV hTwoU
      hTwoV hscale hclone hweight hfreeOne hfreeTwo hfix hnormalNe
      fun atomIndex hone htwo => hnormal atomIndex (pairDirection_apply_off scale hone htwo)
  · obtain ⟨nullVec, hnullNe, hnullBasis, hnullChart⟩ := hsplitVec
    exact hsplit crux data atomOne atomTwo scale freeSlot nullVec hne hOneU hOneV hTwoU
      hTwoV hscale hclone hweight hfreeOne hfreeTwo hnullNe hnullBasis hnullChart

/-- **THE CLONE CLOSURE FROM THE TWO NARROWED RESIDUES.**  No
interiority is needed: the boundary residue line already reduced the
clone branch to its thin half. -/
theorem rankFourOuterCloneClosed_of_fixed_split
    (hfixed : RankFourOuterThinCloneFixedClosed)
    (hsplit : RankFourOuterThinCloneSplitClosed) :
    RankFourOuterCloneClosed :=
  rankFourOuterCloneClosed_of_thin (rankFourOuterThinCloneClosed_of_fixed_split hfixed hsplit)

/-- **THE NARROWED RANK-FOUR DISCHARGE OF CLOSURE ONE.**  The thin clone
input of `Gtz.rankFourSupportTwoClosed_of_thin_triple_interior` splits
into the fixed-line residue and the split residue. -/
theorem rankFourSupportTwoClosed_of_fixedSplit_triple_interior
    (hoff : RankFourOuterOffPairCircuitClosed)
    (hfixed : RankFourOuterThinCloneFixedClosed)
    (hsplit : RankFourOuterThinCloneSplitClosed)
    (htriple : RankFourOuterTripleNullClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
      (atomIndex : Fin 6),
      2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_thin_triple_interior hoff
    (rankFourOuterThinCloneClosed_of_fixed_split hfixed hsplit) htriple hinterior

end NarrowedResidues


end Gtz

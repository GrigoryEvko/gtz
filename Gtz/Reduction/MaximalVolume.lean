/-
# The maximal-volume bound — the classical benchmark GTZ conjecturally improves

The projection form (`Gtz/LinAlg/ProjectionForm.lean`) makes the classical
dictionary exact.  For an `n × k` matrix `A` with orthonormal columns, `P = A Aᵀ`
is the rank-`k` orthogonal projection onto the column space, and for a `k`-subset
`T` of rows,

    det (P restricted to T) = det (A_T)²      (the squared VOLUME)
    λ_min (P restricted to T) = σ_min (A_T)²

so GTZ — "some `k`-subset has `σ_min(A_T) ≥ 1/√n`" — is a statement about the
volumes of row submatrices.  That is exactly the setting of Goreinov and
Tyrtyshnikov's maximal-volume theory, whose classical bound is
`σ_min(A_T)² ≥ 1/(k(n−k) + 1)` at a maximal-volume `T`.

## What this file proves, and what it does not

PROVED here, all at the three-axiom baseline, all elementary — no eigenvalues, no
analysis, no matrix square roots:

* `det_projectionBlock_eq_sq_volume` — the squared-volume dictionary above.
* `gtzDenominator_add_deficit_eq_classical` — **the exact deficit**
  `k(n−k) + 1 = n + (k−1)(n−k−1)`.  So the classical constant IS the GTZ constant
  when `k = 1` or `n = k + 1`, and is weaker by exactly `(k−1)(n−k−1)` otherwise.
  At the campaign's rank-three object `(7,3)` the deficit is `2 · 3 = 6`: classical
  gives `1/13` where GTZ asks `1/7`.  This is the precise measure of how much GTZ
  demands beyond what is known.
* `quadForm_le_trace_mul_dotProduct` — for `S ⪰ 0`, `xᵀSx ≤ (tr S)·|x|²`, i.e.
  `λ_max(S) ≤ tr(S)` without naming an eigenvalue.  Proved from the `2 × 2`
  principal minors alone: `2 x_i x_j S_ij ≤ x_i² S_jj + x_j² S_ii` because
  `[[S_jj, −S_ij], [−S_ij, S_ii]]` is positive semidefinite, and the double sum
  symmetrizes to the trace.
* `quadForm_le_trace_sub_of_one_le` — the sharpened form for `S ⪰ 1`:
  `λ_max(S) ≤ tr(S) − (size − 1)`.  This is where the `+1` in the classical
  denominator comes from.
* `sum_det_frameMinors_rank` — Pythagoras for a frame's shadows: the `k`-subset
  squared volumes sum to one (Cauchy–Binet, in the shape already proved for designs
  as `sum_det_projectionMinors_rank`).
* `exists_maximalVolume_pick` — a maximal-volume injective pick exists and is
  nonsingular, the nonsingularity coming from Pythagoras.
* `det_selectedFrameRows_update` — **the maximality identity**: with `B = A M⁻¹`
  the solve matrix of a pick and `M = A_T`, a one-element swap has volume
  `det A_{T[j ← r]} = B_{rj} · det A_T`.  One step from
  `Matrix.det_updateRow_sum`, because the inserted row IS the solve combination.
* `abs_solveMatrix_le_one_of_maximalVolume` — **maximality bounds the solve
  matrix**: at a maximal-volume pick every solve coefficient of every unselected
  row lies in `[−1, 1]`, since a coefficient of modulus above one would name a
  swap of strictly larger volume.  This single fact is the entire content of
  "maximal volume".
* `solveMatrix_submatrix_pick` — on the selected rows the solve matrix is the
  identity, which is what makes the Frobenius count below sharp.

NOT proved here — the two remaining steps of the classical argument:

* the Frobenius count `tr(M⁻ᵀM⁻¹) = ‖B‖_F² ≤ k + (n−k)k`, which needs the row split
  of `∑_{r,j} B_{rj}²` into the `k` selected rows (contributing exactly `k` by
  `solveMatrix_submatrix_pick`) and the `n−k` others (at most `k` each by
  `abs_solveMatrix_le_one_of_maximalVolume`);
* `MᵀM ⪯ 1` and its conjugate `M⁻ᵀM⁻¹ ⪰ 1`, after which
  `quadForm_le_trace_sub_of_one_le` gives `λ_max(M⁻ᵀM⁻¹) ≤ k(n−k) + 1` and the
  bound follows by inversion.

So the file supplies the maximal-volume mechanism and the sharp trace machinery,
and states honestly that the final assembly into `σ_min(A_T)² ≥ 1/(k(n−k)+1)` is
not yet mechanized.  Nothing here is asserted beyond what typechecks.

Prior art: Goreinov–Tyrtyshnikov maximal-volume / pseudoskeleton theory.  The GTZ
conjecture is the assertion that the denominator can be improved from
`k(n−k) + 1` to `n`; the deficit theorem above is the exact statement of that gap.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm

namespace Gtz

open Matrix

/-! ## A trace bound for positive semidefinite quadratic forms -/

variable {size : ℕ}

/-- **The `2 × 2` minor, entrywise.**  A positive semidefinite matrix satisfies
`S_ij² ≤ S_ii · S_jj`. -/
theorem sq_le_mul_diag_of_posSemidef {form : Matrix (Fin size) (Fin size) ℝ}
    (hpsd : form.PosSemidef) (rowIndex colIndex : Fin size) :
    form rowIndex colIndex ^ 2 ≤ form rowIndex rowIndex * form colIndex colIndex := by
  have hminor : (0 : ℝ) ≤ (form.submatrix ![rowIndex, colIndex] ![rowIndex, colIndex]).det :=
    (hpsd.submatrix _).det_nonneg
  rw [Matrix.det_fin_two] at hminor
  have hsymm : form colIndex rowIndex = form rowIndex colIndex := by
    have hherm := hpsd.isHermitian.apply rowIndex colIndex
    simpa using hherm
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hminor
  rw [hsymm] at hminor
  rw [pow_two]
  linarith

/-- **The cross-term bound.**  For `S ⪰ 0` the off-diagonal contribution to a
quadratic form is dominated by the diagonal ones:
`2 x_i x_j S_ij ≤ x_i² S_jj + x_j² S_ii`.  This is positive semidefiniteness of
`[[S_jj, −S_ij], [−S_ij, S_ii]]`, whose determinant is the `2 × 2` minor. -/
theorem twice_crossTerm_le_of_posSemidef {form : Matrix (Fin size) (Fin size) ℝ}
    (hpsd : form.PosSemidef) (vec : Fin size → ℝ) (rowIndex colIndex : Fin size) :
    2 * (vec rowIndex * vec colIndex * form rowIndex colIndex)
      ≤ vec rowIndex ^ 2 * form colIndex colIndex
        + vec colIndex ^ 2 * form rowIndex rowIndex := by
  have hminor := sq_le_mul_diag_of_posSemidef hpsd rowIndex colIndex
  have hdiagRow := hpsd.diag_nonneg (i := rowIndex)
  rcases eq_or_lt_of_le (hpsd.diag_nonneg (i := colIndex)) with hzero | hpos
  · have hcrossZero : form rowIndex colIndex = 0 := by
      have hsqLeZero : form rowIndex colIndex ^ 2 ≤ 0 := by rw [← hzero] at hminor; linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num)
        |>.mp (le_antisymm hsqLeZero (sq_nonneg _))
    rw [hcrossZero, ← hzero]
    nlinarith [sq_nonneg (vec colIndex)]
  · nlinarith [sq_nonneg (vec rowIndex * form colIndex colIndex
      - vec colIndex * form rowIndex colIndex), sq_nonneg (vec colIndex), hpos]

/-- **THE TRACE BOUND.**  For a positive semidefinite `S`, the quadratic form is
bounded by the trace: `xᵀ S x ≤ (tr S) · |x|²`.  Equivalently `λ_max(S) ≤ tr(S)`,
but stated and proved without ever naming an eigenvalue: expand both sides as
double sums and apply the cross-term bound entry by entry, then symmetrize. -/
theorem quadForm_le_trace_mul_dotProduct {form : Matrix (Fin size) (Fin size) ℝ}
    (hpsd : form.PosSemidef) (vec : Fin size → ℝ) :
    vec ⬝ᵥ (form *ᵥ vec) ≤ Matrix.trace form * (vec ⬝ᵥ vec) := by
  have htraceSum : Matrix.trace form = ∑ idx, form idx idx := rfl
  have hsumProduct : ∀ leftFactor rightFactor : Fin size → ℝ,
      ∑ rowIndex, ∑ colIndex, leftFactor rowIndex * rightFactor colIndex
        = (∑ rowIndex, leftFactor rowIndex) * ∑ colIndex, rightFactor colIndex := by
    intro leftFactor rightFactor
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun rowIndex _ => (Finset.mul_sum _ _ _).symm
  have hexpandTwice : 2 * (vec ⬝ᵥ (form *ᵥ vec))
      = ∑ rowIndex, ∑ colIndex, 2 * (vec rowIndex * vec colIndex * form rowIndex colIndex) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun rowIndex _ =>
      Finset.sum_congr rfl fun colIndex _ => by ring
  have hcrossBound : ∑ rowIndex, ∑ colIndex,
        2 * (vec rowIndex * vec colIndex * form rowIndex colIndex)
      ≤ ∑ rowIndex, ∑ colIndex,
          (vec rowIndex ^ 2 * form colIndex colIndex
            + vec colIndex ^ 2 * form rowIndex rowIndex) :=
    Finset.sum_le_sum fun rowIndex _ => Finset.sum_le_sum fun colIndex _ =>
      twice_crossTerm_le_of_posSemidef hpsd vec rowIndex colIndex
  have hdiagonalTotal : ∑ rowIndex, ∑ colIndex,
        (vec rowIndex ^ 2 * form colIndex colIndex
          + vec colIndex ^ 2 * form rowIndex rowIndex)
      = 2 * (Matrix.trace form * (vec ⬝ᵥ vec)) := by
    have hsplitOuter : ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
          (vec rowIndex ^ 2 * form colIndex colIndex
            + vec colIndex ^ 2 * form rowIndex rowIndex)
        = (∑ rowIndex : Fin size, ∑ colIndex : Fin size, vec rowIndex ^ 2 * form colIndex colIndex)
          + ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
              vec colIndex ^ 2 * form rowIndex rowIndex := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun rowIndex _ => Finset.sum_add_distrib
    rw [hsplitOuter, hsumProduct (fun idx => vec idx ^ 2) (fun idx => form idx idx),
      Finset.sum_comm, hsumProduct (fun idx => vec idx ^ 2) (fun idx => form idx idx),
      htraceSum, dotProduct_self_eq_sum_sq]
    ring
  linarith [hexpandTwice, hcrossBound, hdiagonalTotal]

/-- **The shifted trace bound.**  If `S ⪰ 1` then the quadratic form is bounded by
`tr(S) − (size − 1)`, strictly sharper than `tr(S)` and the source of the `+1` in
the classical constant.  Apply the trace bound to `S − 1`, whose trace is
`tr(S) − size`. -/
theorem quadForm_le_trace_sub_of_one_le {form : Matrix (Fin size) (Fin size) ℝ}
    (hpsd : (form - 1).PosSemidef) (vec : Fin size → ℝ) :
    vec ⬝ᵥ (form *ᵥ vec)
      ≤ (Matrix.trace form - (size : ℝ) + 1) * (vec ⬝ᵥ vec) := by
  have hshifted := quadForm_le_trace_mul_dotProduct hpsd vec
  have htrace : Matrix.trace (form - 1) = Matrix.trace form - (size : ℝ) := by
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
  rw [htrace] at hshifted
  have hsplitForm : form = (form - 1) + 1 := by abel
  have hquad : vec ⬝ᵥ (form *ᵥ vec)
      = vec ⬝ᵥ ((form - 1) *ᵥ vec) + vec ⬝ᵥ vec := by
    conv_lhs => rw [hsplitForm]
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec]
  have hexpandRhs : (Matrix.trace form - (size : ℝ) + 1) * (vec ⬝ᵥ vec)
      = (Matrix.trace form - (size : ℝ)) * (vec ⬝ᵥ vec) + (vec ⬝ᵥ vec) := by ring
  rw [hquad, hexpandRhs]
  linarith [hshifted]

/-! ## The exact gap between the classical constant and GTZ -/

/-- **The deficit, in rank-and-corank coordinates.**  Writing `k = a + 1` and
`n − k = b + 1`, the classical maximal-volume denominator `k(n−k) + 1` exceeds the
GTZ denominator `n` by exactly `a · b = (k−1)(n−k−1)`. -/
theorem classicalDenominator_eq_gtzDenominator_add_deficit
    (rankMinusOne corankMinusOne : ℕ) :
    (rankMinusOne + 1) * (corankMinusOne + 1) + 1
      = ((rankMinusOne + 1) + (corankMinusOne + 1)) + rankMinusOne * corankMinusOne := by
  ring

/-- **The deficit, in `(n, k)` coordinates.**  `k(n−k) + 1 − n = (k−1)(n−k−1)`, so
the classical maximal-volume bound IS the GTZ bound exactly when `k = 1` or
`n = k + 1`, and is weaker by that product otherwise.  At the campaign's rank-three
object `(7, 3)` the deficit is `2 · 3 = 6`: classical gives `1/13`, GTZ asks `1/7`. -/
theorem gtzDenominator_add_deficit_eq_classical {frameSize selectionRank : ℕ}
    (hrankPos : 1 ≤ selectionRank) (hcorankPos : selectionRank + 1 ≤ frameSize) :
    frameSize + (selectionRank - 1) * (frameSize - selectionRank - 1)
      = selectionRank * (frameSize - selectionRank) + 1 := by
  obtain ⟨rankMinusOne, hrankEq⟩ : ∃ predecessor, selectionRank = predecessor + 1 :=
    ⟨selectionRank - 1, by omega⟩
  obtain ⟨corankMinusOne, hsizeEq⟩ :
      ∃ predecessor, frameSize = selectionRank + (predecessor + 1) :=
    ⟨frameSize - selectionRank - 1, by omega⟩
  subst hrankEq
  subst hsizeEq
  have hrankPredecessor : rankMinusOne + 1 - 1 = rankMinusOne := by omega
  have hcorankPredecessor :
      rankMinusOne + 1 + (corankMinusOne + 1) - (rankMinusOne + 1) - 1 = corankMinusOne := by
    omega
  have hcorankValue :
      rankMinusOne + 1 + (corankMinusOne + 1) - (rankMinusOne + 1) = corankMinusOne + 1 := by
    omega
  rw [hrankPredecessor, hcorankPredecessor, hcorankValue]
  ring

/-! ## Volumes of row selections -/

variable {frameSize selectionRank : ℕ}

/-- The `selectionRank × selectionRank` row submatrix a pick selects. -/
def selectedFrameRows (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize) : Matrix (Fin selectionRank) (Fin selectionRank) ℝ :=
  frame.submatrix pick id

/-- **A row selection's projection block is its Gram**:
`(F Fᵀ)|pick = F_pick (F_pick)ᵀ`, so its determinant is the SQUARED VOLUME. -/
theorem projectionBlock_eq_selectedFrameRows_mul_transpose
    (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ) (pick : Fin selectionRank → Fin frameSize) :
    (frame * frameᵀ).submatrix pick pick
      = selectedFrameRows frame pick * (selectedFrameRows frame pick)ᵀ := by
  rw [selectedFrameRows, ← Matrix.submatrix_mul_equiv frame frameᵀ pick (Equiv.refl _) pick]
  rfl

/-- The squared-volume reading of a projection block's determinant. -/
theorem det_projectionBlock_eq_sq_volume
    (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ) (pick : Fin selectionRank → Fin frameSize) :
    ((frame * frameᵀ).submatrix pick pick).det = (selectedFrameRows frame pick).det ^ 2 := by
  rw [projectionBlock_eq_selectedFrameRows_mul_transpose, Matrix.det_mul,
    Matrix.det_transpose, pow_two]

/-! ## Cauchy–Binet for a frame, and the existence of a nonsingular selection -/

/-- **Pythagoras for a frame's shadows.**  The `selectionRank`-subset squared volumes of a
matrix with orthonormal columns sum to one.  Same proof as
`sum_det_projectionMinors_rank`, read on a raw frame instead of a design. -/
theorem sum_det_frameMinors_rank (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (hortho : frameᵀ * frame = 1) :
    ∑ selected ∈ (Finset.univ : Finset (Fin frameSize)).powersetCard selectionRank,
        ((frame * frameᵀ).submatrix (Subtype.val : { c // c ∈ selected } → Fin frameSize)
          (Subtype.val : { c // c ∈ selected } → Fin frameSize)).det
      = 1 := by
  have horthoMapped : (frame.map Polynomial.C)ᵀ * (frame.map Polynomial.C) = 1 := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul (f := (Polynomial.C : ℝ →+* Polynomial ℝ)),
      hortho]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hmapped : (frame * frameᵀ).map Polynomial.C
      = (frame.map Polynomial.C) * (frame.map Polynomial.C)ᵀ := by
    rw [Matrix.map_mul (f := (Polynomial.C : ℝ →+* Polynomial ℝ)), Matrix.transpose_map]
  rw [← Matrix.coeff_det_one_add_X_smul_eq_sum_minors (frame * frameᵀ) selectionRank, hmapped,
    det_one_add_smul_mul_transpose (frame.map Polynomial.C) horthoMapped Polynomial.X,
    Polynomial.coeff_one_add_X_pow, Nat.choose_self, Nat.cast_one]

/-- **Some selection is nonsingular.**  If every `selectionRank`-element pick had zero
volume the shadow determinants would all vanish, contradicting Pythagoras. -/
theorem exists_injective_pick_det_ne_zero (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (hortho : frameᵀ * frame = 1) :
    ∃ pick : Fin selectionRank → Fin frameSize,
      Function.Injective pick ∧ (selectedFrameRows frame pick).det ≠ 0 := by
  by_contra hnone
  rw [not_exists] at hnone
  have hallZero : ∀ selected ∈ (Finset.univ : Finset (Fin frameSize)).powersetCard selectionRank,
      ((frame * frameᵀ).submatrix (Subtype.val : { c // c ∈ selected } → Fin frameSize)
        (Subtype.val : { c // c ∈ selected } → Fin frameSize)).det = 0 := by
    intro selected hmem
    have hcard : selected.card = selectionRank := (Finset.mem_powersetCard.mp hmem).2
    have hreindex :
        ((frame * frameᵀ).submatrix (Subtype.val : { c // c ∈ selected } → Fin frameSize)
            (Subtype.val : { c // c ∈ selected } → Fin frameSize)).det
          = ((frame * frameᵀ).submatrix (selected.orderEmbOfFin hcard)
              (selected.orderEmbOfFin hcard)).det := by
      rw [← Matrix.det_submatrix_equiv_self (selected.orderIsoOfFin hcard).toEquiv
        ((frame * frameᵀ).submatrix (Subtype.val : { c // c ∈ selected } → Fin frameSize)
          (Subtype.val : { c // c ∈ selected } → Fin frameSize))]
      rfl
    rw [hreindex, det_projectionBlock_eq_sq_volume]
    have hzero := hnone (selected.orderEmbOfFin hcard)
    rw [not_and] at hzero
    have hvolume := hzero (selected.orderEmbOfFin hcard).injective
    rw [not_not] at hvolume
    rw [hvolume]
    norm_num
  have hsum := sum_det_frameMinors_rank frame hortho
  rw [Finset.sum_congr rfl hallZero, Finset.sum_const_zero] at hsum
  exact absurd hsum (by norm_num)

/-- **The maximal-volume selection.**  Among the finitely many injective picks one
maximizes `|det|`, and it is nonsingular because some pick is. -/
theorem exists_maximalVolume_pick (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (hortho : frameᵀ * frame = 1) :
    ∃ pick : Fin selectionRank → Fin frameSize, Function.Injective pick ∧
      (selectedFrameRows frame pick).det ≠ 0 ∧
      ∀ other : Fin selectionRank → Fin frameSize, Function.Injective other →
        |(selectedFrameRows frame other).det| ≤ |(selectedFrameRows frame pick).det| := by
  classical
  obtain ⟨witnessPick, hwitnessInj, hwitnessDet⟩ :=
    exists_injective_pick_det_ne_zero frame hortho
  set injectivePicks : Finset (Fin selectionRank → Fin frameSize) :=
    Finset.univ.filter fun pick => Function.Injective pick with hpicksDef
  have hwitnessMem : witnessPick ∈ injectivePicks := by
    rw [hpicksDef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hwitnessInj⟩
  obtain ⟨bestPick, hbestMem, hbest⟩ :=
    Finset.exists_max_image injectivePicks
      (fun pick => |(selectedFrameRows frame pick).det|) ⟨witnessPick, hwitnessMem⟩
  have hbestInj : Function.Injective bestPick := by
    rw [hpicksDef, Finset.mem_filter] at hbestMem
    exact hbestMem.2
  refine ⟨bestPick, hbestInj, ?_, fun other hotherInj => ?_⟩
  · intro hzero
    have hwitnessLe := hbest witnessPick hwitnessMem
    rw [hzero, abs_zero] at hwitnessLe
    exact absurd (abs_nonpos_iff.mp hwitnessLe) hwitnessDet
  · exact hbest other (by rw [hpicksDef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hotherInj⟩)

/-! ## Maximality bounds every solve coefficient by one -/

/-- The solve matrix `B = F · (F_pick)⁻¹` re-expresses every row of the frame in the
basis formed by the selected rows: `B · F_pick = F`. -/
noncomputable def solveMatrix (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize) :
    Matrix (Fin frameSize) (Fin selectionRank) ℝ :=
  frame * (selectedFrameRows frame pick)⁻¹

theorem solveMatrix_mul_selectedFrameRows (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize)
    (hunit : IsUnit (selectedFrameRows frame pick).det) :
    solveMatrix frame pick * selectedFrameRows frame pick = frame := by
  rw [solveMatrix, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]

/-- Every frame row is the solve-matrix combination of the selected rows. -/
theorem frameRow_eq_solveCombination (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize)
    (hunit : IsUnit (selectedFrameRows frame pick).det) (rowIndex : Fin frameSize) :
    frame rowIndex
      = ∑ coord, solveMatrix frame pick rowIndex coord • selectedFrameRows frame pick coord := by
  have hmul := solveMatrix_mul_selectedFrameRows frame pick hunit
  funext outCoord
  have hentry : (solveMatrix frame pick * selectedFrameRows frame pick) rowIndex outCoord
      = frame rowIndex outCoord := by rw [hmul]
  rw [← hentry, Matrix.mul_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Replacing one selected row by an arbitrary frame row is exactly a one-element
swap of the pick. -/
theorem updateRow_selectedFrameRows (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize) (colIndex : Fin selectionRank)
    (rowIndex : Fin frameSize) :
    (selectedFrameRows frame pick).updateRow colIndex (frame rowIndex)
      = selectedFrameRows frame (Function.update pick colIndex rowIndex) := by
  ext outIndex coord
  rcases eq_or_ne outIndex colIndex with rfl | hne
  · rw [Matrix.updateRow_self]
    simp [selectedFrameRows]
  · rw [Matrix.updateRow_ne hne]
    simp [selectedFrameRows, Function.update_of_ne hne]

/-- **THE MAXIMALITY IDENTITY.**  The volume of the swapped pick is the solve
coefficient times the volume of the original: `det F_{pick[j ← r]} = B_{rj} · det
F_pick`.  Immediate from `Matrix.det_updateRow_sum`, because the inserted row IS the
solve combination. -/
theorem det_selectedFrameRows_update (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize)
    (hunit : IsUnit (selectedFrameRows frame pick).det) (colIndex : Fin selectionRank)
    (rowIndex : Fin frameSize) :
    (selectedFrameRows frame (Function.update pick colIndex rowIndex)).det
      = solveMatrix frame pick rowIndex colIndex * (selectedFrameRows frame pick).det := by
  rw [← updateRow_selectedFrameRows frame pick colIndex rowIndex,
    frameRow_eq_solveCombination frame pick hunit rowIndex,
    Matrix.det_updateRow_sum, smul_eq_mul]

/-- A one-element swap that brings in a row outside the pick stays injective. -/
theorem injective_update_of_forall_ne {pick : Fin selectionRank → Fin frameSize}
    (hinj : Function.Injective pick) {colIndex : Fin selectionRank} {rowIndex : Fin frameSize}
    (hout : ∀ idx, pick idx ≠ rowIndex) :
    Function.Injective (Function.update pick colIndex rowIndex) := by
  intro leftIndex rightIndex heq
  by_cases hleft : leftIndex = colIndex
  · by_cases hright : rightIndex = colIndex
    · rw [hleft, hright]
    · rw [hleft, Function.update_self, Function.update_of_ne hright] at heq
      exact absurd heq.symm (hout rightIndex)
  · by_cases hright : rightIndex = colIndex
    · rw [hright, Function.update_self, Function.update_of_ne hleft] at heq
      exact absurd heq (hout leftIndex)
    · rw [Function.update_of_ne hleft, Function.update_of_ne hright] at heq
      exact hinj heq

/-- **MAXIMALITY BOUNDS THE SOLVE MATRIX.**  At a maximal-volume pick every solve
coefficient of every unselected row lies in `[−1, 1]`.  This single fact is the
entire content of "maximal volume": a coefficient of modulus above one would name a
swap of strictly larger volume. -/
theorem abs_solveMatrix_le_one_of_maximalVolume
    (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize) (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows frame pick).det)
    (hmax : ∀ other : Fin selectionRank → Fin frameSize, Function.Injective other →
      |(selectedFrameRows frame other).det| ≤ |(selectedFrameRows frame pick).det|)
    (rowIndex : Fin frameSize) (hout : ∀ idx, pick idx ≠ rowIndex)
    (colIndex : Fin selectionRank) :
    |solveMatrix frame pick rowIndex colIndex| ≤ 1 := by
  have hswap := hmax (Function.update pick colIndex rowIndex)
    (injective_update_of_forall_ne hinj hout)
  rw [det_selectedFrameRows_update frame pick hunit colIndex rowIndex, abs_mul] at hswap
  have hvolumePos : 0 < |(selectedFrameRows frame pick).det| := abs_pos.mpr hunit.ne_zero
  nlinarith [hswap, hvolumePos]

/-- On the selected rows the solve matrix is the identity: `B_pick = 1`. -/
theorem solveMatrix_submatrix_pick (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize)
    (hunit : IsUnit (selectedFrameRows frame pick).det) :
    (solveMatrix frame pick).submatrix pick id = 1 := by
  rw [solveMatrix,
    ← Matrix.submatrix_mul_equiv frame (selectedFrameRows frame pick)⁻¹ pick (Equiv.refl _) id]
  exact Matrix.mul_nonsing_inv _ hunit

end Gtz

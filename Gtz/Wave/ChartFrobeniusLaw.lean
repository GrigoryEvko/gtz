/-
# Tracing the quadratic equation prices the whole of `M`

`Gtz/Wave/ChartQuadraticCore.lean` carries the realizability equation

    `M M + M T + T M + T T = M + T` ,   `T = diag t` .

Take the trace.  Every term is elementary, `tr(T M) = tr(M T)` by cyclicity, and
`tr M = rank - 1` while `tr T = 1`, so

  **`Σ_{p,q} M_pq² = rank - 2 Σ_c t_c M_cc - Σ_c t_c²`**
  (`Gtz.sum_sq_chartGapOfDesign`, design-free in `Gtz.chartCore_sum_sq_gap`).

`M` is symmetric, so the left side is `tr(Mᵀ M)`, the TOTAL square mass of the
matrix.  The identity therefore prices every entry of `M` — every pairing of the
design — against the diagonal and the weights alone.  Splitting off the diagonal,

  **`Σ_{p ≠ q} M_pq² = rank - Σ_c t_c² - Σ_c M_cc(2 t_c + M_cc)`**
  (`Gtz.sum_sq_offDiagonal_chartGapOfDesign`),

so the off-diagonal mass of `M` is a function of its own diagonal and of `t`.  At a
design that reads `M_cc = t_c(ℓ_c - 1)` and the identity becomes
`Σ_{p,q} M_pq² = rank + Σ_c t_c² - 2 Σ_c t_c² ℓ_c`, which is weight-aware and
mentions no bracket, no volume and no Gram minor.

## What it constrains

At `(6,3)` the all-heavy stratum has `M_cc > 0` at every label
(`Gtz.allHeavy_iff_chartGapOfDesign_diag_pos`).  Every such diagonal entry then
SPENDS from the budget above, because `M_cc(2 t_c + M_cc) > 0`, so an all-heavy
design has strictly less off-diagonal mass than `rank - Σ_c t_c²`.  That is a hard
cap on the pairings of an all-heavy design, and it is exactly the direction the
residual stratum is in.

It is a single scalar identity and it decides nothing on its own.  It is recorded
because it is the cheapest weight-aware consequence of the realizability equation
and because any attack on the twenty `(6,3)` blocks has to respect it alongside
`Gtz.chartCore_det_gapBlock_shift_eq` and the layer totals of
`Gtz.sum_det_subsetSum_sub_one_layer`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.ProjectionForm
import Gtz.Wave.ChartQuadraticCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — the three traces -/

/-- **THE TRACE OF A SYMMETRIC SQUARE IS THE TOTAL SQUARE MASS.**  For a symmetric
matrix the trace of its square totals every entry squared. -/
theorem trace_mul_self_of_transpose_eq {size : ℕ} {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : formᵀ = form) :
    Matrix.trace (form * form) = ∑ rowIndex, ∑ colIndex, form rowIndex colIndex ^ 2 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun rowIndex _ => Finset.sum_congr rfl fun colIndex _ => ?_
  have hflip : form colIndex rowIndex = form rowIndex colIndex := by
    have hstep := congrFun (congrFun hsymm rowIndex) colIndex
    rw [Matrix.transpose_apply] at hstep
    exact hstep
  rw [hflip, pow_two]

/-- The trace against a weight diagonal reads the diagonal. -/
theorem trace_mul_weightDiagonal {size : ℕ} (form : Matrix (Fin size) (Fin size) ℝ)
    (entry : Fin size → ℝ) :
    Matrix.trace (form * Matrix.diagonal entry)
      = ∑ index, form index index * entry index := by
  rw [Matrix.trace]
  exact Finset.sum_congr rfl fun index _ => by
    rw [Matrix.diag_apply, Matrix.mul_diagonal]

/-- The trace of a squared weight diagonal totals the squared weights. -/
theorem trace_weightDiagonal_mul_sq {size : ℕ} (entry : Fin size → ℝ) :
    Matrix.trace (Matrix.diagonal entry * Matrix.diagonal entry)
      = ∑ index, entry index ^ 2 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun index _ => (pow_two _).symm

/-! ## Part 2 — the Frobenius law -/

/-- **THE TOTAL SQUARE MASS OF THE CHART GAP.**  Tracing the realizability equation
prices every entry of `M` against its own diagonal and the weights:

    `Σ_{p,q} M_pq² = rank - 2 Σ_c t_c M_cc - Σ_c t_c²` .

No atom, no bracket and no Gram minor appears. -/
theorem sum_sq_chartGapOfDesign (D : WeightedDesign m k) :
    ∑ leftLabel, ∑ rightLabel, chartGapOfDesign D leftLabel rightLabel ^ 2
      = (k : ℝ) - 2 * (∑ atomIndex, D.weight atomIndex
            * chartGapOfDesign D atomIndex atomIndex)
        - ∑ atomIndex, D.weight atomIndex ^ 2 := by
  have hquad := chartGapOfDesign_isQuadratic D
  have htrace := congrArg Matrix.trace hquad
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add] at htrace
  rw [trace_mul_self_of_transpose_eq (chartGapOfDesign_transpose D),
    trace_mul_weightDiagonal, trace_weightDiagonal_mul_sq,
    Matrix.trace_mul_comm (Matrix.diagonal D.weight) (chartGapOfDesign D),
    trace_mul_weightDiagonal, trace_chartGapOfDesign, Matrix.trace_diagonal,
    D.weight_sum_one] at htrace
  have hcomm : ∑ atomIndex, chartGapOfDesign D atomIndex atomIndex * D.weight atomIndex
      = ∑ atomIndex, D.weight atomIndex * chartGapOfDesign D atomIndex atomIndex :=
    Finset.sum_congr rfl fun atomIndex _ => mul_comm _ _
  rw [hcomm] at htrace
  linarith [htrace]

/-- **THE OFF-DIAGONAL MASS IS DETERMINED BY THE DIAGONAL.**  Splitting the diagonal
off the total, the squared entries away from the diagonal total

    `rank - Σ_c t_c² - Σ_c M_cc(2 t_c + M_cc)` .

Every strictly positive diagonal entry SPENDS from that budget, so an all-heavy
design has strictly less off-diagonal mass than `rank - Σ_c t_c²`. -/
theorem sum_sq_offDiagonal_chartGapOfDesign (D : WeightedDesign m k) :
    ∑ leftLabel, ∑ rightLabel ∈ Finset.univ.erase leftLabel,
        chartGapOfDesign D leftLabel rightLabel ^ 2
      = (k : ℝ) - (∑ atomIndex, D.weight atomIndex ^ 2)
        - ∑ atomIndex, chartGapOfDesign D atomIndex atomIndex
            * (2 * D.weight atomIndex + chartGapOfDesign D atomIndex atomIndex) := by
  classical
  have htotal := sum_sq_chartGapOfDesign D
  have hpeel : ∀ leftLabel : Fin m,
      ∑ rightLabel, chartGapOfDesign D leftLabel rightLabel ^ 2
        = chartGapOfDesign D leftLabel leftLabel ^ 2
          + ∑ rightLabel ∈ Finset.univ.erase leftLabel,
              chartGapOfDesign D leftLabel rightLabel ^ 2 := by
    intro leftLabel
    exact (Finset.add_sum_erase _
      (fun rightLabel => chartGapOfDesign D leftLabel rightLabel ^ 2)
      (Finset.mem_univ leftLabel)).symm
  rw [Finset.sum_congr rfl fun leftLabel _ => hpeel leftLabel, Finset.sum_add_distrib] at htotal
  have hmerge : ∑ atomIndex, chartGapOfDesign D atomIndex atomIndex
        * (2 * D.weight atomIndex + chartGapOfDesign D atomIndex atomIndex)
      = 2 * (∑ atomIndex, D.weight atomIndex * chartGapOfDesign D atomIndex atomIndex)
        + ∑ atomIndex, chartGapOfDesign D atomIndex atomIndex ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  rw [hmerge]
  linarith [htotal]

/-- **THE FROBENIUS LAW, DESIGN-FREE.**  The same identity about a
`Gtz.ChartCore`: no atom, no Parseval and no projection appears, only the symmetric
matrix and the weights. -/
theorem chartCore_sum_sq_gap {size rank : ℕ} (core : ChartCore size rank) :
    ∑ leftLabel, ∑ rightLabel, core.gap leftLabel rightLabel ^ 2
      = (rank : ℝ) - 2 * (∑ atomIndex, core.weight atomIndex * core.gap atomIndex atomIndex)
        - ∑ atomIndex, core.weight atomIndex ^ 2 := by
  obtain ⟨D, hweight, hgap⟩ := exists_design_of_chartCore core
  rw [← hgap, ← hweight]
  exact sum_sq_chartGapOfDesign D

/-- The `(6,3)` reading: a `6 × 6` symmetric matrix whose total square mass is
`3 - 2⟨t, diag M⟩ - Σ_c t_c²`. -/
theorem sixThree_sum_sq_chartGap (D : WeightedDesign 6 3) :
    ∑ leftLabel, ∑ rightLabel, chartGapOfDesign D leftLabel rightLabel ^ 2
      = 3 - 2 * (∑ atomIndex, D.weight atomIndex
            * chartGapOfDesign D atomIndex atomIndex)
        - ∑ atomIndex, D.weight atomIndex ^ 2 := by
  have hstep := sum_sq_chartGapOfDesign D
  norm_num at hstep
  exact hstep

/-- **AN ALL-HEAVY DESIGN SPENDS FROM ITS OWN OFF-DIAGONAL BUDGET.**  Every
diagonal entry of the gap of an all-heavy design is strictly positive, so it
subtracts a strictly positive amount from the off-diagonal total. -/
theorem sum_sq_offDiagonal_lt_of_allHeavy (D : WeightedDesign m k) (hsize : 0 < m)
    (hheavy : AllHeavy D) :
    ∑ leftLabel, ∑ rightLabel ∈ Finset.univ.erase leftLabel,
        chartGapOfDesign D leftLabel rightLabel ^ 2
      < (k : ℝ) - ∑ atomIndex, D.weight atomIndex ^ 2 := by
  classical
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hsize
  have hdiag : ∀ atomIndex : Fin m, 0 < chartGapOfDesign D atomIndex atomIndex := by
    intro atomIndex
    rw [chartGapOfDesign_diagonal]
    exact mul_pos (D.weight_pos atomIndex) (by linarith [hheavy atomIndex])
  have hspend : 0 < ∑ atomIndex, chartGapOfDesign D atomIndex atomIndex
      * (2 * D.weight atomIndex + chartGapOfDesign D atomIndex atomIndex) := by
    refine Finset.sum_pos (fun atomIndex _ => ?_) Finset.univ_nonempty
    exact mul_pos (hdiag atomIndex)
      (by linarith [hdiag atomIndex, D.weight_pos atomIndex])
  linarith [sum_sq_offDiagonal_chartGapOfDesign D, hspend]

end Gtz

/-
# At the Gale self-dual cell the complementary blocks share a spectrum

`Gtz/Wave/ChartComplementBlockLaw.lean` proves, at every size and rank,

    `det(M[C, C] + T_C) = det(1 - M[Cᶜ, Cᶜ] - T_{Cᶜ})` .

That is an equality of two numbers.  At `size = 2 · rank` — the Gale self-dual
cell, of which `(6,3)` is the campaign's open one — the two matrices agree far more
strongly: they have the same CHARACTERISTIC POLYNOMIAL, hence the same spectrum.

  **`Gtz.det_shifted_chartGapBlock_eq`.**  For every real `shift`,

      `det(shift·1 - (M[C,C] + T_C)) = det(shift·1 - (1 - M[Cᶜ,Cᶜ] - T_{Cᶜ}))` .

## Why, and why only there

Both blocks are built from the same frame.  With `A` the selected rows and `B` the
complementary rows, `P[C,C] = A Aᵀ` and `(1 - P)[Cᶜ,Cᶜ] = 1 - B Bᵀ`, and
orthonormality splits as `Aᵀ A + Bᵀ B = 1`.  The shifted determinant does not know
which side a product is taken on (`Gtz.det_smul_one_sub_mul_comm`), so

    `det(shift·1 - A Aᵀ) = det(shift·1 - Aᵀ A)` ,
    `det((1-shift)·1 - B Bᵀ) = det((1-shift)·1 - Bᵀ B) = det(shift·1 - Aᵀ A)` up to sign,

and the two sign changes cancel.  **The step that needs `size = 2 · rank` is the
second flip**: `B` is square only there.  Off the self-dual cell `B B ᵀ` and
`Bᵀ B` differ by a block of zeros, and the law fails — measured, the top spectral
difference is `0.97` at `(7,3)` and `0.998` at `(8,3)`.  The determinant law of the
previous module survives everywhere because a determinant is one coefficient, and
that coefficient is the one the zeros do not move.

## What it does NOT say

It does not say that `C` dominates exactly when `Cᶜ` does in the SAME design.
Domination of `C` is `M[C,C] ⪰ 0`, that is `P[C,C] ⪰ T_C`, and the shared spectrum
is of `P[C,C]` against the IDENTITY, not against `T_C`.  Measured, the two
conditions disagree on `2992` of `8000` subsets, so no successor should read this
as a self-duality of domination.  The genuine transport of domination is the sharp
duality of `Gtz/Wave/ChartGapSharpDuality.lean`, which changes the design.

What it does say is that the twenty `3 × 3` blocks of a `(6,3)` chart gap carry
only ten spectra between them, not twenty.  Together with
`Gtz.chartCore_sum_sq_gap` and the layer totals of
`Gtz.sum_det_subsetSum_sub_one_layer` that is the arithmetic a block-level attack
has to respect.

[MEASURED before proving.  The spectral agreement holds at `4.00e-15` at `(6,3)`,
`(8,4)`, `(10,5)` and `(4,2)`, and FAILS off `size = 2 · rank` as recorded above.]
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.ProjectionForm
import Gtz.Wave.NaimarkSharpDesign
import Gtz.Wave.ChartQuadraticCore
import Gtz.Wave.ChartComplementBlockLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — a shifted determinant does not know the order of a product -/

/-- A nonzero shift factors out of a shifted matrix. -/
theorem det_smul_one_sub_eq {size : ℕ} (form : Matrix (Fin size) (Fin size) ℝ) {shift : ℝ}
    (hne : shift ≠ 0) :
    (shift • (1 : Matrix (Fin size) (Fin size) ℝ) - form).det
      = shift ^ size * ((1 : Matrix (Fin size) (Fin size) ℝ) - shift⁻¹ • form).det := by
  have hfactor : shift • (1 : Matrix (Fin size) (Fin size) ℝ) - form
      = shift • ((1 : Matrix (Fin size) (Fin size) ℝ) - shift⁻¹ • form) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hne, one_smul]
  rw [hfactor, Matrix.det_smul, Fintype.card_fin]

/-- **THE SHIFTED WEINSTEIN–ARONSZAJN FLIP.**  For square factors the shifted
determinant is symmetric in the order of the product, at EVERY shift including
zero. -/
theorem det_smul_one_sub_mul_comm {size : ℕ}
    (leftFactor rightFactor : Matrix (Fin size) (Fin size) ℝ) (shift : ℝ) :
    (shift • (1 : Matrix (Fin size) (Fin size) ℝ) - leftFactor * rightFactor).det
      = (shift • (1 : Matrix (Fin size) (Fin size) ℝ) - rightFactor * leftFactor).det := by
  rcases eq_or_ne shift 0 with rfl | hne
  · rw [zero_smul, zero_sub, zero_sub, Matrix.det_neg, Matrix.det_neg, Matrix.det_mul,
      Matrix.det_mul, mul_comm leftFactor.det rightFactor.det]
  · rw [det_smul_one_sub_eq _ hne, det_smul_one_sub_eq _ hne]
    congr 1
    have hleft : shift⁻¹ • (leftFactor * rightFactor)
        = (shift⁻¹ • leftFactor) * rightFactor := (Matrix.smul_mul _ _ _).symm
    have hright : shift⁻¹ • (rightFactor * leftFactor)
        = rightFactor * (shift⁻¹ • leftFactor) := by
      rw [Matrix.mul_smul]
    rw [hleft, hright]
    have hcomm := Matrix.det_one_add_mul_comm (-(shift⁻¹ • leftFactor)) rightFactor
    rw [Matrix.neg_mul, ← sub_eq_add_neg, Matrix.mul_neg, ← sub_eq_add_neg] at hcomm
    exact hcomm

/-- The two sign changes of the argument below cancel. -/
theorem neg_one_pow_mul_self (exponent : ℕ) :
    ((-1 : ℝ) ^ exponent) * ((-1 : ℝ) ^ exponent) = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨exponent, rfl⟩

/-! ## Part 2 — the spectral law at the Gale self-dual cell -/

/-- **THE COMPLEMENTARY BLOCKS SHARE A CHARACTERISTIC POLYNOMIAL.**  When the
selection and its complement have the SAME size — that is, at `size = 2 · rank`,
which the bijectivity hypothesis forces — the shifted determinants agree at every
shift, not only at the shift zero of
`Gtz.det_projectionBlock_eq_det_one_sub_complementBlock`.

The second flip is where the self-dual cell is spent: the complementary row block
is square only there. -/
theorem det_shifted_projectionBlock_eq {size rank : ℕ}
    (frame : Matrix (Fin size) (Fin rank) ℝ) (hortho : frameᵀ * frame = 1)
    {pick copick : Fin rank → Fin size}
    (hpart : Function.Bijective (Sum.elim pick copick)) (shift : ℝ) :
    (shift • (1 : Matrix (Fin rank) (Fin rank) ℝ)
        - (frame * frameᵀ).submatrix pick pick).det
      = (shift • (1 : Matrix (Fin rank) (Fin rank) ℝ)
        - ((1 : Matrix (Fin rank) (Fin rank) ℝ)
          - (frame * frameᵀ).submatrix copick copick)).det := by
  have hsplit := transpose_mul_self_submatrix_add frame hortho hpart
  have hcomplement : (frame.submatrix copick id)ᵀ * (frame.submatrix copick id)
      = 1 - (frame.submatrix pick id)ᵀ * (frame.submatrix pick id) := by
    rw [← hsplit]; abel
  -- the right side, folded into a single shifted product with one sign change
  have hfold : shift • (1 : Matrix (Fin rank) (Fin rank) ℝ)
        - ((1 : Matrix (Fin rank) (Fin rank) ℝ)
          - (frame.submatrix copick id) * (frame.submatrix copick id)ᵀ)
      = -((1 - shift) • (1 : Matrix (Fin rank) (Fin rank) ℝ)
          - (frame.submatrix copick id) * (frame.submatrix copick id)ᵀ) := by
    rw [sub_smul, one_smul]
    abel
  -- the left side, after the flip, folded the same way
  have hfoldLeft : (1 - shift) • (1 : Matrix (Fin rank) (Fin rank) ℝ)
        - (1 - (frame.submatrix pick id)ᵀ * (frame.submatrix pick id))
      = -(shift • (1 : Matrix (Fin rank) (Fin rank) ℝ)
          - (frame.submatrix pick id)ᵀ * (frame.submatrix pick id)) := by
    rw [sub_smul, one_smul]
    abel
  rw [submatrix_mul_transpose_gen frame pick, submatrix_mul_transpose_gen frame copick,
    hfold, Matrix.det_neg, det_smul_one_sub_mul_comm (frame.submatrix copick id),
    hcomplement, hfoldLeft, Matrix.det_neg,
    det_smul_one_sub_mul_comm (frame.submatrix pick id), Fintype.card_fin, ← mul_assoc,
    neg_one_pow_mul_self, one_mul]

/-! ## Part 3 — the law in the chart gap -/

/-- **THE TWO SHIFTS SHARE A SPECTRUM ON COMPLEMENTARY BLOCKS, AT `size = 2 · rank`.**
Every shifted determinant of the first shift on a block equals the corresponding
shifted determinant of the second shift on the complementary block, so the two
matrices are isospectral. -/
theorem det_shifted_chartGapBlock_eq (D : WeightedDesign m k)
    {pick copick : Fin k → Fin m} (hpick : Function.Injective pick)
    (hcopick : Function.Injective copick)
    (hpart : Function.Bijective (Sum.elim pick copick)) (shift : ℝ) :
    (shift • (1 : Matrix (Fin k) (Fin k) ℝ)
        - ((chartGapOfDesign D).submatrix pick pick
          + Matrix.diagonal fun selectedIndex => D.weight (pick selectedIndex))).det
      = (shift • (1 : Matrix (Fin k) (Fin k) ℝ)
        - ((1 : Matrix (Fin k) (Fin k) ℝ)
          - (chartGapOfDesign D).submatrix copick copick
          - Matrix.diagonal fun coIndex => D.weight (copick coIndex))).det := by
  have hleft : (chartGapOfDesign D).submatrix pick pick
        + Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))
      = (projectionOfDesign D).submatrix pick pick := by
    rw [chartGapOfDesign_submatrix D hpick]; abel
  have hright : (1 : Matrix (Fin k) (Fin k) ℝ)
        - (chartGapOfDesign D).submatrix copick copick
        - Matrix.diagonal (fun coIndex => D.weight (copick coIndex))
      = 1 - (projectionOfDesign D).submatrix copick copick := by
    rw [chartGapOfDesign_submatrix D hcopick]; abel
  rw [hleft, hright, projectionOfDesign]
  exact det_shifted_projectionBlock_eq (scaledAtomRows D) (transpose_mul_scaledAtomRows D)
    hpart shift

/-- **THE LAW, DESIGN-FREE.**  The same statement about a `Gtz.ChartCore`. -/
theorem chartCore_det_shifted_gapBlock_eq {size rank : ℕ} (core : ChartCore size rank)
    {pick copick : Fin rank → Fin size} (hpick : Function.Injective pick)
    (hcopick : Function.Injective copick)
    (hpart : Function.Bijective (Sum.elim pick copick)) (shift : ℝ) :
    (shift • (1 : Matrix (Fin rank) (Fin rank) ℝ)
        - ((core.gap).submatrix pick pick
          + Matrix.diagonal fun selectedIndex => core.weight (pick selectedIndex))).det
      = (shift • (1 : Matrix (Fin rank) (Fin rank) ℝ)
        - ((1 : Matrix (Fin rank) (Fin rank) ℝ)
          - (core.gap).submatrix copick copick
          - Matrix.diagonal fun coIndex => core.weight (copick coIndex))).det := by
  obtain ⟨D, hweight, hgap⟩ := exists_design_of_chartCore core
  rw [← hgap, ← hweight]
  exact det_shifted_chartGapBlock_eq D hpick hcopick hpart shift

/-- **THE `(6,3)` READING.**  The twenty `3 × 3` blocks of a `(6,3)` chart gap carry
only TEN spectra between them: the first shift on a triple and the second shift on
the complementary triple are isospectral.

This constrains a tie and decides none.  It does NOT say that a triple dominates
exactly when its complement does — that is false, and the honest transport of
domination is the sharp duality. -/
theorem sixThree_shifted_complementary_block_law (D : WeightedDesign 6 3)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) (hcompl : selectedᶜ.card = 3)
    (shift : ℝ) :
    (shift • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - ((chartGapOfDesign D).submatrix (selected.orderEmbOfFin hcard)
            (selected.orderEmbOfFin hcard)
          + Matrix.diagonal fun selectedIndex =>
              D.weight (selected.orderEmbOfFin hcard selectedIndex))).det
      = (shift • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (chartGapOfDesign D).submatrix (selectedᶜ.orderEmbOfFin hcompl)
              (selectedᶜ.orderEmbOfFin hcompl)
          - Matrix.diagonal fun coIndex =>
              D.weight (selectedᶜ.orderEmbOfFin hcompl coIndex))).det :=
  det_shifted_chartGapBlock_eq D (selected.orderEmbOfFin hcard).injective
    (selectedᶜ.orderEmbOfFin hcompl).injective
    (sumElim_orderEmb_bijective selected hcard hcompl) shift

end Gtz

/-
# The two diagonal shifts of a chart gap are the same law on complementary blocks

`Gtz/Wave/ChartQuadraticCore.lean` reads a pair of a design through TWO diagonal
shifts of one `2 × 2` block of the chart gap `M`: shifting by `T` detects a
parallel pair and shifting by `T - 1` detects four coplanar atoms.  Nothing there
explains why the SAME block carries both.  This module explains it, and at every
block size rather than at pairs.

## The law

For a rank-`rank` orthogonal projection `P = V Vᵀ` on `ℝ^size` and any splitting of
the index set into a `rank`-selection `C` and its complement,

  **`det P[C, C] = det (1 - P)[Cᶜ, Cᶜ]`**
  (`Gtz.det_projectionBlock_eq_det_one_sub_complementBlock`).

Both sides are `det(V_C)²`.  The left side is `det(V_C V_Cᵀ)`; the right side is
`det(1 - V_{Cᶜ} V_{Cᶜ}ᵀ)`, which Weinstein–Aronszajn turns into
`det(1 - V_{Cᶜ}ᵀ V_{Cᶜ})`, and orthonormality of the columns splits `VᵀV = 1` as
`V_Cᵀ V_C + V_{Cᶜ}ᵀ V_{Cᶜ} = 1`.  Four lines, no Jacobi complementary minor
identity, no Cauchy–Binet, and no spectral theorem.

## Read in the gap

`P = M + T`, so the law becomes a relation between the two shifts:

  **`det(M[C, C] + T_C) = det(1 - M[Cᶜ, Cᶜ] - T_{Cᶜ})`**
  (`Gtz.det_chartGapBlock_shift_eq`, and design-free in
  `Gtz.chartCore_det_gapBlock_shift_eq`).

The FIRST shift on a block and the SECOND shift on the COMPLEMENTARY block are one
number.  At `(6,3)` that is a pairing of the twenty `3 × 3` blocks into ten
complementary couples, and at a pair it specialises to the two halves of the hinge
dictionary — which is why they live in the same block.

## What it does and does not buy

It is an EQUALITY between determinants, not between definiteness statements: a
`3 × 3` block can have a positive determinant with two negative eigenvalues, and
`Gtz.tripleGapDet_nonpos_iff_naimark` records exactly that failure of parity to
decide.  So this law constrains the twenty blocks of a `(6,3)` tie without
deciding any of them, and no successor should expect it to close the cell alone.

What it does supply is a hard, weight-aware, design-free constraint on the matrix
`M` of `Gtz.ChartCore`: the twenty determinants of the first shift are not twenty
free numbers, they are ten numbers read twice.  Together with
`Gtz.sum_det_subsetSum_sub_one_layer` — which totals the gap determinants across a
layer — that is the arithmetic any attack on the blocks has to respect.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.ChartPointFactorisation
import Gtz.Wave.NaimarkSharpDesign
import Gtz.Wave.ChartQuadraticCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — the three ingredients

A principal block of a frame square is the selected rows' own square; the
Weinstein–Aronszajn flip for a contraction; and the splitting of orthonormality
across a partition. -/

/-- A principal block of `A Aᵀ` along ANY index map is the selected rows' own
square.  The rank-generic `Gtz.submatrix_mul_transpose_eq` fixes the selection size
to the rank, which the complementary block does not obey. -/
theorem submatrix_mul_transpose_gen {size rank selectionSize : ℕ}
    (frame : Matrix (Fin size) (Fin rank) ℝ) (pick : Fin selectionSize → Fin size) :
    (frame * frameᵀ).submatrix pick pick
      = (frame.submatrix pick id) * (frame.submatrix pick id)ᵀ := by
  ext leftIndex rightIndex
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id]

/-- **THE WEINSTEIN–ARONSZAJN FLIP FOR A CONTRACTION.**  The determinant of
`1 - X Xᵀ` does not know which side the product is taken on. -/
theorem det_one_sub_mul_transpose_comm {rows cols : ℕ} (block : Matrix (Fin rows) (Fin cols) ℝ) :
    ((1 : Matrix (Fin rows) (Fin rows) ℝ) - block * blockᵀ).det
      = ((1 : Matrix (Fin cols) (Fin cols) ℝ) - blockᵀ * block).det := by
  have hcomm := Matrix.det_one_add_mul_comm (-block) blockᵀ
  rw [Matrix.neg_mul, ← sub_eq_add_neg, Matrix.mul_neg, ← sub_eq_add_neg] at hcomm
  exact hcomm

/-- The rows of a selection, squared on the rank side, total the atoms of the
selection. -/
theorem transpose_mul_submatrix_eq_sum {size rank selectionSize : ℕ}
    (frame : Matrix (Fin size) (Fin rank) ℝ) (pick : Fin selectionSize → Fin size) :
    (frame.submatrix pick id)ᵀ * (frame.submatrix pick id)
      = ∑ selectedIndex, atomMatrix (frame (pick selectedIndex)) := by
  rw [transpose_mul_self_eq_sum_rows]
  refine Finset.sum_congr rfl fun selectedIndex _ => ?_
  congr 1

/-- **ORTHONORMALITY SPLITS ACROSS A PARTITION.**  The rank-side squares of a
selection and of its complement total the whole frame's, which is the identity. -/
theorem transpose_mul_self_submatrix_add {size rank corank : ℕ}
    (frame : Matrix (Fin size) (Fin rank) ℝ) (hortho : frameᵀ * frame = 1)
    {pick : Fin rank → Fin size} {copick : Fin corank → Fin size}
    (hpart : Function.Bijective (Sum.elim pick copick)) :
    (frame.submatrix pick id)ᵀ * (frame.submatrix pick id)
        + (frame.submatrix copick id)ᵀ * (frame.submatrix copick id) = 1 := by
  classical
  have hall : ∑ slot : Fin rank ⊕ Fin corank,
      atomMatrix (frame (Sum.elim pick copick slot)) = ∑ index, atomMatrix (frame index) :=
    Fintype.sum_equiv (Equiv.ofBijective _ hpart) _ _ fun _ => rfl
  rw [Fintype.sum_sum_type] at hall
  simp only [Sum.elim_inl, Sum.elim_inr] at hall
  rw [transpose_mul_submatrix_eq_sum, transpose_mul_submatrix_eq_sum, hall,
    ← transpose_mul_self_eq_sum_rows, hortho]

/-! ## Part 2 — the complementary block law -/

/-- **THE COMPLEMENTARY BLOCK LAW.**  For an orthogonal projection presented as a
frame square, the determinant of a principal block on a `rank`-selection equals the
determinant of the COMPLEMENTARY block of the complementary projection.  Both sides
are the squared bracket of the selected rows.

No Jacobi complementary minor identity is used, and no Cauchy–Binet: the only
non-trivial step is `Gtz.det_one_sub_mul_transpose_comm`. -/
theorem det_projectionBlock_eq_det_one_sub_complementBlock {size rank corank : ℕ}
    (frame : Matrix (Fin size) (Fin rank) ℝ) (hortho : frameᵀ * frame = 1)
    {pick : Fin rank → Fin size} {copick : Fin corank → Fin size}
    (hpart : Function.Bijective (Sum.elim pick copick)) :
    ((frame * frameᵀ).submatrix pick pick).det
      = ((1 : Matrix (Fin corank) (Fin corank) ℝ)
          - (frame * frameᵀ).submatrix copick copick).det := by
  have hsplit := transpose_mul_self_submatrix_add frame hortho hpart
  have hcomplement : (1 : Matrix (Fin rank) (Fin rank) ℝ)
      - (frame.submatrix copick id)ᵀ * (frame.submatrix copick id)
      = (frame.submatrix pick id)ᵀ * (frame.submatrix pick id) := by
    rw [← hsplit]; abel
  rw [submatrix_mul_transpose_gen frame pick, submatrix_mul_transpose_gen frame copick,
    det_one_sub_mul_transpose_comm, hcomplement, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]

/-! ## Part 3 — the law in the chart gap

`P = M + T`, so the first shift on a block is the second shift on the
complementary block. -/

/-- **THE TWO SHIFTS ARE ONE NUMBER, ON COMPLEMENTARY BLOCKS.**  Shifting a
`rank`-block of the chart gap by the weight diagonal gives the same determinant as
shifting the complementary block by the weight diagonal LESS the identity. -/
theorem det_chartGapBlock_shift_eq (D : WeightedDesign m k) {corank : ℕ}
    {pick : Fin k → Fin m} {copick : Fin corank → Fin m}
    (hpick : Function.Injective pick) (hcopick : Function.Injective copick)
    (hpart : Function.Bijective (Sum.elim pick copick)) :
    ((chartGapOfDesign D).submatrix pick pick
        + Matrix.diagonal fun selectedIndex => D.weight (pick selectedIndex)).det
      = ((1 : Matrix (Fin corank) (Fin corank) ℝ)
          - (chartGapOfDesign D).submatrix copick copick
          - Matrix.diagonal fun coIndex => D.weight (copick coIndex)).det := by
  have hleft : (chartGapOfDesign D).submatrix pick pick
        + Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))
      = (projectionOfDesign D).submatrix pick pick := by
    rw [chartGapOfDesign_submatrix D hpick]
    abel
  have hright : (1 : Matrix (Fin corank) (Fin corank) ℝ)
        - (chartGapOfDesign D).submatrix copick copick
        - Matrix.diagonal (fun coIndex => D.weight (copick coIndex))
      = 1 - (projectionOfDesign D).submatrix copick copick := by
    rw [chartGapOfDesign_submatrix D hcopick]
    abel
  rw [hleft, hright, projectionOfDesign]
  exact det_projectionBlock_eq_det_one_sub_complementBlock (scaledAtomRows D)
    (transpose_mul_scaledAtomRows D) hpart

/-- **THE LAW, DESIGN-FREE.**  The same statement about a `Gtz.ChartCore`: no atom,
no Parseval and no projection appears, only the symmetric matrix `M`, the weights,
and two complementary index maps. -/
theorem chartCore_det_gapBlock_shift_eq {size rank corank : ℕ} (core : ChartCore size rank)
    {pick : Fin rank → Fin size} {copick : Fin corank → Fin size}
    (hpick : Function.Injective pick) (hcopick : Function.Injective copick)
    (hpart : Function.Bijective (Sum.elim pick copick)) :
    ((core.gap).submatrix pick pick
        + Matrix.diagonal fun selectedIndex => core.weight (pick selectedIndex)).det
      = ((1 : Matrix (Fin corank) (Fin corank) ℝ)
          - (core.gap).submatrix copick copick
          - Matrix.diagonal fun coIndex => core.weight (copick coIndex)).det := by
  obtain ⟨D, hweight, hgap⟩ := exists_design_of_chartCore core
  rw [← hgap, ← hweight]
  exact det_chartGapBlock_shift_eq D hpick hcopick hpart

/-! ## Part 4 — the `(6,3)` reading

At six points and rank three both blocks are `3 × 3`, so the law pairs the twenty
principal blocks of `M` into ten complementary couples. -/

/-- **THE TWENTY BLOCKS OF A `(6,3)` CHART GAP ARE TEN NUMBERS READ TWICE.**  For
every triple and its complementary triple, the first shift of one block and the
second shift of the other have the SAME determinant.

This is a hard constraint on the matrix and it is weight-aware, but it is an
equality of DETERMINANTS and not of definiteness: at `3 × 3` a positive determinant
is consistent with two negative eigenvalues, which is exactly the parity failure
`Gtz.tripleGapDet_nonpos_iff_naimark` records.  It constrains a `(6,3)` tie without
deciding one. -/
theorem sixThree_complementary_block_law (D : WeightedDesign 6 3) (selected : Finset (Fin 6))
    (hcard : selected.card = 3) (hcompl : selectedᶜ.card = 3) :
    ((chartGapOfDesign D).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)
        + Matrix.diagonal fun selectedIndex =>
            D.weight (selected.orderEmbOfFin hcard selectedIndex)).det
      = ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (chartGapOfDesign D).submatrix (selectedᶜ.orderEmbOfFin hcompl)
              (selectedᶜ.orderEmbOfFin hcompl)
          - Matrix.diagonal fun coIndex =>
              D.weight (selectedᶜ.orderEmbOfFin hcompl coIndex)).det :=
  det_chartGapBlock_shift_eq D (selected.orderEmbOfFin hcard).injective
    (selectedᶜ.orderEmbOfFin hcompl).injective
    (sumElim_orderEmb_bijective selected hcard hcompl)

/-- **THE `(6,3)` LAW, WITH THE COMPLEMENT'S CARDINALITY DISCHARGED.**  The
complement of a triple in a six-set is a triple
(`Gtz.card_compl_eq_three_of_card_eq_three`, landed in
`Gtz/Design/UThreeSixDisjunction.lean`). -/
theorem sixThree_complementary_block_law' (D : WeightedDesign 6 3) (selected : Finset (Fin 6))
    (hcard : selected.card = 3) :
    ((chartGapOfDesign D).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)
        + Matrix.diagonal fun selectedIndex =>
            D.weight (selected.orderEmbOfFin hcard selectedIndex)).det
      = ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (chartGapOfDesign D).submatrix
              (selectedᶜ.orderEmbOfFin (card_compl_eq_three_of_card_eq_three selected hcard))
              (selectedᶜ.orderEmbOfFin (card_compl_eq_three_of_card_eq_three selected hcard))
          - Matrix.diagonal fun coIndex =>
              D.weight (selectedᶜ.orderEmbOfFin
                (card_compl_eq_three_of_card_eq_three selected hcard) coIndex)).det :=
  sixThree_complementary_block_law D selected hcard (card_compl_eq_three_of_card_eq_three selected hcard)

end Gtz

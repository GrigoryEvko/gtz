/-
# The Gale dual window: the layer law on the COMPLEMENTARY projection, and the uniform
# `(6,3)` stratum killed with no tie hypothesis

The primal layer window reads the twenty gap determinants of a `(6,3)` design against the
UNWEIGHTED moment `N`.  Its mirror reads them against the complementary projection.  Both
halves are landed here: the inequality that domination forces, and its evaluation on the
uniform slice.

    `galeDualWindow_nonpos_of_forall_dominates`  —  all twenty triples dominate
                                                    implies `e_3(R) - 4 e_2(R) + 10 tr R - 20 <= 0`
    `galeDualWindow_uniform_eq`                  —  at `t = 1/6` that quantity is `56/125`
    `not_forall_dominates_of_uniform_weights_sixThree`  —  hence the uniform stratum dies

`R := diag(1/s) (1 - P)` with `s_c = 1 - t_c` the SLACKS and `P` the design's projection
on the index space.

## Two corrections to the construction as it was handed over

**No `H`, no square roots, no dual vector family.**  The brief factored `1 - P = H Hᵀ`
with `HᵀH = 1`, set `u_c = h_c / sqrt(s_c)` and built the dual moment `M = Σ u_c u_cᵀ` on
`ℝ^3`.  That object is never needed.  Every quantity the window reads is a principal
BLOCK determinant of a `6 x 6` matrix, and `e_j(M) = e_j(diag(s)^{-1/2}(1 - P)
diag(s)^{-1/2})` for `j <= 3` by Cauchy-Binet — so the dual moment's invariants are
already invariants of the complementary projection.  Better still, the symmetric
conjugation and the one-sided `diag(1/s)(1 - P)` have the SAME shifted block
determinants, because on each block they differ by a diagonal similarity.  So no square
root occurs anywhere in this file and no orthonormal basis of a kernel is ever
constructed.  The brief's normalisation was correct as stated (`HᵀH = 1` does hold, the
slacks do total `size - 1`, the dual Loewner condition is `Σ_{c in C} u_c u_cᵀ <= 1`);
it is simply more machinery than the statement needs.

**The dual window is NOT the primal window rescaled, except on the uniform slice.**  The
`5^3 = 125` linking the primal `-56` to the dual `56/125` is real, and
`det_galeDualBlock_sub_one_eq_signed_scaled` is its exact form: on EVERY cell, at EVERY
weighting,

    `det(R_C - 1) = (-1)^rank * (∏_{c in C} t_c / s_c) * det(S_C - 1)` .

At `t = 1/6` the ratio is `(1/5)^3 = 1/125` on all twenty cells and the two aggregates are
proportional.  Off the uniform slice the ratio VARIES FROM TRIPLE TO TRIPLE, so the dual
aggregate is the primal aggregate REWEIGHTED, not rescaled, and the hoped-for derivation
of the general dual window from the shipped primal layer law does not exist.  The general
dual window is proved here on its own terms instead — and it needs less machinery than the
primal one, not more, because the double count alone suffices (see below).

## What the dual does and does not buy, stated against the same bridge

Cell by cell the dual inequality `det(R_C - 1) <= 0` and the primal inequality
`det(S_C - 1) >= 0` are the SAME statement, since the connecting factor is strictly
negative at rank three.  So the dual is not an independent per-cell test and no claim is
made here that it is.  What is independent is the AGGREGATE: the dual window is a second
closed-form linear functional of the same twenty nonnegative numbers, with positive
coefficients `∏_{c in C} t_c / s_c` instead of uniform ones, and having a closed form is
exactly what turns a functional into a no-go.

## THE BLOCK LAYER LAW, which is the reusable piece

    `Σ_{|C| = rank} det(M[C,C] - 1) = Σ_j (-1)^{rank+j} C(size-j, rank-j) e_j(M)`

for an ARBITRARY square `M` — no design, no symmetry, no positivity, no rank condition
(`sum_det_principalBlock_sub_one_eq`).  This is the sibling Cauchy-Binet lane's
`sum_det_subsetSum_sub_one_eq` with the Cauchy-Binet steps deleted: those steps existed
only to move an aggregate off the `size x size` Gram and onto the `rank x rank` moment,
and the dual window's object already lives on the big index.  What is left is the two
shipped combinatorial lemmas of `Gtz.Quantitative.MixtureAggregates` and nothing else.

## Relation to the primal route

`not_forall_dominates_of_uniform_weights_sixThree` is the SAME STATEMENT as
`TieFreeNoGo.not_forall_dominates_uniform_sixThree`, which gets it from the shipped `-56`
in three lines.  The bridge above explains why: on the uniform slice the two windows are
one identity read on `P` and on `1 - P`.  The dual route is recorded because the window
inequality it establishes is general-weight, and because it fixes the `56/125` as a
theorem rather than a measurement.

## Exact-rational cross-check performed outside Lean, no floats

Two hundred independently generated exact rational rank-three projections of `ℝ^6`, built
as `A (AᵀA)^{-1} Aᵀ` from random integer frames: the window of `(6/5)(1 - P)` came out
EXACTLY `56/125` and the window of `6 P` exactly `-56` in every case, confirming that both
values are projection-blind.  The per-cell bridge was checked to exact equality (residual
identically zero, `fractions.Fraction` throughout) on three genuinely non-uniform members
of the split-tetrahedron family.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.ProjectionForm
import Gtz.Quantitative.ChartHadamard
import Gtz.Quantitative.MixtureAggregates
import Gtz.Quantitative.CauchyBinetLayerSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## THE BLOCK LAYER LAW

The layer law for the principal BLOCKS of one fixed square matrix.  This is the
Cauchy-Binet lane's `sum_det_subsetSum_sub_one_eq` with the Cauchy-Binet steps removed:
those steps only served to move an aggregate off the `size × size` Gram and onto the
`rank × rank` moment, and when the object of interest already lives on the big index
there is nothing to move.  What remains is pure double counting, and it holds for an
ARBITRARY square matrix — no design, no symmetry, no positivity, no rank condition. -/

section BlockLayerLaw

variable {size : ℕ}

/-- Summing `e_level` of the principal blocks over all `rank`-subsets multiplies
`e_level` of the whole matrix by the number of `rank`-subsets containing a given
`level`-subset. -/
theorem sum_principalMinorTotal_principalBlock_eq (form : Matrix (Fin size) (Fin size) ℝ)
    (rank level : ℕ) (hlevel : level ≤ rank) :
    ∑ chosen ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
        principalMinorTotal (form.submatrix
          (Subtype.val : { index // index ∈ chosen } → Fin size) Subtype.val) level
      = (((size - level).choose (rank - level) : ℕ) : ℝ) * principalMinorTotal form level := by
  classical
  have hblock : ∀ chosen ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      principalMinorTotal (form.submatrix
          (Subtype.val : { index // index ∈ chosen } → Fin size) Subtype.val) level
        = ∑ inner ∈ chosen.powersetCard level,
            (form.submatrix (Subtype.val : { index // index ∈ inner } → Fin size)
              Subtype.val).det :=
    fun chosen _ => sum_det_principalSubmatrix_subtype form chosen level
  have hcount := sum_powersetCard_sum_powersetCard (indexType := Fin size) (baseRing := ℝ)
    rank level hlevel (fun inner => (form.submatrix
      (Subtype.val : { index // index ∈ inner } → Fin size) Subtype.val).det)
  rw [Finset.sum_congr rfl hblock, hcount, principalMinorTotal, Fintype.card_fin, nsmul_eq_mul]

/-- **THE BLOCK LAYER LAW.**  For every square matrix and every selection size,

    `Σ_{|C| = rank} det(M[C,C] − 1) = Σ_j (−1)^{rank+j} C(size−j, rank−j) e_j(M)` .

The right side depends on the matrix only through its first `rank + 1` principal-minor
totals, so the aggregate of the shifted block determinants is a fixed integral
combination of global invariants.  Nothing is assumed about `M`. -/
theorem sum_det_principalBlock_sub_one_eq (form : Matrix (Fin size) (Fin size) ℝ) (rank : ℕ) :
    ∑ chosen ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
        ((form.submatrix (Subtype.val : { index // index ∈ chosen } → Fin size)
          Subtype.val) - 1).det
      = ∑ level ∈ Finset.range (rank + 1),
          (-1 : ℝ) ^ (rank + level) * (((size - level).choose (rank - level) : ℕ) : ℝ)
            * principalMinorTotal form level := by
  have hexpand : ∀ chosen ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      ((form.submatrix (Subtype.val : { index // index ∈ chosen } → Fin size)
          Subtype.val) - 1).det
        = ∑ level ∈ Finset.range (rank + 1),
            (-1 : ℝ) ^ (rank + level) * principalMinorTotal (form.submatrix
              (Subtype.val : { index // index ∈ chosen } → Fin size) Subtype.val) level := by
    intro chosen hchosen
    have hcard : chosen.card = rank := (Finset.mem_powersetCard.mp hchosen).2
    have hshifted := det_sub_one_eq_sum_signed_principalMinorTotal (form.submatrix
      (Subtype.val : { index // index ∈ chosen } → Fin size) Subtype.val)
    rwa [Fintype.card_coe, hcard] at hshifted
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun level hlevel => ?_
  rw [← Finset.mul_sum, sum_principalMinorTotal_principalBlock_eq form rank level
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hlevel)), ← mul_assoc]

/-- **THE BLOCK LAYER LAW AT `(6,3)`**, the shape the campaign's window is stated in:

    `Σ_{|C| = 3} det(M[C,C] − 1) = e_3(M) − 4 e_2(M) + 10 tr M − 20` .

The coefficients are the three layer counts: each index lies in `C(5,2) = 10` triples,
each pair in `C(4,1) = 4`, and there are `C(6,3) = 20` triples. -/
theorem sum_det_principalBlock_sub_one_sixThree (form : Matrix (Fin 6) (Fin 6) ℝ) :
    ∑ chosen ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        ((form.submatrix (Subtype.val : { index // index ∈ chosen } → Fin 6)
          Subtype.val) - 1).det
      = principalMinorTotal form 3 - 4 * principalMinorTotal form 2
        + 10 * Matrix.trace form - 20 := by
  have hexpanded := sum_det_principalBlock_sub_one_eq form 3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, principalMinorTotal_one, principalMinorTotal_zero] at hexpanded
  rw [hexpanded]
  norm_num [Nat.choose]
  ring

end BlockLayerLaw

/-! ## Reindexing a principal block off the subtype

The block layer law indexes each block by the SUBTYPE `{c // c ∈ C}`; the shipped
projection kit indexes it by `C.orderEmbOfFin`.  One order isomorphism reconciles them,
and since only determinants are compared the reconciliation is a single application of
`Matrix.det_submatrix_equiv_self`. -/

section Reindex

variable {size : ℕ}

/-- Selecting a principal block commutes with subtraction. -/
theorem submatrix_sub_principal {selectionType : Type*}
    (leftForm rightForm : Matrix (Fin size) (Fin size) ℝ) (pick : selectionType → Fin size) :
    (leftForm - rightForm).submatrix pick pick
      = leftForm.submatrix pick pick - rightForm.submatrix pick pick := rfl

/-- Selecting a principal block commutes with the identity shift, on any injective
selection. -/
theorem submatrix_sub_one_principal {selectionType : Type*} [DecidableEq selectionType]
    (form : Matrix (Fin size) (Fin size) ℝ) (pick : selectionType → Fin size)
    (hinj : Function.Injective pick) :
    (form - 1).submatrix pick pick = form.submatrix pick pick - 1 := by
  rw [submatrix_sub_principal, Matrix.submatrix_one pick hinj]

/-- The subtype-indexed principal block and the `orderEmbOfFin`-indexed one have the same
determinant: they differ by the order isomorphism `Fin rank ≃o {c // c ∈ C}`. -/
theorem det_submatrix_val_eq_det_submatrix_orderEmb (form : Matrix (Fin size) (Fin size) ℝ)
    {chosen : Finset (Fin size)} {rank : ℕ} (hcard : chosen.card = rank) :
    (form.submatrix (Subtype.val : { index // index ∈ chosen } → Fin size) Subtype.val).det
      = (form.submatrix (chosen.orderEmbOfFin hcard) (chosen.orderEmbOfFin hcard)).det := by
  have hcompose : form.submatrix (chosen.orderEmbOfFin hcard) (chosen.orderEmbOfFin hcard)
      = (form.submatrix (Subtype.val : { index // index ∈ chosen } → Fin size)
          Subtype.val).submatrix (chosen.orderIsoOfFin hcard).toEquiv
            (chosen.orderIsoOfFin hcard).toEquiv := rfl
  rw [hcompose, Matrix.det_submatrix_equiv_self]

/-- The same reindexing for the SHIFTED block, which is the shape the layer law sums. -/
theorem det_submatrix_val_sub_one_eq (form : Matrix (Fin size) (Fin size) ℝ)
    {chosen : Finset (Fin size)} {rank : ℕ} (hcard : chosen.card = rank) :
    ((form.submatrix (Subtype.val : { index // index ∈ chosen } → Fin size) Subtype.val)
        - 1).det
      = (form.submatrix (chosen.orderEmbOfFin hcard) (chosen.orderEmbOfFin hcard) - 1).det := by
  have hsplitLeft := submatrix_sub_one_principal form
    (Subtype.val : { index // index ∈ chosen } → Fin size) Subtype.val_injective
  have hsplitRight := submatrix_sub_one_principal form (chosen.orderEmbOfFin hcard)
    (chosen.orderEmbOfFin hcard).injective
  rw [← hsplitLeft, ← hsplitRight,
    det_submatrix_val_eq_det_submatrix_orderEmb (form - 1) hcard]

/-- Selecting a principal block of a left-diagonal product selects the diagonal too. -/
theorem submatrix_diagonal_mul {selectionSize : ℕ} (scale : Fin size → ℝ)
    (form : Matrix (Fin size) (Fin size) ℝ) (pick : Fin selectionSize → Fin size) :
    (Matrix.diagonal scale * form).submatrix pick pick
      = Matrix.diagonal (fun slot => scale (pick slot)) * form.submatrix pick pick := by
  ext leftSlot rightSlot
  rw [Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.submatrix_apply]

/-- A product over a `rank`-subset, read along its order embedding. -/
theorem prod_orderEmbOfFin_eq {rank : ℕ} (chosen : Finset (Fin size))
    (hcard : chosen.card = rank) (scale : Fin size → ℝ) :
    ∏ slot, scale (chosen.orderEmbOfFin hcard slot) = ∏ index ∈ chosen, scale index := by
  have himage : Finset.image (chosen.orderEmbOfFin hcard) Finset.univ = chosen := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  calc ∏ slot, scale (chosen.orderEmbOfFin hcard slot)
      = ∏ index ∈ Finset.image (chosen.orderEmbOfFin hcard) Finset.univ, scale index :=
        (Finset.prod_image
          fun left _ right _ hlr => (chosen.orderEmbOfFin hcard).injective hlr).symm
    _ = ∏ index ∈ chosen, scale index := by rw [himage]

end Reindex

/-! ## The square transpose flip on determinants -/

/-- For a SQUARE matrix the two shifted products have the same determinant:
`det(MᵀM − 1) = det(MMᵀ − 1)`.  Weinstein–Aronszajn, with the sign of `det(−A)`
cancelling because both sides have the same dimension.  The shipped
`Gtz.posSemidef_transpose_mul_sub_one_comm` is the Loewner reading of the same flip. -/
theorem det_transpose_mul_sub_one_comm {dimension : ℕ}
    (square : Matrix (Fin dimension) (Fin dimension) ℝ) :
    (squareᵀ * square - 1).det = (square * squareᵀ - 1).det := by
  have hflip : (1 + (-squareᵀ) * square).det = (1 + square * (-squareᵀ)).det :=
    Matrix.det_one_add_mul_comm (-squareᵀ) square
  have hleft : (1 : Matrix (Fin dimension) (Fin dimension) ℝ) + (-squareᵀ) * square
      = -(squareᵀ * square - 1) := by
    rw [Matrix.neg_mul]; abel
  have hright : (1 : Matrix (Fin dimension) (Fin dimension) ℝ) + square * (-squareᵀ)
      = -(square * squareᵀ - 1) := by
    rw [Matrix.mul_neg]; abel
  rw [hleft, hright, Matrix.det_neg, Matrix.det_neg] at hflip
  have hunit : ((-1 : ℝ)) ^ dimension ≠ 0 := pow_ne_zero _ (by norm_num)
  simpa [Fintype.card_fin] using
    mul_left_cancel₀ hunit (by simpa [Fintype.card_fin] using hflip)

/-! ## The Gale dual form

`P = V Vᵀ` is the design's projection on the index space and `1 - P` its complement.  The
Gale dual rescales the complement by the inverse SLACKS `s_c = 1 - t_c`, mirroring the
primal rescaling of `P` by the inverse weights `t_c`.

There is no square root, no orthonormal basis `H` of the kernel and no dual vector family
anywhere in what follows.  The symmetric dual `diag(s)^{-1/2}(1 - P) diag(s)^{-1/2}` and
the one-sided `diag(1/s)(1 - P)` used here differ by a diagonal similarity on every
principal block, so all their shifted block determinants agree — and those determinants
are the only thing the layer law reads. -/

section GaleDual

variable {size rank : ℕ}

/-- The SLACK of an atom, `s_c = 1 - t_c`: the dual weight.  The slacks total
`size - 1`. -/
def dualSlackOf (design : WeightedDesign size rank) (atomIndex : Fin size) : ℝ :=
  1 - design.weight atomIndex

/-- Every slack is positive once there are at least two atoms. -/
theorem dualSlackOf_pos (design : WeightedDesign size rank) (hsize : 2 ≤ size) (atomIndex : Fin size) :
    0 < dualSlackOf design atomIndex := by
  have hlt := weight_lt_one design hsize atomIndex
  rw [dualSlackOf]
  linarith

/-- **THE GALE DUAL FORM**: the complementary projection rescaled by the inverse slacks,
`R = diag(1/s)(1 − P)`. -/
noncomputable def galeDualForm (design : WeightedDesign size rank) : Matrix (Fin size) (Fin size) ℝ :=
  Matrix.diagonal (fun atomIndex => (dualSlackOf design atomIndex)⁻¹) * (1 - projectionOfDesign design)

/-- **THE PER-CELL DUAL GAP FACTORS THROUGH THE PRIMAL PROJECTION BLOCK.**  On any
injective selection,

    `det(R_C − 1) = (∏_{c ∈ C} 1/s_c) · det(diag t_C − P_C)` .

The prefactor is a positive product, so the dual gap determinant carries exactly the sign
of `det(diag t_C − P_C)` — which is `(−1)^{|C|}` times the primal domination test.  The
identity is `diag(1/s)(1 − P_C) − 1 = diag(1/s)(1 − P_C − diag s)` together with
`1 − diag s = diag t`. -/
theorem det_galeDualBlock_sub_one (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    {selectionSize : ℕ} (pick : Fin selectionSize → Fin size) (hinj : Function.Injective pick) :
    ((galeDualForm design).submatrix pick pick - 1).det
      = (∏ slot, (dualSlackOf design (pick slot))⁻¹)
        * (Matrix.diagonal (fun slot => design.weight (pick slot))
            - (projectionOfDesign design).submatrix pick pick).det := by
  have honeBlock : (1 : Matrix (Fin size) (Fin size) ℝ).submatrix pick pick = 1 :=
    Matrix.submatrix_one pick hinj
  have hcancel : Matrix.diagonal (fun slot => (dualSlackOf design (pick slot))⁻¹)
      * Matrix.diagonal (fun slot => dualSlackOf design (pick slot))
      = (1 : Matrix (Fin selectionSize) (Fin selectionSize) ℝ) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun slot =>
      inv_mul_cancel₀ (dualSlackOf_pos design hsize (pick slot)).ne')
  have hslackDiagonal : Matrix.diagonal (fun slot => dualSlackOf design (pick slot))
      = 1 - Matrix.diagonal (fun slot => design.weight (pick slot)) := by
    ext leftSlot rightSlot
    rcases eq_or_ne leftSlot rightSlot with rfl | hne
    · simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.one_apply_eq, dualSlackOf]
    · simp only [Matrix.diagonal_apply_ne _ hne, Matrix.sub_apply, Matrix.one_apply_ne hne]
      ring
  have hfactor : (galeDualForm design).submatrix pick pick - 1
      = Matrix.diagonal (fun slot => (dualSlackOf design (pick slot))⁻¹)
        * (Matrix.diagonal (fun slot => design.weight (pick slot))
            - (projectionOfDesign design).submatrix pick pick) := by
    have hexpandRight : Matrix.diagonal (fun slot => (dualSlackOf design (pick slot))⁻¹)
          * (Matrix.diagonal (fun slot => design.weight (pick slot))
              - (projectionOfDesign design).submatrix pick pick)
        = Matrix.diagonal (fun slot => (dualSlackOf design (pick slot))⁻¹)
          * ((1 - (projectionOfDesign design).submatrix pick pick)
              - Matrix.diagonal (fun slot => dualSlackOf design (pick slot))) := by
      congr 1
      rw [hslackDiagonal]
      abel
    rw [hexpandRight, Matrix.mul_sub, hcancel, galeDualForm, submatrix_diagonal_mul,
      submatrix_sub_principal, honeBlock]
  rw [hfactor, Matrix.det_mul, Matrix.det_diagonal]

/-- **THE PRIMAL–DUAL PER-CELL BRIDGE.**  On every `rank`-subset the dual gap determinant
is a fixed multiple of the primal one:

    `det(R_C − 1) = (−1)^rank · (∏_{c ∈ C} t_c / s_c) · det(S_C − 1)` .

This is the exact statement behind the numerical coincidence that the uniform primal layer
anchor is `-56` while the uniform dual excess is `56/125`: at `t ≡ 1/6` the ratio is
`((1/6)/(5/6))^3 = 1/125` and the rank-three sign is `-1`.

It also settles what the dual DOES and DOES NOT buy.  Cell by cell the dual inequality
`det(R_C − 1) ≤ 0` and the primal inequality `det(S_C − 1) ≥ 0` are the SAME statement, so
the dual is not an independent test.  What differs is the aggregate: the dual window is
the layer sum of the twenty primal gap determinants REWEIGHTED by `∏_{c ∈ C} t_c / s_c`,
and that reweighted aggregate has its own closed form.  Only on the uniform slice are the
weights constant and the two aggregates proportional. -/
theorem det_galeDualBlock_sub_one_eq_signed_scaled (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    {chosen : Finset (Fin size)} (hcard : chosen.card = rank) :
    ((galeDualForm design).submatrix
        (Subtype.val : { index // index ∈ chosen } → Fin size) Subtype.val - 1).det
      = ((-1 : ℝ) ^ rank * ∏ index ∈ chosen, (design.weight index / dualSlackOf design index))
        * (subsetSum design chosen - 1).det := by
  have hinj : Function.Injective (chosen.orderEmbOfFin hcard) :=
    (chosen.orderEmbOfFin hcard).injective
  have himage : Finset.image (chosen.orderEmbOfFin hcard) Finset.univ = chosen := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  have hnegate : (Matrix.diagonal (fun slot => design.weight (chosen.orderEmbOfFin hcard slot))
        - (projectionOfDesign design).submatrix (chosen.orderEmbOfFin hcard)
            (chosen.orderEmbOfFin hcard)).det
      = (-1 : ℝ) ^ rank * ((projectionOfDesign design).submatrix (chosen.orderEmbOfFin hcard)
            (chosen.orderEmbOfFin hcard)
          - Matrix.diagonal (fun slot => design.weight (chosen.orderEmbOfFin hcard slot))).det := by
    have hnegForm : Matrix.diagonal (fun slot => design.weight (chosen.orderEmbOfFin hcard slot))
          - (projectionOfDesign design).submatrix (chosen.orderEmbOfFin hcard)
              (chosen.orderEmbOfFin hcard)
        = -((projectionOfDesign design).submatrix (chosen.orderEmbOfFin hcard)
              (chosen.orderEmbOfFin hcard)
            - Matrix.diagonal (fun slot =>
                design.weight (chosen.orderEmbOfFin hcard slot))) := by abel
    rw [hnegForm, Matrix.det_neg, Fintype.card_fin]
  have hgram : ((projectionOfDesign design).submatrix (chosen.orderEmbOfFin hcard)
          (chosen.orderEmbOfFin hcard)
        - Matrix.diagonal (fun slot => design.weight (chosen.orderEmbOfFin hcard slot))).det
      = (∏ slot, design.weight (chosen.orderEmbOfFin hcard slot)) * (subsetSum design chosen - 1).det := by
    rw [det_projectionBlock_sub_weightDiagonal design (chosen.orderEmbOfFin hcard),
      ← det_transpose_mul_sub_one_comm (selectedAtomRows design (chosen.orderEmbOfFin hcard)),
      transpose_mul_selectedAtomRows design (chosen.orderEmbOfFin hcard) hinj, himage]
  have hproduct : (∏ slot, (dualSlackOf design (chosen.orderEmbOfFin hcard slot))⁻¹)
        * (∏ slot, design.weight (chosen.orderEmbOfFin hcard slot))
      = ∏ index ∈ chosen, (design.weight index / dualSlackOf design index) := by
    rw [← Finset.prod_mul_distrib, ← prod_orderEmbOfFin_eq chosen hcard
      (fun index => design.weight index / dualSlackOf design index)]
    exact Finset.prod_congr rfl fun slot _ => by rw [div_eq_mul_inv]; ring
  rw [det_submatrix_val_sub_one_eq (galeDualForm design) hcard,
    det_galeDualBlock_sub_one design hsize (chosen.orderEmbOfFin hcard) hinj, hnegate, hgram,
    ← hproduct]
  ring

end GaleDual

/-! ## The `(6,3)` dual window -/

section SixThreeDualWindow

/-- At rank three the sign is `(-1)^3 = -1`: the dual gap determinant is MINUS a positive
multiple of the primal one. -/
theorem det_galeDualBlock_sub_one_sixThree (design : WeightedDesign 6 3)
    {chosen : Finset (Fin 6)} (hcard : chosen.card = 3) :
    ((galeDualForm design).submatrix
        (Subtype.val : { index // index ∈ chosen } → Fin 6) Subtype.val - 1).det
      = -(∏ index ∈ chosen, (design.weight index / dualSlackOf design index))
        * (subsetSum design chosen - 1).det := by
  rw [det_galeDualBlock_sub_one_eq_signed_scaled design (by norm_num) hcard]
  norm_num

/-- **DOMINATION MAKES THE DUAL GAP DETERMINANT NONPOSITIVE.**  The primal gap
determinant is nonnegative because `Dominates` IS positive semidefiniteness of the gap;
the dual one is a negative multiple of it. -/
theorem det_galeDualBlock_sub_one_nonpos_of_dominates (design : WeightedDesign 6 3)
    {chosen : Finset (Fin 6)} (hcard : chosen.card = 3) (hdominates : Dominates design chosen) :
    ((galeDualForm design).submatrix
        (Subtype.val : { index // index ∈ chosen } → Fin 6) Subtype.val - 1).det ≤ 0 := by
  have hprimal : 0 ≤ (subsetSum design chosen - 1).det := hdominates.det_nonneg
  have hpositive : 0 < ∏ index ∈ chosen, (design.weight index / dualSlackOf design index) :=
    Finset.prod_pos fun index _ =>
      div_pos (design.weight_pos index) (dualSlackOf_pos design (by norm_num) index)
  rw [det_galeDualBlock_sub_one_sixThree design hcard]
  nlinarith [hprimal, hpositive]

/-- **THE GENERAL DUAL WINDOW.**  If every triple of a `(6,3)` design weakly dominates
then the Gale dual form's window is nonpositive:

    `e_3(R) − 4 e_2(R) + 10 tr R − 20 ≤ 0`,     `R = diag(1/s)(1 − P)` .

No tie, no uniformity, no genericity.  This is the mirror of the primal layer window
`det N − 4 e_2(N) + 10 tr N − 20 ≥ 0`, on the complementary projection and with the
inequality reversed, and the two are genuinely different functionals: by
`det_galeDualBlock_sub_one_eq_signed_scaled` the dual aggregate is the primal one
REWEIGHTED cell by cell by `∏_{c ∈ C} t_c / s_c`. -/
theorem galeDualWindow_nonpos_of_forall_dominates (design : WeightedDesign 6 3)
    (hall : ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected) :
    principalMinorTotal (galeDualForm design) 3
        - 4 * principalMinorTotal (galeDualForm design) 2
        + 10 * Matrix.trace (galeDualForm design) - 20 ≤ 0 := by
  rw [← sum_det_principalBlock_sub_one_sixThree]
  refine Finset.sum_nonpos fun chosen hchosen => ?_
  have hcard : chosen.card = 3 := (Finset.mem_powersetCard.mp hchosen).2
  exact det_galeDualBlock_sub_one_nonpos_of_dominates design hcard (hall chosen hcard)

/-! ### The uniform slice: the dual window value is the design-blind `56/125` -/

/-- At a uniform weight every slack is `5/6`, so every cell's dual-to-primal ratio is the
SAME rational `-(1/5)^3 = -1/125`.  This is where the uniform slice becomes rigid: off it
the ratio varies from triple to triple. -/
theorem det_galeDualBlock_sub_one_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = ((6 : ℝ))⁻¹)
    {chosen : Finset (Fin 6)} (hcard : chosen.card = 3) :
    ((galeDualForm design).submatrix
        (Subtype.val : { index // index ∈ chosen } → Fin 6) Subtype.val - 1).det
      = -((125 : ℝ)⁻¹) * (subsetSum design chosen - 1).det := by
  have hratio : ∀ index ∈ chosen,
      design.weight index / dualSlackOf design index = ((5 : ℝ))⁻¹ := by
    intro index _
    rw [dualSlackOf, huniform index]
    norm_num
  rw [det_galeDualBlock_sub_one_sixThree design hcard, Finset.prod_congr rfl hratio,
    Finset.prod_const, hcard]
  norm_num

/-- **THE UNIFORM DUAL AGGREGATE IS `56/125`, AT EVERY UNIFORM DESIGN.**  The twenty dual
gap determinants total the primal `-56` scaled by `-1/125`.  The value does not depend on
the design: exactly as the primal aggregate is design-blind on the uniform slice, so is
its dual, and the two blindnesses are one statement seen twice. -/
theorem sum_det_galeDualBlock_sub_one_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = ((6 : ℝ))⁻¹) :
    ∑ chosen ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        ((galeDualForm design).submatrix
          (Subtype.val : { index // index ∈ chosen } → Fin 6) Subtype.val - 1).det
      = 56 / 125 := by
  have hterm : ∀ chosen ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      ((galeDualForm design).submatrix
          (Subtype.val : { index // index ∈ chosen } → Fin 6) Subtype.val - 1).det
        = -((125 : ℝ)⁻¹) * (subsetSum design chosen - 1).det :=
    fun chosen hchosen => det_galeDualBlock_sub_one_uniform design huniform
      (Finset.mem_powersetCard.mp hchosen).2
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_det_subsetSum_sub_one_sixThree design huniform]
  norm_num

/-- **THE UNIFORM DUAL WINDOW VALUE, IN CLOSED FORM.**  At every uniform `(6,3)` design

    `e_3(R) − 4 e_2(R) + 10 tr R − 20 = 56/125` ,

a positive constant independent of the design.  Mechanically this is the block layer law
evaluated against the shipped `-56`; conceptually it is the statement that the Gale dual
of a uniform design has its dual moment pinned to `(6/5)` times the identity on a
three-dimensional space, leaving the window no freedom at all. -/
theorem galeDualWindow_uniform_eq (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = ((6 : ℝ))⁻¹) :
    principalMinorTotal (galeDualForm design) 3
        - 4 * principalMinorTotal (galeDualForm design) 2
        + 10 * Matrix.trace (galeDualForm design) - 20 = 56 / 125 := by
  rw [← sum_det_principalBlock_sub_one_sixThree]
  exact sum_det_galeDualBlock_sub_one_uniform design huniform

/-- **NO UNIFORM `(6,3)` DESIGN HAS ALL TWENTY TRIPLES WEAKLY DOMINATING**, proved from
the Gale dual.  Domination forces the dual window `≤ 0`; a uniform weight forces it to be
exactly `56/125 > 0`.  No tie hypothesis anywhere.

This is the same cell that `TieFreeNoGo.not_forall_dominates_uniform_sixThree` reaches
from the primal `-56`, and the per-cell bridge
`det_galeDualBlock_sub_one_eq_signed_scaled` shows why: on the uniform slice the two
aggregates differ by the constant factor `-(1/5)^3`, so they are one theorem read on `P`
and on `1 - P`.  Off the uniform slice the reweighting is triple-dependent and the two
windows separate. -/
theorem not_forall_dominates_of_uniform_weights_sixThree (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = ((6 : ℝ))⁻¹)
    (hall : ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected) :
    False := by
  have hnonpos := galeDualWindow_nonpos_of_forall_dominates design hall
  rw [galeDualWindow_uniform_eq design huniform] at hnonpos
  norm_num at hnonpos

/-- **THE DUAL NO-GO OFF THE UNIFORM SLICE.**  Any `(6,3)` design whose dual window is
strictly positive fails to have all twenty triples dominating, at any weighting.  The
uniform theorem is the `56/125` instance. -/
theorem not_forall_dominates_of_galeDualWindow_pos (design : WeightedDesign 6 3)
    (hwindow : 0 < principalMinorTotal (galeDualForm design) 3
        - 4 * principalMinorTotal (galeDualForm design) 2
        + 10 * Matrix.trace (galeDualForm design) - 20)
    (hall : ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected) :
    False :=
  absurd (galeDualWindow_nonpos_of_forall_dominates design hall) (not_le.mpr hwindow)

end SixThreeDualWindow

end Gtz

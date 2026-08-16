/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Wave.SignBlindCeiling
import Gtz.Wave.SelectionMarginLaws
import Gtz.Wave.ProjectionMinorShift
import Gtz.Wave.ProjectionBlockObjective
import Gtz.Reduction.DiagonalRungs

/-!
# The complementary projection lane

At `(6,3)` the rank is half the label count, so `P` and `1 − P` are both
rank-three symmetric idempotents on six labels.  This module prices that
involution.

The domination gap rearranges as `P_C − diag w_C = diag (1 − w)_C − (1 − P)_C`
(`Gtz.projectionBlock_sub_weightDiagonal_eq_coWeight_sub_complementBlock`), so
the dual READING of the objective is a rearrangement and nothing more.  What is
not a rearrangement is the dual DESIGN: the block gap of `1 − P` against the
same weight is a different matrix, and comparing the two is new.

The two gap blocks always carry opposite off-diagonal entries, and their
diagonals agree exactly when every leverage sits at one half.  On that locus the
dual gap is therefore the primal gap with every pairing negated, so

    det (dual gap) = evenPart − 2·cross,   det (primal gap) = evenPart + 2·cross

and the minimum of the two IS the sign-free margin.  The whole sign-blind class
was computing the minimum over this involution all along, which is why it goes
silent exactly where the involution has a fixed point.

The consequence is a ceiling with a mechanism.  A sound certificate that reads
only the diagonal gaps and the SQUARED pairings cannot distinguish `P` from
`1 − P` on the flat locus, so firing at a triple forces BOTH blocks positive
definite, hence a two-sided sandwich `diag w_C ≺ P_C ≺ diag (1 − w)_C`.  At the
graphic point of `K4` no triple is sandwiched — every triple has one of its two
gap determinants strictly negative — so no such certificate fires anywhere
there, and that is proved in rational arithmetic with no eigenvalue.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size : ℕ}

/-- Reading a symmetric form at swapped arguments.  The corpus states symmetry
as a transpose equation, and every entrywise proof below needs the pointwise
form. -/
theorem apply_symm_of_transpose_eq {count : ℕ} {form : Matrix (Fin count) (Fin count) ℝ}
    (hsymm : formᵀ = form) (left right : Fin count) :
    form left right = form right left := by
  conv_lhs => rw [← hsymm]
  rfl

/-! ## 1. The level-two cross law

The pair minor of the complement exceeds the pair minor of the form by a purely
diagonal quantity.  No off-diagonal entry survives the difference, because the
complement negates an off-diagonal entry and the pair minor reads its square.
-/

/-- **THE LEVEL-TWO CROSS LAW.**  At distinct labels the complement's pair minor
is the form's, shifted by `1 − M_aa − M_bb`.  Hypothesis-free, and the shift
sees no off-diagonal entry at all. -/
theorem pairMinorAt_one_sub_eq (form : Matrix (Fin size) (Fin size) ℝ)
    {first second : Fin size} (hne : first ≠ second) :
    pairMinorAt (1 - form) first second
      = 1 - form first first - form second second + pairMinorAt form first second := by
  simp only [pairMinorAt, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne hne]
  ring

/-- The two pair minors agree exactly when the two diagonal entries total one.
The difference itself is `Gtz.pairMinorAt_one_sub_sub_pairMinorAt`, landed for a
design's projection; the equation above is its general-matrix form, which the
graphic point needs because that point is a bare rational matrix. -/
theorem pairMinorAt_one_sub_eq_self_iff (form : Matrix (Fin size) (Fin size) ℝ)
    {first second : Fin size} (hne : first ≠ second) :
    pairMinorAt (1 - form) first second = pairMinorAt form first second
      ↔ form first first + form second second = 1 := by
  rw [← sub_eq_zero, pairMinorAt_one_sub_eq form hne]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## 2. The flat locus

A form is flat when every diagonal entry is one half.  This is the fixed locus
of the involution `M ↦ 1 − M` read on the diagonal, and it is exactly the
equal-share stratum of the campaign at `(6,3)`.
-/

/-- A form is FLAT when every diagonal entry is one half — the fixed locus of
the complementation involution. -/
def IsFlatDiagonal (form : Matrix (Fin size) (Fin size) ℝ) : Prop :=
  ∀ label : Fin size, form label label = 1 / 2

/-- On the flat locus the complement has the same diagonal as the form. -/
theorem one_sub_diag_of_flat {form : Matrix (Fin size) (Fin size) ℝ}
    (hflat : IsFlatDiagonal form) (label : Fin size) :
    (1 - form) label label = form label label := by
  rw [Matrix.sub_apply, Matrix.one_apply_eq, hflat label]; norm_num

/-- The complement of a flat form is flat. -/
theorem isFlatDiagonal_one_sub {form : Matrix (Fin size) (Fin size) ℝ}
    (hflat : IsFlatDiagonal form) : IsFlatDiagonal (1 - form) := by
  intro label
  rw [one_sub_diag_of_flat hflat label, hflat label]

/-- On the flat locus the level-two cross law holds at EVERY pair, the diagonal
included, because both sides vanish there. -/
theorem pairMinorAt_one_sub_eq_of_flat {form : Matrix (Fin size) (Fin size) ℝ}
    (hflat : IsFlatDiagonal form) (first second : Fin size) :
    pairMinorAt (1 - form) first second
      = 1 - form first first - form second second + pairMinorAt form first second := by
  rcases eq_or_ne first second with rfl | hne
  · rw [pairMinorAt_self, pairMinorAt_self, hflat first]; norm_num
  · exact pairMinorAt_one_sub_eq form hne

/-- **THE LEVEL-TWO TOTAL IS INVARIANT ON THE FLAT LOCUS.**  The ordered double
sum of pair minors is the same for a flat form and for its complement.  The
correction totals `size² − 2·size·trace`, and flatness puts the trace at half
the size, so it vanishes.  RANK enters here as `2·rank = size`. -/
theorem sum_pairMinorAt_one_sub_eq_of_flat {form : Matrix (Fin size) (Fin size) ℝ}
    (hflat : IsFlatDiagonal form) :
    ∑ first : Fin size, ∑ second : Fin size, pairMinorAt (1 - form) first second
      = ∑ first : Fin size, ∑ second : Fin size, pairMinorAt form first second := by
  have hpoint : ∀ first second : Fin size,
      pairMinorAt (1 - form) first second = pairMinorAt form first second := by
    intro first second
    rw [pairMinorAt_one_sub_eq_of_flat hflat first second, hflat first, hflat second]
    ring
  exact Finset.sum_congr rfl fun first _ =>
    Finset.sum_congr rfl fun second _ => hpoint first second

/-! ## 3. The gap block and the involution

The gap block subtracts the weight diagonal from a principal block.  Its
diagonal is the weighted surplus and its off-diagonal is the form's own entry,
so the whole sign structure of the objective lives in it with no square root.
-/

/-- The gap block of a form against a weight, at a selection of three labels. -/
noncomputable def blockGapAt (form : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (pick : Fin 3 → Fin size) : Matrix (Fin 3) (Fin 3) ℝ :=
  form.submatrix pick pick - Matrix.diagonal fun slot => weight (pick slot)

theorem blockGapAt_apply_diag (form : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (pick : Fin 3 → Fin size) (slot : Fin 3) :
    blockGapAt form weight pick slot slot
      = form (pick slot) (pick slot) - weight (pick slot) := by
  simp [blockGapAt]

theorem blockGapAt_apply_offDiag (form : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (pick : Fin 3 → Fin size) {left right : Fin 3}
    (hne : left ≠ right) :
    blockGapAt form weight pick left right = form (pick left) (pick right) := by
  simp [blockGapAt, Matrix.diagonal_apply_ne _ hne]

/-- The gap block of a symmetric form is symmetric, provided the selection is
injective. -/
theorem blockGapAt_transpose {form : Matrix (Fin size) (Fin size) ℝ} (hsymm : formᵀ = form)
    (weight : Fin size → ℝ) (pick : Fin 3 → Fin size) :
    (blockGapAt form weight pick)ᵀ = blockGapAt form weight pick := by
  ext left right
  simp only [blockGapAt, Matrix.transpose_apply, Matrix.sub_apply, Matrix.submatrix_apply,
    Matrix.diagonal_apply]
  rcases eq_or_ne right left with rfl | hne
  · simp
  · rw [if_neg hne, if_neg (Ne.symm hne)]
    rw [apply_symm_of_transpose_eq hsymm (pick right) (pick left)]

/-- **THE OFF-DIAGONALS ALWAYS FLIP.**  The complement's gap block carries the
negated off-diagonal entry, at every form and every weight. -/
theorem blockGapAt_one_sub_offDiag (form : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) {pick : Fin 3 → Fin size} (hinj : Function.Injective pick)
    {left right : Fin 3} (hne : left ≠ right) :
    blockGapAt (1 - form) weight pick left right
      = -blockGapAt form weight pick left right := by
  rw [blockGapAt_apply_offDiag _ _ _ hne, blockGapAt_apply_offDiag _ _ _ hne,
    Matrix.sub_apply, Matrix.one_apply_ne (fun heq => hne (hinj heq))]
  ring

/-- **THE DIAGONALS AGREE EXACTLY ON THE FLAT LOCUS.** -/
theorem blockGapAt_one_sub_diag_of_flat {form : Matrix (Fin size) (Fin size) ℝ}
    (hflat : IsFlatDiagonal form) (weight : Fin size → ℝ) (pick : Fin 3 → Fin size)
    (slot : Fin 3) :
    blockGapAt (1 - form) weight pick slot slot = blockGapAt form weight pick slot slot := by
  rw [blockGapAt_apply_diag, blockGapAt_apply_diag, one_sub_diag_of_flat hflat]

/-- The diagonals agree ONLY on the flat locus: the gap between them is
`1 − 2·M_cc`, so equality at a label pins that leverage at one half. -/
theorem blockGapAt_one_sub_diag_eq_iff (form : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (pick : Fin 3 → Fin size) (slot : Fin 3) :
    blockGapAt (1 - form) weight pick slot slot = blockGapAt form weight pick slot slot
      ↔ form (pick slot) (pick slot) = 1 / 2 := by
  rw [blockGapAt_apply_diag, blockGapAt_apply_diag, Matrix.sub_apply, Matrix.one_apply_eq]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ## 5. The determinant law, and the sign-free margin as a minimum -/

/-- The gap determinant is the campaign's triple determinant form, read on the
gap's own diagonal and off-diagonal entries.  No square root, no weight
normalisation. -/
theorem det_blockGapAt_eq_tripleDetForm {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : formᵀ = form) (weight : Fin size → ℝ) (pick : Fin 3 → Fin size) :
    (blockGapAt form weight pick).det
      = tripleDetForm (blockGapAt form weight pick 0 0) (blockGapAt form weight pick 1 1)
          (blockGapAt form weight pick 2 2) (blockGapAt form weight pick 0 1)
          (blockGapAt form weight pick 0 2) (blockGapAt form weight pick 1 2) := by
  have hgap := blockGapAt_transpose hsymm weight pick
  rw [Matrix.det_fin_three, tripleDetForm,
    apply_symm_of_transpose_eq hgap 1 0, apply_symm_of_transpose_eq hgap 2 0,
    apply_symm_of_transpose_eq hgap 2 1]
  ring

/-- **THE DUAL DETERMINANT IS THE SIGN-FLIPPED DETERMINANT.**  On the flat locus
the complement's gap block has the same diagonal and the negated off-diagonals,
so its determinant is the even part MINUS twice the cross term, while the form's
is the even part PLUS twice the cross term.

This is the geometric content of the whole sign-blind class: the sign flip that
class cannot see IS the complementation involution. -/
theorem det_blockGapAt_one_sub_of_flat {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : formᵀ = form) (hflat : IsFlatDiagonal form) (weight : Fin size → ℝ)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick) :
    (blockGapAt (1 - form) weight pick).det
      = evenTripleDetPart (blockGapAt form weight pick 0 0) (blockGapAt form weight pick 1 1)
          (blockGapAt form weight pick 2 2) (blockGapAt form weight pick 0 1)
          (blockGapAt form weight pick 0 2) (blockGapAt form weight pick 1 2)
        - 2 * (blockGapAt form weight pick 0 1 * blockGapAt form weight pick 0 2
            * blockGapAt form weight pick 1 2) := by
  have hsymm' : (1 - form)ᵀ = 1 - form := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymm]
  rw [det_blockGapAt_eq_tripleDetForm hsymm' weight pick]
  rw [blockGapAt_one_sub_diag_of_flat hflat, blockGapAt_one_sub_diag_of_flat hflat,
    blockGapAt_one_sub_diag_of_flat hflat,
    blockGapAt_one_sub_offDiag form weight hinj (by decide : (0 : Fin 3) ≠ 1),
    blockGapAt_one_sub_offDiag form weight hinj (by decide : (0 : Fin 3) ≠ 2),
    blockGapAt_one_sub_offDiag form weight hinj (by decide : (1 : Fin 3) ≠ 2)]
  rw [tripleDetForm, evenTripleDetPart]
  ring

/-- **THE SUM LAW.**  The two gap determinants total twice the even part, so
their average is sign-free. -/
theorem det_blockGapAt_add_det_one_sub_of_flat {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : formᵀ = form) (hflat : IsFlatDiagonal form) (weight : Fin size → ℝ)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick) :
    (blockGapAt form weight pick).det + (blockGapAt (1 - form) weight pick).det
      = 2 * evenTripleDetPart (blockGapAt form weight pick 0 0)
          (blockGapAt form weight pick 1 1) (blockGapAt form weight pick 2 2)
          (blockGapAt form weight pick 0 1) (blockGapAt form weight pick 0 2)
          (blockGapAt form weight pick 1 2) := by
  rw [det_blockGapAt_eq_tripleDetForm hsymm weight pick,
    det_blockGapAt_one_sub_of_flat hsymm hflat weight hinj, tripleDetForm, evenTripleDetPart]
  ring

/-- **THE DIFFERENCE LAW.**  The two gap determinants differ by four times the
cross term, and by nothing else. -/
theorem det_blockGapAt_sub_det_one_sub_of_flat {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : formᵀ = form) (hflat : IsFlatDiagonal form) (weight : Fin size → ℝ)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick) :
    (blockGapAt form weight pick).det - (blockGapAt (1 - form) weight pick).det
      = 4 * (blockGapAt form weight pick 0 1 * blockGapAt form weight pick 0 2
          * blockGapAt form weight pick 1 2) := by
  rw [det_blockGapAt_eq_tripleDetForm hsymm weight pick,
    det_blockGapAt_one_sub_of_flat hsymm hflat weight hinj, tripleDetForm, evenTripleDetPart]
  ring

/-- The elementary scalar fact behind the headline: the minimum of a value and
its cross-flipped partner is the value minus twice the absolute cross term. -/
theorem min_add_sub_two_mul_abs (evenPart cross : ℝ) :
    min (evenPart + 2 * cross) (evenPart - 2 * cross) = evenPart - 2 * |cross| := by
  rcases le_total 0 cross with hcross | hcross
  · rw [abs_of_nonneg hcross, min_eq_right (by linarith)]
  · rw [abs_of_nonpos hcross, min_eq_left (by linarith)]
    ring

/-- **THE HEADLINE.**  On the flat locus the SIGN-FREE MARGIN of a triple is
exactly the MINIMUM of the two gap determinants — the form's and its
complement's.

The sign-blind class was never merely blind to a sign.  It was computing the
worse of the two sides of the complementation involution, which is why its
ceiling is sharp and why it goes silent precisely where the involution's two
sides disagree. -/
theorem min_det_blockGapAt_one_sub_of_flat {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : formᵀ = form) (hflat : IsFlatDiagonal form) (weight : Fin size → ℝ)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick) :
    min (blockGapAt form weight pick).det (blockGapAt (1 - form) weight pick).det
      = signFreeMargin (blockGapAt form weight pick 0 0) (blockGapAt form weight pick 1 1)
          (blockGapAt form weight pick 2 2) (blockGapAt form weight pick 0 1)
          (blockGapAt form weight pick 0 2) (blockGapAt form weight pick 1 2) := by
  rw [det_blockGapAt_eq_tripleDetForm hsymm weight pick,
    det_blockGapAt_one_sub_of_flat hsymm hflat weight hinj]
  have hrewrite : tripleDetForm (blockGapAt form weight pick 0 0)
        (blockGapAt form weight pick 1 1) (blockGapAt form weight pick 2 2)
        (blockGapAt form weight pick 0 1) (blockGapAt form weight pick 0 2)
        (blockGapAt form weight pick 1 2)
      = evenTripleDetPart (blockGapAt form weight pick 0 0)
          (blockGapAt form weight pick 1 1) (blockGapAt form weight pick 2 2)
          (blockGapAt form weight pick 0 1) (blockGapAt form weight pick 0 2)
          (blockGapAt form weight pick 1 2)
        + 2 * (blockGapAt form weight pick 0 1 * blockGapAt form weight pick 0 2
            * blockGapAt form weight pick 1 2) := by
    rw [tripleDetForm, evenTripleDetPart]
  rw [hrewrite, min_add_sub_two_mul_abs, signFreeMargin, evenTripleDetPart]

/-! ## 6. The ceiling, with its mechanism

A certificate that reads only the gap diagonals and the SQUARED off-diagonals
cannot separate a flat form from its complement, because those two data sets
coincide there.  Soundness then forces BOTH gap blocks positive definite, which
is a two-sided sandwich on the block, and which forces the sign-free margin
positive.  That reproves the landed optimality theorem from geometry.
-/

/-- Both gap blocks positive definite forces the sign-free margin positive.
This is the ceiling on the sign-blind class, derived from the involution rather
than from a sign flip on an abstract tuple. -/
theorem signFreeMargin_pos_of_posDef_both {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : formᵀ = form) (hflat : IsFlatDiagonal form) (weight : Fin size → ℝ)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick)
    (hprimal : (blockGapAt form weight pick).PosDef)
    (hdual : (blockGapAt (1 - form) weight pick).PosDef) :
    0 < signFreeMargin (blockGapAt form weight pick 0 0) (blockGapAt form weight pick 1 1)
      (blockGapAt form weight pick 2 2) (blockGapAt form weight pick 0 1)
      (blockGapAt form weight pick 0 2) (blockGapAt form weight pick 1 2) := by
  rw [← min_det_blockGapAt_one_sub_of_flat hsymm hflat weight hinj]
  exact lt_min hprimal.det_pos hdual.det_pos

/-- **THE CEILING.**  On the flat locus, a non-positive sign-free margin forbids
BOTH gap blocks from being positive definite.  So no sound certificate reading
only the diagonal gaps and the squared pairings can fire at such a triple. -/
theorem not_posDef_both_of_signFreeMargin_nonpos {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : formᵀ = form) (hflat : IsFlatDiagonal form) (weight : Fin size → ℝ)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick)
    (hmargin : signFreeMargin (blockGapAt form weight pick 0 0)
      (blockGapAt form weight pick 1 1) (blockGapAt form weight pick 2 2)
      (blockGapAt form weight pick 0 1) (blockGapAt form weight pick 0 2)
      (blockGapAt form weight pick 1 2) ≤ 0) :
    ¬((blockGapAt form weight pick).PosDef ∧ (blockGapAt (1 - form) weight pick).PosDef) := by
  rintro ⟨hprimal, hdual⟩
  exact absurd (signFreeMargin_pos_of_posDef_both hsymm hflat weight hinj hprimal hdual)
    (not_lt.mpr hmargin)

/-- **THE SANDWICH.**  Both blocks positive definite is exactly a two-sided
strict bound on the principal block: above the weight diagonal and below the
co-weight diagonal. -/
theorem posDef_coWeight_sub_of_posDef_one_sub (form : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) {pick : Fin 3 → Fin size} (hinj : Function.Injective pick)
    (hdual : (blockGapAt (1 - form) weight pick).PosDef) :
    (Matrix.diagonal (fun slot => 1 - weight (pick slot)) - form.submatrix pick pick).PosDef := by
  have hrewrite : Matrix.diagonal (fun slot => 1 - weight (pick slot))
      - form.submatrix pick pick = blockGapAt (1 - form) weight pick := by
    ext left right
    simp only [blockGapAt, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
    rcases eq_or_ne left right with rfl | hne
    · rw [if_pos rfl, if_pos rfl, if_pos rfl]; ring
    · rw [if_neg hne, if_neg hne, if_neg (fun heq => hne (hinj heq))]; ring
  rw [hrewrite]; exact hdual

/-! ## 7. The graphic point of `K4`

The graphic point is flat — every leverage is one half — and rational.  Its
three-subsets carry at most one disjoint pair, so the gap's squared pairings
total at least one eighth, which drives the even part strictly negative at
uniform weight.  The sign-free margin is therefore negative at EVERY triple, so
no sound sign-blind certificate fires anywhere on the rigid stratum.
-/

/-- The graphic point is flat: every diagonal entry is one half. -/
theorem isFlatDiagonal_kfourEdgeProjection : IsFlatDiagonal kfourEdgeProjection := by
  intro edge
  rw [kfourEdgeProjection_apply, kfourGramInt_diag]
  norm_num

/-- **AT MOST ONE DISJOINT PAIR.**  Three distinct edges of `K4` carry at least
two meeting pairs, because a matching of two edges leaves only its own partner
disjoint from both.  Two hundred and sixteen decidable cases. -/
theorem kfourGramInt_two_le_sq_sum (firstEdge secondEdge thirdEdge : Fin 6)
    (hfs : firstEdge ≠ secondEdge) (hft : firstEdge ≠ thirdEdge) (hst : secondEdge ≠ thirdEdge) :
    2 ≤ (kfourGramInt firstEdge secondEdge) ^ 2 + (kfourGramInt firstEdge thirdEdge) ^ 2
      + (kfourGramInt secondEdge thirdEdge) ^ 2 := by
  fin_cases firstEdge <;> fin_cases secondEdge <;> fin_cases thirdEdge <;>
    revert hfs hft hst <;> decide

/-- Off the diagonal the graphic point's entry is an integer over four, so its
square is that integer's square over sixteen. -/
theorem sq_kfourEdgeProjection (leftEdge rightEdge : Fin 6) :
    kfourEdgeProjection leftEdge rightEdge ^ 2
      = ((kfourGramInt leftEdge rightEdge : ℝ)) ^ 2 / 16 := by
  rw [kfourEdgeProjection_apply]; ring

/-- The uniform weight on six labels. -/
noncomputable def sixthWeight : Fin 6 → ℝ := fun _ => 1 / 6

/-- At uniform weight the graphic point's gap block has diagonal one third. -/
theorem blockGapAt_kfour_diag (pick : Fin 3 → Fin 6) (slot : Fin 3) :
    blockGapAt kfourEdgeProjection sixthWeight pick slot slot = 1 / 3 := by
  rw [blockGapAt_apply_diag, kfourEdgeProjection_apply, kfourGramInt_diag, sixthWeight]
  norm_num

/-- **THE EVEN PART IS STRICTLY NEGATIVE AT EVERY TRIPLE OF THE GRAPHIC POINT.**
The three gap diagonals are one third, so the even part is `1/27` minus a third
of the squared-pairing total, and that total is at least one eighth. -/
theorem evenTripleDetPart_kfour_neg {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick) :
    evenTripleDetPart (blockGapAt kfourEdgeProjection sixthWeight pick 0 0)
        (blockGapAt kfourEdgeProjection sixthWeight pick 1 1)
        (blockGapAt kfourEdgeProjection sixthWeight pick 2 2)
        (blockGapAt kfourEdgeProjection sixthWeight pick 0 1)
        (blockGapAt kfourEdgeProjection sixthWeight pick 0 2)
        (blockGapAt kfourEdgeProjection sixthWeight pick 1 2)
      ≤ -(1 / 216) := by
  have hne01 : pick 0 ≠ pick 1 := fun heq => by simpa using hinj heq
  have hne02 : pick 0 ≠ pick 2 := fun heq => by simpa using hinj heq
  have hne12 : pick 1 ≠ pick 2 := fun heq => by simpa using hinj heq
  have hoff01 : blockGapAt kfourEdgeProjection sixthWeight pick 0 1
      = kfourEdgeProjection (pick 0) (pick 1) :=
    blockGapAt_apply_offDiag _ _ _ (by decide)
  have hoff02 : blockGapAt kfourEdgeProjection sixthWeight pick 0 2
      = kfourEdgeProjection (pick 0) (pick 2) :=
    blockGapAt_apply_offDiag _ _ _ (by decide)
  have hoff12 : blockGapAt kfourEdgeProjection sixthWeight pick 1 2
      = kfourEdgeProjection (pick 1) (pick 2) :=
    blockGapAt_apply_offDiag _ _ _ (by decide)
  have hint := kfourGramInt_two_le_sq_sum (pick 0) (pick 1) (pick 2) hne01 hne02 hne12
  have hreal : (2 : ℝ) ≤ ((kfourGramInt (pick 0) (pick 1) : ℝ)) ^ 2
      + ((kfourGramInt (pick 0) (pick 2) : ℝ)) ^ 2
      + ((kfourGramInt (pick 1) (pick 2) : ℝ)) ^ 2 := by
    exact_mod_cast hint
  have hsq : (1 : ℝ) / 8 ≤ blockGapAt kfourEdgeProjection sixthWeight pick 0 1 ^ 2
      + blockGapAt kfourEdgeProjection sixthWeight pick 0 2 ^ 2
      + blockGapAt kfourEdgeProjection sixthWeight pick 1 2 ^ 2 := by
    rw [hoff01, hoff02, hoff12, sq_kfourEdgeProjection, sq_kfourEdgeProjection,
      sq_kfourEdgeProjection]
    linarith
  rw [evenTripleDetPart, blockGapAt_kfour_diag, blockGapAt_kfour_diag, blockGapAt_kfour_diag]
  nlinarith [hsq]

/-- **THE SIGN-FREE MARGIN IS NEGATIVE AT EVERY TRIPLE OF THE GRAPHIC POINT.** -/
theorem signFreeMargin_kfour_neg {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick) :
    signFreeMargin (blockGapAt kfourEdgeProjection sixthWeight pick 0 0)
      (blockGapAt kfourEdgeProjection sixthWeight pick 1 1)
      (blockGapAt kfourEdgeProjection sixthWeight pick 2 2)
      (blockGapAt kfourEdgeProjection sixthWeight pick 0 1)
      (blockGapAt kfourEdgeProjection sixthWeight pick 0 2)
      (blockGapAt kfourEdgeProjection sixthWeight pick 1 2) ≤ -(1 / 216) := by
  have heven := evenTripleDetPart_kfour_neg hinj
  rw [signFreeMargin]
  rw [evenTripleDetPart] at heven
  have habs : 0 ≤ |blockGapAt kfourEdgeProjection sixthWeight pick 0 1
      * blockGapAt kfourEdgeProjection sixthWeight pick 0 2
      * blockGapAt kfourEdgeProjection sixthWeight pick 1 2| := abs_nonneg _
  linarith

/-- **THE RIGID STRATUM DEFEATS THE WHOLE SIGN-BLIND CLASS, AND HERE IS WHY.**
At the graphic point of `K4`, at uniform weight, no triple has both its gap
block and its complement's gap block positive definite.  A sound certificate
that reads only the diagonal gaps and the squared pairings cannot tell the two
apart, so it fires at no triple at all. -/
theorem not_posDef_both_kfourEdgeProjection {pick : Fin 3 → Fin 6}
    (hinj : Function.Injective pick) :
    ¬((blockGapAt kfourEdgeProjection sixthWeight pick).PosDef
      ∧ (blockGapAt (1 - kfourEdgeProjection) sixthWeight pick).PosDef) := by
  refine not_posDef_both_of_signFreeMargin_nonpos kfourEdgeProjection_symm
    isFlatDiagonal_kfourEdgeProjection sixthWeight hinj ?_
  have := signFreeMargin_kfour_neg hinj
  linarith

/-- The same statement read as a disjunction: at every triple of the graphic
point, one of the two gap determinants is not positive. -/
theorem det_nonpos_or_det_one_sub_nonpos_kfour {pick : Fin 3 → Fin 6}
    (hinj : Function.Injective pick) :
    (blockGapAt kfourEdgeProjection sixthWeight pick).det ≤ 0
      ∨ (blockGapAt (1 - kfourEdgeProjection) sixthWeight pick).det ≤ 0 := by
  by_contra hcon
  have hprimal : 0 < (blockGapAt kfourEdgeProjection sixthWeight pick).det := by
    by_contra hle; exact hcon (Or.inl (not_lt.mp hle))
  have hdual : 0 < (blockGapAt (1 - kfourEdgeProjection) sixthWeight pick).det := by
    by_contra hle; exact hcon (Or.inr (not_lt.mp hle))
  have hmin : 0 < min (blockGapAt kfourEdgeProjection sixthWeight pick).det
      (blockGapAt (1 - kfourEdgeProjection) sixthWeight pick).det := lt_min hprimal hdual
  rw [min_det_blockGapAt_one_sub_of_flat kfourEdgeProjection_symm
    isFlatDiagonal_kfourEdgeProjection sixthWeight hinj] at hmin
  have := signFreeMargin_kfour_neg hinj
  linarith

/-! ## 8. The design-level bridge

`Gtz.complementProjection` is definitionally `1 − projectionOfDesign`, so every
law above applies to a design's projection with no transport step.  A design is
FLAT when every leverage sits at one half, which at `(6,3)` is the equal-share
stratum the campaign has repeatedly found to be the crux.
-/

variable {m k : ℕ}

/-- The complement projection is the matrix complement, so the lane's laws
apply to designs directly. -/
theorem complementProjection_eq_one_sub (D : WeightedDesign m k) :
    complementProjection D = 1 - projectionOfDesign D := rfl

/-- A design is FLAT when every leverage sits at one half. -/
def IsFlatDesign (D : WeightedDesign m k) : Prop :=
  IsFlatDiagonal (projectionOfDesign D)

/-- At a flat design the complement's gap block is the design's gap block with
every off-diagonal negated. -/
theorem det_blockGapAt_complementProjection_of_flat {D : WeightedDesign m k}
    (hflat : IsFlatDesign D) {pick : Fin 3 → Fin m} (hinj : Function.Injective pick) :
    (blockGapAt (complementProjection D) D.weight pick).det
      = evenTripleDetPart (blockGapAt (projectionOfDesign D) D.weight pick 0 0)
          (blockGapAt (projectionOfDesign D) D.weight pick 1 1)
          (blockGapAt (projectionOfDesign D) D.weight pick 2 2)
          (blockGapAt (projectionOfDesign D) D.weight pick 0 1)
          (blockGapAt (projectionOfDesign D) D.weight pick 0 2)
          (blockGapAt (projectionOfDesign D) D.weight pick 1 2)
        - 2 * (blockGapAt (projectionOfDesign D) D.weight pick 0 1
            * blockGapAt (projectionOfDesign D) D.weight pick 0 2
            * blockGapAt (projectionOfDesign D) D.weight pick 1 2) := by
  rw [complementProjection_eq_one_sub]
  exact det_blockGapAt_one_sub_of_flat (projectionOfDesign_transpose D) hflat D.weight hinj

/-- **THE MINIMUM LAW AT A FLAT DESIGN.**  The sign-free margin of a triple is
the worse of the design's gap determinant and its complement's. -/
theorem min_det_blockGapAt_complementProjection_of_flat {D : WeightedDesign m k}
    (hflat : IsFlatDesign D) {pick : Fin 3 → Fin m} (hinj : Function.Injective pick) :
    min (blockGapAt (projectionOfDesign D) D.weight pick).det
        (blockGapAt (complementProjection D) D.weight pick).det
      = signFreeMargin (blockGapAt (projectionOfDesign D) D.weight pick 0 0)
          (blockGapAt (projectionOfDesign D) D.weight pick 1 1)
          (blockGapAt (projectionOfDesign D) D.weight pick 2 2)
          (blockGapAt (projectionOfDesign D) D.weight pick 0 1)
          (blockGapAt (projectionOfDesign D) D.weight pick 0 2)
          (blockGapAt (projectionOfDesign D) D.weight pick 1 2) := by
  rw [complementProjection_eq_one_sub]
  exact min_det_blockGapAt_one_sub_of_flat (projectionOfDesign_transpose D) hflat D.weight hinj

/-- At a flat design the sign-free margin is positive exactly when the design
and its complement BOTH have a positive gap determinant at that triple. -/
theorem signFreeMargin_pos_iff_det_pos_both {D : WeightedDesign m k}
    (hflat : IsFlatDesign D) {pick : Fin 3 → Fin m} (hinj : Function.Injective pick) :
    0 < signFreeMargin (blockGapAt (projectionOfDesign D) D.weight pick 0 0)
        (blockGapAt (projectionOfDesign D) D.weight pick 1 1)
        (blockGapAt (projectionOfDesign D) D.weight pick 2 2)
        (blockGapAt (projectionOfDesign D) D.weight pick 0 1)
        (blockGapAt (projectionOfDesign D) D.weight pick 0 2)
        (blockGapAt (projectionOfDesign D) D.weight pick 1 2)
      ↔ 0 < (blockGapAt (projectionOfDesign D) D.weight pick).det
        ∧ 0 < (blockGapAt (complementProjection D) D.weight pick).det := by
  rw [← min_det_blockGapAt_complementProjection_of_flat hflat hinj, lt_min_iff]

/-! ## 9. The bridge to the registry

The gap block of this module is DEFINITIONALLY the block the landed criterion
`Gtz.posDef_subsetSum_iff_posDef_projectionBlock` decides, so an ordered
selection whose gap block is positive definite is a dominating selection.  That
carries the whole lane to `Gtz.ProjectionBlockSelects` and hence to the five
on-path obligations, with no transport step and no new hypothesis.

The point of this section is that anything proved in the involution vocabulary
above lands on the registry rather than beside it.
-/

/-- An injective ordered selection of three labels names a three-element
subset. -/
theorem card_image_pick {pick : Fin 3 → Fin size} (hinj : Function.Injective pick) :
    (Finset.image pick Finset.univ).card = 3 := by
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **THE GAP BLOCK IS THE LANDED CRITERION'S BLOCK.**  Positive definiteness of
this module's gap block is exactly strict domination at the selected subset. -/
theorem posDef_blockGapAt_iff_subsetSum (D : WeightedDesign size 3)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick) :
    (blockGapAt (projectionOfDesign D) D.weight pick).PosDef
      ↔ (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef :=
  (posDef_subsetSum_iff_posDef_projectionBlock D pick hinj).symm

/-- An ordered selection with a positive definite gap block dominates. -/
theorem dominates_image_of_posDef_blockGapAt (D : WeightedDesign size 3)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick)
    (hposDef : (blockGapAt (projectionOfDesign D) D.weight pick).PosDef) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef :=
  (posDef_blockGapAt_iff_subsetSum D hinj).mp hposDef

/-- **THE LANE REACHES THE OBJECTIVE.**  If every primitive design at `(6,3)`
carries an ordered triple whose gap block is positive definite, then the
projection block statement holds. -/
theorem projectionBlockSelects_of_blockGapAt
    (hexists : ∀ D : WeightedDesign 6 3, IsPrimitiveDesign D →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        (blockGapAt (projectionOfDesign D) D.weight pick).PosDef) :
    ProjectionBlockSelects := by
  intro D hprimitive
  obtain ⟨pick, hinj, hposDef⟩ := hexists D hprimitive
  refine ⟨Finset.image pick Finset.univ, card_image_pick hinj, ?_⟩
  exact (posDef_subsetSum_iff_projectionBlockGap D _ (card_image_pick hinj)).mp
    (dominates_image_of_posDef_blockGapAt D hinj hposDef)

/-- **THE LANE REACHES ALL FIVE ON-PATH OBLIGATIONS.**  The involution
vocabulary of this module feeds the registry directly. -/
theorem allFiveOnPath_of_blockGapAt
    (hexists : ∀ D : WeightedDesign 6 3, IsPrimitiveDesign D →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        (blockGapAt (projectionOfDesign D) D.weight pick).PosDef) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  allFiveOnPath_of_projectionBlockSelects (projectionBlockSelects_of_blockGapAt hexists)

/-- The chart form of the consolidated statement follows too. -/
theorem consolidatedStrictTriple_of_blockGapAt
    (hexists : ∀ D : WeightedDesign 6 3, IsPrimitiveDesign D →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        (blockGapAt (projectionOfDesign D) D.weight pick).PosDef) :
    ConsolidatedStrictTriple :=
  consolidatedStrictTriple_of_projectionBlockSelects
    (projectionBlockSelects_of_blockGapAt hexists)

/-- **THE INVOLUTION-SYMMETRIC SUFFICIENT CONDITION REACHES THE REGISTRY.**  On
the flat stratum a triple whose gap block AND whose complement's gap block are
both positive definite certainly certifies the objective, since the first half
alone already does.  Stating it this way records what the sign-blind class
actually buys: it always pays for both sides of the involution, and only one
side is needed. -/
theorem projectionBlockSelects_of_blockGapAt_both
    (hexists : ∀ D : WeightedDesign 6 3, IsPrimitiveDesign D →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        (blockGapAt (projectionOfDesign D) D.weight pick).PosDef ∧
        (blockGapAt (complementProjection D) D.weight pick).PosDef) :
    ProjectionBlockSelects := by
  refine projectionBlockSelects_of_blockGapAt fun D hprimitive => ?_
  obtain ⟨pick, hinj, hprimal, _⟩ := hexists D hprimitive
  exact ⟨pick, hinj, hprimal⟩

end Gtz

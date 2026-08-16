import Gtz.Wave.ThirdLabelSelection
import Gtz.Quantitative.CauchyBinetValueFloor

/-!
# The complement cap on a triple, at general weight

The shifted form is `Z = P − diagonal w`, and its complement is

`1 − Z = (1 − P) + diagonal w`.

Both summands are positive semidefinite — the first is the landed complementary chart
`Gtz.posSemidef_one_sub_projectionOfDesign`, the second is a diagonal of strictly positive
weights.  So **every** three-slot block of `1 − Z` has a nonnegative determinant, at every
weight and at every rank.  That single fact caps the triple from the other side.

The landed `Gtz.posSemidef_one_sub_pickBlockGap` is the same contraction stated on a
selected block, and it carries an injectivity hypothesis on the pick.  The statement here
is the ambient one, so every block follows through `Matrix.PosSemidef.submatrix`, which
needs no injectivity: the cap below holds even when two of the three labels coincide.

## The cancellation

Write `e` for an excess and `r` for a projection pairing.  The two determinants are

`det Z_T = e₁e₂e₃ − e₁r₂₃² − e₂r₁₃² − e₃r₁₂² + 2 r₁₂r₁₃r₂₃`
`det (1−Z)_T = (1−e₁)(1−e₂)(1−e₃) − (1−e₁)r₂₃² − (1−e₂)r₁₃² − (1−e₃)r₁₂² − 2 r₁₂r₁₃r₂₃`

and the three-local monomial `r₁₂r₁₃r₂₃` **cancels exactly** in the sum:

`det Z_T + det (1−Z)_T = e₁e₂e₃ + (1−e₁)(1−e₂)(1−e₃) − (r₁₂² + r₁₃² + r₂₃²)`.

The right side is two-local: it reads three excesses and three squared pairings and no
signed product.  This is the same-triple, general-weight companion of the landed
complementation law `P_T + P_{T'} = 0`, which cancels the same monomial across
complementary triples on a hollow involution.

## What it buys

`Gtz.tripleCap` names the two-local right side.  Since the complement determinant is
nonnegative,

* `Gtz.det_tripleBlock_le_tripleCap` — the cap is an upper bound on the gap determinant at
  general weight,
* `Gtz.sum_sq_pairing_lt_tripleCap_of_det_pos` — a good triple has its three squared
  pairings strictly below the cap, so
* `Gtz.exists_small_pairing_of_det_pos` — a good triple always carries a pair whose squared
  pairing is below a third of the cap, and
* `Gtz.not_det_pos_of_tripleCap_le_sum_sq` — a triple whose squared pairings reach the cap
  is refuted outright, with no determinant computed.

A sibling proved the small-pair statement on the flat locus, where every diagonal is one
half and the weights are uniform.  Everything here is at general weight and at every rank,
and it needs neither flatness nor uniformity.

## Scope

These are a cap and a refuter, not a producer: the corpus records that an upper bound on
the margin can never force a positive margin.  They prune the search and they free the
second Sylvester minor, which is what the pivot floor of `Gtz.Wave.ThirdLabelSelection`
does not supply.
-/

namespace Gtz

open Finset

variable {size rank : ℕ}

/-! ### 1. The complement of the shifted form is positive semidefinite -/

/-- The shifted form's complement splits as the complementary chart plus the weights. -/
theorem one_sub_diagonalShiftForm_eq (design : WeightedDesign size rank) :
    (1 : Matrix (Fin size) (Fin size) ℝ) - diagonalShiftForm design
      = ((1 : Matrix (Fin size) (Fin size) ℝ) - projectionOfDesign design)
        + Matrix.diagonal design.weight := by
  rw [diagonalShiftForm]
  abel

/-- **THE COMPLEMENT IS POSITIVE SEMIDEFINITE, AT GENERAL WEIGHT.**  A projection's
complement is positive semidefinite and so is a diagonal of positive weights. -/
theorem posSemidef_one_sub_diagonalShiftForm (design : WeightedDesign size rank) :
    ((1 : Matrix (Fin size) (Fin size) ℝ) - diagonalShiftForm design).PosSemidef := by
  rw [one_sub_diagonalShiftForm_eq design]
  refine Matrix.PosSemidef.add (posSemidef_one_sub_projectionOfDesign design) ?_
  exact Matrix.posSemidef_diagonal_iff.mpr fun label => (design.weight_pos label).le

/-- **EVERY COMPLEMENT BLOCK HAS A NONNEGATIVE DETERMINANT.**  No distinctness, no rank and
no weight hypothesis: a principal submatrix of a positive semidefinite form is positive
semidefinite. -/
theorem det_tripleBlock_one_sub_nonneg (design : WeightedDesign size rank)
    (first second third : Fin size) :
    0 ≤ (tripleBlock ((1 : Matrix (Fin size) (Fin size) ℝ) - diagonalShiftForm design)
      first second third).det :=
  ((posSemidef_one_sub_diagonalShiftForm design).submatrix _).det_nonneg

/-! ### 2. The entries of the complement, and the cancellation -/

/-- On the diagonal the complement reads one less the excess. -/
theorem one_sub_diagonalShiftForm_diag (design : WeightedDesign size rank) (label : Fin size) :
    ((1 : Matrix (Fin size) (Fin size) ℝ) - diagonalShiftForm design) label label
      = 1 - diagonalShiftForm design label label := by
  simp [Matrix.sub_apply, Matrix.one_apply_eq]

/-- Off the diagonal the complement reads the negated projection pairing. -/
theorem one_sub_diagonalShiftForm_offDiag (design : WeightedDesign size rank)
    {first second : Fin size} (hne : first ≠ second) :
    ((1 : Matrix (Fin size) (Fin size) ℝ) - diagonalShiftForm design) first second
      = -projectionOfDesign design first second := by
  rw [Matrix.sub_apply, Matrix.one_apply_ne hne, diagonalShiftForm_offDiag design hne]
  ring

/-- The complement of the shifted form is symmetric. -/
theorem one_sub_diagonalShiftForm_transpose (design : WeightedDesign size rank) :
    Matrix.transpose ((1 : Matrix (Fin size) (Fin size) ℝ) - diagonalShiftForm design)
      = (1 : Matrix (Fin size) (Fin size) ℝ) - diagonalShiftForm design := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, diagonalShiftForm_transpose]

/-- **THE TWO-LOCAL CAP.**  Three excesses and three squared pairings, with no signed
product of the three pairings anywhere. -/
noncomputable def tripleCap (design : WeightedDesign size rank)
    (first second third : Fin size) : ℝ :=
  diagonalShiftForm design first first * diagonalShiftForm design second second
      * diagonalShiftForm design third third
    + (1 - diagonalShiftForm design first first)
        * (1 - diagonalShiftForm design second second)
        * (1 - diagonalShiftForm design third third)
    - (projectionOfDesign design first second ^ 2
        + projectionOfDesign design first third ^ 2
        + projectionOfDesign design second third ^ 2)

/-- **THE CANCELLATION.**  The gap determinant and its complement sum to the two-local cap:
the three-local monomial `r₁₂ r₁₃ r₂₃` occurs with opposite signs and cancels exactly. -/
theorem det_tripleBlock_add_complement_eq_tripleCap (design : WeightedDesign size rank)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    (tripleBlock (diagonalShiftForm design) first second third).det
        + (tripleBlock ((1 : Matrix (Fin size) (Fin size) ℝ) - diagonalShiftForm design)
            first second third).det
      = tripleCap design first second third := by
  rw [det_tripleBlock (diagonalShiftForm design) (diagonalShiftForm_transpose design),
    det_tripleBlock _ (one_sub_diagonalShiftForm_transpose design),
    one_sub_diagonalShiftForm_diag, one_sub_diagonalShiftForm_diag,
    one_sub_diagonalShiftForm_diag,
    one_sub_diagonalShiftForm_offDiag design hfirstSecond,
    one_sub_diagonalShiftForm_offDiag design hfirstThird,
    one_sub_diagonalShiftForm_offDiag design hsecondThird,
    diagonalShiftForm_offDiag design hfirstSecond,
    diagonalShiftForm_offDiag design hfirstThird,
    diagonalShiftForm_offDiag design hsecondThird,
    tripleCap]
  ring

/-! ### 3. The cap, the small pair and the refuter -/

/-- **THE CAP BOUNDS THE GAP DETERMINANT.**  At general weight and at every rank. -/
theorem det_tripleBlock_le_tripleCap (design : WeightedDesign size rank)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    (tripleBlock (diagonalShiftForm design) first second third).det
      ≤ tripleCap design first second third := by
  have hsum := det_tripleBlock_add_complement_eq_tripleCap design hfirstSecond hfirstThird
    hsecondThird
  have hnonneg := det_tripleBlock_one_sub_nonneg design first second third
  linarith

/-- **A GOOD TRIPLE HAS ITS SQUARED PAIRINGS STRICTLY UNDER THE EXCESS PRODUCTS.**  The
cap, rearranged: a positive gap determinant forces the three squared pairings below the
sum of the two excess products. -/
theorem sum_sq_pairing_lt_of_det_pos (design : WeightedDesign size rank)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hdet : 0 < (tripleBlock (diagonalShiftForm design) first second third).det) :
    projectionOfDesign design first second ^ 2
        + projectionOfDesign design first third ^ 2
        + projectionOfDesign design second third ^ 2
      < diagonalShiftForm design first first * diagonalShiftForm design second second
          * diagonalShiftForm design third third
        + (1 - diagonalShiftForm design first first)
            * (1 - diagonalShiftForm design second second)
            * (1 - diagonalShiftForm design third third) := by
  have hle := det_tripleBlock_le_tripleCap design hfirstSecond hfirstThird hsecondThird
  rw [tripleCap] at hle
  linarith

/-- **EVERY GOOD TRIPLE CARRIES A SMALL PAIR, AT GENERAL WEIGHT.**  Three squares whose
total falls under a bound cannot all reach a third of it.  A sibling proved this on the
flat locus only, where every diagonal is one half and the weights are uniform. -/
theorem exists_small_pairing_of_det_pos (design : WeightedDesign size rank)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hdet : 0 < (tripleBlock (diagonalShiftForm design) first second third).det) :
    projectionOfDesign design first second ^ 2
          < (diagonalShiftForm design first first * diagonalShiftForm design second second
              * diagonalShiftForm design third third
            + (1 - diagonalShiftForm design first first)
                * (1 - diagonalShiftForm design second second)
                * (1 - diagonalShiftForm design third third)) / 3
      ∨ projectionOfDesign design first third ^ 2
          < (diagonalShiftForm design first first * diagonalShiftForm design second second
              * diagonalShiftForm design third third
            + (1 - diagonalShiftForm design first first)
                * (1 - diagonalShiftForm design second second)
                * (1 - diagonalShiftForm design third third)) / 3
      ∨ projectionOfDesign design second third ^ 2
          < (diagonalShiftForm design first first * diagonalShiftForm design second second
              * diagonalShiftForm design third third
            + (1 - diagonalShiftForm design first first)
                * (1 - diagonalShiftForm design second second)
                * (1 - diagonalShiftForm design third third)) / 3 := by
  by_contra hall
  push Not at hall
  obtain ⟨hone, htwo, hthree⟩ := hall
  have hsum := sum_sq_pairing_lt_of_det_pos design hfirstSecond hfirstThird hsecondThird hdet
  linarith

/-- **THE REFUTER.**  A triple whose squared pairings reach the cap cannot be good, and no
determinant is computed to see it. -/
theorem not_det_pos_of_tripleCap_le_sum_sq (design : WeightedDesign size rank)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hreach : diagonalShiftForm design first first * diagonalShiftForm design second second
          * diagonalShiftForm design third third
        + (1 - diagonalShiftForm design first first)
            * (1 - diagonalShiftForm design second second)
            * (1 - diagonalShiftForm design third third)
      ≤ projectionOfDesign design first second ^ 2
        + projectionOfDesign design first third ^ 2
        + projectionOfDesign design second third ^ 2) :
    ¬ 0 < (tripleBlock (diagonalShiftForm design) first second third).det := by
  intro hdet
  have hsum := sum_sq_pairing_lt_of_det_pos design hfirstSecond hfirstThird hsecondThird hdet
  linarith

/-! ### 4. Against the pivot floor

`Gtz.exists_pivot_partner_ge_eleven_oneEightyth` supplies a pivot of excess at least a
third and a partner whose shifted pair minor is at least `11/180`, at general weight.  The
cap prices the third label of that pair. -/

/-- **THE PIVOT PAIR IS PRICED BY THE CAP.**  At the free pivot and partner, a good third
label has all three squared pairings under the cap, so the search for the third inequality
may skip every label whose pairing with the pivot already reaches it. -/
theorem sum_sq_pairing_lt_of_pivot_of_det_pos (design : WeightedDesign 6 3)
    {label partner third : Fin 6} (hpartner : partner ≠ label) (hthirdLabel : third ≠ label)
    (hthirdPartner : third ≠ partner)
    (hdet : 0 < (tripleBlock (diagonalShiftForm design) label partner third).det) :
    projectionOfDesign design label partner ^ 2
        + projectionOfDesign design label third ^ 2
        + projectionOfDesign design partner third ^ 2
      < diagonalShiftForm design label label * diagonalShiftForm design partner partner
          * diagonalShiftForm design third third
        + (1 - diagonalShiftForm design label label)
            * (1 - diagonalShiftForm design partner partner)
            * (1 - diagonalShiftForm design third third) :=
  sum_sq_pairing_lt_of_det_pos design hpartner.symm hthirdLabel.symm hthirdPartner.symm hdet

/-- **A SINGLE PAIRING CAN REFUTE A WHOLE TRIPLE.**  If the pivot's own squared pairing with
one label already reaches the cap, that label cannot complete a good triple with the
partner, whatever the remaining entries do. -/
theorem not_det_pos_of_pivot_pairing_reaches (design : WeightedDesign 6 3)
    {label partner third : Fin 6} (hpartner : partner ≠ label) (hthirdLabel : third ≠ label)
    (hthirdPartner : third ≠ partner)
    (hreach : diagonalShiftForm design label label * diagonalShiftForm design partner partner
          * diagonalShiftForm design third third
        + (1 - diagonalShiftForm design label label)
            * (1 - diagonalShiftForm design partner partner)
            * (1 - diagonalShiftForm design third third)
      ≤ projectionOfDesign design label third ^ 2) :
    ¬ 0 < (tripleBlock (diagonalShiftForm design) label partner third).det := by
  refine not_det_pos_of_tripleCap_le_sum_sq design hpartner.symm hthirdLabel.symm
    hthirdPartner.symm ?_
  nlinarith [sq_nonneg (projectionOfDesign design label partner),
    sq_nonneg (projectionOfDesign design partner third)]

end Gtz

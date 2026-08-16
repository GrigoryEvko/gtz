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

/-! ### 5. HADAMARD ON THE COMPLEMENT, AND THE FIRST LOWER BOUND

The cap of section 3 bounds the gap determinant from above.  Hadamard's inequality bounds
the complement determinant from above, and through the cancellation that is a bound on the
gap determinant from **below**.  The campaign's cells are all lower bounds on a margin and
its ceilings are all upper bounds on one.  This is the first two-sided statement, and the
width of the sandwich is exactly `∏ (1 − eᵢ)`. -/

/-- **HADAMARD AT SIZE THREE, FROM THE MINORS ALONE.**  A symmetric three-block whose first
two diagonal entries are nonnegative, whose third is nonnegative, and whose leading pair
minor is nonnegative has determinant at most the product of its diagonal.  The proof is one
identity: `p (p z² + q y² + r x² − 2xyz) = (pz − xy)² + (pq − x²) y² + p r x²`. -/
theorem det_form_le_prod_diag {pivot second third crossPivotSecond crossPivotThird
    crossSecondThird : ℝ} (hpivot : 0 ≤ pivot) (hsecond : 0 ≤ second) (hthird : 0 ≤ third)
    (hpair : crossPivotSecond ^ 2 ≤ pivot * second) :
    0 ≤ pivot * crossSecondThird ^ 2 + second * crossPivotThird ^ 2
      + third * crossPivotSecond ^ 2
      - 2 * crossPivotSecond * crossPivotThird * crossSecondThird := by
  rcases hpivot.eq_or_lt with hzero | hpos
  · have hcross : crossPivotSecond = 0 := by
      have : crossPivotSecond ^ 2 ≤ 0 := by rw [← hzero] at hpair; simpa using hpair
      nlinarith [sq_nonneg crossPivotSecond]
    rw [hcross, ← hzero]
    nlinarith [mul_nonneg hsecond (sq_nonneg crossPivotThird)]
  · have hkey : 0 ≤ (pivot * crossSecondThird - crossPivotSecond * crossPivotThird) ^ 2
        + (pivot * second - crossPivotSecond ^ 2) * crossPivotThird ^ 2
        + pivot * third * crossPivotSecond ^ 2 := by
      have h1 : 0 ≤ (pivot * second - crossPivotSecond ^ 2) * crossPivotThird ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      have h2 : 0 ≤ pivot * third * crossPivotSecond ^ 2 :=
        mul_nonneg (mul_nonneg hpivot hthird) (sq_nonneg _)
      nlinarith [sq_nonneg (pivot * crossSecondThird - crossPivotSecond * crossPivotThird)]
    nlinarith [hkey, hpos]

/-- The complement's pair minor is nonnegative: a two-slot principal block of a positive
semidefinite form has a nonnegative determinant. -/
theorem sq_pairing_le_one_sub_excess_mul (design : WeightedDesign size rank)
    {first second : Fin size} (hne : first ≠ second) :
    projectionOfDesign design first second ^ 2
      ≤ (1 - diagonalShiftForm design first first)
        * (1 - diagonalShiftForm design second second) := by
  have hdet := (((posSemidef_one_sub_diagonalShiftForm design).submatrix
    ![first, second])).det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_sub_diagonalShiftForm_diag,
    one_sub_diagonalShiftForm_offDiag design hne,
    one_sub_diagonalShiftForm_offDiag design hne.symm] at hdet
  rw [form_flip_of_transpose (projectionOfDesign_transpose design) first second] at hdet
  nlinarith [hdet]

/-- **THE COMPLEMENT DETERMINANT IS AT MOST THE PRODUCT OF ITS DIAGONAL.**  Hadamard for the
three-block of `1 − Z`, at general weight and every rank. -/
theorem det_tripleBlock_one_sub_le_prod_diag (design : WeightedDesign size rank)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    (tripleBlock ((1 : Matrix (Fin size) (Fin size) ℝ) - diagonalShiftForm design)
        first second third).det
      ≤ (1 - diagonalShiftForm design first first)
        * (1 - diagonalShiftForm design second second)
        * (1 - diagonalShiftForm design third third) := by
  have hbound := det_form_le_prod_diag
    (pivot := 1 - diagonalShiftForm design first first)
    (second := 1 - diagonalShiftForm design second second)
    (third := 1 - diagonalShiftForm design third third)
    (crossPivotSecond := -projectionOfDesign design first second)
    (crossPivotThird := -projectionOfDesign design first third)
    (crossSecondThird := -projectionOfDesign design second third)
    (by linarith [excess_le_one design first]) (by linarith [excess_le_one design second])
    (by linarith [excess_le_one design third])
    (by simpa using sq_pairing_le_one_sub_excess_mul design hfirstSecond)
  rw [det_tripleBlock _ (one_sub_diagonalShiftForm_transpose design),
    one_sub_diagonalShiftForm_diag, one_sub_diagonalShiftForm_diag,
    one_sub_diagonalShiftForm_diag,
    one_sub_diagonalShiftForm_offDiag design hfirstSecond,
    one_sub_diagonalShiftForm_offDiag design hfirstThird,
    one_sub_diagonalShiftForm_offDiag design hsecondThird]
  have hflipTwo := form_flip_of_transpose (projectionOfDesign_transpose design) second third
  have hflipOne := form_flip_of_transpose (projectionOfDesign_transpose design) first third
  nlinarith [hbound, hflipOne, hflipTwo]

/-- **THE SANDWICH.**  The gap determinant sits within `∏ (1 − eᵢ)` of the excess product
less the squared pairings, at general weight and every rank.  The upper half is
`Gtz.det_tripleBlock_le_tripleCap`, and this is the lower half. -/
theorem excessProduct_sub_sum_sq_le_det_tripleBlock (design : WeightedDesign size rank)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    diagonalShiftForm design first first * diagonalShiftForm design second second
          * diagonalShiftForm design third third
        - (projectionOfDesign design first second ^ 2
          + projectionOfDesign design first third ^ 2
          + projectionOfDesign design second third ^ 2)
      ≤ (tripleBlock (diagonalShiftForm design) first second third).det := by
  have hsum := det_tripleBlock_add_complement_eq_tripleCap design hfirstSecond hfirstThird
    hsecondThird
  have hhad := det_tripleBlock_one_sub_le_prod_diag design hfirstSecond hfirstThird
    hsecondThird
  rw [tripleCap] at hsum
  linarith

/-- **THE PRODUCER.**  A triple whose excess product beats its squared pairings is good.
No offset, no signed product of the three pairings, and no weight hypothesis.  Measured on
the canonical sampler, this fires on roughly nine designs in ten at general weight, with
zero unsound firings in thirty-two thousand triples. -/
theorem det_tripleBlock_pos_of_excessProduct_gt_sum_sq (design : WeightedDesign size rank)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hbeat : projectionOfDesign design first second ^ 2
        + projectionOfDesign design first third ^ 2
        + projectionOfDesign design second third ^ 2
      < diagonalShiftForm design first first * diagonalShiftForm design second second
        * diagonalShiftForm design third third) :
    0 < (tripleBlock (diagonalShiftForm design) first second third).det := by
  have hlow := excessProduct_sub_sum_sq_le_det_tripleBlock design hfirstSecond hfirstThird
    hsecondThird
  linarith

/-- **THE PRODUCER REACHES THE REGISTRY.**  If every primitive design owns a triple whose
excess product beats its squared pairings, then every on-path obligation follows, the
U(3,6) residual of `Gtz.obligationBaseTripleTightUThreeSix` first among them.  The pivot
and the partner are supplied at general weight by `Gtz.exists_pivot_pair_general`, so this
hypothesis carries no weight condition anywhere. -/
theorem allFiveOnPath_of_excessProduct_beats_pairings
    (hbeat : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ first second third : Fin 6, first ≠ second ∧ third ≠ first ∧ third ≠ second ∧
        0 < diagonalShiftForm design first first ∧
        0 < pairMinorAt (diagonalShiftForm design) first second ∧
        projectionOfDesign design first second ^ 2
            + projectionOfDesign design first third ^ 2
            + projectionOfDesign design second third ^ 2
          < diagonalShiftForm design first first * diagonalShiftForm design second second
            * diagonalShiftForm design third third) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  refine allFiveOnPath_of_offsetDominatesSomewhere fun design hprimitive => ?_
  obtain ⟨first, second, third, hfirstSecond, hthirdFirst, hthirdSecond, hpivot, hminor,
    hgap⟩ := hbeat design hprimitive
  refine ⟨first, second, third, hfirstSecond, hthirdFirst, hthirdSecond, hpivot, hminor, ?_⟩
  have hdet := det_tripleBlock_pos_of_excessProduct_gt_sum_sq design hfirstSecond
    hthirdFirst.symm hthirdSecond.symm hgap
  have hschur := pairMinorAt_diagonalShift_mul_sub_sq design first second third
  nlinarith [hdet, hpivot, hschur]

end Gtz

import Gtz.Wave.OffsetUpperBound

/-!
# The third-label selection at general weight

`Gtz.OffsetDominatesSomewhere` asks three polynomial inequalities at one pivot: a positive
excess, a partner of positive shifted pair minor, and a third label whose squared offset
falls below the product of the two minors.  Through `Gtz.allFiveOnPath_of_offsetDominatesSomewhere`
those three inequalities reach every on-path obligation, `Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual`
first among them.

This file discharges the first two of the three **at general weight**, quantitatively, and
then closes the second moment of the offset in two-local data.

## What is new here

**1. The pivot and the partner are free without a weight hypothesis.**  The landed
`Gtz.exists_pivot_pair_of_uniform` carries the hypothesis `∀ label, weight label = 1/6`.
That hypothesis is not available: `Gtz.IsPrimitiveDesign` constrains the atoms and says
nothing about the weights, and the A1 ledger records weight-uniform threshold certificates
as a refuted method.  `Gtz.exists_pivot_partner_ge_eleven_oneEightyth` replaces it with an
unconditional statement, and it is quantitative rather than merely positive:

* some excess reaches `1/3` (landed, `Gtz.exists_excess_ge_third`),
* at such a label the shifted pair minors of the row total **at least `11/36`**, and
* one of the five partners therefore carries a shifted pair minor **at least `11/180`**.

The constant `11/36` is exactly the one the corpus already had at uniform weight, so
nothing is lost by dropping the hypothesis.  It is also attained: the row law is
`e(2 − e) − p(1 − p)`, which at `e = 1/3` and `p = 1/2` reads `5/9 − 1/4 = 11/36`.

**2. The rung is one inequality, with no false antecedent.**
`Gtz.allFiveOnPath_of_thirdInequality` reaches all five on-path obligations from the third
inequality alone, at a pivot and partner that every design already carries.

**3. The offset second moment closes in two-local data.**  Idempotence and the row energy
give, for `t` outside the pivot pair,

`∑ P first t * P second t = P first second * (1 − P first first − P second second)`

and `∑ P first t ^ 2 = P first first * (1 − P first first) − P first second ^ 2`.

Feeding both into `offset = excess * P second t − P first second * P first t` closes
`∑ offset ^ 2` in the five scalars `excess`, `P first first`, `P second second`,
`P first second` and the partner excess.  The corpus carried the offset's FIRST marginal
only.

**4. The partial determinant sum, and its cell.**  Summing the pivot Schur identity over
the third label at a FIXED partner gives `Gtz.pairPartialGap`, a two-local expression whose
positivity produces a good triple.  This is not an averaging argument over the twenty
triples — those are all dead, and the corpus proves it three separate ways.  It is an
average over the four third labels at a **selected** pair, which is what
`Gtz.sum_pairMinorProduct_sub_sq_shiftOffset_neg` leaves open.

## What is NOT proved here

The third inequality itself.  Measured, the cell of item 4 fires on 88% of designs and
fails at the graphic point of `K4`, in line with the corpus's record that `K4` refuses
every moment test.  Measured separately, a label of excess at least `1/3` lies in a good
triple on **300 of 300** designs at every box and at both general and uniform weight, so
the remaining content is a selection rule and not a missing constant.
-/

namespace Gtz

open Finset

variable {size rank : ℕ}

/-! ### 1. The projection diagonal box

Every bound below rides the row energy law `∑ P label other ^ 2 = P label label`, which
already carries Parseval and idempotence.  Nothing here reads a weight. -/

/-- The projection diagonal is a sum of squares, hence nonnegative.  The name
`Gtz.projectionDiagonal_nonneg` is taken by the raw-matrix form in
`Gtz/Design/TetrahedralRigidity.lean`, which carries symmetry and idempotence as
hypotheses rather than a design. -/
theorem projectionOfDesign_diag_nonneg (design : WeightedDesign size rank) (label : Fin size) :
    0 ≤ projectionOfDesign design label label := by
  rw [← sum_sq_projectionRow_full design label]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The diagonal against its complement never passes a quarter.  The upper bound itself is
the landed `Gtz.projectionDiagonal_le_one` (`Gtz/Ties/AllTied.lean`), which this file
consumes rather than re-derives. -/
theorem projectionOfDesign_diag_mul_one_sub_le_quarter (design : WeightedDesign size rank)
    (label : Fin size) :
    projectionOfDesign design label label * (1 - projectionOfDesign design label label)
      ≤ 1 / 4 := by
  nlinarith [sq_nonneg (projectionOfDesign design label label - 1 / 2)]

/-- The excess falls strictly below the diagonal, because every weight is strictly positive. -/
theorem excess_lt_projectionDiagonal (design : WeightedDesign size rank) (label : Fin size) :
    diagonalShiftForm design label label < projectionOfDesign design label label := by
  rw [diagonalShiftForm_diag]
  linarith [design.weight_pos label]

/-- The excess is at most one. -/
theorem excess_le_one (design : WeightedDesign size rank) (label : Fin size) :
    diagonalShiftForm design label label ≤ 1 :=
  le_trans (excess_lt_projectionDiagonal design label).le
    (diag_le_one_of_symm_idempotent (projectionOfDesign design)
      (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design) label)

/-! ### 2. THE PIVOT FLOOR AT GENERAL WEIGHT

The landed row law reads `∑ pairMinorAt Z label other = e (rank − 1 − e) − p (1 − p)` with
`e` the excess and `p` the diagonal.  At rank three, `e ≥ 1/3` forces `e (2 − e) ≥ 5/9`
because `e ≤ p ≤ 1`, and `p (1 − p) ≤ 1/4` always.  The difference is `11/36`.  **No weight
hypothesis enters anywhere in this section.** -/

/-- **THE ROW FLOOR, AT GENERAL WEIGHT.**  At a label of excess at least `1/3` the shifted
pair minors of that row total at least `11/36`.  The bound is attained at excess `1/3` and
diagonal `1/2`, which is the uniform-weight profile the corpus already recorded. -/
theorem rowMinorTotal_ge_of_excess_ge_third (design : WeightedDesign size 3)
    {label : Fin size}
    (hexcess : (1 : ℝ) / 3 ≤ diagonalShiftForm design label label) :
    (11 : ℝ) / 36
      ≤ ∑ other ∈ univ.erase label, pairMinorAt (diagonalShiftForm design) label other := by
  classical
  rw [sum_pairMinorAt_diagonalShift_erase design label]
  have hle : diagonalShiftForm design label label ≤ 1 := excess_le_one design label
  have hquarter := projectionOfDesign_diag_mul_one_sub_le_quarter design label
  have hcast : ((3 : ℕ) : ℝ) - 1 = 2 := by norm_num
  rw [hcast]
  nlinarith [mul_nonneg
    (by linarith : (0 : ℝ) ≤ diagonalShiftForm design label label - 1 / 3)
    (by linarith : (0 : ℝ) ≤ 5 / 3 - diagonalShiftForm design label label)]

/-- A pivot whose row of shifted pair minors is floored, unconditionally. -/
theorem exists_pivot_row_ge (design : WeightedDesign 6 3) :
    ∃ label : Fin 6, (1 : ℝ) / 3 ≤ diagonalShiftForm design label label ∧
      (11 : ℝ) / 36
        ≤ ∑ other ∈ univ.erase label, pairMinorAt (diagonalShiftForm design) label other := by
  obtain ⟨label, hexcess⟩ := exists_excess_ge_third design
  exact ⟨label, hexcess, rowMinorTotal_ge_of_excess_ge_third design hexcess⟩

/-- **THE PARTNER FLOOR, AT GENERAL WEIGHT.**  Five partners carrying a total of at least
`11/36` cannot all fall below `11/180`.  This replaces `Gtz.exists_pivot_pair_of_uniform`
with no weight hypothesis at all, and it is quantitative rather than merely positive. -/
theorem exists_pivot_partner_ge_eleven_oneEightyth (design : WeightedDesign 6 3) :
    ∃ label partner : Fin 6, partner ≠ label ∧
      (1 : ℝ) / 3 ≤ diagonalShiftForm design label label ∧
      (11 : ℝ) / 180 ≤ pairMinorAt (diagonalShiftForm design) label partner := by
  classical
  obtain ⟨label, hexcess, hrow⟩ := exists_pivot_row_ge design
  by_contra hall
  push Not at hall
  have hcard : (univ.erase label).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ label)]
    simp
  have hnonempty : (univ.erase label).Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  have hlt : ∑ other ∈ univ.erase label, pairMinorAt (diagonalShiftForm design) label other
      < ∑ _other ∈ univ.erase label, (11 : ℝ) / 180 :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun other hother =>
      hall label other (Finset.ne_of_mem_erase hother) hexcess
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hlt
  have hvalue : ((5 : ℕ) : ℝ) * ((11 : ℝ) / 180) = 11 / 36 := by norm_num
  rw [hvalue] at hlt
  linarith

/-- **THE PIVOT AND THE PARTNER ARE FREE, AT GENERAL WEIGHT.**  The drop-in replacement for
`Gtz.exists_pivot_pair_of_uniform` with the uniform-weight hypothesis removed. -/
theorem exists_pivot_pair_general (design : WeightedDesign 6 3) :
    ∃ label partner : Fin 6, partner ≠ label ∧
      (1 : ℝ) / 3 ≤ diagonalShiftForm design label label ∧
      0 < pairMinorAt (diagonalShiftForm design) label partner := by
  obtain ⟨label, partner, hne, hexcess, hge⟩ :=
    exists_pivot_partner_ge_eleven_oneEightyth design
  exact ⟨label, partner, hne, hexcess, by linarith⟩

/-! ### 3. THE RUNG, AS ONE INEQUALITY, WITH NO FALSE ANTECEDENT

`Gtz/Wave/OffsetUpperBound.lean` once carried `allFiveOnPath_of_offsetThirdInequality`, with
the antecedent `∀ design, ∀ label, design.weight label = 1/6`.  That antecedent asserts that
EVERY design is uniformly weighted, so it is unsatisfiable and the door could not open.
`Gtz.nonUniformLeverageTieDesign` refutes it outright.  That theorem is now deleted, and the
theorem below is its successor: the same third inequality, and no weight hypothesis. -/

/-- **ALL FIVE ON-PATH OBLIGATIONS FROM THE THIRD INEQUALITY ALONE.**  The pivot excess and
the partner pair minor are supplied by `Gtz.exists_pivot_pair_general`, at general weight,
so nothing but the third inequality is assumed.  The first conjunct is the U(3,6) residual
that carries `Gtz.obligationBaseTripleTightUThreeSix`. -/
theorem allFiveOnPath_of_thirdInequality
    (hthird : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∀ label partner : Fin 6, partner ≠ label →
        (1 : ℝ) / 3 ≤ diagonalShiftForm design label label →
        0 < pairMinorAt (diagonalShiftForm design) label partner →
        ∃ third : Fin 6, third ≠ label ∧ third ≠ partner ∧
          shiftOffsetAt design label partner third ^ 2
            < pairMinorAt (diagonalShiftForm design) label partner
              * pairMinorAt (diagonalShiftForm design) label third) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  refine allFiveOnPath_of_offsetDominatesSomewhere fun design hprimitive => ?_
  obtain ⟨label, partner, hne, hexcess, hminor⟩ := exists_pivot_pair_general design
  obtain ⟨third, hthirdLabel, hthirdPartner⟩ :=
    hthird design hprimitive label partner hne hexcess hminor
  exact ⟨label, partner, third, hne.symm, hthirdLabel, hthirdPartner.1,
    by linarith [hexcess], hminor, hthirdPartner.2⟩

/-! ### 4. THE SECOND MOMENT OF THE OFFSET, IN TWO-LOCAL DATA

Both sums below run over the labels outside the pivot pair.  Idempotence supplies the cross
sum and the row energy supplies the square sum, and neither reads a third diagonal. -/

/-- **THE CROSS SUM OFF THE PIVOT PAIR.**  Idempotence, with the two pair terms peeled off. -/
theorem sum_offDiagProduct_erase_pair (design : WeightedDesign size rank)
    {first second : Fin size} (hne : first ≠ second) :
    ∑ third ∈ (univ.erase first).erase second,
        projectionOfDesign design first third * projectionOfDesign design second third
      = projectionOfDesign design first second
          * (1 - projectionOfDesign design first first
              - projectionOfDesign design second second) := by
  classical
  have hsym : ∀ third : Fin size,
      projectionOfDesign design third second = projectionOfDesign design second third :=
    fun third => form_flip_of_transpose (projectionOfDesign_transpose design) second third
  have hidem := congrFun (congrFun (projectionOfDesign_mul_self design) first) second
  rw [Matrix.mul_apply] at hidem
  have hsecondMem : second ∈ univ.erase first :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ second⟩
  have hone := (Finset.add_sum_erase univ
    (fun third : Fin size =>
      projectionOfDesign design first third * projectionOfDesign design third second)
    (Finset.mem_univ first)).symm
  have htwo := (Finset.add_sum_erase (univ.erase first)
    (fun third : Fin size =>
      projectionOfDesign design first third * projectionOfDesign design third second)
    hsecondMem).symm
  rw [htwo] at hone
  rw [hone] at hidem
  have hrewrite : ∑ third ∈ (univ.erase first).erase second,
      projectionOfDesign design first third * projectionOfDesign design third second
      = ∑ third ∈ (univ.erase first).erase second,
        projectionOfDesign design first third * projectionOfDesign design second third :=
    Finset.sum_congr rfl fun third _ => by rw [hsym third]
  rw [hrewrite] at hidem
  nlinarith [hidem]

/-- **THE SQUARE SUM OFF THE PIVOT PAIR.**  The row energy law with the two pair terms
peeled off. -/
theorem sum_sq_projectionRow_erase_pair (design : WeightedDesign size rank)
    {first second : Fin size} (hne : first ≠ second) :
    ∑ third ∈ (univ.erase first).erase second, projectionOfDesign design first third ^ 2
      = projectionOfDesign design first first * (1 - projectionOfDesign design first first)
        - projectionOfDesign design first second ^ 2 := by
  classical
  have hfull := sum_sq_projectionRow_full design first
  have hsecondMem : second ∈ univ.erase first :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ second⟩
  have hone := (Finset.add_sum_erase univ
    (fun third : Fin size => projectionOfDesign design first third ^ 2)
    (Finset.mem_univ first)).symm
  have htwo := (Finset.add_sum_erase (univ.erase first)
    (fun third : Fin size => projectionOfDesign design first third ^ 2)
    hsecondMem).symm
  rw [htwo] at hone
  rw [hone] at hfull
  nlinarith [hfull]

/-- The pivot pair erases in either order. -/
theorem erase_pair_comm (first second : Fin size) :
    (univ.erase first).erase second = (univ.erase second).erase first := by
  classical
  ext label
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

/-- **THE OFFSET SECOND MOMENT, CLOSED AND TWO-LOCAL.**  Written with `e` the pivot excess,
`p` and `q` the two diagonals and `r` the pivot pairing, the squared offsets outside the
pivot pair total

`e ^ 2 (q (1 − q) − r ^ 2) − 2 e r ^ 2 (1 − p − q) + r ^ 2 (p (1 − p) − r ^ 2)`.

The corpus carried the offset's first marginal only. -/
theorem sum_sq_shiftOffsetAt_erase_pair (design : WeightedDesign size rank)
    {first second : Fin size} (hne : first ≠ second) :
    ∑ third ∈ (univ.erase first).erase second,
        shiftOffsetAt design first second third ^ 2
      = diagonalShiftForm design first first ^ 2
          * (projectionOfDesign design second second
              * (1 - projectionOfDesign design second second)
            - projectionOfDesign design first second ^ 2)
        - 2 * diagonalShiftForm design first first
            * projectionOfDesign design first second ^ 2
            * (1 - projectionOfDesign design first first
                - projectionOfDesign design second second)
        + projectionOfDesign design first second ^ 2
            * (projectionOfDesign design first first
                * (1 - projectionOfDesign design first first)
              - projectionOfDesign design first second ^ 2) := by
  classical
  have hexpand : ∀ third ∈ (univ.erase first).erase second,
      shiftOffsetAt design first second third ^ 2
        = diagonalShiftForm design first first ^ 2
            * projectionOfDesign design second third ^ 2
          - 2 * diagonalShiftForm design first first
              * projectionOfDesign design first second
              * (projectionOfDesign design first third
                  * projectionOfDesign design second third)
          + projectionOfDesign design first second ^ 2
              * projectionOfDesign design first third ^ 2 := by
    intro third hthird
    have hthirdSecond : second ≠ third := (Finset.ne_of_mem_erase hthird).symm
    have hthirdFirst : first ≠ third :=
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hthird)).symm
    rw [shiftOffsetAt_apply design hne hthirdFirst hthirdSecond, diagonalShiftForm_diag]
    ring
  rw [Finset.sum_congr rfl hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hsecondSq : ∑ third ∈ (univ.erase first).erase second,
      projectionOfDesign design second third ^ 2
      = projectionOfDesign design second second
          * (1 - projectionOfDesign design second second)
        - projectionOfDesign design first second ^ 2 := by
    rw [erase_pair_comm, sum_sq_projectionRow_erase_pair design hne.symm]
    have hflip : projectionOfDesign design second first
        = projectionOfDesign design first second :=
      form_flip_of_transpose (projectionOfDesign_transpose design) first second
    rw [hflip]
  rw [hsecondSq, sum_offDiagProduct_erase_pair design hne,
    sum_sq_projectionRow_erase_pair design hne]
  ring

/-! ### 5. THE PARTIAL DETERMINANT SUM AT A SELECTED PAIR

Summing the pivot Schur identity over the third label, at a pivot pair the producer
SELECTS, is not one of the dead averaging arguments.  Those run over all twenty triples, or
over both partners at a pivot, and the corpus proves each of them negative:
`Gtz.sum_projGap_through_neg` at a label, `Gtz.sum_pairMinorProduct_sub_sq_shiftOffset_neg`
at a pivot, and `Gtz.pairMarginal_le_neg_four_of_flat` at a pair on the flat locus.  This
one fixes the partner and averages over the four remaining labels only. -/

/-- The two-local partial gap at a pivot pair: the minor product against the offset second
moment, with everything written in the five scalars of the pair. -/
noncomputable def pairPartialGap (design : WeightedDesign size 3) (first second : Fin size) : ℝ :=
  pairMinorAt (diagonalShiftForm design) first second
      * (diagonalShiftForm design first first
            * (2 - diagonalShiftForm design first first)
          - projectionOfDesign design first first
              * (1 - projectionOfDesign design first first)
          - pairMinorAt (diagonalShiftForm design) first second)
    - (diagonalShiftForm design first first ^ 2
          * (projectionOfDesign design second second
              * (1 - projectionOfDesign design second second)
            - projectionOfDesign design first second ^ 2)
        - 2 * diagonalShiftForm design first first
            * projectionOfDesign design first second ^ 2
            * (1 - projectionOfDesign design first first
                - projectionOfDesign design second second)
        + projectionOfDesign design first second ^ 2
            * (projectionOfDesign design first first
                * (1 - projectionOfDesign design first first)
              - projectionOfDesign design first second ^ 2))

/-- **THE PARTIAL SUM IS THE TWO-LOCAL EXPRESSION.**  The pivot excess times the sum of the
triple determinants over the third label equals `Gtz.pairPartialGap`, which reads only the
two labels of the pivot pair. -/
theorem excess_mul_sum_det_eq_pairPartialGap (design : WeightedDesign size 3)
    {first second : Fin size} (hne : first ≠ second) :
    diagonalShiftForm design first first
        * ∑ third ∈ (univ.erase first).erase second,
            (tripleBlock (diagonalShiftForm design) first second third).det
      = pairPartialGap design first second := by
  classical
  have hschur : ∀ third ∈ (univ.erase first).erase second,
      diagonalShiftForm design first first
          * (tripleBlock (diagonalShiftForm design) first second third).det
        = pairMinorAt (diagonalShiftForm design) first second
            * pairMinorAt (diagonalShiftForm design) first third
          - shiftOffsetAt design first second third ^ 2 :=
    fun third _ => (pairMinorAt_diagonalShift_mul_sub_sq design first second third).symm
  rw [Finset.mul_sum, Finset.sum_congr rfl hschur, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_sq_shiftOffsetAt_erase_pair design hne]
  have hsecondMem : second ∈ univ.erase first :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ second⟩
  have hrow := sum_pairMinorAt_diagonalShift_erase design first
  have hsplit := (Finset.add_sum_erase (univ.erase first)
    (fun third : Fin size => pairMinorAt (diagonalShiftForm design) first third)
    hsecondMem).symm
  rw [hsplit] at hrow
  have hcast : ((3 : ℕ) : ℝ) - 1 = 2 := by norm_num
  rw [hcast] at hrow
  have hminorSum : ∑ third ∈ (univ.erase first).erase second,
      pairMinorAt (diagonalShiftForm design) first third
      = diagonalShiftForm design first first
            * (2 - diagonalShiftForm design first first)
          - projectionOfDesign design first first
              * (1 - projectionOfDesign design first first)
        - pairMinorAt (diagonalShiftForm design) first second := by linarith
  rw [hminorSum, pairPartialGap]

/-- **A POSITIVE PARTIAL GAP PRODUCES A GOOD THIRD LABEL.**  At a pivot of positive excess a
positive partial gap forces one of the four remaining labels to satisfy the third
inequality. -/
theorem exists_third_of_pairPartialGap_pos (design : WeightedDesign size 3)
    {first second : Fin size} (hne : first ≠ second)
    (hpivot : 0 < diagonalShiftForm design first first)
    (hgap : 0 < pairPartialGap design first second) :
    ∃ third ∈ (univ.erase first).erase second,
      shiftOffsetAt design first second third ^ 2
        < pairMinorAt (diagonalShiftForm design) first second
          * pairMinorAt (diagonalShiftForm design) first third := by
  classical
  have hsum : 0 < ∑ third ∈ (univ.erase first).erase second,
      (tripleBlock (diagonalShiftForm design) first second third).det := by
    by_contra hnot
    push Not at hnot
    have := excess_mul_sum_det_eq_pairPartialGap design hne
    nlinarith [hpivot, hnot, hgap]
  obtain ⟨third, hthird, hpos⟩ := exists_pos_of_sum_pos _ _ hsum
  refine ⟨third, hthird, ?_⟩
  have hschur := pairMinorAt_diagonalShift_mul_sub_sq design first second third
  nlinarith [hschur, hpivot, hpos]

/-- **THE TWO-LOCAL SELECTION CRITERION.**  Every primitive design owns a pivot pair whose
excess, pair minor and partial gap are all positive.  All three read only the two labels of
the pair. -/
def PairPartialGapSomewhere : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    ∃ first second : Fin 6, first ≠ second ∧
      0 < diagonalShiftForm design first first ∧
      0 < pairMinorAt (diagonalShiftForm design) first second ∧
      0 < pairPartialGap design first second

/-- **ALL FIVE ON-PATH OBLIGATIONS FROM THE TWO-LOCAL CRITERION.**  A sixth entrance to the
registry, and the first whose entire hypothesis reads two labels. -/
theorem allFiveOnPath_of_pairPartialGap (hpair : PairPartialGapSomewhere) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  refine allFiveOnPath_of_offsetDominatesSomewhere fun design hprimitive => ?_
  obtain ⟨first, second, hne, hpivot, hminor, hgap⟩ := hpair design hprimitive
  obtain ⟨third, hthird, hsq⟩ :=
    exists_third_of_pairPartialGap_pos design hne hpivot hgap
  have hthirdSecond : third ≠ second := Finset.ne_of_mem_erase hthird
  have hthirdFirst : third ≠ first :=
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hthird)
  exact ⟨first, second, third, hne, hthirdFirst, hthirdSecond, hpivot, hminor, hsq⟩

/-- The consolidated chart statement follows from the two-local criterion too. -/
theorem consolidatedStrictTriple_of_pairPartialGap (hpair : PairPartialGapSomewhere) :
    ConsolidatedStrictTriple := by
  refine consolidatedStrictTriple_of_offsetDominatesSomewhere fun design hprimitive => ?_
  obtain ⟨first, second, hne, hpivot, hminor, hgap⟩ := hpair design hprimitive
  obtain ⟨third, hthird, hsq⟩ :=
    exists_third_of_pairPartialGap_pos design hne hpivot hgap
  have hthirdSecond : third ≠ second := Finset.ne_of_mem_erase hthird
  have hthirdFirst : third ≠ first :=
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hthird)
  exact ⟨first, second, third, hne, hthirdFirst, hthirdSecond, hpivot, hminor, hsq⟩

end Gtz

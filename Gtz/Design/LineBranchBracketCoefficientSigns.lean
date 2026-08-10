import Gtz.Design.LineBranchFreePairBracketExpansion
import Gtz.Design.TightLineRefutationFixtures

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The sign classification of the free-pair bracket ledger

`Gtz.weighted_freePairGap_det_sum_eq_bracketLedger` writes the weighted
three-free-pair determinant aggregate -- equivalently, by
`Gtz.unitAxisMetricDet_mul_freePairRowAggregate_eq_neg_detSum`, the free-pair
row aggregate scaled by the transported metric determinant -- as an exact
Cauchy-Binet ledger in the nineteen coordinate brackets.  This file settles
the SIGN of every coefficient in that ledger.

The answer is that the ledger carries exactly ONE family of negative terms,
the nine one-slot coordinate-bracket squares, and that family's coefficient is
strictly positive at every design.  The three cross families and the
free-frame family carry strictly positive coefficients.

## What this does NOT prove

It does not prove the aggregate positive, and it cannot.  The aggregate is
genuinely negative at a design in this tree: `freePairKillerDesign` has
`freePairRowAggregate = -315/128` (`Gtz.freePairKillerDesign_freePairRowAggregate_neg`,
Gtz/Design/TightLineRefutationFixtures.lean).  Since the ledger identity is
unconditional in the weights and atoms, no argument assembled purely from
coefficient signs can conclude positivity -- the negative family is real and
must be dominated by the positive families, which is exactly the open content
of the free-pair aggregate question and is untouched here.

None of the coefficient facts below mentions the no-one-slot hypothesis, and
that hypothesis is what separates the designs where the aggregate is positive
from `freePairKillerDesign`, which has five strict one-slot triples.
-/

namespace Gtz

/-- Every coefficient multiplying a one-slot coordinate-bracket square in the
free-pair ledger is strictly positive inside the open weight simplex, so those
nine terms are genuinely subtracted. -/
theorem freePairLedger_oneSlotCoefficient_pos
    (chosen otherOne otherTwo : ℝ)
    (hchosen : 0 < chosen) (hotherOne : 0 < otherOne)
    (hotherTwo : 0 < otherTwo)
    (hsum : chosen + otherOne + otherTwo < 1) :
    0 < chosen + otherOne + otherTwo
      - chosen * (2 * (chosen + otherOne + otherTwo) - 1) := by
  let total := chosen + otherOne + otherTwo
  have htotal : 0 < total := by dsimp [total]; linarith
  have hchosenLt : chosen < total := by dsimp [total]; linarith
  by_cases hfactor : 2 * total - 1 ≤ 0
  · have hproduct : chosen * (2 * total - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hchosen.le hfactor
    dsimp [total] at *
    linarith
  · have hfactorPos : 0 < 2 * total - 1 := lt_of_not_ge hfactor
    have hproductLt : chosen * (2 * total - 1)
        < total * (2 * total - 1) :=
      mul_lt_mul_of_pos_right hchosenLt hfactorPos
    have hslack : 0 < 2 * total * (1 - total) :=
      mul_pos (mul_pos (by norm_num) htotal) (by dsimp [total]; linarith)
    dsimp [total] at *
    nlinarith

/-- Every distance-two cross-bracket coefficient in the free-pair ledger is
strictly positive inside the open weight simplex. -/
theorem freePairLedger_crossCoefficient_pos
    (first second remaining : ℝ)
    (hfirst : 0 < first) (hsecond : 0 < second)
    (hremaining : 0 < remaining)
    (hsum : first + second + remaining < 1) :
    0 < (1 - (first + second + remaining))
      * (first + second - 2 * first * second) := by
  have hfirstLt : first < 1 := by linarith
  have hsecondLt : second < 1 := by linarith
  have hleft : 0 < first * (1 - second) :=
    mul_pos hfirst (sub_pos.mpr hsecondLt)
  have hright : 0 < second * (1 - first) :=
    mul_pos hsecond (sub_pos.mpr hfirstLt)
  have hinner : 0 < first + second - 2 * first * second := by
    nlinarith
  exact mul_pos (sub_pos.mpr hsum) hinner

/-- The free-frame determinant-square coefficient in the free-pair ledger is
strictly positive inside the open weight simplex. -/
theorem freePairLedger_freeFrameCoefficient_pos
    (first second third : ℝ)
    (hfirst : 0 < first) (hsecond : 0 < second)
    (hthird : 0 < third)
    (hsum : first + second + third < 1) :
    0 < (2 - (first + second + third))
          * (first * second + first * third + second * third)
      - (3 - 2 * (first + second + third)) * first * second * third := by
  let total := first + second + third
  let triple := first * second * third
  let pairs := first * second + first * third + second * third
  have htotalPos : 0 < total := by dsimp [total]; linarith
  have hfirstLt : first < 1 := by linarith
  have hsecondLt : second < 1 := by linarith
  have hthirdLt : third < 1 := by linarith
  have htriplePos : 0 < triple := by
    dsimp [triple]
    exact mul_pos (mul_pos hfirst hsecond) hthird
  have hpairZero : triple < first * second := by
    dsimp [triple]
    nlinarith [mul_pos (mul_pos hfirst hsecond) (sub_pos.mpr hthirdLt)]
  have hpairOne : triple < first * third := by
    dsimp [triple]
    nlinarith [mul_pos (mul_pos hfirst hthird) (sub_pos.mpr hsecondLt)]
  have hpairTwo : triple < second * third := by
    dsimp [triple]
    nlinarith [mul_pos (mul_pos hsecond hthird) (sub_pos.mpr hfirstLt)]
  have hpairs : 3 * triple < pairs := by
    dsimp [pairs]
    linarith
  have hscale : 0 < 2 - total := by dsimp [total]; linarith
  have hscaled : (2 - total) * (3 * triple) < (2 - total) * pairs :=
    mul_lt_mul_of_pos_left hpairs hscale
  dsimp [total, triple, pairs] at *
  nlinarith

/-- The unit-axis free weights are the design's own weights at labels 3, 4, 5,
hence strictly positive. -/
theorem unitAxisFreeWeight_pos (design : WeightedDesign 6 3) (index : Fin 3) :
    0 < unitAxisFreeWeight design index :=
  design.weight_pos (freeThreeLabel index)

/-- The three unit-axis free weights sum to strictly less than one, because the
three base weights are positive and all six weights sum to one.  This is the
side condition the three coefficient lemmas need, and it is available at every
design with no further hypothesis. -/
theorem unitAxisFreeWeight_sum_lt_one (design : WeightedDesign 6 3) :
    unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
      + unitAxisFreeWeight design 2 < 1 := by
  have hsum : ∑ atomIndex, design.weight atomIndex = 1 := design.weight_sum_one
  rw [Fin.sum_univ_six] at hsum
  have hbaseZero := design.weight_pos 0
  have hbaseOne := design.weight_pos 1
  have hbaseTwo := design.weight_pos 2
  simp only [unitAxisFreeWeight, freeThreeLabel, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linarith

/-- **The sign classification of the free-pair bracket ledger.**  At every
design, every coefficient appearing in
`Gtz.weighted_freePairGap_det_sum_eq_bracketLedger` is strictly positive:
the three one-slot coefficients (whose terms are SUBTRACTED), the three
cross-bracket coefficients, and the free-frame coefficient.

So the ledger has exactly one negative family and that family is real.  This
is a classification, not a positivity proof -- see the module docstring and
`Gtz.freePairKillerDesign_freePairRowAggregate_neg`. -/
theorem freePairLedger_coefficients_pos (design : WeightedDesign 6 3) :
    (0 < unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
          + unitAxisFreeWeight design 2
        - unitAxisFreeWeight design 0
            * (2 * (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
                  + unitAxisFreeWeight design 2) - 1))
      ∧ (0 < unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
              + unitAxisFreeWeight design 2
            - unitAxisFreeWeight design 1
                * (2 * (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
                      + unitAxisFreeWeight design 2) - 1))
      ∧ (0 < unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
              + unitAxisFreeWeight design 2
            - unitAxisFreeWeight design 2
                * (2 * (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
                      + unitAxisFreeWeight design 2) - 1))
      ∧ (0 < (1 - (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
                  + unitAxisFreeWeight design 2))
            * (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
                - 2 * unitAxisFreeWeight design 0 * unitAxisFreeWeight design 1))
      ∧ (0 < (1 - (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
                  + unitAxisFreeWeight design 2))
            * (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 2
                - 2 * unitAxisFreeWeight design 0 * unitAxisFreeWeight design 2))
      ∧ (0 < (1 - (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
                  + unitAxisFreeWeight design 2))
            * (unitAxisFreeWeight design 1 + unitAxisFreeWeight design 2
                - 2 * unitAxisFreeWeight design 1 * unitAxisFreeWeight design 2))
      ∧ 0 < (2 - (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
                  + unitAxisFreeWeight design 2))
              * (unitAxisFreeWeight design 0 * unitAxisFreeWeight design 1
                + unitAxisFreeWeight design 0 * unitAxisFreeWeight design 2
                + unitAxisFreeWeight design 1 * unitAxisFreeWeight design 2)
          - (3 - 2 * (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
                      + unitAxisFreeWeight design 2))
              * unitAxisFreeWeight design 0 * unitAxisFreeWeight design 1
              * unitAxisFreeWeight design 2 := by
  have hzero := unitAxisFreeWeight_pos design 0
  have hone := unitAxisFreeWeight_pos design 1
  have htwo := unitAxisFreeWeight_pos design 2
  have hsum := unitAxisFreeWeight_sum_lt_one design
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := freePairLedger_oneSlotCoefficient_pos
      (unitAxisFreeWeight design 0) (unitAxisFreeWeight design 1)
      (unitAxisFreeWeight design 2) hzero hone htwo hsum
    linarith
  · have := freePairLedger_oneSlotCoefficient_pos
      (unitAxisFreeWeight design 1) (unitAxisFreeWeight design 0)
      (unitAxisFreeWeight design 2) hone hzero htwo (by linarith)
    linarith
  · have := freePairLedger_oneSlotCoefficient_pos
      (unitAxisFreeWeight design 2) (unitAxisFreeWeight design 0)
      (unitAxisFreeWeight design 1) htwo hzero hone (by linarith)
    linarith
  · have := freePairLedger_crossCoefficient_pos
      (unitAxisFreeWeight design 0) (unitAxisFreeWeight design 1)
      (unitAxisFreeWeight design 2) hzero hone htwo hsum
    linarith
  · have := freePairLedger_crossCoefficient_pos
      (unitAxisFreeWeight design 0) (unitAxisFreeWeight design 2)
      (unitAxisFreeWeight design 1) hzero htwo hone (by linarith)
    nlinarith
  · have := freePairLedger_crossCoefficient_pos
      (unitAxisFreeWeight design 1) (unitAxisFreeWeight design 2)
      (unitAxisFreeWeight design 0) hone htwo hzero (by linarith)
    nlinarith
  · have := freePairLedger_freeFrameCoefficient_pos
      (unitAxisFreeWeight design 0) (unitAxisFreeWeight design 1)
      (unitAxisFreeWeight design 2) hzero hone htwo hsum
    linarith

/-- **The coefficient signs cannot decide the aggregate, and this is a
theorem rather than a caution.**  `freePairLedger_coefficients_pos` holds at
EVERY design with no hypothesis, yet the free-pair row aggregate takes both
signs on actual designs of the tree.  Any argument for positivity of the
aggregate must therefore consume a hypothesis that the coefficient facts do
not mention -- in particular the no-one-slot hypothesis, which
`freePairKillerDesign` fails five times over.

The two witnesses are the landed refutation fixtures: `baseTieKillerDesign`
has aggregate `14107/1008` and `freePairKillerDesign` has aggregate
`-315/128`. -/
theorem exists_design_freePairRowAggregate_neg_and_exists_pos :
    (∃ design : WeightedDesign 6 3, freePairRowAggregate design < 0)
      ∧ (∃ design : WeightedDesign 6 3, 0 < freePairRowAggregate design) :=
  ⟨⟨freePairKillerDesign, freePairKillerDesign_freePairRowAggregate_neg⟩,
    ⟨baseTieKillerDesign, baseTieKillerDesign_freePairRowAggregate_pos⟩⟩

end Gtz

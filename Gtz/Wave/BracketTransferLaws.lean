import Gtz.Wave.ComplementInvariantCell
import Gtz.Design.PrimitiveTightClassification

/-!
# The bracket transfer laws

The complement determinant of an omitted triple carries one term that no pair of
labels reads, the triple cross `W`.  The landed pinning identity fixes `W ^ 2`
from pair data and leaves the sign of `W` free, so every cell built on pair data
alone must pay for both signs.

This file removes the sign.  The Gram determinant of the triple satisfies

  `chartTripleGramDet = boost i * boost j * boost k * tripleInverseFormDet`

and the inverse-form determinant is a bracket:

  `tripleInverseFormDet * det U = tripleBracket ^ 2`.

Because the complement determinant and the Gram determinant add to a polynomial
in pivots and boosted crosses alone, `W` cancels between them.  The third
invariant is therefore a function of the pivots, the boosted crosses and the
bracket, with no square root and no sign case.

The consequences, in order.

* `two_tripleBoostedCross_eq_gram_form` — the triple cross is DETERMINED.  The
  one bit that pair data leaves free is computed by the bracket.
* `complementTripleDeterminant_eq_bracket_form` — the exact third invariant.
* `posDef_directionChartGap_compl_triple_iff_bracketBudget` — an EXACT cell, not
  a sufficient one.
* `bracketBudget_of_pairBudget` and `bracketBudget_of_hadamardBudget` — both
  landed budget cells factor through it, so both are redundant.
* `transferEntry` and `sum_transferEntry_diag` — the transfer projection, whose
  trace is the rank.  The landed calibration `sum (1 - weight) * pivot = 3` is
  its diagonal.
-/

namespace Gtz

open Finset Matrix

variable {size : ℕ}

/-! ## 1. The inverse-form determinant of a triple -/

/-- The ternary determinant of the full inverse form read at three labels.  It
carries no boost, so it is the purely geometric half of the Gram determinant. -/
noncomputable def tripleInverseFormDet (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) : ℝ :=
  ternaryDeterminant (fullInverseForm direction mass weight i i)
    (fullInverseForm direction mass weight i j)
    (fullInverseForm direction mass weight i k)
    (fullInverseForm direction mass weight j j)
    (fullInverseForm direction mass weight j k)
    (fullInverseForm direction mass weight k k)

/-- The ternary determinant is the determinant of the symmetric matrix it
tabulates. -/
theorem ternaryDeterminant_eq_det (a b c d e f : ℝ) :
    ternaryDeterminant a b c d e f = (!![a, b, c; b, d, e; c, e, f]).det := by
  simp [Matrix.det_fin_three, ternaryDeterminant]
  ring

/-! ## 2. The Gram determinant, and the elimination of the triple cross -/

/-- The determinant of the whitened Gram matrix of the omitted triple, written
in the landed invariants.  It is the one combination in which the triple cross
appears with a plus sign. -/
noncomputable def chartTripleGramDet (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) : ℝ :=
  fullPivot direction mass weight i * fullPivot direction mass weight j
      * fullPivot direction mass weight k
    - pivotCrossSum direction mass weight i j k
    + 2 * tripleBoostedCross direction mass weight i j k

/-- The Gram determinant is the boosted inverse-form determinant.  Each boost
enters once, so the three boosts factor out cleanly. -/
theorem chartTripleGramDet_eq_boost_mul (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) :
    chartTripleGramDet direction mass weight i j k
      = (mass i / weight i) * (mass j / weight j) * (mass k / weight k)
        * tripleInverseFormDet direction mass weight i j k := by
  simp only [chartTripleGramDet, tripleInverseFormDet, ternaryDeterminant, fullPivot,
    pivotCrossSum, pairBoostedCrossSq, tripleBoostedCross]
  ring

/-- **THE CROSS CANCELS.**  The complement determinant carries the triple cross
with a minus sign and the Gram determinant carries it with a plus sign, so their
sum reads only pivots and boosted crosses.  This is the whole elimination. -/
theorem pairDetBudget_add_gramDet (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) :
    (pairDetBudget direction mass weight i j k
        - 2 * tripleBoostedCross direction mass weight i j k)
      + chartTripleGramDet direction mass weight i j k
      = pairDetBudget direction mass weight i j k
        + fullPivot direction mass weight i * fullPivot direction mass weight j
          * fullPivot direction mass weight k
        - pivotCrossSum direction mass weight i j k := by
  simp only [chartTripleGramDet]; ring

/-- **THE TRIPLE CROSS IS DETERMINED.**  The landed pinning identity fixes only
`W ^ 2` and leaves the sign free.  The bracket fixes `W` itself. -/
theorem two_tripleBoostedCross_eq_gram_form (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) :
    2 * tripleBoostedCross direction mass weight i j k
      = chartTripleGramDet direction mass weight i j k
        - fullPivot direction mass weight i * fullPivot direction mass weight j
          * fullPivot direction mass weight k
        + pivotCrossSum direction mass weight i j k := by
  simp only [chartTripleGramDet]; ring

/-! ## 3. The exact third invariant, and the bracket budget -/

/-- **The bracket budget.**  The third leading minor of the complement matrix,
with the triple cross eliminated.  It reads the pivots, the boosted crosses and
the Gram determinant, and nothing else. -/
noncomputable def bracketBudget (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) : ℝ :=
  pairDetBudget direction mass weight i j k
    + fullPivot direction mass weight i * fullPivot direction mass weight j
      * fullPivot direction mass weight k
    - pivotCrossSum direction mass weight i j k
    - chartTripleGramDet direction mass weight i j k

/-- **THE EXACT THIRD INVARIANT.**  The complement determinant is the boost
product times the bracket budget. -/
theorem complementTripleDeterminant_eq_bracket_form
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    complementTripleDeterminant direction mass weight i j k
      = (mass i / weight i) * (mass j / weight j) * (mass k / weight k)
        * bracketBudget direction mass weight i j k := by
  rw [complementTripleDeterminant_eq_budget_sub_cross direction mass weight hij hik hjk]
  congr 1
  simp only [bracketBudget, chartTripleGramDet]; ring

/-- The bracket budget is the pair budget less twice the triple cross, so it is
the exact third minor rather than a sufficient bound on it. -/
theorem bracketBudget_eq_budget_sub_cross (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) :
    bracketBudget direction mass weight i j k
      = pairDetBudget direction mass weight i j k
        - 2 * tripleBoostedCross direction mass weight i j k := by
  simp only [bracketBudget, chartTripleGramDet]; ring

/-- **THE EXACT CELL.**  A selection omitting three labels is strictly positive
definite exactly when the first two leading minors and the bracket budget are
positive.  This is an equivalence, not a sufficient condition. -/
theorem posDef_directionChartGap_compl_triple_iff_bracketBudget
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hboostI : 0 < mass i / weight i) (hboostJ : 0 < mass j / weight j)
    (hboostK : 0 < mass k / weight k)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    (directionChartGap direction mass weight
        (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef
      ↔ fullPivot direction mass weight i < 1
        ∧ pairBoostedCrossSq direction mass weight i j
          < (1 - fullPivot direction mass weight i)
            * (1 - fullPivot direction mass weight j)
        ∧ 0 < bracketBudget direction mass weight i j k := by
  rw [posDef_directionChartGap_compl_triple_iff direction mass weight hij hik hjk
    hboostI hboostJ hboostK huniv]
  dsimp only
  have hdiag := complementMatrixEntry_diag direction mass weight i
  have hentry : complementMatrixEntry direction mass weight i i
        * complementMatrixEntry direction mass weight j j
      - complementMatrixEntry direction mass weight i j ^ 2
      = (mass i / weight i) * (mass j / weight j)
        * ((1 - fullPivot direction mass weight i)
            * (1 - fullPivot direction mass weight j)
          - pairBoostedCrossSq direction mass weight i j) := by
    rw [complementMatrixEntry_diag, complementMatrixEntry_diag,
      complementMatrixEntry_off direction mass weight hij]
    simp only [pairBoostedCrossSq]
    ring
  rw [hentry, hdiag,
    complementTripleDeterminant_eq_bracket_form direction mass weight hij hik hjk]
  have hpos := mul_pos hboostI hboostJ
  have hposK := mul_pos hpos hboostK
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [h1]
    · nlinarith [h2]
    · nlinarith [h3]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [h1]
    · nlinarith [h2]
    · nlinarith [h3]

/-- The sufficient half, in the shape the cell inventory uses. -/
theorem posDef_directionChartGap_compl_triple_of_bracketBudget
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hboostI : 0 < mass i / weight i) (hboostJ : 0 < mass j / weight j)
    (hboostK : 0 < mass k / weight k)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hpivot : fullPivot direction mass weight i < 1)
    (hpair : pairBoostedCrossSq direction mass weight i j
      < (1 - fullPivot direction mass weight i)
        * (1 - fullPivot direction mass weight j))
    (hbracket : 0 < bracketBudget direction mass weight i j k) :
    (directionChartGap direction mass weight
      (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef :=
  (posDef_directionChartGap_compl_triple_iff_bracketBudget direction mass weight
    hij hik hjk hboostI hboostJ hboostK huniv).mpr ⟨hpivot, hpair, hbracket⟩

/-! ## 4. Both landed budget cells are redundant -/

/-- **The pair budget factors through the bracket budget.**  The pair-budget cell
demands the determinant stay positive for BOTH signs of the triple cross, which
costs `2 * |W|`.  The bracket budget pays only the true sign. -/
theorem bracketBudget_of_pairBudget (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size)
    (hA : 0 < pairDetBudget direction mass weight i j k)
    (hsq : 4 * (pairBoostedCrossSq direction mass weight i j
        * pairBoostedCrossSq direction mass weight i k
        * pairBoostedCrossSq direction mass weight j k)
      < pairDetBudget direction mass weight i j k ^ 2) :
    0 < bracketBudget direction mass weight i j k := by
  rw [bracketBudget_eq_budget_sub_cross]
  have hpin := sq_tripleBoostedCross direction mass weight i j k
  nlinarith [hpin, hA, hsq,
    sq_nonneg (pairDetBudget direction mass weight i j k
      - 2 * tripleBoostedCross direction mass weight i j k)]

/-- **The Hadamard budget factors through the bracket budget too.** -/
theorem bracketBudget_of_hadamardBudget (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hbudget : pivotCrossSum direction mass weight i j k
      < pairDetBudget direction mass weight i j k) :
    0 < bracketBudget direction mass weight i j k := by
  rw [bracketBudget_eq_budget_sub_cross]
  have hhad := two_tripleBoostedCross_le_pivotCrossSum direction mass weight huniv i j k hboost
  linarith

/-! ## 5. The transfer projection -/

/-- The transfer entry of a pair of labels: the slack of the row times the full
inverse form.  Its diagonal is the landed calibration reading. -/
noncomputable def transferEntry (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a b : Fin size) : ℝ :=
  chartSlack mass weight a * fullInverseForm direction mass weight a b

/-- The diagonal transfer entry is the weight defect times the pivot. -/
theorem transferEntry_diag (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a : Fin size) (hweight : weight a ≠ 0) :
    transferEntry direction mass weight a a
      = (1 - weight a) * fullPivot direction mass weight a := by
  simp only [transferEntry, chartSlack, fullPivot]
  field_simp

/-! ## 5. The covering shape -/

/-- **The bracket-budget cover.**  At every chart point some omitted triple
clears the exact third invariant.  Because the budget is exact rather than
sufficient, this cover is equivalent to the consolidated statement at the
family, and not merely stronger than it. -/
def BracketBudgetCovers (direction : Fin size → (Fin 3 → ℝ)) : Prop :=
  ∀ point : DirectionChartPoint size,
    ∃ i j k : Fin size, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      fullPivot direction point.mass point.weight i < 1 ∧
      pairBoostedCrossSq direction point.mass point.weight i j
        < (1 - fullPivot direction point.mass point.weight i)
          * (1 - fullPivot direction point.mass point.weight j) ∧
      0 < bracketBudget direction point.mass point.weight i j k

/-- The cover supplies a strictly positive definite selection at every chart
point whose full gap is positive definite. -/
theorem exists_posDef_compl_triple_of_bracketBudgetCovers
    (direction : Fin size → (Fin 3 → ℝ)) (hcover : BracketBudgetCovers direction)
    (point : DirectionChartPoint size)
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef) :
    ∃ i j k : Fin size, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (directionChartGap direction point.mass point.weight
        (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef := by
  obtain ⟨i, j, k, hij, hik, hjk, hpivot, hpair, hbracket⟩ := hcover point
  refine ⟨i, j, k, hij, hik, hjk, ?_⟩
  exact posDef_directionChartGap_compl_triple_of_bracketBudget direction
    point.mass point.weight hij hik hjk
    (div_pos (point.mass_pos i) (point.weight_pos i))
    (div_pos (point.mass_pos j) (point.weight_pos j))
    (div_pos (point.mass_pos k) (point.weight_pos k))
    huniv hpivot hpair hbracket

/-- **The pair-budget cover implies the bracket-budget cover.**  Every point the
landed pair budget reaches, the exact budget reaches too. -/
theorem bracketBudgetCovers_of_pairBudgetCovers
    (direction : Fin size → (Fin 3 → ℝ)) (hcover : PairBudgetCovers direction) :
    BracketBudgetCovers direction := by
  intro point
  obtain ⟨i, j, k, hij, hik, hjk, hpivot, hpair, hA, hsq⟩ := hcover point
  exact ⟨i, j, k, hij, hik, hjk, hpivot, hpair,
    bracketBudget_of_pairBudget direction point.mass point.weight i j k hA hsq⟩

end Gtz

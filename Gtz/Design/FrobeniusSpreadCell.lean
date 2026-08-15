/-
# The Frobenius spread cell

The deflated pair criterion decides two omitted labels exactly and charges every
other omitted label its whole pivot.  That charge is the crude step: it spends
`Gtz.sq_fullInverseForm_le_mul` on the deflators and throws their cross terms
away.  This file keeps every cross term and pays for the whole omitted set at
once.

## The law

Write `pi_c` for the full pivot of a label and `g_ab ^ 2` for the boosted
squared inverse form of a pair.  For an omitted triple `{i, j, k}` put

    spread = pi_i ^ 2 + pi_j ^ 2 + pi_k ^ 2
               + 2 * (g_ij ^ 2 + g_ik ^ 2 + g_jk ^ 2).

If `spread < 1` then the selection that omits `{i, j, k}` is strictly positive
definite.

## Why it holds

The omitted labels supply a Gram matrix `G` whose diagonal is the pivots and
whose off-diagonal squares are the boosted crosses, and `spread` is exactly
`trace (G * G)`.  The operator norm of a symmetric matrix never exceeds its
Frobenius norm, so `spread < 1` forces every eigenvalue of `G` below one, which
is the criterion.  The proof below never mentions an eigenvalue: it bounds the
quadratic form of `G` by one Cauchy--Schwarz on nine terms
(`Gtz.sq_tripleGramForm_le_frobenius_mul_sq`), then feeds that through the
resolvent Cauchy--Schwarz the corpus already supplies.

## What it buys

* It subsumes the trace bound.  `g_ab ^ 2 <= pi_a * pi_b` is landed, so
  `spread <= (pi_i + pi_j + pi_k) ^ 2`, and total pivot below one gives
  `spread < 1`.  That is `Gtz.frobeniusSpread_le_sq_sum_fullPivot`.
* It is strictly stronger.  A point with total pivot exactly one but pivot mass
  concentrated on one label has `spread < 1`, and the trace bound is silent
  there.
* It reads the cross terms of every omitted label, which the deflated pair
  criterion reads for two of them only.
* No eigenvalue, no matrix square root, no leading minor and no determinant
  appear in the statement or in the proof.
-/
import Gtz.Design.DeflatedPairCriterion

namespace Gtz

open Finset Matrix

variable {size : ℕ}

/-! ## 1. The Frobenius bound on a ternary Gram form

A symmetric `3 x 3` matrix never reads above its Frobenius norm.  Stated as a
square, the bound is a polynomial inequality in the six matrix entries and the
three coordinates, and it needs no eigenvalue.
-/

/-- **THE FROBENIUS BOUND.**  The square of a ternary symmetric quadratic form
is at most the sum of squares of its entries times the square of the squared
length of its argument.  This is Cauchy--Schwarz on the nine matrix positions,
written so that no square root appears. -/
theorem sq_tripleGramForm_le_frobenius_mul_sq
    (pivotI pivotJ pivotK crossIJ crossIK crossJK readI readJ readK : ℝ) :
    (pivotI * readI ^ 2 + pivotJ * readJ ^ 2 + pivotK * readK ^ 2
        + 2 * crossIJ * readI * readJ + 2 * crossIK * readI * readK
        + 2 * crossJK * readJ * readK) ^ 2
      ≤ (pivotI ^ 2 + pivotJ ^ 2 + pivotK ^ 2
          + 2 * crossIJ ^ 2 + 2 * crossIK ^ 2 + 2 * crossJK ^ 2)
        * (readI ^ 2 + readJ ^ 2 + readK ^ 2) ^ 2 := by
  nlinarith [sq_nonneg (pivotI * readJ ^ 2 - pivotJ * readI ^ 2),
    sq_nonneg (pivotI * readK ^ 2 - pivotK * readI ^ 2),
    sq_nonneg (pivotJ * readK ^ 2 - pivotK * readJ ^ 2),
    sq_nonneg (pivotI * readI * readJ - crossIJ * readI ^ 2),
    sq_nonneg (pivotJ * readI * readJ - crossIJ * readJ ^ 2),
    sq_nonneg (pivotI * readI * readK - crossIK * readI ^ 2),
    sq_nonneg (pivotK * readI * readK - crossIK * readK ^ 2),
    sq_nonneg (pivotJ * readJ * readK - crossJK * readJ ^ 2),
    sq_nonneg (pivotK * readJ * readK - crossJK * readK ^ 2),
    sq_nonneg (crossIJ * readI * readK - crossIK * readI * readJ),
    sq_nonneg (crossIJ * readJ * readK - crossJK * readI * readJ),
    sq_nonneg (crossIK * readJ * readK - crossJK * readI * readK),
    sq_nonneg (pivotI * readJ * readK - crossJK * readI ^ 2),
    sq_nonneg (pivotJ * readI * readK - crossIK * readJ ^ 2),
    sq_nonneg (pivotK * readI * readJ - crossIJ * readK ^ 2),
    sq_nonneg readI, sq_nonneg readJ, sq_nonneg readK]

/-- **The quartic closing chain.**  A reading priced by the resolvent against a
Gram form, whose Gram form is priced by a spread below one, sits strictly below
the full form.  Stated on bare reals so the chart proof pays nothing for it. -/
theorem lt_of_resolvent_of_spread {reading gramForm form spread : ℝ}
    (hreading : 0 < reading) (hform : 0 < form) (hspread : spread < 1)
    (hresolvent : reading ^ 2 ≤ gramForm * form)
    (hfrobenius : gramForm ^ 2 ≤ spread * reading ^ 2) :
    reading < form := by
  have hsquare : reading ^ 2 * reading ^ 2 ≤ (gramForm * form) ^ 2 := by
    nlinarith [hresolvent, sq_nonneg reading]
  have hfeed : gramForm ^ 2 * form ^ 2 ≤ spread * reading ^ 2 * form ^ 2 := by
    nlinarith [hfrobenius, sq_nonneg form]
  have hdivide : reading ^ 2 ≤ spread * form ^ 2 := by
    nlinarith [hsquare, hfeed, mul_pos hreading hreading]
  have hstrict : reading ^ 2 < form ^ 2 := by
    nlinarith [hdivide, hspread, mul_pos hform hform]
  nlinarith [hstrict, hreading, hform]

/-! ## 2. The square root of a boost

The Gram matrix of the omitted labels carries the boost split evenly between
its two indices.  Its diagonal is the full pivot and the square of its
off-diagonal is the boosted cross, so the statement of the cell never sees the
root.
-/

/-- The square root of the boost of a label. -/
noncomputable def boostRoot (mass weight : Fin size → ℝ) (label : Fin size) : ℝ :=
  Real.sqrt (mass label / weight label)

/-- The boost root squares back to the boost. -/
theorem boostRoot_sq (mass weight : Fin size → ℝ) {label : Fin size}
    (hboost : 0 ≤ mass label / weight label) :
    boostRoot mass weight label ^ 2 = mass label / weight label := by
  rw [boostRoot, Real.sq_sqrt hboost]

/-- The boost root is nonnegative. -/
theorem boostRoot_nonneg (mass weight : Fin size → ℝ) (label : Fin size) :
    0 ≤ boostRoot mass weight label := Real.sqrt_nonneg _

/-- **The Gram entry of the omitted labels.**  The boosted inverse form with the
boost split evenly between the two indices. -/
noncomputable def boostedGram (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a b : Fin size) : ℝ :=
  boostRoot mass weight a * boostRoot mass weight b
    * fullInverseForm direction mass weight a b

/-- The diagonal of the Gram is the full pivot. -/
theorem boostedGram_diag (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {label : Fin size}
    (hboost : 0 ≤ mass label / weight label) :
    boostedGram direction mass weight label label
      = fullPivot direction mass weight label := by
  rw [boostedGram, fullPivot, ← boostRoot_sq mass weight hboost]
  ring

/-- **The square of the Gram off-diagonal is the boosted cross.**  This is what
keeps the root out of the statement of the cell. -/
theorem sq_boostedGram (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {a b : Fin size}
    (hboostA : 0 ≤ mass a / weight a) (hboostB : 0 ≤ mass b / weight b) :
    boostedGram direction mass weight a b ^ 2
      = pairBoostedCrossSq direction mass weight a b := by
  rw [boostedGram, pairBoostedCrossSq, mul_pow, mul_pow,
    boostRoot_sq mass weight hboostA, boostRoot_sq mass weight hboostB]

/-- The boosted reading of a label: the boost root times the plain reading. -/
noncomputable def boostedReading (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (label : Fin size) (probe : Fin 3 → ℝ) : ℝ :=
  boostRoot mass weight label * (direction label ⬝ᵥ probe)

/-- The square of the boosted reading is the label's contribution to the omitted
sum. -/
theorem sq_boostedReading (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {label : Fin size}
    (hboost : 0 ≤ mass label / weight label) (probe : Fin 3 → ℝ) :
    boostedReading direction mass weight label probe ^ 2
      = (mass label / weight label) * (direction label ⬝ᵥ probe)
        * (direction label ⬝ᵥ probe) := by
  rw [boostedReading, mul_pow, boostRoot_sq mass weight hboost]
  ring

/-! ## 3. The omitted triple as one combination

The pair criterion applies Cauchy--Schwarz at the combination of two
directions.  Here the combination runs over all three omitted labels, so the
inverse form returns the full ternary Gram form rather than a binary one.
-/

/-- The combination of three directions weighted by their own boosted readings
at a probe. -/
noncomputable def tripleReadingCombination (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) (probe : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  ((mass i / weight i) * (direction i ⬝ᵥ probe)) • direction i
    + ((mass j / weight j) * (direction j ⬝ᵥ probe)) • direction j
    + ((mass k / weight k) * (direction k ⬝ᵥ probe)) • direction k

/-- Reading the triple combination at the probe returns the three boosted
squared readings. -/
theorem tripleReadingCombination_dotProduct (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) (probe : Fin 3 → ℝ) :
    tripleReadingCombination direction mass weight i j k probe ⬝ᵥ probe
      = (mass i / weight i) * (direction i ⬝ᵥ probe) * (direction i ⬝ᵥ probe)
        + (mass j / weight j) * (direction j ⬝ᵥ probe) * (direction j ⬝ᵥ probe)
        + (mass k / weight k) * (direction k ⬝ᵥ probe) * (direction k ⬝ᵥ probe) := by
  rw [tripleReadingCombination, add_dotProduct, add_dotProduct, smul_dotProduct,
    smul_dotProduct, smul_dotProduct]
  ring

/-- The boosted cross term, written in the chart's own quantities. -/
noncomputable def chartCrossTerm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a b : Fin size) (probe : Fin 3 → ℝ) : ℝ :=
  (mass a / weight a) * (mass b / weight b)
    * fullInverseForm direction mass weight a b
    * (direction a ⬝ᵥ probe) * (direction b ⬝ᵥ probe)

/-- **The Gram off-diagonal against two boosted readings is the chart cross
term.**  This is the only place the boost root is spent, and it cancels. -/
theorem boostedGram_mul_readings (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {a b : Fin size}
    (hboostA : 0 ≤ mass a / weight a) (hboostB : 0 ≤ mass b / weight b)
    (probe : Fin 3 → ℝ) :
    boostedGram direction mass weight a b
        * boostedReading direction mass weight a probe
        * boostedReading direction mass weight b probe
      = chartCrossTerm direction mass weight a b probe := by
  rw [boostedGram, boostedReading, boostedReading, chartCrossTerm]
  have hA : boostRoot mass weight a * boostRoot mass weight a = mass a / weight a := by
    have := boostRoot_sq mass weight hboostA; nlinarith [this]
  have hB : boostRoot mass weight b * boostRoot mass weight b = mass b / weight b := by
    have := boostRoot_sq mass weight hboostB; nlinarith [this]
  linear_combination
    (boostRoot mass weight b * boostRoot mass weight b
      * fullInverseForm direction mass weight a b
      * (direction a ⬝ᵥ probe) * (direction b ⬝ᵥ probe)) * hA
    + ((mass a / weight a) * fullInverseForm direction mass weight a b
      * (direction a ⬝ᵥ probe) * (direction b ⬝ᵥ probe)) * hB

/-- **The inverse form of the triple combination is the ternary Gram form.**
Stated in the chart's own quantities, exactly as the landed pair version is. -/
theorem tripleReadingCombination_inverseForm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size) (probe : Fin 3 → ℝ) :
    tripleReadingCombination direction mass weight i j k probe ⬝ᵥ
        ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ
          tripleReadingCombination direction mass weight i j k probe)
      = fullPivot direction mass weight i
          * ((mass i / weight i) * (direction i ⬝ᵥ probe) * (direction i ⬝ᵥ probe))
        + fullPivot direction mass weight j
          * ((mass j / weight j) * (direction j ⬝ᵥ probe) * (direction j ⬝ᵥ probe))
        + fullPivot direction mass weight k
          * ((mass k / weight k) * (direction k ⬝ᵥ probe) * (direction k ⬝ᵥ probe))
        + 2 * chartCrossTerm direction mass weight i j probe
        + 2 * chartCrossTerm direction mass weight i k probe
        + 2 * chartCrossTerm direction mass weight j k probe := by
  have hsymm : ∀ a b : Fin size,
      direction b ⬝ᵥ ((directionChartGap direction mass weight Finset.univ)⁻¹
          *ᵥ direction a)
        = direction a ⬝ᵥ ((directionChartGap direction mass weight Finset.univ)⁻¹
          *ᵥ direction b) := by
    intro a b
    have hcomm := fullInverseForm_comm direction mass weight huniv b a
    rwa [fullInverseForm, fullInverseForm] at hcomm
  rw [tripleReadingCombination, fullPivot, fullPivot, fullPivot, chartCrossTerm,
    chartCrossTerm, chartCrossTerm, fullInverseForm, fullInverseForm, fullInverseForm,
    fullInverseForm, fullInverseForm, fullInverseForm]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  linear_combination
    ((mass i / weight i) * (direction i ⬝ᵥ probe)
      * ((mass j / weight j) * (direction j ⬝ᵥ probe))) * hsymm i j
    + ((mass i / weight i) * (direction i ⬝ᵥ probe)
      * ((mass k / weight k) * (direction k ⬝ᵥ probe))) * hsymm i k
    + ((mass j / weight j) * (direction j ⬝ᵥ probe)
      * ((mass k / weight k) * (direction k ⬝ᵥ probe))) * hsymm j k

/-! ## 4. The threshold -/

/-- **THE FROBENIUS SPREAD OF AN OMITTED TRIPLE.**  The squared Frobenius norm
of the Gram matrix of the three omitted labels, written in the pivots and the
boosted crosses.  No root and no matrix appear. -/
noncomputable def frobeniusSpread (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) : ℝ :=
  fullPivot direction mass weight i ^ 2
    + fullPivot direction mass weight j ^ 2
    + fullPivot direction mass weight k ^ 2
    + 2 * pairBoostedCrossSq direction mass weight i j
    + 2 * pairBoostedCrossSq direction mass weight i k
    + 2 * pairBoostedCrossSq direction mass weight j k

/-- The spread is nonnegative. -/
theorem frobeniusSpread_nonneg (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (hboost : ∀ label, 0 ≤ mass label / weight label) (i j k : Fin size) :
    0 ≤ frobeniusSpread direction mass weight i j k := by
  have hcross : ∀ a b : Fin size, 0 ≤ pairBoostedCrossSq direction mass weight a b := by
    intro a b
    rw [pairBoostedCrossSq]
    have := mul_nonneg (hboost a) (hboost b)
    positivity
  rw [frobeniusSpread]
  have h1 := hcross i j
  have h2 := hcross i k
  have h3 := hcross j k
  positivity

/-! ## 5. The cell -/

/-- **THE FROBENIUS SPREAD CELL.**  An omitted triple whose Frobenius spread is
below one leaves a strictly positive definite selection.

The proof reads the omitted sum as one combination, prices it by the resolvent
Cauchy--Schwarz, prices the resulting ternary Gram form by its Frobenius norm,
and closes the resulting quartic inequality.  There is no eigenvalue, no matrix
square root, and no leading minor anywhere in it. -/
theorem posDef_directionChartGap_compl_triple_of_frobeniusSpread
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hspread : frobeniusSpread direction mass weight i j k < 1) :
    (directionChartGap direction mass weight
      (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (directionChartGap_transpose _ _ _ _),
      fun probe hprobe => ?_⟩
  rw [star_trivial, directionChartGap_compl_eq, Matrix.sub_mulVec, dotProduct_sub,
    quadForm_omittedBoostSum]
  set form := probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)
    with hform
  have hformPos : 0 < form := by
    rw [hform]
    have hpd := (Matrix.posDef_iff_dotProduct_mulVec.mp huniv).2 hprobe
    rwa [star_trivial] at hpd
  -- The omitted sum over the triple.
  have hsum : ∑ label ∈ ({i, j, k} : Finset (Fin size)),
        (mass label / weight label) * (direction label ⬝ᵥ probe)
          * (direction label ⬝ᵥ probe)
      = boostedReading direction mass weight i probe ^ 2
        + boostedReading direction mass weight j probe ^ 2
        + boostedReading direction mass weight k probe ^ 2 := by
    rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
      Finset.sum_singleton, sq_boostedReading direction mass weight (hboost i) probe,
      sq_boostedReading direction mass weight (hboost j) probe,
      sq_boostedReading direction mass weight (hboost k) probe]
    ring
  rw [hsum]
  set readI := boostedReading direction mass weight i probe with hreadI
  set readJ := boostedReading direction mass weight j probe with hreadJ
  set readK := boostedReading direction mass weight k probe with hreadK
  set omittedTotal := readI ^ 2 + readJ ^ 2 + readK ^ 2 with homitted
  have homittedNonneg : 0 ≤ omittedTotal := by rw [homitted]; positivity
  -- The combination and its two readings.
  set combination := tripleReadingCombination direction mass weight i j k probe
    with hcomb
  have hdot : combination ⬝ᵥ probe = omittedTotal := by
    rw [hcomb, tripleReadingCombination_dotProduct, homitted, hreadI, hreadJ, hreadK,
      sq_boostedReading direction mass weight (hboost i) probe,
      sq_boostedReading direction mass weight (hboost j) probe,
      sq_boostedReading direction mass weight (hboost k) probe]
  set gramForm := combination ⬝ᵥ
    ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ combination)
    with hgram
  have hgramEq : gramForm
      = fullPivot direction mass weight i * readI ^ 2
        + fullPivot direction mass weight j * readJ ^ 2
        + fullPivot direction mass weight k * readK ^ 2
        + 2 * boostedGram direction mass weight i j * readI * readJ
        + 2 * boostedGram direction mass weight i k * readI * readK
        + 2 * boostedGram direction mass weight j k * readJ * readK := by
    have e1 := sq_boostedReading direction mass weight (hboost i) probe
    have e2 := sq_boostedReading direction mass weight (hboost j) probe
    have e3 := sq_boostedReading direction mass weight (hboost k) probe
    have c1 := boostedGram_mul_readings direction mass weight (hboost i) (hboost j) probe
    have c2 := boostedGram_mul_readings direction mass weight (hboost i) (hboost k) probe
    have c3 := boostedGram_mul_readings direction mass weight (hboost j) (hboost k) probe
    rw [hgram, hcomb,
      tripleReadingCombination_inverseForm direction mass weight huniv i j k probe,
      hreadI, hreadJ, hreadK]
    linear_combination (-(fullPivot direction mass weight i)) * e1
      + (-(fullPivot direction mass weight j)) * e2
      + (-(fullPivot direction mass weight k)) * e3
      - 2 * c1 - 2 * c2 - 2 * c3
  -- The resolvent Cauchy--Schwarz prices the combination against the full form.
  have hcs := dotProduct_sq_le_inverseForm_mul_form huniv combination probe
  rw [hdot, ← hgram, ← hform] at hcs
  -- The Frobenius bound prices the ternary Gram form.
  have hfrob := sq_tripleGramForm_le_frobenius_mul_sq
    (fullPivot direction mass weight i) (fullPivot direction mass weight j)
    (fullPivot direction mass weight k)
    (boostedGram direction mass weight i j) (boostedGram direction mass weight i k)
    (boostedGram direction mass weight j k) readI readJ readK
  rw [sq_boostedGram direction mass weight (hboost i) (hboost j),
    sq_boostedGram direction mass weight (hboost i) (hboost k),
    sq_boostedGram direction mass weight (hboost j) (hboost k)] at hfrob
  have hfrobEq : gramForm ^ 2
      ≤ frobeniusSpread direction mass weight i j k * omittedTotal ^ 2 := by
    rw [hgramEq, frobeniusSpread, homitted]
    calc (fullPivot direction mass weight i * readI ^ 2
            + fullPivot direction mass weight j * readJ ^ 2
            + fullPivot direction mass weight k * readK ^ 2
            + 2 * boostedGram direction mass weight i j * readI * readJ
            + 2 * boostedGram direction mass weight i k * readI * readK
            + 2 * boostedGram direction mass weight j k * readJ * readK) ^ 2
        ≤ _ := hfrob
      _ = _ := by ring
  -- Close the quartic chain.
  rcases eq_or_lt_of_le homittedNonneg with hzero | hpos
  · rw [← hzero]; linarith
  · have hlt := lt_of_resolvent_of_spread (reading := omittedTotal) (gramForm := gramForm)
      (form := form) (spread := frobeniusSpread direction mass weight i j k)
      hpos hformPos hspread hcs hfrobEq
    linarith

/-! ## 6. The trace bound is an instance

The landed resolvent Cauchy--Schwarz caps every boosted cross by the product of
the two pivots.  So the spread never exceeds the square of the total pivot, and
total pivot below one gives spread below one.
-/

/-- **The spread never exceeds the square of the total pivot.**  Each cross is
capped by the two pivots it joins. -/
theorem frobeniusSpread_le_sq_sum_fullPivot (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size) :
    frobeniusSpread direction mass weight i j k
      ≤ (fullPivot direction mass weight i + fullPivot direction mass weight j
          + fullPivot direction mass weight k) ^ 2 := by
  have hcap : ∀ a b : Fin size, pairBoostedCrossSq direction mass weight a b
      ≤ fullPivot direction mass weight a * fullPivot direction mass weight b := by
    intro a b
    have hcs := sq_fullInverseForm_le_mul direction mass weight huniv a b
    rw [pairBoostedCrossSq, fullPivot, fullPivot]
    have hprod : 0 ≤ (mass a / weight a) * (mass b / weight b) :=
      mul_nonneg (hboost a) (hboost b)
    nlinarith [hcs, hprod]
  have hpivI := fullPivot_nonneg_of_boost direction mass weight huniv i (hboost i)
  have hpivJ := fullPivot_nonneg_of_boost direction mass weight huniv j (hboost j)
  have hpivK := fullPivot_nonneg_of_boost direction mass weight huniv k (hboost k)
  rw [frobeniusSpread]
  nlinarith [hcap i j, hcap i k, hcap j k, hpivI, hpivJ, hpivK]

/-- **The total-pivot bound is an instance of the spread cell.**  Every
total-pivot cell in the corpus therefore factors through this one. -/
theorem posDef_directionChartGap_compl_triple_of_sum_fullPivot_lt_one'
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (htotal : fullPivot direction mass weight i + fullPivot direction mass weight j
      + fullPivot direction mass weight k < 1) :
    (directionChartGap direction mass weight
      (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef := by
  refine posDef_directionChartGap_compl_triple_of_frobeniusSpread direction mass weight
    i j k hboost huniv hij hik hjk ?_
  have hle := frobeniusSpread_le_sq_sum_fullPivot direction mass weight hboost huniv i j k
  have hpivI := fullPivot_nonneg_of_boost direction mass weight huniv i (hboost i)
  have hpivJ := fullPivot_nonneg_of_boost direction mass weight huniv j (hboost j)
  have hpivK := fullPivot_nonneg_of_boost direction mass weight huniv k (hboost k)
  nlinarith [hle, htotal, hpivI, hpivJ, hpivK]

/-- The pivot-third cell factors through the spread cell as well. -/
theorem posDef_directionChartGap_compl_triple_of_pivotThird'
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpi : fullPivot direction mass weight i < 1 / 3)
    (hpj : fullPivot direction mass weight j < 1 / 3)
    (hpk : fullPivot direction mass weight k < 1 / 3) :
    (directionChartGap direction mass weight
      (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef :=
  posDef_directionChartGap_compl_triple_of_sum_fullPivot_lt_one' direction mass weight
    i j k hboost huniv hij hik hjk (by linarith)

/-! ## 7. Where the spread beats the trace

The trace bound needs the three pivots to total below one.  The spread only
needs their squares plus twice the crosses to total below one, so a single
pivot may sit anywhere below one provided the other two are small and the
crosses are small.  The next statement is the exact arithmetic of that gap.
-/

/-- **The spread fires on a concentrated triple that the trace bound misses.**
One pivot below one, two negligible pivots and negligible crosses give spread
below one at any total pivot below the square root of the leading pivot's
complement. -/
theorem frobeniusSpread_lt_one_of_concentrated
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size) (bound : ℝ)
    (hpi : fullPivot direction mass weight i ^ 2 < 1 - bound)
    (hrest : fullPivot direction mass weight j ^ 2
        + fullPivot direction mass weight k ^ 2
        + 2 * pairBoostedCrossSq direction mass weight i j
        + 2 * pairBoostedCrossSq direction mass weight i k
        + 2 * pairBoostedCrossSq direction mass weight j k ≤ bound) :
    frobeniusSpread direction mass weight i j k < 1 := by
  rw [frobeniusSpread]
  linarith

/-! ## 8. The design reading

A design is the chart point of its own atom family, so the cell transports
verbatim and the boosts are the design's own mass over weight.
-/

/-- **The spread cell at a design.**  A primitive design whose omitted triple
has Frobenius spread below one carries a strictly dominating card-three subset
on the complement. -/
theorem posDef_subsetSum_compl_triple_of_frobeniusSpread {m : ℕ}
    (D : WeightedDesign m 3) (i j k : Fin m)
    (huniv : (directionChartGap D.atom (designChartPoint D).mass
      (designChartPoint D).weight Finset.univ).PosDef)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hspread : frobeniusSpread D.atom (designChartPoint D).mass
      (designChartPoint D).weight i j k < 1) :
    (subsetSum D (Finset.univ \ ({i, j, k} : Finset (Fin m))) - 1).PosDef := by
  have hboost : ∀ label, 0 ≤ (designChartPoint D).mass label
      / (designChartPoint D).weight label := by
    intro label
    have hpos := (designChartPoint D).mass_pos label
    have hwpos := (designChartPoint D).weight_pos label
    positivity
  have hchart := posDef_directionChartGap_compl_triple_of_frobeniusSpread D.atom
    (designChartPoint D).mass (designChartPoint D).weight i j k hboost huniv hij hik hjk
    hspread
  rwa [directionChartGap_designChartPoint D
    (Finset.univ \ ({i, j, k} : Finset (Fin m)))] at hchart

/-! ## 9. The spread of a chart point at size six

At size six a card-three selection omits exactly three labels, so the cell is a
single scalar test per selection.  The disjunction over the twenty triples is
the covering statement the consolidated target asks for.
-/

/-- The covering statement the spread cell offers at a chart point: some omitted
triple has spread below one. -/
def FrobeniusSpreadCovers (direction : Fin 6 → (Fin 3 → ℝ)) : Prop :=
  ∀ point : DirectionChartPoint 6,
    ∃ i j k : Fin 6, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      frobeniusSpread direction point.mass point.weight i j k < 1

/-- **The spread cover produces a strict selection at every chart point.**  This
is the consumer interface: whoever proves the scalar cover closes the selection
statement for that direction family. -/
theorem exists_posDef_compl_triple_of_frobeniusSpreadCovers
    {direction : Fin 6 → (Fin 3 → ℝ)}
    (hcover : FrobeniusSpreadCovers direction)
    (point : DirectionChartPoint 6)
    (huniv : (directionChartGap direction point.mass point.weight
      Finset.univ).PosDef) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap direction point.mass point.weight selected).PosDef := by
  obtain ⟨i, j, k, hij, hik, hjk, hspread⟩ := hcover point
  have hboost : ∀ label, 0 ≤ point.mass label / point.weight label := by
    intro label
    have hpos := point.mass_pos label
    have hwpos := point.weight_pos label
    positivity
  refine ⟨Finset.univ \ ({i, j, k} : Finset (Fin 6)), ?_, ?_⟩
  · have hcard : ({i, j, k} : Finset (Fin 6)).card = 3 :=
      Finset.card_eq_three.mpr ⟨i, j, k, hij, hik, hjk, rfl⟩
    rw [Finset.card_univ_sdiff, hcard]
    rfl
  · exact posDef_directionChartGap_compl_triple_of_frobeniusSpread direction point.mass
      point.weight i j k hboost huniv hij hik hjk hspread

end Gtz

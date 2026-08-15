/-
# The sharp spread cell

The trace bound reads the omitted Gram through its trace alone.  The Frobenius
spread cell reads it through its squared Frobenius norm alone.  Each throws away
what the other keeps.  This file reads both at once and subsumes them.

## The law

Write `T` for the pivot trace of the omitted triple and `F` for its Frobenius
spread.  If

    T < 3     and     2 * F < T ^ 2 - 2 * T + 3

then the selection that omits the triple is strictly positive definite.

## Why it holds

The omitted labels supply a symmetric `3 x 3` Gram matrix `G` whose diagonal is
the pivots and whose off-diagonal squares are the boosted crosses, so `T` is its
trace and `F` is `trace (G * G)`.  Positive definiteness of the selection is
`G` below the identity.  The trace bound uses `lambda_max <= T`, the Frobenius
cell uses `lambda_max ^ 2 <= F`, and the sharp cell uses the two together.

The engine is one identity.  Centre the form at its own trace and the whole
bound becomes a single weighted Cauchy--Schwarz in six coordinates:

* the three pivot differences carry weight one,
* the three boosted crosses carry weight six,
* and the second Cauchy--Schwarz factor is EXACTLY twice the square of the
  squared probe length (`sq_probe_pairing_eq`).

That last equality is what makes the constant `2` correct rather than merely
sufficient, and it is why the cell is stated with `2 * F` and not `3 * F`.

## What it buys

* It subsumes the Frobenius cell.  The threshold `T ^ 2 - 2 * T + 3` is
  `(T - 1) ^ 2 + 2`, so it never falls below `2`, and `F < 1` fires the sharp
  cell at every trace (`sharpSpreadFires_of_frobeniusSpread_lt_one`).
* It subsumes the trace bound, hence every total-pivot cell in the corpus.  The
  landed cap `F <= T ^ 2` closes it at `T < 1`
  (`sharpSpreadFires_of_sum_fullPivot_lt_one`).
* It is strictly stronger than both at every trace other than one
  (`two_lt_sharpThreshold_of_ne_one`), and `sharp_fires_where_parents_are_silent`
  exhibits the scalars.
* No eigenvalue, no matrix square root, no leading minor and no determinant
  appear in the statement or in the proof.
-/
import Gtz.Design.FrobeniusSpreadCell

namespace Gtz

open Finset Matrix

variable {size : ℕ}

/-! ## 1. A six-coordinate weighted Cauchy--Schwarz

The corpus carries the three-coordinate weighted form.  The sharp bound needs
six coordinates with two distinct weights, so the identity is proved here in
full generality and specialised afterwards.
-/

/-- **The six-coordinate weighted Lagrange identity.**  The Cauchy--Schwarz
defect of a weighted six-term pairing is the weighted sum of the fifteen
two-by-two minors.  A ring identity, so it costs nothing. -/
theorem six_weighted_lagrange_identity
    (dOne dTwo dThree dFour dFive dSix : ℝ)
    (aOne aTwo aThree aFour aFive aSix : ℝ)
    (bOne bTwo bThree bFour bFive bSix : ℝ) :
    (dOne * aOne ^ 2 + dTwo * aTwo ^ 2 + dThree * aThree ^ 2
        + dFour * aFour ^ 2 + dFive * aFive ^ 2 + dSix * aSix ^ 2)
      * (dOne * bOne ^ 2 + dTwo * bTwo ^ 2 + dThree * bThree ^ 2
        + dFour * bFour ^ 2 + dFive * bFive ^ 2 + dSix * bSix ^ 2)
      - (dOne * aOne * bOne + dTwo * aTwo * bTwo + dThree * aThree * bThree
        + dFour * aFour * bFour + dFive * aFive * bFive + dSix * aSix * bSix) ^ 2
      = dOne * dTwo * (aOne * bTwo - aTwo * bOne) ^ 2
        + dOne * dThree * (aOne * bThree - aThree * bOne) ^ 2
        + dOne * dFour * (aOne * bFour - aFour * bOne) ^ 2
        + dOne * dFive * (aOne * bFive - aFive * bOne) ^ 2
        + dOne * dSix * (aOne * bSix - aSix * bOne) ^ 2
        + dTwo * dThree * (aTwo * bThree - aThree * bTwo) ^ 2
        + dTwo * dFour * (aTwo * bFour - aFour * bTwo) ^ 2
        + dTwo * dFive * (aTwo * bFive - aFive * bTwo) ^ 2
        + dTwo * dSix * (aTwo * bSix - aSix * bTwo) ^ 2
        + dThree * dFour * (aThree * bFour - aFour * bThree) ^ 2
        + dThree * dFive * (aThree * bFive - aFive * bThree) ^ 2
        + dThree * dSix * (aThree * bSix - aSix * bThree) ^ 2
        + dFour * dFive * (aFour * bFive - aFive * bFour) ^ 2
        + dFour * dSix * (aFour * bSix - aSix * bFour) ^ 2
        + dFive * dSix * (aFive * bSix - aSix * bFive) ^ 2 := by
  ring

/-- **The six-coordinate Cauchy--Schwarz at weights one and six.**  These are the
only weights the sharp bound needs: the three pivot differences at weight one
and the three boosted crosses at weight six. -/
theorem sq_six_weighted_inner_le
    (aOne aTwo aThree aFour aFive aSix : ℝ)
    (bOne bTwo bThree bFour bFive bSix : ℝ) :
    (aOne * bOne + aTwo * bTwo + aThree * bThree
        + 6 * (aFour * bFour + aFive * bFive + aSix * bSix)) ^ 2
      ≤ (aOne ^ 2 + aTwo ^ 2 + aThree ^ 2
          + 6 * (aFour ^ 2 + aFive ^ 2 + aSix ^ 2))
        * (bOne ^ 2 + bTwo ^ 2 + bThree ^ 2
          + 6 * (bFour ^ 2 + bFive ^ 2 + bSix ^ 2)) := by
  have hid := six_weighted_lagrange_identity 1 1 1 6 6 6
    aOne aTwo aThree aFour aFive aSix bOne bTwo bThree bFour bFive bSix
  nlinarith [hid, sq_nonneg (aOne * bTwo - aTwo * bOne),
    sq_nonneg (aOne * bThree - aThree * bOne), sq_nonneg (aOne * bFour - aFour * bOne),
    sq_nonneg (aOne * bFive - aFive * bOne), sq_nonneg (aOne * bSix - aSix * bOne),
    sq_nonneg (aTwo * bThree - aThree * bTwo), sq_nonneg (aTwo * bFour - aFour * bTwo),
    sq_nonneg (aTwo * bFive - aFive * bTwo), sq_nonneg (aTwo * bSix - aSix * bTwo),
    sq_nonneg (aThree * bFour - aFour * bThree),
    sq_nonneg (aThree * bFive - aFive * bThree),
    sq_nonneg (aThree * bSix - aSix * bThree),
    sq_nonneg (aFour * bFive - aFive * bFour), sq_nonneg (aFour * bSix - aSix * bFour),
    sq_nonneg (aFive * bSix - aSix * bFive)]

/-! ## 2. The three identities that centre the form

Centring the Gram form at its own trace turns the sharp bound into the
Cauchy--Schwarz above.  All three steps are ring identities.
-/

/-- **The centred numerator.**  Three times the Gram form minus the trace times
the squared probe length is the pairing of the pivot differences against the
squared reading differences, plus six times the crosses against the reading
products. -/
theorem centeredGramForm_eq_pairing
    (pivotI pivotJ pivotK crossIJ crossIK crossJK readI readJ readK : ℝ) :
    3 * (pivotI * readI ^ 2 + pivotJ * readJ ^ 2 + pivotK * readK ^ 2
          + 2 * crossIJ * readI * readJ + 2 * crossIK * readI * readK
          + 2 * crossJK * readJ * readK)
        - (pivotI + pivotJ + pivotK) * (readI ^ 2 + readJ ^ 2 + readK ^ 2)
      = (pivotI - pivotJ) * (readI ^ 2 - readJ ^ 2)
        + (pivotI - pivotK) * (readI ^ 2 - readK ^ 2)
        + (pivotJ - pivotK) * (readJ ^ 2 - readK ^ 2)
        + 6 * (crossIJ * (readI * readJ) + crossIK * (readI * readK)
          + crossJK * (readJ * readK)) := by
  ring

/-- **The centred spread.**  Three times the Frobenius spread minus the square of
the trace is the squared length of the same six-coordinate vector. -/
theorem centeredSpread_eq_sq_pairing
    (pivotI pivotJ pivotK crossIJ crossIK crossJK : ℝ) :
    3 * (pivotI ^ 2 + pivotJ ^ 2 + pivotK ^ 2
          + 2 * crossIJ ^ 2 + 2 * crossIK ^ 2 + 2 * crossJK ^ 2)
        - (pivotI + pivotJ + pivotK) ^ 2
      = (pivotI - pivotJ) ^ 2 + (pivotI - pivotK) ^ 2 + (pivotJ - pivotK) ^ 2
        + 6 * (crossIJ ^ 2 + crossIK ^ 2 + crossJK ^ 2) := by
  ring

/-- **THE IDENTITY THAT FIXES THE CONSTANT.**  The second Cauchy--Schwarz factor
is exactly twice the square of the squared probe length.  Not a bound: an
equality.  This is why the sharp threshold carries `2 * F` and not `3 * F`, and
it is the whole reason the cell is sharp rather than merely valid. -/
theorem sq_probe_pairing_eq (readI readJ readK : ℝ) :
    (readI ^ 2 - readJ ^ 2) ^ 2 + (readI ^ 2 - readK ^ 2) ^ 2
        + (readJ ^ 2 - readK ^ 2) ^ 2
        + 6 * ((readI * readJ) ^ 2 + (readI * readK) ^ 2 + (readJ * readK) ^ 2)
      = 2 * (readI ^ 2 + readJ ^ 2 + readK ^ 2) ^ 2 := by
  ring

/-! ## 3. The centred bound

The sharpening of `Gtz.sq_tripleGramForm_le_frobenius_mul_sq`.  That bound
prices the Gram form by the Frobenius spread alone.  This one prices the form
CENTRED AT ITS OWN TRACE, which is strictly more information whenever the trace
is not zero.
-/

/-- **THE CENTRED FROBENIUS BOUND.**  The square of the trace-centred ternary
Gram form is at most twice the centred spread times the square of the squared
probe length.  A polynomial inequality in the six entries and the three
coordinates, with no eigenvalue and no root. -/
theorem sq_centeredGramForm_le_centeredSpread
    (pivotI pivotJ pivotK crossIJ crossIK crossJK readI readJ readK : ℝ) :
    (3 * (pivotI * readI ^ 2 + pivotJ * readJ ^ 2 + pivotK * readK ^ 2
          + 2 * crossIJ * readI * readJ + 2 * crossIK * readI * readK
          + 2 * crossJK * readJ * readK)
        - (pivotI + pivotJ + pivotK) * (readI ^ 2 + readJ ^ 2 + readK ^ 2)) ^ 2
      ≤ 2 * (3 * (pivotI ^ 2 + pivotJ ^ 2 + pivotK ^ 2
            + 2 * crossIJ ^ 2 + 2 * crossIK ^ 2 + 2 * crossJK ^ 2)
          - (pivotI + pivotJ + pivotK) ^ 2)
        * (readI ^ 2 + readJ ^ 2 + readK ^ 2) ^ 2 := by
  have hcs := sq_six_weighted_inner_le
    (pivotI - pivotJ) (pivotI - pivotK) (pivotJ - pivotK) crossIJ crossIK crossJK
    (readI ^ 2 - readJ ^ 2) (readI ^ 2 - readK ^ 2) (readJ ^ 2 - readK ^ 2)
    (readI * readJ) (readI * readK) (readJ * readK)
  calc (3 * (pivotI * readI ^ 2 + pivotJ * readJ ^ 2 + pivotK * readK ^ 2
            + 2 * crossIJ * readI * readJ + 2 * crossIK * readI * readK
            + 2 * crossJK * readJ * readK)
          - (pivotI + pivotJ + pivotK) * (readI ^ 2 + readJ ^ 2 + readK ^ 2)) ^ 2
      = ((pivotI - pivotJ) * (readI ^ 2 - readJ ^ 2)
          + (pivotI - pivotK) * (readI ^ 2 - readK ^ 2)
          + (pivotJ - pivotK) * (readJ ^ 2 - readK ^ 2)
          + 6 * (crossIJ * (readI * readJ) + crossIK * (readI * readK)
            + crossJK * (readJ * readK))) ^ 2 := by
        rw [centeredGramForm_eq_pairing]
    _ ≤ ((pivotI - pivotJ) ^ 2 + (pivotI - pivotK) ^ 2 + (pivotJ - pivotK) ^ 2
          + 6 * (crossIJ ^ 2 + crossIK ^ 2 + crossJK ^ 2))
        * ((readI ^ 2 - readJ ^ 2) ^ 2 + (readI ^ 2 - readK ^ 2) ^ 2
          + (readJ ^ 2 - readK ^ 2) ^ 2
          + 6 * ((readI * readJ) ^ 2 + (readI * readK) ^ 2
            + (readJ * readK) ^ 2)) := hcs
    _ = 2 * (3 * (pivotI ^ 2 + pivotJ ^ 2 + pivotK ^ 2
            + 2 * crossIJ ^ 2 + 2 * crossIK ^ 2 + 2 * crossJK ^ 2)
          - (pivotI + pivotJ + pivotK) ^ 2)
        * (readI ^ 2 + readJ ^ 2 + readK ^ 2) ^ 2 := by
        rw [← centeredSpread_eq_sq_pairing, sq_probe_pairing_eq]; ring

/-! ## 4. The threshold and its arithmetic

The sharp threshold is a parabola in the trace with minimum value two at trace
one.  Every claim about the cell subsuming its two parents is arithmetic on
that parabola.
-/

/-- **THE SHARP THRESHOLD.**  The bound the doubled spread must clear. -/
def sharpThreshold (pivotTrace : ℝ) : ℝ := pivotTrace ^ 2 - 2 * pivotTrace + 3

/-- The threshold is the shifted square, so it never falls below two. -/
theorem sharpThreshold_eq_shifted_sq (pivotTrace : ℝ) :
    sharpThreshold pivotTrace = (pivotTrace - 1) ^ 2 + 2 := by
  rw [sharpThreshold]; ring

/-- **The threshold never falls below two.**  This is the whole Frobenius
subsumption in one line. -/
theorem two_le_sharpThreshold (pivotTrace : ℝ) : 2 ≤ sharpThreshold pivotTrace := by
  rw [sharpThreshold_eq_shifted_sq]
  nlinarith [sq_nonneg (pivotTrace - 1)]

/-- **The threshold exceeds two away from trace one.**  So the sharp cell is
strictly stronger than the Frobenius cell at every trace but one. -/
theorem two_lt_sharpThreshold_of_ne_one {pivotTrace : ℝ} (hne : pivotTrace ≠ 1) :
    2 < sharpThreshold pivotTrace := by
  rw [sharpThreshold_eq_shifted_sq]
  have : 0 < (pivotTrace - 1) ^ 2 := by
    have : pivotTrace - 1 ≠ 0 := sub_ne_zero_of_ne hne
    positivity
  linarith

/-- The threshold is positive at every trace. -/
theorem sharpThreshold_pos (pivotTrace : ℝ) : 0 < sharpThreshold pivotTrace := by
  have := two_le_sharpThreshold pivotTrace; linarith

/-! ## 5. The root-free endgame

The centred bound plus the threshold gives the Gram form strictly below the
squared probe length, with no root taken anywhere.
-/

/-- **The centred bound closes without a root.**  From the centred bound and the
threshold, the Gram form sits strictly below the squared probe length.  The
proof compares squares and never extracts one. -/
theorem lt_of_centered_of_sharpThreshold
    {gramForm pivotTrace spread probeSq : ℝ}
    (hprobe : 0 < probeSq) (htrace : pivotTrace < 3)
    (hsharp : 2 * spread < sharpThreshold pivotTrace)
    (hcentered : (3 * gramForm - pivotTrace * probeSq) ^ 2
      ≤ 2 * (3 * spread - pivotTrace ^ 2) * probeSq ^ 2) :
    gramForm < probeSq := by
  have htracePos : (0 : ℝ) < 3 - pivotTrace := by linarith
  have hright : (0 : ℝ) < (3 - pivotTrace) * probeSq := mul_pos htracePos hprobe
  have hprobeSq : (0 : ℝ) < probeSq ^ 2 := by positivity
  have hgap : 2 * (3 * spread - pivotTrace ^ 2) < (3 - pivotTrace) ^ 2 := by
    rw [sharpThreshold] at hsharp; nlinarith [hsharp]
  have hscaled : 2 * (3 * spread - pivotTrace ^ 2) * probeSq ^ 2
      < (3 - pivotTrace) ^ 2 * probeSq ^ 2 := mul_lt_mul_of_pos_right hgap hprobeSq
  have hsq : (3 * gramForm - pivotTrace * probeSq) ^ 2
      < ((3 - pivotTrace) * probeSq) ^ 2 := by nlinarith [hcentered, hscaled]
  have hlin : 3 * gramForm - pivotTrace * probeSq < (3 - pivotTrace) * probeSq := by
    nlinarith [hsq, hright]
  linarith

/-! ## 6. The pivot trace of an omitted triple -/

/-- **THE PIVOT TRACE.**  The trace of the omitted labels' Gram matrix, which is
the sum of their full pivots. -/
noncomputable def pivotTrace (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) : ℝ :=
  fullPivot direction mass weight i + fullPivot direction mass weight j
    + fullPivot direction mass weight k

/-- The pivot trace is nonnegative. -/
theorem pivotTrace_nonneg (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size) : 0 ≤ pivotTrace direction mass weight i j k := by
  have hi := fullPivot_nonneg_of_boost direction mass weight huniv i (hboost i)
  have hj := fullPivot_nonneg_of_boost direction mass weight huniv j (hboost j)
  have hk := fullPivot_nonneg_of_boost direction mass weight huniv k (hboost k)
  rw [pivotTrace]; linarith

/-- **The squared trace never exceeds three times the spread.**  Cauchy--Schwarz
on the three pivots, plus the nonnegativity of the crosses.  This is what lets
the Frobenius cell hand the sharp cell its trace bound for free. -/
theorem sq_pivotTrace_le_three_mul_frobeniusSpread
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hboost : ∀ label, 0 ≤ mass label / weight label) (i j k : Fin size) :
    pivotTrace direction mass weight i j k ^ 2
      ≤ 3 * frobeniusSpread direction mass weight i j k := by
  have hcross : ∀ a b : Fin size, 0 ≤ pairBoostedCrossSq direction mass weight a b := by
    intro a b
    rw [pairBoostedCrossSq]
    have := mul_nonneg (hboost a) (hboost b)
    positivity
  rw [pivotTrace, frobeniusSpread]
  nlinarith [hcross i j, hcross i k, hcross j k,
    sq_nonneg (fullPivot direction mass weight i - fullPivot direction mass weight j),
    sq_nonneg (fullPivot direction mass weight i - fullPivot direction mass weight k),
    sq_nonneg (fullPivot direction mass weight j - fullPivot direction mass weight k)]

/-! ## 7. The cell -/

/-- **THE SHARP SPREAD CELL.**  An omitted triple whose pivot trace is below
three and whose doubled Frobenius spread clears the sharp threshold leaves a
strictly positive definite selection.

The proof reads the omitted sum as one combination, prices it by the resolvent
Cauchy--Schwarz, prices the resulting ternary Gram form by the CENTRED Frobenius
bound, and closes without taking a root.  No eigenvalue, no matrix square root,
no leading minor and no determinant appear. -/
theorem posDef_directionChartGap_compl_triple_of_sharpSpread
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (htrace : pivotTrace direction mass weight i j k < 3)
    (hsharp : 2 * frobeniusSpread direction mass weight i j k
      < sharpThreshold (pivotTrace direction mass weight i j k)) :
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
  have hcs := dotProduct_sq_le_inverseForm_mul_form huniv combination probe
  rw [hdot, ← hgram, ← hform] at hcs
  -- The centred bound, instantiated at the Gram entries.
  have hcent := sq_centeredGramForm_le_centeredSpread
    (fullPivot direction mass weight i) (fullPivot direction mass weight j)
    (fullPivot direction mass weight k)
    (boostedGram direction mass weight i j) (boostedGram direction mass weight i k)
    (boostedGram direction mass weight j k) readI readJ readK
  rw [sq_boostedGram direction mass weight (hboost i) (hboost j),
    sq_boostedGram direction mass weight (hboost i) (hboost k),
    sq_boostedGram direction mass weight (hboost j) (hboost k)] at hcent
  have hcentEq : (3 * gramForm
        - pivotTrace direction mass weight i j k * omittedTotal) ^ 2
      ≤ 2 * (3 * frobeniusSpread direction mass weight i j k
          - pivotTrace direction mass weight i j k ^ 2) * omittedTotal ^ 2 := by
    rw [hgramEq, pivotTrace, frobeniusSpread, homitted]
    calc (3 * (fullPivot direction mass weight i * readI ^ 2
              + fullPivot direction mass weight j * readJ ^ 2
              + fullPivot direction mass weight k * readK ^ 2
              + 2 * boostedGram direction mass weight i j * readI * readJ
              + 2 * boostedGram direction mass weight i k * readI * readK
              + 2 * boostedGram direction mass weight j k * readJ * readK)
            - (fullPivot direction mass weight i + fullPivot direction mass weight j
              + fullPivot direction mass weight k)
              * (readI ^ 2 + readJ ^ 2 + readK ^ 2)) ^ 2
        ≤ _ := hcent
      _ = _ := by ring
  rcases eq_or_lt_of_le homittedNonneg with hzero | hpos
  · rw [← hzero]; linarith
  · have hlt := lt_of_centered_of_sharpThreshold (gramForm := gramForm)
      (pivotTrace := pivotTrace direction mass weight i j k)
      (spread := frobeniusSpread direction mass weight i j k)
      (probeSq := omittedTotal) hpos htrace hsharp hcentEq
    nlinarith [hcs, hlt, hpos, hformPos]

/-! ## 8. The Frobenius cell is an instance

The threshold never falls below two, so a spread below one clears it at every
trace.  The trace hypothesis comes free from the squared-trace cap.
-/

/-- **The Frobenius cell fires the sharp cell.**  A spread below one gives both
the trace bound and the threshold, so the sharp cell subsumes it outright. -/
theorem sharpSpreadFires_of_frobeniusSpread_lt_one
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hboost : ∀ label, 0 ≤ mass label / weight label) (i j k : Fin size)
    (hspread : frobeniusSpread direction mass weight i j k < 1) :
    pivotTrace direction mass weight i j k < 3
      ∧ 2 * frobeniusSpread direction mass weight i j k
        < sharpThreshold (pivotTrace direction mass weight i j k) := by
  have hcap := sq_pivotTrace_le_three_mul_frobeniusSpread direction mass weight hboost i j k
  refine ⟨?_, ?_⟩
  · nlinarith [hcap, hspread,
      sq_nonneg (pivotTrace direction mass weight i j k - 3),
      sq_nonneg (pivotTrace direction mass weight i j k)]
  · rw [sharpThreshold_eq_shifted_sq]
    nlinarith [hspread, sq_nonneg (pivotTrace direction mass weight i j k - 1)]

/-- **The Frobenius spread cell factors through the sharp cell.** -/
theorem posDef_compl_triple_of_frobeniusSpread_via_sharp
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hspread : frobeniusSpread direction mass weight i j k < 1) :
    (directionChartGap direction mass weight
      (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef := by
  obtain ⟨htrace, hsharp⟩ :=
    sharpSpreadFires_of_frobeniusSpread_lt_one direction mass weight hboost i j k hspread
  exact posDef_directionChartGap_compl_triple_of_sharpSpread direction mass weight
    i j k hboost huniv hij hik hjk htrace hsharp

/-! ## 9. The trace bound is an instance

The landed cap says the spread never exceeds the square of the trace.  At trace
below one that closes the threshold, so every total-pivot cell in the corpus
factors through the sharp cell as well.
-/

/-- **The trace bound fires the sharp cell.**  The landed cap
`Gtz.frobeniusSpread_le_sq_sum_fullPivot` supplies the spread, and the parabola
does the rest. -/
theorem sharpSpreadFires_of_sum_fullPivot_lt_one
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j k : Fin size)
    (htotal : pivotTrace direction mass weight i j k < 1) :
    pivotTrace direction mass weight i j k < 3
      ∧ 2 * frobeniusSpread direction mass weight i j k
        < sharpThreshold (pivotTrace direction mass weight i j k) := by
  have hcap := frobeniusSpread_le_sq_sum_fullPivot direction mass weight hboost huniv i j k
  have hnn := pivotTrace_nonneg direction mass weight hboost huniv i j k
  rw [← pivotTrace] at hcap
  refine ⟨by linarith, ?_⟩
  rw [sharpThreshold]
  nlinarith [hcap, htotal, hnn]

/-- **The total-pivot cell factors through the sharp cell.**  Every total-pivot
cell in the corpus therefore factors through it, the pivot-third cell
included. -/
theorem posDef_compl_triple_of_sum_fullPivot_via_sharp
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (htotal : fullPivot direction mass weight i + fullPivot direction mass weight j
      + fullPivot direction mass weight k < 1) :
    (directionChartGap direction mass weight
      (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef := by
  have htrace : pivotTrace direction mass weight i j k < 1 := by rw [pivotTrace]; linarith
  obtain ⟨h3, hsharp⟩ := sharpSpreadFires_of_sum_fullPivot_lt_one direction mass weight
    hboost huniv i j k htrace
  exact posDef_directionChartGap_compl_triple_of_sharpSpread direction mass weight
    i j k hboost huniv hij hik hjk h3 hsharp

/-- **The pivot-third cell factors through the sharp cell too.** -/
theorem posDef_compl_triple_of_pivotThird_via_sharp
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
  posDef_compl_triple_of_sum_fullPivot_via_sharp direction mass weight
    i j k hboost huniv hij hik hjk (by linarith)

/-! ## 10. Where the sharp cell beats both parents

The gain is exactly the parabola.  At trace `t` the sharp cell admits spread up
to `(t ^ 2 - 2 * t + 3) / 2`, which is one at `t = 1` and strictly more
elsewhere.  The statement below exhibits the scalars; it is arithmetic on the
threshold and does not claim a realised chart point.
-/

/-- **The sharp cell fires where both parents are silent.**  At pivot trace
`3 / 2` a spread of `11 / 10` clears the sharp threshold, while the Frobenius
cell needs spread below one and the trace bound needs trace below one. -/
theorem sharp_fires_where_parents_are_silent :
    ∃ trace spread : ℝ,
      1 ≤ spread ∧ 1 ≤ trace ∧ trace < 3 ∧ 2 * spread < sharpThreshold trace := by
  refine ⟨3 / 2, 11 / 10, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [sharpThreshold]; norm_num

/-- **The admissible spread of the sharp cell never falls below the Frobenius
threshold.**  Half the sharp threshold is at least one at every trace. -/
theorem one_le_sharpThreshold_div_two (trace : ℝ) : 1 ≤ sharpThreshold trace / 2 := by
  have := two_le_sharpThreshold trace; linarith

/-- **And it strictly exceeds it away from trace one.** -/
theorem one_lt_sharpThreshold_div_two_of_ne_one {trace : ℝ} (hne : trace ≠ 1) :
    1 < sharpThreshold trace / 2 := by
  have := two_lt_sharpThreshold_of_ne_one hne; linarith

/-! ## 11. The design reading -/

/-- **The sharp cell at a design.**  A design is the chart point of its own atom
family, so the cell transports verbatim. -/
theorem posDef_subsetSum_compl_triple_of_sharpSpread {m : ℕ}
    (D : WeightedDesign m 3) (i j k : Fin m)
    (huniv : (directionChartGap D.atom (designChartPoint D).mass
      (designChartPoint D).weight Finset.univ).PosDef)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (htrace : pivotTrace D.atom (designChartPoint D).mass
      (designChartPoint D).weight i j k < 3)
    (hsharp : 2 * frobeniusSpread D.atom (designChartPoint D).mass
        (designChartPoint D).weight i j k
      < sharpThreshold (pivotTrace D.atom (designChartPoint D).mass
        (designChartPoint D).weight i j k)) :
    (subsetSum D (Finset.univ \ ({i, j, k} : Finset (Fin m))) - 1).PosDef := by
  have hboost : ∀ label, 0 ≤ (designChartPoint D).mass label
      / (designChartPoint D).weight label := by
    intro label
    have hpos := (designChartPoint D).mass_pos label
    have hwpos := (designChartPoint D).weight_pos label
    positivity
  have hchart := posDef_directionChartGap_compl_triple_of_sharpSpread D.atom
    (designChartPoint D).mass (designChartPoint D).weight i j k hboost huniv hij hik hjk
    htrace hsharp
  rwa [directionChartGap_designChartPoint D
    (Finset.univ \ ({i, j, k} : Finset (Fin m)))] at hchart

/-! ## 12. The covering statement -/

/-- The covering statement the sharp cell offers at a chart point. -/
def SharpSpreadCovers (direction : Fin 6 → (Fin 3 → ℝ)) : Prop :=
  ∀ point : DirectionChartPoint 6,
    ∃ i j k : Fin 6, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      pivotTrace direction point.mass point.weight i j k < 3 ∧
      2 * frobeniusSpread direction point.mass point.weight i j k
        < sharpThreshold (pivotTrace direction point.mass point.weight i j k)

/-- **The sharp cover produces a strict selection at every chart point.**  This
is the consumer interface for the sharp cell. -/
theorem exists_posDef_compl_triple_of_sharpSpreadCovers
    {direction : Fin 6 → (Fin 3 → ℝ)}
    (hcover : SharpSpreadCovers direction)
    (point : DirectionChartPoint 6)
    (huniv : (directionChartGap direction point.mass point.weight
      Finset.univ).PosDef) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap direction point.mass point.weight selected).PosDef := by
  obtain ⟨i, j, k, hij, hik, hjk, htrace, hsharp⟩ := hcover point
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
  · exact posDef_directionChartGap_compl_triple_of_sharpSpread direction point.mass
      point.weight i j k hboost huniv hij hik hjk htrace hsharp

/-- **The Frobenius cover implies the sharp cover.**  So whatever the Frobenius
cell covered, the sharp cell covers as well. -/
theorem sharpSpreadCovers_of_frobeniusSpreadCovers
    {direction : Fin 6 → (Fin 3 → ℝ)}
    (hcover : FrobeniusSpreadCovers direction) : SharpSpreadCovers direction := by
  intro point
  obtain ⟨i, j, k, hij, hik, hjk, hspread⟩ := hcover point
  have hboost : ∀ label, 0 ≤ point.mass label / point.weight label := by
    intro label
    have hpos := point.mass_pos label
    have hwpos := point.weight_pos label
    positivity
  obtain ⟨htrace, hsharp⟩ := sharpSpreadFires_of_frobeniusSpread_lt_one direction
    point.mass point.weight hboost i j k hspread
  exact ⟨i, j, k, hij, hik, hjk, htrace, hsharp⟩

end Gtz

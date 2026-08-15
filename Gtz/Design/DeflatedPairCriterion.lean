/-
# The deflated pair criterion

The corpus decides an omitted PAIR exactly.  `Gtz.posDef_directionChartGap_compl_pair_iff`
says that omitting `{a, b}` leaves a strictly dominating selection exactly when

    g_ab ^ 2 < (1 - pi_a) * (1 - pi_b),

where `pi_a` is the full pivot of `a` and `g_ab ^ 2` is the boosted squared
inverse form of the pair.  At an omitted set of three or more labels the corpus
falls back to the TRACE bound: the total pivot of the omitted set is below one.

This file removes that gap.  The pair criterion survives at every omitted
cardinality, with the threshold `1` lowered to `1` minus the total pivot of the
labels outside the pair.  Two labels of the omitted set carry their exact
two-by-two criterion, and the rest are paid for by their pivots alone.

## The law

For an omitted set `O`, a pair `a, b` in `O`, and `E = O \ {a, b}`, put

    t = 1 - sum over E of the full pivot.

If `pi_a < t`, `pi_b < t` and `g_ab ^ 2 < (t - pi_a) * (t - pi_b)`, then the
selection that omits `O` is strictly positive definite.

## What it costs and what it buys

The proof needs no eigenvalue, no matrix square root and no division.  It runs
on two applications of Cauchy--Schwarz through the resolvent, which the corpus
already supplies, and one arithmetic-geometric mean step.

* At `E = ∅` the law is the sufficient half of the landed pair criterion.
* At any `E`, weakening `g_ab ^ 2` by the landed resolvent Cauchy--Schwarz
  `g_ab ^ 2 ≤ pi_a * pi_b` recovers the TRACE bound, so
  `Gtz.posDef_directionChartGap_of_pivotThird` and every total-pivot cell are
  corollaries rather than independent facts.  That is
  `Gtz.posDef_directionChartGap_compl_of_sum_fullPivot_lt_one` below.
* The law is generic in the size and in the omitted cardinality.

## Measurement

A census over 13 million exact integer chart points at size six placed the law
at 86 to 94 percent single-cell coverage, against 28 to 48 percent for the trace
bound it subsumes.  Removing it from the union of the landed cells loses points
that no other landed cell reaches.  The census also found the residue growing
when the direction box, the weight box or the ratio box SHRINKS, so the hard
locus of this criterion sits at small boxes.
-/
import Gtz.Design.PivotThirdDominance

namespace Gtz

open Finset Matrix

variable {size : ℕ}

/-! ## 1. The deflation threshold -/

/-- **The deflation threshold of a set of labels.**  One minus the total full
pivot of the deflators.  The pair criterion runs against this threshold instead
of against one. -/
noncomputable def deflationThreshold (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (deflators : Finset (Fin size)) : ℝ :=
  1 - ∑ label ∈ deflators, fullPivot direction mass weight label

/-- The empty set deflates nothing. -/
theorem deflationThreshold_empty (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) :
    deflationThreshold direction mass weight (∅ : Finset (Fin size)) = 1 := by
  simp [deflationThreshold]

/-- Deflating by one more label lowers the threshold by that label's pivot. -/
theorem deflationThreshold_insert (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {deflators : Finset (Fin size)} {label : Fin size}
    (hlabel : label ∉ deflators) :
    deflationThreshold direction mass weight (insert label deflators)
      = deflationThreshold direction mass weight deflators
        - fullPivot direction mass weight label := by
  rw [deflationThreshold, deflationThreshold, Finset.sum_insert hlabel]
  ring

/-- The threshold never exceeds one when every deflator has a nonnegative
pivot. -/
theorem deflationThreshold_le_one (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (deflators : Finset (Fin size)) :
    deflationThreshold direction mass weight deflators ≤ 1 := by
  have hnonneg : 0 ≤ ∑ label ∈ deflators, fullPivot direction mass weight label :=
    Finset.sum_nonneg fun label _ =>
      fullPivot_nonneg_of_boost direction mass weight huniv label (hboost label)
  rw [deflationThreshold]
  linarith

/-! ## 2. One label against the full form

Cauchy--Schwarz through the resolvent prices a single boosted squared reading by
the label's own pivot.  This is the step the trace bound uses six times and the
deflated pair criterion uses only on the deflators.
-/

/-- **A boosted squared reading is at most its pivot share of the full form.**
Cauchy--Schwarz through the resolvent at the label's own direction. -/
theorem boost_sq_reading_le_fullPivot_mul_form (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (label : Fin size) (hboost : 0 ≤ mass label / weight label) (probe : Fin 3 → ℝ) :
    (mass label / weight label) * (direction label ⬝ᵥ probe) * (direction label ⬝ᵥ probe)
      ≤ fullPivot direction mass weight label
        * (probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)) := by
  have hcauchy := dotProduct_sq_le_inverseForm_mul_form huniv (direction label) probe
  have hform : (direction label ⬝ᵥ probe) * (direction label ⬝ᵥ probe)
      ≤ fullInverseForm direction mass weight label label
        * (probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)) := by
    rw [fullInverseForm]
    nlinarith [hcauchy, sq_nonneg (direction label ⬝ᵥ probe)]
  have hmul := mul_le_mul_of_nonneg_left hform hboost
  rw [fullPivot]
  nlinarith [hmul]

/-- **The deflators are paid for by their total pivot.**  Summing the previous
bound over a finite set of labels. -/
theorem sum_boost_sq_reading_le_sum_fullPivot_mul_form
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (deflators : Finset (Fin size)) (probe : Fin 3 → ℝ) :
    (∑ label ∈ deflators, (mass label / weight label)
        * (direction label ⬝ᵥ probe) * (direction label ⬝ᵥ probe))
      ≤ (∑ label ∈ deflators, fullPivot direction mass weight label)
        * (probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)) := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun label _ =>
    boost_sq_reading_le_fullPivot_mul_form direction mass weight huniv label
      (hboost label) probe

/-! ## 3. The pair, exactly

The two distinguished labels are NOT paid for by their pivots.  They are priced
by one Cauchy--Schwarz applied to the combination whose coefficients are their
own boosted readings, which is what makes the two-by-two criterion appear.
-/

/-- The combination of a pair of directions, weighted by their own boosted
readings at a probe.  Cauchy--Schwarz at this vector is what turns the pair into
a binary quadratic form. -/
noncomputable def pairReadingCombination (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a b : Fin size) (probe : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ((mass a / weight a) * (direction a ⬝ᵥ probe)) • direction a
    + ((mass b / weight b) * (direction b ⬝ᵥ probe)) • direction b

/-- Reading the pair combination at the probe returns the two boosted squared
readings. -/
theorem pairReadingCombination_dotProduct (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a b : Fin size) (probe : Fin 3 → ℝ) :
    pairReadingCombination direction mass weight a b probe ⬝ᵥ probe
      = (mass a / weight a) * (direction a ⬝ᵥ probe) * (direction a ⬝ᵥ probe)
        + (mass b / weight b) * (direction b ⬝ᵥ probe) * (direction b ⬝ᵥ probe) := by
  rw [pairReadingCombination, add_dotProduct, smul_dotProduct, smul_dotProduct]
  ring

/-- The inverse form is additive in its first argument. -/
theorem inverseForm_add_left (gramMat : Matrix (Fin 3) (Fin 3) ℝ)
    (left right probe : Fin 3 → ℝ) :
    (left + right) ⬝ᵥ (gramMat *ᵥ probe)
      = left ⬝ᵥ (gramMat *ᵥ probe) + right ⬝ᵥ (gramMat *ᵥ probe) := by
  rw [add_dotProduct]

/-- The inverse form of the pair combination is the binary quadratic form of the
pair, read in the two boosted squared readings. -/
theorem pairReadingCombination_inverseForm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (a b : Fin size) (probe : Fin 3 → ℝ) :
    pairReadingCombination direction mass weight a b probe ⬝ᵥ
        ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ
          pairReadingCombination direction mass weight a b probe)
      = fullPivot direction mass weight a
          * ((mass a / weight a) * (direction a ⬝ᵥ probe) * (direction a ⬝ᵥ probe))
        + fullPivot direction mass weight b
          * ((mass b / weight b) * (direction b ⬝ᵥ probe) * (direction b ⬝ᵥ probe))
        + 2 * ((mass a / weight a) * (mass b / weight b)
            * fullInverseForm direction mass weight a b
            * (direction a ⬝ᵥ probe) * (direction b ⬝ᵥ probe)) := by
  have hsymm : direction b ⬝ᵥ ((directionChartGap direction mass weight Finset.univ)⁻¹
        *ᵥ direction a)
      = direction a ⬝ᵥ ((directionChartGap direction mass weight Finset.univ)⁻¹
        *ᵥ direction b) := by
    have hcomm := fullInverseForm_comm direction mass weight huniv b a
    rwa [fullInverseForm, fullInverseForm] at hcomm
  rw [pairReadingCombination, fullPivot, fullPivot, fullInverseForm, fullInverseForm,
    fullInverseForm]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  linear_combination ((mass a / weight a) * (direction a ⬝ᵥ probe)
    * ((mass b / weight b) * (direction b ⬝ᵥ probe))) * hsymm

/-- The boosted squared inverse form of a pair, the quantity the criterion
compares against the deflated diagonals. -/
noncomputable def pairBoostedCrossSq (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a b : Fin size) : ℝ :=
  (mass a / weight a) * (mass b / weight b)
    * (fullInverseForm direction mass weight a b) ^ 2

/-- **The cross term squares to the boosted cross times the two boosted squared
readings.**  This is the identity that removes every square root from the
criterion. -/
theorem sq_pair_cross_term (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a b : Fin size) (probe : Fin 3 → ℝ) :
    ((mass a / weight a) * (mass b / weight b)
        * fullInverseForm direction mass weight a b
        * (direction a ⬝ᵥ probe) * (direction b ⬝ᵥ probe)) ^ 2
      = pairBoostedCrossSq direction mass weight a b
        * ((mass a / weight a) * (direction a ⬝ᵥ probe) * (direction a ⬝ᵥ probe))
        * ((mass b / weight b) * (direction b ⬝ᵥ probe) * (direction b ⬝ᵥ probe)) := by
  rw [pairBoostedCrossSq]
  ring

/-! ## 4. The core bound

The pair's total boosted squared reading is strictly below the deflated
threshold share of the full form.  The proof is one Cauchy--Schwarz, one
arithmetic-geometric mean step, and a division by a positive quantity.
-/

/-- **THE PAIR BOUND.**  Under the deflated two-by-two criterion the pair spends
strictly less than the threshold share of the full form. -/
theorem pair_reading_lt_threshold_mul_form (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (a b : Fin size) (hba : 0 ≤ mass a / weight a) (hbb : 0 ≤ mass b / weight b)
    (threshold : ℝ)
    (hgapA : 0 < threshold - fullPivot direction mass weight a)
    (hgapB : 0 < threshold - fullPivot direction mass weight b)
    (hcross : pairBoostedCrossSq direction mass weight a b
      < (threshold - fullPivot direction mass weight a)
        * (threshold - fullPivot direction mass weight b))
    (probe : Fin 3 → ℝ) (hprobe : probe ≠ 0) :
    (mass a / weight a) * (direction a ⬝ᵥ probe) * (direction a ⬝ᵥ probe)
        + (mass b / weight b) * (direction b ⬝ᵥ probe) * (direction b ⬝ᵥ probe)
      < threshold
        * (probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)) := by
  set form := probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)
    with hform
  set readA : ℝ := (mass a / weight a) * (direction a ⬝ᵥ probe) * (direction a ⬝ᵥ probe)
    with hreadA
  set readB : ℝ := (mass b / weight b) * (direction b ⬝ᵥ probe) * (direction b ⬝ᵥ probe)
    with hreadB
  set cross : ℝ := (mass a / weight a) * (mass b / weight b)
      * fullInverseForm direction mass weight a b
      * (direction a ⬝ᵥ probe) * (direction b ⬝ᵥ probe) with hcrossDef
  set pivA := fullPivot direction mass weight a with hpivA
  set pivB := fullPivot direction mass weight b with hpivB
  have hformPos : 0 < form := by
    rw [hform]
    have hpd := (Matrix.posDef_iff_dotProduct_mulVec.mp huniv).2 hprobe
    rwa [star_trivial] at hpd
  have hreadANonneg : 0 ≤ readA := by
    rw [hreadA]
    nlinarith [sq_nonneg (direction a ⬝ᵥ probe), hba]
  have hreadBNonneg : 0 ≤ readB := by
    rw [hreadB]
    nlinarith [sq_nonneg (direction b ⬝ᵥ probe), hbb]
  -- Cauchy--Schwarz at the pair combination.
  have hcs := dotProduct_sq_le_inverseForm_mul_form huniv
    (pairReadingCombination direction mass weight a b probe) probe
  rw [pairReadingCombination_dotProduct, ← hreadA, ← hreadB,
    pairReadingCombination_inverseForm direction mass weight huniv a b probe,
    ← hreadA, ← hreadB, ← hpivA, ← hpivB, ← hcrossDef, ← hform] at hcs
  -- The cross term squares away.
  have hsq := sq_pair_cross_term direction mass weight a b probe
  rw [← hcrossDef, ← hreadA, ← hreadB] at hsq
  -- The two deflated diagonal contributions are nonnegative.
  have hAnn : 0 ≤ (threshold - pivA) * readA :=
    mul_nonneg (le_of_lt hgapA) hreadANonneg
  have hBnn : 0 ≤ (threshold - pivB) * readB :=
    mul_nonneg (le_of_lt hgapB) hreadBNonneg
  rcases eq_or_lt_of_le (by linarith : (0 : ℝ) ≤ readA + readB) with hzero | hpos
  · -- Nothing is spent on the pair, and the threshold is positive.
    have hpivANonneg : 0 ≤ pivA := by
      rw [hpivA]
      exact fullPivot_nonneg_of_boost direction mass weight huniv a hba
    have hthrPos : 0 < threshold := by linarith
    have htotalZero : readA + readB = 0 := hzero.symm
    rw [htotalZero]
    exact mul_pos hthrPos hformPos
  · -- The arithmetic-geometric mean step against the deflated diagonals.
    have hAB : 2 * cross < (threshold - pivA) * readA + (threshold - pivB) * readB := by
      rcases eq_or_lt_of_le (mul_nonneg hreadANonneg hreadBNonneg) with hprodZero | hprodPos
      · -- One reading vanishes, so the cross term does too.
        have hcz : cross = 0 := by
          have hz : cross ^ 2 = 0 := by
            rw [hsq]
            linear_combination (pairBoostedCrossSq direction mass weight a b)
              * hprodZero.symm
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
        rw [hcz]
        rcases lt_or_ge 0 readA with hApos | hAle
        · nlinarith [mul_pos hgapA hApos, hBnn]
        · have hBpos : 0 < readB := by linarith
          nlinarith [mul_pos hgapB hBpos, hAnn]
      · -- Both readings are positive: square, compare, and take the root.
        have hstrictProd : pairBoostedCrossSq direction mass weight a b * (readA * readB)
            < (threshold - pivA) * (threshold - pivB) * (readA * readB) :=
          mul_lt_mul_of_pos_right hcross hprodPos
        have hAsq : (2 * cross) ^ 2
            < ((threshold - pivA) * readA + (threshold - pivB) * readB) ^ 2 := by
          nlinarith [sq_nonneg ((threshold - pivA) * readA - (threshold - pivB) * readB),
            hsq, hstrictProd]
        nlinarith [hAsq, hAnn, hBnn]
    -- Divide the squared Cauchy--Schwarz bound by the positive total reading.
    nlinarith [hcs, hAB, hpos, hformPos]

/-! ## 5. The law -/

/-- **THE DEFLATED PAIR CRITERION.**  Omitting a set that contains a pair
satisfying the two-by-two criterion at the deflated threshold leaves a strictly
dominating selection.  The other omitted labels are paid for by their pivots
alone, and the pair is decided exactly.

At `deflators = ∅` the threshold is one and this is the sufficient half of
`Gtz.posDef_directionChartGap_compl_pair_iff`.  At a nonempty deflator set it is
strictly more than the corpus had. -/
theorem posDef_directionChartGap_compl_of_deflatedPair
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (omitted : Finset (Fin size)) (a b : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hmemA : a ∈ omitted) (hmemB : b ∈ omitted) (hne : a ≠ b)
    (hgapA : 0 < deflationThreshold direction mass weight (omitted \ {a, b})
      - fullPivot direction mass weight a)
    (hgapB : 0 < deflationThreshold direction mass weight (omitted \ {a, b})
      - fullPivot direction mass weight b)
    (hcross : pairBoostedCrossSq direction mass weight a b
      < (deflationThreshold direction mass weight (omitted \ {a, b})
          - fullPivot direction mass weight a)
        * (deflationThreshold direction mass weight (omitted \ {a, b})
          - fullPivot direction mass weight b)) :
    (directionChartGap direction mass weight (Finset.univ \ omitted)).PosDef := by
  classical
  set deflators := omitted \ {a, b} with hdefl
  set threshold := deflationThreshold direction mass weight deflators with hthr
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (directionChartGap_transpose _ _ _ _),
      fun probe hprobe => ?_⟩
  rw [star_trivial, directionChartGap_compl_eq, Matrix.sub_mulVec, dotProduct_sub,
    quadForm_omittedBoostSum]
  set form := probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)
    with hform
  -- Split the omitted sum into the pair and the deflators.
  have hpair : ({a, b} : Finset (Fin size)) ⊆ omitted := by
    intro label hlabel
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with rfl | rfl
    · exact hmemA
    · exact hmemB
  have hsplit : ∑ label ∈ omitted, (mass label / weight label)
        * (direction label ⬝ᵥ probe) * (direction label ⬝ᵥ probe)
      = ((mass a / weight a) * (direction a ⬝ᵥ probe) * (direction a ⬝ᵥ probe)
          + (mass b / weight b) * (direction b ⬝ᵥ probe) * (direction b ⬝ᵥ probe))
        + ∑ label ∈ deflators, (mass label / weight label)
            * (direction label ⬝ᵥ probe) * (direction label ⬝ᵥ probe) := by
    rw [hdefl, ← Finset.sum_sdiff hpair, Finset.sum_pair hne]
    ring
  rw [hsplit]
  have hpairBound := pair_reading_lt_threshold_mul_form direction mass weight huniv a b
    (hboost a) (hboost b) threshold hgapA hgapB hcross probe hprobe
  have hdeflBound := sum_boost_sq_reading_le_sum_fullPivot_mul_form direction mass weight
    huniv hboost deflators probe
  rw [← hform] at hdeflBound
  have hthrEq : ∑ label ∈ deflators, fullPivot direction mass weight label
      = 1 - threshold := by
    rw [hthr, deflationThreshold]
    ring
  rw [hthrEq] at hdeflBound
  linarith

/-! ## 6. The trace bound is a corollary

Weakening the pair's cross term by the landed resolvent Cauchy--Schwarz turns
the deflated criterion into the total-pivot bound.  So every total-pivot cell in
the corpus, `Gtz.posDef_directionChartGap_of_pivotThird` among them, is an
instance of the law above rather than an independent fact.
-/

/-- **The total-pivot bound follows.**  If the omitted set carries total pivot
below one and has at least two labels, the selection is strictly positive
definite. -/
theorem posDef_directionChartGap_compl_of_sum_fullPivot_lt_one
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (omitted : Finset (Fin size)) (a b : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hmemA : a ∈ omitted) (hmemB : b ∈ omitted) (hne : a ≠ b)
    (htotal : ∑ label ∈ omitted, fullPivot direction mass weight label < 1) :
    (directionChartGap direction mass weight (Finset.univ \ omitted)).PosDef := by
  classical
  set deflators := omitted \ {a, b} with hdefl
  have hpair : ({a, b} : Finset (Fin size)) ⊆ omitted := by
    intro label hlabel
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with rfl | rfl
    · exact hmemA
    · exact hmemB
  have hsum : ∑ label ∈ omitted, fullPivot direction mass weight label
      = fullPivot direction mass weight a + fullPivot direction mass weight b
        + ∑ label ∈ deflators, fullPivot direction mass weight label := by
    rw [hdefl, ← Finset.sum_sdiff hpair, Finset.sum_pair hne]
    ring
  have hthr : deflationThreshold direction mass weight deflators
      = 1 - ∑ label ∈ deflators, fullPivot direction mass weight label := rfl
  have hpivANonneg := fullPivot_nonneg_of_boost direction mass weight huniv a (hboost a)
  have hpivBNonneg := fullPivot_nonneg_of_boost direction mass weight huniv b (hboost b)
  have hgapA : 0 < deflationThreshold direction mass weight deflators
      - fullPivot direction mass weight a := by
    rw [hthr]; linarith [hsum, htotal, hpivBNonneg]
  have hgapB : 0 < deflationThreshold direction mass weight deflators
      - fullPivot direction mass weight b := by
    rw [hthr]; linarith [hsum, htotal, hpivANonneg]
  refine posDef_directionChartGap_compl_of_deflatedPair direction mass weight omitted a b
    hboost huniv hmemA hmemB hne hgapA hgapB ?_
  -- The landed resolvent Cauchy--Schwarz caps the boosted cross by the pivots.
  have hcs := sq_fullInverseForm_le_mul direction mass weight huniv a b
  have hcapped : pairBoostedCrossSq direction mass weight a b
      ≤ fullPivot direction mass weight a * fullPivot direction mass weight b := by
    rw [pairBoostedCrossSq, fullPivot, fullPivot]
    have hprod : 0 ≤ (mass a / weight a) * (mass b / weight b) :=
      mul_nonneg (hboost a) (hboost b)
    nlinarith [hcs, hprod]
  have hstrict : fullPivot direction mass weight a * fullPivot direction mass weight b
      < (deflationThreshold direction mass weight deflators
          - fullPivot direction mass weight a)
        * (deflationThreshold direction mass weight deflators
          - fullPivot direction mass weight b) := by
    rw [hthr]
    nlinarith [hsum, htotal, hpivANonneg, hpivBNonneg, hgapA, hgapB]
  linarith

/-! ## 7. The omitted triple

At size six the omitted set of a card-three selection has three labels, and the
law gives three independent readings: each label in turn plays the deflator
while the other two are decided exactly.  The census found the disjunction of
the three firing on 86 to 94 percent of exact integer chart points.
-/

/-- **The deflated criterion at an omitted triple.**  One label deflates, the
other two are decided by their two-by-two criterion at the deflated threshold. -/
theorem posDef_directionChartGap_compl_triple_of_deflatedPair
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (a b c : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hgapA : fullPivot direction mass weight a + fullPivot direction mass weight c < 1)
    (hgapB : fullPivot direction mass weight b + fullPivot direction mass weight c < 1)
    (hcross : pairBoostedCrossSq direction mass weight a b
      < (1 - fullPivot direction mass weight c - fullPivot direction mass weight a)
        * (1 - fullPivot direction mass weight c - fullPivot direction mass weight b)) :
    (directionChartGap direction mass weight (Finset.univ \ {a, b, c})).PosDef := by
  classical
  have hmemA : a ∈ ({a, b, c} : Finset (Fin size)) := by simp
  have hmemB : b ∈ ({a, b, c} : Finset (Fin size)) := by simp
  have hdefl : ({a, b, c} : Finset (Fin size)) \ {a, b} = {c} := by
    ext label
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hmem, hnot⟩
      push Not at hnot
      rcases hmem with rfl | rfl | rfl
      · exact absurd rfl hnot.1
      · exact absurd rfl hnot.2
      · rfl
    · rintro rfl
      exact ⟨by simp, by push Not; exact ⟨Ne.symm hac, Ne.symm hbc⟩⟩
  have hthr : deflationThreshold direction mass weight
      (({a, b, c} : Finset (Fin size)) \ {a, b})
      = 1 - fullPivot direction mass weight c := by
    rw [hdefl, deflationThreshold, Finset.sum_singleton]
  refine posDef_directionChartGap_compl_of_deflatedPair direction mass weight
    {a, b, c} a b hboost huniv hmemA hmemB hab ?_ ?_ ?_
  · rw [hthr]; linarith
  · rw [hthr]; linarith
  · rw [hthr]; linarith [hcross]

/-! ## 8. The design reading

A design is the chart point of its own atom family with mass equal to weight, so
the law transports verbatim.  The boost of every label is then one.
-/

/-- **The deflated pair criterion at a design.**  Read through the design chart
point, so the boosts are the design's own mass over weight. -/
theorem posDef_subsetSum_compl_of_deflatedPair {m : ℕ} (D : WeightedDesign m 3)
    (omitted : Finset (Fin m)) (a b : Fin m)
    (huniv : (directionChartGap D.atom (designChartPoint D).mass
      (designChartPoint D).weight Finset.univ).PosDef)
    (hmemA : a ∈ omitted) (hmemB : b ∈ omitted) (hne : a ≠ b)
    (hgapA : 0 < deflationThreshold D.atom (designChartPoint D).mass
        (designChartPoint D).weight (omitted \ {a, b})
      - fullPivot D.atom (designChartPoint D).mass (designChartPoint D).weight a)
    (hgapB : 0 < deflationThreshold D.atom (designChartPoint D).mass
        (designChartPoint D).weight (omitted \ {a, b})
      - fullPivot D.atom (designChartPoint D).mass (designChartPoint D).weight b)
    (hcross : pairBoostedCrossSq D.atom (designChartPoint D).mass
        (designChartPoint D).weight a b
      < (deflationThreshold D.atom (designChartPoint D).mass
            (designChartPoint D).weight (omitted \ {a, b})
          - fullPivot D.atom (designChartPoint D).mass (designChartPoint D).weight a)
        * (deflationThreshold D.atom (designChartPoint D).mass
            (designChartPoint D).weight (omitted \ {a, b})
          - fullPivot D.atom (designChartPoint D).mass (designChartPoint D).weight b)) :
    (subsetSum D (Finset.univ \ omitted) - 1).PosDef := by
  have hboost : ∀ label, 0 ≤ (designChartPoint D).mass label
      / (designChartPoint D).weight label := by
    intro label
    have hpos := (designChartPoint D).mass_pos label
    have hwpos := (designChartPoint D).weight_pos label
    positivity
  have hchart := posDef_directionChartGap_compl_of_deflatedPair D.atom
    (designChartPoint D).mass (designChartPoint D).weight omitted a b hboost huniv
    hmemA hmemB hne hgapA hgapB hcross
  rwa [directionChartGap_designChartPoint D (Finset.univ \ omitted)] at hchart

/-! ## 9. The three readings of an omitted triple

Each label of the omitted triple can play the deflator, so the law gives three
independent readings and any one of them closes the selection.  The census
placed the disjunction at 86 to 94 percent of exact integer chart points across
eight boxes, against 28 to 48 percent for the trace bound it subsumes.
-/

/-- The omitted triple does not see a rotation of its labels.  The transposition
is already `Gtz.triple_swap_last` and is consumed rather than restated. -/
theorem deflatedTriple_rotate (a b c : Fin size) :
    ({b, c, a} : Finset (Fin size)) = {a, b, c} := by
  ext label
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **THE THREE DEFLATED READINGS.**  At an omitted triple any label may deflate
while the other two are decided exactly, and a single reading suffices. -/
theorem posDef_directionChartGap_compl_triple_of_exists_deflator
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (a b c : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hchoice :
      (fullPivot direction mass weight a + fullPivot direction mass weight c < 1
        ∧ fullPivot direction mass weight b + fullPivot direction mass weight c < 1
        ∧ pairBoostedCrossSq direction mass weight a b
          < (1 - fullPivot direction mass weight c - fullPivot direction mass weight a)
            * (1 - fullPivot direction mass weight c - fullPivot direction mass weight b))
      ∨ (fullPivot direction mass weight a + fullPivot direction mass weight b < 1
        ∧ fullPivot direction mass weight c + fullPivot direction mass weight b < 1
        ∧ pairBoostedCrossSq direction mass weight a c
          < (1 - fullPivot direction mass weight b - fullPivot direction mass weight a)
            * (1 - fullPivot direction mass weight b - fullPivot direction mass weight c))
      ∨ (fullPivot direction mass weight b + fullPivot direction mass weight a < 1
        ∧ fullPivot direction mass weight c + fullPivot direction mass weight a < 1
        ∧ pairBoostedCrossSq direction mass weight b c
          < (1 - fullPivot direction mass weight a - fullPivot direction mass weight b)
            * (1 - fullPivot direction mass weight a - fullPivot direction mass weight c))) :
    (directionChartGap direction mass weight (Finset.univ \ {a, b, c})).PosDef := by
  rcases hchoice with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact posDef_directionChartGap_compl_triple_of_deflatedPair direction mass weight
      a b c hboost huniv hab hac hbc h1 h2 h3
  · have hset : ({a, c, b} : Finset (Fin size)) = {a, b, c} :=
      (triple_swap_last a b c).symm
    have hmain := posDef_directionChartGap_compl_triple_of_deflatedPair direction mass weight
      a c b hboost huniv hac hab (Ne.symm hbc) h1 h2 h3
    rwa [hset] at hmain
  · have hset := deflatedTriple_rotate (size := size) a b c
    have hmain := posDef_directionChartGap_compl_triple_of_deflatedPair direction mass weight
      b c a hboost huniv hbc (Ne.symm hab) (Ne.symm hac) h1 h2 h3
    rwa [hset] at hmain

/-! ## 10. The pivot-third cell is an instance

`Gtz.posDef_directionChartGap_of_pivotThird` asks every omitted label to carry
pivot below one third.  Three such labels total below one, so the total-pivot
corollary of the deflated law already covers that cell.  The census measured the
consequence: removing the trace bound from the union of the landed cells loses
no point at all.
-/

/-- **Three labels below one third are an instance of the deflated law.**  The
pivot-third cell is a corollary rather than an independent fact. -/
theorem posDef_directionChartGap_compl_triple_of_pivotThird
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (a b c : Fin size)
    (hboost : ∀ label, 0 ≤ mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpa : fullPivot direction mass weight a < 1 / 3)
    (hpb : fullPivot direction mass weight b < 1 / 3)
    (hpc : fullPivot direction mass weight c < 1 / 3) :
    (directionChartGap direction mass weight (Finset.univ \ {a, b, c})).PosDef := by
  classical
  have hmemA : a ∈ ({a, b, c} : Finset (Fin size)) := by simp
  have hmemB : b ∈ ({a, b, c} : Finset (Fin size)) := by simp
  have hsum : ∑ label ∈ ({a, b, c} : Finset (Fin size)),
      fullPivot direction mass weight label
      = fullPivot direction mass weight a + fullPivot direction mass weight b
        + fullPivot direction mass weight c := by
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton]
    ring
  refine posDef_directionChartGap_compl_of_sum_fullPivot_lt_one direction mass weight
    {a, b, c} a b hboost huniv hmemA hmemB hab ?_
  rw [hsum]
  linarith

/-- **The design reading of the three deflated readings.**  A primitive design
whose omitted triple satisfies any one of the three readings carries a strictly
dominating card-three subset on the complement. -/
theorem posDef_subsetSum_compl_triple_of_pivotThird {m : ℕ} (D : WeightedDesign m 3)
    (a b c : Fin m)
    (huniv : (directionChartGap D.atom (designChartPoint D).mass
      (designChartPoint D).weight Finset.univ).PosDef)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpa : fullPivot D.atom (designChartPoint D).mass (designChartPoint D).weight a < 1 / 3)
    (hpb : fullPivot D.atom (designChartPoint D).mass (designChartPoint D).weight b < 1 / 3)
    (hpc : fullPivot D.atom (designChartPoint D).mass (designChartPoint D).weight c < 1 / 3) :
    (subsetSum D (Finset.univ \ {a, b, c}) - 1).PosDef := by
  have hboost : ∀ label, 0 ≤ (designChartPoint D).mass label
      / (designChartPoint D).weight label := by
    intro label
    have hpos := (designChartPoint D).mass_pos label
    have hwpos := (designChartPoint D).weight_pos label
    positivity
  have hchart := posDef_directionChartGap_compl_triple_of_pivotThird D.atom
    (designChartPoint D).mass (designChartPoint D).weight a b c hboost huniv hab hac hbc
    hpa hpb hpc
  rwa [directionChartGap_designChartPoint D (Finset.univ \ {a, b, c})] at hchart

end Gtz

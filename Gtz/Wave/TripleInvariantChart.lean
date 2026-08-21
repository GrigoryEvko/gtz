/-
# The three invariants of a triple, and the complementary volume law at `(6,3)`

A triple's weighted atom sum `W_C = ∑_{c ∈ C} t_c g_c g_cᵀ` is a `3 × 3` matrix
with three elementary symmetric functions, and Cauchy-Binet names all three in
the campaign's own vocabulary:

  **`Gtz.trace_tripleAtomCombo`**  `tr W_C = ∑_{c ∈ C} t_c·l_c` ,
  **`Gtz.secondMinorSum_tripleAtomCombo`**  `e₂ W_C = ∑_{p < q ⊆ C} t_p·t_q·w_pq` ,
  **`Gtz.det_tripleAtomCombo`**  `det W_C = (∏_{c ∈ C} t_c)·[g_C]²` .

Write `A_C` for the first, `B_C` for the second and `V_C` for the third.  All
three are `Matrix.det_fin_three` and `ring`.

## The floor

Parseval says `1 − W_C` is the weighted atom sum of the OUTSIDE atoms, hence
positive semidefinite, hence of nonnegative determinant.  Expanding that
determinant (`Gtz.det_one_sub_eq`) gives, at every `(m,3)` design and every
triple:

  **`Gtz.triple_share_add_volume_le_one_add_areaSum`:**
  `A_C + V_C ≤ 1 + B_C` .

This is the triple sibling of the landed pair floor
`t_p·l_p + t_q·l_q ≤ 1 + t_p·t_q·w_pq`, and it has the same shape one dimension
up.  Against the landed pair CEILING `2·t_p·t_q·w_pq ≤ t_p·l_p + t_q·l_q`,
summed over the three pairs of the triple, it pins

  **`Gtz.triple_deficit_mem_unit_interval`:**  `0 ≤ A_C − B_C ≤ 1 − V_C` ,

so `V_C ≤ 1` at every triple with no budget argument at all.

## The complementary volume law at `(6,3)`

At `m = 6` the complement of a triple is a TRIPLE, so `1 − W_C = W_{Cᶜ}` and the
determinant expansion becomes an identity between the two complementary volumes:

  **`Gtz.complementary_triple_volume_law_sixThree`:**
  `V_C + V_{Cᶜ} = 1 − A_C + B_C` .

Ten such identities, one for each complementary pair of triples.  Two immediate
consequences, both new and both about the campaign's own size:

* **`Gtz.both_degenerate_iff_share_eq_one_add_areaSum_sixThree`.**  A triple and
  its complement are SIMULTANEOUSLY degenerate exactly when `A_C = 1 + B_C`.  So
  the two coplanarities of a `(6,3)` design come in complementary pairs and are
  detected by one scalar equation in the triple's own shares and squared areas.

* **`Gtz.weight_prod_le_one_sub_share_add_areaSum_of_dominates`.**  A weak
  dominator has squared volume at least one, so its weight product is capped:
  `∏_{c ∈ C} t_c ≤ 1 − A_C + B_C`.  At `(6,3)` this is a cap on the weights of
  every weak dominator of every tie, read off the dominator's own data.

## At `(5,3)`

The complement of a triple is a PAIR, whose weighted atom sum is singular, so the
identity loses its second volume:

  **`Gtz.triple_volume_eq_of_size_five`:**  `V_C = 1 − A_C + B_C` ,

and a triple of a `(5,3)` design is degenerate exactly when `A_C = 1 + B_C`
(`Gtz.degenerate_iff_share_eq_one_add_areaSum_fiveThree`).  This determines every
one of the ten volumes from pair data alone, with the two atoms outside the
triple cancelled.

[MEASURED, exact rational arithmetic on the `(5,3)` diamond (`K4 − e`,
conductances `(2,3,3,3,3)`, uniform weight `1/5`).  At the triple `{0,1,2}`:
`A = 2/5 + 13/20 + 13/20 = 17/10`, `B = (5 + 5 + 10)/25 = 4/5`, so
`1 − A + B = 1/10`, and `V = (1/125)·12.5 = 1/10` — equal.  At the rim triple
`{1,2,3}`: `A = 39/20`, `B = (10 + 15/2 + 10)/25 = 11/10`, `1 − A + B = 3/20`,
and `V = (1/125)·18.75 = 3/20` — equal.  At the cycle triple `{0,1,3}`, whose
three edges form a triangle of the graph: `A = 17/10`, `B = (5 + 5 + 15/2)/25 =
7/10`, `1 − A + B = 0`, and the bracket vanishes — equality in the floor, and
the degeneracy criterion fires exactly there.  The same holds at `{0,2,4}`, the
other triangle.  Those two triples are exactly the two of the ten that fail to
dominate.]
-/
import Gtz.Wave.TripleVolumeRowLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The three invariants of three scaled atoms -/

/-- **THE FIRST INVARIANT.**  The trace of a triple's weighted atom sum is the
sum of its three shares. -/
theorem trace_tripleAtomCombo (firstScale secondScale thirdScale : ℝ)
    (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    Matrix.trace (firstScale • atomMatrix firstVec + secondScale • atomMatrix secondVec
        + thirdScale • atomMatrix thirdVec)
      = firstScale * leverageOf firstVec + secondScale * leverageOf secondVec
        + thirdScale * leverageOf thirdVec := by
  simp only [Matrix.trace_fin_three, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    atomMatrix, Matrix.vecMulVec_apply, leverageOf, Fin.sum_univ_three]
  ring

/-- **THE SECOND INVARIANT.**  The sum of the three principal two-by-two minors
of a triple's weighted atom sum is the weighted total of its three pairs' squared
areas.  Cauchy-Binet at the middle compound, written out. -/
theorem secondMinorSum_tripleAtomCombo (firstScale secondScale thirdScale : ℝ)
    (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    secondMinorSum (firstScale • atomMatrix firstVec + secondScale • atomMatrix secondVec
        + thirdScale • atomMatrix thirdVec)
      = firstScale * secondScale * crossNormSq firstVec secondVec
        + firstScale * thirdScale * crossNormSq firstVec thirdVec
        + secondScale * thirdScale * crossNormSq secondVec thirdVec := by
  simp only [secondMinorSum, crossNormSq_eq_leverage_mul_sub_sq, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply, leverageOf,
    dotProduct, Fin.sum_univ_three]
  ring

/-- The characteristic expansion of a rank-three determinant subtracted from the
identity. -/
theorem det_one_sub_eq (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) - M).det
      = 1 - Matrix.trace M + secondMinorSum M - M.det := by
  norm_num +decide [Matrix.det_fin_three, Matrix.sub_apply, Matrix.one_apply,
    secondMinorSum, Matrix.trace_fin_three]
  ring

/-- **THE THREE INVARIANTS TOGETHER.**  Subtracting a triple's weighted atom sum
from the identity leaves a determinant in the triple's own vocabulary: three
shares, three squared areas and one squared volume. -/
theorem det_one_sub_tripleAtomCombo (firstScale secondScale thirdScale : ℝ)
    (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) - (firstScale • atomMatrix firstVec
        + secondScale • atomMatrix secondVec + thirdScale • atomMatrix thirdVec)).det
      = 1 - (firstScale * leverageOf firstVec + secondScale * leverageOf secondVec
          + thirdScale * leverageOf thirdVec)
        + (firstScale * secondScale * crossNormSq firstVec secondVec
          + firstScale * thirdScale * crossNormSq firstVec thirdVec
          + secondScale * thirdScale * crossNormSq secondVec thirdVec)
        - firstScale * secondScale * thirdScale
          * tripleBracket firstVec secondVec thirdVec ^ 2 := by
  rw [det_one_sub_eq, trace_tripleAtomCombo, secondMinorSum_tripleAtomCombo,
    det_tripleAtomCombo]

/-! ## 2. Parseval splits at a triple -/

/-- The weighted atom sum of the three members of a triple. -/
noncomputable def designWeightedTripleSum (D : WeightedDesign m 3) (first second third : Fin m) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  D.weight first • atomMatrix (D.atom first) + D.weight second • atomMatrix (D.atom second)
    + D.weight third • atomMatrix (D.atom third)

/-- **PARSEVAL AT A TRIPLE.**  The complement of a triple carries exactly what the
triple does not. -/
theorem weightedComplement_triple_eq (D : WeightedDesign m 3) {first second third : Fin m}
    (hfs : first ≠ second) (hft : first ≠ third) (hst : second ≠ third) :
    ∑ c ∈ ({first, second, third} : Finset (Fin m))ᶜ, D.weight c • atomMatrix (D.atom c)
      = 1 - designWeightedTripleSum D first second third := by
  classical
  have hsplit := Finset.sum_add_sum_compl ({first, second, third} : Finset (Fin m))
    (fun c => D.weight c • atomMatrix (D.atom c))
  rw [D.isParseval, Finset.sum_insert (by simp [hfs, hft]), Finset.sum_insert (by simp [hst]),
    Finset.sum_singleton] at hsplit
  rw [designWeightedTripleSum]
  linear_combination (norm := module) hsplit

/-- **THE COMPLEMENT OF A TRIPLE, EVALUATED.**  Its determinant is a polynomial in
the triple alone: three shares, three squared areas, one squared volume. -/
theorem det_weightedComplement_triple (D : WeightedDesign m 3) {first second third : Fin m}
    (hfs : first ≠ second) (hft : first ≠ third) (hst : second ≠ third) :
    (∑ c ∈ ({first, second, third} : Finset (Fin m))ᶜ,
        D.weight c • atomMatrix (D.atom c)).det
      = 1 - (D.weight first * leverageOf (D.atom first)
          + D.weight second * leverageOf (D.atom second)
          + D.weight third * leverageOf (D.atom third))
        + (D.weight first * D.weight second * crossNormSq (D.atom first) (D.atom second)
          + D.weight first * D.weight third * crossNormSq (D.atom first) (D.atom third)
          + D.weight second * D.weight third
            * crossNormSq (D.atom second) (D.atom third))
        - D.weight first * D.weight second * D.weight third
          * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 := by
  rw [weightedComplement_triple_eq D hfs hft hst, designWeightedTripleSum,
    det_one_sub_tripleAtomCombo]

/-! ## 3. The triple floor -/

/-- **THE TRIPLE FLOOR.**  The complement of a triple is positive semidefinite, so
its determinant is nonnegative, and the expansion turns that into

  `A_C + V_C ≤ 1 + B_C` ,

the triple sibling of the landed pair floor.  No tie, no dominator, no size
restriction: every `(m,3)` design and every triple. -/
theorem triple_share_add_volume_le_one_add_areaSum (D : WeightedDesign m 3)
    {first second third : Fin m} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) :
    (D.weight first * leverageOf (D.atom first)
        + D.weight second * leverageOf (D.atom second)
        + D.weight third * leverageOf (D.atom third))
      + D.weight first * D.weight second * D.weight third
        * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2
      ≤ 1 + (D.weight first * D.weight second * crossNormSq (D.atom first) (D.atom second)
          + D.weight first * D.weight third * crossNormSq (D.atom first) (D.atom third)
          + D.weight second * D.weight third
            * crossNormSq (D.atom second) (D.atom third)) := by
  have hdet := (posSemidef_weightedSubsum D
    (({first, second, third} : Finset (Fin m))ᶜ)).det_nonneg
  rw [det_weightedComplement_triple D hfs hft hst] at hdet
  linarith

/-- **THE TRIPLE DEFICIT LIVES IN THE UNIT INTERVAL.**  The landed pair ceiling
caps each of the three squared areas by half the corresponding share sum, so
`B_C ≤ A_C`, while the triple floor caps `A_C − B_C` by `1 − V_C`.  Hence every
weighted squared volume of a triple is at most one, with no budget argument. -/
theorem triple_deficit_mem_unit_interval (D : WeightedDesign m 3)
    {first second third : Fin m} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) :
    (D.weight first * D.weight second * crossNormSq (D.atom first) (D.atom second)
        + D.weight first * D.weight third * crossNormSq (D.atom first) (D.atom third)
        + D.weight second * D.weight third * crossNormSq (D.atom second) (D.atom third))
      ≤ D.weight first * leverageOf (D.atom first)
        + D.weight second * leverageOf (D.atom second)
        + D.weight third * leverageOf (D.atom third) := by
  have hfs' := two_mul_weight_mul_crossNormSq_le_share_sum D first second
  have hft' := two_mul_weight_mul_crossNormSq_le_share_sum D first third
  have hst' := two_mul_weight_mul_crossNormSq_le_share_sum D second third
  linarith

/-- **EVERY WEIGHTED SQUARED VOLUME IS AT MOST ONE.** -/
theorem weighted_sq_tripleBracket_le_one (D : WeightedDesign m 3)
    {first second third : Fin m} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) :
    D.weight first * D.weight second * D.weight third
      * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 ≤ 1 := by
  have hfloor := triple_share_add_volume_le_one_add_areaSum D hfs hft hst
  have hdeficit := triple_deficit_mem_unit_interval D hfs hft hst
  linarith

/-! ## 4. The complementary volume law at `(6,3)` -/

/-- **THE COMPLEMENTARY TRIPLE VOLUME LAW AT `(6,3)`.**  The complement of a triple
is a triple, so the determinant expansion becomes an identity between the two
complementary weighted squared volumes and the triple's own pair data. -/
theorem complementary_triple_volume_law_sixThree (D : WeightedDesign 6 3)
    {first second third : Fin 6} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) {outOne outTwo outThree : Fin 6}
    (h12 : outOne ≠ outTwo) (h13 : outOne ≠ outThree) (h23 : outTwo ≠ outThree)
    (hcompl : ({first, second, third} : Finset (Fin 6))ᶜ = {outOne, outTwo, outThree}) :
    D.weight first * D.weight second * D.weight third
        * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2
      + D.weight outOne * D.weight outTwo * D.weight outThree
        * tripleBracket (D.atom outOne) (D.atom outTwo) (D.atom outThree) ^ 2
      = 1 - (D.weight first * leverageOf (D.atom first)
          + D.weight second * leverageOf (D.atom second)
          + D.weight third * leverageOf (D.atom third))
        + (D.weight first * D.weight second * crossNormSq (D.atom first) (D.atom second)
          + D.weight first * D.weight third * crossNormSq (D.atom first) (D.atom third)
          + D.weight second * D.weight third
            * crossNormSq (D.atom second) (D.atom third)) := by
  have hdet := det_weightedComplement_triple D hfs hft hst
  rw [hcompl, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton, ← add_assoc, det_tripleAtomCombo] at hdet
  linarith

/-- **TWO COMPLEMENTARY TRIPLES ARE DEGENERATE TOGETHER.**  At `(6,3)` a triple and
its complement both have vanishing volume exactly when the triple's shares and
squared areas balance, `A_C = 1 + B_C`.  So the coplanarities of a `(6,3)` design
come in complementary pairs, detected by one scalar equation in six numbers. -/
theorem both_degenerate_iff_share_eq_one_add_areaSum_sixThree (D : WeightedDesign 6 3)
    {first second third : Fin 6} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) {outOne outTwo outThree : Fin 6}
    (h12 : outOne ≠ outTwo) (h13 : outOne ≠ outThree) (h23 : outTwo ≠ outThree)
    (hcompl : ({first, second, third} : Finset (Fin 6))ᶜ = {outOne, outTwo, outThree}) :
    (tripleBracket (D.atom first) (D.atom second) (D.atom third) = 0
        ∧ tripleBracket (D.atom outOne) (D.atom outTwo) (D.atom outThree) = 0)
      ↔ D.weight first * leverageOf (D.atom first)
          + D.weight second * leverageOf (D.atom second)
          + D.weight third * leverageOf (D.atom third)
        = 1 + (D.weight first * D.weight second
            * crossNormSq (D.atom first) (D.atom second)
          + D.weight first * D.weight third * crossNormSq (D.atom first) (D.atom third)
          + D.weight second * D.weight third
            * crossNormSq (D.atom second) (D.atom third)) := by
  have hlaw := complementary_triple_volume_law_sixThree D hfs hft hst h12 h13 h23 hcompl
  have hinPos : 0 < D.weight first * D.weight second * D.weight third :=
    mul_pos (mul_pos (D.weight_pos first) (D.weight_pos second)) (D.weight_pos third)
  have houtPos : 0 < D.weight outOne * D.weight outTwo * D.weight outThree :=
    mul_pos (mul_pos (D.weight_pos outOne) (D.weight_pos outTwo)) (D.weight_pos outThree)
  constructor
  · rintro ⟨hin, hout⟩
    rw [hin, hout] at hlaw
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero, zero_add] at hlaw
    linarith
  · intro hbalance
    rw [hbalance] at hlaw
    have hzero : D.weight first * D.weight second * D.weight third
          * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2
        + D.weight outOne * D.weight outTwo * D.weight outThree
          * tripleBracket (D.atom outOne) (D.atom outTwo) (D.atom outThree) ^ 2 = 0 := by
      linarith
    have hinTerm : 0 ≤ D.weight first * D.weight second * D.weight third
        * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 :=
      mul_nonneg hinPos.le (sq_nonneg _)
    have houtTerm : 0 ≤ D.weight outOne * D.weight outTwo * D.weight outThree
        * tripleBracket (D.atom outOne) (D.atom outTwo) (D.atom outThree) ^ 2 :=
      mul_nonneg houtPos.le (sq_nonneg _)
    constructor
    · have hsq : tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 = 0 := by
        by_contra hcon
        have hstrict : 0 < D.weight first * D.weight second * D.weight third
            * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 :=
          mul_pos hinPos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hcon))
        linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    · have hsq : tripleBracket (D.atom outOne) (D.atom outTwo) (D.atom outThree) ^ 2 = 0 := by
        by_contra hcon
        have hstrict : 0 < D.weight outOne * D.weight outTwo * D.weight outThree
            * tripleBracket (D.atom outOne) (D.atom outTwo) (D.atom outThree) ^ 2 :=
          mul_pos houtPos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hcon))
        linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

/-- **A WEAK DOMINATOR'S WEIGHT PRODUCT IS CAPPED BY ITS OWN DEFICIT.**  A weak
dominator has squared volume at least one, so the triple floor caps the product
of its three weights by `1 − A_C + B_C`.  At a tie this is a bound on the weights
of every weak dominator, read off the dominator's own shares and squared
areas. -/
theorem weight_prod_le_one_sub_share_add_areaSum_of_dominates (D : WeightedDesign m 3)
    {first second third : Fin m} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third)
    (hdom : Dominates D ({first, second, third} : Finset (Fin m))) :
    D.weight first * D.weight second * D.weight third
      ≤ 1 - (D.weight first * leverageOf (D.atom first)
          + D.weight second * leverageOf (D.atom second)
          + D.weight third * leverageOf (D.atom third))
        + (D.weight first * D.weight second * crossNormSq (D.atom first) (D.atom second)
          + D.weight first * D.weight third * crossNormSq (D.atom first) (D.atom third)
          + D.weight second * D.weight third
            * crossNormSq (D.atom second) (D.atom third)) := by
  have hfloor := triple_share_add_volume_le_one_add_areaSum D hfs hft hst
  have hvolume := one_le_sq_tripleBracket_of_dominates D first second third hfs hft hst hdom
  have hprodPos : 0 < D.weight first * D.weight second * D.weight third :=
    mul_pos (mul_pos (D.weight_pos first) (D.weight_pos second)) (D.weight_pos third)
  nlinarith [hfloor, hvolume, hprodPos]

/-! ## 5. At `(5,3)` the law loses its second volume -/

/-- **THE TRIPLE VOLUME AT `(5,3)`.**  The complement of a triple is a pair, whose
weighted atom sum is singular, so the triple's weighted squared volume is
determined by its own three shares and three squared areas, with the two outside
atoms cancelled. -/
theorem triple_volume_eq_of_size_five (D : WeightedDesign 5 3)
    {first second third : Fin 5} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) {outFirst outSecond : Fin 5} (hout : outFirst ≠ outSecond)
    (hcompl : ({first, second, third} : Finset (Fin 5))ᶜ = {outFirst, outSecond}) :
    D.weight first * D.weight second * D.weight third
        * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2
      = 1 - (D.weight first * leverageOf (D.atom first)
          + D.weight second * leverageOf (D.atom second)
          + D.weight third * leverageOf (D.atom third))
        + (D.weight first * D.weight second * crossNormSq (D.atom first) (D.atom second)
          + D.weight first * D.weight third * crossNormSq (D.atom first) (D.atom third)
          + D.weight second * D.weight third
            * crossNormSq (D.atom second) (D.atom third)) := by
  have hdet := det_weightedComplement_triple D hfs hft hst
  rw [hcompl, Finset.sum_pair hout, det_pairAtomCombo] at hdet
  linarith

/-- **THE DEGENERACY CRITERION AT `(5,3)`.**  A triple of a `(5,3)` design is
coplanar exactly when its shares and squared areas balance. -/
theorem degenerate_iff_share_eq_one_add_areaSum_fiveThree (D : WeightedDesign 5 3)
    {first second third : Fin 5} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) {outFirst outSecond : Fin 5} (hout : outFirst ≠ outSecond)
    (hcompl : ({first, second, third} : Finset (Fin 5))ᶜ = {outFirst, outSecond}) :
    tripleBracket (D.atom first) (D.atom second) (D.atom third) = 0
      ↔ D.weight first * leverageOf (D.atom first)
          + D.weight second * leverageOf (D.atom second)
          + D.weight third * leverageOf (D.atom third)
        = 1 + (D.weight first * D.weight second
            * crossNormSq (D.atom first) (D.atom second)
          + D.weight first * D.weight third * crossNormSq (D.atom first) (D.atom third)
          + D.weight second * D.weight third
            * crossNormSq (D.atom second) (D.atom third)) := by
  have hlaw := triple_volume_eq_of_size_five D hfs hft hst hout hcompl
  have hprodPos : 0 < D.weight first * D.weight second * D.weight third :=
    mul_pos (mul_pos (D.weight_pos first) (D.weight_pos second)) (D.weight_pos third)
  constructor
  · intro hzero
    rw [hzero] at hlaw
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hlaw
    linarith
  · intro hbalance
    rw [hbalance] at hlaw
    have hsq : tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 = 0 := by
      by_contra hcon
      have hstrict : 0 < D.weight first * D.weight second * D.weight third
          * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 :=
        mul_pos hprodPos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hcon))
      linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

/-- **A WEAK DOMINATOR OF A `(5,3)` DESIGN IS PRICED EXACTLY.**  Its weight product
never exceeds the deficit `1 − A_C + B_C`, and that deficit IS the weighted
squared volume. -/
theorem weight_prod_le_deficit_of_dominates_fiveThree (D : WeightedDesign 5 3)
    {first second third : Fin 5} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) {outFirst outSecond : Fin 5} (hout : outFirst ≠ outSecond)
    (hcompl : ({first, second, third} : Finset (Fin 5))ᶜ = {outFirst, outSecond})
    (hdom : Dominates D ({first, second, third} : Finset (Fin 5))) :
    D.weight first * D.weight second * D.weight third
      ≤ 1 - (D.weight first * leverageOf (D.atom first)
          + D.weight second * leverageOf (D.atom second)
          + D.weight third * leverageOf (D.atom third))
        + (D.weight first * D.weight second * crossNormSq (D.atom first) (D.atom second)
          + D.weight first * D.weight third * crossNormSq (D.atom first) (D.atom third)
          + D.weight second * D.weight third
            * crossNormSq (D.atom second) (D.atom third)) :=
  weight_prod_le_one_sub_share_add_areaSum_of_dominates D hfs hft hst hdom

/-! ## 6. The parallel pair, seen from a triple

A parallel pair kills every volume through it, so a triple carrying a parallel
pair sits at the floor's equality when the design has size five, and at the
complement's own volume when it has size six. -/

/-- **A TRIPLE CARRYING A PARALLEL PAIR HAS NO VOLUME.**  The row law kills every
bracket through a parallel pair, so the triple's own volume vanishes and the
floor becomes an equality at `(5,3)`. -/
theorem share_eq_one_add_areaSum_of_parallel_fiveThree (D : WeightedDesign 5 3)
    {first second third : Fin 5} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) {outFirst outSecond : Fin 5} (hout : outFirst ≠ outSecond)
    (hcompl : ({first, second, third} : Finset (Fin 5))ᶜ = {outFirst, outSecond})
    (hflat : crossNormSq (D.atom first) (D.atom second) = 0) :
    D.weight first * leverageOf (D.atom first)
        + D.weight second * leverageOf (D.atom second)
        + D.weight third * leverageOf (D.atom third)
      = 1 + (D.weight first * D.weight third * crossNormSq (D.atom first) (D.atom third)
          + D.weight second * D.weight third
            * crossNormSq (D.atom second) (D.atom third)) := by
  have hbracket := sq_tripleBracket_eq_zero_of_crossNormSq_eq_zero D hflat third
  have hcrit := (degenerate_iff_share_eq_one_add_areaSum_fiveThree D hfs hft hst hout
    hcompl).mp hbracket
  rw [hflat] at hcrit
  linarith

/-- **AT `(6,3)` A PARALLEL PAIR HANDS ITS TRIPLE'S DEFICIT TO THE COMPLEMENT.**
Every triple through a parallel pair has vanishing volume, so the complementary
triple's weighted squared volume IS the deficit `1 − A_C + B_C`. -/
theorem complement_volume_eq_deficit_of_parallel_sixThree (D : WeightedDesign 6 3)
    {first second third : Fin 6} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) {outOne outTwo outThree : Fin 6}
    (h12 : outOne ≠ outTwo) (h13 : outOne ≠ outThree) (h23 : outTwo ≠ outThree)
    (hcompl : ({first, second, third} : Finset (Fin 6))ᶜ = {outOne, outTwo, outThree})
    (hflat : crossNormSq (D.atom first) (D.atom second) = 0) :
    D.weight outOne * D.weight outTwo * D.weight outThree
        * tripleBracket (D.atom outOne) (D.atom outTwo) (D.atom outThree) ^ 2
      = 1 - (D.weight first * leverageOf (D.atom first)
          + D.weight second * leverageOf (D.atom second)
          + D.weight third * leverageOf (D.atom third))
        + (D.weight first * D.weight third * crossNormSq (D.atom first) (D.atom third)
          + D.weight second * D.weight third
            * crossNormSq (D.atom second) (D.atom third)) := by
  have hlaw := complementary_triple_volume_law_sixThree D hfs hft hst h12 h13 h23 hcompl
  have hbracket := sq_tripleBracket_eq_zero_of_crossNormSq_eq_zero D hflat third
  rw [hbracket, hflat] at hlaw
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_add] at hlaw
  linarith

end Gtz

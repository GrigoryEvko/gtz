/-
# The cross term at the centre of the invariant-leverage polytope

`Gtz/Quantitative/SixThreeNuCovering.lean` reduces the `(6,3)` uniform-share
question to ONE covering statement: every point of the invariant-leverage design
region lies in the cell `K_T` of some triple.  The centre of that polytope is
`nu == 1/3`, and `Gtz.constantThird_mem_invariantLeverageHypersimplex` shows the
centre is a point of the polytope.  This module decides the centre.

## What is new here

1. **The centre is the uniform weight.**  A unit tight frame of six atoms in `R^3`
   has `Gamma = 2 P` with `P` a rank-three projection of constant diagonal one
   half.  So `Gamma[T] - diag(1/3)|_T = 2 (P[T] - diag(1/6)|_T)`.  The centre of
   the `nu` polytope IS uniform weight one sixth on the flat stratum.  The two
   lanes of the campaign meet at one point.

2. **The centre margin in closed form.**  `Gtz.centreMargin` is
   `8/27 + 2 P_T - (2/3) E_T`, where `E_T` is the triple energy and `P_T` is the
   triple edge product.  It is the determinant clause of the cell at the centre.

3. **The `4/9` threshold.**  A coherent triple of energy at most `4/9` is covered
   at the centre.  At energy exactly `4/9` and zero product the margin is exactly
   zero, so `4/9` is sharp.

4. **The cap `8/27`, attained only through decoupling.**  `3 P_T <= E_T` holds on
   every tight Gram, so `centreMargin <= 8/27`.  A decoupled triple attains it.
   The shipped cap `det(gap) <= 1/27` of the flat-locus lane is this cap divided
   by eight, which is the first independent confirmation of the bridge.

5. **The complementary pair law.**  The two halves of a complementary pair share
   the energy and carry opposite products, so
   `max(margin_T, margin_T') = 8/27 - (2/3) E + 2 |P|`.

6. **TWO NO-GO WITNESSES, both exact and both in kernel.**  A certificate that
   reads only the energy cannot cover the centre, and a certificate that reads
   only the product cannot cover the centre either.
   - `Gtz.crossWitnessGram`, the six coordinate-plane diagonals, has EVERY triple
     above the `4/9` threshold, and it is still covered — by the cross term alone,
     with margin exactly `5/108`.  This design is the non-vacuity witness that the
     ledger of `Skeleton.obligationBaseTripleTightUThreeSix` names.
   - `Gtz.bipartiteWitnessGram` has EVERY one of its twenty edge products zero,
     and it is still covered — by a decoupled triple, with margin `8/27`.
   Any hypothesis of the shape "the total coupling is at least a positive
   constant" is false on the flat locus, and the second witness refutes it.

## Two general laws that the witnesses use

`Gtz.tripleEdgeProduct_eq_zero_of_bipartite`: when the nonzero pattern of a
symmetric array is bipartite, all twenty edge products vanish.  `Gtz.
tightTripleEnergy_ge_of_matching`: when the vanishing pairs form a matching and
every other pair carries the same square, every triple spends at least twice that
square.  Both are new, and both are stated for an arbitrary array.
-/
import Gtz.Wave.NuCoveringBand
import Gtz.Wave.ComplementDualLane

namespace Gtz

open Matrix

/-! ## 1. The centre of the polytope -/

/-- **THE CENTRE `nu == 1/3`.**  The mean of the invariant leverages on the
hypersimplex, and the unique point at which no atom is distinguished. -/
noncomputable def centreLeverage : Fin 6 → ℝ := fun _ => 1 / 3

@[simp] theorem centreLeverage_apply (index : Fin 6) : centreLeverage index = 1 / 3 := rfl

theorem centreLeverage_mem_invariantLeverageHypersimplex :
    centreLeverage ∈ invariantLeverageHypersimplex := by
  refine ⟨fun _ => ⟨by norm_num, by norm_num⟩, ?_⟩
  rw [Fin.sum_univ_six]
  norm_num

/-- The centre is interior, so it is a point of the DESIGN region and not only of
the closed hypersimplex.  Every design must be tested against it. -/
theorem centreLeverage_mem_invariantLeverageDesignRegion :
    centreLeverage ∈ invariantLeverageDesignRegion := by
  refine ⟨fun _ => ⟨by norm_num, by norm_num⟩, ?_⟩
  rw [Fin.sum_univ_six]
  norm_num

/-! ## 2. The centre block, and the margin it asks for -/

/-- **THE CENTRE BLOCK.**  At `nu == 1/3` the cell test of a triple is the shipped
slack-shifted hollow block at the constant capacity `2/3`.  This is the bridge:
the capacity `2/3` is `1 - 1/3`, and for `Gamma = 2 P` it is twice the projection
slack `1/2 - 1/6`. -/
theorem submatrix_sub_centre_eq_slackHollowThree {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) (first second third : Fin 6) :
    gram.submatrix ![first, second, third] ![first, second, third]
        - Matrix.diagonal (fun slot => centreLeverage (![first, second, third] slot))
      = slackHollowThree (2 / 3) (2 / 3) (2 / 3)
          (gram first second) (gram first third) (gram second third) := by
  rw [submatrix_sub_diagonal_eq_slackHollowThree gram (hgram.unit first) (hgram.unit second)
    (hgram.unit third) (hgram.comm first second) (hgram.comm first third)
    (hgram.comm second third) centreLeverage]
  norm_num

/-- **THE CENTRE MARGIN.**  The determinant clause of the cell at `nu == 1/3`,
in the two invariants of the triple. -/
noncomputable def centreMargin (gram : Matrix (Fin 6) (Fin 6) ℝ)
    (first second third : Fin 6) : ℝ :=
  8 / 27 + 2 * tripleEdgeProduct gram first second third
    - (2 / 3) * tightTripleEnergy gram first second third

theorem centreMargin_apply (gram : Matrix (Fin 6) (Fin 6) ℝ) (first second third : Fin 6) :
    centreMargin gram first second third
      = 8 / 27 + 2 * tripleEdgeProduct gram first second third
        - (2 / 3) * tightTripleEnergy gram first second third := rfl

/-- The centre margin IS the shipped slack determinant at capacity `2/3`. -/
theorem centreMargin_eq_slackDeterminantThree (gram : Matrix (Fin 6) (Fin 6) ℝ)
    (first second third : Fin 6) :
    centreMargin gram first second third
      = slackDeterminantThree (2 / 3) (2 / 3) (2 / 3)
          (gram first second) (gram first third) (gram second third) := by
  simp only [centreMargin, slackDeterminantThree, tightTripleEnergy, tripleEdgeProduct]
  ring

/-- **THE CENTRE CELL, DECIDED.**  A triple covers the centre exactly when its three
squared correlations stay under `4/9` and its centre margin is nonnegative.  The
three pair clauses are NOT automatic: a tight Gram permits a squared correlation of
one. -/
theorem mem_centre_invariantLeverageCell_iff {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) (first second third : Fin 6) :
    centreLeverage ∈ invariantLeverageCell gram first second third
      ↔ (gram first second) ^ 2 ≤ 4 / 9 ∧ (gram first third) ^ 2 ≤ 4 / 9
        ∧ (gram second third) ^ 2 ≤ 4 / 9 ∧ 0 ≤ centreMargin gram first second third := by
  rw [mem_invariantLeverageCell_iff, submatrix_sub_centre_eq_slackHollowThree hgram,
    posSemidef_slackHollowThree_iff_of_nonneg (by norm_num) (by norm_num) (by norm_num),
    ← centreMargin_eq_slackDeterminantThree]
  constructor
  · rintro ⟨hone, htwo, hthree, hdet⟩
    exact ⟨by linarith, by linarith, by linarith, hdet⟩
  · rintro ⟨hone, htwo, hthree, hdet⟩
    exact ⟨by linarith, by linarith, by linarith, hdet⟩

/-! ### The two-clause criterion

The three pair clauses of the previous theorem are NOT independent of the
determinant clause.  Their SUM, `E_T <= 4/3`, already implies each of them once the
determinant clause holds.  So the centre cell is decided by exactly two numbers, and
both are the invariants this module spends everywhere else. -/

/-- **THE PAIR CLAUSES ARE REDUNDANT.**  If the three squares total at most `4/3` and
the determinant clause holds, then every single square is at most `4/9`.  The proof
is `2 x y z <= |x| (y^2 + z^2)` followed by the exact factorisation
`a^3 - (4/3) a + 16/27 = (a - 2/3)^2 (a + 4/3)`, whose double root at `2/3` is what
makes the bound sharp. -/
theorem sq_le_four_ninths_of_energy_le_of_margin
    {edgeFirst edgeSecond edgeThird : ℝ}
    (henergy : edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2 ≤ 4 / 3)
    (hmargin : (2 / 3) * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2) - 8 / 27
      ≤ 2 * (edgeFirst * edgeSecond * edgeThird)) :
    edgeFirst ^ 2 ≤ 4 / 9 := by
  by_contra hcontra
  push Not at hcontra
  have habsSq : |edgeFirst| ^ 2 = edgeFirst ^ 2 := sq_abs edgeFirst
  have habsNonneg : (0 : ℝ) ≤ |edgeFirst| := abs_nonneg edgeFirst
  have hbig : 2 / 3 < |edgeFirst| := by nlinarith
  have hcross : edgeFirst * edgeSecond * edgeThird
      ≤ |edgeFirst| * (|edgeSecond| * |edgeThird|) := by
    rw [← abs_mul, ← abs_mul, mul_assoc]
    exact le_abs_self _
  have hpair : 2 * (|edgeSecond| * |edgeThird|) ≤ edgeSecond ^ 2 + edgeThird ^ 2 := by
    nlinarith [sq_nonneg (|edgeSecond| - |edgeThird|), sq_abs edgeSecond, sq_abs edgeThird]
  have hamgm : 2 * (edgeFirst * edgeSecond * edgeThird)
      ≤ |edgeFirst| * (edgeSecond ^ 2 + edgeThird ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hpair habsNonneg]
  have hsplit : edgeSecond ^ 2 + edgeThird ^ 2
      = (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2) - |edgeFirst| ^ 2 := by
    rw [habsSq]
    ring
  nlinarith [sq_nonneg (|edgeFirst| - 2 / 3), hamgm, hsplit, henergy, hmargin, hbig,
    habsNonneg, habsSq]

/-- **THE CENTRE CELL IN TWO CLAUSES.**  A triple covers the centre exactly when its
energy is at most `4/3` and its centre margin is nonnegative.  The three pair clauses
of the first criterion are consequences, not hypotheses. -/
theorem mem_centre_invariantLeverageCell_iff_energy_le {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) (first second third : Fin 6) :
    centreLeverage ∈ invariantLeverageCell gram first second third
      ↔ tightTripleEnergy gram first second third ≤ 4 / 3
        ∧ 0 ≤ centreMargin gram first second third := by
  rw [mem_centre_invariantLeverageCell_iff hgram]
  constructor
  · rintro ⟨hone, htwo, hthree, hdet⟩
    refine ⟨?_, hdet⟩
    simp only [tightTripleEnergy]
    linarith
  · rintro ⟨henergy, hdet⟩
    simp only [tightTripleEnergy] at henergy
    have hmargin : (2 / 3) * ((gram first second) ^ 2 + (gram first third) ^ 2
        + (gram second third) ^ 2) - 8 / 27
        ≤ 2 * (gram first second * gram first third * gram second third) := by
      simp only [centreMargin, tightTripleEnergy, tripleEdgeProduct] at hdet
      linarith
    refine ⟨sq_le_four_ninths_of_energy_le_of_margin henergy hmargin, ?_, ?_, hdet⟩
    · exact sq_le_four_ninths_of_energy_le_of_margin (edgeFirst := gram first third)
        (edgeSecond := gram first second) (edgeThird := gram second third)
        (by linarith) (by nlinarith [hmargin])
    · exact sq_le_four_ninths_of_energy_le_of_margin (edgeFirst := gram second third)
        (edgeSecond := gram first second) (edgeThird := gram first third)
        (by linarith) (by nlinarith [hmargin])

/-- **THE CENTRE CELL, IN THE TWO INVARIANTS ALONE.**  Energy at most `4/3`, and twice
the coupling at least `(2/3) E - 8/27`.  Nothing else about the triple matters. -/
theorem mem_centre_invariantLeverageCell_iff_invariants {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) (first second third : Fin 6) :
    centreLeverage ∈ invariantLeverageCell gram first second third
      ↔ tightTripleEnergy gram first second third ≤ 4 / 3
        ∧ (2 / 3) * tightTripleEnergy gram first second third - 8 / 27
          ≤ 2 * tripleEdgeProduct gram first second third := by
  rw [mem_centre_invariantLeverageCell_iff_energy_le hgram]
  simp only [centreMargin]
  constructor
  · rintro ⟨henergy, hmargin⟩
    exact ⟨henergy, by linarith⟩
  · rintro ⟨henergy, hmargin⟩
    exact ⟨henergy, by linarith⟩

/-! ## 3. The `4/9` threshold, and the decoupled law -/

/-- **THE `4/9` THRESHOLD.**  A coherent triple whose energy is at most `4/9` covers
the centre.  No tightness beyond the unit diagonal and the symmetry is spent, and
the three pair clauses come free from the energy bound. -/
theorem mem_centre_invariantLeverageCell_of_energy_le {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second third : Fin 6}
    (henergy : tightTripleEnergy gram first second third ≤ 4 / 9)
    (hproduct : 0 ≤ tripleEdgeProduct gram first second third) :
    centreLeverage ∈ invariantLeverageCell gram first second third := by
  rw [mem_centre_invariantLeverageCell_iff hgram]
  simp only [tightTripleEnergy] at henergy
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [sq_nonneg (gram first third), sq_nonneg (gram second third)]
  · linarith [sq_nonneg (gram first second), sq_nonneg (gram second third)]
  · linarith [sq_nonneg (gram first second), sq_nonneg (gram first third)]
  · simp only [centreMargin, tightTripleEnergy]
    linarith

/-- **THE DECOUPLED LAW.**  When the edge product vanishes the centre margin is
nonnegative exactly at energy `4/9` or less.  So the threshold of the previous
the threshold above is sharp, on a locus that the flat stratum reaches. -/
theorem centreMargin_nonneg_iff_of_zero_product {gram : Matrix (Fin 6) (Fin 6) ℝ}
    {first second third : Fin 6}
    (hproduct : tripleEdgeProduct gram first second third = 0) :
    0 ≤ centreMargin gram first second third
      ↔ tightTripleEnergy gram first second third ≤ 4 / 9 := by
  simp only [centreMargin, hproduct]
  constructor <;> intro hbound <;> linarith

/-- An orthogonal triple sits at the exact centre margin `8/27`. -/
theorem centreMargin_of_orthogonal {gram : Matrix (Fin 6) (Fin 6) ℝ}
    {first second third : Fin 6} (hone : gram first second = 0)
    (htwo : gram first third = 0) (hthree : gram second third = 0) :
    centreMargin gram first second third = 8 / 27 := by
  simp only [centreMargin, tightTripleEnergy, tripleEdgeProduct, hone, htwo, hthree]
  norm_num

/-- **A DECOUPLED TRIPLE COVERS THE CENTRE**, with the largest margin available. -/
theorem mem_centre_invariantLeverageCell_of_orthogonal {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second third : Fin 6}
    (hone : gram first second = 0) (htwo : gram first third = 0)
    (hthree : gram second third = 0) :
    centreLeverage ∈ invariantLeverageCell gram first second third := by
  rw [mem_centre_invariantLeverageCell_iff hgram, hone, htwo, hthree,
    centreMargin_of_orthogonal hone htwo hthree]
  norm_num

/-- **THE EQUIANGULAR THRESHOLD.**  At the equiangular energy `3/5` the centre asks
the triple for a coupling of at least `7/135`.  The shipped constant of
`Gtz.slackDeterminantThree_uniform_equiangular` is twice that, and this theorem
routes the centre margin through it, so the two readings are the same number. -/
theorem centreMargin_nonneg_iff_equiangular {gram : Matrix (Fin 6) (Fin 6) ℝ}
    {first second third : Fin 6}
    (henergy : tightTripleEnergy gram first second third = 3 / 5) :
    0 ≤ centreMargin gram first second third
      ↔ 14 / 135 ≤ 2 * (gram first second * gram first third * gram second third) := by
  rw [centreMargin_eq_slackDeterminantThree,
    slackDeterminantThree_uniform_equiangular (by simpa [tightTripleEnergy] using henergy)]

/-- The same threshold, read on the edge product itself. -/
theorem centreMargin_nonneg_iff_equiangular_product {gram : Matrix (Fin 6) (Fin 6) ℝ}
    {first second third : Fin 6}
    (henergy : tightTripleEnergy gram first second third = 3 / 5) :
    0 ≤ centreMargin gram first second third
      ↔ 7 / 135 ≤ tripleEdgeProduct gram first second third := by
  simp only [centreMargin, henergy]
  constructor <;> intro hbound <;> linarith

/-- **THE EQUIANGULAR ENERGY IS ABOVE THE THRESHOLD.**  `3/5` beats `4/9` by `7/45`,
so the equiangular design is exactly the case the energy regime cannot reach.  This
is the structural reason the energy-only route was never enough. -/
theorem four_ninths_lt_three_fifths : (4 : ℝ) / 9 < 3 / 5 := by norm_num

/-! ## 4. The cap `8/27` -/

/-- **THE THREE-FACTOR BOUND.**  For a real of absolute value at most one in each
slot, three times the product never beats the sum of the squares.  The proof is the
two nonnegative combinations `(1 + z)(x - y)^2` and `(1 - z)(x + y)^2`, once for
each choice of the bounded slot. -/
theorem three_mul_prod_le_sum_sq {first second third : ℝ}
    (hfirstLow : -1 ≤ first) (hfirstHigh : first ≤ 1)
    (hsecondLow : -1 ≤ second) (hsecondHigh : second ≤ 1)
    (hthirdLow : -1 ≤ third) (hthirdHigh : third ≤ 1) :
    3 * (first * second * third) ≤ first ^ 2 + second ^ 2 + third ^ 2 := by
  have hone : first * second * third ≤ (first ^ 2 + second ^ 2) / 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + third) (sq_nonneg (first - second)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - third) (sq_nonneg (first + second))]
  have htwo : first * second * third ≤ (second ^ 2 + third ^ 2) / 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + first) (sq_nonneg (second - third)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - first) (sq_nonneg (second + third))]
  have hthree : first * second * third ≤ (first ^ 2 + third ^ 2) / 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + second) (sq_nonneg (first - third)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - second) (sq_nonneg (first + third))]
  linarith

/-- Every off-diagonal entry of a tight Gram lies in `[-1, 1]`. -/
theorem IsTightGramSix.neg_one_le {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {centre partner : Fin 6} (hne : partner ≠ centre) :
    -1 ≤ gram centre partner := by
  nlinarith [hgram.sq_le_one hne, sq_nonneg (gram centre partner + 1)]

theorem IsTightGramSix.le_one {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {centre partner : Fin 6} (hne : partner ≠ centre) :
    gram centre partner ≤ 1 := by
  nlinarith [hgram.sq_le_one hne, sq_nonneg (gram centre partner - 1)]

/-- **THE COUPLING NEVER OUTRUNS THE ENERGY.**  On a tight Gram every triple obeys
`3 P_T <= E_T`. -/
theorem IsTightGramSix.three_mul_tripleEdgeProduct_le_tightTripleEnergy
    {gram : Matrix (Fin 6) (Fin 6) ℝ} (hgram : IsTightGramSix gram)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    3 * tripleEdgeProduct gram first second third
      ≤ tightTripleEnergy gram first second third := by
  simp only [tripleEdgeProduct, tightTripleEnergy]
  exact three_mul_prod_le_sum_sq (hgram.neg_one_le (Ne.symm hfirstSecond))
    (hgram.le_one (Ne.symm hfirstSecond)) (hgram.neg_one_le (Ne.symm hfirstThird))
    (hgram.le_one (Ne.symm hfirstThird)) (hgram.neg_one_le (Ne.symm hsecondThird))
    (hgram.le_one (Ne.symm hsecondThird))

/-- **THE CAP AT THE CENTRE IS `8/27`.**  The flat-locus lane already caps the gap
determinant at `1/27`.  The bridge multiplies determinants by eight, so the two
caps are the same statement, reached from two different directions. -/
theorem IsTightGramSix.centreMargin_le {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    centreMargin gram first second third ≤ 8 / 27 := by
  have hcoupling := hgram.three_mul_tripleEdgeProduct_le_tightTripleEnergy hfirstSecond
    hfirstThird hsecondThird
  simp only [centreMargin]
  linarith

/-! ## 5. The complementary pair -/

/-- The two halves of a complementary pair share the energy.  This is derived from
the two landed determinant identities, not assumed. -/
theorem IsTightGramSix.tightTripleEnergy_compl {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) :
    tightTripleEnergy gram 3 4 5 = tightTripleEnergy gram 0 1 2 := by
  have hsum := hgram.det_gramBlock_add_compl
  have hmirror := hgram.det_gramBlock_eq_det_coGramBlock_compl
  rw [hgram.det_gramBlock 0 1 2, hgram.det_gramBlock 3 4 5] at hsum
  rw [hgram.det_gramBlock 0 1 2,
    hgram.det_coGramBlock (by decide : (3 : Fin 6) ≠ 4) (by decide : (3 : Fin 6) ≠ 5)
      (by decide : (4 : Fin 6) ≠ 5)] at hmirror
  linarith

/-- The two halves of a complementary pair carry opposite edge products. -/
theorem IsTightGramSix.tripleEdgeProduct_compl {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) :
    tripleEdgeProduct gram 3 4 5 = -tripleEdgeProduct gram 0 1 2 := by
  have hsum := hgram.det_gramBlock_add_compl
  have hmirror := hgram.det_gramBlock_eq_det_coGramBlock_compl
  rw [hgram.det_gramBlock 0 1 2, hgram.det_gramBlock 3 4 5] at hsum
  rw [hgram.det_gramBlock 0 1 2,
    hgram.det_coGramBlock (by decide : (3 : Fin 6) ≠ 4) (by decide : (3 : Fin 6) ≠ 5)
      (by decide : (4 : Fin 6) ≠ 5)] at hmirror
  linarith

/-- **THE PAIR SUM.**  The two centre margins of a complementary pair add to a
quantity that reads only the shared energy.  The coupling cancels. -/
theorem IsTightGramSix.centreMargin_add_compl {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) :
    centreMargin gram 0 1 2 + centreMargin gram 3 4 5
      = 16 / 27 - (4 / 3) * tightTripleEnergy gram 0 1 2 := by
  simp only [centreMargin, hgram.tightTripleEnergy_compl, hgram.tripleEdgeProduct_compl]
  ring

/-- **THE PAIR MAXIMUM.**  The better half of a complementary pair collects the
absolute coupling.  This is the exact law the sign-blind cells of the campaign pay
`2 |P|` to avoid. -/
theorem IsTightGramSix.max_centreMargin_compl {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) :
    max (centreMargin gram 0 1 2) (centreMargin gram 3 4 5)
      = 8 / 27 - (2 / 3) * tightTripleEnergy gram 0 1 2
        + 2 * |tripleEdgeProduct gram 0 1 2| := by
  have henergy := hgram.tightTripleEnergy_compl
  have hproduct := hgram.tripleEdgeProduct_compl
  rcases le_or_gt 0 (tripleEdgeProduct gram 0 1 2) with hsign | hsign
  · rw [abs_of_nonneg hsign,
      max_eq_left (by simp only [centreMargin, henergy, hproduct]; linarith)]
    simp only [centreMargin]
    ring
  · rw [abs_of_neg hsign,
      max_eq_right (by simp only [centreMargin, henergy, hproduct]; linarith)]
    simp only [centreMargin, henergy, hproduct]
    ring

/-- **ONE HALF OF EVERY COMPLEMENTARY PAIR CLEARS THE CENTRE** as soon as the shared
energy is at most `4/9`.  The coupling can only help the better half. -/
theorem IsTightGramSix.max_centreMargin_compl_nonneg {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) (henergy : tightTripleEnergy gram 0 1 2 ≤ 4 / 9) :
    0 ≤ max (centreMargin gram 0 1 2) (centreMargin gram 3 4 5) := by
  rw [hgram.max_centreMargin_compl]
  have habs := abs_nonneg (tripleEdgeProduct gram 0 1 2)
  linarith

/-- **THE COMPLEMENT PRODUCER.**  One energy bound at ONE triple covers the centre,
at that triple or at its complement.  The sign of the coupling selects the half, and
the complement involution supplies the other half with the same energy and the
opposite coupling.  This is a producer for the covering statement of
`Gtz.gtzUniformShareSixThree_iff_forall_coversInvariantLeverageDesignRegion` at the
centre, and it spends no sign hypothesis at all. -/
theorem IsTightGramSix.exists_mem_centre_invariantLeverageCell_compl
    {gram : Matrix (Fin 6) (Fin 6) ℝ} (hgram : IsTightGramSix gram)
    (henergy : tightTripleEnergy gram 0 1 2 ≤ 4 / 9) :
    centreLeverage ∈ invariantLeverageCell gram 0 1 2
      ∨ centreLeverage ∈ invariantLeverageCell gram 3 4 5 := by
  rcases le_or_gt 0 (tripleEdgeProduct gram 0 1 2) with hsign | hsign
  · exact Or.inl (mem_centre_invariantLeverageCell_of_energy_le hgram henergy hsign)
  · refine Or.inr (mem_centre_invariantLeverageCell_of_energy_le hgram ?_ ?_)
    · rw [hgram.tightTripleEnergy_compl]
      exact henergy
    · rw [hgram.tripleEdgeProduct_compl]
      linarith

/-! ### The twenty centre margins -/

/-- **THE TWENTY CENTRE MARGINS**, in the campaign's triple order. -/
noncomputable def totalCentreMargin (gram : Matrix (Fin 6) (Fin 6) ℝ) : ℝ :=
  centreMargin gram 0 1 2 + centreMargin gram 0 1 3 + centreMargin gram 0 1 4
    + centreMargin gram 0 1 5 + centreMargin gram 0 2 3 + centreMargin gram 0 2 4
    + centreMargin gram 0 2 5 + centreMargin gram 0 3 4 + centreMargin gram 0 3 5
    + centreMargin gram 0 4 5 + centreMargin gram 1 2 3 + centreMargin gram 1 2 4
    + centreMargin gram 1 2 5 + centreMargin gram 1 3 4 + centreMargin gram 1 3 5
    + centreMargin gram 1 4 5 + centreMargin gram 2 3 4 + centreMargin gram 2 3 5
    + centreMargin gram 2 4 5 + centreMargin gram 3 4 5

/-- The total splits into the two twenty-triple statistics the tree already owns. -/
theorem totalCentreMargin_split (gram : Matrix (Fin 6) (Fin 6) ℝ) :
    totalCentreMargin gram
      = 160 / 27 + 2 * totalTripleEdgeProduct gram - (2 / 3) * totalTripleEnergy gram := by
  simp only [totalCentreMargin, centreMargin, totalTripleEdgeProduct, totalTripleEnergy]
  ring

/-- The twenty edge products of a tight Gram cancel.  The shipped cancellation lives
on the hollow involution `Gamma - 1`, whose off-diagonal entries are those of
`Gamma`. -/
theorem IsTightGramSix.totalTripleEdgeProduct_eq_zero {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) : totalTripleEdgeProduct gram = 0 := by
  have hzero := hgram.isHollowInvolution_sub_one.totalTripleEdgeProduct_eq_zero
  simp only [totalTripleEdgeProduct, tripleEdgeProduct,
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (0 : Fin 6) ≠ 1),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (0 : Fin 6) ≠ 2),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (0 : Fin 6) ≠ 3),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (0 : Fin 6) ≠ 4),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (0 : Fin 6) ≠ 5),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (1 : Fin 6) ≠ 2),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (1 : Fin 6) ≠ 3),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (1 : Fin 6) ≠ 4),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (1 : Fin 6) ≠ 5),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (2 : Fin 6) ≠ 3),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (2 : Fin 6) ≠ 4),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (2 : Fin 6) ≠ 5),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (3 : Fin 6) ≠ 4),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (3 : Fin 6) ≠ 5),
    IsTightGramSix.sub_one_apply_of_ne (gram := gram) (by decide : (4 : Fin 6) ≠ 5)] at hzero
  simpa only [totalTripleEdgeProduct, tripleEdgeProduct] using hzero

/-- **THE TWENTY CENTRE MARGINS TOTAL `-56/27`.**  This is the shipped constant of
`Gtz.IsHollowInvolution.totalShiftedTripleDet_uniform`, reached from the centre
margin instead of from the shifted determinant.  The two lanes compute one number. -/
theorem IsTightGramSix.totalCentreMargin_eq {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) : totalCentreMargin gram = -(56 / 27) := by
  rw [totalCentreMargin_split, hgram.totalTripleEdgeProduct_eq_zero,
    hgram.totalTripleEnergy_eq_twelve]
  norm_num

/-- **EVERY TIGHT GRAM HAS A TRIPLE THAT FAILS THE CENTRE.**  The mean centre margin
is `-14/135`, so the covering at the centre is never a statement about all triples.
It is always a strict selection, on every design without exception. -/
theorem IsTightGramSix.exists_centreMargin_neg {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ centreMargin gram first second third < 0 := by
  by_contra hcontra
  push Not at hcontra
  have htotal := hgram.totalCentreMargin_eq
  simp only [totalCentreMargin] at htotal
  linarith [
    hcontra 0 1 2 (by decide) (by decide) (by decide),
    hcontra 0 1 3 (by decide) (by decide) (by decide),
    hcontra 0 1 4 (by decide) (by decide) (by decide),
    hcontra 0 1 5 (by decide) (by decide) (by decide),
    hcontra 0 2 3 (by decide) (by decide) (by decide),
    hcontra 0 2 4 (by decide) (by decide) (by decide),
    hcontra 0 2 5 (by decide) (by decide) (by decide),
    hcontra 0 3 4 (by decide) (by decide) (by decide),
    hcontra 0 3 5 (by decide) (by decide) (by decide),
    hcontra 0 4 5 (by decide) (by decide) (by decide),
    hcontra 1 2 3 (by decide) (by decide) (by decide),
    hcontra 1 2 4 (by decide) (by decide) (by decide),
    hcontra 1 2 5 (by decide) (by decide) (by decide),
    hcontra 1 3 4 (by decide) (by decide) (by decide),
    hcontra 1 3 5 (by decide) (by decide) (by decide),
    hcontra 1 4 5 (by decide) (by decide) (by decide),
    hcontra 2 3 4 (by decide) (by decide) (by decide),
    hcontra 2 3 5 (by decide) (by decide) (by decide),
    hcontra 2 4 5 (by decide) (by decide) (by decide),
    hcontra 3 4 5 (by decide) (by decide) (by decide)]

/-- The same statement on the cell itself. -/
theorem IsTightGramSix.exists_notMem_centre_invariantLeverageCell
    {gram : Matrix (Fin 6) (Fin 6) ℝ} (hgram : IsTightGramSix gram) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ centreLeverage ∉ invariantLeverageCell gram first second third := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hneg⟩ :=
    hgram.exists_centreMargin_neg
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  rw [mem_centre_invariantLeverageCell_iff hgram]
  rintro ⟨-, -, -, hmargin⟩
  linarith

/-- **`4/9` IS THE EXACT PAIR THRESHOLD.**  When BOTH halves of a complementary pair
cover the centre, the shared energy is at most `4/9`.  With the complement producer
this makes `4/9` a two-sided threshold on the pair, and not merely a sufficient
condition. -/
theorem IsTightGramSix.tightTripleEnergy_le_of_both_mem_centre_cell
    {gram : Matrix (Fin 6) (Fin 6) ℝ} (hgram : IsTightGramSix gram)
    (hfront : centreLeverage ∈ invariantLeverageCell gram 0 1 2)
    (hback : centreLeverage ∈ invariantLeverageCell gram 3 4 5) :
    tightTripleEnergy gram 0 1 2 ≤ 4 / 9 := by
  rw [mem_centre_invariantLeverageCell_iff hgram] at hfront hback
  have hsum := hgram.centreMargin_add_compl
  linarith [hfront.2.2.2, hback.2.2.2]

/-- **THE PAIR CRITERION, EXACT.**  A complementary pair covers the centre exactly when
its shared energy is at most `4/3` and its absolute coupling clears
`(1/3) E - 4/27`.  Nothing else about the six atoms enters.  The whole centre
question is therefore a statement about the TEN numbers `(E_i, |P_i|)`. -/
theorem IsTightGramSix.mem_centre_invariantLeverageCell_front_or_back_iff
    {gram : Matrix (Fin 6) (Fin 6) ℝ} (hgram : IsTightGramSix gram) :
    (centreLeverage ∈ invariantLeverageCell gram 0 1 2
        ∨ centreLeverage ∈ invariantLeverageCell gram 3 4 5)
      ↔ tightTripleEnergy gram 0 1 2 ≤ 4 / 3
        ∧ (2 / 3) * tightTripleEnergy gram 0 1 2 - 8 / 27
          ≤ 2 * |tripleEdgeProduct gram 0 1 2| := by
  rw [mem_centre_invariantLeverageCell_iff_invariants hgram 0 1 2,
    mem_centre_invariantLeverageCell_iff_invariants hgram 3 4 5,
    hgram.tightTripleEnergy_compl, hgram.tripleEdgeProduct_compl]
  rcases le_or_gt 0 (tripleEdgeProduct gram 0 1 2) with hsign | hsign
  · rw [abs_of_nonneg hsign]
    constructor
    · rintro (⟨henergy, hcoupling⟩ | ⟨henergy, hcoupling⟩) <;> exact ⟨henergy, by linarith⟩
    · rintro ⟨henergy, hcoupling⟩
      exact Or.inl ⟨henergy, by linarith⟩
  · rw [abs_of_neg hsign]
    constructor
    · rintro (⟨henergy, hcoupling⟩ | ⟨henergy, hcoupling⟩) <;> exact ⟨henergy, by linarith⟩
    · rintro ⟨henergy, hcoupling⟩
      exact Or.inr ⟨henergy, by linarith⟩

/-! ### The coupling never outruns the slack

Both `Gamma` and `2 . 1 - Gamma` square to twice themselves, so BOTH are positive
semidefinite, and so is every principal block of each.  The two block determinants
are the shipped `1 - E + 2 P` and `1 - E - 2 P`, so each is nonnegative.  That single
observation caps the energy at one and the coupling at half the slack, and it cuts
the eligible triples down from `E <= 4/3` to `E <= 7/9`. -/

/-- A symmetric array that squares to twice itself is positive semidefinite, because
its quadratic form is half a squared length. -/
theorem posSemidef_of_symm_of_sq_eq_two_smul {mat : Matrix (Fin 6) (Fin 6) ℝ}
    (hsymm : ∀ leftIndex rightIndex, mat rightIndex leftIndex = mat leftIndex rightIndex)
    (hsquare : mat * mat = (2 : ℝ) • mat) : mat.PosSemidef := by
  have htranspose : matᵀ = mat := by
    ext rowIndex colIndex
    exact hsymm rowIndex colIndex
  have hherm : mat.IsHermitian := by
    ext rowIndex colIndex
    simpa using hsymm rowIndex colIndex
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hherm, fun probe => ?_⟩
  rw [star_trivial]
  have hswap : probe ⬝ᵥ mat *ᵥ (mat *ᵥ probe) = (mat *ᵥ probe) ⬝ᵥ (mat *ᵥ probe) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, htranspose]
  have hdouble : probe ⬝ᵥ mat *ᵥ (mat *ᵥ probe) = 2 * (probe ⬝ᵥ mat *ᵥ probe) := by
    rw [Matrix.mulVec_mulVec, hsquare, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hsq : 0 ≤ (mat *ᵥ probe) ⬝ᵥ (mat *ᵥ probe) := by
    simpa using dotProduct_star_self_nonneg (mat *ᵥ probe)
  rw [hswap] at hdouble
  linarith

theorem IsTightGramSix.posSemidef {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) : gram.PosSemidef :=
  posSemidef_of_symm_of_sq_eq_two_smul hgram.comm hgram.idem

/-- The co-Gram `2 . 1 - Gamma` obeys the same square law, so it is also positive
semidefinite. -/
theorem IsTightGramSix.posSemidef_coGram {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) :
    ((2 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - gram).PosSemidef := by
  refine posSemidef_of_symm_of_sq_eq_two_smul (fun leftIndex rightIndex => ?_) ?_
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hgram.comm leftIndex rightIndex]
    rcases eq_or_ne leftIndex rightIndex with heq | hne
    · rw [heq]
    · rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne (Ne.symm hne)]
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hgram.idem]
    module

/-- **THE GRAM BLOCK DETERMINANT IS NONNEGATIVE**: `1 - E_T + 2 P_T >= 0`. -/
theorem IsTightGramSix.det_gramBlock_nonneg {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) (first second third : Fin 6) :
    0 ≤ 1 - tightTripleEnergy gram first second third
      + 2 * tripleEdgeProduct gram first second third := by
  rw [← hgram.det_gramBlock first second third]
  exact (hgram.posSemidef.submatrix ![first, second, third]).det_nonneg

/-- **THE CO-BLOCK DETERMINANT IS NONNEGATIVE**: `1 - E_T - 2 P_T >= 0`. -/
theorem IsTightGramSix.det_coGramBlock_nonneg {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    0 ≤ 1 - tightTripleEnergy gram first second third
      - 2 * tripleEdgeProduct gram first second third := by
  rw [← hgram.det_coGramBlock hfirstSecond hfirstThird hsecondThird]
  exact (hgram.posSemidef_coGram.submatrix ![first, second, third]).det_nonneg

/-- **EVERY TRIPLE ENERGY IS AT MOST ONE.**  The two block determinants add to
`2 (1 - E)`, and both are nonnegative.  The shipped mean is `3/5`, and this is the
first pointwise cap the campaign has. -/
theorem IsTightGramSix.tightTripleEnergy_le_one {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    tightTripleEnergy gram first second third ≤ 1 := by
  have hfront := hgram.det_gramBlock_nonneg first second third
  have hback := hgram.det_coGramBlock_nonneg hfirstSecond hfirstThird hsecondThird
  linarith

/-- **THE COUPLING IS AT MOST HALF THE SLACK**: `2 |P_T| <= 1 - E_T`.  The two block
determinants are the two signs of the same bound. -/
theorem IsTightGramSix.two_mul_abs_tripleEdgeProduct_le {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    2 * |tripleEdgeProduct gram first second third|
      ≤ 1 - tightTripleEnergy gram first second third := by
  have hfront := hgram.det_gramBlock_nonneg first second third
  have hback := hgram.det_coGramBlock_nonneg hfirstSecond hfirstThird hsecondThird
  rcases abs_cases (tripleEdgeProduct gram first second third) with ⟨heq, -⟩ | ⟨heq, -⟩ <;>
    rw [heq] <;> linarith

/-- **ONLY TRIPLES OF ENERGY AT MOST `7/9` CAN COVER THE CENTRE.**  The cell asks for
`2 P >= (2/3) E - 8/27` and the slack cap gives `2 P <= 1 - E`.  The two are
compatible only up to `7/9`, which is far under the `4/3` of the two-clause
criterion.  Every future producer may restrict its search to this band. -/
theorem IsTightGramSix.tightTripleEnergy_le_seven_ninths_of_mem_centre_cell
    {gram : Matrix (Fin 6) (Fin 6) ℝ} (hgram : IsTightGramSix gram)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hcell : centreLeverage ∈ invariantLeverageCell gram first second third) :
    tightTripleEnergy gram first second third ≤ 7 / 9 := by
  rw [mem_centre_invariantLeverageCell_iff_invariants hgram] at hcell
  have hslack := hgram.two_mul_abs_tripleEdgeProduct_le hfirstSecond hfirstThird hsecondThird
  have hle := le_abs_self (tripleEdgeProduct gram first second third)
  linarith [hcell.2]

/-! ### The local pair law

The tree owns ONE cancellation over the twenty triples.  Tightness gives fifteen:
one for each pair, read off a single off-diagonal entry of `Gamma^2 = 2 Gamma`.  The
four triples through a pair have edge products that already cancel among themselves,
and their four centre margins have a closed form in the pair correlation alone. -/

/-- **THE PAIR CANCELLATION.**  For distinct atoms the four other atoms contribute
correlations whose products cancel.  One entry of `Gamma^2 = 2 Gamma`, off the
diagonal. -/
theorem IsTightGramSix.sum_pair_product_eq_zero {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second : Fin 6} (hne : first ≠ second) :
    ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
      gram first other * gram other second = 0 := by
  have hentry : (gram * gram) first second = ((2 : ℝ) • gram) first second := by
    rw [hgram.idem]
  rw [Matrix.mul_apply] at hentry
  simp only [Matrix.smul_apply, smul_eq_mul] at hentry
  have hsplit : ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
        gram first other * gram other second
      + ∑ other ∈ ({first, second} : Finset (Fin 6)), gram first other * gram other second
      = ∑ other, gram first other * gram other second :=
    Finset.sum_sdiff (Finset.subset_univ _)
  have hpair : ∑ other ∈ ({first, second} : Finset (Fin 6)),
      gram first other * gram other second = 2 * gram first second := by
    rw [Finset.sum_pair hne, hgram.unit first, hgram.unit second]
    ring
  rw [hpair, hentry] at hsplit
  linarith

/-- **THE FOUR TRIPLES THROUGH A PAIR HAVE EDGE PRODUCTS SUMMING TO ZERO.**  Fifteen
cancellations, one for each pair, refining the single twenty-triple cancellation the
tree already owns. -/
theorem IsTightGramSix.sum_tripleEdgeProduct_through_pair {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second : Fin 6} (hne : first ≠ second) :
    ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
      tripleEdgeProduct gram first second other = 0 := by
  have hkey := hgram.sum_pair_product_eq_zero hne
  have hrewrite : ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
      tripleEdgeProduct gram first second other
      = gram first second * ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
        gram first other * gram other second := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun other _ => ?_
    rw [tripleEdgeProduct, hgram.comm second other]
    ring
  rw [hrewrite, hkey, mul_zero]

/-- **THE FOUR TRIPLE ENERGIES THROUGH A PAIR.**  Two row budgets and four copies of
the pair correlation. -/
theorem IsTightGramSix.sum_tightTripleEnergy_through_pair {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second : Fin 6} (hne : first ≠ second) :
    ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
      tightTripleEnergy gram first second other
      = 2 + 2 * (gram first second) ^ 2 := by
  have hcard : (Finset.univ \ ({first, second} : Finset (Fin 6))).card = 4 := by
    rw [Finset.card_univ_sdiff, Finset.card_pair hne]
    rfl
  have hrowFirst : ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
      (gram first other) ^ 2 = 1 - (gram first second) ^ 2 := by
    have hsplit : ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
          (gram first other) ^ 2
        + ∑ other ∈ ({first, second} : Finset (Fin 6)), (gram first other) ^ 2
        = ∑ other, (gram first other) ^ 2 :=
      Finset.sum_sdiff (Finset.subset_univ _)
    rw [Finset.sum_pair hne, hgram.unit first, hgram.sum_sq_row_eq_two first] at hsplit
    linarith
  have hrowSecond : ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
      (gram second other) ^ 2 = 1 - (gram first second) ^ 2 := by
    have hsplit : ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
          (gram second other) ^ 2
        + ∑ other ∈ ({first, second} : Finset (Fin 6)), (gram second other) ^ 2
        = ∑ other, (gram second other) ^ 2 :=
      Finset.sum_sdiff (Finset.subset_univ _)
    rw [Finset.sum_pair hne, hgram.unit second, hgram.sum_sq_row_eq_two second,
      hgram.comm first second] at hsplit
    linarith
  have hexpand : ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
        tightTripleEnergy gram first second other
      = ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
          ((gram first second) ^ 2 + (gram first other) ^ 2 + (gram second other) ^ 2) := by
    refine Finset.sum_congr rfl fun other _ => ?_
    rw [tightTripleEnergy]
  rw [hexpand, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, hcard,
    hrowFirst, hrowSecond]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **THE FOUR CENTRE MARGINS THROUGH A PAIR.**  A closed form in the pair correlation
alone: the local total is `-4/27 - (4/3) g^2`, best exactly where the pair is
orthogonal.  Summed over the fifteen pairs this reproduces the global `-56/27`, and
it is strictly finer, because it is local. -/
theorem IsTightGramSix.sum_centreMargin_through_pair {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second : Fin 6} (hne : first ≠ second) :
    ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
      centreMargin gram first second other
      = -(4 / 27) - (4 / 3) * (gram first second) ^ 2 := by
  have hcard : (Finset.univ \ ({first, second} : Finset (Fin 6))).card = 4 := by
    rw [Finset.card_univ_sdiff, Finset.card_pair hne]
    rfl
  have hexpand : ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
        centreMargin gram first second other
      = ∑ other ∈ Finset.univ \ ({first, second} : Finset (Fin 6)),
          (8 / 27 + 2 * tripleEdgeProduct gram first second other
            - (2 / 3) * tightTripleEnergy gram first second other) := by
    refine Finset.sum_congr rfl fun other _ => ?_
    rw [centreMargin]
  rw [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, hcard,
    ← Finset.mul_sum, ← Finset.mul_sum, hgram.sum_tripleEdgeProduct_through_pair hne,
    hgram.sum_tightTripleEnergy_through_pair hne]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-! ## 6. Two structural laws for the witnesses -/

/-- **THE BIPARTITE PRODUCT LAW.**  When the vanishing pairs of a symmetric array
contain every pair inside a two-part split, EVERY edge product vanishes.  Three
indices cannot occupy two parts without a repeat. -/
theorem tripleEdgeProduct_eq_zero_of_bipartite {gram : Matrix (Fin 6) (Fin 6) ℝ}
    {part : Fin 6 → Bool}
    (hzero : ∀ leftIndex rightIndex : Fin 6, leftIndex ≠ rightIndex →
      part leftIndex = part rightIndex → gram leftIndex rightIndex = 0)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    tripleEdgeProduct gram first second third = 0 := by
  have hpigeon : part first = part second ∨ part first = part third
      ∨ part second = part third := by
    cases hpartFirst : part first <;> cases hpartSecond : part second <;>
      cases hpartThird : part third <;> simp
  simp only [tripleEdgeProduct]
  rcases hpigeon with hsame | hsame | hsame
  · rw [hzero first second hfirstSecond hsame]
    ring
  · rw [hzero first third hfirstThird hsame]
    ring
  · rw [hzero second third hsecondThird hsame]
    ring

/-- **THE MATCHING ENERGY FLOOR.**  Suppose an involution marks the vanishing pairs
of an array, and every unmarked pair carries the same square `level`.  Then every
triple spends at least `2 * level`, because a triple meets the matching at most
once. -/
theorem tightTripleEnergy_ge_of_matching {gram : Matrix (Fin 6) (Fin 6) ℝ}
    {partner : Fin 6 → Fin 6} {level : ℝ}
    (hinvolutive : ∀ index : Fin 6, partner (partner index) = index)
    (hoff : ∀ leftIndex rightIndex : Fin 6, leftIndex ≠ rightIndex →
      rightIndex ≠ partner leftIndex → (gram leftIndex rightIndex) ^ 2 = level)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    2 * level ≤ tightTripleEnergy gram first second third := by
  simp only [tightTripleEnergy]
  by_cases hmatchFirstSecond : second = partner first
  · have hnotThird : third ≠ partner first := fun hthird =>
      hsecondThird (hmatchFirstSecond.trans hthird.symm)
    have hnotSecondThird : third ≠ partner second := by
      intro hthird
      apply hfirstThird
      rw [hthird, hmatchFirstSecond, hinvolutive]
    rw [hoff first third hfirstThird hnotThird, hoff second third hsecondThird hnotSecondThird]
    linarith [sq_nonneg (gram first second)]
  · rw [hoff first second hfirstSecond hmatchFirstSecond]
    by_cases hmatchFirstThird : third = partner first
    · have hnotSecondThird : third ≠ partner second := by
        intro hthird
        apply hfirstSecond
        have hpartnerEq : partner second = partner first := by rw [← hthird, hmatchFirstThird]
        have hswap := congrArg partner hpartnerEq
        rw [hinvolutive, hinvolutive] at hswap
        exact hswap.symm
      rw [hoff second third hsecondThird hnotSecondThird]
      linarith [sq_nonneg (gram first third)]
    · rw [hoff first third hfirstThird hmatchFirstThird]
      linarith [sq_nonneg (gram second third)]

/-! ## 7. Witness A, the six coordinate-plane diagonals

This is the design that the ledger of `Skeleton.obligationBaseTripleTightUThreeSix`
names as its non-vacuity witness: the six coordinate-plane diagonals at uniform
weight one sixth.  Its integer directions have squared length two, and their outer
products sum to four times the identity, so the unit atoms form a unit tight frame
of six vectors in `R^3`. -/

/-- The six coordinate-plane diagonals, as integer directions. -/
def crossWitnessDirection : Fin 6 → Fin 3 → ℝ :=
  ![![1, 1, 0], ![1, -1, 0], ![1, 0, 1], ![1, 0, -1], ![0, 1, 1], ![0, 1, -1]]

/-- The Gram of the six coordinate-plane diagonals, at unit atoms. -/
noncomputable def crossWitnessGram : Matrix (Fin 6) (Fin 6) ℝ :=
  !![    1,     0,   1 / 2,   1 / 2,   1 / 2,   1 / 2;
         0,     1,   1 / 2,   1 / 2, -(1 / 2), -(1 / 2);
     1 / 2, 1 / 2,       1,       0,   1 / 2, -(1 / 2);
     1 / 2, 1 / 2,       0,       1, -(1 / 2),   1 / 2;
     1 / 2, -(1 / 2), 1 / 2, -(1 / 2),     1,       0;
     1 / 2, -(1 / 2), -(1 / 2), 1 / 2,     0,       1]

/-- The Gram is the normalized direction Gram: each direction has squared length two. -/
theorem crossWitnessGram_eq_direction_dot (leftIndex rightIndex : Fin 6) :
    crossWitnessGram leftIndex rightIndex
      = (∑ coord, crossWitnessDirection leftIndex coord
          * crossWitnessDirection rightIndex coord) / 2 := by
  fin_cases leftIndex <;> fin_cases rightIndex <;>
    simp [crossWitnessGram, crossWitnessDirection, Fin.sum_univ_three] <;> norm_num

/-- **THE FRAME LAW.**  The outer products of the six directions sum to `4 I`, so the
unit atoms sum to `2 I` and the design is a unit tight frame at uniform weight one
sixth. -/
theorem sum_vecMulVec_crossWitnessDirection :
    ∑ atomIndex, Matrix.vecMulVec (crossWitnessDirection atomIndex)
        (crossWitnessDirection atomIndex)
      = (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply, crossWitnessDirection,
      Fin.sum_univ_six] <;> norm_num

theorem isTightGramSix_crossWitnessGram : IsTightGramSix crossWitnessGram := by
  refine ⟨?_, ?_, ?_⟩
  · intro leftIndex rightIndex
    fin_cases leftIndex <;> fin_cases rightIndex <;> norm_num [crossWitnessGram]
  · intro index
    fin_cases index <;> norm_num [crossWitnessGram]
  · ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.mul_apply, Matrix.smul_apply, crossWitnessGram, Fin.sum_univ_six] <;> norm_num

/-- The three entries of the star triple `{0,2,4}`.  A matrix literal at a numeral
index reduces definitionally, so each is a `rfl`. -/
theorem crossWitnessGram_zero_two : crossWitnessGram 0 2 = 1 / 2 := rfl

theorem crossWitnessGram_zero_four : crossWitnessGram 0 4 = 1 / 2 := rfl

theorem crossWitnessGram_two_four : crossWitnessGram 2 4 = 1 / 2 := rfl

/-- The matching of vanishing pairs: `{0,1}`, `{2,3}`, `{4,5}`. -/
def crossWitnessPartner : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

theorem crossWitnessPartner_involutive (index : Fin 6) :
    crossWitnessPartner (crossWitnessPartner index) = index := by
  fin_cases index <;> rfl

/-- Off the matching every squared correlation is exactly one quarter. -/
theorem crossWitnessGram_sq_off_matching {leftIndex rightIndex : Fin 6}
    (hne : leftIndex ≠ rightIndex) (hoff : rightIndex ≠ crossWitnessPartner leftIndex) :
    (crossWitnessGram leftIndex rightIndex) ^ 2 = 1 / 4 := by
  fin_cases leftIndex <;> fin_cases rightIndex <;>
    simp_all [crossWitnessGram, crossWitnessPartner] <;> norm_num

/-- **NO TRIPLE OF WITNESS A REACHES THE `4/9` THRESHOLD.**  Every triple spends at
least one half, because it meets the matching at most once. -/
theorem crossWitnessGram_energy_ge {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    1 / 2 ≤ tightTripleEnergy crossWitnessGram first second third := by
  have hfloor := tightTripleEnergy_ge_of_matching (gram := crossWitnessGram)
    (partner := crossWitnessPartner) (level := 1 / 4)
    crossWitnessPartner_involutive (fun _ _ hne hoff => crossWitnessGram_sq_off_matching hne hoff)
    hfirstSecond hfirstThird hsecondThird
  linarith

theorem crossWitnessGram_energy_gt_four_ninths {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    4 / 9 < tightTripleEnergy crossWitnessGram first second third := by
  have hfloor := crossWitnessGram_energy_ge hfirstSecond hfirstThird hsecondThird
  linarith

/-- The star triple `{0,2,4}` of witness A carries energy `3/4` and product `1/8`. -/
theorem crossWitnessGram_star_energy : tightTripleEnergy crossWitnessGram 0 2 4 = 3 / 4 := by
  rw [tightTripleEnergy, crossWitnessGram_zero_two, crossWitnessGram_zero_four,
    crossWitnessGram_two_four]
  norm_num

theorem crossWitnessGram_star_product : tripleEdgeProduct crossWitnessGram 0 2 4 = 1 / 8 := by
  rw [tripleEdgeProduct, crossWitnessGram_zero_two, crossWitnessGram_zero_four,
    crossWitnessGram_two_four]
  norm_num

/-- **THE EXACT MARGIN OF WITNESS A** is `5/108`, and it is positive. -/
theorem crossWitnessGram_star_centreMargin : centreMargin crossWitnessGram 0 2 4 = 5 / 108 := by
  rw [centreMargin_apply, crossWitnessGram_star_energy, crossWitnessGram_star_product]
  norm_num

/-- The three entries of the flat triple `{0,1,2}` of witness A. -/
theorem crossWitnessGram_zero_one : crossWitnessGram 0 1 = 0 := rfl

theorem crossWitnessGram_one_two : crossWitnessGram 1 2 = 1 / 2 := rfl

/-- **THE FLAT TRIPLE OF WITNESS A FAILS THE CENTRE**, with margin exactly `-1/27`.
So the covering of witness A is not generic.  It is carried by the coherent star and
by nothing else. -/
theorem crossWitnessGram_flat_centreMargin : centreMargin crossWitnessGram 0 1 2 = -(1 / 27) := by
  rw [centreMargin_apply, tightTripleEnergy, tripleEdgeProduct, crossWitnessGram_zero_one,
    crossWitnessGram_zero_two, crossWitnessGram_one_two]
  norm_num

theorem centreLeverage_notMem_invariantLeverageCell_crossWitness_flat :
    centreLeverage ∉ invariantLeverageCell crossWitnessGram 0 1 2 := by
  rw [mem_centre_invariantLeverageCell_iff isTightGramSix_crossWitnessGram,
    crossWitnessGram_flat_centreMargin]
  rintro ⟨-, -, -, hmargin⟩
  norm_num at hmargin

/-- The second star triple `{1,3,4}` of witness A carries the same margin `5/108`, so
the coherent star is a genuine orbit and not one accident. -/
theorem crossWitnessGram_one_three : crossWitnessGram 1 3 = 1 / 2 := rfl

theorem crossWitnessGram_one_four : crossWitnessGram 1 4 = -(1 / 2) := rfl

theorem crossWitnessGram_three_four : crossWitnessGram 3 4 = -(1 / 2) := rfl

theorem crossWitnessGram_second_star_centreMargin :
    centreMargin crossWitnessGram 1 3 4 = 5 / 108 := by
  rw [centreMargin_apply, tightTripleEnergy, tripleEdgeProduct, crossWitnessGram_one_three,
    crossWitnessGram_one_four, crossWitnessGram_three_four]
  norm_num

theorem centreLeverage_mem_invariantLeverageCell_crossWitness_second_star :
    centreLeverage ∈ invariantLeverageCell crossWitnessGram 1 3 4 := by
  rw [mem_centre_invariantLeverageCell_iff isTightGramSix_crossWitnessGram,
    crossWitnessGram_second_star_centreMargin, crossWitnessGram_one_three,
    crossWitnessGram_one_four, crossWitnessGram_three_four]
  norm_num

/-- **WITNESS A COVERS THE CENTRE.**  The design that the base-triple obligation names
as its non-vacuity witness dominates the centre of the polytope at its star triple. -/
theorem centreLeverage_mem_invariantLeverageCell_crossWitness :
    centreLeverage ∈ invariantLeverageCell crossWitnessGram 0 2 4 := by
  rw [mem_centre_invariantLeverageCell_iff isTightGramSix_crossWitnessGram,
    crossWitnessGram_star_centreMargin]
  rw [crossWitnessGram_zero_two, crossWitnessGram_zero_four, crossWitnessGram_two_four]
  norm_num

/-! ## 8. Witness B, the bipartite frame

Six integer directions of squared length nine whose nonzero correlation pattern is
the complete bipartite graph on the parts `{0,4,5}` and `{1,2,3}`.  A bipartite
pattern has no triangle, so every one of the twenty edge products vanishes. -/

/-- The bipartite frame, as integer directions of squared length nine. -/
def bipartiteWitnessDirection : Fin 6 → Fin 3 → ℝ :=
  ![![3, 0, 0], ![2, 2, 1], ![2, -1, -2], ![1, -2, 2], ![0, 3, 0], ![0, 0, 3]]

/-- The Gram of the bipartite frame, at unit atoms. -/
noncomputable def bipartiteWitnessGram : Matrix (Fin 6) (Fin 6) ℝ :=
  !![    1,   2 / 3,   2 / 3,   1 / 3,       0,       0;
     2 / 3,       1,       0,       0,   2 / 3,   1 / 3;
     2 / 3,       0,       1,       0, -(1 / 3), -(2 / 3);
     1 / 3,       0,       0,       1, -(2 / 3),   2 / 3;
         0,   2 / 3, -(1 / 3), -(2 / 3),     1,       0;
         0,   1 / 3, -(2 / 3),   2 / 3,      0,       1]

theorem bipartiteWitnessGram_eq_direction_dot (leftIndex rightIndex : Fin 6) :
    bipartiteWitnessGram leftIndex rightIndex
      = (∑ coord, bipartiteWitnessDirection leftIndex coord
          * bipartiteWitnessDirection rightIndex coord) / 9 := by
  fin_cases leftIndex <;> fin_cases rightIndex <;>
    simp [bipartiteWitnessGram, bipartiteWitnessDirection, Fin.sum_univ_three] <;> norm_num

/-- **THE FRAME LAW.**  The outer products sum to `18 I`, so the unit atoms sum to
`2 I` and the design is a unit tight frame at uniform weight one sixth. -/
theorem sum_vecMulVec_bipartiteWitnessDirection :
    ∑ atomIndex, Matrix.vecMulVec (bipartiteWitnessDirection atomIndex)
        (bipartiteWitnessDirection atomIndex)
      = (18 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply, bipartiteWitnessDirection,
      Fin.sum_univ_six] <;> norm_num

theorem isTightGramSix_bipartiteWitnessGram : IsTightGramSix bipartiteWitnessGram := by
  refine ⟨?_, ?_, ?_⟩
  · intro leftIndex rightIndex
    fin_cases leftIndex <;> fin_cases rightIndex <;> norm_num [bipartiteWitnessGram]
  · intro index
    fin_cases index <;> norm_num [bipartiteWitnessGram]
  · ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.mul_apply, Matrix.smul_apply, bipartiteWitnessGram, Fin.sum_univ_six] <;>
      norm_num

/-- The three entries of the decoupled triple `{0,4,5}`. -/
theorem bipartiteWitnessGram_zero_four : bipartiteWitnessGram 0 4 = 0 := rfl

theorem bipartiteWitnessGram_zero_five : bipartiteWitnessGram 0 5 = 0 := rfl

theorem bipartiteWitnessGram_four_five : bipartiteWitnessGram 4 5 = 0 := rfl

/-- The bipartition `{0,4,5}` against `{1,2,3}`. -/
def bipartiteWitnessPart : Fin 6 → Bool := ![false, true, true, true, false, false]

/-- Inside a part every correlation vanishes. -/
theorem bipartiteWitnessGram_eq_zero_of_samePart {leftIndex rightIndex : Fin 6}
    (hne : leftIndex ≠ rightIndex)
    (hsame : bipartiteWitnessPart leftIndex = bipartiteWitnessPart rightIndex) :
    bipartiteWitnessGram leftIndex rightIndex = 0 := by
  fin_cases leftIndex <;> fin_cases rightIndex <;>
    simp_all [bipartiteWitnessGram, bipartiteWitnessPart]

/-- **EVERY EDGE PRODUCT OF WITNESS B VANISHES.**  So no averaged coupling price is
available on the flat locus. -/
theorem bipartiteWitnessGram_tripleEdgeProduct_eq_zero {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    tripleEdgeProduct bipartiteWitnessGram first second third = 0 :=
  tripleEdgeProduct_eq_zero_of_bipartite
    (fun _ _ hne hsame => bipartiteWitnessGram_eq_zero_of_samePart hne hsame)
    hfirstSecond hfirstThird hsecondThird

/-- Witness B has a decoupled triple at `{0,4,5}`. -/
theorem bipartiteWitnessGram_star_centreMargin :
    centreMargin bipartiteWitnessGram 0 4 5 = 8 / 27 :=
  centreMargin_of_orthogonal bipartiteWitnessGram_zero_four bipartiteWitnessGram_zero_five
    bipartiteWitnessGram_four_five

/-- **WITNESS B COVERS THE CENTRE**, with the largest margin the cap permits. -/
theorem centreLeverage_mem_invariantLeverageCell_bipartiteWitness :
    centreLeverage ∈ invariantLeverageCell bipartiteWitnessGram 0 4 5 :=
  mem_centre_invariantLeverageCell_of_orthogonal isTightGramSix_bipartiteWitnessGram
    bipartiteWitnessGram_zero_four bipartiteWitnessGram_zero_five
    bipartiteWitnessGram_four_five

/-- Witness A's star energy sits just under the eligibility band `7/9`.  The design
that the base-triple obligation names as its non-vacuity witness is therefore the
tightest covering the campaign has found, and the band explains why. -/
theorem crossWitnessGram_star_energy_lt_seven_ninths :
    tightTripleEnergy crossWitnessGram 0 2 4 < 7 / 9 := by
  rw [crossWitnessGram_star_energy]
  norm_num

/-- **THE BASE-TRIPLE OBLIGATION'S OWN WITNESS, DECIDED.**  The ledger of
`Skeleton.obligationStressFreeHingeSixThree` names the six coordinate-plane diagonals
at uniform weight one sixth as the design that makes the stratum inhabited.  That
design is `Gtz.crossWitnessGram`.  It is a unit tight frame, every one of its twenty
triples is above the `4/9` threshold, its flat triple FAILS the centre, and its
coherent star covers with margin exactly `5/108`. -/
theorem crossWitnessGram_centre_ledger :
    IsTightGramSix crossWitnessGram
      ∧ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
          4 / 9 < tightTripleEnergy crossWitnessGram first second third)
      ∧ centreLeverage ∈ invariantLeverageCell crossWitnessGram 0 2 4
      ∧ centreLeverage ∉ invariantLeverageCell crossWitnessGram 0 1 2
      ∧ centreMargin crossWitnessGram 0 2 4 = 5 / 108
      ∧ centreMargin crossWitnessGram 0 1 2 = -(1 / 27) :=
  ⟨isTightGramSix_crossWitnessGram,
    fun _ _ _ hfirstSecond hfirstThird hsecondThird =>
      crossWitnessGram_energy_gt_four_ninths hfirstSecond hfirstThird hsecondThird,
    centreLeverage_mem_invariantLeverageCell_crossWitness,
    centreLeverage_notMem_invariantLeverageCell_crossWitness_flat,
    crossWitnessGram_star_centreMargin, crossWitnessGram_flat_centreMargin⟩

/-! ## 9. The two-sided no-go -/

/-- **NO ENERGY-ONLY CERTIFICATE COVERS THE CENTRE.**  A tight Gram exists whose every
triple is above the `4/9` threshold and which is still covered.  Any producer that
concludes only from an energy bound must therefore fail on this design, and the
design is the non-vacuity witness of the base-triple obligation. -/
theorem exists_tight_energy_route_insufficient :
    ∃ gram : Matrix (Fin 6) (Fin 6) ℝ, IsTightGramSix gram
      ∧ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
          4 / 9 < tightTripleEnergy gram first second third)
      ∧ centreLeverage ∈ invariantLeverageCell gram 0 2 4 :=
  ⟨crossWitnessGram, isTightGramSix_crossWitnessGram,
    fun _ _ _ hfirstSecond hfirstThird hsecondThird =>
      crossWitnessGram_energy_gt_four_ninths hfirstSecond hfirstThird hsecondThird,
    centreLeverage_mem_invariantLeverageCell_crossWitness⟩

/-- **NO PRODUCT-ONLY CERTIFICATE COVERS THE CENTRE.**  A tight Gram exists whose
twenty edge products all vanish and which is still covered.  Any producer that
concludes from a positive coupling, whether at one triple or averaged over the ten
complementary pairs, fails on this design. -/
theorem exists_tight_product_route_insufficient :
    ∃ gram : Matrix (Fin 6) (Fin 6) ℝ, IsTightGramSix gram
      ∧ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
          tripleEdgeProduct gram first second third = 0)
      ∧ centreLeverage ∈ invariantLeverageCell gram 0 4 5 :=
  ⟨bipartiteWitnessGram, isTightGramSix_bipartiteWitnessGram,
    fun _ _ _ hfirstSecond hfirstThird hsecondThird =>
      bipartiteWitnessGram_tripleEdgeProduct_eq_zero hfirstSecond hfirstThird hsecondThird,
    centreLeverage_mem_invariantLeverageCell_bipartiteWitness⟩

/-- **THE COUPLING PRICE IS REFUTED.**  There is no positive constant `price` for which
"some triple has edge product at least `price`" holds on the flat locus.  Witness B
sends every edge product to zero. -/
theorem not_forall_exists_pos_tripleEdgeProduct (price : ℝ) (hprice : 0 < price) :
    ¬ ∀ gram : Matrix (Fin 6) (Fin 6) ℝ, IsTightGramSix gram →
        ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
          ∧ price ≤ tripleEdgeProduct gram first second third := by
  intro hclaim
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hlarge⟩ :=
    hclaim bipartiteWitnessGram isTightGramSix_bipartiteWitnessGram
  rw [bipartiteWitnessGram_tripleEdgeProduct_eq_zero hfirstSecond hfirstThird hsecondThird]
    at hlarge
  linarith

/-- **THE TWO REGIMES ARE INDEPENDENT.**  On witness A the energy regime never fires.
On witness B the coherent regime never fires.  Each design is still covered, so a
producer for the centre must read the energy AND the coupling.  No refinement of one
invariant alone can close the covering statement. -/
theorem centre_regimes_independent :
    (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
        ¬ tightTripleEnergy crossWitnessGram first second third ≤ 4 / 9)
      ∧ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
        ¬ 0 < tripleEdgeProduct bipartiteWitnessGram first second third) := by
  constructor
  · intro _ _ _ hfirstSecond hfirstThird hsecondThird hbound
    have hfloor := crossWitnessGram_energy_gt_four_ninths hfirstSecond hfirstThird hsecondThird
    linarith
  · intro _ _ _ hfirstSecond hfirstThird hsecondThird hpos
    rw [bipartiteWitnessGram_tripleEdgeProduct_eq_zero hfirstSecond hfirstThird hsecondThird]
      at hpos
    exact lt_irrefl 0 hpos

/-! ## 10. The centre as a necessary condition on the conjecture

The centre is ONE point of the design region, so the shipped covering equivalence
turns every theorem above into a constraint on `Gtz.GtzUniformShareSixThree`
itself. -/

/-- **THE CENTRE COVERING**, the residual this module leaves.  It is the covering
statement of `Gtz.gtzUniformShareSixThree_iff_forall_coversInvariantLeverageDesignRegion`
restricted to the single point `nu == 1/3`. -/
def CoversCentre (gram : Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
  ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
    ∧ centreLeverage ∈ invariantLeverageCell gram first second third

/-- Covering the design region covers the centre, because the centre is a point of
the region. -/
theorem coversCentre_of_coversInvariantLeverageRegion {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hcovers : CoversInvariantLeverageRegion gram invariantLeverageDesignRegion) :
    CoversCentre gram :=
  hcovers centreLeverage centreLeverage_mem_invariantLeverageDesignRegion

/-- **THE CONJECTURE FORCES THE CENTRE.**  Every unit-norm tight frame of six
directions in `R^3` must cover `nu == 1/3`, or `Gtz.GtzUniformShareSixThree` is
false. -/
theorem coversCentre_of_gtzUniformShareSixThree (hgtz : GtzUniformShareSixThree)
    (frame : Matrix (Fin 6) (Fin 3) ℝ) (hframe : IsUnitTightFrameSix frame) :
    CoversCentre (frame * frameᵀ) :=
  coversCentre_of_coversInvariantLeverageRegion
    (gtzUniformShareSixThree_iff_forall_coversInvariantLeverageDesignRegion.mp hgtz frame hframe)

/-- **ONE POINT REFUTES THE CONJECTURE.**  A single tight frame whose twenty triples
all fail at `nu == 1/3` kills `Gtz.GtzUniformShareSixThree` outright.  This is the
cheapest refutation channel the campaign owns: one rational frame, twenty rational
determinants, no search over the polytope. -/
theorem not_gtzUniformShareSixThree_of_not_coversCentre
    (frame : Matrix (Fin 6) (Fin 3) ℝ) (hframe : IsUnitTightFrameSix frame)
    (hfail : ¬ CoversCentre (frame * frameᵀ)) : ¬ GtzUniformShareSixThree :=
  fun hgtz => hfail (coversCentre_of_gtzUniformShareSixThree hgtz frame hframe)

/-- **THE ENERGY PRODUCER FOR THE CENTRE RESIDUAL.**  One energy bound at the front
triple discharges the whole residual, by the complement involution. -/
theorem coversCentre_of_tightTripleEnergy_le {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) (henergy : tightTripleEnergy gram 0 1 2 ≤ 4 / 9) :
    CoversCentre gram := by
  rcases hgram.exists_mem_centre_invariantLeverageCell_compl henergy with hfront | hback
  · exact ⟨0, 1, 2, by decide, by decide, by decide, hfront⟩
  · exact ⟨3, 4, 5, by decide, by decide, by decide, hback⟩

/-- **THE CENTRE RESIDUAL, AS ONE SCALAR INEQUALITY.**  One pair whose absolute
coupling clears `(1/3) E - 4/27` discharges the centre for the whole design.  With
`Gtz.IsTightGramSix.exists_tripleEnergy_le_three_fifths` the energy clause is free at
the mean, where the threshold is the shipped `7/135`. -/
theorem coversCentre_of_abs_tripleEdgeProduct_ge {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) (henergy : tightTripleEnergy gram 0 1 2 ≤ 4 / 3)
    (hcoupling : tightTripleEnergy gram 0 1 2 / 3 - 4 / 27
      ≤ |tripleEdgeProduct gram 0 1 2|) :
    CoversCentre gram := by
  rcases (hgram.mem_centre_invariantLeverageCell_front_or_back_iff).mpr
    ⟨henergy, by linarith⟩ with hfront | hback
  · exact ⟨0, 1, 2, by decide, by decide, by decide, hfront⟩
  · exact ⟨3, 4, 5, by decide, by decide, by decide, hback⟩

/-- **THE DECOUPLED PRODUCER FOR THE CENTRE RESIDUAL.** -/
theorem coversCentre_of_orthogonal {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix gram) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) (hone : gram first second = 0)
    (htwo : gram first third = 0) (hthree : gram second third = 0) :
    CoversCentre gram :=
  ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    mem_centre_invariantLeverageCell_of_orthogonal hgram hone htwo hthree⟩

/-- Witness A discharges the residual through the coherent star. -/
theorem coversCentre_crossWitnessGram : CoversCentre crossWitnessGram :=
  ⟨0, 2, 4, by decide, by decide, by decide,
    centreLeverage_mem_invariantLeverageCell_crossWitness⟩

/-- Witness B discharges the residual through the decoupled triple. -/
theorem coversCentre_bipartiteWitnessGram : CoversCentre bipartiteWitnessGram :=
  ⟨0, 4, 5, by decide, by decide, by decide,
    centreLeverage_mem_invariantLeverageCell_bipartiteWitness⟩

/-! ## 11. The centre cell IS the GTZ second moment at uniform weight

The cell test at the centre reads the Gram block `Gamma[T]`.  The GTZ objective
reads the second-moment matrix `M_T = sum over T of v v transpose`.  For a triple
the two are `A A transpose` and `A transpose A` of ONE square array of atoms, so
their shifted determinants agree.  The centre of the polytope is therefore not an
auxiliary coordinate: it is the uniform-weight instance of the objective. -/

/-- The characteristic value of a three-by-three array at a shift, in the three
trace invariants.  Elementary, and it is what makes the transpose swap free. -/
theorem det_sub_smul_one_fin_three (block : Matrix (Fin 3) (Fin 3) ℝ) (shift : ℝ) :
    (block - shift • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      = -shift ^ 3 + shift ^ 2 * block.trace
        - shift * ((block.trace ^ 2 - (block * block).trace) / 2) + block.det := by
  simp only [Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply_eq, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 1),
    Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 2),
    Matrix.one_apply_ne (by decide : (1 : Fin 3) ≠ 0),
    Matrix.one_apply_ne (by decide : (1 : Fin 3) ≠ 2),
    Matrix.one_apply_ne (by decide : (2 : Fin 3) ≠ 0),
    Matrix.one_apply_ne (by decide : (2 : Fin 3) ≠ 1)]
  ring

/-- **THE TRANSPOSE SWAP.**  A square array and its transpose give the same shifted
determinant, because trace, squared trace and determinant all commute under the
swap.  No spectral theory is spent. -/
theorem det_mul_transpose_sub_smul_one_comm (atoms : Matrix (Fin 3) (Fin 3) ℝ) (shift : ℝ) :
    (atoms * atomsᵀ - shift • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      = (atomsᵀ * atoms - shift • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det := by
  have htrace : (atoms * atomsᵀ).trace = (atomsᵀ * atoms).trace :=
    Matrix.trace_mul_comm atoms atomsᵀ
  have hsquare : (atoms * atomsᵀ * (atoms * atomsᵀ)).trace
      = (atomsᵀ * atoms * (atomsᵀ * atoms)).trace := by
    have hshape : atoms * atomsᵀ * (atoms * atomsᵀ) = atoms * (atomsᵀ * atoms * atomsᵀ) := by
      simp [Matrix.mul_assoc]
    have hother : atomsᵀ * atoms * atomsᵀ * atoms = atomsᵀ * atoms * (atomsᵀ * atoms) := by
      simp [Matrix.mul_assoc]
    rw [hshape, Matrix.trace_mul_comm atoms (atomsᵀ * atoms * atomsᵀ), hother]
  have hdet : (atoms * atomsᵀ).det = (atomsᵀ * atoms).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_comm]
  rw [det_sub_smul_one_fin_three, det_sub_smul_one_fin_three, htrace, hsquare, hdet]

/-- The three atoms of a triple, as a square array. -/
def tripleAtoms (frame : Matrix (Fin 6) (Fin 3) ℝ) (first second third : Fin 6) :
    Matrix (Fin 3) (Fin 3) ℝ := frame.submatrix ![first, second, third] id

/-- **THE SECOND MOMENT OF A TRIPLE**: `M_T = sum over T of v v transpose`, the matrix
the GTZ objective reads. -/
def tripleSecondMoment (frame : Matrix (Fin 6) (Fin 3) ℝ) (first second third : Fin 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (tripleAtoms frame first second third)ᵀ * tripleAtoms frame first second third

theorem tripleSecondMoment_apply (frame : Matrix (Fin 6) (Fin 3) ℝ)
    (first second third : Fin 6) (rowIndex colIndex : Fin 3) :
    tripleSecondMoment frame first second third rowIndex colIndex
      = frame first rowIndex * frame first colIndex
        + frame second rowIndex * frame second colIndex
        + frame third rowIndex * frame third colIndex := by
  simp only [tripleSecondMoment, tripleAtoms, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, id_eq, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- The Gram block of a triple is the outer square of its atom array. -/
theorem frameGram_submatrix_eq (frame : Matrix (Fin 6) (Fin 3) ℝ)
    (first second third : Fin 6) :
    (frame * frameᵀ).submatrix ![first, second, third] ![first, second, third]
      = tripleAtoms frame first second third * (tripleAtoms frame first second third)ᵀ := by
  ext rowIndex colIndex
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, tripleAtoms,
    id_eq]

/-- The centre shift is a scalar multiple of the identity. -/
theorem diagonal_centreLeverage_eq (first second third : Fin 6) :
    Matrix.diagonal (fun slot => centreLeverage (![first, second, third] slot))
      = (1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  rcases eq_or_ne rowIndex colIndex with heq | hne
  · subst heq
    simp
  · simp [Matrix.diagonal_apply_ne _ hne, Matrix.one_apply_ne hne]

/-- **THE CENTRE MARGIN IS THE SHIFTED SECOND-MOMENT DETERMINANT.**  For every triple
of a unit-norm tight frame,

    `centreMargin = det (M_T - (1/3) I)`,

so the cell test at `nu == 1/3` reads the GTZ objective matrix directly.  The centre
of the invariant-leverage polytope is the uniform-weight instance of the objective,
and not an auxiliary coordinate. -/
theorem centreMargin_frameGram_eq_det_tripleSecondMoment
    (frame : Matrix (Fin 6) (Fin 3) ℝ) (hframe : IsUnitTightFrameSix frame)
    (first second third : Fin 6) :
    centreMargin (frame * frameᵀ) first second third
      = (tripleSecondMoment frame first second third
          - (1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det := by
  have hgram := isTightGramSix_frameGram hframe
  have hblock := submatrix_sub_centre_eq_slackHollowThree hgram first second third
  rw [diagonal_centreLeverage_eq, frameGram_submatrix_eq] at hblock
  rw [centreMargin_eq_slackDeterminantThree, ← det_slackHollowThree, ← hblock,
    det_mul_transpose_sub_smul_one_comm]
  rfl

/-- **THE CENTRE COVERING IS A SECOND-MOMENT STATEMENT.**  A triple covers the centre
only if its second moment has nonnegative shifted determinant.  With
`Gtz.not_gtzUniformShareSixThree_of_not_coversCentre` this puts the whole conjecture
under one determinant test per triple, at one point of the polytope. -/
theorem det_tripleSecondMoment_nonneg_of_mem_centre_invariantLeverageCell
    {frame : Matrix (Fin 6) (Fin 3) ℝ} (hframe : IsUnitTightFrameSix frame)
    {first second third : Fin 6}
    (hcell : centreLeverage ∈ invariantLeverageCell (frame * frameᵀ) first second third) :
    0 ≤ (tripleSecondMoment frame first second third
      - (1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det := by
  rw [← centreMargin_frameGram_eq_det_tripleSecondMoment frame hframe]
  rw [mem_centre_invariantLeverageCell_iff (isTightGramSix_frameGram hframe)] at hcell
  exact hcell.2.2.2

/-- The same reading of the residual: `Gtz.CoversCentre` supplies a triple whose
second moment clears the shifted determinant test. -/
theorem exists_det_tripleSecondMoment_nonneg_of_coversCentre
    {frame : Matrix (Fin 6) (Fin 3) ℝ} (hframe : IsUnitTightFrameSix frame)
    (hcovers : CoversCentre (frame * frameᵀ)) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 ≤ (tripleSecondMoment frame first second third
          - (1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcell⟩ := hcovers
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    det_tripleSecondMoment_nonneg_of_mem_centre_invariantLeverageCell hframe hcell⟩

/-! ## 12. Witness B as a rational unit tight frame

Witness B has integer directions of squared length nine, so dividing by three gives
a unit tight frame with RATIONAL entries.  The whole centre analysis therefore lands
on an explicit `(6,3)` design and not only on an abstract Gram. -/

/-- The bipartite witness as a rational unit tight frame of six directions in `R^3`. -/
noncomputable def bipartiteWitnessFrame : Matrix (Fin 6) (Fin 3) ℝ :=
  !![    1,       0,       0;
     2 / 3,   2 / 3,   1 / 3;
     2 / 3, -(1 / 3), -(2 / 3);
     1 / 3, -(2 / 3),   2 / 3;
         0,       1,       0;
         0,       0,       1]

theorem isUnitTightFrameSix_bipartiteWitnessFrame :
    IsUnitTightFrameSix bipartiteWitnessFrame where
  unit := by
    intro index
    fin_cases index <;>
      norm_num [leverageOf, bipartiteWitnessFrame, Fin.sum_univ_three,
        Matrix.cons_val_two, Matrix.tail_cons]
  tight := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.mul_apply, Matrix.smul_apply, bipartiteWitnessFrame,
        Fin.sum_univ_six] <;> norm_num

/-- The frame reproduces the Gram of section 8. -/
theorem bipartiteWitnessFrame_gram :
    bipartiteWitnessFrame * bipartiteWitnessFrameᵀ = bipartiteWitnessGram := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.mul_apply, bipartiteWitnessFrame, bipartiteWitnessGram,
      Fin.sum_univ_three] <;> norm_num

/-- **THE DECOUPLED TRIPLE OF WITNESS B HAS SECOND MOMENT EXACTLY THE IDENTITY.**  Its
three atoms are the standard basis, so the GTZ objective matrix is `I`, which beats
the centre threshold `(1/3) I` by the widest margin the cap allows. -/
theorem bipartiteWitnessFrame_star_rows :
    bipartiteWitnessFrame 0 = ![1, 0, 0] ∧ bipartiteWitnessFrame 4 = ![0, 1, 0]
      ∧ bipartiteWitnessFrame 5 = ![0, 0, 1] := ⟨rfl, rfl, rfl⟩

theorem tripleSecondMoment_bipartiteWitnessFrame_star :
    tripleSecondMoment bipartiteWitnessFrame 0 4 5 = 1 := by
  ext rowIndex colIndex
  rw [tripleSecondMoment_apply, bipartiteWitnessFrame_star_rows.1,
    bipartiteWitnessFrame_star_rows.2.1, bipartiteWitnessFrame_star_rows.2.2]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- The residual is discharged on an explicit rational `(6,3)` design. -/
theorem coversCentre_bipartiteWitnessFrame :
    CoversCentre (bipartiteWitnessFrame * bipartiteWitnessFrameᵀ) := by
  rw [bipartiteWitnessFrame_gram]
  exact coversCentre_bipartiteWitnessGram

/-- The shifted second-moment determinant of that triple is the cap `8/27`. -/
theorem det_tripleSecondMoment_bipartiteWitnessFrame_star :
    (tripleSecondMoment bipartiteWitnessFrame 0 4 5
      - (1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 8 / 27 := by
  rw [← centreMargin_frameGram_eq_det_tripleSecondMoment bipartiteWitnessFrame
    isUnitTightFrameSix_bipartiteWitnessFrame, bipartiteWitnessFrame_gram,
    bipartiteWitnessGram_star_centreMargin]

/-! ## 13. The centre block IS the flat-locus gap block, doubled

The complement-dual lane works with the rank-three projection `P`, whose diagonal is
one half, and asks for `Gtz.blockGapAt P sixthWeight` to be positive.  A tight Gram is
`Gamma = 2 P`.  So the centre block of this module and the gap block of that lane are
the SAME object up to the factor two, and the centre margin is eight times the flat
gap determinant.  The two lanes are one lane. -/

/-- **THE LANE BRIDGE.**  The centre block at `nu == 1/3` of `2 P` is twice the shipped
gap block of `P` at uniform weight one sixth.  Pure algebra: `1/3 = 2 * (1/6)`. -/
theorem centreBlock_eq_two_smul_blockGapAt (form : Matrix (Fin 6) (Fin 6) ℝ)
    (first second third : Fin 6) :
    ((2 : ℝ) • form).submatrix ![first, second, third] ![first, second, third]
        - Matrix.diagonal (fun slot => centreLeverage (![first, second, third] slot))
      = (2 : ℝ) • blockGapAt form sixthWeight ![first, second, third] := by
  ext rowIndex colIndex
  simp only [blockGapAt, Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply,
    smul_eq_mul, centreLeverage_apply, sixthWeight]
  rcases eq_or_ne rowIndex colIndex with heq | hne
  · subst heq
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    ring
  · rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hne]
    ring

/-- **THE CENTRE MARGIN IS EIGHT TIMES THE FLAT GAP DETERMINANT.**  Every constant of
this module is a constant of the complement-dual lane, scaled by eight.  The cap
`8/27` here is the shipped cap `1/27` there, and the total `-56/27` here is `-7/27`
there. -/
theorem centreMargin_eq_eight_mul_det_blockGapAt {form : Matrix (Fin 6) (Fin 6) ℝ}
    (hgram : IsTightGramSix ((2 : ℝ) • form)) (first second third : Fin 6) :
    centreMargin ((2 : ℝ) • form) first second third
      = 8 * (blockGapAt form sixthWeight ![first, second, third]).det := by
  have hblock := submatrix_sub_centre_eq_slackHollowThree hgram first second third
  rw [centreMargin_eq_slackDeterminantThree, ← det_slackHollowThree, ← hblock,
    centreBlock_eq_two_smul_blockGapAt, Matrix.det_smul]
  norm_num

end Gtz

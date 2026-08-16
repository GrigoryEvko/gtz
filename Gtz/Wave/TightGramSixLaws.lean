/-
# The correlation budget of a six-atom tight Gram, and the weak triangle

The `(6,3)` covering statement of `Gtz/Quantitative/SixThreeNuCovering.lean` reads
the twenty cells `K_T = {nu : Gamma[T] ⪰ diag(nu)|_T}` against the hypersimplex
`Delta = {nu in [0,1]^6 : sum nu = 2}`.  Every cell is convex, closed, three-local
and monotone, and the shipped band gate covers `max_c nu_c <= 9/25`.  What no file
carries is a budget on `Gamma` itself.

This module supplies it.  A unit tight frame of six unit vectors in `R^3` has
`Gamma = F F^T` with `F^T F = 2 . 1`, hence

    `Gamma * Gamma = 2 . Gamma`,

which is the ONLY hypothesis used here.  Everything below is a consequence of that
one identity together with the unit diagonal, and none of it mentions a frame, a
design, a weight or a share.

## What is new

1. **The row budget.**  `Gtz.IsTightGramSix.sum_sq_erase_eq_one`: the five
   off-diagonal squares of any row sum to EXACTLY `1`.  The corpus carries the
   design-level row law `sum_{d != c} P_cd^2 = t_c (1 - t_c)`; at a tight Gram the
   leverage diagonal is flat and the law becomes a constant, which is what makes
   the counting below work.

2. **The strong graph is a matching.**  `Gtz.IsTightGramSix.not_two_strong_partners`:
   no atom has two partners of squared correlation above `1/2`, because two such
   already overrun the row budget.  Hence `Gtz.IsTightGramSix.not_strongTriangle`.

3. **THE WEAK TRIANGLE, and it is the headline.**
   `Gtz.IsTightGramSix.exists_weak_triple`: every tight Gram at six atoms carries
   three atoms whose three squared correlations are all at most `1/2`.  The proof
   feeds the matching bound into the landed Ramsey bound `R(3,3) <= 6`
   (`Gtz.exists_mono_triple_of_six`): the monochromatic triple cannot be the strong
   one, so it is the weak one.  Neither half is available alone — the budget alone
   permits three strong edges, and Ramsey alone permits a strong triangle.

4. **The correlation first moment, and it is SHARP.**
   `Gtz.IsTightGramSix.exists_tripleEnergy_le_three_fifths`: some triple has
   `gamma_ab^2 + gamma_ac^2 + gamma_bc^2 <= 3/5`.  The route is an exact counting
   identity, `Gtz.sum_tripleEnergy_eq_four_mul_offDiagEnergy`: each of the fifteen
   pairs lies in exactly four of the twenty triples, so the twenty triple energies
   total `4 * 3 = 12` and the least is at most `3/5`.
   `Gtz.tripleEnergy_eq_three_fifths_of_equicorrelated` shows the equiangular Gram
   attains `3/5` at EVERY triple, so `3/5` cannot be lowered.

5. **The pair budget and its thirds refinement.**
   `Gtz.IsTightGramSix.sq_add_sq_le_one` and
   `Gtz.IsTightGramSix.not_three_third_partners`, with
   `Gtz.IsTightGramSix.tripleEnergy_le_three_halves` as the free per-triple cap.

6. **The covering corollaries.**  `Gtz.IsTightGramSix.pairMinors_of_weak_triple`
   discharges two of the three Sylvester conditions on the weak triple as soon as
   the complementary coordinates clear `1/2` in product, and
   `Gtz.IsTightGramSix.posSemidef_block_of_weak_triple` assembles the block
   statement through the shipped `Gtz.posSemidef_slackHollowThree_iff`.

## What is NOT proved

**The covering itself.**  The weak triangle bounds the correlations at `1/2` and
the pair minors need `x_a x_b >= gamma_ab^2`, so a weak triple certifies only where
the complementary coordinates are large.  The determinant clause is untouched by
the threshold `1/2`, and at the equiangular Gram every triple has energy exactly
`3/5`, where the determinant is carried by the SIGN of `gamma_ab gamma_ac gamma_bc`
and by nothing else.  No statement here asserts the covering, `V6`,
`GtzUniformShareSixThree` or `GtzWeighted 6 3`, and the gap `9/25 -> 1` recorded in
`Gtz/Quantitative/SixThreeNuCovering.lean` is not narrowed.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.WeightedTripleCriterion
import Gtz.Quantitative.SixThreeNuCovering
import Gtz.Wave.QuarterSlackGraph

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## 1. The tight Gram -/

/-- **A TIGHT GRAM AT SIX ATOMS.**  Symmetric, unit diagonal, and idempotent up to
the factor two.  A unit tight frame of six unit vectors in `R^3` produces one, and
the three fields are the only hypotheses this module uses. -/
structure IsTightGramSix (gram : Matrix (Fin 6) (Fin 6) ℝ) : Prop where
  /-- The Gram is symmetric. -/
  comm : ∀ leftIndex rightIndex, gram rightIndex leftIndex = gram leftIndex rightIndex
  /-- Every atom is a unit vector. -/
  unit : ∀ index, gram index index = 1
  /-- Tightness, transported to the Gram: `Gamma^2 = 2 Gamma`. -/
  idem : gram * gram = (2 : ℝ) • gram

namespace IsTightGramSix

variable {gram : Matrix (Fin 6) (Fin 6) ℝ}

/-- **THE ROW LAW.**  Every row of a tight Gram has squared length two. -/
theorem sum_sq_row_eq_two (htight : IsTightGramSix gram) (rowIndex : Fin 6) :
    ∑ colIndex, (gram rowIndex colIndex) ^ 2 = 2 := by
  have hentry : (gram * gram) rowIndex rowIndex = ((2 : ℝ) • gram) rowIndex rowIndex := by
    rw [htight.idem]
  rw [Matrix.mul_apply] at hentry
  simp only [Matrix.smul_apply, smul_eq_mul, htight.unit rowIndex, mul_one] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl fun colIndex _ => ?_
  rw [htight.comm rowIndex colIndex, sq]

/-- **THE ROW BUDGET.**  The five off-diagonal squares of a row sum to exactly one.
This is the constant the whole module spends. -/
theorem sum_sq_erase_eq_one (htight : IsTightGramSix gram) (rowIndex : Fin 6) :
    ∑ colIndex ∈ Finset.univ.erase rowIndex, (gram rowIndex colIndex) ^ 2 = 1 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ rowIndex), sum_sq_row_eq_two htight rowIndex,
    htight.unit rowIndex]
  norm_num

/-- **THE PAIR BUDGET.**  Two distinct partners of a common atom cannot carry more
than the whole row. -/
theorem sq_add_sq_le_one (htight : IsTightGramSix gram) {centre first second : Fin 6}
    (hfirst : first ≠ centre) (hsecond : second ≠ centre) (hdistinct : first ≠ second) :
    (gram centre first) ^ 2 + (gram centre second) ^ 2 ≤ 1 := by
  have hsubset : ({first, second} : Finset (Fin 6)) ⊆ Finset.univ.erase centre := by
    intro index hindex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hindex
    rcases hindex with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hfirst, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hsecond, Finset.mem_univ _⟩
  have hpair : ∑ index ∈ ({first, second} : Finset (Fin 6)), (gram centre index) ^ 2
      = (gram centre first) ^ 2 + (gram centre second) ^ 2 :=
    Finset.sum_pair hdistinct
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun index _ _ => sq_nonneg (gram centre index))
  rw [hpair, sum_sq_erase_eq_one htight centre] at hmono
  exact hmono

/-- Every off-diagonal square is at most one. -/
theorem sq_le_one (htight : IsTightGramSix gram) {centre partner : Fin 6}
    (hne : partner ≠ centre) : (gram centre partner) ^ 2 ≤ 1 := by
  have hsubset : ({partner} : Finset (Fin 6)) ⊆ Finset.univ.erase centre := by
    intro index hindex
    simp only [Finset.mem_singleton] at hindex
    exact hindex ▸ Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun index _ _ => sq_nonneg (gram centre index))
  rw [Finset.sum_singleton, sum_sq_erase_eq_one htight centre] at hmono
  exact hmono

/-- **THE THIRDS REFINEMENT.**  No atom has three partners above one third. -/
theorem not_three_third_partners (htight : IsTightGramSix gram)
    {centre first second third : Fin 6}
    (hfirst : first ≠ centre) (hsecond : second ≠ centre) (hthird : third ≠ centre)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hlowFirst : 1 / 3 < (gram centre first) ^ 2)
    (hlowSecond : 1 / 3 < (gram centre second) ^ 2)
    (hlowThird : 1 / 3 < (gram centre third) ^ 2) : False := by
  have hsubset : ({first, second, third} : Finset (Fin 6)) ⊆ Finset.univ.erase centre := by
    intro index hindex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hindex
    rcases hindex with rfl | rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hfirst, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hsecond, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hthird, Finset.mem_univ _⟩
  have htriple : ∑ index ∈ ({first, second, third} : Finset (Fin 6)), (gram centre index) ^ 2
      = (gram centre first) ^ 2 + (gram centre second) ^ 2 + (gram centre third) ^ 2 := by
    rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
      Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, add_assoc]
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun index _ _ => sq_nonneg (gram centre index))
  rw [htriple, sum_sq_erase_eq_one htight centre] at hmono
  linarith

/-! ## 2. The strong graph is a matching -/

/-- **NO ATOM HAS TWO STRONG PARTNERS.**  Two squared correlations above one half
already exceed the row budget. -/
theorem not_two_strong_partners (htight : IsTightGramSix gram)
    {centre first second : Fin 6}
    (hfirst : first ≠ centre) (hsecond : second ≠ centre) (hdistinct : first ≠ second)
    (hstrongFirst : 1 / 2 < (gram centre first) ^ 2)
    (hstrongSecond : 1 / 2 < (gram centre second) ^ 2) : False := by
  have hbudget := sq_add_sq_le_one htight hfirst hsecond hdistinct
  linarith

/-- **NO STRONG TRIANGLE.**  A triangle would give its first vertex two strong
partners, which the row budget forbids. -/
theorem not_strongTriangle (htight : IsTightGramSix gram) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hstrongFirstSecond : 1 / 2 < (gram first second) ^ 2)
    (hstrongFirstThird : 1 / 2 < (gram first third) ^ 2)
    (_hstrongSecondThird : 1 / 2 < (gram second third) ^ 2) : False :=
  not_two_strong_partners htight (Ne.symm hfirstSecond) (Ne.symm hfirstThird) hsecondThird
    hstrongFirstSecond hstrongFirstThird

/-- **THE WEAK TRIANGLE.**  Every tight Gram at six atoms carries three atoms whose
three squared correlations are all at most one half.

The matching bound and the Ramsey bound are each insufficient alone.  The row
budget permits a strong matching of three edges, which is triangle free but leaves
twelve weak edges undetermined, and Ramsey alone permits the monochromatic triple
to be the strong one.  Together the strong branch is impossible, so the weak branch
holds. -/
theorem exists_weak_triple (htight : IsTightGramSix gram) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      (gram first second) ^ 2 ≤ 1 / 2 ∧ (gram first third) ^ 2 ≤ 1 / 2 ∧
        (gram second third) ^ 2 ≤ 1 / 2 := by
  classical
  haveI : DecidableRel (fun leftIndex rightIndex : Fin 6 =>
      (1 : ℝ) / 2 < (gram leftIndex rightIndex) ^ 2) := fun _ _ => Classical.dec _
  rcases exists_mono_triple_of_six
      (fun leftIndex rightIndex => (1 : ℝ) / 2 < (gram leftIndex rightIndex) ^ 2) with
    ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hone, htwo, hthree⟩ |
    ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hone, htwo, hthree⟩
  · exact absurd (not_strongTriangle htight hfirstSecond hfirstThird hsecondThird hone htwo hthree)
      not_false
  · exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, not_lt.mp hone,
      not_lt.mp htwo, not_lt.mp hthree⟩

/-! ## 3. The explicit row identities -/

/-- The five off-diagonal squares of row zero. -/
theorem row_energy_zero (htight : IsTightGramSix gram) :
    (gram 0 1) ^ 2 + (gram 0 2) ^ 2 + (gram 0 3) ^ 2 + (gram 0 4) ^ 2 + (gram 0 5) ^ 2 = 1 := by
  have hrow := sum_sq_row_eq_two htight 0
  rw [Fin.sum_univ_six, htight.unit 0] at hrow
  norm_num at hrow
  linarith

theorem row_energy_one (htight : IsTightGramSix gram) :
    (gram 0 1) ^ 2 + (gram 1 2) ^ 2 + (gram 1 3) ^ 2 + (gram 1 4) ^ 2 + (gram 1 5) ^ 2 = 1 := by
  have hrow := sum_sq_row_eq_two htight 1
  rw [Fin.sum_univ_six, htight.unit 1, htight.comm 0 1] at hrow
  norm_num at hrow
  linarith

theorem row_energy_two (htight : IsTightGramSix gram) :
    (gram 0 2) ^ 2 + (gram 1 2) ^ 2 + (gram 2 3) ^ 2 + (gram 2 4) ^ 2 + (gram 2 5) ^ 2 = 1 := by
  have hrow := sum_sq_row_eq_two htight 2
  rw [Fin.sum_univ_six, htight.unit 2, htight.comm 0 2, htight.comm 1 2] at hrow
  norm_num at hrow
  linarith

theorem row_energy_three (htight : IsTightGramSix gram) :
    (gram 0 3) ^ 2 + (gram 1 3) ^ 2 + (gram 2 3) ^ 2 + (gram 3 4) ^ 2 + (gram 3 5) ^ 2 = 1 := by
  have hrow := sum_sq_row_eq_two htight 3
  rw [Fin.sum_univ_six, htight.unit 3, htight.comm 0 3, htight.comm 1 3, htight.comm 2 3] at hrow
  norm_num at hrow
  linarith

theorem row_energy_four (htight : IsTightGramSix gram) :
    (gram 0 4) ^ 2 + (gram 1 4) ^ 2 + (gram 2 4) ^ 2 + (gram 3 4) ^ 2 + (gram 4 5) ^ 2 = 1 := by
  have hrow := sum_sq_row_eq_two htight 4
  rw [Fin.sum_univ_six, htight.unit 4, htight.comm 0 4, htight.comm 1 4, htight.comm 2 4,
    htight.comm 3 4] at hrow
  norm_num at hrow
  linarith

theorem row_energy_five (htight : IsTightGramSix gram) :
    (gram 0 5) ^ 2 + (gram 1 5) ^ 2 + (gram 2 5) ^ 2 + (gram 3 5) ^ 2 + (gram 4 5) ^ 2 = 1 := by
  have hrow := sum_sq_row_eq_two htight 5
  rw [Fin.sum_univ_six, htight.unit 5, htight.comm 0 5, htight.comm 1 5, htight.comm 2 5,
    htight.comm 3 5, htight.comm 4 5] at hrow
  norm_num at hrow
  linarith

end IsTightGramSix

/-! ## 4. The correlation first moment -/

/-- The total off-diagonal energy of a six-atom Gram, over the fifteen pairs. -/
noncomputable def offDiagEnergy (gram : Matrix (Fin 6) (Fin 6) ℝ) : ℝ :=
  (gram 0 1) ^ 2 + (gram 0 2) ^ 2 + (gram 0 3) ^ 2 + (gram 0 4) ^ 2 + (gram 0 5) ^ 2
    + (gram 1 2) ^ 2 + (gram 1 3) ^ 2 + (gram 1 4) ^ 2 + (gram 1 5) ^ 2
    + (gram 2 3) ^ 2 + (gram 2 4) ^ 2 + (gram 2 5) ^ 2
    + (gram 3 4) ^ 2 + (gram 3 5) ^ 2 + (gram 4 5) ^ 2

/-- The three squared correlations of a triple. -/
noncomputable def tripleEnergy (gram : Matrix (Fin 6) (Fin 6) ℝ)
    (first second third : Fin 6) : ℝ :=
  (gram first second) ^ 2 + (gram first third) ^ 2 + (gram second third) ^ 2

/-- **THE TOTAL ENERGY IS THREE.**  Summing the six row budgets counts every pair
twice. -/
theorem IsTightGramSix.offDiagEnergy_eq_three {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (htight : IsTightGramSix gram) : offDiagEnergy gram = 3 := by
  have hzero := IsTightGramSix.row_energy_zero htight
  have hone := IsTightGramSix.row_energy_one htight
  have htwo := IsTightGramSix.row_energy_two htight
  have hthree := IsTightGramSix.row_energy_three htight
  have hfour := IsTightGramSix.row_energy_four htight
  have hfive := IsTightGramSix.row_energy_five htight
  rw [offDiagEnergy]
  linarith

/-- The twenty triple energies of a six-atom Gram, in increasing index order. -/
noncomputable def totalTripleEnergy (gram : Matrix (Fin 6) (Fin 6) ℝ) : ℝ :=
  tripleEnergy gram 0 1 2 + tripleEnergy gram 0 1 3 + tripleEnergy gram 0 1 4
    + tripleEnergy gram 0 1 5 + tripleEnergy gram 0 2 3 + tripleEnergy gram 0 2 4
    + tripleEnergy gram 0 2 5 + tripleEnergy gram 0 3 4 + tripleEnergy gram 0 3 5
    + tripleEnergy gram 0 4 5 + tripleEnergy gram 1 2 3 + tripleEnergy gram 1 2 4
    + tripleEnergy gram 1 2 5 + tripleEnergy gram 1 3 4 + tripleEnergy gram 1 3 5
    + tripleEnergy gram 1 4 5 + tripleEnergy gram 2 3 4 + tripleEnergy gram 2 3 5
    + tripleEnergy gram 2 4 5 + tripleEnergy gram 3 4 5

/-- **THE COUNTING IDENTITY.**  Each of the fifteen pairs lies in exactly four of
the twenty triples, so the twenty triple energies total four times the pair
energy.  A polynomial identity in the fifteen off-diagonal entries, with no
hypothesis on the Gram at all. -/
theorem sum_tripleEnergy_eq_four_mul_offDiagEnergy (gram : Matrix (Fin 6) (Fin 6) ℝ) :
    totalTripleEnergy gram = 4 * offDiagEnergy gram := by
  rw [totalTripleEnergy, offDiagEnergy]
  simp only [tripleEnergy]
  ring

/-- **THE FIRST MOMENT.**  At a tight Gram the twenty triple energies total
exactly twelve. -/
theorem IsTightGramSix.totalTripleEnergy_eq_twelve {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (htight : IsTightGramSix gram) : totalTripleEnergy gram = 12 := by
  rw [sum_tripleEnergy_eq_four_mul_offDiagEnergy, htight.offDiagEnergy_eq_three]
  norm_num

/-- **THE LEAST TRIPLE ENERGY IS AT MOST THREE FIFTHS**, and the bound is attained
at the equiangular Gram, so it cannot be lowered.  Twenty triples averaging twelve
cannot all exceed the mean. -/
theorem IsTightGramSix.exists_tripleEnergy_le_three_fifths {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (htight : IsTightGramSix gram) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      tripleEnergy gram first second third ≤ 3 / 5 := by
  by_contra hcontra
  push Not at hcontra
  have htotal := htight.totalTripleEnergy_eq_twelve
  rw [totalTripleEnergy] at htotal
  have h012 := hcontra 0 1 2 (by decide) (by decide) (by decide)
  have h013 := hcontra 0 1 3 (by decide) (by decide) (by decide)
  have h014 := hcontra 0 1 4 (by decide) (by decide) (by decide)
  have h015 := hcontra 0 1 5 (by decide) (by decide) (by decide)
  have h023 := hcontra 0 2 3 (by decide) (by decide) (by decide)
  have h024 := hcontra 0 2 4 (by decide) (by decide) (by decide)
  have h025 := hcontra 0 2 5 (by decide) (by decide) (by decide)
  have h034 := hcontra 0 3 4 (by decide) (by decide) (by decide)
  have h035 := hcontra 0 3 5 (by decide) (by decide) (by decide)
  have h045 := hcontra 0 4 5 (by decide) (by decide) (by decide)
  have h123 := hcontra 1 2 3 (by decide) (by decide) (by decide)
  have h124 := hcontra 1 2 4 (by decide) (by decide) (by decide)
  have h125 := hcontra 1 2 5 (by decide) (by decide) (by decide)
  have h134 := hcontra 1 3 4 (by decide) (by decide) (by decide)
  have h135 := hcontra 1 3 5 (by decide) (by decide) (by decide)
  have h145 := hcontra 1 4 5 (by decide) (by decide) (by decide)
  have h234 := hcontra 2 3 4 (by decide) (by decide) (by decide)
  have h235 := hcontra 2 3 5 (by decide) (by decide) (by decide)
  have h245 := hcontra 2 4 5 (by decide) (by decide) (by decide)
  have h345 := hcontra 3 4 5 (by decide) (by decide) (by decide)
  linarith

/-- **SHARPNESS.**  At an equiangular Gram, whose off-diagonal squares are all one
fifth, every triple has energy exactly three fifths.  So the first moment bound is
attained at every triple simultaneously and no constant below three fifths is
available. -/
theorem tripleEnergy_eq_three_fifths_of_equicorrelated {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (hequi : ∀ leftIndex rightIndex : Fin 6, leftIndex ≠ rightIndex →
      (gram leftIndex rightIndex) ^ 2 = 1 / 5)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    tripleEnergy gram first second third = 3 / 5 := by
  rw [tripleEnergy, hequi first second hfirstSecond, hequi first third hfirstThird,
    hequi second third hsecondThird]
  norm_num

/-- The free per-triple cap: two row budgets bound any triple's energy by three
halves, with no counting at all. -/
theorem IsTightGramSix.tripleEnergy_le_three_halves {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (htight : IsTightGramSix gram) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    tripleEnergy gram first second third ≤ 3 / 2 := by
  have hfirstRow := htight.sq_add_sq_le_one (Ne.symm hfirstSecond) (Ne.symm hfirstThird)
    hsecondThird
  have hsecondRow := htight.sq_add_sq_le_one hfirstSecond (Ne.symm hsecondThird) hfirstThird
  have hthirdRow := htight.sq_add_sq_le_one hfirstThird hsecondThird hfirstSecond
  rw [tripleEnergy]
  have hswapFirst : gram second first = gram first second := htight.comm first second
  have hswapSecond : gram third first = gram first third := htight.comm first third
  have hswapThird : gram third second = gram second third := htight.comm second third
  rw [hswapFirst] at hsecondRow
  rw [hswapSecond, hswapThird] at hthirdRow
  linarith

/-! ## 5. Uniqueness, decoupling, and the rigidity of the equiangular value -/

namespace IsTightGramSix

variable {gram : Matrix (Fin 6) (Fin 6) ℝ}

/-- **THE STRONG PARTNER IS UNIQUE.**  The matching bound in functional form: an
atom has at most one partner above one half, so the strong graph is a matching and
carries at most three of the fifteen pairs. -/
theorem strongPartner_unique (htight : IsTightGramSix gram) {centre first second : Fin 6}
    (hfirst : first ≠ centre) (hsecond : second ≠ centre)
    (hstrongFirst : 1 / 2 < (gram centre first) ^ 2)
    (hstrongSecond : 1 / 2 < (gram centre second) ^ 2) : first = second := by
  by_contra hdistinct
  exact not_two_strong_partners htight hfirst hsecond hdistinct hstrongFirst hstrongSecond

/-- **THE DECOUPLING LAW.**  A pair carrying more than `1 - level`
forces every other correlation out of its first endpoint below `level`. -/
theorem sq_lt_of_saturated (htight : IsTightGramSix gram) {centre partner other : Fin 6}
    {level : ℝ} (hpartner : partner ≠ centre) (hother : other ≠ centre)
    (hdistinct : partner ≠ other) (hsaturated : 1 - level < (gram centre partner) ^ 2) :
    (gram centre other) ^ 2 < level := by
  have hbudget := sq_add_sq_le_one htight hpartner hother hdistinct
  linarith

/-- **FULL SATURATION FORCES ORTHOGONALITY.**  A parallel pair, `gamma^2 = 1`, kills
every other correlation out of that atom.  So the extreme case of the matching
bound is a genuine configuration and not an artefact: the row budget is exactly
spent by the one partner. -/
theorem eq_zero_of_sq_eq_one (htight : IsTightGramSix gram) {centre partner other : Fin 6}
    (hpartner : partner ≠ centre) (hother : other ≠ centre) (hdistinct : partner ≠ other)
    (hfull : (gram centre partner) ^ 2 = 1) : gram centre other = 0 := by
  have hbudget := sq_add_sq_le_one htight hpartner hother hdistinct
  have hsquare : (gram centre other) ^ 2 ≤ 0 := by linarith
  have hzero : (gram centre other) ^ 2 = 0 :=
    le_antisymm hsquare (sq_nonneg (gram centre other))
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero

/-- **THE EQUIANGULAR VALUE IS FORCED.**  A tight Gram at six atoms whose
off-diagonal squares are all equal has that common value exactly one fifth.  The
row budget has five terms and totals one, so no other equicorrelated tight Gram
exists at this size — the icosahedral value is not a choice. -/
theorem eq_one_fifth_of_equicorrelated (htight : IsTightGramSix gram) {level : ℝ}
    (hequi : ∀ leftIndex rightIndex : Fin 6, leftIndex ≠ rightIndex →
      (gram leftIndex rightIndex) ^ 2 = level) : level = 1 / 5 := by
  have hrow := row_energy_zero htight
  rw [hequi 0 1 (by decide), hequi 0 2 (by decide), hequi 0 3 (by decide),
    hequi 0 4 (by decide), hequi 0 5 (by decide)] at hrow
  linarith

/-- **THE WEAK TRIANGLE AT ANY THRESHOLD FROM ONE HALF UP.**  The matching argument
needs only `1 <= 2 * level`, so the threshold one half is exactly where it turns
on, and every larger threshold is free. -/
theorem exists_weak_triple_of_half_le (htight : IsTightGramSix gram) {level : ℝ}
    (hlevel : 1 / 2 ≤ level) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      (gram first second) ^ 2 ≤ level ∧ (gram first third) ^ 2 ≤ level ∧
        (gram second third) ^ 2 ≤ level := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hweakFirstSecond, hweakFirstThird, hweakSecondThird⟩ := exists_weak_triple htight
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    le_trans hweakFirstSecond hlevel, le_trans hweakFirstThird hlevel,
    le_trans hweakSecondThird hlevel⟩

end IsTightGramSix

/-! ## 6. The frame bridge -/

/-- **EVERY UNIT TIGHT FRAME OF SIX VECTORS GIVES A TIGHT GRAM.**  Tightness of the
frame, `F^T F = 2 . 1`, becomes `Gamma^2 = 2 Gamma` by associativity alone.  This is
what carries the whole module to the covering statement of
`Gtz/Quantitative/SixThreeNuCovering.lean`, whose cells read exactly this Gram. -/
theorem isTightGramSix_frameGram {frame : Matrix (Fin 6) (Fin 3) ℝ}
    (hframe : IsUnitTightFrameSix frame) : IsTightGramSix (frame * frameᵀ) where
  comm := fun leftIndex rightIndex => by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun coord _ => mul_comm _ _
  unit := fun index => by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    have hlev := hframe.unit index
    rw [leverageOf] at hlev
    rw [← hlev]
    exact Finset.sum_congr rfl fun coord _ => (sq (frame index coord)).symm ▸ rfl
  idem := by
    calc (frame * frameᵀ) * (frame * frameᵀ)
        = frame * (frameᵀ * frame) * frameᵀ := by
          simp only [Matrix.mul_assoc]
      _ = frame * ((2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) * frameᵀ := by
          rw [hframe.tight]
      _ = (2 : ℝ) • (frame * frameᵀ) := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- The weak triangle, read on a unit tight frame directly. -/
theorem exists_weak_triple_frame {frame : Matrix (Fin 6) (Fin 3) ℝ}
    (hframe : IsUnitTightFrameSix frame) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      ((frame * frameᵀ) first second) ^ 2 ≤ 1 / 2 ∧
        ((frame * frameᵀ) first third) ^ 2 ≤ 1 / 2 ∧
          ((frame * frameᵀ) second third) ^ 2 ≤ 1 / 2 :=
  IsTightGramSix.exists_weak_triple (isTightGramSix_frameGram hframe)

/-- The correlation first moment, read on a unit tight frame directly. -/
theorem exists_tripleEnergy_le_three_fifths_frame {frame : Matrix (Fin 6) (Fin 3) ℝ}
    (hframe : IsUnitTightFrameSix frame) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      tripleEnergy (frame * frameᵀ) first second third ≤ 3 / 5 :=
  IsTightGramSix.exists_tripleEnergy_le_three_fifths (isTightGramSix_frameGram hframe)

/-- The total pair energy of a unit tight frame's Gram is three. -/
theorem offDiagEnergy_frameGram_eq_three {frame : Matrix (Fin 6) (Fin 3) ℝ}
    (hframe : IsUnitTightFrameSix frame) : offDiagEnergy (frame * frameᵀ) = 3 :=
  IsTightGramSix.offDiagEnergy_eq_three (isTightGramSix_frameGram hframe)

/-! ## 7. What the weak triangle buys on the covering side -/

/-- **THE PAIR MINORS AT A WEAK TRIPLE.**  On the weak triangle the two smaller
Sylvester conditions hold as soon as the complementary coordinates clear one half
in product.  This is the covering-side content of the weak triangle, and it is all
of it — the determinant clause is untouched by the threshold one half. -/
theorem IsTightGramSix.pairMinors_of_weak_triple {gram : Matrix (Fin 6) (Fin 6) ℝ}
    {first second third : Fin 6} {complementFirst complementSecond complementThird : ℝ}
    (hweakFirstSecond : (gram first second) ^ 2 ≤ 1 / 2)
    (hweakFirstThird : (gram first third) ^ 2 ≤ 1 / 2)
    (hweakSecondThird : (gram second third) ^ 2 ≤ 1 / 2)
    (hproductFirstSecond : 1 / 2 ≤ complementFirst * complementSecond)
    (hproductFirstThird : 1 / 2 ≤ complementFirst * complementThird)
    (hproductSecondThird : 1 / 2 ≤ complementSecond * complementThird) :
    (gram first second) ^ 2 ≤ complementFirst * complementSecond
      ∧ (gram first third) ^ 2 ≤ complementFirst * complementThird
      ∧ (gram second third) ^ 2 ≤ complementSecond * complementThird :=
  ⟨le_trans hweakFirstSecond hproductFirstSecond,
    le_trans hweakFirstThird hproductFirstThird,
    le_trans hweakSecondThird hproductSecondThird⟩

/-- **THE BLOCK STATEMENT.**  Assembling the weak triangle's pair minors with the
determinant clause through the shipped Sylvester criterion.  The determinant
hypothesis is genuinely required and this module does not discharge it. -/
theorem IsTightGramSix.posSemidef_block_of_weak_triple {gram : Matrix (Fin 6) (Fin 6) ℝ}
    {first second third : Fin 6} {complementFirst complementSecond complementThird : ℝ}
    (hnonnegFirst : 0 ≤ complementFirst) (hnonnegSecond : 0 ≤ complementSecond)
    (hnonnegThird : 0 ≤ complementThird)
    (hweakFirstSecond : (gram first second) ^ 2 ≤ 1 / 2)
    (hweakFirstThird : (gram first third) ^ 2 ≤ 1 / 2)
    (hweakSecondThird : (gram second third) ^ 2 ≤ 1 / 2)
    (hproductFirstSecond : 1 / 2 ≤ complementFirst * complementSecond)
    (hproductFirstThird : 1 / 2 ≤ complementFirst * complementThird)
    (hproductSecondThird : 1 / 2 ≤ complementSecond * complementThird)
    (hdet : 0 ≤ slackDeterminantThree complementFirst complementSecond complementThird
      (gram first second) (gram first third) (gram second third)) :
    (slackHollowThree complementFirst complementSecond complementThird
      (gram first second) (gram first third) (gram second third)).PosSemidef := by
  obtain ⟨hminorFirstSecond, hminorFirstThird, hminorSecondThird⟩ :=
    IsTightGramSix.pairMinors_of_weak_triple hweakFirstSecond hweakFirstThird
      hweakSecondThird hproductFirstSecond hproductFirstThird hproductSecondThird
  exact (posSemidef_slackHollowThree_iff _ _ _ _ _ _).mpr
    ⟨hnonnegFirst, hnonnegSecond, hnonnegThird, hminorFirstSecond, hminorFirstThird,
      hminorSecondThird, hdet⟩

/-! ## 8. The link into the covering statement -/

/-- **THE WEAK TRIPLE IS A CELL MEMBERSHIP.**  Read on the covering file's own cell
`Gtz.invariantLeverageCell`, a weak triple covers an invariant-leverage vector as
soon as the complementary coordinates clear one half in product and the
determinant clause holds.  This is the statement that feeds
`Gtz.CoversInvariantLeverageRegion`, and it isolates precisely what the weak
triangle does NOT supply: the determinant. -/
theorem mem_invariantLeverageCell_of_weak_triple {gram : Matrix (Fin 6) (Fin 6) ℝ}
    {first second third : Fin 6} {invariantLeverage : Fin 6 → ℝ}
    (hunitFirst : gram first first = 1) (hunitSecond : gram second second = 1)
    (hunitThird : gram third third = 1)
    (hcommFirstSecond : gram second first = gram first second)
    (hcommFirstThird : gram third first = gram first third)
    (hcommSecondThird : gram third second = gram second third)
    (hnonnegFirst : 0 ≤ 1 - invariantLeverage first)
    (hnonnegSecond : 0 ≤ 1 - invariantLeverage second)
    (hnonnegThird : 0 ≤ 1 - invariantLeverage third)
    (hweakFirstSecond : (gram first second) ^ 2 ≤ 1 / 2)
    (hweakFirstThird : (gram first third) ^ 2 ≤ 1 / 2)
    (hweakSecondThird : (gram second third) ^ 2 ≤ 1 / 2)
    (hproductFirstSecond :
      1 / 2 ≤ (1 - invariantLeverage first) * (1 - invariantLeverage second))
    (hproductFirstThird :
      1 / 2 ≤ (1 - invariantLeverage first) * (1 - invariantLeverage third))
    (hproductSecondThird :
      1 / 2 ≤ (1 - invariantLeverage second) * (1 - invariantLeverage third))
    (hdet : 0 ≤ slackDeterminantThree (1 - invariantLeverage first)
      (1 - invariantLeverage second) (1 - invariantLeverage third)
      (gram first second) (gram first third) (gram second third)) :
    invariantLeverage ∈ invariantLeverageCell gram first second third := by
  rw [mem_invariantLeverageCell_iff,
    submatrix_sub_diagonal_eq_slackHollowThree gram hunitFirst hunitSecond hunitThird
      hcommFirstSecond hcommFirstThird hcommSecondThird invariantLeverage]
  exact IsTightGramSix.posSemidef_block_of_weak_triple hnonnegFirst hnonnegSecond hnonnegThird
    hweakFirstSecond hweakFirstThird hweakSecondThird hproductFirstSecond hproductFirstThird
    hproductSecondThird hdet

/-- **THE WEAK TRIPLE OF A TIGHT GRAM, AS A CELL.**  The existence half and the
membership half composed: every tight Gram carries a triple whose cell contains
every invariant-leverage vector that clears the product and determinant clauses on
it.  What remains open is exactly the determinant clause, which the threshold one
half does not reach. -/
theorem IsTightGramSix.exists_weak_triple_cell {gram : Matrix (Fin 6) (Fin 6) ℝ}
    (htight : IsTightGramSix gram) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      ∀ invariantLeverage : Fin 6 → ℝ,
        0 ≤ 1 - invariantLeverage first → 0 ≤ 1 - invariantLeverage second →
        0 ≤ 1 - invariantLeverage third →
        1 / 2 ≤ (1 - invariantLeverage first) * (1 - invariantLeverage second) →
        1 / 2 ≤ (1 - invariantLeverage first) * (1 - invariantLeverage third) →
        1 / 2 ≤ (1 - invariantLeverage second) * (1 - invariantLeverage third) →
        0 ≤ slackDeterminantThree (1 - invariantLeverage first)
          (1 - invariantLeverage second) (1 - invariantLeverage third)
          (gram first second) (gram first third) (gram second third) →
        invariantLeverage ∈ invariantLeverageCell gram first second third := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hweakFirstSecond, hweakFirstThird, hweakSecondThird⟩ := exists_weak_triple htight
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  intro invariantLeverage hnonnegFirst hnonnegSecond hnonnegThird hproductFirstSecond
    hproductFirstThird hproductSecondThird hdet
  exact mem_invariantLeverageCell_of_weak_triple (htight.unit first) (htight.unit second)
    (htight.unit third) (htight.comm first second) (htight.comm first third)
    (htight.comm second third) hnonnegFirst hnonnegSecond hnonnegThird hweakFirstSecond
    hweakFirstThird hweakSecondThird hproductFirstSecond hproductFirstThird
    hproductSecondThird hdet

end Gtz

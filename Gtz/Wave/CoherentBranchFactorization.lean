/-
# The coherent branch of the third minor, and exactly what the sign buys

`Gtz/Wave/TripleDeterminantCells.lean` factors the third Sylvester minor on the
equilateral locus at ONE orientation only:

  `Gtz.tripleDetForm_equilateral : tripleDetForm P P P (-t) (-t) (-t)`
  `    = (P - 2 * t) * (P + t) ^ 2`

That is the INCOHERENT branch, where the oriented product of the three pairings is
negative.  The coherent branch is a different polynomial and it is not in the
corpus.  This file supplies it, prices the difference exactly, and closes the one
hypothesis the landed coherent count carries.

## What the sign is worth, as a number

On the equilateral locus the two branches are

  coherent    `(P - t) ^ 2 * (P + 2 * t)`
  incoherent  `(P - 2 * t) * (P + t) ^ 2`

At positive surplus and non-negative pairing magnitude the coherent branch is
NON-NEGATIVE with no hypothesis at all, and strictly positive unless `t = P`.
The incoherent branch needs `2 * t < P`.  The pair minors are positive exactly
when `t < P`.  So along this locus:

  coherent   + positive pair minors  =>  positive determinant, unconditionally
  incoherent + positive pair minors  =>  positive determinant iff `2 * t < P`

**Coherence is worth exactly a factor of two in the pairing budget.**

## Why the landed sign-aware cell is strictly weaker

`Gtz.tripleDetForm_pos_of_nonneg_cross` discards the cross term when it is
non-negative and asks the plain sum condition `p q r > p w ^ 2 + q v ^ 2 + r u ^ 2`.
On the equilateral locus that reads `P ^ 3 > 3 * P * t ^ 2`, which is `3 * t ^ 2 < P ^ 2`
and is STRICTLY STRONGER than the coherent branch's `t <= P`.  The gap is real and
it bites at the campaign's own crux configuration: at `P = 1/3` and
`t = 1/(2 * sqrt 5)` the sum condition fails while the determinant is positive.
`Gtz.tripleDetForm_coherent_gap_witness` records that separation as an exact
rational point.  So the correct composition with a sign-existence theorem is the
FACTORIZATION, not the sum condition.

## The hypothesis the coherent count carries, discharged

`Gtz.four_le_card_coherentTripleSets_sixThree` needs every pairing nonzero.  A
design with an orthogonal pair is outside its scope.  But an orthogonal pair makes
the oriented product of any triple through it exactly zero, which is already
non-negative.  `Gtz.exists_nonneg_atomPairingProduct_sixThree` is therefore
hypothesis-free, and non-negativity is the form the sign-aware consumers ask for.
-/
import Gtz.Wave.TripleDeterminantCells
import Gtz.Quantitative.CoherentCountFloor

namespace Gtz

open Finset

/-! ## 1. The coherent equilateral factorization -/

/-- **THE COHERENT BRANCH.**  Equal surpluses and equal POSITIVE pairings.  The
companion `Gtz.tripleDetForm_equilateral` does the negative orientation. -/
theorem tripleDetForm_equilateral_coherent (bigP smallT : ℝ) :
    tripleDetForm bigP bigP bigP smallT smallT smallT
      = (bigP - smallT) ^ 2 * (bigP + 2 * smallT) := by
  rw [tripleDetForm]; ring

/-- The coherent branch is non-negative with no hypothesis beyond the signs the
locus already carries.  The incoherent branch has no such statement. -/
theorem tripleDetForm_equilateral_coherent_nonneg (bigP smallT : ℝ) (hP : 0 ≤ bigP)
    (hT : 0 ≤ smallT) :
    0 ≤ tripleDetForm bigP bigP bigP smallT smallT smallT := by
  rw [tripleDetForm_equilateral_coherent]
  have hsq : 0 ≤ (bigP - smallT) ^ 2 := sq_nonneg _
  have hlin : 0 ≤ bigP + 2 * smallT := by linarith
  positivity

/-- The coherent branch vanishes exactly at the double root. -/
theorem tripleDetForm_equilateral_coherent_eq_zero_iff (bigP smallT : ℝ) (hP : 0 < bigP)
    (hT : 0 ≤ smallT) :
    tripleDetForm bigP bigP bigP smallT smallT smallT = 0 ↔ smallT = bigP := by
  rw [tripleDetForm_equilateral_coherent]
  have hlin : 0 < bigP + 2 * smallT := by linarith
  constructor
  · intro h
    have hsq : (bigP - smallT) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with hzero | hzero
      · exact hzero
      · exact absurd hzero hlin.ne'
    have hlinzero : bigP - smallT = 0 := by
      have := sq_eq_zero_iff.mp hsq
      exact this
    linarith
  · intro h
    rw [h]
    ring

/-- **THE COHERENT BRANCH IS POSITIVE EXCEPT AT ONE POINT.**  Contrast
`Gtz.tripleDetForm_equilateral_pos_iff`, which needs `4 * t ^ 2 < P * P`. -/
theorem tripleDetForm_equilateral_coherent_pos_iff (bigP smallT : ℝ) (hP : 0 < bigP)
    (hT : 0 ≤ smallT) :
    0 < tripleDetForm bigP bigP bigP smallT smallT smallT ↔ smallT ≠ bigP := by
  have hnonneg := tripleDetForm_equilateral_coherent_nonneg bigP smallT hP.le hT
  have hzero := tripleDetForm_equilateral_coherent_eq_zero_iff bigP smallT hP hT
  constructor
  · intro hpos hEq
    rw [hzero.mpr hEq] at hpos
    exact lt_irrefl 0 hpos
  · intro hne
    rcases hnonneg.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (hzero.mp heq.symm) hne

/-! ## 2. The pairing budget, priced

The pair minors on this locus are positive exactly when `t < P`
(`Gtz.equilateral_pairMinor_pos_iff`).  These two theorems say what each
orientation does with that budget. -/

/-- **COHERENCE SPENDS THE WHOLE TRIANGLE BUDGET.**  A coherent triple whose pair
minors are positive is positive definite on this locus, with no further condition.
-/
theorem tripleDetForm_equilateral_coherent_pos_of_triangle (bigP smallT : ℝ) (hP : 0 < bigP)
    (hT : 0 ≤ smallT) (htriangle : smallT < bigP) :
    0 < tripleDetForm bigP bigP bigP smallT smallT smallT :=
  (tripleDetForm_equilateral_coherent_pos_iff bigP smallT hP hT).mpr htriangle.ne

/-- **INCOHERENCE SPENDS HALF OF IT.**  The same triangle budget leaves the
incoherent orientation short by exactly a factor of two. -/
theorem tripleDetForm_equilateral_incoherent_pos_iff_half (bigP smallT : ℝ) (hP : 0 < bigP)
    (hT : 0 ≤ smallT) :
    0 < tripleDetForm bigP bigP bigP (-smallT) (-smallT) (-smallT) ↔ 2 * smallT < bigP := by
  rw [tripleDetForm_equilateral]
  have hsq : 0 < (bigP + smallT) ^ 2 := by positivity
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    nlinarith
  · intro h
    have hlin : 0 < bigP - 2 * smallT := by linarith
    positivity

/-- **THE FACTOR OF TWO, AS ONE STATEMENT.**  On the equilateral locus, at a
pairing magnitude in the half-open window `[P/2, P)`, the coherent orientation is
positive definite and the incoherent one is not.  That window is exactly what the
sign is worth. -/
theorem coherent_pos_and_incoherent_nonpos_of_mem_window (bigP smallT : ℝ) (hP : 0 < bigP)
    (hlow : bigP ≤ 2 * smallT) (hhigh : smallT < bigP) :
    0 < tripleDetForm bigP bigP bigP smallT smallT smallT ∧
      ¬ 0 < tripleDetForm bigP bigP bigP (-smallT) (-smallT) (-smallT) := by
  have hT : 0 ≤ smallT := by linarith
  refine ⟨tripleDetForm_equilateral_coherent_pos_of_triangle bigP smallT hP hT hhigh, ?_⟩
  intro hpos
  have := (tripleDetForm_equilateral_incoherent_pos_iff_half bigP smallT hP hT).mp hpos
  linarith

/-! ## 3. The whole equal-magnitude locus, by orientation alone

Only the oriented product distinguishes the branches.  Flipping any two pairings
leaves the determinant fixed (`Gtz.tripleDetForm_neg_first` and companions), so
the equal-magnitude locus carries exactly two values. -/

/-- On the equal-magnitude locus the determinant is a fixed even part plus twice
the oriented product. -/
theorem tripleDetForm_equalMagnitude (bigP smallT firstPair secondPair thirdPair : ℝ)
    (hfirst : firstPair ^ 2 = smallT ^ 2) (hsecond : secondPair ^ 2 = smallT ^ 2)
    (hthird : thirdPair ^ 2 = smallT ^ 2) :
    tripleDetForm bigP bigP bigP firstPair secondPair thirdPair
      = bigP ^ 3 - 3 * bigP * smallT ^ 2 + 2 * (firstPair * secondPair * thirdPair) := by
  rw [tripleDetForm]
  linear_combination (-bigP) * hthird + (-bigP) * hsecond + (-bigP) * hfirst

/-- **THE LOCUS HAS EXACTLY TWO VALUES.**  A non-negative oriented product puts
the determinant on the coherent branch. -/
theorem tripleDetForm_equalMagnitude_coherent (bigP smallT firstPair secondPair thirdPair : ℝ)
    (hT : 0 ≤ smallT)
    (hfirst : firstPair ^ 2 = smallT ^ 2) (hsecond : secondPair ^ 2 = smallT ^ 2)
    (hthird : thirdPair ^ 2 = smallT ^ 2)
    (hcoherent : 0 ≤ firstPair * secondPair * thirdPair) :
    tripleDetForm bigP bigP bigP firstPair secondPair thirdPair
      = (bigP - smallT) ^ 2 * (bigP + 2 * smallT) := by
  have hcube : (firstPair * secondPair * thirdPair) ^ 2 = (smallT ^ 3) ^ 2 := by
    have : (firstPair * secondPair * thirdPair) ^ 2
        = firstPair ^ 2 * secondPair ^ 2 * thirdPair ^ 2 := by ring
    rw [this, hfirst, hsecond, hthird]; ring
  have hpow : (0 : ℝ) ≤ smallT ^ 3 := by positivity
  have hval : firstPair * secondPair * thirdPair = smallT ^ 3 := by
    have hfactor : (firstPair * secondPair * thirdPair - smallT ^ 3)
        * (firstPair * secondPair * thirdPair + smallT ^ 3) = 0 := by nlinarith [hcube]
    rcases mul_eq_zero.mp hfactor with hbranch | hbranch
    · linarith
    · linarith
  rw [tripleDetForm_equalMagnitude bigP smallT firstPair secondPair thirdPair hfirst hsecond
    hthird, hval]
  ring

/-! ## 4. The separation from the landed sign-aware cell

`Gtz.tripleDetForm_pos_of_nonneg_cross` drops the cross term.  On this locus that
costs a genuine region, and the loss is not marginal. -/

/-- The plain sum condition on the equilateral locus. -/
theorem equilateral_sumCondition_iff (bigP smallT : ℝ) (hP : 0 < bigP) :
    bigP * bigP * bigP > bigP * smallT ^ 2 + bigP * smallT ^ 2 + bigP * smallT ^ 2
      ↔ 3 * smallT ^ 2 < bigP ^ 2 := by
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **THE SUM CONDITION IS STRICTLY STRONGER THAN THE COHERENT BRANCH.**  Any
magnitude in `[P/sqrt 3, P)` separates them, and the separation is exhibited here
at an exact rational point: `P = 1` and `t = 4/5` give a positive determinant and a
failed sum condition. -/
theorem tripleDetForm_coherent_gap_witness :
    0 < tripleDetForm 1 1 1 (4/5 : ℝ) (4/5) (4/5) ∧
      ¬ ((1 : ℝ) * 1 * 1 > 1 * (4/5 : ℝ) ^ 2 + 1 * (4/5 : ℝ) ^ 2 + 1 * (4/5 : ℝ) ^ 2) := by
  constructor
  · rw [tripleDetForm]; norm_num
  · norm_num

/-- The same separation, stated as a window: strictly between `P / sqrt 3` and `P`
the coherent branch is positive and the sum condition fails. -/
theorem coherent_pos_and_sumCondition_fails (bigP smallT : ℝ) (hP : 0 < bigP)
    (hT : 0 ≤ smallT) (hlow : bigP ^ 2 ≤ 3 * smallT ^ 2) (hhigh : smallT < bigP) :
    0 < tripleDetForm bigP bigP bigP smallT smallT smallT ∧
      ¬ (bigP * bigP * bigP > bigP * smallT ^ 2 + bigP * smallT ^ 2 + bigP * smallT ^ 2) := by
  refine ⟨tripleDetForm_equilateral_coherent_pos_of_triangle bigP smallT hP hT hhigh, ?_⟩
  intro hsum
  have := (equilateral_sumCondition_iff bigP smallT hP).mp hsum
  linarith

/-! ## 4b. The price of the sign, off the equilateral locus

Nothing above needs equal surpluses.  The even part of the third minor depends
only on the pairing magnitudes, so the orientation enters through the cross term
alone and the whole question is one signed quantity. -/

/-- **THE COHERENT ORIENTATION IS THE MAXIMUM.**  At fixed surpluses and fixed
pairing magnitudes the determinant is largest when the oriented product is
non-negative.  No hypothesis on the surpluses. -/
theorem tripleDetForm_le_abs (p q r u v w : ℝ) :
    tripleDetForm p q r u v w ≤ tripleDetForm p q r |u| |v| |w| := by
  rw [tripleDetForm, tripleDetForm, sq_abs, sq_abs, sq_abs]
  have hcross : u * v * w ≤ |u| * |v| * |w| := by
    calc u * v * w ≤ |u * v * w| := le_abs_self _
      _ = |u| * |v| * |w| := by rw [abs_mul, abs_mul]
  linarith

/-- A coherent triple ATTAINS that maximum, so coherence is exactly the statement
that the determinant sits at the best orientation available to its magnitudes. -/
theorem tripleDetForm_eq_abs_of_nonneg_cross (p q r u v w : ℝ) (hcoherent : 0 ≤ u * v * w) :
    tripleDetForm p q r u v w = tripleDetForm p q r |u| |v| |w| := by
  rw [tripleDetForm, tripleDetForm, sq_abs, sq_abs, sq_abs]
  have hcross : u * v * w = |u| * |v| * |w| := by
    rw [← abs_mul, ← abs_mul, abs_of_nonneg hcoherent]
  linarith

/-- **THE PRICE OF THE SIGN, EXACTLY.**  Flipping one pairing costs four times the
oriented product and nothing else, because the even part cannot see the sign. -/
theorem tripleDetForm_coherent_sub_incoherent (p q r a b c : ℝ) :
    tripleDetForm p q r a b c - tripleDetForm p q r (-a) b c = 4 * (a * b * c) := by
  rw [tripleDetForm, tripleDetForm]; ring

/-- The sign-blind reading loses exactly `4 * |u| * |v| * |w|` against the coherent
one.  A certificate that declines to read the orientation pays that gap in full,
which is what makes the sign-blind class incomplete at a large-pairing
configuration. -/
theorem tripleDetForm_signBlind_deficit (p q r u v w : ℝ) :
    tripleDetForm p q r |u| |v| |w| - tripleDetForm p q r (-|u|) |v| |w|
      = 4 * (|u| * |v| * |w|) :=
  tripleDetForm_coherent_sub_incoherent p q r |u| |v| |w|

/-- **A COHERENT TRIPLE IS POSITIVE AS SOON AS THE INCOHERENT READING IS.**  The
converse fails, and the equilateral window measures by how much. -/
theorem tripleDetForm_pos_of_nonneg_cross_of_incoherent_pos (p q r u v w : ℝ)
    (hcoherent : 0 ≤ u * v * w)
    (hincoherent : 0 < tripleDetForm p q r (-|u|) |v| |w|) :
    0 < tripleDetForm p q r u v w := by
  have hdeficit := tripleDetForm_signBlind_deficit p q r u v w
  have habs : 0 ≤ |u| * |v| * |w| := by positivity
  have heq := tripleDetForm_eq_abs_of_nonneg_cross p q r u v w hcoherent
  rw [heq]
  linarith

/-! ## 5. Sign existence without the nonvanishing hypothesis

`Gtz.four_le_card_coherentTripleSets_sixThree` gives four coherent triples of the
twenty, and it asks every pairing to be nonzero.  An orthogonal pair puts a zero
into the oriented product of every triple through it, which is already the
non-negativity the consumers want.  Splitting on that case removes the hypothesis
entirely. -/

/-- A third label exists away from any two. -/
theorem exists_third_ne {sizeIndex : ℕ} (hsize : 3 ≤ sizeIndex) (firstLabel secondLabel :
    Fin sizeIndex) :
    ∃ thirdLabel : Fin sizeIndex, thirdLabel ≠ firstLabel ∧ thirdLabel ≠ secondLabel := by
  classical
  have hcard : (({firstLabel, secondLabel} : Finset (Fin sizeIndex))ᶜ).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    have hpair : ({firstLabel, secondLabel} : Finset (Fin sizeIndex)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    omega
  obtain ⟨thirdLabel, hmem⟩ := hcard
  rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton] at hmem
  push Not at hmem
  exact ⟨thirdLabel, hmem.1, hmem.2⟩

/-- **HYPOTHESIS-FREE SIGN EXISTENCE AT `(6,3)`.**  Every design of six atoms in
rank three carries a triple whose oriented pairing product is non-negative.  The
landed count `Gtz.four_le_card_coherentTripleSets_sixThree` is stronger where its
nonvanishing hypothesis holds and silent where it does not, and this covers both. -/
theorem exists_nonneg_atomPairingProduct_sixThree (D : WeightedDesign 6 3) :
    ∃ firstLabel secondLabel thirdLabel : Fin 6,
      firstLabel ≠ secondLabel ∧ firstLabel ≠ thirdLabel ∧ secondLabel ≠ thirdLabel ∧
        0 ≤ atomPairing D firstLabel secondLabel * atomPairing D firstLabel thirdLabel
          * atomPairing D secondLabel thirdLabel := by
  classical
  by_cases hnonzero : ∀ firstLabel secondLabel : Fin 6, firstLabel ≠ secondLabel →
      atomPairing D firstLabel secondLabel ≠ 0
  · have hcount := four_le_card_coherentTripleSets_sixThree D hnonzero
    have hne : (coherentTripleSets D).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨selected, hmem⟩ := hne
    obtain ⟨firstLabel, secondLabel, thirdLabel, _, hfs, hft, hst, hparity⟩ :=
      (mem_coherentTripleSets_iff D selected).mp hmem
    refine ⟨firstLabel, secondLabel, thirdLabel, hfs, hft, hst, le_of_lt ?_⟩
    refine pos_atomPairingProduct_of_tripleParity_eq_one D hparity ?_
    exact mul_ne_zero (mul_ne_zero (hnonzero _ _ hfs) (hnonzero _ _ hft)) (hnonzero _ _ hst)
  · push Not at hnonzero
    obtain ⟨firstLabel, secondLabel, hne, hzero⟩ := hnonzero
    obtain ⟨thirdLabel, hthirdFirst, hthirdSecond⟩ :=
      exists_third_ne (sizeIndex := 6) (by norm_num) firstLabel secondLabel
    refine ⟨firstLabel, secondLabel, thirdLabel, hne, (Ne.symm hthirdFirst),
      (Ne.symm hthirdSecond), ?_⟩
    rw [hzero]
    simp

/-! ## 6. What coherence does NOT buy

Section 2 shows a coherent triple with positive pair minors is positive definite
ON THE EQUILATERAL LOCUS.  Neither the equilateral hypothesis nor the conclusion
survives without it, and both failures are exhibited here at exact rational
points.  These bound the results above from the other side, and they refute the
selection rule that section 5 might otherwise suggest. -/

/-- **THE EQUILATERAL HYPOTHESIS IS NOT REMOVABLE.**  A coherent triple whose
three pair minors are all strictly positive can still have a negative third
minor.  So coherence plus the triangle does NOT decide a triple in general, and
`Gtz.tripleDetForm_equilateral_coherent_pos_of_triangle` is sharp in its
hypothesis rather than merely convenient. -/
theorem not_forall_pos_tripleDetForm_of_nonneg_cross_of_pairMinors :
    ¬ ∀ p q r u v w : ℝ, 0 < p → 0 < q → 0 < r → 0 ≤ u * v * w →
      0 < p * q - u ^ 2 → 0 < p * r - v ^ 2 → 0 < q * r - w ^ 2 →
        0 < tripleDetForm p q r u v w := by
  intro hall
  have hcontra := hall 1 1 1 (9/10) (9/10) (1/10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [tripleDetForm] at hcontra
  norm_num at hcontra

/-- The same witness, read as a value: the third minor is `-117/250` there while
every pair minor is positive and the oriented product is `81/1000 > 0`. -/
theorem tripleDetForm_coherent_negative_witness :
    tripleDetForm 1 1 1 (9/10 : ℝ) (9/10) (1/10) = -(117/250) ∧
      0 < (9/10 : ℝ) * (9/10) * (1/10) := by
  constructor
  · rw [tripleDetForm]; norm_num
  · norm_num

/-- **INCOHERENCE DOES NOT PRECLUDE DOMINATION.**  An incoherent triple can have
a strictly positive third minor, so a selection rule cannot discard the
incoherent triples either. -/
theorem not_forall_nonpos_tripleDetForm_of_neg_cross :
    ¬ ∀ p q r u v w : ℝ, u * v * w < 0 → tripleDetForm p q r u v w ≤ 0 := by
  intro hall
  have hcontra := hall 1 1 1 (1/4) (1/4) (-(1/4)) (by norm_num)
  rw [tripleDetForm] at hcontra
  norm_num at hcontra

/-- The incoherent witness as a value: `25/32 > 0` at oriented product
`-(1/64) < 0`. -/
theorem tripleDetForm_incoherent_positive_witness :
    tripleDetForm 1 1 1 (1/4 : ℝ) (1/4) (-(1/4)) = 25/32 ∧
      (1/4 : ℝ) * (1/4) * (-(1/4)) < 0 := by
  constructor
  · rw [tripleDetForm]; norm_num
  · norm_num

/-- **THE COHERENT SELECTION RULE IS REFUTED AT THE SCALAR LEVEL.**  Coherence is
neither sufficient for a positive third minor nor necessary for one.  Taken with
`Gtz.tripleDetForm_le_abs`, which says the coherent orientation is the best case
at fixed magnitudes, the picture is exact: reading the sign tells you which of two
values the minor takes, and it does not tell you the sign of either value. -/
theorem coherence_neither_sufficient_nor_necessary :
    (¬ ∀ p q r u v w : ℝ, 0 < p → 0 < q → 0 < r → 0 ≤ u * v * w →
        0 < p * q - u ^ 2 → 0 < p * r - v ^ 2 → 0 < q * r - w ^ 2 →
          0 < tripleDetForm p q r u v w) ∧
      (¬ ∀ p q r u v w : ℝ, u * v * w < 0 → tripleDetForm p q r u v w ≤ 0) :=
  ⟨not_forall_pos_tripleDetForm_of_nonneg_cross_of_pairMinors,
    not_forall_nonpos_tripleDetForm_of_neg_cross⟩

end Gtz

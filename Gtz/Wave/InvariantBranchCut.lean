/-
# The invariant branch cut of the twenty triples, and the two moment inequalities it forces

At `(6,3)` a tie labels each of the twenty triples by the sign pattern of the three
elementary invariants of its gap `S_C - 1`.  This file turns that per-triple label into
AGGREGATE statements about the unweighted moment `N = sum_c g_c g_c^T`.

## What was already landed, and is only consumed here

* `Gtz.posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos`
  (`Gtz/Quantitative/WindowPolarity.lean`) — a symmetric `3 x 3` form with three positive
  invariants is positive definite.  This file consumes that direction only.
* `Gtz.secondInvariant_neg_or_det_nonpos_of_isTie_sixThree`
  (`Gtz/Design/StressFreeStratum.lean`) — the per-triple DICHOTOMY at a tie.
* `Gtz.sixThree_trace_gap_nonneg_of_isTie` (same file) — the leverage floor, read as a
  nonnegative gap trace on all twenty triples.
* `Gtz.sum_principalMinorTotal_subsetSum_eq` (`Gtz/Quantitative/CauchyBinetLayerSum.lean`)
  — the Cauchy-Binet layer count at every level.
* `Gtz.leverage_one_le_of_isTie_sixThree` (`Gtz/Design/StratumEmptinessLedger.lean`).
* `Gtz.exists_one_lt_leverage_of_two_le_rank` (`Gtz/Wave/AllHeavyHingeSchur.lean`).

## What is new here

1. **The eigenvalue dictionary at rank three**, `Gtz.eigenvalueDictionary_three`.  One
   factored characteristic cubic evaluated at three points.

2. **The tie reads one eigenvalue**, `Gtz.exists_eigenvalue_le_one_of_not_posDef_sub_one`.
   A positive semidefinite `3 x 3` form whose unit shift is not positive definite has an
   eigenvalue of at most one.  Everything per-triple below is a corollary of that one line.

3. **The inverse-trace bound**, `Gtz.det_le_secondInvariantOfThree_of_not_posDef_sub_one`:
   `det M <= e2 M`, that is `1/s1 + 1/s2 + 1/s3 >= 1`.  It needs no leverage floor and no
   size restriction, so it holds at every `(m,3)` tie.

4. **THE SHARP TRIPLE VOLUME BOUND**, `Gtz.four_mul_det_subsetSum_le_sq_of_isTie_sixThree`:

       4 * det S_C <= (sum_{c in C} leverage c - 1)^2

   at every triple of a `(6,3)` tie.  This bounds the squared volume of a triple by its
   leverage total alone.  It is ATTAINED: the base triple of
   `Gtz.nonUniformLeverageTieDesign` has Gram spectrum `(1, 9, 9)`, leverage total `19`
   and determinant `81`, and `4 * 81 = 324 = 18^2`.  Part 7 lands that witness.

5. **The moment inequality**, `Gtz.det_moment_le_of_isTie_rankThree`:

       det N <= (m - 2) * e2 N     at every `(m,3)` tie,

   and its leverage companion `Gtz.four_mul_det_moment_le_sq_traceTotal_of_isTie_sixThree`.

6. **The counting theorem**, `Gtz.det_moment_add_branchTotal_le_of_isTie_sixThree` and
   `Gtz.two_mul_card_branch_le_of_isTie_sixThree`.

7. **The first-invariant branch is redundant**, `Gtz.secondInvariantOfThree_nonpos_of_trace_eq_zero`
   and `Gtz.card_traceZeroBranch_le_ten`.

## Why the recorded layer no-go does not block this

`Gtz/Quantitative/WindowCofactorBridge.lean` records that the layer identities hold for
ARBITRARY vectors, so no combination of them alone separates a tie from a non-tie.  That
is correct and it is respected here.  This file never uses a layer identity alone.  Every
aggregate statement multiplies a layer identity against a tie-only per-triple fact.  The
moment inequality is not vacuous: the design with atoms `e_i / sqrt(t_i)` doubled on each
axis has `N = mu * 1` with `mu` as large as the weights allow, and `det N <= 4 e2 N` forces
`mu <= 12`.  So the inequality does exclude designs, and it excludes exactly the ones with
a strictly dominating triple.

## A trap caught during this work, recorded so nobody repeats it

The same chain run against the WEIGHTED Cauchy-Binet identity
`sum_C (prod_{c in C} t_c) det S_C = 1` produces `sum_c t_c^2 * leverage c <= 1`.  That
looks like the first weight-aware tie constraint in the campaign, and it is VACUOUS: every
design has `t_c * leverage c <= 1`, because `t_c g_c g_c^T` is one summand of the Parseval
resolution and its only nonzero eigenvalue is `t_c * leverage c`.  Summing against
`sum t_c = 1` gives the same bound with no tie hypothesis.  The weighted route therefore
loses exactly the whole tie content.  The unweighted route does not.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.WindowPolarity
import Gtz.Quantitative.CauchyBinetLayerSum
import Gtz.Quantitative.ExpectedCharPolynomial
import Gtz.Quantitative.VolumeAverageLaw
import Gtz.Wave.WedgeSumRuleLayerLaw
import Gtz.Design.StressFreeNormalizer
import Gtz.Design.ConservationCalculus
import Gtz.Design.StressFreeStratum
import Gtz.Design.StratumEmptinessLedger
import Gtz.Wave.AllHeavyHingeSchur
import Gtz.Reduction.ExchangeInvariant
import Gtz.Ties.NonUniformLeverageTie
import Gtz.Quantitative.ExtremalBasisActivity

namespace Gtz

open Matrix

/-! ## Part 1. The eigenvalue dictionary at rank three

The three elementary invariants of a Hermitian `3 x 3` real form are the three elementary
symmetric functions of its eigenvalues.  The characteristic cubic
`Gtz.det_scalar_sub_eq_characteristicCubic` is an entrywise identity, and
`Matrix.IsHermitian.charpoly_eq` factors the same polynomial over the eigenvalues.  Three
evaluation points separate the three coefficients. -/

section EigenvalueDictionary

/-- **The characteristic cubic, factored.**  For a Hermitian `3 x 3` real form the shifted
determinant is the product of the three eigenvalue displacements. -/
theorem det_scalar_sub_eq_eigenvalueProduct {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hherm : form.IsHermitian) (point : ℝ) :
    (Matrix.scalar (Fin 3) point - form).det
      = (point - hherm.eigenvalues 0) * (point - hherm.eigenvalues 1)
        * (point - hherm.eigenvalues 2) := by
  rw [← Matrix.eval_charpoly, hherm.charpoly_eq]
  simp [Fin.prod_univ_three]

/-- **THE DICTIONARY.**  The trace, the second invariant and the determinant of a Hermitian
`3 x 3` real form are the three elementary symmetric functions of its eigenvalues.
Evaluated at `0`, at `1` and at `-1`, the cubic identity is a triangular linear system in
the three coefficients. -/
theorem eigenvalueDictionary_three {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hherm : form.IsHermitian) :
    Matrix.trace form
        = hherm.eigenvalues 0 + hherm.eigenvalues 1 + hherm.eigenvalues 2
      ∧ secondInvariantOfThree form
        = hherm.eigenvalues 0 * hherm.eigenvalues 1
          + hherm.eigenvalues 0 * hherm.eigenvalues 2
          + hherm.eigenvalues 1 * hherm.eigenvalues 2
      ∧ form.det
        = hherm.eigenvalues 0 * hherm.eigenvalues 1 * hherm.eigenvalues 2 := by
  have hzero := det_scalar_sub_eq_eigenvalueProduct hherm 0
  have hone := det_scalar_sub_eq_eigenvalueProduct hherm 1
  have hneg := det_scalar_sub_eq_eigenvalueProduct hherm (-1)
  rw [det_scalar_sub_eq_characteristicCubic] at hzero hone hneg
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(1 : ℝ) / 2) * hone + (-(1 : ℝ) / 2) * hneg + hzero
  · linear_combination ((1 : ℝ) / 2) * hone + (-(1 : ℝ) / 2) * hneg
  · linear_combination (-1 : ℝ) * hzero

end EigenvalueDictionary

/-! ## Part 2. What a tie says at one triple

A tie says no triple dominates strictly.  On the gap of one triple that is exactly the
failure of positive definiteness, and through the inertia bridge it is exactly one
statement about the spectrum of `S_C`: SOME eigenvalue is at most one.  Everything
per-triple in this file is a corollary of that. -/

section OneEigenvalue

/-- The unit shift of a `3 x 3` form moves the trace by three. -/
theorem trace_sub_one_fin_three (form : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (form - 1) = Matrix.trace form - 3 := by
  rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
  norm_num

/-- **THE TIE READS ONE EIGENVALUE.**  A Hermitian `3 x 3` real form whose unit shift is
not positive definite has an eigenvalue of at most one.  The proof is the contrapositive
through the landed inertia bridge: three eigenvalues above one make the three shifted
invariants positive, and three positive invariants make the shift positive definite. -/
theorem exists_eigenvalue_le_one_of_not_posDef_sub_one
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hherm : form.IsHermitian)
    (hnot : ¬ (form - 1).PosDef) :
    hherm.eigenvalues 0 ≤ 1 ∨ hherm.eigenvalues 1 ≤ 1 ∨ hherm.eigenvalues 2 ≤ 1 := by
  by_contra hall
  push Not at hall
  obtain ⟨hzeroLarge, honeLarge, htwoLarge⟩ := hall
  obtain ⟨htrace, hsecond, hdet⟩ := eigenvalueDictionary_three hherm
  have hshiftZero : (0 : ℝ) < hherm.eigenvalues 0 - 1 := by linarith
  have hshiftOne : (0 : ℝ) < hherm.eigenvalues 1 - 1 := by linarith
  have hshiftTwo : (0 : ℝ) < hherm.eigenvalues 2 - 1 := by linarith
  have hgapTrace : Matrix.trace (form - 1)
      = (hherm.eigenvalues 0 - 1) + (hherm.eigenvalues 1 - 1)
        + (hherm.eigenvalues 2 - 1) := by
    rw [trace_sub_one_fin_three, htrace]; ring
  have hgapSecond : secondInvariantOfThree (form - 1)
      = (hherm.eigenvalues 0 - 1) * (hherm.eigenvalues 1 - 1)
        + (hherm.eigenvalues 0 - 1) * (hherm.eigenvalues 2 - 1)
        + (hherm.eigenvalues 1 - 1) * (hherm.eigenvalues 2 - 1) := by
    rw [secondInvariantOfThree_sub_one, hsecond, htrace]; ring
  have hgapDet : (form - 1).det
      = (hherm.eigenvalues 0 - 1) * (hherm.eigenvalues 1 - 1)
        * (hherm.eigenvalues 2 - 1) := by
    rw [det_sub_one_eq_secondInvariantOfThree, hdet, hsecond, htrace]; ring
  refine hnot (posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos
    (hherm.sub Matrix.isHermitian_one) ?_ ?_ ?_)
  · rw [hgapTrace]; linarith
  · rw [hgapSecond]
    have hpairZeroOne := mul_pos hshiftZero hshiftOne
    have hpairZeroTwo := mul_pos hshiftZero hshiftTwo
    have hpairOneTwo := mul_pos hshiftOne hshiftTwo
    linarith
  · rw [hgapDet]
    exact mul_pos (mul_pos hshiftZero hshiftOne) hshiftTwo

end OneEigenvalue

/-! ## Part 3. The inverse-trace bound

`det M <= e2 M` for a positive semidefinite `3 x 3` form whose unit shift is not positive
definite.  In eigenvalues it is `s1 s2 s3 <= s1 s2 <= s1 s2 + s1 s3 + s2 s3`, and the only
input is that one eigenvalue is at most one.  The bound is SHARP: three parallel atoms give
`det M = e2 M = 0`. -/

section InverseTrace

/-- The three-variable core: a product of nonnegatives with one factor at most one is no
larger than the total of the three pair products. -/
theorem prod_le_pairTotal_of_le_one {first second third : ℝ}
    (hfirst : 0 ≤ first) (hsecond : 0 ≤ second) (hthird : 0 ≤ third)
    (hsmall : first ≤ 1) :
    first * second * third
      ≤ first * second + first * third + second * third := by
  nlinarith [mul_nonneg hsecond hthird, mul_nonneg hfirst hsecond,
    mul_nonneg hfirst hthird]

/-- **THE INVERSE-TRACE BOUND.**  A positive semidefinite `3 x 3` real form whose unit
shift is not positive definite satisfies `det M <= e2 M`. -/
theorem det_le_secondInvariantOfThree_of_not_posDef_sub_one
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hpsd : form.PosSemidef)
    (hnot : ¬ (form - 1).PosDef) :
    form.det ≤ secondInvariantOfThree form := by
  obtain ⟨_, hsecond, hdet⟩ := eigenvalueDictionary_three hpsd.1
  have hzeroNonneg : (0 : ℝ) ≤ hpsd.1.eigenvalues 0 := hpsd.eigenvalues_nonneg 0
  have honeNonneg : (0 : ℝ) ≤ hpsd.1.eigenvalues 1 := hpsd.eigenvalues_nonneg 1
  have htwoNonneg : (0 : ℝ) ≤ hpsd.1.eigenvalues 2 := hpsd.eigenvalues_nonneg 2
  rw [hsecond, hdet]
  rcases exists_eigenvalue_le_one_of_not_posDef_sub_one hpsd.1 hnot with
    hsmall | hsmall | hsmall
  · nlinarith [prod_le_pairTotal_of_le_one hzeroNonneg honeNonneg htwoNonneg hsmall]
  · nlinarith [prod_le_pairTotal_of_le_one honeNonneg hzeroNonneg htwoNonneg hsmall]
  · nlinarith [prod_le_pairTotal_of_le_one htwoNonneg hzeroNonneg honeNonneg hsmall]

/-- **THE BOUND AT A TIE, ANY SIZE.**  Every triple of an `(m,3)` tie has
`det S_C <= e2 S_C`.  No leverage floor and no size restriction enter: the subset sum is
positive semidefinite for free, and `IsTie` supplies exactly the failure of positive
definiteness the bound needs. -/
theorem det_subsetSum_le_secondInvariantOfThree_of_isTie {size : ℕ}
    (design : WeightedDesign size 3) (htie : IsTie design)
    {selected : Finset (Fin size)} (hcard : selected.card = 3) :
    (subsetSum design selected).det
      ≤ secondInvariantOfThree (subsetSum design selected) :=
  det_le_secondInvariantOfThree_of_not_posDef_sub_one
    (posSemidef_subsetSum design selected) (htie.2 selected hcard)

/-- The same bound read on the gap: at an `(m,3)` tie the gap determinant of every triple
is at most its gap trace plus two.  In the invariant chart of `S_C - 1` this is
`e3 <= e1 + 2`. -/
theorem det_gap_le_trace_gap_add_two_of_isTie {size : ℕ}
    (design : WeightedDesign size 3) (htie : IsTie design)
    {selected : Finset (Fin size)} (hcard : selected.card = 3) :
    (subsetSum design selected - 1).det
      ≤ Matrix.trace (subsetSum design selected - 1) + 2 := by
  have hbound := det_subsetSum_le_secondInvariantOfThree_of_isTie design htie hcard
  rw [det_sub_one_eq_secondInvariantOfThree, trace_sub_one_fin_three]
  linarith

end InverseTrace

/-! ## Part 4. The sharp triple volume bound

The strongest per-triple consequence of a tie in this file, and the one that reads the
leverage floor.  If a positive semidefinite form has an eigenvalue at most one and a trace
at least three then

    4 * det M <= (tr M - 1)^2 .

The proof is two steps of arithmetic-geometric comparison.  Write `a` for the small
eigenvalue and `L` for the trace.  Then `4 a b c <= a (b + c)^2 = a (L - a)^2`, and the
displayed factorization

    (L-1)^2 - a (L-a)^2 = (1-a) (L-1) (L-3) + (1-a)^2 (2L - 2 - a)

is nonnegative term by term for `0 <= a <= 1` and `L >= 3`.

Equality forces `a = 1` and `b = c`, that is the spectrum `(1, (L-1)/2, (L-1)/2)`.  The
base triple of `Gtz.nonUniformLeverageTieDesign` has spectrum `(1, 9, 9)`, so the bound is
ATTAINED at a landed `(6,3)` tie.  Part 7 lands that witness. -/

section SharpVolume

/-- The three-variable core of the sharp volume bound, with the factorization displayed.
Only the first slot is constrained: the other two are arbitrary reals, because the total
bound `3 <= first + second + third` together with `first <= 1` already forces their sum to
be at least two. -/
theorem four_mul_prod_le_sq_total_sub_one {first second third : ℝ}
    (hfirst : 0 ≤ first) (hsmall : first ≤ 1) (htotal : 3 ≤ first + second + third) :
    4 * (first * second * third) ≤ (first + second + third - 1) ^ 2 := by
  set total := first + second + third with htotalDef
  have hsplit : second + third = total - first := by rw [htotalDef]; ring
  -- Step one: the two free eigenvalues compare by arithmetic-geometric mean.
  have hpair : 4 * (second * third) ≤ (total - first) ^ 2 := by
    have hsq : 4 * (second * third) ≤ (second + third) ^ 2 := by nlinarith [sq_nonneg (second - third)]
    rw [hsplit] at hsq
    exact hsq
  have hstepOne : 4 * (first * second * third) ≤ first * (total - first) ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hpair hfirst
    nlinarith [hscaled]
  -- Step two: the displayed factorization is nonnegative term by term.
  have hfactor : (total - 1) ^ 2 - first * (total - first) ^ 2
      = (1 - first) * ((total - 1) * (total - 3))
        + (1 - first) ^ 2 * (2 * total - 2 - first) := by ring
  have hsmallGap : (0 : ℝ) ≤ 1 - first := by linarith
  have hlow : (0 : ℝ) ≤ (total - 1) * (total - 3) := by
    apply mul_nonneg <;> linarith
  have hhigh : (0 : ℝ) ≤ 2 * total - 2 - first := by linarith
  have hstepTwo : first * (total - first) ^ 2 ≤ (total - 1) ^ 2 := by
    nlinarith [mul_nonneg hsmallGap hlow, mul_nonneg (sq_nonneg (1 - first)) hhigh, hfactor]
  linarith

/-- **THE SHARP TRIPLE VOLUME BOUND, at one matrix.**  A positive semidefinite `3 x 3` real
form of trace at least three whose unit shift is not positive definite satisfies

    4 * det M <= (tr M - 1)^2 . -/
theorem four_mul_det_le_sq_trace_sub_one_of_not_posDef_sub_one
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hpsd : form.PosSemidef)
    (hnot : ¬ (form - 1).PosDef) (htrace : 3 ≤ Matrix.trace form) :
    4 * form.det ≤ (Matrix.trace form - 1) ^ 2 := by
  obtain ⟨htotal, _, hdet⟩ := eigenvalueDictionary_three hpsd.1
  have hzeroNonneg : (0 : ℝ) ≤ hpsd.1.eigenvalues 0 := hpsd.eigenvalues_nonneg 0
  have honeNonneg : (0 : ℝ) ≤ hpsd.1.eigenvalues 1 := hpsd.eigenvalues_nonneg 1
  have htwoNonneg : (0 : ℝ) ≤ hpsd.1.eigenvalues 2 := hpsd.eigenvalues_nonneg 2
  rw [htotal] at htrace
  rw [hdet, htotal]
  rcases exists_eigenvalue_le_one_of_not_posDef_sub_one hpsd.1 hnot with
    hsmall | hsmall | hsmall
  · exact four_mul_prod_le_sq_total_sub_one hzeroNonneg hsmall (by linarith)
  · have hperm := four_mul_prod_le_sq_total_sub_one (second := hpsd.1.eigenvalues 0)
      (third := hpsd.1.eigenvalues 2) honeNonneg hsmall (by linarith)
    nlinarith [hperm]
  · have hperm := four_mul_prod_le_sq_total_sub_one (second := hpsd.1.eigenvalues 0)
      (third := hpsd.1.eigenvalues 1) htwoNonneg hsmall (by linarith)
    nlinarith [hperm]

/-- **THE SHARP TRIPLE VOLUME BOUND AT A `(6,3)` TIE.**  For every one of the twenty
triples,

    4 * det S_C <= (sum_{c in C} leverage c - 1)^2 .

The squared volume of a triple is bounded by its leverage total alone.  The leverage floor
supplies the trace hypothesis, so this is the first per-triple bound in the file that is
special to `(6,3)`.  It is ATTAINED at the base triple of
`Gtz.nonUniformLeverageTieDesign`, where the leverage total is `19` and the determinant is
`81`. -/
theorem four_mul_det_subsetSum_le_sq_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    4 * (subsetSum design selected).det
      ≤ (∑ atomLabel ∈ selected, leverageOf (design.atom atomLabel) - 1) ^ 2 := by
  have hfloor := sixThree_trace_gap_nonneg_of_isTie design htie hcard
  rw [trace_sub_one_fin_three] at hfloor
  have hbound := four_mul_det_le_sq_trace_sub_one_of_not_posDef_sub_one
    (posSemidef_subsetSum design selected) (htie.2 selected hcard) (by linarith)
  rwa [trace_subsetSum] at hbound

end SharpVolume

/-! ## Part 5. The three layer totals at rank three

`Gtz.sum_principalMinorTotal_subsetSum_eq` is the Cauchy-Binet layer count at every level.
At rank three only three levels are live, and the binomial coefficients are `C(m-1, 2)`,
`C(m-2, 1) = m - 2` and `C(m-3, 0) = 1`.  Nothing in this part is a tie fact. -/

section LayerTotals

variable {m : ℕ}

/-- **LEVEL ONE.**  The triple traces total `C(m-1, 2)` copies of the moment trace.  At
`m = 6` the coefficient is ten. -/
theorem sum_trace_subsetSum_rankThree (design : WeightedDesign m 3) :
    ∑ block ∈ (Finset.univ : Finset (Fin m)).powersetCard 3,
        Matrix.trace (subsetSum design block)
      = (((m - 1).choose 2 : ℕ) : ℝ) * Matrix.trace (subsetSum design Finset.univ) := by
  have hlayer := sum_principalMinorTotal_subsetSum_eq design 1 (by norm_num)
  simp only [principalMinorTotal_one] at hlayer
  simpa using hlayer

/-- **LEVEL TWO.**  The triple second invariants total `m - 2` copies of the moment second
invariant.  At `m = 6` the coefficient is four, at `m = 5` it is three. -/
theorem sum_secondInvariantOfThree_subsetSum_rankThree (design : WeightedDesign m 3) :
    ∑ block ∈ (Finset.univ : Finset (Fin m)).powersetCard 3,
        secondInvariantOfThree (subsetSum design block)
      = ((m - 2 : ℕ) : ℝ) * secondInvariantOfThree (subsetSum design Finset.univ) := by
  have hlayer := sum_principalMinorTotal_subsetSum_eq design 2 (by norm_num)
  simp only [principalMinorTotal_two_eq_secondInvariantOfThree] at hlayer
  simpa [Nat.choose_one_right] using hlayer

/-- **LEVEL THREE.**  The triple determinants total the moment determinant exactly.  This
is Cauchy-Binet at the top level and it carries no coefficient. -/
theorem sum_det_subsetSum_rankThree (design : WeightedDesign m 3) :
    ∑ block ∈ (Finset.univ : Finset (Fin m)).powersetCard 3,
        (subsetSum design block).det
      = (subsetSum design Finset.univ).det := by
  have hlayer := sum_principalMinorTotal_subsetSum_eq design 3 (by norm_num)
  have hblock : ∀ block : Finset (Fin m),
      principalMinorTotal (subsetSum design block) 3 = (subsetSum design block).det := by
    intro block
    have hcard := principalMinorTotal_card (subsetSum design block)
    rwa [Fintype.card_fin] at hcard
  simp only [hblock] at hlayer
  simpa using hlayer

/-- The number of triples of `Fin index`. -/
theorem card_powersetCard_three (index : ℕ) :
    ((Finset.univ : Finset (Fin index)).powersetCard 3).card = index.choose 3 := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **THE FIRST-INVARIANT LAYER LAW AT `(6,3)`.**  The twenty gap traces total
`10 tr N - 60`.  The companions at levels two and three are
`Gtz.sum_secondInvariantOfThree_subsetSum_sub_one_sixThree` and
`Gtz.sum_det_subsetSum_sub_one_sixThree_eq`, both landed. -/
theorem sum_trace_subsetSum_sub_one_sixThree (design : WeightedDesign 6 3) :
    ∑ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        Matrix.trace (subsetSum design block - 1)
      = 10 * Matrix.trace (subsetSum design Finset.univ) - 60 := by
  have hshift : ∀ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      Matrix.trace (subsetSum design block - 1)
        = Matrix.trace (subsetSum design block) - 3 :=
    fun block _ => trace_sub_one_fin_three (subsetSum design block)
  have hten : (6 - 1 : ℕ).choose 2 = 10 := by decide
  have htwenty : (6 : ℕ).choose 3 = 20 := by decide
  rw [Finset.sum_congr rfl hshift, Finset.sum_sub_distrib,
    sum_trace_subsetSum_rankThree design, Finset.sum_const, card_powersetCard_three,
    hten, htwenty, nsmul_eq_mul]
  norm_num

end LayerTotals

/-! ## Part 6. The two moment inequalities

Each per-triple bound summed against the matching layer total.  These are the first
aggregate consequences of a tie that name only the unweighted moment `N` and the leverage
profile. -/

section MomentInequality

/-- **THE MOMENT INEQUALITY AT RANK THREE.**  At every `(m,3)` tie the unweighted moment
`N = sum_c g_c g_c^T` satisfies

    det N <= (m - 2) * e2 N .

Equivalently `det N <= (m-2) tr(adj N)`, and when `N` is invertible
`tr(N^{-1}) >= 1 / (m - 2)`.

The layer identity alone proves nothing — that is the recorded no-go of
`Gtz/Quantitative/WindowCofactorBridge.lean` — and the per-triple fact alone says nothing
about `N`.  Their product is the statement. -/
theorem det_moment_le_of_isTie_rankThree {m : ℕ} (design : WeightedDesign m 3)
    (htie : IsTie design) :
    (subsetSum design Finset.univ).det
      ≤ ((m - 2 : ℕ) : ℝ) * secondInvariantOfThree (subsetSum design Finset.univ) := by
  have hterm : ∀ block ∈ (Finset.univ : Finset (Fin m)).powersetCard 3,
      (subsetSum design block).det ≤ secondInvariantOfThree (subsetSum design block) := by
    intro block hmember
    exact det_subsetSum_le_secondInvariantOfThree_of_isTie design htie
      (Finset.mem_powersetCard.mp hmember).2
  have hsum := Finset.sum_le_sum hterm
  rwa [sum_det_subsetSum_rankThree design,
    sum_secondInvariantOfThree_subsetSum_rankThree design] at hsum

/-- **THE `(6,3)` READING.**  `det N <= 4 e2 N`. -/
theorem det_moment_le_four_mul_secondInvariant_of_isTie_sixThree
    (design : WeightedDesign 6 3) (htie : IsTie design) :
    (subsetSum design Finset.univ).det
      ≤ 4 * secondInvariantOfThree (subsetSum design Finset.univ) := by
  have hbound := det_moment_le_of_isTie_rankThree design htie
  have hcoeff : ((6 - 2 : ℕ) : ℝ) = 4 := by norm_num
  rwa [hcoeff] at hbound

/-- **THE `(5,3)` READING.**  `det N <= 3 e2 N`.  The `(5,3)` tie is not hypothetical:
`Gtz.diamondDesign_isTie` inhabits it.  The constant `m - 2` GROWS with the size, so this
family is WEAKER at `(6,3)` than at `(5,3)` and cannot by itself separate the two rungs.
Part 8 records that reading. -/
theorem det_moment_le_three_mul_secondInvariant_of_isTie_fiveThree
    (design : WeightedDesign 5 3) (htie : IsTie design) :
    (subsetSum design Finset.univ).det
      ≤ 3 * secondInvariantOfThree (subsetSum design Finset.univ) := by
  have hbound := det_moment_le_of_isTie_rankThree design htie
  have hcoeff : ((5 - 2 : ℕ) : ℝ) = 3 := by norm_num
  rwa [hcoeff] at hbound

/-- The moment inequality in adjugate form at `(6,3)`. -/
theorem det_moment_le_four_mul_trace_adjugate_of_isTie_sixThree
    (design : WeightedDesign 6 3) (htie : IsTie design) :
    (subsetSum design Finset.univ).det
      ≤ 4 * Matrix.trace (subsetSum design Finset.univ).adjugate := by
  have hbound := det_moment_le_four_mul_secondInvariant_of_isTie_sixThree design htie
  rwa [trace_adjugate_eq_secondInvariantOfThree]

/-- **THE LEVERAGE MOMENT INEQUALITY AT `(6,3)`.**  The sharp volume bound of Part 4,
summed against Cauchy-Binet at the top level:

    4 * det N <= sum_C (sum_{c in C} leverage c - 1)^2 .

In closed form the right side is `6 * sum_c leverage_c^2 + 4 tau^2 - 20 tau + 20` with
`tau = tr N`, because each label lies in ten triples and each pair in four.  Exact
calibration: the split diamond tie gives `700 <= 2275/2`, the non-uniform tie gives
`1620 <= 2430`, and the `(5,3)` diamond gives `500 <= 2575/4`. -/
theorem four_mul_det_moment_le_sq_traceTotal_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) :
    4 * (subsetSum design Finset.univ).det
      ≤ ∑ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
          (∑ atomLabel ∈ block, leverageOf (design.atom atomLabel) - 1) ^ 2 := by
  have hterm : ∀ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      4 * (subsetSum design block).det
        ≤ (∑ atomLabel ∈ block, leverageOf (design.atom atomLabel) - 1) ^ 2 := by
    intro block hmember
    exact four_mul_det_subsetSum_le_sq_of_isTie_sixThree design htie
      (Finset.mem_powersetCard.mp hmember).2
  have hsum := Finset.sum_le_sum hterm
  rwa [← Finset.mul_sum, sum_det_subsetSum_rankThree design] at hsum

end MomentInequality

/-! ## Part 7. The counting theorem

The moment inequality throws away the whole nonpositive-determinant branch.  Putting it
back bounds how many triples can sit in that branch, in terms of the slack
`4 e2 N - det N`.

The statement quantifies over an ARBITRARY family of triples with nonpositive gap
determinant, so it needs no decidability instance, and it applies to the full branch by
taking the family to be all twenty triples. -/

section Counting

/-- **THE COUNTING THEOREM.**  At a `(6,3)` tie, every family of triples whose gap
determinant is nonpositive pays its gap trace plus two out of the moment slack:

    det N + sum_{C in family} (tr(S_C - 1) + 2) <= 4 e2 N .

The triples outside the family are charged only the Part 3 bound `det S_C <= e2 S_C`,
which is sharp, so nothing more can be extracted from them. -/
theorem det_moment_add_branchTotal_le_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) (family : Finset (Finset (Fin 6)))
    (hsub : family ⊆ (Finset.univ : Finset (Fin 6)).powersetCard 3)
    (hbranch : ∀ block ∈ family, (subsetSum design block - 1).det ≤ 0) :
    (subsetSum design Finset.univ).det
        + ∑ block ∈ family, (Matrix.trace (subsetSum design block - 1) + 2)
      ≤ 4 * secondInvariantOfThree (subsetSum design Finset.univ) := by
  classical
  set allBlocks := (Finset.univ : Finset (Fin 6)).powersetCard 3 with hallBlocks
  have houtside : ∑ block ∈ allBlocks \ family, (subsetSum design block).det
      ≤ ∑ block ∈ allBlocks \ family, secondInvariantOfThree (subsetSum design block) := by
    refine Finset.sum_le_sum fun block hmember => ?_
    have hin : block ∈ allBlocks := (Finset.mem_sdiff.mp hmember).1
    exact det_subsetSum_le_secondInvariantOfThree_of_isTie design htie
      (Finset.mem_powersetCard.mp hin).2
  have hinside : ∑ block ∈ family,
        ((subsetSum design block).det + (Matrix.trace (subsetSum design block - 1) + 2))
      ≤ ∑ block ∈ family, secondInvariantOfThree (subsetSum design block) := by
    refine Finset.sum_le_sum fun block hmember => ?_
    have hgap := hbranch block hmember
    rw [det_sub_one_eq_secondInvariantOfThree] at hgap
    rw [trace_sub_one_fin_three]
    linarith
  have hsplitDet : (∑ block ∈ allBlocks \ family, (subsetSum design block).det)
      + ∑ block ∈ family, (subsetSum design block).det
      = ∑ block ∈ allBlocks, (subsetSum design block).det := Finset.sum_sdiff hsub
  have hsplitSecond :
      (∑ block ∈ allBlocks \ family, secondInvariantOfThree (subsetSum design block))
      + ∑ block ∈ family, secondInvariantOfThree (subsetSum design block)
      = ∑ block ∈ allBlocks, secondInvariantOfThree (subsetSum design block) :=
    Finset.sum_sdiff hsub
  rw [Finset.sum_add_distrib] at hinside
  have htotalDet : ∑ block ∈ allBlocks, (subsetSum design block).det
      = (subsetSum design Finset.univ).det := sum_det_subsetSum_rankThree design
  have htotalSecond : ∑ block ∈ allBlocks,
      secondInvariantOfThree (subsetSum design block)
      = 4 * secondInvariantOfThree (subsetSum design Finset.univ) := by
    have hlayer := sum_secondInvariantOfThree_subsetSum_rankThree design
    have hcoeff : ((6 - 2 : ℕ) : ℝ) = 4 := by norm_num
    rwa [hcoeff] at hlayer
  rw [htotalDet] at hsplitDet
  rw [htotalSecond] at hsplitSecond
  linarith

/-- **THE CARD BOUND.**  At a `(6,3)` tie the leverage floor makes every gap trace
nonnegative, so each member of a nonpositive-determinant family costs at least two:

    2 * card(family) <= 4 e2 N - det N . -/
theorem two_mul_card_branch_le_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) (family : Finset (Finset (Fin 6)))
    (hsub : family ⊆ (Finset.univ : Finset (Fin 6)).powersetCard 3)
    (hbranch : ∀ block ∈ family, (subsetSum design block - 1).det ≤ 0) :
    2 * (family.card : ℝ)
      ≤ 4 * secondInvariantOfThree (subsetSum design Finset.univ)
        - (subsetSum design Finset.univ).det := by
  have hmain := det_moment_add_branchTotal_le_of_isTie_sixThree design htie family hsub hbranch
  have hfloor : ∑ _block ∈ family, (2 : ℝ)
      ≤ ∑ block ∈ family, (Matrix.trace (subsetSum design block - 1) + 2) := by
    refine Finset.sum_le_sum fun block hmember => ?_
    have hin := hsub hmember
    have hnonneg := sixThree_trace_gap_nonneg_of_isTie design htie
      (Finset.mem_powersetCard.mp hin).2
    linarith
  rw [Finset.sum_const, nsmul_eq_mul] at hfloor
  linarith

/-- **A SMALL MOMENT SLACK FORCES A POSITIVE GAP DETERMINANT.**  If a `(6,3)` tie has
`4 e2 N - det N < 40` then some triple has a strictly positive gap determinant.  Such a
triple is not a strict dominator, so by the landed dichotomy its second invariant is
strictly negative: its gap carries the signature `(+,-,-)`, exactly what
`Gtz.hasNoTwoNegativeGapTriple` excludes. -/
theorem exists_det_gap_pos_of_momentSlack_lt_forty (design : WeightedDesign 6 3)
    (htie : IsTie design)
    (hslack : 4 * secondInvariantOfThree (subsetSum design Finset.univ)
      - (subsetSum design Finset.univ).det < 40) :
    ∃ block : Finset (Fin 6), block.card = 3 ∧ 0 < (subsetSum design block - 1).det := by
  by_contra hnone
  push Not at hnone
  have hbranch : ∀ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (subsetSum design block - 1).det ≤ 0 := by
    intro block hmember
    exact hnone block (Finset.mem_powersetCard.mp hmember).2
  have hcount := two_mul_card_branch_le_of_isTie_sixThree design htie
    ((Finset.univ : Finset (Fin 6)).powersetCard 3) (Finset.Subset.refl _) hbranch
  have htwenty : (6 : ℕ).choose 3 = 20 := by decide
  rw [card_powersetCard_three, htwenty] at hcount
  norm_num at hcount
  linarith

/-- **A POSITIVE GAP DETERMINANT AT A TIE IS A TWO-NEGATIVE GAP.**  The landed dichotomy,
read on the branch the counting theorem produces.  The two spellings of the second
invariant in the corpus agree by definition, and the bridge is taken here. -/
theorem secondInvariantOfThree_neg_of_det_gap_pos_of_isTie_sixThree
    (design : WeightedDesign 6 3) (htie : IsTie design) {selected : Finset (Fin 6)}
    (hcard : selected.card = 3) (hdet : 0 < (subsetSum design selected - 1).det) :
    secondInvariantOfThree (subsetSum design selected - 1) < 0 := by
  have hbridge : secondInvariantThree (subsetSum design selected - 1)
      = secondInvariantOfThree (subsetSum design selected - 1) := rfl
  rcases secondInvariant_neg_or_det_nonpos_of_isTie_sixThree design htie hcard with
    hsecond | hbad
  · rwa [hbridge] at hsecond
  · exact absurd hbad (not_le.mpr hdet)

end Counting

/-! ## Part 8. The first-invariant branch is redundant

The invariant criterion labels each triple of a tie by `e1 = 0` or `e2 <= 0` or `e3 <= 0`,
because the leverage floor makes `e1 >= 0` on all twenty triples.  The first branch is
contained in the second, so the three-branch cut collapses onto the landed two-branch one.
It also holds at most half the triples. -/

section TraceZeroBranch

/-- **A TRACE-ZERO SYMMETRIC FORM HAS A NONPOSITIVE SECOND INVARIANT.**  For a symmetric
`3 x 3` form, `2 e2 = (tr)^2 - |M|_F^2`, so a vanishing trace forces
`e2 = - |M|_F^2 / 2 <= 0`.  No positivity is used. -/
theorem secondInvariantOfThree_nonpos_of_trace_eq_zero
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymm : formᵀ = form)
    (htrace : Matrix.trace form = 0) :
    secondInvariantOfThree form ≤ 0 := by
  have hzeroOne : form 1 0 = form 0 1 := by
    simpa using (congrFun (congrFun hsymm 1) 0).symm
  have hzeroTwo : form 2 0 = form 0 2 := by
    simpa using (congrFun (congrFun hsymm 2) 0).symm
  have honeTwo : form 2 1 = form 1 2 := by
    simpa using (congrFun (congrFun hsymm 2) 1).symm
  rw [Matrix.trace_fin_three] at htrace
  have hsquare : (form 0 0 + form 1 1 + form 2 2) ^ 2 = 0 := by rw [htrace]; ring
  rw [secondInvariantOfThree, hzeroOne, hzeroTwo, honeTwo]
  nlinarith [hsquare, sq_nonneg (form 0 0), sq_nonneg (form 1 1), sq_nonneg (form 2 2),
    sq_nonneg (form 0 1), sq_nonneg (form 0 2), sq_nonneg (form 1 2)]

/-- **BRANCH ONE IS INSIDE BRANCH TWO.**  A triple whose gap trace vanishes has a
nonpositive gap second invariant, at every size and with no tie hypothesis.  So the
three-branch cut adds nothing to the landed
`Gtz.secondInvariant_neg_or_det_nonpos_of_isTie_sixThree`. -/
theorem secondInvariantOfThree_gap_nonpos_of_trace_gap_eq_zero {size : ℕ}
    (design : WeightedDesign size 3) {selected : Finset (Fin size)}
    (hzero : Matrix.trace (subsetSum design selected - 1) = 0) :
    secondInvariantOfThree (subsetSum design selected - 1) ≤ 0 :=
  secondInvariantOfThree_nonpos_of_trace_eq_zero
    (transpose_eq_of_isHermitian (isHermitian_subsetSum_sub_one design selected)) hzero

/-- **BRANCH-ONE RIGIDITY.**  At a `(6,3)` tie a triple with vanishing gap trace has ALL
THREE of its leverages exactly one.  The leverage floor puts each leverage at least one and
the trace pins their total at three, so no slack survives. -/
theorem leverage_eq_one_of_mem_of_trace_gap_eq_zero (design : WeightedDesign 6 3)
    (htie : IsTie design) {selected : Finset (Fin 6)}
    (hzero : Matrix.trace (subsetSum design selected - 1) = 0)
    (hcard : selected.card = 3) {label : Fin 6} (hmem : label ∈ selected) :
    leverageOf (design.atom label) = 1 := by
  have hfloor := leverage_one_le_of_isTie_sixThree design htie
  rw [trace_sub_one_fin_three, trace_subsetSum] at hzero
  have htotal : ∑ atomLabel ∈ selected, leverageOf (design.atom atomLabel) = 3 := by
    linarith
  have hexcess : ∑ atomLabel ∈ selected, (leverageOf (design.atom atomLabel) - 1) = 0 := by
    rw [Finset.sum_sub_distrib, htotal, Finset.sum_const, hcard, nsmul_eq_mul]
    norm_num
  have hnonneg : ∀ atomLabel ∈ selected, (0 : ℝ) ≤ leverageOf (design.atom atomLabel) - 1 :=
    fun atomLabel _ => by linarith [hfloor atomLabel]
  have hzeroTerm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hexcess label hmem
  linarith

/-- **A STRICTLY HEAVY ATOM IS OUTSIDE BRANCH ONE.**  If a triple carries an atom of
leverage more than one then its gap trace is strictly positive. -/
theorem trace_gap_pos_of_mem_of_one_lt_leverage (design : WeightedDesign 6 3)
    (htie : IsTie design) {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    {label : Fin 6} (hmem : label ∈ selected)
    (hheavy : 1 < leverageOf (design.atom label)) :
    0 < Matrix.trace (subsetSum design selected - 1) := by
  have hfloor := leverage_one_le_of_isTie_sixThree design htie
  have hsplit : ∑ atomLabel ∈ selected, leverageOf (design.atom atomLabel)
      = leverageOf (design.atom label)
        + ∑ atomLabel ∈ selected.erase label, leverageOf (design.atom atomLabel) :=
    (Finset.add_sum_erase _ _ hmem).symm
  have hcardErase : (selected.erase label).card = 2 := by
    rw [Finset.card_erase_of_mem hmem, hcard]
  have hrest : (2 : ℝ) ≤ ∑ atomLabel ∈ selected.erase label,
      leverageOf (design.atom atomLabel) := by
    have hconst : ∑ _atomLabel ∈ selected.erase label, (1 : ℝ) = 2 := by
      rw [Finset.sum_const, hcardErase, nsmul_eq_mul]; norm_num
    rw [← hconst]
    exact Finset.sum_le_sum fun atomLabel _ => hfloor atomLabel
  rw [trace_sub_one_fin_three, trace_subsetSum, hsplit]
  linarith

/-- **BRANCH ONE HOLDS AT MOST TEN OF THE TWENTY TRIPLES.**  Rank three is above rank one,
so `Gtz.exists_one_lt_leverage_of_two_le_rank` gives a strictly heavy atom with no tie
hypothesis at all.  Every trace-zero triple avoids that atom, and only ten of the twenty
triples avoid a fixed label. -/
theorem card_traceZeroBranch_le_ten (design : WeightedDesign 6 3) (htie : IsTie design)
    (family : Finset (Finset (Fin 6)))
    (hsub : family ⊆ (Finset.univ : Finset (Fin 6)).powersetCard 3)
    (hzero : ∀ block ∈ family, Matrix.trace (subsetSum design block - 1) = 0) :
    family.card ≤ 10 := by
  classical
  obtain ⟨heavyLabel, hheavy⟩ := exists_one_lt_leverage_of_two_le_rank design (by norm_num)
  have hinside : family ⊆ (Finset.univ.erase heavyLabel).powersetCard 3 := by
    intro block hmember
    have hin := hsub hmember
    have hcard := (Finset.mem_powersetCard.mp hin).2
    have hmiss : heavyLabel ∉ block := by
      intro hbad
      have hpos := trace_gap_pos_of_mem_of_one_lt_leverage design htie hcard hbad hheavy
      rw [hzero block hmember] at hpos
      exact lt_irrefl _ hpos
    refine Finset.mem_powersetCard.mpr ⟨?_, hcard⟩
    intro atomLabel hatom
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ atomLabel⟩
    rintro rfl
    exact hmiss hatom
  have hcardBound := Finset.card_le_card hinside
  rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ heavyLabel),
    Finset.card_univ, Fintype.card_fin] at hcardBound
  have hten : (6 - 1 : ℕ).choose 3 = 10 := by decide
  rwa [hten] at hcardBound

/-- **NO `(6,3)` TIE HAS ALL TWENTY TRIPLES IN BRANCH ONE.**  Ten is less than twenty. -/
theorem not_forall_trace_gap_eq_zero_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) :
    ¬ (∀ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        Matrix.trace (subsetSum design block - 1) = 0) := by
  intro hall
  have hcount := card_traceZeroBranch_le_ten design htie
    ((Finset.univ : Finset (Fin 6)).powersetCard 3) (Finset.Subset.refl _) hall
  rw [card_powersetCard_three] at hcount
  have habsurd : ¬ ((6 : ℕ).choose 3 ≤ 10) := by decide
  exact habsurd hcount

/-- **ALL LEVERAGES ONE IS IMPOSSIBLE AT RANK THREE.**  The same collapse read through
`Gtz.rank_eq_one_of_forall_leverage_eq_one`, with no tie hypothesis. -/
theorem not_forall_leverage_eq_one_sixThree (design : WeightedDesign 6 3) :
    ¬ (∀ label : Fin 6, leverageOf (design.atom label) = 1) := by
  intro hall
  have hrank := rank_eq_one_of_forall_leverage_eq_one design hall
  norm_num at hrank

end TraceZeroBranch

/-! ## Part 9. Calibration and sharpness inside a landed `(6,3)` tie

`Gtz.nonUniformLeverageTieDesign` has three heavy atoms at leverage `19/3` and three
PARALLEL light atoms at leverage `4/3`, all three equal to `(2/3, 2/3, 2/3)`.  The BASE
triple attains the sharp volume bound of Part 4 and the LIGHT triple attains the
inverse-trace bound of Part 3.

Exact branch table of that tie.  Writing `(e1, e2, e3)` for the gap invariants:

* `{0,1,2}` — `(16, 64, 0)`, a weak dominator, Gram spectrum `(1, 9, 9)`.
* the nine triples with two heavy atoms — `(11, 24, 0)`.
* the nine triples with one heavy atom — `(6, 1, -8)`.
* `{3,4,5}` — `(1, -5, 3)`, the ONLY triple with a positive gap determinant.

Nineteen of the twenty triples lie in the nonpositive-determinant branch, and the counting
theorem reads `2 * 19 = 38 <= 4 * 171 - 405 = 279`. -/

section Sharpness

/-- The three heavy atoms of the non-uniform tie have Gram
`19/3` on the diagonal and `-8/3` off it. -/
theorem nonUniformLeverageTieDesign_baseTripleSum_form :
    subsetSum nonUniformLeverageTieDesign ({0, 1, 2} : Finset (Fin 6))
      = !![19 / 3, -(8 / 3), -(8 / 3); -(8 / 3), 19 / 3, -(8 / 3);
          -(8 / 3), -(8 / 3), 19 / 3] := by
  rw [subsetSum_triple nonUniformLeverageTieDesign (by decide) (by decide) (by decide)]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, atomMatrix,
      Matrix.cons_val_two] <;> norm_num

/-- **THE SHARP VOLUME BOUND IS ATTAINED AT A LANDED `(6,3)` TIE.**  The base triple has
leverage total `19` and determinant `81`, and `4 * 81 = 324 = (19 - 1)^2`.  Its Gram
spectrum is `(1, 9, 9)`, which is exactly the equality profile of Part 4: the smallest
eigenvalue sits on the tie boundary and the other two coincide.

No per-triple bound of the shape `4 det S_C <= f(leverage total)` can be sharper. -/
theorem nonUniformLeverageTieDesign_baseTriple_sharp :
    Matrix.trace (subsetSum nonUniformLeverageTieDesign ({0, 1, 2} : Finset (Fin 6))) = 19
      ∧ (subsetSum nonUniformLeverageTieDesign ({0, 1, 2} : Finset (Fin 6))).det = 81
      ∧ 4 * (subsetSum nonUniformLeverageTieDesign ({0, 1, 2} : Finset (Fin 6))).det
          = (Matrix.trace (subsetSum nonUniformLeverageTieDesign
              ({0, 1, 2} : Finset (Fin 6))) - 1) ^ 2 := by
  have htrace : Matrix.trace
      (subsetSum nonUniformLeverageTieDesign ({0, 1, 2} : Finset (Fin 6))) = 19 := by
    rw [nonUniformLeverageTieDesign_baseTripleSum_form, Matrix.trace_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hdet : (subsetSum nonUniformLeverageTieDesign ({0, 1, 2} : Finset (Fin 6))).det
      = 81 := by
    rw [nonUniformLeverageTieDesign_baseTripleSum_form, Matrix.det_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨htrace, hdet, ?_⟩
  rw [htrace, hdet]
  norm_num

/-- The three light atoms are equal, so their subset sum is the rank-one form with every
entry `4/3`. -/
theorem nonUniformLeverageTieDesign_lightTripleSum_form :
    subsetSum nonUniformLeverageTieDesign ({3, 4, 5} : Finset (Fin 6))
      = !![4 / 3, 4 / 3, 4 / 3; 4 / 3, 4 / 3, 4 / 3; 4 / 3, 4 / 3, 4 / 3] := by
  rw [subsetSum_triple nonUniformLeverageTieDesign (by decide) (by decide) (by decide)]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, atomMatrix,
      Matrix.cons_val_two] <;> norm_num

/-- **THE INVERSE-TRACE BOUND IS ATTAINED TOO.**  The light triple has
`det S_C = 0 = e2 S_C`, so `det S_C <= e2 S_C` is an EQUALITY there.  Three parallel atoms
are exactly the equality locus of Part 3. -/
theorem nonUniformLeverageTieDesign_lightTriple_det_eq_secondInvariant :
    (subsetSum nonUniformLeverageTieDesign ({3, 4, 5} : Finset (Fin 6))).det = 0
      ∧ secondInvariantOfThree
          (subsetSum nonUniformLeverageTieDesign ({3, 4, 5} : Finset (Fin 6))) = 0 := by
  rw [nonUniformLeverageTieDesign_lightTripleSum_form]
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · rw [secondInvariantOfThree]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The gap of the light triple, entrywise. -/
theorem nonUniformLeverageTieDesign_lightTripleGap_matrix :
    subsetSum nonUniformLeverageTieDesign ({3, 4, 5} : Finset (Fin 6)) - 1
      = !![1 / 3, 4 / 3, 4 / 3; 4 / 3, 1 / 3, 4 / 3; 4 / 3, 4 / 3, 1 / 3] := by
  rw [nonUniformLeverageTieDesign_lightTripleSum_form]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.one_fin_three, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    norm_num

/-- **THE TWO-NEGATIVE BRANCH IS INHABITED AT A REAL `(6,3)` TIE.**  The light triple has
gap invariants `(1, -5, 3)`: nonnegative trace, strictly negative second invariant and
strictly positive determinant, so its inertia is `(+,-,-)`.

This is the exact obstruction to the shipped determinant window.  It also shows that the
conclusion of `Gtz.exists_det_gap_pos_of_momentSlack_lt_forty` describes something real. -/
theorem nonUniformLeverageTieDesign_lightTripleGap_invariants :
    Matrix.trace (subsetSum nonUniformLeverageTieDesign ({3, 4, 5} : Finset (Fin 6)) - 1) = 1
      ∧ secondInvariantOfThree
          (subsetSum nonUniformLeverageTieDesign ({3, 4, 5} : Finset (Fin 6)) - 1) = -5
      ∧ (subsetSum nonUniformLeverageTieDesign ({3, 4, 5} : Finset (Fin 6)) - 1).det = 3 := by
  rw [nonUniformLeverageTieDesign_lightTripleGap_matrix]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.trace_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · rw [secondInvariantOfThree]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · rw [Matrix.det_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- **THE ANTECEDENT IS INHABITED.**  Every theorem of this file assumes `IsTie` at
`(6,3)`.  Two landed designs satisfy it, so no statement above is vacuous. -/
theorem isTie_sixThree_inhabited :
    IsTie sixSplitDiamondDesign ∧ IsTie nonUniformLeverageTieDesign :=
  ⟨sixSplitDiamondDesign_isTie, nonUniformLeverageTieDesign_isTie⟩

/-- The moment inequality at the non-uniform tie.  Exact calibration gives `det N = 405`
and `4 e2 N = 684`, so the slack is `279`. -/
theorem det_moment_le_four_mul_secondInvariant_nonUniformLeverageTie :
    (subsetSum nonUniformLeverageTieDesign Finset.univ).det
      ≤ 4 * secondInvariantOfThree (subsetSum nonUniformLeverageTieDesign Finset.univ) :=
  det_moment_le_four_mul_secondInvariant_of_isTie_sixThree _ nonUniformLeverageTieDesign_isTie

/-- The moment inequality at the split diamond tie.  Exact calibration gives `det N = 175`
and `4 e2 N = 380`, so the slack is `205`. -/
theorem det_moment_le_four_mul_secondInvariant_sixSplitDiamond :
    (subsetSum sixSplitDiamondDesign Finset.univ).det
      ≤ 4 * secondInvariantOfThree (subsetSum sixSplitDiamondDesign Finset.univ) :=
  det_moment_le_four_mul_secondInvariant_of_isTie_sixThree _ sixSplitDiamondDesign_isTie

/-- The sharp volume moment inequality at the non-uniform tie.  Exact calibration gives
`4 det N = 1620` and `sum_C (leverage total - 1)^2 = 2430`. -/
theorem four_mul_det_moment_le_nonUniformLeverageTie :
    4 * (subsetSum nonUniformLeverageTieDesign Finset.univ).det
      ≤ ∑ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
          (∑ atomLabel ∈ block,
            leverageOf (nonUniformLeverageTieDesign.atom atomLabel) - 1) ^ 2 :=
  four_mul_det_moment_le_sq_traceTotal_of_isTie_sixThree _ nonUniformLeverageTieDesign_isTie

end Sharpness

/-! ## Part 10. What separates `(6,3)` from `(5,3)` in this language, and what does not

Exact branch tables of the six fixtures, in rational and quadratic-surd arithmetic.
Writing `tau = tr N`:

| fixture | size | `tau` | `e2 N` | `det N` | `(m-2) e2 N - det N` | triples with `e3 > 0` |
|---|---|---|---|---|---|---|
| `diamondDesign` | `(5,3)` tie | `15` | `75` | `125` | `100` | `0` of `10` |
| `sixSplitDiamondDesign` | `(6,3)` tie | `17` | `95` | `175` | `205` | `0` of `20` |
| `nonUniformLeverageTieDesign` | `(6,3)` tie | `23` | `171` | `405` | `279` | `1` of `20` |
| `icosaDesign` | `(6,3)` strict | `18` | `108` | `216` | `216` | `10` of `20` |
| `kFourDesign` | `(6,3)` strict | `18` | `108` | `216` | `216` | `4` of `20` |
| `graphicKFourDesign` | `(6,3)` strict | `18` | `108` | `216` | `216` | `4` of `20` |

`Gtz.kFourDesign` and `Gtz.graphicKFourDesign` are the same six directions at the same
uniform weight, so their tables agree entry by entry.

The sharp volume bound of Part 4 read on the same fixtures, as `4 det S_C` against
`(leverage total - 1)^2`, tightest triple first:

| fixture | tightest slack | attained at |
|---|---|---|
| `nonUniformLeverageTieDesign` | `0` | the base triple `{0,1,2}` |
| `diamondDesign` `(5,3)` | `25/16` | the rim triple `{1,2,3}` |
| `sixSplitDiamondDesign` | `25/16` | the rim triple `{1,2,3}` |
| `kFourDesign` | `10` | `{0,1,2}` |
| `icosaDesign` | `104/5 - 216 sqrt 5 / 25` | `{0,1,2}` |

**The honest negative.**  Nothing in Part 6 or Part 7 separates the two rungs.  The
constant of the moment inequality is `m - 2`, which GROWS with the size, so the `(6,3)`
statement `det N <= 4 e2 N` is strictly WEAKER than the `(5,3)` statement
`det N <= 3 e2 N`.  The `(5,3)` diamond satisfies its own inequality with slack `100`, and
the two `(6,3)` ties satisfy theirs with slack `205` and `279`.  The counting bound reads
`20 <= 100`, `40 <= 205` and `38 <= 279`: true everywhere, and vacuous everywhere, because
a count of triples can never exceed the number of triples.

**The leverage floor does not separate either.**  It holds at `(4,3)`, `(5,3)` and `(6,3)`
alike, through `Gtz.leverage_one_le_of_isTie` against the proved rungs below.  The `(5,3)`
diamond has gap traces `11/2` and `27/4` on its ten triples, all strictly positive, so the
floor is slack there too.  And the tie floor does not improve the unconditional trace
bound: `Gtz.sq_rank_le_trace_subsetSum_univ` already gives `9 <= tr N` for every `(6,3)`
design, while the floor with the weighted trace identity yields only `8 <= tr N`.  A
`6 <= tr N` or `8 <= tr N` tie corollary is therefore SUPERSEDED and is not landed here.

**The one quantity that moves the right way** is the fraction of triples that dominate
WEAKLY, that is the triples with `e3 = 0` and nonnegative `e1` and `e2`: `8` of `10` at the
`(5,3)` diamond, `12` of `20` at the split diamond and `10` of `20` at the non-uniform tie.
A `(6,3)` proof would have to bound that count from above.  Nothing here touches it,
because both per-triple bounds are inequalities and say nothing about their own equality
locus.

## Where the argument stops, exactly

Two independent per-triple bounds are landed and BOTH are attained inside one landed
`(6,3)` tie: the inverse-trace bound at the light triple and the sharp volume bound at the
base triple.  So neither can be improved as a per-triple statement of its own shape.

On the branch where the gap determinant is positive, `det S_C <= e2 S_C` is the only
available charge and it is exactly attained, so the counting argument gives an upper bound
on the size of the nonpositive-determinant branch and NO upper bound on the size of the
positive-determinant branch — the branch that obstructs the determinant window.  That
asymmetry is where the route stops.

Sharpening would need a strictly positive lower bound on the smallest eigenvalue of `S_C`.
A tie supplies only the upper bound `s_min <= 1`, never a positive floor, and three
parallel atoms realize `s_min = 0` inside a landed tie.  Any further progress must come
from a hypothesis that forbids parallel atoms, which is precisely the content of
`Gtz.HingeHoldsAtSize 6 3`. -/

end Gtz

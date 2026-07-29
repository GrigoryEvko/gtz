/-
# V1: the domination criterion of a triple in SLACK coordinates

The equal-share `(6,3)` stratum (`Gtz.IsEqualShare`) pins BOTH the weights and the
leverages.  The pen's V6 layer keeps only the share — six unit directions with
`sum_c u_c u_c^T = 2 . 1`, so `M = Gamma - 1` is still a hollow symmetric
involution (`Gtz.isHollowInvolution_correlationInvolution`), but the weights `t_c`
are free.  Everything the U6 development proved about the involution therefore
survives verbatim; what breaks is the DICTIONARY, because `Gtz.Dominates` is not
invariant under the atom rescaling that fixes the shares.  Repairing the
dictionary is the whole content of this file.

## The change of variables

Write `ell_c` for the leverage and

  `weightSlack D c := 1 - 1/ell_c`   (the pen's `tau_c`).

At uniform share `s_c = t_c ell_c = k/m` this is `1 - (m/k) t_c`, so at `(6,3)`
it is the pen's `tau_c = 1 - 2 t_c` on the nose
(`Gtz.weightSlack_eq_one_sub_weight_div_atomShare`), and the weight normalisation
`sum_c t_c = 1` becomes

  `sum_c tau_c = m - m/k`,  which at `(6,3)` is `4`
  (`Gtz.sum_weightSlack_of_uniformShare`, `Gtz.sum_weightSlack_eq_four`).

## The criterion

`Gtz.dominates_triple_iff_posSemidef_slackHollowThree`: a triple of distinct atoms
of a rank-three design with all three leverages positive dominates exactly when

  `diag(tau_a, tau_b, tau_c) + M[T] ⪰ 0`,

`M[T]` being the hollow block of the three direction cosines.  The proof is the
congruence by `diag(sqrt(ell))` of the shipped
`Gtz.dominates_triple_iff_posSemidef_tripleGapMatrix` — which needs only that the
three indices are distinct — through `Gtz.posSemidef_congr_right`.  It is NOT the
shipped rho normal form: that one normalises by the EXCESS `ell - 1`, so it
carries an all-heavy hypothesis and degenerates exactly on the boundary
`tau_c -> 0` that the covering argument has to reach.

Expanded (`Gtz.dominates_triple_iff_slackClauses`) the criterion is the pen's four
inequalities plus the three diagonal ones that the pen leaves implicit:

* three PAIRWISE clauses `w_cd <= tau_c tau_d` on the squared cosines
  `Gtz.edgeWeight`;
* one DETERMINANT clause `0 <= Delta`, with
  `Delta = tau_a tau_b tau_c - (tau_a w_bc + tau_b w_ca + tau_c w_ab) + 2 P`
  (`Gtz.slackDeterminantThree`);
* and `0 <= tau_c` at each atom, which on the design side is exactly heaviness.

The pen's FOUR-clause reading, without the diagonal conjuncts, is FALSE:
`Gtz.exists_slackClauses_without_posSemidef` exhibits `tau = (-1, 0, 0)` with all
three edges zero, where the three pairwise clauses and the determinant clause all
hold and the block is not positive semidefinite.  Nothing downstream is affected
— on `Sigma` the diagonal clause is free — but the criterion has to carry it.

## Theorem A

The cell `K_T = {tau | T dominates}` is CONVEX
(`Gtz.convex_tripleSlackCell`, from `PosSemidef.add` and `PosSemidef.smul`, since
the block is affine in `tau` and the edges are share-free), UPWARD CLOSED
(`Gtz.mem_tripleSlackCell_of_le`, from `PosSemidef.diagonal`), CLOSED
(`Gtz.isClosed_tripleSlackCell`) and 3-LOCAL (`Gtz.tripleSlackCell_congr`: the
membership predicate reads exactly three coordinates).  The pen's derivative
statement `dDelta/dtau_c = tau_a tau_b - w_ab` is landed as the three exact
difference identities `Gtz.slackDeterminantThree_sub_first` and siblings, so the
monotonicity is division-free and holds as an equality, not an estimate.

And the covering reformulation is a genuine EQUIVALENCE, not merely a sufficient
condition (`Gtz.gtzUniformShareSixThree_iff_forall_coversHeavySlackSimplex`):

> every uniform-share all-heavy weighted `(6,3)` design has a dominating triple
> **iff** for every unit-norm tight frame of six directions in `R^3` the twenty
> triple cells cover `{tau in (0,1)^6 : sum tau = 4}`.

Both directions are unconditional.  Forward: the design's own unit directions form
such a frame (`Gtz.isUnitTightFrameSix_unitAtomRows`) and its slack vector lies in
the region.  Backward: `Gtz.slackFrameDesign` realises EVERY admissible slack
vector on EVERY such frame as a genuine weighted design, with prescribed slack,
share `1/2` and unchanged directions.  So no realizability gap is hidden: the
frame is the free parameter and the weights are the free point.

The abstract-involution form of the covering is landed only as a SUFFICIENT
condition (`Gtz.exists_dominates_of_coversHeavySlackSimplex`).  Turning that one
into an equivalence would need every hollow symmetric involution on `Fin 6` to be
the Gram of a tight frame — true, but it is a rank-three factorisation this file
does not prove and does not use.

## U6 is one point of this family

`tau ≡ 2/3` is the constant vector of `Sigma`
(`Gtz.constantTwoThirds_mem_slackSimplex`) and it is exactly the equal-share
stratum's slack (`Gtz.weightSlack_eq_two_thirds_of_isEqualShare`), where the
criterion collapses to `(2/3) . 1 + M[T] ⪰ 0`
(`Gtz.slackHollowThree_self`) — U6's conclusion verbatim.  So U6 is literally the
single-point restriction of the covering, and
`Gtz.exists_dominates_of_isEqualShare_six` re-derives the equal-share theorem
through this file's criterion, consuming only the abstract
`Gtz.IsHollowInvolution.exists_posSemidef_twoThirds_shift`.

Upward closure then turns the shipped MARGIN into a genuine band gate:
`Gtz.exists_dominates_of_sixteen_twentyfifths_le_weightSlack` covers every slack
vector with `min_c tau_c >= 16/25`.  That gate is strictly stronger than the pen's
proposed g-transform gate, whose exact threshold is `sqrt 3 - 1` (the brief's
sharpening of the campaign's decimal "about 0.73", correct as stated):
`Gtz.sixteen_twentyfifths_lt_sqrtThree_sub_one`.  The g-transform layer therefore
buys nothing on the top band that the shipped margin does not already buy.

## The weight-side order statistics

`sum tau = 4` with `tau < 1` is a budget, and the budget alone gives the pen's V2.
One pigeonhole `Gtz.exists_lt_of_budget` — no sorting, no `Tuple.sort` — delivers
`Gtz.exists_lt_of_mem_slackSimplex`, whose instances at cardinality `5`, `4`, `3`
are the pen's `tau_(2) > 3/5`, `tau_(3) > 1/2`, `tau_(4) > 1/3`; the cardinality-3
instance is spelt out as `Gtz.card_cheapSlackSet_le_two`, AT MOST TWO ATOMS ARE
CHEAP.  The non-strict top statistic `tau_(1) >= 2/3` is out of that pigeonhole's
reach and gets its own two-line argument
(`Gtz.exists_two_thirds_le_of_sum_eq_four`).

Four atoms above `1/3` in slack is four atoms above `3/2` in leverage
(`Gtz.weightSlack_le_third_iff_leverage_le`), which beats the shipped heaviness
profile on this stratum: `Gtz.rank_sub_one_sub_threshold_le_card_heavySet` at rank
three and excess threshold `1/2` bounds the count below by `3/2` only, hence forces
two such atoms, not four.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Design.FrameConservation
import Gtz.Design.RhoNormalForm
import Gtz.Reduction.PrincipalMinorsThree
import Gtz.Reduction.Reductions
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.WeightProductFloor
import Gtz.Quantitative.EqualShareSixThreeMargin

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {size m k : ℕ}

/-! ## 1. The slack-shifted hollow block

The abstract `3 x 3` object of V1: a hollow symmetric block with an arbitrary
diagonal, rather than the scalar diagonal `level . 1` of
`Gtz.hollowSymmetricThree`'s criterion layer. -/

/-- **The slack-shifted hollow block** `diag(tau) + M[T]`, with the edges in the
slots `(0,1)`, `(0,2)`, `(1,2)` — the slot convention of
`Gtz.hollowMatrixThree` and `Gtz.correlationMatrixThree`. -/
def slackHollowThree (slackFirst slackSecond slackThird
    edgeFirst edgeSecond edgeThird : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![slackFirst, edgeFirst, edgeSecond;
     edgeFirst, slackSecond, edgeThird;
     edgeSecond, edgeThird, slackThird]

theorem slackHollowThree_transpose (slackFirst slackSecond slackThird
    edgeFirst edgeSecond edgeThird : ℝ) :
    (slackHollowThree slackFirst slackSecond slackThird edgeFirst edgeSecond edgeThird)ᵀ
      = slackHollowThree slackFirst slackSecond slackThird edgeFirst edgeSecond edgeThird := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> rfl

/-- The block splits as diagonal plus hollow — the pen's `D_tau[T] + M[T]`. -/
theorem slackHollowThree_eq_diagonal_add (slackFirst slackSecond slackThird
    edgeFirst edgeSecond edgeThird : ℝ) :
    slackHollowThree slackFirst slackSecond slackThird edgeFirst edgeSecond edgeThird
      = Matrix.diagonal ![slackFirst, slackSecond, slackThird]
        + hollowMatrixThree edgeFirst edgeSecond edgeThird := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [slackHollowThree, hollowMatrixThree, Matrix.diagonal]

/-- **THE U6 SLICE.**  At a CONSTANT slack the block is the scalar shift the whole
`Gtz.Quantitative.TripleCubicCriterion` layer is written in.  This one identity is
why U6 is the single point `tau ≡ 2/3` of the V6 family. -/
theorem slackHollowThree_self (level edgeFirst edgeSecond edgeThird : ℝ) :
    slackHollowThree level level level edgeFirst edgeSecond edgeThird
      = level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowMatrixThree edgeFirst edgeSecond edgeThird := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [slackHollowThree, hollowMatrixThree]

/-- **The determinant clause** `Delta` of the pen's V1, in the six scalars. -/
def slackDeterminantThree (slackFirst slackSecond slackThird
    edgeFirst edgeSecond edgeThird : ℝ) : ℝ :=
  slackFirst * slackSecond * slackThird
    - (slackFirst * edgeThird ^ 2 + slackSecond * edgeSecond ^ 2 + slackThird * edgeFirst ^ 2)
    + 2 * (edgeFirst * edgeSecond * edgeThird)

theorem det_slackHollowThree (slackFirst slackSecond slackThird
    edgeFirst edgeSecond edgeThird : ℝ) :
    (slackHollowThree slackFirst slackSecond slackThird edgeFirst edgeSecond edgeThird).det
      = slackDeterminantThree slackFirst slackSecond slackThird
          edgeFirst edgeSecond edgeThird := by
  rw [Matrix.det_fin_three, slackDeterminantThree]
  simp only [slackHollowThree, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-! ### The expanded criterion -/

/-- **V1, EXPANDED.**  The slack-shifted hollow block is positive semidefinite
exactly when the three diagonal entries are nonnegative, the three PAIRWISE
clauses `edge^2 <= slack * slack` hold, and the DETERMINANT clause `0 <= Delta`
holds.

All seven are load-bearing.  The pen lists only the last four; the diagonal ones
are not implied by them, since `slack * slack >= edge^2 >= 0` is compatible with
both slacks negative.  On the design side the diagonal clause is heaviness, so on
the pen's `Sigma` it is free — but the criterion is stated for arbitrary reals and
must carry it. -/
theorem posSemidef_slackHollowThree_iff (slackFirst slackSecond slackThird
    edgeFirst edgeSecond edgeThird : ℝ) :
    (slackHollowThree slackFirst slackSecond slackThird
        edgeFirst edgeSecond edgeThird).PosSemidef
      ↔ 0 ≤ slackFirst ∧ 0 ≤ slackSecond ∧ 0 ≤ slackThird
        ∧ edgeFirst ^ 2 ≤ slackFirst * slackSecond
        ∧ edgeSecond ^ 2 ≤ slackFirst * slackThird
        ∧ edgeThird ^ 2 ≤ slackSecond * slackThird
        ∧ 0 ≤ slackDeterminantThree slackFirst slackSecond slackThird
            edgeFirst edgeSecond edgeThird := by
  constructor
  · intro hpsd
    have hminor : ∀ (selSize : ℕ) (pick : Fin selSize → Fin 3),
        (0 : ℝ) ≤ ((slackHollowThree slackFirst slackSecond slackThird
          edgeFirst edgeSecond edgeThird).submatrix pick pick).det :=
      fun _ pick => (hpsd.submatrix pick).det_nonneg
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hdiag := hminor 1 ![0]
      rwa [Matrix.det_fin_one, Matrix.submatrix_apply] at hdiag
    · have hdiag := hminor 1 ![1]
      rwa [Matrix.det_fin_one, Matrix.submatrix_apply] at hdiag
    · have hdiag := hminor 1 ![2]
      rwa [Matrix.det_fin_one, Matrix.submatrix_apply] at hdiag
    · have hpair := hminor 2 ![0, 1]
      rw [Matrix.det_fin_two] at hpair
      simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        slackHollowThree, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.of_apply] at hpair
      nlinarith [hpair]
    · have hpair := hminor 2 ![0, 2]
      rw [Matrix.det_fin_two] at hpair
      simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, slackHollowThree, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_fin_const, Matrix.of_apply] at hpair
      nlinarith [hpair]
    · have hpair := hminor 2 ![1, 2]
      rw [Matrix.det_fin_two] at hpair
      simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, slackHollowThree, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_fin_const, Matrix.of_apply] at hpair
      nlinarith [hpair]
    · rw [← det_slackHollowThree]
      exact hpsd.det_nonneg
  · rintro ⟨hdiagFirst, hdiagSecond, hdiagThird, hpairFirst, hpairSecond, hpairThird,
      hdeterminant⟩
    refine posSemidef_three_of_principalMinors
      (slackHollowThree_transpose _ _ _ _ _ _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [slackHollowThree, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
    · exact hdiagFirst
    · exact hdiagSecond
    · exact hdiagThird
    · nlinarith [hpairFirst]
    · nlinarith [hpairSecond]
    · nlinarith [hpairThird]
    · rw [show (!![slackFirst, edgeFirst, edgeSecond; edgeFirst, slackSecond, edgeThird;
          edgeSecond, edgeThird, slackThird] : Matrix (Fin 3) (Fin 3) ℝ)
          = slackHollowThree slackFirst slackSecond slackThird
              edgeFirst edgeSecond edgeThird from rfl,
        det_slackHollowThree]
      exact hdeterminant

/-- The pen's own four-clause form, available once the diagonal is known
nonnegative — which on `Sigma` it always is. -/
theorem posSemidef_slackHollowThree_iff_of_nonneg {slackFirst slackSecond slackThird : ℝ}
    (hdiagFirst : 0 ≤ slackFirst) (hdiagSecond : 0 ≤ slackSecond) (hdiagThird : 0 ≤ slackThird)
    (edgeFirst edgeSecond edgeThird : ℝ) :
    (slackHollowThree slackFirst slackSecond slackThird
        edgeFirst edgeSecond edgeThird).PosSemidef
      ↔ edgeFirst ^ 2 ≤ slackFirst * slackSecond
        ∧ edgeSecond ^ 2 ≤ slackFirst * slackThird
        ∧ edgeThird ^ 2 ≤ slackSecond * slackThird
        ∧ 0 ≤ slackDeterminantThree slackFirst slackSecond slackThird
            edgeFirst edgeSecond edgeThird := by
  rw [posSemidef_slackHollowThree_iff]
  tauto

/-- **THE DIAGONAL CLAUSES ARE NOT REDUNDANT.**  The pen's expanded criterion
lists the three pairwise clauses and the determinant clause and stops.  That
four-clause reading is FALSE: at `tau = (-1, 0, 0)` with all three edges zero all
four clauses hold and the block `diag(-1,0,0)` is not positive semidefinite.

The omission is harmless for Theorem A — on `Gtz.slackSimplex` every coordinate
is nonnegative, which is exactly the missing conjunct, supplied by
`Gtz.posSemidef_slackHollowThree_iff_of_nonneg` — but the criterion as stated for
arbitrary reals needs all seven minors, which is why
`Gtz.posSemidef_slackHollowThree_iff` carries them. -/
theorem exists_slackClauses_without_posSemidef :
    ((0 : ℝ) ^ 2 ≤ (-1 : ℝ) * 0 ∧ (0 : ℝ) ^ 2 ≤ (-1 : ℝ) * 0 ∧ (0 : ℝ) ^ 2 ≤ (0 : ℝ) * 0
        ∧ 0 ≤ slackDeterminantThree (-1) 0 0 0 0 0)
      ∧ ¬ (slackHollowThree (-1) 0 0 0 0 0).PosSemidef := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by simp [slackDeterminantThree]⟩, ?_⟩
  intro hpsd
  have hdiagonal := ((posSemidef_slackHollowThree_iff (-1) 0 0 0 0 0).mp hpsd).1
  norm_num at hdiagonal

/-! ### Monotonicity of the determinant clause

The pen's `dDelta/dtau_c = tau_a tau_b - w_ab` as three exact difference
identities.  Division-free, and equalities rather than estimates, so they also
say by exactly how much the determinant moves. -/

theorem slackDeterminantThree_sub_first (slackFirst raisedFirst slackSecond slackThird
    edgeFirst edgeSecond edgeThird : ℝ) :
    slackDeterminantThree raisedFirst slackSecond slackThird edgeFirst edgeSecond edgeThird
        - slackDeterminantThree slackFirst slackSecond slackThird
            edgeFirst edgeSecond edgeThird
      = (raisedFirst - slackFirst) * (slackSecond * slackThird - edgeThird ^ 2) := by
  simp only [slackDeterminantThree]
  ring

theorem slackDeterminantThree_sub_second (slackFirst slackSecond raisedSecond slackThird
    edgeFirst edgeSecond edgeThird : ℝ) :
    slackDeterminantThree slackFirst raisedSecond slackThird edgeFirst edgeSecond edgeThird
        - slackDeterminantThree slackFirst slackSecond slackThird
            edgeFirst edgeSecond edgeThird
      = (raisedSecond - slackSecond) * (slackFirst * slackThird - edgeSecond ^ 2) := by
  simp only [slackDeterminantThree]
  ring

theorem slackDeterminantThree_sub_third (slackFirst slackSecond slackThird raisedThird
    edgeFirst edgeSecond edgeThird : ℝ) :
    slackDeterminantThree slackFirst slackSecond raisedThird edgeFirst edgeSecond edgeThird
        - slackDeterminantThree slackFirst slackSecond slackThird
            edgeFirst edgeSecond edgeThird
      = (raisedThird - slackThird) * (slackFirst * slackSecond - edgeFirst ^ 2) := by
  simp only [slackDeterminantThree]
  ring

/-- **THE PEN'S MONOTONICITY**, read off the first difference identity: under the
opposite pairwise clause, `Delta` is nondecreasing in each slack. -/
theorem slackDeterminantThree_le_of_le_first {slackFirst raisedFirst slackSecond slackThird
    edgeFirst edgeSecond edgeThird : ℝ} (hraise : slackFirst ≤ raisedFirst)
    (hpair : edgeThird ^ 2 ≤ slackSecond * slackThird) :
    slackDeterminantThree slackFirst slackSecond slackThird edgeFirst edgeSecond edgeThird
      ≤ slackDeterminantThree raisedFirst slackSecond slackThird
          edgeFirst edgeSecond edgeThird := by
  have hdifference := slackDeterminantThree_sub_first slackFirst raisedFirst slackSecond
    slackThird edgeFirst edgeSecond edgeThird
  nlinarith [mul_nonneg (sub_nonneg.mpr hraise) (sub_nonneg.mpr hpair)]

theorem slackDeterminantThree_le_of_le_second {slackFirst slackSecond raisedSecond slackThird
    edgeFirst edgeSecond edgeThird : ℝ} (hraise : slackSecond ≤ raisedSecond)
    (hpair : edgeSecond ^ 2 ≤ slackFirst * slackThird) :
    slackDeterminantThree slackFirst slackSecond slackThird edgeFirst edgeSecond edgeThird
      ≤ slackDeterminantThree slackFirst raisedSecond slackThird
          edgeFirst edgeSecond edgeThird := by
  have hdifference := slackDeterminantThree_sub_second slackFirst slackSecond raisedSecond
    slackThird edgeFirst edgeSecond edgeThird
  nlinarith [mul_nonneg (sub_nonneg.mpr hraise) (sub_nonneg.mpr hpair)]

theorem slackDeterminantThree_le_of_le_third {slackFirst slackSecond slackThird raisedThird
    edgeFirst edgeSecond edgeThird : ℝ} (hraise : slackThird ≤ raisedThird)
    (hpair : edgeFirst ^ 2 ≤ slackFirst * slackSecond) :
    slackDeterminantThree slackFirst slackSecond slackThird edgeFirst edgeSecond edgeThird
      ≤ slackDeterminantThree slackFirst slackSecond raisedThird
          edgeFirst edgeSecond edgeThird := by
  have hdifference := slackDeterminantThree_sub_third slackFirst slackSecond slackThird
    raisedThird edgeFirst edgeSecond edgeThird
  nlinarith [mul_nonneg (sub_nonneg.mpr hraise) (sub_nonneg.mpr hpair)]

/-! ### Upward closure and convexity of the block itself -/

/-- **UPWARD CLOSURE, at matrix level.**  Raising any slack preserves positive
semidefiniteness, because the increment is a nonnegative diagonal.  No pairwise
clause is needed: the pen derives the monotonicity from `Delta`, but the matrix
statement is both stronger and cheaper. -/
theorem posSemidef_slackHollowThree_of_le {slackFirst slackSecond slackThird
    raisedFirst raisedSecond raisedThird edgeFirst edgeSecond edgeThird : ℝ}
    (hpsd : (slackHollowThree slackFirst slackSecond slackThird
      edgeFirst edgeSecond edgeThird).PosSemidef)
    (hfirst : slackFirst ≤ raisedFirst) (hsecond : slackSecond ≤ raisedSecond)
    (hthird : slackThird ≤ raisedThird) :
    (slackHollowThree raisedFirst raisedSecond raisedThird
      edgeFirst edgeSecond edgeThird).PosSemidef := by
  have hgapFirst : (0 : ℝ) ≤ raisedFirst - slackFirst := by linarith
  have hgapSecond : (0 : ℝ) ≤ raisedSecond - slackSecond := by linarith
  have hgapThird : (0 : ℝ) ≤ raisedThird - slackThird := by linarith
  have hincrement : (slackHollowThree (raisedFirst - slackFirst) (raisedSecond - slackSecond)
      (raisedThird - slackThird) 0 0 0).PosSemidef := by
    refine (posSemidef_slackHollowThree_iff _ _ _ _ _ _).mpr
      ⟨hgapFirst, hgapSecond, hgapThird, ?_, ?_, ?_, ?_⟩
    · nlinarith [mul_nonneg hgapFirst hgapSecond]
    · nlinarith [mul_nonneg hgapFirst hgapThird]
    · nlinarith [mul_nonneg hgapSecond hgapThird]
    · simp only [slackDeterminantThree]
      nlinarith [mul_nonneg (mul_nonneg hgapFirst hgapSecond) hgapThird]
  have hshape : slackHollowThree raisedFirst raisedSecond raisedThird
        edgeFirst edgeSecond edgeThird
      = slackHollowThree slackFirst slackSecond slackThird edgeFirst edgeSecond edgeThird
        + slackHollowThree (raisedFirst - slackFirst) (raisedSecond - slackSecond)
            (raisedThird - slackThird) 0 0 0 := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, slackHollowThree, Matrix.add_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.of_apply] <;>
      ring
  rw [hshape]
  exact hpsd.add hincrement

/-- **THE FLOOR GATE.**  A constant floor that works at the triple transports to
every slack vector above it.  This is the shape every band argument uses: the
U6-style theorems produce a scalar shift, and this turns it into a region of the
weight polytope. -/
theorem posSemidef_slackHollowThree_of_floor {level slackFirst slackSecond slackThird
    edgeFirst edgeSecond edgeThird : ℝ}
    (hfloor : (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowMatrixThree edgeFirst edgeSecond edgeThird).PosSemidef)
    (hfirst : level ≤ slackFirst) (hsecond : level ≤ slackSecond) (hthird : level ≤ slackThird) :
    (slackHollowThree slackFirst slackSecond slackThird
      edgeFirst edgeSecond edgeThird).PosSemidef := by
  refine posSemidef_slackHollowThree_of_le (slackFirst := level) (slackSecond := level)
    (slackThird := level) ?_ hfirst hsecond hthird
  rwa [slackHollowThree_self]

/-- **CONVEXITY, as a matrix identity.**  Because the edges do NOT move with the
weights, the block is affine in the slack vector, and a convex combination of
slacks gives the same convex combination of blocks.  This is the whole reason
`K_T` is convex; no `ConvexCone` instance for `Matrix.PosSemidef` is needed
(Mathlib has none). -/
theorem slackHollowThree_convexCombination {leftShare rightShare : ℝ}
    (hshares : leftShare + rightShare = 1)
    (leftFirst leftSecond leftThird rightFirst rightSecond rightThird
      edgeFirst edgeSecond edgeThird : ℝ) :
    slackHollowThree (leftShare * leftFirst + rightShare * rightFirst)
        (leftShare * leftSecond + rightShare * rightSecond)
        (leftShare * leftThird + rightShare * rightThird) edgeFirst edgeSecond edgeThird
      = leftShare • slackHollowThree leftFirst leftSecond leftThird
            edgeFirst edgeSecond edgeThird
        + rightShare • slackHollowThree rightFirst rightSecond rightThird
            edgeFirst edgeSecond edgeThird := by
  have hcomplement : rightShare = 1 - leftShare := by linarith
  subst hcomplement
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, slackHollowThree, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply] <;>
    ring

/-! ## 2. The weight slack of an atom -/

/-- **THE WEIGHT SLACK** `tau_c = 1 - 1/ell_c` of an atom — the pen's `tau`.  The
project bans identifiers of three characters or fewer, and `tau` is in any case
already spoken for twice in this repository (an excess threshold in
`Gtz.HeavinessProfileAt`, a margin scalar in `Gtz/Corner/CoveringMargin.lean`), so
the name says what the quantity is: the fraction of the atom's own capacity that
its weight leaves unspent. -/
noncomputable def weightSlack (D : WeightedDesign m k) (atomIndex : Fin m) : ℝ :=
  1 - (leverageOf (D.atom atomIndex))⁻¹

/-- A nondegenerate atom has slack strictly below one. -/
theorem weightSlack_lt_one (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) : weightSlack D atomIndex < 1 := by
  rw [weightSlack]
  have hinverse : 0 < (leverageOf (D.atom atomIndex))⁻¹ := inv_pos.mpr hpositive
  linarith

/-- **HEAVINESS IS POSITIVE SLACK.**  At a nondegenerate atom `0 < tau_c` and
`1 < ell_c` are the same statement, so `Gtz.AllHeavy` is exactly positivity of the
slack.  Nondegeneracy is genuinely needed for the forward direction: a zero atom
has leverage `0` and slack `1`, so the right-hand side fails while the left-hand
side holds. -/
theorem weightSlack_pos_iff_one_lt_leverage (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    0 < weightSlack D atomIndex ↔ 1 < leverageOf (D.atom atomIndex) := by
  rw [weightSlack, sub_pos]
  constructor
  · intro hslack
    by_contra hcontra
    rw [not_lt] at hcontra
    have hbound : (1 : ℝ) ≤ (leverageOf (D.atom atomIndex))⁻¹ :=
      one_le_inv_iff₀.mpr ⟨hpositive, hcontra⟩
    linarith
  · intro hheavy
    exact (inv_lt_one_iff₀).mpr (Or.inr hheavy)

theorem weightSlack_pos (D : WeightedDesign m k) (hheavy : AllHeavy D) (atomIndex : Fin m) :
    0 < weightSlack D atomIndex :=
  (weightSlack_pos_iff_one_lt_leverage D
    (lt_trans zero_lt_one (hheavy atomIndex))).mpr (hheavy atomIndex)

/-- **THE INVERSE CHANGE OF VARIABLES**: `ell_c = 1/(1 - tau_c)`, unconditionally.
Even a degenerate atom obeys it, `0` being its own double inverse. -/
theorem inv_one_sub_weightSlack (D : WeightedDesign m k) (atomIndex : Fin m) :
    (1 - weightSlack D atomIndex)⁻¹ = leverageOf (D.atom atomIndex) := by
  rw [weightSlack, sub_sub_cancel, inv_inv]

/-- **THE THRESHOLD DICTIONARY, from below.**  A slack floor is a leverage floor:
`level <= tau_c` iff `1/(1 - level) <= ell_c`.  Every band statement in slack
coordinates therefore reads directly as a leverage statement. -/
theorem le_weightSlack_iff_le_leverage (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) {level : ℝ} (hlevel : level < 1) :
    level ≤ weightSlack D atomIndex ↔ (1 - level)⁻¹ ≤ leverageOf (D.atom atomIndex) := by
  have hgap : (0 : ℝ) < 1 - level := by linarith
  rw [weightSlack, le_sub_comm, inv_le_comm₀ hpositive hgap]

/-- **THE THRESHOLD DICTIONARY, from above.**  A slack ceiling is a leverage
ceiling: `tau_c <= level` iff `ell_c <= 1/(1 - level)`.  At `level = 1/3` this
reads "cheap means leverage at most `3/2`". -/
theorem weightSlack_le_iff_leverage_le (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) {level : ℝ} (hlevel : level < 1) :
    weightSlack D atomIndex ≤ level ↔ leverageOf (D.atom atomIndex) ≤ (1 - level)⁻¹ := by
  have hgap : (0 : ℝ) < 1 - level := by linarith
  rw [weightSlack, sub_le_comm, le_inv_comm₀ hgap hpositive]

/-- The pen's calibration in leverage: slack `2/3` is leverage `3`, the equal-share
value; slack `1/3` is leverage `3/2`. -/
theorem two_thirds_le_weightSlack_iff_three_le_leverage (D : WeightedDesign m k)
    {atomIndex : Fin m} (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    (2 : ℝ) / 3 ≤ weightSlack D atomIndex ↔ (3 : ℝ) ≤ leverageOf (D.atom atomIndex) := by
  rw [le_weightSlack_iff_le_leverage D hpositive (by norm_num : (2 : ℝ) / 3 < 1)]
  norm_num

theorem weightSlack_le_third_iff_leverage_le (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    weightSlack D atomIndex ≤ 1 / 3 ↔ leverageOf (D.atom atomIndex) ≤ 3 / 2 := by
  rw [weightSlack_le_iff_leverage_le D hpositive (by norm_num : (1 : ℝ) / 3 < 1)]
  norm_num

/-- **THE PEN'S FORMULA.**  At an atom of positive share `s_c` the slack is
`1 - t_c/s_c`.  At the V6 stratum's share `1/2` this reads `tau_c = 1 - 2 t_c`. -/
theorem weightSlack_eq_one_sub_weight_div_atomShare (D : WeightedDesign m k)
    {atomIndex : Fin m} (hshare : 0 < atomShare D atomIndex) :
    weightSlack D atomIndex = 1 - D.weight atomIndex / atomShare D atomIndex := by
  have hleverage : 0 < leverageOf (D.atom atomIndex) := by
    by_contra hcontra
    rw [not_lt] at hcontra
    have hzero : leverageOf (D.atom atomIndex) = 0 :=
      le_antisymm hcontra (leverageOf_nonneg _)
    rw [atomShare, hzero, mul_zero] at hshare
    exact absurd hshare (lt_irrefl 0)
  have hweightNe : D.weight atomIndex ≠ 0 := (D.weight_pos atomIndex).ne'
  have hleverageNe : leverageOf (D.atom atomIndex) ≠ 0 := hleverage.ne'
  rw [weightSlack, atomShare]
  field_simp

/-! ### The normalisation `sum tau = 4` -/

/-- **THE WEIGHT NORMALISATION IN SLACK COORDINATES.**  On a design of uniform
share `k/m` the slacks sum to `m - m/k`.  This is `sum_c t_c = 1` rewritten: at
uniform share, `1/ell_c = (m/k) t_c`.  At `(6,3)` the total is `4`, the pen's
`Sigma`. -/
theorem sum_weightSlack_of_uniformShare (D : WeightedDesign m k) (hrank : 0 < k)
    (hshare : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ)) :
    ∑ atomIndex, weightSlack D atomIndex = (m : ℝ) - (m : ℝ) / (k : ℝ) := by
  have hsizePositive : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hzero | hpositive
    · subst hzero
      have hsum := D.weight_sum_one
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
      exact absurd hsum (by norm_num)
    · exact hpositive
  have hsizeReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hsizePositive
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hshareReal : (0 : ℝ) < (k : ℝ) / (m : ℝ) := div_pos hrankReal hsizeReal
  have hterm : ∀ atomIndex : Fin m,
      weightSlack D atomIndex = 1 - (m : ℝ) / (k : ℝ) * D.weight atomIndex := by
    intro atomIndex
    have hpositive : 0 < atomShare D atomIndex := by rw [hshare atomIndex]; exact hshareReal
    rw [weightSlack_eq_one_sub_weight_div_atomShare D hpositive, hshare atomIndex]
    field_simp
  rw [Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex, Finset.sum_sub_distrib,
    ← Finset.mul_sum, D.weight_sum_one, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **`sum tau = 4` at `(6,3)`.** -/
theorem sum_weightSlack_eq_four (D : WeightedDesign 6 3)
    (hshare : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    ∑ atomIndex, weightSlack D atomIndex = 4 := by
  have hnormalised := sum_weightSlack_of_uniformShare D (by norm_num) (by
    intro atomIndex
    rw [hshare atomIndex]
    norm_num)
  rw [hnormalised]
  norm_num

/-- Every equal-share design sits at the constant slack `2/3` — the U6 point. -/
theorem weightSlack_eq_two_thirds_of_isEqualShare {D : WeightedDesign m 3}
    (hequal : IsEqualShare D) (atomIndex : Fin m) : weightSlack D atomIndex = 2 / 3 := by
  rw [weightSlack, hequal.leverage_eq atomIndex]
  norm_num

/-! ## 3. THE CRITERION (V1)

The congruence by `diag(sqrt ell)`, applied to the shipped gap matrix. -/

/-- The congruence `diag(sqrt(ell_a), sqrt(ell_b), sqrt(ell_c))` of V1.  It divides
by the LEVERAGES, unlike `Gtz.excessSqrtDiagonal`, which divides by the excesses
and therefore blows up as an atom approaches leverage one. -/
noncomputable def leverageSqrtDiagonal (D : WeightedDesign m 3)
    (first second third : Fin m) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![Real.sqrt (leverageOf (D.atom first)), Real.sqrt (leverageOf (D.atom second)),
    Real.sqrt (leverageOf (D.atom third))]

theorem leverageSqrtDiagonal_transpose (D : WeightedDesign m 3) (first second third : Fin m) :
    (leverageSqrtDiagonal D first second third)ᵀ = leverageSqrtDiagonal D first second third :=
  Matrix.diagonal_transpose _

theorem isUnit_det_leverageSqrtDiagonal (D : WeightedDesign m 3) {first second third : Fin m}
    (hfirst : 0 < leverageOf (D.atom first)) (hsecond : 0 < leverageOf (D.atom second))
    (hthird : 0 < leverageOf (D.atom third)) :
    IsUnit (leverageSqrtDiagonal D first second third).det := by
  rw [leverageSqrtDiagonal, Matrix.det_diagonal]
  refine isUnit_iff_ne_zero.mpr ?_
  rw [Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  positivity

/-- **THE V1 CONGRUENCE.**  The shipped gap matrix of a triple — heavy excesses on
the diagonal, raw pairings off it — is the slack-shifted hollow block conjugated
by the square roots of the leverages.  Both sides are stated in the design's own
scalars, and the only hypothesis is that the three leverages are positive. -/
theorem tripleGapMatrix_eq_congr_slackHollowThree (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirst : 0 < leverageOf (D.atom first))
    (hsecond : 0 < leverageOf (D.atom second)) (hthird : 0 < leverageOf (D.atom third)) :
    tripleGapMatrix D first second third
      = (leverageSqrtDiagonal D first second third)ᵀ
        * slackHollowThree (weightSlack D first) (weightSlack D second) (weightSlack D third)
            (directionGram D first second) (directionGram D first third)
            (directionGram D second third)
        * leverageSqrtDiagonal D first second third := by
  have hroot : ∀ atomIndex : Fin m, 0 < leverageOf (D.atom atomIndex) →
      Real.sqrt (leverageOf (D.atom atomIndex)) * Real.sqrt (leverageOf (D.atom atomIndex))
        = leverageOf (D.atom atomIndex) :=
    fun atomIndex hpositive => Real.mul_self_sqrt hpositive.le
  have hdiagonalEntry : ∀ atomIndex : Fin m, 0 < leverageOf (D.atom atomIndex) →
      Real.sqrt (leverageOf (D.atom atomIndex)) * weightSlack D atomIndex
          * Real.sqrt (leverageOf (D.atom atomIndex))
        = heavyExcess D atomIndex := by
    intro atomIndex hpositive
    rw [show Real.sqrt (leverageOf (D.atom atomIndex)) * weightSlack D atomIndex
        * Real.sqrt (leverageOf (D.atom atomIndex))
        = (Real.sqrt (leverageOf (D.atom atomIndex))
            * Real.sqrt (leverageOf (D.atom atomIndex))) * weightSlack D atomIndex from by ring,
      hroot atomIndex hpositive, weightSlack, heavyExcess, mul_sub, mul_one,
      mul_inv_cancel₀ hpositive.ne']
  have hoffEntry : ∀ leftIndex rightIndex : Fin m, 0 < leverageOf (D.atom leftIndex) →
      0 < leverageOf (D.atom rightIndex) →
      Real.sqrt (leverageOf (D.atom leftIndex)) * directionGram D leftIndex rightIndex
          * Real.sqrt (leverageOf (D.atom rightIndex))
        = atomPairing D leftIndex rightIndex := by
    intro leftIndex rightIndex hleft hright
    rw [directionGram_eq_scaled_atomPairing D leftIndex rightIndex, atomPairing]
    have hleftRoot : Real.sqrt (leverageOf (D.atom leftIndex)) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr hleft
    have hrightRoot : Real.sqrt (leverageOf (D.atom rightIndex)) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr hright
    field_simp
  rw [leverageSqrtDiagonal_transpose]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, leverageSqrtDiagonal,
      Matrix.mul_diagonal, Matrix.diagonal_mul, tripleGapMatrix, slackHollowThree,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply] <;>
    first
      | linear_combination -(hdiagonalEntry first hfirst)
      | linear_combination -(hdiagonalEntry second hsecond)
      | linear_combination -(hdiagonalEntry third hthird)
      | linear_combination -(hoffEntry first second hfirst hsecond)
      | linear_combination -(hoffEntry first third hfirst hthird)
      | linear_combination -(hoffEntry second third hsecond hthird)

/-- **THE V1 CRITERION.**  A triple of DISTINCT atoms of a rank-three design with
three positive leverages dominates exactly when

  `diag(tau_a, tau_b, tau_c) + M[T] ⪰ 0`.

Nothing else is assumed: no heaviness, no uniform share, no uniform leverage, no
size condition, and no involution.  This is the free-weight repair of
`Gtz.dominates_triple_iff_posSemidef_hollowShift`, whose scalar `2/3` shift is the
special case `ell ≡ 3`. -/
theorem dominates_triple_iff_posSemidef_slackHollowThree (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirst : 0 < leverageOf (D.atom first))
    (hsecond : 0 < leverageOf (D.atom second)) (hthird : 0 < leverageOf (D.atom third))
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    Dominates D {first, second, third}
      ↔ (slackHollowThree (weightSlack D first) (weightSlack D second) (weightSlack D third)
          (directionGram D first second) (directionGram D first third)
          (directionGram D second third)).PosSemidef := by
  rw [dominates_triple_iff_posSemidef_tripleGapMatrix D hfirstSecond hfirstThird hsecondThird,
    tripleGapMatrix_eq_congr_slackHollowThree D hfirst hsecond hthird]
  exact (posSemidef_congr_right (slackHollowThree_transpose _ _ _ _ _ _)
    (isUnit_det_leverageSqrtDiagonal D hfirst hsecond hthird)).symm

/-- **THE V1 CRITERION, EXPANDED.**  Domination of a triple is seven scalar
inequalities: nonnegative slack at each atom (equivalently `1 <= ell_c`), the
three pairwise clauses against `Gtz.edgeWeight`, and the determinant clause.
Everything is polynomial in the three slacks and the three cosines, so a covering
argument never has to touch a matrix again. -/
theorem dominates_triple_iff_slackClauses (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirst : 0 < leverageOf (D.atom first))
    (hsecond : 0 < leverageOf (D.atom second)) (hthird : 0 < leverageOf (D.atom third))
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    Dominates D {first, second, third}
      ↔ 0 ≤ weightSlack D first ∧ 0 ≤ weightSlack D second ∧ 0 ≤ weightSlack D third
        ∧ edgeWeight D first second ≤ weightSlack D first * weightSlack D second
        ∧ edgeWeight D first third ≤ weightSlack D first * weightSlack D third
        ∧ edgeWeight D second third ≤ weightSlack D second * weightSlack D third
        ∧ 0 ≤ slackDeterminantThree (weightSlack D first) (weightSlack D second)
            (weightSlack D third) (directionGram D first second) (directionGram D first third)
            (directionGram D second third) := by
  rw [dominates_triple_iff_posSemidef_slackHollowThree D hfirst hsecond hthird hfirstSecond
    hfirstThird hsecondThird, posSemidef_slackHollowThree_iff, edgeWeight, edgeWeight, edgeWeight]

/-- **THE PAIRWISE CLAUSE IS NECESSARY.**  A triple carrying an edge heavier than
the product of its two endpoint slacks cannot dominate — the cheapest exclusion
tool the criterion supplies, and the one that kills a triple without touching the
determinant. -/
theorem not_dominates_of_lt_edgeWeight (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirst : 0 < leverageOf (D.atom first))
    (hsecond : 0 < leverageOf (D.atom second)) (hthird : 0 < leverageOf (D.atom third))
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hheavyEdge : weightSlack D first * weightSlack D second < edgeWeight D first second) :
    ¬ Dominates D {first, second, third} := by
  intro hdominates
  have hclauses := (dominates_triple_iff_slackClauses D hfirst hsecond hthird hfirstSecond
    hfirstThird hsecondThird).mp hdominates
  linarith [hclauses.2.2.2.1]

/-- **THE FLOOR GATE ON A DESIGN.**  If the triple's hollow block admits the
scalar floor `level` and all three atoms have slack at least `level`, the triple
dominates.  This is the transport that turns every U6-style scalar theorem into a
region of the weight polytope. -/
theorem dominates_triple_of_floor (D : WeightedDesign m 3) {level : ℝ}
    {first second third : Fin m} (hfirst : 0 < leverageOf (D.atom first))
    (hsecond : 0 < leverageOf (D.atom second)) (hthird : 0 < leverageOf (D.atom third))
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hfloor : (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowMatrixThree (directionGram D first second) (directionGram D first third)
        (directionGram D second third)).PosSemidef)
    (hslackFirst : level ≤ weightSlack D first) (hslackSecond : level ≤ weightSlack D second)
    (hslackThird : level ≤ weightSlack D third) :
    Dominates D {first, second, third} :=
  (dominates_triple_iff_posSemidef_slackHollowThree D hfirst hsecond hthird hfirstSecond
    hfirstThird hsecondThird).mpr
    (posSemidef_slackHollowThree_of_floor hfloor hslackFirst hslackSecond hslackThird)

/-- **THREE-LOCALITY ON THE DESIGN SIDE.**  Two rank-three designs which agree on
a triple's three slacks and three cosines agree on whether that triple dominates.
The weights of the other atoms, and their directions, are invisible. -/
theorem dominates_triple_congr {sizeLeft sizeRight : ℕ} (leftDesign : WeightedDesign sizeLeft 3)
    (rightDesign : WeightedDesign sizeRight 3)
    {leftFirst leftSecond leftThird : Fin sizeLeft}
    {rightFirst rightSecond rightThird : Fin sizeRight}
    (hleftFirst : 0 < leverageOf (leftDesign.atom leftFirst))
    (hleftSecond : 0 < leverageOf (leftDesign.atom leftSecond))
    (hleftThird : 0 < leverageOf (leftDesign.atom leftThird))
    (hrightFirst : 0 < leverageOf (rightDesign.atom rightFirst))
    (hrightSecond : 0 < leverageOf (rightDesign.atom rightSecond))
    (hrightThird : 0 < leverageOf (rightDesign.atom rightThird))
    (hleftDistinctOne : leftFirst ≠ leftSecond) (hleftDistinctTwo : leftFirst ≠ leftThird)
    (hleftDistinctThree : leftSecond ≠ leftThird)
    (hrightDistinctOne : rightFirst ≠ rightSecond) (hrightDistinctTwo : rightFirst ≠ rightThird)
    (hrightDistinctThree : rightSecond ≠ rightThird)
    (hslackFirst : weightSlack leftDesign leftFirst = weightSlack rightDesign rightFirst)
    (hslackSecond : weightSlack leftDesign leftSecond = weightSlack rightDesign rightSecond)
    (hslackThird : weightSlack leftDesign leftThird = weightSlack rightDesign rightThird)
    (hedgeFirst : directionGram leftDesign leftFirst leftSecond
      = directionGram rightDesign rightFirst rightSecond)
    (hedgeSecond : directionGram leftDesign leftFirst leftThird
      = directionGram rightDesign rightFirst rightThird)
    (hedgeThird : directionGram leftDesign leftSecond leftThird
      = directionGram rightDesign rightSecond rightThird) :
    Dominates leftDesign {leftFirst, leftSecond, leftThird}
      ↔ Dominates rightDesign {rightFirst, rightSecond, rightThird} := by
  rw [dominates_triple_iff_posSemidef_slackHollowThree leftDesign hleftFirst hleftSecond
      hleftThird hleftDistinctOne hleftDistinctTwo hleftDistinctThree,
    dominates_triple_iff_posSemidef_slackHollowThree rightDesign hrightFirst hrightSecond
      hrightThird hrightDistinctOne hrightDistinctTwo hrightDistinctThree,
    hslackFirst, hslackSecond, hslackThird, hedgeFirst, hedgeSecond, hedgeThird]

/-! ## 4. Theorem A, part one: the cell `K_T` -/

/-- **THE DOMINATION CELL** `K_T` of a triple of indices, as a subset of slack
space.  The involution supplies the three edges; the slack vector is the free
point. -/
def tripleSlackCell (invol : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) : Set (Fin size → ℝ) :=
  {slack | (slackHollowThree (slack first) (slack second) (slack third)
    (invol first second) (invol first third) (invol second third)).PosSemidef}

theorem mem_tripleSlackCell_iff {invol : Matrix (Fin size) (Fin size) ℝ}
    {first second third : Fin size} {slack : Fin size → ℝ} :
    slack ∈ tripleSlackCell invol first second third
      ↔ (slackHollowThree (slack first) (slack second) (slack third)
          (invol first second) (invol first third) (invol second third)).PosSemidef :=
  Iff.rfl

/-- **`K_T` IS 3-LOCAL.**  Membership reads exactly the three coordinates of the
triple; two slack vectors that agree there are indistinguishable to the cell. -/
theorem tripleSlackCell_congr {invol : Matrix (Fin size) (Fin size) ℝ}
    {first second third : Fin size} {leftSlack rightSlack : Fin size → ℝ}
    (hfirst : leftSlack first = rightSlack first)
    (hsecond : leftSlack second = rightSlack second)
    (hthird : leftSlack third = rightSlack third) :
    leftSlack ∈ tripleSlackCell invol first second third
      ↔ rightSlack ∈ tripleSlackCell invol first second third := by
  rw [mem_tripleSlackCell_iff, mem_tripleSlackCell_iff, hfirst, hsecond, hthird]

/-- **`K_T` IS UPWARD CLOSED.**  Raising the weights' slack — i.e. lightening the
atoms — never destroys domination. -/
theorem mem_tripleSlackCell_of_le {invol : Matrix (Fin size) (Fin size) ℝ}
    {first second third : Fin size} {slack raisedSlack : Fin size → ℝ}
    (hmember : slack ∈ tripleSlackCell invol first second third)
    (hfirst : slack first ≤ raisedSlack first) (hsecond : slack second ≤ raisedSlack second)
    (hthird : slack third ≤ raisedSlack third) :
    raisedSlack ∈ tripleSlackCell invol first second third :=
  posSemidef_slackHollowThree_of_le hmember hfirst hsecond hthird

/-- **`K_T` IS CONVEX.**  The block is affine in the slack vector because the
edges do not move with the weights, so the cell is the preimage of the positive
semidefinite cone under an affine map — proved here directly from
`Matrix.PosSemidef.add` and `Matrix.PosSemidef.smul`, since Mathlib carries no
convexity statement about `Matrix.PosSemidef` at all. -/
theorem convex_tripleSlackCell (invol : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    Convex ℝ (tripleSlackCell invol first second third) := by
  intro leftSlack hleft rightSlack hright leftShare rightShare hleftShare hrightShare hshares
  rw [mem_tripleSlackCell_iff] at hleft hright ⊢
  have hcombination : (leftShare • leftSlack + rightShare • rightSlack) first
      = leftShare * leftSlack first + rightShare * rightSlack first := rfl
  have hcombinationSecond : (leftShare • leftSlack + rightShare • rightSlack) second
      = leftShare * leftSlack second + rightShare * rightSlack second := rfl
  have hcombinationThird : (leftShare • leftSlack + rightShare • rightSlack) third
      = leftShare * leftSlack third + rightShare * rightSlack third := rfl
  rw [hcombination, hcombinationSecond, hcombinationThird,
    slackHollowThree_convexCombination hshares]
  exact (hleft.smul hleftShare).add (hright.smul hrightShare)

/-- **EVERY CELL IS NONEMPTY**, and it contains the top corner of the box: at
slack `1` the block is `1 + M[T]`, positive semidefinite by the norm cap.  With
convexity and upward closure this says each `K_T` is a nonempty convex body
reaching the top of `[0,1]^6`; the covering question is exactly how far down each
one reaches. -/
theorem constantOne_mem_tripleSlackCell {invol : Matrix (Fin size) (Fin size) ℝ}
    (hinvol : IsHollowInvolution invol) {first second third : Fin size}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (fun _ => (1 : ℝ)) ∈ tripleSlackCell invol first second third := by
  have hpick : Function.Injective ![first, second, third] :=
    injective_three_of_ne hfirstSecond hfirstThird hsecondThird
  have hlower := hinvol.posSemidef_one_add_submatrix ![first, second, third] hpick
  rw [hinvol.submatrix_three_eq_hollowMatrixThree first second third] at hlower
  rw [mem_tripleSlackCell_iff, slackHollowThree_self]
  simpa using hlower

/-- **`K_T` IS CLOSED.**  It is the intersection, over probe vectors, of the
closed half-spaces cut out by the quadratic form, each of which is affine — hence
continuous — in the slack vector. -/
theorem isClosed_tripleSlackCell (invol : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    IsClosed (tripleSlackCell invol first second third) := by
  have hshape : tripleSlackCell invol first second third
      = ⋂ probe : Fin 3 → ℝ,
        {slack : Fin size → ℝ | 0 ≤ slack first * probe 0 ^ 2 + slack second * probe 1 ^ 2
          + slack third * probe 2 ^ 2
          + 2 * invol first second * probe 0 * probe 1
          + 2 * invol first third * probe 0 * probe 2
          + 2 * invol second third * probe 1 * probe 2} := by
    ext slack
    rw [mem_tripleSlackCell_iff, Set.mem_iInter,
      posSemidef_iff_quadForm_nonneg _ (slackHollowThree_transpose _ _ _ _ _ _)]
    refine forall_congr' fun probe => ?_
    rw [Set.mem_setOf_eq]
    have hform : probe ⬝ᵥ (slackHollowThree (slack first) (slack second) (slack third)
        (invol first second) (invol first third) (invol second third) *ᵥ probe)
        = slack first * probe 0 ^ 2 + slack second * probe 1 ^ 2 + slack third * probe 2 ^ 2
          + 2 * invol first second * probe 0 * probe 1
          + 2 * invol first third * probe 0 * probe 2
          + 2 * invol second third * probe 1 * probe 2 := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, slackHollowThree,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.of_apply]
      ring
    rw [hform]
  rw [hshape]
  refine isClosed_iInter fun probe => ?_
  exact isClosed_le continuous_const (by fun_prop)

/-! ## 5. Theorem A, part two: the polytope and the covering -/

/-- **THE SLACK POLYTOPE** `Sigma = {tau in [0,1]^6 : sum tau = 4}` — the pen's
`Sigma`, the hypersimplex the twenty cells must cover. -/
def slackSimplex : Set (Fin 6 → ℝ) :=
  {slack | (∀ index, slack index ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ index, slack index = 4}

/-- **THE REALISED PART OF THE POLYTOPE.**  The corners `tau_c = 0` (leverage one)
and `tau_c = 1` (an atom of infinite leverage, i.e. a deleted atom) are limits, not
members: a genuine all-heavy design lands strictly inside.  This is the region the
covering equivalence is stated over. -/
def heavySlackSimplex : Set (Fin 6 → ℝ) :=
  {slack | (∀ index, 0 < slack index ∧ slack index < 1) ∧ ∑ index, slack index = 4}

theorem heavySlackSimplex_subset_slackSimplex : heavySlackSimplex ⊆ slackSimplex := by
  rintro slack ⟨hbounds, hsum⟩
  exact ⟨fun index => ⟨(hbounds index).1.le, (hbounds index).2.le⟩, hsum⟩

theorem convex_slackSimplex : Convex ℝ slackSimplex := by
  rintro leftSlack ⟨hleftBounds, hleftSum⟩ rightSlack ⟨hrightBounds, hrightSum⟩
    leftShare rightShare hleftShare hrightShare hshares
  refine ⟨fun index => ⟨?_, ?_⟩, ?_⟩
  · have hleft := (hleftBounds index).1
    have hright := (hrightBounds index).1
    have hvalue : (leftShare • leftSlack + rightShare • rightSlack) index
        = leftShare * leftSlack index + rightShare * rightSlack index := rfl
    rw [hvalue]
    positivity
  · have hleft := (hleftBounds index).2
    have hright := (hrightBounds index).2
    have hvalue : (leftShare • leftSlack + rightShare • rightSlack) index
        = leftShare * leftSlack index + rightShare * rightSlack index := rfl
    rw [hvalue]
    nlinarith [hleftShare, hrightShare]
  · have hvalue : ∀ index : Fin 6, (leftShare • leftSlack + rightShare • rightSlack) index
        = leftShare * leftSlack index + rightShare * rightSlack index := fun _ => rfl
    rw [Finset.sum_congr rfl fun index _ => hvalue index, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hleftSum, hrightSum]
    linarith

/-- **`Sigma` IS COMPACT** — a closed box intersected with a hyperplane.  Together
with `Gtz.isClosed_tripleSlackCell` this is what a finite-subcover or
minimum-attained argument over the polytope needs. -/
theorem isCompact_slackSimplex : IsCompact slackSimplex := by
  have hshape : slackSimplex = (Set.univ.pi fun _ : Fin 6 => Set.Icc (0 : ℝ) 1)
      ∩ {slack : Fin 6 → ℝ | ∑ index, slack index = 4} := by
    ext slack
    simp only [slackSimplex, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_univ_pi]
  rw [hshape]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
    (isClosed_eq (by fun_prop) continuous_const)

/-- The constant vector `2/3` — the U6 point — lies in `Sigma`. -/
theorem constantTwoThirds_mem_slackSimplex :
    (fun _ : Fin 6 => (2 : ℝ) / 3) ∈ slackSimplex := by
  refine ⟨fun _ => ⟨by norm_num, by norm_num⟩, ?_⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

theorem constantTwoThirds_mem_heavySlackSimplex :
    (fun _ : Fin 6 => (2 : ℝ) / 3) ∈ heavySlackSimplex := by
  refine ⟨fun _ => ⟨by norm_num, by norm_num⟩, ?_⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **THE COVERING PROPERTY.**  The twenty domination cells of an involution on
`Fin 6` cover a region of slack space.  The pen's Theorem A is this predicate at
`region = slackSimplex`. -/
def CoversSlackRegion (invol : Matrix (Fin 6) (Fin 6) ℝ) (region : Set (Fin 6 → ℝ)) : Prop :=
  ∀ slack ∈ region, ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third
    ∧ second ≠ third ∧ slack ∈ tripleSlackCell invol first second third

theorem coversSlackRegion_mono {invol : Matrix (Fin 6) (Fin 6) ℝ}
    {largerRegion smallerRegion : Set (Fin 6 → ℝ)} (hsubset : smallerRegion ⊆ largerRegion)
    (hcovers : CoversSlackRegion invol largerRegion) :
    CoversSlackRegion invol smallerRegion :=
  fun slack hmember => hcovers slack (hsubset hmember)

/-- **THE COVERING, AS A COVERING.**  The predicate is literally the statement
that `Sigma` is contained in the union of the cells — the form in which the
question "do twenty convex upward-closed sets cover a hypersimplex?" is asked. -/
theorem coversSlackRegion_iff_subset_iUnion (invol : Matrix (Fin 6) (Fin 6) ℝ)
    (region : Set (Fin 6 → ℝ)) :
    CoversSlackRegion invol region
      ↔ region ⊆ ⋃ first : Fin 6, ⋃ second : Fin 6, ⋃ third : Fin 6,
          ⋃ _ : first ≠ second, ⋃ _ : first ≠ third, ⋃ _ : second ≠ third,
            tripleSlackCell invol first second third := by
  constructor
  · intro hcovers slack hmember
    obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcell⟩ :=
      hcovers slack hmember
    simp only [Set.mem_iUnion]
    exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcell⟩
  · intro hsubset slack hmember
    have hunion := hsubset hmember
    simp only [Set.mem_iUnion] at hunion
    obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcell⟩ := hunion
    exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcell⟩

/-! ## 6. Unit-norm tight frames of six directions in `R^3` -/

/-- **A UNIT-NORM TIGHT FRAME OF SIX DIRECTIONS IN `R^3`**: six unit rows with
`frame^T frame = 2 . 1`.  This is exactly the geometry of the pen's V6 object with
the weights stripped off, and it is the free parameter of the covering
equivalence. -/
structure IsUnitTightFrameSix (frame : Matrix (Fin 6) (Fin 3) ℝ) : Prop where
  /-- Every row is a unit vector. -/
  unit : ∀ index, leverageOf (frame index) = 1
  /-- The rows resolve the identity at level two. -/
  tight : frameᵀ * frame = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)

/-- The frame's correlation matrix `M = frame frame^T - 1`. -/
noncomputable def frameCorrelationInvolution (frame : Matrix (Fin 6) (Fin 3) ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  frame * frameᵀ - 1

theorem frameCorrelationInvolution_apply_of_ne (frame : Matrix (Fin 6) (Fin 3) ℝ)
    {first second : Fin 6} (hdistinct : first ≠ second) :
    frameCorrelationInvolution frame first second = frame first ⬝ᵥ frame second := by
  rw [frameCorrelationInvolution, Matrix.sub_apply, Matrix.one_apply_ne hdistinct, sub_zero,
    Matrix.mul_apply]
  rfl

/-- **THE FRAME BRIDGE.**  The correlation matrix of a unit-norm tight frame of
six directions in `R^3` is a hollow symmetric involution, so the entire U6
development applies to it — with NO design, NO weights and NO share hypothesis.
`(frame frame^T)^2 = 2 (frame frame^T)` is the whole proof. -/
theorem isHollowInvolution_frameCorrelationInvolution {frame : Matrix (Fin 6) (Fin 3) ℝ}
    (hframe : IsUnitTightFrameSix frame) :
    IsHollowInvolution (frameCorrelationInvolution frame) where
  symmetric := by
    rw [frameCorrelationInvolution, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  square_eq_one := by
    have hsquare : (frame * frameᵀ) * (frame * frameᵀ) = (2 : ℝ) • (frame * frameᵀ) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc frameᵀ, hframe.tight, Matrix.smul_mul,
        Matrix.one_mul, Matrix.mul_smul]
    rw [frameCorrelationInvolution, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hsquare]
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs <;> ring
  diagonal_eq_zero := fun index => by
    rw [frameCorrelationInvolution, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
    rw [show ∑ coord, frame index coord * frameᵀ coord index
        = leverageOf (frame index) from by
      simp only [leverageOf, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun coord _ => (pow_two (frame index coord)).symm,
      hframe.unit index, sub_self]

/-- A design's own unit directions form such a frame, as soon as its shares are
all `1/2`.  No leverage hypothesis: the share carries exactly the normalisation
the directions remove. -/
theorem isUnitTightFrameSix_unitAtomRows (D : WeightedDesign 6 3)
    (hpositive : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex))
    (hshare : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    IsUnitTightFrameSix (unitAtomRows D) where
  unit := fun index => leverageOf_unitAtom D (hpositive index)
  tight := by
    have hframeLaw := sum_atomShare_smul_atomMatrix_unitAtom D
    have hcollapse : ∑ atomIndex : Fin 6,
        atomShare D atomIndex • atomMatrix (unitAtom D atomIndex)
        = ((1 : ℝ) / 2) • ∑ atomIndex : Fin 6, atomMatrix (unitAtom D atomIndex) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun atomIndex _ => by rw [hshare atomIndex]
    rw [hcollapse] at hframeLaw
    have hrows : (unitAtomRows D)ᵀ * unitAtomRows D
        = ∑ atomIndex, atomMatrix (unitAtom D atomIndex) := by
      rw [transpose_mul_self_eq_sum_rows]
      rfl
    rw [hrows]
    have hscaled := congrArg (fun target : Matrix (Fin 3) (Fin 3) ℝ => (2 : ℝ) • target)
      hframeLaw
    simp only [smul_smul] at hscaled
    rw [show (2 : ℝ) * ((1 : ℝ) / 2) = 1 from by norm_num, one_smul] at hscaled
    exact hscaled

/-- The frame correlation of a design's direction rows IS its correlation
involution. -/
theorem frameCorrelationInvolution_unitAtomRows (D : WeightedDesign 6 3) :
    frameCorrelationInvolution (unitAtomRows D) = correlationInvolution D := by
  rw [frameCorrelationInvolution, correlationInvolution, directionGramMatrix_eq_mul_transpose]

/-! ### Realising an arbitrary slack point on a frame -/

/-- **THE REALISATION.**  Every admissible slack vector on every unit-norm tight
frame of six directions is the slack vector of a genuine weighted `(6,3)` design
with the same directions, uniform share `1/2` and all atoms heavy: put
`g_c = (1 - tau_c)^(-1/2) u_c` and `t_c = (1 - tau_c)/2`.  Parseval holds because
`sum_c t_c ell_c u_c u_c^T = (1/2) sum_c u_c u_c^T = 1`, and the weights sum to
`(6 - 4)/2 = 1` exactly because the slacks sum to four.

This is what makes the covering reformulation an EQUIVALENCE rather than a
sufficient condition: the weight polytope is not a shadow of the design space, it
is a free coordinate on it. -/
noncomputable def slackFrameDesign (frame : Matrix (Fin 6) (Fin 3) ℝ)
    (slack : Fin 6 → ℝ) (hslack : ∀ index, slack index < 1)
    (hsum : ∑ index, slack index = 4)
    (htight : frameᵀ * frame = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) :
    WeightedDesign 6 3 where
  atom index := (Real.sqrt (1 - slack index))⁻¹ • frame index
  weight index := (1 - slack index) / 2
  weight_pos := fun index => by
    have hgap : 0 < 1 - slack index := by linarith [hslack index]
    linarith
  weight_sum_one := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  isParseval := by
    have hterm : ∀ index : Fin 6,
        ((1 - slack index) / 2) • atomMatrix ((Real.sqrt (1 - slack index))⁻¹ • frame index)
          = ((1 : ℝ) / 2) • atomMatrix (frame index) := by
      intro index
      have hgap : 0 < 1 - slack index := by linarith [hslack index]
      rw [atomMatrix_smul, smul_smul, inv_pow, Real.sq_sqrt hgap.le]
      congr 1
      field_simp
    rw [Finset.sum_congr rfl fun index _ => hterm index, ← Finset.smul_sum,
      ← transpose_mul_self_eq_sum_rows, htight, smul_smul]
    norm_num

theorem slackFrameDesign_atom (frame : Matrix (Fin 6) (Fin 3) ℝ) (slack : Fin 6 → ℝ)
    (hslack : ∀ index, slack index < 1) (hsum : ∑ index, slack index = 4)
    (htight : frameᵀ * frame = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (index : Fin 6) :
    (slackFrameDesign frame slack hslack hsum htight).atom index
      = (Real.sqrt (1 - slack index))⁻¹ • frame index := rfl

theorem leverageOf_slackFrameDesign_atom {frame : Matrix (Fin 6) (Fin 3) ℝ} {slack : Fin 6 → ℝ}
    (hframe : IsUnitTightFrameSix frame) (hslack : ∀ index, slack index < 1)
    (hsum : ∑ index, slack index = 4)
    (htight : frameᵀ * frame = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (index : Fin 6) :
    leverageOf ((slackFrameDesign frame slack hslack hsum htight).atom index)
      = (1 - slack index)⁻¹ := by
  have hgap : 0 < 1 - slack index := by linarith [hslack index]
  rw [slackFrameDesign_atom, leverageOf_smul, hframe.unit index, mul_one, inv_pow,
    Real.sq_sqrt hgap.le]

theorem weightSlack_slackFrameDesign {frame : Matrix (Fin 6) (Fin 3) ℝ} {slack : Fin 6 → ℝ}
    (hframe : IsUnitTightFrameSix frame) (hslack : ∀ index, slack index < 1)
    (hsum : ∑ index, slack index = 4)
    (htight : frameᵀ * frame = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (index : Fin 6) :
    weightSlack (slackFrameDesign frame slack hslack hsum htight) index = slack index := by
  rw [weightSlack, leverageOf_slackFrameDesign_atom hframe hslack hsum htight index, inv_inv]
  ring

theorem atomShare_slackFrameDesign {frame : Matrix (Fin 6) (Fin 3) ℝ} {slack : Fin 6 → ℝ}
    (hframe : IsUnitTightFrameSix frame) (hslack : ∀ index, slack index < 1)
    (hsum : ∑ index, slack index = 4)
    (htight : frameᵀ * frame = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (index : Fin 6) :
    atomShare (slackFrameDesign frame slack hslack hsum htight) index = 1 / 2 := by
  have hgap : 0 < 1 - slack index := by linarith [hslack index]
  rw [atomShare, leverageOf_slackFrameDesign_atom hframe hslack hsum htight index,
    show (slackFrameDesign frame slack hslack hsum htight).weight index
      = (1 - slack index) / 2 from rfl]
  field_simp

theorem unitAtom_slackFrameDesign {frame : Matrix (Fin 6) (Fin 3) ℝ} {slack : Fin 6 → ℝ}
    (hframe : IsUnitTightFrameSix frame) (hslack : ∀ index, slack index < 1)
    (hsum : ∑ index, slack index = 4)
    (htight : frameᵀ * frame = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (index : Fin 6) :
    unitAtom (slackFrameDesign frame slack hslack hsum htight) index = frame index := by
  have hgap : 0 < 1 - slack index := by linarith [hslack index]
  have hroot : Real.sqrt (1 - slack index) ≠ 0 := Real.sqrt_ne_zero'.mpr hgap
  rw [unitAtom, leverageOf_slackFrameDesign_atom hframe hslack hsum htight index,
    slackFrameDesign_atom, Real.sqrt_inv, inv_inv, smul_smul,
    mul_inv_cancel₀ hroot, one_smul]

theorem directionGram_slackFrameDesign {frame : Matrix (Fin 6) (Fin 3) ℝ} {slack : Fin 6 → ℝ}
    (hframe : IsUnitTightFrameSix frame) (hslack : ∀ index, slack index < 1)
    (hsum : ∑ index, slack index = 4)
    (htight : frameᵀ * frame = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
    (first second : Fin 6) :
    directionGram (slackFrameDesign frame slack hslack hsum htight) first second
      = frame first ⬝ᵥ frame second := by
  rw [directionGram, unitAtom_slackFrameDesign hframe hslack hsum htight,
    unitAtom_slackFrameDesign hframe hslack hsum htight]

/-! ## 7. THEOREM A -/

/-- **THE `(6,3)` UNIFORM-SHARE STATEMENT** — the pen's V6.  Every weighted
`(6,3)` design whose atoms all carry share `1/2` and are all heavy has a
dominating triple.  The equal-share stratum, where the leverages are additionally
pinned to `3`, is the single point `tau ≡ 2/3` of this family and is a THEOREM
(U6); the free-weight statement is open. -/
def GtzUniformShareSixThree : Prop :=
  ∀ D : WeightedDesign 6 3, (∀ atomIndex, atomShare D atomIndex = 1 / 2) → AllHeavy D →
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C

/-- **THEOREM A, the sufficient half at the design's own involution.**  A covering
of the heavy region by the twenty cells of `M = Gamma - 1` produces a dominating
triple. -/
theorem exists_dominates_of_coversHeavySlackSimplex (D : WeightedDesign 6 3)
    (hshare : ∀ atomIndex, atomShare D atomIndex = 1 / 2) (hheavy : AllHeavy D)
    (hcovers : CoversSlackRegion (correlationInvolution D) heavySlackSimplex) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C := by
  have hpositive : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) :=
    fun atomIndex => lt_trans zero_lt_one (hheavy atomIndex)
  have hmember : weightSlack D ∈ heavySlackSimplex := by
    refine ⟨fun index => ⟨weightSlack_pos D hheavy index,
      weightSlack_lt_one D (hpositive index)⟩, sum_weightSlack_eq_four D hshare⟩
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcell⟩ :=
    hcovers _ hmember
  refine ⟨{first, second, third}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
      Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]
  · refine (dominates_triple_iff_posSemidef_slackHollowThree D (hpositive first)
      (hpositive second) (hpositive third) hfirstSecond hfirstThird hsecondThird).mpr ?_
    rw [mem_tripleSlackCell_iff, correlationInvolution_apply_of_ne D hfirstSecond,
      correlationInvolution_apply_of_ne D hfirstThird,
      correlationInvolution_apply_of_ne D hsecondThird] at hcell
    exact hcell

/-- **THEOREM A.**  The pen's V6 statement is EQUIVALENT to the covering of the
realised slack region by the twenty cells, uniformly over unit-norm tight frames
of six directions in `R^3`.

Both directions are unconditional.  Forward, a design supplies its own frame
(`Gtz.isUnitTightFrameSix_unitAtomRows`) and its own slack point.  Backward,
`Gtz.slackFrameDesign` turns any frame and any admissible slack point into a
design realising them, so no slack point of any frame escapes the hypothesis.

This is the statement the frontier argument is about: twenty convex, closed,
upward-closed, 3-local subsets of a five-dimensional hypersimplex, and the
question of whether they cover it. -/
theorem gtzUniformShareSixThree_iff_forall_coversHeavySlackSimplex :
    GtzUniformShareSixThree
      ↔ ∀ frame : Matrix (Fin 6) (Fin 3) ℝ, IsUnitTightFrameSix frame →
          CoversSlackRegion (frameCorrelationInvolution frame) heavySlackSimplex := by
  constructor
  · intro hstatement frame hframe slack hmember
    obtain ⟨hbounds, hsum⟩ := hmember
    have hslackUpper : ∀ index, slack index < 1 := fun index => (hbounds index).2
    set realised : WeightedDesign 6 3 :=
      slackFrameDesign frame slack hslackUpper hsum hframe.tight with hrealised
    have hshare : ∀ atomIndex, atomShare realised atomIndex = 1 / 2 :=
      atomShare_slackFrameDesign hframe hslackUpper hsum hframe.tight
    have hslackEq : ∀ index, weightSlack realised index = slack index :=
      weightSlack_slackFrameDesign hframe hslackUpper hsum hframe.tight
    have hleveragePositive : ∀ atomIndex : Fin 6, 0 < leverageOf (realised.atom atomIndex) := by
      intro atomIndex
      rw [hrealised, leverageOf_slackFrameDesign_atom hframe hslackUpper hsum hframe.tight]
      exact inv_pos.mpr (by linarith [(hbounds atomIndex).2])
    have hheavy : AllHeavy realised := by
      intro atomIndex
      refine (weightSlack_pos_iff_one_lt_leverage realised (hleveragePositive atomIndex)).mp ?_
      rw [hslackEq atomIndex]
      exact (hbounds atomIndex).1
    have hpositive : ∀ atomIndex : Fin 6, 0 < leverageOf (realised.atom atomIndex) :=
      fun atomIndex => lt_trans zero_lt_one (hheavy atomIndex)
    obtain ⟨selected, hcard, hdominates⟩ := hstatement realised hshare hheavy
    obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hshape⟩ :=
      Finset.card_eq_three.mp hcard
    rw [hshape] at hdominates
    refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
    have hcriterion := (dominates_triple_iff_posSemidef_slackHollowThree realised
      (hpositive first) (hpositive second) (hpositive third) hfirstSecond hfirstThird
      hsecondThird).mp hdominates
    rw [hslackEq, hslackEq, hslackEq,
      directionGram_slackFrameDesign hframe hslackUpper hsum hframe.tight,
      directionGram_slackFrameDesign hframe hslackUpper hsum hframe.tight,
      directionGram_slackFrameDesign hframe hslackUpper hsum hframe.tight] at hcriterion
    rw [mem_tripleSlackCell_iff, frameCorrelationInvolution_apply_of_ne frame hfirstSecond,
      frameCorrelationInvolution_apply_of_ne frame hfirstThird,
      frameCorrelationInvolution_apply_of_ne frame hsecondThird]
    exact hcriterion
  · intro hcovering D hshare hheavy
    have hpositive : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) :=
      fun atomIndex => lt_trans zero_lt_one (hheavy atomIndex)
    refine exists_dominates_of_coversHeavySlackSimplex D hshare hheavy ?_
    have hframe := isUnitTightFrameSix_unitAtomRows D hpositive hshare
    have hcovers := hcovering (unitAtomRows D) hframe
    rwa [frameCorrelationInvolution_unitAtomRows] at hcovers

/-- **THE PEN'S THEOREM A, AS A SUFFICIENT CONDITION.**  Covering the CLOSED
polytope `Sigma` suffices, since the realised region sits inside it.  This is the
implication a frontier argument delivers: prove the covering, get the theorem. -/
theorem gtzUniformShareSixThree_of_forall_coversSlackSimplex
    (hcovering : ∀ frame : Matrix (Fin 6) (Fin 3) ℝ, IsUnitTightFrameSix frame →
      CoversSlackRegion (frameCorrelationInvolution frame) slackSimplex) :
    GtzUniformShareSixThree :=
  gtzUniformShareSixThree_iff_forall_coversHeavySlackSimplex.mpr fun frame hframe =>
    coversSlackRegion_mono heavySlackSimplex_subset_slackSimplex (hcovering frame hframe)

/-! ## 8. U6 is the single point `tau ≡ 2/3`

Everything below consumes only the abstract, unconditional U6 theorem
`Gtz.IsHollowInvolution.exists_posSemidef_twoThirds_shift` and its margin
strengthening — no coherence, no realizability, no non-parallel hypothesis. -/

/-- **THE DEFINITION PIN.**  On a uniform-leverage-three design the slack block IS
the shipped `2/3` shift, so this file's criterion and
`Gtz.dominates_triple_iff_posSemidef_hollowShift` are the same statement at that
stratum — two independently derived congruences (this one by `diag(sqrt ell)`, the
shipped one by the scalar rescale) agreeing on the nose. -/
theorem slackHollowThree_eq_hollowShift_of_leverage_eq_three (D : WeightedDesign m 3)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3) (first second third : Fin m) :
    slackHollowThree (weightSlack D first) (weightSlack D second) (weightSlack D third)
        (directionGram D first second) (directionGram D first third)
        (directionGram D second third)
      = hollowMatrixThree (directionGram D first second) (directionGram D first third)
          (directionGram D second third) + (2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hslack : ∀ atomIndex : Fin m, weightSlack D atomIndex = 2 / 3 := by
    intro atomIndex
    rw [weightSlack, hleverage atomIndex]
    norm_num
  rw [hslack, hslack, hslack, slackHollowThree_self, add_comm]

/-- **U6 AS A COVERING STATEMENT.**  Every hollow symmetric involution on `Fin 6`
covers the constant slack point `2/3`.  This is
`Gtz.IsHollowInvolution.exists_posSemidef_twoThirds_shift` read in slack
coordinates, and it is the single point of `Sigma` the campaign had before this
file. -/
theorem coversSlackRegion_singleton_twoThirds {invol : Matrix (Fin 6) (Fin 6) ℝ}
    (hinvol : IsHollowInvolution invol) :
    CoversSlackRegion invol {fun _ : Fin 6 => (2 : ℝ) / 3} := by
  rintro slack rfl
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hshift⟩ :=
    hinvol.exists_posSemidef_twoThirds_shift
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  rw [mem_tripleSlackCell_iff, slackHollowThree_self]
  rwa [hinvol.submatrix_three_eq_hollowMatrixThree first second third] at hshift

/-- **THE TOP-BAND GATE.**  Every slack vector all of whose coordinates are at
least `16/25` is covered — the shipped margin theorem
`Gtz.IsHollowInvolution.exists_posSemidef_marginShift` transported through upward
closure.

The pen proposed to reach this band by its g-transform, whose exact threshold at
`w_56 = 0` is `sqrt 3 - 1` (see `Gtz.gTransform_at_sqrtThree_sub_one`).  That
threshold is strictly worse than `16/25`
(`Gtz.sixteen_twentyfifths_lt_sqrtThree_sub_one`), so the g-transform layer does
not have to be built to cover the top band. -/
theorem coversSlackRegion_of_marginFloor {invol : Matrix (Fin 6) (Fin 6) ℝ}
    (hinvol : IsHollowInvolution invol) :
    CoversSlackRegion invol {slack : Fin 6 → ℝ | ∀ index, (16 : ℝ) / 25 ≤ slack index} := by
  intro slack hmember
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hshift⟩ :=
    hinvol.exists_posSemidef_marginShift
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  rw [hinvol.submatrix_three_eq_hollowMatrixThree first second third] at hshift
  rw [mem_tripleSlackCell_iff]
  exact posSemidef_slackHollowThree_of_floor hshift (hmember first) (hmember second)
    (hmember third)

/-- **THE TOP-BAND GATE ON A DESIGN.**  Any uniform-share design whose atoms are
all at slack at least `16/25` — equivalently, all of leverage at least `25/9` —
has a dominating triple.  No coherence, no cap, no case split. -/
theorem exists_dominates_of_sixteen_twentyfifths_le_weightSlack (D : WeightedDesign 6 3)
    (hshare : ∀ atomIndex, atomShare D atomIndex = 1 / 2) (hheavy : AllHeavy D)
    (hband : ∀ atomIndex, (16 : ℝ) / 25 ≤ weightSlack D atomIndex) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C := by
  have hpositive : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) :=
    fun atomIndex => lt_trans zero_lt_one (hheavy atomIndex)
  have hframe := isUnitTightFrameSix_unitAtomRows D hpositive hshare
  have hinvol : IsHollowInvolution (correlationInvolution D) := by
    have hbridge := isHollowInvolution_frameCorrelationInvolution hframe
    rwa [frameCorrelationInvolution_unitAtomRows] at hbridge
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcell⟩ :=
    coversSlackRegion_of_marginFloor hinvol (weightSlack D) hband
  refine ⟨{first, second, third}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
      Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]
  · refine (dominates_triple_iff_posSemidef_slackHollowThree D (hpositive first)
      (hpositive second) (hpositive third) hfirstSecond hfirstThird hsecondThird).mpr ?_
    rw [mem_tripleSlackCell_iff, correlationInvolution_apply_of_ne D hfirstSecond,
      correlationInvolution_apply_of_ne D hfirstThird,
      correlationInvolution_apply_of_ne D hsecondThird] at hcell
    exact hcell

/-- **U6 IS A COROLLARY OF THIS FILE'S CRITERION.**  The equal-share `(6,3)`
theorem, re-derived through the slack criterion at the single point `tau ≡ 2/3`.
The proof consumes only the abstract involution theorem, so it is a genuine
specialisation of the covering rather than a repetition of the U6 argument. -/
theorem exists_dominates_of_isEqualShare_six (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C := by
  have hpositive : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) :=
    fun atomIndex => hequal.leverage_pos (by norm_num) atomIndex
  have hinvol : IsHollowInvolution (correlationInvolution D) :=
    isHollowInvolution_correlationInvolution D hequal (by norm_num) (by norm_num)
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcell⟩ :=
    coversSlackRegion_singleton_twoThirds hinvol _ rfl
  refine ⟨{first, second, third}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
      Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]
  · refine (dominates_triple_iff_posSemidef_slackHollowThree D (hpositive first)
      (hpositive second) (hpositive third) hfirstSecond hfirstThird hsecondThird).mpr ?_
    rw [mem_tripleSlackCell_iff, correlationInvolution_apply_of_ne D hfirstSecond,
      correlationInvolution_apply_of_ne D hfirstThird,
      correlationInvolution_apply_of_ne D hsecondThird] at hcell
    rw [weightSlack_eq_two_thirds_of_isEqualShare hequal,
      weightSlack_eq_two_thirds_of_isEqualShare hequal,
      weightSlack_eq_two_thirds_of_isEqualShare hequal]
    exact hcell

/-! ### Why the g-transform layer is not needed for the top band -/

/-- **THE TOP-BAND GATE BEATS THE G-TRANSFORM THRESHOLD.**  The pen proposed to
reach the top band of `Sigma` through its `g(theta) = (1 + theta/2)^2 (1 - theta)`,
whose value at the campaign's decimal "about 0.73" is exactly
`g(sqrt 3 - 1) = 1/2`, so that gate fires only from `sqrt 3 - 1` upward.
`Gtz.coversSlackRegion_of_marginFloor` already fires from `16/25`, and
`16/25 < sqrt 3 - 1`: the band the g-transform would buy is strictly contained in
the band the shipped margin already buys.  (The g-transform itself is developed in
`Gtz.Quantitative.GTransformGate`; only the comparison is needed here.) -/
theorem sixteen_twentyfifths_lt_sqrtThree_sub_one : (16 : ℝ) / 25 < Real.sqrt 3 - 1 := by
  have hsquare : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [hsquare, Real.sqrt_nonneg 3]

/-! ## 9. V2: the weight-side order statistics

One pigeonhole, no sorting.  `Tuple.sort` would give the sorted tuple but not the
subset form, and the subset form is what a covering argument uses ("no 4-set is
entirely cheap"). -/

/-- **THE BUDGET PIGEONHOLE.**  If every value is strictly below `cap`, the total
is at least `total`, the complement of `selected` is nonempty, and the budget
`|complement| cap + |selected| level` does not exceed `total`, then some index of
`selected` carries a value strictly above `level`. -/
theorem exists_lt_of_budget {value : Fin size → ℝ} {cap level total : ℝ}
    (hcap : ∀ index, value index < cap) (htotal : total ≤ ∑ index, value index)
    {selected : Finset (Fin size)} (hcomplement : selectedᶜ.Nonempty)
    (hbudget : (selectedᶜ.card : ℝ) * cap + (selected.card : ℝ) * level ≤ total) :
    ∃ index ∈ selected, level < value index := by
  by_contra hcontra
  have hbelow : ∀ index ∈ selected, value index ≤ level := by
    intro index hmember
    by_contra hlarge
    exact hcontra ⟨index, hmember, not_le.mp hlarge⟩
  have hselectedBound : ∑ index ∈ selected, value index ≤ (selected.card : ℝ) * level := by
    calc ∑ index ∈ selected, value index ≤ ∑ _index ∈ selected, level :=
          Finset.sum_le_sum fun index hmember => hbelow index hmember
      _ = (selected.card : ℝ) * level := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcomplementBound : ∑ index ∈ selectedᶜ, value index < (selectedᶜ.card : ℝ) * cap := by
    calc ∑ index ∈ selectedᶜ, value index < ∑ _index ∈ selectedᶜ, cap :=
          Finset.sum_lt_sum_of_nonempty hcomplement fun index _ => hcap index
      _ = (selectedᶜ.card : ℝ) * cap := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsplit : ∑ index ∈ selected, value index + ∑ index ∈ selectedᶜ, value index
      = ∑ index, value index := Finset.sum_add_sum_compl selected value
  linarith

/-- **THE TOP ORDER STATISTIC**, non-strict: at total four with six coordinates,
some coordinate is at least `2/3`.  In leverage this is `ell >= 3`, the shipped
`Gtz.exists_leverage_three_le` — but here it comes out of the budget alone. -/
theorem exists_two_thirds_le_of_sum_eq_four {value : Fin 6 → ℝ}
    (htotal : ∑ index, value index = 4) : ∃ index, (2 : ℝ) / 3 ≤ value index := by
  by_contra hcontra
  have hbelow : ∀ index : Fin 6, value index < 2 / 3 := by
    intro index
    by_contra hlarge
    exact hcontra ⟨index, not_lt.mp hlarge⟩
  have hbound : ∑ index, value index < ∑ _index : Fin 6, (2 : ℝ) / 3 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun index _ => hbelow index
  rw [htotal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbound
  norm_num at hbound

/-- **THE ORDER STATISTICS OF `Sigma`, in one statement.**  On the pen's polytope
every subset of size `j` contains a coordinate strictly above `(4 - (6 - j))/j`,
provided its complement is nonempty.  Instantiated at `j = 5, 4, 3` this is the
pen's `tau_(2) > 3/5`, `tau_(3) > 1/2`, `tau_(4) > 1/3`. -/
theorem exists_lt_of_mem_slackSimplex {slack : Fin 6 → ℝ} (hmember : slack ∈ slackSimplex)
    {selected : Finset (Fin 6)} {level : ℝ} (hcomplement : selectedᶜ.Nonempty)
    (hstrict : ∀ index, slack index < 1)
    (hbudget : (selectedᶜ.card : ℝ) + (selected.card : ℝ) * level ≤ 4) :
    ∃ index ∈ selected, level < slack index := by
  refine exists_lt_of_budget hstrict (le_of_eq hmember.2.symm) hcomplement ?_
  rw [mul_one]
  exact hbudget

/-- **AT MOST TWO ATOMS ARE CHEAP.**  A third coordinate at or below `1/3` is
arithmetically impossible on `Sigma`: the budget cannot pay for it.  This is the
pen's V2 headline, and it is strictly sharper on this stratum than the shipped
heaviness profile, which only forbids a fourth. -/
theorem card_cheapSlackSet_le_two {slack : Fin 6 → ℝ} (hmember : slack ∈ slackSimplex)
    (hstrict : ∀ index, slack index < 1) :
    (Finset.univ.filter fun index => slack index ≤ 1 / 3).card ≤ 2 := by
  by_contra hcontra
  rw [not_le] at hcontra
  obtain ⟨cheapTriple, hsubset, hcard⟩ := Finset.exists_subset_card_eq
    (show 3 ≤ (Finset.univ.filter fun index => slack index ≤ 1 / 3).card from hcontra)
  have hcomplement : cheapTripleᶜ.Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_compl, hcard, Fintype.card_fin]
    norm_num
  have hbudget : ((cheapTripleᶜ).card : ℝ) + (cheapTriple.card : ℝ) * (1 / 3) ≤ 4 := by
    rw [Finset.card_compl, hcard, Fintype.card_fin]
    norm_num
  obtain ⟨index, hmemberTriple, hlarge⟩ :=
    exists_lt_of_mem_slackSimplex hmember hcomplement hstrict hbudget
  have hcheap := Finset.mem_filter.mp (hsubset hmemberTriple)
  linarith [hcheap.2]

/-- The design-side reading, in slack coordinates. -/
theorem card_cheapAtomSet_le_two (D : WeightedDesign 6 3)
    (hshare : ∀ atomIndex, atomShare D atomIndex = 1 / 2) (hheavy : AllHeavy D) :
    (Finset.univ.filter fun atomIndex => weightSlack D atomIndex ≤ 1 / 3).card ≤ 2 := by
  have hpositive : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) :=
    fun atomIndex => lt_trans zero_lt_one (hheavy atomIndex)
  refine card_cheapSlackSet_le_two ?_ (fun index => weightSlack_lt_one D (hpositive index))
  exact ⟨fun index => ⟨(weightSlack_pos D hheavy index).le,
    (weightSlack_lt_one D (hpositive index)).le⟩, sum_weightSlack_eq_four D hshare⟩

end Gtz

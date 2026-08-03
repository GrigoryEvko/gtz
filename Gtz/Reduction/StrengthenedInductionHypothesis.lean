/-
# The strengthened induction hypothesis, and why it cannot propagate

`Gtz.Reduction.RankInductionStep` names the wall: `exists_all_certificates_but_discriminant`
buys six of the Lifting Lemma's seven certificates from `GtzWeightedAll k`, and the
seventh — the `∀ testVec` conjunct of `LiftingLemma` — is `r rᵀ ⪯ A · (G′ − I)` in the
Loewner order, a demand for SLACK in one direction where the rank-`k` hypothesis
supplies only `G′ − I ⪰ 0`. This file asks whether a STRENGTHENED hypothesis `Q(k)`
exists with (a) `Q(k) → GtzWeighted (M(k)) k`, (b) `Q(k) → Q(k+1)`, (c) `Q(2)` true.

**What is built here.** The seventh conjunct is re-founded on named objects —
`couplingVector` (the direction), `projectedGap` (the form) and `liftBudget` (the
budget) — turning it into a rank-one Loewner condition, and then:

* `borderedMatrix_posSemidef_iff_solutionRate_le` — the BORDERED PSD LEMMA in the
  SINGULAR case, both directions. Mathlib's `Matrix.PosSemidef.fromBlocks₁₁` needs the
  corner block positive DEFINITE and reads the Schur complement through an inverse;
  the lift needs the semidefinite case, so the rate `crossᵀ block⁺ cross` is read off a
  SOLUTION vector of `block *ᵥ solution = cross` (`solutionRate_unique`: the value does
  not depend on the solution, which is what makes the name `block⁺` honest). The proof
  is completion of squares in the form's own semi-inner product — no inverse, no
  pseudo-inverse, no eigenvalues, no positive-definiteness — so it stays inside the
  repo's spectral-theorem-free `PsdKit` discipline.
* `dominates_insert_iff_loewnerSlack` — the seventh conjunct at a fixed
  `(pivot, subset)` pair IS domination of `insert pivot subset`, an equivalence.
* `BorderedSlackLifting` — the candidate `Q`, in generalized-Schur form, with
  `gtzWeighted_succ_of_borderedSlackLifting` for (a).
* `DoesPropagateBorderedSlack` — (b), stated as a `Prop`, never as a theorem, with the
  missing ingredient named.
* Three REFUTATIONS of the candidates the experiments killed:
  `not_posSemidef_gramShift_of_overfull` (the literal "bordered-PSD at every remaining
  atom" reading, dead at every rank), `not_hasUniformDominationSlack_four_three`
  (uniform slack, dead at rank 3 at the regular tetrahedron), and
  `not_heavyPivotInDominator_four_two` (the route's own named residual, refuted by an
  explicit all-heavy `(4,3)` design).

**The crux, measured — its premise is FALSE.** The natural hope was that at the tie
stratum `G′ − I` is singular with a null vector orthogonal to `r`, so the conjunct
would hold by continuity where no uniform slack exists. It fails for the opposite
reason to the one expected: at the tie stratum `G′ − I` is NONSINGULAR. Exact
rationals, `(7,3)` split tetrahedron in all three multiplicity profiles (13/17/20
dominating triples, 0 strict, Parseval and tightness verified exactly, also under
skewed within-class weights): at all 150 (pivot, dominating-pair) combinations the
deflated gap is `N = [[5/3,-4/3],[-4/3,5/3]]`, `det N = 1`, `spec N = {1/3, 3}`,
`ker N = 0`, and the conjunct holds with EXACT EQUALITY `qᵀ N⁻¹ q = 6 = lam(lam−1)`,
slack `0`. At `(11,4)`, all 10 profiles, 2788 combinations: `N = (11/4)·I − (5/4)·(J−I)`,
`spec = {1/4, 4, 4}`, `qᵀ N⁻¹ q = 12` = budget, zero failures, zero singular `N`.
Promoted to an identity for ranks 2..12: at the rank-`d` simplex tie
`N = d·I − ((d+1)/d)·J`, `det N = d^(d−3)`, `lambda_min(N) = 1/d`, `q` is precisely
`N`'s minimal eigenvector, and `qᵀ N⁻¹ q = d(d−1)` = budget exactly at every rank. At
the `(4,3)` regular simplex and the `(7,3)` split tetrahedron every one of the 12 resp.
56 (pivot, dominator) pairs LIFTS. So the singularity at a tie is an UPSTAIRS
phenomenon — and it IS this equality; deflation at any atom removes it. The tie
stratum is not even in the image of deflation: a deflated design has a dead atom of
positive weight, and Parseval then forces that weight to be exactly `0`.
Consequently `crossSum_eq_zero_of_dominates_insert_of_tight` never fires at a tie, no
continuity argument can be built there, and Albert's range condition never binds:
`r ∈ range(G′ − I)` held on 100% of 26565 dominating pairs with
`lambda_min ≥ 1.5e-5 > 0`, and 1535/1535 (dim 3) and 2895/2895 (dim 4) FAILURES also
had `G′ − I` nonsingular. The wall is entirely the rate condition
`liftBudget ≥ rᵀ (G′−I)⁻¹ r`, on the nonsingular stratum.

**The wall, quantified.** Failure rate of the seventh conjunct on
(pivot, downstairs-dominator) pairs: 27.6% / 30.1% / 34.9% at dim 3, `m = 5/6/7`;
30.3% / 31.8% / 32.4% / 36.3% at dim 4, `m = 8..11`. Worst `floor / leverage` ratio
1095.8 (dim 3) and 64360.0 (dim 4), reproducing the `3.4x`–`26058x` band the wall file
reports. Largest violation
`lambda_max(r rᵀ − A·(G′−I)) = 0.23335729360178846303760267936174017204257896650417`
(50 digits, 90-dps roots of an exact rational characteristic polynomial) at a `(4,3)`
design, and `0.17152877859260413756251014547016506904623153722737` at `(11,4)`. But the
wall file's "tracking `1/lambdaMin(G′−I)` exactly" is TOO STRONG: the product
`factor × lambda_min(G′−I)` spreads by 133364x at `(7,3)`, and failures occur at
downstairs margins up to 2.87.

**Why (b) is impossible — the deflation fibre.** Any `Q(k)` a consumer of the lifting
lemma can use is a predicate of the DOWNSTAIRS data `(G′, weights, pivot, subset)`.
The upstairs design is that data plus a Naimark co-vector `z` with `Σ t_c z_c² = 1` and
`G′ diag(t) z = 0`, and the lift condition at `(pivot, subset)` is
`G′_S − I ⪰ w_S w_Sᵀ/(w_p² − Q(w))` for `w` in `ker(G′ diag t)` — a condition on `z`,
which deflation destroys. Scanning the fibre at FIXED downstairs data: 1783/1691/1400
exact fibre points over 23/23/24 designs (dim3 m7, dim4 m9, dim4 m11) gave 3–35, 3–86
and 8–122 DISTINCT lifting sets, with 508/575/418 fibre points where NO subset lifts —
and 0/23, 0/23, 0/24 designs had a subset lifting at EVERY fibre point. Restricted to
`leverage ≥ rank` the dead points vanish (0/277, 0/77) but 2/11 and 1/6 designs still
have no uniformly-lifting subset. Minimal witness: two valid all-heavy `(6,3)` designs
with IDENTICAL deflated Gram (denominator 632), identical weights
`(1/6,1/18,5/18,1/9,1/3,1/18)`, identical pivot slot, identical subset, identical
`N = [[991/632,-999/316],[-999/316,1093/158]]` (PSD, `det = 539/632`) and identical
pivot leverage `4374/1309 = 3.3415 ≥ 3` — with the seventh conjunct TRUE for one fibre
point and FALSE for the other. Every one of certificates 1–6 is the same proposition on
both sides; only the DIRECTION of `q` relative to `N` differs. So no downstairs
predicate can select a lifting subset. Conversely a `Q(k)` allowed to see `z` is not a
strengthening: `(rank-k design, fibre point)` is LITERALLY the same data as
`(rank-(k+1) design, designated pivot)`, so such a `Q(k)` IS the rank-`(k+1)` statement.

**CORRECTION (adversarial audit, 2026-07-25).** The candidate below is exactly that
degenerate case, and the collapse is a THEOREM, not a risk:

    BorderedSlackLifting rank  ↔  ∀ size, GtzWeighted size (rank + 1)
    BorderedSlackLifting rank  ↔  LiftingLemma rank

because a rank-one Loewner bound ALREADY forces range membership: if
`(r · v)² ≤ A · (v · M v)` for every `v` with `M ⪰ 0`, decompose `r = M s + w` with
`w ∈ ker M`; the bound at `w` reads `|w|⁴ ≤ 0`, so `w = 0`. Hence `hsolves` and `hrate`
are never extra demands — the seventh conjunct produces both. This is the same collapse
`LiftingLemma.lean:590` (`liftingLemma_iff_gtzWeighted_succ`) already records for the
object being refined.

Two consequences, both against the earlier reading here. Requirement (c) is NOT
unmeetable: `BorderedSlackLifting 0` and `BorderedSlackLifting 1` both HOLD, from
`gtz_rank_one` and `gtz_rank_two` — the claim that `BorderedSlackLifting 1` would imply
`GtzWeighted size 3` is an off-by-one, it gives `GtzWeighted size 2`. And (a) holds
outright. **Only (b) is open, and (b) is verbatim the original induction step.** The
wall therefore stands exactly where it did; what is refuted is the REASON given for it.
That is why `DoesPropagateBorderedSlack` is a `Prop` below and not a theorem.

**Selection rules, all refuted.** Downstairs rules at `(11,4)`, exact best-case rates:
`minTraceInverse` (the Batson–Spielman–Srivastava lower barrier at 0) 595/624,
`maxLambdaMin` 593/624, `maxDetN` 588/624, `maxVol` (pseudoskeleton-classical) 586/624,
`maxLambdaMinNormalised` 536/624, `maxTraceN` 529/624 — none reaches 100% at any size or
rank. Upstairs pivot rules over 33700 designs, every counterexample re-verified at 90
digits: `maxHeavyMargin` 99.90%, `maxProjectionDiagonal` 99.57%, `maxLeverage` 99.54%,
`anyFloorPivot` 98.11%, `maxWeight` 92.87%, `minWeight` 92.19%. The last survivor —
take the pivot whose MARGIN-MAXIMAL dominator lifts — held on 50050/50050 random
designs and was then refuted by hill-climbing plus exact rational snapping (badness
1.3898 at `(4,3)`, 1.0877 at `(5,3)`, 1.0681 at `(7,3)`, no near-ties); the mechanism is
an anti-correlation, maximising the downstairs margin systematically selects the subset
coupling hardest to the pivot. Optimizer note: the minimax searches are SLSQP;
Nelder–Mead stalls here at `1e-4`..`1e-5` returning bit-identical values, and every
negative was re-verified in exact rationals or at 60–90 digits, never from a float
margin (`sigma_min(G_C) − 1` by SVD, never `lambda_min` of the squared frame operator).

**GTZ itself is untouched.** 0 designs without a dominating top subset in roughly 45000
exact designs across ranks 3–5. What this file refutes is the ROUTE, and one named
residual on it.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.Reductions
import Gtz.Reduction.LiftingLemma
import Gtz.Reduction.RankInductionStep
import Gtz.Ties.TetrahedronCertifiedTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ### The rate of a positive semidefinite form along a direction

`directionᵀ W⁺ direction` without a pseudo-inverse: read it off a SOLUTION vector of
`W *ᵥ solution = direction`. `solutionRate_unique` is what licenses the notation —
the value is independent of which solution is chosen. -/

section Rate

variable {size : ℕ}

/-- The quadratic form of a positive semidefinite matrix is nonnegative. -/
theorem quadForm_nonneg_of_posSemidef {form : Matrix (Fin size) (Fin size) ℝ}
    (hform : form.PosSemidef) (testVec : Fin size → ℝ) :
    0 ≤ testVec ⬝ᵥ (form *ᵥ testVec) :=
  (posSemidef_iff_quadForm_nonneg form (transpose_eq_of_isHermitian hform.1)).mp
    hform testVec

/-- **Cauchy–Schwarz for a positive semidefinite form**, division-free: the mixed term
is dominated by the two diagonal ones. Rides on the repo's scalar discriminant
converse, applied to the form at `leftVec + coordinate · rightVec`. -/
theorem quadForm_sq_le_mul_of_posSemidef {form : Matrix (Fin size) (Fin size) ℝ}
    (hform : form.PosSemidef) (leftVec rightVec : Fin size → ℝ) :
    (leftVec ⬝ᵥ (form *ᵥ rightVec)) ^ 2
      ≤ (rightVec ⬝ᵥ (form *ᵥ rightVec)) * (leftVec ⬝ᵥ (form *ᵥ leftVec)) := by
  have hsymm : formᵀ = form := transpose_eq_of_isHermitian hform.1
  have hcross : rightVec ⬝ᵥ (form *ᵥ leftVec) = leftVec ⬝ᵥ (form *ᵥ rightVec) :=
    dot_mulVec_comm hsymm rightVec leftVec
  refine discriminant_le_of_quadratic_nonneg
    (quadForm_nonneg_of_posSemidef hform rightVec) fun coordinate => ?_
  have hexpand : (leftVec + coordinate • rightVec)
        ⬝ᵥ (form *ᵥ (leftVec + coordinate • rightVec))
      = (rightVec ⬝ᵥ (form *ᵥ rightVec)) * coordinate ^ 2
        + 2 * coordinate * (leftVec ⬝ᵥ (form *ᵥ rightVec))
        + leftVec ⬝ᵥ (form *ᵥ leftVec) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hcross]
    ring
  rw [← hexpand]
  exact quadForm_nonneg_of_posSemidef hform _

/-- The rate of a solution IS the form at the solution. -/
theorem solutionRate_eq_quadForm {form : Matrix (Fin size) (Fin size) ℝ}
    {solution direction : Fin size → ℝ} (hsolves : form *ᵥ solution = direction) :
    solution ⬝ᵥ direction = solution ⬝ᵥ (form *ᵥ solution) := by
  rw [hsolves]

/-- The rate of a solution is nonnegative. -/
theorem solutionRate_nonneg {form : Matrix (Fin size) (Fin size) ℝ}
    (hform : form.PosSemidef) {solution direction : Fin size → ℝ}
    (hsolves : form *ᵥ solution = direction) : 0 ≤ solution ⬝ᵥ direction := by
  rw [solutionRate_eq_quadForm hsolves]
  exact quadForm_nonneg_of_posSemidef hform solution

/-- **The rate does not depend on which solution is chosen**, so `solution ⬝ᵥ direction`
deserves the name `directionᵀ W⁺ direction`: symmetry of the form moves the matrix from
one solution to the other. -/
theorem solutionRate_unique {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : formᵀ = form) {firstSolution secondSolution direction : Fin size → ℝ}
    (hfirst : form *ᵥ firstSolution = direction)
    (hsecond : form *ᵥ secondSolution = direction) :
    firstSolution ⬝ᵥ direction = secondSolution ⬝ᵥ direction :=
  calc firstSolution ⬝ᵥ direction
      = firstSolution ⬝ᵥ (form *ᵥ secondSolution) := by rw [hsecond]
    _ = secondSolution ⬝ᵥ (form *ᵥ firstSolution) := dot_mulVec_comm hsymm _ _
    _ = secondSolution ⬝ᵥ direction := by rw [hfirst]

/-- **A solution exists whenever the form is invertible** — the nonsingular stratum,
which the measurements say carries the entire wall (`r ∈ range(G′−I)` on 100% of 26565
dominating pairs, and 1535/1535 resp. 2895/2895 failures with `G′−I` nonsingular). -/
theorem exists_solution_of_isUnit_det {form : Matrix (Fin size) (Fin size) ℝ}
    (hdet : IsUnit form.det) (direction : Fin size → ℝ) :
    ∃ solution : Fin size → ℝ, form *ᵥ solution = direction :=
  ⟨form⁻¹ *ᵥ direction, by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv form hdet, Matrix.one_mulVec]⟩

/-- **The rank-one Loewner bound from a solution**, in quadratic-form shape: with
`direction` in the range of a positive semidefinite `form` and the rate below `budget`,
the rank-one form is dominated by `budget · form`. Pure Cauchy–Schwarz in the form's own
semi-inner product — no inverse, no pseudo-inverse, no eigenvalues, and no
positive-definiteness. -/
theorem rankOneForm_le_of_solutionRate_le {form : Matrix (Fin size) (Fin size) ℝ}
    (hform : form.PosSemidef) {solution direction : Fin size → ℝ} {budget : ℝ}
    (hsolves : form *ᵥ solution = direction)
    (hrate : solution ⬝ᵥ direction ≤ budget) (testVec : Fin size → ℝ) :
    (direction ⬝ᵥ testVec) ^ 2 ≤ budget * (testVec ⬝ᵥ (form *ᵥ testVec)) := by
  have hsymm : formᵀ = form := transpose_eq_of_isHermitian hform.1
  have hmixed : solution ⬝ᵥ (form *ᵥ testVec) = direction ⬝ᵥ testVec := by
    rw [dot_mulVec_comm hsymm solution testVec, hsolves, dotProduct_comm]
  have hcs := quadForm_sq_le_mul_of_posSemidef hform solution testVec
  rw [hmixed, ← solutionRate_eq_quadForm hsolves] at hcs
  have hquadNonneg := quadForm_nonneg_of_posSemidef hform testVec
  nlinarith [hcs, hquadNonneg, hrate]

/-- The converse at a given solution: the rank-one bound forces the rate below the
budget — test the bound at the solution itself. The nonnegative-budget hypothesis is NOT
decoration: at `form = 0`, `direction = 0` and `budget = -1` the rank-one bound holds
vacuously while the rate `0` exceeds the budget. In every use below the budget is
`liftBudget` and its nonnegativity is the Lifting Lemma's own leverage floor. -/
theorem solutionRate_le_of_rankOneForm_le {form : Matrix (Fin size) (Fin size) ℝ}
    (hform : form.PosSemidef) {solution direction : Fin size → ℝ} {budget : ℝ}
    (hbudget : 0 ≤ budget) (hsolves : form *ᵥ solution = direction)
    (hbound : ∀ testVec : Fin size → ℝ,
      (direction ⬝ᵥ testVec) ^ 2 ≤ budget * (testVec ⬝ᵥ (form *ᵥ testVec))) :
    solution ⬝ᵥ direction ≤ budget := by
  have hatSolution := hbound solution
  rw [dotProduct_comm direction solution, ← solutionRate_eq_quadForm hsolves]
    at hatSolution
  have hrateNonneg := solutionRate_nonneg hform hsolves
  by_contra hbad
  push Not at hbad
  nlinarith [hatSolution, hrateNonneg, hbad, hbudget]

/-- **The rank-one Loewner criterion at a solution**, both directions: for a positive
semidefinite form and a direction in its range, `direction directionᵀ ⪯ budget · form` is
EXACTLY `rate ≤ budget`. The singular-case replacement for
`posSemidef_sub_vecMulVec_iff`, which needs `form` positive DEFINITE and reads the rate
through `form⁻¹`. -/
theorem rankOneForm_le_iff_solutionRate_le {form : Matrix (Fin size) (Fin size) ℝ}
    (hform : form.PosSemidef) {solution direction : Fin size → ℝ} {budget : ℝ}
    (hbudget : 0 ≤ budget) (hsolves : form *ᵥ solution = direction) :
    (∀ testVec : Fin size → ℝ,
        (direction ⬝ᵥ testVec) ^ 2 ≤ budget * (testVec ⬝ᵥ (form *ᵥ testVec)))
      ↔ solution ⬝ᵥ direction ≤ budget :=
  ⟨solutionRate_le_of_rankOneForm_le hform hbudget hsolves,
    rankOneForm_le_of_solutionRate_le hform hsolves⟩

/-- The same criterion as a Loewner statement between matrices. -/
theorem posSemidef_smul_sub_vecMulVec_of_solutionRate_le
    {form : Matrix (Fin size) (Fin size) ℝ} (hform : form.PosSemidef)
    {solution direction : Fin size → ℝ} {budget : ℝ}
    (hsolves : form *ᵥ solution = direction)
    (hrate : solution ⬝ᵥ direction ≤ budget) :
    (budget • form - Matrix.vecMulVec direction direction).PosSemidef := by
  have hsymm : formᵀ = form := transpose_eq_of_isHermitian hform.1
  have hgapSymm : (budget • form - Matrix.vecMulVec direction direction)ᵀ
      = budget • form - Matrix.vecMulVec direction direction := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hsymm,
      Matrix.transpose_vecMulVec]
  refine (posSemidef_iff_quadForm_nonneg _ hgapSymm).mpr fun testVec => ?_
  have hquad : testVec
        ⬝ᵥ ((budget • form - Matrix.vecMulVec direction direction) *ᵥ testVec)
      = budget * (testVec ⬝ᵥ (form *ᵥ testVec)) - (direction ⬝ᵥ testVec) ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm testVec direction]
    ring
  rw [hquad]
  linarith [rankOneForm_le_of_solutionRate_le hform hsolves hrate testVec]

end Rate

/-! ### The bordered positive semidefinite lemma, SINGULAR case

Mathlib's `Matrix.PosSemidef.fromBlocks₁₁` needs the corner block positive DEFINITE and
invertible; the lift needs the case where the block is only semidefinite and the Schur
complement is read through a solution vector. -/

section Bordered

variable {size : ℕ}

/-- The bordered symmetric matrix `[[corner, crossᵀ], [cross, block]]`. -/
def borderedMatrix (corner : ℝ) (cross : Fin size → ℝ)
    (block : Matrix (Fin size) (Fin size) ℝ) :
    Matrix (Unit ⊕ Fin size) (Unit ⊕ Fin size) ℝ :=
  Matrix.fromBlocks (Matrix.of fun _ _ => corner) (Matrix.of fun _ slot => cross slot)
    (Matrix.of fun slot _ => cross slot) block

theorem borderedMatrix_transpose (corner : ℝ) (cross : Fin size → ℝ)
    {block : Matrix (Fin size) (Fin size) ℝ} (hblock : blockᵀ = block) :
    (borderedMatrix corner cross block)ᵀ = borderedMatrix corner cross block := by
  have hentry : ∀ rowSlot colSlot : Fin size,
      block colSlot rowSlot = block rowSlot colSlot := fun rowSlot colSlot => by
    have hcongr := congrFun (congrFun hblock rowSlot) colSlot
    simpa using hcongr
  ext rowIdx colIdx
  cases rowIdx with
  | inl _ =>
      cases colIdx with
      | inl _ => rfl
      | inr _ => rfl
  | inr rowSlot =>
      cases colIdx with
      | inl _ => rfl
      | inr colSlot => exact hentry rowSlot colSlot

/-- Symmetry as Hermitianness. The repo's `isHermitian_of_transpose_eq` is typed at
`Fin`-indexed square matrices; the bordered matrix is indexed by `Unit ⊕ Fin size`. -/
theorem borderedMatrix_isHermitian (corner : ℝ) (cross : Fin size → ℝ)
    {block : Matrix (Fin size) (Fin size) ℝ} (hblock : blockᵀ = block) :
    (borderedMatrix corner cross block).IsHermitian := by
  show (borderedMatrix corner cross block)ᴴ = borderedMatrix corner cross block
  ext rowIdx colIdx
  rw [Matrix.conjTranspose_apply, star_trivial]
  exact congrFun (congrFun (borderedMatrix_transpose corner cross hblock) rowIdx) colIdx

/-- The bordered matrix acting on the corner coordinate. -/
theorem borderedMatrix_mulVec_inl (corner : ℝ) (cross : Fin size → ℝ)
    (block : Matrix (Fin size) (Fin size) ℝ) (testVec : Unit ⊕ Fin size → ℝ) :
    (borderedMatrix corner cross block *ᵥ testVec) (Sum.inl ())
      = corner * testVec (Sum.inl ()) + cross ⬝ᵥ (testVec ∘ Sum.inr) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton, borderedMatrix, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Function.comp_apply]

/-- The bordered matrix acting on a block coordinate. -/
theorem borderedMatrix_mulVec_inr (corner : ℝ) (cross : Fin size → ℝ)
    (block : Matrix (Fin size) (Fin size) ℝ) (testVec : Unit ⊕ Fin size → ℝ)
    (slot : Fin size) :
    (borderedMatrix corner cross block *ᵥ testVec) (Sum.inr slot)
      = cross slot * testVec (Sum.inl ())
        + (block *ᵥ (testVec ∘ Sum.inr)) slot := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton, borderedMatrix, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Function.comp_apply]

/-- The quadratic form of the bordered matrix, in the split coordinates. -/
theorem borderedMatrix_form_eq (corner : ℝ) (cross : Fin size → ℝ)
    (block : Matrix (Fin size) (Fin size) ℝ) (testVec : Unit ⊕ Fin size → ℝ) :
    testVec ⬝ᵥ (borderedMatrix corner cross block *ᵥ testVec)
      = corner * testVec (Sum.inl ()) ^ 2
        + 2 * testVec (Sum.inl ()) * (cross ⬝ᵥ (testVec ∘ Sum.inr))
        + (testVec ∘ Sum.inr) ⬝ᵥ (block *ᵥ (testVec ∘ Sum.inr)) := by
  have hblockPart : ∑ slot : Fin size,
        testVec (Sum.inr slot)
          * (borderedMatrix corner cross block *ᵥ testVec) (Sum.inr slot)
      = testVec (Sum.inl ()) * ((testVec ∘ Sum.inr) ⬝ᵥ cross)
        + (testVec ∘ Sum.inr) ⬝ᵥ (block *ᵥ (testVec ∘ Sum.inr)) := by
    have hterm : ∀ slot : Fin size,
        testVec (Sum.inr slot)
            * (borderedMatrix corner cross block *ᵥ testVec) (Sum.inr slot)
          = testVec (Sum.inl ()) * ((testVec ∘ Sum.inr) slot * cross slot)
            + (testVec ∘ Sum.inr) slot * (block *ᵥ (testVec ∘ Sum.inr)) slot := by
      intro slot
      rw [borderedMatrix_mulVec_inr]
      simp only [Function.comp_apply]
      ring
    rw [Finset.sum_congr rfl fun slot _ => hterm slot, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rfl
  rw [dotProduct, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton,
    borderedMatrix_mulVec_inl, hblockPart, dotProduct_comm (testVec ∘ Sum.inr) cross]
  ring

/-- **THE BORDERED PSD LEMMA, SINGULAR CASE.** For a symmetric block matrix
`[[corner, crossᵀ], [cross, block]]` with `block ⪰ 0`, `cross` in the RANGE of `block`
(witnessed by a solution vector) and `corner` at least the rate `crossᵀ block⁺ cross`
(read as the solution's rate), the bordered matrix is positive semidefinite. Proof:
completion of squares against the form's own semi-inner product —
`corner·a² + 2a⟨cross, y⟩ + ⟨y, block y⟩ ≥ ⟨a·solution + y, block (a·solution + y)⟩ ≥ 0`
— so no inverse, no pseudo-inverse and no definiteness anywhere. This is Albert's
theorem (Albert 1969; Gallier, *The Schur Complement and Symmetric Positive Semidefinite
Matrices*, Thm 4.3) with the Moore–Penrose inverse replaced by an arbitrary solution,
which `solutionRate_unique` shows loses nothing. -/
theorem borderedMatrix_posSemidef_of_solutionRate_le {corner : ℝ}
    {cross : Fin size → ℝ} {block : Matrix (Fin size) (Fin size) ℝ}
    (hblock : block.PosSemidef) {solution : Fin size → ℝ}
    (hsolves : block *ᵥ solution = cross) (hcorner : solution ⬝ᵥ cross ≤ corner) :
    (borderedMatrix corner cross block).PosSemidef := by
  have hblockSymm : blockᵀ = block := transpose_eq_of_isHermitian hblock.1
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨borderedMatrix_isHermitian corner cross hblockSymm, fun testVec => ?_⟩
  rw [star_trivial, borderedMatrix_form_eq]
  set cornerCoord := testVec (Sum.inl ()) with hcornerCoord
  set liftVec := testVec ∘ Sum.inr with hliftVec
  have hshift : (cornerCoord • solution + liftVec)
        ⬝ᵥ (block *ᵥ (cornerCoord • solution + liftVec))
      = (solution ⬝ᵥ cross) * cornerCoord ^ 2
        + 2 * cornerCoord * (cross ⬝ᵥ liftVec)
        + liftVec ⬝ᵥ (block *ᵥ liftVec) := by
    have hmixed : liftVec ⬝ᵥ (block *ᵥ solution) = cross ⬝ᵥ liftVec := by
      rw [hsolves, dotProduct_comm]
    have hsolutionMixed : solution ⬝ᵥ (block *ᵥ liftVec) = cross ⬝ᵥ liftVec := by
      rw [dot_mulVec_comm hblockSymm solution liftVec, hsolves, dotProduct_comm]
    have hself : solution ⬝ᵥ (block *ᵥ solution) = solution ⬝ᵥ cross := by
      rw [hsolves]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hmixed, hsolutionMixed, hself]
    ring
  have hnonneg := quadForm_nonneg_of_posSemidef hblock (cornerCoord • solution + liftVec)
  rw [hshift] at hnonneg
  nlinarith [hnonneg, sq_nonneg cornerCoord, hcorner]

/-- The converse at a given solution: a positive semidefinite bordered matrix has its
rate below the corner. -/
theorem solutionRate_le_of_borderedMatrix_posSemidef {corner : ℝ}
    {cross : Fin size → ℝ} {block : Matrix (Fin size) (Fin size) ℝ}
    {solution : Fin size → ℝ} (hsolves : block *ᵥ solution = cross)
    (hbordered : (borderedMatrix corner cross block).PosSemidef) :
    solution ⬝ᵥ cross ≤ corner := by
  set probeVec : Unit ⊕ Fin size → ℝ :=
    Sum.elim (fun _ : Unit => (1 : ℝ)) (-solution) with hprobeVec
  have hatTest := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbordered).2 probeVec
  rw [star_trivial, borderedMatrix_form_eq] at hatTest
  have hcornerCoord : probeVec (Sum.inl ()) = 1 := rfl
  have hlift : probeVec ∘ Sum.inr = -solution := rfl
  rw [hcornerCoord, hlift] at hatTest
  have hselfForm : (-solution) ⬝ᵥ (block *ᵥ (-solution)) = solution ⬝ᵥ cross := by
    rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, hsolves]
  have hcrossForm : cross ⬝ᵥ (-solution) = -(solution ⬝ᵥ cross) := by
    rw [dotProduct_neg, dotProduct_comm]
  rw [hselfForm, hcrossForm] at hatTest
  nlinarith [hatTest]

/-- **The bordered criterion is EXACT at every solution**: with `block ⪰ 0` and any
solution of `block *ᵥ solution = cross`, the bordered matrix is positive semidefinite iff
the rate is under the corner. -/
theorem borderedMatrix_posSemidef_iff_solutionRate_le {corner : ℝ}
    {cross : Fin size → ℝ} {block : Matrix (Fin size) (Fin size) ℝ}
    (hblock : block.PosSemidef) {solution : Fin size → ℝ}
    (hsolves : block *ᵥ solution = cross) :
    (borderedMatrix corner cross block).PosSemidef ↔ solution ⬝ᵥ cross ≤ corner :=
  ⟨solutionRate_le_of_borderedMatrix_posSemidef hsolves,
    borderedMatrix_posSemidef_of_solutionRate_le hblock hsolves⟩

end Bordered

/-! ### The literal "bordered PSD at every remaining atom" reading is dead

The first candidate one reaches for is intrinsic to the rank-`k` design: some
`k`-subset `T` dominates AND for every remaining atom `q` the bordered matrix
`Gram_{T ∪ {q}} − I` is positive semidefinite. That is `k+1` vectors in `ℝ^k`, so the
Gram is singular and the shift always has an eigenvalue `−1`: the condition holds
NOWHERE. Measured before mechanizing: 7872 `(T, q)` pairs, held 0 times, best
`lambda_min = −1.000000000000`. The theorem below is the general reason, and it is why
`BorderedSlackLifting` is stated one rank up. -/

/-- **More columns than rows kills the Gram shift.** For any real matrix with strictly
more columns than rows, `columnsᵀ * columns − 1` is never positive semidefinite: the
columns are linearly dependent, and the shift's form at a nontrivial relation is
`−|coefficients|² < 0`. -/
theorem not_posSemidef_transpose_mul_sub_one_of_overfull {rows cols : ℕ}
    (hovershoot : rows < cols) (columns : Matrix (Fin rows) (Fin cols) ℝ) :
    ¬ (columnsᵀ * columns - 1).PosSemidef := by
  intro hposSemidef
  have hnotInjective : ¬ Function.Injective columns.mulVecLin := by
    intro hinjective
    have hrankLe := LinearMap.finrank_le_finrank_of_injective hinjective
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_fin, Fintype.card_fin]
      at hrankLe
    omega
  rw [← LinearMap.ker_eq_bot] at hnotInjective
  obtain ⟨coeffs, hkernelMem, hcoeffsNe⟩ := (Submodule.ne_bot_iff _).mp hnotInjective
  have hannihilates : columns *ᵥ coeffs = 0 := LinearMap.mem_ker.mp hkernelMem
  have hform : coeffs ⬝ᵥ ((columnsᵀ * columns - 1) *ᵥ coeffs)
      = (columns *ᵥ coeffs) ⬝ᵥ (columns *ᵥ coeffs) - coeffs ⬝ᵥ coeffs := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_comm coeffs (columnsᵀ *ᵥ (columns *ᵥ coeffs)),
      dotProduct_mulVec_transpose]
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposSemidef).2 coeffs
  rw [star_trivial, hform, hannihilates] at hvalue
  have hcoeffsPos : 0 < coeffs ⬝ᵥ coeffs := dotProduct_self_pos hcoeffsNe
  simp only [zero_dotProduct] at hvalue
  linarith

/-- The reading, spelled out at the level of a vector family: `rank + 1` vectors in
`ℝ^rank` never have `Gram ⪰ I`. So "the coupling vector of every remaining atom
satisfies the bordered condition, INTRINSICALLY downstairs" is unsatisfiable at every
rank. -/
theorem not_posSemidef_gramShift_of_overfull {rank : ℕ}
    (vecs : Fin (rank + 1) → (Fin rank → ℝ)) :
    ¬ (Matrix.of (fun rowIdx colIdx => vecs rowIdx ⬝ᵥ vecs colIdx)
        - 1 : Matrix (Fin (rank + 1)) (Fin (rank + 1)) ℝ).PosSemidef := by
  have hgram : (Matrix.of (fun rowIdx colIdx => vecs rowIdx ⬝ᵥ vecs colIdx)
      : Matrix (Fin (rank + 1)) (Fin (rank + 1)) ℝ)
      = (Matrix.of fun coord slot => vecs slot coord)ᵀ
        * Matrix.of fun coord slot => vecs slot coord := by
    ext rowIdx colIdx
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct]
  rw [hgram]
  exact not_posSemidef_transpose_mul_sub_one_of_overfull (Nat.lt_succ_self rank) _

/-! ### The seventh conjunct, re-founded on named objects

Three definitions turn the `∀ testVec` conjunct of `LiftingLemma` into a rank-one
Loewner condition: the DIRECTION, the FORM, and the BUDGET. -/

section Reformulation

variable {m rank : ℕ}

/-- The **coupling vector** `r = Σ_{c ∈ S} ⟨u, g_c⟩ · B g_c` of a pivot direction and a
subset: the direction in which the projected domination is asked for slack. -/
def couplingVector (D : WeightedDesign m (rank + 1)) (pivotUnit : Fin (rank + 1) → ℝ)
    (deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ) (subset : Finset (Fin m)) :
    Fin rank → ℝ :=
  ∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) • (deflator *ᵥ D.atom c)

/-- The **lift budget** `A`. NOTE, against the wall file's prose: this is NOT the bare
pivot excess `leverage_p − 1`. It carries the subset's own overlaps with the pivot
direction, `A = leverage_p − 1 + Σ_{c ∈ S} ⟨u, g_c⟩²`, and that extra term is exactly
what lets `exists_all_certificates_but_discriminant` discharge the floor
subset-independently at a heavy pivot. Verified against the literal Lean formulas on 660
designs at ranks 3/4/5, worst error `3.6e-15`, and the induced rate identity
`rᵀ(G′−I)⁺r = Σ⟨u,g_c⟩² + s_Sᵀ(Gram′_S−I)⁺s_S` at worst relative error `5.1e-10`; after
cancellation the conjunct is the weight-free `rhatᵀ(Gram_S − I)⁺ rhat ≤ leverage_p − 1`
with `rhat_c = ⟨g_c, g_p⟩`. -/
def liftBudget (D : WeightedDesign m (rank + 1)) (pivot : Fin m)
    (pivotUnit : Fin (rank + 1) → ℝ) (subset : Finset (Fin m)) : ℝ :=
  (pivotUnit ⬝ᵥ D.atom pivot) ^ 2 + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1

theorem liftBudget_eq (D : WeightedDesign m (rank + 1)) (pivot : Fin m)
    (pivotUnit : Fin (rank + 1) → ℝ) (subset : Finset (Fin m)) :
    liftBudget D pivot pivotUnit subset
      = (pivotUnit ⬝ᵥ D.atom pivot) ^ 2
        + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1 := rfl

/-- The **projected gap** `G′ − I` of the selected subset in the compression: the form
whose slack the conjunct demands. -/
def projectedGap (D : WeightedDesign m (rank + 1))
    (deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ)
    (hcoisometry : deflator * deflatorᵀ = 1) (subset : Finset (Fin m)) :
    Matrix (Fin rank) (Fin rank) ℝ :=
  subsetSum (coisometryPushforward D deflator hcoisometry) subset - 1

/-- Projected domination IS positive semidefiniteness of the projected gap
(definitional). -/
theorem dominates_pushforward_iff_projectedGap_posSemidef
    (D : WeightedDesign m (rank + 1))
    (deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ)
    (hcoisometry : deflator * deflatorᵀ = 1) (subset : Finset (Fin m)) :
    Dominates (coisometryPushforward D deflator hcoisometry) subset
      ↔ (projectedGap D deflator hcoisometry subset).PosSemidef := Iff.rfl

theorem projectedGap_transpose (D : WeightedDesign m (rank + 1))
    (deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ)
    (hcoisometry : deflator * deflatorᵀ = 1) (subset : Finset (Fin m)) :
    (projectedGap D deflator hcoisometry subset)ᵀ
      = projectedGap D deflator hcoisometry subset := by
  rw [projectedGap, Matrix.transpose_sub, Matrix.transpose_one, subsetSum_transpose]

/-- The coupling vector pairs with a test vector exactly as the conjunct's cross sum. -/
theorem couplingVector_dotProduct (D : WeightedDesign m (rank + 1))
    (pivotUnit : Fin (rank + 1) → ℝ)
    (deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ) (subset : Finset (Fin m))
    (testVec : Fin rank → ℝ) :
    couplingVector D pivotUnit deflator subset ⬝ᵥ testVec
      = ∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
          * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) := by
  rw [couplingVector, sum_dotProduct]
  exact Finset.sum_congr rfl fun c _ => by rw [smul_dotProduct, smul_eq_mul]

/-- The projected gap's form is exactly the conjunct's constant term. -/
theorem projectedGap_form (D : WeightedDesign m (rank + 1))
    (deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ)
    (hcoisometry : deflator * deflatorᵀ = 1) (subset : Finset (Fin m))
    (testVec : Fin rank → ℝ) :
    testVec ⬝ᵥ (projectedGap D deflator hcoisometry subset *ᵥ testVec)
      = (∑ c ∈ subset, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
        - testVec ⬝ᵥ testVec := by
  rw [projectedGap, dominationGap_form]
  exact congrArg (· - testVec ⬝ᵥ testVec)
    (Finset.sum_congr rfl fun c _ => by rw [coisometryPushforward_atom])

/-- **The seventh conjunct, in the named objects.** The `∀ testVec` clause of
`LiftingLemma` is verbatim the rank-one Loewner condition
`couplingVector couplingVectorᵀ ⪯ liftBudget · projectedGap`. -/
theorem discriminantConjunct_iff_loewnerSlack (D : WeightedDesign m (rank + 1))
    (pivot : Fin m) (pivotUnit : Fin (rank + 1) → ℝ)
    (deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ)
    (hcoisometry : deflator * deflatorᵀ = 1) (subset : Finset (Fin m)) :
    (∀ testVec : Fin rank → ℝ,
        (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
            * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec)) ^ 2
          ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
                + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
              * ((∑ c ∈ subset, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
                - testVec ⬝ᵥ testVec))
      ↔ ∀ testVec : Fin rank → ℝ,
          (couplingVector D pivotUnit deflator subset ⬝ᵥ testVec) ^ 2
            ≤ liftBudget D pivot pivotUnit subset
              * (testVec
                ⬝ᵥ (projectedGap D deflator hcoisometry subset *ᵥ testVec)) := by
  constructor
  · intro hconjunct testVec
    rw [couplingVector_dotProduct, liftBudget_eq,
      projectedGap_form D deflator hcoisometry subset testVec]
    exact hconjunct testVec
  · intro hslack testVec
    have hhere := hslack testVec
    rw [couplingVector_dotProduct, liftBudget_eq,
      projectedGap_form D deflator hcoisometry subset testVec] at hhere
    exact hhere

/-- **The bordered lemma, consumed.** A solution of
`projectedGap *ᵥ solution = couplingVector` whose rate is under the budget discharges
the seventh conjunct. This is the only place a pseudo-inverse would classically appear;
here it is a solution vector, and the projected gap may be singular. -/
theorem discriminantConjunct_of_solutionRate_le (D : WeightedDesign m (rank + 1))
    (pivot : Fin m) (pivotUnit : Fin (rank + 1) → ℝ)
    {deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ}
    (hcoisometry : deflator * deflatorᵀ = 1) (subset : Finset (Fin m))
    (hprojectedDominates :
      Dominates (coisometryPushforward D deflator hcoisometry) subset)
    {couplingSolution : Fin rank → ℝ}
    (hsolves : projectedGap D deflator hcoisometry subset *ᵥ couplingSolution
      = couplingVector D pivotUnit deflator subset)
    (hrate : couplingSolution ⬝ᵥ couplingVector D pivotUnit deflator subset
      ≤ liftBudget D pivot pivotUnit subset)
    (testVec : Fin rank → ℝ) :
    (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
        * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec)) ^ 2
      ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
            + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
          * ((∑ c ∈ subset, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
            - testVec ⬝ᵥ testVec) :=
  (discriminantConjunct_iff_loewnerSlack D pivot pivotUnit deflator hcoisometry
      subset).mpr
    (rankOneForm_le_of_solutionRate_le hprojectedDominates hsolves hrate) testVec

/-- The converse at a given solution: the seventh conjunct forces the rate under the
budget. Together with the previous theorem the generalized-Schur reading is EXACT on the
whole range of the projected gap, singular or not. -/
theorem solutionRate_le_of_discriminantConjunct (D : WeightedDesign m (rank + 1))
    (pivot : Fin m) (pivotUnit : Fin (rank + 1) → ℝ)
    {deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ}
    (hcoisometry : deflator * deflatorᵀ = 1) (subset : Finset (Fin m))
    (hprojectedDominates :
      Dominates (coisometryPushforward D deflator hcoisometry) subset)
    (hfloor : 0 ≤ liftBudget D pivot pivotUnit subset)
    {couplingSolution : Fin rank → ℝ}
    (hsolves : projectedGap D deflator hcoisometry subset *ᵥ couplingSolution
      = couplingVector D pivotUnit deflator subset)
    (hconjunct : ∀ testVec : Fin rank → ℝ,
      (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
          * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec)) ^ 2
        ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
              + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
            * ((∑ c ∈ subset, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
              - testVec ⬝ᵥ testVec)) :
    couplingSolution ⬝ᵥ couplingVector D pivotUnit deflator subset
      ≤ liftBudget D pivot pivotUnit subset :=
  solutionRate_le_of_rankOneForm_le hprojectedDominates hfloor hsolves
    ((discriminantConjunct_iff_loewnerSlack D pivot pivotUnit deflator hcoisometry
      subset).mp hconjunct)

/-- **The seventh conjunct IS the conclusion, not an estimate of it.** At a fixed
`(pivot, subset)` pair with the deflation data and projected domination in hand, the
Loewner slack condition is EQUIVALENT to domination of `insert pivot subset` upstairs.
Both halves are already in the repo (`dominates_insert_of_projection_certificates` and
`discriminant_of_dominates_insert`); packaging them as an equivalence is what forbids
reading the wall as a lossy sufficient condition that a stronger induction hypothesis
could bound. Measured before mechanizing: 0 breaks over roughly 45000 exact
`(pivot, subset)` pairs (dim 3 at `m = 5..7`, dim 4 at `m = 8..11`, all-heavy, Parseval
verified as `G diag(t) G = G`), and 0/3325 verdict mismatches between this deflator form
and the weight-free projection form `r rᵀ ⪯ (P_pp(P_pp − t_p)/t_p)·M′`. -/
theorem dominates_insert_iff_loewnerSlack (D : WeightedDesign m (rank + 1))
    (pivot : Fin m) {pivotUnit : Fin (rank + 1) → ℝ}
    {deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ}
    (hcoisometry : deflator * deflatorᵀ = 1)
    (hunit : pivotUnit ⬝ᵥ pivotUnit = 1)
    (hsplit : deflatorᵀ * deflator + atomMatrix pivotUnit = 1)
    (hkill : deflator *ᵥ D.atom pivot = 0)
    (subset : Finset (Fin m)) (hnotMem : pivot ∉ subset)
    (hprojectedDominates :
      Dominates (coisometryPushforward D deflator hcoisometry) subset)
    (hfloor : 0 ≤ liftBudget D pivot pivotUnit subset) :
    Dominates D (insert pivot subset)
      ↔ ∀ testVec : Fin rank → ℝ,
          (couplingVector D pivotUnit deflator subset ⬝ᵥ testVec) ^ 2
            ≤ liftBudget D pivot pivotUnit subset
              * (testVec
                ⬝ᵥ (projectedGap D deflator hcoisometry subset *ᵥ testVec)) := by
  have hfloorRaw : 0 ≤ (pivotUnit ⬝ᵥ D.atom pivot) ^ 2
      + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1 := hfloor
  rw [← discriminantConjunct_iff_loewnerSlack D pivot pivotUnit deflator hcoisometry
    subset]
  constructor
  · intro hdominates testVec
    exact discriminant_of_dominates_insert D pivot hcoisometry hunit hsplit hkill
      subset hnotMem hfloorRaw hdominates testVec
  · intro hconjunct
    refine dominates_insert_of_projection_certificates D pivot hsplit hkill subset
      hnotMem (fun testVec => ?_) hfloorRaw hconjunct
    have hnonneg : 0 ≤ testVec
        ⬝ᵥ (projectedGap D deflator hcoisometry subset *ᵥ testVec) :=
      quadForm_nonneg_of_posSemidef hprojectedDominates testVec
    rw [projectedGap_form] at hnonneg
    linarith

end Reformulation

/-! ### The candidate strengthened hypothesis

`BorderedSlackLifting rank` is the generalized-Schur / pseudo-inverse form of the
Lifting Lemma: some `rank`-subset dominates in the compression AND the coupling vector
lies in the RANGE of the projected gap with rate under the lift budget. It is at least
as strong as the target (`gtzWeighted_succ_of_borderedSlackLifting`), by construction
not weaker, and the bordered lemma is what consumes it. -/

section Candidate

/-- **THE STRENGTHENED HYPOTHESIS.** For every weighted design in dimension `rank + 1`
there are a pivot, its deflation, a dominating `rank`-subset of the compression, AND a
SOLUTION vector realizing the generalized-Schur condition: the coupling vector is in the
range of the projected gap (`hsolves`) with rate under the lift budget (`hrate`).

The final two clauses are the quantitative slack the plain rank-`rank` hypothesis cannot
supply; they are strictly more than `projectedGap ⪰ 0`, and by
`borderedMatrix_posSemidef_iff_solutionRate_le` they are exactly the bordered-PSD
condition for `[[liftBudget, couplingVectorᵀ], [couplingVector, projectedGap]]`. -/
def BorderedSlackLifting (rank : ℕ) : Prop :=
  ∀ (size : ℕ) (D : WeightedDesign size (rank + 1)),
    ∃ (pivot : Fin size) (pivotUnit : Fin (rank + 1) → ℝ)
      (deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ)
      (hcoisometry : deflator * deflatorᵀ = 1)
      (subset : Finset (Fin size)) (couplingSolution : Fin rank → ℝ),
      deflatorᵀ * deflator + atomMatrix pivotUnit = 1
      ∧ deflator *ᵥ D.atom pivot = 0
      ∧ pivot ∉ subset
      ∧ subset.card = rank
      ∧ Dominates (coisometryPushforward D deflator hcoisometry) subset
      ∧ 0 ≤ liftBudget D pivot pivotUnit subset
      ∧ projectedGap D deflator hcoisometry subset *ᵥ couplingSolution
          = couplingVector D pivotUnit deflator subset
      ∧ couplingSolution ⬝ᵥ couplingVector D pivotUnit deflator subset
          ≤ liftBudget D pivot pivotUnit subset

/-- **(a): the strengthened hypothesis implies the Lifting Lemma.** The bordered lemma
turns the solution-and-rate pair into the seventh conjunct; the other six certificates
are carried verbatim. -/
theorem liftingLemma_of_borderedSlackLifting {rank : ℕ}
    (hslack : BorderedSlackLifting rank) : LiftingLemma rank := by
  intro size D
  obtain ⟨pivot, pivotUnit, deflator, hcoisometry, subset, couplingSolution, hsplit,
    hkill, hnotMem, hcard, hprojectedDominates, hfloor, hsolves, hrate⟩ := hslack size D
  refine ⟨pivot, pivotUnit, deflator, subset, hsplit, hkill, hnotMem, hcard,
    fun testVec => ?_, hfloor, fun testVec => ?_⟩
  · have hnonneg : 0 ≤ testVec
        ⬝ᵥ (projectedGap D deflator hcoisometry subset *ᵥ testVec) :=
      quadForm_nonneg_of_posSemidef hprojectedDominates testVec
    rw [projectedGap_form] at hnonneg
    linarith
  · exact discriminantConjunct_of_solutionRate_le D pivot pivotUnit hcoisometry subset
      hprojectedDominates hsolves hrate testVec

/-- **(a), the target itself**: the strengthened hypothesis at rank `rank` closes
weighted GTZ in dimension `rank + 1`, at every size. So the definition above is not
weaker than what the induction must produce — requirement (a) of the search. -/
theorem gtzWeighted_succ_of_borderedSlackLifting {rank : ℕ}
    (hslack : BorderedSlackLifting rank) (size : ℕ) : GtzWeighted size (rank + 1) :=
  gtzWeighted_succ_of_liftingLemma (liftingLemma_of_borderedSlackLifting hslack) size

/-- The all-rank consequence, for the record: strengthening at every rank collapses the
whole ladder exactly as `gtzWeightedAll_of_liftingLemma` does. -/
theorem gtzWeightedAll_of_borderedSlackLifting
    (hslack : ∀ rank, BorderedSlackLifting rank) : ∀ rank, GtzWeightedAll rank :=
  gtzWeightedAll_of_liftingLemma fun rank =>
    liftingLemma_of_borderedSlackLifting (hslack rank)

/-- **(b), STATED AND NOT PROVED.** Propagation of the strengthened hypothesis one rank
up. It is a `Prop` here, deliberately, and the missing ingredient is named precisely:

deflating a rank-`(rank+2)` design at a pivot produces a rank-`(rank+1)` design TOGETHER
WITH a Naimark co-vector `z` (`Σ t_c z_c² = 1`, `G′ diag(t) z = 0`), and the lift
condition at `(pivot, subset)` is `G′_S − I ⪰ w_S w_Sᵀ/(w_p² − Q(w))` for `w` in
`ker(G′ diag t)` — a condition on `z`, which deflation destroys. `BorderedSlackLifting
rank` is a statement about the rank-`(rank+1)` design ALONE, so it cannot see `w`;
scanning the deflation fibre at FIXED downstairs data produces fibre points with
DISJOINT and with EMPTY lifting sets (1783/1691/1400 exact fibre points over 23/23/24
designs gave 3–35, 3–86 and 8–122 distinct lifting sets, with 508/575/418 dead points,
and 0/23, 0/23, 0/24 designs had a subset lifting at every fibre point; under the
route's own `leverage ≥ rank` guarantee the dead points vanish but 2/11 and 1/6 designs
still have no uniformly-lifting subset). Conversely a hypothesis strong enough to see
`w` is not a strengthening: `(rank-(rank+1) design, fibre point)` is literally the same
data as `(rank-(rank+2) design, designated pivot)`, so it IS the target one rank up.
CORRECTED: this `Prop` is therefore EQUIVALENT to `(∀ size, GtzWeighted size (rank+1)) →
(∀ size, GtzWeighted size (rank+2))`, the original induction step verbatim — not a
weaker sufficient condition. Requirement (c) is met, not unmeetable:
`BorderedSlackLifting 0` and `BorderedSlackLifting 1` both hold (`gtz_rank_one`,
`gtz_rank_two`); the earlier "`BorderedSlackLifting 1` would already imply
`GtzWeighted size 3`" was an off-by-one — it yields `GtzWeighted size 2`.

Nothing below derives this. It is recorded so that a future consumer states its
dependence rather than assuming it. -/
def DoesPropagateBorderedSlack (rank : ℕ) : Prop :=
  BorderedSlackLifting rank → BorderedSlackLifting (rank + 1)

/-- Every `Fin 0`-indexed real matrix is positive semidefinite: both clauses of the
quadratic-form criterion quantify over an empty index. -/
theorem posSemidef_of_isEmptyIndex (mat : Matrix (Fin 0) (Fin 0) ℝ) : mat.PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun testVec => ?_⟩
  · show matᴴ = mat
    ext rowIndex; exact rowIndex.elim0
  · simp [dotProduct]

/-- The one quantitative content of the base case: a rank-one design has an atom whose
squared coordinate is at least one. This IS `Gtz.gtz_rank_one` read through
`Gtz.sum_sq_ge_of_dominates` at the dominating singleton. -/
theorem exists_one_le_sq_atom_of_rank_one (size : ℕ) (D : WeightedDesign size 1) :
    ∃ pivot : Fin size, 1 ≤ (D.atom pivot 0) ^ 2 := by
  obtain ⟨dominator, hcard, hdominates⟩ := gtz_rank_one size D
  obtain ⟨pivot, hpivot⟩ := Finset.card_eq_one.mp hcard
  refine ⟨pivot, ?_⟩
  have hsum := sum_sq_ge_of_dominates hdominates (fun _ => (1 : ℝ))
  rw [hpivot, Finset.sum_singleton] at hsum
  simpa [dotProduct] using hsum

/-- **Requirement (c), DISCHARGED — the base case is a theorem, not a hypothesis.**

At rank zero the deflator is a `Fin 0`-row matrix, so the coisometry, kill, solve and
rate clauses are `Subsingleton`-trivial and the projected domination is dimension-zero.
The ONLY surviving quantitative clause is the lift budget, and that clause IS rank-one
GTZ, which ships unconditionally as `Gtz.gtz_rank_one`. The header above recorded this
as true in prose (`BorderedSlackLifting 0` and `1` "both hold"); here it is kernel-checked,
which is what lets `Gtz.gtzWeightedAll_of_base_of_propagates` drop its base-case binder. -/
theorem borderedSlackLifting_zero : BorderedSlackLifting 0 := by
  intro size D
  obtain ⟨pivot, hleverage⟩ := exists_one_le_sq_atom_of_rank_one size D
  refine ⟨pivot, fun _ => (1 : ℝ), (0 : Matrix (Fin 0) (Fin 1) ℝ), ?_, (∅ : Finset (Fin size)),
    (fun slot => slot.elim0), ?_, ?_, (by simp), Finset.card_empty, ?_, ?_, ?_, ?_⟩
  · ext rowIndex; exact rowIndex.elim0
  · ext rowIndex colIndex
    fin_cases rowIndex; fin_cases colIndex
    simp [atomMatrix, Matrix.vecMulVec_apply]
  · ext rowIndex; exact rowIndex.elim0
  · exact posSemidef_of_isEmptyIndex _
  · show (0 : ℝ) ≤ liftBudget D pivot (fun _ => (1 : ℝ)) ∅
    rw [liftBudget_eq]
    simpa [dotProduct] using hleverage
  · ext rowIndex; exact rowIndex.elim0
  · show (fun slot : Fin 0 => slot.elim0) ⬝ᵥ _ ≤ liftBudget D pivot (fun _ => (1 : ℝ)) ∅
    rw [liftBudget_eq]
    simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty]
    simpa [dotProduct] using hleverage

/-- **The propagation Prop is exactly as strong as the ladder it would climb.** Given
propagation at every rank, GTZ falls at every rank — the shape the search was after,
with the ONE unproved input isolated as a hypothesis. The base case used to be a second
hypothesis; `Gtz.borderedSlackLifting_zero` discharges it, so this is now a conditional
on propagation alone. The NAME is unchanged so the audit pin keeps pointing at it. -/
theorem gtzWeightedAll_of_base_of_propagates
    (hpropagates : ∀ rank, DoesPropagateBorderedSlack rank) :
    ∀ rank, GtzWeightedAll rank := by
  have hall : ∀ rank, BorderedSlackLifting rank := by
    intro rank
    induction rank with
    | zero => exact borderedSlackLifting_zero
    | succ predRank ih => exact hpropagates predRank ih
  exact gtzWeightedAll_of_borderedSlackLifting hall

end Candidate

/-! ### The uniform-slack candidate, refuted at rank three

The other natural candidate asks for a dominating subset with a UNIFORM positive margin:
`S_C − I ⪰ slack · I` for some `slack > 0`. It fails requirement (b) at the first rank
where the step would fire, because the infimum of the margin is ATTAINED: the regular
tetrahedron `(4,3)` is an exact tie (`tetraDesign_isTie`), so every one of its four
dominating triples sits on the positive-semidefinite boundary. The same happens at rank
2 — the Sengupta–Pautov extremal `n = 3` design with `Gram = [[2,1,1],[1,2,−1],[1,−1,2]]`
and weights `1/3` has `det(Gram_S − I) = 0` on all three pairs, so
`max_S lambda_min = 0` exactly — and at `(7,3)`, where 20 of the 35 triples dominate and
every one of them is tight. -/

/-- **The uniform-slack hypothesis** at size `size` and rank `rank`: some `rank`-subset
dominates with a strictly positive uniform margin. -/
def HasUniformDominationSlack (size rank : ℕ) : Prop :=
  ∀ D : WeightedDesign size rank, ∃ (C : Finset (Fin size)) (slack : ℝ),
    C.card = rank ∧ 0 < slack
      ∧ (subsetSum D C - 1 - slack • (1 : Matrix (Fin rank) (Fin rank) ℝ)).PosSemidef

/-- Uniform slack upgrades weak domination to STRICT domination. -/
theorem posDef_of_uniformSlack {rank : ℕ} {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ}
    (hsymm : gapMatrixᵀ = gapMatrix) {slack : ℝ} (hslackPos : 0 < slack)
    (hshifted : (gapMatrix - slack • (1 : Matrix (Fin rank) (Fin rank) ℝ)).PosSemidef) :
    gapMatrix.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun testVec htestNe => ?_⟩
  have hshiftedForm := quadForm_nonneg_of_posSemidef hshifted testVec
  have hsplitForm : testVec
        ⬝ᵥ ((gapMatrix - slack • (1 : Matrix (Fin rank) (Fin rank) ℝ)) *ᵥ testVec)
      = testVec ⬝ᵥ (gapMatrix *ᵥ testVec) - slack * (testVec ⬝ᵥ testVec) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
  rw [hsplitForm] at hshiftedForm
  have hnormPos : 0 < testVec ⬝ᵥ testVec := dotProduct_self_pos htestNe
  rw [star_trivial]
  nlinarith [hshiftedForm, hnormPos, hslackPos]

/-- **Uniform slack is FALSE at rank three**, at the regular tetrahedron: it is an exact
tie, so no `3`-subset dominates strictly, while uniform slack would make one do so.
Hence propagation is unavailable for this candidate — requirement (b) fails at the very
first step `rank = 2 → rank = 3`, whatever requirement (c) says at rank 2 (where it also
fails, at the Sengupta–Pautov extremal). -/
theorem not_hasUniformDominationSlack_four_three : ¬ HasUniformDominationSlack 4 3 := by
  intro huniform
  obtain ⟨C, slack, hcard, hslackPos, hshifted⟩ := huniform tetraDesign
  have hsymm : (subsetSum tetraDesign C - 1)ᵀ = subsetSum tetraDesign C - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum_transpose]
  exact tetraDesign_no_strictDominator C hcard
    (posDef_of_uniformSlack hsymm hslackPos hshifted)

/-! ### The route's named residual, refuted

`Gtz.Reduction.RankInductionStep.HasHeavyPivotInDominator` is what the wall file records as
surviving: some dominating `(rank+1)`-subset contains an atom of leverage at least
`rank + 1`. As CODED that is false, and the witness below is an explicit all-heavy
`(4,3)` design — smaller than the unmechanized `m = 11`, `dim = 4` witness the wall file
describes.

Construction: a scaled regular simplex of three atoms in the `xy`-plane, each lifted by a
common `z`-component, plus one pivot atom on the `z`-axis. Parseval forces the weights;
the free parameter is the lift. Exactly:

* the pivot-free triple dominates iff `3·lift² ≥ 1`;
* every pivot-containing triple dominates iff `3·lift² ≤ 1`;

so at `3·lift² > 1` the unique dominator is pivot-free, and its atoms' leverage can be
pushed below `3`. Here `lift² = 3/8`, giving simplex leverage `23/8 = 2.875 < 3` and
pivot leverage `7/2 = 3.5 > 3`, with the pivot in no dominator at all.

The threshold is SHARP, and this is the calibration that matters: the largest leverage
achievable inside a dominator, over the whole family at rank `K − 1` in dimension `K`,
is `K − 1 + 1/K` (`7/3`, `13/4`, `21/5`, `31/6` at `K = 3,4,5,6`, each verified in exact
rationals; atom-splitting checked at `m = 4,5,6,7`; an independent SLSQP minimax at
dim 3 converges to `7/3` from above — `2.46254`, `2.37506`, `2.33755`, `2.33370` at
separations `1e-2`, `1e-3`, `1e-5`, `1e-7`). The coded demand is `K`, always above what
is achievable; the wall file's PROSE demand ("leverage at least the rank" = `K − 1`) is
NOT refuted, since `K − 1 + 1/K > K − 1`. So this is an off-by-one in the coded
threshold, and the sharp constant is `rank + 1/(rank+1)`. The failure set is thin —
0 failures in roughly 16000 all-heavy RANDOM designs, minimum achieved threshold `3.0536`
at dim 3, `m = 4` — which is why random search missed it. -/

section LightTopWitness

/-- Half the simplex side, in the `x` direction: `sqrt(5/8)`. -/
noncomputable def lightTopSide : ℝ := Real.sqrt (5 / 8)

/-- The simplex half-height in the `y` direction: `sqrt(15/8)`. -/
noncomputable def lightTopHeight : ℝ := Real.sqrt (15 / 8)

/-- The common `z`-lift of the three simplex atoms: `sqrt(3/8)`. Its square exceeds
`1/3`, which is exactly what pushes the pivot out of every dominator. -/
noncomputable def lightTopLift : ℝ := Real.sqrt (3 / 8)

/-- The pivot's `z`-coordinate: `sqrt(7/2)`, so the pivot's leverage is `7/2 > 3`. -/
noncomputable def lightTopPivotHeight : ℝ := Real.sqrt (7 / 2)

theorem lightTopSide_sq : lightTopSide ^ 2 = 5 / 8 := Real.sq_sqrt (by norm_num)

theorem lightTopHeight_sq : lightTopHeight ^ 2 = 15 / 8 := Real.sq_sqrt (by norm_num)

theorem lightTopLift_sq : lightTopLift ^ 2 = 3 / 8 := Real.sq_sqrt (by norm_num)

theorem lightTopPivotHeight_sq : lightTopPivotHeight ^ 2 = 7 / 2 :=
  Real.sq_sqrt (by norm_num)

/-- The four atoms: index `0` is the pivot on the `z`-axis, indices `1, 2, 3` the lifted
simplex. -/
noncomputable def lightTopAtom : Fin 4 → Fin 3 → ℝ :=
  ![![0, 0, lightTopPivotHeight],
    ![2 * lightTopSide, 0, lightTopLift],
    ![-lightTopSide, lightTopHeight, lightTopLift],
    ![-lightTopSide, -lightTopHeight, lightTopLift]]

theorem lightTopAtom_pivot : lightTopAtom 0 = ![0, 0, lightTopPivotHeight] := rfl

theorem lightTopAtom_one :
    lightTopAtom 1 = ![2 * lightTopSide, 0, lightTopLift] := rfl

theorem lightTopAtom_two :
    lightTopAtom 2 = ![-lightTopSide, lightTopHeight, lightTopLift] := rfl

theorem lightTopAtom_three :
    lightTopAtom 3 = ![-lightTopSide, -lightTopHeight, lightTopLift] := rfl

/-- **The witness design.** Parseval holds exactly: the `xy`-block is
`(4/15)·6·(5/8)·I = I` and `(4/15)·2·(15/8) = 1`, the `z` entry is
`(1/5)(7/2) + (4/15)·3·(3/8) = 7/10 + 3/10 = 1`, and every off-diagonal entry cancels by
the simplex's threefold symmetry. -/
noncomputable def lightTopDesign : WeightedDesign 4 3 where
  atom := lightTopAtom
  weight := ![1 / 5, 4 / 15, 4 / 15, 4 / 15]
  weight_pos := by intro index; fin_cases index <;> norm_num
  weight_sum_one := by simp [Fin.sum_univ_four]; norm_num
  isParseval := by
    ext rowIdx colIdx
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_four, smul_eq_mul]
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [lightTopAtom] <;>
      linarith [lightTopSide_sq, lightTopHeight_sq, lightTopLift_sq,
        lightTopPivotHeight_sq]

@[simp] theorem lightTopDesign_atom : lightTopDesign.atom = lightTopAtom := rfl

/-- The pivot's leverage is `7/2`, comfortably above the coded demand `3`. -/
theorem lightTopAtom_leverage_pivot : leverageOf (lightTopAtom 0) = 7 / 2 := by
  rw [lightTopAtom_pivot]
  simp only [leverageOf, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination lightTopPivotHeight_sq

theorem lightTopAtom_leverage_one : leverageOf (lightTopAtom 1) = 23 / 8 := by
  rw [lightTopAtom_one]
  simp only [leverageOf, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination 4 * lightTopSide_sq + lightTopLift_sq

theorem lightTopAtom_leverage_two : leverageOf (lightTopAtom 2) = 23 / 8 := by
  rw [lightTopAtom_two]
  simp only [leverageOf, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination lightTopSide_sq + lightTopHeight_sq + lightTopLift_sq

theorem lightTopAtom_leverage_three : leverageOf (lightTopAtom 3) = 23 / 8 := by
  rw [lightTopAtom_three]
  simp only [leverageOf, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination lightTopSide_sq + lightTopHeight_sq + lightTopLift_sq

/-- Every simplex atom has leverage `23/8`, strictly BELOW the coded demand `3`. -/
theorem lightTopAtom_leverage_simplex (index : Fin 4) (hnotPivot : index ≠ 0) :
    leverageOf (lightTopAtom index) = 23 / 8 := by
  fin_cases index
  · exact absurd rfl hnotPivot
  · exact lightTopAtom_leverage_one
  · exact lightTopAtom_leverage_two
  · exact lightTopAtom_leverage_three

theorem lightTopAtom_pairing_pivotOne :
    lightTopAtom 0 ⬝ᵥ lightTopAtom 1 = lightTopPivotHeight * lightTopLift := by
  rw [lightTopAtom_pivot, lightTopAtom_one]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem lightTopAtom_pairing_pivotTwo :
    lightTopAtom 0 ⬝ᵥ lightTopAtom 2 = lightTopPivotHeight * lightTopLift := by
  rw [lightTopAtom_pivot, lightTopAtom_two]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem lightTopAtom_pairing_pivotThree :
    lightTopAtom 0 ⬝ᵥ lightTopAtom 3 = lightTopPivotHeight * lightTopLift := by
  rw [lightTopAtom_pivot, lightTopAtom_three]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- Only the SQUARE of the pivot pairing is rational, and only the square enters the gap
form. -/
theorem lightTopPivotPairing_sq :
    (lightTopPivotHeight * lightTopLift) ^ 2 = 21 / 16 := by
  rw [mul_pow, lightTopPivotHeight_sq, lightTopLift_sq]
  norm_num

theorem lightTopAtom_pairing_oneTwo :
    lightTopAtom 1 ⬝ᵥ lightTopAtom 2 = -7 / 8 := by
  rw [lightTopAtom_one, lightTopAtom_two]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination (-2) * lightTopSide_sq + lightTopLift_sq

theorem lightTopAtom_pairing_oneThree :
    lightTopAtom 1 ⬝ᵥ lightTopAtom 3 = -7 / 8 := by
  rw [lightTopAtom_one, lightTopAtom_three]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination (-2) * lightTopSide_sq + lightTopLift_sq

theorem lightTopAtom_pairing_twoThree :
    lightTopAtom 2 ⬝ᵥ lightTopAtom 3 = -7 / 8 := by
  rw [lightTopAtom_two, lightTopAtom_three]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination lightTopSide_sq - lightTopHeight_sq + lightTopLift_sq

/-- **The pivot-free triple dominates**, and strictly: its gap is the diagonal form
`(11/4)x² + (11/4)y² + (1/8)z²`, the three cross terms cancelling by the simplex's
threefold symmetry. So the design satisfies weighted GTZ. -/
theorem lightTopDesign_dominates_simplexTriple :
    Dominates lightTopDesign {1, 2, 3} := by
  refine dominates_of_coercive lightTopDesign {1, 2, 3} fun probe => ?_
  have hexpand : (∑ c ∈ ({1, 2, 3} : Finset (Fin 4)),
        (lightTopDesign.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe
      = 11 / 4 * probe 0 ^ 2 + 11 / 4 * probe 1 ^ 2 + 1 / 8 * probe 2 ^ 2 := by
    rw [show ({1, 2, 3} : Finset (Fin 4)) = insert 1 (insert 2 {3}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, lightTopDesign_atom, lightTopAtom_one, lightTopAtom_two,
      lightTopAtom_three]
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination (6 * probe 0 ^ 2) * lightTopSide_sq
      + (2 * probe 1 ^ 2) * lightTopHeight_sq + (3 * probe 2 ^ 2) * lightTopLift_sq
  nlinarith [hexpand, sq_nonneg (probe 0), sq_nonneg (probe 1), sq_nonneg (probe 2)]

/-- **No pivot-containing triple dominates.** The gap form at the ONE simplex atom the
triple omits is `21/16 + 49/64 + 49/64 − 23/8 = −1/32 < 0`: the pivot's squared coupling
plus the two simplex pairings fall short of the omitted atom's leverage. This is where
`3·lift² > 1` enters — at `3·lift² = 1` the value is exactly `0`, and at `3·lift² < 1` it
is positive and the pivot-containing triples dominate instead. -/
theorem lightTopDesign_not_dominates_zeroOneTwo :
    ¬ Dominates lightTopDesign {0, 1, 2} := by
  intro hdominates
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2
    (lightTopAtom 3)
  rw [star_trivial, dominationGap_form,
    show ({0, 1, 2} : Finset (Fin 4)) = insert 0 (insert 1 {2}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    lightTopDesign_atom, lightTopAtom_pairing_pivotThree, lightTopPivotPairing_sq,
    lightTopAtom_pairing_oneThree, lightTopAtom_pairing_twoThree,
    ← leverageOf_eq_dotProduct, lightTopAtom_leverage_three] at hnonneg
  norm_num at hnonneg

theorem lightTopDesign_not_dominates_zeroOneThree :
    ¬ Dominates lightTopDesign {0, 1, 3} := by
  intro hdominates
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2
    (lightTopAtom 2)
  have hthreeTwo : lightTopAtom 3 ⬝ᵥ lightTopAtom 2 = -7 / 8 := by
    rw [dotProduct_comm]; exact lightTopAtom_pairing_twoThree
  rw [star_trivial, dominationGap_form,
    show ({0, 1, 3} : Finset (Fin 4)) = insert 0 (insert 1 {3}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    lightTopDesign_atom, lightTopAtom_pairing_pivotTwo, lightTopPivotPairing_sq,
    lightTopAtom_pairing_oneTwo, hthreeTwo,
    ← leverageOf_eq_dotProduct, lightTopAtom_leverage_two] at hnonneg
  norm_num at hnonneg

theorem lightTopDesign_not_dominates_zeroTwoThree :
    ¬ Dominates lightTopDesign {0, 2, 3} := by
  intro hdominates
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2
    (lightTopAtom 1)
  have htwoOne : lightTopAtom 2 ⬝ᵥ lightTopAtom 1 = -7 / 8 := by
    rw [dotProduct_comm]; exact lightTopAtom_pairing_oneTwo
  have hthreeOne : lightTopAtom 3 ⬝ᵥ lightTopAtom 1 = -7 / 8 := by
    rw [dotProduct_comm]; exact lightTopAtom_pairing_oneThree
  rw [star_trivial, dominationGap_form,
    show ({0, 2, 3} : Finset (Fin 4)) = insert 0 (insert 2 {3}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    lightTopDesign_atom, lightTopAtom_pairing_pivotOne, lightTopPivotPairing_sq,
    htwoOne, hthreeOne,
    ← leverageOf_eq_dotProduct, lightTopAtom_leverage_one] at hnonneg
  norm_num at hnonneg

/-- Three atoms out of four, with the pivot among them: exactly three subsets. -/
theorem pivotTriples_enumerated (C : Finset (Fin 4)) (hcard : C.card = 3)
    (hpivotMem : (0 : Fin 4) ∈ C) :
    C = {0, 1, 2} ∨ C = {0, 1, 3} ∨ C = {0, 2, 3} := by
  revert hcard hpivotMem
  revert C
  decide

/-- The pivot is the ONLY atom heavy enough for the coded demand. -/
theorem lightTopAtom_heavy_iff_pivot (index : Fin 4)
    (hheavy : (3 : ℝ) ≤ leverageOf (lightTopAtom index)) : index = 0 := by
  by_contra hnotPivot
  rw [lightTopAtom_leverage_simplex index hnotPivot] at hheavy
  norm_num at hheavy

/-- **THE ROUTE'S NAMED RESIDUAL IS FALSE AS CODED.** `HasHeavyPivotInDominator 4 2` demands
a dominating triple containing an atom of leverage at least `3`. In `lightTopDesign` the
only such atom is the pivot, the pivot lies in no dominating triple, and the unique
dominating triple carries leverage `23/8 = 2.875` throughout.

The design is all-heavy and satisfies GTZ (`lightTopDesign_dominates_simplexTriple`), so
this refutes the residual without touching the 1997 statement — which is exactly the
wall file's own reading of the residual as "formally stronger than GTZ". -/
theorem not_heavyPivotInDominator_four_two : ¬ HasHeavyPivotInDominator 4 2 := by
  intro hresidual
  obtain ⟨dominator, pivot, hcard, hpivotMem, hheavy, hdominates⟩ :=
    hresidual lightTopDesign
  have hpivotIsZero : pivot = 0 := by
    refine lightTopAtom_heavy_iff_pivot pivot ?_
    rw [← lightTopDesign_atom]
    norm_num at hheavy ⊢
    exact hheavy
  rw [hpivotIsZero] at hpivotMem
  rcases pivotTriples_enumerated dominator hcard hpivotMem with heq | heq | heq
  · exact lightTopDesign_not_dominates_zeroOneTwo (heq ▸ hdominates)
  · exact lightTopDesign_not_dominates_zeroOneThree (heq ▸ hdominates)
  · exact lightTopDesign_not_dominates_zeroTwoThree (heq ▸ hdominates)

/-- The design is all-heavy: leverages `7/2, 23/8, 23/8, 23/8`, every one above `1`. So
the refutation is not an artifact of a degenerate or dead atom — it lives inside the
class `GtzWeightedHeavy` quantifies over. -/
theorem lightTopDesign_allHeavy : AllHeavy lightTopDesign := by
  intro index
  rw [lightTopDesign_atom]
  rcases eq_or_ne index 0 with hisPivot | hnotPivot
  · rw [hisPivot, lightTopAtom_leverage_pivot]; norm_num
  · rw [lightTopAtom_leverage_simplex index hnotPivot]; norm_num

end LightTopWitness

end Gtz

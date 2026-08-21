/-
# The complete classification of rank-two ties

A rank-two exact tie is not a rare accident: it is a THREE-CLASS object, and this
file computes every one of its numbers.

**THEOREM.**  Let `D : WeightedDesign m 2` be an exact tie.  Then the atoms fall
into exactly THREE nonempty classes.  Two atoms are in the same class if and only
if they are PARALLEL.  Each class `A` carries one common leverage
`l_A = (1 + 1/T_A)/2`, where `T_A` is the weight of the class, and the three class
weights sum to one.  Every pair drawn from two DIFFERENT classes weakly dominates.
No pair inside a class dominates, and such a pair has gap determinant `-1/T_A`.

## The mechanism

Write `t_c` for the weight, `l_c` for the leverage and `J_cd` for the wedge
`g_c0 g_d1 - g_c1 g_d0`.  The whole file turns on one matrix,

    F_cd := t_c t_d (l_c + l_d - 1 - J_cd^2)          (`Gtz.tieCoupling`)

whose off-diagonal is MINUS the weighted gap determinant of the pair `{c,d}`
(`Gtz.det_pairGap_eq`), so `F_cd >= 0` says exactly that the pair does not
dominate strictly.  Three facts drive everything.

* **The row law** `sum_d F_cd = t_c` (`Gtz.sum_tieCoupling`).  It is two Parseval
  readings and nothing else, and it holds at EVERY rank-two design.
* **The Laplacian**.  A symmetric matrix with nonnegative entries and row sums `t`
  makes `diag t - F` positive semidefinite, by the identity
  `x.(diag t - F)x = (1/2) sum F_cd (x_c - x_d)^2`.  No spectral theorem.
* **The Veronese factorisation** `F = R R^T - s s^T` with `R` of THREE columns
  (`Gtz.normalizedCoupling_eq`), because the symmetric two by two matrices form a
  three-dimensional space.  The trace of the normalised coupling is `2k - 1 = 3`.

Those three facts pin the normalised coupling `N` to be the orthogonal projection
onto the column space of `R` (`Gtz.normalizedCoupling_eq_couplingProjection`).  The
argument is a trace sandwich, not an eigenvalue count: `1 - N` is positive
semidefinite with trace `m - 3` and dominates the identity on a subspace that the
projection `Pi` onto `ker R^T` sees, so `tr(1 - N) >= tr(Pi) = m - 3` with equality,
and a positive semidefinite matrix of zero trace is zero.

From idempotency the rest is short.  `S := diag(t)^-1 F` is stochastic, idempotent
and entrywise nonnegative with a positive diagonal, so `c ~ d :<-> F_cd > 0` is an
EQUIVALENCE relation whose classes are cliques.  A Perron step run through the
projection (`Gtz.tieCoupling_mul_classWeight`) forces each block to be the rank-one
`F_cd = t_c t_d / T_A`, and then the DIAGONAL of that formula reads
`2 l_c - 1 = 1/T_A` while its OFF-DIAGONAL reads `J_cd = 0`.  Same class, parallel,
equal leverage: one line each.  The class count is the trace, `3 = sum_c t_c / T_c`.

## What is landed here

* `Gtz.rankTwoTieClassification` — the classification, all fields.
* `Gtz.hingeHoldsAtSize_rank_two` — `HingeHoldsAtSize m 2` for every `m >= 4`.
  The tree already reaches this conclusion by the Bloch-chart route
  (`Gtz.not_isTie_of_fourNonParallel`); the CLASSIFICATION is strictly more, and
  this corollary is a two-line consequence of it, not a reproof.
* `Gtz.weight_mul_two_leverage_sub_one_le_one` — the per-atom leverage cap
  `t_d (2 l_d - 1) <= 1`.  It needs only the row law and entrywise nonnegativity,
  so it holds with NO tie hypothesis, at every rank-two design with no strictly
  dominating pair.
* `Gtz.four_mul_size_le_sum_card_dominatingPartners` — at least `2 size - 3`
  unordered pairs weakly dominate, and
  `Gtz.fourteen_le_sum_card_dominatingPartners_five` reads that as SEVEN pairs at
  five atoms.
* `Gtz.rankTwoTie_three_atoms` — at three atoms all three classes are singletons,
  all three pairs dominate, and `t_c (2 l_c - 1) = 1`, that is
  `l_c = (1 + t_c)/(2 t_c)`.  The weights are NOT forced uniform.
* `Gtz.planeShadow_three_classes` and
  `Gtz.planeShadow_exists_frameBracket_eq_zero` — the rank-THREE payload.  Every
  plane shadow of a rank-three design is a rank-two design
  (`Gtz.inPlaneRestriction`), and the shadow wedge is the frame bracket, which the
  tree reads as the triple bracket against the normal
  (`Gtz.pairBracket_inPlaneRestriction_eq_frameOrientation_mul_tripleBracket`).  So
  the classification reads on the whole sphere of normals.

## What is NOT landed, and why not

Nothing lifts to rank three, and the obstruction is measured, not guessed.  At rank
`k` the matrix with row sums `t` is `P o P - (1/(k-1)) d d^T`, and at the `(5,3)`
diamond (`t = 1/5`, share `0.65`) its DIAGONAL already exceeds its row sum, so it
is not entrywise nonnegative and the Laplacian step dies.  Three ingredients are
rank-two only: pairs ARE the selections, `rank (P o P) <= dim Sym^2 R^k = 3` only
at `k = 2`, and `tr S = 2k - 1 = 3` only at `k = 2`.

Numerics behind the file, at exact ties found by direct minimisation of
`max over pairs of lambda_min` (the TRUE maximum, not a smoothed surrogate) at
four, five and six atoms: row sums of `F` correct to `2e-16`, `F >= 0` entrywise,
`tr(diag(t)^-1 F) = 3.000000000000`, exactly three classes at every minimiser, and
per class `S_A = (1 + T_A)/2` and `l_c = (1 + 1/T_A)/2` to nine digits.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Design.FrameConservation
import Gtz.Design.InPlaneRestriction
import Gtz.Design.StratumEmptinessLedger
import Gtz.Quantitative.ChartHadamard
import Gtz.Reduction.CompactnessReduction
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## Part A: the wedge dictionary

At rank two the pair gap has a two-term determinant, and the term that is not the
leverage sum is the SQUARE OF THE WEDGE.  Every inequality below is an inequality
about that one scalar. -/

/-- Two planar vectors agree when their two coordinates agree. -/
private theorem funext_two {leftVec rightVec : Fin 2 → ℝ}
    (hzero : leftVec 0 = rightVec 0) (hone : leftVec 1 = rightVec 1) : leftVec = rightVec := by
  funext index
  fin_cases index
  · exact hzero
  · exact hone

/-- The wedge `u_0 v_1 - u_1 v_0` of two planar vectors: the determinant of the two
by two matrix with those columns. -/
def planeWedge (leftVec rightVec : Fin 2 → ℝ) : ℝ :=
  leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0

@[simp] theorem planeWedge_self (vec : Fin 2 → ℝ) : planeWedge vec vec = 0 := by
  simp only [planeWedge]; ring

theorem planeWedge_comm (leftVec rightVec : Fin 2 → ℝ) :
    planeWedge leftVec rightVec = -planeWedge rightVec leftVec := by
  simp only [planeWedge]; ring

theorem sq_planeWedge_comm (leftVec rightVec : Fin 2 → ℝ) :
    planeWedge leftVec rightVec ^ 2 = planeWedge rightVec leftVec ^ 2 := by
  rw [planeWedge_comm]; ring

theorem planeWedge_smul_right (scale : ℝ) (leftVec rightVec : Fin 2 → ℝ) :
    planeWedge leftVec (scale • rightVec) = scale * planeWedge leftVec rightVec := by
  simp only [planeWedge, Pi.smul_apply, smul_eq_mul]; ring

/-- **Lagrange at rank two.**  Pairing squared plus wedge squared is the product of
the leverages.  This one identity turns every statement about the pair Gram into a
statement about the wedge. -/
theorem sq_dotProduct_add_sq_planeWedge (leftVec rightVec : Fin 2 → ℝ) :
    (leftVec ⬝ᵥ rightVec) ^ 2 + planeWedge leftVec rightVec ^ 2
      = leverageOf leftVec * leverageOf rightVec := by
  simp only [planeWedge, leverageOf, dotProduct, Fin.sum_univ_two]
  ring

/-- A vanishing wedge against a nonzero vector makes the second vector a multiple of
the first. -/
theorem exists_smul_of_planeWedge_eq_zero {leftVec rightVec : Fin 2 → ℝ}
    (hnonzero : leftVec ≠ 0) (hwedge : planeWedge leftVec rightVec = 0) :
    ∃ scale : ℝ, rightVec = scale • leftVec := by
  simp only [planeWedge, sub_eq_zero] at hwedge
  by_cases hfirst : leftVec 0 = 0
  · have hsecond : leftVec 1 ≠ 0 := by
      intro hzero
      exact hnonzero (funext_two (by simpa using hfirst) (by simpa using hzero))
    have hzeroCoord : rightVec 0 = 0 := by
      rw [hfirst] at hwedge
      rcases mul_eq_zero.mp (by linarith [hwedge] : leftVec 1 * rightVec 0 = 0) with h | h
      · exact absurd h hsecond
      · exact h
    exact ⟨rightVec 1 / leftVec 1, funext_two
      (by simp only [Pi.smul_apply, smul_eq_mul, hfirst, hzeroCoord, mul_zero])
      (by simp only [Pi.smul_apply, smul_eq_mul]; field_simp)⟩
  · exact ⟨rightVec 0 / leftVec 0,
      funext_two (by simp only [Pi.smul_apply, smul_eq_mul]; field_simp)
      (by simp only [Pi.smul_apply, smul_eq_mul]; field_simp; linarith [hwedge])⟩

/-- **The pair gap determinant at rank two.**  For distinct atoms the gap
`S_{c,d} - 1` has determinant `J^2 - (l_c + l_d - 1)`.  Weak domination is
`det >= 0` under a nonnegative trace, so the WHOLE domination question for a pair is
the sign of `l_c + l_d - 1 - J^2`. -/
theorem det_pairGap_eq (D : WeightedDesign m 2) {atomFirst atomSecond : Fin m}
    (hdistinct : atomFirst ≠ atomSecond) :
    (subsetSum D {atomFirst, atomSecond} - 1).det
      = planeWedge (D.atom atomFirst) (D.atom atomSecond) ^ 2
        - (leverageOf (D.atom atomFirst) + leverageOf (D.atom atomSecond) - 1) := by
  rw [subsetSum, Finset.sum_pair hdistinct]
  simp only [Matrix.det_fin_two, atomMatrix, Matrix.vecMulVec_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.one_apply, planeWedge, leverageOf, Fin.sum_univ_two,
    Fin.isValue, ne_eq, Fin.zero_eta, Fin.mk_one, one_ne_zero, not_false_eq_true,
    if_true, if_false, zero_ne_one, reduceCtorEq]
  norm_num
  ring

/-- The gap trace at rank two is `l_c + l_d - 2`. -/
theorem trace_pairGap_eq (D : WeightedDesign m 2) {atomFirst atomSecond : Fin m}
    (hdistinct : atomFirst ≠ atomSecond) :
    (subsetSum D {atomFirst, atomSecond} - 1) 0 0
        + (subsetSum D {atomFirst, atomSecond} - 1) 1 1
      = leverageOf (D.atom atomFirst) + leverageOf (D.atom atomSecond) - 2 := by
  rw [subsetSum, Finset.sum_pair hdistinct]
  simp only [atomMatrix, Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.one_apply, leverageOf, Fin.sum_univ_two, Fin.isValue, if_true]
  ring

/-- The gap of any subset is symmetric. -/
theorem pairGap_transpose (D : WeightedDesign m 2) (selected : Finset (Fin m)) :
    (subsetSum D selected - 1)ᵀ = subsetSum D selected - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by
    simp only [atomMatrix, Matrix.transpose_vecMulVec]

/-- A two by two symmetric matrix with positive determinant and nonnegative trace is
positive definite: the strict half of the tree's
`Gtz.posSemidef_two_iff_of_trace_pos`, by the same sum of squares. -/
theorem posDef_two_of_det_pos_of_trace_nonneg {gapMatrix : Matrix (Fin 2) (Fin 2) ℝ}
    (hsymm : gapMatrixᵀ = gapMatrix) (hdet : 0 < gapMatrix.det)
    (htrace : 0 ≤ gapMatrix 0 0 + gapMatrix 1 1) : gapMatrix.PosDef := by
  have hcross : gapMatrix 1 0 = gapMatrix 0 1 := by
    have := congrFun (congrFun hsymm 0) 1
    rwa [Matrix.transpose_apply] at this
  rw [Matrix.det_fin_two, hcross] at hdet
  have hproduct : 0 < gapMatrix 0 0 * gapMatrix 1 1 := by
    nlinarith [sq_nonneg (gapMatrix 0 1)]
  have hcornerPos : 0 < gapMatrix 0 0 := by
    rcases lt_trichotomy (gapMatrix 0 0) 0 with hneg | hzero | hpos
    · exfalso
      have hother : gapMatrix 1 1 < 0 := by nlinarith
      linarith
    · exfalso; rw [hzero] at hproduct; simp at hproduct
    · exact hpos
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun testVec hnonzero => ?_⟩
  rw [star_trivial, dot_mulVec_two, hcross]
  have hcoord : testVec 0 ≠ 0 ∨ testVec 1 ≠ 0 := by
    by_contra hcontra
    push_neg at hcontra
    exact hnonzero (funext_two (by simpa using hcontra.1) (by simpa using hcontra.2))
  have hkey : 0 < gapMatrix 0 0 *
      (gapMatrix 0 0 * testVec 0 ^ 2 + (gapMatrix 0 1 + gapMatrix 0 1) * (testVec 0 * testVec 1)
        + gapMatrix 1 1 * testVec 1 ^ 2) := by
    rcases eq_or_ne (testVec 1) 0 with hzero | hnz
    · have hfirst : testVec 0 ≠ 0 := by
        rcases hcoord with h | h
        · exact h
        · exact absurd hzero h
      have hsq : 0 < testVec 0 ^ 2 := by positivity
      have hcornerSq : 0 < gapMatrix 0 0 * gapMatrix 0 0 := mul_pos hcornerPos hcornerPos
      rw [hzero]
      nlinarith [mul_pos hcornerSq hsq]
    · have hsq : 0 < testVec 1 ^ 2 := by positivity
      nlinarith [sq_nonneg (gapMatrix 0 0 * testVec 0 + gapMatrix 0 1 * testVec 1),
        mul_pos hdet hsq]
  nlinarith [hkey, hcornerPos]

/-! ## Part B: the coupling matrix and its row law -/

/-- **The coupling of a pair**, `F_cd = t_c t_d (l_c + l_d - 1 - J_cd^2)`.  Off the
diagonal it is minus the weighted gap determinant of the pair, so nonnegativity says
exactly that the pair does not dominate strictly.  On the diagonal it is
`t_c^2 (2 l_c - 1)`. -/
noncomputable def tieCoupling (D : WeightedDesign m 2) (atomFirst atomSecond : Fin m) : ℝ :=
  D.weight atomFirst * D.weight atomSecond *
    (leverageOf (D.atom atomFirst) + leverageOf (D.atom atomSecond) - 1
      - planeWedge (D.atom atomFirst) (D.atom atomSecond) ^ 2)

theorem tieCoupling_comm (D : WeightedDesign m 2) (atomFirst atomSecond : Fin m) :
    tieCoupling D atomFirst atomSecond = tieCoupling D atomSecond atomFirst := by
  simp only [tieCoupling, sq_planeWedge_comm (D.atom atomFirst) (D.atom atomSecond)]
  ring

theorem tieCoupling_self (D : WeightedDesign m 2) (atomIndex : Fin m) :
    tieCoupling D atomIndex atomIndex
      = D.weight atomIndex ^ 2 * (2 * leverageOf (D.atom atomIndex) - 1) := by
  simp only [tieCoupling, planeWedge_self]
  ring

/-- The coupling is minus the weighted gap determinant. -/
theorem tieCoupling_eq_neg_det (D : WeightedDesign m 2) {atomFirst atomSecond : Fin m}
    (hdistinct : atomFirst ≠ atomSecond) :
    tieCoupling D atomFirst atomSecond
      = -(D.weight atomFirst * D.weight atomSecond
          * (subsetSum D {atomFirst, atomSecond} - 1).det) := by
  rw [det_pairGap_eq D hdistinct, tieCoupling]
  ring

/-- **The wedge row law.**  `sum_d t_d J_cd^2 = l_c`, at every rank-two design.  It
is Lagrange fed by the tree's two Parseval readings: the pairing row law
`Gtz.sum_weight_mul_sq_atomPairing` and the trace `Gtz.sum_weighted_leverage`. -/
theorem sum_weight_mul_sq_planeWedge (D : WeightedDesign m 2) (atomIndex : Fin m) :
    ∑ otherIndex, D.weight otherIndex
        * planeWedge (D.atom atomIndex) (D.atom otherIndex) ^ 2
      = leverageOf (D.atom atomIndex) := by
  have hsplit : ∀ otherIndex : Fin m,
      D.weight otherIndex * planeWedge (D.atom atomIndex) (D.atom otherIndex) ^ 2
        = leverageOf (D.atom atomIndex)
            * (D.weight otherIndex * leverageOf (D.atom otherIndex))
          - D.weight otherIndex * (D.atom atomIndex ⬝ᵥ D.atom otherIndex) ^ 2 := by
    intro otherIndex
    linear_combination D.weight otherIndex
      * sq_dotProduct_add_sq_planeWedge (D.atom atomIndex) (D.atom otherIndex)
  rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) => hsplit otherIndex,
    Finset.sum_sub_distrib, ← Finset.mul_sum, sum_weighted_leverage D,
    sum_weight_mul_sq_atomPairing D atomIndex]
  push_cast
  ring

/-- **The row law of the coupling.**  `sum_d F_cd = t_c`, at every rank-two design,
with no hypothesis at all: two Parseval readings and the wedge row law. -/
theorem sum_tieCoupling (D : WeightedDesign m 2) (atomIndex : Fin m) :
    ∑ otherIndex, tieCoupling D atomIndex otherIndex = D.weight atomIndex := by
  have hsplit : ∀ otherIndex : Fin m,
      tieCoupling D atomIndex otherIndex
        = D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1) * D.weight otherIndex
          + D.weight atomIndex * (D.weight otherIndex * leverageOf (D.atom otherIndex))
          - D.weight atomIndex
              * (D.weight otherIndex
                  * planeWedge (D.atom atomIndex) (D.atom otherIndex) ^ 2) := by
    intro otherIndex
    simp only [tieCoupling]
    ring
  rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) => hsplit otherIndex,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, D.weight_sum_one, sum_weighted_leverage D,
    sum_weight_mul_sq_planeWedge D atomIndex]
  push_cast
  ring

/-- The total wedge energy of a rank-two design is exactly two. -/
theorem sum_sum_weight_mul_weight_mul_sq_planeWedge (D : WeightedDesign m 2) :
    ∑ atomIndex, ∑ otherIndex, D.weight atomIndex * (D.weight otherIndex
        * planeWedge (D.atom atomIndex) (D.atom otherIndex) ^ 2) = 2 := by
  have hrow : ∀ atomIndex : Fin m,
      ∑ otherIndex, D.weight atomIndex * (D.weight otherIndex
          * planeWedge (D.atom atomIndex) (D.atom otherIndex) ^ 2)
        = D.weight atomIndex * leverageOf (D.atom atomIndex) := by
    intro atomIndex
    rw [← Finset.mul_sum, sum_weight_mul_sq_planeWedge D atomIndex]
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hrow atomIndex,
    sum_weighted_leverage D]
  norm_num

/-- **Every rank-two design carries two non-parallel atoms**, because the wedge
energy is two and not zero. -/
theorem exists_planeWedge_ne_zero (D : WeightedDesign m 2) :
    ∃ atomFirst atomSecond : Fin m,
      planeWedge (D.atom atomFirst) (D.atom atomSecond) ≠ 0 := by
  by_contra hcontra
  push_neg at hcontra
  have hzero : ∑ atomIndex, ∑ otherIndex, D.weight atomIndex * (D.weight otherIndex
      * planeWedge (D.atom atomIndex) (D.atom otherIndex) ^ 2) = 0 :=
    Finset.sum_eq_zero fun atomIndex _ => Finset.sum_eq_zero fun otherIndex _ => by
      rw [hcontra atomIndex otherIndex]; ring
  rw [sum_sum_weight_mul_weight_mul_sq_planeWedge D] at hzero
  norm_num at hzero

/-! ## Part C: nonnegativity at a tie, and the free leverage cap

The hypothesis carried from here on is `NoStrictPair`: no pair dominates strictly.
A tie has it by definition, and it is strictly weaker than a tie because it does not
ask for a dominating pair to exist. -/

/-- No pair of the design dominates STRICTLY: the second clause of `Gtz.IsTie` at
rank two, where the `k`-subsets are the pairs. -/
def NoStrictPair (D : WeightedDesign m 2) : Prop :=
  ∀ atomFirst atomSecond : Fin m, atomFirst ≠ atomSecond →
    ¬ (subsetSum D {atomFirst, atomSecond} - 1).PosDef

/-- **The coupling is nonnegative.**  Heaviness makes the gap trace nonnegative, so a
positive gap determinant would make the pair dominate strictly.  This is the ONLY
place the domination hypothesis is spent. -/
theorem tieCoupling_nonneg (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (atomFirst atomSecond : Fin m) :
    0 ≤ tieCoupling D atomFirst atomSecond := by
  rcases eq_or_ne atomFirst atomSecond with rfl | hdistinct
  · rw [tieCoupling_self]
    have := hheavy atomFirst
    have hweight := D.weight_pos atomFirst
    nlinarith
  · rw [tieCoupling_eq_neg_det D hdistinct]
    have hdetNonpos : (subsetSum D {atomFirst, atomSecond} - 1).det ≤ 0 := by
      by_contra hcontra
      push_neg at hcontra
      refine hnostrict atomFirst atomSecond hdistinct
        (posDef_two_of_det_pos_of_trace_nonneg (pairGap_transpose D _) hcontra ?_)
      rw [trace_pairGap_eq D hdistinct]
      linarith [hheavy atomFirst, hheavy atomSecond]
    have hweights := mul_pos (D.weight_pos atomFirst) (D.weight_pos atomSecond)
    nlinarith

/-- **THE PER-ATOM LEVERAGE CAP**, `t_d (2 l_d - 1) <= 1`.  It uses the row law and
entrywise nonnegativity ONLY, so it holds at every rank-two design with no strictly
dominating pair, whether or not that design is a tie and whether or not a dominating
pair exists.  The proof is three lines: the diagonal entry of the coupling is one
term of a row whose total is `t_d`, and every other term is nonnegative. -/
theorem weight_mul_two_leverage_sub_one_le_one (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (atomIndex : Fin m) :
    D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1) ≤ 1 := by
  have hdiag : tieCoupling D atomIndex atomIndex
      ≤ ∑ otherIndex, tieCoupling D atomIndex otherIndex :=
    Finset.single_le_sum
      (fun otherIndex _ => tieCoupling_nonneg D hheavy hnostrict atomIndex otherIndex)
      (Finset.mem_univ atomIndex)
  rw [sum_tieCoupling D atomIndex, tieCoupling_self] at hdiag
  have hweight := D.weight_pos atomIndex
  nlinarith

/-- The cap written as a ceiling on the leverage: `l_d <= (1 + t_d)/(2 t_d)`. -/
theorem leverage_le_of_noStrictPair (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (atomIndex : Fin m) :
    leverageOf (D.atom atomIndex) ≤ (1 + D.weight atomIndex) / (2 * D.weight atomIndex) := by
  have hcap := weight_mul_two_leverage_sub_one_le_one D hheavy hnostrict atomIndex
  have hweight := D.weight_pos atomIndex
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **Parallel atoms couple strictly positively.**  This is why the classification
never separates a parallel pair. -/
theorem tieCoupling_pos_of_planeWedge_eq_zero (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    {atomFirst atomSecond : Fin m}
    (hwedge : planeWedge (D.atom atomFirst) (D.atom atomSecond) = 0) :
    0 < tieCoupling D atomFirst atomSecond := by
  have hpos : (0 : ℝ) < leverageOf (D.atom atomFirst) + leverageOf (D.atom atomSecond) - 1
      - planeWedge (D.atom atomFirst) (D.atom atomSecond) ^ 2 := by
    rw [hwedge]
    have := hheavy atomFirst
    have := hheavy atomSecond
    nlinarith
  exact mul_pos (mul_pos (D.weight_pos atomFirst) (D.weight_pos atomSecond)) hpos

/-! ## Part D: three pairwise non-parallel atoms

The Veronese factorisation of Part E has three columns and needs them independent,
which is exactly this statement. -/

/-- Atoms of a heavy design are nonzero. -/
theorem atom_ne_zero_of_heavy (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex)) (atomIndex : Fin m) :
    D.atom atomIndex ≠ 0 := by
  intro hzero
  have hlev := hheavy atomIndex
  rw [hzero] at hlev
  simp only [leverageOf, Pi.zero_apply] at hlev
  norm_num at hlev

/-- The wedge against a fixed vector transports along parallelism, division-free. -/
theorem leverage_mul_sq_planeWedge_transport {vecBase vecPivot vecPartner : Fin 2 → ℝ}
    {scale : ℝ} (hparallel : vecPartner = scale • vecPivot) :
    leverageOf vecPivot * planeWedge vecBase vecPartner ^ 2
      = leverageOf vecPartner * planeWedge vecBase vecPivot ^ 2 := by
  subst hparallel
  rw [planeWedge_smul_right]
  simp only [leverageOf, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  ring

/-- **The block wedge law.**  If every atom outside a block is parallel to the pivot
and every atom inside it is parallel to the partner, then the wedge row law at the
pivot reads the block's SHARE against the pivot-partner wedge. -/
theorem block_wedge_row (D : WeightedDesign m 2) {basePivot basePartner : Fin m}
    (block : Finset (Fin m))
    (houtside : ∀ atomIndex ∉ block, planeWedge (D.atom basePivot) (D.atom atomIndex) = 0)
    (hinside : ∀ atomIndex ∈ block, ∃ scale : ℝ, D.atom atomIndex = scale • D.atom basePartner) :
    leverageOf (D.atom basePartner) * leverageOf (D.atom basePivot)
      = (∑ atomIndex ∈ block, D.weight atomIndex * leverageOf (D.atom atomIndex))
          * planeWedge (D.atom basePivot) (D.atom basePartner) ^ 2 := by
  have hrow := sum_weight_mul_sq_planeWedge D basePivot
  have hstep : leverageOf (D.atom basePartner) * leverageOf (D.atom basePivot)
      = ∑ atomIndex, leverageOf (D.atom basePartner)
          * (D.weight atomIndex * planeWedge (D.atom basePivot) (D.atom atomIndex) ^ 2) := by
    rw [← Finset.mul_sum, hrow]
  have hrestrict : ∑ atomIndex ∈ block, leverageOf (D.atom basePartner)
        * (D.weight atomIndex * planeWedge (D.atom basePivot) (D.atom atomIndex) ^ 2)
      = ∑ atomIndex, leverageOf (D.atom basePartner)
          * (D.weight atomIndex * planeWedge (D.atom basePivot) (D.atom atomIndex) ^ 2) := by
    refine Finset.sum_subset (Finset.subset_univ block) fun atomIndex _ hnot => ?_
    rw [houtside atomIndex hnot]
    ring
  rw [hstep, ← hrestrict, Finset.sum_mul]
  refine Finset.sum_congr rfl fun atomIndex hmem => ?_
  obtain ⟨scale, hscale⟩ := hinside atomIndex hmem
  linear_combination D.weight atomIndex
    * leverage_mul_sq_planeWedge_transport (vecBase := D.atom basePivot) hscale

/-- **Every rank-two design with no strictly dominating pair carries THREE pairwise
non-parallel atoms.**  Suppose not.  Two atoms are non-parallel and every other is
parallel to one of them, so the index set splits into two blocks.  The block wedge
law reads the two shares against each other and forces both to be one, hence the two
base atoms ORTHOGONAL and every cross pair orthogonal.  A cross pair of orthogonal
atoms has coupling `-t_c t_d (l_c - 1)(l_d - 1)`, so heaviness kills every cross
product of excesses, and multiplying the two block excesses gives `T_1 T_2 = 0`,
which positive weights forbid. -/
theorem exists_three_pairwise_nonParallel (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) :
    ∃ atomFirst atomSecond atomThird : Fin m,
      planeWedge (D.atom atomFirst) (D.atom atomSecond) ≠ 0 ∧
      planeWedge (D.atom atomFirst) (D.atom atomThird) ≠ 0 ∧
      planeWedge (D.atom atomSecond) (D.atom atomThird) ≠ 0 := by
  classical
  by_contra hcontra
  push_neg at hcontra
  obtain ⟨baseFirst, baseSecond, hbase⟩ := exists_planeWedge_ne_zero D
  have hdichotomy : ∀ atomIndex : Fin m,
      planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0 ∨
      planeWedge (D.atom baseSecond) (D.atom atomIndex) = 0 := by
    intro atomIndex
    by_cases hfirst : planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0
    · exact Or.inl hfirst
    · exact Or.inr (hcontra baseFirst baseSecond atomIndex hbase hfirst)
  -- The two blocks: parallel to the first base atom, and the rest.
  have hmemFirst : baseFirst ∈ Finset.univ.filter
      fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0 := by
    simp
  have hmemSecond : baseSecond ∈ Finset.univ.filter
      fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0 := by
    simpa using hbase
  have hlawFirst := block_wedge_row D (basePivot := baseSecond) (basePartner := baseFirst)
    (Finset.univ.filter fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0)
    (fun atomIndex hnot => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnot
      exact (hdichotomy atomIndex).resolve_left hnot)
    (fun atomIndex hmem => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact exists_smul_of_planeWedge_eq_zero (atom_ne_zero_of_heavy D hheavy baseFirst) hmem)
  have hlawSecond := block_wedge_row D (basePivot := baseFirst) (basePartner := baseSecond)
    (Finset.univ.filter fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0)
    (fun atomIndex hnot => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnot
      exact hnot)
    (fun atomIndex hmem => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact exists_smul_of_planeWedge_eq_zero (atom_ne_zero_of_heavy D hheavy baseSecond)
        ((hdichotomy atomIndex).resolve_left hmem))
  -- The two shares add to two, so the wedge law makes each of them one.
  have hshareSum : (∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex * leverageOf (D.atom atomIndex))
      + (∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex * leverageOf (D.atom atomIndex)) = 2 := by
    rw [Finset.sum_filter_add_sum_filter_not, sum_weighted_leverage D]
    norm_num
  have hwedgeSq : (0 : ℝ) < planeWedge (D.atom baseFirst) (D.atom baseSecond) ^ 2 :=
    pow_pos (abs_pos.mpr hbase) 2 |>.trans_le (le_of_eq (by rw [sq_abs]))
  have hshareEq : (∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex * leverageOf (D.atom atomIndex))
      = ∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex * leverageOf (D.atom atomIndex) := by
    have hcomm := sq_planeWedge_comm (D.atom baseSecond) (D.atom baseFirst)
    have hmul : (∑ atomIndex ∈ Finset.univ.filter
          fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
            D.weight atomIndex * leverageOf (D.atom atomIndex))
        * planeWedge (D.atom baseFirst) (D.atom baseSecond) ^ 2
        = (∑ atomIndex ∈ Finset.univ.filter
          fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
            D.weight atomIndex * leverageOf (D.atom atomIndex))
          * planeWedge (D.atom baseFirst) (D.atom baseSecond) ^ 2 := by
      rw [← hlawSecond, ← hcomm, ← hlawFirst]
      ring
    exact mul_right_cancel₀ (ne_of_gt hwedgeSq) hmul
  have hshareFirstOne : (∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex * leverageOf (D.atom atomIndex)) = 1 := by
    linarith [hshareSum, hshareEq]
  -- Hence the two base atoms are orthogonal.
  have hleverageProduct : leverageOf (D.atom baseFirst) * leverageOf (D.atom baseSecond)
      = planeWedge (D.atom baseFirst) (D.atom baseSecond) ^ 2 := by
    rw [mul_comm (leverageOf (D.atom baseFirst)) (leverageOf (D.atom baseSecond)),
      hlawSecond, ← hshareEq, hshareFirstOne, one_mul]
  have horth : D.atom baseFirst ⬝ᵥ D.atom baseSecond = 0 := by
    have hlag := sq_dotProduct_add_sq_planeWedge (D.atom baseFirst) (D.atom baseSecond)
    have hsq : (D.atom baseFirst ⬝ᵥ D.atom baseSecond) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  -- Every cross pair is orthogonal, so its excess product vanishes.
  have hcross : ∀ atomIndex ∈ Finset.univ.filter
        fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
      ∀ otherIndex ∈ Finset.univ.filter
        fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
      D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1)
        * (D.weight otherIndex * (leverageOf (D.atom otherIndex) - 1)) = 0 := by
    intro atomIndex hmem otherIndex hother
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem hother
    obtain ⟨scaleFirst, hscaleFirst⟩ :=
      exists_smul_of_planeWedge_eq_zero (atom_ne_zero_of_heavy D hheavy baseFirst) hmem
    obtain ⟨scaleSecond, hscaleSecond⟩ :=
      exists_smul_of_planeWedge_eq_zero (atom_ne_zero_of_heavy D hheavy baseSecond)
        ((hdichotomy otherIndex).resolve_left hother)
    have hdot : D.atom atomIndex ⬝ᵥ D.atom otherIndex = 0 := by
      rw [hscaleFirst, hscaleSecond, smul_dotProduct, dotProduct_smul, horth]
      simp
    have hwedgeCross : planeWedge (D.atom atomIndex) (D.atom otherIndex) ^ 2
        = leverageOf (D.atom atomIndex) * leverageOf (D.atom otherIndex) := by
      have := sq_dotProduct_add_sq_planeWedge (D.atom atomIndex) (D.atom otherIndex)
      rw [hdot] at this
      linarith
    have hcoup := tieCoupling_nonneg D hheavy hnostrict atomIndex otherIndex
    rw [tieCoupling, hwedgeCross] at hcoup
    have hweights := mul_pos (D.weight_pos atomIndex) (D.weight_pos otherIndex)
    have hexcessNonpos : (leverageOf (D.atom atomIndex) - 1)
        * (leverageOf (D.atom otherIndex) - 1) ≤ 0 := by nlinarith
    have hexcessNonneg : 0 ≤ (leverageOf (D.atom atomIndex) - 1)
        * (leverageOf (D.atom otherIndex) - 1) :=
      mul_nonneg (by linarith [hheavy atomIndex]) (by linarith [hheavy otherIndex])
    have : (leverageOf (D.atom atomIndex) - 1) * (leverageOf (D.atom otherIndex) - 1) = 0 :=
      le_antisymm hexcessNonpos hexcessNonneg
    rw [show D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1)
        * (D.weight otherIndex * (leverageOf (D.atom otherIndex) - 1))
      = D.weight atomIndex * D.weight otherIndex
        * ((leverageOf (D.atom atomIndex) - 1) * (leverageOf (D.atom otherIndex) - 1)) by ring,
      this]
    ring
  -- The two block excesses are the two complementary weights, and their product is zero.
  have hproductZero : (∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1))
      * (∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1)) = 0 := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun atomIndex hmem =>
      Finset.sum_eq_zero fun otherIndex hother => hcross atomIndex hmem otherIndex hother
  have hweightSplit : (∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0, D.weight atomIndex)
      + (∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not, D.weight_sum_one]
  have hexcessFirst : (∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1))
      = 1 - ∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex := by
    have hsplit : (∑ atomIndex ∈ Finset.univ.filter
          fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
            D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1))
        = (∑ atomIndex ∈ Finset.univ.filter
            fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
              D.weight atomIndex * leverageOf (D.atom atomIndex))
          - ∑ atomIndex ∈ Finset.univ.filter
            fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
              D.weight atomIndex := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsplit, hshareFirstOne]
  have hshareSecondOne : (∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex * leverageOf (D.atom atomIndex)) = 1 := by
    linarith [hshareEq, hshareFirstOne]
  have hexcessSecond : (∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1))
      = 1 - ∑ atomIndex ∈ Finset.univ.filter
        fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
          D.weight atomIndex := by
    have hsplit : (∑ atomIndex ∈ Finset.univ.filter
          fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
            D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1))
        = (∑ atomIndex ∈ Finset.univ.filter
            fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
              D.weight atomIndex * leverageOf (D.atom atomIndex))
          - ∑ atomIndex ∈ Finset.univ.filter
            fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
              D.weight atomIndex := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsplit, hshareSecondOne]
  have hposFirst : 0 < ∑ atomIndex ∈ Finset.univ.filter
      fun atomIndex => planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0, D.weight atomIndex :=
    Finset.sum_pos' (fun i _ => (D.weight_pos i).le) ⟨baseFirst, hmemFirst, D.weight_pos baseFirst⟩
  have hposSecond : 0 < ∑ atomIndex ∈ Finset.univ.filter
      fun atomIndex => ¬ planeWedge (D.atom baseFirst) (D.atom atomIndex) = 0,
        D.weight atomIndex :=
    Finset.sum_pos' (fun i _ => (D.weight_pos i).le)
      ⟨baseSecond, hmemSecond, D.weight_pos baseSecond⟩
  rw [hexcessFirst, hexcessSecond] at hproductZero
  nlinarith [hproductZero, hweightSplit, hposFirst, hposSecond]

/-! ## Part E: quadratic forms, and a trace sandwich for projections

Three elementary facts about real symmetric matrices with a nonnegative quadratic
form replace the whole spectral theorem in this file. -/

/-- Moving a symmetric matrix across the dot product. -/
theorem dotProduct_symm_mulVec {size : ℕ} {gram : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : gramᵀ = gram) (leftVec rightVec : Fin size → ℝ) :
    leftVec ⬝ᵥ (gram *ᵥ rightVec) = (gram *ᵥ leftVec) ⬝ᵥ rightVec := by
  rw [dotProduct_mulVec, ← vecMul_transpose, hsymm]

/-- The diagonal entry as a quadratic form value. -/
theorem dotProduct_single_mulVec_single {size : ℕ} (gram : Matrix (Fin size) (Fin size) ℝ)
    (index : Fin size) :
    (Pi.single index 1 : Fin size → ℝ) ⬝ᵥ (gram *ᵥ Pi.single index 1) = gram index index := by
  rw [Matrix.mulVec_single_one, single_dotProduct, one_mul]
  rfl

/-- A real matrix whose quadratic form is nonnegative. -/
def FormNonneg {size : ℕ} (gram : Matrix (Fin size) (Fin size) ℝ) : Prop :=
  ∀ testVec : Fin size → ℝ, 0 ≤ testVec ⬝ᵥ (gram *ᵥ testVec)

/-- **A null vector of a nonnegative form is annihilated by the matrix.**  Polarise:
`(x + s y)` has a nonnegative form for every `s`, and the choice
`s = -cross/(quad + 1)` makes the value strictly negative unless the cross term
vanishes. -/
theorem FormNonneg.mulVec_eq_zero {size : ℕ} {gram : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : gramᵀ = gram) (hform : FormNonneg gram) {nullVec : Fin size → ℝ}
    (hzero : nullVec ⬝ᵥ (gram *ᵥ nullVec) = 0) : gram *ᵥ nullVec = 0 := by
  have hcross : ∀ testVec : Fin size → ℝ, testVec ⬝ᵥ (gram *ᵥ nullVec) = 0 := by
    intro testVec
    have hexpand : ∀ scale : ℝ,
        (nullVec + scale • testVec) ⬝ᵥ (gram *ᵥ (nullVec + scale • testVec))
          = scale * (2 * (testVec ⬝ᵥ (gram *ᵥ nullVec)))
            + scale ^ 2 * (testVec ⬝ᵥ (gram *ᵥ testVec)) := by
      intro scale
      have hswap : nullVec ⬝ᵥ (gram *ᵥ testVec) = testVec ⬝ᵥ (gram *ᵥ nullVec) := by
        rw [dotProduct_symm_mulVec hsymm, dotProduct_comm]
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        dotProduct_add, smul_dotProduct, smul_dotProduct, dotProduct_smul,
        dotProduct_smul, hzero, hswap]
      simp only [smul_eq_mul]
      ring
    by_contra hne
    have hquadNonneg : 0 ≤ testVec ⬝ᵥ (gram *ᵥ testVec) := hform testVec
    have hden : (0 : ℝ) < testVec ⬝ᵥ (gram *ᵥ testVec) + 1 := by linarith
    have hsq : 0 < (testVec ⬝ᵥ (gram *ᵥ nullVec)) ^ 2 := by positivity
    have hval := hform (nullVec
      + (-(testVec ⬝ᵥ (gram *ᵥ nullVec)) / (testVec ⬝ᵥ (gram *ᵥ testVec) + 1)) • testVec)
    rw [hexpand] at hval
    have hrewrite : (-(testVec ⬝ᵥ (gram *ᵥ nullVec)) / (testVec ⬝ᵥ (gram *ᵥ testVec) + 1))
          * (2 * (testVec ⬝ᵥ (gram *ᵥ nullVec)))
        + (-(testVec ⬝ᵥ (gram *ᵥ nullVec)) / (testVec ⬝ᵥ (gram *ᵥ testVec) + 1)) ^ 2
          * (testVec ⬝ᵥ (gram *ᵥ testVec))
        = (testVec ⬝ᵥ (gram *ᵥ nullVec)) ^ 2
            * ((testVec ⬝ᵥ (gram *ᵥ testVec)) - 2 * ((testVec ⬝ᵥ (gram *ᵥ testVec)) + 1))
          / ((testVec ⬝ᵥ (gram *ᵥ testVec)) + 1) ^ 2 := by
      field_simp
      ring
    rw [hrewrite] at hval
    have hnum : (testVec ⬝ᵥ (gram *ᵥ nullVec)) ^ 2
        * ((testVec ⬝ᵥ (gram *ᵥ testVec)) - 2 * ((testVec ⬝ᵥ (gram *ᵥ testVec)) + 1)) < 0 := by
      nlinarith
    have hneg := div_neg_of_neg_of_pos hnum (by positivity :
      (0 : ℝ) < ((testVec ⬝ᵥ (gram *ᵥ testVec)) + 1) ^ 2)
    linarith
  exact dotProduct_self_eq_zero.mp (hcross (gram *ᵥ nullVec))

/-- The diagonal of a nonnegative form is nonnegative. -/
theorem FormNonneg.diag_nonneg {size : ℕ} {gram : Matrix (Fin size) (Fin size) ℝ}
    (hform : FormNonneg gram) (index : Fin size) : 0 ≤ gram index index := by
  rw [← dotProduct_single_mulVec_single gram index]
  exact hform _

/-- The trace of a nonnegative form is nonnegative. -/
theorem FormNonneg.trace_nonneg {size : ℕ} {gram : Matrix (Fin size) (Fin size) ℝ}
    (hform : FormNonneg gram) : 0 ≤ gram.trace :=
  Finset.sum_nonneg fun index _ => hform.diag_nonneg index

/-- **A nonnegative form of zero trace is the zero matrix.** -/
theorem FormNonneg.eq_zero_of_trace_eq_zero {size : ℕ}
    {gram : Matrix (Fin size) (Fin size) ℝ} (hsymm : gramᵀ = gram) (hform : FormNonneg gram)
    (htrace : gram.trace = 0) : gram = 0 := by
  have hdiag : ∀ index : Fin size, gram index index = 0 := by
    intro index
    by_contra hcontra
    have hstrict : 0 < gram index index :=
      lt_of_le_of_ne (hform.diag_nonneg index) (Ne.symm hcontra)
    have hpos : 0 < ∑ other, gram other other :=
      Finset.sum_pos' (fun other _ => hform.diag_nonneg other)
        ⟨index, Finset.mem_univ index, hstrict⟩
    have hsum : ∑ other, gram other other = 0 := htrace
    linarith
  ext rowIndex colIndex
  have hnull : gram *ᵥ (Pi.single colIndex 1 : Fin size → ℝ) = 0 := by
    refine hform.mulVec_eq_zero hsymm ?_
    rw [dotProduct_single_mulVec_single, hdiag]
  have hentry := congrFun hnull rowIndex
  rw [Matrix.mulVec_single_one] at hentry
  simpa using hentry

/-- **THE TRACE SANDWICH.**  Let `gapForm` be symmetric with a nonnegative quadratic
form, let `proj` be a symmetric idempotent of the same trace, and let `gapForm`
dominate the identity on the range of `proj`.  Then `gapForm = proj`.

This replaces the eigenvalue count.  The two matrices `proj * gapForm * proj - proj`
and `(1 - proj) * gapForm * (1 - proj)` both have nonnegative forms and their traces
add to zero, so both are zero, and the two equations they carry compose. -/
theorem eq_of_trace_sandwich {size : ℕ} {gapForm proj : Matrix (Fin size) (Fin size) ℝ}
    (hgapSymm : gapFormᵀ = gapForm) (hgapForm : FormNonneg gapForm)
    (hprojSymm : projᵀ = proj) (hprojIdem : proj * proj = proj)
    (htrace : gapForm.trace = proj.trace)
    (hdominates : ∀ testVec : Fin size → ℝ,
        (proj *ᵥ testVec) ⬝ᵥ (proj *ᵥ testVec)
          ≤ (proj *ᵥ testVec) ⬝ᵥ (gapForm *ᵥ (proj *ᵥ testVec))) :
    gapForm = proj := by
  have hcompSymm : ((1 : Matrix (Fin size) (Fin size) ℝ) - proj)ᵀ = 1 - proj := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hprojSymm]
  have hprojQuad : ∀ testVec : Fin size → ℝ,
      testVec ⬝ᵥ (proj *ᵥ testVec) = (proj *ᵥ testVec) ⬝ᵥ (proj *ᵥ testVec) := by
    intro testVec
    conv_lhs => rw [← hprojIdem]
    rw [← Matrix.mulVec_mulVec, dotProduct_symm_mulVec hprojSymm]
  set innerResidue : Matrix (Fin size) (Fin size) ℝ := proj * gapForm * proj - proj
    with hinnerResidue
  have hinnerSymm : innerResidueᵀ = innerResidue := by
    rw [hinnerResidue, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      hprojSymm, hgapSymm, Matrix.mul_assoc]
  have hinnerForm : FormNonneg innerResidue := by
    intro testVec
    have hquad : testVec ⬝ᵥ (innerResidue *ᵥ testVec)
        = (proj *ᵥ testVec) ⬝ᵥ (gapForm *ᵥ (proj *ᵥ testVec))
          - (proj *ᵥ testVec) ⬝ᵥ (proj *ᵥ testVec) := by
      rw [hinnerResidue, Matrix.sub_mulVec, dotProduct_sub, ← hprojQuad]
      congr 1
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_symm_mulVec hprojSymm]
    rw [hquad]
    linarith [hdominates testVec]
  set outerResidue : Matrix (Fin size) (Fin size) ℝ :=
    (1 - proj) * gapForm * (1 - proj) with houterResidue
  have houterSymm : outerResidueᵀ = outerResidue := by
    rw [houterResidue, Matrix.transpose_mul, Matrix.transpose_mul, hcompSymm, hgapSymm,
      Matrix.mul_assoc]
  have houterQuad : ∀ testVec : Fin size → ℝ, testVec ⬝ᵥ (outerResidue *ᵥ testVec)
      = ((1 - proj) *ᵥ testVec) ⬝ᵥ (gapForm *ᵥ ((1 - proj) *ᵥ testVec)) := by
    intro testVec
    rw [houterResidue, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_symm_mulVec hcompSymm]
  have houterForm : FormNonneg outerResidue := fun testVec => by
    rw [houterQuad testVec]; exact hgapForm _
  have htraceProj : (proj * gapForm * proj).trace = (gapForm * proj).trace := by
    rw [Matrix.trace_mul_comm (proj * gapForm) proj, ← Matrix.mul_assoc, hprojIdem,
      Matrix.trace_mul_comm proj gapForm]
  have htraceInner : innerResidue.trace = (gapForm * proj).trace - proj.trace := by
    rw [hinnerResidue, Matrix.trace_sub, htraceProj]
  have htraceOuter : outerResidue.trace = gapForm.trace - (gapForm * proj).trace := by
    have hexpand : (1 - proj) * gapForm * (1 - proj)
        = gapForm - proj * gapForm - gapForm * proj + proj * gapForm * proj := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [houterResidue, hexpand, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
      htraceProj, Matrix.trace_mul_comm proj gapForm]
    ring
  have hsumZero : innerResidue.trace + outerResidue.trace = 0 := by
    rw [htraceInner, htraceOuter, htrace]; ring
  have hinnerZero : innerResidue = 0 :=
    hinnerForm.eq_zero_of_trace_eq_zero hinnerSymm
      (le_antisymm (by linarith [houterForm.trace_nonneg]) hinnerForm.trace_nonneg)
  have houterZero : outerResidue = 0 :=
    houterForm.eq_zero_of_trace_eq_zero houterSymm
      (le_antisymm (by linarith [hinnerForm.trace_nonneg]) houterForm.trace_nonneg)
  have hkill : gapForm * (1 - proj) = 0 := by
    have hcol : ∀ testVec : Fin size → ℝ, gapForm *ᵥ ((1 - proj) *ᵥ testVec) = 0 := by
      intro testVec
      refine hgapForm.mulVec_eq_zero hgapSymm ?_
      rw [← houterQuad testVec, houterZero, Matrix.zero_mulVec, dotProduct_zero]
    ext rowIndex colIndex
    have hentry := congrFun (hcol (Pi.single colIndex 1)) rowIndex
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hentry
    simpa [Matrix.transpose_apply] using hentry
  have hgapProj : gapForm * proj = gapForm := by
    have hstep := hkill
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hstep
    exact hstep.symm
  have hprojGap : proj * gapForm = gapForm := by
    have hstep := congrArg Matrix.transpose hgapProj
    rwa [Matrix.transpose_mul, hprojSymm, hgapSymm] at hstep
  have hinner : proj * gapForm * proj = proj := by
    have hstep := hinnerZero
    rw [hinnerResidue, sub_eq_zero] at hstep
    exact hstep
  rw [hprojGap, hgapProj] at hinner
  exact hinner

/-! ## Part F: the Veronese factorisation, and the projection

The symmetric two by two matrices form a THREE-dimensional space, so the Hadamard
square of the design Gram is the Gram of `m` vectors in `R^3`.  That is where the
number three comes from, and it is the one step that does not reach rank three. -/

/-- The square root of a weight. -/
noncomputable def rootWeight (D : WeightedDesign m 2) (atomIndex : Fin m) : ℝ :=
  Real.sqrt (D.weight atomIndex)

theorem rootWeight_pos (D : WeightedDesign m 2) (atomIndex : Fin m) :
    0 < rootWeight D atomIndex :=
  Real.sqrt_pos.mpr (D.weight_pos atomIndex)

theorem rootWeight_mul_self (D : WeightedDesign m 2) (atomIndex : Fin m) :
    rootWeight D atomIndex * rootWeight D atomIndex = D.weight atomIndex :=
  Real.mul_self_sqrt (D.weight_pos atomIndex).le

/-- **The normalised coupling** `N_cd = sqrt(t_c t_d) (l_c + l_d - 1 - J_cd^2)`: the
coupling conjugated by the square roots of the weights.  It is what the trace
sandwich sees. -/
noncomputable def normalizedCoupling (D : WeightedDesign m 2) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun atomFirst atomSecond => rootWeight D atomFirst * rootWeight D atomSecond *
    (leverageOf (D.atom atomFirst) + leverageOf (D.atom atomSecond) - 1
      - planeWedge (D.atom atomFirst) (D.atom atomSecond) ^ 2)

theorem normalizedCoupling_apply (D : WeightedDesign m 2) (atomFirst atomSecond : Fin m) :
    normalizedCoupling D atomFirst atomSecond = rootWeight D atomFirst * rootWeight D atomSecond *
      (leverageOf (D.atom atomFirst) + leverageOf (D.atom atomSecond) - 1
        - planeWedge (D.atom atomFirst) (D.atom atomSecond) ^ 2) := rfl

theorem tieCoupling_eq_rootWeight_mul (D : WeightedDesign m 2) (atomFirst atomSecond : Fin m) :
    tieCoupling D atomFirst atomSecond
      = rootWeight D atomFirst * rootWeight D atomSecond
        * normalizedCoupling D atomFirst atomSecond := by
  have hfirst := rootWeight_mul_self D atomFirst
  have hsecond := rootWeight_mul_self D atomSecond
  simp only [tieCoupling, normalizedCoupling_apply]
  rw [← hfirst, ← hsecond]
  ring

theorem normalizedCoupling_transpose (D : WeightedDesign m 2) :
    (normalizedCoupling D)ᵀ = normalizedCoupling D := by
  ext atomFirst atomSecond
  simp only [Matrix.transpose_apply, normalizedCoupling_apply,
    sq_planeWedge_comm (D.atom atomSecond) (D.atom atomFirst)]
  ring

theorem normalizedCoupling_diag (D : WeightedDesign m 2) (atomIndex : Fin m) :
    normalizedCoupling D atomIndex atomIndex
      = D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1) := by
  simp only [normalizedCoupling_apply, planeWedge_self]
  rw [rootWeight_mul_self]
  ring

/-- **The trace of the normalised coupling is `2k - 1 = 3`.**  Two Parseval readings:
the leverage trace is `k = 2`, and the weights sum to one. -/
theorem trace_normalizedCoupling (D : WeightedDesign m 2) :
    (normalizedCoupling D).trace = 3 := by
  have hsum : (normalizedCoupling D).trace
      = ∑ atomIndex, D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1) :=
    Finset.sum_congr rfl fun atomIndex _ => normalizedCoupling_diag D atomIndex
  rw [hsum]
  have hsplit : ∀ atomIndex : Fin m,
      D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1)
        = 2 * (D.weight atomIndex * leverageOf (D.atom atomIndex)) - D.weight atomIndex :=
    fun _ => by ring
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hsplit atomIndex,
    Finset.sum_sub_distrib, ← Finset.mul_sum, sum_weighted_leverage D, D.weight_sum_one]
  norm_num

/-- The Veronese rows `sqrt(t_c) * (a^2, sqrt 2 * a b, b^2)`, whose Gram is the
Hadamard square of the design Gram. -/
noncomputable def couplingVeronese (D : WeightedDesign m 2) : Matrix (Fin m) (Fin 3) ℝ :=
  Matrix.of fun atomIndex coordIndex =>
    rootWeight D atomIndex *
      ![D.atom atomIndex 0 ^ 2, Real.sqrt 2 * (D.atom atomIndex 0 * D.atom atomIndex 1),
        D.atom atomIndex 1 ^ 2] coordIndex

/-- The heavy-excess vector `s_c = sqrt(t_c) (l_c - 1)`. -/
noncomputable def couplingShift (D : WeightedDesign m 2) (atomIndex : Fin m) : ℝ :=
  rootWeight D atomIndex * (leverageOf (D.atom atomIndex) - 1)

/-- **THE VERONESE FACTORISATION**, `N = R R^T - s s^T`, with `R` of three columns.
The Gram of the Veronese rows is the Hadamard square of the design Gram, and
Lagrange turns that square into the wedge form. -/
theorem normalizedCoupling_eq (D : WeightedDesign m 2) :
    normalizedCoupling D
      = couplingVeronese D * (couplingVeronese D)ᵀ
        - Matrix.vecMulVec (couplingShift D) (couplingShift D) := by
  have hroot : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext atomFirst atomSecond
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, couplingVeronese,
    Matrix.of_apply, Matrix.vecMulVec_apply, couplingShift, normalizedCoupling_apply,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, planeWedge, leverageOf, Fin.sum_univ_two]
  linear_combination (-(rootWeight D atomFirst * rootWeight D atomSecond
    * (D.atom atomFirst 0 * D.atom atomFirst 1)
    * (D.atom atomSecond 0 * D.atom atomSecond 1))) * hroot

/-- **The Laplacian identity.**  For a symmetric matrix with row sums `t`, the
Dirichlet form of `diag t - F` is the edge sum.  This replaces positive
semidefiniteness of the gap. -/
theorem laplacian_identity (D : WeightedDesign m 2) (probe : Fin m → ℝ) :
    (∑ atomIndex, D.weight atomIndex * probe atomIndex ^ 2)
        - ∑ atomIndex, ∑ otherIndex,
            probe atomIndex * (tieCoupling D atomIndex otherIndex * probe otherIndex)
      = (1 / 2) * ∑ atomIndex, ∑ otherIndex,
          tieCoupling D atomIndex otherIndex * (probe atomIndex - probe otherIndex) ^ 2 := by
  have hrowFirst : ∑ atomIndex, ∑ otherIndex,
      tieCoupling D atomIndex otherIndex * probe atomIndex ^ 2
        = ∑ atomIndex, D.weight atomIndex * probe atomIndex ^ 2 := by
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [← Finset.sum_mul, sum_tieCoupling D atomIndex]
  have hrowSecond : ∑ atomIndex, ∑ otherIndex,
      tieCoupling D atomIndex otherIndex * probe otherIndex ^ 2
        = ∑ atomIndex, D.weight atomIndex * probe atomIndex ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun otherIndex _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    rw [← sum_tieCoupling D otherIndex]
    exact Finset.sum_congr rfl fun atomIndex _ => tieCoupling_comm D atomIndex otherIndex
  have hexpand : ∀ atomIndex otherIndex : Fin m,
      tieCoupling D atomIndex otherIndex * (probe atomIndex - probe otherIndex) ^ 2
        = tieCoupling D atomIndex otherIndex * probe atomIndex ^ 2
          + tieCoupling D atomIndex otherIndex * probe otherIndex ^ 2
          - 2 * (probe atomIndex
              * (tieCoupling D atomIndex otherIndex * probe otherIndex)) :=
    fun _ _ => by ring
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) =>
    Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) =>
      hexpand atomIndex otherIndex]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hrowFirst, hrowSecond]
  ring

/-- The quadratic form of the normalised coupling, read against the reweighted
probe. -/
theorem dotProduct_normalizedCoupling_mulVec (D : WeightedDesign m 2) (testVec : Fin m → ℝ) :
    testVec ⬝ᵥ (normalizedCoupling D *ᵥ testVec)
      = ∑ atomIndex, ∑ otherIndex,
          (testVec atomIndex / rootWeight D atomIndex)
            * (tieCoupling D atomIndex otherIndex
                * (testVec otherIndex / rootWeight D otherIndex)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => Finset.sum_congr rfl fun otherIndex _ => ?_
  have hfirst := (rootWeight_pos D atomIndex).ne'
  have hsecond := (rootWeight_pos D otherIndex).ne'
  rw [tieCoupling_eq_rootWeight_mul]
  field_simp

/-- **The gap of the normalised coupling has a nonnegative form.**  Entrywise
nonnegativity plus the row law, through the Laplacian identity. -/
theorem formNonneg_one_sub_normalizedCoupling (D : WeightedDesign m 2)
    (hcoupling : ∀ atomFirst atomSecond : Fin m, 0 ≤ tieCoupling D atomFirst atomSecond) :
    FormNonneg (1 - normalizedCoupling D) := by
  intro testVec
  have hweights : ∀ atomIndex : Fin m,
      testVec atomIndex * testVec atomIndex
        = D.weight atomIndex * (testVec atomIndex / rootWeight D atomIndex) ^ 2 := by
    intro atomIndex
    have hroot := rootWeight_mul_self D atomIndex
    have hne := (rootWeight_pos D atomIndex).ne'
    field_simp
    nlinarith [hroot]
  have hsplit : testVec ⬝ᵥ ((1 - normalizedCoupling D) *ᵥ testVec)
      = (∑ atomIndex, D.weight atomIndex
            * (testVec atomIndex / rootWeight D atomIndex) ^ 2)
        - ∑ atomIndex, ∑ otherIndex,
            (testVec atomIndex / rootWeight D atomIndex)
              * (tieCoupling D atomIndex otherIndex
                  * (testVec otherIndex / rootWeight D otherIndex)) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      dotProduct_normalizedCoupling_mulVec]
    congr 1
    exact Finset.sum_congr rfl fun atomIndex _ => hweights atomIndex
  rw [hsplit, laplacian_identity D (fun atomIndex => testVec atomIndex / rootWeight D atomIndex)]
  have hterms : (0 : ℝ) ≤ ∑ atomIndex, ∑ otherIndex,
      tieCoupling D atomIndex otherIndex
        * (testVec atomIndex / rootWeight D atomIndex
            - testVec otherIndex / rootWeight D otherIndex) ^ 2 :=
    Finset.sum_nonneg fun atomIndex _ => Finset.sum_nonneg fun otherIndex _ =>
      mul_nonneg (hcoupling atomIndex otherIndex) (sq_nonneg _)
  linarith

/-! ### The Veronese Gram is invertible -/

/-- **Three pairwise non-parallel vectors carry no conic.**  Cramer's rule on the
three by three Veronese matrix, whose determinant is the product of the three
wedges. -/
theorem conic_coefficients_eq_zero {vecFirst vecSecond vecThird : Fin 2 → ℝ}
    {coefSquareFirst coefCross coefSquareSecond : ℝ}
    (hone : planeWedge vecFirst vecSecond ≠ 0) (htwo : planeWedge vecFirst vecThird ≠ 0)
    (hthree : planeWedge vecSecond vecThird ≠ 0)
    (heqFirst : coefSquareFirst * vecFirst 0 ^ 2 + coefCross * (vecFirst 0 * vecFirst 1)
        + coefSquareSecond * vecFirst 1 ^ 2 = 0)
    (heqSecond : coefSquareFirst * vecSecond 0 ^ 2 + coefCross * (vecSecond 0 * vecSecond 1)
        + coefSquareSecond * vecSecond 1 ^ 2 = 0)
    (heqThird : coefSquareFirst * vecThird 0 ^ 2 + coefCross * (vecThird 0 * vecThird 1)
        + coefSquareSecond * vecThird 1 ^ 2 = 0) :
    coefSquareFirst = 0 ∧ coefCross = 0 ∧ coefSquareSecond = 0 := by
  have hdet : planeWedge vecFirst vecSecond * planeWedge vecFirst vecThird
      * planeWedge vecSecond vecThird ≠ 0 :=
    mul_ne_zero (mul_ne_zero hone htwo) hthree
  refine ⟨?_, ?_, ?_⟩
  · have hcramer : coefSquareFirst * (planeWedge vecFirst vecSecond
        * planeWedge vecFirst vecThird * planeWedge vecSecond vecThird) = 0 := by
      simp only [planeWedge]
      linear_combination
        (vecSecond 1 * vecThird 1 * (vecSecond 0 * vecThird 1 - vecSecond 1 * vecThird 0))
            * heqFirst
        - (vecFirst 1 * vecThird 1 * (vecFirst 0 * vecThird 1 - vecFirst 1 * vecThird 0))
            * heqSecond
        + (vecFirst 1 * vecSecond 1 * (vecFirst 0 * vecSecond 1 - vecFirst 1 * vecSecond 0))
            * heqThird
    exact (mul_eq_zero.mp hcramer).resolve_right hdet
  · have hcramer : coefCross * (planeWedge vecFirst vecSecond
        * planeWedge vecFirst vecThird * planeWedge vecSecond vecThird) = 0 := by
      simp only [planeWedge]
      linear_combination
        (-(vecSecond 0 * vecThird 1 - vecSecond 1 * vecThird 0)
            * (vecSecond 0 * vecThird 1 + vecSecond 1 * vecThird 0)) * heqFirst
        + ((vecFirst 0 * vecThird 1 - vecFirst 1 * vecThird 0)
            * (vecFirst 0 * vecThird 1 + vecFirst 1 * vecThird 0)) * heqSecond
        - ((vecFirst 0 * vecSecond 1 - vecFirst 1 * vecSecond 0)
            * (vecFirst 0 * vecSecond 1 + vecFirst 1 * vecSecond 0)) * heqThird
    exact (mul_eq_zero.mp hcramer).resolve_right hdet
  · have hcramer : coefSquareSecond * (planeWedge vecFirst vecSecond
        * planeWedge vecFirst vecThird * planeWedge vecSecond vecThird) = 0 := by
      simp only [planeWedge]
      linear_combination
        (vecSecond 0 * vecThird 0 * (vecSecond 0 * vecThird 1 - vecSecond 1 * vecThird 0))
            * heqFirst
        - (vecFirst 0 * vecThird 0 * (vecFirst 0 * vecThird 1 - vecFirst 1 * vecThird 0))
            * heqSecond
        + (vecFirst 0 * vecSecond 0 * (vecFirst 0 * vecSecond 1 - vecFirst 1 * vecSecond 0))
            * heqThird
    exact (mul_eq_zero.mp hcramer).resolve_right hdet

/-- The three by three Gram of the Veronese rows. -/
noncomputable def couplingGram (D : WeightedDesign m 2) : Matrix (Fin 3) (Fin 3) ℝ :=
  (couplingVeronese D)ᵀ * couplingVeronese D

theorem couplingGram_transpose (D : WeightedDesign m 2) :
    (couplingGram D)ᵀ = couplingGram D := by
  rw [couplingGram, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **The Veronese Gram is invertible.**  Its kernel would be a conic through every
atom, and three pairwise non-parallel atoms carry none. -/
theorem isUnit_det_couplingGram (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) : IsUnit (couplingGram D).det := by
  rw [isUnit_iff_ne_zero]
  intro hdetZero
  obtain ⟨coefVec, hnonzero, hkernel⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := couplingGram D)).mpr hdetZero
  have hstep : coefVec ⬝ᵥ (couplingGram D *ᵥ coefVec)
      = (couplingVeronese D *ᵥ coefVec) ⬝ᵥ (couplingVeronese D *ᵥ coefVec) := by
    rw [couplingGram, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have hquad : (couplingVeronese D *ᵥ coefVec) ⬝ᵥ (couplingVeronese D *ᵥ coefVec) = 0 := by
    rw [← hstep, hkernel, dotProduct_zero]
  have hzero : couplingVeronese D *ᵥ coefVec = 0 := dotProduct_self_eq_zero.mp hquad
  obtain ⟨firstLabel, secondLabel, thirdLabel, hone, htwo, hthree⟩ :=
    exists_three_pairwise_nonParallel D hheavy hnostrict
  have hconic : ∀ atomIndex : Fin m,
      coefVec 0 * D.atom atomIndex 0 ^ 2
        + (coefVec 1 * Real.sqrt 2) * (D.atom atomIndex 0 * D.atom atomIndex 1)
        + coefVec 2 * D.atom atomIndex 1 ^ 2 = 0 := by
    intro atomIndex
    have hentry := congrFun hzero atomIndex
    simp only [Matrix.mulVec, dotProduct, couplingVeronese, Matrix.of_apply,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply] at hentry
    have hroot := (rootWeight_pos D atomIndex).ne'
    have hfactor : rootWeight D atomIndex *
        (coefVec 0 * D.atom atomIndex 0 ^ 2
          + (coefVec 1 * Real.sqrt 2) * (D.atom atomIndex 0 * D.atom atomIndex 1)
          + coefVec 2 * D.atom atomIndex 1 ^ 2) = 0 := by
      rw [← hentry]; ring
    rcases mul_eq_zero.mp hfactor with h | h
    · exact absurd h hroot
    · exact h
  obtain ⟨hcoefZero, hcoefOne, hcoefTwo⟩ :=
    conic_coefficients_eq_zero (vecFirst := D.atom firstLabel) (vecSecond := D.atom secondLabel)
      (vecThird := D.atom thirdLabel) hone htwo hthree
      (hconic firstLabel) (hconic secondLabel) (hconic thirdLabel)
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  refine hnonzero (funext fun coordIndex => ?_)
  fin_cases coordIndex
  · simpa using hcoefZero
  · have hmid : coefVec 1 = 0 := (mul_eq_zero.mp hcoefOne).resolve_right hsqrtTwo
    simpa using hmid
  · simpa using hcoefTwo

/-- The orthogonal projection onto the column space of the Veronese matrix. -/
noncomputable def couplingProjection (D : WeightedDesign m 2) : Matrix (Fin m) (Fin m) ℝ :=
  couplingVeronese D * (couplingGram D)⁻¹ * (couplingVeronese D)ᵀ

theorem couplingProjection_transpose (D : WeightedDesign m 2) :
    (couplingProjection D)ᵀ = couplingProjection D := by
  rw [couplingProjection, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, couplingGram_transpose,
    Matrix.mul_assoc]

theorem couplingProjection_idem (D : WeightedDesign m 2)
    (hunit : IsUnit (couplingGram D).det) :
    couplingProjection D * couplingProjection D = couplingProjection D := by
  rw [couplingProjection]
  calc couplingVeronese D * (couplingGram D)⁻¹ * (couplingVeronese D)ᵀ
        * (couplingVeronese D * (couplingGram D)⁻¹ * (couplingVeronese D)ᵀ)
      = couplingVeronese D * ((couplingGram D)⁻¹ * ((couplingVeronese D)ᵀ
          * couplingVeronese D) * (couplingGram D)⁻¹) * (couplingVeronese D)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = couplingVeronese D * (couplingGram D)⁻¹ * (couplingVeronese D)ᵀ := by
        rw [← couplingGram, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul, Matrix.mul_assoc]

theorem trace_couplingProjection (D : WeightedDesign m 2)
    (hunit : IsUnit (couplingGram D).det) : (couplingProjection D).trace = 3 := by
  rw [couplingProjection, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← couplingGram,
    Matrix.mul_nonsing_inv _ hunit, Matrix.trace_one]
  norm_num

/-- The complementary projection lands in the kernel of the Veronese transpose. -/
theorem veroneseTranspose_mul_one_sub_couplingProjection (D : WeightedDesign m 2)
    (hunit : IsUnit (couplingGram D).det) :
    (couplingVeronese D)ᵀ * (1 - couplingProjection D) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, couplingProjection, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← couplingGram, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul,
    sub_self]

/-- **On the Veronese kernel the gap dominates the identity.**  The Veronese part of
the normalised coupling dies there and only the rank-one shift survives, with a sign
that helps. -/
theorem le_dotProduct_one_sub_normalizedCoupling (D : WeightedDesign m 2)
    (probeVec : Fin m → ℝ) (hkernel : (couplingVeronese D)ᵀ *ᵥ probeVec = 0) :
    probeVec ⬝ᵥ probeVec ≤ probeVec ⬝ᵥ ((1 - normalizedCoupling D) *ᵥ probeVec) := by
  have hveronese :
      probeVec ⬝ᵥ ((couplingVeronese D * (couplingVeronese D)ᵀ) *ᵥ probeVec) = 0 := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, hkernel, dotProduct_zero]
  have hnormalized : probeVec ⬝ᵥ (normalizedCoupling D *ᵥ probeVec)
      = -(couplingShift D ⬝ᵥ probeVec) ^ 2 := by
    rw [normalizedCoupling_eq D, Matrix.sub_mulVec, dotProduct_sub, hveronese,
      dotProduct_vecMulVec_mulVec]
    ring
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hnormalized]
  nlinarith [sq_nonneg (couplingShift D ⬝ᵥ probeVec)]

/-- **THE PROJECTION THEOREM.**  At a rank-two design whose coupling is entrywise
nonnegative, the normalised coupling IS the orthogonal projection onto the column
space of the Veronese matrix.  Hence it is idempotent, positive semidefinite, and of
rank exactly three.

The trace sandwich supplies the argument: `1 - N` has a nonnegative form and trace
`m - 3`, the complementary projection has trace `m - 3`, and on the range of that
projection the Veronese part of `N` dies, so `1 - N` dominates the identity there. -/
theorem normalizedCoupling_eq_couplingProjection (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) :
    normalizedCoupling D = couplingProjection D := by
  have hunit := isUnit_det_couplingGram D hheavy hnostrict
  have hcoupling := tieCoupling_nonneg D hheavy hnostrict
  have hcompSymm : ((1 : Matrix (Fin m) (Fin m) ℝ) - couplingProjection D)ᵀ
      = 1 - couplingProjection D := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, couplingProjection_transpose]
  have hsandwich : (1 : Matrix (Fin m) (Fin m) ℝ) - normalizedCoupling D
      = 1 - couplingProjection D := by
    refine eq_of_trace_sandwich ?_ (formNonneg_one_sub_normalizedCoupling D hcoupling)
      hcompSymm ?_ ?_ ?_
    · rw [Matrix.transpose_sub, Matrix.transpose_one, normalizedCoupling_transpose]
    · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        couplingProjection_idem D hunit]
      abel
    · rw [Matrix.trace_sub, Matrix.trace_sub, trace_normalizedCoupling D,
        trace_couplingProjection D hunit]
    · intro testVec
      refine le_dotProduct_one_sub_normalizedCoupling D _ ?_
      rw [Matrix.mulVec_mulVec, veroneseTranspose_mul_one_sub_couplingProjection D hunit,
        Matrix.zero_mulVec]
  have hcancel := hsandwich
  rw [sub_right_inj] at hcancel
  exact hcancel

/-! ## Part G: the classes, and the rank-one blocks

The normalised coupling is now an orthogonal projection with nonnegative entries and
a positive diagonal, so `c ~ d :<-> F_cd > 0` is an equivalence relation whose classes
are CLIQUES.  One Perron step pins each block to `F_cd = t_c t_d / T_A`, and the
diagonal and the off-diagonal of that formula are the two halves of the
classification. -/

/-- The class of an atom: every atom it couples to strictly. -/
noncomputable def tieClass (D : WeightedDesign m 2) (pivot : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun other => 0 < tieCoupling D pivot other

theorem mem_tieClass_iff (D : WeightedDesign m 2) (pivot other : Fin m) :
    other ∈ tieClass D pivot ↔ 0 < tieCoupling D pivot other := by
  simp [tieClass]

theorem normalizedCoupling_nonneg (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (atomFirst atomSecond : Fin m) :
    0 ≤ normalizedCoupling D atomFirst atomSecond := by
  have hcoup := tieCoupling_nonneg D hheavy hnostrict atomFirst atomSecond
  rw [tieCoupling_eq_rootWeight_mul] at hcoup
  have hroots := mul_pos (rootWeight_pos D atomFirst) (rootWeight_pos D atomSecond)
  nlinarith [hcoup, hroots]

theorem normalizedCoupling_pos_iff (D : WeightedDesign m 2) (atomFirst atomSecond : Fin m) :
    0 < normalizedCoupling D atomFirst atomSecond ↔ 0 < tieCoupling D atomFirst atomSecond := by
  rw [tieCoupling_eq_rootWeight_mul]
  have hroots := mul_pos (rootWeight_pos D atomFirst) (rootWeight_pos D atomSecond)
  constructor
  · intro hpos; exact mul_pos hroots hpos
  · intro hpos
    by_contra hcontra
    push_neg at hcontra
    nlinarith [hroots, hpos, mul_nonneg hroots.le (neg_nonneg.mpr hcontra)]

theorem normalizedCoupling_diag_pos (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex)) (atomIndex : Fin m) :
    0 < normalizedCoupling D atomIndex atomIndex := by
  rw [normalizedCoupling_pos_iff]
  exact tieCoupling_pos_of_planeWedge_eq_zero D hheavy (planeWedge_self (D.atom atomIndex))

theorem self_mem_tieClass (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex)) (pivot : Fin m) :
    pivot ∈ tieClass D pivot := by
  rw [mem_tieClass_iff]
  exact tieCoupling_pos_of_planeWedge_eq_zero D hheavy (planeWedge_self (D.atom pivot))

/-- **The row law, normalised.**  The square-root weight vector is a fixed vector of
the normalised coupling. -/
theorem normalizedCoupling_mulVec_rootWeight (D : WeightedDesign m 2) :
    normalizedCoupling D *ᵥ rootWeight D = rootWeight D := by
  funext atomIndex
  have hroot := rootWeight_mul_self D atomIndex
  have hne := (rootWeight_pos D atomIndex).ne'
  have hsum : (∑ otherIndex, normalizedCoupling D atomIndex otherIndex
        * rootWeight D otherIndex) * rootWeight D atomIndex = D.weight atomIndex := by
    rw [Finset.sum_mul, ← sum_tieCoupling D atomIndex]
    refine Finset.sum_congr rfl fun otherIndex _ => ?_
    rw [tieCoupling_eq_rootWeight_mul]
    ring
  have hgoal : (normalizedCoupling D *ᵥ rootWeight D) atomIndex * rootWeight D atomIndex
      = rootWeight D atomIndex * rootWeight D atomIndex := by
    simp only [Matrix.mulVec, dotProduct]
    rw [hsum, hroot]
  exact mul_right_cancel₀ hne hgoal

/-- The normalised coupling is idempotent at a design with no strictly dominating
pair. -/
theorem normalizedCoupling_mul_self (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) :
    normalizedCoupling D * normalizedCoupling D = normalizedCoupling D := by
  rw [normalizedCoupling_eq_couplingProjection D hheavy hnostrict]
  exact couplingProjection_idem D (isUnit_det_couplingGram D hheavy hnostrict)

/-- **The class relation is transitive**, because the coupling is idempotent with
nonnegative entries: `N_ce >= N_cd N_de`. -/
theorem tieCoupling_pos_trans (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) {atomFirst atomMiddle atomLast : Fin m}
    (hone : 0 < tieCoupling D atomFirst atomMiddle)
    (htwo : 0 < tieCoupling D atomMiddle atomLast) :
    0 < tieCoupling D atomFirst atomLast := by
  rw [← normalizedCoupling_pos_iff] at hone htwo ⊢
  have hidem := congrFun (congrFun (normalizedCoupling_mul_self D hheavy hnostrict) atomFirst)
    atomLast
  rw [Matrix.mul_apply] at hidem
  rw [← hidem]
  refine lt_of_lt_of_le (mul_pos hone htwo) (Finset.single_le_sum
    (f := fun middle => normalizedCoupling D atomFirst middle
      * normalizedCoupling D middle atomLast) ?_ (Finset.mem_univ atomMiddle))
  intro middle _
  exact mul_nonneg (normalizedCoupling_nonneg D hheavy hnostrict _ _)
    (normalizedCoupling_nonneg D hheavy hnostrict _ _)

/-- The blocks of the coupling: an atom outside the class of `pivot` has zero
coupling to every member of that class. -/
theorem tieCoupling_eq_zero_of_not_mem (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) {pivot inside outside : Fin m}
    (hinside : inside ∈ tieClass D pivot) (houtside : outside ∉ tieClass D pivot) :
    tieCoupling D inside outside = 0 := by
  rw [mem_tieClass_iff] at hinside
  rw [mem_tieClass_iff] at houtside
  refine le_antisymm ?_ (tieCoupling_nonneg D hheavy hnostrict inside outside)
  by_contra hcontra
  push_neg at hcontra
  exact houtside (tieCoupling_pos_trans D hheavy hnostrict hinside hcontra)

/-- Class members have the same class. -/
theorem tieClass_eq_of_mem (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) {pivot member : Fin m} (hmember : member ∈ tieClass D pivot) :
    tieClass D member = tieClass D pivot := by
  rw [mem_tieClass_iff] at hmember
  ext other
  simp only [mem_tieClass_iff]
  constructor
  · intro hpos
    exact tieCoupling_pos_trans D hheavy hnostrict hmember hpos
  · intro hpos
    refine tieCoupling_pos_trans D hheavy hnostrict ?_ hpos
    rw [tieCoupling_comm]
    exact hmember

/-- The class weight is positive. -/
theorem classWeight_pos (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex)) (pivot : Fin m) :
    0 < ∑ member ∈ tieClass D pivot, D.weight member :=
  Finset.sum_pos' (fun member _ => (D.weight_pos member).le)
    ⟨pivot, self_mem_tieClass D hheavy pivot, D.weight_pos pivot⟩

/-- **THE RANK-ONE BLOCK.**  Inside a class the coupling is the outer product of the
weights divided by the class weight: `F_cd * T_A = t_c t_d`, division-free.

The Perron step: the `c`-th column of the projection is a NONNEGATIVE fixed vector
supported in the class, so subtracting the smallest multiple of the square-root
weight vector leaves a nonnegative fixed vector with a zero entry, and one row of the
fixed-point equation then kills the whole vector. -/
theorem tieCoupling_mul_classWeight (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (pivot : Fin m) {memberFirst memberSecond : Fin m}
    (hfirst : memberFirst ∈ tieClass D pivot) (hsecond : memberSecond ∈ tieClass D pivot) :
    tieCoupling D memberFirst memberSecond * (∑ member ∈ tieClass D pivot, D.weight member)
      = D.weight memberFirst * D.weight memberSecond := by
  classical
  have hidem := normalizedCoupling_mul_self D hheavy hnostrict
  have hnn := normalizedCoupling_nonneg D hheavy hnostrict
  have hsymmEntry : ∀ atomFirst atomSecond : Fin m,
      normalizedCoupling D atomFirst atomSecond = normalizedCoupling D atomSecond atomFirst :=
    fun atomFirst atomSecond =>
      congrFun (congrFun (normalizedCoupling_transpose D).symm atomFirst) atomSecond
  have hoffBlock : ∀ inside ∈ tieClass D pivot, ∀ outside ∉ tieClass D pivot,
      normalizedCoupling D inside outside = 0 := by
    intro inside hin outside hout
    have hzero := tieCoupling_eq_zero_of_not_mem D hheavy hnostrict hin hout
    rw [tieCoupling_eq_rootWeight_mul] at hzero
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (mul_pos (rootWeight_pos D inside) (rootWeight_pos D outside)).ne'
    · exact h
  -- The class-restricted square-root weight vector, and its two evaluations.
  set classVec : Fin m → ℝ :=
    fun atomIndex => if atomIndex ∈ tieClass D pivot then rootWeight D atomIndex else 0
    with hclassVec
  have hclassIn : ∀ atomIndex ∈ tieClass D pivot,
      classVec atomIndex = rootWeight D atomIndex := by
    intro atomIndex hmem
    show (if atomIndex ∈ tieClass D pivot then rootWeight D atomIndex else 0)
      = rootWeight D atomIndex
    simp [hmem]
  have hclassOut : ∀ atomIndex ∉ tieClass D pivot, classVec atomIndex = 0 := by
    intro atomIndex hmem
    show (if atomIndex ∈ tieClass D pivot then rootWeight D atomIndex else 0) = 0
    simp [hmem]
  have hfix : normalizedCoupling D *ᵥ classVec = classVec := by
    funext atomIndex
    have hrow := congrFun (normalizedCoupling_mulVec_rootWeight D) atomIndex
    simp only [Matrix.mulVec, dotProduct] at hrow ⊢
    by_cases hmem : atomIndex ∈ tieClass D pivot
    · have hsplit : ∑ other, normalizedCoupling D atomIndex other * classVec other
          = ∑ other, normalizedCoupling D atomIndex other * rootWeight D other := by
        refine Finset.sum_congr rfl fun other _ => ?_
        by_cases hother : other ∈ tieClass D pivot
        · rw [hclassIn other hother]
        · rw [hclassOut other hother, hoffBlock atomIndex hmem other hother]; ring
      rw [hsplit, hrow, hclassIn atomIndex hmem]
    · have hvanish : ∑ other, normalizedCoupling D atomIndex other * classVec other = 0 := by
        refine Finset.sum_eq_zero fun other _ => ?_
        by_cases hother : other ∈ tieClass D pivot
        · rw [hsymmEntry atomIndex other, hoffBlock other hother atomIndex hmem]; ring
        · rw [hclassOut other hother]; ring
      rw [hvanish, hclassOut atomIndex hmem]
  -- The `memberSecond` column is a nonnegative fixed vector supported in the class.
  set columnVec : Fin m → ℝ := fun atomIndex => normalizedCoupling D atomIndex memberSecond
    with hcolumnVec
  have hcolumnApply : ∀ atomIndex : Fin m,
      columnVec atomIndex = normalizedCoupling D atomIndex memberSecond := fun _ => rfl
  have hcolumnFix : normalizedCoupling D *ᵥ columnVec = columnVec := by
    funext atomIndex
    have hstep := congrFun (congrFun hidem atomIndex) memberSecond
    rw [Matrix.mul_apply] at hstep
    show ∑ other, normalizedCoupling D atomIndex other * columnVec other
      = normalizedCoupling D atomIndex memberSecond
    exact hstep
  have hcolumnNonneg : ∀ atomIndex, 0 ≤ columnVec atomIndex := fun atomIndex => hnn _ _
  have hcolumnSupport : ∀ atomIndex ∉ tieClass D pivot, columnVec atomIndex = 0 := by
    intro atomIndex hout
    rw [hcolumnApply, hsymmEntry atomIndex memberSecond]
    exact hoffBlock memberSecond hsecond atomIndex hout
  -- The smallest ratio on the class.
  obtain ⟨minLabel, hminMem, hmin⟩ := Finset.exists_min_image (tieClass D pivot)
    (fun atomIndex => columnVec atomIndex / rootWeight D atomIndex)
    ⟨pivot, self_mem_tieClass D hheavy pivot⟩
  set ratio : ℝ := columnVec minLabel / rootWeight D minLabel with hratio
  set residueVec : Fin m → ℝ := fun atomIndex => columnVec atomIndex - ratio * classVec atomIndex
    with hresidueVec
  have hresidueApply : ∀ atomIndex : Fin m,
      residueVec atomIndex = columnVec atomIndex - ratio * classVec atomIndex := fun _ => rfl
  have hresidueNonneg : ∀ atomIndex, 0 ≤ residueVec atomIndex := by
    intro atomIndex
    rw [hresidueApply]
    by_cases hmem : atomIndex ∈ tieClass D pivot
    · have hroot := rootWeight_pos D atomIndex
      have hkey := mul_le_mul_of_nonneg_right (hmin atomIndex hmem) hroot.le
      rw [div_mul_cancel₀ _ hroot.ne'] at hkey
      rw [hclassIn atomIndex hmem, hratio]
      linarith
    · rw [hclassOut atomIndex hmem, hcolumnSupport atomIndex hmem]; simp
  have hresidueFix : normalizedCoupling D *ᵥ residueVec = residueVec := by
    have hsplit : residueVec = columnVec - ratio • classVec := by
      funext atomIndex
      rw [hresidueApply]
      simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsplit, Matrix.mulVec_sub, Matrix.mulVec_smul, hcolumnFix, hfix]
  have hresidueMin : residueVec minLabel = 0 := by
    rw [hresidueApply, hclassIn minLabel hminMem, hratio,
      div_mul_cancel₀ _ (rootWeight_pos D minLabel).ne', sub_self]
  have hresidueZero : ∀ member ∈ tieClass D pivot, residueVec member = 0 := by
    have hrow := congrFun hresidueFix minLabel
    rw [hresidueMin] at hrow
    have hsum : ∑ other, normalizedCoupling D minLabel other * residueVec other = 0 := hrow
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg fun member (_ : member ∈ Finset.univ) =>
      mul_nonneg (hnn minLabel member) (hresidueNonneg member)).mp hsum
    intro member hmem
    have hpos : 0 < normalizedCoupling D minLabel member := by
      rw [normalizedCoupling_pos_iff]
      have hone := (mem_tieClass_iff D pivot minLabel).mp hminMem
      have htwo := (mem_tieClass_iff D pivot member).mp hmem
      rw [tieCoupling_comm] at hone
      exact tieCoupling_pos_trans D hheavy hnostrict hone htwo
    rcases mul_eq_zero.mp (hterms member (Finset.mem_univ member)) with h | h
    · exact absurd h hpos.ne'
    · exact h
  have hcolumnEq : ∀ member ∈ tieClass D pivot,
      columnVec member = ratio * rootWeight D member := by
    intro member hmem
    have hzero := hresidueZero member hmem
    rw [hresidueApply, hclassIn member hmem] at hzero
    linarith
  -- The ratio is pinned by the row law.
  have hclassWeight : ∑ member ∈ tieClass D pivot, D.weight member
      = ∑ member ∈ tieClass D pivot, rootWeight D member * rootWeight D member :=
    Finset.sum_congr rfl fun member _ => (rootWeight_mul_self D member).symm
  have hpin : ratio * (∑ member ∈ tieClass D pivot, D.weight member)
      = rootWeight D memberSecond := by
    have hrow := congrFun hfix memberSecond
    rw [hclassIn memberSecond hsecond] at hrow
    have hsum : ∑ other, normalizedCoupling D memberSecond other * classVec other
        = rootWeight D memberSecond := hrow
    have hconv : ∀ other : Fin m, normalizedCoupling D memberSecond other * classVec other
        = if other ∈ tieClass D pivot then
            ratio * (rootWeight D other * rootWeight D other) else 0 := by
      intro other
      by_cases hother : other ∈ tieClass D pivot
      · rw [hclassIn other hother, hsymmEntry memberSecond other, ← hcolumnApply,
          hcolumnEq other hother]
        simp [hother]; ring
      · rw [hclassOut other hother]
        simp [hother]
    rw [Finset.sum_congr rfl fun other (_ : other ∈ Finset.univ) => hconv other,
      ← Finset.sum_filter] at hsum
    rw [← hsum, hclassWeight, ← Finset.mul_sum, Finset.filter_univ_mem]
  -- Assemble.
  have hcoupling : tieCoupling D memberFirst memberSecond
      = rootWeight D memberFirst * rootWeight D memberSecond
        * (ratio * rootWeight D memberFirst) := by
    rw [tieCoupling_eq_rootWeight_mul]
    congr 1
    rw [← hcolumnApply memberFirst, hcolumnEq memberFirst hfirst]
  rw [hcoupling]
  have hfirstRoot := rootWeight_mul_self D memberFirst
  have hsecondRoot := rootWeight_mul_self D memberSecond
  calc rootWeight D memberFirst * rootWeight D memberSecond
        * (ratio * rootWeight D memberFirst)
        * (∑ member ∈ tieClass D pivot, D.weight member)
      = (rootWeight D memberFirst * rootWeight D memberFirst) * rootWeight D memberSecond
        * (ratio * (∑ member ∈ tieClass D pivot, D.weight member)) := by ring
    _ = D.weight memberFirst * D.weight memberSecond := by
        rw [hfirstRoot, hpin, mul_assoc, hsecondRoot]

/-! ## Part H: the classification

Everything below reads off the rank-one block.  Its DIAGONAL says `2 l_c - 1 = 1/T_A`,
so the leverage is constant on a class and is what the class weight dictates.  Its
OFF-DIAGONAL then says `J_cd = 0`, so the class is a parallel class. -/

/-- A two by two symmetric matrix with nonnegative determinant and nonnegative trace is
positive semidefinite. -/
theorem posSemidef_two_of_det_nonneg_of_trace_nonneg {gapMatrix : Matrix (Fin 2) (Fin 2) ℝ}
    (hsymm : gapMatrixᵀ = gapMatrix) (hdet : 0 ≤ gapMatrix.det)
    (htrace : 0 ≤ gapMatrix 0 0 + gapMatrix 1 1) : gapMatrix.PosSemidef := by
  have hcross : gapMatrix 1 0 = gapMatrix 0 1 := by
    have hentry := congrFun (congrFun hsymm 0) 1
    rwa [Matrix.transpose_apply] at hentry
  rw [Matrix.det_fin_two, hcross] at hdet
  rw [posSemidef_two_iff hsymm]
  refine ⟨?_, ?_, by nlinarith [sq_nonneg (gapMatrix 0 1)]⟩
  · by_contra hcontra
    push_neg at hcontra
    nlinarith [sq_nonneg (gapMatrix 0 1)]
  · by_contra hcontra
    push_neg at hcontra
    nlinarith [sq_nonneg (gapMatrix 0 1)]

/-- **The class leverage.**  Every atom of a class carries the same leverage, and the
class weight dictates it: `(2 l_c - 1) T_A = 1`, that is `l_c = (1 + 1/T_A)/2`. -/
theorem two_leverage_sub_one_mul_classWeight (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (pivot : Fin m) {member : Fin m}
    (hmember : member ∈ tieClass D pivot) :
    (2 * leverageOf (D.atom member) - 1) * (∑ other ∈ tieClass D pivot, D.weight other) = 1 := by
  have hblock := tieCoupling_mul_classWeight D hheavy hnostrict pivot hmember hmember
  rw [tieCoupling_self] at hblock
  have hweight := D.weight_pos member
  have hsq : (0 : ℝ) < D.weight member ^ 2 := by positivity
  nlinarith [hblock, hsq]

/-- **Same class implies parallel.**  The diagonal of the rank-one block equalises the
leverages, and then the off-diagonal forces the wedge to vanish. -/
theorem planeWedge_eq_zero_of_mem_tieClass (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (pivot : Fin m) {memberFirst memberSecond : Fin m}
    (hfirst : memberFirst ∈ tieClass D pivot) (hsecond : memberSecond ∈ tieClass D pivot) :
    planeWedge (D.atom memberFirst) (D.atom memberSecond) = 0 := by
  have hweightPos := classWeight_pos D hheavy pivot
  have hlevFirst := two_leverage_sub_one_mul_classWeight D hheavy hnostrict pivot hfirst
  have hlevSecond := two_leverage_sub_one_mul_classWeight D hheavy hnostrict pivot hsecond
  have hblock := tieCoupling_mul_classWeight D hheavy hnostrict pivot hfirst hsecond
  rw [tieCoupling] at hblock
  have hfirstWeight := D.weight_pos memberFirst
  have hsecondWeight := D.weight_pos memberSecond
  have hlevEq : leverageOf (D.atom memberFirst) = leverageOf (D.atom memberSecond) := by
    have hdiff : (2 * leverageOf (D.atom memberFirst) - 2 * leverageOf (D.atom memberSecond))
        * (∑ other ∈ tieClass D pivot, D.weight other) = 0 := by
      linear_combination hlevFirst - hlevSecond
    rcases mul_eq_zero.mp hdiff with h | h
    · linarith
    · exact absurd h hweightPos.ne'
  have hprod : (0 : ℝ) < D.weight memberFirst * D.weight memberSecond :=
    mul_pos hfirstWeight hsecondWeight
  have hrw : D.weight memberFirst * D.weight memberSecond
        * ((leverageOf (D.atom memberFirst) + leverageOf (D.atom memberSecond) - 1
            - planeWedge (D.atom memberFirst) (D.atom memberSecond) ^ 2)
          * (∑ other ∈ tieClass D pivot, D.weight other))
      = D.weight memberFirst * D.weight memberSecond * 1 := by
    linear_combination hblock
  have hcancel : (leverageOf (D.atom memberFirst) + leverageOf (D.atom memberSecond) - 1
        - planeWedge (D.atom memberFirst) (D.atom memberSecond) ^ 2)
      * (∑ other ∈ tieClass D pivot, D.weight other) = 1 :=
    mul_left_cancel₀ hprod.ne' hrw
  have hwedgeSq : planeWedge (D.atom memberFirst) (D.atom memberSecond) ^ 2
      * (∑ other ∈ tieClass D pivot, D.weight other) = 0 := by
    linear_combination hlevFirst - hcancel
      - (∑ other ∈ tieClass D pivot, D.weight other) * hlevEq
  have hzero : planeWedge (D.atom memberFirst) (D.atom memberSecond) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hwedgeSq with h | h
    · exact h
    · exact absurd h hweightPos.ne'
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero

/-- **Parallel implies same class**, because a parallel pair couples strictly
positively. -/
theorem mem_tieClass_of_planeWedge_eq_zero (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    {pivot other : Fin m} (hwedge : planeWedge (D.atom pivot) (D.atom other) = 0) :
    other ∈ tieClass D pivot := by
  rw [mem_tieClass_iff]
  exact tieCoupling_pos_of_planeWedge_eq_zero D hheavy hwedge

/-- **THE CLASS CRITERION.**  Two atoms are in the same class exactly when they are
parallel. -/
theorem mem_tieClass_iff_planeWedge_eq_zero (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (pivot other : Fin m) :
    other ∈ tieClass D pivot ↔ planeWedge (D.atom pivot) (D.atom other) = 0 := by
  constructor
  · intro hmem
    exact planeWedge_eq_zero_of_mem_tieClass D hheavy hnostrict pivot
      (self_mem_tieClass D hheavy pivot) hmem
  · exact mem_tieClass_of_planeWedge_eq_zero D hheavy

/-- **Cross-class pairs weakly dominate.**  Their coupling vanishes, so the gap
determinant vanishes, and heaviness makes the trace nonnegative. -/
theorem dominates_of_planeWedge_ne_zero (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) {atomFirst atomSecond : Fin m}
    (hdistinct : atomFirst ≠ atomSecond)
    (hwedge : planeWedge (D.atom atomFirst) (D.atom atomSecond) ≠ 0) :
    Dominates D {atomFirst, atomSecond} := by
  have hnotmem : atomSecond ∉ tieClass D atomFirst := by
    rw [mem_tieClass_iff_planeWedge_eq_zero D hheavy hnostrict]
    exact hwedge
  have hzero := tieCoupling_eq_zero_of_not_mem D hheavy hnostrict
    (self_mem_tieClass D hheavy atomFirst) hnotmem
  rw [tieCoupling_eq_neg_det D hdistinct, neg_eq_zero] at hzero
  have hweights := mul_pos (D.weight_pos atomFirst) (D.weight_pos atomSecond)
  have hdet : (subsetSum D {atomFirst, atomSecond} - 1).det = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hweights.ne'
    · exact h
  refine posSemidef_two_of_det_nonneg_of_trace_nonneg (pairGap_transpose D _)
    (le_of_eq hdet.symm) ?_
  rw [trace_pairGap_eq D hdistinct]
  linarith [hheavy atomFirst, hheavy atomSecond]

/-- **The gap determinant inside a class** is `-1/T_A`: no pair of a class dominates,
and the deficit is exactly the reciprocal of the class weight. -/
theorem det_pairGap_mul_classWeight_of_mem_tieClass (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (pivot : Fin m) {memberFirst memberSecond : Fin m}
    (hdistinct : memberFirst ≠ memberSecond) (hfirst : memberFirst ∈ tieClass D pivot)
    (hsecond : memberSecond ∈ tieClass D pivot) :
    (subsetSum D {memberFirst, memberSecond} - 1).det
        * (∑ other ∈ tieClass D pivot, D.weight other) = -1 := by
  have hblock := tieCoupling_mul_classWeight D hheavy hnostrict pivot hfirst hsecond
  rw [tieCoupling_eq_neg_det D hdistinct] at hblock
  have hfirstWeight := D.weight_pos memberFirst
  have hsecondWeight := D.weight_pos memberSecond
  have hprod := mul_pos hfirstWeight hsecondWeight
  nlinarith [hblock, hprod]

/-! ### The class count is three -/

/-- The trace identity in design vocabulary: `sum_c t_c (2 l_c - 1) = 2k - 1 = 3`. -/
theorem sum_weight_mul_two_leverage_sub_one (D : WeightedDesign m 2) :
    ∑ atomIndex, D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1) = 3 := by
  rw [← trace_normalizedCoupling D]
  exact (Finset.sum_congr rfl fun atomIndex _ => normalizedCoupling_diag D atomIndex).symm

/-- The fibre of the class map over a class is that class. -/
theorem filter_tieClass_eq (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (pivot : Fin m) :
    Finset.univ.filter (fun atomIndex => tieClass D atomIndex = tieClass D pivot)
      = tieClass D pivot := by
  ext atomIndex
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hclass
    rw [← hclass]
    exact self_mem_tieClass D hheavy atomIndex
  · intro hmem
    exact tieClass_eq_of_mem D hheavy hnostrict hmem

/-- Each class carries exactly one unit of the trace. -/
theorem sum_class_weight_mul_two_leverage_sub_one (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (pivot : Fin m) :
    ∑ member ∈ tieClass D pivot,
      D.weight member * (2 * leverageOf (D.atom member) - 1) = 1 := by
  have hweightPos := classWeight_pos D hheavy pivot
  have hscaled : (∑ member ∈ tieClass D pivot,
        D.weight member * (2 * leverageOf (D.atom member) - 1))
      * (∑ other ∈ tieClass D pivot, D.weight other)
      = ∑ other ∈ tieClass D pivot, D.weight other := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun member hmember => ?_
    have hlev := two_leverage_sub_one_mul_classWeight D hheavy hnostrict pivot hmember
    calc D.weight member * (2 * leverageOf (D.atom member) - 1)
          * (∑ other ∈ tieClass D pivot, D.weight other)
        = D.weight member
            * ((2 * leverageOf (D.atom member) - 1)
              * (∑ other ∈ tieClass D pivot, D.weight other)) := by ring
      _ = D.weight member := by rw [hlev, mul_one]
  exact mul_right_cancel₀ hweightPos.ne' (by rw [hscaled, one_mul])

/-- **THERE ARE EXACTLY THREE CLASSES.**  The trace is `2k - 1 = 3` and each class
carries exactly one unit of it. -/
theorem card_image_tieClass_eq_three (D : WeightedDesign m 2)
    (hheavy : ∀ atomIndex : Fin m, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) :
    (Finset.univ.image (tieClass D)).card = 3 := by
  classical
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin m))) (t := Finset.univ.image (tieClass D))
    (g := tieClass D) (f := fun atomIndex => D.weight atomIndex
      * (2 * leverageOf (D.atom atomIndex) - 1))
    (fun atomIndex _ => Finset.mem_image_of_mem _ (Finset.mem_univ atomIndex))
  rw [sum_weight_mul_two_leverage_sub_one D] at hfiber
  have hunits : ∀ classSet ∈ Finset.univ.image (tieClass D),
      ∑ atomIndex ∈ Finset.univ.filter (fun atomIndex => tieClass D atomIndex = classSet),
        D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1) = 1 := by
    intro classSet hclassSet
    obtain ⟨pivot, _, hpivot⟩ := Finset.mem_image.mp hclassSet
    subst hpivot
    rw [filter_tieClass_eq D hheavy hnostrict pivot]
    exact sum_class_weight_mul_two_leverage_sub_one D hheavy hnostrict pivot
  rw [Finset.sum_congr rfl hunits, Finset.sum_const, nsmul_eq_mul, mul_one] at hfiber
  exact_mod_cast hfiber

/-! ### Ties, and the hinge at rank two -/

/-- A rank-two tie has no strictly dominating pair. -/
theorem noStrictPair_of_isTie {size : ℕ} (D : WeightedDesign size 2) (htie : IsTie D) :
    NoStrictPair D := fun atomFirst atomSecond hdistinct =>
  htie.2 {atomFirst, atomSecond} (Finset.card_pair hdistinct)

/-- **Every atom of a rank-two tie is heavy**, unconditionally: the leverage floor
`Gtz.leverage_one_le_of_isTie` runs on the LANDED rank-two GTZ one size down. -/
theorem heavy_of_isTie {size : ℕ} (D : WeightedDesign size 2) (htie : IsTie D)
    (label : Fin size) : 1 ≤ leverageOf (D.atom label) := by
  have hsize : 2 ≤ size := rank_le_of_design D
  obtain ⟨predSize, rfl⟩ : ∃ predSize, size = predSize + 1 := ⟨size - 1, by omega⟩
  exact leverage_one_le_of_isTie D (by omega) (gtz_rank_two predSize) htie label

/-- **A design with no strictly dominating pair and no parallel pair has exactly THREE
atoms.**  Every class is then a singleton, so the trace `3` counts the atoms. -/
theorem size_eq_three_of_pairwise_nonParallel {size : ℕ} (D : WeightedDesign size 2)
    (hheavy : ∀ atomIndex : Fin size, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D)
    (hnonParallel : ∀ atomFirst atomSecond : Fin size, atomFirst ≠ atomSecond →
      planeWedge (D.atom atomFirst) (D.atom atomSecond) ≠ 0) :
    size = 3 := by
  have hsingleton : ∀ atomIndex : Fin size, tieClass D atomIndex = {atomIndex} := by
    intro atomIndex
    ext other
    simp only [Finset.mem_singleton]
    constructor
    · intro hmem
      by_contra hne
      exact hnonParallel atomIndex other (Ne.symm hne)
        ((mem_tieClass_iff_planeWedge_eq_zero D hheavy hnostrict atomIndex other).mp hmem)
    · intro heq
      subst heq
      exact self_mem_tieClass D hheavy other
  have hunit : ∀ atomIndex : Fin size,
      D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1) = 1 := by
    intro atomIndex
    have hlev := two_leverage_sub_one_mul_classWeight D hheavy hnostrict atomIndex
      (self_mem_tieClass D hheavy atomIndex)
    rw [hsingleton atomIndex, Finset.sum_singleton] at hlev
    linarith [hlev]
  have hcount := sum_weight_mul_two_leverage_sub_one D
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hunit atomIndex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hcount
  exact_mod_cast hcount

/-- **THE HINGE AT RANK TWO.**  Every exact tie on four or more atoms carries a
parallel pair.

The tree already reaches this conclusion through the Bloch-chart equality stratum
(`Gtz.not_isTie_of_fourNonParallel`).  What is new here is the road: the conclusion
is a two-line consequence of the CLASSIFICATION, because three classes cannot hold
four pairwise non-parallel atoms. -/
theorem hingeHoldsAtSize_rank_two (size : ℕ) (hsize : 4 ≤ size) : HingeHoldsAtSize size 2 := by
  intro D htie
  by_contra hnoPair
  have hheavy := heavy_of_isTie D htie
  have hnostrict := noStrictPair_of_isTie D htie
  have hnonParallel : ∀ atomFirst atomSecond : Fin size, atomFirst ≠ atomSecond →
      planeWedge (D.atom atomFirst) (D.atom atomSecond) ≠ 0 := by
    intro atomFirst atomSecond hdistinct hwedge
    obtain ⟨scale, hscale⟩ :=
      exists_smul_of_planeWedge_eq_zero (atom_ne_zero_of_heavy D hheavy atomFirst) hwedge
    exact hnoPair ⟨atomFirst, atomSecond, scale, hdistinct, hscale⟩
  have := size_eq_three_of_pairwise_nonParallel D hheavy hnostrict hnonParallel
  omega

/-- **At three atoms every class is a singleton**, so all three pairs weakly dominate
and the leverages are `l_c = (1 + t_c)/(2 t_c)`.  The weights are NOT forced to be
uniform: the classification constrains only the three directions and the three class
weights. -/
theorem rankTwoTie_three_atoms (D : WeightedDesign 3 2) (htie : IsTie D) :
    (∀ atomIndex : Fin 3,
        D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1) = 1) ∧
      ∀ atomFirst atomSecond : Fin 3, atomFirst ≠ atomSecond →
        Dominates D {atomFirst, atomSecond} := by
  have hheavy := heavy_of_isTie D htie
  have hnostrict := noStrictPair_of_isTie D htie
  have hnonParallel : ∀ atomFirst atomSecond : Fin 3, atomFirst ≠ atomSecond →
      planeWedge (D.atom atomFirst) (D.atom atomSecond) ≠ 0 := by
    intro atomFirst atomSecond hdistinct hwedge
    have hmem := mem_tieClass_of_planeWedge_eq_zero D hheavy hwedge
    have hclassSum := two_leverage_sub_one_mul_classWeight D hheavy hnostrict atomFirst hmem
    have hself := two_leverage_sub_one_mul_classWeight D hheavy hnostrict atomFirst
      (self_mem_tieClass D hheavy atomFirst)
    -- Two distinct atoms in one class would make four classes impossible at three atoms.
    have hclassCard := card_image_tieClass_eq_three D hheavy hnostrict
    have hsub : Finset.univ.image (tieClass D) ⊆ Finset.univ.image (tieClass D) := le_refl _
    have hbound : (Finset.univ.image (tieClass D)).card ≤ (Finset.univ : Finset (Fin 3)).card :=
      Finset.card_image_le
    rw [hclassCard, Finset.card_univ, Fintype.card_fin] at hbound
    -- Three classes on three atoms forces the class map to be injective.
    have hinj : Function.Injective (tieClass D) := by
      have hcard : (Finset.univ.image (tieClass D)).card = (Finset.univ : Finset (Fin 3)).card := by
        rw [hclassCard, Finset.card_univ, Fintype.card_fin]
      exact fun labelFirst labelSecond hlabels => by
        have := Finset.card_image_iff.mp hcard
        exact this (Finset.mem_coe.mpr (Finset.mem_univ labelFirst))
          (Finset.mem_coe.mpr (Finset.mem_univ labelSecond)) hlabels
    exact hdistinct (hinj (tieClass_eq_of_mem D hheavy hnostrict hmem).symm)
  refine ⟨fun atomIndex => ?_, fun atomFirst atomSecond hdistinct =>
    dominates_of_planeWedge_ne_zero D hheavy hnostrict hdistinct
      (hnonParallel atomFirst atomSecond hdistinct)⟩
  have hsingleton : tieClass D atomIndex = {atomIndex} := by
    ext other
    simp only [Finset.mem_singleton]
    constructor
    · intro hmem
      by_contra hne
      exact hnonParallel atomIndex other (Ne.symm hne)
        ((mem_tieClass_iff_planeWedge_eq_zero D hheavy hnostrict atomIndex other).mp hmem)
    · intro heq
      subst heq
      exact self_mem_tieClass D hheavy other
  have hlev := two_leverage_sub_one_mul_classWeight D hheavy hnostrict atomIndex
    (self_mem_tieClass D hheavy atomIndex)
  rw [hsingleton, Finset.sum_singleton] at hlev
  linarith [hlev]

/-! ## Part I: the capstone, and the rank-three payload -/

/-- **THE CLASSIFICATION OF RANK-TWO TIES.**  Every exact rank-two tie splits into
exactly THREE classes.  Two atoms share a class exactly when they are parallel.  On a
class the leverage is constant and dictated by the class weight, `(2 l - 1) T_A = 1`.
Every cross-class pair weakly dominates, and every within-class pair has gap
determinant `-1/T_A`.

The hypotheses are only `Gtz.IsTie`; heaviness comes from the landed rank-two GTZ one
size down (`Gtz.gtz_rank_two` through `Gtz.leverage_one_le_of_isTie`), and no strictly
dominating pair is the second clause of the tie. -/
theorem rankTwoTieClassification {size : ℕ} (D : WeightedDesign size 2) (htie : IsTie D) :
    (Finset.univ.image (tieClass D)).card = 3
      ∧ (∀ pivot other : Fin size,
          other ∈ tieClass D pivot ↔ planeWedge (D.atom pivot) (D.atom other) = 0)
      ∧ (∀ pivot member : Fin size, member ∈ tieClass D pivot →
          (2 * leverageOf (D.atom member) - 1)
            * (∑ other ∈ tieClass D pivot, D.weight other) = 1)
      ∧ (∀ atomFirst atomSecond : Fin size, atomFirst ≠ atomSecond →
          planeWedge (D.atom atomFirst) (D.atom atomSecond) ≠ 0 →
            Dominates D {atomFirst, atomSecond})
      ∧ (∀ pivot memberFirst memberSecond : Fin size, memberFirst ≠ memberSecond →
          memberFirst ∈ tieClass D pivot → memberSecond ∈ tieClass D pivot →
            (subsetSum D {memberFirst, memberSecond} - 1).det
              * (∑ other ∈ tieClass D pivot, D.weight other) = -1) := by
  have hheavy := heavy_of_isTie D htie
  have hnostrict := noStrictPair_of_isTie D htie
  exact ⟨card_image_tieClass_eq_three D hheavy hnostrict,
    mem_tieClass_iff_planeWedge_eq_zero D hheavy hnostrict,
    fun pivot member hmember =>
      two_leverage_sub_one_mul_classWeight D hheavy hnostrict pivot hmember,
    fun atomFirst atomSecond hdistinct hwedge =>
      dominates_of_planeWedge_ne_zero D hheavy hnostrict hdistinct hwedge,
    fun pivot memberFirst memberSecond hdistinct hfirst hsecond =>
      det_pairGap_mul_classWeight_of_mem_tieClass D hheavy hnostrict pivot hdistinct
        hfirst hsecond⟩

/-- The leverage of a plane shadow atom, in frame coordinates. -/
theorem leverageOf_inPlaneRestriction_atom {size : ℕ} (design : WeightedDesign size 3)
    (basisFirst basisSecond : Fin 3 → ℝ) (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1) (horth : basisFirst ⬝ᵥ basisSecond = 0)
    (label : Fin size) :
    leverageOf ((inPlaneRestriction design basisFirst basisSecond hfirstUnit hsecondUnit
        horth).atom label)
      = (design.atom label ⬝ᵥ basisFirst) ^ 2 + (design.atom label ⬝ᵥ basisSecond) ^ 2 := by
  simp [inPlaneRestriction, leverageOf, Fin.sum_univ_two]

/-- The wedge of two plane shadow atoms is the frame bracket, which the tree reads as
the triple bracket against the normal
(`Gtz.pairBracket_inPlaneRestriction_eq_frameOrientation_mul_tripleBracket`). -/
theorem planeWedge_inPlaneRestriction {size : ℕ} (design : WeightedDesign size 3)
    (basisFirst basisSecond : Fin 3 → ℝ) (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1) (horth : basisFirst ⬝ᵥ basisSecond = 0)
    (labelFirst labelSecond : Fin size) :
    planeWedge
        ((inPlaneRestriction design basisFirst basisSecond hfirstUnit hsecondUnit horth).atom
          labelFirst)
        ((inPlaneRestriction design basisFirst basisSecond hfirstUnit hsecondUnit horth).atom
          labelSecond)
      = (design.atom labelFirst ⬝ᵥ basisFirst) * (design.atom labelSecond ⬝ᵥ basisSecond)
        - (design.atom labelFirst ⬝ᵥ basisSecond) * (design.atom labelSecond ⬝ᵥ basisFirst) := by
  simp [inPlaneRestriction, planeWedge]

/-- **THE RANK-THREE PAYLOAD.**  Every two-dimensional subspace of `R^3` carries a
rank-two shadow of a rank-three design, because Parseval restricts to the plane
(`Gtz.inPlaneRestriction`).  So the classification reads on the whole sphere of
normals: at four or more atoms, a plane whose shadow is heavy and carries no strictly
dominating pair must have TWO atoms whose frame bracket vanishes — that is, two atoms
whose plane shadows are parallel.

The bracket in the conclusion is the triple bracket of the two atoms against the
normal of the plane, up to the sign of the frame
(`Gtz.pairBracket_inPlaneRestriction_eq_frameOrientation_mul_tripleBracket`). -/
theorem planeShadow_exists_frameBracket_eq_zero {size : ℕ} (design : WeightedDesign size 3)
    (basisFirst basisSecond : Fin 3 → ℝ) (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1) (horth : basisFirst ⬝ᵥ basisSecond = 0)
    (hsize : 4 ≤ size)
    (hheavy : ∀ label : Fin size, 1 ≤ (design.atom label ⬝ᵥ basisFirst) ^ 2
      + (design.atom label ⬝ᵥ basisSecond) ^ 2)
    (hnostrict : NoStrictPair
      (inPlaneRestriction design basisFirst basisSecond hfirstUnit hsecondUnit horth)) :
    ∃ labelFirst labelSecond : Fin size, labelFirst ≠ labelSecond ∧
      (design.atom labelFirst ⬝ᵥ basisFirst) * (design.atom labelSecond ⬝ᵥ basisSecond)
        - (design.atom labelFirst ⬝ᵥ basisSecond) * (design.atom labelSecond ⬝ᵥ basisFirst)
        = 0 := by
  set shadow := inPlaneRestriction design basisFirst basisSecond hfirstUnit hsecondUnit horth
    with hshadow
  have hshadowHeavy : ∀ label : Fin size, 1 ≤ leverageOf (shadow.atom label) := by
    intro label
    rw [hshadow, leverageOf_inPlaneRestriction_atom]
    exact hheavy label
  by_contra hcontra
  push_neg at hcontra
  have hnonParallel : ∀ labelFirst labelSecond : Fin size, labelFirst ≠ labelSecond →
      planeWedge (shadow.atom labelFirst) (shadow.atom labelSecond) ≠ 0 := by
    intro labelFirst labelSecond hdistinct
    rw [hshadow, planeWedge_inPlaneRestriction]
    exact hcontra labelFirst labelSecond hdistinct
  have := size_eq_three_of_pairwise_nonParallel shadow hshadowHeavy hnostrict hnonParallel
  omega

/-- **The plane-shadow classification, in full.**  The three classes of the shadow are
the three frame-bracket classes, and the shadow leverage of a class is dictated by the
class weight.  This is the classification read on one plane of a rank-three design. -/
theorem planeShadow_three_classes {size : ℕ} (design : WeightedDesign size 3)
    (basisFirst basisSecond : Fin 3 → ℝ) (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1) (horth : basisFirst ⬝ᵥ basisSecond = 0)
    (hheavy : ∀ label : Fin size, 1 ≤ (design.atom label ⬝ᵥ basisFirst) ^ 2
      + (design.atom label ⬝ᵥ basisSecond) ^ 2)
    (hnostrict : NoStrictPair
      (inPlaneRestriction design basisFirst basisSecond hfirstUnit hsecondUnit horth)) :
    (Finset.univ.image (tieClass
        (inPlaneRestriction design basisFirst basisSecond hfirstUnit hsecondUnit horth))).card = 3
      ∧ ∀ pivot member : Fin size,
          member ∈ tieClass
              (inPlaneRestriction design basisFirst basisSecond hfirstUnit hsecondUnit horth) pivot
            ↔ (design.atom pivot ⬝ᵥ basisFirst) * (design.atom member ⬝ᵥ basisSecond)
              - (design.atom pivot ⬝ᵥ basisSecond) * (design.atom member ⬝ᵥ basisFirst) = 0 := by
  set shadow := inPlaneRestriction design basisFirst basisSecond hfirstUnit hsecondUnit horth
    with hshadow
  have hshadowHeavy : ∀ label : Fin size, 1 ≤ leverageOf (shadow.atom label) := by
    intro label
    rw [hshadow, leverageOf_inPlaneRestriction_atom]
    exact hheavy label
  refine ⟨card_image_tieClass_eq_three shadow hshadowHeavy hnostrict, fun pivot member => ?_⟩
  rw [mem_tieClass_iff_planeWedge_eq_zero shadow hshadowHeavy hnostrict, hshadow,
    planeWedge_inPlaneRestriction]

/-! ### The count of weakly dominating pairs

Three classes on `m` atoms leave at most `(m-2)(m-3)/2` parallel pairs, so at least
`2m - 3` pairs weakly dominate.  At five atoms that is SEVEN, which is the number
Question 7.1 of the campaign asks for in its rank-two form, with room. -/

/-- The class of an atom has at most `size - 2` members, because the other two classes
are nonempty. -/
theorem card_tieClass_le {size : ℕ} (D : WeightedDesign size 2)
    (hheavy : ∀ atomIndex : Fin size, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (pivot : Fin size) :
    (tieClass D pivot).card + 2 ≤ size := by
  classical
  have hcount := card_image_tieClass_eq_three D hheavy hnostrict
  have hcard : ∑ classSet ∈ Finset.univ.image (tieClass D), classSet.card = size := by
    have hfiber := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin size))) (t := Finset.univ.image (tieClass D))
      (f := tieClass D) (fun atomIndex _ => Finset.mem_image_of_mem _ (Finset.mem_univ atomIndex))
    rw [Finset.card_univ, Fintype.card_fin] at hfiber
    have hcongr : ∑ classSet ∈ Finset.univ.image (tieClass D), classSet.card
        = ∑ classSet ∈ Finset.univ.image (tieClass D),
          (Finset.univ.filter (fun atomIndex => tieClass D atomIndex = classSet)).card := by
      refine Finset.sum_congr rfl fun classSet hclassSet => ?_
      obtain ⟨other, _, hother⟩ := Finset.mem_image.mp hclassSet
      subst hother
      rw [filter_tieClass_eq D hheavy hnostrict other]
    exact hcongr.trans hfiber.symm
  have hmem : tieClass D pivot ∈ Finset.univ.image (tieClass D) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ pivot)
  have hrest : ∑ classSet ∈ (Finset.univ.image (tieClass D)).erase (tieClass D pivot),
      classSet.card ≥ 2 := by
    have hcardErase : ((Finset.univ.image (tieClass D)).erase (tieClass D pivot)).card = 2 := by
      rw [Finset.card_erase_of_mem hmem, hcount]
    have hpos : ∀ classSet ∈ (Finset.univ.image (tieClass D)).erase (tieClass D pivot),
        1 ≤ classSet.card := by
      intro classSet hclassSet
      obtain ⟨other, _, hother⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hclassSet)
      subst hother
      exact Finset.card_pos.mpr ⟨other, self_mem_tieClass D hheavy other⟩
    have hle := Finset.card_nsmul_le_sum
      ((Finset.univ.image (tieClass D)).erase (tieClass D pivot))
      (fun classSet => classSet.card) 1 hpos
    simpa [hcardErase] using hle
  have hsplit := Finset.add_sum_erase _ (fun classSet => Finset.card classSet) hmem
  omega

/-- The partners of an atom split into its class and the atoms it weakly dominates
with. -/
theorem card_dominatingPartners_add_card_tieClass {size : ℕ} (D : WeightedDesign size 2)
    (hheavy : ∀ atomIndex : Fin size, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (pivot : Fin size) :
    (Finset.univ.filter fun other =>
          planeWedge (D.atom pivot) (D.atom other) ≠ 0).card + (tieClass D pivot).card = size := by
  classical
  have hclass : tieClass D pivot
      = Finset.univ.filter fun other => ¬ planeWedge (D.atom pivot) (D.atom other) ≠ 0 := by
    ext other
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    exact mem_tieClass_iff_planeWedge_eq_zero D hheavy hnostrict pivot other
  rw [hclass, Finset.card_filter_add_card_filter_not
    (fun other => planeWedge (D.atom pivot) (D.atom other) ≠ 0), Finset.card_univ,
    Fintype.card_fin]

/-- **Every atom weakly dominates with at least two others.**  Its class misses at
least the two other classes. -/
theorem two_le_card_dominatingPartners {size : ℕ} (D : WeightedDesign size 2)
    (hheavy : ∀ atomIndex : Fin size, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) (pivot : Fin size) :
    2 ≤ (Finset.univ.filter fun other =>
      planeWedge (D.atom pivot) (D.atom other) ≠ 0).card := by
  have hsplit := card_dominatingPartners_add_card_tieClass D hheavy hnostrict pivot
  have hbound := card_tieClass_le D hheavy hnostrict pivot
  omega

/-- The atom-wise class sizes add up to the sum of the squared class sizes. -/
theorem sum_card_tieClass_eq {size : ℕ} (D : WeightedDesign size 2)
    (hheavy : ∀ atomIndex : Fin size, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) :
    ∑ atomIndex, (tieClass D atomIndex).card
      = ∑ classSet ∈ Finset.univ.image (tieClass D), classSet.card * classSet.card := by
  classical
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin size))) (t := Finset.univ.image (tieClass D))
    (g := tieClass D) (f := fun atomIndex => (tieClass D atomIndex).card)
    (fun atomIndex _ => Finset.mem_image_of_mem _ (Finset.mem_univ atomIndex))
  rw [← hfiber]
  refine Finset.sum_congr rfl fun classSet hclassSet => ?_
  obtain ⟨pivot, _, hpivot⟩ := Finset.mem_image.mp hclassSet
  subst hpivot
  rw [filter_tieClass_eq D hheavy hnostrict pivot, Finset.sum_congr rfl
    (fun member hmember => congrArg Finset.card (tieClass_eq_of_mem D hheavy hnostrict hmember)),
    Finset.sum_const, smul_eq_mul]

/-- **The sharp class-size bound.**  Three nonempty classes on `size` atoms have
squared sizes summing to at most `(size - 2)^2 + 2`, the value at the split
`(size - 2, 1, 1)`. -/
theorem sum_card_tieClass_le {size : ℕ} (D : WeightedDesign size 2)
    (hheavy : ∀ atomIndex : Fin size, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) :
    (∑ atomIndex, (tieClass D atomIndex).card) + 4 * size ≤ size * size + 6 := by
  classical
  have hcount := card_image_tieClass_eq_three D hheavy hnostrict
  obtain ⟨classOne, classTwo, classThree, hne12, hne13, hne23, himage⟩ :=
    Finset.card_eq_three.mp hcount
  have hpos : ∀ classSet ∈ Finset.univ.image (tieClass D), 1 ≤ classSet.card := by
    intro classSet hclassSet
    obtain ⟨pivot, _, hpivot⟩ := Finset.mem_image.mp hclassSet
    subst hpivot
    exact Finset.card_pos.mpr ⟨pivot, self_mem_tieClass D hheavy pivot⟩
  have hsum : ∑ classSet ∈ Finset.univ.image (tieClass D), classSet.card = size := by
    have hfiber := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin size))) (t := Finset.univ.image (tieClass D))
      (f := tieClass D) (fun atomIndex _ => Finset.mem_image_of_mem _ (Finset.mem_univ atomIndex))
    rw [Finset.card_univ, Fintype.card_fin] at hfiber
    have hcongr : ∑ classSet ∈ Finset.univ.image (tieClass D), classSet.card
        = ∑ classSet ∈ Finset.univ.image (tieClass D),
          (Finset.univ.filter (fun atomIndex => tieClass D atomIndex = classSet)).card := by
      refine Finset.sum_congr rfl fun classSet hclassSet => ?_
      obtain ⟨other, _, hother⟩ := Finset.mem_image.mp hclassSet
      subst hother
      rw [filter_tieClass_eq D hheavy hnostrict other]
    exact hcongr.trans hfiber.symm
  rw [sum_card_tieClass_eq D hheavy hnostrict, himage] at *
  have honeMem : classOne ∈ ({classOne, classTwo, classThree} : Finset (Finset (Fin size))) := by
    simp
  have htwoMem : classTwo ∈ ({classOne, classTwo, classThree} : Finset (Finset (Fin size))) := by
    simp
  have hthreeMem : classThree ∈ ({classOne, classTwo, classThree} : Finset (Finset (Fin size))) := by
    simp
  have hone := hpos classOne honeMem
  have htwo := hpos classTwo htwoMem
  have hthree := hpos classThree hthreeMem
  rw [Finset.sum_insert (by simp [hne12, hne13]), Finset.sum_insert (by simp [hne23]),
    Finset.sum_singleton] at hsum ⊢
  nlinarith [hone, htwo, hthree, hsum]

/-- **THE PAIR COUNT.**  Summed over atoms, the number of partners that weakly
dominate is at least `4 * size - 6`, so at least `2 * size - 3` UNORDERED pairs weakly
dominate.  At five atoms that is SEVEN, the number Question 7.1 asks for in its
rank-two form, with room; at four atoms it is five, matching the measured count at
every minimiser found. -/
theorem four_mul_size_le_sum_card_dominatingPartners {size : ℕ} (D : WeightedDesign size 2)
    (hheavy : ∀ atomIndex : Fin size, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) :
    4 * size ≤ (∑ atomIndex, (Finset.univ.filter fun other =>
      planeWedge (D.atom atomIndex) (D.atom other) ≠ 0).card) + 6 := by
  classical
  have hsplit : (∑ atomIndex, (Finset.univ.filter fun other =>
        planeWedge (D.atom atomIndex) (D.atom other) ≠ 0).card)
      + ∑ atomIndex, (tieClass D atomIndex).card = size * size := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun atomIndex _ =>
      card_dominatingPartners_add_card_tieClass D hheavy hnostrict atomIndex,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hbound := sum_card_tieClass_le D hheavy hnostrict
  omega

/-- **At five atoms a tie has at least seven weakly dominating pairs**, in the summed
form.  The three classes split five atoms as `(3,1,1)` or `(2,2,1)`, giving seven or
eight cross-class pairs. -/
theorem fourteen_le_sum_card_dominatingPartners_five (D : WeightedDesign 5 2) (htie : IsTie D) :
    14 ≤ ∑ atomIndex, (Finset.univ.filter fun other =>
      planeWedge (D.atom atomIndex) (D.atom other) ≠ 0).card := by
  have hheavy := heavy_of_isTie D htie
  have hnostrict := noStrictPair_of_isTie D htie
  have := four_mul_size_le_sum_card_dominatingPartners D hheavy hnostrict
  omega

end Gtz

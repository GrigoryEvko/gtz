/-
# The max-volume selector at (7,3)-uniform: exchange bounds, isotropy in
# coordinates, the fifths floor, and the share-agnostic gate

Fix a weighted design and a rank-sized pick of atoms whose unit directions are
linearly independent.  Writing every atom in the picked basis (the `solveMatrix`
of the landed maximal-volume kit, instantiated at the design's unit-atom rows),
three facts stack:

* **Exchange.**  If no one-row swap increases the picked volume, every solve
  coordinate lies in `[-1, 1]` — `abs_solveMatrix_le_one_of_swapMaximalRowPick`,
  a swap-only sharpening of the landed
  `abs_solveMatrix_le_one_of_maximalVolume` (which quantified over all
  injective picks).
* **Isotropy in coordinates.**  The design law transported through the basis
  gives `Σ_c t_c x_c x_cᵀ = (S Sᵀ)⁻¹` for raw atoms, and at uniform share `s`
  the unit-atom version `Σ_c x_c x_cᵀ = s⁻¹ (Γ)⁻¹` with `Γ` the picked Gram.
  Splitting off the picked rows (where `x = e_j`) bounds every diagonal entry
  of `Γ⁻¹` by `s · (1 + #outside)` — at `(7,3)`: `15/7`, trace `45/7`.
* **The fifths floor.**  At `(7,3)`-uniform the trace cap forces
  `Γ - (1/5)·1 ⪰ 0`, and the boundary is *impossible*: it pins the Gram to the
  `(7/5, 7/5, 1/5)` sign pattern with all twelve outside coordinates `±1`, and
  a `±1` coordinate vector can never have unit norm against that Gram (the
  parity kill `extremalSignQuadratic_ne_one`).  Hence the strict
  `Γ - (1/5)·1 ≻ 0` — the fifths theorem, eigenvalue-free.

The scalar heart is a `(κ, β)`-parametrised master: for a unit-diagonal
symmetric `3×3` Gram with off-diagonal square sum `σ`, product `P`, the trace
cap `3 - σ ≤ κ · det` plus the universal AM–GM `27 P² ≤ σ³` force
`0 ≤ β³ - βσ + 2P = det(Γ - (1-β)·1)` whenever `κβ² + (κ-3)β = 2(κ-3)` and
`κβ ≤ κ - 1`.  Instances: `(κ, β) = (45/7, 4/5)` gives the `(7,3)` fifths
floor `1 - β = 1/5`; `(κ, β) = (6, (√17-1)/4)` gives the `(6,3)` equal-share
calibration floor `1 - β = (5 - √17)/4`.

The share-agnostic gate (rank 3, every size, every weights): if the picked
weight mass plus the reciprocal picked leverage mass reaches one,
`t(T) + 1/(ℓ_a + ℓ_b + ℓ_c) ≥ 1`, the pick dominates
(`dominates_of_pickWeight_add_inv_leverageSum`).  At `(7,3)` equal share the
left side is `3/7 + 1/9 = 34/63 < 1` — the gate is silent there, recorded as
`pickWeight_add_inv_leverageSum_lt_one_of_sevenThree`.
-/
import Gtz.Reduction.MaximalVolume
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.TauOrderStatistics
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Quantitative.GTransformGate
import Gtz.LinAlg.PsdKit
import Gtz.Core.Sanity

namespace Gtz

open Matrix

variable {frameSize selectionRank size rank : ℕ}

/-! ## The scalar heart: the trace-cap cubic master -/

/-- **The Newton half of the trace cap.**  For the elementary-symmetric data of
a unit-diagonal symmetric `3×3` matrix — `e₂ = 3 - σ`, `e₃ = 1 - σ + 2P` — the
universal AM–GM `27P² ≤ σ³` yields Newton's inequality `e₂² ≥ 9e₃`, and the
trace cap `e₂ ≤ κ·e₃` then forces `κ·e₂ ≥ 9`, i.e. `κσ ≤ 3κ - 9`. -/
theorem offSquareSumScaled_le_of_traceCap {capRatio squareSum tripleProduct : ℝ}
    (hcap : 0 < capRatio) (hupper : squareSum < 3) (hlower : 0 ≤ squareSum)
    (hamgm : 27 * tripleProduct ^ 2 ≤ squareSum ^ 3)
    (htrace : 0 ≤ capRatio * (1 - squareSum + 2 * tripleProduct) - (3 - squareSum)) :
    capRatio * squareSum ≤ 3 * capRatio - 9 := by
  have hnewton : 0 ≤ squareSum ^ 2 + 3 * squareSum - 18 * tripleProduct := by
    have hproduct : 0 ≤ (squareSum ^ 2 + 3 * squareSum - 18 * tripleProduct)
        * (squareSum ^ 2 + 3 * squareSum + 18 * tripleProduct) := by
      have hexpand : (squareSum ^ 2 + 3 * squareSum - 18 * tripleProduct)
          * (squareSum ^ 2 + 3 * squareSum + 18 * tripleProduct)
          = (squareSum * (squareSum - 3)) ^ 2
            + 12 * (squareSum ^ 3 - 27 * tripleProduct ^ 2) := by ring
      rw [hexpand]
      have hsquare := sq_nonneg (squareSum * (squareSum - 3))
      linarith
    rcases le_or_gt 0 (squareSum ^ 2 + 3 * squareSum - 18 * tripleProduct) with hok | hbad
    · exact hok
    · exfalso
      have hmass : 0 ≤ squareSum ^ 2 + 3 * squareSum := by
        have := sq_nonneg squareSum
        nlinarith
      have hsumNonpos : squareSum ^ 2 + 3 * squareSum + 18 * tripleProduct ≤ 0 := by
        by_contra hpos
        push Not at hpos
        have hnegprod := mul_pos (neg_pos.mpr hbad) hpos
        nlinarith [hproduct, hnegprod]
      linarith
  have hstep : 9 * (1 - squareSum + 2 * tripleProduct) ≤ (3 - squareSum) ^ 2 := by
    have hidentity : (3 - squareSum) ^ 2 - 9 * (1 - squareSum + 2 * tripleProduct)
        = squareSum ^ 2 + 3 * squareSum - 18 * tripleProduct := by ring
    linarith
  have hgapPos : 0 < 3 - squareSum := by linarith
  have htr : 3 - squareSum ≤ capRatio * (1 - squareSum + 2 * tripleProduct) := by linarith
  have hchain : 9 * (3 - squareSum) ≤ capRatio * (3 - squareSum) ^ 2 := by
    have hleft : 9 * (3 - squareSum) ≤ 9 * (capRatio * (1 - squareSum + 2 * tripleProduct)) := by
      linarith
    have hright : capRatio * (9 * (1 - squareSum + 2 * tripleProduct))
        ≤ capRatio * (3 - squareSum) ^ 2 :=
      mul_le_mul_of_nonneg_left hstep hcap.le
    nlinarith [hleft, hright]
  have hfloor : 9 ≤ capRatio * (3 - squareSum) := by
    nlinarith [hchain, hgapPos, mul_pos hgapPos hgapPos]
  nlinarith [hfloor]

/-- **THE TRACE-CAP CUBIC MASTER.**  The parametrised shifted-determinant floor:
with `σ ≥ 0`, the universal AM–GM `27P² ≤ σ³`, and the trace cap
`0 ≤ κ(1-σ+2P) - (3-σ)`, the root relation `κβ² + (κ-3)β = 2(κ-3)` and the
slack `κβ ≤ κ-1` force `0 ≤ β³ - βσ + 2P` — the determinant of the Gram
shifted by `1 - β`.  Case `4σ ≥ 3β²` is the exact linear identity
`κ·(β³-βσ+2P) = T + (κ-1-κβ)(σ - 3β²/4) + ((β+2)/4)·root`; case `4σ < 3β²`
rides the universal factorisation
`27β²(β²-σ)² - 4σ³ = (3β²-4σ)(σ-3β²)²`. -/
theorem shiftedDetThreshold_nonneg_of_traceCap {capRatio betaGap squareSum tripleProduct : ℝ}
    (hcap : 0 < capRatio) (hbeta : 0 < betaGap)
    (hroot : capRatio * betaGap ^ 2 + (capRatio - 3) * betaGap = 2 * (capRatio - 3))
    (hslack : capRatio * betaGap ≤ capRatio - 1)
    (hlower : 0 ≤ squareSum)
    (hamgm : 27 * tripleProduct ^ 2 ≤ squareSum ^ 3)
    (htrace : 0 ≤ capRatio * (1 - squareSum + 2 * tripleProduct) - (3 - squareSum)) :
    0 ≤ betaGap ^ 3 - betaGap * squareSum + 2 * tripleProduct := by
  rcases le_or_gt (3 * betaGap ^ 2) (4 * squareSum) with hbig | hsmall
  · -- the linear regime: the exact identity against the root relation
    have hrootZero : capRatio * betaGap ^ 2 + (capRatio - 3) * betaGap
        - 2 * (capRatio - 3) = 0 := by linarith
    have hidentity : capRatio * (betaGap ^ 3 - betaGap * squareSum + 2 * tripleProduct)
        = (capRatio * (1 - squareSum + 2 * tripleProduct) - (3 - squareSum))
          + (capRatio - 1 - capRatio * betaGap) * (squareSum - 3 * betaGap ^ 2 / 4)
          + (betaGap + 2) / 4
            * (capRatio * betaGap ^ 2 + (capRatio - 3) * betaGap - 2 * (capRatio - 3)) := by
      ring
    have hterm : 0 ≤ (capRatio - 1 - capRatio * betaGap) * (squareSum - 3 * betaGap ^ 2 / 4) :=
      mul_nonneg (by linarith) (by linarith)
    have hscaled : 0 ≤ capRatio * (betaGap ^ 3 - betaGap * squareSum + 2 * tripleProduct) := by
      rw [hidentity, hrootZero]
      have hzero : (betaGap + 2) / 4 * (0 : ℝ) = 0 := by ring
      rw [hzero]
      linarith
    exact (mul_nonneg_iff_of_pos_left hcap).mp hscaled
  · -- the AM–GM regime: the universal factorisation
    rcases le_or_gt 0 tripleProduct with hprodPos | hprodNeg
    · have hscaledSmall : betaGap * (4 * squareSum) < betaGap * (3 * betaGap ^ 2) :=
        mul_lt_mul_of_pos_left hsmall hbeta
      have hcube : 0 < betaGap ^ 3 := pow_pos hbeta 3
      nlinarith [hscaledSmall, hprodPos, hcube]
    · have hfactor : 27 * betaGap ^ 2 * (betaGap ^ 2 - squareSum) ^ 2 - 4 * squareSum ^ 3
          = (3 * betaGap ^ 2 - 4 * squareSum) * (squareSum - 3 * betaGap ^ 2) ^ 2 := by ring
      have hfactorPos : 0 ≤ (3 * betaGap ^ 2 - 4 * squareSum)
          * (squareSum - 3 * betaGap ^ 2) ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      have hcubeBound : 4 * squareSum ^ 3 ≤ 27 * betaGap ^ 2 * (betaGap ^ 2 - squareSum) ^ 2 := by
        linarith
      have hgapBound : 0 ≤ betaGap * (betaGap ^ 2 - squareSum) := by
        have hgap : 0 ≤ betaGap ^ 2 - squareSum := by nlinarith [sq_nonneg betaGap]
        exact mul_nonneg hbeta.le hgap
      have hsquares : (2 * tripleProduct) ^ 2 ≤ (betaGap * (betaGap ^ 2 - squareSum)) ^ 2 := by
        nlinarith [hamgm, hcubeBound]
      nlinarith [hsquares, hgapBound]

/-- **The (7,3) boundary is a single point.**  If the shifted determinant
`(4/5)³ - (4/5)σ + 2P` vanishes under the `(7,3)` trace cap, then
`σ = 12/25` and `P = -8/125` — the all-`(±2/5)` tetrahedral sign pattern.
Below `σ = 12/25` the factorisation
`27(64-100σ)² - 62500σ³ = -4(25σ-12)(25σ-48)²` keeps the determinant
strictly positive; at and above, the identity
`28(64-100σ+250P) = 75·T + 2·(25σ+125P-4)` pins both lines to zero. -/
theorem sevenThreeShiftedDet_boundary_forces {squareSum tripleProduct : ℝ}
    (hlower : 0 ≤ squareSum)
    (hamgm : 27 * tripleProduct ^ 2 ≤ squareSum ^ 3)
    (htrace : 0 ≤ (45 : ℝ) / 7 * (1 - squareSum + 2 * tripleProduct) - (3 - squareSum))
    (hzero : ((4 : ℝ) / 5) ^ 3 - 4 / 5 * squareSum + 2 * tripleProduct = 0) :
    squareSum = 12 / 25 ∧ tripleProduct = -(8 / 125) := by
  have hline : 64 - 100 * squareSum + 250 * tripleProduct = 0 := by linarith
  have htraceScaled : 0 ≤ 24 - 38 * squareSum + 90 * tripleProduct := by linarith
  rcases le_or_gt (12 / 25 : ℝ) squareSum with hbig | hsmall
  · -- both auxiliary lines are nonnegative and combine to zero
    have hlagrange : 0 ≤ 25 * squareSum + 125 * tripleProduct - 4 := by
      -- 18·L ≥ 1400σ - 672 ≥ 0 on σ ≥ 12/25, via 2250P ≥ 950σ - 600
      nlinarith [htraceScaled, hbig]
    have hcombine : 28 * (64 - 100 * squareSum + 250 * tripleProduct)
        = 75 * (24 - 38 * squareSum + 90 * tripleProduct)
          + 2 * (25 * squareSum + 125 * tripleProduct - 4) := by ring
    have htZero : 24 - 38 * squareSum + 90 * tripleProduct = 0 := by
      nlinarith [hline, hcombine, hlagrange, htraceScaled]
    have hlZero : 25 * squareSum + 125 * tripleProduct - 4 = 0 := by
      nlinarith [hline, hcombine, htZero]
    constructor
    · linarith
    · linarith
  · -- strictly below the boundary the determinant cannot vanish
    exfalso
    rcases le_or_gt 0 tripleProduct with hprodPos | hprodNeg
    · nlinarith [hline, hsmall, hprodPos]
    · have hvalue : 64 - 100 * squareSum = -(250 * tripleProduct) := by linarith
      have hfactor : 27 * (64 - 100 * squareSum) ^ 2 - 62500 * squareSum ^ 3
          = -4 * (25 * squareSum - 12) * (25 * squareSum - 48) ^ 2 := by ring
      have hedge : 25 * squareSum - 48 ≠ 0 := by intro heq; nlinarith [heq]
      have hsqPos : 0 < (25 * squareSum - 48) ^ 2 :=
        (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hedge))
      have hstrict : 0 < -4 * (25 * squareSum - 12) * (25 * squareSum - 48) ^ 2 := by
        have hleft : 0 < -4 * (25 * squareSum - 12) := by linarith
        exact mul_pos hleft hsqPos
      -- so 27·(250P)² > 62500σ³, i.e. 27P² > σ³, contradicting AM–GM
      have hswap : 27 * (250 * tripleProduct) ^ 2 = 27 * (64 - 100 * squareSum) ^ 2 := by
        rw [hvalue]; ring
      nlinarith [hstrict, hswap, hamgm]

/-- **THE PARITY KILL.**  Against a Gram whose three off-diagonal entries all
have square `4/25` — the `(7/5, 7/5, 1/5)` boundary pattern — no `±1`
coordinate vector has unit norm: the quadratic value is `3 + 2·(sum of three
`±2/5`'s)` ∈ `{3/5, 7/5·…}`, never `1`.  Pure sign arithmetic. -/
theorem extremalSignQuadratic_ne_one {edgeOne edgeTwo edgeThree : ℝ}
    {coordZero coordOne coordTwo : ℝ}
    (hedgeOne : edgeOne ^ 2 = 4 / 25) (hedgeTwo : edgeTwo ^ 2 = 4 / 25)
    (hedgeThree : edgeThree ^ 2 = 4 / 25)
    (hcoordZero : coordZero ^ 2 = 1) (hcoordOne : coordOne ^ 2 = 1)
    (hcoordTwo : coordTwo ^ 2 = 1) :
    3 + 2 * (edgeOne * coordZero * coordOne + edgeTwo * coordZero * coordTwo
      + edgeThree * coordOne * coordTwo) ≠ 1 := by
  intro hunit
  have hsplit : ∀ signedTerm : ℝ, signedTerm ^ 2 = 4 / 25
      → signedTerm = 2 / 5 ∨ signedTerm = -(2 / 5) := by
    intro signedTerm hsquare
    have hfactor : (signedTerm - 2 / 5) * (signedTerm + 2 / 5) = 0 := by
      linear_combination hsquare
    rcases mul_eq_zero.mp hfactor with hcase | hcase
    · left; linarith
    · right; linarith
  have hfirst : (edgeOne * coordZero * coordOne) ^ 2 = 4 / 25 := by
    have hexpand : (edgeOne * coordZero * coordOne) ^ 2
        = edgeOne ^ 2 * (coordZero ^ 2 * coordOne ^ 2) := by ring
    rw [hexpand, hedgeOne, hcoordZero, hcoordOne]; norm_num
  have hsecond : (edgeTwo * coordZero * coordTwo) ^ 2 = 4 / 25 := by
    have hexpand : (edgeTwo * coordZero * coordTwo) ^ 2
        = edgeTwo ^ 2 * (coordZero ^ 2 * coordTwo ^ 2) := by ring
    rw [hexpand, hedgeTwo, hcoordZero, hcoordTwo]; norm_num
  have hthird : (edgeThree * coordOne * coordTwo) ^ 2 = 4 / 25 := by
    have hexpand : (edgeThree * coordOne * coordTwo) ^ 2
        = edgeThree ^ 2 * (coordOne ^ 2 * coordTwo ^ 2) := by ring
    rw [hexpand, hedgeThree, hcoordOne, hcoordTwo]; norm_num
  rcases hsplit _ hfirst with hone | hone <;>
    rcases hsplit _ hsecond with htwo | htwo <;>
      rcases hsplit _ hthird with hthree | hthree <;>
        rw [hone, htwo, hthree] at hunit <;> norm_num at hunit

/-! ## Three-by-three workers: determinant, inverse diagonal, and the master
positive-semidefiniteness theorem -/

/-- The determinant of a symmetric unit-diagonal `3×3` matrix in the campaign
coordinates: `det = 1 - σ + 2P` with `σ` the off-diagonal square sum and `P`
the off-diagonal product. -/
theorem det_of_unitDiagonalThree {gram : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : gramᵀ = gram) (hzero : gram 0 0 = 1) (hone : gram 1 1 = 1)
    (htwo : gram 2 2 = 1) :
    gram.det = 1 - (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
      + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
  have hflipOne : gram 1 0 = gram 0 1 := by
    conv_lhs => rw [← hsym]
    rfl
  have hflipTwo : gram 2 0 = gram 0 2 := by
    conv_lhs => rw [← hsym]
    rfl
  have hflipThree : gram 2 1 = gram 1 2 := by
    conv_lhs => rw [← hsym]
    rfl
  rw [Matrix.det_fin_three, hzero, hone, htwo, hflipOne, hflipTwo, hflipThree]
  ring

/-- The inverse of a symmetric unit-diagonal `3×3` matrix has diagonal entries
`(1 - w_opposite)/det`: the adjugate diagonal is the opposite `2×2` minor. -/
theorem inv_diagonal_of_unitDiagonalThree {gram : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : gramᵀ = gram) (hzero : gram 0 0 = 1) (hone : gram 1 1 = 1)
    (htwo : gram 2 2 = 1) :
    gram⁻¹ 0 0 = gram.det⁻¹ * (1 - gram 1 2 ^ 2)
      ∧ gram⁻¹ 1 1 = gram.det⁻¹ * (1 - gram 0 2 ^ 2)
      ∧ gram⁻¹ 2 2 = gram.det⁻¹ * (1 - gram 0 1 ^ 2) := by
  have hflipThree : gram 2 1 = gram 1 2 := by
    conv_lhs => rw [← hsym]
    rfl
  have hflipTwo : gram 2 0 = gram 0 2 := by
    conv_lhs => rw [← hsym]
    rfl
  have hflipOne : gram 1 0 = gram 0 1 := by
    conv_lhs => rw [← hsym]
    rfl
  have hinv : gram⁻¹ = gram.det⁻¹ • gram.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  refine ⟨?_, ?_, ?_⟩
  · rw [hinv, Matrix.smul_apply, Matrix.adjugate_fin_three, smul_eq_mul]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const,
      Matrix.of_apply, Matrix.cons_val_fin_one, Matrix.empty_val']
    rw [hone, htwo, hflipThree]
    ring
  · rw [hinv, Matrix.smul_apply, Matrix.adjugate_fin_three, smul_eq_mul]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const,
      Matrix.of_apply, Matrix.cons_val_fin_one, Matrix.empty_val']
    rw [hzero, htwo, hflipTwo]
    ring
  · rw [hinv, Matrix.smul_apply, Matrix.adjugate_fin_three, smul_eq_mul]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const,
      Matrix.of_apply, Matrix.cons_val_fin_one, Matrix.empty_val']
    rw [hzero, hone, hflipOne]
    ring

/-- **THE MASTER FLOOR.**  A symmetric unit-diagonal `3×3` Gram with `σ < 3`
and the trace cap `3 - σ ≤ κ·det` is positive semidefinite after shifting by
`1 - β`, whenever `(κ, β)` satisfies the root relation and the slack.  This is
the eigenvalue-free residue of "`tr Γ⁻¹ ≤ κ` forces `λ_min ≥ 1 - β`". -/
theorem posSemidef_sub_smul_one_of_traceCap {gram : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : gramᵀ = gram) (hzero : gram 0 0 = 1) (hone : gram 1 1 = 1)
    (htwo : gram 2 2 = 1)
    (hsigma : gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2 < 3)
    {capRatio betaGap : ℝ} (hcap : 0 < capRatio) (hbeta : 0 < betaGap)
    (hroot : capRatio * betaGap ^ 2 + (capRatio - 3) * betaGap = 2 * (capRatio - 3))
    (hslack : capRatio * betaGap ≤ capRatio - 1)
    (htrace : 3 - (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) ≤ capRatio * gram.det) :
    (gram - (1 - betaGap) • 1).PosSemidef := by
  have hflipOne : gram 1 0 = gram 0 1 := by
    conv_lhs => rw [← hsym]
    rfl
  have hflipTwo : gram 2 0 = gram 0 2 := by
    conv_lhs => rw [← hsym]
    rfl
  have hflipThree : gram 2 1 = gram 1 2 := by
    conv_lhs => rw [← hsym]
    rfl
  have hdetFormula := det_of_unitDiagonalThree hsym hzero hone htwo
  have hamgm := twentySeven_mul_sq_tripleProduct_le_cube_squareSum
    (gram 0 1) (gram 0 2) (gram 1 2)
  have hsigmaNonneg : 0 ≤ gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2 := by positivity
  have htraceCap : 0 ≤ capRatio * (1 - (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
      + 2 * (gram 0 1 * gram 0 2 * gram 1 2))
      - (3 - (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)) := by
    rw [hdetFormula] at htrace
    linarith
  -- the two scalar floors
  have hsigmaCap := offSquareSumScaled_le_of_traceCap hcap hsigma hsigmaNonneg hamgm htraceCap
  have hdetShift := shiftedDetThreshold_nonneg_of_traceCap hcap hbeta hroot hslack
    hsigmaNonneg hamgm htraceCap
  -- β < 1 and κ > 3, then σ ≤ 3β²
  have hbetaLtOne : betaGap < 1 := by
    by_contra hbad
    push Not at hbad
    have hstep : capRatio * 1 ≤ capRatio * betaGap :=
      mul_le_mul_of_nonneg_left hbad hcap.le
    linarith
  have hcapGtThree : 3 < capRatio := by
    by_contra hbad
    push Not at hbad
    have hproductPos : 0 < capRatio * betaGap ^ 2 := mul_pos hcap (pow_pos hbeta 2)
    nlinarith [hroot, hbad, hbeta, hbetaLtOne]
  have hrootGap : capRatio - 3 ≤ capRatio * betaGap ^ 2 := by
    have hpositive : 0 ≤ (capRatio - 3) * (1 - betaGap) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hroot, hpositive]
  have hsigmaBeta : gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2 ≤ 3 * betaGap ^ 2 := by
    have hscaled : 0 ≤ capRatio * (3 * betaGap ^ 2
        - (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)) := by
      nlinarith [hsigmaCap, hrootGap]
    have := (mul_nonneg_iff_of_pos_left hcap).mp hscaled
    linarith
  -- entry bookkeeping for the shifted matrix
  have hshiftDiag : ∀ index : Fin 3, ((1 - betaGap) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      index index = 1 - betaGap := by
    intro index
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  have hshiftOff : ∀ rowIndex colIndex : Fin 3, rowIndex ≠ colIndex
      → ((1 - betaGap) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) rowIndex colIndex = 0 := by
    intro rowIndex colIndex hne
    rw [Matrix.smul_apply, Matrix.one_apply_ne hne, smul_eq_mul, mul_zero]
  refine posSemidef_three_of_elementarySymmetric ?_ ?_ ?_ ?_
  · rw [Matrix.transpose_sub, hsym, Matrix.transpose_smul, Matrix.transpose_one]
  · simp only [Matrix.sub_apply, hshiftDiag, hzero, hone, htwo]
    linarith
  · simp only [Matrix.sub_apply, hshiftDiag, hzero, hone, htwo,
      hshiftOff 0 1 (by decide), hshiftOff 1 0 (by decide),
      hshiftOff 0 2 (by decide), hshiftOff 2 0 (by decide),
      hshiftOff 1 2 (by decide), hshiftOff 2 1 (by decide)]
    rw [hflipOne, hflipTwo, hflipThree]
    nlinarith [hsigmaBeta]
  · have hdetShifted : (gram - (1 - betaGap) • 1).det
        = betaGap ^ 3 - betaGap * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
          + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
      rw [Matrix.det_fin_three]
      simp only [Matrix.sub_apply, hshiftDiag, hzero, hone, htwo,
        hshiftOff 0 1 (by decide), hshiftOff 1 0 (by decide),
        hshiftOff 0 2 (by decide), hshiftOff 2 0 (by decide),
        hshiftOff 1 2 (by decide), hshiftOff 2 1 (by decide)]
      rw [hflipOne, hflipTwo, hflipThree]
      ring
    rw [hdetShifted]
    linarith [hdetShift]

/-- **The PSD trace cap.**  For a positive-semidefinite `3×3` form,
`(tr H)·1 - H ⪰ 0`: the quadratic form never exceeds the trace times the
square norm.  Proved entrywise from the seven principal-minor consequences of
positive semidefiniteness — no eigenvalues. -/
theorem posSemidef_trace_smul_one_sub_of_three {quadForm : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : quadForm.PosSemidef) :
    (Matrix.trace quadForm • (1 : Matrix (Fin 3) (Fin 3) ℝ) - quadForm).PosSemidef := by
  have hsym : quadFormᵀ = quadForm := by
    have := hpsd.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hflipOne : quadForm 1 0 = quadForm 0 1 := by
    conv_lhs => rw [← hsym]
    rfl
  have hflipTwo : quadForm 2 0 = quadForm 0 2 := by
    conv_lhs => rw [← hsym]
    rfl
  have hflipThree : quadForm 2 1 = quadForm 1 2 := by
    conv_lhs => rw [← hsym]
    rfl
  have hdiagZero : 0 ≤ quadForm 0 0 := hpsd.diag_nonneg
  have hdiagOne : 0 ≤ quadForm 1 1 := hpsd.diag_nonneg
  have hdiagTwo : 0 ≤ quadForm 2 2 := hpsd.diag_nonneg
  have hminor : ∀ leftIndex rightIndex : Fin 3, leftIndex ≠ rightIndex
      → 0 ≤ quadForm leftIndex leftIndex * quadForm rightIndex rightIndex
        - quadForm leftIndex rightIndex ^ 2 := by
    intro leftIndex rightIndex hne
    have hsub := hpsd.submatrix ![leftIndex, rightIndex]
    have hsubSym : (quadForm.submatrix ![leftIndex, rightIndex] ![leftIndex, rightIndex])ᵀ
        = quadForm.submatrix ![leftIndex, rightIndex] ![leftIndex, rightIndex] := by
      rw [Matrix.transpose_submatrix, hsym]
    have hfacts := (posSemidef_two_iff hsubSym).mp hsub
    have hraw := hfacts.2.2
    simpa [Matrix.submatrix_apply] using hraw
  have hminorOne := hminor 0 1 (by decide)
  have hminorTwo := hminor 0 2 (by decide)
  have hminorThree := hminor 1 2 (by decide)
  have hdetNonneg : 0 ≤ quadForm.det := hpsd.det_nonneg
  have hdetExpanded : 0 ≤ quadForm 0 0 * quadForm 1 1 * quadForm 2 2
      - quadForm 0 0 * quadForm 1 2 ^ 2 - quadForm 1 1 * quadForm 0 2 ^ 2
      - quadForm 2 2 * quadForm 0 1 ^ 2
      + 2 * (quadForm 0 1 * quadForm 0 2 * quadForm 1 2) := by
    rw [Matrix.det_fin_three, hflipOne, hflipTwo, hflipThree] at hdetNonneg
    nlinarith [hdetNonneg]
  -- the product bound |h01 h02 h12| ≤ abc
  have hproductBound : quadForm 0 1 * quadForm 0 2 * quadForm 1 2
      ≤ quadForm 0 0 * quadForm 1 1 * quadForm 2 2 := by
    have hstepOne : quadForm 0 1 ^ 2 * quadForm 0 2 ^ 2
        ≤ (quadForm 0 0 * quadForm 1 1) * (quadForm 0 0 * quadForm 2 2) :=
      mul_le_mul (by linarith) (by linarith) (sq_nonneg _)
        (mul_nonneg hdiagZero hdiagOne)
    have hstepTwo : (quadForm 0 1 ^ 2 * quadForm 0 2 ^ 2) * quadForm 1 2 ^ 2
        ≤ ((quadForm 0 0 * quadForm 1 1) * (quadForm 0 0 * quadForm 2 2))
          * (quadForm 1 1 * quadForm 2 2) :=
      mul_le_mul hstepOne (by linarith) (sq_nonneg _)
        (mul_nonneg (mul_nonneg hdiagZero hdiagOne) (mul_nonneg hdiagZero hdiagTwo))
    have hsquares : (quadForm 0 1 * quadForm 0 2 * quadForm 1 2) ^ 2
        ≤ (quadForm 0 0 * quadForm 1 1 * quadForm 2 2) ^ 2 := by nlinarith [hstepTwo]
    have hcubeNonneg : 0 ≤ quadForm 0 0 * quadForm 1 1 * quadForm 2 2 :=
      mul_nonneg (mul_nonneg hdiagZero hdiagOne) hdiagTwo
    nlinarith [hsquares, hcubeNonneg]
  have hshiftDiag : ∀ index : Fin 3,
      (Matrix.trace quadForm • (1 : Matrix (Fin 3) (Fin 3) ℝ)) index index
        = Matrix.trace quadForm := by
    intro index
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  have hshiftOff : ∀ rowIndex colIndex : Fin 3, rowIndex ≠ colIndex
      → (Matrix.trace quadForm • (1 : Matrix (Fin 3) (Fin 3) ℝ)) rowIndex colIndex = 0 := by
    intro rowIndex colIndex hne
    rw [Matrix.smul_apply, Matrix.one_apply_ne hne, smul_eq_mul, mul_zero]
  refine posSemidef_three_of_elementarySymmetric ?_ ?_ ?_ ?_
  · rw [Matrix.transpose_sub, hsym, Matrix.transpose_smul, Matrix.transpose_one]
  · simp only [Matrix.sub_apply, hshiftDiag]
    rw [Matrix.trace_fin_three]
    linarith
  · simp only [Matrix.sub_apply, hshiftDiag,
      hshiftOff 0 1 (by decide), hshiftOff 1 0 (by decide),
      hshiftOff 0 2 (by decide), hshiftOff 2 0 (by decide),
      hshiftOff 1 2 (by decide), hshiftOff 2 1 (by decide)]
    rw [Matrix.trace_fin_three, hflipOne, hflipTwo, hflipThree]
    nlinarith [hminorOne, hminorTwo, hminorThree,
      sq_nonneg (quadForm 0 0 + quadForm 1 1 + quadForm 2 2)]
  · have hdetShift : (Matrix.trace quadForm • (1 : Matrix (Fin 3) (Fin 3) ℝ) - quadForm).det
        = (quadForm 0 0 + quadForm 1 1)
            * (quadForm 0 0 * quadForm 1 1 - quadForm 0 1 ^ 2)
          + (quadForm 0 0 + quadForm 2 2)
            * (quadForm 0 0 * quadForm 2 2 - quadForm 0 2 ^ 2)
          + (quadForm 1 1 + quadForm 2 2)
            * (quadForm 1 1 * quadForm 2 2 - quadForm 1 2 ^ 2)
          + 2 * (quadForm 0 0 * quadForm 1 1 * quadForm 2 2
            - quadForm 0 1 * quadForm 0 2 * quadForm 1 2) := by
      rw [Matrix.det_fin_three]
      simp only [Matrix.sub_apply, hshiftDiag,
        hshiftOff 0 1 (by decide), hshiftOff 1 0 (by decide),
        hshiftOff 0 2 (by decide), hshiftOff 2 0 (by decide),
        hshiftOff 1 2 (by decide), hshiftOff 2 1 (by decide)]
      rw [Matrix.trace_fin_three, hflipOne, hflipTwo, hflipThree]
      ring
    rw [hdetShift]
    have htermOne : 0 ≤ (quadForm 0 0 + quadForm 1 1)
        * (quadForm 0 0 * quadForm 1 1 - quadForm 0 1 ^ 2) :=
      mul_nonneg (by linarith) hminorOne
    have htermTwo : 0 ≤ (quadForm 0 0 + quadForm 2 2)
        * (quadForm 0 0 * quadForm 2 2 - quadForm 0 2 ^ 2) :=
      mul_nonneg (by linarith) hminorTwo
    have htermThree : 0 ≤ (quadForm 1 1 + quadForm 2 2)
        * (quadForm 1 1 * quadForm 2 2 - quadForm 1 2 ^ 2) :=
      mul_nonneg (by linarith) hminorThree
    linarith [hproductBound]

/-- Cauchy–Schwarz for a positive-definite quadratic form, squared. -/
private theorem sq_dotProduct_mulVec_le_of_posDef {gram : Matrix (Fin 3) (Fin 3) ℝ}
    (hpd : gram.PosDef) (hsym : gramᵀ = gram) {probe target : Fin 3 → ℝ}
    (htarget : target ≠ 0) :
    (probe ⬝ᵥ (gram *ᵥ target)) ^ 2
      ≤ (probe ⬝ᵥ (gram *ᵥ probe)) * (target ⬝ᵥ (gram *ᵥ target)) := by
  have htargetForm : 0 < target ⬝ᵥ (gram *ᵥ target) := by
    have hraw := hpd.dotProduct_mulVec_pos htarget
    rwa [star_trivial] at hraw
  have hcross : target ⬝ᵥ (gram *ᵥ probe) = probe ⬝ᵥ (gram *ᵥ target) := by
    have hstep := dotProduct_mulVec_transpose gram target probe
    rw [hsym] at hstep
    rw [← hstep, dotProduct_comm]
  have hquad := hpd.posSemidef.dotProduct_mulVec_nonneg
    ((target ⬝ᵥ (gram *ᵥ target)) • probe - (probe ⬝ᵥ (gram *ᵥ target)) • target)
  rw [star_trivial] at hquad
  have hexpand : ((target ⬝ᵥ (gram *ᵥ target)) • probe
        - (probe ⬝ᵥ (gram *ᵥ target)) • target)
      ⬝ᵥ (gram *ᵥ ((target ⬝ᵥ (gram *ᵥ target)) • probe
        - (probe ⬝ᵥ (gram *ᵥ target)) • target))
      = (target ⬝ᵥ (gram *ᵥ target))
        * ((probe ⬝ᵥ (gram *ᵥ probe)) * (target ⬝ᵥ (gram *ᵥ target))
          - (probe ⬝ᵥ (gram *ᵥ target)) ^ 2) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [hcross]
    ring
  rw [hexpand] at hquad
  have hgap := (mul_nonneg_iff_of_pos_left htargetForm).mp hquad
  linarith

/-! ## The exchange layer: swap maximality bounds every solve coordinate -/

/-- **Swap maximality**: no one-row swap of the pick increases the selected
volume.  Weaker than the landed all-pick maximality (`Function.update` swaps
only), and no injectivity is demanded — a swap that duplicates a row has
volume zero and satisfies the bound trivially. -/
def IsSwapMaximalRowPick (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize) : Prop :=
  ∀ (rowIndex : Fin frameSize) (colIndex : Fin selectionRank),
    |(selectedFrameRows frame (Function.update pick colIndex rowIndex)).det|
      ≤ |(selectedFrameRows frame pick).det|

/-- **Exchange bound from swaps alone.**  At a swap-maximal pick every solve
coordinate of every row lies in `[-1, 1]` — the swap identity
`det F_{pick[j ← r]} = B_{rj} · det F_pick` (landed as
`det_selectedFrameRows_update`) forces it. -/
theorem abs_solveMatrix_le_one_of_swapMaximalRowPick
    {frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ}
    {pick : Fin selectionRank → Fin frameSize}
    (hunit : IsUnit (selectedFrameRows frame pick).det)
    (hswap : IsSwapMaximalRowPick frame pick)
    (rowIndex : Fin frameSize) (colIndex : Fin selectionRank) :
    |solveMatrix frame pick rowIndex colIndex| ≤ 1 := by
  have hbound := hswap rowIndex colIndex
  rw [det_selectedFrameRows_update frame pick hunit colIndex rowIndex, abs_mul] at hbound
  have hpositive : 0 < |(selectedFrameRows frame pick).det| := abs_pos.mpr hunit.ne_zero
  nlinarith [hbound, hpositive, abs_nonneg (solveMatrix frame pick rowIndex colIndex)]

/-! ## Isotropy in coordinates -/

/-- The design's raw atoms as a `size × rank` row matrix — the unnormalised
sibling of the landed `unitAtomRows`. -/
def rawAtomRows (D : WeightedDesign size rank) : Matrix (Fin size) (Fin rank) ℝ :=
  Matrix.of fun atomIndex coord => D.atom atomIndex coord

@[simp] theorem rawAtomRows_apply (D : WeightedDesign size rank) (atomIndex : Fin size) :
    rawAtomRows D atomIndex = D.atom atomIndex := rfl

/-- A solve row is the transposed-inverse image of the frame row. -/
private theorem solveMatrix_row_eq_mulVec
    (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize) (rowIndex : Fin frameSize) :
    solveMatrix frame pick rowIndex
      = ((selectedFrameRows frame pick)⁻¹)ᵀ *ᵥ frame rowIndex := by
  funext colIndex
  simp only [solveMatrix, Matrix.mul_apply, Matrix.mulVec, Matrix.transpose_apply, dotProduct]
  exact Finset.sum_congr rfl fun innerIndex _ => mul_comm _ _

/-- **ISOTROPY IN COORDINATES, raw form.**  Transporting the design law through
a nonsingular pick basis: the weighted coordinate atoms resolve the *inverse*
of the picked Gram, `Σ_c t_c x_c x_cᵀ = (S Sᵀ)⁻¹`. -/
theorem sum_weight_smul_atomMatrix_solveMatrix (D : WeightedDesign size rank)
    (pick : Fin rank → Fin size)
    (hunit : IsUnit (selectedFrameRows (rawAtomRows D) pick).det) :
    ∑ atomIndex, D.weight atomIndex
        • atomMatrix (solveMatrix (rawAtomRows D) pick atomIndex)
      = (selectedFrameRows (rawAtomRows D) pick
          * (selectedFrameRows (rawAtomRows D) pick)ᵀ)⁻¹ := by
  have hsum : ∑ atomIndex, D.weight atomIndex
        • atomMatrix (solveMatrix (rawAtomRows D) pick atomIndex)
      = ((selectedFrameRows (rawAtomRows D) pick)⁻¹)ᵀ
        * (∑ atomIndex, D.weight atomIndex • atomMatrix (D.atom atomIndex))
        * (((selectedFrameRows (rawAtomRows D) pick)⁻¹)ᵀ)ᵀ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [solveMatrix_row_eq_mulVec, rawAtomRows_apply, atomMatrix_conj,
      Matrix.mul_smul, Matrix.smul_mul]
  rw [hsum, D.isParseval, Matrix.mul_one, Matrix.transpose_transpose,
    Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]

/-- **ISOTROPY IN COORDINATES, unit form at uniform share.**  At uniform share
`s` the unit-atom coordinate atoms resolve `s⁻¹ · (Γ)⁻¹` with `Γ` the picked
unit Gram — the `(m, k)`-generic master behind the `(7,3)` bound `15/7` and
the `(6,3)` bound `2`. -/
theorem sum_atomMatrix_solveMatrix_of_uniformShare (D : WeightedDesign size rank)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hshare : 0 < shareValue) (pick : Fin rank → Fin size)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det) :
    ∑ atomIndex, atomMatrix (solveMatrix (unitAtomRows D) pick atomIndex)
      = shareValue⁻¹ • (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ)⁻¹ := by
  have hrowEq : ∀ atomIndex, unitAtomRows D atomIndex = unitAtom D atomIndex :=
    fun _ => rfl
  have hsum : ∑ atomIndex, atomMatrix (solveMatrix (unitAtomRows D) pick atomIndex)
      = ((selectedFrameRows (unitAtomRows D) pick)⁻¹)ᵀ
        * (∑ atomIndex, atomMatrix (unitAtom D atomIndex))
        * (((selectedFrameRows (unitAtomRows D) pick)⁻¹)ᵀ)ᵀ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [solveMatrix_row_eq_mulVec, hrowEq, atomMatrix_conj]
  rw [hsum, sum_atomMatrix_unitAtom_of_uniformShare D huniform hshare,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.transpose_transpose,
    Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]

/-- On the picked atoms the solve coordinates are the standard basis rows. -/
private theorem solveMatrix_pick_row_eq_one
    {frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ}
    {pick : Fin selectionRank → Fin frameSize}
    (hunit : IsUnit (selectedFrameRows frame pick).det) (slot : Fin selectionRank) :
    solveMatrix frame pick (pick slot)
      = fun colIndex => (1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ) slot colIndex := by
  funext colIndex
  have hone := solveMatrix_submatrix_pick frame pick hunit
  have hentry := congrFun (congrFun hone slot) colIndex
  simpa [Matrix.submatrix_apply] using hentry

/-- **THE GATE IDENTITY.**  Splitting the raw isotropy-in-coordinates at the
pick: `(S Sᵀ)⁻¹ = diag(t ∘ pick) + Σ_outside t_d x_d x_dᵀ` — the picked block
contributes exactly the picked weights on the diagonal. -/
theorem inv_pickGram_eq_diagonal_add_outside (D : WeightedDesign size rank)
    {pick : Fin rank → Fin size} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (rawAtomRows D) pick).det) :
    (selectedFrameRows (rawAtomRows D) pick
        * (selectedFrameRows (rawAtomRows D) pick)ᵀ)⁻¹
      = Matrix.diagonal (fun slot => D.weight (pick slot))
        + ∑ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
            D.weight atomIndex • atomMatrix (solveMatrix (rawAtomRows D) pick atomIndex) := by
  rw [← sum_weight_smul_atomMatrix_solveMatrix D pick hunit,
    ← Finset.sum_add_sum_compl (Finset.image pick Finset.univ)]
  congr 1
  rw [Finset.sum_image (fun leftSlot _ rightSlot _ heq => hinj heq)]
  ext rowIndex colIndex
  rw [Matrix.sum_apply]
  simp only [solveMatrix_pick_row_eq_one hunit, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul, Matrix.one_apply, Matrix.diagonal_apply]
  rcases eq_or_ne rowIndex colIndex with heq | hne
  · subst heq
    rw [if_pos rfl, Finset.sum_eq_single rowIndex]
    · rw [if_pos rfl]
      ring
    · intro otherSlot _ hother
      rw [if_neg hother]
      ring
    · intro habsent
      exact absurd (Finset.mem_univ rowIndex) habsent
  · rw [if_neg hne, Finset.sum_eq_zero]
    intro slot _
    rcases eq_or_ne slot rowIndex with hrow | hrow
    · subst hrow
      rw [if_pos rfl, if_neg hne]
      ring
    · rw [if_neg hrow]
      ring

/-- **The diagonal split, unit form.**  At uniform share the `(slot, slot)`
entry of the inverse picked Gram is the share times one plus the outside
coordinate mass in direction `slot`. -/
theorem inv_unitPickGram_diagonal_of_uniformShare (D : WeightedDesign size rank)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hshare : 0 < shareValue) {pick : Fin rank → Fin size}
    (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (slot : Fin rank) :
    (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ)⁻¹ slot slot
      = shareValue * (1 + ∑ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
          solveMatrix (unitAtomRows D) pick atomIndex slot ^ 2) := by
  have hmaster := sum_atomMatrix_solveMatrix_of_uniformShare D huniform hshare pick hunit
  have hentry := congrFun (congrFun hmaster slot) slot
  rw [Matrix.sum_apply] at hentry
  simp only [atomMatrix, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul] at hentry
  -- split the full coordinate mass at the pick
  rw [← Finset.sum_add_sum_compl (Finset.image pick Finset.univ)] at hentry
  have himage : ∑ atomIndex ∈ Finset.image pick Finset.univ,
      solveMatrix (unitAtomRows D) pick atomIndex slot
        * solveMatrix (unitAtomRows D) pick atomIndex slot = 1 := by
    rw [Finset.sum_image (fun leftSlot _ rightSlot _ heq => hinj heq)]
    rw [Finset.sum_eq_single slot]
    · rw [solveMatrix_pick_row_eq_one hunit]
      simp [Matrix.one_apply_eq]
    · intro otherSlot _ hother
      rw [solveMatrix_pick_row_eq_one hunit]
      simp [Matrix.one_apply_ne hother]
    · intro habsent
      exact absurd (Finset.mem_univ slot) habsent
  rw [himage] at hentry
  have hsquare : ∑ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
      solveMatrix (unitAtomRows D) pick atomIndex slot
        * solveMatrix (unitAtomRows D) pick atomIndex slot
      = ∑ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
          solveMatrix (unitAtomRows D) pick atomIndex slot ^ 2 :=
    Finset.sum_congr rfl fun atomIndex _ => (pow_two _).symm
  rw [hsquare] at hentry
  have hshareNe : shareValue ≠ 0 := hshare.ne'
  field_simp at hentry ⊢
  linarith [hentry]

/-- **The diagonal bound.**  At a swap-maximal nonsingular pick every diagonal
entry of the inverse unit Gram is at most `share · (1 + #outside)` — the
`(m, k)`-generic master behind `15/7` at `(7,3)` and `2` at `(6,3)`. -/
theorem inv_unitPickGram_diagonal_le_of_swapMaximal (D : WeightedDesign size rank)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hshare : 0 < shareValue) {pick : Fin rank → Fin size}
    (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hswap : IsSwapMaximalRowPick (unitAtomRows D) pick)
    (slot : Fin rank) :
    (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ)⁻¹ slot slot
      ≤ shareValue * (1 + ((Finset.image pick Finset.univ)ᶜ.card : ℝ)) := by
  rw [inv_unitPickGram_diagonal_of_uniformShare D huniform hshare hinj hunit slot]
  have hmass : ∑ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
      solveMatrix (unitAtomRows D) pick atomIndex slot ^ 2
      ≤ ((Finset.image pick Finset.univ)ᶜ.card : ℝ) := by
    have hpointwise : ∀ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
        solveMatrix (unitAtomRows D) pick atomIndex slot ^ 2 ≤ 1 := by
      intro atomIndex _
      exact (sq_le_one_iff_abs_le_one _).mpr
        (abs_solveMatrix_le_one_of_swapMaximalRowPick hunit hswap atomIndex slot)
    have hcard := Finset.sum_le_card_nsmul _ _ _ hpointwise
    rwa [nsmul_eq_mul, mul_one] at hcard
  have hinner : 1 + ∑ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
      solveMatrix (unitAtomRows D) pick atomIndex slot ^ 2
      ≤ 1 + ((Finset.image pick Finset.univ)ᶜ.card : ℝ) := by linarith
  exact mul_le_mul_of_nonneg_left hinner hshare.le

/-! ## Design-side gram facts -/

/-- A nonsingular square times its transpose is positive definite. -/
private theorem posDef_mul_transpose_self_of_isUnit {dimension : ℕ}
    {square : Matrix (Fin dimension) (Fin dimension) ℝ} (hunit : IsUnit square.det) :
    (square * squareᵀ).PosDef := by
  have hsym : (square * squareᵀ)ᵀ = square * squareᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsym, fun probe hprobe => ?_⟩
  rw [star_trivial]
  have hquad : probe ⬝ᵥ ((square * squareᵀ) *ᵥ probe)
      = (squareᵀ *ᵥ probe) ⬝ᵥ (squareᵀ *ᵥ probe) := by
    rw [← Matrix.mulVec_mulVec]
    exact (dotProduct_mulVec_transpose square probe (squareᵀ *ᵥ probe)).symm
  rw [hquad]
  have hkernel : squareᵀ *ᵥ probe ≠ 0 := by
    intro hzero
    apply hprobe
    have hcancel : (squareᵀ)⁻¹ *ᵥ (squareᵀ *ᵥ probe) = probe := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose]),
        Matrix.one_mulVec]
    rw [← hcancel, hzero, Matrix.mulVec_zero]
  exact dotProduct_self_pos hkernel

/-- At uniform positive share the picked unit Gram has unit diagonal. -/
private theorem unitPickGram_diag_one (D : WeightedDesign size rank) {shareValue : ℝ}
    (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue) (hshare : 0 < shareValue)
    (pick : Fin rank → Fin size) (slot : Fin rank) :
    (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ) slot slot = 1 := by
  have hleverage : 0 < leverageOf (D.atom (pick slot)) :=
    leverageOf_pos_of_atomShare_pos D (by rw [huniform (pick slot)]; exact hshare)
  have hcompute : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) slot slot
      = leverageOf (unitAtom D (pick slot)) := by
    rw [Matrix.mul_apply, leverageOf]
    refine Finset.sum_congr rfl fun coord _ => ?_
    rw [Matrix.transpose_apply, pow_two]
    rfl
  rw [hcompute, leverageOf_unitAtom D hleverage]

/-- The picked raw Gram carries the leverages on its diagonal. -/
private theorem rawPickGram_diag (D : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (slot : Fin rank) :
    (selectedFrameRows (rawAtomRows D) pick
        * (selectedFrameRows (rawAtomRows D) pick)ᵀ) slot slot
      = leverageOf (D.atom (pick slot)) := by
  rw [Matrix.mul_apply, leverageOf]
  refine Finset.sum_congr rfl fun coord _ => ?_
  rw [Matrix.transpose_apply, pow_two]
  rfl

/-- The outside count at a `(7,3)` pick is four. -/
private theorem sevenThree_card_compl {pick : Fin 3 → Fin 7}
    (hinj : Function.Injective pick) :
    (((Finset.image pick Finset.univ)ᶜ).card : ℝ) = 4 := by
  rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  simp

/-! ## The (7,3) diagonal and trace bounds -/

/-- **The `(7,3)` diagonal bound**: at uniform share `3/7` and a swap-maximal
nonsingular pick, every diagonal entry of the inverse picked unit Gram is at
most `15/7` — four outside atoms, each contributing at most one. -/
theorem inv_unitPickGram_diagonal_le_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hswap : IsSwapMaximalRowPick (unitAtomRows D) pick) (slot : Fin 3) :
    (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ)⁻¹ slot slot ≤ 15 / 7 := by
  have hshare : (0 : ℝ) < 3 / 7 := by norm_num
  have hbound := inv_unitPickGram_diagonal_le_of_swapMaximal D huniform hshare hinj
    hunit hswap slot
  rw [sevenThree_card_compl hinj] at hbound
  norm_num at hbound
  linarith

/-- **The `(7,3)` trace bound**: `tr Γ⁻¹ ≤ 45/7` at a swap-maximal pick. -/
theorem trace_inv_unitPickGram_le_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hswap : IsSwapMaximalRowPick (unitAtomRows D) pick) :
    Matrix.trace ((selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ)⁻¹) ≤ 45 / 7 := by
  rw [Matrix.trace_fin_three]
  have hzero := inv_unitPickGram_diagonal_le_sevenThree D huniform hinj hunit hswap 0
  have hone := inv_unitPickGram_diagonal_le_sevenThree D huniform hinj hunit hswap 1
  have htwo := inv_unitPickGram_diagonal_le_sevenThree D huniform hinj hunit hswap 2
  linarith

/-- The `(7,3)` entrywise trace cap: `3 - σ ≤ (45/7)·det Γ`. -/
private theorem sevenThree_scalar_traceCap (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hswap : IsSwapMaximalRowPick (unitAtomRows D) pick) :
    3 - ((selectedFrameRows (unitAtomRows D) pick
            * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 0 1 ^ 2
        + (selectedFrameRows (unitAtomRows D) pick
            * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 0 2 ^ 2
        + (selectedFrameRows (unitAtomRows D) pick
            * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 1 2 ^ 2)
      ≤ 45 / 7 * (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ).det := by
  have hshare : (0 : ℝ) < 3 / 7 := by norm_num
  set pickGram := selectedFrameRows (unitAtomRows D) pick
    * (selectedFrameRows (unitAtomRows D) pick)ᵀ with hpickGramDef
  have hsymGram : pickGramᵀ = pickGram := by
    rw [hpickGramDef, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hdiagZero := unitPickGram_diag_one D huniform hshare pick 0
  have hdiagOne := unitPickGram_diag_one D huniform hshare pick 1
  have hdiagTwo := unitPickGram_diag_one D huniform hshare pick 2
  have hdetSq : pickGram.det = (selectedFrameRows (unitAtomRows D) pick).det ^ 2 := by
    rw [hpickGramDef, Matrix.det_mul, Matrix.det_transpose, ← pow_two]
  have hdetPos : 0 < pickGram.det := by
    rw [hdetSq]
    exact (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hunit.ne_zero))
  obtain ⟨hinvZero, hinvOne, hinvTwo⟩ :=
    inv_diagonal_of_unitDiagonalThree hsymGram hdiagZero hdiagOne hdiagTwo
  have hboundZero := inv_unitPickGram_diagonal_le_sevenThree D huniform hinj hunit hswap 0
  have hboundOne := inv_unitPickGram_diagonal_le_sevenThree D huniform hinj hunit hswap 1
  have hboundTwo := inv_unitPickGram_diagonal_le_sevenThree D huniform hinj hunit hswap 2
  rw [← hpickGramDef] at hboundZero hboundOne hboundTwo
  rw [hinvZero] at hboundZero
  rw [hinvOne] at hboundOne
  rw [hinvTwo] at hboundTwo
  have hsum : pickGram.det⁻¹
      * (3 - (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2)) ≤ 45 / 7 := by
    have hexpand : pickGram.det⁻¹
        * (3 - (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2))
        = pickGram.det⁻¹ * (1 - pickGram 1 2 ^ 2)
          + pickGram.det⁻¹ * (1 - pickGram 0 2 ^ 2)
          + pickGram.det⁻¹ * (1 - pickGram 0 1 ^ 2) := by ring
    rw [hexpand]
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hsum hdetPos.le
  have hcancel : pickGram.det⁻¹
      * (3 - (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2)) * pickGram.det
      = 3 - (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2) := by
    field_simp
  rw [hcancel] at hscaled
  linarith

/-! ## The fifths theorem -/

/-- **THE FIFTHS THEOREM, eigenvalue-free and strict.**  At `(7,3)`-uniform
share, every swap-maximal nonsingular pick has `Γ - (1/5)·1 ≻ 0` — the picked
unit Gram sits strictly above `1/5`.  Semidefiniteness is the trace-cap
master at `(κ, β) = (45/7, 4/5)`; strictness is the boundary kill: a vanishing
shifted determinant pins `σ = 12/25` and `P = -8/125`, the per-diagonal bounds
then pin every edge weight to `4/25` and saturate all outside coordinates at
`±1`, and no `±1` vector has unit norm against that Gram
(`extremalSignQuadratic_ne_one`). -/
theorem posDef_unitPickGram_sub_fifth_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hswap : IsSwapMaximalRowPick (unitAtomRows D) pick) :
    (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ
      - (5 : ℝ)⁻¹ • 1).PosDef := by
  have hshare : (0 : ℝ) < 3 / 7 := by norm_num
  have hcap := sevenThree_scalar_traceCap D huniform hinj hunit hswap
  have hdiagZero := unitPickGram_diag_one D huniform hshare pick 0
  have hdiagOne := unitPickGram_diag_one D huniform hshare pick 1
  have hdiagTwo := unitPickGram_diag_one D huniform hshare pick 2
  have hposDefGram := posDef_mul_transpose_self_of_isUnit hunit
  have hboundZero := inv_unitPickGram_diagonal_le_sevenThree D huniform hinj hunit hswap 0
  have hboundOne := inv_unitPickGram_diagonal_le_sevenThree D huniform hinj hunit hswap 1
  have hboundTwo := inv_unitPickGram_diagonal_le_sevenThree D huniform hinj hunit hswap 2
  have hsplitDiag := fun slot =>
    inv_unitPickGram_diagonal_of_uniformShare D huniform hshare hinj hunit slot
  set pickGram := selectedFrameRows (unitAtomRows D) pick
    * (selectedFrameRows (unitAtomRows D) pick)ᵀ with hpickGramDef
  have hsymGram : pickGramᵀ = pickGram := by
    rw [hpickGramDef, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hflipOne : pickGram 1 0 = pickGram 0 1 := by
    conv_lhs => rw [← hsymGram]
    rfl
  have hflipTwo : pickGram 2 0 = pickGram 0 2 := by
    conv_lhs => rw [← hsymGram]
    rfl
  have hflipThree : pickGram 2 1 = pickGram 1 2 := by
    conv_lhs => rw [← hsymGram]
    rfl
  obtain ⟨hinvZero, hinvOne, hinvTwo⟩ :=
    inv_diagonal_of_unitDiagonalThree hsymGram hdiagZero hdiagOne hdiagTwo
  have hdetFormula := det_of_unitDiagonalThree hsymGram hdiagZero hdiagOne hdiagTwo
  -- strict pairwise bounds from positive definiteness
  have hedgeLtOne : pickGram 0 1 ^ 2 < 1 ∧ pickGram 0 2 ^ 2 < 1 ∧ pickGram 1 2 ^ 2 < 1 := by
    refine ⟨?_, ?_, ?_⟩
    · have hne : (![pickGram 0 1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
        intro hzero
        have := congrFun hzero 1
        norm_num at this
      have hq := hposDefGram.dotProduct_mulVec_pos hne
      rw [star_trivial] at hq
      have hval : (![pickGram 0 1, -1, 0] : Fin 3 → ℝ)
          ⬝ᵥ (pickGram *ᵥ ![pickGram 0 1, -1, 0]) = 1 - pickGram 0 1 ^ 2 := by
        simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        rw [hdiagZero, hdiagOne, hflipOne]
        ring
      rw [hval] at hq
      linarith
    · have hne : (![pickGram 0 2, 0, -1] : Fin 3 → ℝ) ≠ 0 := by
        intro hzero
        have := congrFun hzero 2
        simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
      have hq := hposDefGram.dotProduct_mulVec_pos hne
      rw [star_trivial] at hq
      have hval : (![pickGram 0 2, 0, -1] : Fin 3 → ℝ)
          ⬝ᵥ (pickGram *ᵥ ![pickGram 0 2, 0, -1]) = 1 - pickGram 0 2 ^ 2 := by
        simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        rw [hdiagZero, hdiagTwo, hflipTwo]
        ring
      rw [hval] at hq
      linarith
    · have hne : (![0, pickGram 1 2, -1] : Fin 3 → ℝ) ≠ 0 := by
        intro hzero
        have := congrFun hzero 2
        simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
      have hq := hposDefGram.dotProduct_mulVec_pos hne
      rw [star_trivial] at hq
      have hval : (![0, pickGram 1 2, -1] : Fin 3 → ℝ)
          ⬝ᵥ (pickGram *ᵥ ![0, pickGram 1 2, -1]) = 1 - pickGram 1 2 ^ 2 := by
        simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        rw [hdiagOne, hdiagTwo, hflipThree]
        ring
      rw [hval] at hq
      linarith
  obtain ⟨hwOneLt, hwTwoLt, hwThreeLt⟩ := hedgeLtOne
  have hsigmaLtThree : pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2 < 3 := by
    linarith
  have hsigmaNonneg : 0 ≤ pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2 := by
    positivity
  have hamgm := twentySeven_mul_sq_tripleProduct_le_cube_squareSum
    (pickGram 0 1) (pickGram 0 2) (pickGram 1 2)
  have htraceCapForm : 0 ≤ 45 / 7
      * (1 - (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2)
        + 2 * (pickGram 0 1 * pickGram 0 2 * pickGram 1 2))
      - (3 - (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2)) := by
    rw [hdetFormula] at hcap
    linarith
  have hdetShiftNonneg := shiftedDetThreshold_nonneg_of_traceCap
    (by norm_num : (0 : ℝ) < 45 / 7) (by norm_num : (0 : ℝ) < 4 / 5)
    (by norm_num) (by norm_num) hsigmaNonneg hamgm htraceCapForm
  have hsigmaCap := offSquareSumScaled_le_of_traceCap
    (by norm_num : (0 : ℝ) < 45 / 7) hsigmaLtThree hsigmaNonneg hamgm htraceCapForm
  -- the boundary kill
  have hdetShiftNe : (4 / 5 : ℝ) ^ 3
      - 4 / 5 * (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2)
      + 2 * (pickGram 0 1 * pickGram 0 2 * pickGram 1 2) ≠ 0 := by
    intro hzero
    obtain ⟨hsigmaEq, hprodEq⟩ :=
      sevenThreeShiftedDet_boundary_forces hsigmaNonneg hamgm htraceCapForm hzero
    have hdetVal : pickGram.det = 49 / 125 := by
      rw [hdetFormula, hsigmaEq, hprodEq]
      norm_num
    -- every edge weight is exactly 4/25
    rw [hinvZero, hdetVal] at hboundZero
    rw [hinvOne, hdetVal] at hboundOne
    rw [hinvTwo, hdetVal] at hboundTwo
    norm_num at hboundZero hboundOne hboundTwo
    have hwOne : pickGram 0 1 ^ 2 = 4 / 25 := by linarith
    have hwTwo : pickGram 0 2 ^ 2 = 4 / 25 := by linarith
    have hwThree : pickGram 1 2 ^ 2 = 4 / 25 := by linarith
    -- the outside coordinate mass saturates in every direction
    have hdiagValZero : pickGram⁻¹ 0 0 = 15 / 7 := by
      rw [hinvZero, hdetVal, hwThree]
      norm_num
    have hdiagValOne : pickGram⁻¹ 1 1 = 15 / 7 := by
      rw [hinvOne, hdetVal, hwTwo]
      norm_num
    have hdiagValTwo : pickGram⁻¹ 2 2 = 15 / 7 := by
      rw [hinvTwo, hdetVal, hwOne]
      norm_num
    have hsaturate : ∀ slot : Fin 3,
        ∑ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
          solveMatrix (unitAtomRows D) pick atomIndex slot ^ 2 = 4 := by
      intro slot
      have hsplit := hsplitDiag slot
      have hdiagVal : pickGram⁻¹ slot slot = 15 / 7 := by
        fin_cases slot
        · exact hdiagValZero
        · exact hdiagValOne
        · exact hdiagValTwo
      rw [hdiagVal] at hsplit
      linarith
    -- an outside atom exists
    have hcardCompl : ((Finset.image pick Finset.univ)ᶜ).card = 4 := by
      rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ]
      simp
    have houtside : ((Finset.image pick Finset.univ)ᶜ).Nonempty := by
      rw [← Finset.card_pos, hcardCompl]
      norm_num
    obtain ⟨outsideAtom, houtMem⟩ := houtside
    -- its coordinates are all signs
    have hcoordSq : ∀ slot : Fin 3,
        solveMatrix (unitAtomRows D) pick outsideAtom slot ^ 2 = 1 := by
      intro slot
      have hpointwise : ∀ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
          solveMatrix (unitAtomRows D) pick atomIndex slot ^ 2 ≤ 1 := fun atomIndex _ =>
        (sq_le_one_iff_abs_le_one _).mpr
          (abs_solveMatrix_le_one_of_swapMaximalRowPick hunit hswap atomIndex slot)
      by_contra hne
      have hlt : solveMatrix (unitAtomRows D) pick outsideAtom slot ^ 2 < 1 :=
        lt_of_le_of_ne (hpointwise outsideAtom houtMem) hne
      have hstrict : ∑ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
          solveMatrix (unitAtomRows D) pick atomIndex slot ^ 2
          < ∑ _atomIndex ∈ (Finset.image pick Finset.univ)ᶜ, (1 : ℝ) :=
        Finset.sum_lt_sum hpointwise ⟨outsideAtom, houtMem, hlt⟩
      rw [hsaturate slot, Finset.sum_const, hcardCompl, nsmul_eq_mul] at hstrict
      norm_num at hstrict
    -- the unit-norm parity contradiction
    have hlevOutside : 0 < leverageOf (D.atom outsideAtom) :=
      leverageOf_pos_of_atomShare_pos D (by rw [huniform outsideAtom]; norm_num)
    have hxu : (selectedFrameRows (unitAtomRows D) pick)ᵀ
        *ᵥ solveMatrix (unitAtomRows D) pick outsideAtom = unitAtom D outsideAtom := by
      funext coord
      have hcoord := congrFun
        (frameRow_eq_solveCombination (unitAtomRows D) pick hunit outsideAtom) coord
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      rw [show unitAtom D outsideAtom coord = unitAtomRows D outsideAtom coord from rfl,
        hcoord]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun slot _ => mul_comm _ _
    have hquadEq : solveMatrix (unitAtomRows D) pick outsideAtom
        ⬝ᵥ (pickGram *ᵥ solveMatrix (unitAtomRows D) pick outsideAtom) = 1 := by
      calc solveMatrix (unitAtomRows D) pick outsideAtom
            ⬝ᵥ (pickGram *ᵥ solveMatrix (unitAtomRows D) pick outsideAtom)
          = solveMatrix (unitAtomRows D) pick outsideAtom
            ⬝ᵥ (selectedFrameRows (unitAtomRows D) pick
              *ᵥ ((selectedFrameRows (unitAtomRows D) pick)ᵀ
                *ᵥ solveMatrix (unitAtomRows D) pick outsideAtom)) := by
            rw [hpickGramDef, ← Matrix.mulVec_mulVec]
        _ = ((selectedFrameRows (unitAtomRows D) pick)ᵀ
              *ᵥ solveMatrix (unitAtomRows D) pick outsideAtom)
            ⬝ᵥ ((selectedFrameRows (unitAtomRows D) pick)ᵀ
              *ᵥ solveMatrix (unitAtomRows D) pick outsideAtom) :=
            (dotProduct_mulVec_transpose _ _ _).symm
        _ = unitAtom D outsideAtom ⬝ᵥ unitAtom D outsideAtom := by rw [hxu]
        _ = leverageOf (unitAtom D outsideAtom) := dotProduct_self_eq_sum_sq _
        _ = 1 := leverageOf_unitAtom D hlevOutside
    have hexpand : solveMatrix (unitAtomRows D) pick outsideAtom
        ⬝ᵥ (pickGram *ᵥ solveMatrix (unitAtomRows D) pick outsideAtom)
        = solveMatrix (unitAtomRows D) pick outsideAtom 0 ^ 2
          + solveMatrix (unitAtomRows D) pick outsideAtom 1 ^ 2
          + solveMatrix (unitAtomRows D) pick outsideAtom 2 ^ 2
          + 2 * (pickGram 0 1 * solveMatrix (unitAtomRows D) pick outsideAtom 0
              * solveMatrix (unitAtomRows D) pick outsideAtom 1
            + pickGram 0 2 * solveMatrix (unitAtomRows D) pick outsideAtom 0
              * solveMatrix (unitAtomRows D) pick outsideAtom 2
            + pickGram 1 2 * solveMatrix (unitAtomRows D) pick outsideAtom 1
              * solveMatrix (unitAtomRows D) pick outsideAtom 2) := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      rw [hdiagZero, hdiagOne, hdiagTwo, hflipOne, hflipTwo, hflipThree]
      ring
    rw [hexpand, hcoordSq 0, hcoordSq 1, hcoordSq 2] at hquadEq
    exact extremalSignQuadratic_ne_one hwOne hwTwo hwThree
      (hcoordSq 0) (hcoordSq 1) (hcoordSq 2) (by linarith)
  have hdetStrict : 0 < (4 / 5 : ℝ) ^ 3
      - 4 / 5 * (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2)
      + 2 * (pickGram 0 1 * pickGram 0 2 * pickGram 1 2) :=
    lt_of_le_of_ne hdetShiftNonneg (Ne.symm hdetShiftNe)
  -- assemble positive definiteness through the elementary symmetric criterion
  have hshiftDiag : ∀ index : Fin 3, ((5 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      index index = (5 : ℝ)⁻¹ := by
    intro index
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  have hshiftOff : ∀ rowIndex colIndex : Fin 3, rowIndex ≠ colIndex
      → ((5 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ)) rowIndex colIndex = 0 := by
    intro rowIndex colIndex hne
    rw [Matrix.smul_apply, Matrix.one_apply_ne hne, smul_eq_mul, mul_zero]
  refine posDef_three_of_elementarySymmetric ?_ ?_ ?_ ?_
  · rw [Matrix.transpose_sub, hsymGram, Matrix.transpose_smul, Matrix.transpose_one]
  · simp only [Matrix.sub_apply, hshiftDiag, hdiagZero, hdiagOne, hdiagTwo]
    norm_num
  · simp only [Matrix.sub_apply, hshiftDiag, hdiagZero, hdiagOne, hdiagTwo,
      hshiftOff 0 1 (by decide), hshiftOff 1 0 (by decide),
      hshiftOff 0 2 (by decide), hshiftOff 2 0 (by decide),
      hshiftOff 1 2 (by decide), hshiftOff 2 1 (by decide)]
    rw [hflipOne, hflipTwo, hflipThree]
    nlinarith [hsigmaCap]
  · have hdetShifted : (pickGram - (5 : ℝ)⁻¹ • 1).det
        = (4 / 5) ^ 3
          - 4 / 5 * (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2)
          + 2 * (pickGram 0 1 * pickGram 0 2 * pickGram 1 2) := by
      rw [Matrix.det_fin_three]
      simp only [Matrix.sub_apply, hshiftDiag, hdiagZero, hdiagOne, hdiagTwo,
        hshiftOff 0 1 (by decide), hshiftOff 1 0 (by decide),
        hshiftOff 0 2 (by decide), hshiftOff 2 0 (by decide),
        hshiftOff 1 2 (by decide), hshiftOff 2 1 (by decide)]
      rw [hflipOne, hflipTwo, hflipThree]
      ring
    rw [hdetShifted]
    exact hdetStrict

/-- The semidefinite form of the fifths theorem, for downstream consumers that
only need the closed cone. -/
theorem posSemidef_unitPickGram_sub_fifth_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hswap : IsSwapMaximalRowPick (unitAtomRows D) pick) :
    (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ
      - (5 : ℝ)⁻¹ • 1).PosSemidef :=
  (posDef_unitPickGram_sub_fifth_sevenThree D huniform hinj hunit hswap).posSemidef

/-! ## The (6,3) equal-share calibration floor -/

/-- Strict pairwise Cauchy–Schwarz on a positive-definite unit-diagonal Gram. -/
private theorem offdiag_sq_lt_one_of_posDef {gram : Matrix (Fin 3) (Fin 3) ℝ}
    (hpd : gram.PosDef) (hsym : gramᵀ = gram) (hzero : gram 0 0 = 1)
    (hone : gram 1 1 = 1) (htwo : gram 2 2 = 1) :
    gram 0 1 ^ 2 < 1 ∧ gram 0 2 ^ 2 < 1 ∧ gram 1 2 ^ 2 < 1 := by
  have hflipOne : gram 1 0 = gram 0 1 := by
    conv_lhs => rw [← hsym]
    rfl
  have hflipTwo : gram 2 0 = gram 0 2 := by
    conv_lhs => rw [← hsym]
    rfl
  have hflipThree : gram 2 1 = gram 1 2 := by
    conv_lhs => rw [← hsym]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · have hne : (![gram 0 1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro hvanish
      have := congrFun hvanish 1
      norm_num at this
    have hquad := hpd.dotProduct_mulVec_pos hne
    rw [star_trivial] at hquad
    have hval : (![gram 0 1, -1, 0] : Fin 3 → ℝ)
        ⬝ᵥ (gram *ᵥ ![gram 0 1, -1, 0]) = 1 - gram 0 1 ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hzero, hone, hflipOne]
      ring
    rw [hval] at hquad
    linarith
  · have hne : (![gram 0 2, 0, -1] : Fin 3 → ℝ) ≠ 0 := by
      intro hvanish
      have := congrFun hvanish 2
      simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
    have hquad := hpd.dotProduct_mulVec_pos hne
    rw [star_trivial] at hquad
    have hval : (![gram 0 2, 0, -1] : Fin 3 → ℝ)
        ⬝ᵥ (gram *ᵥ ![gram 0 2, 0, -1]) = 1 - gram 0 2 ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hzero, htwo, hflipTwo]
      ring
    rw [hval] at hquad
    linarith
  · have hne : (![0, gram 1 2, -1] : Fin 3 → ℝ) ≠ 0 := by
      intro hvanish
      have := congrFun hvanish 2
      simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
    have hquad := hpd.dotProduct_mulVec_pos hne
    rw [star_trivial] at hquad
    have hval : (![0, gram 1 2, -1] : Fin 3 → ℝ)
        ⬝ᵥ (gram *ᵥ ![0, gram 1 2, -1]) = 1 - gram 1 2 ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hone, htwo, hflipThree]
      ring
    rw [hval] at hquad
    linarith

/-- **The (6,3) calibration floor.**  At `(6,3)`-uniform share (`s = 1/2`,
three outside atoms, diagonal cap `2`, trace cap `6`) the same trace-cap
master gives `Γ - ((5 - √17)/4)·1 ⪰ 0` at every swap-maximal nonsingular pick
— the floor `(5 - √17)/4 ≈ 0.219` of the pen calibration, handled through the
root relation `2β² + β = 2` for `β = (√17 - 1)/4`. -/
theorem posSemidef_unitPickGram_sub_sqrtSeventeenFloor_sixThree (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hswap : IsSwapMaximalRowPick (unitAtomRows D) pick) :
    (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ
      - ((5 - Real.sqrt 17) / 4) • 1).PosSemidef := by
  have hshare : (0 : ℝ) < 1 / 2 := by norm_num
  have hsqrtSq : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg 17
  have hsqrtLarge : 4 < Real.sqrt 17 := by nlinarith [hsqrtSq, hsqrtNonneg]
  have hsqrtSmall : Real.sqrt 17 < 13 / 3 := by nlinarith [hsqrtSq, hsqrtNonneg]
  have hdiagZero := unitPickGram_diag_one D huniform hshare pick 0
  have hdiagOne := unitPickGram_diag_one D huniform hshare pick 1
  have hdiagTwo := unitPickGram_diag_one D huniform hshare pick 2
  have hposDefGram := posDef_mul_transpose_self_of_isUnit hunit
  have hcardCompl : (((Finset.image pick Finset.univ)ᶜ).card : ℝ) = 3 := by
    rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp
  have hboundZero := inv_unitPickGram_diagonal_le_of_swapMaximal D huniform hshare hinj
    hunit hswap 0
  have hboundOne := inv_unitPickGram_diagonal_le_of_swapMaximal D huniform hshare hinj
    hunit hswap 1
  have hboundTwo := inv_unitPickGram_diagonal_le_of_swapMaximal D huniform hshare hinj
    hunit hswap 2
  rw [hcardCompl] at hboundZero hboundOne hboundTwo
  norm_num at hboundZero hboundOne hboundTwo
  set pickGram := selectedFrameRows (unitAtomRows D) pick
    * (selectedFrameRows (unitAtomRows D) pick)ᵀ with hpickGramDef
  have hsymGram : pickGramᵀ = pickGram := by
    rw [hpickGramDef, Matrix.transpose_mul, Matrix.transpose_transpose]
  obtain ⟨hinvZero, hinvOne, hinvTwo⟩ :=
    inv_diagonal_of_unitDiagonalThree hsymGram hdiagZero hdiagOne hdiagTwo
  have hdetFormula := det_of_unitDiagonalThree hsymGram hdiagZero hdiagOne hdiagTwo
  have hdetPos : 0 < pickGram.det := by
    have hdetSq : pickGram.det = (selectedFrameRows (unitAtomRows D) pick).det ^ 2 := by
      rw [hpickGramDef, Matrix.det_mul, Matrix.det_transpose, ← pow_two]
    rw [hdetSq]
    exact (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hunit.ne_zero))
  obtain ⟨hwOneLt, hwTwoLt, hwThreeLt⟩ :=
    offdiag_sq_lt_one_of_posDef hposDefGram hsymGram hdiagZero hdiagOne hdiagTwo
  have hsigmaLtThree : pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2 < 3 := by
    linarith
  -- the (6,3) trace cap: 3 - σ ≤ 6·det
  rw [hinvZero] at hboundZero
  rw [hinvOne] at hboundOne
  rw [hinvTwo] at hboundTwo
  have htraceCap : 3 - (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2)
      ≤ 6 * pickGram.det := by
    have hsum : pickGram.det⁻¹
        * (3 - (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2)) ≤ 6 := by
      have hexpand : pickGram.det⁻¹
          * (3 - (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2))
          = pickGram.det⁻¹ * (1 - pickGram 1 2 ^ 2)
            + pickGram.det⁻¹ * (1 - pickGram 0 2 ^ 2)
            + pickGram.det⁻¹ * (1 - pickGram 0 1 ^ 2) := by ring
      rw [hexpand]
      linarith
    have hscaled := mul_le_mul_of_nonneg_right hsum hdetPos.le
    have hcancel : pickGram.det⁻¹
        * (3 - (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2)) * pickGram.det
        = 3 - (pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2) := by
      field_simp
    rw [hcancel] at hscaled
    linarith
  -- the master at (κ, β) = (6, (√17 - 1)/4)
  have hbetaPos : (0 : ℝ) < (Real.sqrt 17 - 1) / 4 := by linarith
  have hroot : (6 : ℝ) * ((Real.sqrt 17 - 1) / 4) ^ 2
      + ((6 : ℝ) - 3) * ((Real.sqrt 17 - 1) / 4) = 2 * ((6 : ℝ) - 3) := by
    linear_combination (3 / 8 : ℝ) * hsqrtSq
  have hslack : (6 : ℝ) * ((Real.sqrt 17 - 1) / 4) ≤ (6 : ℝ) - 1 := by linarith
  have hmain := posSemidef_sub_smul_one_of_traceCap hsymGram hdiagZero hdiagOne hdiagTwo
    hsigmaLtThree (by norm_num : (0 : ℝ) < 6) hbetaPos hroot hslack htraceCap
  have hconst : (5 - Real.sqrt 17) / 4 = 1 - (Real.sqrt 17 - 1) / 4 := by ring
  rw [hconst]
  exact hmain

/-! ## The share-agnostic gate -/

/-- **GATE-W, the share-agnostic domination gate** (rank three, every size,
every weight vector).  If the picked weight mass plus the reciprocal picked
leverage mass reaches one, a swap-maximal nonsingular pick dominates:
`t(T) + 1/(ℓ_a + ℓ_b + ℓ_c) ≥ 1  ⟹  Dominates`.  The proof runs
`G⁻¹ = diag(t) + Σ_out t x xᵀ` (trace ≤ 3 - 2t(T)), the Cauchy–Schwarz floor
`G⁻¹ ⪰ (tr G)⁻¹·1`, the PSD trace cap, and the congruence
`Sᵀ(1 - G⁻¹)S = S_T - 1`. -/
theorem dominates_of_pickWeight_add_inv_leverageSum (D : WeightedDesign size 3)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (rawAtomRows D) pick).det)
    (hswap : IsSwapMaximalRowPick (rawAtomRows D) pick)
    (hgate : 1 ≤ (∑ slot, D.weight (pick slot))
      + (∑ slot, leverageOf (D.atom (pick slot)))⁻¹) :
    Dominates D (Finset.image pick Finset.univ) := by
  have hposDefGram := posDef_mul_transpose_self_of_isUnit hunit
  have hdiagLev := fun slot => rawPickGram_diag D pick slot
  have hidentity := inv_pickGram_eq_diagonal_add_outside D hinj hunit
  set selected := selectedFrameRows (rawAtomRows D) pick with hselectedDef
  set gateGram := selected * selectedᵀ with hgateGramDef
  have hsymGram : gateGramᵀ = gateGram := by
    rw [hgateGramDef, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hunitT : IsUnit (selectedᵀ).det := by
    rw [Matrix.det_transpose]
    exact hunit
  have hunitGram : IsUnit gateGram.det := by
    rw [hgateGramDef, Matrix.det_mul, Matrix.det_transpose]
    exact hunit.mul hunit
  have htraceGram : Matrix.trace gateGram = ∑ slot, leverageOf (D.atom (pick slot)) := by
    rw [Matrix.trace_fin_three, hdiagLev 0, hdiagLev 1, hdiagLev 2, Fin.sum_univ_three]
  have htracePos : 0 < Matrix.trace gateGram := by
    have hdiagPos : 0 < gateGram 0 0 := by
      have hne : ((Pi.single 0 1 : Fin 3 → ℝ)) ≠ 0 := by
        intro hvanish
        have := congrFun hvanish 0
        simp at this
      have hquad := hposDefGram.dotProduct_mulVec_pos hne
      rw [star_trivial] at hquad
      have hval : (Pi.single 0 1 : Fin 3 → ℝ)
          ⬝ᵥ (gateGram *ᵥ (Pi.single 0 1 : Fin 3 → ℝ)) = gateGram 0 0 := by
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.single_apply]
      rw [hval] at hquad
      exact hquad
    have hdiagOne : 0 ≤ gateGram 1 1 := hposDefGram.posSemidef.diag_nonneg
    have hdiagTwo : 0 ≤ gateGram 2 2 := hposDefGram.posSemidef.diag_nonneg
    rw [Matrix.trace_fin_three]
    linarith
  have hinvPsd : (gateGram⁻¹).PosSemidef := by
    rw [hidentity]
    refine Matrix.PosSemidef.add
      (Matrix.posSemidef_diagonal_iff.mpr fun slot => (D.weight_pos (pick slot)).le)
      (Matrix.posSemidef_sum _ fun atomIndex _ => ?_)
    exact (posSemidef_atomMatrix _).smul (D.weight_pos atomIndex).le
  -- trace of the inverse
  have hweightSplit : (∑ slot, D.weight (pick slot))
      + ∑ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ, D.weight atomIndex = 1 := by
    rw [← D.weight_sum_one (m := size), ← Finset.sum_add_sum_compl (Finset.image pick Finset.univ)]
    congr 1
    rw [Finset.sum_image (fun leftSlot _ rightSlot _ heq => hinj heq)]
  have htraceInv : Matrix.trace (gateGram⁻¹)
      ≤ 3 - 2 * ∑ slot, D.weight (pick slot) := by
    rw [hidentity, Matrix.trace_add, Matrix.trace_diagonal, Matrix.trace_sum]
    have htermBound : ∀ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
        Matrix.trace (D.weight atomIndex
          • atomMatrix (solveMatrix (rawAtomRows D) pick atomIndex))
        ≤ 3 * D.weight atomIndex := by
      intro atomIndex _
      rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]
      have hcoordMass : leverageOf (solveMatrix (rawAtomRows D) pick atomIndex) ≤ 3 := by
        rw [leverageOf, Fin.sum_univ_three]
        have hzero := (sq_le_one_iff_abs_le_one _).mpr
          (abs_solveMatrix_le_one_of_swapMaximalRowPick hunit hswap atomIndex 0)
        have hone := (sq_le_one_iff_abs_le_one _).mpr
          (abs_solveMatrix_le_one_of_swapMaximalRowPick hunit hswap atomIndex 1)
        have htwo := (sq_le_one_iff_abs_le_one _).mpr
          (abs_solveMatrix_le_one_of_swapMaximalRowPick hunit hswap atomIndex 2)
        linarith
      nlinarith [(D.weight_pos atomIndex).le, hcoordMass]
    have hsumBound := Finset.sum_le_sum htermBound
    have houtWeight : ∑ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
        3 * D.weight atomIndex
        = 3 * (1 - ∑ slot, D.weight (pick slot)) := by
      rw [← Finset.mul_sum]
      have hcomplWeight : ∑ atomIndex ∈ (Finset.image pick Finset.univ)ᶜ,
          D.weight atomIndex = 1 - ∑ slot, D.weight (pick slot) := by
        linarith [hweightSplit]
      rw [hcomplWeight]
    linarith [hsumBound, houtWeight ▸ hsumBound]
  -- the Cauchy–Schwarz floor
  have hfloor : (gateGram⁻¹ - (Matrix.trace gateGram)⁻¹ • 1).PosSemidef := by
    have hsubSym : (gateGram⁻¹ - (Matrix.trace gateGram)⁻¹ • 1)ᵀ
        = gateGram⁻¹ - (Matrix.trace gateGram)⁻¹ • 1 := by
      rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.transpose_nonsing_inv, hsymGram]
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hsubSym, fun probe => ?_⟩
    rw [star_trivial]
    rcases eq_or_ne probe 0 with hvanish | hnonzero
    · subst hvanish
      simp
    · have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hnonzero
      have hback : gateGram *ᵥ (gateGram⁻¹ *ᵥ probe) = probe := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunitGram, Matrix.one_mulVec]
      have htargetNe : gateGram⁻¹ *ᵥ probe ≠ 0 := by
        intro hvanish
        apply hnonzero
        rw [← hback, hvanish, Matrix.mulVec_zero]
      have hcs := sq_dotProduct_mulVec_le_of_posDef hposDefGram hsymGram
        (probe := probe) htargetNe
      rw [hback] at hcs
      have hswitch : (gateGram⁻¹ *ᵥ probe) ⬝ᵥ probe
          = probe ⬝ᵥ (gateGram⁻¹ *ᵥ probe) := dotProduct_comm _ _
      rw [hswitch] at hcs
      have hcapForm := (posSemidef_trace_smul_one_sub_of_three
        hposDefGram.posSemidef).dotProduct_mulVec_nonneg probe
      rw [star_trivial] at hcapForm
      have hcapExpand : probe ⬝ᵥ ((Matrix.trace gateGram • 1 - gateGram) *ᵥ probe)
          = Matrix.trace gateGram * (probe ⬝ᵥ probe)
            - probe ⬝ᵥ (gateGram *ᵥ probe) := by
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
          Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      rw [hcapExpand] at hcapForm
      have hinvNonneg : 0 ≤ probe ⬝ᵥ (gateGram⁻¹ *ᵥ probe) := by
        have := hinvPsd.dotProduct_mulVec_nonneg probe
        rwa [star_trivial] at this
      have hGle : probe ⬝ᵥ (gateGram *ᵥ probe)
          ≤ Matrix.trace gateGram * (probe ⬝ᵥ probe) := by linarith
      have hchain : (probe ⬝ᵥ probe) ^ 2
          ≤ Matrix.trace gateGram * (probe ⬝ᵥ probe)
            * (probe ⬝ᵥ (gateGram⁻¹ *ᵥ probe)) := by
        calc (probe ⬝ᵥ probe) ^ 2
            ≤ (probe ⬝ᵥ (gateGram *ᵥ probe)) * (probe ⬝ᵥ (gateGram⁻¹ *ᵥ probe)) := hcs
          _ ≤ Matrix.trace gateGram * (probe ⬝ᵥ probe)
              * (probe ⬝ᵥ (gateGram⁻¹ *ᵥ probe)) :=
            mul_le_mul_of_nonneg_right hGle hinvNonneg
      have hgoalExpand : probe ⬝ᵥ ((gateGram⁻¹ - (Matrix.trace gateGram)⁻¹ • 1) *ᵥ probe)
          = probe ⬝ᵥ (gateGram⁻¹ *ᵥ probe)
            - (Matrix.trace gateGram)⁻¹ * (probe ⬝ᵥ probe) := by
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
          Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      rw [hgoalExpand]
      have hXfloor : probe ⬝ᵥ probe
          ≤ Matrix.trace gateGram * (probe ⬝ᵥ (gateGram⁻¹ *ᵥ probe)) := by
        nlinarith [hchain, hprobePos]
      have hscaled := mul_le_mul_of_nonneg_left hXfloor (inv_nonneg.mpr htracePos.le)
      rw [← mul_assoc, inv_mul_cancel₀ htracePos.ne', one_mul] at hscaled
      linarith
  -- the cap through the floored matrix
  have hcapMatrix := posSemidef_trace_smul_one_sub_of_three hfloor
  have htraceFloor : Matrix.trace (gateGram⁻¹ - (Matrix.trace gateGram)⁻¹ • 1)
      = Matrix.trace (gateGram⁻¹) - 3 * (Matrix.trace gateGram)⁻¹ := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    simp [Fintype.card_fin]
    ring
  have hcapShift : ((Matrix.trace (gateGram⁻¹) - 2 * (Matrix.trace gateGram)⁻¹)
      • (1 : Matrix (Fin 3) (Fin 3) ℝ) - gateGram⁻¹).PosSemidef := by
    have hrewrite : (Matrix.trace (gateGram⁻¹) - 2 * (Matrix.trace gateGram)⁻¹)
        • (1 : Matrix (Fin 3) (Fin 3) ℝ) - gateGram⁻¹
        = Matrix.trace (gateGram⁻¹ - (Matrix.trace gateGram)⁻¹ • 1)
          • (1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (gateGram⁻¹ - (Matrix.trace gateGram)⁻¹ • 1) := by
      rw [htraceFloor]
      have hsplitScalar : Matrix.trace (gateGram⁻¹) - 2 * (Matrix.trace gateGram)⁻¹
          = (Matrix.trace (gateGram⁻¹) - 3 * (Matrix.trace gateGram)⁻¹)
            + (Matrix.trace gateGram)⁻¹ := by ring
      rw [hsplitScalar, add_smul]
      abel
    rw [hrewrite]
    exact hcapMatrix
  have hgap : Matrix.trace (gateGram⁻¹) - 2 * (Matrix.trace gateGram)⁻¹ ≤ 1 := by
    have hinvFloor : 1 - (∑ slot, D.weight (pick slot)) ≤ (Matrix.trace gateGram)⁻¹ := by
      rw [htraceGram]
      linarith
    linarith
  have hOneSub : ((1 : Matrix (Fin 3) (Fin 3) ℝ) - gateGram⁻¹).PosSemidef := by
    have hdecompose : (1 : Matrix (Fin 3) (Fin 3) ℝ) - gateGram⁻¹
        = ((Matrix.trace (gateGram⁻¹) - 2 * (Matrix.trace gateGram)⁻¹) • 1 - gateGram⁻¹)
          + (1 - (Matrix.trace (gateGram⁻¹) - 2 * (Matrix.trace gateGram)⁻¹)) • 1 := by
      module
    rw [hdecompose]
    exact hcapShift.add (Matrix.PosSemidef.one.smul (by linarith :
      (0 : ℝ) ≤ 1 - (Matrix.trace (gateGram⁻¹) - 2 * (Matrix.trace gateGram)⁻¹)))
  -- congruence back to the subset sum
  have hsubSym : ((1 : Matrix (Fin 3) (Fin 3) ℝ) - gateGram⁻¹)ᵀ = 1 - gateGram⁻¹ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_nonsing_inv, hsymGram]
  have hcongr := (posSemidef_congr_right hsubSym hunit).mp hOneSub
  have hsubset : subsetSum D (Finset.image pick Finset.univ) = selectedᵀ * selected := by
    rw [subsetSum, Finset.sum_image (fun leftSlot _ rightSlot _ heq => hinj heq),
      transpose_mul_self_eq_sum_rows]
    exact Finset.sum_congr rfl fun slot _ => rfl
  have hmiddle : selectedᵀ * gateGram⁻¹ * selected = 1 := by
    rw [hgateGramDef, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hunitT, Matrix.one_mul, Matrix.nonsing_inv_mul _ hunit]
  have hsandwich : selectedᵀ * (1 - gateGram⁻¹) * selected
      = subsetSum D (Finset.image pick Finset.univ) - 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hmiddle, hsubset]
  show (subsetSum D (Finset.image pick Finset.univ) - 1).PosSemidef
  rw [← hsandwich]
  exact hcongr

/-- **The gate is silent at `(7,3)` equal share**: with picked weights `1/7`
and picked leverages `3`, the gate quantity is `3/7 + 1/9 = 34/63 < 1` — the
share-agnostic gate fires only when the picked triple is share-heavy, which is
the free-weight `(7,3)` regime it was built for. -/
theorem pickWeight_add_inv_leverageSum_lt_one_of_sevenThree (D : WeightedDesign 7 3)
    {pick : Fin 3 → Fin 7}
    (hweights : ∀ slot, D.weight (pick slot) = 1 / 7)
    (hleverages : ∀ slot, leverageOf (D.atom (pick slot)) = 3) :
    (∑ slot, D.weight (pick slot))
      + (∑ slot, leverageOf (D.atom (pick slot)))⁻¹ < 1 := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three, hweights 0, hweights 1, hweights 2,
    hleverages 0, hleverages 1, hleverages 2]
  norm_num

end Gtz

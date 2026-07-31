/-
# The M7 march: the two-row minor slack pushes the `(7,3)` floor from `31/150` to `37/150`

`Gtz.posDef_unitPickGram_sub_cauchyBinetFloor_sevenThree` lands
`lambda_min(Gamma[T#]) > 31/150` at every `(7,3)`-uniform maximal-volume pick,
and `Gtz.SevenThreeCBFloor` names its own blocker: the extremal sign kill
`fourEvenSignVectors_unitNorm_inconsistent` is an EQUALITY-CASE statement, and
turning it into a floor strictly above `31/150` needs a QUANTITATIVE perturbation
of the tightness forcing.  This file supplies that perturbation and runs the
march.

## PROVED (unconditional, no new hypothesis)

  * `sq_twoByTwoMinor_le_entrySlack` — THE REAL LEVER.  For reals with
    `a^2, b^2, c^2, d^2 <= 1` and `(a d - b c)^2 <= 1`,
        `(a d - b c)^2 <= (1-a^2) + (1-b^2) + (1-c^2) + (1-d^2)`.
    A `2x2` determinant that the exchange bound caps at one is quantitatively
    forced towards zero by how close its entries are to `+-1`.  The equality case
    is `(1,1,0,1)`, so the constant on each slack term is sharp pointwise.  The
    limiting content is `twoByTwoSignMinor_eq_zero_of_sq_le_one`: a `+-1` matrix
    has an EVEN determinant, so the cap `|det| <= 1` forces `det = 0`.
  * `exists_complex_unimodular_minor_ne_zero` — the lever is FIELD-SENSITIVE,
    hence not excluded by barrier B1.  Over the complex numbers four unimodular
    entries can carry a minor of modulus exactly one and nonzero: the witness is
    `(1, 1; (1 + i sqrt 3)/2, 1)`, whose minor is `(1 - i sqrt 3)/2`.
  * `minorGate_of_maximalVolume_sevenThree` — THE NEW GATE.  At every
    `(7,3)`-uniform design and maximal-volume nonsingular pick,
        `233 sigma - 128 <= 522 P`
    in the `(sigma, P)` entry coordinates of the picked unit Gram.  Its content
    upstream is `e2(R) + 6 e1(R) <= 72` for the outside coordinate Gram
    `R = X_o^T X_o`, from the eighteen two-row exchange bounds through
    Binet-Cauchy: each of the twelve entries of `X_o` sits in exactly six of the
    eighteen `2x2` minors, so summing the lever gives `e2(R) <= 6 (12 - e1(R))`.
    The landed trace gate `38 sigma - 24 <= 90 P` follows from this one whenever
    `sigma >= 0` (certificate `63 sigma + 56 >= 0`), so the new gate strictly
    dominates it.
  * `posDef_unitPickGram_sub_minorFloor_sevenThree` and
    `exists_pick_posDef_unitPickGram_sub_minorFloor_sevenThree` — THE NEW FLOOR:
        `lambda_min(Gamma[T#]) > 37/150 = 0.24666...`,
    against the landed `31/150 = 0.20666...`.  A gain of exactly `1/25`.
  * `posDef_unitPickGram_sub_minorFloor_sixThree` — the calibration twin on the
    stratum where U6 is already a theorem: `lambda_min(Gamma[T#]) > 7/25 = 0.28`,
    against the landed `9/40 = 0.225`.  Non-vacuous on the icosahedral design.
  * `exists_correlation_satisfying_gates_not_posDef_at_quarter_sevenThree` — THE
    FOURTH BARRIER, with an exact rational witness.  The correlation matrix with
    off-diagonals `(-11/20, -3/10, -1/4)` satisfies BOTH exchange gates and is
    positive definite (`det = 37/80`), yet `det(Gamma - (1/4) 1) = -3/1600 < 0`.
    So the two-gate certificate cannot deliver `1/4`, let alone `1/3`.

## NOT PROVED

  * Conjecture M7 (`Gtz.MaxVolumeGramThirdFloorSevenThree`, the `1/3` floor)
    remains OPEN.  This file moves `31/150 -> 37/150`; the residual gap to `1/3`
    is `1/3 - 37/150 = 13/150`, and it is NOT reachable by this route -- see the
    barrier above.
  * The exact optimum of the two-gate relaxation is the smallest root
    `g** = 0.2473927...` of `1809 x^3 - 5427 x^2 + 4599 x - 833`, bracketed here
    by `C**(37/150) = -204099/125000 < 0 < 373/64 = C**(1/4)`.  So the landed
    `37/150` is within `7.3 . 10^-4` of everything this route can give, and the
    route's ceiling is strictly below `1/4`.  The gate corner is the exact point
    `(sigma, P) = (92/201, -74/1809)`, where BOTH gates are tight
    (`exchangeGates_corner_tight_sevenThree`), `Delta = 833/1809`, and the outside
    spectrum data is `(e1, e2, e3) = (168/17, 216/17, 4)` -- satisfying isotropy
    `12 + 5 e1 - 2 e2 - 9 e3 = 0` exactly.
  * The aggregation `e2(R) <= 6 (12 - e1(R))` is not claimed sharp.  Its
    per-minor input IS sharp, and one zero entry among eleven `+-1` entries
    attains the aggregate too (`e1 = 11`, `e2 = 6`), but that point violates
    `e3 <= 4` under isotropy (`9 e3 = 55`), so the true optimum is interior and
    unlocated.  Whether a SHARPER aggregation of the same per-minor data can pass
    `1/4` is OPEN — the `1/4` barrier below bounds only the two AGGREGATED gates,
    and its witness is not shown to be realizable by any `4x3` outside block.
  * Nothing here says the barrier witness arises from a genuine `(7,3)`-uniform
    design at a maximal-volume pick.  The barrier is on the CERTIFICATE, not on
    the truth of M7.

## The arithmetic, exactly

At uniform share `3/7` the outside coordinate matrix `X_o` (four rows) satisfies
`R + 1 = (7/3) Gamma^-1`, whence `e1(R) = (7/3)(3-sigma)/Delta - 3` and
`e2(R) = (7 + 14 sigma)/(3 Delta) + 3` with `Delta = det Gamma = 1 - sigma + 2P`.
Feeding `e2(R) + 6 e1(R) <= 72` through those gives `133 - 28 sigma <= 261 Delta`,
i.e. `233 sigma - 128 <= 522 P`.  Against the landed volume gate
`36 sigma - 22 <= 135 P` the corner is `(92/201, -74/1809)`, and the shifted
determinant there is `psi(37/150) = 68033/75375000 > 0` -- the exact margin of
the landed floor.  At `(6,3)` the same skeleton at share `1/2` gives
`41 sigma - 21 <= 90 P` against `P >= 0`, corner `(21/41, 0)`, exact optimum
`1 - sqrt 861 / 41 = 0.2843225...` and margin `psi(7/25) = 2862/640625`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.MaximalVolume
import Gtz.Reduction.RealVolumeFloor
import Gtz.Design.FrameConservation
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Quantitative.GTransformGate
import Gtz.Quantitative.SevenThreeCBFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. The real lever: a capped `2x2` minor is forced towards zero by entry slack -/

/-- The scalar core of the lever.  For `p, q` in `[-1,1]` with `|p - q| <= 1` the
form `p^2 + q^2 - p q` is at most one.  Two branches: when `p q >= 0` the
certificate is `(1-p^2)(1-q^2) >= 0` together with `p q <= 1`; when `p q < 0` the
capped difference already gives `p^2 + q^2 <= 1 + 2 p q`. -/
theorem pairProductForm_le_one {mainProduct crossProduct : ℝ}
    (hmain : mainProduct ^ 2 ≤ 1) (hcross : crossProduct ^ 2 ≤ 1)
    (hdifference : (mainProduct - crossProduct) ^ 2 ≤ 1) :
    mainProduct ^ 2 + crossProduct ^ 2 - mainProduct * crossProduct ≤ 1 := by
  rcases le_or_gt 0 (mainProduct * crossProduct) with hsign | hsign
  · have hproductLeOne : mainProduct * crossProduct ≤ 1 := by
      nlinarith [sq_nonneg (mainProduct - crossProduct), sq_nonneg (mainProduct + crossProduct)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmain) (sub_nonneg.mpr hcross)]
  · nlinarith [hdifference]

/-- **THE REAL LEVER.**  A `2x2` determinant whose four entries lie in `[-1,1]`
and which is itself capped by one in absolute value is quantitatively forced
towards zero by the total entry slack `sum (1 - entry^2)`:

    `(a d - b c)^2 <= (1 - a^2) + (1 - b^2) + (1 - c^2) + (1 - d^2)`.

This is what the equality-case sign kill of `Gtz.SevenThreeCBFloor` lacked.  The
proof routes through `pairProductForm_le_one` on the two products `a d` and
`b c`, then trades `2 - (a d)^2 - (b c)^2` for the entry slack using
`(1-a^2)(1-d^2) >= 0` and `(1-b^2)(1-c^2) >= 0`.  Equality at `(1,1,0,1)`, so
the constant one on each slack term cannot be improved pointwise. -/
theorem sq_twoByTwoMinor_le_entrySlack {topLeft topRight bottomLeft bottomRight : ℝ}
    (htopLeft : topLeft ^ 2 ≤ 1) (htopRight : topRight ^ 2 ≤ 1)
    (hbottomLeft : bottomLeft ^ 2 ≤ 1) (hbottomRight : bottomRight ^ 2 ≤ 1)
    (hminor : (topLeft * bottomRight - topRight * bottomLeft) ^ 2 ≤ 1) :
    (topLeft * bottomRight - topRight * bottomLeft) ^ 2
      ≤ (1 - topLeft ^ 2) + (1 - topRight ^ 2) + (1 - bottomLeft ^ 2)
        + (1 - bottomRight ^ 2) := by
  have hmainSq : (topLeft * bottomRight) ^ 2 ≤ 1 := by nlinarith [htopLeft, hbottomRight]
  have hcrossSq : (topRight * bottomLeft) ^ 2 ≤ 1 := by nlinarith [htopRight, hbottomLeft]
  have hpair := pairProductForm_le_one hmainSq hcrossSq hminor
  nlinarith [mul_nonneg (sub_nonneg.mpr htopLeft) (sub_nonneg.mpr hbottomRight),
    mul_nonneg (sub_nonneg.mpr htopRight) (sub_nonneg.mpr hbottomLeft), hpair]

/-- **The limiting case, and the reason the lever exists at all.**  When all four
entries are exactly `+-1` the `2x2` determinant is an EVEN integer, so the
exchange cap `|det| <= 1` forces it to vanish.  Stated over the reals with
`entry^2 = 1` in place of integrality: the two products `a d` and `b c` are then
`+-1`, and a difference of two such numbers capped by one must be zero.  This is
the zero-slack end of `sq_twoByTwoMinor_le_entrySlack`. -/
theorem twoByTwoSignMinor_eq_zero_of_sq_le_one {topLeft topRight bottomLeft bottomRight : ℝ}
    (htopLeft : topLeft ^ 2 = 1) (htopRight : topRight ^ 2 = 1)
    (hbottomLeft : bottomLeft ^ 2 = 1) (hbottomRight : bottomRight ^ 2 = 1)
    (hminor : (topLeft * bottomRight - topRight * bottomLeft) ^ 2 ≤ 1) :
    topLeft * bottomRight - topRight * bottomLeft = 0 := by
  have hmainSq : (topLeft * bottomRight) ^ 2 = 1 := by
    have hrewrite : (topLeft * bottomRight) ^ 2 = topLeft ^ 2 * bottomRight ^ 2 := by ring
    rw [hrewrite, htopLeft, hbottomRight]
    norm_num
  have hcrossSq : (topRight * bottomLeft) ^ 2 = 1 := by
    have hrewrite : (topRight * bottomLeft) ^ 2 = topRight ^ 2 * bottomLeft ^ 2 := by ring
    rw [hrewrite, htopRight, hbottomLeft]
    norm_num
  have hexpandDifference : (topLeft * bottomRight - topRight * bottomLeft) ^ 2
      = (topLeft * bottomRight) ^ 2 + (topRight * bottomLeft) ^ 2
        - 2 * (topLeft * bottomRight * (topRight * bottomLeft)) := by ring
  rw [hexpandDifference, hmainSq, hcrossSq] at hminor
  have hproductLarge : 1 / 2 ≤ topLeft * bottomRight * (topRight * bottomLeft) := by
    linarith [hminor]
  have hfactored : (topLeft * bottomRight * (topRight * bottomLeft) - 1)
      * (topLeft * bottomRight * (topRight * bottomLeft) + 1) = 0 := by
    have hrewrite : (topLeft * bottomRight * (topRight * bottomLeft) - 1)
        * (topLeft * bottomRight * (topRight * bottomLeft) + 1)
        = (topLeft * bottomRight) ^ 2 * (topRight * bottomLeft) ^ 2 - 1 := by ring
    rw [hrewrite, hmainSq, hcrossSq]
    norm_num
  rcases mul_eq_zero.mp hfactored with hone | hnegativeOne
  · have hproductOne : topLeft * bottomRight * (topRight * bottomLeft) = 1 := by linarith [hone]
    have hsquareZero : (topLeft * bottomRight - topRight * bottomLeft) ^ 2 = 0 := by
      rw [hexpandDifference, hmainSq, hcrossSq, hproductOne]
      ring
    exact sq_eq_zero_iff.mp hsquareZero
  · exfalso
    linarith [hnegativeOne, hproductLarge]

/-- **The lever is FIELD-SENSITIVE**, so barrier B1 (the field-blind ceiling at
`g* = 0.2067052...`) does not exclude it.  Over the complex numbers the limiting
case fails outright: the four entries `(1, 1; (1 + i sqrt 3)/2, 1)` all have
modulus one, their minor `(1 - i sqrt 3)/2` has modulus exactly one -- so it
satisfies the exchange cap -- and it is nonzero.  Real `+-1` entries have no
such configuration (`twoByTwoSignMinor_eq_zero_of_sq_le_one`).  Consuming this
asymmetry is exactly what barriers B1 and B3 demand of any route. -/
theorem exists_complex_unimodular_minor_ne_zero :
    ∃ topLeft topRight bottomLeft bottomRight : ℂ,
      Complex.normSq topLeft = 1 ∧ Complex.normSq topRight = 1
        ∧ Complex.normSq bottomLeft = 1 ∧ Complex.normSq bottomRight = 1
        ∧ Complex.normSq (topLeft * bottomRight - topRight * bottomLeft) = 1
        ∧ topLeft * bottomRight - topRight * bottomLeft ≠ 0 := by
  have hrootSq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hminorValue : (1 : ℂ) * 1 - 1 * Complex.mk (1 / 2) (Real.sqrt 3 / 2)
      = Complex.mk (1 / 2) (-(Real.sqrt 3 / 2)) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
      norm_num
    · simp only [Complex.mul_im, Complex.sub_im, Complex.one_re, Complex.one_im]
      norm_num
  refine ⟨1, 1, Complex.mk (1 / 2) (Real.sqrt 3 / 2), 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Complex.normSq]
  · simp [Complex.normSq]
  · simp only [Complex.normSq_mk]
    nlinarith [hrootSq]
  · simp [Complex.normSq]
  · rw [hminorValue]
    simp only [Complex.normSq_mk]
    nlinarith [hrootSq]
  · rw [hminorValue]
    intro hzero
    have hrealPart : (1 : ℝ) / 2 = 0 := congrArg Complex.re hzero
    norm_num at hrealPart

/-! ## 2. Binet-Cauchy aggregation over the outside block -/

/-- Binet-Cauchy over four rows: the `2x2` Gram minor of two columns is the sum
of the six squared `2x2` row minors. -/
private theorem lagrangeFourRows (leftZero leftOne leftTwo leftThree
    rightZero rightOne rightTwo rightThree : ℝ) :
    (leftZero ^ 2 + leftOne ^ 2 + leftTwo ^ 2 + leftThree ^ 2)
        * (rightZero ^ 2 + rightOne ^ 2 + rightTwo ^ 2 + rightThree ^ 2)
      - (leftZero * rightZero + leftOne * rightOne + leftTwo * rightTwo
          + leftThree * rightThree) ^ 2
      = (leftZero * rightOne - leftOne * rightZero) ^ 2
        + (leftZero * rightTwo - leftTwo * rightZero) ^ 2
        + (leftZero * rightThree - leftThree * rightZero) ^ 2
        + (leftOne * rightTwo - leftTwo * rightOne) ^ 2
        + (leftOne * rightThree - leftThree * rightOne) ^ 2
        + (leftTwo * rightThree - leftThree * rightTwo) ^ 2 := by
  ring

/-- Binet-Cauchy over three rows, for the `(6,3)` twin. -/
private theorem lagrangeThreeRows (leftZero leftOne leftTwo
    rightZero rightOne rightTwo : ℝ) :
    (leftZero ^ 2 + leftOne ^ 2 + leftTwo ^ 2)
        * (rightZero ^ 2 + rightOne ^ 2 + rightTwo ^ 2)
      - (leftZero * rightZero + leftOne * rightOne + leftTwo * rightTwo) ^ 2
      = (leftZero * rightOne - leftOne * rightZero) ^ 2
        + (leftZero * rightTwo - leftTwo * rightZero) ^ 2
        + (leftOne * rightTwo - leftTwo * rightOne) ^ 2 := by
  ring

/-- **The column-pair aggregation, four rows.**  For a `4x3` block whose entries
and whose `2x2` minors are all capped by one, each `2x2` principal minor of the
Gram `X^T X` is at most three times the joint entry slack of its two columns.
The factor three is the number of row pairs through a fixed row among four. -/
theorem columnPairMinor_le_entrySlack_fourRows (block : Matrix (Fin 4) (Fin 3) ℝ)
    (hentrySq : ∀ rowIndex colIndex, block rowIndex colIndex ^ 2 ≤ 1)
    (hminorSq : ∀ (rowFirst rowSecond : Fin 4) (colFirst colSecond : Fin 3),
      (block rowFirst colFirst * block rowSecond colSecond
        - block rowFirst colSecond * block rowSecond colFirst) ^ 2 ≤ 1)
    (colFirst colSecond : Fin 3) :
    (blockᵀ * block) colFirst colFirst * (blockᵀ * block) colSecond colSecond
        - (blockᵀ * block) colFirst colSecond * (blockᵀ * block) colSecond colFirst
      ≤ 3 * (8 - (blockᵀ * block) colFirst colFirst
          - (blockᵀ * block) colSecond colSecond) := by
  have hgram : ∀ leftCol rightCol : Fin 3, (blockᵀ * block) leftCol rightCol
      = block 0 leftCol * block 0 rightCol + block 1 leftCol * block 1 rightCol
        + block 2 leftCol * block 2 rightCol + block 3 leftCol * block 3 rightCol := by
    intro leftCol rightCol
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    simp only [Matrix.transpose_apply]
  rw [hgram, hgram, hgram, hgram]
  have hslack : ∀ rowFirst rowSecond : Fin 4,
      (block rowFirst colFirst * block rowSecond colSecond
          - block rowFirst colSecond * block rowSecond colFirst) ^ 2
        ≤ (1 - block rowFirst colFirst ^ 2) + (1 - block rowFirst colSecond ^ 2)
          + (1 - block rowSecond colFirst ^ 2) + (1 - block rowSecond colSecond ^ 2) := by
    intro rowFirst rowSecond
    have hbound := sq_twoByTwoMinor_le_entrySlack (topLeft := block rowFirst colFirst)
      (topRight := block rowFirst colSecond) (bottomLeft := block rowSecond colFirst)
      (bottomRight := block rowSecond colSecond)
      (hentrySq rowFirst colFirst) (hentrySq rowFirst colSecond)
      (hentrySq rowSecond colFirst) (hentrySq rowSecond colSecond)
      (hminorSq rowFirst rowSecond colFirst colSecond)
    linarith [hbound]
  have hlagrange := lagrangeFourRows (block 0 colFirst) (block 1 colFirst) (block 2 colFirst)
    (block 3 colFirst) (block 0 colSecond) (block 1 colSecond) (block 2 colSecond)
    (block 3 colSecond)
  linarith [hlagrange, hslack 0 1, hslack 0 2, hslack 0 3, hslack 1 2, hslack 1 3, hslack 2 3]

/-- **The column-pair aggregation, three rows** — the `(6,3)` twin.  The factor
two is the number of row pairs through a fixed row among three. -/
theorem columnPairMinor_le_entrySlack_threeRows (block : Matrix (Fin 3) (Fin 3) ℝ)
    (hentrySq : ∀ rowIndex colIndex, block rowIndex colIndex ^ 2 ≤ 1)
    (hminorSq : ∀ (rowFirst rowSecond : Fin 3) (colFirst colSecond : Fin 3),
      (block rowFirst colFirst * block rowSecond colSecond
        - block rowFirst colSecond * block rowSecond colFirst) ^ 2 ≤ 1)
    (colFirst colSecond : Fin 3) :
    (blockᵀ * block) colFirst colFirst * (blockᵀ * block) colSecond colSecond
        - (blockᵀ * block) colFirst colSecond * (blockᵀ * block) colSecond colFirst
      ≤ 2 * (6 - (blockᵀ * block) colFirst colFirst
          - (blockᵀ * block) colSecond colSecond) := by
  have hgram : ∀ leftCol rightCol : Fin 3, (blockᵀ * block) leftCol rightCol
      = block 0 leftCol * block 0 rightCol + block 1 leftCol * block 1 rightCol
        + block 2 leftCol * block 2 rightCol := by
    intro leftCol rightCol
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    simp only [Matrix.transpose_apply]
  rw [hgram, hgram, hgram, hgram]
  have hslack : ∀ rowFirst rowSecond : Fin 3,
      (block rowFirst colFirst * block rowSecond colSecond
          - block rowFirst colSecond * block rowSecond colFirst) ^ 2
        ≤ (1 - block rowFirst colFirst ^ 2) + (1 - block rowFirst colSecond ^ 2)
          + (1 - block rowSecond colFirst ^ 2) + (1 - block rowSecond colSecond ^ 2) := by
    intro rowFirst rowSecond
    have hbound := sq_twoByTwoMinor_le_entrySlack (topLeft := block rowFirst colFirst)
      (topRight := block rowFirst colSecond) (bottomLeft := block rowSecond colFirst)
      (bottomRight := block rowSecond colSecond)
      (hentrySq rowFirst colFirst) (hentrySq rowFirst colSecond)
      (hentrySq rowSecond colFirst) (hentrySq rowSecond colSecond)
      (hminorSq rowFirst rowSecond colFirst colSecond)
    linarith [hbound]
  have hlagrange := lagrangeThreeRows (block 0 colFirst) (block 1 colFirst) (block 2 colFirst)
    (block 0 colSecond) (block 1 colSecond) (block 2 colSecond)
  linarith [hlagrange, hslack 0 1, hslack 0 2, hslack 1 2]

/-! ## 3. The scalar layer: the minor laws, the new cubics, the abstract floors -/

/-- **The minor law in adjugate coordinates, `(7,3)`.**  With `Delta = det Gamma`
and `b = 7 adj(Gamma) - 3 Delta . 1` (so `b = 3 Delta R` for the outside Gram
`R = (7/3) Gamma^-1 - 1`), the combination `e2(R) + 6 e1(R)` scaled by
`9 Delta^2` is exactly `Delta (399 - 84 sigma - 135 Delta)`.  This is the
identity that turns the aggregation into a linear gate on `(sigma, P)`. -/
theorem minorLawIdentity_sevenThree (gramOne gramTwo gramThree determinantValue squareSum : ℝ)
    (hdeterminant : determinantValue
      = 1 - (gramOne ^ 2 + gramTwo ^ 2 + gramThree ^ 2)
        + 2 * (gramOne * gramTwo * gramThree))
    (hsquareSum : squareSum = gramOne ^ 2 + gramTwo ^ 2 + gramThree ^ 2) :
    ((7 * (1 - gramTwo ^ 2) - 3 * determinantValue)
          * (7 * (1 - gramOne ^ 2) - 3 * determinantValue)
        - (7 * (gramOne * gramTwo - gramThree)) ^ 2)
      + ((7 * (1 - gramThree ^ 2) - 3 * determinantValue)
          * (7 * (1 - gramOne ^ 2) - 3 * determinantValue)
        - (7 * (gramOne * gramThree - gramTwo)) ^ 2)
      + ((7 * (1 - gramThree ^ 2) - 3 * determinantValue)
          * (7 * (1 - gramTwo ^ 2) - 3 * determinantValue)
        - (7 * (gramTwo * gramThree - gramOne)) ^ 2)
      + 18 * determinantValue * ((7 * (1 - gramThree ^ 2) - 3 * determinantValue)
          + (7 * (1 - gramTwo ^ 2) - 3 * determinantValue)
          + (7 * (1 - gramOne ^ 2) - 3 * determinantValue))
      = determinantValue * (399 - 84 * squareSum - 135 * determinantValue) := by
  subst hdeterminant
  subst hsquareSum
  ring

/-- **The minor law in adjugate coordinates, `(6,3)`.**  Same skeleton at share
`1/2`, where `b = 2 adj(Gamma) - Delta . 1` and the scaling is `Delta^2`. -/
theorem minorLawIdentity_sixThree (gramOne gramTwo gramThree determinantValue squareSum : ℝ)
    (hdeterminant : determinantValue
      = 1 - (gramOne ^ 2 + gramTwo ^ 2 + gramThree ^ 2)
        + 2 * (gramOne * gramTwo * gramThree))
    (hsquareSum : squareSum = gramOne ^ 2 + gramTwo ^ 2 + gramThree ^ 2) :
    ((2 * (1 - gramTwo ^ 2) - determinantValue) * (2 * (1 - gramOne ^ 2) - determinantValue)
        - (2 * (gramOne * gramTwo - gramThree)) ^ 2)
      + ((2 * (1 - gramThree ^ 2) - determinantValue)
          * (2 * (1 - gramOne ^ 2) - determinantValue)
        - (2 * (gramOne * gramThree - gramTwo)) ^ 2)
      + ((2 * (1 - gramThree ^ 2) - determinantValue)
          * (2 * (1 - gramTwo ^ 2) - determinantValue)
        - (2 * (gramTwo * gramThree - gramOne)) ^ 2)
      + 4 * determinantValue * ((2 * (1 - gramThree ^ 2) - determinantValue)
          + (2 * (1 - gramTwo ^ 2) - determinantValue)
          + (2 * (1 - gramOne ^ 2) - determinantValue))
      = determinantValue * (24 - 4 * squareSum - 9 * determinantValue) := by
  subst hdeterminant
  subst hsquareSum
  ring

/-- **The new floor cubic and the new relaxation cubic are the same object.**
Under the eigenvalue dictionary `u = (7 - 3x)/(3x)` between the outside mass `R`
and the picked Gram, the minor-refined relaxation cubic
`17 u^3 - 168 u^2 + 216 u - 68` -- whose root set is the outside spectrum forced
by `(e1, e2, e3) = (168/17, 216/17, 4)` at the gate corner -- becomes `-7` times
`C**(x) = 1809 x^3 - 5427 x^2 + 4599 x - 833`, cleared of denominators.  So the
largest root `u* = 8.4316983...` corresponds to the smallest root
`g** = 0.2473927...`. -/
theorem minorRelaxationCubic_image_eq_minorFloorCubic_sevenThree (floorValue : ℝ) :
    17 * (7 - 3 * floorValue) ^ 3 - 168 * (3 * floorValue) * (7 - 3 * floorValue) ^ 2
        + 216 * (3 * floorValue) ^ 2 * (7 - 3 * floorValue) - 68 * (3 * floorValue) ^ 3
      = -7 * (1809 * floorValue ^ 3 - 5427 * floorValue ^ 2 + 4599 * floorValue - 833) := by
  ring

/-- The new floor cubic is negative at the landed rational floor `37/150`, so the
exact minor-relaxation optimum `g**` lies strictly ABOVE `37/150`.  Exact value
`C**(37/150) = -204099/125000`. -/
theorem minorFloorCubic_sevenThree_neg_at_landedFloor :
    1809 * ((37 : ℝ) / 150) ^ 3 - 5427 * ((37 : ℝ) / 150) ^ 2 + 4599 * ((37 : ℝ) / 150) - 833
      = -(204099 / 125000) := by
  norm_num

/-- The new floor cubic is positive at `1/4`, so `g**` lies strictly BELOW `1/4`.
Exact value `C**(1/4) = 373/64`.  With the previous sign this brackets
`g** in (37/150, 1/4)`: the minor-refined exchange relaxation CANNOT reach a
quarter, let alone a third. -/
theorem minorFloorCubic_sevenThree_pos_at_quarter :
    0 < 1809 * ((1 : ℝ) / 4) ^ 3 - 5427 * ((1 : ℝ) / 4) ^ 2 + 4599 * ((1 : ℝ) / 4) - 833 := by
  norm_num

/-- The `(6,3)` minor-relaxation optimum is the algebraic number
`1 - sqrt 861 / 41 = 0.2843225...`, the root in `(0,1)` of `41 x^2 - 82 x + 20`.
The quadratic opens upward, so it is POSITIVE below that root: value `159/625`
at the landed floor `7/25`. -/
theorem minorFloorQuadratic_sixThree_pos_at_landedFloor :
    41 * ((7 : ℝ) / 25) ^ 2 - 82 * ((7 : ℝ) / 25) + 20 = 159 / 625 := by
  norm_num

/-- ...and NEGATIVE just above it: value `-4/49` at `2/7`.  Together these
bracket the `(6,3)` minor-relaxation optimum in `(7/25, 2/7)`. -/
theorem minorFloorQuadratic_sixThree_neg_at_upperBracket :
    41 * ((2 : ℝ) / 7) ^ 2 - 82 * ((2 : ℝ) / 7) + 20 = -(4 / 49) := by
  norm_num

/-- Diagonal entry of a shift.  (Private twin of the shift helpers owned by
`Gtz.SevenThreeCBFloor`, which keeps them file-local.) -/
private theorem shiftedDiagonalEntry (gram : Matrix (Fin 3) (Fin 3) ℝ) (shift : ℝ)
    (index : Fin 3) : (gram - shift • 1) index index = gram index index - shift := by
  simp [Matrix.sub_apply, Matrix.smul_apply]

/-- Off-diagonal entry of a shift. -/
private theorem shiftedOffDiagonalEntry (gram : Matrix (Fin 3) (Fin 3) ℝ) (shift : ℝ)
    {rowIndex colIndex : Fin 3} (hne : rowIndex ≠ colIndex) :
    (gram - shift • 1) rowIndex colIndex = gram rowIndex colIndex := by
  simp [Matrix.sub_apply, Matrix.smul_apply, hne]

/-- The shifted determinant of a symmetric unit-diagonal `3x3` matrix in
`(sigma, P)` coordinates. -/
private theorem detShifted_of_symmetric_unitDiagonal {gram : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymmetric : gramᵀ = gram)
    (hdiagZero : gram 0 0 = 1) (hdiagOne : gram 1 1 = 1) (hdiagTwo : gram 2 2 = 1)
    (shift : ℝ) :
    (gram - shift • 1).det
      = (1 - shift) ^ 3 - (1 - shift) * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
        + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
  have hflipOne : gram 1 0 = gram 0 1 := congrFun (congrFun hsymmetric 0) 1
  have hflipTwo : gram 2 0 = gram 0 2 := congrFun (congrFun hsymmetric 0) 2
  have hflipThree : gram 2 1 = gram 1 2 := congrFun (congrFun hsymmetric 1) 2
  rw [Matrix.det_fin_three, shiftedDiagonalEntry, shiftedDiagonalEntry, shiftedDiagonalEntry,
    shiftedOffDiagonalEntry gram shift (by decide : (0 : Fin 3) ≠ 1),
    shiftedOffDiagonalEntry gram shift (by decide : (0 : Fin 3) ≠ 2),
    shiftedOffDiagonalEntry gram shift (by decide : (1 : Fin 3) ≠ 0),
    shiftedOffDiagonalEntry gram shift (by decide : (1 : Fin 3) ≠ 2),
    shiftedOffDiagonalEntry gram shift (by decide : (2 : Fin 3) ≠ 0),
    shiftedOffDiagonalEntry gram shift (by decide : (2 : Fin 3) ≠ 1),
    hdiagZero, hdiagOne, hdiagTwo, hflipOne, hflipTwo, hflipThree]
  ring

/-- **THE MINOR GATE, abstract form at `(7,3)`.**  A symmetric unit-diagonal
correlation matrix `Gamma` with positive determinant, related to an auxiliary
matrix `R` by the isotropy law `det(Gamma) . (1 + R) = (7/3) . adj(Gamma)` and
satisfying `e2(R) + 6 e1(R) <= 72`, obeys `233 sigma - 128 <= 522 P`.  All nine
scaled entries `3 Delta R_jk` are read off the adjugate, and the collapse is the
`ring` identity `minorLawIdentity_sevenThree` followed by one division by
`Delta > 0`. -/
theorem minorGateFromAdjugateLaw_sevenThree {gram outsideGram : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymmetric : gramᵀ = gram)
    (hdiagZero : gram 0 0 = 1) (hdiagOne : gram 1 1 = 1) (hdiagTwo : gram 2 2 = 1)
    (hdetPos : 0 < gram.det)
    (hlaw : gram.det • ((1 : Matrix (Fin 3) (Fin 3) ℝ) + outsideGram)
      = (7 / 3 : ℝ) • gram.adjugate)
    (hbound : (outsideGram 0 0 * outsideGram 1 1 - outsideGram 0 1 * outsideGram 1 0)
      + (outsideGram 0 0 * outsideGram 2 2 - outsideGram 0 2 * outsideGram 2 0)
      + (outsideGram 1 1 * outsideGram 2 2 - outsideGram 1 2 * outsideGram 2 1)
      + 6 * (outsideGram 0 0 + outsideGram 1 1 + outsideGram 2 2) ≤ 72) :
    233 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 128
      ≤ 522 * (gram 0 1 * gram 0 2 * gram 1 2) := by
  have hflipOne : gram 1 0 = gram 0 1 := congrFun (congrFun hsymmetric 0) 1
  have hflipTwo : gram 2 0 = gram 0 2 := congrFun (congrFun hsymmetric 0) 2
  have hflipThree : gram 2 1 = gram 1 2 := congrFun (congrFun hsymmetric 1) 2
  have hdetCoord : gram.det
      = 1 - (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
        + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
    have hshift := detShifted_of_symmetric_unitDiagonal hsymmetric hdiagZero hdiagOne hdiagTwo 0
    rw [zero_smul, sub_zero] at hshift
    rw [hshift]
    ring
  have hentryLaw : ∀ rowSlot colSlot : Fin 3,
      gram.det * ((1 : Matrix (Fin 3) (Fin 3) ℝ) rowSlot colSlot + outsideGram rowSlot colSlot)
        = 7 / 3 * gram.adjugate rowSlot colSlot := by
    intro rowSlot colSlot
    have hval := congrFun (congrFun hlaw rowSlot) colSlot
    simpa [Matrix.smul_apply, Matrix.add_apply] using hval
  have hadjZeroZero : gram.adjugate 0 0 = gram 1 1 * gram 2 2 - gram 1 2 * gram 2 1 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjOneOne : gram.adjugate 1 1 = gram 0 0 * gram 2 2 - gram 0 2 * gram 2 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjTwoTwo : gram.adjugate 2 2 = gram 0 0 * gram 1 1 - gram 0 1 * gram 1 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjZeroOne : gram.adjugate 0 1 = -(gram 0 1 * gram 2 2) + gram 0 2 * gram 2 1 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjOneZero : gram.adjugate 1 0 = -(gram 1 0 * gram 2 2) + gram 1 2 * gram 2 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjZeroTwo : gram.adjugate 0 2 = gram 0 1 * gram 1 2 - gram 0 2 * gram 1 1 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjTwoZero : gram.adjugate 2 0 = gram 1 0 * gram 2 1 - gram 1 1 * gram 2 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjOneTwo : gram.adjugate 1 2 = -(gram 0 0 * gram 1 2) + gram 0 2 * gram 1 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjTwoOne : gram.adjugate 2 1 = -(gram 0 0 * gram 2 1) + gram 0 1 * gram 2 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hscaledZeroZero : 3 * gram.det * outsideGram 0 0
      = 7 * (1 - gram 1 2 ^ 2) - 3 * gram.det := by
    have hval := hentryLaw 0 0
    rw [Matrix.one_apply_eq, hadjZeroZero, hdiagOne, hdiagTwo, hflipThree] at hval
    linear_combination 3 * hval
  have hscaledOneOne : 3 * gram.det * outsideGram 1 1
      = 7 * (1 - gram 0 2 ^ 2) - 3 * gram.det := by
    have hval := hentryLaw 1 1
    rw [Matrix.one_apply_eq, hadjOneOne, hdiagZero, hdiagTwo, hflipTwo] at hval
    linear_combination 3 * hval
  have hscaledTwoTwo : 3 * gram.det * outsideGram 2 2
      = 7 * (1 - gram 0 1 ^ 2) - 3 * gram.det := by
    have hval := hentryLaw 2 2
    rw [Matrix.one_apply_eq, hadjTwoTwo, hdiagZero, hdiagOne, hflipOne] at hval
    linear_combination 3 * hval
  have hscaledZeroOne : 3 * gram.det * outsideGram 0 1
      = 7 * (gram 0 2 * gram 1 2 - gram 0 1) := by
    have hval := hentryLaw 0 1
    rw [Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 1), hadjZeroOne, hdiagTwo,
      hflipThree] at hval
    linear_combination 3 * hval
  have hscaledOneZero : 3 * gram.det * outsideGram 1 0
      = 7 * (gram 0 2 * gram 1 2 - gram 0 1) := by
    have hval := hentryLaw 1 0
    rw [Matrix.one_apply_ne (by decide : (1 : Fin 3) ≠ 0), hadjOneZero, hflipOne, hdiagTwo,
      hflipTwo] at hval
    linear_combination 3 * hval
  have hscaledZeroTwo : 3 * gram.det * outsideGram 0 2
      = 7 * (gram 0 1 * gram 1 2 - gram 0 2) := by
    have hval := hentryLaw 0 2
    rw [Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 2), hadjZeroTwo, hdiagOne] at hval
    linear_combination 3 * hval
  have hscaledTwoZero : 3 * gram.det * outsideGram 2 0
      = 7 * (gram 0 1 * gram 1 2 - gram 0 2) := by
    have hval := hentryLaw 2 0
    rw [Matrix.one_apply_ne (by decide : (2 : Fin 3) ≠ 0), hadjTwoZero, hflipOne, hflipThree,
      hdiagOne, hflipTwo] at hval
    linear_combination 3 * hval
  have hscaledOneTwo : 3 * gram.det * outsideGram 1 2
      = 7 * (gram 0 1 * gram 0 2 - gram 1 2) := by
    have hval := hentryLaw 1 2
    rw [Matrix.one_apply_ne (by decide : (1 : Fin 3) ≠ 2), hadjOneTwo, hdiagZero,
      hflipOne] at hval
    linear_combination 3 * hval
  have hscaledTwoOne : 3 * gram.det * outsideGram 2 1
      = 7 * (gram 0 1 * gram 0 2 - gram 1 2) := by
    have hval := hentryLaw 2 1
    rw [Matrix.one_apply_ne (by decide : (2 : Fin 3) ≠ 1), hadjTwoOne, hdiagZero, hflipThree,
      hflipTwo] at hval
    linear_combination 3 * hval
  have hexpanded : 9 * gram.det ^ 2
      * ((outsideGram 0 0 * outsideGram 1 1 - outsideGram 0 1 * outsideGram 1 0)
        + (outsideGram 0 0 * outsideGram 2 2 - outsideGram 0 2 * outsideGram 2 0)
        + (outsideGram 1 1 * outsideGram 2 2 - outsideGram 1 2 * outsideGram 2 1)
        + 6 * (outsideGram 0 0 + outsideGram 1 1 + outsideGram 2 2))
      = ((3 * gram.det * outsideGram 1 1) * (3 * gram.det * outsideGram 2 2)
            - (3 * gram.det * outsideGram 1 2) * (3 * gram.det * outsideGram 2 1))
        + ((3 * gram.det * outsideGram 0 0) * (3 * gram.det * outsideGram 2 2)
            - (3 * gram.det * outsideGram 0 2) * (3 * gram.det * outsideGram 2 0))
        + ((3 * gram.det * outsideGram 0 0) * (3 * gram.det * outsideGram 1 1)
            - (3 * gram.det * outsideGram 0 1) * (3 * gram.det * outsideGram 1 0))
        + 18 * gram.det * ((3 * gram.det * outsideGram 0 0)
            + (3 * gram.det * outsideGram 1 1)
            + (3 * gram.det * outsideGram 2 2)) := by ring
  have hidentity := minorLawIdentity_sevenThree (gram 0 1) (gram 0 2) (gram 1 2) gram.det
    (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) hdetCoord rfl
  have hcombined : 9 * gram.det ^ 2
      * ((outsideGram 0 0 * outsideGram 1 1 - outsideGram 0 1 * outsideGram 1 0)
        + (outsideGram 0 0 * outsideGram 2 2 - outsideGram 0 2 * outsideGram 2 0)
        + (outsideGram 1 1 * outsideGram 2 2 - outsideGram 1 2 * outsideGram 2 1)
        + 6 * (outsideGram 0 0 + outsideGram 1 1 + outsideGram 2 2))
      = gram.det * (399 - 84 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
        - 135 * gram.det) := by
    rw [hexpanded, hscaledZeroZero, hscaledOneOne, hscaledTwoTwo, hscaledZeroOne, hscaledOneZero,
      hscaledZeroTwo, hscaledTwoZero, hscaledOneTwo, hscaledTwoOne]
    linear_combination hidentity
  have hscaleNonneg : (0 : ℝ) ≤ 9 * gram.det ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hbound hscaleNonneg
  rw [hcombined] at hscaled
  have hdivisible : gram.det * (399 - 84 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
      - 135 * gram.det) ≤ gram.det * (648 * gram.det) := by
    have hring : gram.det * (648 * gram.det) = 9 * gram.det ^ 2 * 72 := by ring
    rw [hring]
    exact hscaled
  have hresult := le_of_mul_le_mul_left hdivisible hdetPos
  rw [hdetCoord] at hresult
  linarith [hresult]

/-- **THE MINOR GATE, abstract form at `(6,3)`.**  Share `1/2`: the isotropy law
is `det(Gamma) . (1 + R) = 2 . adj(Gamma)`, the aggregation is
`e2(R) + 4 e1(R) <= 36`, and the gate is `41 sigma - 21 <= 90 P`. -/
theorem minorGateFromAdjugateLaw_sixThree {gram outsideGram : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymmetric : gramᵀ = gram)
    (hdiagZero : gram 0 0 = 1) (hdiagOne : gram 1 1 = 1) (hdiagTwo : gram 2 2 = 1)
    (hdetPos : 0 < gram.det)
    (hlaw : gram.det • ((1 : Matrix (Fin 3) (Fin 3) ℝ) + outsideGram)
      = (2 : ℝ) • gram.adjugate)
    (hbound : (outsideGram 0 0 * outsideGram 1 1 - outsideGram 0 1 * outsideGram 1 0)
      + (outsideGram 0 0 * outsideGram 2 2 - outsideGram 0 2 * outsideGram 2 0)
      + (outsideGram 1 1 * outsideGram 2 2 - outsideGram 1 2 * outsideGram 2 1)
      + 4 * (outsideGram 0 0 + outsideGram 1 1 + outsideGram 2 2) ≤ 36) :
    41 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 21
      ≤ 90 * (gram 0 1 * gram 0 2 * gram 1 2) := by
  have hflipOne : gram 1 0 = gram 0 1 := congrFun (congrFun hsymmetric 0) 1
  have hflipTwo : gram 2 0 = gram 0 2 := congrFun (congrFun hsymmetric 0) 2
  have hflipThree : gram 2 1 = gram 1 2 := congrFun (congrFun hsymmetric 1) 2
  have hdetCoord : gram.det
      = 1 - (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
        + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
    have hshift := detShifted_of_symmetric_unitDiagonal hsymmetric hdiagZero hdiagOne hdiagTwo 0
    rw [zero_smul, sub_zero] at hshift
    rw [hshift]
    ring
  have hentryLaw : ∀ rowSlot colSlot : Fin 3,
      gram.det * ((1 : Matrix (Fin 3) (Fin 3) ℝ) rowSlot colSlot + outsideGram rowSlot colSlot)
        = 2 * gram.adjugate rowSlot colSlot := by
    intro rowSlot colSlot
    have hval := congrFun (congrFun hlaw rowSlot) colSlot
    simpa [Matrix.smul_apply, Matrix.add_apply] using hval
  have hadjZeroZero : gram.adjugate 0 0 = gram 1 1 * gram 2 2 - gram 1 2 * gram 2 1 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjOneOne : gram.adjugate 1 1 = gram 0 0 * gram 2 2 - gram 0 2 * gram 2 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjTwoTwo : gram.adjugate 2 2 = gram 0 0 * gram 1 1 - gram 0 1 * gram 1 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjZeroOne : gram.adjugate 0 1 = -(gram 0 1 * gram 2 2) + gram 0 2 * gram 2 1 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjOneZero : gram.adjugate 1 0 = -(gram 1 0 * gram 2 2) + gram 1 2 * gram 2 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjZeroTwo : gram.adjugate 0 2 = gram 0 1 * gram 1 2 - gram 0 2 * gram 1 1 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjTwoZero : gram.adjugate 2 0 = gram 1 0 * gram 2 1 - gram 1 1 * gram 2 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjOneTwo : gram.adjugate 1 2 = -(gram 0 0 * gram 1 2) + gram 0 2 * gram 1 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hadjTwoOne : gram.adjugate 2 1 = -(gram 0 0 * gram 2 1) + gram 0 1 * gram 2 0 := by
    rw [Matrix.adjugate_fin_three]; simp
  have hscaledZeroZero : gram.det * outsideGram 0 0
      = 2 * (1 - gram 1 2 ^ 2) - gram.det := by
    have hval := hentryLaw 0 0
    rw [Matrix.one_apply_eq, hadjZeroZero, hdiagOne, hdiagTwo, hflipThree] at hval
    linear_combination hval
  have hscaledOneOne : gram.det * outsideGram 1 1
      = 2 * (1 - gram 0 2 ^ 2) - gram.det := by
    have hval := hentryLaw 1 1
    rw [Matrix.one_apply_eq, hadjOneOne, hdiagZero, hdiagTwo, hflipTwo] at hval
    linear_combination hval
  have hscaledTwoTwo : gram.det * outsideGram 2 2
      = 2 * (1 - gram 0 1 ^ 2) - gram.det := by
    have hval := hentryLaw 2 2
    rw [Matrix.one_apply_eq, hadjTwoTwo, hdiagZero, hdiagOne, hflipOne] at hval
    linear_combination hval
  have hscaledZeroOne : gram.det * outsideGram 0 1
      = 2 * (gram 0 2 * gram 1 2 - gram 0 1) := by
    have hval := hentryLaw 0 1
    rw [Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 1), hadjZeroOne, hdiagTwo,
      hflipThree] at hval
    linear_combination hval
  have hscaledOneZero : gram.det * outsideGram 1 0
      = 2 * (gram 0 2 * gram 1 2 - gram 0 1) := by
    have hval := hentryLaw 1 0
    rw [Matrix.one_apply_ne (by decide : (1 : Fin 3) ≠ 0), hadjOneZero, hflipOne, hdiagTwo,
      hflipTwo] at hval
    linear_combination hval
  have hscaledZeroTwo : gram.det * outsideGram 0 2
      = 2 * (gram 0 1 * gram 1 2 - gram 0 2) := by
    have hval := hentryLaw 0 2
    rw [Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 2), hadjZeroTwo, hdiagOne] at hval
    linear_combination hval
  have hscaledTwoZero : gram.det * outsideGram 2 0
      = 2 * (gram 0 1 * gram 1 2 - gram 0 2) := by
    have hval := hentryLaw 2 0
    rw [Matrix.one_apply_ne (by decide : (2 : Fin 3) ≠ 0), hadjTwoZero, hflipOne, hflipThree,
      hdiagOne, hflipTwo] at hval
    linear_combination hval
  have hscaledOneTwo : gram.det * outsideGram 1 2
      = 2 * (gram 0 1 * gram 0 2 - gram 1 2) := by
    have hval := hentryLaw 1 2
    rw [Matrix.one_apply_ne (by decide : (1 : Fin 3) ≠ 2), hadjOneTwo, hdiagZero,
      hflipOne] at hval
    linear_combination hval
  have hscaledTwoOne : gram.det * outsideGram 2 1
      = 2 * (gram 0 1 * gram 0 2 - gram 1 2) := by
    have hval := hentryLaw 2 1
    rw [Matrix.one_apply_ne (by decide : (2 : Fin 3) ≠ 1), hadjTwoOne, hdiagZero, hflipThree,
      hflipTwo] at hval
    linear_combination hval
  have hexpanded : gram.det ^ 2
      * ((outsideGram 0 0 * outsideGram 1 1 - outsideGram 0 1 * outsideGram 1 0)
        + (outsideGram 0 0 * outsideGram 2 2 - outsideGram 0 2 * outsideGram 2 0)
        + (outsideGram 1 1 * outsideGram 2 2 - outsideGram 1 2 * outsideGram 2 1)
        + 4 * (outsideGram 0 0 + outsideGram 1 1 + outsideGram 2 2))
      = ((gram.det * outsideGram 1 1) * (gram.det * outsideGram 2 2)
            - (gram.det * outsideGram 1 2) * (gram.det * outsideGram 2 1))
        + ((gram.det * outsideGram 0 0) * (gram.det * outsideGram 2 2)
            - (gram.det * outsideGram 0 2) * (gram.det * outsideGram 2 0))
        + ((gram.det * outsideGram 0 0) * (gram.det * outsideGram 1 1)
            - (gram.det * outsideGram 0 1) * (gram.det * outsideGram 1 0))
        + 4 * gram.det * ((gram.det * outsideGram 0 0)
            + (gram.det * outsideGram 1 1)
            + (gram.det * outsideGram 2 2)) := by ring
  have hidentity := minorLawIdentity_sixThree (gram 0 1) (gram 0 2) (gram 1 2) gram.det
    (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) hdetCoord rfl
  have hcombined : gram.det ^ 2
      * ((outsideGram 0 0 * outsideGram 1 1 - outsideGram 0 1 * outsideGram 1 0)
        + (outsideGram 0 0 * outsideGram 2 2 - outsideGram 0 2 * outsideGram 2 0)
        + (outsideGram 1 1 * outsideGram 2 2 - outsideGram 1 2 * outsideGram 2 1)
        + 4 * (outsideGram 0 0 + outsideGram 1 1 + outsideGram 2 2))
      = gram.det * (24 - 4 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
        - 9 * gram.det) := by
    rw [hexpanded, hscaledZeroZero, hscaledOneOne, hscaledTwoTwo, hscaledZeroOne, hscaledOneZero,
      hscaledZeroTwo, hscaledTwoZero, hscaledOneTwo, hscaledTwoOne]
    linear_combination hidentity
  have hscaleNonneg : (0 : ℝ) ≤ gram.det ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hbound hscaleNonneg
  rw [hcombined] at hscaled
  have hdivisible : gram.det * (24 - 4 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
      - 9 * gram.det) ≤ gram.det * (36 * gram.det) := by
    have hring : gram.det * (36 * gram.det) = gram.det ^ 2 * 36 := by ring
    rw [hring]
    exact hscaled
  have hresult := le_of_mul_le_mul_left hdivisible hdetPos
  rw [hdetCoord] at hresult
  linarith [hresult]

/-- **THE ABSTRACT MINOR FLOOR, `(7,3)`.**  A symmetric unit-diagonal `3x3`
correlation matrix with positive determinant satisfying the MINOR GATE
`233 sigma - 128 <= 522 P` and the landed VOLUME GATE `36 sigma - 22 <= 135 P`
is positive definite past `37/150`.  Eigenvalue-free: the minor gate implies the
landed trace gate for `sigma >= 0`, whence the `sigma`-cap `4/3` of
`Gtz.SevenThreeCBFloor` supplies `e2 > 0`, and the determinant is LINEAR in
`(sigma, P)` with exact margin `68033/75375000` at the gates' corner
`(92/201, -74/1809)`. -/
theorem posDef_sub_minorFloor_of_exchangeGates_sevenThree
    {gram : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : gramᵀ = gram)
    (hdiagZero : gram 0 0 = 1) (hdiagOne : gram 1 1 = 1) (hdiagTwo : gram 2 2 = 1)
    (hdetPos : 0 < gram.det)
    (hentryRange : gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2 ≤ 3)
    (hminorGate : 233 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 128
      ≤ 522 * (gram 0 1 * gram 0 2 * gram 1 2))
    (hvolumeGate : 36 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 22
      ≤ 135 * (gram 0 1 * gram 0 2 * gram 1 2)) :
    (gram - (37 / 150 : ℝ) • 1).PosDef := by
  have hflipOne : gram 1 0 = gram 0 1 := congrFun (congrFun hsymmetric 0) 1
  have hflipTwo : gram 2 0 = gram 0 2 := congrFun (congrFun hsymmetric 0) 2
  have hflipThree : gram 2 1 = gram 1 2 := congrFun (congrFun hsymmetric 1) 2
  have hdetCoord : 0 < 1 - (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
      + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
    have hzeroShift := detShifted_of_symmetric_unitDiagonal hsymmetric hdiagZero hdiagOne
      hdiagTwo 0
    rw [zero_smul, sub_zero] at hzeroShift
    rw [hzeroShift] at hdetPos
    linarith [hdetPos]
  have hsigmaNonneg : 0 ≤ gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2 := by positivity
  have htraceGate : 38 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 24
      ≤ 90 * (gram 0 1 * gram 0 2 * gram 1 2) := by linarith [hminorGate, hsigmaNonneg]
  have hamgm : 27 * (gram 0 1 * gram 0 2 * gram 1 2) ^ 2
      ≤ (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) ^ 3 := by
    have hcube := twentySeven_mul_sq_tripleProduct_le_cube_squareSum
      (gram 0 1) (gram 0 2) (gram 1 2)
    nlinarith [hcube]
  have hsigmaCap := squareSum_le_fourThirds_of_traceGate htraceGate hamgm hentryRange hdetCoord
  have hsymShift : (gram - (37 / 150 : ℝ) • 1)ᵀ = gram - (37 / 150 : ℝ) • 1 := by
    rw [Matrix.transpose_sub, hsymmetric, Matrix.transpose_smul, Matrix.transpose_one]
  refine posDef_three_of_elementarySymmetric hsymShift ?_ ?_ ?_
  · rw [shiftedDiagonalEntry, shiftedDiagonalEntry, shiftedDiagonalEntry,
      hdiagZero, hdiagOne, hdiagTwo]
    norm_num
  · rw [shiftedDiagonalEntry, shiftedDiagonalEntry, shiftedDiagonalEntry,
      shiftedOffDiagonalEntry gram _ (by decide : (0 : Fin 3) ≠ 1),
      shiftedOffDiagonalEntry gram _ (by decide : (0 : Fin 3) ≠ 2),
      shiftedOffDiagonalEntry gram _ (by decide : (1 : Fin 3) ≠ 0),
      shiftedOffDiagonalEntry gram _ (by decide : (1 : Fin 3) ≠ 2),
      shiftedOffDiagonalEntry gram _ (by decide : (2 : Fin 3) ≠ 0),
      shiftedOffDiagonalEntry gram _ (by decide : (2 : Fin 3) ≠ 1),
      hdiagZero, hdiagOne, hdiagTwo, hflipOne, hflipTwo, hflipThree]
    nlinarith [hsigmaCap]
  · rw [detShifted_of_symmetric_unitDiagonal hsymmetric hdiagZero hdiagOne hdiagTwo]
    linarith [hminorGate, hvolumeGate]

/-- **THE ABSTRACT MINOR FLOOR, `(6,3)`.**  Same skeleton at share `1/2`: the
minor gate is `41 sigma - 21 <= 90 P`, the volume gate degenerates to `P >= 0`,
the `sigma`-cap is `5/4`, and the floor is `7/25 = 0.28`, with exact determinant
margin `2862/640625` at the corner `(sigma, P) = (21/41, 0)`. -/
theorem posDef_sub_minorFloor_of_exchangeGates_sixThree
    {gram : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : gramᵀ = gram)
    (hdiagZero : gram 0 0 = 1) (hdiagOne : gram 1 1 = 1) (hdiagTwo : gram 2 2 = 1)
    (hdetPos : 0 < gram.det)
    (hentryRange : gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2 ≤ 3)
    (hminorGate : 41 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 21
      ≤ 90 * (gram 0 1 * gram 0 2 * gram 1 2))
    (hproductGate : 0 ≤ gram 0 1 * gram 0 2 * gram 1 2) :
    (gram - (7 / 25 : ℝ) • 1).PosDef := by
  have hflipOne : gram 1 0 = gram 0 1 := congrFun (congrFun hsymmetric 0) 1
  have hflipTwo : gram 2 0 = gram 0 2 := congrFun (congrFun hsymmetric 0) 2
  have hflipThree : gram 2 1 = gram 1 2 := congrFun (congrFun hsymmetric 1) 2
  have hdetCoord : 0 < 1 - (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
      + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
    have hzeroShift := detShifted_of_symmetric_unitDiagonal hsymmetric hdiagZero hdiagOne
      hdiagTwo 0
    rw [zero_smul, sub_zero] at hzeroShift
    rw [hzeroShift] at hdetPos
    linarith [hdetPos]
  have hsigmaNonneg : 0 ≤ gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2 := by positivity
  have htraceGate : 5 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 3
      ≤ 12 * (gram 0 1 * gram 0 2 * gram 1 2) := by linarith [hminorGate, hsigmaNonneg]
  have hamgm : 27 * (gram 0 1 * gram 0 2 * gram 1 2) ^ 2
      ≤ (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) ^ 3 := by
    have hcube := twentySeven_mul_sq_tripleProduct_le_cube_squareSum
      (gram 0 1) (gram 0 2) (gram 1 2)
    nlinarith [hcube]
  have hsigmaCap := squareSum_le_fiveFourths_of_traceGate htraceGate hamgm hentryRange hdetCoord
  have hsymShift : (gram - (7 / 25 : ℝ) • 1)ᵀ = gram - (7 / 25 : ℝ) • 1 := by
    rw [Matrix.transpose_sub, hsymmetric, Matrix.transpose_smul, Matrix.transpose_one]
  refine posDef_three_of_elementarySymmetric hsymShift ?_ ?_ ?_
  · rw [shiftedDiagonalEntry, shiftedDiagonalEntry, shiftedDiagonalEntry,
      hdiagZero, hdiagOne, hdiagTwo]
    norm_num
  · rw [shiftedDiagonalEntry, shiftedDiagonalEntry, shiftedDiagonalEntry,
      shiftedOffDiagonalEntry gram _ (by decide : (0 : Fin 3) ≠ 1),
      shiftedOffDiagonalEntry gram _ (by decide : (0 : Fin 3) ≠ 2),
      shiftedOffDiagonalEntry gram _ (by decide : (1 : Fin 3) ≠ 0),
      shiftedOffDiagonalEntry gram _ (by decide : (1 : Fin 3) ≠ 2),
      shiftedOffDiagonalEntry gram _ (by decide : (2 : Fin 3) ≠ 0),
      shiftedOffDiagonalEntry gram _ (by decide : (2 : Fin 3) ≠ 1),
      hdiagZero, hdiagOne, hdiagTwo, hflipOne, hflipTwo, hflipThree]
    nlinarith [hsigmaCap]
  · rw [detShifted_of_symmetric_unitDiagonal hsymmetric hdiagZero hdiagOne hdiagTwo]
    linarith [hminorGate, hproductGate]

/-! ## 4. Plumbing: the frame law, the solve Gram, the adjugate, the row split -/

/-- The solve-matrix entry at a picked row is the identity entry. -/
private theorem solveMatrixEntryAtPick {frameSize selectionRank : ℕ}
    (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize)
    (hunit : IsUnit (selectedFrameRows frame pick).det) (slot colIndex : Fin selectionRank) :
    solveMatrix frame pick (pick slot) colIndex
      = (1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ) slot colIndex := by
  have hidentity := congrFun (congrFun (solveMatrix_submatrix_pick frame pick hunit) slot) colIndex
  simpa [Matrix.submatrix_apply] using hidentity

/-- The frame law of the unit rows at uniform share: `U^T U = share^-1 . 1`. -/
private theorem transposeMulUnitAtomRows_uniformShare {m k : ℕ} (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hsharePos : 0 < shareValue) :
    (unitAtomRows D)ᵀ * unitAtomRows D = shareValue⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  calc (unitAtomRows D)ᵀ * unitAtomRows D
      = ∑ atomIndex, atomMatrix (unitAtomRows D atomIndex) :=
        transpose_mul_self_eq_sum_rows (unitAtomRows D)
    _ = shareValue⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) :=
        sum_atomMatrix_unitAtom_of_uniformShare D huniform hsharePos

/-- The solve Gram is the rescaled inverse picked Gram. -/
private theorem solveGramEqSmulInvPickGram {m k : ℕ} (D : WeightedDesign m k) {shareValue : ℝ}
    (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue) (hsharePos : 0 < shareValue)
    (pick : Fin k → Fin m) :
    (solveMatrix (unitAtomRows D) pick)ᵀ * solveMatrix (unitAtomRows D) pick
      = shareValue⁻¹ • (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ)⁻¹ := by
  rw [solveMatrix, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (unitAtomRows D)ᵀ,
    transposeMulUnitAtomRows_uniformShare D huniform hsharePos,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]

/-- **`det(Gamma) . (Y^T Y) = share^-1 . adj(Gamma)`** — Cramer's rule with the
inverse supplied by the solve-Gram identity, in the inverse-free form the minor
law consumes. -/
private theorem detSmulSolveGram_eq_smulAdjugate {m k : ℕ} (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hsharePos : 0 < shareValue) {pick : Fin k → Fin m}
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det) :
    (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ).det
        • ((solveMatrix (unitAtomRows D) pick)ᵀ * solveMatrix (unitAtomRows D) pick)
      = shareValue⁻¹ • (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ).adjugate := by
  have hdetNe : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mp (hunit.mul hunit)
  rw [solveGramEqSmulInvPickGram D huniform hsharePos pick, smul_smul, Matrix.inv_def,
    Ring.inverse_eq_inv', smul_smul]
  congr 1
  field_simp

/-- **The row split of the solve Gram**: `Y^T Y = 1 + X_o^T X_o`, the picked rows
contributing the identity. -/
private theorem solveGramRowSplit {frameSize selectionRank outCard : ℕ}
    (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    {pick : Fin selectionRank → Fin frameSize} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows frame pick).det)
    {outEnum : Fin outCard → Fin frameSize} (houtInj : Function.Injective outEnum)
    (himage : Finset.image outEnum Finset.univ = (Finset.image pick Finset.univ)ᶜ) :
    (solveMatrix frame pick)ᵀ * solveMatrix frame pick
      = 1 + ((solveMatrix frame pick).submatrix outEnum id)ᵀ
          * (solveMatrix frame pick).submatrix outEnum id := by
  ext leftCoord rightCoord
  rw [Matrix.mul_apply, Matrix.add_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  rw [← Finset.sum_add_sum_compl (Finset.image pick Finset.univ)
      (fun rowIndex => solveMatrix frame pick rowIndex leftCoord
        * solveMatrix frame pick rowIndex rightCoord),
    ← himage, Finset.sum_image (fun _ _ _ _ heq => houtInj heq),
    Finset.sum_image (fun _ _ _ _ heq => hinj heq)]
  congr 1
  calc ∑ slot, solveMatrix frame pick (pick slot) leftCoord
        * solveMatrix frame pick (pick slot) rightCoord
      = ∑ slot, (1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ) slot leftCoord
          * (1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ) slot rightCoord :=
        Finset.sum_congr rfl fun slot _ => by
          rw [solveMatrixEntryAtPick frame pick hunit slot leftCoord,
            solveMatrixEntryAtPick frame pick hunit slot rightCoord]
    _ = ((1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ)ᵀ
          * (1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ)) leftCoord rightCoord := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun slot _ => rfl
    _ = (1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ) leftCoord rightCoord := by
        rw [Matrix.transpose_one, Matrix.one_mul]

/-- An entry of the unit picked Gram is the direction correlation. -/
private theorem unitPickGramEntry {m k : ℕ} (D : WeightedDesign m k) (pick : Fin k → Fin m)
    (rowSlot colSlot : Fin k) :
    (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ)
        rowSlot colSlot
      = directionGram D (pick rowSlot) (pick colSlot) := by
  rw [Matrix.mul_apply, directionGram, dotProduct]
  exact Finset.sum_congr rfl fun coord _ => rfl

/-- The unit picked Gram is symmetric. -/
private theorem unitPickGramTranspose {m k : ℕ} (D : WeightedDesign m k) (pick : Fin k → Fin m) :
    (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ)ᵀ
      = selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The determinant of the unit picked Gram is a nonzero square. -/
private theorem detUnitPickGramPos {m k : ℕ} (D : WeightedDesign m k) {pick : Fin k → Fin m}
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det) :
    0 < (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ).det := by
  rw [Matrix.det_mul, Matrix.det_transpose, ← sq]
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hunit.ne_zero))

/-! ## 5. The `(7,3)` assembly: the new gate and the new floor -/

section SevenThreeAssembly

variable (D : WeightedDesign 7 3)

/-- **THE MINOR GATE at `(7,3)`-uniform.**  At every maximal-volume nonsingular
pick of the unit rows,

    `233 sigma(T#) - 128 <= 522 P(T#)`,

the `(sigma, P)` reading of `e2(X_o^T X_o) + 6 e1(X_o^T X_o) <= 72`.  The bound
upstream is the eighteen two-row exchange minors put through the real lever
`sq_twoByTwoMinor_le_entrySlack` and aggregated by Binet-Cauchy: each of the
twelve outside coordinates occurs in exactly six of the eighteen minors.  This
gate strictly dominates the landed trace gate `38 sigma - 24 <= 90 P` (the
difference certificate is `63 sigma + 56 >= 0`) and is the ONE new input of this file. -/
theorem minorGate_of_maximalVolume_sevenThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 7, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    233 * directionTripleSigma D (pick 0) (pick 1) (pick 2) - 128
      ≤ 522 * directionTripleProduct D (pick 0) (pick 1) (pick 2) := by
  classical
  have hsharePos : (0 : ℝ) < 3 / 7 := by norm_num
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hcardOut : ((Finset.image pick Finset.univ)ᶜ : Finset (Fin 7)).card = 4 := by
    rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp
  obtain ⟨outEnum, houtInj, himageOut⟩ :
      ∃ enumeration : Fin 4 → Fin 7, Function.Injective enumeration
        ∧ Finset.image enumeration Finset.univ = (Finset.image pick Finset.univ)ᶜ := by
    refine ⟨fun outIndex => ((Finset.image pick Finset.univ)ᶜ :
      Finset (Fin 7)).orderEmbOfFin hcardOut outIndex, ?_, ?_⟩
    · exact fun _ _ heq => (((Finset.image pick Finset.univ)ᶜ :
        Finset (Fin 7)).orderEmbOfFin hcardOut).injective heq
    · apply Finset.coe_injective
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact Finset.range_orderEmbOfFin _ hcardOut
  obtain ⟨outsideBlock, houtsideBlockDef⟩ :
      ∃ block : Matrix (Fin 4) (Fin 3) ℝ,
        block = (solveMatrix (unitAtomRows D) pick).submatrix outEnum id := ⟨_, rfl⟩
  have hlaw : (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ).det
        • ((1 : Matrix (Fin 3) (Fin 3) ℝ) + outsideBlockᵀ * outsideBlock)
      = (7 / 3 : ℝ) • (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ).adjugate := by
    have hsplit := solveGramRowSplit (unitAtomRows D) hinj hunit houtInj himageOut
    have hcoeff : ((3 : ℝ) / 7)⁻¹ = 7 / 3 := by norm_num
    rw [houtsideBlockDef, ← hcoeff, ← hsplit]
    exact detSmulSolveGram_eq_smulAdjugate D huniform hsharePos hunit
  have hentrySq : ∀ (rowIndex : Fin 4) (colIndex : Fin 3),
      outsideBlock rowIndex colIndex ^ 2 ≤ 1 := by
    intro rowIndex colIndex
    rw [houtsideBlockDef]
    simp only [Matrix.submatrix_apply, id_eq]
    exact (sq_le_one_iff_abs_le_one _).mpr
      (abs_solveMatrix_le_one_of_maximalVolume_row (unitAtomRows D) pick hinj hunit hmax _ _)
  have hminorSq : ∀ (rowFirst rowSecond : Fin 4) (colFirst colSecond : Fin 3),
      (outsideBlock rowFirst colFirst * outsideBlock rowSecond colSecond
        - outsideBlock rowFirst colSecond * outsideBlock rowSecond colFirst) ^ 2 ≤ 1 := by
    intro rowFirst rowSecond colFirst colSecond
    by_cases hcolEq : colFirst = colSecond
    · subst hcolEq
      have hvanishes : outsideBlock rowFirst colFirst * outsideBlock rowSecond colFirst
          - outsideBlock rowFirst colFirst * outsideBlock rowSecond colFirst = 0 := by ring
      rw [hvanishes]
      norm_num
    · rw [houtsideBlockDef]
      simp only [Matrix.submatrix_apply, id_eq]
      exact (sq_le_one_iff_abs_le_one _).mpr
        (abs_twoRowMinor_solveMatrix_le_one_of_maximalVolume (unitAtomRows D) pick hunit hmax
          (outEnum rowFirst) (outEnum rowSecond) hcolEq)
  have hbound : ((outsideBlockᵀ * outsideBlock) 0 0 * (outsideBlockᵀ * outsideBlock) 1 1
        - (outsideBlockᵀ * outsideBlock) 0 1 * (outsideBlockᵀ * outsideBlock) 1 0)
      + ((outsideBlockᵀ * outsideBlock) 0 0 * (outsideBlockᵀ * outsideBlock) 2 2
        - (outsideBlockᵀ * outsideBlock) 0 2 * (outsideBlockᵀ * outsideBlock) 2 0)
      + ((outsideBlockᵀ * outsideBlock) 1 1 * (outsideBlockᵀ * outsideBlock) 2 2
        - (outsideBlockᵀ * outsideBlock) 1 2 * (outsideBlockᵀ * outsideBlock) 2 1)
      + 6 * ((outsideBlockᵀ * outsideBlock) 0 0 + (outsideBlockᵀ * outsideBlock) 1 1
        + (outsideBlockᵀ * outsideBlock) 2 2) ≤ 72 := by
    have hfirst := columnPairMinor_le_entrySlack_fourRows outsideBlock hentrySq hminorSq 0 1
    have hsecond := columnPairMinor_le_entrySlack_fourRows outsideBlock hentrySq hminorSq 0 2
    have hthird := columnPairMinor_le_entrySlack_fourRows outsideBlock hentrySq hminorSq 1 2
    linarith [hfirst, hsecond, hthird]
  have hsymmG := unitPickGramTranspose D pick
  have hentry : ∀ rowSlot colSlot : Fin 3,
      (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ) rowSlot colSlot
        = directionGram D (pick rowSlot) (pick colSlot) :=
    fun rowSlot colSlot => unitPickGramEntry D pick rowSlot colSlot
  have hdiagZero : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 0 0 = 1 := by
    rw [hentry 0 0]; exact directionGram_self D (hlevPos (pick 0))
  have hdiagOne : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 1 1 = 1 := by
    rw [hentry 1 1]; exact directionGram_self D (hlevPos (pick 1))
  have hdiagTwo : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 2 2 = 1 := by
    rw [hentry 2 2]; exact directionGram_self D (hlevPos (pick 2))
  have hgate := minorGateFromAdjugateLaw_sevenThree hsymmG hdiagZero hdiagOne hdiagTwo
    (detUnitPickGramPos D hunit) hlaw hbound
  rw [hentry 0 1, hentry 0 2, hentry 1 2] at hgate
  rw [directionTripleSigma, directionTripleProduct]
  exact hgate

/-- **THE MINOR FLOOR, `(7,3)`.**  At every `(7,3)`-uniform design and every
maximal-volume nonsingular pick of the unit-atom rows,

    `lambda_min(Gamma[T#]) > 37/150 = 0.24666...`,

exactly `1/25` above the landed Cauchy-Binet floor `31/150` and within
`7.3 . 10^-4` of the minor relaxation's exact optimum `g** = 0.2473927...`. -/
theorem posDef_unitPickGram_sub_minorFloor_sevenThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 7, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ
      - (37 / 150 : ℝ) • 1).PosDef := by
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hminorGate := minorGate_of_maximalVolume_sevenThree D huniform hinj hunit hmax
  have hvolumeGate := volumeGate_of_maximalVolume_sevenThree D huniform hinj hunit hmax
  have hsymmG := unitPickGramTranspose D pick
  have hentry : ∀ rowSlot colSlot : Fin 3,
      (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ) rowSlot colSlot
        = directionGram D (pick rowSlot) (pick colSlot) :=
    fun rowSlot colSlot => unitPickGramEntry D pick rowSlot colSlot
  have hdiagZero : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 0 0 = 1 := by
    rw [hentry 0 0]; exact directionGram_self D (hlevPos (pick 0))
  have hdiagOne : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 1 1 = 1 := by
    rw [hentry 1 1]; exact directionGram_self D (hlevPos (pick 1))
  have hdiagTwo : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 2 2 = 1 := by
    rw [hentry 2 2]; exact directionGram_self D (hlevPos (pick 2))
  have hentryRange : (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 0 1 ^ 2
      + (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 0 2 ^ 2
      + (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 1 2 ^ 2 ≤ 3 := by
    rw [hentry 0 1, hentry 0 2, hentry 1 2]
    have hboundOne := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 1))
    have hboundTwo := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 2))
    have hboundThree := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 1) (pick 2))
    linarith [hboundOne, hboundTwo, hboundThree]
  refine posDef_sub_minorFloor_of_exchangeGates_sevenThree hsymmG hdiagZero hdiagOne hdiagTwo
    (detUnitPickGramPos D hunit) hentryRange ?_ ?_
  · rw [hentry 0 1, hentry 0 2, hentry 1 2]
    rw [directionTripleSigma, directionTripleProduct] at hminorGate
    exact hminorGate
  · rw [hentry 0 1, hentry 0 2, hentry 1 2]
    rw [directionTripleSigma, directionTripleProduct] at hvolumeGate
    exact hvolumeGate

/-- The minor floor read on the direction Gram matrix block. -/
theorem posDef_directionGramMatrix_submatrix_sub_minorFloor_sevenThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 7, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    ((directionGramMatrix D).submatrix pick pick - (37 / 150 : ℝ) • 1).PosDef := by
  rw [← unitPickGram_eq_directionGramMatrix_submatrix]
  exact posDef_unitPickGram_sub_minorFloor_sevenThree D huniform hinj hunit hmax

/-- **The minor floor with the pick supplied**: every `(7,3)`-uniform design has
a maximal-volume pick, and at it the unit Gram clears `37/150`.  The march
`1/5 < 31/150 < 37/150 <= g** < 1/4 < 1/3` in one existence statement. -/
theorem exists_pick_posDef_unitPickGram_sub_minorFloor_sevenThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    ∃ pick : Fin 3 → Fin 7, Function.Injective pick ∧
      (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ
        - (37 / 150 : ℝ) • 1).PosDef := by
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  obtain ⟨pick, hinj, hdet, hmax⟩ := exists_maximalVolume_pick_unitAtomRows D hlevPos
  exact ⟨pick, hinj, posDef_unitPickGram_sub_minorFloor_sevenThree D huniform hinj
    (isUnit_iff_ne_zero.mpr hdet) hmax⟩

end SevenThreeAssembly

/-! ## 6. The `(6,3)` calibration twin -/

section SixThreeAssembly

variable (D : WeightedDesign 6 3)

/-- **THE MINOR GATE at `(6,3)`-uniform**: `41 sigma - 21 <= 90 P` at every
maximal-volume nonsingular pick, from `e2(X_o^T X_o) + 4 e1(X_o^T X_o) <= 36`
(nine two-row minors over three outside rows, each of the nine coordinates in
exactly four of them). -/
theorem minorGate_of_maximalVolume_sixThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 6, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    41 * directionTripleSigma D (pick 0) (pick 1) (pick 2) - 21
      ≤ 90 * directionTripleProduct D (pick 0) (pick 1) (pick 2) := by
  classical
  have hsharePos : (0 : ℝ) < 1 / 2 := by norm_num
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hcardOut : ((Finset.image pick Finset.univ)ᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp
  obtain ⟨outEnum, houtInj, himageOut⟩ :
      ∃ enumeration : Fin 3 → Fin 6, Function.Injective enumeration
        ∧ Finset.image enumeration Finset.univ = (Finset.image pick Finset.univ)ᶜ := by
    refine ⟨fun outIndex => ((Finset.image pick Finset.univ)ᶜ :
      Finset (Fin 6)).orderEmbOfFin hcardOut outIndex, ?_, ?_⟩
    · exact fun _ _ heq => (((Finset.image pick Finset.univ)ᶜ :
        Finset (Fin 6)).orderEmbOfFin hcardOut).injective heq
    · apply Finset.coe_injective
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact Finset.range_orderEmbOfFin _ hcardOut
  obtain ⟨outsideBlock, houtsideBlockDef⟩ :
      ∃ block : Matrix (Fin 3) (Fin 3) ℝ,
        block = (solveMatrix (unitAtomRows D) pick).submatrix outEnum id := ⟨_, rfl⟩
  have hlaw : (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ).det
        • ((1 : Matrix (Fin 3) (Fin 3) ℝ) + outsideBlockᵀ * outsideBlock)
      = (2 : ℝ) • (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ).adjugate := by
    have hsplit := solveGramRowSplit (unitAtomRows D) hinj hunit houtInj himageOut
    have hcoeff : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
    rw [houtsideBlockDef, ← hcoeff, ← hsplit]
    exact detSmulSolveGram_eq_smulAdjugate D huniform hsharePos hunit
  have hentrySq : ∀ (rowIndex : Fin 3) (colIndex : Fin 3),
      outsideBlock rowIndex colIndex ^ 2 ≤ 1 := by
    intro rowIndex colIndex
    rw [houtsideBlockDef]
    simp only [Matrix.submatrix_apply, id_eq]
    exact (sq_le_one_iff_abs_le_one _).mpr
      (abs_solveMatrix_le_one_of_maximalVolume_row (unitAtomRows D) pick hinj hunit hmax _ _)
  have hminorSq : ∀ (rowFirst rowSecond : Fin 3) (colFirst colSecond : Fin 3),
      (outsideBlock rowFirst colFirst * outsideBlock rowSecond colSecond
        - outsideBlock rowFirst colSecond * outsideBlock rowSecond colFirst) ^ 2 ≤ 1 := by
    intro rowFirst rowSecond colFirst colSecond
    by_cases hcolEq : colFirst = colSecond
    · subst hcolEq
      have hvanishes : outsideBlock rowFirst colFirst * outsideBlock rowSecond colFirst
          - outsideBlock rowFirst colFirst * outsideBlock rowSecond colFirst = 0 := by ring
      rw [hvanishes]
      norm_num
    · rw [houtsideBlockDef]
      simp only [Matrix.submatrix_apply, id_eq]
      exact (sq_le_one_iff_abs_le_one _).mpr
        (abs_twoRowMinor_solveMatrix_le_one_of_maximalVolume (unitAtomRows D) pick hunit hmax
          (outEnum rowFirst) (outEnum rowSecond) hcolEq)
  have hbound : ((outsideBlockᵀ * outsideBlock) 0 0 * (outsideBlockᵀ * outsideBlock) 1 1
        - (outsideBlockᵀ * outsideBlock) 0 1 * (outsideBlockᵀ * outsideBlock) 1 0)
      + ((outsideBlockᵀ * outsideBlock) 0 0 * (outsideBlockᵀ * outsideBlock) 2 2
        - (outsideBlockᵀ * outsideBlock) 0 2 * (outsideBlockᵀ * outsideBlock) 2 0)
      + ((outsideBlockᵀ * outsideBlock) 1 1 * (outsideBlockᵀ * outsideBlock) 2 2
        - (outsideBlockᵀ * outsideBlock) 1 2 * (outsideBlockᵀ * outsideBlock) 2 1)
      + 4 * ((outsideBlockᵀ * outsideBlock) 0 0 + (outsideBlockᵀ * outsideBlock) 1 1
        + (outsideBlockᵀ * outsideBlock) 2 2) ≤ 36 := by
    have hfirst := columnPairMinor_le_entrySlack_threeRows outsideBlock hentrySq hminorSq 0 1
    have hsecond := columnPairMinor_le_entrySlack_threeRows outsideBlock hentrySq hminorSq 0 2
    have hthird := columnPairMinor_le_entrySlack_threeRows outsideBlock hentrySq hminorSq 1 2
    linarith [hfirst, hsecond, hthird]
  have hsymmG := unitPickGramTranspose D pick
  have hentry : ∀ rowSlot colSlot : Fin 3,
      (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ) rowSlot colSlot
        = directionGram D (pick rowSlot) (pick colSlot) :=
    fun rowSlot colSlot => unitPickGramEntry D pick rowSlot colSlot
  have hdiagZero : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 0 0 = 1 := by
    rw [hentry 0 0]; exact directionGram_self D (hlevPos (pick 0))
  have hdiagOne : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 1 1 = 1 := by
    rw [hentry 1 1]; exact directionGram_self D (hlevPos (pick 1))
  have hdiagTwo : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 2 2 = 1 := by
    rw [hentry 2 2]; exact directionGram_self D (hlevPos (pick 2))
  have hgate := minorGateFromAdjugateLaw_sixThree hsymmG hdiagZero hdiagOne hdiagTwo
    (detUnitPickGramPos D hunit) hlaw hbound
  rw [hentry 0 1, hentry 0 2, hentry 1 2] at hgate
  rw [directionTripleSigma, directionTripleProduct]
  exact hgate

/-- **THE MINOR FLOOR, `(6,3)`** — the calibration twin on the stratum where U6
is already a theorem: at every `(6,3)`-uniform design and maximal-volume
nonsingular pick, `lambda_min(Gamma[T#]) > 7/25 = 0.28`, against the landed
Cauchy-Binet floor `9/40 = 0.225`.  The exact relaxation optimum here is the
algebraic number `1 - sqrt 861 / 41 = 0.2843225...`. -/
theorem posDef_unitPickGram_sub_minorFloor_sixThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 6, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ
      - (7 / 25 : ℝ) • 1).PosDef := by
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hminorGate := minorGate_of_maximalVolume_sixThree D huniform hinj hunit hmax
  have hproductGate := nonneg_directionTripleProduct_of_maximalVolume_sixThree D huniform hinj
    hunit hmax
  have hsymmG := unitPickGramTranspose D pick
  have hentry : ∀ rowSlot colSlot : Fin 3,
      (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ) rowSlot colSlot
        = directionGram D (pick rowSlot) (pick colSlot) :=
    fun rowSlot colSlot => unitPickGramEntry D pick rowSlot colSlot
  have hdiagZero : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 0 0 = 1 := by
    rw [hentry 0 0]; exact directionGram_self D (hlevPos (pick 0))
  have hdiagOne : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 1 1 = 1 := by
    rw [hentry 1 1]; exact directionGram_self D (hlevPos (pick 1))
  have hdiagTwo : (selectedFrameRows (unitAtomRows D) pick
      * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 2 2 = 1 := by
    rw [hentry 2 2]; exact directionGram_self D (hlevPos (pick 2))
  have hentryRange : (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 0 1 ^ 2
      + (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 0 2 ^ 2
      + (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ) 1 2 ^ 2 ≤ 3 := by
    rw [hentry 0 1, hentry 0 2, hentry 1 2]
    have hboundOne := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 1))
    have hboundTwo := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 2))
    have hboundThree := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 1) (pick 2))
    linarith [hboundOne, hboundTwo, hboundThree]
  refine posDef_sub_minorFloor_of_exchangeGates_sixThree hsymmG hdiagZero hdiagOne hdiagTwo
    (detUnitPickGramPos D hunit) hentryRange ?_ ?_
  · rw [hentry 0 1, hentry 0 2, hentry 1 2]
    rw [directionTripleSigma, directionTripleProduct] at hminorGate
    exact hminorGate
  · rw [hentry 0 1, hentry 0 2, hentry 1 2]
    rw [directionTripleProduct] at hproductGate
    exact hproductGate

/-- The `(6,3)` minor floor with the pick supplied. -/
theorem exists_pick_posDef_unitPickGram_sub_minorFloor_sixThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ
        - (7 / 25 : ℝ) • 1).PosDef := by
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  obtain ⟨pick, hinj, hdet, hmax⟩ := exists_maximalVolume_pick_unitAtomRows D hlevPos
  exact ⟨pick, hinj, posDef_unitPickGram_sub_minorFloor_sixThree D huniform hinj
    (isUnit_iff_ne_zero.mpr hdet) hmax⟩

end SixThreeAssembly

/-- **The `(6,3)` minor floor is non-vacuous**: the icosahedral design lies on
the uniform-share stratum, so it carries a maximal-volume pick whose unit Gram
clears `7/25`. -/
theorem exists_pick_posDef_sub_minorFloor_icosaDesign :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      (selectedFrameRows (unitAtomRows icosaDesign) pick
          * (selectedFrameRows (unitAtomRows icosaDesign) pick)ᵀ
        - (7 / 25 : ℝ) • 1).PosDef :=
  exists_pick_posDef_unitPickGram_sub_minorFloor_sixThree icosaDesign atomShare_icosaDesign

/-! ## 7. The fourth barrier: the two-gate certificate cannot reach `1/4` -/

/-- **The gate corner is exact.**  At `(sigma, P) = (92/201, -74/1809)` BOTH the
minor gate and the volume gate hold with EQUALITY.  There `Delta = 833/1809` and
the outside spectrum data is `(e1, e2, e3) = (168/17, 216/17, 4)`, satisfying
isotropy `12 + 5 e1 - 2 e2 - 9 e3 = 0` exactly. -/
theorem exchangeGates_corner_tight_sevenThree :
    233 * ((92 : ℝ) / 201) - 128 = 522 * (-(74 / 1809))
      ∧ 36 * ((92 : ℝ) / 201) - 22 = 135 * (-(74 / 1809)) := by
  constructor <;> norm_num

/-- **The corner determinant IS the new floor cubic.**  At the gate corner the
shifted determinant of a correlation matrix with those `(sigma, P)` equals
`-C**(t)/1809`.  So the two-gate certificate can license a floor `t` only when
`C**(t) <= 0`, i.e. only up to the smallest root `g** = 0.2473927...`.  That is
the exact ceiling of the minor-refined exchange relaxation. -/
theorem shiftedDet_at_gateCorner_eq_minorFloorCubic_sevenThree (floorValue : ℝ) :
    (1 - floorValue) ^ 3 - (1 - floorValue) * (92 / 201) + 2 * (-(74 / 1809))
      = -(1809 * floorValue ^ 3 - 5427 * floorValue ^ 2 + 4599 * floorValue - 833) / 1809 := by
  ring

/-- **THE FOURTH BARRIER, with an exact rational witness.**  There is a symmetric
unit-diagonal correlation matrix -- off-diagonals `(-11/20, -3/10, -1/4)`, so
`sigma = 91/200` and `P = -33/800` -- which satisfies BOTH exchange gates and is
positive definite (`det = 37/80`), yet whose shift at `1/4` has determinant
`-3/1600 < 0` and hence is NOT positive semidefinite.  Therefore the two-gate
certificate of this file CANNOT deliver `lambda_min >= 1/4`, and a fortiori not
conjecture M7's `1/3`.  Any route past `1/4` must strengthen at least one of the
two AGGREGATED gates.

This is a barrier on the CERTIFICATE, not on the truth, and on the AGGREGATES
only.  The witness is a bare correlation matrix: it is NOT shown to arise from a
`(7,3)`-uniform design at a maximal-volume pick, and NOT shown to arise from any
`4x3` outside block obeying the INDIVIDUAL entry, two-row and three-row bounds.
So it does not bar a sharper aggregation of the same exchange data — only these
two gates.  What it refutes is the hope that this gate pair alone reaches `1/3`. -/
theorem exists_correlation_satisfying_gates_not_posDef_at_quarter_sevenThree :
    ∃ gram : Matrix (Fin 3) (Fin 3) ℝ, gramᵀ = gram
      ∧ gram 0 0 = 1 ∧ gram 1 1 = 1 ∧ gram 2 2 = 1
      ∧ 0 < gram.det
      ∧ 233 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 128
          ≤ 522 * (gram 0 1 * gram 0 2 * gram 1 2)
      ∧ 36 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 22
          ≤ 135 * (gram 0 1 * gram 0 2 * gram 1 2)
      ∧ ¬ (gram - (1 / 4 : ℝ) • 1).PosSemidef := by
  have hsymmetric : (!![(1 : ℝ), -(11 / 20), -(3 / 10);
        -(11 / 20), 1, -(1 / 4);
        -(3 / 10), -(1 / 4), 1])ᵀ
      = !![(1 : ℝ), -(11 / 20), -(3 / 10);
        -(11 / 20), 1, -(1 / 4);
        -(3 / 10), -(1 / 4), 1] := by
    apply Matrix.ext
    intro rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp
  have hdiagZero : (!![(1 : ℝ), -(11 / 20), -(3 / 10);
      -(11 / 20), 1, -(1 / 4);
      -(3 / 10), -(1 / 4), 1]) 0 0 = 1 := by simp
  have hdiagOne : (!![(1 : ℝ), -(11 / 20), -(3 / 10);
      -(11 / 20), 1, -(1 / 4);
      -(3 / 10), -(1 / 4), 1]) 1 1 = 1 := by simp
  have hdiagTwo : (!![(1 : ℝ), -(11 / 20), -(3 / 10);
      -(11 / 20), 1, -(1 / 4);
      -(3 / 10), -(1 / 4), 1]) 2 2 = 1 := by simp
  have hzeroOne : (!![(1 : ℝ), -(11 / 20), -(3 / 10);
      -(11 / 20), 1, -(1 / 4);
      -(3 / 10), -(1 / 4), 1]) 0 1 = -(11 / 20) := by simp
  have hzeroTwo : (!![(1 : ℝ), -(11 / 20), -(3 / 10);
      -(11 / 20), 1, -(1 / 4);
      -(3 / 10), -(1 / 4), 1]) 0 2 = -(3 / 10) := by simp
  have honeTwo : (!![(1 : ℝ), -(11 / 20), -(3 / 10);
      -(11 / 20), 1, -(1 / 4);
      -(3 / 10), -(1 / 4), 1]) 1 2 = -(1 / 4) := by simp
  refine ⟨!![(1 : ℝ), -(11 / 20), -(3 / 10);
            -(11 / 20), 1, -(1 / 4);
            -(3 / 10), -(1 / 4), 1], hsymmetric, hdiagZero, hdiagOne, hdiagTwo, ?_, ?_, ?_, ?_⟩
  · have hzeroShift := detShifted_of_symmetric_unitDiagonal hsymmetric hdiagZero hdiagOne
      hdiagTwo 0
    rw [zero_smul, sub_zero] at hzeroShift
    rw [hzeroShift, hzeroOne, hzeroTwo, honeTwo]
    norm_num
  · rw [hzeroOne, hzeroTwo, honeTwo]
    norm_num
  · rw [hzeroOne, hzeroTwo, honeTwo]
    norm_num
  · intro hposSemidef
    have hdetNonneg := hposSemidef.det_nonneg
    rw [detShifted_of_symmetric_unitDiagonal hsymmetric hdiagZero hdiagOne hdiagTwo,
      hzeroOne, hzeroTwo, honeTwo] at hdetNonneg
    norm_num at hdetNonneg

end Gtz

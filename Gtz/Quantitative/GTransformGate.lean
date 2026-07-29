/-
# The `g`-transform gate: the pen's V4, and the four-set covering gate it feeds

The pen's V4 bounds the Gram determinant of a triple by a cubic in the triple's
SPECTRAL FLOOR — the least level `theta` at which `theta . 1 + M[T]` is positive
semidefinite, written `theta-star` by the pen:

    det Gamma[T]  =  det(1 + M[T])  <=  (1 + theta/2)^2 (1 - theta)  =:  g(theta),

with `g` strictly decreasing on `[0, 1]`.  Run backwards this is a COVERING GATE:
a lower bound on some triple's determinant is an upper bound on that triple's
spectral floor, and a triple whose spectral floor sits below every one of its
three weight capacities dominates.

## The route taken here is eigenvalue-free

The pen justifies the bound by sorting the block's eigenvalues `a1 >= a2 >= a3`,
putting `theta = -a3 = a1 + a2` and maximising `(1+a1)(1+a2)` at `a1 = a2 =
theta/2`.  This file never sorts an eigenvalue and never mentions one.  What the
argument really consumes is the single scalar inequality

    squareSum  >=  (3/4) * theta^2      (`threeQuarters_mul_sq_le_squareSum_of_shiftedDet_eq_zero`)

whenever `theta` is a nonnegative root of the shifted determinant `theta^3 -
theta * squareSum + 2 * tripleProduct`, and that follows from AM-GM
(`twentySeven_mul_sq_tripleProduct_le_cube_squareSum`) by one exact polynomial
identity.  So the whole of V4 lands with `nlinarith` and `ring` over the two
scalars `squareSum` and `tripleProduct`, on the shipped substrate of
`Gtz.Quantitative.TripleCubicCriterion`.

The pen's ordering statement `a2 <= min(a1, 1-a1) <= 1/2` is landed too
(`middle_le_min_of_traceZero_of_capped`), as the scalar lemma it is; it is
recorded for the record, NOT used, and the docstring there says which inequality
replaces it.

## What is proved

* **The transform.**  `gTransform theta = (1 + theta/2)^2 (1 - theta)`, with the
  cubic closed form `gTransform theta = 1 - (theta^3 + 3 theta^2)/4`
  (`gTransform_eq_one_sub_quarter_mul_cubicSum`).  The cubic form is the useful
  one: antitonicity is one `nlinarith` with no derivative
  (`gTransform_lt_gTransform_of_lt`), and the gate threshold becomes an exact
  linear condition (below).

* **The exact threshold.**  `gTransform (sqrt 3 - 1) = 1/2`
  (`gTransform_sqrtThree_sub_one`) — the campaign's recorded decimal "about 0.73"
  is the algebraic number `sqrt 3 - 1`, exactly, because
  `((1 + sqrt 3)/2)^2 (2 - sqrt 3) = ((2 + sqrt 3)/2)(2 - sqrt 3) = 1/2`.

* **The gate, quantitative and monotone in the complementary pair weight.**
  `gTransform_le_iff_cube_add_three_mul_sq_le` :

      gTransform theta <= (1 - pairWeight)/2   <->   2 + 2 pairWeight <= theta^3 + 3 theta^2,

  an IFF with no slack, affine in `pairWeight`.  Shifted by one this is the
  depressed cubic `(1 + theta)^3 - 3 (1 + theta) = 2 pairWeight`
  (`cubicSum_eq_depressedCubic_shifted`), whose relevant root runs from `sqrt 3`
  at `pairWeight = 0` to `2` at `pairWeight = 1`.  An explicit RATIONAL affine
  threshold that clears it for every `pairWeight` in `[0,1]` is `11/15 +
  pairWeight/3` (`gTransform_affineThreshold_le`), against the sharp
  `sqrt 3 - 1 = 0.7320508...` at `pairWeight = 0`; the loss is `0.0013`.

* **V4(2), sharp.**  `det_one_add_le_gTransform_of_shiftedDet_eq_zero` : at a
  nonnegative root `theta <= 1` of the shifted determinant,
  `det(1 + N) <= gTransform theta`.

* **V4(2), run backwards — THE GATE.**
  `posSemidef_smul_one_add_hollowMatrixThree_of_gTransform_le_det` : under the
  norm cap `squareSum + 2 |tripleProduct| <= 1` and `0 <= theta <= 1`,

      gTransform theta <= det(1 + N)   ==>   (theta . 1 + N) positive semidefinite.

  Its contrapositive `det_one_add_lt_gTransform_of_not_posSemidef` is the pen's
  V4(2) with no root hypothesis at all, and STRICT.

* **The load-bearing floor lemma, at every dimension.**
  `posSemidef_diagonal_add_of_floor` : a flat shift that works at the floor works
  at every capacity vector above it.  This is the pen's "min over T of tau_c >=
  theta-star_T implies domination", and it is `Matrix.PosSemidef.diagonal` plus
  `Matrix.PosSemidef.add` — no eigenvalue shift, no monotonicity of a
  determinant, and no pairwise clauses.  Its upward-closure twin
  `posSemidef_diagonal_add_of_le` is the convexity-free half of "the criterion
  cell is upward closed".

* **THE FOUR-SET IDENTITY.**
  `IsHollowInvolution.sum_det_one_add_submatrix_fourSet_eq` : on a hollow
  symmetric involution of `Fin 6`, the four triple determinants of
  any four-set sum to `2 (1 - w)` where `w` is the squared entry of the
  complementary PAIR.  Both halves come from the shipped block-relation trace
  laws at a `4-2` split — the quadratic law gives the six-edge square sum
  `1 + w` and the cubic law gives the four-product sum `0` — so neither the row
  law nor Jacobi's complementary-minor identity is needed, and no spectrum is
  computed.

* **The four-set gate and the covering corollary.**
  `IsHollowInvolution.exists_triple_det_ge_of_fourSet` pigeonholes the identity:
  some triple of the four-set has `det(1 + M[T]) >= (1 - w)/2`.
  `IsHollowInvolution.exists_pick_posSemidef_diagonal_add_of_capacity_floor` then
  runs the gate and the floor lemma: if every atom outside the complementary
  pair has capacity at least a `theta` clearing the cubic threshold, some triple
  avoiding that pair is positive semidefinite at the ACTUAL capacities.  That is
  the pen's "tau_(4) >= g-inverse((1 - w_56)/2) implies covered", with
  `g-inverse` replaced by the exact cubic condition and no inverse function
  defined anywhere.

## The band this gate actually covers, stated honestly

`gTransform_le_half_iff_sqrtThree_sub_one_le` makes the threshold EXACT at
`pairWeight = 0`: for a nonnegative floor, `g(theta) <= 1/2` iff `theta >=
sqrt 3 - 1`.  Since the four-set gate's determinant floor `(1 - w)/2` never
exceeds `1/2`, the gate NEVER fires below `sqrt 3 - 1 = 0.7320508...`, and in
particular never at the equal-share capacity `2/3`, where `g(2/3) = 16/27 > 1/2`
(`half_lt_gTransform_twoThirds`).  This is a strict TOP-BAND gate.  The pen's V2
order statistics only give `tau_(4) > 1/3`, so the band `(1/3, sqrt 3 - 1)` is
left entirely to other mechanisms — the shipped `9/25` margin at the centre, the
merge-boundary orthogonal pair at the collar, and the cheap-atom gate at the
corners.  Reading `tau_(4)`: the pen's statement is this file's corollary with the
complementary pair chosen to be the two SMALLEST capacities, so that "every atom
outside the pair has capacity at least theta" is exactly `tau_(4) >= theta`.

## What is NOT proved

Nothing here identifies `theta-star` as `-lambda_min` of the block, and nothing
asserts that a spectral floor exists.  It does not have to: the gate quantifies
over `theta`, and the pen's `det <= g(theta-star)` is recovered in the strict
contrapositive form `not positive semidefinite at theta ==> det < g(theta)`,
which is what a covering argument consumes.  Nor is the four-set identity
transported to a weighted design: the transport is the `tau`-coordinate
congruence `Gram[T] - diag(2 t_c)`, which belongs to the V1 layer, and the shape
`Matrix.diagonal capacity + block` used throughout here is exactly what that
congruence produces.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Quantitative.EqualShareSixThreeMargin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## 0. The two hollow constructors are literally the same matrix

`Gtz.hollowMatrixThree` (the involution layer) and `Gtz.hollowSymmetricThree`
(the criterion layer) are character-for-character the same definition in two
files, and their lemma sets are disjoint.  This is the missing bridge; every
theorem below is stated on the involution-side constructor and reaches the
criterion-side lemmas through it. -/

/-- The involution layer's hollow `3 x 3` IS the criterion layer's. -/
theorem hollowMatrixThree_eq_hollowSymmetricThree (edgeFirst edgeSecond edgeThird : ℝ) :
    hollowMatrixThree edgeFirst edgeSecond edgeThird
      = hollowSymmetricThree edgeFirst edgeSecond edgeThird := rfl

/-- **The Gram determinant of a triple in its two scalars.**  `det(1 + N) =
1 - squareSum + 2 tripleProduct`, the `level = 1` case of the shipped shifted
determinant. -/
theorem det_one_add_hollowMatrixThree (edgeFirst edgeSecond edgeThird : ℝ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) + hollowMatrixThree edgeFirst edgeSecond edgeThird).det
      = 1 - (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
        + 2 * (edgeFirst * edgeSecond * edgeThird) := by
  rw [show ((1 : Matrix (Fin 3) (Fin 3) ℝ) + hollowMatrixThree edgeFirst edgeSecond edgeThird)
      = (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird by
    rw [one_smul, hollowMatrixThree_eq_hollowSymmetricThree],
    det_smul_one_add_hollowSymmetricThree]
  ring

/-- The shifted determinant of a triple in its two scalars, at an arbitrary level. -/
theorem det_smul_one_add_hollowMatrixThree (level edgeFirst edgeSecond edgeThird : ℝ) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowMatrixThree edgeFirst edgeSecond edgeThird).det
      = level ^ 3 - level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
        + 2 * (edgeFirst * edgeSecond * edgeThird) := by
  rw [hollowMatrixThree_eq_hollowSymmetricThree, det_smul_one_add_hollowSymmetricThree]

/-! ## 1. The `g`-transform

`g(theta) = (1 + theta/2)^2 (1 - theta)` is the largest Gram determinant a hollow
symmetric `3 x 3` with spectral floor `theta` can carry: with `a1 + a2 = theta`
the product `(1 + a1)(1 + a2)` is maximal at `a1 = a2 = theta/2`, and the
remaining factor is `1 - theta`.  Everything below uses only the cubic closed
form. -/

/-- **THE `g`-TRANSFORM.**  `g(theta) = (1 + theta/2)^2 (1 - theta)`, the pen's V4
determinant cap at spectral floor `theta`. -/
noncomputable def gTransform (spectralFloor : ℝ) : ℝ :=
  (1 + spectralFloor / 2) ^ 2 * (1 - spectralFloor)

/-- **The cubic closed form**, which is what every proof below actually uses:
`g(theta) = 1 - (theta^3 + 3 theta^2)/4`.  Strictly better than the factored
form — antitonicity needs no derivative, and the gate threshold becomes affine. -/
theorem gTransform_eq_one_sub_quarter_mul_cubicSum (spectralFloor : ℝ) :
    gTransform spectralFloor = 1 - (spectralFloor ^ 3 + 3 * spectralFloor ^ 2) / 4 := by
  rw [gTransform]; ring

theorem gTransform_zero : gTransform 0 = 1 := by rw [gTransform]; norm_num

theorem gTransform_one : gTransform 1 = 0 := by rw [gTransform]; norm_num

/-- **`g` is strictly decreasing on the nonnegative reals.**  From the cubic form,
`g(low) - g(high) = (3/4)(high^2 - low^2) + (1/4)(high^3 - low^3) > 0`.  No
derivative, no `StrictAntiOn`, no mean value theorem. -/
theorem gTransform_lt_gTransform_of_lt {lowFloor highFloor : ℝ} (hnonneg : 0 ≤ lowFloor)
    (hlt : lowFloor < highFloor) : gTransform highFloor < gTransform lowFloor := by
  rw [gTransform_eq_one_sub_quarter_mul_cubicSum, gTransform_eq_one_sub_quarter_mul_cubicSum]
  nlinarith [sq_nonneg (highFloor - lowFloor), sq_nonneg (highFloor + lowFloor), hnonneg, hlt]

/-- `g` is antitone on the nonnegative reals. -/
theorem gTransform_le_gTransform_of_le {lowFloor highFloor : ℝ} (hnonneg : 0 ≤ lowFloor)
    (hle : lowFloor ≤ highFloor) : gTransform highFloor ≤ gTransform lowFloor := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq]
  · exact (gTransform_lt_gTransform_of_lt hnonneg hlt).le

/-- `g` is nonnegative up to the spectral floor `1`, where it vanishes. -/
theorem gTransform_nonneg_of_le_one {spectralFloor : ℝ} (hle : spectralFloor ≤ 1) :
    0 ≤ gTransform spectralFloor := by
  rw [gTransform]
  exact mul_nonneg (sq_nonneg _) (by linarith)

/-- **THE EXACT V4 THRESHOLD.**  `g(sqrt 3 - 1) = 1/2` on the nose:
`((1 + sqrt 3)/2)^2 (2 - sqrt 3) = ((2 + sqrt 3)/2)(2 - sqrt 3) = (4 - 3)/2`.
The campaign's recorded decimal "about 0.73" is this algebraic number. -/
theorem gTransform_sqrtThree_sub_one : gTransform (Real.sqrt 3 - 1) = 1 / 2 := by
  have hsquare : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [gTransform]
  nlinarith [hsquare, Real.sqrt_nonneg 3]

/-! ## 2. The gate threshold, quantitative and monotone in the pair weight

The four-set gate below produces a determinant floor `(1 - pairWeight)/2`.  Since
`g` is affine in the cubic `theta^3 + 3 theta^2`, clearing that floor is an exact
linear condition, with no inequality slack anywhere. -/

/-- **THE GATE THRESHOLD, AS AN IFF.**  `g(theta) <= (1 - pairWeight)/2` exactly
when `2 + 2 pairWeight <= theta^3 + 3 theta^2`.  Both sides are affine in
`pairWeight`, so the gate is monotone in the complementary pair weight with no
loss. -/
theorem gTransform_le_iff_cube_add_three_mul_sq_le (spectralFloor pairWeight : ℝ) :
    gTransform spectralFloor ≤ (1 - pairWeight) / 2
      ↔ 2 + 2 * pairWeight ≤ spectralFloor ^ 3 + 3 * spectralFloor ^ 2 := by
  rw [gTransform_eq_one_sub_quarter_mul_cubicSum]
  constructor <;> intro hbound <;> linarith

/-- **The threshold is a depressed cubic in `1 + theta`.**  `theta^3 + 3 theta^2 =
(1 + theta)^3 - 3 (1 + theta) + 2`, so `g(theta) <= (1 - w)/2` reads
`(1 + theta)^3 - 3 (1 + theta) >= 2 w`.  The exact threshold therefore runs from
`1 + theta = sqrt 3` at `w = 0` to `1 + theta = 2` at `w = 1`. -/
theorem cubicSum_eq_depressedCubic_shifted (spectralFloor : ℝ) :
    spectralFloor ^ 3 + 3 * spectralFloor ^ 2
      = (1 + spectralFloor) ^ 3 - 3 * (1 + spectralFloor) + 2 := by ring

/-- The `pairWeight = 1` end of the threshold: at a saturated complementary pair
the gate asks only for `theta = 1`, and it is exactly tight there. -/
theorem gTransform_one_le_of_pairWeight_le_one {pairWeight : ℝ} (hle : pairWeight ≤ 1) :
    gTransform 1 ≤ (1 - pairWeight) / 2 := by
  rw [gTransform_one]; linarith

/-- **AN EXPLICIT RATIONAL AFFINE THRESHOLD.**  For every `pairWeight` in `[0,1]`
the rational affine level `11/15 + pairWeight/3` clears the gate:
`g(11/15 + pairWeight/3) <= (1 - pairWeight)/2`.  At `pairWeight = 0` it costs
`11/15 - (sqrt 3 - 1) = 0.00128...` against the sharp algebraic threshold, and at
`pairWeight = 1` it overshoots `1` (where the gate is free anyway).  This is the
statement a covering argument instantiates: no root-finding, no inverse
function, one rational number per pair weight. -/
theorem gTransform_affineThreshold_le {pairWeight : ℝ} (hnonneg : 0 ≤ pairWeight) :
    gTransform (11 / 15 + pairWeight / 3) ≤ (1 - pairWeight) / 2 := by
  rw [gTransform_le_iff_cube_add_three_mul_sq_le]
  nlinarith [sq_nonneg pairWeight, pow_nonneg hnonneg 3, hnonneg,
    mul_nonneg hnonneg hnonneg]

/-- **THE THRESHOLD AT A ZERO PAIR WEIGHT IS EXACTLY `sqrt 3 - 1`.**  For a
nonnegative floor, `g(theta) <= 1/2` holds precisely when `theta >= sqrt 3 - 1`.
So the algebraic constant is not merely sufficient — it is the covering threshold
of the four-set gate at `pairWeight = 0`, and no rational bound can improve on
it. -/
theorem gTransform_le_half_iff_sqrtThree_sub_one_le {spectralFloor : ℝ}
    (hnonneg : 0 ≤ spectralFloor) :
    gTransform spectralFloor ≤ 1 / 2 ↔ Real.sqrt 3 - 1 ≤ spectralFloor := by
  have hroot : (0 : ℝ) ≤ Real.sqrt 3 - 1 := by
    have hmono : Real.sqrt 1 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
    rw [Real.sqrt_one] at hmono
    linarith
  constructor
  · intro hbound
    by_contra hcontra
    rw [not_le] at hcontra
    have hstrict := gTransform_lt_gTransform_of_lt hnonneg hcontra
    rw [gTransform_sqrtThree_sub_one] at hstrict
    linarith
  · intro hbound
    have hanti := gTransform_le_gTransform_of_le hroot hbound
    rw [gTransform_sqrtThree_sub_one] at hanti
    linarith

/-- **THE GATE IS STRICTLY A TOP-BAND GATE.**  `g(2/3) = 16/27 > 1/2`, so the
four-set gate — whose determinant floor never exceeds `1/2` — cannot fire at the
equal-share capacity `2/3`.  The band it covers starts at `sqrt 3 - 1 =
0.7320508...`, strictly above `2/3`; the centre of the weight polytope is the
shipped `9/25` margin's business, not this file's. -/
theorem half_lt_gTransform_twoThirds : (1 : ℝ) / 2 < gTransform (2 / 3) := by
  rw [gTransform]; norm_num

/-- **THE GATE IS NON-VACUOUS AT THE ICOSAHEDRAL PAIR WEIGHT.**  `Gtz.icosaDesign`
is six lines at squared cosine `1/5`, so every pair weight of its correlation
involution is `1/5`; at that pair weight the level `4/5` clears the gate,
`g(4/5) = 49/125 <= 2/5`.  So a four-set of the icosahedron whose four live
capacities all reach `4/5` is covered — and `tau = (4/5, 4/5, 4/5, 4/5, 2/5, 2/5)`
is an admissible weight vector, summing to four with every coordinate below
one. -/
theorem gTransform_fourFifths_le_at_pairWeight_fifth :
    gTransform (4 / 5) ≤ (1 - 1 / 5) / 2 := by
  rw [gTransform]; norm_num

/-- The affine threshold stays inside `[0, 1]` for every pair weight up to `4/5`,
which is what the gate's `theta <= 1` hypothesis needs.  Above `4/5` the caller
should instead take `theta = 1`, where `gTransform_one_le_of_pairWeight_le_one`
clears the gate outright. -/
theorem affineThreshold_mem_unitInterval {pairWeight : ℝ} (hnonneg : 0 ≤ pairWeight)
    (hcapped : pairWeight ≤ 4 / 5) :
    0 ≤ 11 / 15 + pairWeight / 3 ∧ 11 / 15 + pairWeight / 3 ≤ 1 :=
  ⟨by linarith [hnonneg], by linarith [hcapped]⟩

/-! ## 3. The two scalar cores

AM-GM on the three squared edges, and the inequality it produces at a root of the
shifted determinant.  The second is the whole content of the pen's eigenvalue
sorting. -/

/-- **AM-GM on the squared edges.**  `27 P^2 <= squareSum^3`, i.e. `27 x y z <=
(x + y + z)^3` at `x = a^2` and so on.  The certificate is
`(x+y+z)^3 - 27xyz = (1/2)(x+y+z)[(x-y)^2+(y-z)^2+(z-x)^2] + 3[x(y-z)^2 +
y(z-x)^2 + z(x-y)^2]`. -/
theorem twentySeven_mul_sq_tripleProduct_le_cube_squareSum
    (edgeFirst edgeSecond edgeThird : ℝ) :
    27 * (edgeFirst * edgeSecond * edgeThird) ^ 2
      ≤ (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2) ^ 3 := by
  nlinarith [mul_nonneg (sq_nonneg edgeFirst) (sq_nonneg (edgeSecond ^ 2 - edgeThird ^ 2)),
    mul_nonneg (sq_nonneg edgeSecond) (sq_nonneg (edgeThird ^ 2 - edgeFirst ^ 2)),
    mul_nonneg (sq_nonneg edgeThird) (sq_nonneg (edgeFirst ^ 2 - edgeSecond ^ 2)),
    mul_nonneg (by positivity : (0 : ℝ) ≤ edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      (sq_nonneg (edgeFirst ^ 2 - edgeSecond ^ 2)),
    mul_nonneg (by positivity : (0 : ℝ) ≤ edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      (sq_nonneg (edgeSecond ^ 2 - edgeThird ^ 2)),
    mul_nonneg (by positivity : (0 : ℝ) ≤ edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      (sq_nonneg (edgeThird ^ 2 - edgeFirst ^ 2))]

/-- **THE POSITIVITY CERTIFICATE BEHIND BOTH BRANCHES.**  With
`gap := (3/4) theta^2 - squareSum`,

    27 theta^2 (theta^2 - squareSum)^2 - 4 squareSum^3
      = (81/4) theta^4 gap + 18 theta^2 gap^2 + 4 gap^3,

an exact polynomial identity.  So a nonnegative `gap` makes the left side
nonnegative and a strictly positive `gap` with `theta > 0` makes it strictly
positive.  Everything the `g`-transform needs is one of those two readings. -/
theorem cappedCubicResidual_eq_gapCertificate (spectralFloor squareSum : ℝ) :
    27 * spectralFloor ^ 2 * (spectralFloor ^ 2 - squareSum) ^ 2 - 4 * squareSum ^ 3
      = 81 / 4 * spectralFloor ^ 4 * (3 / 4 * spectralFloor ^ 2 - squareSum)
        + 18 * spectralFloor ^ 2 * (3 / 4 * spectralFloor ^ 2 - squareSum) ^ 2
        + 4 * (3 / 4 * spectralFloor ^ 2 - squareSum) ^ 3 := by ring

/-- The certificate read forwards: below the `(3/4) theta^2` line the capped cubic
residual is nonnegative. -/
theorem four_mul_cube_le_cappedCubic_of_le_threeQuarters {spectralFloor squareSum : ℝ}
    (hlight : squareSum ≤ 3 / 4 * spectralFloor ^ 2) :
    4 * squareSum ^ 3 ≤ 27 * spectralFloor ^ 2 * (spectralFloor ^ 2 - squareSum) ^ 2 := by
  have hgap : 0 ≤ 3 / 4 * spectralFloor ^ 2 - squareSum := by linarith
  have hfirst : 0 ≤ 81 / 4 * spectralFloor ^ 4 * (3 / 4 * spectralFloor ^ 2 - squareSum) :=
    mul_nonneg (by positivity) hgap
  have hsecond : 0 ≤ 18 * spectralFloor ^ 2 * (3 / 4 * spectralFloor ^ 2 - squareSum) ^ 2 := by
    positivity
  have hthird : 0 ≤ 4 * (3 / 4 * spectralFloor ^ 2 - squareSum) ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg hgap 3)
  linarith [hfirst, hsecond, hthird]

/-- **THE SORTING-FREE CORE OF V4, as a scalar statement.**  At a nonnegative root
`theta` of the shifted determinant `theta^3 - theta * squareSum + 2 *
tripleProduct`, with AM-GM supplied, the edge square sum is at least
`(3/4) theta^2`.

This replaces the pen's `a2 <= theta/2 <= a1`: read spectrally that ordering says
`a1 a2 <= (theta/2)^2`, i.e. `theta^2 - squareSum <= theta^2/4`, which is exactly
this inequality.  No eigenvalue is sorted here: substituting `2 P = theta *
squareSum - theta^3` into AM-GM gives `27 theta^2 (theta^2 - squareSum)^2 <=
4 squareSum^3`, which `cappedCubicResidual_eq_gapCertificate` contradicts as soon
as the gap is positive. -/
theorem threeQuarters_mul_sq_le_of_amgm_of_root
    {spectralFloor squareSum tripleProduct : ℝ} (hfloorNonneg : 0 ≤ spectralFloor)
    (hsquareSumNonneg : 0 ≤ squareSum)
    (hamgm : 27 * tripleProduct ^ 2 ≤ squareSum ^ 3)
    (hroot : spectralFloor ^ 3 - spectralFloor * squareSum + 2 * tripleProduct = 0) :
    3 / 4 * spectralFloor ^ 2 ≤ squareSum := by
  by_contra hcontra
  rw [not_le] at hcontra
  have hgap : 0 < 3 / 4 * spectralFloor ^ 2 - squareSum := by linarith
  have hfloorPos : 0 < spectralFloor := by nlinarith [sq_nonneg spectralFloor]
  have hsquared : 4 * tripleProduct ^ 2
      = spectralFloor ^ 2 * (spectralFloor ^ 2 - squareSum) ^ 2 := by
    linear_combination (2 * tripleProduct - spectralFloor ^ 3 + spectralFloor * squareSum) * hroot
  have hcapped : 27 * spectralFloor ^ 2 * (spectralFloor ^ 2 - squareSum) ^ 2
      ≤ 4 * squareSum ^ 3 := by linarith [hamgm, hsquared]
  have hfirst : 0 < 81 / 4 * spectralFloor ^ 4 * (3 / 4 * spectralFloor ^ 2 - squareSum) :=
    mul_pos (by positivity) hgap
  have hsecond : 0 ≤ 18 * spectralFloor ^ 2 * (3 / 4 * spectralFloor ^ 2 - squareSum) ^ 2 := by
    positivity
  have hthird : 0 < 4 * (3 / 4 * spectralFloor ^ 2 - squareSum) ^ 3 := by positivity
  linarith [hcapped, hfirst, hsecond, hthird]

/-- The edge form of the sorting-free core: AM-GM is supplied internally. -/
theorem threeQuarters_mul_sq_le_squareSum_of_shiftedDet_eq_zero
    {spectralFloor edgeFirst edgeSecond edgeThird : ℝ} (hfloorNonneg : 0 ≤ spectralFloor)
    (hroot : spectralFloor ^ 3
        - spectralFloor * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
        + 2 * (edgeFirst * edgeSecond * edgeThird) = 0) :
    3 / 4 * spectralFloor ^ 2 ≤ edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2 :=
  threeQuarters_mul_sq_le_of_amgm_of_root hfloorNonneg (by positivity)
    (twentySeven_mul_sq_tripleProduct_le_cube_squareSum edgeFirst edgeSecond edgeThird) hroot

/-! ## 4. The two scalar branches the gate runs on -/

/-- **THE SECOND ELEMENTARY SYMMETRIC BOUND.**  Under the norm cap and a
determinant floor at level `theta`, the edge square sum is at most `3 theta^2` —
which is exactly the hypothesis the cap-free backward criterion
`Gtz.posSemidef_smul_one_add_hollowSymmetricThree_of_squareSum_le` asks for.

Were it false, the determinant floor would force `tripleProduct > squareSum/3`,
hence `27 tripleProduct^2 > 3 squareSum^2`; AM-GM then gives `3 squareSum^2 <
squareSum^3`, so `squareSum > 3`, which the cap forbids.

STATEMENT HYGIENE: neither `0 <= spectralFloor` nor `0 <= squareSum` is needed —
`spectralFloor <= 1` alone drives `spectralFloor^3 <= spectralFloor^2`, and
positivity of `squareSum` falls out of the contradiction hypothesis. -/
theorem squareSum_le_three_mul_sq_of_amgm_of_determinantFloor
    {spectralFloor squareSum tripleProduct : ℝ}
    (hfloorLeOne : spectralFloor ≤ 1) (hsquareSumLeOne : squareSum ≤ 1)
    (hamgm : 27 * tripleProduct ^ 2 ≤ squareSum ^ 3)
    (hfloorBound : squareSum - 3 / 4 * spectralFloor ^ 2 - 1 / 4 * spectralFloor ^ 3
      ≤ 2 * tripleProduct) :
    squareSum ≤ 3 * spectralFloor ^ 2 := by
  by_contra hcontra
  rw [not_le] at hcontra
  have hcube : spectralFloor ^ 3 ≤ spectralFloor ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg spectralFloor) (by linarith : (0 : ℝ) ≤ 1 - spectralFloor)]
  have hpositive : 0 < squareSum := by nlinarith [sq_nonneg spectralFloor]
  have hproductBig : squareSum < 3 * tripleProduct := by linarith
  have hsquared : squareSum ^ 2 < 9 * tripleProduct ^ 2 := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 3 * tripleProduct - squareSum)
      (by linarith : (0 : ℝ) < 3 * tripleProduct + squareSum)]
  have hcubeBig : 3 * squareSum ^ 2 < squareSum ^ 3 := by linarith [hamgm, hsquared]
  nlinarith [hcubeBig, hpositive,
    mul_nonneg (sq_nonneg squareSum) (by linarith : (0 : ℝ) ≤ 1 - squareSum)]

/-- **THE DETERMINANT CRITERION.**  Under AM-GM and a determinant floor at level
`theta` in `[0,1]`, the criterion `theta * squareSum - 2 tripleProduct <=
theta^3` holds — the other hypothesis of the cap-free backward criterion.

The proof splits at the line `squareSum = (3/4) theta^2`.  Above it the
factorisation `(1 - theta)(squareSum - (3/4) theta^2) >= 0` turns the determinant
floor into the criterion directly.  Below it the floor is not used at all: the
criterion would fail only with `-2 tripleProduct > theta (theta^2 - squareSum)
>= 0`, whose square contradicts `four_mul_cube_le_cappedCubic_of_le_threeQuarters`
against AM-GM. -/
theorem criterion_of_amgm_of_determinantFloor
    {spectralFloor squareSum tripleProduct : ℝ} (hfloorNonneg : 0 ≤ spectralFloor)
    (hfloorLeOne : spectralFloor ≤ 1) (hsquareSumNonneg : 0 ≤ squareSum)
    (hamgm : 27 * tripleProduct ^ 2 ≤ squareSum ^ 3)
    (hfloorBound : squareSum - 3 / 4 * spectralFloor ^ 2 - 1 / 4 * spectralFloor ^ 3
      ≤ 2 * tripleProduct) :
    spectralFloor * squareSum - 2 * tripleProduct ≤ spectralFloor ^ 3 := by
  rcases le_total (3 / 4 * spectralFloor ^ 2) squareSum with hheavy | hlight
  · linarith [hfloorBound, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - spectralFloor)
      (by linarith : (0 : ℝ) ≤ squareSum - 3 / 4 * spectralFloor ^ 2)]
  · by_contra hcontra
    rw [not_le] at hcontra
    have hsquareSumLeSq : squareSum ≤ spectralFloor ^ 2 := by
      nlinarith [sq_nonneg spectralFloor]
    have hbase : 0 ≤ spectralFloor * (spectralFloor ^ 2 - squareSum) :=
      mul_nonneg hfloorNonneg (by linarith)
    have hstrict : spectralFloor * (spectralFloor ^ 2 - squareSum) < -(2 * tripleProduct) := by
      nlinarith [hcontra]
    have hsquared : (spectralFloor * (spectralFloor ^ 2 - squareSum)) ^ 2
        < 4 * tripleProduct ^ 2 := by
      nlinarith [mul_pos (by linarith : (0 : ℝ) < -(2 * tripleProduct)
          - spectralFloor * (spectralFloor ^ 2 - squareSum))
        (by linarith : (0 : ℝ) < -(2 * tripleProduct)
          + spectralFloor * (spectralFloor ^ 2 - squareSum))]
    linarith [four_mul_cube_le_cappedCubic_of_le_threeQuarters hlight, hamgm, hsquared]

/-! ## 5. V4(1): the pen's ordering statement, as the scalar lemma it is

Recorded for the record and NOT used: the sorting-free core above replaces it. -/

/-- **V4(1).**  For a trace-zero pair `(a1, a2)` with `a2 <= a1` whose completion
`a3 = -(a1 + a2)` is at least `-1` — the eigenvalues of a `3 x 3` block of a
hollow symmetric involution, whose norm cap is exactly `a3 >= -1` — the middle one
satisfies `a2 <= min(a1, 1 - a1) <= 1/2`.  The first bound is the ordering, the
second is `a1 + a2 = -a3 <= 1`, the third is elementary.

STATEMENT HYGIENE: the pen also assumes `a3 <= a2`, and that hypothesis is not
needed.  Nothing downstream consumes this lemma at all; the inequality that does
the work is `threeQuarters_mul_sq_le_of_amgm_of_root`, which is what the
ordering says once it is pushed through `a1 a2 <= ((a1+a2)/2)^2`. -/
theorem middle_le_min_of_traceZero_of_capped {topValue middleValue bottomValue : ℝ}
    (hsum : topValue + middleValue + bottomValue = 0) (hmiddleLeTop : middleValue ≤ topValue)
    (hcap : -1 ≤ bottomValue) :
    middleValue ≤ min topValue (1 - topValue) ∧ min topValue (1 - topValue) ≤ 1 / 2 := by
  refine ⟨le_min hmiddleLeTop (by linarith), ?_⟩
  rcases le_total topValue (1 - topValue) with hlow | hhigh
  · rw [min_eq_left hlow]; linarith
  · rw [min_eq_right hhigh]; linarith

/-! ## 6. V4(2) and the gate -/

/-- **V4(2), SHARP.**  At a nonnegative root `theta <= 1` of the shifted
determinant, the Gram determinant is at most `g(theta)`:
`det(1 + N) <= (1 + theta/2)^2 (1 - theta)`.

Substituting `2 P = theta * squareSum - theta^3` gives
`det(1 + N) = 1 - squareSum (1 - theta) - theta^3`, and
`squareSum >= (3/4) theta^2` with `theta <= 1` closes it. -/
theorem det_one_add_le_gTransform_of_shiftedDet_eq_zero
    {spectralFloor edgeFirst edgeSecond edgeThird : ℝ} (hfloorNonneg : 0 ≤ spectralFloor)
    (hfloorLeOne : spectralFloor ≤ 1)
    (hroot : (spectralFloor • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowMatrixThree edgeFirst edgeSecond edgeThird).det = 0) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) + hollowMatrixThree edgeFirst edgeSecond edgeThird).det
      ≤ gTransform spectralFloor := by
  rw [det_smul_one_add_hollowMatrixThree] at hroot
  have hsquareSum := threeQuarters_mul_sq_le_squareSum_of_shiftedDet_eq_zero
    hfloorNonneg hroot
  rw [det_one_add_hollowMatrixThree, gTransform_eq_one_sub_quarter_mul_cubicSum]
  nlinarith [hroot, hsquareSum, hfloorLeOne, hfloorNonneg]

/-- **THE `g`-TRANSFORM GATE.**  Under the norm cap `squareSum + 2 |P| <= 1` — what
every triple of a hollow symmetric involution carries — a Gram determinant at
least `g(theta)` forces the shifted block `theta . 1 + N` to be positive
semidefinite, for every `theta` in `[0, 1]`.

The proof supplies the two hypotheses of the cap-free backward criterion
`Gtz.posSemidef_smul_one_add_hollowSymmetricThree_of_squareSum_le`.  The second
elementary symmetric bound `squareSum <= 3 theta^2` comes from AM-GM against the
cap; the determinant criterion `theta * squareSum - 2 P <= theta^3` splits at
`squareSum = (3/4) theta^2`, the coherent side by one factorisation
`(1 - theta)(squareSum - (3/4) theta^2) >= 0` and the light side by AM-GM again. -/
theorem posSemidef_smul_one_add_hollowMatrixThree_of_gTransform_le_det
    {spectralFloor edgeFirst edgeSecond edgeThird : ℝ}
    (hcap : edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2
      + 2 * |edgeFirst * edgeSecond * edgeThird| ≤ 1)
    (hfloorNonneg : 0 ≤ spectralFloor) (hfloorLeOne : spectralFloor ≤ 1)
    (hdet : gTransform spectralFloor
      ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + hollowMatrixThree edgeFirst edgeSecond edgeThird).det) :
    (spectralFloor • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowMatrixThree edgeFirst edgeSecond edgeThird).PosSemidef := by
  rw [det_one_add_hollowMatrixThree, gTransform_eq_one_sub_quarter_mul_cubicSum] at hdet
  have hsquareSumNonneg : (0 : ℝ) ≤ edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2 := by positivity
  have hsquareSumLeOne : edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2 ≤ 1 := by
    have habs : (0 : ℝ) ≤ |edgeFirst * edgeSecond * edgeThird| := abs_nonneg _
    linarith
  have hamgm : 27 * (edgeFirst * edgeSecond * edgeThird) ^ 2
      ≤ (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2) ^ 3 :=
    twentySeven_mul_sq_tripleProduct_le_cube_squareSum edgeFirst edgeSecond edgeThird
  have hfloorBound : (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      - 3 / 4 * spectralFloor ^ 2 - 1 / 4 * spectralFloor ^ 3
      ≤ 2 * (edgeFirst * edgeSecond * edgeThird) := by linarith
  rw [hollowMatrixThree_eq_hollowSymmetricThree]
  exact posSemidef_smul_one_add_hollowSymmetricThree_of_squareSum_le hfloorNonneg
    (squareSum_le_three_mul_sq_of_amgm_of_determinantFloor hfloorLeOne hsquareSumLeOne
      hamgm hfloorBound)
    (criterion_of_amgm_of_determinantFloor hfloorNonneg hfloorLeOne hsquareSumNonneg
      hamgm hfloorBound)

/-- **V4(2) with no root hypothesis, and STRICT.**  The contrapositive of the gate:
if the shifted block fails to be positive semidefinite at `theta` then the Gram
determinant is strictly below `g(theta)`.  This is the pen's `det Gamma[T] <=
g(theta-star)` in the form a covering argument consumes — no spectral floor has
to exist, and no eigenvalue is sorted. -/
theorem det_one_add_lt_gTransform_of_not_posSemidef
    {spectralFloor edgeFirst edgeSecond edgeThird : ℝ}
    (hcap : edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2
      + 2 * |edgeFirst * edgeSecond * edgeThird| ≤ 1)
    (hfloorNonneg : 0 ≤ spectralFloor) (hfloorLeOne : spectralFloor ≤ 1)
    (hfail : ¬ (spectralFloor • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowMatrixThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) + hollowMatrixThree edgeFirst edgeSecond edgeThird).det
      < gTransform spectralFloor := by
  by_contra hcontra
  rw [not_lt] at hcontra
  exact hfail (posSemidef_smul_one_add_hollowMatrixThree_of_gTransform_le_det hcap
    hfloorNonneg hfloorLeOne hcontra)

/-- **The gate on a hollow involution's triple.**  The norm cap is supplied by
`Gtz.IsHollowInvolution.normCap_triple`, so three distinct indices are all the
caller needs. -/
theorem IsHollowInvolution.posSemidef_smul_one_add_submatrix_of_gTransform_le_det
    {size : ℕ} {invol : Matrix (Fin size) (Fin size) ℝ} (hinvol : IsHollowInvolution invol)
    {firstIndex secondIndex thirdIndex : Fin size} {spectralFloor : ℝ}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex)
    (hfloorNonneg : 0 ≤ spectralFloor) (hfloorLeOne : spectralFloor ≤ 1)
    (hdet : gTransform spectralFloor
      ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + invol.submatrix ![firstIndex, secondIndex, thirdIndex]
              ![firstIndex, secondIndex, thirdIndex]).det) :
    (spectralFloor • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + invol.submatrix ![firstIndex, secondIndex, thirdIndex]
          ![firstIndex, secondIndex, thirdIndex]).PosSemidef := by
  have hblock := hinvol.submatrix_three_eq_hollowMatrixThree firstIndex secondIndex thirdIndex
  rw [hblock] at hdet ⊢
  exact posSemidef_smul_one_add_hollowMatrixThree_of_gTransform_le_det
    (hinvol.normCap_triple hfirstSecond hfirstThird hsecondThird)
    hfloorNonneg hfloorLeOne hdet

/-! ## 7. The floor lemma: a flat shift transports to every capacity above it

This is the elementary but load-bearing step of the pen's V4 gate — "if
`min_{c in T} tau_c >= theta-star_T` then `T` dominates" — and it is stated here
at every dimension, for an arbitrary off-diagonal part.  No hollowness, no
involution, no pairwise clauses. -/

/-- **THE CRITERION CELL IS UPWARD CLOSED.**  Raising any capacity preserves
positive semidefiniteness of `diagonal capacity + offDiagonal`.  The pen derives
this from `d Delta / d tau_c = tau_a tau_b - w_ab >= 0` under the pairwise
clauses; at the matrix level it is `PosSemidef.diagonal` plus `PosSemidef.add`,
with no side condition at all. -/
theorem posSemidef_diagonal_add_of_le {dimension : ℕ}
    {lowCapacity highCapacity : Fin dimension → ℝ}
    (hmonotone : ∀ index, lowCapacity index ≤ highCapacity index)
    {offDiagonal : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hlow : (Matrix.diagonal lowCapacity + offDiagonal).PosSemidef) :
    (Matrix.diagonal highCapacity + offDiagonal).PosSemidef := by
  have hgap : (Matrix.diagonal (highCapacity - lowCapacity)).PosSemidef :=
    Matrix.PosSemidef.diagonal fun index => sub_nonneg.mpr (hmonotone index)
  have hrewrite : Matrix.diagonal highCapacity + offDiagonal
      = Matrix.diagonal (highCapacity - lowCapacity)
        + (Matrix.diagonal lowCapacity + offDiagonal) := by
    have hsplit : Matrix.diagonal (highCapacity - lowCapacity)
        = Matrix.diagonal highCapacity - Matrix.diagonal lowCapacity := by
      rw [Matrix.diagonal_sub]; rfl
    rw [hsplit]; abel
  rw [hrewrite]
  exact hgap.add hlow

/-- **THE FLOOR LEMMA.**  If the FLAT shift at `floorLevel` is positive
semidefinite and every capacity is at least `floorLevel`, then the DIAGONAL shift
at the actual capacities is positive semidefinite.  Read on a triple of a hollow
involution with `floorLevel = theta-star_T`, this is exactly "min over `T` of
`tau_c >= theta-star_T` implies `T` dominates". -/
theorem posSemidef_diagonal_add_of_floor {dimension : ℕ} {capacity : Fin dimension → ℝ}
    {floorLevel : ℝ} (hfloor : ∀ index, floorLevel ≤ capacity index)
    {offDiagonal : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hflat : (floorLevel • (1 : Matrix (Fin dimension) (Fin dimension) ℝ)
      + offDiagonal).PosSemidef) :
    (Matrix.diagonal capacity + offDiagonal).PosSemidef := by
  refine posSemidef_diagonal_add_of_le (lowCapacity := fun _ => floorLevel) hfloor ?_
  rwa [show (Matrix.diagonal (fun _ : Fin dimension => floorLevel))
      = floorLevel • (1 : Matrix (Fin dimension) (Fin dimension) ℝ) by
    rw [Matrix.smul_one_eq_diagonal]]

/-- **THE `g`-TRANSFORM GATE IN CAPACITY COORDINATES.**  The composite the frontier
argument runs: a determinant floor plus a capacity floor gives positive
semidefiniteness at the actual capacities.  The shape `Matrix.diagonal capacity +
block` is exactly what the `tau`-coordinate congruence `Gram[T] - diag(2 t_c)`
produces. -/
theorem posSemidef_diagonal_add_hollowMatrixThree_of_gTransform_le_det
    {capacity : Fin 3 → ℝ} {spectralFloor edgeFirst edgeSecond edgeThird : ℝ}
    (hcap : edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2
      + 2 * |edgeFirst * edgeSecond * edgeThird| ≤ 1)
    (hfloorNonneg : 0 ≤ spectralFloor) (hfloorLeOne : spectralFloor ≤ 1)
    (hfloor : ∀ slot, spectralFloor ≤ capacity slot)
    (hdet : gTransform spectralFloor
      ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + hollowMatrixThree edgeFirst edgeSecond edgeThird).det) :
    (Matrix.diagonal capacity + hollowMatrixThree edgeFirst edgeSecond edgeThird).PosSemidef :=
  posSemidef_diagonal_add_of_floor hfloor
    (posSemidef_smul_one_add_hollowMatrixThree_of_gTransform_le_det hcap hfloorNonneg
      hfloorLeOne hdet)

/-- **The gate and the floor, on a hollow involution's triple.**  The form the
four-set gate below instantiates, and the form a covering argument wants: three
distinct indices, a capacity floor at each, and a determinant floor. -/
theorem IsHollowInvolution.posSemidef_diagonal_add_submatrix_of_gTransform_le_det
    {size : ℕ} {invol : Matrix (Fin size) (Fin size) ℝ} (hinvol : IsHollowInvolution invol)
    {firstIndex secondIndex thirdIndex : Fin size} {capacity : Fin size → ℝ} {spectralFloor : ℝ}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex)
    (hfloorNonneg : 0 ≤ spectralFloor) (hfloorLeOne : spectralFloor ≤ 1)
    (hcapacityFirst : spectralFloor ≤ capacity firstIndex)
    (hcapacitySecond : spectralFloor ≤ capacity secondIndex)
    (hcapacityThird : spectralFloor ≤ capacity thirdIndex)
    (hdet : gTransform spectralFloor
      ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + invol.submatrix ![firstIndex, secondIndex, thirdIndex]
              ![firstIndex, secondIndex, thirdIndex]).det) :
    (Matrix.diagonal (fun slot => capacity (![firstIndex, secondIndex, thirdIndex] slot))
      + invol.submatrix ![firstIndex, secondIndex, thirdIndex]
          ![firstIndex, secondIndex, thirdIndex]).PosSemidef := by
  refine posSemidef_diagonal_add_of_floor (floorLevel := spectralFloor) (fun slot => ?_)
    (hinvol.posSemidef_smul_one_add_submatrix_of_gTransform_le_det hfirstSecond hfirstThird
      hsecondThird hfloorNonneg hfloorLeOne hdet)
  fin_cases slot
  · exact hcapacityFirst
  · exact hcapacitySecond
  · exact hcapacityThird

/-! ## 8. The four-set determinant identity

At a `4-2` split of a hollow symmetric involution of `Fin 6` the shipped block
trace laws read off both scalars of the four-set at once: the quadratic law gives
the six-edge square sum and the cubic law gives the four-triangle product sum.
Neither the row law nor Jacobi's complementary-minor identity is needed, and no
spectrum is computed — `Gtz.trace_square_sub_trace_square_of_blockRelations` and
`Gtz.trace_cube_add_trace_cube_of_blockRelations` hold at arbitrary block sizes
over any commutative ring. -/

/-- **The hollow symmetric `4 x 4`** with its six off-diagonal entries in the
slots `(0,1)`, `(0,2)`, `(0,3)`, `(1,2)`, `(1,3)`, `(2,3)`. -/
def hollowMatrixFour (edgeZeroOne edgeZeroTwo edgeZeroThree edgeOneTwo edgeOneThree
    edgeTwoThree : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, edgeZeroOne, edgeZeroTwo, edgeZeroThree;
     edgeZeroOne, 0, edgeOneTwo, edgeOneThree;
     edgeZeroTwo, edgeOneTwo, 0, edgeTwoThree;
     edgeZeroThree, edgeOneThree, edgeTwoThree, 0]

/-- **The hollow symmetric `2 x 2`**, the complementary pair's block. -/
def hollowMatrixTwo (edge : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, edge;
     edge, 0]

theorem trace_hollowMatrixFour (edgeZeroOne edgeZeroTwo edgeZeroThree edgeOneTwo edgeOneThree
    edgeTwoThree : ℝ) :
    (hollowMatrixFour edgeZeroOne edgeZeroTwo edgeZeroThree edgeOneTwo edgeOneThree
      edgeTwoThree).trace = 0 := by
  simp [Matrix.trace, hollowMatrixFour, Fin.sum_univ_four]

/-- `tr(N^2) = 2 * (sum of the six squared edges)` at size four. -/
theorem trace_square_hollowMatrixFour (edgeZeroOne edgeZeroTwo edgeZeroThree edgeOneTwo
    edgeOneThree edgeTwoThree : ℝ) :
    (hollowMatrixFour edgeZeroOne edgeZeroTwo edgeZeroThree edgeOneTwo edgeOneThree edgeTwoThree
        * hollowMatrixFour edgeZeroOne edgeZeroTwo edgeZeroThree edgeOneTwo edgeOneThree
          edgeTwoThree).trace
      = 2 * (edgeZeroOne ^ 2 + edgeZeroTwo ^ 2 + edgeZeroThree ^ 2 + edgeOneTwo ^ 2
        + edgeOneThree ^ 2 + edgeTwoThree ^ 2) := by
  simp [Matrix.trace, hollowMatrixFour, Fin.sum_univ_four]
  ring

/-- `tr(N^3) = 6 * (sum of the four oriented triangle products)` at size four: every
nonzero term of `sum_{i,j,k} N_ij N_jk N_ki` has three distinct indices, and each
of the four unordered triples supplies six orderings of one product. -/
theorem trace_cube_hollowMatrixFour (edgeZeroOne edgeZeroTwo edgeZeroThree edgeOneTwo
    edgeOneThree edgeTwoThree : ℝ) :
    (hollowMatrixFour edgeZeroOne edgeZeroTwo edgeZeroThree edgeOneTwo edgeOneThree edgeTwoThree
        * hollowMatrixFour edgeZeroOne edgeZeroTwo edgeZeroThree edgeOneTwo edgeOneThree
          edgeTwoThree
        * hollowMatrixFour edgeZeroOne edgeZeroTwo edgeZeroThree edgeOneTwo edgeOneThree
          edgeTwoThree).trace
      = 6 * (edgeZeroOne * edgeZeroTwo * edgeOneTwo
        + edgeZeroOne * edgeZeroThree * edgeOneThree
        + edgeZeroTwo * edgeZeroThree * edgeTwoThree
        + edgeOneTwo * edgeOneThree * edgeTwoThree) := by
  simp [Matrix.trace, hollowMatrixFour, Fin.sum_univ_four]
  ring

theorem trace_hollowMatrixTwo (edge : ℝ) : (hollowMatrixTwo edge).trace = 0 := by
  simp [Matrix.trace, hollowMatrixTwo, Fin.sum_univ_two]

theorem trace_square_hollowMatrixTwo (edge : ℝ) :
    (hollowMatrixTwo edge * hollowMatrixTwo edge).trace = 2 * edge ^ 2 := by
  simp [Matrix.trace, hollowMatrixTwo, Fin.sum_univ_two]
  ring

/-- The hollow `2 x 2` has vanishing cube trace — this is why the four-set's
product sum vanishes rather than mirroring anything. -/
theorem trace_cube_hollowMatrixTwo (edge : ℝ) :
    (hollowMatrixTwo edge * hollowMatrixTwo edge * hollowMatrixTwo edge).trace = 0 := by
  simp [Matrix.trace, hollowMatrixTwo, Fin.sum_univ_two]

/-- Four pairwise distinct values enumerate injectively. -/
theorem injective_four_of_ne {carrier : Type*}
    {valueZero valueOne valueTwo valueThree : carrier}
    (hzeroOne : valueZero ≠ valueOne) (hzeroTwo : valueZero ≠ valueTwo)
    (hzeroThree : valueZero ≠ valueThree) (honeTwo : valueOne ≠ valueTwo)
    (honeThree : valueOne ≠ valueThree) (htwoThree : valueTwo ≠ valueThree) :
    Function.Injective ![valueZero, valueOne, valueTwo, valueThree] := by
  intro leftSlot rightSlot hvalue
  fin_cases leftSlot <;> fin_cases rightSlot <;>
    first
      | rfl
      | exact absurd hvalue (by assumption)
      | exact absurd hvalue.symm (by assumption)

/-- Two distinct values enumerate injectively. -/
theorem injective_two_of_ne {carrier : Type*} {valueZero valueOne : carrier}
    (hzeroOne : valueZero ≠ valueOne) : Function.Injective ![valueZero, valueOne] := by
  intro leftSlot rightSlot hvalue
  fin_cases leftSlot <;> fin_cases rightSlot <;>
    first
      | rfl
      | exact absurd hvalue (by assumption)
      | exact absurd hvalue.symm (by assumption)

/-- Splitting a sum over `Fin 6` along a `4-2` enumeration. -/
theorem sum_split_four_two_of_bijective_six {additive : Type*} [AddCommMonoid additive]
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    (summand : Fin 6 → additive) :
    ∑ position, summand position
      = ∑ slot, summand (![first, second, third, fourth] slot)
        + ∑ slot, summand (![fifth, sixth] slot) := by
  rw [← Fintype.sum_bijective ![first, second, third, fourth, fifth, sixth] hbijective
    (fun slot => summand (![first, second, third, fourth, fifth, sixth] slot)) summand
    (fun _ => rfl)]
  simp [Fin.sum_univ_six, Fin.sum_univ_four, Fin.sum_univ_two, add_assoc]

namespace IsHollowInvolution

variable {size : ℕ} {invol : Matrix (Fin size) (Fin size) ℝ}

/-- The compression at four indices IS the hollow `4 x 4` of its six entries. -/
theorem submatrix_four_eq_hollowMatrixFour (hinvol : IsHollowInvolution invol)
    (firstIndex secondIndex thirdIndex fourthIndex : Fin size) :
    invol.submatrix ![firstIndex, secondIndex, thirdIndex, fourthIndex]
        ![firstIndex, secondIndex, thirdIndex, fourthIndex]
      = hollowMatrixFour (invol firstIndex secondIndex) (invol firstIndex thirdIndex)
          (invol firstIndex fourthIndex) (invol secondIndex thirdIndex)
          (invol secondIndex fourthIndex) (invol thirdIndex fourthIndex) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Matrix.submatrix_apply, hollowMatrixFour] <;>
    first
      | exact hinvol.diagonal_eq_zero _
      | rfl
      | exact hinvol.apply_comm _ _

/-- The compression at two indices IS the hollow `2 x 2` of its entry. -/
theorem submatrix_two_eq_hollowMatrixTwo (hinvol : IsHollowInvolution invol)
    (firstIndex secondIndex : Fin size) :
    invol.submatrix ![firstIndex, secondIndex] ![firstIndex, secondIndex]
      = hollowMatrixTwo (invol firstIndex secondIndex) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Matrix.submatrix_apply, hollowMatrixTwo] <;>
    first
      | exact hinvol.diagonal_eq_zero _
      | rfl
      | exact hinvol.apply_comm _ _

end IsHollowInvolution

namespace IsHollowInvolution

variable {invol : Matrix (Fin 6) (Fin 6) ℝ}

/-- The three block relations of a `4-2` split, packaged for the trace laws. -/
private theorem blockRelations_four_two (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    (invol.submatrix ![first, second, third, fourth] ![first, second, third, fourth]
        * invol.submatrix ![first, second, third, fourth] ![first, second, third, fourth]
      + invol.submatrix ![first, second, third, fourth] ![fifth, sixth]
        * (invol.submatrix ![first, second, third, fourth] ![fifth, sixth])ᵀ = 1)
    ∧ (invol.submatrix ![first, second, third, fourth] ![first, second, third, fourth]
        * invol.submatrix ![first, second, third, fourth] ![fifth, sixth]
      + invol.submatrix ![first, second, third, fourth] ![fifth, sixth]
        * invol.submatrix ![fifth, sixth] ![fifth, sixth] = 0)
    ∧ ((invol.submatrix ![first, second, third, fourth] ![fifth, sixth])ᵀ
        * invol.submatrix ![first, second, third, fourth] ![fifth, sixth]
      + invol.submatrix ![fifth, sixth] ![fifth, sixth]
        * invol.submatrix ![fifth, sixth] ![fifth, sixth] = 1) := by
  have hsplit := sum_split_four_two_of_bijective_six (additive := ℝ) hbijective
  have hleftInjective : Function.Injective ![first, second, third, fourth] :=
    injective_four_of_ne (ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 1))
      (ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 2))
      (ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 3))
      (ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 2))
      (ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 3))
      (ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 3))
  have hrightInjective : Function.Injective ![fifth, sixth] :=
    injective_two_of_ne (ne_of_bijective_six hbijective (by decide : (4 : Fin 6) ≠ 5))
  have hdisjoint : ∀ leftSlot : Fin 4, ∀ rightSlot : Fin 2,
      ![first, second, third, fourth] leftSlot ≠ ![fifth, sixth] rightSlot := by
    intro leftSlot rightSlot
    fin_cases leftSlot <;> fin_cases rightSlot <;>
      first
        | exact ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 4)
        | exact ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 5)
        | exact ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 4)
        | exact ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 5)
        | exact ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 4)
        | exact ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 5)
        | exact ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 4)
        | exact ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 5)
  exact ⟨upperBlockRelation_of_squareEqOne hinvol.symmetric hinvol.square_eq_one
      hleftInjective hsplit,
    crossBlockRelation_of_squareEqOne hinvol.square_eq_one hdisjoint hsplit,
    lowerBlockRelation_of_squareEqOne hinvol.symmetric hinvol.square_eq_one
      hrightInjective hsplit⟩

/-- **THE FOUR-SET EDGE BUDGET.**  The six squared edges of a four-set sum to
`1 + w`, where `w` is the squared entry of the complementary PAIR.  This is the
quadratic block trace law `tr(A^2) - tr(D^2) = 4 - 2` read through
`tr(N^2) = 2 sigma`; the row law is not used. -/
theorem sum_sq_edge_fourSet_eq (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    invol first second ^ 2 + invol first third ^ 2 + invol first fourth ^ 2
        + invol second third ^ 2 + invol second fourth ^ 2 + invol third fourth ^ 2
      = 1 + invol fifth sixth ^ 2 := by
  obtain ⟨hupper, -, hlower⟩ := hinvol.blockRelations_four_two hbijective
  have htrace := trace_square_sub_trace_square_of_blockRelations hupper hlower
  rw [hinvol.submatrix_four_eq_hollowMatrixFour first second third fourth,
    hinvol.submatrix_two_eq_hollowMatrixTwo fifth sixth,
    trace_square_hollowMatrixFour, trace_square_hollowMatrixTwo] at htrace
  simp only [Fintype.card_fin] at htrace
  push_cast at htrace
  linarith

/-- **THE FOUR-SET PRODUCT SUM VANISHES.**  The four oriented triangle products of
a four-set sum to zero.  This is the cubic block trace law
`tr(A^3) + tr(D^3) = 0` read through `tr(N^3) = 6 P`, with `tr(D^3) = 0` because a
hollow `2 x 2` cubes to a hollow `2 x 2`. -/
theorem sum_tripleProduct_fourSet_eq_zero (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    invol first second * invol first third * invol second third
        + invol first second * invol first fourth * invol second fourth
        + invol first third * invol first fourth * invol third fourth
        + invol second third * invol second fourth * invol third fourth = 0 := by
  obtain ⟨hupper, hcross, hlower⟩ := hinvol.blockRelations_four_two hbijective
  have htraceUpper : (invol.submatrix ![first, second, third, fourth]
      ![first, second, third, fourth]).trace = 0 := by
    rw [hinvol.submatrix_four_eq_hollowMatrixFour first second third fourth,
      trace_hollowMatrixFour]
  have htraceLower : (invol.submatrix ![fifth, sixth] ![fifth, sixth]).trace = 0 := by
    rw [hinvol.submatrix_two_eq_hollowMatrixTwo fifth sixth, trace_hollowMatrixTwo]
  have htrace := trace_cube_add_trace_cube_of_blockRelations hupper hcross hlower htraceUpper
    htraceLower
  rw [hinvol.submatrix_four_eq_hollowMatrixFour first second third fourth,
    hinvol.submatrix_two_eq_hollowMatrixTwo fifth sixth,
    trace_cube_hollowMatrixFour, trace_cube_hollowMatrixTwo] at htrace
  linarith

/-- **THE FOUR-SET DETERMINANT IDENTITY.**  The four triple Gram determinants of a
four-set sum to `2 (1 - w)`, `w` the squared entry of the complementary pair.
Each determinant is `1 - sigma_T + 2 P_T`; each edge lies in exactly two of the
four triples, so the square sums contribute `-2 (1 + w)`, and the product sums
contribute nothing. -/
theorem sum_det_one_add_submatrix_fourSet_eq (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + invol.submatrix ![first, second, third] ![first, second, third]).det
        + ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + invol.submatrix ![first, second, fourth] ![first, second, fourth]).det
        + ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + invol.submatrix ![first, third, fourth] ![first, third, fourth]).det
        + ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + invol.submatrix ![second, third, fourth] ![second, third, fourth]).det
      = 2 * (1 - invol fifth sixth ^ 2) := by
  have hedge := hinvol.sum_sq_edge_fourSet_eq hbijective
  have hproduct := hinvol.sum_tripleProduct_fourSet_eq_zero hbijective
  rw [hinvol.submatrix_three_eq_hollowMatrixThree first second third,
    hinvol.submatrix_three_eq_hollowMatrixThree first second fourth,
    hinvol.submatrix_three_eq_hollowMatrixThree first third fourth,
    hinvol.submatrix_three_eq_hollowMatrixThree second third fourth,
    det_one_add_hollowMatrixThree, det_one_add_hollowMatrixThree,
    det_one_add_hollowMatrixThree, det_one_add_hollowMatrixThree]
  linarith

end IsHollowInvolution

/-! ## 9. The four-set gate and the covering corollary -/

/-- Pigeonhole on four reals: if they sum to at least `4 * level`, one is at least
`level`. -/
theorem exists_ge_of_four_sum {firstValue secondValue thirdValue fourthValue level : ℝ}
    (hsum : 4 * level ≤ firstValue + secondValue + thirdValue + fourthValue) :
    level ≤ firstValue ∨ level ≤ secondValue ∨ level ≤ thirdValue ∨ level ≤ fourthValue := by
  by_contra hcontra
  simp only [not_or, not_le] at hcontra
  obtain ⟨hfirst, hsecond, hthird, hfourth⟩ := hcontra
  linarith

namespace IsHollowInvolution

variable {invol : Matrix (Fin 6) (Fin 6) ℝ}

/-- **THE FOUR-SET GATE.**  Some triple of a four-set has Gram determinant at least
`(1 - w)/2`, `w` the squared entry of the complementary pair.  Pigeonhole on the
four-set identity. -/
theorem exists_triple_det_ge_of_fourSet (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    (1 - invol fifth sixth ^ 2) / 2
        ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + invol.submatrix ![first, second, third] ![first, second, third]).det
      ∨ (1 - invol fifth sixth ^ 2) / 2
        ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + invol.submatrix ![first, second, fourth] ![first, second, fourth]).det
      ∨ (1 - invol fifth sixth ^ 2) / 2
        ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + invol.submatrix ![first, third, fourth] ![first, third, fourth]).det
      ∨ (1 - invol fifth sixth ^ 2) / 2
        ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          + invol.submatrix ![second, third, fourth] ![second, third, fourth]).det :=
  exists_ge_of_four_sum (by linarith [hinvol.sum_det_one_add_submatrix_fourSet_eq hbijective])

/-- **THE COVERING COROLLARY.**  Fix a four-set of a hollow symmetric involution of
`Fin 6` and let `w` be the squared entry of the complementary pair.  If a level
`theta` in `[0,1]` clears the cubic threshold `2 + 2 w <= theta^3 + 3 theta^2` and
every atom outside the complementary pair has capacity at least `theta`, then
some triple avoiding that pair is positive semidefinite at the ACTUAL capacities.

This is the pen's "`tau_(4) >= g-inverse((1 - w_56)/2)` implies covered", with
the inverse function replaced by the exact cubic condition: no root is extracted,
no inverse is defined, and `gTransform_affineThreshold_le` supplies a rational
`theta` for every `w`.  The gate fires only above `sqrt 3 - 1`
(`gTransform_le_half_iff_sqrtThree_sub_one_le`), so it is a TOP-BAND statement —
see `half_lt_gTransform_twoThirds`. -/
theorem exists_pick_posSemidef_diagonal_add_of_capacity_floor
    (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    {capacity : Fin 6 → ℝ} {spectralFloor : ℝ}
    (hfloorNonneg : 0 ≤ spectralFloor) (hfloorLeOne : spectralFloor ≤ 1)
    (hthreshold : 2 + 2 * invol fifth sixth ^ 2
      ≤ spectralFloor ^ 3 + 3 * spectralFloor ^ 2)
    (hcapacity : ∀ index, index ≠ fifth → index ≠ sixth → spectralFloor ≤ capacity index) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick
      ∧ (∀ slot, pick slot ≠ fifth ∧ pick slot ≠ sixth)
      ∧ (Matrix.diagonal (fun slot => capacity (pick slot))
          + invol.submatrix pick pick).PosSemidef := by
  have hgTransform : gTransform spectralFloor ≤ (1 - invol fifth sixth ^ 2) / 2 :=
    (gTransform_le_iff_cube_add_three_mul_sq_le spectralFloor
      (invol fifth sixth ^ 2)).mpr hthreshold
  have hliveFirst : first ≠ fifth ∧ first ≠ sixth :=
    ⟨ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 4),
      ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 5)⟩
  have hliveSecond : second ≠ fifth ∧ second ≠ sixth :=
    ⟨ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 4),
      ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 5)⟩
  have hliveThird : third ≠ fifth ∧ third ≠ sixth :=
    ⟨ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 4),
      ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 5)⟩
  have hliveFourth : fourth ≠ fifth ∧ fourth ≠ sixth :=
    ⟨ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 4),
      ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 5)⟩
  have hfirstSecond : first ≠ second := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 1)
  have hfirstThird : first ≠ third := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 2)
  have hfirstFourth : first ≠ fourth := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 3)
  have hsecondThird : second ≠ third := ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 2)
  have hsecondFourth : second ≠ fourth :=
    ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 3)
  have hthirdFourth : third ≠ fourth := ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 3)
  have hstep : ∀ pickFirst pickSecond pickThird : Fin 6,
      pickFirst ≠ pickSecond → pickFirst ≠ pickThird → pickSecond ≠ pickThird →
      (pickFirst ≠ fifth ∧ pickFirst ≠ sixth) → (pickSecond ≠ fifth ∧ pickSecond ≠ sixth) →
      (pickThird ≠ fifth ∧ pickThird ≠ sixth) →
      (1 - invol fifth sixth ^ 2) / 2 ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        + invol.submatrix ![pickFirst, pickSecond, pickThird]
          ![pickFirst, pickSecond, pickThird]).det →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick
        ∧ (∀ slot, pick slot ≠ fifth ∧ pick slot ≠ sixth)
        ∧ (Matrix.diagonal (fun slot => capacity (pick slot))
            + invol.submatrix pick pick).PosSemidef := by
    intro pickFirst pickSecond pickThird hpairOne hpairTwo hpairThree hliveOne hliveTwo
      hliveThree hdet
    refine ⟨![pickFirst, pickSecond, pickThird],
      injective_three_of_ne hpairOne hpairTwo hpairThree, fun slot => ?_,
      hinvol.posSemidef_diagonal_add_submatrix_of_gTransform_le_det hpairOne hpairTwo hpairThree
        hfloorNonneg hfloorLeOne (hcapacity pickFirst hliveOne.1 hliveOne.2)
        (hcapacity pickSecond hliveTwo.1 hliveTwo.2)
        (hcapacity pickThird hliveThree.1 hliveThree.2) (le_trans hgTransform hdet)⟩
    fin_cases slot
    · exact hliveOne
    · exact hliveTwo
    · exact hliveThree
  rcases hinvol.exists_triple_det_ge_of_fourSet hbijective with
    hcase | hcase | hcase | hcase
  · exact hstep first second third hfirstSecond hfirstThird hsecondThird hliveFirst hliveSecond
      hliveThird hcase
  · exact hstep first second fourth hfirstSecond hfirstFourth hsecondFourth hliveFirst hliveSecond
      hliveFourth hcase
  · exact hstep first third fourth hfirstThird hfirstFourth hthirdFourth hliveFirst hliveThird
      hliveFourth hcase
  · exact hstep second third fourth hsecondThird hsecondFourth hthirdFourth hliveSecond hliveThird
      hliveFourth hcase

/-- **THE COVERING COROLLARY, WITH THE TRIPLE NAMED.**  The same statement with the
selected triple exposed as three indices and the block written as
`Gtz.hollowMatrixThree`, which is the form the criterion layer's lemmas consume
directly. -/
theorem exists_triple_posSemidef_diagonal_add_hollowMatrixThree_of_capacity_floor
    (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    {capacity : Fin 6 → ℝ} {spectralFloor : ℝ}
    (hfloorNonneg : 0 ≤ spectralFloor) (hfloorLeOne : spectralFloor ≤ 1)
    (hthreshold : 2 + 2 * invol fifth sixth ^ 2
      ≤ spectralFloor ^ 3 + 3 * spectralFloor ^ 2)
    (hcapacity : ∀ index, index ≠ fifth → index ≠ sixth → spectralFloor ≤ capacity index) :
    ∃ pickFirst pickSecond pickThird : Fin 6,
      pickFirst ≠ pickSecond ∧ pickFirst ≠ pickThird ∧ pickSecond ≠ pickThird
      ∧ (pickFirst ≠ fifth ∧ pickFirst ≠ sixth) ∧ (pickSecond ≠ fifth ∧ pickSecond ≠ sixth)
      ∧ (pickThird ≠ fifth ∧ pickThird ≠ sixth)
      ∧ (Matrix.diagonal ![capacity pickFirst, capacity pickSecond, capacity pickThird]
          + hollowMatrixThree (invol pickFirst pickSecond) (invol pickFirst pickThird)
              (invol pickSecond pickThird)).PosSemidef := by
  obtain ⟨pick, hinjective, hlive, hpositive⟩ :=
    hinvol.exists_pick_posSemidef_diagonal_add_of_capacity_floor hbijective hfloorNonneg
      hfloorLeOne hthreshold hcapacity
  have heta : pick = ![pick 0, pick 1, pick 2] := by
    funext slot; fin_cases slot <;> rfl
  have hdiagonal : (fun slot => capacity (pick slot))
      = ![capacity (pick 0), capacity (pick 1), capacity (pick 2)] := by
    funext slot; fin_cases slot <;> rfl
  rw [hdiagonal] at hpositive
  refine ⟨pick 0, pick 1, pick 2,
    fun hvalue => absurd (hinjective hvalue) (by decide),
    fun hvalue => absurd (hinjective hvalue) (by decide),
    fun hvalue => absurd (hinjective hvalue) (by decide),
    hlive 0, hlive 1, hlive 2, ?_⟩
  rw [← hinvol.submatrix_three_eq_hollowMatrixThree (pick 0) (pick 1) (pick 2), ← heta]
  exact hpositive

/-- **THE COVERING COROLLARY WITH THE RATIONAL THRESHOLD.**  Instantiating the
covering corollary at `theta = 11/15 + w/3` removes the cubic hypothesis: as long
as the complementary pair weight is at most `4/5` — so that the affine threshold
stays inside `[0,1]` — a capacity floor of `11/15 + w/3` on the four live atoms
covers.  A caller with `w > 4/5` should take `theta = 1` instead, where the gate
is free. -/
theorem exists_pick_posSemidef_diagonal_add_of_affineThreshold
    (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    {capacity : Fin 6 → ℝ}
    (hpairWeight : invol fifth sixth ^ 2 ≤ 4 / 5)
    (hcapacity : ∀ index, index ≠ fifth → index ≠ sixth →
      11 / 15 + invol fifth sixth ^ 2 / 3 ≤ capacity index) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick
      ∧ (∀ slot, pick slot ≠ fifth ∧ pick slot ≠ sixth)
      ∧ (Matrix.diagonal (fun slot => capacity (pick slot))
          + invol.submatrix pick pick).PosSemidef := by
  obtain ⟨hnonneg, hleOne⟩ := affineThreshold_mem_unitInterval
    (sq_nonneg (invol fifth sixth)) hpairWeight
  refine hinvol.exists_pick_posSemidef_diagonal_add_of_capacity_floor hbijective hnonneg hleOne
    ?_ hcapacity
  have hclears := gTransform_affineThreshold_le (sq_nonneg (invol fifth sixth))
  rw [gTransform_le_iff_cube_add_three_mul_sq_le] at hclears
  exact hclears

end IsHollowInvolution

end Gtz

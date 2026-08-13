import Gtz.Wave.CertificateCornerBackbone
import Gtz.Wave.KFourCertificateReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The K4 certificate proof — the opposite-pair dichotomy closes closure three

The K4 certificate reduction narrowed closure three to one polynomial
statement.  This module proves that statement.  The kill is a case
analysis over the three opposite edge pairs of the tetrahedron.

## The dichotomy

Each edge read makes its shifted weight an eigenvalue of a two-by-two
corner of `M`.  The diagonal idempotency entries and the trace make
the spectra of two opposite corners complementary.  Thus each opposite
pair satisfies the product identity
`(x + y - 1) * (Ti + Tj - x + y - 1) = 0`:
the two shifted weights sum to one, or the pair satisfies the tau
relation.

## The case analysis

A sum pair equates `2 * value` with the sum of the four other
weights.  That sum is positive, against `value < 0`.  Thus every pair
satisfies the tau relation.  Then the corner excess balance collapses
to `w01 * w23 + w02 * w13 + w03 * w12 = 2 * value - 3 * value ^ 2`.
The left side is a sum of positive products.  The right side is
negative at a negative value.  This is the contradiction.

## Key results

* `Gtz.corner_dichotomy_zero_one`, `Gtz.corner_dichotomy_zero_two`,
  `Gtz.corner_dichotomy_zero_three` — **THE DICHOTOMY LAWS.**
* `Gtz.kFourCertificate_holds` — **THE CERTIFICATE PROOF.**
* `Gtz.rankFourKFourClosed_holds` — **CLOSURE THREE.**

## Vacuity

Every lemma is an unconditional statement about real numbers and real
matrices.  No crux hypothesis appears.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the opposite-pair dichotomy laws -/

/-- **THE DICHOTOMY AT THE PAIR (0, 1).**  An eigenvalue `x` of the
`(0, 1)` corner and an eigenvalue `y` of the `(2, 3)` corner of a
trace-two idempotent satisfy the product identity: the two eigenvalues
sum to one, or `y` equals one minus the second corner eigenvalue.  The
proof consumes only the four diagonal idempotency entries, the trace,
and the two corner characteristic equations. -/
theorem corner_dichotomy_zero_one {M : Matrix (Fin 4) (Fin 4) ℝ} {x y : ℝ}
    (hidem : M * M = M)
    (htr : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2)
    (hx : M 0 1 * M 1 0 = (x - M 0 0) * (x - M 1 1))
    (hy : M 2 3 * M 3 2 = (y - M 2 2) * (y - M 3 3)) :
    (x + y - 1) * (M 0 0 + M 1 1 - x + y - 1) = 0 := by
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 0 2 * M 2 0
      + M 0 3 * M 3 0 = M 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 0) 0
  have h11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 + M 1 2 * M 2 1
      + M 1 3 * M 3 1 = M 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 1) 1
  have h22 : M 2 0 * M 0 2 + M 2 1 * M 1 2 + M 2 2 * M 2 2
      + M 2 3 * M 3 2 = M 2 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 2) 2
  have h33 : M 3 0 * M 0 3 + M 3 1 * M 1 3 + M 3 2 * M 2 3
      + M 3 3 * M 3 3 = M 3 3 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 3) 3
  linear_combination (-(1 : ℝ) / 2) * h00 + (-(1 : ℝ) / 2) * h11
    + ((1 : ℝ) / 2) * h22 + ((1 : ℝ) / 2) * h33 + hx - hy
    + (y + (M 0 0 + M 1 1) / 2 - (M 2 2 + M 3 3) / 2 - 1 / 2) * htr

/-- **THE DICHOTOMY AT THE PAIR (0, 2).**  The same law at the second
opposite pair of the tetrahedron. -/
theorem corner_dichotomy_zero_two {M : Matrix (Fin 4) (Fin 4) ℝ} {x y : ℝ}
    (hidem : M * M = M)
    (htr : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2)
    (hx : M 0 2 * M 2 0 = (x - M 0 0) * (x - M 2 2))
    (hy : M 1 3 * M 3 1 = (y - M 1 1) * (y - M 3 3)) :
    (x + y - 1) * (M 0 0 + M 2 2 - x + y - 1) = 0 := by
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 0 2 * M 2 0
      + M 0 3 * M 3 0 = M 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 0) 0
  have h11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 + M 1 2 * M 2 1
      + M 1 3 * M 3 1 = M 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 1) 1
  have h22 : M 2 0 * M 0 2 + M 2 1 * M 1 2 + M 2 2 * M 2 2
      + M 2 3 * M 3 2 = M 2 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 2) 2
  have h33 : M 3 0 * M 0 3 + M 3 1 * M 1 3 + M 3 2 * M 2 3
      + M 3 3 * M 3 3 = M 3 3 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 3) 3
  linear_combination (-(1 : ℝ) / 2) * h00 + (-(1 : ℝ) / 2) * h22
    + ((1 : ℝ) / 2) * h11 + ((1 : ℝ) / 2) * h33 + hx - hy
    + (y + (M 0 0 + M 2 2) / 2 - (M 1 1 + M 3 3) / 2 - 1 / 2) * htr

/-- **THE DICHOTOMY AT THE PAIR (0, 3).**  The same law at the third
opposite pair of the tetrahedron. -/
theorem corner_dichotomy_zero_three {M : Matrix (Fin 4) (Fin 4) ℝ} {x y : ℝ}
    (hidem : M * M = M)
    (htr : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2)
    (hx : M 0 3 * M 3 0 = (x - M 0 0) * (x - M 3 3))
    (hy : M 1 2 * M 2 1 = (y - M 1 1) * (y - M 2 2)) :
    (x + y - 1) * (M 0 0 + M 3 3 - x + y - 1) = 0 := by
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 0 2 * M 2 0
      + M 0 3 * M 3 0 = M 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 0) 0
  have h11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 + M 1 2 * M 2 1
      + M 1 3 * M 3 1 = M 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 1) 1
  have h22 : M 2 0 * M 0 2 + M 2 1 * M 1 2 + M 2 2 * M 2 2
      + M 2 3 * M 3 2 = M 2 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 2) 2
  have h33 : M 3 0 * M 0 3 + M 3 1 * M 1 3 + M 3 2 * M 2 3
      + M 3 3 * M 3 3 = M 3 3 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 3) 3
  linear_combination (-(1 : ℝ) / 2) * h00 + (-(1 : ℝ) / 2) * h33
    + ((1 : ℝ) / 2) * h11 + ((1 : ℝ) / 2) * h22 + hx - hy
    + (y + (M 0 0 + M 3 3) / 2 - (M 1 1 + M 2 2) / 2 - 1 / 2) * htr

/-! ## Layer 2 — the certificate proof -/

set_option maxHeartbeats 800000 in
/-- **THE CERTIFICATE PROOF.**  The K4 certificate holds.  The six
corner products feed the three opposite-pair dichotomies.  A sum pair
dies on the weight cone.  In the all-tau branch the corner excess
balance collapses to the opposite weight products against a negative
right side. -/
theorem kFourCertificate_holds : KFourCertificate := by
  intro value w01 w02 w03 w12 w13 w23 a01 b01 a02 b02 a03 b03 a12 b12
    a13 b13 a23 b23 M _ hvalue hw01 hw02 hw03 hw12 hw13 hw23 hwsum
    hidem htrace h01a h01b h02a h02b h03a h03b h12a h12b h13a h13b
    h23a h23b _ _ _ _ _ _ _ _ _ _ ha01 hb01 ha02 hb02 ha03 hb03 ha12
    hb12 ha13 hb13 ha23 hb23
  -- the six corner products
  have p01 := corner_product_of_reads ha01 hb01 h01a h01b
  have p02 := corner_product_of_reads ha02 hb02 h02a h02b
  have p03 := corner_product_of_reads ha03 hb03 h03a h03b
  have p12 := corner_product_of_reads ha12 hb12 h12a h12b
  have p13 := corner_product_of_reads ha13 hb13 h13a h13b
  have p23 := corner_product_of_reads ha23 hb23 h23a h23b
  -- the three opposite-pair dichotomies
  have hD1 := corner_dichotomy_zero_one hidem htrace p01 p23
  have hD2 := corner_dichotomy_zero_two hidem htrace p02 p13
  have hD3 := corner_dichotomy_zero_three hidem htrace p03 p12
  -- a sum pair equates two values with a positive weight sum
  rcases mul_eq_zero.mp hD1 with hsum1 | htau1
  · linarith
  rcases mul_eq_zero.mp hD2 with hsum2 | htau2
  · linarith
  rcases mul_eq_zero.mp hD3 with hsum3 | htau3
  · linarith
  -- the all-tau branch: the balance collapses to the weight products
  have hbal := kfour_corner_excess_sum hidem htrace h01a h01b h02a h02b
    h03a h03b h12a h12b h13a h13b h23a h23b ha01 hb01 ha02 hb02 ha03
    hb03 ha12 hb12 ha13 hb13 ha23 hb23
  have hkey : w01 * w23 + w02 * w13 + w03 * w12
      = 2 * value - 3 * value ^ 2 := by
    linear_combination (-(1 : ℝ) / 2) * hbal
      + ((w01 - w23) / 2) * htau1 + ((w02 - w13) / 2) * htau2
      + ((w03 - w12) / 2) * htau3
      + ((3 * value + w12 + w13 + w23) / 2) * htrace
      - ((2 * value - 1) / 2) * hwsum
  linarith [mul_pos hw01 hw23, mul_pos hw02 hw13, mul_pos hw03 hw12,
    sq_nonneg value]

/-! ## Layer 3 — the closure -/

/-- **CLOSURE THREE.**  The dense K4 profile dies at every frame. -/
theorem rankFourKFourClosed_holds : RankFourKFourClosed :=
  rankFourKFourClosed_of_certificate kFourCertificate_holds

end Gtz

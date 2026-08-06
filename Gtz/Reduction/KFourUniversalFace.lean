import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-
# P2: the universal face -- branchless consequences of `lambda_min <= 1`

Mechanization of the matroid lane's rung-11 law P2
(the M(K4) matroid-lane ledger): for a positive real triple of pencil
eigenvalues with minimum at most one,
  `e2 - e3 = lam1 (lam2 + lam3) + lam2 lam3 (1 - lam1) >= 0`   and
  `e3 < e1^2 / 4`,
where `e1, e2, e3` are the elementary symmetric functions.  Both are pure
symmetric-function algebra over an ordered field: no matrices, no branch
split on which eigenvalue is small.  The first is in fact STRICT on
positive triples, and both strict forms are delivered; the ledger's `>= 0`
follows.  These are the first branchless faces of the negation system on
the M(K4) stratum: every tree with `lambda_min(A_T) <= 1` satisfies them.
-/

namespace Gtz

/-- Core case of P2 with the small eigenvalue named first:
`e2 > e3` for a positive triple whose first entry is at most one.  The
rearrangement is `e2 - e3 = lam1 (lam2 + lam3) + lam2 lam3 (1 - lam1)`,
a sum of a positive and a nonnegative term. -/
theorem pairSum_gt_product_of_first_le_one (eigFirst eigSecond eigThird : ℝ)
    (hFirst : 0 < eigFirst) (hSecond : 0 < eigSecond) (hThird : 0 < eigThird)
    (hSmall : eigFirst ≤ 1) :
    eigFirst * eigSecond * eigThird
      < eigFirst * eigSecond + eigFirst * eigThird + eigSecond * eigThird := by
  nlinarith [mul_pos hFirst (add_pos hSecond hThird),
    mul_nonneg (mul_pos hSecond hThird).le (sub_nonneg.mpr hSmall)]

/-- Core case of the P2 cap with the small eigenvalue named first:
`e3 < e1^2 / 4` -- the chain
`lam1 lam2 lam3 <= lam2 lam3 <= ((lam2 + lam3)/2)^2 < (e1/2)^2`. -/
theorem product_lt_quarter_sq_sum_of_first_le_one
    (eigFirst eigSecond eigThird : ℝ)
    (hFirst : 0 < eigFirst) (hSecond : 0 < eigSecond) (hThird : 0 < eigThird)
    (hSmall : eigFirst ≤ 1) :
    eigFirst * eigSecond * eigThird
      < (eigFirst + eigSecond + eigThird) ^ 2 / 4 := by
  nlinarith [sq_nonneg (eigSecond - eigThird), mul_pos hSecond hThird,
    mul_nonneg (mul_pos hSecond hThird).le (sub_nonneg.mpr hSmall),
    mul_pos hFirst (add_pos hSecond hThird), sq_nonneg eigFirst]

/-- **P2, the universal face (strict form).**  A positive pencil
eigenvalue triple with minimum at most one has `e2 > e3`: per tree of the
M(K4) negation system, no branch split needed. -/
theorem universalFace_pairSum_gt_product (eigFirst eigSecond eigThird : ℝ)
    (hFirst : 0 < eigFirst) (hSecond : 0 < eigSecond) (hThird : 0 < eigThird)
    (hMin : min eigFirst (min eigSecond eigThird) ≤ 1) :
    eigFirst * eigSecond * eigThird
      < eigFirst * eigSecond + eigFirst * eigThird + eigSecond * eigThird := by
  rcases min_le_iff.mp hMin with hSmall | hRest
  · exact pairSum_gt_product_of_first_le_one eigFirst eigSecond eigThird
      hFirst hSecond hThird hSmall
  rcases min_le_iff.mp hRest with hSmall | hSmall
  · have hcore := pairSum_gt_product_of_first_le_one eigSecond eigFirst eigThird
      hSecond hFirst hThird hSmall
    nlinarith [hcore]
  · have hcore := pairSum_gt_product_of_first_le_one eigThird eigFirst eigSecond
      hThird hFirst hSecond hSmall
    nlinarith [hcore]

/-- **P2 in the ledger's form**: `e2 - e3 >= 0` under `lambda_min <= 1`. -/
theorem universalFace_pairSum_ge_product (eigFirst eigSecond eigThird : ℝ)
    (hFirst : 0 < eigFirst) (hSecond : 0 < eigSecond) (hThird : 0 < eigThird)
    (hMin : min eigFirst (min eigSecond eigThird) ≤ 1) :
    eigFirst * eigSecond * eigThird
      ≤ eigFirst * eigSecond + eigFirst * eigThird + eigSecond * eigThird :=
  (universalFace_pairSum_gt_product eigFirst eigSecond eigThird
    hFirst hSecond hThird hMin).le

/-- **P2, the determinant cap**: `e3 < e1^2 / 4` under `lambda_min <= 1`. -/
theorem universalFace_product_lt_quarter_sq_trace
    (eigFirst eigSecond eigThird : ℝ)
    (hFirst : 0 < eigFirst) (hSecond : 0 < eigSecond) (hThird : 0 < eigThird)
    (hMin : min eigFirst (min eigSecond eigThird) ≤ 1) :
    eigFirst * eigSecond * eigThird
      < (eigFirst + eigSecond + eigThird) ^ 2 / 4 := by
  rcases min_le_iff.mp hMin with hSmall | hRest
  · exact product_lt_quarter_sq_sum_of_first_le_one eigFirst eigSecond eigThird
      hFirst hSecond hThird hSmall
  rcases min_le_iff.mp hRest with hSmall | hSmall
  · have hcore := product_lt_quarter_sq_sum_of_first_le_one eigSecond eigFirst
      eigThird hSecond hFirst hThird hSmall
    nlinarith [hcore]
  · have hcore := product_lt_quarter_sq_sum_of_first_le_one eigThird eigFirst
      eigSecond hThird hFirst hSecond hSmall
    nlinarith [hcore]

end Gtz

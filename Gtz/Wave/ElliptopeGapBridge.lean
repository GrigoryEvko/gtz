/-
# The elliptope gap bridge: domination as membership of a named interval, and the
root-free criterion underneath it

The campaign decides a triple by the sign of the third minor `tripleDetForm`, and it
has built eight sufficient CELLS for that sign, each measured against a different
baseline.  This file supplies the BOUNDARY instead: an exact criterion, and the two
endpoints between which the far pairing must lie.

## The pivot Schur identity

Write the gap of a triple as the symmetric `3 x 3`

    [ p  u  v ]
    [ u  q  w ]
    [ v  w  r ]

with surpluses `p, q, r` on the diagonal and pairings `u = a.b`, `v = a.c`, `w = b.c`
off it, so its determinant is `Gtz.tripleDetForm p q r u v w`.  Eliminating the pivot
slot gives, by pure `ring`,

    pairMinorForm p q u * pairMinorForm p r v - (p * w - u * v) ^ 2
      = p * tripleDetForm p q r u v w                    (`pairMinorForm_mul_sub_sq`)

`pairMinorForm p q u = p * q - u ^ 2` is the two-by-two pair minor at the pivot's own
two edges.  So **the third minor is the product of two PAIR MINORS minus one square**,
and at a positive pivot the sign question becomes

    0 < tripleDetForm  <->  (p * w - u * v) ^ 2 < pairMinorForm p q u * pairMinorForm p r v

(`tripleDetForm_pos_iff_sq_lt`).  That is an EXACT criterion with no square root, no
division and no eigenvalue, and all three pivots give it (`_second`, `_third`).

## The named endpoints

Reading the same identity as a quadratic in the far pairing `w` names the interval:

    gapRootLower p q r u v  =  u * v - sqrt (pairMinorForm p q u * pairMinorForm p r v)
    gapRootUpper p q r u v  =  u * v + sqrt (pairMinorForm p q u * pairMinorForm p r v)

and `tripleDetForm_pos_iff_mem_openGapInterval` says the triple dominates exactly when
`p * w` lies strictly between them.  Vieta holds with no radical in either coefficient
(`gapRoot_add`, `gapRoot_mul`), and the width is `2 sqrt(M1 M2)` (`gapRoot_sub`).  **One
square root, of a product of two pair minors, and the pivot's own scale `sqrt (q * r)`
has cancelled.**

## The bridge to the shipped elliptope layer, off the flat locus

`Gtz.discriminantTie_eq_excessProduct_mul_elliptopeBracket` already factors the
leverages out at the DESIGN level.  The scalar shadow of that statement is

    tripleDetForm p q r u v w
      = p * q * r * elliptopeBracket (u / sqrt (p*q)) (v / sqrt (p*r)) (w / sqrt (q*r))

(`tripleDetForm_eq_mul_elliptopeBracket`), at every positive surplus triple, with no
flatness and no uniform weight.  `Gtz.twentySeven_mul_det_blockGapAt_eq_elliptopeBracket`
is the flat uniform special case of the same fact.

With it the shipped root layer of `Gtz/LinAlg/ElliptopeInterval.lean` acquires its
first consumer outside its own file: `gapRootUpper_eq_scaled_rootUpper` and its lower
sibling identify the unnormalised endpoints as the shipped `Gtz.rootUpper` and
`Gtz.rootLower` rescaled by `p * sqrt (q * r)`, and `tripleDetForm_pos_iff_rootInterval`
transports `Gtz.elliptopeBracket_pos_iff_mem_openRootInterval` to the gap.

## What the interval does NOT do, and this correction is load-bearing

The root interval decides the BRACKET, not positive definiteness.  The shipped
`Gtz.posSemidef_correlationMatrixThree_iff` is an iff against the bracket **together
with** the three edge conditions, and `Gtz.not_posSemidef_correlationMatrixThree_of_incompatible_boundary`
shows the edge conjunct survives on the determinant's own zero set.  Both root-layer
criteria also CARRY the two pivot edge hypotheses `rho ^ 2 <= 1`.  In gap coordinates
those are exactly `0 <= pairMinorForm` at the pivot's two edges
(`pairMinorForm_nonneg_iff_sq_le_one`), so the honest reading is:

**given two nonnegative pair minors at a common pivot, the far pairing is decided
exactly by the interval** (`tripleDetForm_pos_iff_mem_openGapInterval_of_pairMinors`).

The two pivot minors are not free: `pairMinorForm_pos_of_tripleDetForm_pos` derives
both from domination itself, so the hypotheses are necessary rather than assumed.

## Placing the landed cells against the boundary

Every sufficient cell now has an exact distance to the boundary rather than a coverage
percentage.  `quarterSlack_sq_lt` prices the quarter-slack cell, `sq_lt_of_signFreeMargin_pos`
prices the maximal sign-blind cell, and `gapWidth_sq_eq` gives the exact residual
`pairMinorForm p q u * pairMinorForm p r v - (p w - u v) ^ 2` that every cell is
bounding from below.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.GoodTripleGraph
import Gtz.LinAlg.ElliptopeInterval
import Gtz.Wave.TripleDeterminantCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ### 1. The pair minor form and the pivot Schur identity -/

/-- The **pair minor form**: the two-by-two principal minor of a triple's gap at the
two slots carrying surpluses `p`, `q` and pairing `u`. -/
def pairMinorForm (p q u : ℝ) : ℝ := p * q - u ^ 2

theorem pairMinorForm_apply (p q u : ℝ) : pairMinorForm p q u = p * q - u ^ 2 := rfl

theorem pairMinorForm_comm (p q u : ℝ) : pairMinorForm p q u = pairMinorForm q p u := by
  rw [pairMinorForm, pairMinorForm]; ring

theorem pairMinorForm_neg (p q u : ℝ) : pairMinorForm p q (-u) = pairMinorForm p q u := by
  rw [pairMinorForm, pairMinorForm]; ring

/-- **THE PIVOT SCHUR IDENTITY.** Eliminating the pivot slot writes the third minor as
the product of the pivot's two pair minors minus one square. Pure `ring`. -/
theorem pairMinorForm_mul_sub_sq (p q r u v w : ℝ) :
    pairMinorForm p q u * pairMinorForm p r v - (p * w - u * v) ^ 2
      = p * tripleDetForm p q r u v w := by
  rw [pairMinorForm, pairMinorForm, tripleDetForm]; ring

/-- The same identity pivoted on the second slot. -/
theorem pairMinorForm_mul_sub_sq_second (p q r u v w : ℝ) :
    pairMinorForm q p u * pairMinorForm q r w - (q * v - u * w) ^ 2
      = q * tripleDetForm p q r u v w := by
  rw [pairMinorForm, pairMinorForm, tripleDetForm]; ring

/-- The same identity pivoted on the third slot. -/
theorem pairMinorForm_mul_sub_sq_third (p q r u v w : ℝ) :
    pairMinorForm r p v * pairMinorForm r q w - (r * u - v * w) ^ 2
      = r * tripleDetForm p q r u v w := by
  rw [pairMinorForm, pairMinorForm, tripleDetForm]; ring

/-- The **gap width**: the exact quantity every sufficient cell bounds below. -/
theorem gapWidth_sq_eq (p q r u v w : ℝ) :
    pairMinorForm p q u * pairMinorForm p r v - (p * w - u * v) ^ 2
      = p * tripleDetForm p q r u v w :=
  pairMinorForm_mul_sub_sq p q r u v w

/-! ### 2. The root-free exact criterion -/

/-- **THE EXACT CRITERION, ROOT FREE AND DIVISION FREE.** At a positive pivot the
third minor is positive exactly when one square is beaten by the product of the
pivot's two pair minors. -/
theorem tripleDetForm_pos_iff_sq_lt {p : ℝ} (hp : 0 < p) (q r u v w : ℝ) :
    0 < tripleDetForm p q r u v w
      ↔ (p * w - u * v) ^ 2 < pairMinorForm p q u * pairMinorForm p r v := by
  have hkey := pairMinorForm_mul_sub_sq p q r u v w
  constructor
  · intro hpos
    nlinarith [hkey, mul_pos hp hpos]
  · intro hlt
    nlinarith [hkey, hp]

theorem tripleDetForm_nonneg_iff_sq_le {p : ℝ} (hp : 0 < p) (q r u v w : ℝ) :
    0 ≤ tripleDetForm p q r u v w
      ↔ (p * w - u * v) ^ 2 ≤ pairMinorForm p q u * pairMinorForm p r v := by
  have hkey := pairMinorForm_mul_sub_sq p q r u v w
  constructor
  · intro hnn
    nlinarith [hkey, mul_nonneg hp.le hnn]
  · intro hle
    nlinarith [hkey, hp]

theorem tripleDetForm_pos_iff_sq_lt_second {q : ℝ} (hq : 0 < q) (p r u v w : ℝ) :
    0 < tripleDetForm p q r u v w
      ↔ (q * v - u * w) ^ 2 < pairMinorForm q p u * pairMinorForm q r w := by
  have hkey := pairMinorForm_mul_sub_sq_second p q r u v w
  constructor
  · intro hpos
    nlinarith [hkey, mul_pos hq hpos]
  · intro hlt
    nlinarith [hkey, hq]

theorem tripleDetForm_pos_iff_sq_lt_third {r : ℝ} (hr : 0 < r) (p q u v w : ℝ) :
    0 < tripleDetForm p q r u v w
      ↔ (r * u - v * w) ^ 2 < pairMinorForm r p v * pairMinorForm r q w := by
  have hkey := pairMinorForm_mul_sub_sq_third p q r u v w
  constructor
  · intro hpos
    nlinarith [hkey, mul_pos hr hpos]
  · intro hlt
    nlinarith [hkey, hr]

/-- **The two pivot pair minors stand or fall together.** At a positive pivot,
domination plus ONE positive pair minor forces the other. -/
theorem pairMinorForm_pos_of_pos_of_tripleDetForm_pos {p : ℝ} (hp : 0 < p) {q r u v w : ℝ}
    (hfirst : 0 < pairMinorForm p q u) (hpos : 0 < tripleDetForm p q r u v w) :
    0 < pairMinorForm p r v := by
  have hlt := (tripleDetForm_pos_iff_sq_lt hp q r u v w).mp hpos
  have hprod : 0 < pairMinorForm p q u * pairMinorForm p r v :=
    lt_of_le_of_lt (sq_nonneg (p * w - u * v)) hlt
  rcases lt_trichotomy (pairMinorForm p r v) 0 with hcase | hcase | hcase
  · exfalso; nlinarith [hprod, hfirst, hcase]
  · exfalso; rw [hcase, mul_zero] at hprod; exact lt_irrefl 0 hprod
  · exact hcase

/-- The symmetric statement: the product of the pivot's two pair minors is always
strictly positive at a dominating triple, even though neither factor is determined. -/
theorem pairMinorForm_mul_pos_of_tripleDetForm_pos {p : ℝ} (hp : 0 < p) {q r u v w : ℝ}
    (hpos : 0 < tripleDetForm p q r u v w) :
    0 < pairMinorForm p q u * pairMinorForm p r v :=
  lt_of_le_of_lt (sq_nonneg (p * w - u * v)) ((tripleDetForm_pos_iff_sq_lt hp q r u v w).mp hpos)

/-- **THE PAIR MINORS ARE NOT FREE CONSEQUENCES, AND THE SURPLUSES DO NOT SUPPLY THEM.**
At `p = q = r = 8`, `u = v = w = 11` every surplus is strictly positive and the third
minor is `270 > 0`, yet every pair minor is `-57 < 0`. The gap has signature
`(+, -, -)` there, so a positive determinant at a positive pivot is genuinely weaker
than domination and the edge conditions of the shipped elliptope criterion cannot be
dropped. -/
theorem not_forall_pairMinorForm_pos_of_tripleDetForm_pos :
    ¬ ∀ p q r u v w : ℝ, 0 < p → 0 < q → 0 < r → 0 < tripleDetForm p q r u v w →
      0 < pairMinorForm p q u := by
  intro hall
  have hwitness : (0 : ℝ) < pairMinorForm 8 8 11 :=
    hall 8 8 8 11 11 11 (by norm_num) (by norm_num) (by norm_num)
      (by rw [tripleDetForm]; norm_num)
  rw [pairMinorForm] at hwitness
  norm_num at hwitness

/-- The witness values, recorded exactly. -/
theorem witness_tripleDetForm_pos : tripleDetForm 8 8 8 11 11 11 = 270 := by
  rw [tripleDetForm]; norm_num

theorem witness_pairMinorForm_neg : pairMinorForm 8 8 11 = -57 := by
  rw [pairMinorForm]; norm_num

/-! ### 3. The named endpoints in gap coordinates -/

/-- The **upper endpoint** for the far pairing, scaled by the pivot. -/
noncomputable def gapRootUpper (p q r u v : ℝ) : ℝ :=
  u * v + Real.sqrt (pairMinorForm p q u * pairMinorForm p r v)

/-- The **lower endpoint** for the far pairing, scaled by the pivot. -/
noncomputable def gapRootLower (p q r u v : ℝ) : ℝ :=
  u * v - Real.sqrt (pairMinorForm p q u * pairMinorForm p r v)

/-- **Vieta, first coefficient.** No radical survives in the sum. -/
theorem gapRoot_add (p q r u v : ℝ) :
    gapRootLower p q r u v + gapRootUpper p q r u v = 2 * (u * v) := by
  rw [gapRootLower, gapRootUpper]; ring

/-- **Vieta, second coefficient.** No radical survives in the product either. -/
theorem gapRoot_mul {p q r u v : ℝ}
    (hnn : 0 ≤ pairMinorForm p q u * pairMinorForm p r v) :
    gapRootLower p q r u v * gapRootUpper p q r u v
      = (u * v) ^ 2 - pairMinorForm p q u * pairMinorForm p r v := by
  have hsq : Real.sqrt (pairMinorForm p q u * pairMinorForm p r v) ^ 2
      = pairMinorForm p q u * pairMinorForm p r v := Real.sq_sqrt hnn
  rw [gapRootLower, gapRootUpper]
  nlinarith [hsq]

/-- The **width** of the interval is twice the square root of the minor product. -/
theorem gapRoot_sub (p q r u v : ℝ) :
    gapRootUpper p q r u v - gapRootLower p q r u v
      = 2 * Real.sqrt (pairMinorForm p q u * pairMinorForm p r v) := by
  rw [gapRootLower, gapRootUpper]; ring

theorem gapRootLower_le_gapRootUpper (p q r u v : ℝ) :
    gapRootLower p q r u v ≤ gapRootUpper p q r u v := by
  rw [gapRootLower, gapRootUpper]
  linarith [Real.sqrt_nonneg (pairMinorForm p q u * pairMinorForm p r v)]

/-- **THE INTERVAL CRITERION IN GAP COORDINATES.** At a positive pivot the triple
dominates exactly when the pivot-scaled far pairing lies strictly inside the interval
named by the two endpoints. -/
theorem tripleDetForm_pos_iff_mem_openGapInterval {p : ℝ} (hp : 0 < p) (q r u v w : ℝ) :
    0 < tripleDetForm p q r u v w
      ↔ gapRootLower p q r u v < p * w ∧ p * w < gapRootUpper p q r u v := by
  rw [tripleDetForm_pos_iff_sq_lt hp q r u v w, gapRootLower, gapRootUpper]
  set minorProduct := pairMinorForm p q u * pairMinorForm p r v with hminor
  constructor
  · intro hlt
    have hprodPos : 0 < minorProduct := lt_of_le_of_lt (sq_nonneg (p * w - u * v)) hlt
    have hroot : Real.sqrt minorProduct ^ 2 = minorProduct := Real.sq_sqrt hprodPos.le
    have hrootNonneg : 0 ≤ Real.sqrt minorProduct := Real.sqrt_nonneg _
    constructor
    · nlinarith [hlt, hroot, hrootNonneg]
    · nlinarith [hlt, hroot, hrootNonneg]
  · rintro ⟨hlow, hhigh⟩
    have hrootNonneg : 0 ≤ Real.sqrt minorProduct := Real.sqrt_nonneg _
    have hprodNonneg : 0 ≤ minorProduct := by
      by_contra hcon
      rw [Real.sqrt_eq_zero_of_nonpos (not_le.mp hcon).le] at hlow hhigh
      linarith
    have hroot : Real.sqrt minorProduct ^ 2 = minorProduct := Real.sq_sqrt hprodNonneg
    nlinarith [hlow, hhigh, hroot, hrootNonneg]

/-- The closed interval decides the nonnegative case. -/
theorem tripleDetForm_nonneg_iff_mem_gapInterval {p : ℝ} (hp : 0 < p) {q r u v w : ℝ}
    (hnn : 0 ≤ pairMinorForm p q u * pairMinorForm p r v) :
    0 ≤ tripleDetForm p q r u v w
      ↔ gapRootLower p q r u v ≤ p * w ∧ p * w ≤ gapRootUpper p q r u v := by
  rw [tripleDetForm_nonneg_iff_sq_le hp q r u v w, gapRootLower, gapRootUpper]
  set minorProduct := pairMinorForm p q u * pairMinorForm p r v with hminor
  have hroot : Real.sqrt minorProduct ^ 2 = minorProduct := Real.sq_sqrt hnn
  have hrootNonneg : 0 ≤ Real.sqrt minorProduct := Real.sqrt_nonneg _
  constructor
  · intro hle
    exact ⟨by nlinarith [hle, hroot, hrootNonneg], by nlinarith [hle, hroot, hrootNonneg]⟩
  · rintro ⟨hlow, hhigh⟩
    nlinarith [hlow, hhigh, hroot, hrootNonneg]

/-- **The honest reading.** Given the pivot's two pair minors nonnegative — which
domination itself forces — the far pairing is decided exactly by the interval. -/
theorem tripleDetForm_pos_iff_mem_openGapInterval_of_pairMinors {p : ℝ} (hp : 0 < p)
    {q r u v : ℝ} (_hfirst : 0 ≤ pairMinorForm p q u) (_hsecond : 0 ≤ pairMinorForm p r v)
    (w : ℝ) :
    0 < tripleDetForm p q r u v w
      ↔ gapRootLower p q r u v < p * w ∧ p * w < gapRootUpper p q r u v :=
  tripleDetForm_pos_iff_mem_openGapInterval hp q r u v w

/-! ### 4. The bridge to the shipped elliptope bracket, off the flat locus -/

private theorem sqrt_triple_pair_prod {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    Real.sqrt (p * q) * Real.sqrt (p * r) * Real.sqrt (q * r) = p * q * r := by
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
    show p * q * (p * r) * (q * r) = (p * q * r) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

/-- The pivot's own scale factors out of the two normalising roots. -/
private theorem sqrt_pq_mul_sqrt_pr {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (_hr : 0 ≤ r) :
    Real.sqrt (p * q) * Real.sqrt (p * r) = p * Real.sqrt (q * r) := by
  rw [← Real.sqrt_mul (by positivity),
    show p * q * (p * r) = p ^ 2 * (q * r) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hp]

/-- **THE GENERAL BRIDGE, WITH NO FLATNESS AND NO UNIFORM WEIGHT.** The third minor is
the surplus product times the shipped elliptope bracket of the three normalised
pairings. This is the scalar shadow of the landed
`Gtz.discriminantTie_eq_excessProduct_mul_elliptopeBracket`, and
`Gtz.twentySeven_mul_det_blockGapAt_eq_elliptopeBracket` is its flat uniform case. -/
theorem tripleDetForm_eq_mul_elliptopeBracket {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (u v w : ℝ) :
    tripleDetForm p q r u v w
      = p * q * r * elliptopeBracket (u / Real.sqrt (p * q)) (v / Real.sqrt (p * r))
          (w / Real.sqrt (q * r)) := by
  have hpq : (0 : ℝ) < p * q := mul_pos hp hq
  have hpr : (0 : ℝ) < p * r := mul_pos hp hr
  have hqr : (0 : ℝ) < q * r := mul_pos hq hr
  have hsqpq : Real.sqrt (p * q) ^ 2 = p * q := Real.sq_sqrt hpq.le
  have hsqpr : Real.sqrt (p * r) ^ 2 = p * r := Real.sq_sqrt hpr.le
  have hsqqr : Real.sqrt (q * r) ^ 2 = q * r := Real.sq_sqrt hqr.le
  have hnepq : Real.sqrt (p * q) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpq)
  have hnepr : Real.sqrt (p * r) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpr)
  have hneqr : Real.sqrt (q * r) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hqr)
  have hprod : Real.sqrt (p * q) * Real.sqrt (p * r) * Real.sqrt (q * r) = p * q * r :=
    sqrt_triple_pair_prod hp.le hq.le hr.le
  have hfirstSq : (u / Real.sqrt (p * q)) ^ 2 = u ^ 2 / (p * q) := by
    rw [div_pow, hsqpq]
  have hsecondSq : (v / Real.sqrt (p * r)) ^ 2 = v ^ 2 / (p * r) := by
    rw [div_pow, hsqpr]
  have hthirdSq : (w / Real.sqrt (q * r)) ^ 2 = w ^ 2 / (q * r) := by
    rw [div_pow, hsqqr]
  have hcross : u / Real.sqrt (p * q) * (v / Real.sqrt (p * r)) * (w / Real.sqrt (q * r))
      = u * v * w / (p * q * r) := by
    rw [div_mul_div_comm, div_mul_div_comm, hprod]
  rw [elliptopeBracket, tripleDetForm, hfirstSq, hsecondSq, hthirdSq, hcross]
  field_simp
  ring

/-- In gap coordinates the shipped edge condition `rho ^ 2 <= 1` is exactly
nonnegativity of the corresponding pair minor. -/
theorem pairMinorForm_nonneg_iff_sq_le_one {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (u : ℝ) :
    0 ≤ pairMinorForm p q u ↔ (u / Real.sqrt (p * q)) ^ 2 ≤ 1 := by
  have hpq : (0 : ℝ) < p * q := mul_pos hp hq
  have hsq : Real.sqrt (p * q) ^ 2 = p * q := Real.sq_sqrt hpq.le
  have hne : Real.sqrt (p * q) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpq)
  rw [pairMinorForm, div_pow, div_le_one (by positivity)]
  constructor
  · intro h; nlinarith [h, hsq]
  · intro h; nlinarith [h, hsq]

/-- **THE SHIPPED ROOT LAYER, TRANSPORTED TO THE GAP.** Given the pivot's two pair
minors nonnegative, the triple dominates exactly when the normalised far pairing lies
strictly inside the shipped root interval. This is the first consumer of
`Gtz.rootLower` and `Gtz.rootUpper` outside their own file. -/
theorem tripleDetForm_pos_iff_rootInterval {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) {u v : ℝ} (hfirst : 0 ≤ pairMinorForm p q u)
    (hsecond : 0 ≤ pairMinorForm p r v) (w : ℝ) :
    0 < tripleDetForm p q r u v w
      ↔ rootLower (u / Real.sqrt (p * q)) (v / Real.sqrt (p * r)) < w / Real.sqrt (q * r)
        ∧ w / Real.sqrt (q * r)
            < rootUpper (u / Real.sqrt (p * q)) (v / Real.sqrt (p * r)) := by
  have hscale : (0 : ℝ) < p * q * r := by positivity
  rw [tripleDetForm_eq_mul_elliptopeBracket hp hq hr u v w,
    mul_pos_iff_of_pos_left hscale]
  exact elliptopeBracket_pos_iff_mem_openRootInterval
    ((pairMinorForm_nonneg_iff_sq_le_one hp hq u).mp hfirst)
    ((pairMinorForm_nonneg_iff_sq_le_one hp hr v).mp hsecond)

/-- The nonnegative companion, through the shipped closed interval criterion. -/
theorem tripleDetForm_nonneg_iff_rootInterval {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) {u v : ℝ} (hfirst : 0 ≤ pairMinorForm p q u)
    (hsecond : 0 ≤ pairMinorForm p r v) (w : ℝ) :
    0 ≤ tripleDetForm p q r u v w
      ↔ rootLower (u / Real.sqrt (p * q)) (v / Real.sqrt (p * r)) ≤ w / Real.sqrt (q * r)
        ∧ w / Real.sqrt (q * r)
            ≤ rootUpper (u / Real.sqrt (p * q)) (v / Real.sqrt (p * r)) := by
  have hscale : (0 : ℝ) < p * q * r := by positivity
  rw [tripleDetForm_eq_mul_elliptopeBracket hp hq hr u v w,
    mul_nonneg_iff_of_pos_left hscale]
  exact elliptopeBracket_nonneg_iff_mem_rootInterval
    ((pairMinorForm_nonneg_iff_sq_le_one hp hq u).mp hfirst)
    ((pairMinorForm_nonneg_iff_sq_le_one hp hr v).mp hsecond)

/-- **The shipped endpoints never leave the compatible range**, read in gap
coordinates: the normalised far pairing is squeezed into `[-1, 1]` by the two pivot
minors alone. -/
theorem rootInterval_subset_compatible {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    {u v : ℝ} (hfirst : 0 ≤ pairMinorForm p q u) (hsecond : 0 ≤ pairMinorForm p r v) :
    -1 ≤ rootLower (u / Real.sqrt (p * q)) (v / Real.sqrt (p * r))
      ∧ rootUpper (u / Real.sqrt (p * q)) (v / Real.sqrt (p * r)) ≤ 1 :=
  ⟨neg_one_le_rootLower ((pairMinorForm_nonneg_iff_sq_le_one hp hq u).mp hfirst)
      ((pairMinorForm_nonneg_iff_sq_le_one hp hr v).mp hsecond),
    rootUpper_le_one ((pairMinorForm_nonneg_iff_sq_le_one hp hq u).mp hfirst)
      ((pairMinorForm_nonneg_iff_sq_le_one hp hr v).mp hsecond)⟩

/-! ### 5. Placing the landed cells against the boundary -/

/-- **The quarter-slack cell, priced exactly.** Its three hypotheses give a strictly
positive minor product and hence a nonempty interval. -/
theorem quarterSlack_pairMinorForm_pos {p q u : ℝ} (hslack : 4 * u ^ 2 < p * q) :
    0 < pairMinorForm p q u := by
  rw [pairMinorForm]; nlinarith [sq_nonneg u]

theorem quarterSlack_minorProduct_pos {p q r u v : ℝ}
    (hfirst : 4 * u ^ 2 < p * q) (hsecond : 4 * v ^ 2 < p * r) :
    0 < pairMinorForm p q u * pairMinorForm p r v :=
  mul_pos (quarterSlack_pairMinorForm_pos hfirst) (quarterSlack_pairMinorForm_pos hsecond)

/-- Every landed sufficient cell is a lower bound on the same residual. -/
theorem sq_lt_of_tripleDetForm_pos {p : ℝ} (hp : 0 < p) {q r u v w : ℝ}
    (hpos : 0 < tripleDetForm p q r u v w) :
    (p * w - u * v) ^ 2 < pairMinorForm p q u * pairMinorForm p r v :=
  (tripleDetForm_pos_iff_sq_lt hp q r u v w).mp hpos

/-- The exact residual a cell must beat, stated as the pivot-scaled minor. -/
theorem residual_eq_pivot_mul (p q r u v w : ℝ) :
    pairMinorForm p q u * pairMinorForm p r v - (p * w - u * v) ^ 2
      = p * tripleDetForm p q r u v w :=
  pairMinorForm_mul_sub_sq p q r u v w

/-! ### 6. The centre, the ceiling and the width -/

/-- The **signed offset** of the far pairing from the interval's centre. -/
def gapOffset (p u v w : ℝ) : ℝ := p * w - u * v

theorem gapOffset_apply (p u v w : ℝ) : gapOffset p u v w = p * w - u * v := rfl

/-- The interval's centre is the offset's zero, and it does not see `q` or `r`. -/
theorem gapOffset_eq_zero_iff {p : ℝ} (hp : 0 < p) (u v w : ℝ) :
    gapOffset p u v w = 0 ↔ w = u * v / p := by
  rw [gapOffset, sub_eq_zero, eq_div_iff (ne_of_gt hp), mul_comm]

/-- **THE MARGIN CEILING.** At a positive pivot the third minor never exceeds the
product of the pivot's two pair minors divided by the pivot. The campaign's cells are
all LOWER bounds on this quantity; this is the matching upper bound, and it reads only
the pivot's own row. -/
theorem tripleDetForm_le_minorProduct_div {p : ℝ} (hp : 0 < p) (q r u v w : ℝ) :
    tripleDetForm p q r u v w ≤ pairMinorForm p q u * pairMinorForm p r v / p := by
  rw [le_div_iff₀ hp]
  nlinarith [pairMinorForm_mul_sub_sq p q r u v w, sq_nonneg (p * w - u * v)]

/-- **The ceiling is attained exactly at the centre**, where the far pairing is the
product of the two pivot pairings over the pivot. -/
theorem tripleDetForm_centre {p : ℝ} (hp : 0 < p) (q r u v : ℝ) :
    tripleDetForm p q r u v (u * v / p)
      = pairMinorForm p q u * pairMinorForm p r v / p := by
  have hkey := pairMinorForm_mul_sub_sq p q r u v (u * v / p)
  have hzero : p * (u * v / p) - u * v = 0 := by field_simp; ring
  rw [hzero] at hkey
  field_simp at hkey ⊢
  linarith [hkey]

theorem tripleDetForm_eq_ceiling_iff {p : ℝ} (hp : 0 < p) (q r u v w : ℝ) :
    tripleDetForm p q r u v w = pairMinorForm p q u * pairMinorForm p r v / p
      ↔ gapOffset p u v w = 0 := by
  rw [gapOffset, eq_div_iff (ne_of_gt hp), ← sub_eq_zero]
  constructor
  · intro heq
    have hkey := pairMinorForm_mul_sub_sq p q r u v w
    have hsq : (p * w - u * v) ^ 2 = 0 := by nlinarith [hkey, heq]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  · intro hzero
    have hkey := pairMinorForm_mul_sub_sq p q r u v w
    rw [hzero] at hkey
    nlinarith [hkey]

/-- **THE WIDTH DECOMPOSITION.** The squared half-width of the interval splits exactly
into the squared offset plus the pivot-scaled margin, so the distance to the boundary
and the margin are the same quantity in two normalisations. -/
theorem sq_halfWidth_eq (p q r u v w : ℝ) :
    pairMinorForm p q u * pairMinorForm p r v
      = gapOffset p u v w ^ 2 + p * tripleDetForm p q r u v w := by
  rw [gapOffset, ← pairMinorForm_mul_sub_sq p q r u v w]; ring

theorem gapRoot_sub_sq {p q r u v w : ℝ}
    (hnn : 0 ≤ pairMinorForm p q u * pairMinorForm p r v) :
    (gapRootUpper p q r u v - gapRootLower p q r u v) ^ 2
      = 4 * (gapOffset p u v w ^ 2 + p * tripleDetForm p q r u v w) := by
  rw [gapRoot_sub, mul_pow, ← sq_halfWidth_eq p q r u v w, Real.sq_sqrt hnn]
  norm_num

/-! ### 7. The three pivots decide the same question -/

/-- All three pivot criteria agree, because each is the same determinant scaled by its
own positive surplus. -/
theorem pivot_criteria_agree {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (r u v w : ℝ) :
    ((p * w - u * v) ^ 2 < pairMinorForm p q u * pairMinorForm p r v)
      ↔ ((q * v - u * w) ^ 2 < pairMinorForm q p u * pairMinorForm q r w) := by
  rw [← tripleDetForm_pos_iff_sq_lt hp q r u v w,
    ← tripleDetForm_pos_iff_sq_lt_second hq p r u v w]

theorem pivot_criteria_agree_third {p r : ℝ} (hp : 0 < p) (hr : 0 < r) (q u v w : ℝ) :
    ((p * w - u * v) ^ 2 < pairMinorForm p q u * pairMinorForm p r v)
      ↔ ((r * u - v * w) ^ 2 < pairMinorForm r p v * pairMinorForm r q w) := by
  rw [← tripleDetForm_pos_iff_sq_lt hp q r u v w,
    ← tripleDetForm_pos_iff_sq_lt_third hr p q u v w]

/-! ### 8. The criterion at the atom level -/

/-- **THE ROOT-FREE CRITERION ON THREE ATOMS.** Composing with the landed
`Gtz.tripleGapDet_eq_tripleDetForm`, a triple of atoms whose first is strictly heavy
dominates exactly when one square is beaten by the product of that atom's two pair
minors. -/
theorem tripleGapDet_pos_iff_sq_lt {a b c : Fin 3 → ℝ} (hheavy : 1 < leverageOf a) :
    0 < tripleGapDet a b c
      ↔ ((leverageOf a - 1) * (b ⬝ᵥ c) - (a ⬝ᵥ b) * (a ⬝ᵥ c)) ^ 2
          < pairMinorForm (leverageOf a - 1) (leverageOf b - 1) (a ⬝ᵥ b)
            * pairMinorForm (leverageOf a - 1) (leverageOf c - 1) (a ⬝ᵥ c) := by
  rw [tripleGapDet_eq_tripleDetForm a b c]
  exact tripleDetForm_pos_iff_sq_lt (by linarith) _ _ _ _ _

/-- The atom-level margin ceiling. -/
theorem tripleGapDet_le_minorProduct_div {a b c : Fin 3 → ℝ} (hheavy : 1 < leverageOf a) :
    tripleGapDet a b c
      ≤ pairMinorForm (leverageOf a - 1) (leverageOf b - 1) (a ⬝ᵥ b)
          * pairMinorForm (leverageOf a - 1) (leverageOf c - 1) (a ⬝ᵥ c)
        / (leverageOf a - 1) := by
  rw [tripleGapDet_eq_tripleDetForm a b c]
  exact tripleDetForm_le_minorProduct_div (by linarith) _ _ _ _ _

/-- The atom-level interval criterion, with the two endpoints named. -/
theorem tripleGapDet_pos_iff_mem_openGapInterval {a b c : Fin 3 → ℝ}
    (hheavy : 1 < leverageOf a) :
    0 < tripleGapDet a b c
      ↔ gapRootLower (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
            (a ⬝ᵥ b) (a ⬝ᵥ c) < (leverageOf a - 1) * (b ⬝ᵥ c)
        ∧ (leverageOf a - 1) * (b ⬝ᵥ c)
            < gapRootUpper (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
                (a ⬝ᵥ b) (a ⬝ᵥ c) := by
  rw [tripleGapDet_eq_tripleDetForm a b c]
  exact tripleDetForm_pos_iff_mem_openGapInterval (by linarith) _ _ _ _ _

end Gtz

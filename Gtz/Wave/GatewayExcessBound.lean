/-
# The gateway target is a theorem on the box

`Gtz.gateway_no_handelman_certificate` proves that the gateway target

  **`a_1 + a_2 + a_3 <= 1`**

carries NO certificate of Handelman type over the box generators, at any
degree.  Five rounds of linear programming had searched for one.  This module
proves the target instead, by an argument no such certificate can express: a
case split on which of the three atoms carries more excess than slack.

## The two coordinates that make it work

Write `c_i = 1 - a_i - t_i` for the weight cap slack and `x_i = a_i + t_i`, so
that `x_i + c_i = 1`.  Divide by the excess and set

  `Y_i = x_i / a_i` ,   `Z_i = c_i / a_i` ,   so that   `Y_i + Z_i = 1 / a_i` .

In these coordinates BOTH determinant conditions become symmetric-function
inequalities and the target becomes a sum of reciprocals
(`Gtz.reform.py` in the lane's scratch, and the three identities are checked in
Lean by `ring` below):

  `0 <= detM`   iff   `Y_1 Y_2 Y_3 >= Y_1 + Y_2 + Y_3 + 2`   iff
    `sum_i a_i / (a_i + x_i) <= 1` ,
  `0 <= detIM`  iff   `Z_1 Z_2 Z_3 >= Z_1 + Z_2 + Z_3 - 2` ,
  `target`      iff   `sum_i 1 / (Y_i + Z_i) <= 1` .

The pair constraint `a_i a_j <= c_i c_j` says `Z_i Z_j >= 1`, so **at most one
index has `Z_i < 1`**, that is, at most one atom carries more excess than cap
slack.  That is the case split.

## The light case is the second determinant, exactly

If `a_i <= c_i` at every index then `a_i + x_i <= 1`, so `a_i <= a_i/(a_i+x_i)`,
and the second determinant condition is literally
`sum a_i/(a_i+x_i) <= 1` (`Gtz.gateway_excess_le_one_of_light`).  One
determinant closes the case with nothing else.

## The heavy case is one scalar lemma

With `a_1 > c_1` put `z = Z_1 < 1`, `p_i = t_i / a_i`, and
`mu = Z_1 Z_2 - 1`, `nu = Z_1 Z_3 - 1`, both nonnegative by the two pair
constraints at the first index.  Then the first determinant condition is
exactly `mu * nu >= (1 - z)^2`, the second is
`p_2 p_3 + p_1 (p_2 + p_3 + p_2 p_3) >= 4`, and the target clears its
denominators into `Gtz.gatewayHeavy_core`.  That lemma splits once more on
`p_2 p_3 >= 4`:

* above four, the Cauchy-Schwarz bound `A B >= (z sqrt(p_2p_3) + sqrt(mu nu))^2`
  gives `A B >= (1+z)^2` outright and the target follows from the first factor
  alone;
* below four, `sqrt(p_2p_3) >= p_2p_3/2`, so `A B >= z p_2p_3 + (1-z)^2`, the
  three remaining terms collapse to `p_1 (z (p_2p_3+p_2+p_3) + 4(1-z))`, and the
  second determinant condition finishes through
  `z w + 4(1-z) >= z^2 w` for `w >= 0`, `z <= 1`.

Both square roots leave through squares, so the whole proof is polynomial.

## What this does NOT settle, and the measurement that says so

The box is the lane's own object, and `0 <= branchDetComplement` is one of its
GENERATORS.  It is not a consequence of the design-level system.  Write `M` for
the weighted outside Gram, so `M_ii = x_i`, `M_ij^2 = t_i t_j <g_i,g_j>^2`, and
Parseval gives `0 <= M <= 1` outright.  On that system
`branchDetComplement` reaches `-0.018519`, at the point

  `a = (0.08334, 0.08332, 0.83333)` , `t = (0.49993, 0.50004, 0)` ,
  `r = (0.41665, -0.26354, 0.26351)` ,

which satisfies every design-level constraint and has `sum a = 1.000000`.  So
this module closes the box, and the design-level `E1` needs its own argument.

[MEASURED.  The target is tight: the lane's two-parameter family attains
`sum a = 1` exactly, and so do the symmetric point `a = t = (1/3,1/3,1/3)` and
the true-system optimum, at which all three pair minors vanish and both true
determinants are zero.  Maximising `sum a` over the design-level system with a
weight floor `t_i >= tau` returns exactly `1 - tau` at `tau = 0` and
`tau = 0.05`.  A sharpening to `sum a <= 1 - min t` is FALSE on the box: the
symmetric point gives `sum a + min t = 4/3`.]
-/
import Gtz.Wave.GatewayCertificateObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace Gtz

/-! ## 1. One pair caps two excesses

Nothing but the pair constraint and the two weight caps.  This also disposes of
every degenerate index, because an atom of zero excess leaves a pair behind. -/

/-- **A PAIR CONSTRAINT CAPS ITS OWN TWO EXCESSES.**  Two atoms whose excess
product is under their slack product carry at most the whole budget between
them. -/
theorem excess_pair_le_one {ai aj ti tj : ℝ}
    (hti : 0 ≤ ti) (htj : 0 ≤ tj)
    (hci : 0 ≤ 1 - ai - ti) (hcj : 0 ≤ 1 - aj - tj)
    (hpair : ai * aj ≤ (1 - ai - ti) * (1 - aj - tj)) :
    ai + aj ≤ 1 := by
  nlinarith [mul_nonneg htj hci, mul_nonneg hti hcj, mul_nonneg hti htj]

/-! ## 2. The light case: the second determinant is the target

With `m_i = a_i + x_i = 2 a_i + t_i` the second determinant is exactly the
cleared form of `sum a_i / m_i <= 1`, and `m_i <= 1` turns that into the
target. -/

/-- The second determinant, in the coordinate `m_i = 2 a_i + t_i`. -/
theorem branchDetOutside_eq_excessForm (a1 a2 a3 t1 t2 t3 : ℝ) :
    branchDetOutside a1 a2 a3 t1 t2 t3
      = (2 * a1 + t1) * (2 * a2 + t2) * (2 * a3 + t3)
        - (a1 * ((2 * a2 + t2) * (2 * a3 + t3))
            + a2 * ((2 * a1 + t1) * (2 * a3 + t3))
            + a3 * ((2 * a1 + t1) * (2 * a2 + t2))) := by
  unfold branchDetOutside; ring

/-- **THE LIGHT CASE.**  If no atom carries more excess than cap slack, the
second determinant alone caps the total excess at one. -/
theorem gateway_excess_le_one_of_light {a1 a2 a3 t1 t2 t3 : ℝ}
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hm1pos : 0 < 2 * a1 + t1) (hm2pos : 0 < 2 * a2 + t2) (hm3pos : 0 < 2 * a3 + t3)
    (hm1 : 2 * a1 + t1 ≤ 1) (hm2 : 2 * a2 + t2 ≤ 1) (hm3 : 2 * a3 + t3 ≤ 1)
    (hM : 0 ≤ branchDetOutside a1 a2 a3 t1 t2 t3) :
    a1 + a2 + a3 ≤ 1 := by
  rw [branchDetOutside_eq_excessForm] at hM
  have h1 : 0 ≤ a1 * (1 - (2 * a1 + t1)) * ((2 * a2 + t2) * (2 * a3 + t3)) :=
    mul_nonneg (mul_nonneg ha1 (by linarith)) (by positivity)
  have h2 : 0 ≤ a2 * (1 - (2 * a2 + t2)) * ((2 * a1 + t1) * (2 * a3 + t3)) :=
    mul_nonneg (mul_nonneg ha2 (by linarith)) (by positivity)
  have h3 : 0 ≤ a3 * (1 - (2 * a3 + t3)) * ((2 * a1 + t1) * (2 * a2 + t2)) :=
    mul_nonneg (mul_nonneg ha3 (by linarith)) (by positivity)
  have hP : 0 < (2 * a1 + t1) * (2 * a2 + t2) * (2 * a3 + t3) := by positivity
  by_contra hcon
  push_neg at hcon
  nlinarith [h1, h2, h3, hM, mul_pos (sub_pos.mpr hcon) hP]

/-! ## 3. The scalar core of the heavy case -/

/-- Two nonnegative reals compare as their squares do. -/
theorem gateway_le_of_sq_le_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : y ^ 2 ≤ x ^ 2) : y ≤ x := by
  have hsqrt := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hy, Real.sqrt_sq hx] at hsqrt

/-- **THE HEAVY CASE, AS A SCALAR LEMMA.**  Six nonnegative reals, the first
capped at one, carrying the two determinant conditions in their normalized
form.  The conclusion is the target with its denominators cleared. -/
theorem gatewayHeavy_core {z p1 p2 p3 mu nu : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hp3 : 0 ≤ p3)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu)
    (hD1 : (1 - z) ^ 2 ≤ mu * nu)
    (hD2 : 4 ≤ p2 * p3 + p1 * (p2 + p3 + p2 * p3)) :
    (1 + z) ^ 2 * z
      ≤ (z + p1) * ((z * p2 + mu) * (z * p3 + nu))
        + p1 * ((z * p2 + mu) + (z * p3 + nu))
        + (1 + z) * p1 * (1 - z) := by
  have hA : 0 ≤ z * p2 + mu := by positivity
  have hB : 0 ≤ z * p3 + nu := by positivity
  have hcross : 4 * ((p2 * p3) * (mu * nu)) ≤ (p2 * nu + p3 * mu) ^ 2 := by
    nlinarith [sq_nonneg (p2 * nu - p3 * mu)]
  have hcrossNonneg : 0 ≤ p2 * nu + p3 * mu := by positivity
  have hsum : 2 * (1 - z) ≤ mu + nu := by
    refine gateway_le_of_sq_le_sq (by linarith) (by linarith) ?_
    nlinarith [sq_nonneg (mu - nu), hD1]
  rcases le_or_gt 4 (p2 * p3) with hpi | hpi
  · -- the excess product is large: the first factor alone carries the target
    have hc : 4 * (1 - z) ≤ p2 * nu + p3 * mu := by
      refine gateway_le_of_sq_le_sq hcrossNonneg (by linarith) ?_
      nlinarith [hcross, hD1, hpi, sq_nonneg (1 - z)]
    have hAB : (1 + z) ^ 2 ≤ (z * p2 + mu) * (z * p3 + nu) := by
      nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hpi),
        mul_nonneg hz0 (sub_nonneg.mpr hc), hD1]
    have hfirst : (z + p1) * (1 + z) ^ 2 ≤ (z + p1) * ((z * p2 + mu) * (z * p3 + nu)) :=
      mul_le_mul_of_nonneg_left hAB (by linarith)
    nlinarith [hfirst, mul_nonneg hp1 (add_nonneg hA hB),
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + z) hp1) (by linarith : (0:ℝ) ≤ 1 - z),
      sq_nonneg (1 + z)]
  · -- the excess product is small: the second determinant supplies the rest
    have hc : (p2 * p3) * (1 - z) ≤ p2 * nu + p3 * mu := by
      refine gateway_le_of_sq_le_sq hcrossNonneg
        (mul_nonneg (mul_nonneg hp2 hp3) (by linarith)) ?_
      nlinarith [hcross,
        mul_nonneg (mul_nonneg hp2 hp3)
          (mul_nonneg (sq_nonneg (1 - z)) (by linarith : (0:ℝ) ≤ 4 - p2 * p3)),
        mul_nonneg (mul_nonneg hp2 hp3) (sub_nonneg.mpr hD1)]
    have hAB : z * (p2 * p3) + (1 - z) ^ 2 ≤ (z * p2 + mu) * (z * p3 + nu) := by
      nlinarith [hc, hD1, hz0, mul_nonneg hp2 hp3]
    have hfirst : (z + p1) * (z * (p2 * p3) + (1 - z) ^ 2)
        ≤ (z + p1) * ((z * p2 + mu) * (z * p3 + nu)) :=
      mul_le_mul_of_nonneg_left hAB (by linarith)
    have hsecond : p1 * (z * (p2 + p3) + 2 * (1 - z))
        ≤ p1 * ((z * p2 + mu) + (z * p3 + nu)) :=
      mul_le_mul_of_nonneg_left (by linarith) hp1
    have hw : 0 ≤ p2 + p3 + p2 * p3 := by positivity
    have hmono : z ^ 2 * (p2 + p3 + p2 * p3)
        ≤ z * (p2 + p3 + p2 * p3) + 4 * (1 - z) := by
      nlinarith [mul_nonneg (mul_nonneg hw hz0) (sub_nonneg.mpr hz1),
        sub_nonneg.mpr hz1]
    have hkey : z ^ 2 * (4 - p2 * p3) ≤ p1 * (z * (p2 + p3 + p2 * p3) + 4 * (1 - z)) := by
      have hstep : z ^ 2 * (4 - p2 * p3) ≤ z ^ 2 * (p1 * (p2 + p3 + p2 * p3)) := by
        nlinarith [hD2, sq_nonneg z]
      calc z ^ 2 * (4 - p2 * p3) ≤ z ^ 2 * (p1 * (p2 + p3 + p2 * p3)) := hstep
        _ = p1 * (z ^ 2 * (p2 + p3 + p2 * p3)) := by ring
        _ ≤ p1 * (z * (p2 + p3 + p2 * p3) + 4 * (1 - z)) :=
            mul_le_mul_of_nonneg_left hmono hp1
    nlinarith [hfirst, hsecond, hkey]

/-! ## 4. The heavy case at the box -/

/-- The change of coordinates, as one polynomial identity.  The target times the
square of the first cap slack is the cleared core, up to sign. -/
theorem gatewayHeavy_translate {a1 a2 a3 t1 t2 t3 z p1 p2 p3 mu nu : ℝ}
    (ha1 : a1 ≠ 0) (ha2 : a2 ≠ 0) (ha3 : a3 ≠ 0)
    (hz : z = (1 - a1 - t1) / a1) (hq1 : p1 = t1 / a1)
    (hq2 : p2 = t2 / a2) (hq3 : p3 = t3 / a3)
    (hmu : mu = ((1 - a1 - t1) * (1 - a2 - t2) - a1 * a2) / (a1 * a2))
    (hnu : nu = ((1 - a1 - t1) * (1 - a3 - t3) - a1 * a3) / (a1 * a3)) :
    ((z + p1) * ((z * p2 + mu) * (z * p3 + nu))
        + p1 * ((z * p2 + mu) + (z * p3 + nu))
        + (1 + z) * p1 * (1 - z) - (1 + z) ^ 2 * z) * (a1 ^ 3 * a2 * a3)
      = (1 - a1 - a2 - a3) * (1 - a1 - t1) ^ 2 := by
  subst hz hq1 hq2 hq3 hmu hnu
  field_simp
  ring

/-- **THE HEAVY CASE.**  One atom carries more excess than cap slack.  Its two
pair constraints supply the nonnegative `mu` and `nu`, the first determinant
supplies their product bound and the second supplies the excess bound. -/
theorem gateway_excess_le_one_of_heavy {a1 a2 a3 t1 t2 t3 : ℝ}
    (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (ht3 : 0 ≤ t3)
    (hc1 : 0 ≤ 1 - a1 - t1)
    (hbig : 1 - a1 - t1 ≤ a1)
    (hp12 : a1 * a2 ≤ (1 - a1 - t1) * (1 - a2 - t2))
    (hp13 : a1 * a3 ≤ (1 - a1 - t1) * (1 - a3 - t3))
    (hIM : 0 ≤ branchDetComplement a1 a2 a3 t1 t2 t3)
    (hM : 0 ≤ branchDetOutside a1 a2 a3 t1 t2 t3) :
    a1 + a2 + a3 ≤ 1 := by
  have hc1pos : 0 < 1 - a1 - t1 := by
    rcases eq_or_lt_of_le hc1 with hzero | hpos
    · exfalso
      rw [← hzero, zero_mul] at hp12
      nlinarith [mul_pos ha1 ha2]
    · exact hpos
  have hmu : 0 ≤ (1 - a1 - t1) * (1 - a2 - t2) - a1 * a2 := by linarith
  have hnu : 0 ≤ (1 - a1 - t1) * (1 - a3 - t3) - a1 * a3 := by linarith
  have hz0 : (0 : ℝ) ≤ (1 - a1 - t1) / a1 := div_nonneg hc1 ha1.le
  have hz1 : (1 - a1 - t1) / a1 ≤ 1 := (div_le_one ha1).mpr hbig
  have hp1 : (0 : ℝ) ≤ t1 / a1 := div_nonneg ht1 ha1.le
  have hp2 : (0 : ℝ) ≤ t2 / a2 := div_nonneg ht2 ha2.le
  have hp3 : (0 : ℝ) ≤ t3 / a3 := div_nonneg ht3 ha3.le
  have hmu0 : (0 : ℝ) ≤ ((1 - a1 - t1) * (1 - a2 - t2) - a1 * a2) / (a1 * a2) :=
    div_nonneg hmu (by positivity)
  have hnu0 : (0 : ℝ) ≤ ((1 - a1 - t1) * (1 - a3 - t3) - a1 * a3) / (a1 * a3) :=
    div_nonneg hnu (by positivity)
  have hD1 : (1 - (1 - a1 - t1) / a1) ^ 2
      ≤ (((1 - a1 - t1) * (1 - a2 - t2) - a1 * a2) / (a1 * a2))
        * (((1 - a1 - t1) * (1 - a3 - t3) - a1 * a3) / (a1 * a3)) := by
    rw [← sub_nonneg]
    have hrw : (((1 - a1 - t1) * (1 - a2 - t2) - a1 * a2) / (a1 * a2))
          * (((1 - a1 - t1) * (1 - a3 - t3) - a1 * a3) / (a1 * a3))
          - (1 - (1 - a1 - t1) / a1) ^ 2
        = ((1 - a1 - t1) * branchDetComplement a1 a2 a3 t1 t2 t3) / (a1 ^ 2 * a2 * a3) := by
      unfold branchDetComplement
      field_simp
      ring
    rw [hrw]
    exact div_nonneg (mul_nonneg hc1 hIM) (by positivity)
  have hD2 : (4 : ℝ) ≤ (t2 / a2) * (t3 / a3)
      + (t1 / a1) * ((t2 / a2) + (t3 / a3) + (t2 / a2) * (t3 / a3)) := by
    rw [← sub_nonneg]
    have hrw : (t2 / a2) * (t3 / a3)
          + (t1 / a1) * ((t2 / a2) + (t3 / a3) + (t2 / a2) * (t3 / a3)) - 4
        = branchDetOutside a1 a2 a3 t1 t2 t3 / (a1 * a2 * a3) := by
      unfold branchDetOutside
      field_simp
      ring
    rw [hrw]
    exact div_nonneg hM (by positivity)
  have hcore := gatewayHeavy_core hz0 hz1 hp1 hp2 hp3 hmu0 hnu0 hD1 hD2
  have hid := gatewayHeavy_translate (a1 := a1) (a2 := a2) (a3 := a3)
    (t1 := t1) (t2 := t2) (t3 := t3) (ne_of_gt ha1) (ne_of_gt ha2) (ne_of_gt ha3)
    rfl rfl rfl rfl rfl rfl
  have hpos : 0 < a1 ^ 3 * a2 * a3 := by positivity
  have hdag : 0 ≤ (1 - a1 - a2 - a3) * (1 - a1 - t1) ^ 2 := by
    rw [← hid]
    exact mul_nonneg (by linarith) hpos.le
  nlinarith [hdag, mul_pos hc1pos hc1pos]

/-! ## 5. The box theorem -/

/-- The first determinant is symmetric in its three index pairs. -/
theorem branchDetComplement_swap (a1 a2 a3 t1 t2 t3 : ℝ) :
    branchDetComplement a2 a1 a3 t2 t1 t3 = branchDetComplement a1 a2 a3 t1 t2 t3 := by
  unfold branchDetComplement; ring

/-- The second determinant is symmetric in its three index pairs. -/
theorem branchDetOutside_swap (a1 a2 a3 t1 t2 t3 : ℝ) :
    branchDetOutside a2 a1 a3 t2 t1 t3 = branchDetOutside a1 a2 a3 t1 t2 t3 := by
  unfold branchDetOutside; ring

/-- The first determinant under the cycle sending the third index first. -/
theorem branchDetComplement_cycle (a1 a2 a3 t1 t2 t3 : ℝ) :
    branchDetComplement a3 a1 a2 t3 t1 t2 = branchDetComplement a1 a2 a3 t1 t2 t3 := by
  unfold branchDetComplement; ring

/-- The second determinant under the same cycle. -/
theorem branchDetOutside_cycle (a1 a2 a3 t1 t2 t3 : ℝ) :
    branchDetOutside a3 a1 a2 t3 t1 t2 = branchDetOutside a1 a2 a3 t1 t2 t3 := by
  unfold branchDetOutside; ring

/-- **THE GATEWAY TARGET.**  On the box of the corank-two arm the three weighted
leverage excesses total at most one.  The pair constraints admit at most one
atom whose excess passes its cap slack, and that atom decides which of the two
cases runs.

This is the statement `Gtz.gateway_no_handelman_certificate` shows has no
certificate of Handelman type at any degree. -/
theorem gateway_excess_le_one {a1 a2 a3 t1 t2 t3 : ℝ}
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (ht3 : 0 ≤ t3)
    (hc1 : 0 ≤ 1 - a1 - t1) (hc2 : 0 ≤ 1 - a2 - t2) (hc3 : 0 ≤ 1 - a3 - t3)
    (hp12 : a1 * a2 ≤ (1 - a1 - t1) * (1 - a2 - t2))
    (hp13 : a1 * a3 ≤ (1 - a1 - t1) * (1 - a3 - t3))
    (hp23 : a2 * a3 ≤ (1 - a2 - t2) * (1 - a3 - t3))
    (hIM : 0 ≤ branchDetComplement a1 a2 a3 t1 t2 t3)
    (hM : 0 ≤ branchDetOutside a1 a2 a3 t1 t2 t3) :
    a1 + a2 + a3 ≤ 1 := by
  rcases eq_or_lt_of_le ha1 with h1 | h1
  · have := excess_pair_le_one ht2 ht3 hc2 hc3 hp23
    linarith
  rcases eq_or_lt_of_le ha2 with h2 | h2
  · have := excess_pair_le_one ht1 ht3 hc1 hc3 hp13
    linarith
  rcases eq_or_lt_of_le ha3 with h3 | h3
  · have := excess_pair_le_one ht1 ht2 hc1 hc2 hp12
    linarith
  rcases le_or_gt (2 * a1 + t1) 1 with hm1 | hm1
  · rcases le_or_gt (2 * a2 + t2) 1 with hm2 | hm2
    · rcases le_or_gt (2 * a3 + t3) 1 with hm3 | hm3
      · exact gateway_excess_le_one_of_light ha1 ha2 ha3 (by linarith) (by linarith)
          (by linarith) hm1 hm2 hm3 hM
      · have hcyc := gateway_excess_le_one_of_heavy (a1 := a3) (a2 := a1) (a3 := a2)
          (t1 := t3) (t2 := t1) (t3 := t2) h3 h1 h2 ht3 ht1 ht2 hc3 (by linarith)
          (by nlinarith [hp13]) (by nlinarith [hp23])
          (by rw [branchDetComplement_cycle]; exact hIM)
          (by rw [branchDetOutside_cycle]; exact hM)
        linarith
    · have hswap := gateway_excess_le_one_of_heavy (a1 := a2) (a2 := a1) (a3 := a3)
        (t1 := t2) (t2 := t1) (t3 := t3) h2 h1 h3 ht2 ht1 ht3 hc2 (by linarith)
        (by nlinarith [hp12]) (by nlinarith [hp23])
        (by rw [branchDetComplement_swap]; exact hIM)
        (by rw [branchDetOutside_swap]; exact hM)
      linarith
  · exact gateway_excess_le_one_of_heavy h1 h2 h3 ht1 ht2 ht3 hc1 (by linarith)
      hp12 hp13 hIM hM

end Gtz

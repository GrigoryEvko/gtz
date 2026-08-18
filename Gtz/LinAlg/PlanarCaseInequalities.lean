import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6000000

/-!
# The planar corank-two case inequalities

The pure-real endgame of the planar corank-two closure.  In the normalized
coordinates `w_k` (outside weight shares) and `z_k` (whitened self-readings)
the tie's starred hypotheses meet a polygon: the fat caps `z_k < 1 − w_k`,
the thin floors `z_k ≥ 1 − w_k`, and `Σ z = 2`.  This module proves the
three polygon polynomials negative on their polygons.  Each polynomial is
linear in `z`, so each sign case is one exact ring identity against a
vertex value; each vertex value factors through `1 − Σw` with a manifestly
signed cofactor, or carries a degree-four Pólya certificate: after
homogenization by `w1 + w2 + w3 + (1 − Σw) = 1` every coefficient of its
negation is nonnegative.

The design content — how a primitive planar corank-two `(6,3)` tie produces
these hypotheses — lives in `Gtz/Wave/CorankTwoPlanarClosure.lean`.
-/

namespace Gtz

/-! ## 1. The Pólya vertex certificates -/

theorem planarVertex_capOne {w1 w2 w3 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2)
    (h3 : 0 < w3) (hS : w1 + w2 + w3 < 1) :
    -2*w1^3*w2 + w1^3 - 2*w1^2*w2^2 - w1^2*w2*w3 + 2*w1^2*w2 + 2*w1^2*w3 - w1^2 + w1*w2^2*w3 - w1*w2^2 + w1*w2*w3^2 + w1*w2 + w1*w3^2 - 2*w1*w3 - w2^2*w3 + 2*w2^2 - w2*w3^2 + 2*w2*w3 - 2*w2 + w3^2 - w3 < 0 := by
  have he : (0:ℝ) < 1 - w1 - w2 - w3 := by linarith
  have hm0 : (0:ℝ) < w3 * (1 - w1 - w2 - w3)^3 := mul_pos (h3) (pow_pos he 3)
  have hm1 : (0:ℝ) < w3^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h3 2) (pow_pos he 2)
  have hm2 : (0:ℝ) < w3^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h3 3) (he)
  have hm3 : (0:ℝ) < w2 * (1 - w1 - w2 - w3)^3 := mul_pos (h2) (pow_pos he 3)
  have hm4 : (0:ℝ) < w2 * w3 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h2) (h3)) (pow_pos he 2)
  have hm5 : (0:ℝ) < w2 * w3^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h2) (pow_pos h3 2)) (he)
  have hm6 : (0:ℝ) < w2 * w3^3 := mul_pos (h2) (pow_pos h3 3)
  have hm7 : (0:ℝ) < w2^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h2 2) (pow_pos he 2)
  have hm8 : (0:ℝ) < w2^2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h2 2) (h3)) (he)
  have hm9 : (0:ℝ) < w2^2 * w3^2 := mul_pos (pow_pos h2 2) (pow_pos h3 2)
  have hm10 : (0:ℝ) < w2^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h2 3) (he)
  have hm11 : (0:ℝ) < w2^3 * w3 := mul_pos (pow_pos h2 3) (h3)
  have hm12 : (0:ℝ) < w1 * w3 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h1) (h3)) (pow_pos he 2)
  have hm13 : (0:ℝ) < w1 * w3^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h1) (pow_pos h3 2)) (he)
  have hm14 : (0:ℝ) < w1 * w3^3 := mul_pos (h1) (pow_pos h3 3)
  have hm15 : (0:ℝ) < w1 * w2 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h1) (h2)) (pow_pos he 2)
  have hm16 : (0:ℝ) < w1 * w2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (mul_pos (h1) (h2)) (h3)) (he)
  have hm17 : (0:ℝ) < w1 * w2 * w3^2 := mul_pos (mul_pos (h1) (h2)) (pow_pos h3 2)
  have hm18 : (0:ℝ) < w1 * w2^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h1) (pow_pos h2 2)) (he)
  have hm19 : (0:ℝ) < w1 * w2^2 * w3 := mul_pos (mul_pos (h1) (pow_pos h2 2)) (h3)
  have hm20 : (0:ℝ) < w1 * w2^3 := mul_pos (h1) (pow_pos h2 3)
  have hm21 : (0:ℝ) < w1^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h1 2) (pow_pos he 2)
  have hm22 : (0:ℝ) < w1^2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h1 2) (h3)) (he)
  have hm23 : (0:ℝ) < w1^2 * w3^2 := mul_pos (pow_pos h1 2) (pow_pos h3 2)
  have hm24 : (0:ℝ) < w1^2 * w2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h1 2) (h2)) (he)
  have hm25 : (0:ℝ) < w1^2 * w2 * w3 := mul_pos (mul_pos (pow_pos h1 2) (h2)) (h3)
  have hm26 : (0:ℝ) < w1^2 * w2^2 := mul_pos (pow_pos h1 2) (pow_pos h2 2)
  have hm27 : (0:ℝ) < w1^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h1 3) (he)
  have hm28 : (0:ℝ) < w1^3 * w3 := mul_pos (pow_pos h1 3) (h3)
  have hm29 : (0:ℝ) < w1^3 * w2 := mul_pos (pow_pos h1 3) (h2)
  have hkey : -(-2*w1^3*w2 + w1^3 - 2*w1^2*w2^2 - w1^2*w2*w3 + 2*w1^2*w2 + 2*w1^2*w3 - w1^2 + w1*w2^2*w3 - w1*w2^2 + w1*w2*w3^2 + w1*w2 + w1*w3^2 - 2*w1*w3 - w2^2*w3 + 2*w2^2 - w2*w3^2 + 2*w2*w3 - 2*w2 + w3^2 - w3)
      = (w3 * (1 - w1 - w2 - w3)^3) + 2 * (w3^2 * (1 - w1 - w2 - w3)^2) + (w3^3 * (1 - w1 - w2 - w3)) + 2 * (w2 * (1 - w1 - w2 - w3)^3) + 7 * (w2 * w3 * (1 - w1 - w2 - w3)^2) + 7 * (w2 * w3^2 * (1 - w1 - w2 - w3)) + 2 * (w2 * w3^3) + 4 * (w2^2 * (1 - w1 - w2 - w3)^2) + 8 * (w2^2 * w3 * (1 - w1 - w2 - w3)) + 4 * (w2^2 * w3^2) + 2 * (w2^3 * (1 - w1 - w2 - w3)) + 2 * (w2^3 * w3) + 5 * (w1 * w3 * (1 - w1 - w2 - w3)^2) + 7 * (w1 * w3^2 * (1 - w1 - w2 - w3)) + 2 * (w1 * w3^3) + 5 * (w1 * w2 * (1 - w1 - w2 - w3)^2) + 16 * (w1 * w2 * w3 * (1 - w1 - w2 - w3)) + 8 * (w1 * w2 * w3^2) + 7 * (w1 * w2^2 * (1 - w1 - w2 - w3)) + 8 * (w1 * w2^2 * w3) + 2 * (w1 * w2^3) + (w1^2 * (1 - w1 - w2 - w3)^2) + 7 * (w1^2 * w3 * (1 - w1 - w2 - w3)) + 4 * (w1^2 * w3^2) + 4 * (w1^2 * w2 * (1 - w1 - w2 - w3)) + 8 * (w1^2 * w2 * w3) + 4 * (w1^2 * w2^2) + (w1^3 * (1 - w1 - w2 - w3)) + 2 * (w1^3 * w3) + 2 * (w1^3 * w2) := by ring
  linarith [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29]

theorem planarVertex_capTwo {w1 w2 w3 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2)
    (h3 : 0 < w3) (hS : w1 + w2 + w3 < 1) :
    -2*w1^2*w2^2 + w1^2*w2*w3 - w1^2*w2 - w1^2*w3 + 2*w1^2 - 2*w1*w2^3 - w1*w2^2*w3 + 2*w1*w2^2 + w1*w2*w3^2 + w1*w2 - w1*w3^2 + 2*w1*w3 - 2*w1 + w2^3 + 2*w2^2*w3 - w2^2 + w2*w3^2 - 2*w2*w3 + w3^2 - w3 < 0 := by
  have he : (0:ℝ) < 1 - w1 - w2 - w3 := by linarith
  have hm0 : (0:ℝ) < w3 * (1 - w1 - w2 - w3)^3 := mul_pos (h3) (pow_pos he 3)
  have hm1 : (0:ℝ) < w3^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h3 2) (pow_pos he 2)
  have hm2 : (0:ℝ) < w3^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h3 3) (he)
  have hm3 : (0:ℝ) < w2 * w3 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h2) (h3)) (pow_pos he 2)
  have hm4 : (0:ℝ) < w2 * w3^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h2) (pow_pos h3 2)) (he)
  have hm5 : (0:ℝ) < w2 * w3^3 := mul_pos (h2) (pow_pos h3 3)
  have hm6 : (0:ℝ) < w2^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h2 2) (pow_pos he 2)
  have hm7 : (0:ℝ) < w2^2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h2 2) (h3)) (he)
  have hm8 : (0:ℝ) < w2^2 * w3^2 := mul_pos (pow_pos h2 2) (pow_pos h3 2)
  have hm9 : (0:ℝ) < w2^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h2 3) (he)
  have hm10 : (0:ℝ) < w2^3 * w3 := mul_pos (pow_pos h2 3) (h3)
  have hm11 : (0:ℝ) < w1 * (1 - w1 - w2 - w3)^3 := mul_pos (h1) (pow_pos he 3)
  have hm12 : (0:ℝ) < w1 * w3 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h1) (h3)) (pow_pos he 2)
  have hm13 : (0:ℝ) < w1 * w3^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h1) (pow_pos h3 2)) (he)
  have hm14 : (0:ℝ) < w1 * w3^3 := mul_pos (h1) (pow_pos h3 3)
  have hm15 : (0:ℝ) < w1 * w2 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h1) (h2)) (pow_pos he 2)
  have hm16 : (0:ℝ) < w1 * w2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (mul_pos (h1) (h2)) (h3)) (he)
  have hm17 : (0:ℝ) < w1 * w2 * w3^2 := mul_pos (mul_pos (h1) (h2)) (pow_pos h3 2)
  have hm18 : (0:ℝ) < w1 * w2^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h1) (pow_pos h2 2)) (he)
  have hm19 : (0:ℝ) < w1 * w2^2 * w3 := mul_pos (mul_pos (h1) (pow_pos h2 2)) (h3)
  have hm20 : (0:ℝ) < w1 * w2^3 := mul_pos (h1) (pow_pos h2 3)
  have hm21 : (0:ℝ) < w1^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h1 2) (pow_pos he 2)
  have hm22 : (0:ℝ) < w1^2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h1 2) (h3)) (he)
  have hm23 : (0:ℝ) < w1^2 * w3^2 := mul_pos (pow_pos h1 2) (pow_pos h3 2)
  have hm24 : (0:ℝ) < w1^2 * w2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h1 2) (h2)) (he)
  have hm25 : (0:ℝ) < w1^2 * w2 * w3 := mul_pos (mul_pos (pow_pos h1 2) (h2)) (h3)
  have hm26 : (0:ℝ) < w1^2 * w2^2 := mul_pos (pow_pos h1 2) (pow_pos h2 2)
  have hm27 : (0:ℝ) < w1^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h1 3) (he)
  have hm28 : (0:ℝ) < w1^3 * w3 := mul_pos (pow_pos h1 3) (h3)
  have hm29 : (0:ℝ) < w1^3 * w2 := mul_pos (pow_pos h1 3) (h2)
  have hkey : -(-2*w1^2*w2^2 + w1^2*w2*w3 - w1^2*w2 - w1^2*w3 + 2*w1^2 - 2*w1*w2^3 - w1*w2^2*w3 + 2*w1*w2^2 + w1*w2*w3^2 + w1*w2 - w1*w3^2 + 2*w1*w3 - 2*w1 + w2^3 + 2*w2^2*w3 - w2^2 + w2*w3^2 - 2*w2*w3 + w3^2 - w3)
      = (w3 * (1 - w1 - w2 - w3)^3) + 2 * (w3^2 * (1 - w1 - w2 - w3)^2) + (w3^3 * (1 - w1 - w2 - w3)) + 5 * (w2 * w3 * (1 - w1 - w2 - w3)^2) + 7 * (w2 * w3^2 * (1 - w1 - w2 - w3)) + 2 * (w2 * w3^3) + (w2^2 * (1 - w1 - w2 - w3)^2) + 7 * (w2^2 * w3 * (1 - w1 - w2 - w3)) + 4 * (w2^2 * w3^2) + (w2^3 * (1 - w1 - w2 - w3)) + 2 * (w2^3 * w3) + 2 * (w1 * (1 - w1 - w2 - w3)^3) + 7 * (w1 * w3 * (1 - w1 - w2 - w3)^2) + 7 * (w1 * w3^2 * (1 - w1 - w2 - w3)) + 2 * (w1 * w3^3) + 5 * (w1 * w2 * (1 - w1 - w2 - w3)^2) + 16 * (w1 * w2 * w3 * (1 - w1 - w2 - w3)) + 8 * (w1 * w2 * w3^2) + 4 * (w1 * w2^2 * (1 - w1 - w2 - w3)) + 8 * (w1 * w2^2 * w3) + 2 * (w1 * w2^3) + 4 * (w1^2 * (1 - w1 - w2 - w3)^2) + 8 * (w1^2 * w3 * (1 - w1 - w2 - w3)) + 4 * (w1^2 * w3^2) + 7 * (w1^2 * w2 * (1 - w1 - w2 - w3)) + 8 * (w1^2 * w2 * w3) + 4 * (w1^2 * w2^2) + 2 * (w1^3 * (1 - w1 - w2 - w3)) + 2 * (w1^3 * w3) + 2 * (w1^3 * w2) := by ring
  linarith [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29]

theorem planarVertex_origin {w1 w2 w3 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2)
    (h3 : 0 < w3) (hS : w1 + w2 + w3 < 1) :
    -4*w1^2*w2 + 3*w1^2 - 4*w1*w2^2 + 6*w1*w2 + w1*w3 - 3*w1 + 3*w2^2 + w2*w3 - 3*w2 + 2*w3^2 - 2*w3 < 0 := by
  have he : (0:ℝ) < 1 - w1 - w2 - w3 := by linarith
  have hm0 : (0:ℝ) < w3 * (1 - w1 - w2 - w3)^3 := mul_pos (h3) (pow_pos he 3)
  have hm1 : (0:ℝ) < w3^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h3 2) (pow_pos he 2)
  have hm2 : (0:ℝ) < w3^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h3 3) (he)
  have hm3 : (0:ℝ) < w2 * (1 - w1 - w2 - w3)^3 := mul_pos (h2) (pow_pos he 3)
  have hm4 : (0:ℝ) < w2 * w3 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h2) (h3)) (pow_pos he 2)
  have hm5 : (0:ℝ) < w2 * w3^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h2) (pow_pos h3 2)) (he)
  have hm6 : (0:ℝ) < w2 * w3^3 := mul_pos (h2) (pow_pos h3 3)
  have hm7 : (0:ℝ) < w2^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h2 2) (pow_pos he 2)
  have hm8 : (0:ℝ) < w2^2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h2 2) (h3)) (he)
  have hm9 : (0:ℝ) < w2^2 * w3^2 := mul_pos (pow_pos h2 2) (pow_pos h3 2)
  have hm10 : (0:ℝ) < w2^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h2 3) (he)
  have hm11 : (0:ℝ) < w2^3 * w3 := mul_pos (pow_pos h2 3) (h3)
  have hm12 : (0:ℝ) < w1 * (1 - w1 - w2 - w3)^3 := mul_pos (h1) (pow_pos he 3)
  have hm13 : (0:ℝ) < w1 * w3 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h1) (h3)) (pow_pos he 2)
  have hm14 : (0:ℝ) < w1 * w3^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h1) (pow_pos h3 2)) (he)
  have hm15 : (0:ℝ) < w1 * w3^3 := mul_pos (h1) (pow_pos h3 3)
  have hm16 : (0:ℝ) < w1 * w2 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h1) (h2)) (pow_pos he 2)
  have hm17 : (0:ℝ) < w1 * w2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (mul_pos (h1) (h2)) (h3)) (he)
  have hm18 : (0:ℝ) < w1 * w2 * w3^2 := mul_pos (mul_pos (h1) (h2)) (pow_pos h3 2)
  have hm19 : (0:ℝ) < w1 * w2^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h1) (pow_pos h2 2)) (he)
  have hm20 : (0:ℝ) < w1 * w2^2 * w3 := mul_pos (mul_pos (h1) (pow_pos h2 2)) (h3)
  have hm21 : (0:ℝ) < w1 * w2^3 := mul_pos (h1) (pow_pos h2 3)
  have hm22 : (0:ℝ) < w1^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h1 2) (pow_pos he 2)
  have hm23 : (0:ℝ) < w1^2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h1 2) (h3)) (he)
  have hm24 : (0:ℝ) < w1^2 * w3^2 := mul_pos (pow_pos h1 2) (pow_pos h3 2)
  have hm25 : (0:ℝ) < w1^2 * w2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h1 2) (h2)) (he)
  have hm26 : (0:ℝ) < w1^2 * w2 * w3 := mul_pos (mul_pos (pow_pos h1 2) (h2)) (h3)
  have hm27 : (0:ℝ) < w1^2 * w2^2 := mul_pos (pow_pos h1 2) (pow_pos h2 2)
  have hm28 : (0:ℝ) < w1^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h1 3) (he)
  have hm29 : (0:ℝ) < w1^3 * w3 := mul_pos (pow_pos h1 3) (h3)
  have hm30 : (0:ℝ) < w1^3 * w2 := mul_pos (pow_pos h1 3) (h2)
  have hkey : -(-4*w1^2*w2 + 3*w1^2 - 4*w1*w2^2 + 6*w1*w2 + w1*w3 - 3*w1 + 3*w2^2 + w2*w3 - 3*w2 + 2*w3^2 - 2*w3)
      = 2 * (w3 * (1 - w1 - w2 - w3)^3) + 4 * (w3^2 * (1 - w1 - w2 - w3)^2) + 2 * (w3^3 * (1 - w1 - w2 - w3)) + 3 * (w2 * (1 - w1 - w2 - w3)^3) + 14 * (w2 * w3 * (1 - w1 - w2 - w3)^2) + 15 * (w2 * w3^2 * (1 - w1 - w2 - w3)) + 4 * (w2 * w3^3) + 6 * (w2^2 * (1 - w1 - w2 - w3)^2) + 16 * (w2^2 * w3 * (1 - w1 - w2 - w3)) + 8 * (w2^2 * w3^2) + 3 * (w2^3 * (1 - w1 - w2 - w3)) + 4 * (w2^3 * w3) + 3 * (w1 * (1 - w1 - w2 - w3)^3) + 14 * (w1 * w3 * (1 - w1 - w2 - w3)^2) + 15 * (w1 * w3^2 * (1 - w1 - w2 - w3)) + 4 * (w1 * w3^3) + 12 * (w1 * w2 * (1 - w1 - w2 - w3)^2) + 32 * (w1 * w2 * w3 * (1 - w1 - w2 - w3)) + 16 * (w1 * w2 * w3^2) + 13 * (w1 * w2^2 * (1 - w1 - w2 - w3)) + 16 * (w1 * w2^2 * w3) + 4 * (w1 * w2^3) + 6 * (w1^2 * (1 - w1 - w2 - w3)^2) + 16 * (w1^2 * w3 * (1 - w1 - w2 - w3)) + 8 * (w1^2 * w3^2) + 13 * (w1^2 * w2 * (1 - w1 - w2 - w3)) + 16 * (w1^2 * w2 * w3) + 8 * (w1^2 * w2^2) + 3 * (w1^3 * (1 - w1 - w2 - w3)) + 4 * (w1^3 * w3) + 4 * (w1^3 * w2) := by ring
  linarith [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29, hm30]

theorem planarVertex_oneFat_capTwo {w1 w2 w3 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2)
    (h3 : 0 < w3) (hS : w1 + w2 + w3 < 1) :
    -w1^2*w2^2 + w1^2*w2*w3 - w1^2*w2 - w1^2*w3 + 2*w1^2 - w1*w2^3 + w1*w2*w3^2 - w1*w2*w3 + 2*w1*w2 - w1*w3^2 + 2*w1*w3 - 2*w1 + w2^2 - w2 + w3^2 - w3 < 0 := by
  have he : (0:ℝ) < 1 - w1 - w2 - w3 := by linarith
  have hm0 : (0:ℝ) < w3 * (1 - w1 - w2 - w3)^3 := mul_pos (h3) (pow_pos he 3)
  have hm1 : (0:ℝ) < w3^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h3 2) (pow_pos he 2)
  have hm2 : (0:ℝ) < w3^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h3 3) (he)
  have hm3 : (0:ℝ) < w2 * (1 - w1 - w2 - w3)^3 := mul_pos (h2) (pow_pos he 3)
  have hm4 : (0:ℝ) < w2 * w3 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h2) (h3)) (pow_pos he 2)
  have hm5 : (0:ℝ) < w2 * w3^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h2) (pow_pos h3 2)) (he)
  have hm6 : (0:ℝ) < w2 * w3^3 := mul_pos (h2) (pow_pos h3 3)
  have hm7 : (0:ℝ) < w2^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h2 2) (pow_pos he 2)
  have hm8 : (0:ℝ) < w2^2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h2 2) (h3)) (he)
  have hm9 : (0:ℝ) < w2^2 * w3^2 := mul_pos (pow_pos h2 2) (pow_pos h3 2)
  have hm10 : (0:ℝ) < w2^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h2 3) (he)
  have hm11 : (0:ℝ) < w2^3 * w3 := mul_pos (pow_pos h2 3) (h3)
  have hm12 : (0:ℝ) < w1 * (1 - w1 - w2 - w3)^3 := mul_pos (h1) (pow_pos he 3)
  have hm13 : (0:ℝ) < w1 * w3 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h1) (h3)) (pow_pos he 2)
  have hm14 : (0:ℝ) < w1 * w3^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h1) (pow_pos h3 2)) (he)
  have hm15 : (0:ℝ) < w1 * w3^3 := mul_pos (h1) (pow_pos h3 3)
  have hm16 : (0:ℝ) < w1 * w2 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h1) (h2)) (pow_pos he 2)
  have hm17 : (0:ℝ) < w1 * w2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (mul_pos (h1) (h2)) (h3)) (he)
  have hm18 : (0:ℝ) < w1 * w2 * w3^2 := mul_pos (mul_pos (h1) (h2)) (pow_pos h3 2)
  have hm19 : (0:ℝ) < w1 * w2^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h1) (pow_pos h2 2)) (he)
  have hm20 : (0:ℝ) < w1 * w2^2 * w3 := mul_pos (mul_pos (h1) (pow_pos h2 2)) (h3)
  have hm21 : (0:ℝ) < w1 * w2^3 := mul_pos (h1) (pow_pos h2 3)
  have hm22 : (0:ℝ) < w1^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h1 2) (pow_pos he 2)
  have hm23 : (0:ℝ) < w1^2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h1 2) (h3)) (he)
  have hm24 : (0:ℝ) < w1^2 * w3^2 := mul_pos (pow_pos h1 2) (pow_pos h3 2)
  have hm25 : (0:ℝ) < w1^2 * w2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h1 2) (h2)) (he)
  have hm26 : (0:ℝ) < w1^2 * w2 * w3 := mul_pos (mul_pos (pow_pos h1 2) (h2)) (h3)
  have hm27 : (0:ℝ) < w1^2 * w2^2 := mul_pos (pow_pos h1 2) (pow_pos h2 2)
  have hm28 : (0:ℝ) < w1^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h1 3) (he)
  have hm29 : (0:ℝ) < w1^3 * w3 := mul_pos (pow_pos h1 3) (h3)
  have hm30 : (0:ℝ) < w1^3 * w2 := mul_pos (pow_pos h1 3) (h2)
  have hkey : -(-w1^2*w2^2 + w1^2*w2*w3 - w1^2*w2 - w1^2*w3 + 2*w1^2 - w1*w2^3 + w1*w2*w3^2 - w1*w2*w3 + 2*w1*w2 - w1*w3^2 + 2*w1*w3 - 2*w1 + w2^2 - w2 + w3^2 - w3)
      = (w3 * (1 - w1 - w2 - w3)^3) + 2 * (w3^2 * (1 - w1 - w2 - w3)^2) + (w3^3 * (1 - w1 - w2 - w3)) + (w2 * (1 - w1 - w2 - w3)^3) + 6 * (w2 * w3 * (1 - w1 - w2 - w3)^2) + 7 * (w2 * w3^2 * (1 - w1 - w2 - w3)) + 2 * (w2 * w3^3) + 2 * (w2^2 * (1 - w1 - w2 - w3)^2) + 7 * (w2^2 * w3 * (1 - w1 - w2 - w3)) + 4 * (w2^2 * w3^2) + (w2^3 * (1 - w1 - w2 - w3)) + 2 * (w2^3 * w3) + 2 * (w1 * (1 - w1 - w2 - w3)^3) + 7 * (w1 * w3 * (1 - w1 - w2 - w3)^2) + 7 * (w1 * w3^2 * (1 - w1 - w2 - w3)) + 2 * (w1 * w3^3) + 7 * (w1 * w2 * (1 - w1 - w2 - w3)^2) + 17 * (w1 * w2 * w3 * (1 - w1 - w2 - w3)) + 8 * (w1 * w2 * w3^2) + 6 * (w1 * w2^2 * (1 - w1 - w2 - w3)) + 8 * (w1 * w2^2 * w3) + 2 * (w1 * w2^3) + 4 * (w1^2 * (1 - w1 - w2 - w3)^2) + 8 * (w1^2 * w3 * (1 - w1 - w2 - w3)) + 4 * (w1^2 * w3^2) + 8 * (w1^2 * w2 * (1 - w1 - w2 - w3)) + 8 * (w1^2 * w2 * w3) + 4 * (w1^2 * w2^2) + 2 * (w1^3 * (1 - w1 - w2 - w3)) + 2 * (w1^3 * w3) + 2 * (w1^3 * w2) := by ring
  linarith [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29, hm30]

theorem planarVertex_oneFat_sum {w1 w2 w3 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2)
    (h3 : 0 < w3) (hS : w1 + w2 + w3 < 1) :
    w1^2*w2*w3 - w1^2*w2 - w1^2*w3^2 - w1^2*w3 + 2*w1^2 + w1*w2^2*w3 - w1*w2^2 - w1*w2*w3 + 2*w1*w2 - w1*w3^3 + 2*w1*w3 - 2*w1 + w2^2 - w2 + w3^2 - w3 < 0 := by
  have he : (0:ℝ) < 1 - w1 - w2 - w3 := by linarith
  have hm0 : (0:ℝ) < w3 * (1 - w1 - w2 - w3)^3 := mul_pos (h3) (pow_pos he 3)
  have hm1 : (0:ℝ) < w3^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h3 2) (pow_pos he 2)
  have hm2 : (0:ℝ) < w3^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h3 3) (he)
  have hm3 : (0:ℝ) < w2 * (1 - w1 - w2 - w3)^3 := mul_pos (h2) (pow_pos he 3)
  have hm4 : (0:ℝ) < w2 * w3 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h2) (h3)) (pow_pos he 2)
  have hm5 : (0:ℝ) < w2 * w3^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h2) (pow_pos h3 2)) (he)
  have hm6 : (0:ℝ) < w2 * w3^3 := mul_pos (h2) (pow_pos h3 3)
  have hm7 : (0:ℝ) < w2^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h2 2) (pow_pos he 2)
  have hm8 : (0:ℝ) < w2^2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h2 2) (h3)) (he)
  have hm9 : (0:ℝ) < w2^2 * w3^2 := mul_pos (pow_pos h2 2) (pow_pos h3 2)
  have hm10 : (0:ℝ) < w2^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h2 3) (he)
  have hm11 : (0:ℝ) < w2^3 * w3 := mul_pos (pow_pos h2 3) (h3)
  have hm12 : (0:ℝ) < w1 * (1 - w1 - w2 - w3)^3 := mul_pos (h1) (pow_pos he 3)
  have hm13 : (0:ℝ) < w1 * w3 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h1) (h3)) (pow_pos he 2)
  have hm14 : (0:ℝ) < w1 * w3^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h1) (pow_pos h3 2)) (he)
  have hm15 : (0:ℝ) < w1 * w3^3 := mul_pos (h1) (pow_pos h3 3)
  have hm16 : (0:ℝ) < w1 * w2 * (1 - w1 - w2 - w3)^2 := mul_pos (mul_pos (h1) (h2)) (pow_pos he 2)
  have hm17 : (0:ℝ) < w1 * w2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (mul_pos (h1) (h2)) (h3)) (he)
  have hm18 : (0:ℝ) < w1 * w2 * w3^2 := mul_pos (mul_pos (h1) (h2)) (pow_pos h3 2)
  have hm19 : (0:ℝ) < w1 * w2^2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (h1) (pow_pos h2 2)) (he)
  have hm20 : (0:ℝ) < w1 * w2^2 * w3 := mul_pos (mul_pos (h1) (pow_pos h2 2)) (h3)
  have hm21 : (0:ℝ) < w1 * w2^3 := mul_pos (h1) (pow_pos h2 3)
  have hm22 : (0:ℝ) < w1^2 * (1 - w1 - w2 - w3)^2 := mul_pos (pow_pos h1 2) (pow_pos he 2)
  have hm23 : (0:ℝ) < w1^2 * w3 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h1 2) (h3)) (he)
  have hm24 : (0:ℝ) < w1^2 * w3^2 := mul_pos (pow_pos h1 2) (pow_pos h3 2)
  have hm25 : (0:ℝ) < w1^2 * w2 * (1 - w1 - w2 - w3) := mul_pos (mul_pos (pow_pos h1 2) (h2)) (he)
  have hm26 : (0:ℝ) < w1^2 * w2 * w3 := mul_pos (mul_pos (pow_pos h1 2) (h2)) (h3)
  have hm27 : (0:ℝ) < w1^2 * w2^2 := mul_pos (pow_pos h1 2) (pow_pos h2 2)
  have hm28 : (0:ℝ) < w1^3 * (1 - w1 - w2 - w3) := mul_pos (pow_pos h1 3) (he)
  have hm29 : (0:ℝ) < w1^3 * w3 := mul_pos (pow_pos h1 3) (h3)
  have hm30 : (0:ℝ) < w1^3 * w2 := mul_pos (pow_pos h1 3) (h2)
  have hkey : -(w1^2*w2*w3 - w1^2*w2 - w1^2*w3^2 - w1^2*w3 + 2*w1^2 + w1*w2^2*w3 - w1*w2^2 - w1*w2*w3 + 2*w1*w2 - w1*w3^3 + 2*w1*w3 - 2*w1 + w2^2 - w2 + w3^2 - w3)
      = (w3 * (1 - w1 - w2 - w3)^3) + 2 * (w3^2 * (1 - w1 - w2 - w3)^2) + (w3^3 * (1 - w1 - w2 - w3)) + (w2 * (1 - w1 - w2 - w3)^3) + 6 * (w2 * w3 * (1 - w1 - w2 - w3)^2) + 7 * (w2 * w3^2 * (1 - w1 - w2 - w3)) + 2 * (w2 * w3^3) + 2 * (w2^2 * (1 - w1 - w2 - w3)^2) + 7 * (w2^2 * w3 * (1 - w1 - w2 - w3)) + 4 * (w2^2 * w3^2) + (w2^3 * (1 - w1 - w2 - w3)) + 2 * (w2^3 * w3) + 2 * (w1 * (1 - w1 - w2 - w3)^3) + 7 * (w1 * w3 * (1 - w1 - w2 - w3)^2) + 6 * (w1 * w3^2 * (1 - w1 - w2 - w3)) + 2 * (w1 * w3^3) + 7 * (w1 * w2 * (1 - w1 - w2 - w3)^2) + 17 * (w1 * w2 * w3 * (1 - w1 - w2 - w3)) + 8 * (w1 * w2 * w3^2) + 7 * (w1 * w2^2 * (1 - w1 - w2 - w3)) + 8 * (w1 * w2^2 * w3) + 2 * (w1 * w2^3) + 4 * (w1^2 * (1 - w1 - w2 - w3)^2) + 8 * (w1^2 * w3 * (1 - w1 - w2 - w3)) + 4 * (w1^2 * w3^2) + 8 * (w1^2 * w2 * (1 - w1 - w2 - w3)) + 8 * (w1^2 * w2 * w3) + 4 * (w1^2 * w2^2) + 2 * (w1^3 * (1 - w1 - w2 - w3)) + 2 * (w1^3 * w3) + 2 * (w1^3 * w2) := by ring
  linarith [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29, hm30]


/-! ## 2. The polygon negativity, division-free -/

/-- **All three pairs fat.**  On the open polygon `0 < z_k < 1 − w_k`,
`Σ z = 2`, the ledger polynomial is negative. -/
theorem planarPolygon_allFat {w1 w2 w3 z1 z2 z3 : ℝ}
    (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3) (hS : w1 + w2 + w3 < 1)
    (hz1 : 0 < z1) (hz2 : 0 < z2) (hz3 : 0 < z3)
    (hzs : z1 + z2 + z3 = 2)
    (hc1 : z1 < 1 - w1) (hc2 : z2 < 1 - w2) (hc3 : z3 < 1 - w3) :
    (w1^2 + w1*w2*w3 - w1*w2 - w1*w3 - w1 + w2^2 - w2*w3 - w2 + w3^2 - w3)
      + z1 * (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3)
      + z2 * (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2)
      + z3 * (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3) < 0 := by
  have hw1 : w1 < 1 := by linarith
  have hw2 : w2 < 1 := by linarith
  have hw3 : w3 < 1 := by linarith
  rcases le_total (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3) (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2) with h12 | h12
  · rcases le_total (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3) (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3) with h13 | h13
    · have hU : (0:ℝ) < w1*(1-w2)*(1-w3) + w2*w3*(1-w2-w3+w1) :=
        add_pos (mul_pos (mul_pos h1 (by linarith)) (by linarith))
          (mul_pos (mul_pos h2 h3) (by linarith))
      have hkey : (w1^2 + w1*w2*w3 - w1*w2 - w1*w3 - w1 + w2^2 - w2*w3 - w2 + w3^2 - w3)
            + z1 * (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3)
            + z2 * (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2)
            + z3 * (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3)
          = (w1+w2+w3-1) * (w1*(1-w2)*(1-w3) + w2*w3*(1-w2-w3+w1))
            + (z2-(1-w2)) * ((-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2) - (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3))
            + (z3-(1-w3)) * ((-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3) - (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3))
            + (z1+z2+z3-2) * (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3) := by ring
      have hz0 : (z1+z2+z3-2) * (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3) = 0 := by rw [hzs]; ring
      nlinarith [hz0, hkey, mul_pos (by linarith : (0:ℝ) < 1-(w1+w2+w3)) hU,
        mul_nonneg (by linarith : (0:ℝ) ≤ (1-w2)-z2)
          (by linarith : (0:ℝ) ≤ (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2) - (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3)),
        mul_nonneg (by linarith : (0:ℝ) ≤ (1-w3)-z3)
          (by linarith : (0:ℝ) ≤ (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3) - (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3))]
    · have hU : (0:ℝ) < w3*(1-w1)*(1-w2) + w1*w2*(1-w1-w2+w3) :=
        add_pos (mul_pos (mul_pos h3 (by linarith)) (by linarith))
          (mul_pos (mul_pos h1 h2) (by linarith))
      have hkey : (w1^2 + w1*w2*w3 - w1*w2 - w1*w3 - w1 + w2^2 - w2*w3 - w2 + w3^2 - w3)
            + z1 * (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3)
            + z2 * (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2)
            + z3 * (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3)
          = (w1+w2+w3-1) * (w3*(1-w1)*(1-w2) + w1*w2*(1-w1-w2+w3))
            + (z1-(1-w1)) * ((w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3) - (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3))
            + (z2-(1-w2)) * ((-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2) - (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3))
            + (z1+z2+z3-2) * (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3) := by ring
      have hz0 : (z1+z2+z3-2) * (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3) = 0 := by rw [hzs]; ring
      nlinarith [hz0, hkey, mul_pos (by linarith : (0:ℝ) < 1-(w1+w2+w3)) hU,
        mul_nonneg (by linarith : (0:ℝ) ≤ (1-w1)-z1)
          (by linarith : (0:ℝ) ≤ (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3) - (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3)),
        mul_nonneg (by linarith : (0:ℝ) ≤ (1-w2)-z2)
          (by linarith : (0:ℝ) ≤ (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2) - (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3))]
  · rcases le_total (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2) (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3) with h23 | h23
    · have hU : (0:ℝ) < w2*(1-w1)*(1-w3) + w1*w3*(1-w1-w3+w2) :=
        add_pos (mul_pos (mul_pos h2 (by linarith)) (by linarith))
          (mul_pos (mul_pos h1 h3) (by linarith))
      have hkey : (w1^2 + w1*w2*w3 - w1*w2 - w1*w3 - w1 + w2^2 - w2*w3 - w2 + w3^2 - w3)
            + z1 * (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3)
            + z2 * (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2)
            + z3 * (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3)
          = (w1+w2+w3-1) * (w2*(1-w1)*(1-w3) + w1*w3*(1-w1-w3+w2))
            + (z1-(1-w1)) * ((w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3) - (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2))
            + (z3-(1-w3)) * ((-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3) - (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2))
            + (z1+z2+z3-2) * (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2) := by ring
      have hz0 : (z1+z2+z3-2) * (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2) = 0 := by rw [hzs]; ring
      nlinarith [hz0, hkey, mul_pos (by linarith : (0:ℝ) < 1-(w1+w2+w3)) hU,
        mul_nonneg (by linarith : (0:ℝ) ≤ (1-w1)-z1)
          (by linarith : (0:ℝ) ≤ (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3) - (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2)),
        mul_nonneg (by linarith : (0:ℝ) ≤ (1-w3)-z3)
          (by linarith : (0:ℝ) ≤ (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3) - (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2))]
    · have hU : (0:ℝ) < w3*(1-w1)*(1-w2) + w1*w2*(1-w1-w2+w3) :=
        add_pos (mul_pos (mul_pos h3 (by linarith)) (by linarith))
          (mul_pos (mul_pos h1 h2) (by linarith))
      have hkey : (w1^2 + w1*w2*w3 - w1*w2 - w1*w3 - w1 + w2^2 - w2*w3 - w2 + w3^2 - w3)
            + z1 * (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3)
            + z2 * (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2)
            + z3 * (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3)
          = (w1+w2+w3-1) * (w3*(1-w1)*(1-w2) + w1*w2*(1-w1-w2+w3))
            + (z1-(1-w1)) * ((w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3) - (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3))
            + (z2-(1-w2)) * ((-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2) - (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3))
            + (z1+z2+z3-2) * (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3) := by ring
      have hz0 : (z1+z2+z3-2) * (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3) = 0 := by rw [hzs]; ring
      nlinarith [hz0, hkey, mul_pos (by linarith : (0:ℝ) < 1-(w1+w2+w3)) hU,
        mul_nonneg (by linarith : (0:ℝ) ≤ (1-w1)-z1)
          (by linarith : (0:ℝ) ≤ (w1 - w2^2*w3 - w2*w3^2 + 2*w2*w3) - (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3)),
        mul_nonneg (by linarith : (0:ℝ) ≤ (1-w2)-z2)
          (by linarith : (0:ℝ) ≤ (-w1^2*w3 - w1*w3^2 + 2*w1*w3 + w2) - (-w1^2*w2 - w1*w2^2 + 2*w1*w2 + w3))]

/-- **Pairs one and two fat, pair three thin.** -/
theorem planarPolygon_twoFat {w1 w2 w3 z1 z2 z3 : ℝ}
    (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3) (hS : w1 + w2 + w3 < 1)
    (hz1 : 0 < z1) (hz2 : 0 < z2) (hzs : z1 + z2 + z3 = 2)
    (hc1 : z1 < 1 - w1) (hc2 : z2 < 1 - w2) (ht3 : 1 - w3 ≤ z3) :
    (-4*w1^2*w2 + 3*w1^2 - 4*w1*w2^2 + 6*w1*w2 + w1*w3 - 3*w1 + 3*w2^2 + w2*w3 - 3*w2 + 2*w3^2 - 2*w3)
      + z1 * (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3)
      + z2 * (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3) < 0 := by
  have hw1 : w1 < 1 := by linarith
  have hw2 : w2 < 1 := by linarith
  have hw3 : w3 < 1 := by linarith
  have hsum12 : z1 + z2 ≤ 1 + w3 := by linarith
  rcases le_total (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3) 0 with hcs1 | hcs1
  · rcases le_total (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3) 0 with hcs2 | hcs2
    · have hV := planarVertex_origin h1 h2 h3 hS
      nlinarith [mul_nonneg hz1.le (neg_nonneg.2 hcs1),
        mul_nonneg hz2.le (neg_nonneg.2 hcs2)]
    · have hV := planarVertex_capTwo h1 h2 h3 hS
      have hkey : (-4*w1^2*w2 + 3*w1^2 - 4*w1*w2^2 + 6*w1*w2 + w1*w3 - 3*w1 + 3*w2^2 + w2*w3 - 3*w2 + 2*w3^2 - 2*w3)
            + z1 * (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3)
            + z2 * (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3)
          = (-2*w1^2*w2^2 + w1^2*w2*w3 - w1^2*w2 - w1^2*w3 + 2*w1^2 - 2*w1*w2^3 - w1*w2^2*w3 + 2*w1*w2^2 + w1*w2*w3^2 + w1*w2 - w1*w3^2 + 2*w1*w3 - 2*w1 + w2^3 + 2*w2^2*w3 - w2^2 + w2*w3^2 - 2*w2*w3 + w3^2 - w3)
            + z1 * (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3)
            + (z2 - (1-w2)) * (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3) := by ring
      nlinarith [hkey, hV, mul_nonneg hz1.le (neg_nonneg.2 hcs1),
        mul_nonneg (by linarith : (0:ℝ) ≤ (1-w2)-z2) hcs2]
  · rcases le_total (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3) 0 with hcs2 | hcs2
    · have hV := planarVertex_capOne h1 h2 h3 hS
      have hkey : (-4*w1^2*w2 + 3*w1^2 - 4*w1*w2^2 + 6*w1*w2 + w1*w3 - 3*w1 + 3*w2^2 + w2*w3 - 3*w2 + 2*w3^2 - 2*w3)
            + z1 * (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3)
            + z2 * (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3)
          = (-2*w1^3*w2 + w1^3 - 2*w1^2*w2^2 - w1^2*w2*w3 + 2*w1^2*w2 + 2*w1^2*w3 - w1^2 + w1*w2^2*w3 - w1*w2^2 + w1*w2*w3^2 + w1*w2 + w1*w3^2 - 2*w1*w3 - w2^2*w3 + 2*w2^2 - w2*w3^2 + 2*w2*w3 - 2*w2 + w3^2 - w3)
            + (z1 - (1-w1)) * (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3)
            + z2 * (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3) := by ring
      nlinarith [hkey, hV, mul_nonneg (by linarith : (0:ℝ) ≤ (1-w1)-z1) hcs1,
        mul_nonneg hz2.le (neg_nonneg.2 hcs2)]
    · rcases le_total (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3) (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3) with hcc | hcc
      · have hE : (0:ℝ) < w1*w3*(1-w1-w3) + w3*(1-w3) + w2*(2*(1-w1-w3)+3*w1*w3) := by
          nlinarith [mul_pos h1 h3, mul_pos (mul_pos h1 h3) h2,
            mul_pos h3 (by linarith : (0:ℝ) < 1-w3),
            mul_pos h2 (by linarith : (0:ℝ) < 1-w1-w3)]
        have hkey : (-4*w1^2*w2 + 3*w1^2 - 4*w1*w2^2 + 6*w1*w2 + w1*w3 - 3*w1 + 3*w2^2 + w2*w3 - 3*w2 + 2*w3^2 - 2*w3)
              + z1 * (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3)
              + z2 * (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3)
            = (w1+w2+w3-1) * (w1*w3*(1-w1-w3) + w3*(1-w3) + w2*(2*(1-w1-w3)+3*w1*w3))
              + (z1+z2-(1+w3)) * (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3)
              + (z1-(1-w1)) * ((2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3) - (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3)) := by ring
        nlinarith [hkey, mul_pos (by linarith : (0:ℝ) < 1-(w1+w2+w3)) hE,
          mul_nonneg (by linarith : (0:ℝ) ≤ (1+w3)-(z1+z2)) hcs2,
          mul_nonneg (by linarith : (0:ℝ) ≤ (1-w1)-z1)
            (by linarith : (0:ℝ) ≤ (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3) - (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3))]
      · have hE : (0:ℝ) < 2*w1*(1-w2-w3) + 3*w1*w2*w3 + w2*w3*(1-w2-w3) + w3*(1-w3) := by
          nlinarith [mul_pos (mul_pos h1 h2) h3, mul_pos h2 h3,
            mul_pos h3 (by linarith : (0:ℝ) < 1-w3),
            mul_pos h1 (by linarith : (0:ℝ) < 1-w2-w3),
            mul_pos (mul_pos h2 h3) (by linarith : (0:ℝ) < 1-w2-w3)]
        have hkey : (-4*w1^2*w2 + 3*w1^2 - 4*w1*w2^2 + 6*w1*w2 + w1*w3 - 3*w1 + 3*w2^2 + w2*w3 - 3*w2 + 2*w3^2 - 2*w3)
              + z1 * (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3)
              + z2 * (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3)
            = (w1+w2+w3-1) * (2*w1*(1-w2-w3) + 3*w1*w2*w3 + w2*w3*(1-w2-w3) + w3*(1-w3))
              + (z1+z2-(1+w3)) * (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3)
              + (z2-(1-w2)) * ((2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3) - (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3)) := by ring
        nlinarith [hkey, mul_pos (by linarith : (0:ℝ) < 1-(w1+w2+w3)) hE,
          mul_nonneg (by linarith : (0:ℝ) ≤ (1+w3)-(z1+z2)) hcs1,
          mul_nonneg (by linarith : (0:ℝ) ≤ (1-w2)-z2)
            (by linarith : (0:ℝ) ≤ (2*w1^2*w2 - w1^2*w3 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - w1*w3^2 + w1*w3 + w1 - w2^2 - 2*w2*w3 + 3*w2 - w3^2 + w3) - (2*w1^2*w2 - w1^2 + 2*w1*w2^2 + w1*w2*w3 - 4*w1*w2 - 2*w1*w3 + 3*w1 - w2^2*w3 - w2^2 - w2*w3^2 + w2*w3 + w2 - w3^2 + w3))]

/-- **Only pair one fat, pairs two and three thin.** -/
theorem planarPolygon_oneFat {w1 w2 w3 z1 z2 z3 : ℝ}
    (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3) (hS : w1 + w2 + w3 < 1)
    (hz1 : 0 < z1) (hzs : z1 + z2 + z3 = 2)
    (ht2 : 1 - w2 ≤ z2) (ht3 : 1 - w3 ≤ z3) :
    (-2*w1^2*w2 + 2*w1^2 - 2*w1*w2^2 + 3*w1*w2 + w1*w3 - 2*w1 + w2^2 - w2 + w3^2 - w3)
      + z1 * (w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3)
      + z2 * (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3) < 0 := by
  have hw1 : w1 < 1 := by linarith
  have hw2 : w2 < 1 := by linarith
  have hw3 : w3 < 1 := by linarith
  have hcap1 : z1 ≤ w2 + w3 := by linarith
  have hsum12 : z1 + z2 ≤ 1 + w3 := by linarith
  have hEA : (0:ℝ) < 2*w1*(1-w2)*(1-w3) + w2*(1-w2) + w3*(1-w3) := by
    nlinarith [mul_pos (mul_pos h1 (by linarith : (0:ℝ) < 1-w2))
        (by linarith : (0:ℝ) < 1-w3),
      mul_pos h2 (by linarith : (0:ℝ) < 1-w2),
      mul_pos h3 (by linarith : (0:ℝ) < 1-w3)]
  rcases le_total (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3) 0 with hcs2 | hcs2
  · rcases le_total (w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3) 0 with hcs1 | hcs1
    · have hV := planarVertex_oneFat_capTwo h1 h2 h3 hS
      have hkey : (-2*w1^2*w2 + 2*w1^2 - 2*w1*w2^2 + 3*w1*w2 + w1*w3 - 2*w1 + w2^2 - w2 + w3^2 - w3)
            + z1 * (w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3)
            + z2 * (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3)
          = (-w1^2*w2^2 + w1^2*w2*w3 - w1^2*w2 - w1^2*w3 + 2*w1^2 - w1*w2^3 + w1*w2*w3^2 - w1*w2*w3 + 2*w1*w2 - w1*w3^2 + 2*w1*w3 - 2*w1 + w2^2 - w2 + w3^2 - w3)
            + z1 * (w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3)
            + (z2-(1-w2)) * (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3) := by ring
      nlinarith [hkey, hV, mul_nonneg hz1.le (neg_nonneg.2 hcs1),
        mul_nonneg (by linarith : (0:ℝ) ≤ z2-(1-w2)) (neg_nonneg.2 hcs2)]
    · have hkey : (-2*w1^2*w2 + 2*w1^2 - 2*w1*w2^2 + 3*w1*w2 + w1*w3 - 2*w1 + w2^2 - w2 + w3^2 - w3)
            + z1 * (w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3)
            + z2 * (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3)
          = (w1+w2+w3-1) * (2*w1*(1-w2)*(1-w3) + w2*(1-w2) + w3*(1-w3))
            + (z1-(w2+w3)) * (w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3)
            + (z2-(1-w2)) * (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3) := by ring
      nlinarith [hkey, mul_pos (by linarith : (0:ℝ) < 1-(w1+w2+w3)) hEA,
        mul_nonneg (by linarith : (0:ℝ) ≤ (w2+w3)-z1) hcs1,
        mul_nonneg (by linarith : (0:ℝ) ≤ z2-(1-w2)) (neg_nonneg.2 hcs2)]
  · rcases le_total (w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3) (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3) with hcc | hcc
    · have hV := planarVertex_oneFat_sum h1 h2 h3 hS
      have hkey : (-2*w1^2*w2 + 2*w1^2 - 2*w1*w2^2 + 3*w1*w2 + w1*w3 - 2*w1 + w2^2 - w2 + w3^2 - w3)
            + z1 * (w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3)
            + z2 * (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3)
          = (w1^2*w2*w3 - w1^2*w2 - w1^2*w3^2 - w1^2*w3 + 2*w1^2 + w1*w2^2*w3 - w1*w2^2 - w1*w2*w3 + 2*w1*w2 - w1*w3^3 + 2*w1*w3 - 2*w1 + w2^2 - w2 + w3^2 - w3)
            + (z1+z2-(1+w3)) * (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3)
            + z1 * ((w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3) - (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3)) := by ring
      nlinarith [hkey, hV,
        mul_nonneg (by linarith : (0:ℝ) ≤ (1+w3)-(z1+z2)) hcs2,
        mul_nonneg hz1.le (by linarith : (0:ℝ) ≤ (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3) - (w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3))]
    · have hkey : (-2*w1^2*w2 + 2*w1^2 - 2*w1*w2^2 + 3*w1*w2 + w1*w3 - 2*w1 + w2^2 - w2 + w3^2 - w3)
            + z1 * (w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3)
            + z2 * (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3)
          = (w1+w2+w3-1) * (2*w1*(1-w2)*(1-w3) + w2*(1-w2) + w3*(1-w3))
            + (z1+z2-(1+w3)) * (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3)
            + (z1-(w2+w3)) * ((w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3) - (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3)) := by ring
      nlinarith [hkey, mul_pos (by linarith : (0:ℝ) < 1-(w1+w2+w3)) hEA,
        mul_nonneg (by linarith : (0:ℝ) ≤ (1+w3)-(z1+z2)) hcs2,
        mul_nonneg (by linarith : (0:ℝ) ≤ (w2+w3)-z1)
          (by linarith : (0:ℝ) ≤ (w1^2*w2 - w1^2 + w1*w2^2 + w1*w2*w3 - 3*w1*w2 - 2*w1*w3 + 3*w1 - w2^2 + w2 - w3^2 + w3) - (w1^2*w2 - w1^2*w3 + w1*w2^2 - w1*w2 - w1*w3^2 + w1*w3))]


/-! ## 3. The starred case refutations -/

/-- **All three pairs fat: the starred triple is contradictory.** -/
theorem planarCase_allFat {A1 A2 A3 L1 L2 L3 D lam : ℝ}
    (hlam : 2 < lam) (hD : 0 < D)
    (hA1 : 2 < A1) (hA2 : 2 < A2) (hA3 : 2 < A3)
    (hA1l : A1 < lam) (hA2l : A2 < lam) (hA3l : A3 < lam)
    (hAsum : A1 + A2 + A3 = 2*lam + 2)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hL3 : 0 < L3)
    (hledger : A1*L1 + A2*L2 + A3*L3 = 2*lam*D)
    (hf1 : L1 < D)
    (hf2 : L2 < D)
    (hf3 : L3 < D)

    (hstar1 : -A1^2*A2*L1^2 - A1^2*A3*L1^2 + A1*A2*D*L1*lam + A1*A3*D*L1*lam + A2^3*L2^2 - A2^2*A3*L2^2 - A2^2*D*L2*lam - A2*A3^2*L3^2 + A2*A3*D*L2*lam + A2*A3*D*L3*lam + A3^3*L3^2 - A3^2*D*L3*lam
      ≥ 2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1*lam - 2*A1*A2*A3*D*L2 - 2*A1*A2*A3*D*L3 + 2*A1*A2*A3*L1*L2 + 2*A1*A2*A3*L1*L3)
    (hstar2 : A1^3*L1^2 - A1^2*A3*L1^2 - A1^2*D*L1*lam - A1*A2^2*L2^2 + A1*A2*D*L2*lam - A1*A3^2*L3^2 + A1*A3*D*L1*lam + A1*A3*D*L3*lam - A2^2*A3*L2^2 + A2*A3*D*L2*lam + A3^3*L3^2 - A3^2*D*L3*lam
      ≥ 2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1 - 2*A1*A2*A3*D*L2*lam - 2*A1*A2*A3*D*L3 + 2*A1*A2*A3*L1*L2 + 2*A1*A2*A3*L2*L3)
    (hstar3 : A1^3*L1^2 - A1^2*A2*L1^2 - A1^2*D*L1*lam - A1*A2^2*L2^2 + A1*A2*D*L1*lam + A1*A2*D*L2*lam - A1*A3^2*L3^2 + A1*A3*D*L3*lam + A2^3*L2^2 - A2^2*D*L2*lam - A2*A3^2*L3^2 + A2*A3*D*L3*lam
      ≥ 2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1 - 2*A1*A2*A3*D*L2 - 2*A1*A2*A3*D*L3*lam + 2*A1*A2*A3*L1*L3 + 2*A1*A2*A3*L2*L3) : False := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hD0 : lam * D ≠ 0 := by positivity
  have hw1 : 0 < (lam - A1)/lam := div_pos (by linarith) hlam0
  have hw2 : 0 < (lam - A2)/lam := div_pos (by linarith) hlam0
  have hw3 : 0 < (lam - A3)/lam := div_pos (by linarith) hlam0
  have hS : (lam - A1)/lam + (lam - A2)/lam + (lam - A3)/lam < 1 := by
    rw [← add_div, ← add_div, div_lt_one hlam0]
    linarith
  have hz1 : 0 < A1*L1/(lam*D) :=
    div_pos (mul_pos (by linarith) hL1) (mul_pos hlam0 hD)
  have hz2 : 0 < A2*L2/(lam*D) :=
    div_pos (mul_pos (by linarith) hL2) (mul_pos hlam0 hD)
  have hz3 : 0 < A3*L3/(lam*D) :=
    div_pos (mul_pos (by linarith) hL3) (mul_pos hlam0 hD)
  have hzs : A1*L1/(lam*D) + A2*L2/(lam*D) + A3*L3/(lam*D) = 2 := by
    rw [← add_div, ← add_div, div_eq_iff hD0]
    linarith
  have hc1 : A1*L1/(lam*D) < 1 - (lam - A1)/lam := by
    rw [show (1:ℝ) - (lam - A1)/lam = A1/lam from by field_simp; try ring]
    rw [div_lt_div_iff₀ (mul_pos hlam0 hD) hlam0]
    nlinarith [mul_pos hlam0 (mul_pos (show (0:ℝ) < A1 by linarith) (sub_pos.2 hf1))]
  have hc2 : A2*L2/(lam*D) < 1 - (lam - A2)/lam := by
    rw [show (1:ℝ) - (lam - A2)/lam = A2/lam from by field_simp; try ring]
    rw [div_lt_div_iff₀ (mul_pos hlam0 hD) hlam0]
    nlinarith [mul_pos hlam0 (mul_pos (show (0:ℝ) < A2 by linarith) (sub_pos.2 hf2))]
  have hc3 : A3*L3/(lam*D) < 1 - (lam - A3)/lam := by
    rw [show (1:ℝ) - (lam - A3)/lam = A3/lam from by field_simp; try ring]
    rw [div_lt_div_iff₀ (mul_pos hlam0 hD) hlam0]
    nlinarith [mul_pos hlam0 (mul_pos (show (0:ℝ) < A3 by linarith) (sub_pos.2 hf3))]

  have h1 := hw1
  have h2 := hw2
  have h3 := hw3
  have hpoly := planarPolygon_allFat h1 h2 h3 hS hz1 hz2 hz3 hzs hc1 hc2 hc3
  have hz3eq : A3*L3/(lam*D) = 2 - A1*L1/(lam*D) - A2*L2/(lam*D) := by
    linarith [hzs]
  rw [hz3eq] at hpoly
  have hbridge : ((-A1^2*A2*L1^2 - A1^2*A3*L1^2 + A1*A2*D*L1*lam + A1*A3*D*L1*lam + A2^3*L2^2 - A2^2*A3*L2^2 - A2^2*D*L2*lam - A2*A3^2*L3^2 + A2*A3*D*L2*lam + A2*A3*D*L3*lam + A3^3*L3^2 - A3^2*D*L3*lam) - (2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1*lam - 2*A1*A2*A3*D*L2 - 2*A1*A2*A3*D*L3 + 2*A1*A2*A3*L1*L2 + 2*A1*A2*A3*L1*L3)) + ((A1^3*L1^2 - A1^2*A3*L1^2 - A1^2*D*L1*lam - A1*A2^2*L2^2 + A1*A2*D*L2*lam - A1*A3^2*L3^2 + A1*A3*D*L1*lam + A1*A3*D*L3*lam - A2^2*A3*L2^2 + A2*A3*D*L2*lam + A3^3*L3^2 - A3^2*D*L3*lam) - (2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1 - 2*A1*A2*A3*D*L2*lam - 2*A1*A2*A3*D*L3 + 2*A1*A2*A3*L1*L2 + 2*A1*A2*A3*L2*L3)) + ((A1^3*L1^2 - A1^2*A2*L1^2 - A1^2*D*L1*lam - A1*A2^2*L2^2 + A1*A2*D*L1*lam + A1*A2*D*L2*lam - A1*A3^2*L3^2 + A1*A3*D*L3*lam + A2^3*L2^2 - A2^2*D*L2*lam - A2*A3^2*L3^2 + A2*A3*D*L3*lam) - (2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1 - 2*A1*A2*A3*D*L2 - 2*A1*A2*A3*D*L3*lam + 2*A1*A2*A3*L1*L3 + 2*A1*A2*A3*L2*L3))
      = 2 * D * (-A1^3*A2*L1 + A1^3*L1*lam - A1^2*A2^2*L1 - A1^2*A2^2*L2 + A1^2*A2*A3*L2 + 2*A1^2*A2*D*lam + 2*A1^2*A2*L1*lam - A1^2*D*lam^2 - 2*A1^2*L1*lam^2 - A1*A2^3*L2 + A1*A2^2*A3*L1 + 2*A1*A2^2*D*lam + 2*A1*A2^2*L2*lam + A1*A2*A3^2*L1 + A1*A2*A3^2*L2 - A1*A2*A3*D*lam - 2*A1*A2*A3*L1*lam - 2*A1*A2*A3*L2*lam - 4*A1*A2*D*lam^2 - A1*A3^2*L1*lam + 2*A1*A3*L1*lam^2 + 2*A1*D*lam^3 + A2^3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - A2*A3^2*L2*lam + 2*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + A3^2*D*lam^2 - 2*A3*D*lam^3) := by
    linear_combination (2*A1^2*A2*D - 2*A1^2*D*lam + 2*A1^2*L1 + 2*A1*A2^2*D - 4*A1*A2*D*lam - 2*A1*A2*L1 - 2*A1*A2*L2 - 2*A1*A3*L1 - 2*A1*A3*L3 + 4*A1*D*lam^2 + 2*A1*D*lam - 2*A2^2*A3*D + 2*A2^2*L2 - 2*A2*A3^2*D + 6*A2*A3*D*lam + 4*A2*A3*D - 2*A2*A3*L2 - 2*A2*A3*L3 - 2*A2*D*lam + 2*A3^2*D*lam + 2*A3^2*L3 - 4*A3*D*lam^2 - 2*A3*D*lam) * hledger + (-2*A1*A2*A3*D*L2 - 2*A1*A2*A3*D*L3 + 2*A1*A2*D*L2*lam + 2*A1*A3*D*L3*lam - 2*A1*D^2*lam^2 + 2*A2^2*A3*D*L2 - 2*A2^2*D*L2*lam + 2*A2*A3^2*D*L3 - 4*A2*A3*D^2*lam + 2*A2*D^2*lam^2 - 2*A3^2*D*L3*lam + 2*A3*D^2*lam^2) * hAsum
  have hscale : lam^4 * D * (-((lam - A1)/lam)^2*((lam - A2)/lam)*(2 - A1*L1/(lam*D) - A2*L2/(lam*D)) - ((lam - A1)/lam)^2*((lam - A3)/lam)*(A2*L2/(lam*D)) + ((lam - A1)/lam)^2 - ((lam - A1)/lam)*((lam - A2)/lam)^2*(2 - A1*L1/(lam*D) - A2*L2/(lam*D)) + ((lam - A1)/lam)*((lam - A2)/lam)*((lam - A3)/lam) + 2*((lam - A1)/lam)*((lam - A2)/lam)*(2 - A1*L1/(lam*D) - A2*L2/(lam*D)) - ((lam - A1)/lam)*((lam - A2)/lam) - ((lam - A1)/lam)*((lam - A3)/lam)^2*(A2*L2/(lam*D)) + 2*((lam - A1)/lam)*((lam - A3)/lam)*(A2*L2/(lam*D)) - ((lam - A1)/lam)*((lam - A3)/lam) + ((lam - A1)/lam)*(A1*L1/(lam*D)) - ((lam - A1)/lam) - ((lam - A2)/lam)^2*((lam - A3)/lam)*(A1*L1/(lam*D)) + ((lam - A2)/lam)^2 - ((lam - A2)/lam)*((lam - A3)/lam)^2*(A1*L1/(lam*D)) + 2*((lam - A2)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) - ((lam - A2)/lam)*((lam - A3)/lam) + ((lam - A2)/lam)*(A2*L2/(lam*D)) - ((lam - A2)/lam) + ((lam - A3)/lam)^2 + ((lam - A3)/lam)*(2 - A1*L1/(lam*D) - A2*L2/(lam*D)) - ((lam - A3)/lam))
      = (-A1^3*A2*L1 + A1^3*L1*lam - A1^2*A2^2*L1 - A1^2*A2^2*L2 + A1^2*A2*A3*L2 + 2*A1^2*A2*D*lam + 2*A1^2*A2*L1*lam - A1^2*D*lam^2 - 2*A1^2*L1*lam^2 - A1*A2^3*L2 + A1*A2^2*A3*L1 + 2*A1*A2^2*D*lam + 2*A1*A2^2*L2*lam + A1*A2*A3^2*L1 + A1*A2*A3^2*L2 - A1*A2*A3*D*lam - 2*A1*A2*A3*L1*lam - 2*A1*A2*A3*L2*lam - 4*A1*A2*D*lam^2 - A1*A3^2*L1*lam + 2*A1*A3*L1*lam^2 + 2*A1*D*lam^3 + A2^3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - A2*A3^2*L2*lam + 2*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + A3^2*D*lam^2 - 2*A3*D*lam^3) := by
    field_simp [ne_of_gt hlam0, ne_of_gt hD]
    ring
  have hQneg : lam^4 * D * (-((lam - A1)/lam)^2*((lam - A2)/lam)*(2 - A1*L1/(lam*D) - A2*L2/(lam*D)) - ((lam - A1)/lam)^2*((lam - A3)/lam)*(A2*L2/(lam*D)) + ((lam - A1)/lam)^2 - ((lam - A1)/lam)*((lam - A2)/lam)^2*(2 - A1*L1/(lam*D) - A2*L2/(lam*D)) + ((lam - A1)/lam)*((lam - A2)/lam)*((lam - A3)/lam) + 2*((lam - A1)/lam)*((lam - A2)/lam)*(2 - A1*L1/(lam*D) - A2*L2/(lam*D)) - ((lam - A1)/lam)*((lam - A2)/lam) - ((lam - A1)/lam)*((lam - A3)/lam)^2*(A2*L2/(lam*D)) + 2*((lam - A1)/lam)*((lam - A3)/lam)*(A2*L2/(lam*D)) - ((lam - A1)/lam)*((lam - A3)/lam) + ((lam - A1)/lam)*(A1*L1/(lam*D)) - ((lam - A1)/lam) - ((lam - A2)/lam)^2*((lam - A3)/lam)*(A1*L1/(lam*D)) + ((lam - A2)/lam)^2 - ((lam - A2)/lam)*((lam - A3)/lam)^2*(A1*L1/(lam*D)) + 2*((lam - A2)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) - ((lam - A2)/lam)*((lam - A3)/lam) + ((lam - A2)/lam)*(A2*L2/(lam*D)) - ((lam - A2)/lam) + ((lam - A3)/lam)^2 + ((lam - A3)/lam)*(2 - A1*L1/(lam*D) - A2*L2/(lam*D)) - ((lam - A3)/lam))
      < 0 := by
    have hqq := mul_pos (mul_pos (pow_pos hlam0 4) hD) (neg_pos.2 hpoly)
    nlinarith [hqq]
  have hPtneg : (-A1^3*A2*L1 + A1^3*L1*lam - A1^2*A2^2*L1 - A1^2*A2^2*L2 + A1^2*A2*A3*L2 + 2*A1^2*A2*D*lam + 2*A1^2*A2*L1*lam - A1^2*D*lam^2 - 2*A1^2*L1*lam^2 - A1*A2^3*L2 + A1*A2^2*A3*L1 + 2*A1*A2^2*D*lam + 2*A1*A2^2*L2*lam + A1*A2*A3^2*L1 + A1*A2*A3^2*L2 - A1*A2*A3*D*lam - 2*A1*A2*A3*L1*lam - 2*A1*A2*A3*L2*lam - 4*A1*A2*D*lam^2 - A1*A3^2*L1*lam + 2*A1*A3*L1*lam^2 + 2*A1*D*lam^3 + A2^3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - A2*A3^2*L2*lam + 2*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + A3^2*D*lam^2 - 2*A3*D*lam^3) < 0 := by linarith [hscale, hQneg]
  have hsum : 0 ≤ 2 * D * (-A1^3*A2*L1 + A1^3*L1*lam - A1^2*A2^2*L1 - A1^2*A2^2*L2 + A1^2*A2*A3*L2 + 2*A1^2*A2*D*lam + 2*A1^2*A2*L1*lam - A1^2*D*lam^2 - 2*A1^2*L1*lam^2 - A1*A2^3*L2 + A1*A2^2*A3*L1 + 2*A1*A2^2*D*lam + 2*A1*A2^2*L2*lam + A1*A2*A3^2*L1 + A1*A2*A3^2*L2 - A1*A2*A3*D*lam - 2*A1*A2*A3*L1*lam - 2*A1*A2*A3*L2*lam - 4*A1*A2*D*lam^2 - A1*A3^2*L1*lam + 2*A1*A3*L1*lam^2 + 2*A1*D*lam^3 + A2^3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - A2*A3^2*L2*lam + 2*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + A3^2*D*lam^2 - 2*A3*D*lam^3) := by
    linarith [hbridge, hstar1, hstar2, hstar3]
  nlinarith [hPtneg, hsum, mul_pos hD (neg_pos.2 hPtneg)]

/-- **Pairs one, two fat and pair three thin: contradictory.** -/
theorem planarCase_twoFat {A1 A2 A3 L1 L2 L3 D lam : ℝ}
    (hlam : 2 < lam) (hD : 0 < D)
    (hA1 : 2 < A1) (hA2 : 2 < A2) (hA3 : 2 < A3)
    (hA1l : A1 < lam) (hA2l : A2 < lam) (hA3l : A3 < lam)
    (hAsum : A1 + A2 + A3 = 2*lam + 2)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hL3 : 0 < L3)
    (hledger : A1*L1 + A2*L2 + A3*L3 = 2*lam*D)
    (hf1 : L1 < D)
    (hf2 : L2 < D)
    (ht3 : D ≤ L3)
    (hstar1 : -A1^2*A2*L1^2 - A1^2*A3*L1^2 + A1*A2*D*L1*lam + A1*A3*D*L1*lam + A2^3*L2^2 - A2^2*A3*L2^2 - A2^2*D*L2*lam - A2*A3^2*L3^2 + A2*A3*D*L2*lam + A2*A3*D*L3*lam + A3^3*L3^2 - A3^2*D*L3*lam
      ≥ 2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1*lam - 2*A1*A2*A3*D*L2 - 2*A1*A2*A3*D*L3 + 2*A1*A2*A3*L1*L2 + 2*A1*A2*A3*L1*L3)
    (hstar2 : A1^3*L1^2 - A1^2*A3*L1^2 - A1^2*D*L1*lam - A1*A2^2*L2^2 + A1*A2*D*L2*lam - A1*A3^2*L3^2 + A1*A3*D*L1*lam + A1*A3*D*L3*lam - A2^2*A3*L2^2 + A2*A3*D*L2*lam + A3^3*L3^2 - A3^2*D*L3*lam
      ≥ 2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1 - 2*A1*A2*A3*D*L2*lam - 2*A1*A2*A3*D*L3 + 2*A1*A2*A3*L1*L2 + 2*A1*A2*A3*L2*L3) : False := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hD0 : lam * D ≠ 0 := by positivity
  have hw1 : 0 < (lam - A1)/lam := div_pos (by linarith) hlam0
  have hw2 : 0 < (lam - A2)/lam := div_pos (by linarith) hlam0
  have hw3 : 0 < (lam - A3)/lam := div_pos (by linarith) hlam0
  have hS : (lam - A1)/lam + (lam - A2)/lam + (lam - A3)/lam < 1 := by
    rw [← add_div, ← add_div, div_lt_one hlam0]
    linarith
  have hz1 : 0 < A1*L1/(lam*D) :=
    div_pos (mul_pos (by linarith) hL1) (mul_pos hlam0 hD)
  have hz2 : 0 < A2*L2/(lam*D) :=
    div_pos (mul_pos (by linarith) hL2) (mul_pos hlam0 hD)
  have hz3 : 0 < A3*L3/(lam*D) :=
    div_pos (mul_pos (by linarith) hL3) (mul_pos hlam0 hD)
  have hzs : A1*L1/(lam*D) + A2*L2/(lam*D) + A3*L3/(lam*D) = 2 := by
    rw [← add_div, ← add_div, div_eq_iff hD0]
    linarith
  have hc1 : A1*L1/(lam*D) < 1 - (lam - A1)/lam := by
    rw [show (1:ℝ) - (lam - A1)/lam = A1/lam from by field_simp; try ring]
    rw [div_lt_div_iff₀ (mul_pos hlam0 hD) hlam0]
    nlinarith [mul_pos hlam0 (mul_pos (show (0:ℝ) < A1 by linarith) (sub_pos.2 hf1))]
  have hc2 : A2*L2/(lam*D) < 1 - (lam - A2)/lam := by
    rw [show (1:ℝ) - (lam - A2)/lam = A2/lam from by field_simp; try ring]
    rw [div_lt_div_iff₀ (mul_pos hlam0 hD) hlam0]
    nlinarith [mul_pos hlam0 (mul_pos (show (0:ℝ) < A2 by linarith) (sub_pos.2 hf2))]
  have hcf3 : 1 - (lam - A3)/lam ≤ A3*L3/(lam*D) := by
    rw [show (1:ℝ) - (lam - A3)/lam = A3/lam from by field_simp; try ring]
    rw [div_le_div_iff₀ hlam0 (mul_pos hlam0 hD)]
    nlinarith [mul_nonneg (mul_nonneg hlam0.le (show (0:ℝ) ≤ A3 by linarith)) (sub_nonneg.2 ht3)]
  have h1 := hw1
  have h2 := hw2
  have h3 := hw3
  have hpoly := planarPolygon_twoFat h1 h2 h3 hS hz1 hz2 hzs hc1 hc2 hcf3
  have hbridge : ((-A1^2*A2*L1^2 - A1^2*A3*L1^2 + A1*A2*D*L1*lam + A1*A3*D*L1*lam + A2^3*L2^2 - A2^2*A3*L2^2 - A2^2*D*L2*lam - A2*A3^2*L3^2 + A2*A3*D*L2*lam + A2*A3*D*L3*lam + A3^3*L3^2 - A3^2*D*L3*lam) - (2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1*lam - 2*A1*A2*A3*D*L2 - 2*A1*A2*A3*D*L3 + 2*A1*A2*A3*L1*L2 + 2*A1*A2*A3*L1*L3)) + ((A1^3*L1^2 - A1^2*A3*L1^2 - A1^2*D*L1*lam - A1*A2^2*L2^2 + A1*A2*D*L2*lam - A1*A3^2*L3^2 + A1*A3*D*L1*lam + A1*A3*D*L3*lam - A2^2*A3*L2^2 + A2*A3*D*L2*lam + A3^3*L3^2 - A3^2*D*L3*lam) - (2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1 - 2*A1*A2*A3*D*L2*lam - 2*A1*A2*A3*D*L3 + 2*A1*A2*A3*L1*L2 + 2*A1*A2*A3*L2*L3))
      = 1 * D * (-2*A1^3*A2*L1 + A1^3*L1*lam - 2*A1^2*A2^2*L1 - 2*A1^2*A2^2*L2 - A1^2*A2*A3*L1 + A1^2*A2*A3*L2 + 4*A1^2*A2*D*lam + 5*A1^2*A2*L1*lam - A1^2*A3*L1*lam - A1^2*D*lam^2 - 2*A1^2*L1*lam^2 - 2*A1*A2^3*L2 + A1*A2^2*A3*L1 - A1*A2^2*A3*L2 + 4*A1*A2^2*D*lam + 5*A1*A2^2*L2*lam + A1*A2*A3^2*L1 + A1*A2*A3^2*L2 - 2*A1*A2*A3*L1*lam - 2*A1*A2*A3*L2*lam - 10*A1*A2*D*lam^2 - 2*A1*A3^2*L1*lam + A1*A3*D*lam^2 + 4*A1*A3*L1*lam^2 + 2*A1*D*lam^3 + A2^3*L2*lam - A2^2*A3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - 2*A2*A3^2*L2*lam + A2*A3*D*lam^2 + 4*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + 2*A3^2*D*lam^2 - 4*A3*D*lam^3) := by
    linear_combination (2*A1^2*A2*D - A1^2*D*lam + A1^2*L1 + 2*A1*A2^2*D + A1*A2*A3*D - 5*A1*A2*D*lam - A1*A2*L1 - A1*A2*L2 + A1*A3*D*lam - 2*A1*A3*L1 - A1*A3*L3 + 2*A1*D*lam^2 + A1*D*lam - A2^2*A3*D + A2^2*L2 - A2*A3^2*D + 4*A2*A3*D*lam + 2*A2*A3*D - 2*A2*A3*L2 - A2*A3*L3 - A2*D*lam + 2*A3^2*D*lam + 2*A3^2*L3 - 4*A3*D*lam^2 - 2*A3*D*lam) * hledger + (-A1*A2*A3*D*L2 - 2*A1*A2*A3*D*L3 + A1*A2*D*L2*lam + A1*A3*D*L3*lam - A1*D^2*lam^2 + A2^2*A3*D*L2 - A2^2*D*L2*lam + A2*A3^2*D*L3 - 2*A2*A3*D^2*lam + A2*D^2*lam^2 - 2*A3^2*D*L3*lam + 2*A3*D^2*lam^2) * hAsum
  have hscale : lam^4 * D * (2*((lam - A1)/lam)^2*((lam - A2)/lam)*(A1*L1/(lam*D)) + 2*((lam - A1)/lam)^2*((lam - A2)/lam)*(A2*L2/(lam*D)) - 4*((lam - A1)/lam)^2*((lam - A2)/lam) - ((lam - A1)/lam)^2*((lam - A3)/lam)*(A2*L2/(lam*D)) - ((lam - A1)/lam)^2*(A1*L1/(lam*D)) - ((lam - A1)/lam)^2*(A2*L2/(lam*D)) + 3*((lam - A1)/lam)^2 + 2*((lam - A1)/lam)*((lam - A2)/lam)^2*(A1*L1/(lam*D)) + 2*((lam - A1)/lam)*((lam - A2)/lam)^2*(A2*L2/(lam*D)) - 4*((lam - A1)/lam)*((lam - A2)/lam)^2 + ((lam - A1)/lam)*((lam - A2)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) + ((lam - A1)/lam)*((lam - A2)/lam)*((lam - A3)/lam)*(A2*L2/(lam*D)) - 4*((lam - A1)/lam)*((lam - A2)/lam)*(A1*L1/(lam*D)) - 4*((lam - A1)/lam)*((lam - A2)/lam)*(A2*L2/(lam*D)) + 6*((lam - A1)/lam)*((lam - A2)/lam) - ((lam - A1)/lam)*((lam - A3)/lam)^2*(A2*L2/(lam*D)) - 2*((lam - A1)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) + ((lam - A1)/lam)*((lam - A3)/lam)*(A2*L2/(lam*D)) + ((lam - A1)/lam)*((lam - A3)/lam) + 3*((lam - A1)/lam)*(A1*L1/(lam*D)) + ((lam - A1)/lam)*(A2*L2/(lam*D)) - 3*((lam - A1)/lam) - ((lam - A2)/lam)^2*((lam - A3)/lam)*(A1*L1/(lam*D)) - ((lam - A2)/lam)^2*(A1*L1/(lam*D)) - ((lam - A2)/lam)^2*(A2*L2/(lam*D)) + 3*((lam - A2)/lam)^2 - ((lam - A2)/lam)*((lam - A3)/lam)^2*(A1*L1/(lam*D)) + ((lam - A2)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) - 2*((lam - A2)/lam)*((lam - A3)/lam)*(A2*L2/(lam*D)) + ((lam - A2)/lam)*((lam - A3)/lam) + ((lam - A2)/lam)*(A1*L1/(lam*D)) + 3*((lam - A2)/lam)*(A2*L2/(lam*D)) - 3*((lam - A2)/lam) - ((lam - A3)/lam)^2*(A1*L1/(lam*D)) - ((lam - A3)/lam)^2*(A2*L2/(lam*D)) + 2*((lam - A3)/lam)^2 + ((lam - A3)/lam)*(A1*L1/(lam*D)) + ((lam - A3)/lam)*(A2*L2/(lam*D)) - 2*((lam - A3)/lam))
      = (-2*A1^3*A2*L1 + A1^3*L1*lam - 2*A1^2*A2^2*L1 - 2*A1^2*A2^2*L2 - A1^2*A2*A3*L1 + A1^2*A2*A3*L2 + 4*A1^2*A2*D*lam + 5*A1^2*A2*L1*lam - A1^2*A3*L1*lam - A1^2*D*lam^2 - 2*A1^2*L1*lam^2 - 2*A1*A2^3*L2 + A1*A2^2*A3*L1 - A1*A2^2*A3*L2 + 4*A1*A2^2*D*lam + 5*A1*A2^2*L2*lam + A1*A2*A3^2*L1 + A1*A2*A3^2*L2 - 2*A1*A2*A3*L1*lam - 2*A1*A2*A3*L2*lam - 10*A1*A2*D*lam^2 - 2*A1*A3^2*L1*lam + A1*A3*D*lam^2 + 4*A1*A3*L1*lam^2 + 2*A1*D*lam^3 + A2^3*L2*lam - A2^2*A3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - 2*A2*A3^2*L2*lam + A2*A3*D*lam^2 + 4*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + 2*A3^2*D*lam^2 - 4*A3*D*lam^3) := by
    field_simp [ne_of_gt hlam0, ne_of_gt hD]
    ring
  have hQneg : lam^4 * D * (2*((lam - A1)/lam)^2*((lam - A2)/lam)*(A1*L1/(lam*D)) + 2*((lam - A1)/lam)^2*((lam - A2)/lam)*(A2*L2/(lam*D)) - 4*((lam - A1)/lam)^2*((lam - A2)/lam) - ((lam - A1)/lam)^2*((lam - A3)/lam)*(A2*L2/(lam*D)) - ((lam - A1)/lam)^2*(A1*L1/(lam*D)) - ((lam - A1)/lam)^2*(A2*L2/(lam*D)) + 3*((lam - A1)/lam)^2 + 2*((lam - A1)/lam)*((lam - A2)/lam)^2*(A1*L1/(lam*D)) + 2*((lam - A1)/lam)*((lam - A2)/lam)^2*(A2*L2/(lam*D)) - 4*((lam - A1)/lam)*((lam - A2)/lam)^2 + ((lam - A1)/lam)*((lam - A2)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) + ((lam - A1)/lam)*((lam - A2)/lam)*((lam - A3)/lam)*(A2*L2/(lam*D)) - 4*((lam - A1)/lam)*((lam - A2)/lam)*(A1*L1/(lam*D)) - 4*((lam - A1)/lam)*((lam - A2)/lam)*(A2*L2/(lam*D)) + 6*((lam - A1)/lam)*((lam - A2)/lam) - ((lam - A1)/lam)*((lam - A3)/lam)^2*(A2*L2/(lam*D)) - 2*((lam - A1)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) + ((lam - A1)/lam)*((lam - A3)/lam)*(A2*L2/(lam*D)) + ((lam - A1)/lam)*((lam - A3)/lam) + 3*((lam - A1)/lam)*(A1*L1/(lam*D)) + ((lam - A1)/lam)*(A2*L2/(lam*D)) - 3*((lam - A1)/lam) - ((lam - A2)/lam)^2*((lam - A3)/lam)*(A1*L1/(lam*D)) - ((lam - A2)/lam)^2*(A1*L1/(lam*D)) - ((lam - A2)/lam)^2*(A2*L2/(lam*D)) + 3*((lam - A2)/lam)^2 - ((lam - A2)/lam)*((lam - A3)/lam)^2*(A1*L1/(lam*D)) + ((lam - A2)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) - 2*((lam - A2)/lam)*((lam - A3)/lam)*(A2*L2/(lam*D)) + ((lam - A2)/lam)*((lam - A3)/lam) + ((lam - A2)/lam)*(A1*L1/(lam*D)) + 3*((lam - A2)/lam)*(A2*L2/(lam*D)) - 3*((lam - A2)/lam) - ((lam - A3)/lam)^2*(A1*L1/(lam*D)) - ((lam - A3)/lam)^2*(A2*L2/(lam*D)) + 2*((lam - A3)/lam)^2 + ((lam - A3)/lam)*(A1*L1/(lam*D)) + ((lam - A3)/lam)*(A2*L2/(lam*D)) - 2*((lam - A3)/lam))
      < 0 := by
    have hqq := mul_pos (mul_pos (pow_pos hlam0 4) hD) (neg_pos.2 hpoly)
    nlinarith [hqq]
  have hPtneg : (-2*A1^3*A2*L1 + A1^3*L1*lam - 2*A1^2*A2^2*L1 - 2*A1^2*A2^2*L2 - A1^2*A2*A3*L1 + A1^2*A2*A3*L2 + 4*A1^2*A2*D*lam + 5*A1^2*A2*L1*lam - A1^2*A3*L1*lam - A1^2*D*lam^2 - 2*A1^2*L1*lam^2 - 2*A1*A2^3*L2 + A1*A2^2*A3*L1 - A1*A2^2*A3*L2 + 4*A1*A2^2*D*lam + 5*A1*A2^2*L2*lam + A1*A2*A3^2*L1 + A1*A2*A3^2*L2 - 2*A1*A2*A3*L1*lam - 2*A1*A2*A3*L2*lam - 10*A1*A2*D*lam^2 - 2*A1*A3^2*L1*lam + A1*A3*D*lam^2 + 4*A1*A3*L1*lam^2 + 2*A1*D*lam^3 + A2^3*L2*lam - A2^2*A3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - 2*A2*A3^2*L2*lam + A2*A3*D*lam^2 + 4*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + 2*A3^2*D*lam^2 - 4*A3*D*lam^3) < 0 := by linarith [hscale, hQneg]
  have hsum : 0 ≤ 1 * D * (-2*A1^3*A2*L1 + A1^3*L1*lam - 2*A1^2*A2^2*L1 - 2*A1^2*A2^2*L2 - A1^2*A2*A3*L1 + A1^2*A2*A3*L2 + 4*A1^2*A2*D*lam + 5*A1^2*A2*L1*lam - A1^2*A3*L1*lam - A1^2*D*lam^2 - 2*A1^2*L1*lam^2 - 2*A1*A2^3*L2 + A1*A2^2*A3*L1 - A1*A2^2*A3*L2 + 4*A1*A2^2*D*lam + 5*A1*A2^2*L2*lam + A1*A2*A3^2*L1 + A1*A2*A3^2*L2 - 2*A1*A2*A3*L1*lam - 2*A1*A2*A3*L2*lam - 10*A1*A2*D*lam^2 - 2*A1*A3^2*L1*lam + A1*A3*D*lam^2 + 4*A1*A3*L1*lam^2 + 2*A1*D*lam^3 + A2^3*L2*lam - A2^2*A3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - 2*A2*A3^2*L2*lam + A2*A3*D*lam^2 + 4*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + 2*A3^2*D*lam^2 - 4*A3*D*lam^3) := by
    linarith [hbridge, hstar1, hstar2]
  nlinarith [hPtneg, hsum, mul_pos hD (neg_pos.2 hPtneg)]

/-- **Pair one fat, pairs two, three thin: contradictory.** -/
theorem planarCase_oneFat {A1 A2 A3 L1 L2 L3 D lam : ℝ}
    (hlam : 2 < lam) (hD : 0 < D)
    (hA1 : 2 < A1) (hA2 : 2 < A2) (hA3 : 2 < A3)
    (hA1l : A1 < lam) (hA2l : A2 < lam) (hA3l : A3 < lam)
    (hAsum : A1 + A2 + A3 = 2*lam + 2)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hL3 : 0 < L3)
    (hledger : A1*L1 + A2*L2 + A3*L3 = 2*lam*D)
    (hf1 : L1 < D)
    (ht2 : D ≤ L2)
    (ht3 : D ≤ L3)
    (hstar1 : -A1^2*A2*L1^2 - A1^2*A3*L1^2 + A1*A2*D*L1*lam + A1*A3*D*L1*lam + A2^3*L2^2 - A2^2*A3*L2^2 - A2^2*D*L2*lam - A2*A3^2*L3^2 + A2*A3*D*L2*lam + A2*A3*D*L3*lam + A3^3*L3^2 - A3^2*D*L3*lam
      ≥ 2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1*lam - 2*A1*A2*A3*D*L2 - 2*A1*A2*A3*D*L3 + 2*A1*A2*A3*L1*L2 + 2*A1*A2*A3*L1*L3) : False := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hD0 : lam * D ≠ 0 := by positivity
  have hw1 : 0 < (lam - A1)/lam := div_pos (by linarith) hlam0
  have hw2 : 0 < (lam - A2)/lam := div_pos (by linarith) hlam0
  have hw3 : 0 < (lam - A3)/lam := div_pos (by linarith) hlam0
  have hS : (lam - A1)/lam + (lam - A2)/lam + (lam - A3)/lam < 1 := by
    rw [← add_div, ← add_div, div_lt_one hlam0]
    linarith
  have hz1 : 0 < A1*L1/(lam*D) :=
    div_pos (mul_pos (by linarith) hL1) (mul_pos hlam0 hD)
  have hz2 : 0 < A2*L2/(lam*D) :=
    div_pos (mul_pos (by linarith) hL2) (mul_pos hlam0 hD)
  have hz3 : 0 < A3*L3/(lam*D) :=
    div_pos (mul_pos (by linarith) hL3) (mul_pos hlam0 hD)
  have hzs : A1*L1/(lam*D) + A2*L2/(lam*D) + A3*L3/(lam*D) = 2 := by
    rw [← add_div, ← add_div, div_eq_iff hD0]
    linarith
  have hc1 : A1*L1/(lam*D) < 1 - (lam - A1)/lam := by
    rw [show (1:ℝ) - (lam - A1)/lam = A1/lam from by field_simp; try ring]
    rw [div_lt_div_iff₀ (mul_pos hlam0 hD) hlam0]
    nlinarith [mul_pos hlam0 (mul_pos (show (0:ℝ) < A1 by linarith) (sub_pos.2 hf1))]
  have hcf2 : 1 - (lam - A2)/lam ≤ A2*L2/(lam*D) := by
    rw [show (1:ℝ) - (lam - A2)/lam = A2/lam from by field_simp; try ring]
    rw [div_le_div_iff₀ hlam0 (mul_pos hlam0 hD)]
    nlinarith [mul_nonneg (mul_nonneg hlam0.le (show (0:ℝ) ≤ A2 by linarith)) (sub_nonneg.2 ht2)]
  have hcf3 : 1 - (lam - A3)/lam ≤ A3*L3/(lam*D) := by
    rw [show (1:ℝ) - (lam - A3)/lam = A3/lam from by field_simp; try ring]
    rw [div_le_div_iff₀ hlam0 (mul_pos hlam0 hD)]
    nlinarith [mul_nonneg (mul_nonneg hlam0.le (show (0:ℝ) ≤ A3 by linarith)) (sub_nonneg.2 ht3)]
  have h1 := hw1
  have h2 := hw2
  have h3 := hw3
  have hpoly := planarPolygon_oneFat h1 h2 h3 hS hz1 hzs hcf2 hcf3
  have hbridge : ((-A1^2*A2*L1^2 - A1^2*A3*L1^2 + A1*A2*D*L1*lam + A1*A3*D*L1*lam + A2^3*L2^2 - A2^2*A3*L2^2 - A2^2*D*L2*lam - A2*A3^2*L3^2 + A2*A3*D*L2*lam + A2*A3*D*L3*lam + A3^3*L3^2 - A3^2*D*L3*lam) - (2*A1*A2*A3*D^2*lam - 2*A1*A2*A3*D*L1*lam - 2*A1*A2*A3*D*L2 - 2*A1*A2*A3*D*L3 + 2*A1*A2*A3*L1*L2 + 2*A1*A2*A3*L1*L3))
      = 1 * D * (-A1^3*A2*L1 - A1^2*A2^2*L1 - A1^2*A2^2*L2 - A1^2*A2*A3*L1 + A1^2*A2*A3*L2 + 2*A1^2*A2*D*lam + 2*A1^2*A2*L1*lam - A1^2*A3*L1*lam - A1*A2^3*L2 + 2*A1*A2^2*D*lam + 3*A1*A2^2*L2*lam + A1*A2*A3^2*L2 + A1*A2*A3*L1*lam - 3*A1*A2*A3*L2*lam - 5*A1*A2*D*lam^2 - A1*A3^2*L1*lam + A1*A3*D*lam^2 + 2*A1*A3*L1*lam^2 + A2^3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - A2*A3^2*L2*lam + 2*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + A3^2*D*lam^2 - 2*A3*D*lam^3) := by
    linear_combination (A1^2*A2*D + A1*A2^2*D + A1*A2*A3*D - 2*A1*A2*D*lam - A1*A2*L1 + A1*A3*D*lam - A1*A3*L1 + A2^2*L2 + A2*A3*D*lam - A2*A3*L2 - A2*A3*L3 - A2*D*lam + A3^2*D*lam + A3^2*L3 - 2*A3*D*lam^2 - A3*D*lam) * hledger + (-A1*A2*A3*D*L2 - A1*A2*A3*D*L3 - A2^2*D*L2*lam + A2*D^2*lam^2 - A3^2*D*L3*lam + A3*D^2*lam^2) * hAsum
  have hscale : lam^4 * D * (((lam - A1)/lam)^2*((lam - A2)/lam)*(A1*L1/(lam*D)) + ((lam - A1)/lam)^2*((lam - A2)/lam)*(A2*L2/(lam*D)) - 2*((lam - A1)/lam)^2*((lam - A2)/lam) - ((lam - A1)/lam)^2*((lam - A3)/lam)*(A2*L2/(lam*D)) - ((lam - A1)/lam)^2*(A1*L1/(lam*D)) + 2*((lam - A1)/lam)^2 + ((lam - A1)/lam)*((lam - A2)/lam)^2*(A1*L1/(lam*D)) + ((lam - A1)/lam)*((lam - A2)/lam)^2*(A2*L2/(lam*D)) - 2*((lam - A1)/lam)*((lam - A2)/lam)^2 + ((lam - A1)/lam)*((lam - A2)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) - 3*((lam - A1)/lam)*((lam - A2)/lam)*(A1*L1/(lam*D)) - ((lam - A1)/lam)*((lam - A2)/lam)*(A2*L2/(lam*D)) + 3*((lam - A1)/lam)*((lam - A2)/lam) - ((lam - A1)/lam)*((lam - A3)/lam)^2*(A2*L2/(lam*D)) - 2*((lam - A1)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) + ((lam - A1)/lam)*((lam - A3)/lam)*(A2*L2/(lam*D)) + ((lam - A1)/lam)*((lam - A3)/lam) + 3*((lam - A1)/lam)*(A1*L1/(lam*D)) - 2*((lam - A1)/lam) - ((lam - A2)/lam)^2*(A1*L1/(lam*D)) + ((lam - A2)/lam)^2 + ((lam - A2)/lam)*(A1*L1/(lam*D)) - ((lam - A2)/lam) - ((lam - A3)/lam)^2*(A1*L1/(lam*D)) + ((lam - A3)/lam)^2 + ((lam - A3)/lam)*(A1*L1/(lam*D)) - ((lam - A3)/lam))
      = (-A1^3*A2*L1 - A1^2*A2^2*L1 - A1^2*A2^2*L2 - A1^2*A2*A3*L1 + A1^2*A2*A3*L2 + 2*A1^2*A2*D*lam + 2*A1^2*A2*L1*lam - A1^2*A3*L1*lam - A1*A2^3*L2 + 2*A1*A2^2*D*lam + 3*A1*A2^2*L2*lam + A1*A2*A3^2*L2 + A1*A2*A3*L1*lam - 3*A1*A2*A3*L2*lam - 5*A1*A2*D*lam^2 - A1*A3^2*L1*lam + A1*A3*D*lam^2 + 2*A1*A3*L1*lam^2 + A2^3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - A2*A3^2*L2*lam + 2*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + A3^2*D*lam^2 - 2*A3*D*lam^3) := by
    field_simp [ne_of_gt hlam0, ne_of_gt hD]
    ring
  have hQneg : lam^4 * D * (((lam - A1)/lam)^2*((lam - A2)/lam)*(A1*L1/(lam*D)) + ((lam - A1)/lam)^2*((lam - A2)/lam)*(A2*L2/(lam*D)) - 2*((lam - A1)/lam)^2*((lam - A2)/lam) - ((lam - A1)/lam)^2*((lam - A3)/lam)*(A2*L2/(lam*D)) - ((lam - A1)/lam)^2*(A1*L1/(lam*D)) + 2*((lam - A1)/lam)^2 + ((lam - A1)/lam)*((lam - A2)/lam)^2*(A1*L1/(lam*D)) + ((lam - A1)/lam)*((lam - A2)/lam)^2*(A2*L2/(lam*D)) - 2*((lam - A1)/lam)*((lam - A2)/lam)^2 + ((lam - A1)/lam)*((lam - A2)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) - 3*((lam - A1)/lam)*((lam - A2)/lam)*(A1*L1/(lam*D)) - ((lam - A1)/lam)*((lam - A2)/lam)*(A2*L2/(lam*D)) + 3*((lam - A1)/lam)*((lam - A2)/lam) - ((lam - A1)/lam)*((lam - A3)/lam)^2*(A2*L2/(lam*D)) - 2*((lam - A1)/lam)*((lam - A3)/lam)*(A1*L1/(lam*D)) + ((lam - A1)/lam)*((lam - A3)/lam)*(A2*L2/(lam*D)) + ((lam - A1)/lam)*((lam - A3)/lam) + 3*((lam - A1)/lam)*(A1*L1/(lam*D)) - 2*((lam - A1)/lam) - ((lam - A2)/lam)^2*(A1*L1/(lam*D)) + ((lam - A2)/lam)^2 + ((lam - A2)/lam)*(A1*L1/(lam*D)) - ((lam - A2)/lam) - ((lam - A3)/lam)^2*(A1*L1/(lam*D)) + ((lam - A3)/lam)^2 + ((lam - A3)/lam)*(A1*L1/(lam*D)) - ((lam - A3)/lam))
      < 0 := by
    have hqq := mul_pos (mul_pos (pow_pos hlam0 4) hD) (neg_pos.2 hpoly)
    nlinarith [hqq]
  have hPtneg : (-A1^3*A2*L1 - A1^2*A2^2*L1 - A1^2*A2^2*L2 - A1^2*A2*A3*L1 + A1^2*A2*A3*L2 + 2*A1^2*A2*D*lam + 2*A1^2*A2*L1*lam - A1^2*A3*L1*lam - A1*A2^3*L2 + 2*A1*A2^2*D*lam + 3*A1*A2^2*L2*lam + A1*A2*A3^2*L2 + A1*A2*A3*L1*lam - 3*A1*A2*A3*L2*lam - 5*A1*A2*D*lam^2 - A1*A3^2*L1*lam + A1*A3*D*lam^2 + 2*A1*A3*L1*lam^2 + A2^3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - A2*A3^2*L2*lam + 2*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + A3^2*D*lam^2 - 2*A3*D*lam^3) < 0 := by linarith [hscale, hQneg]
  have hsum : 0 ≤ 1 * D * (-A1^3*A2*L1 - A1^2*A2^2*L1 - A1^2*A2^2*L2 - A1^2*A2*A3*L1 + A1^2*A2*A3*L2 + 2*A1^2*A2*D*lam + 2*A1^2*A2*L1*lam - A1^2*A3*L1*lam - A1*A2^3*L2 + 2*A1*A2^2*D*lam + 3*A1*A2^2*L2*lam + A1*A2*A3^2*L2 + A1*A2*A3*L1*lam - 3*A1*A2*A3*L2*lam - 5*A1*A2*D*lam^2 - A1*A3^2*L1*lam + A1*A3*D*lam^2 + 2*A1*A3*L1*lam^2 + A2^3*L2*lam - A2^2*D*lam^2 - 2*A2^2*L2*lam^2 - A2*A3^2*L2*lam + 2*A2*A3*L2*lam^2 + 2*A2*D*lam^3 + A3^2*D*lam^2 - 2*A3*D*lam^3) := by
    linarith [hbridge, hstar1]
  nlinarith [hPtneg, hsum, mul_pos hD (neg_pos.2 hPtneg)]




/-! ## 4. The scalar dispatch -/

/-- **The scalar endgame dispatch.**  Fourteen scalars carry the whole
planar corner: the scaled weights `T`, the outside gap determinant `DD`,
the turned self-readings `LL`, the conjugated off-readings `P`, and the
outside norms `l`.  Given the determinant ledger, the conjugated isotropy
(`hEL`), the Gram quadrances (`hQ`), and the per-pair dichotomy — thin
(`DD ≤ LL`) or the fat pigeonhole — every sign pattern is contradictory. -/
theorem planar_scalar_dispatch {lam T1 T2 T3 DD LL1 LL2 LL3 P21 P31 P32
    l1 l2 l3 : ℝ}
    (hlam2 : 2 < lam)
    (hT1 : 0 < T1) (hT2 : 0 < T2) (hT3 : 0 < T3)
    (hTtot : T1 + T2 + T3 = lam - 2)
    (hDD : 0 < DD)
    (hL1 : 0 < LL1) (hL2 : 0 < LL2) (hL3 : 0 < LL3)
    (hledger : (lam - T1)*LL1 + (lam - T2)*LL2 + (lam - T3)*LL3
      = 2*lam*DD)
    (hTrEq : LL1 + LL2 + LL3 = 2*DD + (l1 + l2 + l3) - 2)
    (hEL1 : (lam - T1)*LL1^2 + (lam - T2)*P21^2 + (lam - T3)*P31^2
      = lam*DD*LL1)
    (hEL2 : (lam - T1)*P21^2 + (lam - T2)*LL2^2 + (lam - T3)*P32^2
      = lam*DD*LL2)
    (hEL3 : (lam - T1)*P31^2 + (lam - T2)*P32^2 + (lam - T3)*LL3^2
      = lam*DD*LL3)
    (hQ1 : LL1^2 + P21^2 + P31^2
      = DD*LL1 + (l1 + l2 + l3 - 2)*LL1 - DD*l1)
    (hQ2 : P21^2 + LL2^2 + P32^2
      = DD*LL2 + (l1 + l2 + l3 - 2)*LL2 - DD*l2)
    (hQ3 : P31^2 + P32^2 + LL3^2
      = DD*LL3 + (l1 + l2 + l3 - 2)*LL3 - DD*l3)
    (hdich1 : DD ≤ LL1 ∨ (lam - 2)*(DD - LL1) ≤ l2 + l3 - 2)
    (hdich2 : DD ≤ LL2 ∨ (lam - 2)*(DD - LL2) ≤ l1 + l3 - 2)
    (hdich3 : DD ≤ LL3 ∨ (lam - 2)*(DD - LL3) ≤ l1 + l2 - 2) : False := by
  have hB1 : 2 < lam - T1 := by linarith
  have hB2 : 2 < lam - T2 := by linarith
  have hB3 : 2 < lam - T3 := by linarith
  have hB1l : lam - T1 < lam := by linarith
  have hB2l : lam - T2 < lam := by linarith
  have hB3l : lam - T3 < lam := by linarith
  have hBsum : (lam - T1) + (lam - T2) + (lam - T3) = 2*lam + 2 := by
    linarith
  have hE21 : 2*(lam - T1)*(lam - T2)*P21^2
      = (lam - T1)*LL1*(lam*DD - (lam - T1)*LL1)
        + (lam - T2)*LL2*(lam*DD - (lam - T2)*LL2)
        - (lam - T3)*LL3*(lam*DD - (lam - T3)*LL3) := by
    linear_combination (lam - T1) * hEL1 + (lam - T2) * hEL2
      - (lam - T3) * hEL3
  have hE31 : 2*(lam - T1)*(lam - T3)*P31^2
      = (lam - T1)*LL1*(lam*DD - (lam - T1)*LL1)
        + (lam - T3)*LL3*(lam*DD - (lam - T3)*LL3)
        - (lam - T2)*LL2*(lam*DD - (lam - T2)*LL2) := by
    linear_combination (lam - T1) * hEL1 + (lam - T3) * hEL3
      - (lam - T2) * hEL2
  have hE32 : 2*(lam - T2)*(lam - T3)*P32^2
      = (lam - T2)*LL2*(lam*DD - (lam - T2)*LL2)
        + (lam - T3)*LL3*(lam*DD - (lam - T3)*LL3)
        - (lam - T1)*LL1*(lam*DD - (lam - T1)*LL1) := by
    linear_combination (lam - T2) * hEL2 + (lam - T3) * hEL3
      - (lam - T1) * hEL1
  have hstar1c : (lam - 2)*(DD - LL1) ≤ l2 + l3 - 2 →
      (-(lam - T1)^2*(lam - T2)*LL1^2 - (lam - T1)^2*(lam - T3)*LL1^2 + (lam - T1)*(lam - T2)*DD*LL1*lam + (lam - T1)*(lam - T3)*DD*LL1*lam + (lam - T2)^3*LL2^2 - (lam - T2)^2*(lam - T3)*LL2^2 - (lam - T2)^2*DD*LL2*lam - (lam - T2)*(lam - T3)^2*LL3^2 + (lam - T2)*(lam - T3)*DD*LL2*lam + (lam - T2)*(lam - T3)*DD*LL3*lam + (lam - T3)^3*LL3^2 - (lam - T3)^2*DD*LL3*lam)
      ≥ (2*(lam - T1)*(lam - T2)*(lam - T3)*DD^2*lam - 2*(lam - T1)*(lam - T2)*(lam - T3)*DD*LL1*lam - 2*(lam - T1)*(lam - T2)*(lam - T3)*DD*LL2 - 2*(lam - T1)*(lam - T2)*(lam - T3)*DD*LL3 + 2*(lam - T1)*(lam - T2)*(lam - T3)*LL1*LL2 + 2*(lam - T1)*(lam - T2)*(lam - T3)*LL1*LL3) := by
    intro hpig
    have hHYP : P21^2 + P31^2
        ≥ (DD - LL1)*((lam - 2)*DD - (LL1 + LL2 + LL3 - 2*DD) + LL1) := by
      have hkey : (P21^2 + P31^2)
          - (DD - LL1)*((lam - 2)*DD - (LL1 + LL2 + LL3 - 2*DD) + LL1)
          = DD*((l2 + l3 - 2) - (lam - 2)*(DD - LL1)) := by
        linear_combination hQ1 + (DD - LL1) * hTrEq
      nlinarith [hkey, mul_nonneg hDD.le (sub_nonneg.2 hpig)]
    nlinarith [hE21, hE31,
      mul_le_mul_of_nonneg_left hHYP
        (by positivity : (0:ℝ) ≤ 2*(lam - T1)*(lam - T2)*(lam - T3))]
  have hstar2c : (lam - 2)*(DD - LL2) ≤ l1 + l3 - 2 →
      ((lam - T1)^3*LL1^2 - (lam - T1)^2*(lam - T3)*LL1^2 - (lam - T1)^2*DD*LL1*lam - (lam - T1)*(lam - T2)^2*LL2^2 + (lam - T1)*(lam - T2)*DD*LL2*lam - (lam - T1)*(lam - T3)^2*LL3^2 + (lam - T1)*(lam - T3)*DD*LL1*lam + (lam - T1)*(lam - T3)*DD*LL3*lam - (lam - T2)^2*(lam - T3)*LL2^2 + (lam - T2)*(lam - T3)*DD*LL2*lam + (lam - T3)^3*LL3^2 - (lam - T3)^2*DD*LL3*lam)
      ≥ (2*(lam - T1)*(lam - T2)*(lam - T3)*DD^2*lam - 2*(lam - T1)*(lam - T2)*(lam - T3)*DD*LL1 - 2*(lam - T1)*(lam - T2)*(lam - T3)*DD*LL2*lam - 2*(lam - T1)*(lam - T2)*(lam - T3)*DD*LL3 + 2*(lam - T1)*(lam - T2)*(lam - T3)*LL1*LL2 + 2*(lam - T1)*(lam - T2)*(lam - T3)*LL2*LL3) := by
    intro hpig
    have hHYP : P21^2 + P32^2
        ≥ (DD - LL2)*((lam - 2)*DD - (LL1 + LL2 + LL3 - 2*DD) + LL2) := by
      have hkey : (P21^2 + P32^2)
          - (DD - LL2)*((lam - 2)*DD - (LL1 + LL2 + LL3 - 2*DD) + LL2)
          = DD*((l1 + l3 - 2) - (lam - 2)*(DD - LL2)) := by
        linear_combination hQ2 + (DD - LL2) * hTrEq
      nlinarith [hkey, mul_nonneg hDD.le (sub_nonneg.2 hpig)]
    nlinarith [hE21, hE32,
      mul_le_mul_of_nonneg_left hHYP
        (by positivity : (0:ℝ) ≤ 2*(lam - T1)*(lam - T2)*(lam - T3))]
  have hstar3c : (lam - 2)*(DD - LL3) ≤ l1 + l2 - 2 →
      ((lam - T1)^3*LL1^2 - (lam - T1)^2*(lam - T2)*LL1^2 - (lam - T1)^2*DD*LL1*lam - (lam - T1)*(lam - T2)^2*LL2^2 + (lam - T1)*(lam - T2)*DD*LL1*lam + (lam - T1)*(lam - T2)*DD*LL2*lam - (lam - T1)*(lam - T3)^2*LL3^2 + (lam - T1)*(lam - T3)*DD*LL3*lam + (lam - T2)^3*LL2^2 - (lam - T2)^2*DD*LL2*lam - (lam - T2)*(lam - T3)^2*LL3^2 + (lam - T2)*(lam - T3)*DD*LL3*lam)
      ≥ (2*(lam - T1)*(lam - T2)*(lam - T3)*DD^2*lam - 2*(lam - T1)*(lam - T2)*(lam - T3)*DD*LL1 - 2*(lam - T1)*(lam - T2)*(lam - T3)*DD*LL2 - 2*(lam - T1)*(lam - T2)*(lam - T3)*DD*LL3*lam + 2*(lam - T1)*(lam - T2)*(lam - T3)*LL1*LL3 + 2*(lam - T1)*(lam - T2)*(lam - T3)*LL2*LL3) := by
    intro hpig
    have hHYP : P31^2 + P32^2
        ≥ (DD - LL3)*((lam - 2)*DD - (LL1 + LL2 + LL3 - 2*DD) + LL3) := by
      have hkey : (P31^2 + P32^2)
          - (DD - LL3)*((lam - 2)*DD - (LL1 + LL2 + LL3 - 2*DD) + LL3)
          = DD*((l1 + l2 - 2) - (lam - 2)*(DD - LL3)) := by
        linear_combination hQ3 + (DD - LL3) * hTrEq
      nlinarith [hkey, mul_nonneg hDD.le (sub_nonneg.2 hpig)]
    nlinarith [hE31, hE32,
      mul_le_mul_of_nonneg_left hHYP
        (by positivity : (0:ℝ) ≤ 2*(lam - T1)*(lam - T2)*(lam - T3))]

  rcases lt_or_ge LL1 DD with hf1 | ht1
  · rcases lt_or_ge LL2 DD with hf2 | ht2
    · rcases lt_or_ge LL3 DD with hf3 | ht3
      · -- all three pairs fat
        exact planarCase_allFat hlam2 hDD hB1 hB2 hB3 hB1l hB2l hB3l hBsum
          hL1 hL2 hL3 hledger hf1 hf2 hf3
          (hstar1c (hdich1.resolve_left (not_le.2 hf1)))
          (hstar2c (hdich2.resolve_left (not_le.2 hf2)))
          (hstar3c (hdich3.resolve_left (not_le.2 hf3)))
      · -- pairs one, two fat; pair three thin
        exact planarCase_twoFat hlam2 hDD hB1 hB2 hB3 hB1l hB2l hB3l hBsum
          hL1 hL2 hL3 hledger hf1 hf2 ht3
          (hstar1c (hdich1.resolve_left (not_le.2 hf1)))
          (hstar2c (hdich2.resolve_left (not_le.2 hf2)))
    · rcases lt_or_ge LL3 DD with hf3 | ht3
      · -- pairs one, three fat; pair two thin
        exact planarCase_twoFat hlam2 hDD hB1 hB3 hB2 hB1l hB3l hB2l
          (by linarith) hL1 hL3 hL2 (by linarith) hf1 hf3 ht2
          (by linarith [hstar1c (hdich1.resolve_left (not_le.2 hf1))])
          (by linarith [hstar3c (hdich3.resolve_left (not_le.2 hf3))])
      · -- pair one fat; pairs two, three thin
        exact planarCase_oneFat hlam2 hDD hB1 hB2 hB3 hB1l hB2l hB3l hBsum
          hL1 hL2 hL3 hledger hf1 ht2 ht3
          (hstar1c (hdich1.resolve_left (not_le.2 hf1)))
  · rcases lt_or_ge LL2 DD with hf2 | ht2
    · rcases lt_or_ge LL3 DD with hf3 | ht3
      · -- pairs two, three fat; pair one thin
        exact planarCase_twoFat hlam2 hDD hB2 hB3 hB1 hB2l hB3l hB1l
          (by linarith) hL2 hL3 hL1 (by linarith) hf2 hf3 ht1
          (by linarith [hstar2c (hdich2.resolve_left (not_le.2 hf2))])
          (by linarith [hstar3c (hdich3.resolve_left (not_le.2 hf3))])
      · -- pair two fat; pairs one, three thin
        exact planarCase_oneFat hlam2 hDD hB2 hB1 hB3 hB2l hB1l hB3l
          (by linarith) hL2 hL1 hL3 (by linarith) hf2 ht1 ht3
          (by linarith [hstar2c (hdich2.resolve_left (not_le.2 hf2))])
    · rcases lt_or_ge LL3 DD with hf3 | ht3
      · -- pair three fat; pairs one, two thin
        exact planarCase_oneFat hlam2 hDD hB3 hB1 hB2 hB3l hB1l hB2l
          (by linarith) hL3 hL1 hL2 (by linarith) hf3 ht1 ht2
          (by linarith [hstar3c (hdich3.resolve_left (not_le.2 hf3))])
      · -- all three pairs thin: the determinant ledger overflows
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ lam - T1)
            (sub_nonneg.2 ht1),
          mul_nonneg (by linarith : (0:ℝ) ≤ lam - T2) (sub_nonneg.2 ht2),
          mul_nonneg (by linarith : (0:ℝ) ≤ lam - T3) (sub_nonneg.2 ht3),
          hledger, hDD]

end Gtz

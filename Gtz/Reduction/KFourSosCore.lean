import Gtz.Reduction.KFourTreeAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-
# The det-trace law's three steps at M(K4): SOS core (gamma), argmax
# bound (beta), leverage identity (alpha) -- and the law itself

Mechanization of the matroid lane's rung-8 theorem
(the M(K4) matroid-lane ledger, det-trace proof): at any spanning
tree maximising the conductance product `prod_T y`, the determinant
dominates the trace, `e1(T*) < e3(T*)`, so at most one generalized
eigenvalue of `B^{-1} S_{T*}` can fail to exceed one (laws L1 and L2).

The three steps, each in constraint-light form:
* **gamma** -- for every one of the sixteen trees, the homogeneous SOS
  identity `Q(T) + Sq(x) + (1/2) sum (z_i - z_j)^2 + CROSS(T) = (sum w)^2`
  holds as a polynomial identity (`ring`); on the open simplex every SOS
  summand is nonnegative and `Sq(x)` is positive, so `Q(T) < 1` STRICTLY.
  The ledger's `1 - Q(T') = SOS` form is recovered at the two orbit
  representatives.
* **beta** -- the term-by-term argmax bound, per edge:
  `y_c F_c(m) <= bound * F_c(w)` whenever every tree conductance product
  is at most `bound`; summed over a tree,
  `e1(T) det B = sum_{c in T} y_c F_c(m) <= bound * Q(T)`.
* **alpha** -- the matrix-tree leverage identity: the adjugate pairing of
  each edge covector equals that edge's companion sum,
  `v_c^T adj(B) v_c = F_c(m)`, hence
  `m_c nu_c det B = sum_{T through c} prod_T m`.

Chained: `e1(T) det B <= (prod_{T*} y) Q(T) < prod_{T*} y = e3(T*) det B`
for EVERY tree `T` -- the rung-8 bonus -- and at `T = T*` this is the
det-trace law.
-/

namespace Gtz

open Matrix

/-! ## Step gamma: the sixteen homogeneous SOS identities -/

/-- Step gamma, homogeneous SOS at tree `(0, 1, 2)` (star orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_starZero (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (0, 1, 2)
      + (weight 0 ^ 2 + weight 1 ^ 2 + weight 2 ^ 2
        + (weight 0 * weight 1 + weight 0 * weight 2 + weight 1 * weight 2)
        + ((weight 3 - weight 4) ^ 2 + (weight 3 - weight 5) ^ 2 + (weight 4 - weight 5) ^ 2) / 2
        + (weight 3 * (weight 0 + weight 1) + weight 4 * (weight 0 + weight 2) + weight 5 * (weight 1 + weight 2)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(0, 1, 4)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path014 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (0, 1, 4)
      + (weight 0 ^ 2 + weight 1 ^ 2 + weight 4 ^ 2
        + (weight 0 * weight 1 + weight 0 * weight 4 + weight 1 * weight 4)
        + ((weight 2 - weight 3) ^ 2 + (weight 2 - weight 5) ^ 2 + (weight 3 - weight 5) ^ 2) / 2
        + (weight 3 * (weight 1 + weight 5 + weight 0) + weight 2 * (weight 5 + weight 0 + weight 4)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(0, 1, 5)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path015 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (0, 1, 5)
      + (weight 0 ^ 2 + weight 1 ^ 2 + weight 5 ^ 2
        + (weight 0 * weight 1 + weight 0 * weight 5 + weight 1 * weight 5)
        + ((weight 2 - weight 3) ^ 2 + (weight 2 - weight 4) ^ 2 + (weight 3 - weight 4) ^ 2) / 2
        + (weight 3 * (weight 0 + weight 4 + weight 1) + weight 2 * (weight 4 + weight 1 + weight 5)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(0, 2, 3)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path023 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (0, 2, 3)
      + (weight 0 ^ 2 + weight 2 ^ 2 + weight 3 ^ 2
        + (weight 0 * weight 2 + weight 0 * weight 3 + weight 2 * weight 3)
        + ((weight 1 - weight 4) ^ 2 + (weight 1 - weight 5) ^ 2 + (weight 4 - weight 5) ^ 2) / 2
        + (weight 1 * (weight 3 + weight 5 + weight 0) + weight 4 * (weight 5 + weight 0 + weight 2)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(0, 2, 5)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path025 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (0, 2, 5)
      + (weight 0 ^ 2 + weight 2 ^ 2 + weight 5 ^ 2
        + (weight 0 * weight 2 + weight 0 * weight 5 + weight 2 * weight 5)
        + ((weight 1 - weight 3) ^ 2 + (weight 1 - weight 4) ^ 2 + (weight 3 - weight 4) ^ 2) / 2
        + (weight 4 * (weight 0 + weight 3 + weight 2) + weight 1 * (weight 3 + weight 2 + weight 5)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(0, 3, 4)` (star orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_starOne (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (0, 3, 4)
      + (weight 0 ^ 2 + weight 3 ^ 2 + weight 4 ^ 2
        + (weight 0 * weight 3 + weight 0 * weight 4 + weight 3 * weight 4)
        + ((weight 1 - weight 2) ^ 2 + (weight 1 - weight 5) ^ 2 + (weight 2 - weight 5) ^ 2) / 2
        + (weight 1 * (weight 0 + weight 3) + weight 2 * (weight 0 + weight 4) + weight 5 * (weight 3 + weight 4)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(0, 3, 5)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path035 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (0, 3, 5)
      + (weight 0 ^ 2 + weight 3 ^ 2 + weight 5 ^ 2
        + (weight 0 * weight 3 + weight 0 * weight 5 + weight 3 * weight 5)
        + ((weight 1 - weight 2) ^ 2 + (weight 1 - weight 4) ^ 2 + (weight 2 - weight 4) ^ 2) / 2
        + (weight 1 * (weight 0 + weight 2 + weight 3) + weight 4 * (weight 2 + weight 3 + weight 5)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(0, 4, 5)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path045 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (0, 4, 5)
      + (weight 0 ^ 2 + weight 4 ^ 2 + weight 5 ^ 2
        + (weight 0 * weight 4 + weight 0 * weight 5 + weight 4 * weight 5)
        + ((weight 1 - weight 2) ^ 2 + (weight 1 - weight 3) ^ 2 + (weight 2 - weight 3) ^ 2) / 2
        + (weight 2 * (weight 0 + weight 1 + weight 4) + weight 3 * (weight 1 + weight 4 + weight 5)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(1, 2, 3)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path123 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (1, 2, 3)
      + (weight 1 ^ 2 + weight 2 ^ 2 + weight 3 ^ 2
        + (weight 1 * weight 2 + weight 1 * weight 3 + weight 2 * weight 3)
        + ((weight 0 - weight 4) ^ 2 + (weight 0 - weight 5) ^ 2 + (weight 4 - weight 5) ^ 2) / 2
        + (weight 0 * (weight 3 + weight 4 + weight 1) + weight 5 * (weight 4 + weight 1 + weight 2)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(1, 2, 4)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path124 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (1, 2, 4)
      + (weight 1 ^ 2 + weight 2 ^ 2 + weight 4 ^ 2
        + (weight 1 * weight 2 + weight 1 * weight 4 + weight 2 * weight 4)
        + ((weight 0 - weight 3) ^ 2 + (weight 0 - weight 5) ^ 2 + (weight 3 - weight 5) ^ 2) / 2
        + (weight 0 * (weight 4 + weight 3 + weight 2) + weight 5 * (weight 3 + weight 2 + weight 1)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(1, 3, 4)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path134 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (1, 3, 4)
      + (weight 1 ^ 2 + weight 3 ^ 2 + weight 4 ^ 2
        + (weight 1 * weight 3 + weight 1 * weight 4 + weight 3 * weight 4)
        + ((weight 0 - weight 2) ^ 2 + (weight 0 - weight 5) ^ 2 + (weight 2 - weight 5) ^ 2) / 2
        + (weight 0 * (weight 1 + weight 2 + weight 3) + weight 5 * (weight 2 + weight 3 + weight 4)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(1, 3, 5)` (star orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_starTwo (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (1, 3, 5)
      + (weight 1 ^ 2 + weight 3 ^ 2 + weight 5 ^ 2
        + (weight 1 * weight 3 + weight 1 * weight 5 + weight 3 * weight 5)
        + ((weight 0 - weight 2) ^ 2 + (weight 0 - weight 4) ^ 2 + (weight 2 - weight 4) ^ 2) / 2
        + (weight 0 * (weight 1 + weight 3) + weight 2 * (weight 1 + weight 5) + weight 4 * (weight 3 + weight 5)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(1, 4, 5)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path145 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (1, 4, 5)
      + (weight 1 ^ 2 + weight 4 ^ 2 + weight 5 ^ 2
        + (weight 1 * weight 4 + weight 1 * weight 5 + weight 4 * weight 5)
        + ((weight 0 - weight 2) ^ 2 + (weight 0 - weight 3) ^ 2 + (weight 2 - weight 3) ^ 2) / 2
        + (weight 2 * (weight 1 + weight 0 + weight 5) + weight 3 * (weight 0 + weight 5 + weight 4)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(2, 3, 4)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path234 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (2, 3, 4)
      + (weight 2 ^ 2 + weight 3 ^ 2 + weight 4 ^ 2
        + (weight 2 * weight 3 + weight 2 * weight 4 + weight 3 * weight 4)
        + ((weight 0 - weight 1) ^ 2 + (weight 0 - weight 5) ^ 2 + (weight 1 - weight 5) ^ 2) / 2
        + (weight 0 * (weight 2 + weight 1 + weight 4) + weight 5 * (weight 1 + weight 4 + weight 3)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(2, 3, 5)` (path orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_path235 (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (2, 3, 5)
      + (weight 2 ^ 2 + weight 3 ^ 2 + weight 5 ^ 2
        + (weight 2 * weight 3 + weight 2 * weight 5 + weight 3 * weight 5)
        + ((weight 0 - weight 1) ^ 2 + (weight 0 - weight 4) ^ 2 + (weight 1 - weight 4) ^ 2) / 2
        + (weight 1 * (weight 2 + weight 0 + weight 5) + weight 4 * (weight 0 + weight 5 + weight 3)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring

/-- Step gamma, homogeneous SOS at tree `(2, 4, 5)` (star orbit):
`Q(T) + SOS_T = (total weight)^2` with every SOS summand nonnegative on
the nonnegative orthant. -/
theorem kFourTreeQuadratic_sos_starThree (weight : Fin 6 → ℝ) :
    kFourTreeQuadratic weight (2, 4, 5)
      + (weight 2 ^ 2 + weight 4 ^ 2 + weight 5 ^ 2
        + (weight 2 * weight 4 + weight 2 * weight 5 + weight 4 * weight 5)
        + ((weight 0 - weight 1) ^ 2 + (weight 0 - weight 3) ^ 2 + (weight 1 - weight 3) ^ 2) / 2
        + (weight 0 * (weight 2 + weight 4) + weight 1 * (weight 2 + weight 5) + weight 3 * (weight 4 + weight 5)))
      = (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5) ^ 2 := by
  simp only [kFourTreeQuadratic, kFourEdgeCompanionSum]
  ring


/-- **Step gamma, strict form**: on the open weight simplex every one of
the sixteen tree quadratics is strictly below one. -/
theorem kFourTreeQuadratic_lt_one (weight : Fin 6 → ℝ)
    (hw : ∀ edge, 0 < weight edge) (hsum : ∑ edge, weight edge = 1) :
    ∀ tree ∈ k4TreeTriples, kFourTreeQuadratic weight tree < 1 := by
  have hsix : weight 0 + weight 1 + weight 2 + weight 3 + weight 4
      + weight 5 = 1 := by
    simpa [Fin.sum_univ_six] using hsum
  have hone : (weight 0 + weight 1 + weight 2 + weight 3 + weight 4
      + weight 5) ^ 2 = 1 := by
    rw [hsix]; norm_num
  have hsos_starZero := kFourTreeQuadratic_sos_starZero weight
  have hsos_path014 := kFourTreeQuadratic_sos_path014 weight
  have hsos_path015 := kFourTreeQuadratic_sos_path015 weight
  have hsos_path023 := kFourTreeQuadratic_sos_path023 weight
  have hsos_path025 := kFourTreeQuadratic_sos_path025 weight
  have hsos_starOne := kFourTreeQuadratic_sos_starOne weight
  have hsos_path035 := kFourTreeQuadratic_sos_path035 weight
  have hsos_path045 := kFourTreeQuadratic_sos_path045 weight
  have hsos_path123 := kFourTreeQuadratic_sos_path123 weight
  have hsos_path124 := kFourTreeQuadratic_sos_path124 weight
  have hsos_path134 := kFourTreeQuadratic_sos_path134 weight
  have hsos_starTwo := kFourTreeQuadratic_sos_starTwo weight
  have hsos_path145 := kFourTreeQuadratic_sos_path145 weight
  have hsos_path234 := kFourTreeQuadratic_sos_path234 weight
  have hsos_path235 := kFourTreeQuadratic_sos_path235 weight
  have hsos_starThree := kFourTreeQuadratic_sos_starThree weight
  have hsq01 : (0 : ℝ) ≤ (weight 0 - weight 1) ^ 2 := sq_nonneg _
  have hsq02 : (0 : ℝ) ≤ (weight 0 - weight 2) ^ 2 := sq_nonneg _
  have hsq03 : (0 : ℝ) ≤ (weight 0 - weight 3) ^ 2 := sq_nonneg _
  have hsq04 : (0 : ℝ) ≤ (weight 0 - weight 4) ^ 2 := sq_nonneg _
  have hsq05 : (0 : ℝ) ≤ (weight 0 - weight 5) ^ 2 := sq_nonneg _
  have hsq12 : (0 : ℝ) ≤ (weight 1 - weight 2) ^ 2 := sq_nonneg _
  have hsq13 : (0 : ℝ) ≤ (weight 1 - weight 3) ^ 2 := sq_nonneg _
  have hsq14 : (0 : ℝ) ≤ (weight 1 - weight 4) ^ 2 := sq_nonneg _
  have hsq15 : (0 : ℝ) ≤ (weight 1 - weight 5) ^ 2 := sq_nonneg _
  have hsq23 : (0 : ℝ) ≤ (weight 2 - weight 3) ^ 2 := sq_nonneg _
  have hsq24 : (0 : ℝ) ≤ (weight 2 - weight 4) ^ 2 := sq_nonneg _
  have hsq25 : (0 : ℝ) ≤ (weight 2 - weight 5) ^ 2 := sq_nonneg _
  have hsq34 : (0 : ℝ) ≤ (weight 3 - weight 4) ^ 2 := sq_nonneg _
  have hsq35 : (0 : ℝ) ≤ (weight 3 - weight 5) ^ 2 := sq_nonneg _
  have hsq45 : (0 : ℝ) ≤ (weight 4 - weight 5) ^ 2 := sq_nonneg _
  have hpr01 : (0 : ℝ) ≤ weight 0 * weight 1 := mul_nonneg (hw 0).le (hw 1).le
  have hpr02 : (0 : ℝ) ≤ weight 0 * weight 2 := mul_nonneg (hw 0).le (hw 2).le
  have hpr03 : (0 : ℝ) ≤ weight 0 * weight 3 := mul_nonneg (hw 0).le (hw 3).le
  have hpr04 : (0 : ℝ) ≤ weight 0 * weight 4 := mul_nonneg (hw 0).le (hw 4).le
  have hpr05 : (0 : ℝ) ≤ weight 0 * weight 5 := mul_nonneg (hw 0).le (hw 5).le
  have hpr12 : (0 : ℝ) ≤ weight 1 * weight 2 := mul_nonneg (hw 1).le (hw 2).le
  have hpr13 : (0 : ℝ) ≤ weight 1 * weight 3 := mul_nonneg (hw 1).le (hw 3).le
  have hpr14 : (0 : ℝ) ≤ weight 1 * weight 4 := mul_nonneg (hw 1).le (hw 4).le
  have hpr15 : (0 : ℝ) ≤ weight 1 * weight 5 := mul_nonneg (hw 1).le (hw 5).le
  have hpr23 : (0 : ℝ) ≤ weight 2 * weight 3 := mul_nonneg (hw 2).le (hw 3).le
  have hpr24 : (0 : ℝ) ≤ weight 2 * weight 4 := mul_nonneg (hw 2).le (hw 4).le
  have hpr25 : (0 : ℝ) ≤ weight 2 * weight 5 := mul_nonneg (hw 2).le (hw 5).le
  have hpr34 : (0 : ℝ) ≤ weight 3 * weight 4 := mul_nonneg (hw 3).le (hw 4).le
  have hpr35 : (0 : ℝ) ≤ weight 3 * weight 5 := mul_nonneg (hw 3).le (hw 5).le
  have hpr45 : (0 : ℝ) ≤ weight 4 * weight 5 := mul_nonneg (hw 4).le (hw 5).le
  have hpw0 : (0 : ℝ) < weight 0 ^ 2 := pow_pos (hw 0) 2
  have hpw1 : (0 : ℝ) < weight 1 ^ 2 := pow_pos (hw 1) 2
  have hpw2 : (0 : ℝ) < weight 2 ^ 2 := pow_pos (hw 2) 2
  have hpw3 : (0 : ℝ) < weight 3 ^ 2 := pow_pos (hw 3) 2
  have hpw4 : (0 : ℝ) < weight 4 ^ 2 := pow_pos (hw 4) 2
  have hpw5 : (0 : ℝ) < weight 5 ^ 2 := pow_pos (hw 5) 2
  intro tree htree
  fin_cases htree <;> linarith

/-- Step gamma in the ledger's form at the star representative:
`1 - Q(star at apex 0) = Sq(x) + (1/2) sum (z_i - z_j)^2 + CROSS` on the
weight simplex. -/
theorem one_sub_kFourTreeQuadratic_starZero (weight : Fin 6 → ℝ)
    (hsum : ∑ edge, weight edge = 1) :
    1 - kFourTreeQuadratic weight (0, 1, 2)
      = weight 0 ^ 2 + weight 1 ^ 2 + weight 2 ^ 2
        + (weight 0 * weight 1 + weight 0 * weight 2 + weight 1 * weight 2)
        + ((weight 3 - weight 4) ^ 2 + (weight 3 - weight 5) ^ 2
            + (weight 4 - weight 5) ^ 2) / 2
        + (weight 3 * (weight 0 + weight 1) + weight 4 * (weight 0 + weight 2)
            + weight 5 * (weight 1 + weight 2)) := by
  have hsix : weight 0 + weight 1 + weight 2 + weight 3 + weight 4
      + weight 5 = 1 := by
    simpa [Fin.sum_univ_six] using hsum
  have hsos := kFourTreeQuadratic_sos_starZero weight
  linear_combination (-1 : ℝ) * hsos
    - (1 + (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5))
      * hsix

/-- Step gamma in the ledger's form at the path representative
`0-1-2-3` (tree edges `{0, 3, 5}`, chords `z = {1, 2, 4}`). -/
theorem one_sub_kFourTreeQuadratic_pathZeroThreeFive (weight : Fin 6 → ℝ)
    (hsum : ∑ edge, weight edge = 1) :
    1 - kFourTreeQuadratic weight (0, 3, 5)
      = weight 0 ^ 2 + weight 3 ^ 2 + weight 5 ^ 2
        + (weight 0 * weight 3 + weight 0 * weight 5 + weight 3 * weight 5)
        + ((weight 1 - weight 2) ^ 2 + (weight 1 - weight 4) ^ 2
            + (weight 2 - weight 4) ^ 2) / 2
        + (weight 1 * (weight 0 + weight 2 + weight 3)
            + weight 4 * (weight 2 + weight 3 + weight 5)) := by
  have hsix : weight 0 + weight 1 + weight 2 + weight 3 + weight 4
      + weight 5 = 1 := by
    simpa [Fin.sum_univ_six] using hsum
  have hsos := kFourTreeQuadratic_sos_path035 weight
  linear_combination (-1 : ℝ) * hsos
    - (1 + (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5))
      * hsix

/-! ## Step beta: the argmax bound -/

/-- **Step beta at one edge**: if every tree conductance product is at
most `bound`, then `y_c * F_c(m) <= bound * F_c(w)` -- each mass companion
term `y_c prod_{T minus c} m` IS `prod_T y * prod_{T minus c} w`, bounded
term by term. -/
theorem conductance_mul_massCompanion_le_bound_mul_weightCompanion
    (conductance weight : Fin 6 → ℝ) (hw : ∀ edge, 0 ≤ weight edge)
    (bound : ℝ)
    (hbound : ∀ tree ∈ k4TreeTriples,
      kFourTreeWeightProduct conductance tree ≤ bound) :
    ∀ edge : Fin 6,
      conductance edge
          * kFourEdgeCompanionSum (fun other => conductance other * weight other)
              edge
        ≤ bound * kFourEdgeCompanionSum weight edge
  | 0 => by
      have scaled12 := mul_le_mul_of_nonneg_right
        (hbound (0, 1, 2) (by decide))
        (mul_nonneg (hw 1) (hw 2))
      have scaled14 := mul_le_mul_of_nonneg_right
        (hbound (0, 1, 4) (by decide))
        (mul_nonneg (hw 1) (hw 4))
      have scaled15 := mul_le_mul_of_nonneg_right
        (hbound (0, 1, 5) (by decide))
        (mul_nonneg (hw 1) (hw 5))
      have scaled23 := mul_le_mul_of_nonneg_right
        (hbound (0, 2, 3) (by decide))
        (mul_nonneg (hw 2) (hw 3))
      have scaled25 := mul_le_mul_of_nonneg_right
        (hbound (0, 2, 5) (by decide))
        (mul_nonneg (hw 2) (hw 5))
      have scaled34 := mul_le_mul_of_nonneg_right
        (hbound (0, 3, 4) (by decide))
        (mul_nonneg (hw 3) (hw 4))
      have scaled35 := mul_le_mul_of_nonneg_right
        (hbound (0, 3, 5) (by decide))
        (mul_nonneg (hw 3) (hw 5))
      have scaled45 := mul_le_mul_of_nonneg_right
        (hbound (0, 4, 5) (by decide))
        (mul_nonneg (hw 4) (hw 5))
      simp only [kFourTreeWeightProduct] at scaled12 scaled14 scaled15 scaled23 scaled25 scaled34 scaled35 scaled45
      simp only [kFourEdgeCompanionSum]
      linarith
  | 1 => by
      have scaled02 := mul_le_mul_of_nonneg_right
        (hbound (0, 1, 2) (by decide))
        (mul_nonneg (hw 0) (hw 2))
      have scaled04 := mul_le_mul_of_nonneg_right
        (hbound (0, 1, 4) (by decide))
        (mul_nonneg (hw 0) (hw 4))
      have scaled05 := mul_le_mul_of_nonneg_right
        (hbound (0, 1, 5) (by decide))
        (mul_nonneg (hw 0) (hw 5))
      have scaled23 := mul_le_mul_of_nonneg_right
        (hbound (1, 2, 3) (by decide))
        (mul_nonneg (hw 2) (hw 3))
      have scaled24 := mul_le_mul_of_nonneg_right
        (hbound (1, 2, 4) (by decide))
        (mul_nonneg (hw 2) (hw 4))
      have scaled34 := mul_le_mul_of_nonneg_right
        (hbound (1, 3, 4) (by decide))
        (mul_nonneg (hw 3) (hw 4))
      have scaled35 := mul_le_mul_of_nonneg_right
        (hbound (1, 3, 5) (by decide))
        (mul_nonneg (hw 3) (hw 5))
      have scaled45 := mul_le_mul_of_nonneg_right
        (hbound (1, 4, 5) (by decide))
        (mul_nonneg (hw 4) (hw 5))
      simp only [kFourTreeWeightProduct] at scaled02 scaled04 scaled05 scaled23 scaled24 scaled34 scaled35 scaled45
      simp only [kFourEdgeCompanionSum]
      linarith
  | 2 => by
      have scaled01 := mul_le_mul_of_nonneg_right
        (hbound (0, 1, 2) (by decide))
        (mul_nonneg (hw 0) (hw 1))
      have scaled03 := mul_le_mul_of_nonneg_right
        (hbound (0, 2, 3) (by decide))
        (mul_nonneg (hw 0) (hw 3))
      have scaled05 := mul_le_mul_of_nonneg_right
        (hbound (0, 2, 5) (by decide))
        (mul_nonneg (hw 0) (hw 5))
      have scaled13 := mul_le_mul_of_nonneg_right
        (hbound (1, 2, 3) (by decide))
        (mul_nonneg (hw 1) (hw 3))
      have scaled14 := mul_le_mul_of_nonneg_right
        (hbound (1, 2, 4) (by decide))
        (mul_nonneg (hw 1) (hw 4))
      have scaled34 := mul_le_mul_of_nonneg_right
        (hbound (2, 3, 4) (by decide))
        (mul_nonneg (hw 3) (hw 4))
      have scaled35 := mul_le_mul_of_nonneg_right
        (hbound (2, 3, 5) (by decide))
        (mul_nonneg (hw 3) (hw 5))
      have scaled45 := mul_le_mul_of_nonneg_right
        (hbound (2, 4, 5) (by decide))
        (mul_nonneg (hw 4) (hw 5))
      simp only [kFourTreeWeightProduct] at scaled01 scaled03 scaled05 scaled13 scaled14 scaled34 scaled35 scaled45
      simp only [kFourEdgeCompanionSum]
      linarith
  | 3 => by
      have scaled02 := mul_le_mul_of_nonneg_right
        (hbound (0, 2, 3) (by decide))
        (mul_nonneg (hw 0) (hw 2))
      have scaled04 := mul_le_mul_of_nonneg_right
        (hbound (0, 3, 4) (by decide))
        (mul_nonneg (hw 0) (hw 4))
      have scaled05 := mul_le_mul_of_nonneg_right
        (hbound (0, 3, 5) (by decide))
        (mul_nonneg (hw 0) (hw 5))
      have scaled12 := mul_le_mul_of_nonneg_right
        (hbound (1, 2, 3) (by decide))
        (mul_nonneg (hw 1) (hw 2))
      have scaled14 := mul_le_mul_of_nonneg_right
        (hbound (1, 3, 4) (by decide))
        (mul_nonneg (hw 1) (hw 4))
      have scaled15 := mul_le_mul_of_nonneg_right
        (hbound (1, 3, 5) (by decide))
        (mul_nonneg (hw 1) (hw 5))
      have scaled24 := mul_le_mul_of_nonneg_right
        (hbound (2, 3, 4) (by decide))
        (mul_nonneg (hw 2) (hw 4))
      have scaled25 := mul_le_mul_of_nonneg_right
        (hbound (2, 3, 5) (by decide))
        (mul_nonneg (hw 2) (hw 5))
      simp only [kFourTreeWeightProduct] at scaled02 scaled04 scaled05 scaled12 scaled14 scaled15 scaled24 scaled25
      simp only [kFourEdgeCompanionSum]
      linarith
  | 4 => by
      have scaled01 := mul_le_mul_of_nonneg_right
        (hbound (0, 1, 4) (by decide))
        (mul_nonneg (hw 0) (hw 1))
      have scaled03 := mul_le_mul_of_nonneg_right
        (hbound (0, 3, 4) (by decide))
        (mul_nonneg (hw 0) (hw 3))
      have scaled05 := mul_le_mul_of_nonneg_right
        (hbound (0, 4, 5) (by decide))
        (mul_nonneg (hw 0) (hw 5))
      have scaled12 := mul_le_mul_of_nonneg_right
        (hbound (1, 2, 4) (by decide))
        (mul_nonneg (hw 1) (hw 2))
      have scaled13 := mul_le_mul_of_nonneg_right
        (hbound (1, 3, 4) (by decide))
        (mul_nonneg (hw 1) (hw 3))
      have scaled15 := mul_le_mul_of_nonneg_right
        (hbound (1, 4, 5) (by decide))
        (mul_nonneg (hw 1) (hw 5))
      have scaled23 := mul_le_mul_of_nonneg_right
        (hbound (2, 3, 4) (by decide))
        (mul_nonneg (hw 2) (hw 3))
      have scaled25 := mul_le_mul_of_nonneg_right
        (hbound (2, 4, 5) (by decide))
        (mul_nonneg (hw 2) (hw 5))
      simp only [kFourTreeWeightProduct] at scaled01 scaled03 scaled05 scaled12 scaled13 scaled15 scaled23 scaled25
      simp only [kFourEdgeCompanionSum]
      linarith
  | 5 => by
      have scaled01 := mul_le_mul_of_nonneg_right
        (hbound (0, 1, 5) (by decide))
        (mul_nonneg (hw 0) (hw 1))
      have scaled02 := mul_le_mul_of_nonneg_right
        (hbound (0, 2, 5) (by decide))
        (mul_nonneg (hw 0) (hw 2))
      have scaled03 := mul_le_mul_of_nonneg_right
        (hbound (0, 3, 5) (by decide))
        (mul_nonneg (hw 0) (hw 3))
      have scaled04 := mul_le_mul_of_nonneg_right
        (hbound (0, 4, 5) (by decide))
        (mul_nonneg (hw 0) (hw 4))
      have scaled13 := mul_le_mul_of_nonneg_right
        (hbound (1, 3, 5) (by decide))
        (mul_nonneg (hw 1) (hw 3))
      have scaled14 := mul_le_mul_of_nonneg_right
        (hbound (1, 4, 5) (by decide))
        (mul_nonneg (hw 1) (hw 4))
      have scaled23 := mul_le_mul_of_nonneg_right
        (hbound (2, 3, 5) (by decide))
        (mul_nonneg (hw 2) (hw 3))
      have scaled24 := mul_le_mul_of_nonneg_right
        (hbound (2, 4, 5) (by decide))
        (mul_nonneg (hw 2) (hw 4))
      simp only [kFourTreeWeightProduct] at scaled01 scaled02 scaled03 scaled04 scaled13 scaled14 scaled23 scaled24
      simp only [kFourEdgeCompanionSum]
      linarith

/-- **Step beta at a tree**: the trace numerator
`e1(T) det B = sum_{c in T} y_c F_c(m)` is at most `bound * Q(T)`. -/
theorem kFourTraceNumerator_le_bound_mul_treeQuadratic
    (conductance weight : Fin 6 → ℝ) (hw : ∀ edge, 0 ≤ weight edge)
    (bound : ℝ)
    (hbound : ∀ tree ∈ k4TreeTriples,
      kFourTreeWeightProduct conductance tree ≤ bound)
    (tree : Fin 6 × Fin 6 × Fin 6) :
    kFourTraceNumerator conductance weight tree
      ≤ bound * kFourTreeQuadratic weight tree := by
  have hfirst := conductance_mul_massCompanion_le_bound_mul_weightCompanion
    conductance weight hw bound hbound tree.1
  have hsecond := conductance_mul_massCompanion_le_bound_mul_weightCompanion
    conductance weight hw bound hbound tree.2.1
  have hthird := conductance_mul_massCompanion_le_bound_mul_weightCompanion
    conductance weight hw bound hbound tree.2.2
  simp only [kFourTraceNumerator, kFourTreeQuadratic]
  linarith

/-! ## Step alpha: the leverage identity -/

/-- The gauge covector of each K4 edge, matching `k4Drop`:
`kFourDropCovector edge ⬝ᵥ probe = k4Drop probe edge`. -/
def kFourDropCovector : Fin 6 → Fin 3 → ℝ
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![0, 0, 1]
  | 3 => ![1, -1, 0]
  | 4 => ![1, 0, -1]
  | 5 => ![0, 1, -1]

theorem kFourDropCovector_dotProduct (probe : Fin 3 → ℝ) :
    ∀ edge : Fin 6, kFourDropCovector edge ⬝ᵥ probe = k4Drop probe edge
  | 0 => by simp [kFourDropCovector, dotProduct, Fin.sum_univ_three, k4Drop_zero]
  | 1 => by simp [kFourDropCovector, dotProduct, Fin.sum_univ_three, k4Drop_one]
  | 2 => by simp [kFourDropCovector, dotProduct, Fin.sum_univ_three, k4Drop_two]
  | 3 => by
      simp [kFourDropCovector, dotProduct, Fin.sum_univ_three, k4Drop_three]
      ring
  | 4 => by
      simp [kFourDropCovector, dotProduct, Fin.sum_univ_three, k4Drop_four]
      ring
  | 5 => by
      simp [kFourDropCovector, dotProduct, Fin.sum_univ_three, k4Drop_five]
      ring

/-- The reduced Laplacian as a matrix literal, for the adjugate rewrite. -/
theorem kFourWeightLaplacian_eq_matrixLiteral (mass : Fin 6 → ℝ) :
    kFourWeightLaplacian mass
      = !![mass 0 + mass 3 + mass 4, -mass 3, -mass 4;
           -mass 3, mass 1 + mass 3 + mass 5, -mass 5;
           -mass 4, -mass 5, mass 2 + mass 4 + mass 5] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> rfl

/-- **Step alpha, the matrix-tree leverage identity at K4**: the adjugate
pairing of each edge covector IS that edge's companion sum,
`v_c^T adj(B(m)) v_c = F_c(m)` -- the all-minors matrix-tree theorem at
the `3 x 3` instance, closed by `ring` per edge. -/
theorem dropCovector_dotProduct_adjugate_mulVec (mass : Fin 6 → ℝ) :
    ∀ edge : Fin 6,
      kFourDropCovector edge ⬝ᵥ
          ((kFourWeightLaplacian mass).adjugate).mulVec (kFourDropCovector edge)
        = kFourEdgeCompanionSum mass edge
  | 0 => by
      rw [kFourWeightLaplacian_eq_matrixLiteral, Matrix.adjugate_fin_three_of]
      simp [kFourDropCovector, kFourEdgeCompanionSum, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three]
      ring
  | 1 => by
      rw [kFourWeightLaplacian_eq_matrixLiteral, Matrix.adjugate_fin_three_of]
      simp [kFourDropCovector, kFourEdgeCompanionSum, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three]
      ring
  | 2 => by
      rw [kFourWeightLaplacian_eq_matrixLiteral, Matrix.adjugate_fin_three_of]
      simp [kFourDropCovector, kFourEdgeCompanionSum, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three]
      ring
  | 3 => by
      rw [kFourWeightLaplacian_eq_matrixLiteral, Matrix.adjugate_fin_three_of]
      simp [kFourDropCovector, kFourEdgeCompanionSum, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three]
      ring
  | 4 => by
      rw [kFourWeightLaplacian_eq_matrixLiteral, Matrix.adjugate_fin_three_of]
      simp [kFourDropCovector, kFourEdgeCompanionSum, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three]
      ring
  | 5 => by
      rw [kFourWeightLaplacian_eq_matrixLiteral, Matrix.adjugate_fin_three_of]
      simp [kFourDropCovector, kFourEdgeCompanionSum, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three]
      ring

/-- Step alpha in the ledger's division-free `nu` form:
`m_c * (v_c^T adj(B) v_c) = sum over trees through c of prod_T m`, i.e.
`m_c nu_c det B` is the mass tree sum through the edge. -/
theorem mass_mul_adjugatePairing_eq_treesThroughEdge_sum (mass : Fin 6 → ℝ)
    (edge : Fin 6) :
    mass edge * (kFourDropCovector edge ⬝ᵥ
        ((kFourWeightLaplacian mass).adjugate).mulVec (kFourDropCovector edge))
      = ((kFourTreesThroughEdge edge).map (kFourTreeWeightProduct mass)).sum := by
  rw [dropCovector_dotProduct_adjugate_mulVec,
    weight_mul_kFourEdgeCompanionSum]

/-! ## The det-trace law -/

/-- A conductance-product maximiser exists among the sixteen trees. -/
theorem exists_kFourTreeWeightProduct_max (conductance : Fin 6 → ℝ) :
    ∃ maxTree ∈ k4TreeTriples, ∀ tree ∈ k4TreeTriples,
      kFourTreeWeightProduct conductance tree
        ≤ kFourTreeWeightProduct conductance maxTree := by
  obtain ⟨maxTree, hmem, hmax⟩ := k4TreeTriples.toFinset.exists_max_image
    (kFourTreeWeightProduct conductance)
    ⟨(0, 1, 2), List.mem_toFinset.mpr (by decide)⟩
  exact ⟨maxTree, List.mem_toFinset.mp hmem,
    fun tree htree => hmax tree (List.mem_toFinset.mpr htree)⟩

/-- **The rung-8 bonus, kernel form**: EVERY tree's trace numerator is
strictly below the maximiser's conductance product --
`e1(T) det B < prod_{T*} y = e3(T*) det B` for all sixteen trees. -/
theorem kFourTraceNumerator_lt_maxTree_product
    (conductance weight : Fin 6 → ℝ)
    (hcond : ∀ edge, 0 < conductance edge) (hw : ∀ edge, 0 < weight edge)
    (hsum : ∑ edge, weight edge = 1)
    (maxTree : Fin 6 × Fin 6 × Fin 6)
    (hmax : ∀ tree ∈ k4TreeTriples,
      kFourTreeWeightProduct conductance tree
        ≤ kFourTreeWeightProduct conductance maxTree)
    (tree : Fin 6 × Fin 6 × Fin 6) (htree : tree ∈ k4TreeTriples) :
    kFourTraceNumerator conductance weight tree
      < kFourTreeWeightProduct conductance maxTree := by
  have hbeta := kFourTraceNumerator_le_bound_mul_treeQuadratic conductance
    weight (fun edge => (hw edge).le) _ hmax tree
  have hquad := kFourTreeQuadratic_lt_one weight hw hsum tree htree
  have hpos : 0 < kFourTreeWeightProduct conductance maxTree :=
    lt_of_lt_of_le (kFourTreeWeightProduct_pos conductance hcond tree)
      (hmax tree htree)
  have hshrink := mul_lt_mul_of_pos_left hquad hpos
  rw [mul_one] at hshrink
  linarith

/-- **THE K4 DET-TRACE LAW (rung 8).**  At any tree maximising the
conductance product, `e1(T*) det B < e3(T*) det B`: the trace of
`B^{-1} S_{T*}` is strictly below its determinant, so
`lambda_1 lambda_2 = e3/lambda_3 > 1` and at most ONE generalized
eigenvalue of the max tree can fail to exceed one. -/
theorem kFour_detTrace_law (conductance weight : Fin 6 → ℝ)
    (hcond : ∀ edge, 0 < conductance edge) (hw : ∀ edge, 0 < weight edge)
    (hsum : ∑ edge, weight edge = 1)
    (maxTree : Fin 6 × Fin 6 × Fin 6) (hmem : maxTree ∈ k4TreeTriples)
    (hmax : ∀ tree ∈ k4TreeTriples,
      kFourTreeWeightProduct conductance tree
        ≤ kFourTreeWeightProduct conductance maxTree) :
    kFourTraceNumerator conductance weight maxTree
      < kFourTreeWeightProduct conductance maxTree :=
  kFourTraceNumerator_lt_maxTree_product conductance weight hcond hw hsum
    maxTree hmax maxTree hmem

end Gtz

import Mathlib.LinearAlgebra.CrossProduct
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The plane two-form kit: quarter turn, resolve, and the Gram identity

Frame-free linear algebra on the plane orthogonal to a unit vector `u` in
`ℝ³`.  The quarter turn is `v ↦ u ⨯₃ v`; no basis of the plane is chosen.

* `plane_resolve` — a nonzero plane vector and its quarter turn resolve every
  plane vector: `(v·v) • x = (x·v) • v + (x·Jv) • Jv`.
* `plane_pythagoras`, `plane_polar` — the reading identities of the resolve.
* `cross_binet` — the plane determinant read in turn coordinates.
* `threeForm_diag`, `threeForm_gram` — **the Gram identity** of the
  three-atom plane form `Φ(w) = (x·w)² + (y·w)² + (z·w)² − w·w`:

    `Φ(v)·Φ(w) − Ψ(v,w)² = D · (u·(v ⨯₃ w))²`

  with `Ψ` the polar form and `D` the two-by-two determinant invariant
  `Σ (u·(atom ⨯₃ atom'))² − Σ |atom|² + 1`.  The diagonal pair `(v, u ⨯₃ v)`
  is the Lagrange identity; the resolve transports it to every pair.
* `threeForm_det_pos` — a positive definite plane form has `D > 0`.
* `threeForm_turn_floor` — a witness `w` where one atom's reading covers the
  form prices the turned atom: `Φ(w) ≤ (q·w)²` forces `D·|q|² ≤ Φ(u ⨯₃ q)`
  when `Φ(w) > 0` and `D ≥ 0`.

A pair form is the same object with the third atom set to `0`, so every
statement covers the pair instances of the planar corank-two endgame.
-/

namespace Gtz

open Matrix

/-! ## 1. The quarter turn -/

theorem cross_smul_left (a : ℝ) (x y : Fin 3 → ℝ) :
    (a • x) ⨯₃ y = a • (x ⨯₃ y) := by
  rw [map_smul, LinearMap.smul_apply]

theorem cross_add_left (x x' y : Fin 3 → ℝ) :
    (x + x') ⨯₃ y = x ⨯₃ y + x' ⨯₃ y := by
  rw [map_add, LinearMap.add_apply]

theorem turn_dot_u (u v : Fin 3 → ℝ) : (u ⨯₃ v) ⬝ᵥ u = 0 := by
  rw [dotProduct_comm]
  exact dot_self_cross u v

theorem turn_dot_self (u v : Fin 3 → ℝ) : (u ⨯₃ v) ⬝ᵥ v = 0 := by
  rw [dotProduct_comm]
  exact dot_cross_self u v

theorem turn_normSq {u v : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ u = 0) :
    (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) = v ⬝ᵥ v := by
  rw [cross_dot_cross, hunit, dotProduct_comm u v, hv]
  ring

theorem turn_normSq_general {u : Fin 3 → ℝ} (q : Fin 3 → ℝ)
    (hunit : u ⬝ᵥ u = 1) :
    (u ⨯₃ q) ⬝ᵥ (u ⨯₃ q) = q ⬝ᵥ q - (q ⬝ᵥ u) ^ 2 := by
  rw [cross_dot_cross, hunit, dotProduct_comm u q]
  ring

theorem turn_read (u v w : Fin 3 → ℝ) : u ⬝ᵥ v ⨯₃ w = w ⬝ᵥ u ⨯₃ v := by
  rw [triple_product_permutation, triple_product_permutation v w u]

/-- The turned-pair reading: `u·((u ⨯₃ q) ⨯₃ w) = −(q·w)` for plane `w` and
arbitrary `q`. -/
theorem turn_cross_read {u q w : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hw : w ⬝ᵥ u = 0) :
    u ⬝ᵥ (u ⨯₃ q) ⨯₃ w = -(q ⬝ᵥ w) := by
  have h := congrArg (fun t => u ⬝ᵥ t) (cross_cross_eq_smul_sub_smul u q w)
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
  rw [show u ⬝ᵥ w = 0 from by rwa [dotProduct_comm] at hw, hunit] at h
  rw [h]
  ring

/-! ## 2. The resolve -/

/-- **The resolve.**  A nonzero plane vector and its quarter turn resolve
every plane vector. -/
theorem plane_resolve {u x v : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hx : x ⬝ᵥ u = 0) (hv : v ⬝ᵥ u = 0) (hvne : v ≠ 0) :
    (v ⬝ᵥ v) • x = (x ⬝ᵥ v) • v + (x ⬝ᵥ (u ⨯₃ v)) • (u ⨯₃ v) := by
  have hyv : ((v ⬝ᵥ v) • x - (x ⬝ᵥ v) • v - (x ⬝ᵥ (u ⨯₃ v)) • (u ⨯₃ v)) ⬝ᵥ v
      = 0 := by
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [turn_dot_self, dotProduct_comm x v]
    ring
  have hyu : u ⬝ᵥ ((v ⬝ᵥ v) • x - (x ⬝ᵥ v) • v - (x ⬝ᵥ (u ⨯₃ v)) • (u ⨯₃ v))
      = 0 := by
    rw [dotProduct_comm]
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hx, hv, turn_dot_u]
    ring
  have hyJ : ((v ⬝ᵥ v) • x - (x ⬝ᵥ v) • v - (x ⬝ᵥ (u ⨯₃ v)) • (u ⨯₃ v))
      ⬝ᵥ (u ⨯₃ v) = 0 := by
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [turn_normSq hunit hv, dotProduct_comm v (u ⨯₃ v), turn_dot_self]
    ring
  have hcombo : ((v ⬝ᵥ v) • x - (x ⬝ᵥ v) • v - (x ⬝ᵥ (u ⨯₃ v)) • (u ⨯₃ v))
      ⨯₃ (u ⨯₃ v) = 0 := by
    rw [cross_cross_eq_smul_sub_smul', hyv, hyu]
    simp
  have hnormzero :
      (((v ⬝ᵥ v) • x - (x ⬝ᵥ v) • v - (x ⬝ᵥ (u ⨯₃ v)) • (u ⨯₃ v))
          ⬝ᵥ ((v ⬝ᵥ v) • x - (x ⬝ᵥ v) • v - (x ⬝ᵥ (u ⨯₃ v)) • (u ⨯₃ v)))
        * (v ⬝ᵥ v) = 0 := by
    have hdd := cross_dot_cross
      ((v ⬝ᵥ v) • x - (x ⬝ᵥ v) • v - (x ⬝ᵥ (u ⨯₃ v)) • (u ⨯₃ v)) (u ⨯₃ v)
      ((v ⬝ᵥ v) • x - (x ⬝ᵥ v) • v - (x ⬝ᵥ (u ⨯₃ v)) • (u ⨯₃ v)) (u ⨯₃ v)
    rw [hcombo, hyJ, turn_normSq hunit hv] at hdd
    simpa using hdd.symm
  have hyzero : (v ⬝ᵥ v) • x - (x ⬝ᵥ v) • v - (x ⬝ᵥ (u ⨯₃ v)) • (u ⨯₃ v)
      = 0 := by
    rcases mul_eq_zero.mp hnormzero with h | h
    · exact eq_zero_of_dotProduct_self_eq_zero h
    · exact absurd h (ne_of_gt (dotProduct_self_pos hvne))
  rw [sub_sub] at hyzero
  exact sub_eq_zero.mp hyzero

/-- **Pythagoras in the plane.** -/
theorem plane_pythagoras {u x v : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hx : x ⬝ᵥ u = 0) (hv : v ⬝ᵥ u = 0) :
    (x ⬝ᵥ v) ^ 2 + (x ⬝ᵥ (u ⨯₃ v)) ^ 2 = (x ⬝ᵥ x) * (v ⬝ᵥ v) := by
  rcases eq_or_ne v 0 with rfl | hvne
  · simp
  · have h := congrArg (fun t => t ⬝ᵥ x) (plane_resolve hunit hx hv hvne)
    simp only [smul_dotProduct, add_dotProduct, smul_eq_mul] at h
    rw [dotProduct_comm v x, dotProduct_comm (u ⨯₃ v) x] at h
    nlinarith [h]

/-- The polarized resolve reading, for a plane `x` against an arbitrary
`y`. -/
theorem plane_polar {u x v : Fin 3 → ℝ} (y : Fin 3 → ℝ) (hunit : u ⬝ᵥ u = 1)
    (hx : x ⬝ᵥ u = 0) (hv : v ⬝ᵥ u = 0) :
    (v ⬝ᵥ v) * (x ⬝ᵥ y) = (x ⬝ᵥ v) * (y ⬝ᵥ v)
      + (x ⬝ᵥ (u ⨯₃ v)) * (y ⬝ᵥ (u ⨯₃ v)) := by
  rcases eq_or_ne v 0 with rfl | hvne
  · simp
  · have h := congrArg (fun t => t ⬝ᵥ y) (plane_resolve hunit hx hv hvne)
    simp only [smul_dotProduct, add_dotProduct, smul_eq_mul] at h
    rw [dotProduct_comm v y, dotProduct_comm (u ⨯₃ v) y] at h
    linarith [h]

/-- **The plane determinant in turn coordinates.** -/
theorem cross_binet {u x y v : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hx : x ⬝ᵥ u = 0) (hy : y ⬝ᵥ u = 0) (hv : v ⬝ᵥ u = 0) :
    (v ⬝ᵥ v) * (u ⬝ᵥ x ⨯₃ y)
      = (x ⬝ᵥ v) * (y ⬝ᵥ (u ⨯₃ v)) - (x ⬝ᵥ (u ⨯₃ v)) * (y ⬝ᵥ v) := by
  rcases eq_or_ne v 0 with rfl | hvne
  · simp
  · have hres := plane_resolve hunit hx hv hvne
    have hcross : ((v ⬝ᵥ v) • x) ⨯₃ y
        = (x ⬝ᵥ v) • (v ⨯₃ y) + (x ⬝ᵥ (u ⨯₃ v)) • ((u ⨯₃ v) ⨯₃ y) := by
      rw [hres, cross_add_left, cross_smul_left, cross_smul_left]
    have h := congrArg (fun t => u ⬝ᵥ t) hcross
    simp only [dotProduct_smul, dotProduct_add, smul_eq_mul] at h
    rw [cross_smul_left, dotProduct_smul, smul_eq_mul] at h
    rw [show u ⬝ᵥ v ⨯₃ y = y ⬝ᵥ u ⨯₃ v from turn_read u v y,
      turn_cross_read hunit hy] at h
    rw [h, dotProduct_comm v y]
    ring

/-! ## 3. The Gram identity of the three-atom form -/

/-- **The Gram identity on the diagonal pair** `(v, u ⨯₃ v)`: the Lagrange
identity in turn coordinates. -/
theorem threeForm_diag {u x y z v : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hx : x ⬝ᵥ u = 0) (hy : y ⬝ᵥ u = 0) (hz : z ⬝ᵥ u = 0)
    (hv : v ⬝ᵥ u = 0) :
    ((x ⬝ᵥ v) ^ 2 + (y ⬝ᵥ v) ^ 2 + (z ⬝ᵥ v) ^ 2 - v ⬝ᵥ v)
        * ((x ⬝ᵥ (u ⨯₃ v)) ^ 2 + (y ⬝ᵥ (u ⨯₃ v)) ^ 2 + (z ⬝ᵥ (u ⨯₃ v)) ^ 2
            - v ⬝ᵥ v)
      - ((x ⬝ᵥ v) * (x ⬝ᵥ (u ⨯₃ v)) + (y ⬝ᵥ v) * (y ⬝ᵥ (u ⨯₃ v))
          + (z ⬝ᵥ v) * (z ⬝ᵥ (u ⨯₃ v))) ^ 2
      = ((u ⬝ᵥ x ⨯₃ y) ^ 2 + (u ⬝ᵥ x ⨯₃ z) ^ 2 + (u ⬝ᵥ y ⨯₃ z) ^ 2
          - (x ⬝ᵥ x + y ⬝ᵥ y + z ⬝ᵥ z) + 1) * (v ⬝ᵥ v) ^ 2 := by
  have hxx := plane_pythagoras hunit hx hv
  have hyy := plane_pythagoras hunit hy hv
  have hzz := plane_pythagoras hunit hz hv
  have hAxy := cross_binet hunit hx hy hv
  have hAxz := cross_binet hunit hx hz hv
  have hAyz := cross_binet hunit hy hz hv
  linear_combination
    (-((v ⬝ᵥ v) * (u ⬝ᵥ x ⨯₃ y)
        + ((x ⬝ᵥ v) * (y ⬝ᵥ (u ⨯₃ v)) - (x ⬝ᵥ (u ⨯₃ v)) * (y ⬝ᵥ v)))) * hAxy
    + (-((v ⬝ᵥ v) * (u ⬝ᵥ x ⨯₃ z)
        + ((x ⬝ᵥ v) * (z ⬝ᵥ (u ⨯₃ v)) - (x ⬝ᵥ (u ⨯₃ v)) * (z ⬝ᵥ v)))) * hAxz
    + (-((v ⬝ᵥ v) * (u ⬝ᵥ y ⨯₃ z)
        + ((y ⬝ᵥ v) * (z ⬝ᵥ (u ⨯₃ v)) - (y ⬝ᵥ (u ⨯₃ v)) * (z ⬝ᵥ v)))) * hAyz
    + (-(v ⬝ᵥ v)) * hxx + (-(v ⬝ᵥ v)) * hyy + (-(v ⬝ᵥ v)) * hzz

/-- **The general Gram identity** of the three-atom plane form. -/
theorem threeForm_gram {u x y z v w : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hx : x ⬝ᵥ u = 0) (hy : y ⬝ᵥ u = 0) (hz : z ⬝ᵥ u = 0)
    (hv : v ⬝ᵥ u = 0) (hw : w ⬝ᵥ u = 0) :
    ((x ⬝ᵥ v) ^ 2 + (y ⬝ᵥ v) ^ 2 + (z ⬝ᵥ v) ^ 2 - v ⬝ᵥ v)
        * ((x ⬝ᵥ w) ^ 2 + (y ⬝ᵥ w) ^ 2 + (z ⬝ᵥ w) ^ 2 - w ⬝ᵥ w)
      - ((x ⬝ᵥ v) * (x ⬝ᵥ w) + (y ⬝ᵥ v) * (y ⬝ᵥ w) + (z ⬝ᵥ v) * (z ⬝ᵥ w)
          - v ⬝ᵥ w) ^ 2
      = ((u ⬝ᵥ x ⨯₃ y) ^ 2 + (u ⬝ᵥ x ⨯₃ z) ^ 2 + (u ⬝ᵥ y ⨯₃ z) ^ 2
          - (x ⬝ᵥ x + y ⬝ᵥ y + z ⬝ᵥ z) + 1) * (u ⬝ᵥ v ⨯₃ w) ^ 2 := by
  rcases eq_or_ne v 0 with rfl | hvne
  · simp
  · have hn : (0 : ℝ) < v ⬝ᵥ v := dotProduct_self_pos hvne
    have hrx := plane_polar (u := u) (x := w) (v := v) x hunit hw hv
    have hry := plane_polar (u := u) (x := w) (v := v) y hunit hw hv
    have hrz := plane_polar (u := u) (x := w) (v := v) z hunit hw hv
    have hrw := plane_polar (u := u) (x := w) (v := v) w hunit hw hv
    have hvJ : v ⬝ᵥ (u ⨯₃ v) = 0 := by
      rw [dotProduct_comm]; exact turn_dot_self u v
    have hU := cross_binet (x := v) (y := w) hunit hv hw hv
    rw [hvJ, zero_mul, sub_zero] at hU
    have hdiag := threeForm_diag (v := v) hunit hx hy hz hv
    -- transport: multiply the goal by (v·v)² and eliminate through the
    -- polar readings
    have hkey : (v ⬝ᵥ v) ^ 2
          * (((x ⬝ᵥ v) ^ 2 + (y ⬝ᵥ v) ^ 2 + (z ⬝ᵥ v) ^ 2 - v ⬝ᵥ v)
              * ((x ⬝ᵥ w) ^ 2 + (y ⬝ᵥ w) ^ 2 + (z ⬝ᵥ w) ^ 2 - w ⬝ᵥ w)
            - ((x ⬝ᵥ v) * (x ⬝ᵥ w) + (y ⬝ᵥ v) * (y ⬝ᵥ w)
                + (z ⬝ᵥ v) * (z ⬝ᵥ w) - w ⬝ᵥ v) ^ 2)
        = (v ⬝ᵥ v) ^ 2
          * (((u ⬝ᵥ x ⨯₃ y) ^ 2 + (u ⬝ᵥ x ⨯₃ z) ^ 2 + (u ⬝ᵥ y ⨯₃ z) ^ 2
              - (x ⬝ᵥ x + y ⬝ᵥ y + z ⬝ᵥ z) + 1) * (u ⬝ᵥ v ⨯₃ w) ^ 2) := by
      set n : ℝ := v ⬝ᵥ v
      set av : ℝ := w ⬝ᵥ v
      set bv : ℝ := w ⬝ᵥ (u ⨯₃ v)
      set ax : ℝ := x ⬝ᵥ v
      set bx : ℝ := x ⬝ᵥ (u ⨯₃ v)
      set ay : ℝ := y ⬝ᵥ v
      set by' : ℝ := y ⬝ᵥ (u ⨯₃ v)
      set az : ℝ := z ⬝ᵥ v
      set bz : ℝ := z ⬝ᵥ (u ⨯₃ v)
      rw [dotProduct_comm w x] at hrx
      rw [dotProduct_comm w y] at hry
      rw [dotProduct_comm w z] at hrz
      linear_combination
        (bv ^ 2) * hdiag
        + ((ax ^ 2 + ay ^ 2 + az ^ 2 - n)
            * ((n * (x ⬝ᵥ w)) + (av * ax + bv * bx))
          - (2 * (av * (ax ^ 2 + ay ^ 2 + az ^ 2 - n)
                + bv * (ax * bx + ay * by' + az * bz))
              + (ax * (n * (x ⬝ᵥ w) - (av * ax + bv * bx))
                + ay * (n * (y ⬝ᵥ w) - (av * ay + bv * by'))
                + az * (n * (z ⬝ᵥ w) - (av * az + bv * bz))
                )) * ax) * hrx
        + ((ax ^ 2 + ay ^ 2 + az ^ 2 - n)
            * ((n * (y ⬝ᵥ w)) + (av * ay + bv * by'))
          - (2 * (av * (ax ^ 2 + ay ^ 2 + az ^ 2 - n)
                + bv * (ax * bx + ay * by' + az * bz))
              + (ax * (n * (x ⬝ᵥ w) - (av * ax + bv * bx))
                + ay * (n * (y ⬝ᵥ w) - (av * ay + bv * by'))
                + az * (n * (z ⬝ᵥ w) - (av * az + bv * bz))
                )) * ay) * hry
        + ((ax ^ 2 + ay ^ 2 + az ^ 2 - n)
            * ((n * (z ⬝ᵥ w)) + (av * az + bv * bz))
          - (2 * (av * (ax ^ 2 + ay ^ 2 + az ^ 2 - n)
                + bv * (ax * bx + ay * by' + az * bz))
              + (ax * (n * (x ⬝ᵥ w) - (av * ax + bv * bx))
                + ay * (n * (y ⬝ᵥ w) - (av * ay + bv * by'))
                + az * (n * (z ⬝ᵥ w) - (av * az + bv * bz))
                )) * az) * hrz
        + (-(n * (ax ^ 2 + ay ^ 2 + az ^ 2 - n))) * hrw
        + (-(((u ⬝ᵥ x ⨯₃ y) ^ 2 + (u ⬝ᵥ x ⨯₃ z) ^ 2 + (u ⬝ᵥ y ⨯₃ z) ^ 2
              - (x ⬝ᵥ x + y ⬝ᵥ y + z ⬝ᵥ z) + 1)
            * (n * (u ⬝ᵥ v ⨯₃ w) + n * bv))) * hU
    rw [dotProduct_comm v w]
    exact mul_left_cancel₀ (by positivity : (v ⬝ᵥ v) ^ 2 ≠ 0) hkey

/-- **A positive definite plane form has a positive determinant
invariant.**  The nonzero plane direction is supplied by the caller. -/
theorem threeForm_det_pos {u x y z v : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hx : x ⬝ᵥ u = 0) (hy : y ⬝ᵥ u = 0) (hz : z ⬝ᵥ u = 0)
    (hv : v ⬝ᵥ u = 0) (hvne : v ≠ 0)
    (hpos : ∀ w : Fin 3 → ℝ, w ⬝ᵥ u = 0 → w ≠ 0 →
      0 < (x ⬝ᵥ w) ^ 2 + (y ⬝ᵥ w) ^ 2 + (z ⬝ᵥ w) ^ 2 - w ⬝ᵥ w) :
    0 < (u ⬝ᵥ x ⨯₃ y) ^ 2 + (u ⬝ᵥ x ⨯₃ z) ^ 2 + (u ⬝ᵥ y ⨯₃ z) ^ 2
        - (x ⬝ᵥ x + y ⬝ᵥ y + z ⬝ᵥ z) + 1 := by
  have hn : (0 : ℝ) < v ⬝ᵥ v := dotProduct_self_pos hvne
  have hJu : (u ⨯₃ v) ⬝ᵥ u = 0 := turn_dot_u u v
  have hJne : u ⨯₃ v ≠ 0 := by
    intro hzero
    have h := turn_normSq hunit hv
    rw [hzero] at h
    simp only [zero_dotProduct] at h
    exact absurd h.symm (ne_of_gt hn)
  have hFv := hpos v hv hvne
  have hFJ := hpos (u ⨯₃ v) hJu hJne
  rw [turn_normSq hunit hv] at hFJ
  have hdiag := threeForm_diag (v := v) hunit hx hy hz hv
  by_contra hcon
  push_neg at hcon
  -- the witness with a nonpositive form value
  set Px : ℝ := (x ⬝ᵥ v) * (x ⬝ᵥ (u ⨯₃ v)) + (y ⬝ᵥ v) * (y ⬝ᵥ (u ⨯₃ v))
      + (z ⬝ᵥ v) * (z ⬝ᵥ (u ⨯₃ v)) with hPx
  set Fv : ℝ := (x ⬝ᵥ v) ^ 2 + (y ⬝ᵥ v) ^ 2 + (z ⬝ᵥ v) ^ 2 - v ⬝ᵥ v with hFvdef
  set w : Fin 3 → ℝ := (-Px) • v + Fv • (u ⨯₃ v) with hw
  have hwu : w ⬝ᵥ u = 0 := by
    simp only [hw, add_dotProduct, smul_dotProduct, smul_eq_mul, hv,
      turn_dot_u]
    ring
  have hwne : w ≠ 0 := by
    intro hzero
    have hdotJ := congrArg (fun t => t ⬝ᵥ (u ⨯₃ v)) hzero
    simp only [hw, add_dotProduct, smul_dotProduct, smul_eq_mul,
      zero_dotProduct] at hdotJ
    rw [show v ⬝ᵥ (u ⨯₃ v) = 0 from by
        rw [dotProduct_comm]; exact turn_dot_self u v,
      turn_normSq hunit hv] at hdotJ
    have hzero' : Fv * (v ⬝ᵥ v) = 0 := by linarith [hdotJ]
    rcases mul_eq_zero.mp hzero' with h | h
    · exact absurd h (ne_of_gt hFv)
    · exact absurd h (ne_of_gt hn)
  have hval : (x ⬝ᵥ w) ^ 2 + (y ⬝ᵥ w) ^ 2 + (z ⬝ᵥ w) ^ 2 - w ⬝ᵥ w
      = Fv * (Fv * ((x ⬝ᵥ (u ⨯₃ v)) ^ 2 + (y ⬝ᵥ (u ⨯₃ v)) ^ 2
          + (z ⬝ᵥ (u ⨯₃ v)) ^ 2 - v ⬝ᵥ v) - Px ^ 2) := by
    simp only [hw, dotProduct_add, dotProduct_smul, add_dotProduct,
      smul_dotProduct, smul_eq_mul]
    rw [turn_normSq hunit hv,
      show v ⬝ᵥ (u ⨯₃ v) = 0 from by
        rw [dotProduct_comm]; exact turn_dot_self u v,
      show (u ⨯₃ v) ⬝ᵥ v = 0 from turn_dot_self u v]
    simp only [hPx, hFvdef]
    ring
  have hposw := hpos w hwu hwne
  rw [hval, hdiag] at hposw
  nlinarith [hposw, hcon, mul_nonneg hFv.le (sq_nonneg (v ⬝ᵥ v))]

/-- **The turned-atom floor.**  A witness where a scaled reading covers the
positive form prices the turned reader against the determinant invariant.
The reader `q` need not be planar; its turn is. -/
theorem threeForm_turn_floor {u x y z q w : Fin 3 → ℝ} {c : ℝ}
    (hunit : u ⬝ᵥ u = 1)
    (hx : x ⬝ᵥ u = 0) (hy : y ⬝ᵥ u = 0) (hz : z ⬝ᵥ u = 0)
    (hw : w ⬝ᵥ u = 0)
    (hwitness : c * ((x ⬝ᵥ w) ^ 2 + (y ⬝ᵥ w) ^ 2 + (z ⬝ᵥ w) ^ 2 - w ⬝ᵥ w)
      ≤ (q ⬝ᵥ w) ^ 2)
    (hpos : 0 < (x ⬝ᵥ w) ^ 2 + (y ⬝ᵥ w) ^ 2 + (z ⬝ᵥ w) ^ 2 - w ⬝ᵥ w)
    (hdet : 0 ≤ (u ⬝ᵥ x ⨯₃ y) ^ 2 + (u ⬝ᵥ x ⨯₃ z) ^ 2 + (u ⬝ᵥ y ⨯₃ z) ^ 2
        - (x ⬝ᵥ x + y ⬝ᵥ y + z ⬝ᵥ z) + 1) :
    c * ((u ⬝ᵥ x ⨯₃ y) ^ 2 + (u ⬝ᵥ x ⨯₃ z) ^ 2 + (u ⬝ᵥ y ⨯₃ z) ^ 2
        - (x ⬝ᵥ x + y ⬝ᵥ y + z ⬝ᵥ z) + 1)
      ≤ (x ⬝ᵥ (u ⨯₃ q)) ^ 2 + (y ⬝ᵥ (u ⨯₃ q)) ^ 2 + (z ⬝ᵥ (u ⨯₃ q)) ^ 2
        - (q ⬝ᵥ q - (q ⬝ᵥ u) ^ 2) := by
  have hJq : (u ⨯₃ q) ⬝ᵥ u = 0 := turn_dot_u u q
  have hgram := threeForm_gram (v := u ⨯₃ q) (w := w) hunit hx hy hz hJq hw
  rw [turn_cross_read hunit hw, turn_normSq_general q hunit] at hgram
  have hDW : ((u ⬝ᵥ x ⨯₃ y) ^ 2 + (u ⬝ᵥ x ⨯₃ z) ^ 2 + (u ⬝ᵥ y ⨯₃ z) ^ 2
        - (x ⬝ᵥ x + y ⬝ᵥ y + z ⬝ᵥ z) + 1)
        * (c * ((x ⬝ᵥ w) ^ 2 + (y ⬝ᵥ w) ^ 2 + (z ⬝ᵥ w) ^ 2 - w ⬝ᵥ w))
      ≤ ((u ⬝ᵥ x ⨯₃ y) ^ 2 + (u ⬝ᵥ x ⨯₃ z) ^ 2 + (u ⬝ᵥ y ⨯₃ z) ^ 2
        - (x ⬝ᵥ x + y ⬝ᵥ y + z ⬝ᵥ z) + 1) * (q ⬝ᵥ w) ^ 2 :=
    mul_le_mul_of_nonneg_left hwitness hdet
  have hchain : (c * ((u ⬝ᵥ x ⨯₃ y) ^ 2 + (u ⬝ᵥ x ⨯₃ z) ^ 2
        + (u ⬝ᵥ y ⨯₃ z) ^ 2 - (x ⬝ᵥ x + y ⬝ᵥ y + z ⬝ᵥ z) + 1))
        * ((x ⬝ᵥ w) ^ 2 + (y ⬝ᵥ w) ^ 2 + (z ⬝ᵥ w) ^ 2 - w ⬝ᵥ w)
      ≤ ((x ⬝ᵥ (u ⨯₃ q)) ^ 2 + (y ⬝ᵥ (u ⨯₃ q)) ^ 2 + (z ⬝ᵥ (u ⨯₃ q)) ^ 2
          - (q ⬝ᵥ q - (q ⬝ᵥ u) ^ 2))
        * ((x ⬝ᵥ w) ^ 2 + (y ⬝ᵥ w) ^ 2 + (z ⬝ᵥ w) ^ 2 - w ⬝ᵥ w) := by
    nlinarith [hgram, hDW,
      sq_nonneg ((x ⬝ᵥ (u ⨯₃ q)) * (x ⬝ᵥ w) + (y ⬝ᵥ (u ⨯₃ q)) * (y ⬝ᵥ w)
        + (z ⬝ᵥ (u ⨯₃ q)) * (z ⬝ᵥ w) - (u ⨯₃ q) ⬝ᵥ w)]
  exact le_of_mul_le_mul_right hchain hpos

end Gtz

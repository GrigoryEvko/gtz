import Gtz.Wave.SecondInvariantLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The shell anchor

The both-light roof lives at the total weight collapse: one outside weight
absorbs the simplex and the pencil frame degenerates along one axis.  In
that limit the measured system reduces to a pure opposition: the seventh
floor demands a subconvex combination of three capped quantities to reach
one, and the corner links then force the collapse axis components of the
corner atoms into an exactly impossible configuration.

This module lands the two exact anchors of that analysis.

* `Gtz.shell_equality_forcing` — the arithmetic core: if the weights are a
  subprobability vector, the three quantities obey their caps, and the
  seventh-floor combination reaches one, then EVERY slack vanishes: the cap
  deficits, the spectator weights, and the weighted `s`-margin all are zero.
  Pure linear arithmetic, no geometry.

* `Gtz.corner_oneAxisZero_not_parallel` — the geometric kill at the forced
  configuration: on the corner the inside atoms cannot be parallel to the
  erased atom.  The landed orthogonality `g_x·g_y = 0` and the unit norm
  `|g_x| = 1` make parallelism collapse the inside atom to zero, and the
  cell hypothesis `a_y ≠ 0` refuses.

Together: the shell's equality corner forces the transverse data to vanish,
vanishing transverse data makes the corner atoms parallel, and parallel
corner atoms are absurd.  The quantitative interpolation between the two
anchors is the remaining shell work.
-/

namespace Gtz

open Matrix Finset

/-- **THE EQUALITY FORCING.**  If `w` is a subprobability five-vector, the
three quantities obey caps `h² ≤ 1 − s` with `s ≥ 0`, `a² ≤ 1`, `b² ≤ 1`,
and the seventh-floor combination reaches one, then every slack vanishes. -/
theorem shell_equality_forcing {wx wy wz w5 w6 s h a b : ℝ}
    (hwx : 0 ≤ wx) (hwy : 0 ≤ wy) (hwz : 0 ≤ wz) (hw5 : 0 ≤ w5) (hw6 : 0 ≤ w6)
    (hsum : wx + wy + wz + w5 + w6 = 1)
    (hs : 0 ≤ s) (hh : h ^ 2 ≤ 1 - s) (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1)
    (hfloor : 1 ≤ wx * h ^ 2 + wy * a ^ 2 + wz * b ^ 2) :
    wx * s = 0 ∧ wy * (1 - a ^ 2) = 0 ∧ wz * (1 - b ^ 2) = 0
      ∧ w5 = 0 ∧ w6 = 0 := by
  have h1 : wx * h ^ 2 ≤ wx * (1 - s) := by
    exact mul_le_mul_of_nonneg_left hh hwx
  have h2 : wy * a ^ 2 ≤ wy * 1 := mul_le_mul_of_nonneg_left ha hwy
  have h3 : wz * b ^ 2 ≤ wz * 1 := mul_le_mul_of_nonneg_left hb hwz
  have hxs : 0 ≤ wx * s := mul_nonneg hwx hs
  have hya : 0 ≤ wy * (1 - a ^ 2) := mul_nonneg hwy (by linarith)
  have hzb : 0 ≤ wz * (1 - b ^ 2) := mul_nonneg hwz (by linarith)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- **THE CORNER ATOMS ARE NEVER PARALLEL.**  On the corner, an inside atom
that reads the axis cannot be a multiple of the erased atom: orthogonality
plus the unit norm would collapse it to zero. -/
theorem corner_oneAxisZero_not_parallel (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (hay : D.atom y ⬝ᵥ u ≠ 0) :
    ∀ c : ℝ, D.atom y ≠ c • D.atom x := by
  intro c hcon
  have hxy0 : D.atom x ⬝ᵥ D.atom y = 0 :=
    (corner_oneAxisZero_xOrthogonal D hxy hxz hyz hlam.le hunit hgap hax).1
  have hxunit : D.atom x ⬝ᵥ D.atom x = 1 :=
    corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam.le hunit hgap
      (by simp) hax
  have hc0 : c = 0 := by
    have hdot : D.atom x ⬝ᵥ (c • D.atom x) = c := by
      rw [dotProduct_smul, hxunit, smul_eq_mul, mul_one]
    rw [hcon, hdot] at hxy0
    exact hxy0
  rw [hc0, zero_smul] at hcon
  exact hay (by rw [hcon]; simp)

/-- The `z`-side twin of the parallel refusal. -/
theorem corner_oneAxisZero_not_parallel_z (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0) :
    ∀ c : ℝ, D.atom z ≠ c • D.atom x := by
  intro c hcon
  have hxz0 : D.atom x ⬝ᵥ D.atom z = 0 :=
    (corner_oneAxisZero_xOrthogonal D hxy hxz hyz hlam.le hunit hgap hax).2
  have hxunit : D.atom x ⬝ᵥ D.atom x = 1 :=
    corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam.le hunit hgap
      (by simp) hax
  have hc0 : c = 0 := by
    have hdot : D.atom x ⬝ᵥ (c • D.atom x) = c := by
      rw [dotProduct_smul, hxunit, smul_eq_mul, mul_one]
    rw [hcon, hdot] at hxz0
    exact hxz0
  rw [hc0, zero_smul] at hcon
  exact haz (by rw [hcon]; simp)

end Gtz

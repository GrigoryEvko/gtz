/-
# The frame normal form of the two-zero stratum

`Gtz.k2Chart_kill` empties the `(5,3)` two-zero CHART.  Between it and the
design-level kill sits the bridge: every design-level two-zero tie must satisfy
the chart hypotheses.  This module lands the backbone of that bridge — the
normal form — and it turns out to be nothing but Parseval read at two probes.

## The configuration

A two-zero dominator `C = {x, y, z}` has an AXIS atom `x` of unit leverage
orthogonal to its two partners, so `w := g_x` is a unit null direction of the
gap and the partners are plane atoms.  In `Gtz.axisTriple_bracket_sq` the same
configuration is written `leverageOf (D.atom x) = 1`, `atomPairing D x y = 0`,
`atomPairing D x z = 0`, and that is the shape used here.

## The two readings

Everything the chart needs comes from `Gtz.parseval_bilinear` at the axis:

* **the axis total** (`Gtz.k2Axis_reading_total`) — the weighted squared axis
  readings of ALL atoms total one, because the axis has unit leverage;
* **the mixed total** (`Gtz.k2Axis_mixed_total_zero`) — against any probe
  orthogonal to the axis, the weighted products of the axis reading and the
  probe reading total zero.

The plane atoms drop out of both sums (they read the axis at zero), and the
axis reads itself at one.  So at `(5,3)`, with outside atoms `d` and `e`:

* the axis total becomes `t_x + t_d·α² + t_e·β² = 1` with `α = g_d·w`,
  `β = g_e·w` (`Gtz.k2FiveAxis_reading`), whence the chart's excess equation
  `t_d·ed + t_e·ee = t_y + t_z` with `ed = α² − 1`
  (`Gtz.k2FiveAxis_excess_eq`), and the chart's budget `t_d+t_e+t_y+t_z < 1`
  (`Gtz.k2FiveAxis_budget`);
* the mixed total becomes **`t_d·α·(g_d·u) + t_e·β·(g_e·u) = 0`** for every
  probe `u` orthogonal to the axis (`Gtz.k2FiveAxis_collinear`).  That is THE
  COLLINEARITY: the two outside plane parts lie on one line, which is what
  makes the plane a two-atom problem and the chart eight-dimensional.

The collinearity has an immediate reading (`Gtz.k2FiveAxis_planePair_reading`):
against a probe orthogonal to the axis AND to the plane part of `d`, both
outside atoms read zero, so the plane pair alone resolves the probe,

  `t_y·(g_y·n)² + t_z·(g_z·n)² = n·n` .

At a unit such probe the two summands are the chart's plane angle `X` and its
complement, so `0 ≤ X ≤ 1` is free — the chart's angle hypotheses cost nothing.

## What is measured, and not yet proved

[MEASURED, `scratchpad/f51/`, 40000 exact weak-dominator designs.]  The
remaining chart coordinates are `P = |g_d − (g_d·w)w|²`, the squared plane part
of `d`, and `X = t_y·(g_y·n)²` above.  With those, all four chart slacks are
the four refusal determinants times POSITIVE monomials —
`CapD = −t_y t_z t_e(1+ee)·det(S_{y,z,d}−1)`,
`CapE = −t_y t_z t_e²(1+ee)·det(S_{y,z,e}−1)`,
`RefusalY = −t_y t_e²(1+ee)·det(S_{y,d,e}−1)`,
`RefusalZ = −t_z t_e²(1+ee)·det(S_{z,d,e}−1)` — so each slack is nonnegative
exactly when its triple is refused (residuals `1e-13` over 200 designs).  The
four strict chart positives hold at 40000 of 40000 weak-dominator designs, and
two of them have exact design readings,
`Vn = t_y t_z((g_y·n)² + (g_z·n)² − 1)` and
`Wom = t_e β² t_y t_z·(plane bracket)²` (residuals `1e-16`), so `Wom > 0` is
exactly the independence of the plane pair and `Vn > 0` follows from the plane
reading above together with `t_y, t_z < 1`.  None of that is in the kernel yet.
-/
import Gtz.Wave.PairNormalParseval
import Gtz.Wave.KTwoLeverageExcess

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The two axis readings, at every size -/

/-- **THE AXIS TOTAL.**  At an atom of unit leverage the weighted squared axis
readings of all atoms total one.  Parseval at the axis, twice. -/
theorem k2Axis_reading_total (D : WeightedDesign m 3) {x : Fin m}
    (hunit : leverageOf (D.atom x) = 1) :
    ∑ c, D.weight c * atomPairing D c x ^ 2 = 1 := by
  have h := parseval_bilinear D (D.atom x) (D.atom x)
  rw [dotProduct_self_eq_leverage, hunit] at h
  rw [← h]
  exact Finset.sum_congr rfl fun c _ => by rw [atomPairing]; try ring

/-- **THE MIXED TOTAL.**  Against a probe orthogonal to the axis, the weighted
products of the axis reading and the probe reading total zero. -/
theorem k2Axis_mixed_total_zero (D : WeightedDesign m 3) {x : Fin m}
    (u : Fin 3 → ℝ) (hu : D.atom x ⬝ᵥ u = 0) :
    ∑ c, D.weight c * (atomPairing D c x * (D.atom c ⬝ᵥ u)) = 0 := by
  have h := parseval_bilinear D (D.atom x) u
  rw [hu] at h
  rw [← h]
  exact Finset.sum_congr rfl fun c _ => by rw [atomPairing]; try ring

/-! ## 2. The normal form at `(5,3)` -/

/-- The axis reading of an atom, in the two-zero normal form: atom `0` is the
axis, `1` and `2` the plane pair, `3` and `4` the outside pair. -/
theorem k2FiveAxis_reading (D : WeightedDesign 5 3)
    (hunit : leverageOf (D.atom 0) = 1)
    (hy : atomPairing D 0 1 = 0) (hz : atomPairing D 0 2 = 0) :
    D.weight 0 + D.weight 3 * atomPairing D 3 0 ^ 2
        + D.weight 4 * atomPairing D 4 0 ^ 2 = 1 := by
  have h := k2Axis_reading_total D hunit
  rw [Fin.sum_univ_five] at h
  have h1 : atomPairing D 1 0 = 0 := by
    rw [atomPairing, dotProduct_comm]; exact hy
  have h2 : atomPairing D 2 0 = 0 := by
    rw [atomPairing, dotProduct_comm]; exact hz
  have h0 : atomPairing D 0 0 = 1 := by
    rw [atomPairing, dotProduct_self_eq_leverage]; exact hunit
  rw [h0, h1, h2] at h
  linarith [h]

/-- **THE EXCESS EQUATION OF THE CHART.**  The two outside leverage excesses,
weighted, total the two plane weights.  This is the chart hypothesis
`td*ed + te*ee = ty + tz` with `ed`, `ee` the squared axis readings less one. -/
theorem k2FiveAxis_excess_eq (D : WeightedDesign 5 3)
    (hunit : leverageOf (D.atom 0) = 1)
    (hy : atomPairing D 0 1 = 0) (hz : atomPairing D 0 2 = 0) :
    D.weight 3 * (atomPairing D 3 0 ^ 2 - 1)
        + D.weight 4 * (atomPairing D 4 0 ^ 2 - 1)
      = D.weight 1 + D.weight 2 := by
  have hread := k2FiveAxis_reading D hunit hy hz
  have hsum : D.weight 0 + D.weight 1 + D.weight 2 + D.weight 3 + D.weight 4 = 1 := by
    have h := D.weight_sum_one
    rw [Fin.sum_univ_five] at h
    linarith [h]
  linarith [hread, hsum]

/-- **THE BUDGET OF THE CHART.**  The four non-axis weights fall short of one,
because the axis weight is strictly positive. -/
theorem k2FiveAxis_budget (D : WeightedDesign 5 3) :
    D.weight 3 + D.weight 4 + D.weight 1 + D.weight 2 < 1 := by
  have hsum : D.weight 0 + D.weight 1 + D.weight 2 + D.weight 3 + D.weight 4 = 1 := by
    have h := D.weight_sum_one
    rw [Fin.sum_univ_five] at h
    linarith [h]
  have h0 := D.weight_pos 0
  linarith [hsum, h0]

/-! ## 3. The collinearity -/

/-- **THE OUTSIDE PLANE PARTS ARE COLLINEAR.**  Against every probe orthogonal
to the axis, the two outside atoms read in exact opposition, weighted by their
axis readings.  The plane parts therefore lie on one line, which is what makes
the two-zero chart eight-dimensional.

The plane atoms contribute nothing because they read the axis at zero, and the
axis contributes nothing because it reads the probe at zero. -/
theorem k2FiveAxis_collinear (D : WeightedDesign 5 3)
    (hunit : leverageOf (D.atom 0) = 1)
    (hy : atomPairing D 0 1 = 0) (hz : atomPairing D 0 2 = 0)
    (u : Fin 3 → ℝ) (hu : D.atom 0 ⬝ᵥ u = 0) :
    D.weight 3 * (atomPairing D 3 0 * (D.atom 3 ⬝ᵥ u))
        + D.weight 4 * (atomPairing D 4 0 * (D.atom 4 ⬝ᵥ u)) = 0 := by
  have h := k2Axis_mixed_total_zero D u hu
  rw [Fin.sum_univ_five] at h
  have h1 : atomPairing D 1 0 = 0 := by
    rw [atomPairing, dotProduct_comm]; exact hy
  have h2 : atomPairing D 2 0 = 0 := by
    rw [atomPairing, dotProduct_comm]; exact hz
  have h0 : atomPairing D 0 0 = 1 := by
    rw [atomPairing, dotProduct_self_eq_leverage]; exact hunit
  rw [h0, h1, h2, hu] at h
  linarith [h]

/-! ## 4. The plane pair alone resolves the transverse probe -/

/-- **THE PLANE PAIR RESOLVES THE TRANSVERSE PROBE.**  A probe orthogonal to
the axis at which the first outside atom also reads zero is read by the plane
pair alone: the second outside atom reads zero there too, by collinearity,
provided the first outside atom has a nonzero axis reading.

At a unit probe this says `t_y·(g_y·n)² + t_z·(g_z·n)² = 1`, so each summand
lies in the unit interval — the chart's plane angle needs no hypothesis. -/
theorem k2FiveAxis_planePair_reading (D : WeightedDesign 5 3)
    (hunit : leverageOf (D.atom 0) = 1)
    (hy : atomPairing D 0 1 = 0) (hz : atomPairing D 0 2 = 0)
    (u : Fin 3 → ℝ) (hu : D.atom 0 ⬝ᵥ u = 0)
    (hdu : D.atom 3 ⬝ᵥ u = 0) (hax : atomPairing D 4 0 ≠ 0) :
    D.weight 1 * (D.atom 1 ⬝ᵥ u) ^ 2 + D.weight 2 * (D.atom 2 ⬝ᵥ u) ^ 2
      = u ⬝ᵥ u := by
  have hcol := k2FiveAxis_collinear D hunit hy hz u hu
  rw [hdu] at hcol
  have heu : D.atom 4 ⬝ᵥ u = 0 := by
    have hw4 := D.weight_pos 4
    have : D.weight 4 * (atomPairing D 4 0 * (D.atom 4 ⬝ᵥ u)) = 0 := by linarith [hcol]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt hw4)
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hax
      · exact h'
  have h := parseval_bilinear D u u
  rw [Fin.sum_univ_five] at h
  rw [hu, hdu, heu] at h
  linarith [h]

end Gtz

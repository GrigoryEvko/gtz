import Gtz.Wave.ErasedEnergyLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The erased-witness Gram

The weight-gap determinant law carries two cross terms through the erased
atom: `(g_x×g_y)ᵀK(g_x×g_y)` and `(g_x×g_z)ᵀK(g_x×g_z)`.  This module
prices them in the witness data of the previous module.

The mechanism is the corner: `g_x` is a unit vector orthogonal to `g_y`
and to `g_z`, so `|g_x×g_y|² = |g_y|²` exactly, and the cross vector is a
unit-length rotation of `g_y` inside the plane orthogonal to `g_x`.  The
gap energy of that cross vector is therefore bounded by the outside gap's
extreme readings on the whole plane, which the trace of `K` controls.

* `Gtz.corner_cross_normSq` — `|g_x×g_y|² = |g_y|²` at the corner.
* `Gtz.corner_cross_energy_le_trace` — the cross energy is at most the
  positive part of `tr K` times `|g_y|²`, whenever `K + 1 = S_{Cᶜ}` is
  positive semidefinite (always).
* `Gtz.corner_inside_leverage_sum` — the two inside leverages total
  `2 + λ` at a `Z1`-proper corner with a unit erased atom.
* `Gtz.corner_bothLight_cross_terms_cap` — THE CROSS-TERM CAP: the two
  cross terms of the weight-gap law together obey

    `t_xt_y·(g_x×g_y)ᵀK(g_x×g_y) + t_xt_z·(g_x×g_z)ᵀK(g_x×g_z)
       ≤ t_x·max(t_y,t_z)·(2+λ)·(tr K)₊` ,

  a bound in weights, the corner scale, and one trace.  With the landed
  `λ`-cap and the erased-energy ledger, every term of the weight-gap law
  is now priced by weights, `tr K`, and `kxx`.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The cross norm at the corner -/

/-- **THE CORNER CROSS NORM.**  A unit erased atom orthogonal to an inside
atom gives the cross the inside atom's own length: `|g_x×g_y|² = |g_y|²`. -/
theorem corner_cross_normSq {gx gy : Fin 3 → ℝ}
    (hxunit : gx ⬝ᵥ gx = 1) (hxy0 : gx ⬝ᵥ gy = 0) :
    crossProduct gx gy ⬝ᵥ crossProduct gx gy = gy ⬝ᵥ gy := by
  rw [cross_dotProduct_self, hxunit, hxy0]
  ring

/-! ## 2. The trace caps every energy -/

/-- **THE TRACE CAP.**  A positive semidefinite form never reads more than
its trace times the squared probe length. -/
theorem posSemidef_energy_le_trace {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.PosSemidef) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (A *ᵥ v) ≤ Matrix.trace A * (v ⬝ᵥ v) :=
  form_le_trace_mul_normSq_of_posSemidef hA v

/-- **THE CROSS ENERGY CAP.**  At the corner the gap energy of the cross is
capped by the trace against the inside leverage: for positive semidefinite
`S`,

  `(g_x×g_y)ᵀ(S − 1)(g_x×g_y) ≤ (tr S − 1)·|g_y|²` .

The corner makes the cross exactly as long as the inside atom, and a
positive semidefinite form never reads more than its trace. -/
theorem corner_cross_energy_le_trace {S : Matrix (Fin 3) (Fin 3) ℝ}
    (hS : S.PosSemidef) {gx gy : Fin 3 → ℝ}
    (hxunit : gx ⬝ᵥ gx = 1) (hxy0 : gx ⬝ᵥ gy = 0) :
    crossProduct gx gy ⬝ᵥ ((S - 1) *ᵥ crossProduct gx gy)
      ≤ (Matrix.trace S - 1) * (gy ⬝ᵥ gy) := by
  have hcap := posSemidef_energy_le_trace hS (crossProduct gx gy)
  have hnorm := corner_cross_normSq hxunit hxy0
  have hsplit : crossProduct gx gy ⬝ᵥ ((S - 1) *ᵥ crossProduct gx gy)
      = crossProduct gx gy ⬝ᵥ (S *ᵥ crossProduct gx gy)
        - crossProduct gx gy ⬝ᵥ crossProduct gx gy := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
  rw [hsplit, hnorm]
  rw [hnorm] at hcap
  linarith [hcap]

/-! ## 3. The inside leverage total -/

/-- **THE INSIDE LEVERAGE TOTAL.**  At a corner with a unit erased atom the
two remaining inside leverages total `2 + λ`. -/
theorem corner_inside_leverage_sum {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1) :
    D.atom y ⬝ᵥ D.atom y + D.atom z ⬝ᵥ D.atom z = 2 + lam := by
  have htr := corner_trace_identity D hxy hxz hyz hunit hgap
  linarith [htr, hxunit]

/-! ## 4. The cross-term cap of the weight-gap law -/

/-- **THE CROSS-TERM CAP.**  The two cross terms of the weight-gap law are
together capped by the weights, the corner scale, and the outside trace:

  `t_xt_y·(g_x×g_y)ᵀK(g_x×g_y) + t_xt_z·(g_x×g_z)ᵀK(g_x×g_z)
     ≤ t_x·tin·(2+λ)·(tr S_{Cᶜ} − 1)` ,

with `tin` any bound of the two remaining inside weights.  Every quantity
on the right is weight data, the corner scale, and one trace: the cross
half of the roof is now priced. -/
theorem corner_bothLight_cross_terms_cap {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0)
    (htrace : 1 ≤ Matrix.trace (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)))
    {tin : ℝ} (hy : D.weight y ≤ tin) (hz : D.weight z ≤ tin) :
    D.weight x * D.weight y
        * (crossProduct (D.atom x) (D.atom y) ⬝ᵥ
          ((subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) - 1)
            *ᵥ crossProduct (D.atom x) (D.atom y)))
      + D.weight x * D.weight z
        * (crossProduct (D.atom x) (D.atom z) ⬝ᵥ
          ((subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) - 1)
            *ᵥ crossProduct (D.atom x) (D.atom z)))
      ≤ D.weight x * tin * (2 + lam)
        * (Matrix.trace (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)) - 1) := by
  classical
  set S : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) with hSDef
  have hSpsd : S.PosSemidef := by
    rw [hSDef, subsetSum]
    exact Matrix.posSemidef_sum _ (fun d _ => posSemidef_atomMatrix (D.atom d))
  have hcy := corner_cross_energy_le_trace hSpsd hxunit hxy0
  have hcz := corner_cross_energy_le_trace hSpsd hxunit hxz0
  have hlev := corner_inside_leverage_sum D hxy hxz hyz hunit hgap hxunit
  have hylev : 0 ≤ D.atom y ⬝ᵥ D.atom y := by
    rw [dotProduct_self_eq_sum_sq]; positivity
  have hzlev : 0 ≤ D.atom z ⬝ᵥ D.atom z := by
    rw [dotProduct_self_eq_sum_sq]; positivity
  have hxw := (D.weight_pos x).le
  have hyw := (D.weight_pos y).le
  have hzw := (D.weight_pos z).le
  have htr0 : 0 ≤ Matrix.trace S - 1 := by linarith [htrace]
  -- step one: each cross energy pays its own leverage
  have hstep1 : D.weight x * D.weight y
        * (crossProduct (D.atom x) (D.atom y) ⬝ᵥ ((S - 1)
          *ᵥ crossProduct (D.atom x) (D.atom y)))
      ≤ D.weight x * D.weight y
        * ((Matrix.trace S - 1) * (D.atom y ⬝ᵥ D.atom y)) :=
    mul_le_mul_of_nonneg_left hcy (mul_nonneg hxw hyw)
  have hstep2 : D.weight x * D.weight z
        * (crossProduct (D.atom x) (D.atom z) ⬝ᵥ ((S - 1)
          *ᵥ crossProduct (D.atom x) (D.atom z)))
      ≤ D.weight x * D.weight z
        * ((Matrix.trace S - 1) * (D.atom z ⬝ᵥ D.atom z)) :=
    mul_le_mul_of_nonneg_left hcz (mul_nonneg hxw hzw)
  -- step two: the inside weights go up to the cap
  have hstep3 : D.weight x * D.weight y
        * ((Matrix.trace S - 1) * (D.atom y ⬝ᵥ D.atom y))
      ≤ D.weight x * tin
        * ((Matrix.trace S - 1) * (D.atom y ⬝ᵥ D.atom y)) := by
    have hnn : 0 ≤ (Matrix.trace S - 1) * (D.atom y ⬝ᵥ D.atom y) :=
      mul_nonneg htr0 hylev
    nlinarith [mul_nonneg hxw (sub_nonneg.mpr hy), hnn, hxw]
  have hstep4 : D.weight x * D.weight z
        * ((Matrix.trace S - 1) * (D.atom z ⬝ᵥ D.atom z))
      ≤ D.weight x * tin
        * ((Matrix.trace S - 1) * (D.atom z ⬝ᵥ D.atom z)) := by
    have hnn : 0 ≤ (Matrix.trace S - 1) * (D.atom z ⬝ᵥ D.atom z) :=
      mul_nonneg htr0 hzlev
    nlinarith [mul_nonneg hxw (sub_nonneg.mpr hz), hnn, hxw]
  -- step three: the two leverages total the corner scale
  have hcombine : D.weight x * tin
        * ((Matrix.trace S - 1) * (D.atom y ⬝ᵥ D.atom y))
      + D.weight x * tin
        * ((Matrix.trace S - 1) * (D.atom z ⬝ᵥ D.atom z))
      = D.weight x * tin * (2 + lam) * (Matrix.trace S - 1) := by
    rw [← hlev]
    ring
  linarith [hstep1, hstep2, hstep3, hstep4, hcombine]

end Gtz

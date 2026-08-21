/-
# The plane frame, and the last chart positive

Two things finish the algebraic half of the chart-to-design bridge, and both are
in this module.

## 1. The determinant reading

`Gtz.KTwoBridgePositives` read three of the four chart positives off the plane
gap `B − 1` and left the fourth — the determinant — verified but untranscribed.
It is here (`Gtz.k2Plane_Dn_clear`), through two design-free laws:

* **the determinant law** (`Gtz.k2Plane_det_law`): for `c + d = 1` and
  `a c = b d`,

    `ty·tz·((1−ty)(1−tz) − (1−a−b)(d(1−tz) + c(1−ty)))
       = (a·tz + b·ty − ty·tz)(c·tz + d·ty − ty·tz) − a·c·(tz−ty)²` ;

* **the cross-square law** (`Gtz.k2Plane_cross_sq`): the second plane reading
  turns the squared plane pairing into the product of the two first-coordinate
  masses, `(ty·tz)²(y₁y₂+z₁z₂)² = (ty·y₁²)(ty·y₂²)(tz−ty)²`.

At `a = ty y₁²`, `b = tz z₁²`, `c = ty y₂²`, `d = tz z₂²` the two brackets on the
right of the determinant law are `ty·tz·(B₁₁−1)` and `ty·tz·(B₂₂−1)`, and the
correction is the off-diagonal square.  So all four chart positives are now the
plane gap, read at its two diagonal entries, its determinant, and the mass the
plane pair puts on the shared outside line.

## 2. The plane frame

Everything the bridge proves is stated in coordinates.  This module supplies
them, and they are not a construction but a READING.  Take any orthonormal pair
`v̂, n̂` spanning the axis's orthogonal complement with the FIRST aligned to the
outside line — that is, `g_d · n̂ = 0`.  Then the four relations the identities
consume are exactly four Parseval readings:

| relation | reading |
|---|---|
| `r1` | Parseval at `(v̂, v̂)` |
| `r2` | Parseval at `(v̂, n̂)` |
| `r3` | Parseval at `(n̂, n̂)` |
| `hcol` | the collinearity at `v̂` |

The axis drops out of all four because it is orthogonal to both probes, and the
two outside atoms drop out of `r2` and `r3` because both are orthogonal to `n̂`
— the second by collinearity (`Gtz.k2FivePlane_outside_nhat_zero`), which is
where the stratum's own structure is spent.

`Gtz.k2FivePlane_relations` packages all four.  With it, every coordinate
identity in this bridge becomes a statement about a design and a plane frame,
and the only thing left between here and the design-level `(5,3)` kill is
producing the frame — one normalisation of the outside plane part.
-/
import Gtz.Wave.KTwoBridgeDominates
import Gtz.Wave.KTwoBridgePositives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace Gtz

variable {m : ℕ}

/-! ## 1. Two design-free laws -/

/-- **THE DETERMINANT LAW.**  Two numbers summing to one and cross-multiplying
turn the plane's determinant reading into a product of two diagonal readings
less an off-diagonal square. -/
theorem k2Plane_det_law (a b c d ty tz : ℝ)
    (hcd : c + d = 1) (hac : a*c = b*d) :
    ty*tz*((1-ty)*(1-tz) - (1-a-b)*(d*(1-tz) + c*(1-ty)))
      = (a*tz + b*ty - ty*tz)*(c*tz + d*ty - ty*tz) - a*c*(tz-ty)^2 := by
  linear_combination (-ty*tz*(a*tz + b*ty - ty - tz + 1))*hcd
    + (-ty*(ty-tz)*(tz-1))*hac

/-- **THE CROSS-SQUARE LAW.**  The second plane reading converts the squared
plane pairing into the product of the two first-coordinate masses. -/
theorem k2Plane_cross_sq (y1 y2 z1 z2 ty tz : ℝ)
    (h2 : ty*(y1*y2) + tz*(z1*z2) = 0) :
    (ty*tz)^2*(y1*y2 + z1*z2)^2 = (ty*y1^2)*(ty*y2^2)*(tz-ty)^2 := by
  linear_combination (ty^2*(tz*(y1*y2 + z1*z2) + (y1*y2)*(tz-ty)))*h2

/-! ## 2. The determinant reading of the chart -/

/-- **THE LAST CHART POSITIVE IS THE DETERMINANT OF THE PLANE GAP.**  Cleared by
the two plane weights, so no division appears. -/
theorem k2Plane_Dn_clear (y1 y2 z1 z2 al be ty tz td te p v : ℝ)
    (h1 : ty*y1^2 + tz*z1^2 + td*p^2 + te*v^2 = 1)
    (h2 : ty*(y1*y2) + tz*(z1*z2) = 0)
    (h3 : ty*y2^2 + tz*z2^2 = 1)
    (hcol : td*al*p + te*be*v = 0) :
    ty*tz*(te*be^2*((1-ty)*(1-tz))
        - p^2*td*(td*al^2 + te*be^2)
          * ((1 - ty*y2^2)*(1-tz) + (ty*y2^2)*(1-ty)))
      = te*be^2*(ty*tz)^2
          * ((y1^2 + z1^2 - 1)*(y2^2 + z2^2 - 1) - (y1*y2 + z1*z2)^2) := by
  have hW := k2Plane_Wom_eq y1 z1 al be ty tz td te p v h1 hcol
  have hom : p^2*td*(td*al^2 + te*be^2)
      = te*be^2*(1 - (ty*y1^2 + tz*z1^2)) := by linarith [hW]
  have hac : (ty*y1^2)*(ty*y2^2) = (tz*z1^2)*(tz*z2^2) := by
    linear_combination (ty*(y1*y2) - tz*(z1*z2))*h2
  have hlaw := k2Plane_det_law (ty*y1^2) (tz*z1^2) (ty*y2^2) (tz*z2^2) ty tz h3 hac
  have hcs := k2Plane_cross_sq y1 y2 z1 z2 ty tz h2
  rw [hom]
  linear_combination (be^2*te)*hlaw + (be^2*te)*hcs
    + (be^2*te*ty^2*tz^2*y1^2 - be^2*te*ty^2*tz*y1^2 + be^2*te*ty*tz^3*z1^2
        - be^2*te*ty*tz^2*z1^2 - be^2*te*ty*tz^2 + be^2*te*ty*tz)*h3

/-! ## 3. The outside atoms are transverse to the second probe -/

/-- **BOTH OUTSIDE ATOMS ARE ORTHOGONAL TO THE SECOND PROBE.**  The first is by
the choice of frame, the second by the collinearity — provided it reads the axis
at all.  This is where the stratum's own structure enters the frame. -/
theorem k2FivePlane_outside_nhat_zero (D : WeightedDesign 5 3)
    (hunit : leverageOf (D.atom 0) = 1)
    (hy : atomPairing D 0 1 = 0) (hz : atomPairing D 0 2 = 0)
    (nh : Fin 3 → ℝ) (hn : D.atom 0 ⬝ᵥ nh = 0)
    (hdn : D.atom 3 ⬝ᵥ nh = 0) (hax : atomPairing D 4 0 ≠ 0) :
    D.atom 4 ⬝ᵥ nh = 0 := by
  have hcol := k2FiveAxis_collinear D hunit hy hz nh hn
  rw [hdn] at hcol
  have hw4 := D.weight_pos 4
  have hzero : D.weight 4 * (atomPairing D 4 0 * (D.atom 4 ⬝ᵥ nh)) = 0 := by
    linarith [hcol]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h (ne_of_gt hw4)
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hax
    · exact h'

/-! ## 4. The four relations, read off Parseval -/

/-- **THE FOUR BRIDGE RELATIONS ARE FOUR PARSEVAL READINGS.**  At an orthonormal
plane frame whose first probe carries the outside line, the three plane readings
of Parseval and the collinearity are exactly the relations every identity of
this bridge consumes.

The axis drops out of all four, being orthogonal to both probes; the two outside
atoms drop out of the last two, being orthogonal to the second probe. -/
theorem k2FivePlane_relations (D : WeightedDesign 5 3)
    (hunit : leverageOf (D.atom 0) = 1)
    (hy : atomPairing D 0 1 = 0) (hz : atomPairing D 0 2 = 0)
    (vh nh : Fin 3 → ℝ)
    (hvv : vh ⬝ᵥ vh = 1) (hnn : nh ⬝ᵥ nh = 1) (hvn : vh ⬝ᵥ nh = 0)
    (hv0 : D.atom 0 ⬝ᵥ vh = 0) (hn0 : D.atom 0 ⬝ᵥ nh = 0)
    (hdn : D.atom 3 ⬝ᵥ nh = 0) (hax : atomPairing D 4 0 ≠ 0) :
    D.weight 1 * (D.atom 1 ⬝ᵥ vh)^2 + D.weight 2 * (D.atom 2 ⬝ᵥ vh)^2
        + D.weight 3 * (D.atom 3 ⬝ᵥ vh)^2 + D.weight 4 * (D.atom 4 ⬝ᵥ vh)^2 = 1
      ∧ D.weight 1 * ((D.atom 1 ⬝ᵥ vh) * (D.atom 1 ⬝ᵥ nh))
          + D.weight 2 * ((D.atom 2 ⬝ᵥ vh) * (D.atom 2 ⬝ᵥ nh)) = 0
      ∧ D.weight 1 * (D.atom 1 ⬝ᵥ nh)^2
          + D.weight 2 * (D.atom 2 ⬝ᵥ nh)^2 = 1
      ∧ D.weight 3 * (atomPairing D 3 0 * (D.atom 3 ⬝ᵥ vh))
          + D.weight 4 * (atomPairing D 4 0 * (D.atom 4 ⬝ᵥ vh)) = 0 := by
  have hen := k2FivePlane_outside_nhat_zero D hunit hy hz nh hn0 hdn hax
  refine ⟨?_, ?_, ?_, k2FiveAxis_collinear D hunit hy hz vh hv0⟩
  · have h := parseval_bilinear D vh vh
    rw [Fin.sum_univ_five, hvv, hv0] at h
    have e : ∀ c : Fin 5, D.weight c * ((D.atom c ⬝ᵥ vh) * (D.atom c ⬝ᵥ vh))
        = D.weight c * (D.atom c ⬝ᵥ vh)^2 := fun c => by ring
    rw [e 1, e 2, e 3, e 4] at h
    linarith [h]
  · have h := parseval_bilinear D vh nh
    rw [Fin.sum_univ_five, hvn, hv0, hdn, hen] at h
    simp only [zero_mul, mul_zero, add_zero, zero_add] at h
    linarith [h]
  · have h := parseval_bilinear D nh nh
    rw [Fin.sum_univ_five, hnn, hn0, hdn, hen] at h
    have e : ∀ c : Fin 5, D.weight c * ((D.atom c ⬝ᵥ nh) * (D.atom c ⬝ᵥ nh))
        = D.weight c * (D.atom c ⬝ᵥ nh)^2 := fun c => by ring
    rw [e 1, e 2] at h
    linarith [h]

end Gtz

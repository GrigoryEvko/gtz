/-
# The two-at-cap(5) anchor: the certificate frame is nonvacuous, in-kernel

The audited exact anchor that every workflow's pipeline gate evaluates
(two-at-cap at leverage 5): atoms `u_A = (4/5, 3/5)`, `u_B = (4/5, −3/5)`,
`u_C = (−1, 0)` with weights `(1/9, 1/9, 7/9)`, moment `ξ = (3/8, 0)`, and
stress `λ = (7/36, 29/72, 29/72)` on the edges `AB, AC, BC`. Every layer of
the certificate frame holds at exact rationals:

* the planar design equations (weights sum, closure of the Bloch squares
  `S = ℓ·u`, trace 2);
* the focal conic `ν = 1/2 + ⟨ξ,u⟩` with `ℓ(1−ν) = 1` at each atom
  (`ν = 4/5, 4/5, 1/8`, `ℓ = 5, 5, 8/7`);
* tightness `(1+⟨u,u'⟩)/2 = ν·ν'` on all three edges;
* the stress mass `Σλ = 1` and the splitting rule
  `Σ_d λ_cd·β_d/(β_c+β_d) = t_c` at every atom (`β = ℓν = 4, 4, 1/7`).

A formalized certificate frame that this anchor did NOT satisfy would be
wrong; a guarded exclusion that killed it would over-exclude. Keeping the
witness in the kernel makes both failure modes impossible silently.
-/
import Mathlib

namespace Gtz

/-- The anchor is a planar design: weights sum to one, the weighted Bloch
squares `S = ℓ·u` close, and the weighted leverages trace to two. -/
theorem anchor_is_design :
    (1:ℝ)/9 + 1/9 + 7/9 = 1
      ∧ (1:ℝ)/9 * 4 + 1/9 * 4 + 7/9 * (-8/7) = 0
      ∧ (1:ℝ)/9 * 3 + 1/9 * (-3) + 7/9 * 0 = 0
      ∧ (1:ℝ)/9 * 5 + 1/9 * 5 + 7/9 * (8/7) = 2 := by
  norm_num

/-- The focal conic holds at each atom: `ν = 1/2 + ⟨ξ,u⟩` and `ℓ(1−ν) = 1`. -/
theorem anchor_conic :
    ((4:ℝ)/5 = 1/2 + (3/8 * (4/5) + 0 * (3/5))
        ∧ (5:ℝ) * (1 - 4/5) = 1)
      ∧ ((4:ℝ)/5 = 1/2 + (3/8 * (4/5) + 0 * (-3/5))
        ∧ (5:ℝ) * (1 - 4/5) = 1)
      ∧ ((1:ℝ)/8 = 1/2 + (3/8 * (-1) + 0 * 0)
        ∧ (8:ℝ)/7 * (1 - 1/8) = 1) := by
  norm_num

/-- All three edges are tight: `(1+⟨u,u'⟩)/2 = ν·ν'`. -/
theorem anchor_edges_tight :
    ((1 + ((4:ℝ)/5 * (4/5) + 3/5 * (-3/5))) / 2 = 4/5 * (4/5))
      ∧ ((1 + ((4:ℝ)/5 * (-1) + 3/5 * 0)) / 2 = 4/5 * (1/8))
      ∧ ((1 + ((4:ℝ)/5 * (-1) + (-3/5) * 0)) / 2 = 4/5 * (1/8)) := by
  norm_num

/-- The stress mass is pinned: `Σλ = 1`. -/
theorem anchor_stress_mass : (7:ℝ)/36 + 29/72 + 29/72 = 1 := by
  norm_num

/-- The splitting rule holds at every atom: `Σ_d λ_cd·β_d/(β_c+β_d) = t_c`
with `β = (4, 4, 1/7)`. -/
theorem anchor_splitting :
    ((7:ℝ)/36 * (4/(4+4)) + 29/72 * ((1/7)/(4+1/7)) = 1/9)
      ∧ ((7:ℝ)/36 * (4/(4+4)) + 29/72 * ((1/7)/(4+1/7)) = 1/9)
      ∧ ((29:ℝ)/72 * (4/(1/7+4)) + 29/72 * (4/(1/7+4)) = 7/9) := by
  norm_num

/-- The harmonic rule holds in its ordered-pair normalization (each edge
twice, matching the stress mass `Σλ = 2` ordered = `1` unordered):
`Σ_{c,d} λ_cd·β_cβ_d/(β_c+β_d) = 1`. -/
theorem anchor_harmonic :
    2 * ((7:ℝ)/36 * (4*4/(4+4))) + 2 * (29/72 * (4*(1/7)/(4+1/7)))
      + 2 * (29/72 * (4*(1/7)/(4+1/7))) = 1 := by
  norm_num

end Gtz

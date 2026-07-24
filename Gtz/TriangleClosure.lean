/-
# Triangle closure: the tight-walk QRT step is identically 3-torsion

The Poncelet-torsion wall's kill (workflow gtz3-poncelet-torsion, both
audits SOUND): on the focal-normalized GTZ biquadratic
`B(x, y) = L(x)·y² + 2xy + C(x)` with
`L(x) = −ρ²x² + ρ² + ρx² + 3x²/4 − 1/4` and
`C(x) = ρ²x² − ρ² − ρ − x²/4 + 3/4`, two tight edges meeting at an atom
with distinct far endpoints force the THIRD edge closed — the walk map
satisfies `W³ = id`. Every clone-free tight walk closes after exactly
three steps: 2-regular tight components are triangles, and no cycle of
length `k ≥ 4` (in particular no deep full-stress cycle, single `C_k`
with `k ≥ 12` or unions of `≥ 11`-cycles) exists, over ANY field. With
`tight_partners_le_two` this makes `cyclic_stress_vanishes_of_open`
unconditional for every `k ≠ 3`; the zero-set classification's deep-cycle
stratum is vacuous.

Proof shape: `qrt_step_deterministic` (the kernel QRT step, SS120) gives
the Vieta sum `L(x₂)·(x₁ + x₃) = −2x₂`; a division-free `L(x₂)²`-cleared
polynomial certificate (checked by `linear_combination`) then closes
`B(x₃, x₁) = 0`. The pole guard `L(x₂) ≠ 0` is carried as an explicit
hypothesis — at a pole the partner is the antipode, which the feasibility
layer excludes separately.
-/
import Mathlib
import Gtz.Basic
import Gtz.FrameEncoding

set_option maxHeartbeats 4000000

namespace Gtz

/-- **Triangle closure (W³ = id) over the GTZ biquadratic.**
Two tight edges meeting at atom `x2` (the quadratics `L2·t² + 2·x2·t + C2 = 0`
at `t = x1` and `t = x3`) with distinct far endpoints (`x1 ≠ x3`, clone-free)
force the THIRD edge `B(x3, x1) = 0`. So every clone-free tight walk closes
after exactly three steps: the tight graph's 2-regular components are
triangles, and no cycle of length `k ≥ 4` (in particular no deep full-stress
cycle) exists. -/
theorem triangle_closure_biquadratic (rho x1 x2 x3 : ℝ)
    (hL2 : (-rho^2*x2^2 + rho^2 + rho*x2^2 + 3*x2^2/4 - 1/4) ≠ 0)
    (hB21 : (-rho^2*x2^2 + rho^2 + rho*x2^2 + 3*x2^2/4 - 1/4) * x1 ^ 2
        + 2 * x2 * x1 + (rho^2*x2^2 - rho^2 - rho - x2^2/4 + 3/4) = 0)
    (hB23 : (-rho^2*x2^2 + rho^2 + rho*x2^2 + 3*x2^2/4 - 1/4) * x3 ^ 2
        + 2 * x2 * x3 + (rho^2*x2^2 - rho^2 - rho - x2^2/4 + 3/4) = 0)
    (hne : x1 ≠ x3) :
    (-rho^2*x1^2 + rho^2 + rho*x1^2 + 3*x1^2/4 - 1/4) * x3 ^ 2
      + 2 * x1 * x3 + (rho^2*x1^2 - rho^2 - rho - x1^2/4 + 3/4) = 0 := by
  -- Vieta sum for the two partners of x2, from the kernel QRT-step theorem.
  have hsum : (-rho^2*x2^2 + rho^2 + rho*x2^2 + 3*x2^2/4 - 1/4) * (x1 + x3)
      = -(2 * x2) :=
    (qrt_step_deterministic hB21 hB23 hne).1
  -- The L2²-cleared closure certificate (division-free, ring-checked).
  have hL2sq : ((-rho^2*x2^2 + rho^2 + rho*x2^2 + 3*x2^2/4 - 1/4) ^ 2 : ℝ)
      ≠ 0 := pow_ne_zero 2 hL2
  have key : ((-rho^2*x2^2 + rho^2 + rho*x2^2 + 3*x2^2/4 - 1/4) ^ 2)
      * ((-rho^2*x1^2 + rho^2 + rho*x1^2 + 3*x1^2/4 - 1/4) * x3 ^ 2
        + 2 * x1 * x3 + (rho^2*x1^2 - rho^2 - rho - x1^2/4 + 3/4)) = 0 := by
    linear_combination (-rho^4*x1^3*x2^2 + rho^4*x1^3 + rho^4*x1^2*x2^2*x3 - rho^4*x1^2*x3 + rho^4*x1*x2^2 - rho^4*x1 - rho^4*x2^2*x3 + rho^4*x3 + 2*rho^3*x1^3*x2^2 - rho^3*x1^3 - 2*rho^3*x1^2*x2^2*x3 + rho^3*x1^2*x3 - rho^3*x1*x2^2 + rho^3*x2^2*x3 + rho^2*x1^3*x2^2/2 - rho^2*x1^3 - rho^2*x1^2*x2^2*x3/2 + 2*rho^2*x1^2*x2 + rho^2*x1^2*x3 - 3*rho^2*x1*x2^2 + 5*rho^2*x1/2 + rho^2*x2^2*x3 - 2*rho^2*x2 - rho^2*x3/2 - 3*rho*x1^3*x2^2/2 + rho*x1^3/4 + 3*rho*x1^2*x2^2*x3/2 - 2*rho*x1^2*x2 - rho*x1^2*x3/4 + 9*rho*x1*x2^2/4 - rho*x2^2*x3/4 - 9*x1^3*x2^2/16 + 3*x1^3/16 + 9*x1^2*x2^2*x3/16 - 3*x1^2*x2/2 - 3*x1^2*x3/16 + 27*x1*x2^2/16 - 9*x1/16 - 3*x2^2*x3/16 + x2/2 + x3/16) * hsum + (rho^4*x1^2*x2^2 - rho^4*x1^2 - rho^4*x2^2 + rho^4 - 2*rho^3*x1^2*x2^2 + rho^3*x1^2 + rho^3*x2^2 - rho^2*x1^2*x2^2/2 + rho^2*x1^2 - 2*rho^2*x1*x2 + 3*rho^2*x2^2 - rho^2/2 + 3*rho*x1^2*x2^2/2 - rho*x1^2/4 + 2*rho*x1*x2 - 9*rho*x2^2/4 + 9*x1^2*x2^2/16 - 3*x1^2/16 + 3*x1*x2/2 - 27*x2^2/16 + 1/16) * hB21
  exact (mul_eq_zero.mp key).resolve_left hL2sq

end Gtz

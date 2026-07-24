/-
# The P4 exclusion certificate: the guarded variety is empty, kernel-checked

The Nullstellensatz cofactors extracted by the cofactor workflow
(Groebner.jl change matrix over ℚ, residual verified EXACTLY 0 in two
independent audit stacks sharing no code), consumed as one
`linear_combination`. Twelve hypotheses over twelve real unknowns — the
TRIMMED geometric form: four Pythagoras rows, the three tight edges of the
path P4 on the focal conic (gauge ξ = (r,0)), the two stress-leaf rows, and
three clone Rabinowitsch guards. NO stress system, NO closure, NO λ: the
certificate is the algebraic double-leaf-tangency argument, 516 cofactor
terms, degree ≤ 9, coefficients ≤ 6 bits.

With the FrameEncoding bridge ("equality design ⟹ variety point") this is
the kernel half of: **no full-support asymmetric P4 equality design exists**.
Variable names match the published Appendix-A system verbatim — the audits
anchored every coefficient against the artifact text, and renaming would
break that auditability.

The companion `leaf_corner_certificate` is the 15-term pole/nondegeneracy
kill at the leaf corner.
-/
import Mathlib

namespace Gtz

set_option maxHeartbeats 3200000 in
theorem p4_geometric_certificate_variety_empty
    (c1 s1 c2 s2 c3 s3 c4 s4 r w2 w4 w5 : ℝ)
    (h1 : c1^2 + s1^2 - 1 = 0)
    (h2 : c2^2 + s2^2 - 1 = 0)
    (h3 : c3^2 + s3^2 - 1 = 0)
    (h4 : c4^2 + s4^2 - 1 = 0)
    (h5 : -4*c1*c2*r^2 + 2*c1*c2 - 2*c1*r + 2*s1*s2 - 2*c2*r + 1 = 0)
    (h6 : -4*c2*c3*r^2 + 2*c2*c3 - 2*c2*r + 2*s2*s3 - 2*c3*r + 1 = 0)
    (h7 : -4*c3*c4*r^2 + 2*c3*c4 - 2*c3*r + 2*s3*s4 - 2*c4*r + 1 = 0)
    (h8 : c1*s2 + 2*s1*c2*r^2 - s1*c2 + s1*r = 0)
    (h9 : 2*c3*s4*r^2 - c3*s4 + s3*c4 + s4*r = 0)
    (h10 : c1^2*w2 - 2*c1*c3*w2 + s1^2*w2 - 2*s1*s3*w2 + c3^2*w2 + s3^2*w2 - 1 = 0)
    (h11 : c2^2*w4 - 2*c2*c3*w4 + s2^2*w4 - 2*s2*s3*w4 + c3^2*w4 + s3^2*w4 - 1 = 0)
    (h12 : c2^2*w5 - 2*c2*c4*w5 + s2^2*w5 - 2*s2*s4*w5 + c4^2*w5 + s4^2*w5 - 1 = 0)
    : False := by
  have oneEqZero : (1 : ℝ) = 0 := by
    linear_combination
      (8*c1*s2^2*c3*r^2*w2^2*w4 + 4*s1*s2*c3*r*w2^2 + c2*s2*s4*r*w2*w5 + 2*s2^2*c3*c4*r^2*w2*w4 - 4*s2^2*c3*c4*w2*w4 - 2*s2^2*c3*s4^2*r*w2*w4*w5 - 2*s2^2*c3*r*w2*w4 + 8*s2^2*c4*r*w2*w4 - s2^2*c4*r*w2*w5 - 8*s2^2*r^2*w2^2*w4 + 6*s2^2*r^2*w2*w4 - 2*s2^2*r^2*w2*w5 + s2*c4*s4*r*w2*w5 + 4*s2*s4*r^2*w2*w5 - s2*s4*r^2*w2 + c3*r*w2 + 2*r^2*w2) * h1 +
      (-4*c1*c2*c3^2*r^2*w2*w4 - 4*c1*c2*s3^2*r^2*w2*w5 + 16*c1*s2*c3*s3*r^2*w2*w4*w5 + 4*c1*s2*c3*s3*r^2*w2*w4 - 4*c1*s2*c3*s3*r^2*w2*w5 + 4*c1*s2*s3*r*w2*w5 - 8*c1*c3*s3^2*r^2*w2*w4*w5 - 8*c1*c3*s3^2*r^2*w2*w4 + 4*c1*c3*r^2*w2*w4 + 2*c1*s3^2*r*w2*w5 - 2*s1*c3*s3*r*w2*w5 - 4*s1*s3*r^2*w2*w5 - c2*c3^2*c4*r^2*w4 + 2*c2*c3^2*c4*w4 + c2*c3^2*s4^2*r*w4*w5 + c2*c3^2*r*w4 - 4*c2*c3*c4*r*w4 + 4*c2*c3*r^2*w2*w4 - 3*c2*c3*r^2*w4 - c2*s3^2*c4*r^2*w5 + 2*c2*s3^2*c4*w5 + c2*s3^2*s4^2*r*w5^2 + c2*s3^2*r*w5 + 4*c2*s3*c4*s4*w5 + 3*c2*s3*s4*r*w5 + 1/2*c2*c4^2*r*w5 + c2*c4*r^2*w5 + 1/2*c2*s4^2*r*w5 + 4*s2*c3*s3*c4*r^2*w4*w5 + s2*c3*s3*c4*r^2*w4 - s2*c3*s3*c4*r^2*w5 - 8*s2*c3*s3*c4*w4*w5 - 2*s2*c3*s3*c4*w4 + 2*s2*c3*s3*c4*w5 - 4*s2*c3*s3*s4^2*r*w4*w5^2 - s2*c3*s3*s4^2*r*w4*w5 + s2*c3*s3*s4^2*r*w5^2 - 4*s2*c3*s3*r*w4*w5 - s2*c3*s3*r*w4 + s2*c3*s3*r*w5 - 4*s2*s3*c4^2*w5 + 16*s2*s3*c4*r*w4*w5 + 4*s2*s3*c4*r*w4 - 7*s2*s3*c4*r*w5 - 16*s2*s3*r^2*w2*w4*w5 - 4*s2*s3*r^2*w2*w4 + 4*s2*s3*r^2*w2*w5 + 12*s2*s3*r^2*w4*w5 + 3*s2*s3*r^2*w4 - 3*s2*s3*r^2*w5 - s2*s4*r^2*w5 - 2*c3*s3^2*c4*r^2*w4*w5 - 2*c3*s3^2*c4*r^2*w4 + 4*c3*s3^2*c4*w4*w5 + 4*c3*s3^2*c4*w4 + 2*c3*s3^2*s4^2*r*w4*w5^2 + 2*c3*s3^2*s4^2*r*w4*w5 + 2*c3*s3^2*r*w4*w5 + 2*c3*s3^2*r*w4 + c3*c4*r^2*w4 - 2*c3*c4*w4 - c3*s4^2*r*w4*w5 - c3*r*w4 - 8*s3^2*c4*r*w4*w5 - 8*s3^2*c4*r*w4 + 8*s3^2*r^2*w2*w4*w5 + 8*s3^2*r^2*w2*w4 - 6*s3^2*r^2*w4*w5 - 6*s3^2*r^2*w4 - s3*c4*s4*r*w5^2 - 2*s3*s4*r^2*w5^2 - 2*s3*s4*w5 + 4*c4*r*w4 - 1/2*c4*r*w5 + 2*s4^2*r^2*w5 - 4*r^2*w2*w4 + 3*r^2*w4 - r^2*w5) * h2 +
      (8*c1*c2^2*c3*r^2*w2*w4 - 4*c1*c2*c3^2*r^2*w2*w4 + 4*c1*c2*r^2*w2 - 8*c1*s2^2*c3*r^2*w2^2*w4 + 4*c1*s2*c3*s3*r^2*w2*w4 - 4*c1*c3*r^2*w2*w4 - 2*c1*r*w2 - 4*s1*s2*c3*r*w2^2 + 2*c2^2*c3*c4*r^2*w4 - 4*c2^2*c3*c4*w4 - 2*c2^2*c3*s4^2*r*w4*w5 - 2*c2^2*c3*r*w4 + 8*c2^2*c4*r*w4 - 8*c2^2*r^2*w2*w4 + 6*c2^2*r^2*w4 - c2*s2*s4*r*w2*w5 - c2*c3^2*c4*r^2*w4 + 2*c2*c3^2*c4*w4 + c2*c3^2*s4^2*r*w4*w5 + c2*c3^2*r*w4 - 4*c2*c3*c4*r*w4 + 4*c2*c3*r^2*w2*w4 - 3*c2*c3*r^2*w4 + c2*c4*r^2 - 2*c2*c4 - c2*s4^2*r*w5 - c2*r - 2*s2^2*c3*c4*r^2*w2*w4 + 4*s2^2*c3*c4*w2*w4 + 2*s2^2*c3*s4^2*r*w2*w4*w5 + 2*s2^2*c3*r*w2*w4 - 8*s2^2*c4*r*w2*w4 + s2^2*c4*r*w2*w5 + 8*s2^2*r^2*w2^2*w4 - 6*s2^2*r^2*w2*w4 + 2*s2^2*r^2*w2*w5 + s2*c3*s3*c4*r^2*w4 - 2*s2*c3*s3*c4*w4 - s2*c3*s3*s4^2*r*w4*w5 - s2*c3*s3*r*w4 + 4*s2*s3*c4*r*w4 - 4*s2*s3*r^2*w2*w4 + 3*s2*s3*r^2*w4 - s2*c4*s4*r*w2*w5 - 4*s2*s4*r^2*w2*w5 + s2*s4*r^2*w2 - c3*c4*r^2*w4 + 2*c3*c4*w4 + c3*s4^2*r*w4*w5 + c3*r*w2 + c3*r*w4 - 4*c4*r*w4 + 4*r^2*w2*w4 + 2*r^2*w2 - 3*r^2*w4) * h3 +
      (4*c1*c2*s3^2*r^2*w2*w5 - 16*c1*s2*c3*s3*r^2*w2*w4*w5 + 4*c1*s2*c3*s3*r^2*w2*w5 - 4*c1*s2*s3*r*w2*w5 + 8*c1*c3*s3^2*r^2*w2*w4*w5 - 2*c1*s3^2*r*w2*w5 + 2*s1*c3*s3*r*w2*w5 + 4*s1*s3*r^2*w2*w5 - c2^2*c4*r*w5 - 2*c2^2*r^2*w5 - c2*s2*s4*r*w5 + c2*s3^2*c4*r^2*w5 - 2*c2*s3^2*c4*w5 - c2*s3^2*s4^2*r*w5^2 - c2*s3^2*r*w5 - 4*c2*s3*c4*s4*w5 - 3*c2*s3*s4*r*w5 + 1/2*c2*c4^2*r*w5 + c2*c4*r^2*w5 + 1/2*c2*s4^2*r*w5 - 1/2*c2*r - 4*s2*c3*s3*c4*r^2*w4*w5 + s2*c3*s3*c4*r^2*w5 + 8*s2*c3*s3*c4*w4*w5 - 2*s2*c3*s3*c4*w5 + 4*s2*c3*s3*s4^2*r*w4*w5^2 - s2*c3*s3*s4^2*r*w5^2 + 4*s2*c3*s3*r*w4*w5 - s2*c3*s3*r*w5 + 4*s2*s3*c4^2*w5 - 16*s2*s3*c4*r*w4*w5 + 7*s2*s3*c4*r*w5 + 16*s2*s3*r^2*w2*w4*w5 - 4*s2*s3*r^2*w2*w5 - 12*s2*s3*r^2*w4*w5 + 3*s2*s3*r^2*w5 - s2*s4*r^2*w5 + 2*c3*s3^2*c4*r^2*w4*w5 - 4*c3*s3^2*c4*w4*w5 - 2*c3*s3^2*s4^2*r*w4*w5^2 - 2*c3*s3^2*r*w4*w5 - 8*c3*c4*r^2 + 4*c3*c4 + 8*s3^2*c4*r*w4*w5 - 8*s3^2*r^2*w2*w4*w5 + 6*s3^2*r^2*w4*w5 + s3*c4*s4*r*w5^2 + 2*s3*s4*r^2*w5^2 - 2*s3*s4*r^2*w5 + 2*s3*s4*w5 + 1/2*c4*r*w5 - 4*c4*r + r^2*w5) * h4 +
      (-8*c1*s1*s2*c3*r^2*w2^2*w4 - 4*s1^2*c3*r*w2^2 - s1*c2*s4*r*w2*w5 - 2*s1*s2*c3*c4*r^2*w2*w4 + 4*s1*s2*c3*c4*w2*w4 + 2*s1*s2*c3*s4^2*r*w2*w4*w5 + 2*s1*s2*c3*r*w2*w4 - 8*s1*s2*c4*r*w2*w4 + s1*s2*c4*r*w2*w5 + 8*s1*s2*r^2*w2^2*w4 - 6*s1*s2*r^2*w2*w4 + 2*s1*s2*r^2*w2*w5 - s1*c4*s4*r*w2*w5 - 4*s1*s4*r^2*w2*w5 + s1*s4*r^2*w2 + 2*c3*r*w2) * h5 +
      (8*c1*s1*s2*c3*r^2*w2^2*w4 + 4*c1*c2*s3*s4*r^2*w2*w5 - 16*c1*s2*c3*s4*r^2*w2*w4*w5 + 4*c1*s2*c3*s4*r^2*w2*w5 - 4*c1*s2*s4*r*w2*w5 + 8*c1*c3*s3*s4*r^2*w2*w4*w5 - 2*c1*s3*s4*r*w2*w5 - 2*c1*r*w2 + 4*s1^2*c3*r*w2^2 + s1*c2*s4*r*w2*w5 + 2*s1*s2*c3*c4*r^2*w2*w4 - 4*s1*s2*c3*c4*w2*w4 - 2*s1*s2*c3*s4^2*r*w2*w4*w5 - 2*s1*s2*c3*r*w2*w4 + 8*s1*s2*c4*r*w2*w4 - s1*s2*c4*r*w2*w5 - 8*s1*s2*r^2*w2^2*w4 + 6*s1*s2*r^2*w2*w4 - 2*s1*s2*r^2*w2*w5 + 2*s1*c3*s4*r*w2*w5 + s1*c4*s4*r*w2*w5 + 8*s1*s4*r^2*w2*w5 - s1*s4*r^2*w2 + c2*s3*c4*s4*r^2*w5 - 2*c2*s3*c4*s4*w5 - c2*s3*s4^3*r*w5^2 - c2*s3*s4*r*w5 - 4*c2*c4*s4^2*w5 - 3*c2*s4^2*r*w5 - 4*s2*c3*c4*s4*r^2*w4*w5 + s2*c3*c4*s4*r^2*w5 + 8*s2*c3*c4*s4*w4*w5 - 2*s2*c3*c4*s4*w5 + 4*s2*c3*s4^3*r*w4*w5^2 - s2*c3*s4^3*r*w5^2 + 4*s2*c3*s4*r*w4*w5 - s2*c3*s4*r*w5 + 4*s2*c4^2*s4*w5 - 16*s2*c4*s4*r*w4*w5 + 7*s2*c4*s4*r*w5 + 16*s2*s4*r^2*w2*w4*w5 - 4*s2*s4*r^2*w2*w5 - 12*s2*s4*r^2*w4*w5 + 3*s2*s4*r^2*w5 + 2*c3*s3*c4*s4*r^2*w4*w5 - 4*c3*s3*c4*s4*w4*w5 - 2*c3*s3*s4^3*r*w4*w5^2 - 2*c3*s3*s4*r*w4*w5 + 8*s3*c4*s4*r*w4*w5 - 8*s3*s4*r^2*w2*w4*w5 + 6*s3*s4*r^2*w4*w5 + 2*c4^2 + c4*s4^2*r*w5^2 + 3/2*c4*r + 2*s4^2*r^2*w5^2 + 2*s4^2*w5) * h6 +
      (-4*c1*c2*s3*s4*r^2*w2*w5 + 16*c1*s2*c3*s4*r^2*w2*w4*w5 - 4*c1*s2*c3*s4*r^2*w2*w5 + 4*c1*s2*s4*r*w2*w5 - 8*c1*c3*s3*s4*r^2*w2*w4*w5 + 2*c1*s3*s4*r*w2*w5 - 2*s1*c3*s4*r*w2*w5 - 4*s1*s4*r^2*w2*w5 - c2*s3*c4*s4*r^2*w5 + 2*c2*s3*c4*s4*w5 + c2*s3*s4^3*r*w5^2 + c2*s3*s4*r*w5 + 4*c2*c4*s4^2*w5 - 2*c2*c4 + 3*c2*s4^2*r*w5 - 3/2*c2*r + 4*s2*c3*c4*s4*r^2*w4*w5 - s2*c3*c4*s4*r^2*w5 - 8*s2*c3*c4*s4*w4*w5 + 2*s2*c3*c4*s4*w5 - 4*s2*c3*s4^3*r*w4*w5^2 + s2*c3*s4^3*r*w5^2 - 4*s2*c3*s4*r*w4*w5 + s2*c3*s4*r*w5 - 4*s2*c4^2*s4*w5 + 16*s2*c4*s4*r*w4*w5 - 7*s2*c4*s4*r*w5 - 16*s2*s4*r^2*w2*w4*w5 + 4*s2*s4*r^2*w2*w5 + 12*s2*s4*r^2*w4*w5 - 3*s2*s4*r^2*w5 - 2*c3*s3*c4*s4*r^2*w4*w5 + 4*c3*s3*c4*s4*w4*w5 + 2*c3*s3*s4^3*r*w4*w5^2 + 2*c3*s3*s4*r*w4*w5 - 8*s3*c4*s4*r*w4*w5 + 8*s3*s4*r^2*w2*w4*w5 - 6*s3*s4*r^2*w4*w5 - 2*c4^2 - c4*s4^2*r*w5^2 - 2*s4^2*r^2*w5^2 + s4^2*r^2*w5 - 2*s4^2*w5 + 1) * h7 +
      (-16*c1^2*s2*c3*r^2*w2^2*w4 - 8*c1*s1*c3*r*w2^2 - 2*c1*c2*s4*r*w2*w5 + 16*c1*s2*c3^2*r^2*w2^2*w4 - 4*c1*s2*c3*c4*r^2*w2*w4 + 8*c1*s2*c3*c4*w2*w4 + 4*c1*s2*c3*s4^2*r*w2*w4*w5 + 4*c1*s2*c3*r*w2*w4 - 16*c1*s2*c4*r*w2*w4 + 2*c1*s2*c4*r*w2*w5 + 16*c1*s2*r^2*w2^2*w4 - 12*c1*s2*r^2*w2*w4 + 4*c1*s2*r^2*w2*w5 - 2*c1*c4*s4*r*w2*w5 - 8*c1*s4*r^2*w2*w5 + 2*c1*s4*r^2*w2 + 8*s1*c3^2*r*w2^2 + 2*c2*c3*s4*r*w2*w5 + 4*s2*c3^2*c4*r^2*w2*w4 - 8*s2*c3^2*c4*w2*w4 - 4*s2*c3^2*s4^2*r*w2*w4*w5 - 4*s2*c3^2*r*w2*w4 + 16*s2*c3*c4*r*w2*w4 - 2*s2*c3*c4*r*w2*w5 - 16*s2*c3*r^2*w2^2*w4 + 12*s2*c3*r^2*w2*w4 - 4*s2*c3*r^2*w2*w5 + 2*c3*c4*s4*r*w2*w5 + 8*c3*s4*r^2*w2*w5 - 2*c3*s4*r^2*w2) * h8 +
      (8*c1*c2^2*s3*r^2*w2*w5 - 32*c1*c2*s2*c3*r^2*w2*w4*w5 + 8*c1*c2*s2*c3*r^2*w2*w5 - 8*c1*c2*s2*r*w2*w5 + 16*c1*c2*c3*s3*r^2*w2*w4*w5 - 8*c1*c2*s3*c4*r^2*w2*w5 - 4*c1*c2*s3*r*w2*w5 + 32*c1*s2*c3*c4*r^2*w2*w4*w5 - 8*c1*s2*c3*c4*r^2*w2*w5 + 8*c1*s2*c4*r*w2*w5 - 16*c1*c3*s3*c4*r^2*w2*w4*w5 + 4*c1*s3*c4*r*w2*w5 + 4*s1*c2*c3*r*w2*w5 + 8*s1*c2*r^2*w2*w5 - 4*s1*c3*c4*r*w2*w5 - 8*s1*c4*r^2*w2*w5 + 2*c2^2*s3*c4*r^2*w5 - 4*c2^2*s3*c4*w5 - 2*c2^2*s3*s4^2*r*w5^2 - 2*c2^2*s3*r*w5 - 8*c2^2*c4*s4*w5 - 6*c2^2*s4*r*w5 - 8*c2*s2*c3*c4*r^2*w4*w5 + 2*c2*s2*c3*c4*r^2*w5 + 16*c2*s2*c3*c4*w4*w5 - 4*c2*s2*c3*c4*w5 + 8*c2*s2*c3*s4^2*r*w4*w5^2 - 2*c2*s2*c3*s4^2*r*w5^2 + 8*c2*s2*c3*r*w4*w5 - 2*c2*s2*c3*r*w5 + 8*c2*s2*c4^2*w5 - 32*c2*s2*c4*r*w4*w5 + 14*c2*s2*c4*r*w5 + 32*c2*s2*r^2*w2*w4*w5 - 8*c2*s2*r^2*w2*w5 - 24*c2*s2*r^2*w4*w5 + 6*c2*s2*r^2*w5 + 4*c2*c3*s3*c4*r^2*w4*w5 - 8*c2*c3*s3*c4*w4*w5 - 4*c2*c3*s3*s4^2*r*w4*w5^2 - 4*c2*c3*s3*r*w4*w5 - 2*c2*s3*c4^2*r^2*w5 + 4*c2*s3*c4^2*w5 + 2*c2*s3*c4*s4^2*r*w5^2 + 16*c2*s3*c4*r*w4*w5 + 2*c2*s3*c4*r*w5 - 16*c2*s3*r^2*w2*w4*w5 + 12*c2*s3*r^2*w4*w5 + 8*c2*c4^2*s4*w5 + 2*c2*c4*s4*r*w5^2 + 6*c2*c4*s4*r*w5 + 4*c2*s4*r^2*w5^2 + 4*c2*s4*w5 + 8*s2*c3*c4^2*r^2*w4*w5 - 2*s2*c3*c4^2*r^2*w5 - 16*s2*c3*c4^2*w4*w5 + 4*s2*c3*c4^2*w5 - 8*s2*c3*c4*s4^2*r*w4*w5^2 + 2*s2*c3*c4*s4^2*r*w5^2 - 8*s2*c3*c4*r*w4*w5 + 2*s2*c3*c4*r*w5 - 8*s2*c4^3*w5 + 32*s2*c4^2*r*w4*w5 - 14*s2*c4^2*r*w5 - 32*s2*c4*r^2*w2*w4*w5 + 8*s2*c4*r^2*w2*w5 + 24*s2*c4*r^2*w4*w5 - 6*s2*c4*r^2*w5 - 4*c3*s3*c4^2*r^2*w4*w5 + 8*c3*s3*c4^2*w4*w5 + 4*c3*s3*c4*s4^2*r*w4*w5^2 + 4*c3*s3*c4*r*w4*w5 - 16*s3*c4^2*r*w4*w5 + 16*s3*c4*r^2*w2*w4*w5 - 12*s3*c4*r^2*w4*w5 - 2*c4^2*s4*r*w5^2 - 4*c4*s4*r^2*w5^2 + 2*c4*s4*r^2*w5 - 4*c4*s4*w5 + 4*c4*s4 + s4*r*w5) * h9 +
      (8*c1*s2^2*c3*r^2*w2*w4 + 4*s1*s2*c3*r*w2 + c2*s2*s4*r*w5 + 2*s2^2*c3*c4*r^2*w4 - 4*s2^2*c3*c4*w4 - 2*s2^2*c3*s4^2*r*w4*w5 - 2*s2^2*c3*r*w4 + 8*s2^2*c4*r*w4 - s2^2*c4*r*w5 - 8*s2^2*r^2*w2*w4 + 6*s2^2*r^2*w4 - 2*s2^2*r^2*w5 + s2*c4*s4*r*w5 + 4*s2*s4*r^2*w5 - s2*s4*r^2 - c3*r - 2*r^2) * h10 +
      (4*c1*c2*c3^2*r^2*w2 - 4*c1*s2*c3*s3*r^2*w2 + 4*c1*c3*r^2*w2 + c2*c3^2*c4*r^2 - 2*c2*c3^2*c4 - c2*c3^2*s4^2*r*w5 - c2*c3^2*r + 4*c2*c3*c4*r - 4*c2*c3*r^2*w2 + 3*c2*c3*r^2 - s2*c3*s3*c4*r^2 + 2*s2*c3*s3*c4 + s2*c3*s3*s4^2*r*w5 + s2*c3*s3*r - 4*s2*s3*c4*r + 4*s2*s3*r^2*w2 - 3*s2*s3*r^2 + c3*c4*r^2 - 2*c3*c4 - c3*s4^2*r*w5 - c3*r + 4*c4*r - 4*r^2*w2 + 3*r^2) * h11 +
      (4*c1*c2*s3^2*r^2*w2 - 16*c1*s2*c3*s3*r^2*w2*w4 + 4*c1*s2*c3*s3*r^2*w2 - 4*c1*s2*s3*r*w2 + 8*c1*c3*s3^2*r^2*w2*w4 - 2*c1*s3^2*r*w2 + 2*s1*c3*s3*r*w2 + 4*s1*s3*r^2*w2 + c2*s3^2*c4*r^2 - 2*c2*s3^2*c4 - c2*s3^2*s4^2*r*w5 - c2*s3^2*r - 4*c2*s3*c4*s4 - 3*c2*s3*s4*r - 1/2*c2*c4^2*r - c2*c4*r^2 - 1/2*c2*s4^2*r - 4*s2*c3*s3*c4*r^2*w4 + s2*c3*s3*c4*r^2 + 8*s2*c3*s3*c4*w4 - 2*s2*c3*s3*c4 + 4*s2*c3*s3*s4^2*r*w4*w5 - s2*c3*s3*s4^2*r*w5 + 4*s2*c3*s3*r*w4 - s2*c3*s3*r + 4*s2*s3*c4^2 - 16*s2*s3*c4*r*w4 + 7*s2*s3*c4*r + 16*s2*s3*r^2*w2*w4 - 4*s2*s3*r^2*w2 - 12*s2*s3*r^2*w4 + 3*s2*s3*r^2 + s2*s4*r^2 + 2*c3*s3^2*c4*r^2*w4 - 4*c3*s3^2*c4*w4 - 2*c3*s3^2*s4^2*r*w4*w5 - 2*c3*s3^2*r*w4 + 8*s3^2*c4*r*w4 - 8*s3^2*r^2*w2*w4 + 6*s3^2*r^2*w4 + s3*c4*s4*r*w5 + 2*s3*s4*r^2*w5 + 2*s3*s4 - 1/2*c4*r - r^2) * h12
  exact one_ne_zero oneEqZero

set_option maxHeartbeats 3200000 in
theorem leaf_tangency_corner_certificate
    (c1 s1 c2 s2 c3 s3 r w v : ℝ)
    (h1 : c1^2 + s1^2 - 1 = 0)
    (h2 : c2^2 + s2^2 - 1 = 0)
    (h3 : c3^2 + s3^2 - 1 = 0)
    (h4 : -4*c1*c2*r^2 + 2*c1*c2 - 2*c1*r + 2*s1*s2 - 2*c2*r + 1 = 0)
    (h5 : -4*c2*c3*r^2 + 2*c2*c3 - 2*c2*r + 2*s2*s3 - 2*c3*r + 1 = 0)
    (h6 : c1*s2 + 2*s1*c2*r^2 - s1*c2 + s1*r = 0)
    (h7 : c1^2*w - 2*c1*c3*w + s1^2*w - 2*s1*s3*w + c3^2*w + s3^2*w - 1 = 0)
    (h8 : -2*c2*r*v + v - 1 = 0)
    : False := by
  have oneEqZero : (1 : ℝ) = 0 := by
    linear_combination
      (-8*c2*c3*r^2*w*v + 4*c2*c3*w*v + 4*s2*s3*w*v - 4*c3*r*w*v + w) * h1 +
      (w) * h3 +
      (-2*c1*c3*w*v - 2*s1*s3*w*v) * h4 +
      (2*w*v) * h5 +
      (-4*c1*s3*w*v + 4*s1*c3*w*v) * h6 +
      (-1) * h7 +
      (2*c1*c3*w + 2*s1*s3*w - 2*w) * h8
  exact one_ne_zero oneEqZero

end Gtz

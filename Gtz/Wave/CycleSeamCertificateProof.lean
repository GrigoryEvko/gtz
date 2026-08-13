import Gtz.Wave.KFourCertificateProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The cycle seam certificate proof — the dichotomy closes closure four

The cycle seam reduction narrowed closure four to one polynomial
statement.  This module proves that statement with the opposite-pair
dichotomy of the K4 proof module.

## The kill

The independent pair prices the corner trace: `T0 + T1 = d0 + d1`.
One read of the independent pair and one read of the parallel pair
feed the dichotomy at the pair `(0, 1)` against the pair `(2, 3)`.
The dichotomy leaves two branches: `d0 + dc = 1` or `d1 + dc = 1`.
Each branch equates `2 * value` with a positive weight sum, against
`value < 0`.  The balance layer is not necessary: the seam dies before
the uncarried corners enter.

## Key results

* `Gtz.cycleSeamCertificate_holds` — **THE CERTIFICATE PROOF.**
* `Gtz.rankFourCycleIndependentClosed_holds` — **CLOSURE FOUR.**

## Vacuity

Every lemma is an unconditional statement about real numbers and real
matrices.  No crux hypothesis appears.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the certificate proof -/

set_option maxHeartbeats 400000 in
/-- **THE CERTIFICATE PROOF.**  The cycle seam certificate holds.  The
pair trace law and two corner products feed the dichotomy, and the two
branches die on the weight cone. -/
theorem cycleSeamCertificate_holds : CycleSeamCertificate := by
  intro value w0 w1 wc w4 w5 qK0 qK1 qK4 qL0 qL1 qL5 qM2 qM3 qM4 qN2
    qN3 qN5 M _ hvalue hw0 hw1 hwc hw4 hw5 hwsum hidem htrace h0a h0b
    h1a h1b h2a h2b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdetKL hqK0 _ _
    hqL0 _ _ hqM2 _ _ hqN2 _ _
  -- the independent pair prices its corner trace
  have htraceKL := pair_trace_of_reads h0a h0b h1a h1b hdetKL
  -- the two corner products feed the dichotomy
  have pKL := corner_product_of_reads hqK0 hqL0 h0a h0b
  have pMN := corner_product_of_reads hqM2 hqN2 h2a h2b
  have hD := corner_dichotomy_zero_one hidem htrace pKL pMN
  -- the two branches die on the weight cone
  rcases mul_eq_zero.mp hD with hsum | htau
  · linarith
  · linarith

/-! ## Layer 2 — the closure -/

/-- **CLOSURE FOUR.**  The labeled cycle with some nonzero cross
determinant dies at every frame. -/
theorem rankFourCycleIndependentClosed_holds :
    RankFourCycleIndependentClosed :=
  rankFourCycleIndependentClosed_of_seam_certificate
    cycleSeamCertificate_holds

end Gtz

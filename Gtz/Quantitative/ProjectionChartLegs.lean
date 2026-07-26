/-
# The projection chart, and the two rank-three legs as polynomials in it

`Gtz.Quantitative.FlooredSpreadRegion` fixes the region a certificate would
target, and records in its MEASURED section that every number was computed "in
the projection chart `P_cd = sqrt(t_c t_d) <g_c, g_d>` with `P^2 = P` and
`trace P = 3`, whose leg translation was verified symbolically over `Q`". That
translation is stated there in prose only. This file proves it.

There is no certificate here. Rank three is not proved, and nothing below claims
it is.

## Why the chart

The design's own coordinates carry an `O(3)` gauge: rotating every atom leaves
`Dominates`, both legs and the whole region invariant, so a certificate written
in the atoms must either quotient that gauge or waste its entire multiplier
budget re-proving invariance. Putting `V_c = sqrt(t_c) g_c` turns Parseval into
`V^T V = I` and the gauge is quotiented exactly by passing to `P = V V^T`, a
rank-three symmetric idempotent whose entries are the chart coordinates. `P` is
automatically bounded — `trace (P^T P) = trace P = 3` — so the chart is
Archimedean for free, which the atom coordinates are not.

The obstruction is that `P_cd` carries a SQUARE ROOT of the weights. What makes
the chart usable is that both legs are even enough to clear it:

  `chartEntry_self`      `P_cc = t_c * |g_c|^2`
  `chartEntry_sq`        `P_cd^2 = t_c t_d <g_c,g_d>^2`
  `chartEntry_triangle`  `P_ab P_ac P_bc = t_a t_b t_c <g_a,g_b><g_a,g_c><g_b,g_c>`

The third is the one that matters. The triangle monomial is the only odd term in
either leg, and it carries EXACTLY the weight product, because each of the three
weights appears in exactly two of the three factors. So no square root survives,
and with `chartGapDiagonal c = P_cc - t_c = t_c * heavyExcess c`:

  `chartTie_eq`       `t_a t_b t_c * discriminantTie = det (P_T - diag t_T)`
  `chartMinorSum_eq`  `t_a t_b t_c * discriminantMinorSum` is the `t`-weighted
                      sum of the three `2x2` principal minors of the same matrix

both by `ring` from the three product lemmas. The weight product is strictly
positive (`weightProduct_pos`), so the scalings are sign-preserving and the
region's two leg inequalities may be read off the chart directly
(`chartTie_nonneg_iff`, `chartMinorSum_nonneg_iff`).

`chartGapMatrix_eq` records the structural reason: the gap matrix IS the
congruence `D_T^{1/2} (Gram_T - I) D_T^{1/2}` by a positive diagonal, so by
Sylvester's law it has the same inertia as `Gram_T - I`, and `Dominates` on a
triple is exactly `P_T >= diag t_T`.

The realness payoff is the point. Over `R` the triangle monomial satisfies
`(P_ab P_ac P_bc)^2 = P_ab^2 P_ac^2 P_bc^2` as an identity between monomials,
whereas the phase-free data of a Hermitian design only gives `<=`. So in this
chart the relation that `Gtz.Quantitative.PhaseFreeNoGo` proves a real
certificate must engage is not an extra generator at all — it is a monomial
identity, and the work is carried instead by the ideal `P^2 - P`, which
`Gtz.Quantitative.FlooredSpreadRegion` records as the place where the complex
trine is actually excluded.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

Everything named above, for `WeightedDesign m 3` at any size `m`.

## CITED (proved elsewhere in this repo, used in the proofs below)

`heavyExcess`, `atomPairing`, `atomPairing_self`, `discriminantMinorSum`,
`discriminantTie` (`Gtz.Quantitative.DiscriminantSystem`); `leverageOf`,
`WeightedDesign` (`Gtz.Core.Basic`).

## REFERENCED IN PROSE ONLY (not imported, not used in any proof here)

`HasSpreadAtLeast`, `HasWeightFloor`, `FlooredSpreadCovering`
(`Gtz.Quantitative.FlooredSpreadRegion`) for the region these coordinates were
built to serve; `Gtz.Quantitative.PhaseFreeNoGo` for the realness requirement;
`Gtz.Complex.SharpConstantLedger` for the trine that forces it.

## MEASURED (computed outside Lean, NOT proved here, stated as such)

The translation proved below was cross-validated before it was trusted, in three
independent arithmetics, against the raw `(g,t)` definitions of
`Gtz.Quantitative.DiscriminantSystem`:

* EXACT, over `Q`: on seven families of exactly rational `(6,3)` designs — four
  built from Cayley-transform rational orthogonal frames with weights that are
  rational squares, three split tetrahedra — both legs computed on both routes
  agree with difference identically `0`, at all twenty triples of each.
* At `70` DIGITS, on random designs: worst relative discrepancy `2.5e-68`, at
  Parseval residual `3.6e-71`.
* In FLOAT64, division-free: worst absolute discrepancy `3.3e-16` over `500`
  random designs times `20` triples. Dividing back out by `t_a t_b t_c` inflates
  that to `1.9e-9` when the smallest weight reaches `1e-4`, which is a statement
  about the division and not about the identity — the identity is the one proved
  below.
* SEMANTICS, on the same sample: the Sylvester reading and the leg criterion were
  checked against a direct eigenvalue test of `Dominates` on all `10000` triples,
  with zero disagreements.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.DiscriminantSystem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## The chart -/

/-- The Stiefel row of an atom: the atom scaled by the square root of its weight.
Parseval says exactly that these rows have Gram the identity. -/
noncomputable def chartBasis (D : WeightedDesign m 3) (atomIndex : Fin m) : Fin 3 → ℝ :=
  fun coordinate => Real.sqrt (D.weight atomIndex) * D.atom atomIndex coordinate

/-- **The projection-chart entry** `P_cd = sqrt (t_c t_d) <g_c, g_d>`: the `(c,d)`
entry of `V V^T`, the rank-three orthogonal projection that quotients the `O(3)`
gauge of the design. -/
noncomputable def chartEntry (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) : ℝ :=
  chartBasis D atomFirst ⬝ᵥ chartBasis D atomSecond

theorem chartEntry_comm (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    chartEntry D atomFirst atomSecond = chartEntry D atomSecond atomFirst :=
  dotProduct_comm _ _

/-- The chart entry factors as the two weight roots times the atom pairing. -/
theorem chartEntry_eq (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    chartEntry D atomFirst atomSecond
      = Real.sqrt (D.weight atomFirst) * Real.sqrt (D.weight atomSecond)
        * atomPairing D atomFirst atomSecond := by
  simp only [chartEntry, chartBasis, atomPairing, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun coordinate _ => by ring

/-- **The diagonal**: `P_cc = t_c |g_c|^2`. The first square root to clear. -/
theorem chartEntry_self (D : WeightedDesign m 3) (atomIndex : Fin m) :
    chartEntry D atomIndex atomIndex
      = D.weight atomIndex * leverageOf (D.atom atomIndex) := by
  rw [chartEntry_eq, atomPairing_self, Real.mul_self_sqrt (D.weight_pos atomIndex).le]

/-- **The square**: `P_cd^2 = t_c t_d <g_c,g_d>^2`. Every even monomial in the
off-diagonal clears its roots. -/
theorem chartEntry_sq (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    chartEntry D atomFirst atomSecond ^ 2
      = D.weight atomFirst * D.weight atomSecond
        * atomPairing D atomFirst atomSecond ^ 2 := by
  have hfirst := Real.mul_self_sqrt (D.weight_pos atomFirst).le
  have hsecond := Real.mul_self_sqrt (D.weight_pos atomSecond).le
  calc chartEntry D atomFirst atomSecond ^ 2
      = (Real.sqrt (D.weight atomFirst) * Real.sqrt (D.weight atomFirst))
          * (Real.sqrt (D.weight atomSecond) * Real.sqrt (D.weight atomSecond))
          * atomPairing D atomFirst atomSecond ^ 2 := by
        rw [chartEntry_eq]; ring
    _ = _ := by rw [hfirst, hsecond]

/-- **The triangle**, the identity the whole chart rests on: the product of the
three off-diagonal entries of a triple carries EXACTLY the weight product,
because each weight appears in precisely two of the three factors. This is the
only odd monomial in either leg, so with it cleared both legs become polynomial
in `(P, t)`. Over `R` it also makes `(P_ab P_ac P_bc)^2 = P_ab^2 P_ac^2 P_bc^2`
a monomial identity — the realness relation, free of charge, in these
coordinates. -/
theorem chartEntry_triangle (D : WeightedDesign m 3)
    (atomFirst atomSecond atomThird : Fin m) :
    chartEntry D atomFirst atomSecond * chartEntry D atomFirst atomThird
        * chartEntry D atomSecond atomThird
      = D.weight atomFirst * D.weight atomSecond * D.weight atomThird
        * (atomPairing D atomFirst atomSecond * atomPairing D atomFirst atomThird
            * atomPairing D atomSecond atomThird) := by
  have hfirst := Real.mul_self_sqrt (D.weight_pos atomFirst).le
  have hsecond := Real.mul_self_sqrt (D.weight_pos atomSecond).le
  have hthird := Real.mul_self_sqrt (D.weight_pos atomThird).le
  calc chartEntry D atomFirst atomSecond * chartEntry D atomFirst atomThird
          * chartEntry D atomSecond atomThird
      = (Real.sqrt (D.weight atomFirst) * Real.sqrt (D.weight atomFirst))
          * (Real.sqrt (D.weight atomSecond) * Real.sqrt (D.weight atomSecond))
          * (Real.sqrt (D.weight atomThird) * Real.sqrt (D.weight atomThird))
          * (atomPairing D atomFirst atomSecond * atomPairing D atomFirst atomThird
              * atomPairing D atomSecond atomThird) := by
        rw [chartEntry_eq, chartEntry_eq, chartEntry_eq]; ring
    _ = _ := by rw [hfirst, hsecond, hthird]

/-! ## The gap matrix of a triple, and the two legs as chart polynomials -/

/-- The diagonal of the chart gap matrix, `P_cc - t_c`. -/
noncomputable def chartGapDiagonal (D : WeightedDesign m 3) (atomIndex : Fin m) : ℝ :=
  chartEntry D atomIndex atomIndex - D.weight atomIndex

/-- The gap diagonal is the heavy excess, scaled by the weight — so the chart gap
matrix is the congruence of `Gram_T - I` by the positive diagonal
`diag (sqrt t)`, and by Sylvester's law the two have the same inertia. In
particular `Dominates D {a,b,c}` is exactly `P_T >= diag t_T`. -/
theorem chartGapDiagonal_eq (D : WeightedDesign m 3) (atomIndex : Fin m) :
    chartGapDiagonal D atomIndex = D.weight atomIndex * heavyExcess D atomIndex := by
  rw [chartGapDiagonal, chartEntry_self, heavyExcess]
  ring

/-- The gap matrix off the diagonal is the chart entry, and on it the gap
diagonal — the congruence written out at every entry. -/
theorem chartGapMatrix_eq (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    (if atomFirst = atomSecond then chartGapDiagonal D atomFirst
      else chartEntry D atomFirst atomSecond)
      = Real.sqrt (D.weight atomFirst) * Real.sqrt (D.weight atomSecond)
        * (if atomFirst = atomSecond then heavyExcess D atomFirst
            else atomPairing D atomFirst atomSecond) := by
  by_cases hsame : atomFirst = atomSecond
  · subst hsame
    rw [if_pos rfl, if_pos rfl, chartGapDiagonal_eq,
      Real.mul_self_sqrt (D.weight_pos atomFirst).le]
  · rw [if_neg hsame, if_neg hsame, chartEntry_eq]

/-- The determinant of the chart gap matrix of a triple, written out. -/
noncomputable def chartGapDeterminant (D : WeightedDesign m 3)
    (atomFirst atomSecond atomThird : Fin m) : ℝ :=
  chartGapDiagonal D atomFirst * chartGapDiagonal D atomSecond
      * chartGapDiagonal D atomThird
    - chartGapDiagonal D atomFirst * chartEntry D atomSecond atomThird ^ 2
    - chartGapDiagonal D atomSecond * chartEntry D atomFirst atomThird ^ 2
    - chartGapDiagonal D atomThird * chartEntry D atomFirst atomSecond ^ 2
    + 2 * (chartEntry D atomFirst atomSecond * chartEntry D atomFirst atomThird
        * chartEntry D atomSecond atomThird)

/-- The weight-weighted sum of the three `2x2` principal minors of the chart gap
matrix. The weights are what the minor-sum leg picks up when its own square roots
are cleared; the plain sum of minors is a different polynomial. -/
noncomputable def chartGapWeightedMinorSum (D : WeightedDesign m 3)
    (atomFirst atomSecond atomThird : Fin m) : ℝ :=
  D.weight atomThird * (chartGapDiagonal D atomFirst * chartGapDiagonal D atomSecond
      - chartEntry D atomFirst atomSecond ^ 2)
    + D.weight atomSecond * (chartGapDiagonal D atomFirst * chartGapDiagonal D atomThird
      - chartEntry D atomFirst atomThird ^ 2)
    + D.weight atomFirst * (chartGapDiagonal D atomSecond * chartGapDiagonal D atomThird
      - chartEntry D atomSecond atomThird ^ 2)

/-- **THE TIE LEG IS A CHART DETERMINANT.** `t_a t_b t_c * e_3 = det (P_T - diag t_T)`.
Every square root is cleared by `chartEntry_sq` and `chartEntry_triangle`; what
is left is `ring`. -/
theorem chartTie_eq (D : WeightedDesign m 3) (atomFirst atomSecond atomThird : Fin m) :
    D.weight atomFirst * D.weight atomSecond * D.weight atomThird
        * discriminantTie D atomFirst atomSecond atomThird
      = chartGapDeterminant D atomFirst atomSecond atomThird := by
  rw [chartGapDeterminant, discriminantTie, chartGapDiagonal_eq, chartGapDiagonal_eq,
    chartGapDiagonal_eq, chartEntry_sq, chartEntry_sq, chartEntry_sq, chartEntry_triangle]
  ring

/-- **THE MINOR-SUM LEG IS A WEIGHTED CHART MINOR SUM.** The same statement for
`e_2`; here no triangle appears, so `chartEntry_sq` alone suffices. -/
theorem chartMinorSum_eq (D : WeightedDesign m 3)
    (atomFirst atomSecond atomThird : Fin m) :
    D.weight atomFirst * D.weight atomSecond * D.weight atomThird
        * discriminantMinorSum D atomFirst atomSecond atomThird
      = chartGapWeightedMinorSum D atomFirst atomSecond atomThird := by
  rw [chartGapWeightedMinorSum, discriminantMinorSum, chartGapDiagonal_eq,
    chartGapDiagonal_eq, chartGapDiagonal_eq, chartEntry_sq, chartEntry_sq, chartEntry_sq]
  ring

/-- The weight product of a triple is strictly positive. -/
theorem weightProduct_pos (D : WeightedDesign m 3) (atomFirst atomSecond atomThird : Fin m) :
    0 < D.weight atomFirst * D.weight atomSecond * D.weight atomThird :=
  mul_pos (mul_pos (D.weight_pos atomFirst) (D.weight_pos atomSecond))
    (D.weight_pos atomThird)

/-- **The tie leg's SIGN is a chart quantity.** The scaling is by a strictly
positive factor, so a certificate may work entirely in `(P, t)`. -/
theorem chartTie_nonneg_iff (D : WeightedDesign m 3)
    (atomFirst atomSecond atomThird : Fin m) :
    0 ≤ chartGapDeterminant D atomFirst atomSecond atomThird
      ↔ 0 ≤ discriminantTie D atomFirst atomSecond atomThird := by
  rw [← chartTie_eq]
  exact mul_nonneg_iff_of_pos_left (weightProduct_pos D atomFirst atomSecond atomThird)

/-- **The minor-sum leg's SIGN is a chart quantity.** -/
theorem chartMinorSum_nonneg_iff (D : WeightedDesign m 3)
    (atomFirst atomSecond atomThird : Fin m) :
    0 ≤ chartGapWeightedMinorSum D atomFirst atomSecond atomThird
      ↔ 0 ≤ discriminantMinorSum D atomFirst atomSecond atomThird := by
  rw [← chartMinorSum_eq]
  exact mul_nonneg_iff_of_pos_left (weightProduct_pos D atomFirst atomSecond atomThird)

/-- **The spread generator is a chart quantity too**, and the weights cancel out
of it entirely — which is why `HasSpreadAtLeast` of
`Gtz.Quantitative.FlooredSpreadRegion` is simultaneously gauge-invariant and
weight-free. -/
theorem chartSpread_iff (D : WeightedDesign m 3) (spread : ℝ)
    (atomFirst atomSecond : Fin m) :
    chartEntry D atomFirst atomSecond ^ 2
        ≤ (1 - spread) * (chartEntry D atomFirst atomFirst
          * chartEntry D atomSecond atomSecond)
      ↔ atomPairing D atomFirst atomSecond ^ 2
        ≤ (1 - spread) * (leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond)) := by
  have hweights : 0 < D.weight atomFirst * D.weight atomSecond :=
    mul_pos (D.weight_pos atomFirst) (D.weight_pos atomSecond)
  rw [chartEntry_sq, chartEntry_self, chartEntry_self]
  constructor
  · intro hbound; nlinarith [hbound, hweights]
  · intro hbound; nlinarith [hbound, hweights]

end Gtz

/-
# The criticality branch: the quadric law, and why no tie is attained on ONE subset

**This file is the ADDITIONAL-ASSUMPTION branch of the tie ledger.**  Everything
proved here is a theorem about a hypothesised multiplier; the hypothesis itself —
the QUADRIC LAW — is NOT proved anywhere, and it must never be used to prove
`GtzWeighted` at the size where it is assumed.  See the provenance note below.

## The law

Call a symmetric `Λ` a CRITICAL MULTIPLIER of the design at the `k`-subset `C`
when

    tr Λ = 1,     Λ (S_C − 1) = 0,     g_cᵀ Λ g_c = 1  for EVERY atom c .

The third condition is the quadric law: all `m` atoms lie on the single quadric
`{x : xᵀ Λ x = 1}`.

## PROVED here (unconditional, given the hypotheses)

* `trace_mul_subsetSum` — `tr(Λ S_C) = Σ_{c∈C} g_cᵀ Λ g_c`, pure linearity.
* `trace_mul_gap_of_quadricLaw` — **the gap-trace law**: under the quadric law
  and `tr Λ = 1`, EVERY `k`-subset satisfies `tr(Λ (S_C − 1)) = k − 1`.  The
  multiplier reads the same number off every subset, active or not.
* `not_isCriticalMultiplierAt` — hence, for `k ≥ 2`, **no critical multiplier
  annihilates the gap of a `k`-subset**: annihilation forces that trace to be
  `0`, and `0 = k − 1` forces `k = 1`.

## What that means for totality (PROSE, not proved here)

Stationarity of the design manifold at a tie whose max is attained on a SINGLE
`k`-subset `C` produces exactly such a multiplier: the KKT conditions for
minimising `max_C λ_min(S_C)` subject to Parseval and `Σ t_c = 1` read

    Σ_{C ∋ c} λ_C (w_C ⬝ g_c) w_C = t_c Λ g_c ,    g_cᵀ Λ g_c = −ν  for every c,

with `Λ = Σ_C λ_C w_C w_Cᵀ` (so `Λ ⪰ 0`, `tr Λ = 1`) and `ν = −1` after summing
against Parseval; a single active subset makes `Λ` supported on `ker(S_C − 1)`,
i.e. `Λ (S_C − 1) = 0`.  `not_isCriticalMultiplierAt` then says that
configuration is impossible — so at a tie the max is attained at TWO OR MORE
`k`-subsets, and (from the same stationarity, the COVERAGE LAW
`Σ_{C ∋ c} λ_C (w_C ⬝ g_c)² = t_c`) every atom lies in an active subset.

**Provenance of the hypothesis, and the circularity it would create.**  Those
KKT conditions hold at a tie only if the tie is a local MINIMUM of
`max_C λ_min(S_C)`, which is precisely `GtzWeighted m k` in a neighbourhood.  So
the quadric law at size `m` is a consequence of the statement being proved at
size `m`, never an input to it.  Read in the sound direction it says: a tie with
a single active `k`-subset admits a descent direction, and its neighbourhood
contains designs with NO dominating `k`-subset — exhibiting one would REFUTE
`GtzWeighted m k`.  Partial ties of that shape are therefore exactly as hard to
produce as GTZ counterexamples.

The unconditional half of the totality question lives in
`Gtz.Ties.TotalTieCorankOne`: at `m = k + 1` every tie IS total, its matroid IS
uniform, and it IS simple, with no criticality assumption anywhere.

[MEASURED, outside Lean, in exact rational arithmetic]  The law is not vacuous:
at the tetrahedron `(4,3)` tie it holds with `Λ = 1/3 · I` (every leverage is
`3`), and the coverage law reads `Σ_{j ≠ c} (1/4)(g_j ⬝ g_c)²/3 = 1/4 = t_c`.  At
the `(7,3)` split tetrahedron it is the shipped Farkas certificate of
`Gtz.Ties.StratumFirstOrder` with `Λ = 1/3 · I`, which is why that certificate's
right-hand side `2 Σ_c t_c ⟨g_c, dg_c⟩` vanishes on every tangent direction.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.RayleighCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- **The critical-multiplier interface.**  `Λ` has unit trace, annihilates the
gap of `C`, and puts every atom of the design on the quadric `xᵀ Λ x = 1`.  This
is the KKT stationarity data of a tie whose max is attained on `C` alone — a
hypothesis, never a theorem; see the header. -/
def IsCriticalMultiplierAt (D : WeightedDesign m k) (C : Finset (Fin m))
    (multiplier : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  Matrix.trace multiplier = 1 ∧
    multiplier * (subsetSum D C - 1) = 0 ∧
    ∀ c : Fin m, D.atom c ⬝ᵥ (multiplier *ᵥ D.atom c) = 1

/-- Pairing a matrix against a subset's atom sum is summing the quadratic form
over the selected atoms. -/
theorem trace_mul_subsetSum (D : WeightedDesign m k) (C : Finset (Fin m))
    (multiplier : Matrix (Fin k) (Fin k) ℝ) :
    Matrix.trace (multiplier * subsetSum D C)
      = ∑ c ∈ C, D.atom c ⬝ᵥ (multiplier *ᵥ D.atom c) := by
  rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.trace_mul_comm, atomMatrix_trace_pairing]

/-- **The gap-trace law.**  Under the quadric law every `k`-subset — active or
not, basis or not — pairs with the multiplier to the same number: the gap
`S_C − 1` has multiplier-trace exactly `k − 1`.  The subset never enters; only
its cardinality does. -/
theorem trace_mul_gap_of_quadricLaw (D : WeightedDesign m k) (C : Finset (Fin m))
    (hcard : C.card = k) (multiplier : Matrix (Fin k) (Fin k) ℝ)
    (htrace : Matrix.trace multiplier = 1)
    (hquadric : ∀ c : Fin m, D.atom c ⬝ᵥ (multiplier *ᵥ D.atom c) = 1) :
    Matrix.trace (multiplier * (subsetSum D C - 1)) = (k : ℝ) - 1 := by
  have hpaired : Matrix.trace (multiplier * subsetSum D C) = (k : ℝ) := by
    rw [trace_mul_subsetSum]
    rw [Finset.sum_congr rfl fun c _ => hquadric c, Finset.sum_const, hcard, nsmul_eq_mul,
      mul_one]
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one, hpaired, htrace]

/-- **No tie is attained on a single `k`-subset** (`k ≥ 2`).  A critical
multiplier annihilates the gap of `C`, so that gap's multiplier-trace is `0`;
the gap-trace law says it is `k − 1`; hence `k = 1`.

This is the whole content of the first-order exclusion, and it is one line of
linear algebra once the quadric law is granted.  What it does NOT do is prove
that a tie's active set is ALL of the bases — the law is blind to which subsets
are active, so totality does not follow from criticality, and the per-matroid
tie systems must keep the active pattern as an explicit branch. -/
theorem not_isCriticalMultiplierAt (hk : 2 ≤ k) (D : WeightedDesign m k) (C : Finset (Fin m))
    (hcard : C.card = k) (multiplier : Matrix (Fin k) (Fin k) ℝ) :
    ¬ IsCriticalMultiplierAt D C multiplier := by
  rintro ⟨htrace, hannihilates, hquadric⟩
  have hlaw := trace_mul_gap_of_quadricLaw D C hcard multiplier htrace hquadric
  rw [hannihilates, Matrix.trace_zero] at hlaw
  have hrank : (k : ℝ) = 1 := by linarith
  have hcast : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [hrank] at hcast
  linarith

/-- The exclusion in the shape the sweep consumes: at rank three no critical
multiplier exists at any triple, whatever the design and whatever the size. -/
theorem not_isCriticalMultiplierAt_rankThree (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) (multiplier : Matrix (Fin 3) (Fin 3) ℝ) :
    ¬ IsCriticalMultiplierAt D C multiplier :=
  not_isCriticalMultiplierAt (by omega) D C hcard multiplier

end Gtz

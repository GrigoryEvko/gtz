/-
# The rational Schur-pigeonhole layer: trace identity, excess balance, pigeonhole

The certificate class of the campaign (diary §46, proven at k=3 in
`gtz_proof_gtz3_ratpigeon.md` §2, general (m,k) in `gtz_proof_gtz_allk_lift.md` §4.1):
for any base set Q with S_Q ≻ I and pivot values q_c = tr((S_Q − I)⁻¹ g_c g_cᵀ),

  Σ_{d∈Q} (1 − t_d) q_d = k + Σ_{e∉Q} t_e q_e            (trace identity)
  Σ_{d∈Q} (1 − t_d)(q_d − 1) = Σ_{e∉Q} t_e (q_e − 1)     (excess balance, |Q| = k+1)

and the pigeonhole: if the outsiders' excess is ≤ 0 then some insider has q_d ≤ 1
and Q ∖ {d} dominates (rank-one Schur).

Informal proofs are one line from Parseval; the Lean versions need the
`(subsetSum D Q − 1).PosDef` hypothesis throughout — `Matrix.inv` of a singular
matrix is the ZERO matrix in Mathlib (junk value), so `pivot` is meaningful only
under PosDef. Every statement here carries it.

STATUS: statements (roadmap targets); proofs pending.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- The trace identity: multiply Parseval's
S_Q − I = Σ_{d∈Q}(1−t_d)A_d − Σ_{e∉Q}t_e A_e by (S_Q − I)⁻¹ and take traces. -/
theorem trace_identity (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) :
    ∑ d ∈ Q, (1 - D.weight d) * pivot D Q d
      = k + ∑ e ∈ Qᶜ, D.weight e * pivot D Q e := by
  sorry

/-- Excess balance at |Q| = k+1: subtract Σ_{d∈Q}(1−t_d) = |Q| − 1 + Σ_out t_e. -/
theorem excess_balance (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) (hcard : Q.card = k + 1) :
    ∑ d ∈ Q, (1 - D.weight d) * (pivot D Q d - 1)
      = ∑ e ∈ Qᶜ, D.weight e * (pivot D Q e - 1) := by
  sorry

/-- Rank-one Schur step: for d ∈ Q, S_Q − A_d ⪰ I ⟺ q_d ≤ 1 (under S_Q ≻ I). -/
theorem erase_dominates_iff_pivot_le_one (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) {d : Fin m} (hd : d ∈ Q) :
    Dominates D (Q.erase d) ↔ pivot D Q d ≤ 1 := by
  sorry

/-- **Branch (a), the pigeonhole**: |Q| = k+1, S_Q ≻ I, outsiders' weighted excess
≤ 0 ⟹ some insider drop dominates. The m = k+1 case (no outsiders) is the exact
tie — the (k+1)-cycle pigeonhole for every k. -/
theorem pigeonhole (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) (hcard : Q.card = k + 1)
    (houtside : ∑ e ∈ Qᶜ, D.weight e * (pivot D Q e - 1) ≤ 0) :
    ∃ d ∈ Q, Dominates D (Q.erase d) := by
  sorry

end Gtz

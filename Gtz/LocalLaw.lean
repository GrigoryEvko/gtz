/-
# The local-law linear program and the weight-split invariance

Two more pre-audit claims mechanized (mechanization as audit):

* `budget_le_vertex_bound` — the **LP bound behind the first-order constant**.
  At a family point the budget is `Σ_k W_k x_k` with `x_k = σ* − σ_k ≥ 0`, and
  the tangent-space relation contributes `Σ_k λ_k x_k = σ*·Σλ` with all
  `λ_k > 0`. The bound `Σ W_k x_k ≤ (max_k W_k Σλ/λ_k)·σ*` is exactly the
  vertex evaluation the build calls `C_B(pt) = max_k W_k (Σλ)/λ_k` — so the
  first-order constant is a weighted-max, not an average.
* `weightSplit_design_invariant` — the **structural root of σ-independence**:
  when two atoms carry the same square, splitting their combined weight in any
  proportion leaves every design equation unchanged. This is why the anchored
  covector cannot depend on the split parameter `σ` (Theorem Σ's mechanism, at
  the level where it is a one-line fact rather than a 25×25 solve).
-/
import Mathlib
import Gtz.PsdKit
import Gtz.Pushoff

namespace Gtz

open Matrix

/-! ### The vertex bound -/

/-- **The LP vertex bound** (three-term form, the family triangle): with
positive multipliers `λ`, nonnegative budget rates `W`, nonnegative slack
deficits `x`, and the tangent relation `Σ λ_k x_k = maxSlack · Σ λ`, the budget
`Σ W_k x_k` is at most `(max_k W_k·Σλ/λ_k) · maxSlack`. The maximum over `k`
— not any average — is the first-order constant. -/
theorem budget_le_vertex_bound
    (firstRate secondRate thirdRate : ℝ)
    (firstMult secondMult thirdMult : ℝ)
    (firstDeficit secondDeficit thirdDeficit : ℝ) (maxSlack vertexBound : ℝ)
    (hfirstMult : 0 < firstMult) (hsecondMult : 0 < secondMult)
    (hthirdMult : 0 < thirdMult)
    (hfirstDeficit : 0 ≤ firstDeficit) (hsecondDeficit : 0 ≤ secondDeficit)
    (hthirdDeficit : 0 ≤ thirdDeficit)
    (hfirstVertex : firstRate / firstMult ≤ vertexBound)
    (hsecondVertex : secondRate / secondMult ≤ vertexBound)
    (hthirdVertex : thirdRate / thirdMult ≤ vertexBound)
    (htangent : firstMult * firstDeficit + secondMult * secondDeficit
      + thirdMult * thirdDeficit
      = maxSlack * (firstMult + secondMult + thirdMult)) :
    firstRate * firstDeficit + secondRate * secondDeficit
        + thirdRate * thirdDeficit
      ≤ vertexBound * (maxSlack * (firstMult + secondMult + thirdMult)) := by
  have hfirstTerm : firstRate * firstDeficit
      ≤ vertexBound * (firstMult * firstDeficit) := by
    have hrate : firstRate ≤ vertexBound * firstMult := by
      rw [div_le_iff₀ hfirstMult] at hfirstVertex
      linarith
    nlinarith [hfirstDeficit, hrate]
  have hsecondTerm : secondRate * secondDeficit
      ≤ vertexBound * (secondMult * secondDeficit) := by
    have hrate : secondRate ≤ vertexBound * secondMult := by
      rw [div_le_iff₀ hsecondMult] at hsecondVertex
      linarith
    nlinarith [hsecondDeficit, hrate]
  have hthirdTerm : thirdRate * thirdDeficit
      ≤ vertexBound * (thirdMult * thirdDeficit) := by
    have hrate : thirdRate ≤ vertexBound * thirdMult := by
      rw [div_le_iff₀ hthirdMult] at hthirdVertex
      linarith
    nlinarith [hthirdDeficit, hrate]
  rw [← htangent]
  linarith

/-! ### Weight splitting -/

/-- **Weight splitting is invisible to the design equations.** If two atoms
carry the same square (hence the same leverage), then redistributing their
combined weight between them changes no design sum: weight, closure, and
trace are all functions of the total. This is the structural reason the
anchored covector of the tied variety cannot depend on the split parameter. -/
theorem weightSplit_design_invariant (sharedSquare : Fin 2 → ℝ)
    (totalWeight splitFraction : ℝ) :
    (splitFraction * totalWeight + (1 - splitFraction) * totalWeight
        = totalWeight)
      ∧ ((splitFraction * totalWeight) • sharedSquare
          + ((1 - splitFraction) * totalWeight) • sharedSquare
        = totalWeight • sharedSquare)
      ∧ (splitFraction * totalWeight * planarNorm sharedSquare
          + (1 - splitFraction) * totalWeight * planarNorm sharedSquare
        = totalWeight * planarNorm sharedSquare) := by
  refine ⟨by ring, ?_, by ring⟩
  rw [← add_smul]
  congr 1
  ring

/-- The same invariance for the defect pairing: a split pair contributes to
`Σ t_c d_c` exactly as the merged atom does, so the pairing leash and every
covector identity are split-blind. -/
theorem weightSplit_defect_invariant (moment sharedSquare : Fin 2 → ℝ)
    (totalWeight splitFraction : ℝ) :
    splitFraction * totalWeight * planarDefect moment sharedSquare
        + (1 - splitFraction) * totalWeight * planarDefect moment sharedSquare
      = totalWeight * planarDefect moment sharedSquare := by
  ring

end Gtz

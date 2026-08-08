/-
# The complement engine: outside-share domination certifies a strict dominator

For any subset `C` of a weighted design at ANY rank, the unweighted subset sum
dominates the weighted one scaled by the reciprocal of `C`'s largest weight, and
Parseval turns the weighted inside sum into `1 - (outside share)`.  So when the
outside atoms' weighted Parseval share stays strictly below `1 - max weight in C`
in every direction, `C` strictly dominates.  No pair, no pivot, no chart, no
heaviness: the certificate reads only the OUTSIDE of the candidate subset.

This is the BALANCE-side counterpart of the concentration-side engine
`Gtz.exists_pos_discriminantTie_of_pos_surplusForm`
(`Gtz/Quantitative/TieRowLaw.lean`).  That one needs an atom of above-half
leverage share -- `Gtz.sum_atomShare_eq_rank` pins the average share to exactly a
half at `(6,3)`, so it is dead on the balanced stratum.  This one fires precisely
when no direction is dominated by the complement, which is exactly that stratum:
at `Gtz.icosaDesign` every share surplus is `-1/6` and the shipped engine cannot
fire, while the outside share of a well-spread triple stays clear of the bound.
The two certificates are logical complements, not competitors.

The proof is one line of mathematics.  Each inside atom satisfies
`a a^T >= (weight / maxWeight) * a a^T`, so the unweighted inside sum dominates
the weighted inside sum divided by `maxWeight`; and Parseval splits the weighted
total as inside plus outside, so the inside weighted mass exceeds
`maxWeight * |probe|^2` whenever the outside stays below `(1 - maxWeight) * |probe|^2`.
-/
import Gtz.Ties.TotalTieCorankOne
import Gtz.Quantitative.DesignQuadraticFloors
import Gtz.Quantitative.PhaseFreeNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-- **THE COMPLEMENT ENGINE.**  If every direction sees the atoms OUTSIDE `C`
carry strictly less than `1 - maxWeight` of the weighted Parseval mass, where
`maxWeight` bounds every weight inside `C`, then `C` strictly dominates.  Works
at every rank, for every subset size, with no heaviness hypothesis. -/
theorem posDef_subsetSum_of_outside_share_lt (D : WeightedDesign m k)
    (C : Finset (Fin m)) (maxWeight : ℝ) (hmaxPos : 0 < maxWeight)
    (hbound : ∀ label ∈ C, D.weight label ≤ maxWeight)
    (houtside : ∀ probe : Fin k → ℝ, probe ≠ 0 →
      ∑ label ∈ Cᶜ, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2
        < (1 - maxWeight) * (probe ⬝ᵥ probe)) :
    (subsetSum D C - 1).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D C), fun probe hprobeNe => ?_⟩
  rw [star_trivial]
  have hquad : probe ⬝ᵥ (subsetSum D C - 1) *ᵥ probe
      = (∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
    rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
      Matrix.one_mulVec]
  rw [hquad]
  have hinside : ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
      ≤ maxWeight * ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hsq : 0 ≤ (D.atom c ⬝ᵥ probe) ^ 2 := sq_nonneg _
    nlinarith [hbound c hc, hsq]
  have huniv : probe ⬝ᵥ probe
      = ∑ c, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
    rw [dotProduct_eq_sum_weight_mul_pair D probe probe]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hparseval : probe ⬝ᵥ probe
      = (∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2)
        + ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
    rw [huniv]
    exact (Finset.sum_add_sum_compl C
      (fun c => D.weight c * (D.atom c ⬝ᵥ probe) ^ 2)).symm
  have houtsideBound := houtside probe hprobeNe
  have hinsidePos : maxWeight * (probe ⬝ᵥ probe)
      < ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
    nlinarith [houtsideBound, hparseval]
  have hchain : maxWeight * (probe ⬝ᵥ probe)
      < maxWeight * ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 :=
    lt_of_lt_of_le hinsidePos hinside
  have hfinal : probe ⬝ᵥ probe < ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 :=
    lt_of_mul_lt_mul_left hchain hmaxPos.le
  linarith

end Gtz

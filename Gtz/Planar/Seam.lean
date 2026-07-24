/-
# The seam propositions

The two halves of the τ-seam, each an elementary comparison once the platform
identities are in place. Both were flagged as clean-proven-absent in the
inventory; the mechanization makes their smallness visible.

**Above the seam** (`σ* > τ`): any absolute ceiling on the budget converts to
a linear law with constant `ceiling/τ`, because the slack itself exceeds the
floor. Nothing about the platform enters — the trivial branch really is
trivial.

**Below the seam** (`σ* ≤ τ`): the τ-essential set sits inside the level-`a`
essential set, and when every cross contribution of the larger set is
nonnegative — which is what silence guarantees through the pair entries — the
smaller budget is dominated term by term. The subsumption is a subset-sum
comparison, nothing more.
-/
import Mathlib

namespace Gtz

/-- **Seam, the trivial branch**: a bounded budget above the seam obeys the
linear law with constant `ceiling/floor`. -/
theorem seam_trivial_scale {budget ceiling floor slack : ℝ}
    (hbudget : budget ≤ ceiling) (hfloor : 0 < floor)
    (hseam : floor < slack) (hceiling : 0 ≤ ceiling) :
    budget ≤ ceiling / floor * slack := by
  have hratio : ceiling ≤ ceiling / floor * slack := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hfloor]
    nlinarith [hceiling, hseam]
  linarith

/-- **Seam, the subsumption branch**: on a smaller index set the pair budget is
dominated term by term, provided the larger set's contributions are all
nonnegative. The sum runs over ordered pairs; the diagonal is included on both
sides so no off-diagonal bookkeeping is needed. -/
theorem seam_subsumption {atomCount : ℕ}
    (essentialSmall essentialLarge : Finset (Fin atomCount))
    (contribution : Fin atomCount → Fin atomCount → ℝ)
    (hsubset : essentialSmall ⊆ essentialLarge)
    (hnonneg : ∀ c ∈ essentialLarge, ∀ d ∈ essentialLarge,
      0 ≤ contribution c d) :
    ∑ c ∈ essentialSmall, ∑ d ∈ essentialSmall, contribution c d
      ≤ ∑ c ∈ essentialLarge, ∑ d ∈ essentialLarge, contribution c d := by
  have hinner : ∀ c ∈ essentialSmall,
      ∑ d ∈ essentialSmall, contribution c d
        ≤ ∑ d ∈ essentialLarge, contribution c d := by
    intro c hc
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      fun d hd _ => hnonneg c (hsubset hc) d hd
  calc ∑ c ∈ essentialSmall, ∑ d ∈ essentialSmall, contribution c d
      ≤ ∑ c ∈ essentialSmall, ∑ d ∈ essentialLarge, contribution c d :=
        Finset.sum_le_sum hinner
    _ ≤ ∑ c ∈ essentialLarge, ∑ d ∈ essentialLarge, contribution c d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset fun c hc _ =>
          Finset.sum_nonneg fun d hd => hnonneg c hc d hd

end Gtz

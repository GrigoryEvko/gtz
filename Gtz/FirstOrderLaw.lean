/-
# The corrected first-order constant, and the positive-covector fire rate

Two pieces of the closure round, both stated for an arbitrary finite index set.

**The vanishing-atom channel.** The budget near a family point is
`Σ_k W_k (1 − x_k) + y·H`: the main clusters contribute their slack deficits,
and an extra atom of vanishing weight `y` contributes its own rate `H`. The
weights are not free — the covector pairing leashes them,
`y·d + Σ_k λ_k (1 − x_k)·(−1) ...`, which in deficit coordinates
`u_k = 1 − x_k` is exactly

  `y·d + Σ_k λ_k u_k = 1`   (the stress multipliers being normalized `Σλ = 1`).

Against that single linear constraint the objective is bounded by
`max( max_k W_k/λ_k , H/d )` — the cluster face and the channel face — and BOTH
faces are attained. So the first-order constant is a maximum of two rates, not
the cluster rate alone: `C_first = max(C_B, η)`. The proof is three lines of
weighted comparison; the content is that the channel face exists at all, since
a fixed-atom-count analysis never sees it.

**The fire rate.** A strictly positive covector annihilating a value vector
forces a negative component whose size is controlled by the covector's own
spread: if some component has size at least `β`, some component is at most
`−λ_index·β/‖λ‖₁`. When the large component is already negative the rate is the
full `β` — the two-case split that localizes the weight-degeneration of the
rate into a single cone.
-/
import Mathlib

namespace Gtz

variable {ι : Type*} [Fintype ι]

/-! ### The two-face first-order bound -/

/-- **The corrected first-order law**: under the covector leash the budget is at
most the larger of the cluster rate `max_k W_k/λ_k` and the channel rate `H/d`.
Every hypothesis is an inequality between named nonnegative quantities; no
optimization, no vertex enumeration. -/
theorem budget_le_max_of_leash
    (mult rate deficit : ι → ℝ)
    (channelRate channelDefect channelWeight bound : ℝ)
    (hmultPos : ∀ i, 0 < mult i)
    (hdeficitNonneg : ∀ i, 0 ≤ deficit i)
    (hchannelWeightNonneg : 0 ≤ channelWeight)
    (hchannelDefectPos : 0 < channelDefect)
    (hleash : channelWeight * channelDefect + ∑ i, mult i * deficit i = 1)
    (hclusterFace : ∀ i, rate i / mult i ≤ bound)
    (hchannelFace : channelRate / channelDefect ≤ bound) :
    (∑ i, rate i * deficit i) + channelWeight * channelRate ≤ bound := by
  have hclusterTerm : ∀ i, rate i * deficit i ≤ bound * (mult i * deficit i) := by
    intro i
    have hrate : rate i ≤ bound * mult i :=
      (div_le_iff₀ (hmultPos i)).mp (hclusterFace i)
    nlinarith [hdeficitNonneg i, hrate]
  have hclusterSum : ∑ i, rate i * deficit i
      ≤ bound * ∑ i, mult i * deficit i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hclusterTerm i
  have hchannelTerm : channelWeight * channelRate
      ≤ bound * (channelWeight * channelDefect) := by
    have hrate : channelRate ≤ bound * channelDefect :=
      (div_le_iff₀ hchannelDefectPos).mp hchannelFace
    nlinarith [hchannelWeightNonneg, hrate]
  have hcombine : bound * (∑ i, mult i * deficit i)
      + bound * (channelWeight * channelDefect) = bound := by
    rw [← mul_add, add_comm (∑ i, mult i * deficit i), hleash, mul_one]
  linarith [hclusterSum, hchannelTerm, hcombine]

/-- **The channel face is attained**: putting no deficit on the clusters and
spending the whole leash on the extra atom realizes the rate `H/d` exactly.
This is the configuration a fixed-atom-count analysis cannot see, because the
extra atom's weight vanishes with the slack. -/
theorem channelFace_attained
    (mult rate : ι → ℝ) (channelRate channelDefect : ℝ)
    (hchannelDefectPos : 0 < channelDefect) :
    (∑ i, rate i * (0 : ℝ)) + channelDefect⁻¹ * channelRate
        = channelRate / channelDefect
      ∧ channelDefect⁻¹ * channelDefect + ∑ i, mult i * (0 : ℝ) = 1 := by
  constructor
  · simp [div_eq_inv_mul]
  · simp [inv_mul_cancel₀ (ne_of_gt hchannelDefectPos)]

/-- **The cluster face is attained**: spending the whole leash on one cluster's
deficit realizes that cluster's rate `W_j/λ_j` exactly, with no extra atom. The
two attainment witnesses together make `max(C_B, η)` the exact first-order
constant rather than merely an upper bound. -/
theorem clusterFace_attained [DecidableEq ι]
    (mult rate : ι → ℝ) (chosen : ι) (hmultPos : ∀ i, 0 < mult i) :
    -- the deficit is concentrated on `chosen` at the leash-saturating level

    (∑ i, rate i * (if i = chosen then (mult chosen)⁻¹ else 0))
        = rate chosen / mult chosen
      ∧ (0 : ℝ) * (1 : ℝ)
          + ∑ i, mult i * (if i = chosen then (mult chosen)⁻¹ else 0) = 1 := by
  have hpick : ∀ f : ι → ℝ,
      (∑ i, f i * (if i = chosen then (mult chosen)⁻¹ else 0))
        = f chosen * (mult chosen)⁻¹ := by
    intro f
    rw [Finset.sum_eq_single chosen]
    · simp
    · intro i _ hne
      simp [hne]
    · intro hnot
      exact absurd (Finset.mem_univ chosen) hnot
  refine ⟨?_, ?_⟩
  · rw [hpick rate, div_eq_mul_inv]
  · rw [hpick mult, zero_mul, zero_add,
      mul_inv_cancel₀ (ne_of_gt (hmultPos chosen))]

/-! ### The positive-covector fire rate -/

/-- A strictly positive covector annihilating a value vector forces some value
to be nonpositive. -/
theorem exists_value_nonpos_of_positive_covector
    (mult value : ι → ℝ) (witness : ι)
    (hmultPos : ∀ i, 0 < mult i)
    (hannihilate : ∑ i, mult i * value i = 0) :
    ∃ i, value i ≤ 0 := by
  by_contra hcontra
  push_neg at hcontra
  have hpos : 0 < ∑ i, mult i * value i :=
    Finset.sum_pos (fun i _ => mul_pos (hmultPos i) (hcontra i))
      ⟨witness, Finset.mem_univ witness⟩
  exact absurd hannihilate (ne_of_gt hpos)

/-- **Lemma C1′, the two-case fire rate**: with a strictly positive covector
annihilating the value vector, a component of size at least `floor` forces some
component below `−mult index · floor / ‖mult‖₁`. When the large component is
itself negative the rate is the full `floor` (the covector plays no role); only
when it is positive does the covector's spread enter. That is the localization
which confines the weight-degeneration of the rate to a single cone. -/
theorem exists_fire_of_positive_covector
    (mult value : ι → ℝ) (index : ι) (floor : ℝ)
    (hmultPos : ∀ i, 0 < mult i)
    (hannihilate : ∑ i, mult i * value i = 0)
    (hfloorPos : 0 < floor) (hlarge : floor ≤ |value index|) :
    ∃ i, mult index * floor / (∑ j, mult j) ≤ -value i := by
  classical
  have hmassPos : 0 < ∑ j, mult j :=
    Finset.sum_pos (fun j _ => hmultPos j) ⟨index, Finset.mem_univ index⟩
  have hmassGe : mult index ≤ ∑ j, mult j :=
    Finset.single_le_sum (fun j _ => (hmultPos j).le) (Finset.mem_univ index)
  rcases le_or_gt (value index) 0 with hneg | hpos
  · -- the dominant component is already negative: the full floor fires there
    refine ⟨index, ?_⟩
    have hfloorLe : floor ≤ -value index := by
      rw [abs_of_nonpos hneg] at hlarge
      exact hlarge
    have hratio : mult index * floor / (∑ j, mult j) ≤ floor := by
      rw [div_le_iff₀ hmassPos, mul_comm floor (∑ j, mult j)]
      exact mul_le_mul_of_nonneg_right hmassGe hfloorPos.le
    linarith
  · -- the dominant component is positive: the covector spread supplies the rate
    obtain ⟨best, _, hbest⟩ := Finset.exists_max_image Finset.univ
      (fun i => -value i) ⟨index, Finset.mem_univ index⟩
    refine ⟨best, ?_⟩
    obtain ⟨nonpos, hnonpos⟩ :=
      exists_value_nonpos_of_positive_covector mult value index hmultPos
        hannihilate
    have hbestNonneg : 0 ≤ -value best := by
      have := hbest nonpos (Finset.mem_univ nonpos)
      linarith
    -- λ_index·v_index = Σ_{i ≠ index} λ_i·(−v_i) ≤ ‖λ‖₁·max(−v)
    have hsplit : mult index * value index
        = ∑ i ∈ Finset.univ.erase index, mult i * (-value i) := by
      have hrest := Finset.add_sum_erase Finset.univ
        (fun i => mult i * value i) (Finset.mem_univ index)
      have hnegSum : ∑ i ∈ Finset.univ.erase index, mult i * (-value i)
          = -∑ i ∈ Finset.univ.erase index, mult i * value i := by
        simp [mul_neg]
      rw [hnegSum]
      linarith [hrest, hannihilate]
    have hdominate : ∑ i ∈ Finset.univ.erase index, mult i * (-value i)
        ≤ (∑ j, mult j) * (-value best) := by
      calc ∑ i ∈ Finset.univ.erase index, mult i * (-value i)
          ≤ ∑ i ∈ Finset.univ.erase index, mult i * (-value best) :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (hbest i (Finset.mem_univ i))
                (hmultPos i).le
        _ = (∑ i ∈ Finset.univ.erase index, mult i) * (-value best) := by
            rw [Finset.sum_mul]
        _ ≤ (∑ j, mult j) * (-value best) := by
            refine mul_le_mul_of_nonneg_right ?_ hbestNonneg
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.erase_subset _ _) fun j _ _ => (hmultPos j).le
    have hfloorLe : floor ≤ value index := by
      rw [abs_of_pos hpos] at hlarge
      exact hlarge
    have hstep : mult index * floor ≤ mult index * value index :=
      mul_le_mul_of_nonneg_left hfloorLe (hmultPos index).le
    rw [div_le_iff₀ hmassPos, mul_comm (-value best)]
    linarith [hstep, hsplit, hdominate]

end Gtz

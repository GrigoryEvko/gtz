/-
# The collinear stratum is empty

The β = 0 branch of the Gordan covering theorem. A degenerate certificate
forces every square onto a line through the origin (`StressFrame` handles the
β ≠ 0 branch), so the design data collapses to signed positions on that line.
Closure splits the leverage mass evenly — each side carries exactly `1` — and
silence caps the leverages of at least one full side at `1`. But a side whose
leverages are capped at one cannot carry leverage mass `1` on weight strictly
below `1`: the design equations and silence are jointly unsatisfiable on a
line. No equality design is collinear, so every Gordan certificate has
`β ≠ 0`, the focal conic exists, and the covering theorem closes.
-/
import Mathlib

namespace Gtz

/-- **The collinear stratum is empty.** Signed positions on a line with
positive weights, weight one, closure, trace two, and pairwise silence across
the origin (every opposite pair has a side of leverage at most one) are
contradictory. -/
theorem collinear_stratum_empty {m : ℕ} (weight signedPos : Fin m → ℝ)
    (hweightPos : ∀ c, 0 < weight c)
    (hweightSum : ∑ c, weight c = 1)
    (hclosure : ∑ c, weight c * signedPos c = 0)
    (htrace : ∑ c, weight c * |signedPos c| = 2)
    (hsilent : ∀ c d, signedPos c < 0 → 0 < signedPos d →
      -signedPos c ≤ 1 ∨ signedPos d ≤ 1) : False := by
  classical
  set posSide := Finset.univ.filter (fun c => 0 < signedPos c) with hposSide
  set negSide := Finset.univ.filter (fun c => signedPos c < 0) with hnegSide
  -- the two signed masses
  set posMass := ∑ c ∈ posSide, weight c * signedPos c with hposMass
  set negMass := ∑ c ∈ negSide, weight c * (-signedPos c) with hnegMass
  -- split the closure sum: terms outside both sides vanish
  have hsplitClosure : posMass - negMass = 0 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun c => 0 < signedPos c) (fun c => weight c * signedPos c)
    have hrest : ∑ c ∈ Finset.univ.filter (fun c => ¬ 0 < signedPos c),
        weight c * signedPos c = -negMass := by
      have hsplitRest := Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun c => ¬ 0 < signedPos c))
        (fun c => signedPos c < 0) (fun c => weight c * signedPos c)
      have hzeroPart : ∑ c ∈ (Finset.univ.filter
          (fun c => ¬ 0 < signedPos c)).filter (fun c => ¬ signedPos c < 0),
          weight c * signedPos c = 0 := by
        refine Finset.sum_eq_zero fun c hc => ?_
        have hmem := Finset.mem_filter.mp hc
        have hnotPos := (Finset.mem_filter.mp hmem.1).2
        have hnotNeg := hmem.2
        have hzero : signedPos c = 0 := le_antisymm
          (not_lt.mp hnotPos) (not_lt.mp hnotNeg)
        rw [hzero, mul_zero]
      have hnegEq : (Finset.univ.filter (fun c => ¬ 0 < signedPos c)).filter
          (fun c => signedPos c < 0) = negSide := by
        rw [hnegSide, Finset.filter_filter]
        refine Finset.filter_congr fun c _ => ?_
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨not_lt.mpr h.le, h⟩
      have hnegSum : ∑ c ∈ negSide, weight c * signedPos c = -negMass := by
        rw [hnegMass, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [hnegEq, hnegSum, hzeroPart, add_zero] at hsplitRest
      exact hsplitRest.symm
    rw [hrest] at hsplit
    rw [← hclosure, ← hsplit, hposMass]
    ring
  -- split the trace sum the same way
  have hsplitTrace : posMass + negMass = 2 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun c => 0 < signedPos c) (fun c => weight c * |signedPos c|)
    have habsPos : ∑ c ∈ posSide, weight c * |signedPos c| = posMass := by
      refine Finset.sum_congr rfl fun c hc => ?_
      have hpos := (Finset.mem_filter.mp hc).2
      rw [abs_of_pos hpos]
    have hrest : ∑ c ∈ Finset.univ.filter (fun c => ¬ 0 < signedPos c),
        weight c * |signedPos c| = negMass := by
      have hsplitRest := Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun c => ¬ 0 < signedPos c))
        (fun c => signedPos c < 0) (fun c => weight c * |signedPos c|)
      have hzeroPart : ∑ c ∈ (Finset.univ.filter
          (fun c => ¬ 0 < signedPos c)).filter (fun c => ¬ signedPos c < 0),
          weight c * |signedPos c| = 0 := by
        refine Finset.sum_eq_zero fun c hc => ?_
        have hmem := Finset.mem_filter.mp hc
        have hzero : signedPos c = 0 := le_antisymm
          (not_lt.mp (Finset.mem_filter.mp hmem.1).2) (not_lt.mp hmem.2)
        rw [hzero, abs_zero, mul_zero]
      have hnegEq : (Finset.univ.filter (fun c => ¬ 0 < signedPos c)).filter
          (fun c => signedPos c < 0) = negSide := by
        rw [hnegSide, Finset.filter_filter]
        refine Finset.filter_congr fun c _ => ?_
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨not_lt.mpr h.le, h⟩
      have hnegSum : ∑ c ∈ negSide, weight c * |signedPos c| = negMass := by
        rw [hnegMass]
        refine Finset.sum_congr rfl fun c hc => ?_
        have hneg := (Finset.mem_filter.mp hc).2
        rw [abs_of_neg hneg]
      rw [hnegEq, hnegSum, hzeroPart, add_zero] at hsplitRest
      exact hsplitRest.symm
    rw [habsPos, hrest] at hsplit
    rw [← htrace, ← hsplit]
  have hposMassOne : posMass = 1 := by linarith
  have hnegMassOne : negMass = 1 := by linarith
  -- each side is nonempty, so each side carries positive weight
  have hnegNonempty : negSide.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hnegMass, hempty, Finset.sum_empty] at hnegMassOne
    norm_num at hnegMassOne
  have hposNonempty : posSide.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hposMass, hempty, Finset.sum_empty] at hposMassOne
    norm_num at hposMassOne
  have hnegWeightPos : 0 < ∑ c ∈ negSide, weight c :=
    Finset.sum_pos (fun c _ => hweightPos c) hnegNonempty
  have hposWeightPos : 0 < ∑ c ∈ posSide, weight c :=
    Finset.sum_pos (fun c _ => hweightPos c) hposNonempty
  -- side weights add to at most one
  have hsideWeights : (∑ c ∈ posSide, weight c) + ∑ c ∈ negSide, weight c
      ≤ 1 := by
    have hdisjoint : Disjoint posSide negSide := by
      rw [Finset.disjoint_left]
      intro c hcPos hcNeg
      have hpos := (Finset.mem_filter.mp hcPos).2
      have hneg := (Finset.mem_filter.mp hcNeg).2
      linarith
    rw [← Finset.sum_union hdisjoint, ← hweightSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun c _ _ => (hweightPos c).le
  -- silence caps one full side at leverage one
  by_cases hdeep : ∃ d ∈ negSide, 1 < -signedPos d
  · -- a deep negative atom caps the whole positive side
    obtain ⟨deepIdx, hdeepMem, hdeepVal⟩ := hdeep
    have hdeepNeg := (Finset.mem_filter.mp hdeepMem).2
    have hcap : ∀ c ∈ posSide, signedPos c ≤ 1 := by
      intro c hc
      have hcPos := (Finset.mem_filter.mp hc).2
      rcases hsilent deepIdx c hdeepNeg hcPos with hleft | hright
      · linarith
      · exact hright
    have hbound : posMass ≤ ∑ c ∈ posSide, weight c := by
      rw [hposMass]
      refine Finset.sum_le_sum fun c hc => ?_
      have hcap' := hcap c hc
      nlinarith [(hweightPos c).le, hcap']
    linarith [hposMassOne, hbound, hsideWeights, hnegWeightPos]
  · -- otherwise the whole negative side is capped
    push_neg at hdeep
    have hbound : negMass ≤ ∑ c ∈ negSide, weight c := by
      rw [hnegMass]
      refine Finset.sum_le_sum fun c hc => ?_
      have hcap := hdeep c hc
      nlinarith [(hweightPos c).le, hcap]
    linarith [hnegMassOne, hbound, hsideWeights, hposWeightPos]

end Gtz

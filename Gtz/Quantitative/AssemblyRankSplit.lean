import Mathlib
import Gtz.Quantitative.FourActiveCoefficientProjection
import Gtz.Quantitative.SixThreeExclusionFrontier
import Gtz.Quantitative.ChartStationaryDesignFreeWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The assembly rank split — the survivor list `(4,2,2)`, `(5,2,3)`, `(5,3,2)`, `(6,3,3)`

The tree already holds every ingredient of the rank split, but not the split.
`Gtz.Quantitative.AssemblyRankFloor` proves the floor `4 ≤ rank Ξ` and re-proves
the corner decomposition INLINE, four separate times, without one reusable
additivity statement.  `Gtz.Quantitative.CapturedRankFloor` proves each corner
has rank at least two.  Nothing states the caps `rank(P Ξ) ≤ 3` and
`rank((1-P) Ξ) ≤ 3`, although each is one containment plus the landed
trace/range identity of an idempotent.  This file extracts the additivity ONCE,
lands the two caps, and closes the case list: a `(6,3)` crux assembly sits at
`(rank Ξ, rank(P Ξ), rank((1-P) Ξ))` equal to `(4,2,2)`, `(5,2,3)`, `(5,3,2)` or
`(6,3,3)`, at EVERY stationary datum the crux produces.

The file also lands the two scalar windows the same package needs.  The captured
trace sits in `1/54 ≤ tr(P Ξ) < 1/6`: the trace law gives `value + 1/6` and the
crux value window gives `-(4/27) ≤ value < 0`.  The shifted weight
`d_y = value + t_y` sits in `[0, 1)`: the floor is unconditional, the strict cap
uses negativity, and the unconditional strict form is REFUTED in
`Gtz.Quantitative.ChartStationaryDesignFreeWindow`, so the sign hypothesis is not
removable.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.finrank_range_eq_captured_add_of_commutes` — **THE ADDITIVITY.**  For an
  idempotent that commutes with a matrix, the matrix's range dimension is the sum
  of the two captured corner dimensions.  Extracted from the four inline copies.
* `Gtz.finrank_range_mul_le_of_idempotent_trace` — the corner cap: a corner's
  range sits inside the idempotent's range, whose dimension IS the trace.
* `Gtz.projectedMultiplier_range_finrank_le_rank` and
  `Gtz.complementProjectedMultiplier_range_finrank_le_corank` — the caps at a
  stationary datum, at every `(size, rank)`.
* `Gtz.SixThreeCrux.multiplierAssembly_rankSplit_survivors` — **THE SURVIVOR
  LIST.**  Four cases and nothing else.
* `Gtz.SixThreeCrux.finrank_range_multiplier_mem_rankWindow` and
  `Gtz.SixThreeCrux.finrank_range_multiplier_eq_four_or_five_or_six` — the rank
  window `[4, 6]` and its trichotomy.
* `Gtz.SixThreeCrux.trace_projection_mul_multiplier_mem_traceWindow` and the
  complement window — `tr(P Ξ) ∈ [1/54, 1/6)` and `tr((1-P) Ξ) ∈ (5/6, 53/54]`.
* `Gtz.SixThreeCrux.value_add_weight_mem_shiftedWindow` — `0 ≤ d_y < 1` at a
  crux datum.
* `Gtz.gtzWeighted_six_three_of_forall_isSixThreeAssemblyRankExcluded` — **THE
  RANK SPINE.**  Three named rungs `4, 5, 6` prove the cell, and
  `Gtz.forall_isSixThreeAssemblyRankExcluded_iff_gtzWeighted_six_three` shows the
  decomposition is LOSSLESS: the conjunction of the three rungs is EQUIVALENT to
  the cell, exactly as the sixteen count rungs are.

## NOT PROVED here, and named

The rungs `Gtz.IsSixThreeAssemblyRankExcluded assemblyRank` for
`assemblyRank = 4, 5, 6` are open.  They are the campaign's three milestones.
The count ladder of `Gtz.Quantitative.SixThreeIndexLadderSpine` stays available
as a verification spine, but the rank spine has THREE rungs against its sixteen.

## Vacuity

Every crux-quantified statement here is vacuous if `Gtz.GtzWeighted 6 3` holds,
for the standard reason: the structure is then empty.  Read a discharged rung as
one of three cases closed, never as evidence about the conjecture.
-/

namespace Gtz

open Matrix

/-! ## The generic corner algebra -/

/-- A corner's range dimension is capped by the idempotent's trace: the corner
factors through the idempotent, and an idempotent's range dimension IS its trace
(`Gtz.trace_eq_finrank_range_of_idempotent`). -/
theorem finrank_range_mul_le_of_idempotent_trace {size : ℕ}
    (projection form : Matrix (Fin size) (Fin size) ℝ) (bound : ℕ)
    (hidempotent : projection * projection = projection)
    (htrace : Matrix.trace projection = (bound : ℝ)) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' (projection * form))) ≤ bound := by
  have hcontain : LinearMap.range (Matrix.toLin' (projection * form))
      ≤ LinearMap.range (Matrix.toLin' projection) := by
    rw [Matrix.toLin'_mul]
    exact LinearMap.range_comp_le_range _ _
  have hidentity := trace_eq_finrank_range_of_idempotent projection hidempotent
  rw [htrace] at hidentity
  have hrankProjection :
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' projection)) = bound := by
    exact_mod_cast hidentity.symm
  calc Module.finrank ℝ (LinearMap.range (Matrix.toLin' (projection * form)))
      ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin' projection)) :=
        Submodule.finrank_mono hcontain
    _ = bound := hrankProjection

/-- **THE EXACT RANGE SPLIT.**  A matrix that commutes with an idempotent has its
range equal to the SUP of the two captured corner ranges: one containment from
`P + (1 - P) = 1`, the other from commutation. -/
theorem range_eq_captured_sup_of_commutes {size : ℕ}
    (projection form : Matrix (Fin size) (Fin size) ℝ)
    (hcommutes : projection * form = form * projection) :
    LinearMap.range (Matrix.toLin' form)
      = LinearMap.range (Matrix.toLin' (projection * form))
        ⊔ LinearMap.range (Matrix.toLin' ((1 - projection) * form)) := by
  have hsum : (projection * form) + ((1 - projection) * form) = form := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  apply le_antisymm
  · intro vector hvector
    rcases hvector with ⟨preimage, hpreimage⟩
    rw [Matrix.toLin'_apply] at hpreimage
    refine Submodule.mem_sup.mpr ⟨(projection * form) *ᵥ preimage,
      LinearMap.mem_range.mpr ⟨preimage, Matrix.toLin'_apply _ _⟩,
      ((1 - projection) * form) *ᵥ preimage,
      LinearMap.mem_range.mpr ⟨preimage, Matrix.toLin'_apply _ _⟩, ?_⟩
    rw [← Matrix.add_mulVec, hsum]
    exact hpreimage
  · refine sup_le ?_ ?_
    · rw [hcommutes, Matrix.toLin'_mul]
      exact LinearMap.range_comp_le_range _ _
    · have hcomplementCommutes : (1 - projection) * form = form * (1 - projection) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hcommutes]
      rw [hcomplementCommutes, Matrix.toLin'_mul]
      exact LinearMap.range_comp_le_range _ _

/-- The two captured corner ranges meet trivially: a common vector is chart-fixed
through one corner and chart-annihilated through the other. -/
theorem disjoint_captured_ranges_of_idempotent {size : ℕ}
    (projection form : Matrix (Fin size) (Fin size) ℝ)
    (hidempotent : projection * projection = projection) :
    Disjoint (LinearMap.range (Matrix.toLin' (projection * form)))
      (LinearMap.range (Matrix.toLin' ((1 - projection) * form))) := by
  have hannihilate : projection * (1 - projection) = (0 : Matrix (Fin size) (Fin size) ℝ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hidempotent, sub_self]
  rw [Submodule.disjoint_def]
  intro vector hprimal hkernel
  rcases hprimal with ⟨primalPreimage, hprimalEq⟩
  rcases hkernel with ⟨kernelPreimage, hkernelEq⟩
  rw [Matrix.toLin'_apply] at hprimalEq hkernelEq
  have hfixed : projection *ᵥ vector = vector := by
    rw [← hprimalEq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hidempotent]
  have hkilled : projection *ᵥ vector = 0 := by
    rw [← hkernelEq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hannihilate,
      Matrix.zero_mul, Matrix.zero_mulVec]
  exact hfixed.symm.trans hkilled

/-- **THE ADDITIVITY.**  For an idempotent that commutes with a matrix, the
matrix's range dimension is EXACTLY the sum of the two captured corner
dimensions.  The four inline copies in `Gtz.Quantitative.AssemblyRankFloor`,
`Gtz.Wave.FourActiveRankSplit` and `Gtz.Wave.PositiveRowSpanRankFloor` prove only
the `≥` half of this statement. -/
theorem finrank_range_eq_captured_add_of_commutes {size : ℕ}
    (projection form : Matrix (Fin size) (Fin size) ℝ)
    (hidempotent : projection * projection = projection)
    (hcommutes : projection * form = form * projection) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' form))
      = Module.finrank ℝ (LinearMap.range (Matrix.toLin' (projection * form)))
        + Module.finrank ℝ (LinearMap.range (Matrix.toLin' ((1 - projection) * form))) := by
  have hsplit := range_eq_captured_sup_of_commutes projection form hcommutes
  have hdisjoint := disjoint_captured_ranges_of_idempotent projection form hidempotent
  have hdimension := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (Matrix.toLin' (projection * form)))
    (LinearMap.range (Matrix.toLin' ((1 - projection) * form)))
  rw [hdisjoint.eq_bot, finrank_bot, add_zero] at hdimension
  rw [hsplit]
  exact hdimension

/-! ## The caps and the split at a stationary datum -/

variable {size : ℕ} {activeIndex : Type*}
variable {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- The primal captured corner never exceeds the chart rank.  The corner factors
through the projection, whose trace is the rank. -/
theorem projectedMultiplier_range_finrank_le_rank
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      (projection * chartMultiplierAssembly activeSet activeWeight tightDir))) ≤ rank :=
  finrank_range_mul_le_of_idempotent_trace projection _ rank hdata.isIdempotent
    hdata.hasTraceRank

/-- The complement captured corner never exceeds the corank `size - rank`.  The
complement is idempotent with trace `size - rank`. -/
theorem complementProjectedMultiplier_range_finrank_le_corank
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hrankLe : rank ≤ size) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir)))
      ≤ size - rank := by
  have hcomplementIdempotent :
      ((1 : Matrix (Fin size) (Fin size) ℝ) - projection)
          * ((1 : Matrix (Fin size) (Fin size) ℝ) - projection)
        = (1 : Matrix (Fin size) (Fin size) ℝ) - projection := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hdata.isIdempotent,
      sub_self, sub_zero]
  have hcomplementTrace :
      Matrix.trace ((1 : Matrix (Fin size) (Fin size) ℝ) - projection)
        = ((size - rank : ℕ) : ℝ) := by
    rw [Matrix.trace_sub, Matrix.trace_one, hdata.hasTraceRank, Nat.cast_sub hrankLe,
      Fintype.card_fin]
  exact finrank_range_mul_le_of_idempotent_trace _ _ (size - rank) hcomplementIdempotent
    hcomplementTrace

/-- **THE RANK SPLIT AT A STATIONARY DATUM.**  Commutation splits the assembly's
rank into the two captured corner ranks, at every `(size, rank)` and every
datum. -/
theorem finrank_range_multiplier_eq_captured_add_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir)))
      = Module.finrank ℝ (LinearMap.range (Matrix.toLin'
          (projection * chartMultiplierAssembly activeSet activeWeight tightDir)))
        + Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir))) :=
  finrank_range_eq_captured_add_of_commutes projection
    (chartMultiplierAssembly activeSet activeWeight tightDir)
    hdata.isIdempotent hdata.assembly_commutes

/-! ## The `(6,3)` crux survivor list -/

namespace SixThreeCrux

variable {activeIndex : Type*}

/-- **THE SURVIVOR LIST.**  At every stationary datum of a `(6,3)` crux the
triple `(rank Ξ, rank(P Ξ), rank((1-P) Ξ))` is `(4,2,2)`, `(5,2,3)`, `(5,3,2)`
or `(6,3,3)`.  Floors from `Gtz.Quantitative.CapturedRankFloor`, caps from the
trace/range identity, additivity from the exact range split. -/
theorem multiplierAssembly_rankSplit_survivors
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir) :
    (Module.finrank ℝ (LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir))) = 4
        ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            ((chartPointOfDesign crux.design).chart
              * chartMultiplierAssembly activeSet activeWeight tightDir))) = 2
        ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            ((1 - (chartPointOfDesign crux.design).chart)
              * chartMultiplierAssembly activeSet activeWeight tightDir))) = 2)
      ∨ (Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            (chartMultiplierAssembly activeSet activeWeight tightDir))) = 5
        ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            ((chartPointOfDesign crux.design).chart
              * chartMultiplierAssembly activeSet activeWeight tightDir))) = 2
        ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            ((1 - (chartPointOfDesign crux.design).chart)
              * chartMultiplierAssembly activeSet activeWeight tightDir))) = 3)
      ∨ (Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            (chartMultiplierAssembly activeSet activeWeight tightDir))) = 5
        ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            ((chartPointOfDesign crux.design).chart
              * chartMultiplierAssembly activeSet activeWeight tightDir))) = 3
        ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            ((1 - (chartPointOfDesign crux.design).chart)
              * chartMultiplierAssembly activeSet activeWeight tightDir))) = 2)
      ∨ (Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            (chartMultiplierAssembly activeSet activeWeight tightDir))) = 6
        ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            ((chartPointOfDesign crux.design).chart
              * chartMultiplierAssembly activeSet activeWeight tightDir))) = 3
        ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            ((1 - (chartPointOfDesign crux.design).chart)
              * chartMultiplierAssembly activeSet activeWeight tightDir))) = 3) := by
  classical
  have hadd := finrank_range_multiplier_eq_captured_add_of_isChartStationaryData hdata
  have hprimalNot := crux.not_projectedMultiplier_range_finrank_le_one hdata
  have hkernelNot := crux.not_complementProjectedMultiplier_range_finrank_le_one hdata
  have hprimalCap := projectedMultiplier_range_finrank_le_rank hdata
  have hkernelCap := complementProjectedMultiplier_range_finrank_le_corank hdata
    (by norm_num)
  omega

/-- **THE RANK WINDOW.**  The assembly rank of a `(6,3)` crux datum sits in
`[4, 6]`. -/
theorem finrank_range_multiplier_mem_rankWindow
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir) :
    4 ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir)))
      ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir))) ≤ 6 := by
  rcases crux.multiplierAssembly_rankSplit_survivors hdata with
    ⟨htotal, -, -⟩ | ⟨htotal, -, -⟩ | ⟨htotal, -, -⟩ | ⟨htotal, -, -⟩ <;> omega

/-- **THE TRICHOTOMY.**  The assembly rank of a `(6,3)` crux datum is four, five
or six. -/
theorem finrank_range_multiplier_eq_four_or_five_or_six
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir))) = 4
      ∨ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir))) = 5
      ∨ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir))) = 6 := by
  rcases crux.multiplierAssembly_rankSplit_survivors hdata with
    ⟨htotal, -, -⟩ | ⟨htotal, -, -⟩ | ⟨htotal, -, -⟩ | ⟨htotal, -, -⟩ <;> omega

/-! ### The scalar windows of the package -/

/-- **THE CAPTURED TRACE WINDOW.**  `tr(P Ξ) = value + 1/6` sits in
`[1/54, 1/6)`: the floor is the crux value window `-(4/27) ≤ value`, the cap is
negativity.  The constant `1/54 = 1/6 - 4/27` appears here for the first time in
the tree. -/
theorem trace_projection_mul_multiplier_mem_traceWindow
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir) :
    (1 / 54 : ℝ) ≤ Matrix.trace ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly activeSet activeWeight tightDir)
      ∧ Matrix.trace ((chartPointOfDesign crux.design).chart
          * chartMultiplierAssembly activeSet activeWeight tightDir) < 1 / 6 := by
  have htrace := trace_projection_mul_multiplier_of_isChartStationaryData hdata
  have hfloor := crux.neg_four_div_twentySeven_le_chartObjective
  have hnegative := crux.hasNegativeChartValue
  have hinv : (((6 : ℕ) : ℝ))⁻¹ = 1 / 6 := by norm_num
  rw [hinv] at htrace
  rw [htrace]
  constructor
  · linarith
  · linarith

/-- **THE COMPLEMENT TRACE WINDOW.**  `tr((1-P) Ξ) = 1 - value - 1/6` sits in
`(5/6, 53/54]`, the Naimark mirror of the captured window. -/
theorem trace_complementProjection_mul_multiplier_mem_traceWindow
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir) :
    (5 / 6 : ℝ) < Matrix.trace ((1 - (chartPointOfDesign crux.design).chart)
        * chartMultiplierAssembly activeSet activeWeight tightDir)
      ∧ Matrix.trace ((1 - (chartPointOfDesign crux.design).chart)
          * chartMultiplierAssembly activeSet activeWeight tightDir) ≤ 53 / 54 := by
  have htrace := trace_complementProjection_mul_multiplier_of_isChartStationaryData hdata
  have hfloor := crux.neg_four_div_twentySeven_le_chartObjective
  have hnegative := crux.hasNegativeChartValue
  have hinv : (((6 : ℕ) : ℝ))⁻¹ = 1 / 6 := by norm_num
  rw [hinv] at htrace
  rw [htrace]
  constructor
  · linarith
  · linarith

/-- **THE SHIFTED-WEIGHT WINDOW.**  Every shifted weight `d_y = value + t_y` of a
crux datum sits in `[0, 1)`.  The floor is unconditional at every datum; the
strict cap consumes the crux's negativity, and the unconditional strict form is
refuted (`Gtz.not_forall_value_add_weight_lt_one_of_isChartStationaryData`), so
the sign hypothesis is not removable. -/
theorem value_add_weight_mem_shiftedWindow
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (atomIndex : Fin 6) :
    0 ≤ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex
      ∧ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex < 1 := by
  refine ⟨?_, value_add_weight_lt_one_of_isChartStationaryData_of_neg hdata
    crux.hasNegativeChartValue atomIndex⟩
  have hfloor := weight_ge_neg_value_of_isChartStationaryData hdata atomIndex
  linarith

end SixThreeCrux

/-! ## The rank spine — three named rungs against the count ladder's sixteen -/

/-- **A RUNG OF THE RANK SPINE.**  No `(6,3)` counterexample carries a stationary
datum whose assembly has range dimension `assemblyRank`.  The three instances
`assemblyRank = 4, 5, 6` are the whole residual of this route, by
`Gtz.SixThreeCrux.finrank_range_multiplier_eq_four_or_five_or_six`.

VACUOUS if `Gtz.GtzWeighted 6 3` holds — see
`Gtz.forall_isSixThreeAssemblyRankExcluded_iff_gtzWeighted_six_three`. -/
def IsSixThreeAssemblyRankExcluded (assemblyRank : ℕ) : Prop :=
  ∀ (crux : SixThreeCrux) (activeIndex : Type) (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin 6)) (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → Fin 6 → ℝ),
    IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir →
    Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      (chartMultiplierAssembly activeSet activeWeight tightDir))) ≠ assemblyRank

/-- Every assembly rank below four is excluded outright, by the landed floor. -/
theorem isSixThreeAssemblyRankExcluded_of_lt_four (assemblyRank : ℕ)
    (hsmall : assemblyRank < 4) : IsSixThreeAssemblyRankExcluded assemblyRank := by
  intro crux activeIndex activeSet activeSubset activeWeight tightDir hdata hequal
  have hfloor := crux.four_le_finrank_range_multiplier hdata
  omega

/-- Every assembly rank above six is excluded outright, by the two corner caps. -/
theorem isSixThreeAssemblyRankExcluded_of_six_lt (assemblyRank : ℕ)
    (hlarge : 6 < assemblyRank) : IsSixThreeAssemblyRankExcluded assemblyRank := by
  intro crux activeIndex activeSet activeSubset activeWeight tightDir hdata hequal
  obtain ⟨-, hceiling⟩ := crux.finrank_range_multiplier_mem_rankWindow hdata
  omega

/-- Excluding the three surviving assembly ranks leaves a counterexample with no
datum to sit at — but every crux carries a datum. -/
theorem false_of_sixThreeCrux_of_forall_isSixThreeAssemblyRankExcluded
    (hladder : ∀ assemblyRank : ℕ, 4 ≤ assemblyRank → assemblyRank ≤ 6 →
      IsSixThreeAssemblyRankExcluded assemblyRank)
    (crux : SixThreeCrux) : False := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  obtain ⟨hfloor, hceiling⟩ := crux.finrank_range_multiplier_mem_rankWindow hdata
  exact hladder _ hfloor hceiling crux (Finset (Fin 6)) _ _ multiplier selection hdata rfl

/-- **THE RANK SPINE.**  Three rungs `4, 5, 6` prove the cell. -/
theorem gtzWeighted_six_three_of_forall_isSixThreeAssemblyRankExcluded
    (hladder : ∀ assemblyRank : ℕ, 4 ≤ assemblyRank → assemblyRank ≤ 6 →
      IsSixThreeAssemblyRankExcluded assemblyRank) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_isEmpty_sixThreeCrux
    ⟨false_of_sixThreeCrux_of_forall_isSixThreeAssemblyRankExcluded hladder⟩

/-- **THE RANK-THREE PAYOFF.**  Three rungs close rank three at every size,
through the landed `Gtz.gtzWeightedAll_three_of_six_three`. -/
theorem gtzWeightedAll_three_of_forall_isSixThreeAssemblyRankExcluded
    (hladder : ∀ assemblyRank : ℕ, 4 ≤ assemblyRank → assemblyRank ≤ 6 →
      IsSixThreeAssemblyRankExcluded assemblyRank) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_forall_isSixThreeAssemblyRankExcluded hladder)

/-- **THE DECOMPOSITION IS LOSSLESS, AND THEREFORE BUYS NOTHING BY ITSELF.**  The
conjunction of the three rungs is EQUIVALENT to the cell, exactly as the sixteen
count rungs are.  What the rank spine buys is a residual of THREE named cases in
place of sixteen, with the count ladder available inside each case. -/
theorem forall_isSixThreeAssemblyRankExcluded_iff_gtzWeighted_six_three :
    (∀ assemblyRank : ℕ, 4 ≤ assemblyRank → assemblyRank ≤ 6 →
      IsSixThreeAssemblyRankExcluded assemblyRank)
      ↔ GtzWeighted 6 3 := by
  constructor
  · exact gtzWeighted_six_three_of_forall_isSixThreeAssemblyRankExcluded
  · intro hcell assemblyRank _ _ crux
    exact absurd hcell (not_gtzWeighted_six_three_of_sixThreeCrux crux)

end Gtz

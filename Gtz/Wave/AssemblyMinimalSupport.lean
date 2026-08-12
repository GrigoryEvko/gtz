import Gtz.Wave.StationaryPositiveSupport
import Gtz.Quantitative.SixThreeCrux
import Gtz.Ties.ConicCaratheodory

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The support-minimal stationary multiplier — independent constraint columns

A stationary datum fixes the assembly `Ξ = Σ_C μ_C q_C q_Cᵀ`, but the
multiplier vector `μ` is not unique: any linear relation among the rank-one
matrices `q_C q_Cᵀ` over the positive support is a slide direction that keeps
`Ξ` LITERALLY UNCHANGED.  The trace pins the budget — every active `q_C` is a
unit vector, so a relation has coefficient sum zero and carries both signs —
and one slide along it zeroes a positive multiplier without a sign violation.
Iterate: every datum reduces to one whose positive-support rank-one matrices
are LINEARLY INDEPENDENT, with the same assembly and every other field intact.

The independent objects are the CONSTRAINT COLUMNS `q_C q_Cᵀ`, not the tight
directions `q_C`.  Independence of the matrices does not give independence of
the vectors, and no statement here claims it — this is the distinction the
campaign brief demands, made formal by the statement shape.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.mem_positiveActiveSet` and `Gtz.positiveActiveSet_subset_activeSet` —
  the two membership utilities the positive-support file left implicit.
* `Gtz.exists_relation_of_not_linearIndependent_on` — a dependent finite
  family carries a relation supported on the given finset.  The finset form of
  `Gtz.exists_relation_of_finrank_lt_card`, triggered by dependence instead of
  by count.
* `Gtz.trace_atomMatrix_tightDir_eq_one` and
  `Gtz.sum_relation_eq_zero_of_relation_atomMatrix` — **THE TRACE BUDGET.**  A
  relation among positive atom matrices has coefficient sum zero, so it carries
  both signs and every slide terminates on the orthant boundary.
* `Gtz.exists_slid_weight_of_dependent_positive_support` — **ONE SLIDE.**  A
  dependent positive support yields a new multiplier with the same assembly,
  all thirteen fields, and a strictly smaller positive support.
* `Gtz.exists_isChartStationaryData_independent_positive_support` — **THE
  SUPPORT-MINIMAL MULTIPLIER.**  Every stationary datum admits a multiplier
  with the same assembly whose positive-support atom matrices are linearly
  independent.  At every `(size, rank)`, with no crux hypothesis.
* `Gtz.SixThreeCrux.exists_multiplier_isChartStationaryData_independent_positive_support`
  — the crux instance: a `(6,3)` counterexample carries a stationary datum
  with independent positive constraint columns.

## What this buys the rank split

Under independence the positive support size EQUALS the dimension of the span
of the constraint columns.  The columns live inside the symmetric matrices
carried by `range Ξ`, so the campaign's `|S| ≤ r(r+1)/2` cap becomes a span
computation over the rank-split survivor list — the next brick, not this one.

## Vacuity

The crux instance is vacuous if `Gtz.GtzWeighted 6 3` holds.  The generic
theorems are not: they hold at every stationary datum, including the landed
tetrahedron and octahedron witnesses.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## Membership utilities for the positive support -/

/-- Membership in the positive support, unfolded. -/
theorem mem_positiveActiveSet {index : activeIndex} :
    index ∈ positiveActiveSet activeSet activeWeight
      ↔ index ∈ activeSet ∧ 0 < activeWeight index := by
  rw [positiveActiveSet, Finset.mem_filter]

/-- The positive support sits inside the active family. -/
theorem positiveActiveSet_subset_activeSet :
    positiveActiveSet activeSet activeWeight ⊆ activeSet :=
  Finset.filter_subset _ _

/-! ## The relation extraction and the trace budget -/

/-- A dependent finite family carries a relation supported on the given finset:
zero off the finset, vanishing combination, and a nonzero witness inside. -/
theorem exists_relation_of_not_linearIndependent_on
    {space : Type*} [AddCommGroup space] [Module ℝ space] {label : Type*}
    (vector : label → space) (support : Finset label)
    (hdependent : ¬ LinearIndependent ℝ
      (fun index : {index // index ∈ support} => vector index.1)) :
    ∃ relation : label → ℝ, (∀ index, index ∉ support → relation index = 0)
      ∧ (∑ index ∈ support, relation index • vector index = 0)
      ∧ ∃ witness ∈ support, relation witness ≠ 0 := by
  classical
  obtain ⟨relationOnSupport, hrelationSum, witness, hwitnessNe⟩ :=
    Fintype.not_linearIndependent_iff.mp hdependent
  refine ⟨fun index => if hmem : index ∈ support then relationOnSupport ⟨index, hmem⟩ else 0,
    fun index hout => dif_neg hout, ?_, witness.1, witness.2, ?_⟩
  · rw [← Finset.sum_attach support (fun index =>
      (if hmem : index ∈ support then relationOnSupport ⟨index, hmem⟩ else 0) • vector index),
      ← hrelationSum, Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun subtypeIndex _ => ?_
    simp only [dif_pos subtypeIndex.2, Subtype.coe_eta]
  · simpa only [dif_pos witness.2, Subtype.coe_eta] using hwitnessNe

/-- The atom matrix of an active tight direction has trace one: the direction
is a unit vector, and the trace of `q qᵀ` is the leverage `|q|²`. -/
theorem trace_atomMatrix_tightDir_eq_one
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {index : activeIndex} (hmem : index ∈ activeSet) :
    Matrix.trace (atomMatrix (tightDir index)) = 1 := by
  rw [trace_atomMatrix]
  have hunit := hdata.tightDir_unit index hmem
  rw [dotProduct] at hunit
  rw [leverageOf, ← hunit]
  exact Finset.sum_congr rfl fun coordinate _ => pow_two (tightDir index coordinate)

/-- **THE TRACE BUDGET.**  A relation among the positive-support atom matrices
has coefficient sum zero: apply the trace, and every unit direction contributes
its coefficient exactly. -/
theorem sum_relation_eq_zero_of_relation_atomMatrix
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (relation : activeIndex → ℝ)
    (hrelationSum : ∑ index ∈ positiveActiveSet activeSet activeWeight,
      relation index • atomMatrix (tightDir index) = 0) :
    ∑ index ∈ positiveActiveSet activeSet activeWeight, relation index = 0 := by
  have htrace := congrArg Matrix.trace hrelationSum
  rw [Matrix.trace_sum, Matrix.trace_zero] at htrace
  rw [← htrace]
  refine Finset.sum_congr rfl fun index hmem => ?_
  rw [Matrix.trace_smul,
    trace_atomMatrix_tightDir_eq_one hdata (positiveActiveSet_subset_activeSet hmem),
    smul_eq_mul, mul_one]

/-! ## One slide -/

/-- **ONE SLIDE.**  If the positive-support atom matrices of a stationary datum
are dependent, a slide along the relation produces a new multiplier with the
same assembly, all thirteen fields, and a STRICTLY SMALLER positive support.
The trace budget supplies the negative direction entry, and the orthant
boundary supplies the pivot. -/
theorem exists_slid_weight_of_dependent_positive_support
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hnonneg : ∀ index, 0 ≤ activeWeight index)
    (hdependent : ¬ LinearIndependent ℝ
      (fun index : {index // index ∈ positiveActiveSet activeSet activeWeight} =>
        atomMatrix (tightDir index.1))) :
    ∃ slidWeight : activeIndex → ℝ,
      (∀ index, 0 ≤ slidWeight index)
      ∧ IsChartStationaryData rank projection weight value activeSet activeSubset
          slidWeight tightDir
      ∧ chartMultiplierAssembly activeSet slidWeight tightDir
          = chartMultiplierAssembly activeSet activeWeight tightDir
      ∧ (positiveActiveSet activeSet slidWeight).card
          < (positiveActiveSet activeSet activeWeight).card := by
  classical
  obtain ⟨relation, hrelationOff, hrelationSum, witness, hwitnessMem, hwitnessNe⟩ :=
    exists_relation_of_not_linearIndependent_on
      (fun index => atomMatrix (tightDir index))
      (positiveActiveSet activeSet activeWeight) hdependent
  have hsubset : positiveActiveSet activeSet activeWeight ⊆ activeSet :=
    positiveActiveSet_subset_activeSet
  have htraceZero : ∑ index ∈ positiveActiveSet activeSet activeWeight, relation index = 0 :=
    sum_relation_eq_zero_of_relation_atomMatrix hdata relation hrelationSum
  have hnegativeExists :
      ∃ index ∈ positiveActiveSet activeSet activeWeight, relation index < 0 := by
    by_contra hnone
    push Not at hnone
    have hallZero := (Finset.sum_eq_zero_iff_of_nonneg
      fun index hmem => hnone index hmem).mp htraceZero
    exact hwitnessNe (hallZero witness hwitnessMem)
  obtain ⟨step, pivot, hstepNonneg, hpivotMem, hpivotZero, hshiftedNonneg⟩ :=
    exists_step_zeroing_one_label activeWeight relation
      (positiveActiveSet activeSet activeWeight) hnonneg hrelationOff hnegativeExists
  obtain ⟨slidWeight, hslidDef⟩ :
      ∃ slidWeight : activeIndex → ℝ,
        slidWeight = fun index => activeWeight index + step * relation index := ⟨_, rfl⟩
  have hslidNonneg : ∀ index, 0 ≤ slidWeight index := by
    intro index
    rw [hslidDef]
    exact hshiftedNonneg index
  have hslidPivotZero : slidWeight pivot = 0 := by
    rw [hslidDef]
    exact hpivotZero
  have hrelationActiveSum :
      ∑ index ∈ activeSet, relation index • atomMatrix (tightDir index) = 0 := by
    rw [← Finset.sum_subset hsubset (fun index _ hnotMem => by
      rw [hrelationOff index hnotMem, zero_smul])]
    exact hrelationSum
  have hrelationActiveScalar : ∑ index ∈ activeSet, relation index = 0 := by
    rw [← Finset.sum_subset hsubset (fun index _ hnotMem => hrelationOff index hnotMem)]
    exact htraceZero
  have hassemblyEq : chartMultiplierAssembly activeSet slidWeight tightDir
      = chartMultiplierAssembly activeSet activeWeight tightDir := by
    unfold chartMultiplierAssembly
    have hsplit : ∀ index ∈ activeSet,
        slidWeight index • atomMatrix (tightDir index)
          = activeWeight index • atomMatrix (tightDir index)
            + step • (relation index • atomMatrix (tightDir index)) := by
      intro index _
      rw [hslidDef]
      simp only [add_smul, smul_smul]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.smul_sum,
      hrelationActiveSum, smul_zero, add_zero]
  have hslidSumOne : ∑ index ∈ activeSet, slidWeight index = 1 := by
    have hsplit : ∀ index ∈ activeSet,
        slidWeight index = activeWeight index + step * relation index := by
      intro index _
      rw [hslidDef]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum,
      hrelationActiveScalar, mul_zero, add_zero]
    exact hdata.activeWeight_sum_one
  have hslidData : IsChartStationaryData rank projection weight value activeSet activeSubset
      slidWeight tightDir :=
    ⟨hdata.isSymmetric, hdata.isIdempotent, hdata.hasTraceRank, hdata.weight_pos,
      hdata.weight_sum_one, fun index _ => hslidNonneg index, hslidSumOne,
      hdata.activeSubset_card, hdata.tightDir_unit, hdata.tightDir_support,
      hdata.tightDir_isTight,
      fun atomIndex => by rw [hassemblyEq]; exact hdata.assembly_diagonal atomIndex,
      by rw [hassemblyEq]; exact hdata.assembly_commutes⟩
  have hsupportSubset : positiveActiveSet activeSet slidWeight
      ⊆ (positiveActiveSet activeSet activeWeight).erase pivot := by
    intro index hmem
    obtain ⟨hmemActive, hposSlid⟩ := mem_positiveActiveSet.mp hmem
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hcontra
      rw [hcontra, hslidPivotZero] at hposSlid
      exact lt_irrefl 0 hposSlid
    · by_contra hnotMem
      have hweightZero : activeWeight index = 0 := by
        have hnotPos : ¬ 0 < activeWeight index := fun hpos =>
          hnotMem (mem_positiveActiveSet.mpr ⟨hmemActive, hpos⟩)
        exact le_antisymm (not_lt.mp hnotPos) (hnonneg index)
      have hrelationZero : relation index = 0 := hrelationOff index hnotMem
      rw [hslidDef] at hposSlid
      simp only [hweightZero, hrelationZero, mul_zero, add_zero] at hposSlid
      exact lt_irrefl 0 hposSlid
  refine ⟨slidWeight, hslidNonneg, hslidData, hassemblyEq, ?_⟩
  have hcardLe := Finset.card_le_card hsupportSubset
  have hcardErase := Finset.card_erase_of_mem hpivotMem
  have hcardPos : 1 ≤ (positiveActiveSet activeSet activeWeight).card :=
    Finset.card_pos.mpr ⟨pivot, hpivotMem⟩
  omega

/-! ## The pivot loop and the support-minimal multiplier -/

/-- The pivot loop, with the positive-support cardinality as the termination
measure. -/
private theorem exists_independent_slide_aux :
    ∀ (fuel : ℕ) (currentWeight : activeIndex → ℝ),
      (positiveActiveSet activeSet currentWeight).card ≤ fuel →
      (∀ index, 0 ≤ currentWeight index) →
      IsChartStationaryData rank projection weight value activeSet activeSubset
        currentWeight tightDir →
      ∃ reducedWeight : activeIndex → ℝ,
        (∀ index, 0 ≤ reducedWeight index)
        ∧ IsChartStationaryData rank projection weight value activeSet activeSubset
            reducedWeight tightDir
        ∧ chartMultiplierAssembly activeSet reducedWeight tightDir
            = chartMultiplierAssembly activeSet currentWeight tightDir
        ∧ LinearIndependent ℝ
            (fun index : {index // index ∈ positiveActiveSet activeSet reducedWeight} =>
              atomMatrix (tightDir index.1)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro currentWeight hcard hnonneg hdata
      have hempty : positiveActiveSet activeSet currentWeight = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      haveI hisEmpty : IsEmpty {index // index ∈ positiveActiveSet activeSet currentWeight} :=
        ⟨fun index => Finset.notMem_empty index.1 (hempty ▸ index.2)⟩
      exact ⟨currentWeight, hnonneg, hdata, rfl, linearIndependent_empty_type⟩
  | succ previousFuel inductiveStep =>
      intro currentWeight hcard hnonneg hdata
      by_cases hindependent : LinearIndependent ℝ
        (fun index : {index // index ∈ positiveActiveSet activeSet currentWeight} =>
          atomMatrix (tightDir index.1))
      · exact ⟨currentWeight, hnonneg, hdata, rfl, hindependent⟩
      obtain ⟨slidWeight, hslidNonneg, hslidData, hslidAssembly, hslidCard⟩ :=
        exists_slid_weight_of_dependent_positive_support hdata hnonneg hindependent
      obtain ⟨reducedWeight, hreducedNonneg, hreducedData, hreducedAssembly, hreducedFree⟩ :=
        inductiveStep slidWeight (by omega) hslidNonneg hslidData
      exact ⟨reducedWeight, hreducedNonneg, hreducedData,
        hreducedAssembly.trans hslidAssembly, hreducedFree⟩

/-- **THE SUPPORT-MINIMAL MULTIPLIER.**  Every stationary datum admits a
multiplier with the SAME assembly whose positive-support atom matrices are
linearly independent — at every `(size, rank)`, with every other component of
the datum unchanged.  The independence is among the constraint columns
`q_C q_Cᵀ`, NOT among the tight directions `q_C`. -/
theorem exists_isChartStationaryData_independent_positive_support
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∃ reducedWeight : activeIndex → ℝ,
      IsChartStationaryData rank projection weight value activeSet activeSubset
        reducedWeight tightDir
      ∧ chartMultiplierAssembly activeSet reducedWeight tightDir
          = chartMultiplierAssembly activeSet activeWeight tightDir
      ∧ LinearIndependent ℝ
          (fun index : {index // index ∈ positiveActiveSet activeSet reducedWeight} =>
            atomMatrix (tightDir index.1)) := by
  classical
  obtain ⟨clampedWeight, hclampedDef⟩ :
      ∃ clampedWeight : activeIndex → ℝ,
        clampedWeight = fun index => if index ∈ activeSet then activeWeight index else 0 :=
    ⟨_, rfl⟩
  have hclampedOn : ∀ index ∈ activeSet, clampedWeight index = activeWeight index := by
    intro index hmem
    rw [hclampedDef]
    exact if_pos hmem
  have hclampedNonneg : ∀ index, 0 ≤ clampedWeight index := by
    intro index
    simp only [hclampedDef]
    by_cases hmem : index ∈ activeSet
    · simp only [if_pos hmem]
      exact hdata.activeWeight_nonneg index hmem
    · simp only [if_neg hmem, le_refl]
  have hclampedAssembly : chartMultiplierAssembly activeSet clampedWeight tightDir
      = chartMultiplierAssembly activeSet activeWeight tightDir := by
    unfold chartMultiplierAssembly
    exact Finset.sum_congr rfl fun index hmem => by rw [hclampedOn index hmem]
  have hclampedSum : ∑ index ∈ activeSet, clampedWeight index = 1 := by
    rw [Finset.sum_congr rfl hclampedOn]
    exact hdata.activeWeight_sum_one
  have hclampedData : IsChartStationaryData rank projection weight value activeSet
      activeSubset clampedWeight tightDir :=
    ⟨hdata.isSymmetric, hdata.isIdempotent, hdata.hasTraceRank, hdata.weight_pos,
      hdata.weight_sum_one, fun index _ => hclampedNonneg index, hclampedSum,
      hdata.activeSubset_card, hdata.tightDir_unit, hdata.tightDir_support,
      hdata.tightDir_isTight,
      fun atomIndex => by rw [hclampedAssembly]; exact hdata.assembly_diagonal atomIndex,
      by rw [hclampedAssembly]; exact hdata.assembly_commutes⟩
  obtain ⟨reducedWeight, -, hreducedData, hreducedAssembly, hreducedFree⟩ :=
    exists_independent_slide_aux (positiveActiveSet activeSet clampedWeight).card
      clampedWeight le_rfl hclampedNonneg hclampedData
  exact ⟨reducedWeight, hreducedData, hreducedAssembly.trans hclampedAssembly, hreducedFree⟩

/-! ## The crux instance -/

/-- **THE CRUX CARRIES A SUPPORT-MINIMAL DATUM.**  A `(6,3)` counterexample
carries a stationary datum at its argmax family whose positive-support
constraint columns are linearly independent. -/
theorem SixThreeCrux.exists_multiplier_isChartStationaryData_independent_positive_support
    (crux : SixThreeCrux) :
    ∃ (multiplier : Finset (Fin 6) → ℝ) (selection : Finset (Fin 6) → (Fin 6 → ℝ)),
      IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design))
        (chartArgmaxFamily (chartPointOfDesign crux.design))
        (id : Finset (Fin 6) → Finset (Fin 6)) multiplier selection
      ∧ LinearIndependent ℝ
          (fun index : {index // index ∈ positiveActiveSet
            (chartArgmaxFamily (chartPointOfDesign crux.design)) multiplier} =>
            atomMatrix (selection index.1)) := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  obtain ⟨reducedWeight, hreducedData, -, hreducedFree⟩ :=
    exists_isChartStationaryData_independent_positive_support hdata
  exact ⟨reducedWeight, selection, hreducedData, hreducedFree⟩

end Gtz

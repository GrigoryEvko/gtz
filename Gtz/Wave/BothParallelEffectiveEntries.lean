import Gtz.Wave.BothParallelCollapseSupply

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The both-parallel effective entries — the decomposition readers

The diagonal core writes the assembly as a finite sum of weighted atom
matrices.  This module supplies the generic entry readers of any such
decomposition: the diagonal read and the commutation entry.  The module
also extends the diagonal core with one extra parallel class: the
circuit branch carries the four basis classes plus the circuit class.

The chain:

1. A decomposition entry is a coefficient sum of coordinate products.
2. The commutation entry of the chart against a decomposed assembly
   collapses to the projected-column sum on each side.
3. Two circuit directions are parallel, because the singular pair block
   has a one-dimensional kernel.
4. The class partition with the extra class prices the assembly as the
   effective diagonal plus the circuit mass.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.decomposition_diagonal_read` — the diagonal read.
* `Gtz.decomposition_commutation_entry` — **THE COMMUTATION READER.**
* `Gtz.circuit_direction_parallel` — the circuit kernel line.
* `Gtz.extraClass`, `Gtz.extraMass` — the circuit class.
* `Gtz.assembly_eq_effective_diagonal_with_extra` — **THE FIVE-CLASS
  CORE.**

## Vacuity

Nothing here quantifies over a crux.  Every statement holds at each
stationary datum with the stated hypotheses.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the generic decomposition readers -/

/-- The entry of a weighted atom-matrix sum is the coefficient sum of the
coordinate products. -/
theorem decomposition_apply {termCount : ℕ} (coef : Fin termCount → ℝ)
    (vec : Fin termCount → (Fin size → ℝ)) (atomRow atomCol : Fin size) :
    (∑ termIndex, coef termIndex • atomMatrix (vec termIndex)) atomRow atomCol
      = ∑ termIndex, coef termIndex
          * (vec termIndex atomRow * vec termIndex atomCol) := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul]

/-- **THE DIAGONAL READ.**  A decomposed assembly prices each diagonal
atom at the inverse size. -/
theorem decomposition_diagonal_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {termCount : ℕ} {coef : Fin termCount → ℝ}
    {vec : Fin termCount → (Fin size → ℝ)}
    (hdecomp : chartMultiplierAssembly activeSet activeWeight tightDir
      = ∑ termIndex, coef termIndex • atomMatrix (vec termIndex))
    (atomIndex : Fin size) :
    ∑ termIndex, coef termIndex * vec termIndex atomIndex ^ 2
      = ((size : ℝ))⁻¹ := by
  have happ := congrFun (congrFun hdecomp atomIndex) atomIndex
  rw [hdata.assembly_diagonal atomIndex,
    decomposition_apply coef vec atomIndex atomIndex] at happ
  calc ∑ termIndex, coef termIndex * vec termIndex atomIndex ^ 2
      = ∑ termIndex, coef termIndex
          * (vec termIndex atomIndex * vec termIndex atomIndex) :=
        Finset.sum_congr rfl fun termIndex _ => by ring
    _ = ((size : ℝ))⁻¹ := happ.symm

/-- **THE COMMUTATION READER.**  The commutation entry of the chart
against a decomposed assembly collapses to the coefficient sum of the
projected-column products. -/
theorem decomposition_commutation_entry
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {termCount : ℕ} {coef : Fin termCount → ℝ}
    {vec : Fin termCount → (Fin size → ℝ)}
    (hdecomp : chartMultiplierAssembly activeSet activeWeight tightDir
      = ∑ termIndex, coef termIndex • atomMatrix (vec termIndex))
    (atomRow atomCol : Fin size) :
    ∑ termIndex, coef termIndex
        * ((projection *ᵥ vec termIndex) atomRow * vec termIndex atomCol
          - vec termIndex atomRow * (projection *ᵥ vec termIndex) atomCol)
      = 0 := by
  classical
  have hcommute := congrFun (congrFun hdata.assembly_commutes atomRow) atomCol
  rw [Matrix.mul_apply, Matrix.mul_apply] at hcommute
  have hleftSum : ∑ atomMid, projection atomRow atomMid
        * chartMultiplierAssembly activeSet activeWeight tightDir
            atomMid atomCol
      = ∑ termIndex, coef termIndex
          * ((projection *ᵥ vec termIndex) atomRow
            * vec termIndex atomCol) := by
    calc ∑ atomMid, projection atomRow atomMid
          * chartMultiplierAssembly activeSet activeWeight tightDir
              atomMid atomCol
        = ∑ atomMid, ∑ termIndex, projection atomRow atomMid
            * (coef termIndex
              * (vec termIndex atomMid * vec termIndex atomCol)) := by
          refine Finset.sum_congr rfl fun atomMid _ => ?_
          rw [congrFun (congrFun hdecomp atomMid) atomCol,
            decomposition_apply coef vec atomMid atomCol, Finset.mul_sum]
      _ = ∑ termIndex, ∑ atomMid, projection atomRow atomMid
            * (coef termIndex
              * (vec termIndex atomMid * vec termIndex atomCol)) :=
          Finset.sum_comm
      _ = ∑ termIndex, coef termIndex
            * ((projection *ᵥ vec termIndex) atomRow
              * vec termIndex atomCol) := by
          refine Finset.sum_congr rfl fun termIndex _ => ?_
          simp only [Matrix.mulVec, dotProduct, Finset.sum_mul,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun atomMid _ => ?_
          ring
  have hrightSum : ∑ atomMid, chartMultiplierAssembly activeSet activeWeight
        tightDir atomRow atomMid * projection atomMid atomCol
      = ∑ termIndex, coef termIndex
          * (vec termIndex atomRow
            * (projection *ᵥ vec termIndex) atomCol) := by
    calc ∑ atomMid, chartMultiplierAssembly activeSet activeWeight tightDir
          atomRow atomMid * projection atomMid atomCol
        = ∑ atomMid, ∑ termIndex, coef termIndex
            * (vec termIndex atomRow * vec termIndex atomMid)
            * projection atomMid atomCol := by
          refine Finset.sum_congr rfl fun atomMid _ => ?_
          rw [congrFun (congrFun hdecomp atomRow) atomMid,
            decomposition_apply coef vec atomRow atomMid, Finset.sum_mul]
      _ = ∑ termIndex, ∑ atomMid, coef termIndex
            * (vec termIndex atomRow * vec termIndex atomMid)
            * projection atomMid atomCol := Finset.sum_comm
      _ = ∑ termIndex, coef termIndex
            * (vec termIndex atomRow
              * (projection *ᵥ vec termIndex) atomCol) := by
          refine Finset.sum_congr rfl fun termIndex _ => ?_
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun atomMid _ => ?_
          rw [projection_entry_symm hdata atomMid atomCol]
          ring
  rw [hleftSum, hrightSum] at hcommute
  calc ∑ termIndex, coef termIndex
        * ((projection *ᵥ vec termIndex) atomRow * vec termIndex atomCol
          - vec termIndex atomRow * (projection *ᵥ vec termIndex) atomCol)
      = ∑ termIndex, (coef termIndex
          * ((projection *ᵥ vec termIndex) atomRow * vec termIndex atomCol)
        - coef termIndex
          * (vec termIndex atomRow
            * (projection *ᵥ vec termIndex) atomCol)) := by
        refine Finset.sum_congr rfl fun termIndex _ => ?_
        ring
    _ = 0 := by
        rw [Finset.sum_sub_distrib, hcommute, sub_self]

/-! ## Layer 2 — the circuit kernel line -/

/-- **THE CIRCUIT KERNEL LINE.**  Two pair-supported directions alive at
the first pair atom are parallel: the shifted pair block is singular
with a one-dimensional kernel. -/
theorem circuit_direction_parallel
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {labelOne labelTwo : activeIndex}
    (hmemOne : labelOne ∈ activeSet) (hmemTwo : labelTwo ∈ activeSet)
    {atomB atomD : Fin size} (hBD : atomB ≠ atomD)
    (hsuppOne : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      tightDir labelOne atomIndex = 0)
    (hsuppTwo : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      tightDir labelTwo atomIndex = 0)
    (honeB : tightDir labelOne atomB ≠ 0)
    (htwoB : tightDir labelTwo atomB ≠ 0)
    (hshift : chartStationaryGap projection weight atomB atomB - value ≠ 0) :
    ∃ scal : ℝ, tightDir labelTwo = scal • tightDir labelOne := by
  have hmemBOne : atomB ∈ activeSubset labelOne := by
    by_contra hnot
    exact honeB (hdata.tightDir_support labelOne hmemOne atomB hnot)
  have hmemBTwo : atomB ∈ activeSubset labelTwo := by
    by_contra hnot
    exact htwoB (hdata.tightDir_support labelTwo hmemTwo atomB hnot)
  have hrowOne := gap_row_eigen_pair hdata hmemOne hmemBOne hBD hsuppOne
  have hrowTwo := gap_row_eigen_pair hdata hmemTwo hmemBTwo hBD hsuppTwo
  have hcrossNe : chartStationaryGap projection weight atomB atomD ≠ 0 := by
    intro hzero
    have honeD : (chartStationaryGap projection weight atomB atomB
        - value) * tightDir labelOne atomB = 0 := by
      rw [hzero] at hrowOne
      linear_combination hrowOne
    rcases mul_eq_zero.mp honeD with hcase | hcase
    · exact hshift hcase
    · exact honeB hcase
  have hdet : tightDir labelOne atomB * tightDir labelTwo atomD
      - tightDir labelTwo atomB * tightDir labelOne atomD = 0 := by
    have hker : chartStationaryGap projection weight atomB atomD
        * (tightDir labelOne atomB * tightDir labelTwo atomD
          - tightDir labelTwo atomB * tightDir labelOne atomD) = 0 := by
      linear_combination tightDir labelOne atomB * hrowTwo
        - tightDir labelTwo atomB * hrowOne
    rcases mul_eq_zero.mp hker with hcase | hcase
    · exact absurd hcase hcrossNe
    · exact hcase
  refine ⟨tightDir labelTwo atomB / tightDir labelOne atomB, ?_⟩
  funext atomIndex
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hcaseB : atomIndex = atomB
  · rw [hcaseB, div_mul_cancel₀ _ honeB]
  by_cases hcaseD : atomIndex = atomD
  · rw [hcaseD, div_mul_eq_mul_div, eq_div_iff honeB]
    linear_combination hdet
  · rw [hsuppOne atomIndex hcaseB hcaseD, hsuppTwo atomIndex hcaseB hcaseD]
    ring

/-! ## Layer 3 — the circuit class and the five-class core -/

/-- The positive labels parallel to the extra direction. -/
noncomputable def extraClass (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    (extraDir : Fin size → ℝ) : Finset activeIndex :=
  letI : DecidablePred fun label : activeIndex =>
      ∃ scal : ℝ, tightDir label = scal • extraDir :=
    Classical.decPred _
  (positiveActiveSet activeSet activeWeight).filter fun label =>
    ∃ scal : ℝ, tightDir label = scal • extraDir

/-- Membership in the extra class, unfolded. -/
theorem mem_extraClass {extraDir : Fin size → ℝ} {label : activeIndex} :
    label ∈ extraClass activeSet activeWeight tightDir extraDir
      ↔ label ∈ positiveActiveSet activeSet activeWeight
        ∧ ∃ scal : ℝ, tightDir label = scal • extraDir := by
  letI : DecidablePred fun label : activeIndex =>
      ∃ scal : ℝ, tightDir label = scal • extraDir :=
    Classical.decPred _
  rw [extraClass]
  exact Finset.mem_filter

/-- The circuit mass: the weight of the extra class. -/
noncomputable def extraMass (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    (extraDir : Fin size → ℝ) : ℝ :=
  ∑ label ∈ extraClass activeSet activeWeight tightDir extraDir,
    activeWeight label

/-- The circuit mass dominates the weight of each member. -/
theorem extraMass_pos_of_mem {extraDir : Fin size → ℝ} {label : activeIndex}
    (hmem : label ∈ extraClass activeSet activeWeight tightDir extraDir) :
    0 < extraMass activeSet activeWeight tightDir extraDir := by
  have hpos := (mem_positiveActiveSet.mp (mem_extraClass.mp hmem).1).2
  have hle : activeWeight label
      ≤ extraMass activeSet activeWeight tightDir extraDir := by
    refine Finset.single_le_sum (fun other hother => ?_) hmem
    exact (mem_positiveActiveSet.mp (mem_extraClass.mp hother).1).2.le
  linarith

/-- **THE FIVE-CLASS CORE.**  When every positive label is parallel to a
basis direction or to the extra direction, the assembly is the effective
diagonal plus the extra mass on the extra atom matrix. -/
theorem assembly_eq_effective_diagonal_with_extra
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hmemPos : ∀ slot, basisLabel slot
      ∈ positiveActiveSet activeSet activeWeight)
    {extraDir : Fin size → ℝ} (hextraUnit : extraDir ⬝ᵥ extraDir = 1)
    (hnotpar : ∀ (slot : Fin basisCount) (scal : ℝ),
      extraDir ≠ scal • tightDir (basisLabel slot))
    (hsplit : ∀ label ∈ positiveActiveSet activeSet activeWeight,
      (∃ (slot : Fin basisCount) (scal : ℝ),
        tightDir label = scal • tightDir (basisLabel slot))
      ∨ ∃ scal : ℝ, tightDir label = scal • extraDir) :
    chartMultiplierAssembly activeSet activeWeight tightDir
      = (∑ slot, effectiveMultiplier activeSet activeWeight tightDir
          basisLabel slot • atomMatrix (tightDir (basisLabel slot)))
        + extraMass activeSet activeWeight tightDir extraDir
          • atomMatrix extraDir := by
  classical
  have hunitOf : ∀ label ∈ positiveActiveSet activeSet activeWeight,
      tightDir label ⬝ᵥ tightDir label = 1 := fun label hmem =>
    hdata.tightDir_unit label (positiveActiveSet_subset_activeSet hmem)
  have hdisjointExtra : ∀ slot : Fin basisCount,
      Disjoint (parallelClass activeSet activeWeight tightDir basisLabel slot)
        (extraClass activeSet activeWeight tightDir extraDir) := by
    intro slot
    rw [Finset.disjoint_left]
    intro label hmemSlot hmemExtra
    obtain ⟨hmemP, scalOne, hparOne⟩ := mem_parallelClass.mp hmemSlot
    obtain ⟨-, scalTwo, hparTwo⟩ := mem_extraClass.mp hmemExtra
    have hscalTwo : scalTwo ≠ 0 := by
      intro hzero
      rw [hzero, zero_smul] at hparTwo
      have hunit := hunitOf label hmemP
      rw [hparTwo] at hunit
      simp [dotProduct] at hunit
    refine hnotpar slot (scalOne / scalTwo) ?_
    funext atomIndex
    have hone := congrFun hparOne atomIndex
    have htwo := congrFun hparTwo atomIndex
    rw [Pi.smul_apply, smul_eq_mul] at hone htwo
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hscalTwo]
    linear_combination hone - htwo
  have hdisjointBasis : ∀ slotOne ∈ (Finset.univ : Finset (Fin basisCount)),
      ∀ slotTwo ∈ (Finset.univ : Finset (Fin basisCount)),
      slotOne ≠ slotTwo →
      Disjoint (parallelClass activeSet activeWeight tightDir basisLabel
          slotOne)
        (parallelClass activeSet activeWeight tightDir basisLabel slotTwo) := by
    intro slotOne _ slotTwo _ hne
    rw [Finset.disjoint_left]
    intro label hmemOne hmemTwo
    obtain ⟨hmemP, scalOne, hparOne⟩ := mem_parallelClass.mp hmemOne
    obtain ⟨-, scalTwo, hparTwo⟩ := mem_parallelClass.mp hmemTwo
    exact false_of_parallel_two_slots basisLabel hleft hne
      (hunitOf label hmemP) (hunitOf (basisLabel slotOne) (hmemPos slotOne))
      hparOne hparTwo
  have hcover : positiveActiveSet activeSet activeWeight
      = (Finset.univ.biUnion fun slot =>
          parallelClass activeSet activeWeight tightDir basisLabel slot)
        ∪ extraClass activeSet activeWeight tightDir extraDir := by
    apply Finset.Subset.antisymm
    · intro label hmem
      rcases hsplit label hmem with ⟨slot, scal, hpar⟩ | ⟨scal, hpar⟩
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨slot, Finset.mem_univ slot,
            mem_parallelClass.mpr ⟨hmem, scal, hpar⟩⟩)
      · exact Finset.mem_union_right _
          (mem_extraClass.mpr ⟨hmem, scal, hpar⟩)
    · intro label hmem
      rcases Finset.mem_union.mp hmem with hmemB | hmemE
      · obtain ⟨slot, -, hmemClass⟩ := Finset.mem_biUnion.mp hmemB
        exact (mem_parallelClass.mp hmemClass).1
      · exact (mem_extraClass.mp hmemE).1
  have hdisjointUnion : Disjoint
      (Finset.univ.biUnion fun slot =>
        parallelClass activeSet activeWeight tightDir basisLabel slot)
      (extraClass activeSet activeWeight tightDir extraDir) := by
    rw [Finset.disjoint_left]
    intro label hmemB hmemE
    obtain ⟨slot, -, hmemClass⟩ := Finset.mem_biUnion.mp hmemB
    exact Finset.disjoint_left.mp (hdisjointExtra slot) hmemClass hmemE
  calc chartMultiplierAssembly activeSet activeWeight tightDir
      = chartMultiplierAssembly (positiveActiveSet activeSet activeWeight)
          activeWeight tightDir :=
        (chartMultiplierAssembly_positiveActiveSet hdata).symm
    _ = ∑ label ∈ (Finset.univ.biUnion fun slot =>
            parallelClass activeSet activeWeight tightDir basisLabel slot)
          ∪ extraClass activeSet activeWeight tightDir extraDir,
          activeWeight label • atomMatrix (tightDir label) := by
        rw [chartMultiplierAssembly, hcover]
    _ = (∑ label ∈ Finset.univ.biUnion (fun slot =>
            parallelClass activeSet activeWeight tightDir basisLabel slot),
          activeWeight label • atomMatrix (tightDir label))
        + ∑ label ∈ extraClass activeSet activeWeight tightDir extraDir,
            activeWeight label • atomMatrix (tightDir label) :=
        Finset.sum_union hdisjointUnion
    _ = (∑ slot, effectiveMultiplier activeSet activeWeight tightDir
          basisLabel slot • atomMatrix (tightDir (basisLabel slot)))
        + extraMass activeSet activeWeight tightDir extraDir
          • atomMatrix extraDir := by
        congr 1
        · rw [Finset.sum_biUnion hdisjointBasis]
          refine Finset.sum_congr rfl fun slot _ => ?_
          rw [effectiveMultiplier, Finset.sum_smul]
          refine Finset.sum_congr rfl fun label hmem => ?_
          obtain ⟨hmemP, scal, hpar⟩ := mem_parallelClass.mp hmem
          rw [atomMatrix_eq_of_unit_parallel hpar (hunitOf label hmemP)
            (hunitOf (basisLabel slot) (hmemPos slot))]
        · rw [extraMass, Finset.sum_smul]
          refine Finset.sum_congr rfl fun label hmem => ?_
          obtain ⟨hmemP, scal, hpar⟩ := mem_extraClass.mp hmem
          rw [atomMatrix_eq_of_unit_parallel hpar (hunitOf label hmemP)
            hextraUnit]

/-! ## Layer 4 — the five-term entry forms -/

/-- The five-term diagonal read of the extra decomposition. -/
theorem extra_diagonal_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {extraDir : Fin size → ℝ}
    (hdecomp : chartMultiplierAssembly activeSet activeWeight tightDir
      = (∑ slot, effectiveMultiplier activeSet activeWeight tightDir
          basisLabel slot • atomMatrix (tightDir (basisLabel slot)))
        + extraMass activeSet activeWeight tightDir extraDir
          • atomMatrix extraDir)
    (atomIndex : Fin size) :
    (∑ slot, effectiveMultiplier activeSet activeWeight tightDir
        basisLabel slot * tightDir (basisLabel slot) atomIndex ^ 2)
      + extraMass activeSet activeWeight tightDir extraDir
        * extraDir atomIndex ^ 2
      = ((size : ℝ))⁻¹ := by
  have happ := congrFun (congrFun hdecomp atomIndex) atomIndex
  rw [hdata.assembly_diagonal atomIndex] at happ
  have hentry : ((∑ slot, effectiveMultiplier activeSet activeWeight tightDir
        basisLabel slot • atomMatrix (tightDir (basisLabel slot)))
      + extraMass activeSet activeWeight tightDir extraDir
        • atomMatrix extraDir) atomIndex atomIndex
      = (∑ slot, effectiveMultiplier activeSet activeWeight tightDir
          basisLabel slot * tightDir (basisLabel slot) atomIndex ^ 2)
        + extraMass activeSet activeWeight tightDir extraDir
          * extraDir atomIndex ^ 2 := by
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
    congr 1
    · exact Finset.sum_congr rfl fun slot _ => by ring
    · ring
  rw [hentry] at happ
  exact happ.symm

/-- The five-term commutation entry of the extra decomposition. -/
theorem extra_commutation_entry
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {extraDir : Fin size → ℝ}
    (hdecomp : chartMultiplierAssembly activeSet activeWeight tightDir
      = (∑ slot, effectiveMultiplier activeSet activeWeight tightDir
          basisLabel slot • atomMatrix (tightDir (basisLabel slot)))
        + extraMass activeSet activeWeight tightDir extraDir
          • atomMatrix extraDir)
    (atomRow atomCol : Fin size) :
    (∑ slot, effectiveMultiplier activeSet activeWeight tightDir
        basisLabel slot
        * ((projection *ᵥ tightDir (basisLabel slot)) atomRow
            * tightDir (basisLabel slot) atomCol
          - tightDir (basisLabel slot) atomRow
            * (projection *ᵥ tightDir (basisLabel slot)) atomCol))
      + extraMass activeSet activeWeight tightDir extraDir
        * ((projection *ᵥ extraDir) atomRow * extraDir atomCol
          - extraDir atomRow * (projection *ᵥ extraDir) atomCol)
      = 0 := by
  classical
  set mass := extraMass activeSet activeWeight tightDir extraDir
  -- Reindex the five terms over `Fin (basisCount + 1)`.
  set coefFive : Fin (basisCount + 1) → ℝ := Fin.cons mass
    (fun slot => effectiveMultiplier activeSet activeWeight tightDir
      basisLabel slot) with hcoefFive
  set vecFive : Fin (basisCount + 1) → (Fin size → ℝ) := Fin.cons extraDir
    (fun slot => tightDir (basisLabel slot)) with hvecFive
  have hdecompFive : chartMultiplierAssembly activeSet activeWeight tightDir
      = ∑ termIndex, coefFive termIndex • atomMatrix (vecFive termIndex) := by
    rw [Fin.sum_univ_succ, hdecomp]
    simp only [hcoefFive, hvecFive, Fin.cons_zero, Fin.cons_succ]
    exact add_comm _ _
  have hentry := decomposition_commutation_entry hdata hdecompFive
    atomRow atomCol
  rw [Fin.sum_univ_succ] at hentry
  simp only [hcoefFive, hvecFive, Fin.cons_zero, Fin.cons_succ] at hentry
  linarith [hentry]

end Gtz

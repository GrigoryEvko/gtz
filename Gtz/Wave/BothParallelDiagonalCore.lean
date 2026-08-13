import Gtz.Wave.BothParallelTrichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The both-parallel diagonal core — the assembly under the trichotomy

The trichotomy classifies every positive label of a both-parallel C4
datum: parallel to a basis direction, or the circuit.  This module
prices the parallel branch.  When every positive label is parallel to a
basis direction, the assembly collapses to the diagonal core: a sum of
four basis atoms with positive effective multipliers.

The chain:

1. A unit direction parallel to a unit direction has the same atom
   matrix, because the scalar squares to one.
2. The left inverse separates the parallel classes: one label does not
   align with two different basis slots.
3. The positive support partitions into the four parallel classes, and
   the assembly sum collapses class by class.
4. The entry reads follow: the diagonal read, the vanished cross entry
   at the two single atoms, and the four-term commutation pricing.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomMatrix_eq_of_unit_parallel` — the unit atom collapse.
* `Gtz.parallel_scal_ne_zero` — the nonzero scalar.
* `Gtz.false_of_parallel_two_slots` — **THE CLASS SEPARATION.**
* `Gtz.parallelClass`, `Gtz.effectiveMultiplier` — the definitions.
* `Gtz.basisLabel_mem_parallelClass`,
  `Gtz.effectiveMultiplier_pos` — the class anchors.
* `Gtz.assembly_eq_effective_diagonal` — **THE DIAGONAL CORE.**
* `Gtz.effective_diagonal_apply` — the entry form.
* `Gtz.effective_diagonal_read` — the diagonal read.
* `Gtz.bothParallel_effective_cross_vanish` — **THE ZERO CROSS ENTRY.**
* `Gtz.bothParallel_effective_cross_commutation` — **THE PRICING.**

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

/-! ## Layer 1 — the unit atom collapse -/

/-- A scalar that carries one unit vector onto one more unit vector
squares to one. -/
theorem parallel_scal_sq_one {dirLabel dirBase : Fin size → ℝ} {scal : ℝ}
    (hpar : dirLabel = scal • dirBase)
    (hunitLabel : dirLabel ⬝ᵥ dirLabel = 1)
    (hunitBase : dirBase ⬝ᵥ dirBase = 1) : scal ^ 2 = 1 := by
  rw [hpar, smul_dotProduct, dotProduct_smul, hunitBase] at hunitLabel
  calc scal ^ 2 = scal * (scal * 1) := by ring
    _ = 1 := hunitLabel

/-- The scalar of a unit parallel direction is nonzero. -/
theorem parallel_scal_ne_zero {dirLabel dirBase : Fin size → ℝ} {scal : ℝ}
    (hpar : dirLabel = scal • dirBase)
    (hunitLabel : dirLabel ⬝ᵥ dirLabel = 1)
    (hunitBase : dirBase ⬝ᵥ dirBase = 1) : scal ≠ 0 := by
  intro hzero
  have hsq := parallel_scal_sq_one hpar hunitLabel hunitBase
  rw [hzero] at hsq
  norm_num at hsq

/-- **THE UNIT ATOM COLLAPSE.**  Parallel unit directions share one atom
matrix. -/
theorem atomMatrix_eq_of_unit_parallel {dirLabel dirBase : Fin size → ℝ}
    {scal : ℝ} (hpar : dirLabel = scal • dirBase)
    (hunitLabel : dirLabel ⬝ᵥ dirLabel = 1)
    (hunitBase : dirBase ⬝ᵥ dirBase = 1) :
    atomMatrix dirLabel = atomMatrix dirBase := by
  rw [hpar, atomMatrix_smul,
    parallel_scal_sq_one hpar hunitLabel hunitBase, one_smul]

/-! ## Layer 2 — the class separation -/

/-- **THE CLASS SEPARATION.**  One unit direction does not align with
two different basis slots, because the left inverse separates the
columns. -/
theorem false_of_parallel_two_slots
    (basisLabel : Fin basisCount → activeIndex)
    {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo : Fin basisCount} (hne : slotOne ≠ slotTwo)
    {label : activeIndex}
    (hunit : tightDir label ⬝ᵥ tightDir label = 1)
    (hunitOne : tightDir (basisLabel slotOne)
      ⬝ᵥ tightDir (basisLabel slotOne) = 1)
    {scalOne scalTwo : ℝ}
    (hparOne : tightDir label = scalOne • tightDir (basisLabel slotOne))
    (hparTwo : tightDir label = scalTwo • tightDir (basisLabel slotTwo)) :
    False := by
  have hscalOne := parallel_scal_ne_zero hparOne hunit hunitOne
  have hentryOne := congrFun (congrFun hleft slotOne) slotOne
  have hentryTwo := congrFun (congrFun hleft slotOne) slotTwo
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hentryOne
  rw [Matrix.mul_apply, Matrix.one_apply_ne hne] at hentryTwo
  have hcoordEq : ∀ atomIndex, scalOne
        * tightDir (basisLabel slotOne) atomIndex
      = scalTwo * tightDir (basisLabel slotTwo) atomIndex := by
    intro atomIndex
    have honeApp := congrFun hparOne atomIndex
    have htwoApp := congrFun hparTwo atomIndex
    rw [Pi.smul_apply, smul_eq_mul] at honeApp htwoApp
    rw [← honeApp, ← htwoApp]
  have hsumEq : scalOne * ∑ atomIndex, leftInv slotOne atomIndex
        * tightBasisColumns tightDir basisLabel atomIndex slotOne
      = scalTwo * ∑ atomIndex, leftInv slotOne atomIndex
        * tightBasisColumns tightDir basisLabel atomIndex slotTwo := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    have hcoord := hcoordEq atomIndex
    simp only [tightBasisColumns]
    linear_combination leftInv slotOne atomIndex * hcoord
  rw [hentryOne, hentryTwo, mul_one, mul_zero] at hsumEq
  exact hscalOne hsumEq

/-! ## Layer 3 — the classes and the effective multipliers -/

/-- The positive labels parallel to one basis slot. -/
noncomputable def parallelClass (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    (basisLabel : Fin basisCount → activeIndex) (slot : Fin basisCount) :
    Finset activeIndex :=
  letI : DecidablePred fun label : activeIndex =>
      ∃ scal : ℝ, tightDir label = scal • tightDir (basisLabel slot) :=
    Classical.decPred _
  (positiveActiveSet activeSet activeWeight).filter fun label =>
    ∃ scal : ℝ, tightDir label = scal • tightDir (basisLabel slot)

/-- Membership in a parallel class, unfolded. -/
theorem mem_parallelClass {basisLabel : Fin basisCount → activeIndex}
    {slot : Fin basisCount} {label : activeIndex} :
    label ∈ parallelClass activeSet activeWeight tightDir basisLabel slot
      ↔ label ∈ positiveActiveSet activeSet activeWeight
        ∧ ∃ scal : ℝ, tightDir label = scal • tightDir (basisLabel slot) := by
  letI : DecidablePred fun label : activeIndex =>
      ∃ scal : ℝ, tightDir label = scal • tightDir (basisLabel slot) :=
    Classical.decPred _
  rw [parallelClass]
  exact Finset.mem_filter

/-- The effective multiplier of one slot: the weight mass of its
parallel class. -/
noncomputable def effectiveMultiplier (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    (basisLabel : Fin basisCount → activeIndex) (slot : Fin basisCount) : ℝ :=
  ∑ label ∈ parallelClass activeSet activeWeight tightDir basisLabel slot,
    activeWeight label

/-- Each basis label sits in its own parallel class. -/
theorem basisLabel_mem_parallelClass
    (basisLabel : Fin basisCount → activeIndex) (slot : Fin basisCount)
    (hmemPos : basisLabel slot ∈ positiveActiveSet activeSet activeWeight) :
    basisLabel slot
      ∈ parallelClass activeSet activeWeight tightDir basisLabel slot := by
  exact mem_parallelClass.mpr ⟨hmemPos, 1, (one_smul ℝ _).symm⟩

/-- The effective multiplier of one slot is positive: the class carries
its own basis label. -/
theorem effectiveMultiplier_pos
    (basisLabel : Fin basisCount → activeIndex) (slot : Fin basisCount)
    (hmemPos : basisLabel slot ∈ positiveActiveSet activeSet activeWeight) :
    0 < effectiveMultiplier activeSet activeWeight tightDir basisLabel slot := by
  have hpos := (mem_positiveActiveSet.mp hmemPos).2
  have hle : activeWeight (basisLabel slot)
      ≤ effectiveMultiplier activeSet activeWeight tightDir basisLabel slot := by
    refine Finset.single_le_sum (fun label hmem => ?_)
      (basisLabel_mem_parallelClass basisLabel slot hmemPos)
    have hmemP := (mem_parallelClass.mp hmem).1
    exact (mem_positiveActiveSet.mp hmemP).2.le
  linarith

/-! ## Layer 4 — the diagonal core -/

/-- **THE DIAGONAL CORE.**  When every positive label is parallel to a
basis direction, the assembly is the effective-multiplier sum of the
four basis atoms. -/
theorem assembly_eq_effective_diagonal
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hmemPos : ∀ slot, basisLabel slot
      ∈ positiveActiveSet activeSet activeWeight)
    (hparallel : ∀ label ∈ positiveActiveSet activeSet activeWeight,
      ∃ (slot : Fin basisCount) (scal : ℝ),
        tightDir label = scal • tightDir (basisLabel slot)) :
    chartMultiplierAssembly activeSet activeWeight tightDir
      = ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
          basisLabel slot • atomMatrix (tightDir (basisLabel slot)) := by
  classical
  have hunitOf : ∀ label ∈ positiveActiveSet activeSet activeWeight,
      tightDir label ⬝ᵥ tightDir label = 1 := fun label hmem =>
    hdata.tightDir_unit label (positiveActiveSet_subset_activeSet hmem)
  have hcover : positiveActiveSet activeSet activeWeight
      = Finset.univ.biUnion (fun slot =>
          parallelClass activeSet activeWeight tightDir basisLabel slot) := by
    apply Finset.Subset.antisymm
    · intro label hmem
      obtain ⟨slot, scal, hpar⟩ := hparallel label hmem
      exact Finset.mem_biUnion.mpr ⟨slot, Finset.mem_univ slot,
        mem_parallelClass.mpr ⟨hmem, scal, hpar⟩⟩
    · intro label hmem
      obtain ⟨slot, _, hmemClass⟩ := Finset.mem_biUnion.mp hmem
      exact (mem_parallelClass.mp hmemClass).1
  have hdisjoint : ∀ slotOne ∈ (Finset.univ : Finset (Fin basisCount)),
      ∀ slotTwo ∈ (Finset.univ : Finset (Fin basisCount)),
      slotOne ≠ slotTwo →
      Disjoint (parallelClass activeSet activeWeight tightDir basisLabel
          slotOne)
        (parallelClass activeSet activeWeight tightDir basisLabel slotTwo) := by
    intro slotOne _ slotTwo _ hne
    rw [Finset.disjoint_left]
    intro label hmemOne hmemTwo
    obtain ⟨hmemP, scalOne, hparOne⟩ := mem_parallelClass.mp hmemOne
    obtain ⟨_, scalTwo, hparTwo⟩ := mem_parallelClass.mp hmemTwo
    exact false_of_parallel_two_slots basisLabel hleft hne
      (hunitOf label hmemP) (hunitOf (basisLabel slotOne) (hmemPos slotOne))
      hparOne hparTwo
  calc chartMultiplierAssembly activeSet activeWeight tightDir
      = chartMultiplierAssembly (positiveActiveSet activeSet activeWeight)
          activeWeight tightDir :=
        (chartMultiplierAssembly_positiveActiveSet hdata).symm
    _ = ∑ label ∈ Finset.univ.biUnion (fun slot =>
          parallelClass activeSet activeWeight tightDir basisLabel slot),
          activeWeight label • atomMatrix (tightDir label) := by
        rw [chartMultiplierAssembly, hcover]
    _ = ∑ slot, ∑ label ∈ parallelClass activeSet activeWeight tightDir
          basisLabel slot, activeWeight label • atomMatrix (tightDir label) :=
        Finset.sum_biUnion hdisjoint
    _ = ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
          basisLabel slot • atomMatrix (tightDir (basisLabel slot)) := by
        refine Finset.sum_congr rfl fun slot _ => ?_
        rw [effectiveMultiplier, Finset.sum_smul]
        refine Finset.sum_congr rfl fun label hmem => ?_
        obtain ⟨hmemP, scal, hpar⟩ := mem_parallelClass.mp hmem
        rw [atomMatrix_eq_of_unit_parallel hpar (hunitOf label hmemP)
          (hunitOf (basisLabel slot) (hmemPos slot))]

/-! ## Layer 5 — the entry reads -/

/-- The entry form of the diagonal core. -/
theorem effective_diagonal_apply
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hmemPos : ∀ slot, basisLabel slot
      ∈ positiveActiveSet activeSet activeWeight)
    (hparallel : ∀ label ∈ positiveActiveSet activeSet activeWeight,
      ∃ (slot : Fin basisCount) (scal : ℝ),
        tightDir label = scal • tightDir (basisLabel slot))
    (atomRow atomCol : Fin size) :
    chartMultiplierAssembly activeSet activeWeight tightDir atomRow atomCol
      = ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
          basisLabel slot
          * (tightDir (basisLabel slot) atomRow
            * tightDir (basisLabel slot) atomCol) := by
  rw [assembly_eq_effective_diagonal hdata basisLabel hleft hmemPos hparallel]
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul]

/-- The diagonal read of the diagonal core: the weight stationarity
prices each atom at the inverse size. -/
theorem effective_diagonal_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hmemPos : ∀ slot, basisLabel slot
      ∈ positiveActiveSet activeSet activeWeight)
    (hparallel : ∀ label ∈ positiveActiveSet activeSet activeWeight,
      ∃ (slot : Fin basisCount) (scal : ℝ),
        tightDir label = scal • tightDir (basisLabel slot))
    (atomIndex : Fin size) :
    ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
        basisLabel slot * tightDir (basisLabel slot) atomIndex ^ 2
      = ((size : ℝ))⁻¹ := by
  have happ := effective_diagonal_apply hdata basisLabel hleft hmemPos
    hparallel atomIndex atomIndex
  rw [hdata.assembly_diagonal atomIndex] at happ
  calc ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
        basisLabel slot * tightDir (basisLabel slot) atomIndex ^ 2
      = ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
          basisLabel slot * (tightDir (basisLabel slot) atomIndex
            * tightDir (basisLabel slot) atomIndex) :=
        Finset.sum_congr rfl fun slot _ => by ring
    _ = ((size : ℝ))⁻¹ := happ.symm

/-- **THE ZERO CROSS ENTRY.**  At the both-parallel C4 support pattern,
the diagonal core vanishes at the two single atoms: every basis
direction misses one of them. -/
theorem bothParallel_effective_cross_vanish
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hmemPos : ∀ slot, basisLabel slot
      ∈ positiveActiveSet activeSet activeWeight)
    (hparallel : ∀ label ∈ positiveActiveSet activeSet activeWeight,
      ∃ (slot : Fin basisCount) (scal : ℝ),
        tightDir label = scal • tightDir (basisLabel slot))
    {slotA slotB slotC slotD : Fin basisCount}
    (hslots : ∀ slot : Fin basisCount, slot = slotA ∨ slot = slotB
      ∨ slot = slotC ∨ slot = slotD)
    {atomB atomD : Fin size}
    (hqAb : tightDir (basisLabel slotA) atomB = 0)
    (hqBd : tightDir (basisLabel slotB) atomD = 0)
    (hqCd : tightDir (basisLabel slotC) atomD = 0)
    (hqDb : tightDir (basisLabel slotD) atomB = 0) :
    chartMultiplierAssembly activeSet activeWeight tightDir atomB atomD
      = 0 := by
  rw [effective_diagonal_apply hdata basisLabel hleft hmemPos hparallel]
  refine Finset.sum_eq_zero fun slot _ => ?_
  rcases hslots slot with heq | heq | heq | heq
  · rw [heq, hqAb]
    ring
  · rw [heq, hqBd]
    ring
  · rw [heq, hqCd]
    ring
  · rw [heq, hqDb]
    ring

/-- **THE PRICING.**  The commutation entry at the two single atoms
collapses to four terms: the projected columns of the two anchor
carriers against the two single carriers. -/
theorem bothParallel_effective_cross_commutation
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hmemPos : ∀ slot, basisLabel slot
      ∈ positiveActiveSet activeSet activeWeight)
    (hparallel : ∀ label ∈ positiveActiveSet activeSet activeWeight,
      ∃ (slot : Fin basisCount) (scal : ℝ),
        tightDir label = scal • tightDir (basisLabel slot))
    {slotA slotB slotC slotD : Fin basisCount}
    (hslots : ∀ slot : Fin basisCount, slot = slotA ∨ slot = slotB
      ∨ slot = slotC ∨ slot = slotD)
    (hslotABne : slotA ≠ slotB) (hslotACne : slotA ≠ slotC)
    (hslotADne : slotA ≠ slotD) (hslotBCne : slotB ≠ slotC)
    (hslotBDne : slotB ≠ slotD) (hslotCDne : slotC ≠ slotD)
    {atomB atomD : Fin size}
    (hqAb : tightDir (basisLabel slotA) atomB = 0)
    (hqBd : tightDir (basisLabel slotB) atomD = 0)
    (hqCd : tightDir (basisLabel slotC) atomD = 0)
    (hqDb : tightDir (basisLabel slotD) atomB = 0) :
    effectiveMultiplier activeSet activeWeight tightDir basisLabel slotA
        * (projection *ᵥ tightDir (basisLabel slotA)) atomB
        * tightDir (basisLabel slotA) atomD
      + effectiveMultiplier activeSet activeWeight tightDir basisLabel slotD
        * (projection *ᵥ tightDir (basisLabel slotD)) atomB
        * tightDir (basisLabel slotD) atomD
      = effectiveMultiplier activeSet activeWeight tightDir basisLabel slotB
        * tightDir (basisLabel slotB) atomB
        * (projection *ᵥ tightDir (basisLabel slotB)) atomD
      + effectiveMultiplier activeSet activeWeight tightDir basisLabel slotC
        * tightDir (basisLabel slotC) atomB
        * (projection *ᵥ tightDir (basisLabel slotC)) atomD := by
  classical
  have hcommute := congrFun (congrFun hdata.assembly_commutes atomB) atomD
  rw [Matrix.mul_apply, Matrix.mul_apply] at hcommute
  have hleftSum : ∑ atomMid, projection atomB atomMid
        * chartMultiplierAssembly activeSet activeWeight tightDir
            atomMid atomD
      = ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
          basisLabel slot
          * ((projection *ᵥ tightDir (basisLabel slot)) atomB
            * tightDir (basisLabel slot) atomD) := by
    calc ∑ atomMid, projection atomB atomMid
          * chartMultiplierAssembly activeSet activeWeight tightDir
              atomMid atomD
        = ∑ atomMid, ∑ slot, projection atomB atomMid
            * (effectiveMultiplier activeSet activeWeight tightDir
                basisLabel slot
              * (tightDir (basisLabel slot) atomMid
                * tightDir (basisLabel slot) atomD)) := by
          refine Finset.sum_congr rfl fun atomMid _ => ?_
          rw [effective_diagonal_apply hdata basisLabel hleft hmemPos
            hparallel atomMid atomD, Finset.mul_sum]
      _ = ∑ slot, ∑ atomMid, projection atomB atomMid
            * (effectiveMultiplier activeSet activeWeight tightDir
                basisLabel slot
              * (tightDir (basisLabel slot) atomMid
                * tightDir (basisLabel slot) atomD)) := Finset.sum_comm
      _ = ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
            basisLabel slot
            * ((projection *ᵥ tightDir (basisLabel slot)) atomB
              * tightDir (basisLabel slot) atomD) := by
          refine Finset.sum_congr rfl fun slot _ => ?_
          simp only [Matrix.mulVec, dotProduct, Finset.sum_mul,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun atomMid _ => ?_
          ring
  have hrightSum : ∑ atomMid, chartMultiplierAssembly activeSet activeWeight
        tightDir atomB atomMid * projection atomMid atomD
      = ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
          basisLabel slot
          * (tightDir (basisLabel slot) atomB
            * (projection *ᵥ tightDir (basisLabel slot)) atomD) := by
    calc ∑ atomMid, chartMultiplierAssembly activeSet activeWeight tightDir
          atomB atomMid * projection atomMid atomD
        = ∑ atomMid, ∑ slot, effectiveMultiplier activeSet activeWeight
            tightDir basisLabel slot
            * (tightDir (basisLabel slot) atomB
              * tightDir (basisLabel slot) atomMid)
            * projection atomMid atomD := by
          refine Finset.sum_congr rfl fun atomMid _ => ?_
          rw [effective_diagonal_apply hdata basisLabel hleft hmemPos
            hparallel atomB atomMid, Finset.sum_mul]
      _ = ∑ slot, ∑ atomMid, effectiveMultiplier activeSet activeWeight
            tightDir basisLabel slot
            * (tightDir (basisLabel slot) atomB
              * tightDir (basisLabel slot) atomMid)
            * projection atomMid atomD := Finset.sum_comm
      _ = ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
            basisLabel slot
            * (tightDir (basisLabel slot) atomB
              * (projection *ᵥ tightDir (basisLabel slot)) atomD) := by
          refine Finset.sum_congr rfl fun slot _ => ?_
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun atomMid _ => ?_
          rw [projection_entry_symm hdata atomMid atomD]
          ring
  have huniv : (Finset.univ : Finset (Fin basisCount))
      = {slotA, slotB, slotC, slotD} := by
    ext slot
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
      Finset.mem_singleton]
    exact hslots slot
  have hnotA : slotA ∉ ({slotB, slotC, slotD} : Finset (Fin basisCount)) := by
    simp [hslotABne, hslotACne, hslotADne]
  have hnotB : slotB ∉ ({slotC, slotD} : Finset (Fin basisCount)) := by
    simp [hslotBCne, hslotBDne]
  have hnotC : slotC ∉ ({slotD} : Finset (Fin basisCount)) := by
    simp [hslotCDne]
  have hLfour : ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
        basisLabel slot
        * ((projection *ᵥ tightDir (basisLabel slot)) atomB
          * tightDir (basisLabel slot) atomD)
      = effectiveMultiplier activeSet activeWeight tightDir basisLabel slotA
        * ((projection *ᵥ tightDir (basisLabel slotA)) atomB
          * tightDir (basisLabel slotA) atomD)
        + effectiveMultiplier activeSet activeWeight tightDir basisLabel
            slotD
          * ((projection *ᵥ tightDir (basisLabel slotD)) atomB
            * tightDir (basisLabel slotD) atomD) := by
    rw [huniv, Finset.sum_insert hnotA, Finset.sum_insert hnotB,
      Finset.sum_insert hnotC, Finset.sum_singleton, hqBd, hqCd]
    ring
  have hRfour : ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
        basisLabel slot
        * (tightDir (basisLabel slot) atomB
          * (projection *ᵥ tightDir (basisLabel slot)) atomD)
      = effectiveMultiplier activeSet activeWeight tightDir basisLabel slotB
        * (tightDir (basisLabel slotB) atomB
          * (projection *ᵥ tightDir (basisLabel slotB)) atomD)
        + effectiveMultiplier activeSet activeWeight tightDir basisLabel
            slotC
          * (tightDir (basisLabel slotC) atomB
            * (projection *ᵥ tightDir (basisLabel slotC)) atomD) := by
    rw [huniv, Finset.sum_insert hnotA, Finset.sum_insert hnotB,
      Finset.sum_insert hnotC, Finset.sum_singleton, hqAb, hqDb]
    ring
  rw [hleftSum, hrightSum, hLfour, hRfour] at hcommute
  linear_combination hcommute

end Gtz

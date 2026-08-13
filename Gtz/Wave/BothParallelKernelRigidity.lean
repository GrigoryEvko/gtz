import Gtz.Wave.CycleIndependentClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The both-parallel kernel rigidity — the H-free layer of closure five

The both-parallel C4 configuration carries two parallel pair
restrictions.  Each parallel pair supplies a pair kernel vector, and the
two kernel vectors span the kernel of the assembly.  The commutation
keeps that kernel under the chart, and the annihilated coordinates of
the projected kernel vectors read four entry laws per pair.  Every
statement here is free of the Gram core: the laws hold for the FULL
positive-semidefinite core of the frame, not only for a diagonal
multiplier vector.

The chain, for the pair `{atomA1, atomA2}` with carriers `slotA, slotB`:

1. The basis columns annihilate the pair kernel vector, because the two
   carriers restrict to the pair proportionally and the other two
   directions vanish there.
2. The assembly annihilates it through the Gram form, and the
   commutation extends the annihilation to the projected vector.
3. The left inverse pulls the assembly annihilation back to the basis
   columns: the Gram core has a trivial kernel.
4. The annihilated coordinates collapse: the projected kernel vector
   vanishes at the two single atoms and satisfies one balance per pair.
   The collapse divides by the concentration determinant, and the
   degenerate determinant dies through the landed dependent kill.

The consumers turn the four reads into the rigidity laws: the twin
weights of each pair, the equal pair diagonal of the gap, the pair
proportionality of the two single-atom gap rows, and the two
cross-block balances.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.basisColumns_transpose_dot`, `Gtz.triple_dot_collapse` — the
  entry plumbing.
* `Gtz.bothParallel_pairKernel_annihilated` — **THE ANNIHILATION.**
* `Gtz.basisTranspose_zero_of_assembly_mulVec_zero` — **THE PULLBACK.**
* `Gtz.bothParallel_annihilated_reads` — **THE COLLAPSE.**
* `Gtz.bothParallel_projected_kernel_reads` — **THE PROJECTED READS.**
* `Gtz.pair_row_proportional_of_reads`,
  `Gtz.pair_balance_of_reads` — the entry forms.
* `Gtz.bothParallel_twin_weights` — **THE TWIN WEIGHTS.**
* `Gtz.bothParallel_pair_diag_eq` — the equal pair diagonal.

## Vacuity

Nothing here quantifies over a crux.  Every statement holds at each
stationary datum with the stated pattern hypotheses.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the entry plumbing -/

/-- One row of the transposed basis columns against a probe is the dot
sum of the direction with the probe. -/
theorem basisColumns_transpose_dot
    (basisLabel : Fin basisCount → activeIndex) (probe : Fin size → ℝ)
    (columnIndex : Fin basisCount) :
    ((tightBasisColumns tightDir basisLabel)ᵀ *ᵥ probe) columnIndex
      = ∑ atomIndex : Fin size,
          tightDir (basisLabel columnIndex) atomIndex * probe atomIndex := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    tightBasisColumns]

/-- A dot sum against a direction with a card-3 support collapses to the
three supported terms. -/
theorem triple_dot_collapse {dir probe : Fin size → ℝ}
    {atomU atomV atomT : Fin size} (hUV : atomU ≠ atomV) (hUT : atomU ≠ atomT)
    (hVT : atomV ≠ atomT)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomT → dir atomIndex = 0) :
    ∑ atomIndex : Fin size, dir atomIndex * probe atomIndex
      = dir atomU * probe atomU + dir atomV * probe atomV
        + dir atomT * probe atomT := by
  have hnotU : atomU ∉ ({atomV, atomT} : Finset (Fin size)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hUV heq
    · exact hUT (Finset.mem_singleton.mp hmem')
  have hnotV : atomV ∉ ({atomT} : Finset (Fin size)) := fun hmem =>
    hVT (Finset.mem_singleton.mp hmem)
  have hrestrict : ∑ atomIndex : Fin size, dir atomIndex * probe atomIndex
      = ∑ atomIndex ∈ ({atomU, atomV, atomT} : Finset (Fin size)),
          dir atomIndex * probe atomIndex := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    obtain ⟨hcu, hcv, hct⟩ := notMem_triple.mp hnot
    rw [hsupp atomIndex hcu hcv hct, zero_mul]
  rw [hrestrict, Finset.sum_insert hnotU, Finset.sum_insert hnotV,
    Finset.sum_singleton]
  ring

/-! ## Layer 2 — the annihilation and the pullback -/

/-- **THE ANNIHILATION.**  At a both-parallel pair, the basis columns
annihilate the pair kernel vector: the two carriers restrict to the pair
proportionally, and every other basis direction vanishes there. -/
theorem bothParallel_pairKernel_annihilated
    (basisLabel : Fin basisCount → activeIndex)
    {slotA slotB : Fin basisCount} {atomA1 atomA2 : Fin size}
    (hne : atomA1 ≠ atomA2)
    (hdetAB : tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomA2
      - tightDir (basisLabel slotA) atomA2
        * tightDir (basisLabel slotB) atomA1 = 0)
    (hvanish : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) atomA1 = 0
        ∧ tightDir (basisLabel columnIndex) atomA2 = 0) :
    (tightBasisColumns tightDir basisLabel)ᵀ
        *ᵥ pairKernelVec (tightDir (basisLabel slotA) atomA1)
            (tightDir (basisLabel slotA) atomA2) atomA1 atomA2 = 0 := by
  refine basis_transpose_mulVec_pairKernelVec hne _ _ ?_
  intro columnIndex
  by_cases hA : columnIndex = slotA
  · rw [hA]
    ring
  · by_cases hB : columnIndex = slotB
    · rw [hB]
      linear_combination -hdetAB
    · obtain ⟨hone, htwo⟩ := hvanish columnIndex hA hB
      rw [hone, htwo]
      ring

/-- **THE PULLBACK.**  The left inverse pulls an assembly annihilation
back to the basis columns: the Gram core has a trivial kernel, and the
left inverse strips the columns from the Gram form. -/
theorem basisTranspose_zero_of_assembly_mulVec_zero
    (basisLabel : Fin basisCount → activeIndex)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hker : ∀ coeffVec : Fin basisCount → ℝ, H *ᵥ coeffVec = 0 → coeffVec = 0)
    {probe : Fin size → ℝ}
    (hzero : chartMultiplierAssembly activeSet activeWeight tightDir
      *ᵥ probe = 0) :
    (tightBasisColumns tightDir basisLabel)ᵀ *ᵥ probe = 0 := by
  refine hker _ ?_
  have happ := congrArg (fun ambientVec => L *ᵥ ambientVec) hzero
  simp only [Matrix.mulVec_zero] at happ
  rw [← hHform, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] at happ
  exact happ

/-! ## Layer 3 — the collapse of an annihilated probe -/

/-- **THE COLLAPSE.**  A probe annihilated by the basis columns of a
both-parallel C4 pattern vanishes at the two single atoms and satisfies
one balance per pair.  The collapse divides by the concentration
determinant, which the caller supplies as nonzero. -/
theorem bothParallel_annihilated_reads
    (basisLabel : Fin basisCount → activeIndex)
    {slotA slotB slotC slotD : Fin basisCount}
    {atomA1 atomA2 atomB atomC1 atomC2 atomD : Fin size}
    (hA12 : atomA1 ≠ atomA2) (hA1D : atomA1 ≠ atomD) (hA2D : atomA2 ≠ atomD)
    (hA1B : atomA1 ≠ atomB) (hA2B : atomA2 ≠ atomB)
    (hC12 : atomC1 ≠ atomC2) (hC1B : atomC1 ≠ atomB) (hC2B : atomC2 ≠ atomB)
    (hC1D : atomC1 ≠ atomD) (hC2D : atomC2 ≠ atomD)
    (hsuppA : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotA) atomIndex = 0)
    (hsuppB : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotB) atomIndex = 0)
    (hsuppC : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotC) atomIndex = 0)
    (hsuppD : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotD) atomIndex = 0)
    (hdetAB : tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomA2
      - tightDir (basisLabel slotA) atomA2
        * tightDir (basisLabel slotB) atomA1 = 0)
    (hdetCD : tightDir (basisLabel slotC) atomC1
        * tightDir (basisLabel slotD) atomC2
      - tightDir (basisLabel slotC) atomC2
        * tightDir (basisLabel slotD) atomC1 = 0)
    (hqAa1 : tightDir (basisLabel slotA) atomA1 ≠ 0)
    (hqBb : tightDir (basisLabel slotB) atomB ≠ 0)
    (hDelta : tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomB
        * tightDir (basisLabel slotC) atomC1
        * tightDir (basisLabel slotD) atomD
      - tightDir (basisLabel slotB) atomA1
        * tightDir (basisLabel slotA) atomD
        * tightDir (basisLabel slotD) atomC1
        * tightDir (basisLabel slotC) atomB ≠ 0)
    {probe : Fin size → ℝ}
    (hzero : (tightBasisColumns tightDir basisLabel)ᵀ *ᵥ probe = 0) :
    probe atomB = 0 ∧ probe atomD = 0
      ∧ tightDir (basisLabel slotA) atomA1 * probe atomA1
          + tightDir (basisLabel slotA) atomA2 * probe atomA2 = 0
      ∧ tightDir (basisLabel slotC) atomC1 * probe atomC1
          + tightDir (basisLabel slotC) atomC2 * probe atomC2 = 0 := by
  have hrowA := congrFun hzero slotA
  have hrowB := congrFun hzero slotB
  have hrowC := congrFun hzero slotC
  have hrowD := congrFun hzero slotD
  rw [Pi.zero_apply, basisColumns_transpose_dot basisLabel probe slotA,
    triple_dot_collapse hA12 hA1D hA2D hsuppA] at hrowA
  rw [Pi.zero_apply, basisColumns_transpose_dot basisLabel probe slotB,
    triple_dot_collapse hA12 hA1B hA2B hsuppB] at hrowB
  rw [Pi.zero_apply, basisColumns_transpose_dot basisLabel probe slotC,
    triple_dot_collapse hC12 hC1B hC2B hsuppC] at hrowC
  rw [Pi.zero_apply, basisColumns_transpose_dot basisLabel probe slotD,
    triple_dot_collapse hC12 hC1D hC2D hsuppD] at hrowD
  have hI : tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomB * probe atomB
      - tightDir (basisLabel slotB) atomA1
        * tightDir (basisLabel slotA) atomD * probe atomD = 0 := by
    linear_combination tightDir (basisLabel slotA) atomA1 * hrowB
      - tightDir (basisLabel slotB) atomA1 * hrowA - probe atomA2 * hdetAB
  have hII : tightDir (basisLabel slotD) atomC1
        * tightDir (basisLabel slotC) atomB * probe atomB
      - tightDir (basisLabel slotC) atomC1
        * tightDir (basisLabel slotD) atomD * probe atomD = 0 := by
    linear_combination tightDir (basisLabel slotD) atomC1 * hrowC
      - tightDir (basisLabel slotC) atomC1 * hrowD + probe atomC2 * hdetCD
  have hIII : probe atomD
      * (tightDir (basisLabel slotA) atomA1
          * tightDir (basisLabel slotB) atomB
          * tightDir (basisLabel slotC) atomC1
          * tightDir (basisLabel slotD) atomD
        - tightDir (basisLabel slotB) atomA1
          * tightDir (basisLabel slotA) atomD
          * tightDir (basisLabel slotD) atomC1
          * tightDir (basisLabel slotC) atomB) = 0 := by
    linear_combination tightDir (basisLabel slotD) atomC1
        * tightDir (basisLabel slotC) atomB * hI
      - tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomB * hII
  have hprobeD : probe atomD = 0 := by
    rcases mul_eq_zero.mp hIII with hcase | hcase
    · exact hcase
    · exact absurd hcase hDelta
  have hprobeB : probe atomB = 0 := by
    rw [hprobeD] at hI
    have hprod : tightDir (basisLabel slotA) atomA1
        * (tightDir (basisLabel slotB) atomB * probe atomB) = 0 := by
      linear_combination hI
    rcases mul_eq_zero.mp hprod with hcase | hcase
    · exact absurd hcase hqAa1
    · rcases mul_eq_zero.mp hcase with hcase' | hcase'
      · exact absurd hcase' hqBb
      · exact hcase'
  refine ⟨hprobeB, hprobeD, ?_, ?_⟩
  · rw [hprobeD] at hrowA
    linear_combination hrowA
  · rw [hprobeB] at hrowC
    linear_combination hrowC

/-! ## Layer 4 — the projected kernel reads -/

/-- **THE PROJECTED READS.**  The chart's image of the pair kernel
vector stays annihilated by the basis columns: the chain runs the
annihilation, the Gram form, the commutation, and the pullback.  The
collapse then reads its four coordinates. -/
theorem bothParallel_projected_kernel_reads
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hker : ∀ coeffVec : Fin basisCount → ℝ, H *ᵥ coeffVec = 0 → coeffVec = 0)
    {slotA slotB slotC slotD : Fin basisCount}
    {atomA1 atomA2 atomB atomC1 atomC2 atomD : Fin size}
    (hA12 : atomA1 ≠ atomA2) (hA1D : atomA1 ≠ atomD) (hA2D : atomA2 ≠ atomD)
    (hA1B : atomA1 ≠ atomB) (hA2B : atomA2 ≠ atomB)
    (hC12 : atomC1 ≠ atomC2) (hC1B : atomC1 ≠ atomB) (hC2B : atomC2 ≠ atomB)
    (hC1D : atomC1 ≠ atomD) (hC2D : atomC2 ≠ atomD)
    (hsuppA : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotA) atomIndex = 0)
    (hsuppB : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotB) atomIndex = 0)
    (hsuppC : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotC) atomIndex = 0)
    (hsuppD : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotD) atomIndex = 0)
    (hdetAB : tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomA2
      - tightDir (basisLabel slotA) atomA2
        * tightDir (basisLabel slotB) atomA1 = 0)
    (hdetCD : tightDir (basisLabel slotC) atomC1
        * tightDir (basisLabel slotD) atomC2
      - tightDir (basisLabel slotC) atomC2
        * tightDir (basisLabel slotD) atomC1 = 0)
    (hqAa1 : tightDir (basisLabel slotA) atomA1 ≠ 0)
    (hqBb : tightDir (basisLabel slotB) atomB ≠ 0)
    (hDelta : tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomB
        * tightDir (basisLabel slotC) atomC1
        * tightDir (basisLabel slotD) atomD
      - tightDir (basisLabel slotB) atomA1
        * tightDir (basisLabel slotA) atomD
        * tightDir (basisLabel slotD) atomC1
        * tightDir (basisLabel slotC) atomB ≠ 0)
    {pairSlot : Fin basisCount} {pairAtomOne pairAtomTwo : Fin size}
    (hann : (tightBasisColumns tightDir basisLabel)ᵀ
        *ᵥ pairKernelVec (tightDir (basisLabel pairSlot) pairAtomOne)
            (tightDir (basisLabel pairSlot) pairAtomTwo)
            pairAtomOne pairAtomTwo = 0) :
    (projection *ᵥ pairKernelVec (tightDir (basisLabel pairSlot) pairAtomOne)
        (tightDir (basisLabel pairSlot) pairAtomTwo)
        pairAtomOne pairAtomTwo) atomB = 0
      ∧ (projection *ᵥ pairKernelVec (tightDir (basisLabel pairSlot) pairAtomOne)
          (tightDir (basisLabel pairSlot) pairAtomTwo)
          pairAtomOne pairAtomTwo) atomD = 0
      ∧ tightDir (basisLabel slotA) atomA1
          * (projection *ᵥ pairKernelVec
              (tightDir (basisLabel pairSlot) pairAtomOne)
              (tightDir (basisLabel pairSlot) pairAtomTwo)
              pairAtomOne pairAtomTwo) atomA1
        + tightDir (basisLabel slotA) atomA2
          * (projection *ᵥ pairKernelVec
              (tightDir (basisLabel pairSlot) pairAtomOne)
              (tightDir (basisLabel pairSlot) pairAtomTwo)
              pairAtomOne pairAtomTwo) atomA2 = 0
      ∧ tightDir (basisLabel slotC) atomC1
          * (projection *ᵥ pairKernelVec
              (tightDir (basisLabel pairSlot) pairAtomOne)
              (tightDir (basisLabel pairSlot) pairAtomTwo)
              pairAtomOne pairAtomTwo) atomC1
        + tightDir (basisLabel slotC) atomC2
          * (projection *ᵥ pairKernelVec
              (tightDir (basisLabel pairSlot) pairAtomOne)
              (tightDir (basisLabel pairSlot) pairAtomTwo)
              pairAtomOne pairAtomTwo) atomC2 = 0 := by
  have hassembly := assembly_mulVec_of_basis_transpose_zero hHform hann
  have hprojected := assembly_mulVec_projection_pairKernelVec hdata hassembly
  have hpulled := basisTranspose_zero_of_assembly_mulVec_zero basisLabel hleft
    hHform hker hprojected
  exact bothParallel_annihilated_reads basisLabel hA12 hA1D hA2D hA1B hA2B
    hC12 hC1B hC2B hC1D hC2D hsuppA hsuppB hsuppC hsuppD hdetAB hdetCD
    hqAa1 hqBb hDelta hpulled

/-! ## Layer 5 — the entry forms of the reads -/

/-- A vanished single-atom coordinate of a projected kernel vector is the
pair proportionality of that chart row. -/
theorem pair_row_proportional_of_reads
    {firstCoord secondCoord : ℝ} {atomOne atomTwo atomRow : Fin size}
    (hne : atomOne ≠ atomTwo)
    (hread : (projection *ᵥ pairKernelVec firstCoord secondCoord
        atomOne atomTwo) atomRow = 0) :
    projection atomRow atomOne * secondCoord
      - projection atomRow atomTwo * firstCoord = 0 := by
  rw [← assembly_row_pairKernelVec hne atomRow]
  exact hread

/-- A pair balance of a projected kernel vector in entry form. -/
theorem pair_balance_of_reads
    {firstCoord secondCoord : ℝ} {atomOne atomTwo : Fin size}
    {balanceCoordOne balanceCoordTwo : ℝ} {atomRowOne atomRowTwo : Fin size}
    (hne : atomOne ≠ atomTwo)
    (hread : balanceCoordOne * (projection *ᵥ pairKernelVec firstCoord
          secondCoord atomOne atomTwo) atomRowOne
        + balanceCoordTwo * (projection *ᵥ pairKernelVec firstCoord
          secondCoord atomOne atomTwo) atomRowTwo = 0) :
    balanceCoordOne * (projection atomRowOne atomOne * secondCoord
        - projection atomRowOne atomTwo * firstCoord)
      + balanceCoordTwo * (projection atomRowTwo atomOne * secondCoord
        - projection atomRowTwo atomTwo * firstCoord) = 0 := by
  rw [← assembly_row_pairKernelVec hne atomRowOne,
    ← assembly_row_pairKernelVec hne atomRowTwo]
  exact hread

/-! ## Layer 6 — the rigidity consumers -/

/-- **THE TWIN WEIGHTS.**  The pair balance of a pair's own projected
kernel vector, with equal coordinate squares and the chart symmetry,
forces equal diagonal chart entries on the pair. -/
theorem bothParallel_twin_weights
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} {atomOne atomTwo : Fin size}
    (hne : atomOne ≠ atomTwo)
    (hone : tightDir label atomOne ≠ 0) (htwo : tightDir label atomTwo ≠ 0)
    (hsq : tightDir label atomOne ^ 2 = tightDir label atomTwo ^ 2)
    (hbalance : tightDir label atomOne
        * (projection *ᵥ pairKernelVec (tightDir label atomOne)
            (tightDir label atomTwo) atomOne atomTwo) atomOne
      + tightDir label atomTwo
        * (projection *ᵥ pairKernelVec (tightDir label atomOne)
            (tightDir label atomTwo) atomOne atomTwo) atomTwo = 0) :
    projection atomOne atomOne = projection atomTwo atomTwo := by
  have hentry := pair_balance_of_reads hne hbalance
  have hsymm := projection_entry_symm hdata atomTwo atomOne
  have hproduct : tightDir label atomOne * tightDir label atomTwo
      * (projection atomOne atomOne - projection atomTwo atomTwo) = 0 := by
    linear_combination hentry + projection atomOne atomTwo * hsq
      - tightDir label atomTwo ^ 2 * hsymm
  rcases mul_eq_zero.mp hproduct with hcase | hcase
  · rcases mul_eq_zero.mp hcase with hcase' | hcase'
    · exact absurd hcase' hone
    · exact absurd hcase' htwo
  · linarith [hcase]

/-- **THE EQUAL PAIR DIAGONAL.**  The two eigen rows of a pair carrier,
the pair proportionality of the anchor column, and equal coordinate
squares force equal gap diagonal entries on the pair. -/
theorem bothParallel_pair_diag_eq
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomOne atomTwo atomAnchor : Fin size}
    (h12 : atomOne ≠ atomTwo) (h1A : atomOne ≠ atomAnchor)
    (h2A : atomTwo ≠ atomAnchor)
    (hrowOne : atomOne ∈ activeSubset label)
    (hrowTwo : atomTwo ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      atomIndex ≠ atomAnchor → tightDir label atomIndex = 0)
    (hone : tightDir label atomOne ≠ 0) (htwo : tightDir label atomTwo ≠ 0)
    (hsq : tightDir label atomOne ^ 2 = tightDir label atomTwo ^ 2)
    (hanchor : chartStationaryGap projection weight atomAnchor atomOne
        * tightDir label atomTwo
      - chartStationaryGap projection weight atomAnchor atomTwo
        * tightDir label atomOne = 0) :
    chartStationaryGap projection weight atomOne atomOne
      = chartStationaryGap projection weight atomTwo atomTwo := by
  have hrow1 := gap_row_eigen_triple hdata hmem hrowOne h12 h1A h2A hsupp
  have hrow2 := gap_row_eigen_triple hdata hmem hrowTwo h12 h1A h2A hsupp
  have hsymm12 := gap_entry_symm hdata atomOne atomTwo
  have hsymm1A := gap_entry_symm hdata atomOne atomAnchor
  have hsymm2A := gap_entry_symm hdata atomTwo atomAnchor
  have hproduct : tightDir label atomOne * tightDir label atomTwo
      * (chartStationaryGap projection weight atomOne atomOne
        - chartStationaryGap projection weight atomTwo atomTwo) = 0 := by
    linear_combination tightDir label atomTwo * hrow1
      - tightDir label atomOne * hrow2
      + chartStationaryGap projection weight atomTwo atomOne * hsq
      - tightDir label atomTwo ^ 2 * hsymm12
      - tightDir label atomAnchor * tightDir label atomTwo * hsymm1A
      + tightDir label atomAnchor * tightDir label atomOne * hsymm2A
      - tightDir label atomAnchor * hanchor
  rcases mul_eq_zero.mp hproduct with hcase | hcase
  · rcases mul_eq_zero.mp hcase with hcase' | hcase'
    · exact absurd hcase' hone
    · exact absurd hcase' htwo
  · linarith [hcase]

/-! ## Layer 7 — the rigidity capstone -/

/-- **THE RIGIDITY CAPSTONE.**  At every both-parallel C4 stationary
datum with a left inverse and a kernel-free Gram core, the chart's
images of the two pair kernel vectors satisfy the four reads each.  The
degenerate concentration determinant dies inside the proof through the
landed dependent kill, and only the independent case reaches the
conclusion. -/
theorem bothParallel_kernel_rigidity
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hker : ∀ coeffVec : Fin basisCount → ℝ, H *ᵥ coeffVec = 0 → coeffVec = 0)
    {slotA slotB slotC slotD : Fin basisCount}
    (hCA : slotC ≠ slotA) (hCB : slotC ≠ slotB) (hCD : slotC ≠ slotD)
    {atomA1 atomA2 atomB atomC1 atomC2 atomD : Fin size}
    (hA12 : atomA1 ≠ atomA2) (hA1D : atomA1 ≠ atomD) (hA2D : atomA2 ≠ atomD)
    (hA1B : atomA1 ≠ atomB) (hA2B : atomA2 ≠ atomB)
    (hC12 : atomC1 ≠ atomC2) (hC1B : atomC1 ≠ atomB) (hC2B : atomC2 ≠ atomB)
    (hC1D : atomC1 ≠ atomD) (hC2D : atomC2 ≠ atomD) (hBD : atomB ≠ atomD)
    (hsuppA : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotA) atomIndex = 0)
    (hsuppB : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotB) atomIndex = 0)
    (hsuppC : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotC) atomIndex = 0)
    (hsuppD : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotD) atomIndex = 0)
    (hdetAB : tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomA2
      - tightDir (basisLabel slotA) atomA2
        * tightDir (basisLabel slotB) atomA1 = 0)
    (hdetCD : tightDir (basisLabel slotC) atomC1
        * tightDir (basisLabel slotD) atomC2
      - tightDir (basisLabel slotC) atomC2
        * tightDir (basisLabel slotD) atomC1 = 0)
    (hvanishA : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) atomA1 = 0
        ∧ tightDir (basisLabel columnIndex) atomA2 = 0)
    (hvanishC : ∀ columnIndex, columnIndex ≠ slotC → columnIndex ≠ slotD →
      tightDir (basisLabel columnIndex) atomC1 = 0
        ∧ tightDir (basisLabel columnIndex) atomC2 = 0)
    (hqAa1 : tightDir (basisLabel slotA) atomA1 ≠ 0)
    (hqBb : tightDir (basisLabel slotB) atomB ≠ 0)
    (hqDc1 : tightDir (basisLabel slotD) atomC1 ≠ 0) :
    ((projection *ᵥ pairKernelVec (tightDir (basisLabel slotA) atomA1)
        (tightDir (basisLabel slotA) atomA2) atomA1 atomA2) atomB = 0
      ∧ (projection *ᵥ pairKernelVec (tightDir (basisLabel slotA) atomA1)
          (tightDir (basisLabel slotA) atomA2) atomA1 atomA2) atomD = 0
      ∧ tightDir (basisLabel slotA) atomA1
          * (projection *ᵥ pairKernelVec (tightDir (basisLabel slotA) atomA1)
              (tightDir (basisLabel slotA) atomA2) atomA1 atomA2) atomA1
        + tightDir (basisLabel slotA) atomA2
          * (projection *ᵥ pairKernelVec (tightDir (basisLabel slotA) atomA1)
              (tightDir (basisLabel slotA) atomA2) atomA1 atomA2) atomA2 = 0
      ∧ tightDir (basisLabel slotC) atomC1
          * (projection *ᵥ pairKernelVec (tightDir (basisLabel slotA) atomA1)
              (tightDir (basisLabel slotA) atomA2) atomA1 atomA2) atomC1
        + tightDir (basisLabel slotC) atomC2
          * (projection *ᵥ pairKernelVec (tightDir (basisLabel slotA) atomA1)
              (tightDir (basisLabel slotA) atomA2) atomA1 atomA2) atomC2 = 0)
    ∧ ((projection *ᵥ pairKernelVec (tightDir (basisLabel slotC) atomC1)
        (tightDir (basisLabel slotC) atomC2) atomC1 atomC2) atomB = 0
      ∧ (projection *ᵥ pairKernelVec (tightDir (basisLabel slotC) atomC1)
          (tightDir (basisLabel slotC) atomC2) atomC1 atomC2) atomD = 0
      ∧ tightDir (basisLabel slotA) atomA1
          * (projection *ᵥ pairKernelVec (tightDir (basisLabel slotC) atomC1)
              (tightDir (basisLabel slotC) atomC2) atomC1 atomC2) atomA1
        + tightDir (basisLabel slotA) atomA2
          * (projection *ᵥ pairKernelVec (tightDir (basisLabel slotC) atomC1)
              (tightDir (basisLabel slotC) atomC2) atomC1 atomC2) atomA2 = 0
      ∧ tightDir (basisLabel slotC) atomC1
          * (projection *ᵥ pairKernelVec (tightDir (basisLabel slotC) atomC1)
              (tightDir (basisLabel slotC) atomC2) atomC1 atomC2) atomC1
        + tightDir (basisLabel slotC) atomC2
          * (projection *ᵥ pairKernelVec (tightDir (basisLabel slotC) atomC1)
              (tightDir (basisLabel slotC) atomC2) atomC1 atomC2) atomC2 = 0) := by
  by_cases hDelta : tightDir (basisLabel slotA) atomA1
      * tightDir (basisLabel slotB) atomB
      * tightDir (basisLabel slotC) atomC1
      * tightDir (basisLabel slotD) atomD
    - tightDir (basisLabel slotB) atomA1
      * tightDir (basisLabel slotA) atomD
      * tightDir (basisLabel slotD) atomC1
      * tightDir (basisLabel slotC) atomB = 0
  · exfalso
    have hsuppR : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
        (tightDir (basisLabel slotB) atomA1 • tightDir (basisLabel slotA)
          - tightDir (basisLabel slotA) atomA1 • tightDir (basisLabel slotB))
          atomIndex = 0 :=
      bothParallel_concentration_support hdetAB hsuppA hsuppB
    have hsuppR' : ∀ atomIndex, atomIndex ≠ atomD → atomIndex ≠ atomB →
        (tightDir (basisLabel slotD) atomC1 • tightDir (basisLabel slotC)
          - tightDir (basisLabel slotC) atomC1 • tightDir (basisLabel slotD))
          atomIndex = 0 :=
      bothParallel_concentration_support hdetCD hsuppC hsuppD
    have hval1 : (tightDir (basisLabel slotB) atomA1
          • tightDir (basisLabel slotA)
        - tightDir (basisLabel slotA) atomA1
          • tightDir (basisLabel slotB)) atomB
        = -(tightDir (basisLabel slotA) atomA1
          * tightDir (basisLabel slotB) atomB) :=
      bothParallel_concentration_value_single hA1B.symm hA2B.symm hBD hsuppA
    have hval2 : (tightDir (basisLabel slotB) atomA1
          • tightDir (basisLabel slotA)
        - tightDir (basisLabel slotA) atomA1
          • tightDir (basisLabel slotB)) atomD
        = tightDir (basisLabel slotB) atomA1
          * tightDir (basisLabel slotA) atomD :=
      bothParallel_concentration_value_anchor hA1D.symm hA2D.symm hBD.symm
        hsuppB
    have hval3 : (tightDir (basisLabel slotD) atomC1
          • tightDir (basisLabel slotC)
        - tightDir (basisLabel slotC) atomC1
          • tightDir (basisLabel slotD)) atomD
        = -(tightDir (basisLabel slotC) atomC1
          * tightDir (basisLabel slotD) atomD) :=
      bothParallel_concentration_value_single hC1D.symm hC2D.symm hBD.symm
        hsuppC
    have hval4 : (tightDir (basisLabel slotD) atomC1
          • tightDir (basisLabel slotC)
        - tightDir (basisLabel slotC) atomC1
          • tightDir (basisLabel slotD)) atomB
        = tightDir (basisLabel slotD) atomC1
          * tightDir (basisLabel slotC) atomB :=
      bothParallel_concentration_value_anchor hC1B.symm hC2B.symm hBD hsuppD
    refine false_of_bothParallel_concentrations_dependent basisLabel hleft
      hCA hCB hCD rfl rfl hsuppR
      (fun atomIndex hnotB hnotD => hsuppR' atomIndex hnotD hnotB) ?_ ?_ hqDc1
    · rw [hval1, hval2, hval3, hval4]
      linear_combination hDelta
    · rw [hval1]
      exact neg_ne_zero.mpr (mul_ne_zero hqAa1 hqBb)
  · constructor
    · exact bothParallel_projected_kernel_reads hdata basisLabel hleft hHform
        hker hA12 hA1D hA2D hA1B hA2B hC12 hC1B hC2B hC1D hC2D hsuppA hsuppB
        hsuppC hsuppD hdetAB hdetCD hqAa1 hqBb hDelta
        (bothParallel_pairKernel_annihilated basisLabel hA12 hdetAB hvanishA)
    · exact bothParallel_projected_kernel_reads hdata basisLabel hleft hHform
        hker hA12 hA1D hA2D hA1B hA2B hC12 hC1B hC2B hC1D hC2D hsuppA hsuppB
        hsuppC hsuppD hdetAB hdetCD hqAa1 hqBb hDelta
        (bothParallel_pairKernel_annihilated basisLabel hC12 hdetCD hvanishC)

end Gtz

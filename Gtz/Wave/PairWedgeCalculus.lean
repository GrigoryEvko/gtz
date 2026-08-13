import Gtz.Wave.SharedPairCaptureNarrowing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The pair wedge calculus — the sharer rows meet the kernel direction

The positive bridge narrows the support-two closure to the outer sharer
kill with strictly positive shifted pair weights.  The floor dual of the
probe layer names the tight rows of the sharers as the binding family.
This file lands the row calculus of that kill: every sharer row, read
against the pair kernel direction, prices the sharer wedge.

The mechanism, in five layers:

1. **The kernel row laws.**  The two tight rows of the pair column say
   that the pair gap block has the pair direction as an eigenvector.
   Read against the kernel direction, the block acts by the complement
   eigenvalue: the trace minus the value.
2. **The triple support read.**  The action of a matrix row on a vector
   with a three-atom support reads three entries.  Every block has three
   atoms, thus every tight row is such a read.
3. **The sharer wedge laws.**  A sharer with the two pair atoms in its
   block couples its wedge to the third-atom column: the complement
   excess times the wedge is the third-atom coupling.  A sharer with one
   pair atom couples through the pair cross entry.
4. **The third-atom read of the pair block.**  The third row of the pair
   column annihilates, thus the wedge coefficient at the third atom
   collapses to one gap entry.
5. **The wedge energy.**  The assembly quadratic of the kernel direction
   is the multiplier-weighted sum of the squared wedges, and the
   assembly pair minor caps it by one third.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.pair_gap_kernel_row_first`, `Gtz.pair_gap_kernel_row_second` —
  **THE KERNEL ROW LAWS.**
* `Gtz.mulVec_apply_of_triple_support` — **THE TRIPLE SUPPORT READ.**
* `Gtz.chartStationaryGap_entry_symm` — the gap entry symmetry.
* `Gtz.bothPair_sharer_row_wedge`, `Gtz.bothPair_sharer_wedge_law` —
  **THE SHARER WEDGE LAWS.**
* `Gtz.singlePair_sharer_wedge_law` — the one-atom sharer law.
* `Gtz.pair_third_wedge_read` — **THE THIRD-ATOM READ.**
* `Gtz.assembly_pairKernel_wedge_sum`, `Gtz.assembly_entry_symm`,
  `Gtz.wedge_energy_eq`, `Gtz.wedge_energy_le_third` — **THE WEDGE
  ENERGY.**
* `Gtz.RankFourFrame.false_of_vanishing_basis_wedges` — **THE
  ALIGNED-WEDGE KILL.**
* `Gtz.rankFourSupportTwoClosed_of_wedge_outer_kill` — **THE WEDGE
  BRIDGE.**

## Vacuity

The closure statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no
crux exists, thus no frame exists.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## Layer 0 — the gap entry symmetry -/

/-- The stationary gap has symmetric entries: the chart is symmetric and
the diagonal correction is diagonal. -/
theorem chartStationaryGap_entry_symm
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomA atomB : Fin size) :
    chartStationaryGap projection weight atomA atomB
      = chartStationaryGap projection weight atomB atomA := by
  have hproj : projection atomA atomB = projection atomB atomA := by
    have hentry := congrFun (congrFun hdata.isSymmetric atomA) atomB
    rw [Matrix.transpose_apply] at hentry
    exact hentry.symm
  by_cases hAB : atomA = atomB
  · rw [hAB]
  · simp only [chartStationaryGap, Matrix.sub_apply]
    rw [Matrix.diagonal_apply_ne _ hAB, Matrix.diagonal_apply_ne _ (Ne.symm hAB),
      sub_zero, sub_zero, hproj]

/-! ## Layer 1 — the kernel row laws -/

/-- **THE FIRST KERNEL ROW LAW.**  The pair gap block acts on the kernel
direction by the complement eigenvalue at the first coordinate: this is
the second tight row of the pair column, rearranged. -/
theorem pair_gap_kernel_row_first
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV)
    (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomU atomU * tightDir label atomV
        - chartStationaryGap projection weight atomU atomV * tightDir label atomU
      = (chartStationaryGap projection weight atomU atomU
          + chartStationaryGap projection weight atomV atomV - value)
        * tightDir label atomV := by
  have hrowV := hdata.tightDir_isTight label hmem atomV hmemV
  rw [mulVec_apply_of_pair_support _ hne hsupp atomV] at hrowV
  have hsymmUV := chartStationaryGap_entry_symm hdata atomU atomV
  linear_combination (-1 : ℝ) * hrowV
    - tightDir label atomU * hsymmUV

/-- **THE SECOND KERNEL ROW LAW.**  The pair gap block acts on the
kernel direction by the complement eigenvalue at the second coordinate:
this is the first tight row of the pair column, rearranged. -/
theorem pair_gap_kernel_row_second
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomU atomV * tightDir label atomV
        - chartStationaryGap projection weight atomV atomV * tightDir label atomU
      = -((chartStationaryGap projection weight atomU atomU
            + chartStationaryGap projection weight atomV atomV - value)
          * tightDir label atomU) := by
  have hrowU := hdata.tightDir_isTight label hmem atomU hmemU
  rw [mulVec_apply_of_pair_support _ hne hsupp atomU] at hrowU
  linear_combination hrowU

/-! ## Layer 2 — the triple support read and the gap symmetry -/

/-- **THE TRIPLE SUPPORT READ.**  The action of a matrix row on a vector
with a three-atom support reads three entries. -/
theorem mulVec_apply_of_triple_support {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) {atomA atomB atomC : Fin n}
    (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC) (hBC : atomB ≠ atomC)
    {q : Fin n → ℝ}
    (hsupp : ∀ atomIndex, atomIndex ≠ atomA → atomIndex ≠ atomB →
      atomIndex ≠ atomC → q atomIndex = 0)
    (rowIndex : Fin n) :
    (S *ᵥ q) rowIndex
      = S rowIndex atomA * q atomA + S rowIndex atomB * q atomB
        + S rowIndex atomC * q atomC := by
  have hterm : ∀ atomIndex : Fin n, S rowIndex atomIndex * q atomIndex
      = (if atomIndex = atomA then S rowIndex atomA * q atomA else 0)
        + (if atomIndex = atomB then S rowIndex atomB * q atomB else 0)
        + (if atomIndex = atomC then S rowIndex atomC * q atomC else 0) := by
    intro atomIndex
    by_cases hA : atomIndex = atomA
    · subst hA
      rw [if_pos rfl, if_neg hAB, if_neg hAC]
      ring
    by_cases hB : atomIndex = atomB
    · subst hB
      rw [if_neg hA, if_pos rfl, if_neg hBC]
      ring
    by_cases hC : atomIndex = atomC
    · subst hC
      rw [if_neg hA, if_neg hB, if_pos rfl]
      ring
    · rw [hsupp atomIndex hA hB hC, if_neg hA, if_neg hB, if_neg hC]
      ring
  show (∑ atomIndex : Fin n, S rowIndex atomIndex * q atomIndex) = _
  rw [Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ atomA, Finset.sum_ite_eq' Finset.univ atomB,
    Finset.sum_ite_eq' Finset.univ atomC]
  simp only [Finset.mem_univ, if_pos]

/-! ## Layer 3 — the sharer wedge laws -/

/-- **THE SHARER ROW WEDGE.**  For a label with the two pair atoms in
its block, the kernel combination of its two tight rows prices the value
times the wedge. -/
theorem bothPair_sharer_row_wedge
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {sharer : activeIndex} (hmemSharer : sharer ∈ activeSet)
    {atomU atomV : Fin size}
    (hmemU : atomU ∈ activeSubset sharer) (hmemV : atomV ∈ activeSubset sharer)
    (pairCoordU pairCoordV : ℝ) :
    pairCoordV * (chartStationaryGap projection weight *ᵥ tightDir sharer) atomU
        - pairCoordU * (chartStationaryGap projection weight *ᵥ tightDir sharer) atomV
      = value * (tightDir sharer atomU * pairCoordV
          - tightDir sharer atomV * pairCoordU) := by
  have hrowU := hdata.tightDir_isTight sharer hmemSharer atomU hmemU
  have hrowV := hdata.tightDir_isTight sharer hmemSharer atomV hmemV
  rw [hrowU, hrowV]
  ring

/-- **THE BOTH-PAIR SHARER WEDGE LAW.**  A sharer whose block is the two
pair atoms and one third atom couples its wedge to the third-atom
column: the complement excess times the wedge is the negative of the
third coordinate times the wedge coefficient of the third column. -/
theorem bothPair_sharer_wedge_law
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label sharer : activeIndex} (hmemLabel : label ∈ activeSet)
    (hmemSharer : sharer ∈ activeSet)
    {atomU atomV atomT : Fin size} (hUV : atomU ≠ atomV)
    (hUT : atomU ≠ atomT) (hVT : atomV ≠ atomT)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hmemUs : atomU ∈ activeSubset sharer) (hmemVs : atomV ∈ activeSubset sharer)
    (hsuppSharer : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0) :
    (chartStationaryGap projection weight atomU atomU
        + chartStationaryGap projection weight atomV atomV - 2 * value)
      * (tightDir sharer atomU * tightDir label atomV
          - tightDir sharer atomV * tightDir label atomU)
      = -(tightDir sharer atomT
          * (tightDir label atomV * chartStationaryGap projection weight atomU atomT
            - tightDir label atomU
              * chartStationaryGap projection weight atomV atomT)) := by
  have hrowWedge := bothPair_sharer_row_wedge hdata hmemSharer hmemUs hmemVs
    (tightDir label atomU) (tightDir label atomV)
  rw [mulVec_apply_of_triple_support _ hUV hUT hVT hsuppSharer atomU,
    mulVec_apply_of_triple_support _ hUV hUT hVT hsuppSharer atomV] at hrowWedge
  have hfirst := pair_gap_kernel_row_first hdata hmemLabel hUV hmemV hsupp
  have hsecond := pair_gap_kernel_row_second hdata hmemLabel hUV hmemU hsupp
  have hsymmUV := chartStationaryGap_entry_symm hdata atomU atomV
  linear_combination hrowWedge - tightDir sharer atomU * hfirst
    - tightDir sharer atomV * hsecond
    - tightDir sharer atomU * tightDir label atomU * hsymmUV

/-- **THE ONE-ATOM SHARER WEDGE LAW.**  A sharer with one pair atom and
two outer atoms couples its wedge through the pair cross entry and the
two outer columns. -/
theorem singlePair_sharer_wedge_law
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label sharer : activeIndex} (hmemLabel : label ∈ activeSet)
    (hmemSharer : sharer ∈ activeSet)
    {atomU atomV atomS atomT : Fin size} (hUV : atomU ≠ atomV)
    (hUS : atomU ≠ atomS) (hUT : atomU ≠ atomT) (hST : atomS ≠ atomT)
    (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hmemUs : atomU ∈ activeSubset sharer)
    (hsuppSharer : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomS →
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0) :
    (chartStationaryGap projection weight atomU atomU
        + chartStationaryGap projection weight atomV atomV - 2 * value)
      * (tightDir sharer atomU * tightDir label atomV)
      = -(tightDir sharer atomU * tightDir label atomU
            * chartStationaryGap projection weight atomU atomV)
        - tightDir label atomV
          * (tightDir sharer atomS * chartStationaryGap projection weight atomU atomS
            + tightDir sharer atomT
              * chartStationaryGap projection weight atomU atomT) := by
  have hrowU := hdata.tightDir_isTight sharer hmemSharer atomU hmemUs
  rw [mulVec_apply_of_triple_support _ hUS hUT hST hsuppSharer atomU] at hrowU
  have hfirst := pair_gap_kernel_row_first hdata hmemLabel hUV hmemV hsupp
  linear_combination tightDir label atomV * hrowU
    - tightDir sharer atomU * hfirst

/-! ## Layer 4 — the third-atom read of the pair block -/

/-- **THE THIRD-ATOM READ.**  The third tight row of the pair column
annihilates, thus the wedge coefficient of the third column collapses to
one gap entry against the unit norm. -/
theorem pair_third_wedge_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} {atomU atomV atomZ : Fin size} :
    tightDir label atomV
        * (tightDir label atomV * chartStationaryGap projection weight atomU atomZ
          - tightDir label atomU * chartStationaryGap projection weight atomV atomZ)
      = chartStationaryGap projection weight atomU atomZ
        * (tightDir label atomU ^ 2 + tightDir label atomV ^ 2)
        - tightDir label atomU
          * (chartStationaryGap projection weight atomZ atomU * tightDir label atomU
            + chartStationaryGap projection weight atomZ atomV
              * tightDir label atomV) := by
  have hsymmUZ := chartStationaryGap_entry_symm hdata atomU atomZ
  have hsymmVZ := chartStationaryGap_entry_symm hdata atomV atomZ
  linear_combination (-(tightDir label atomU ^ 2)) * hsymmUZ
    + (-(tightDir label atomU * tightDir label atomV)) * hsymmVZ

/-- The annihilated third row: the tight row of the pair column at its
third block atom reads zero. -/
theorem pair_third_row_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV atomZ : Fin size} (hUV : atomU ≠ atomV)
    (hUZ : atomU ≠ atomZ) (hVZ : atomV ≠ atomZ)
    (hmemZ : atomZ ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomZ atomU * tightDir label atomU
        + chartStationaryGap projection weight atomZ atomV * tightDir label atomV
      = 0 := by
  have hrowZ := hdata.tightDir_isTight label hmem atomZ hmemZ
  rw [mulVec_apply_of_pair_support _ hUV hsupp atomZ] at hrowZ
  rw [hsupp atomZ (Ne.symm hUZ) (Ne.symm hVZ), mul_zero] at hrowZ
  exact hrowZ

/-! ## Layer 5 — the wedge energy -/

/-- The assembly entries are symmetric: each summand is a product of two
coordinates. -/
theorem assembly_entry_symm (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    (atomA atomB : Fin size) :
    chartMultiplierAssembly activeSet activeWeight tightDir atomA atomB
      = chartMultiplierAssembly activeSet activeWeight tightDir atomB atomA := by
  rw [chartMultiplierAssembly_apply, chartMultiplierAssembly_apply]
  exact Finset.sum_congr rfl fun activeLabel _ => by ring

/-- **THE WEDGE ENERGY SUM.**  The assembly quadratic of the pair kernel
vector is the multiplier-weighted sum of the squared wedges. -/
theorem assembly_pairKernel_wedge_sum (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    {atomU atomV : Fin size} (hne : atomU ≠ atomV) (firstCoord secondCoord : ℝ) :
    pairKernelVec firstCoord secondCoord atomU atomV
        ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir
          *ᵥ pairKernelVec firstCoord secondCoord atomU atomV)
      = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * (secondCoord * tightDir activeLabel atomU
            - firstCoord * tightDir activeLabel atomV) ^ 2 := by
  rw [pairKernel_quadratic_read _ hne, chartMultiplierAssembly_apply,
    chartMultiplierAssembly_apply, chartMultiplierAssembly_apply,
    chartMultiplierAssembly_apply, Finset.sum_mul, ← Finset.sum_add_distrib,
    Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun activeLabel _ => by ring

/-- **THE WEDGE ENERGY READ.**  The wedge energy of the pair column is
the uniform diagonal minus the assembly cross mass. -/
theorem wedge_energy_eq
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    ∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * (tightDir label atomV * tightDir activeLabel atomU
          - tightDir label atomU * tightDir activeLabel atomV) ^ 2
      = ((size : ℝ))⁻¹
        - 2 * chartMultiplierAssembly activeSet activeWeight tightDir atomU atomV
          * (tightDir label atomU * tightDir label atomV) := by
  have hunit := pair_support_unit_read hdata hmem hne hsupp
  have hsum := assembly_pairKernel_wedge_sum activeSet activeWeight tightDir hne
    (tightDir label atomU) (tightDir label atomV)
  have hread := assembly_pairKernel_quadratic_read hdata hne
    (tightDir label atomU) (tightDir label atomV)
  have hsymm := assembly_entry_symm activeSet activeWeight tightDir atomU atomV
  rw [hsum, hunit, one_mul] at hread
  rw [hread, hsymm]
  ring

/-- **THE WEDGE ENERGY CAP.**  The wedge energy of the pair column is at
most one third: the assembly pair minor caps the cross mass, and the
unit norm caps the pair product. -/
theorem wedge_energy_le_third
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    ∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * (tightDir label atomV * tightDir activeLabel atomU
          - tightDir label atomU * tightDir activeLabel atomV) ^ 2
      ≤ 2 * ((size : ℝ))⁻¹ := by
  have hunit := pair_support_unit_read hdata hmem hne hsupp
  have heq := wedge_energy_eq hdata hmem hne hsupp
  have hminor := assembly_pair_offdiag_sq_le hdata hne
  have hinvPos : (0 : ℝ) < ((size : ℝ))⁻¹ :=
    inv_pos.mpr (size_cast_pos_of_isChartStationaryData hdata)
  have hfour : 4 * (tightDir label atomU * tightDir label atomV) ^ 2 ≤ 1 := by
    nlinarith [hunit, sq_nonneg (tightDir label atomU ^ 2
      - tightDir label atomV ^ 2)]
  have hscaled : 4 * (((size : ℝ))⁻¹) ^ 2
        * (tightDir label atomU * tightDir label atomV) ^ 2
      ≤ (((size : ℝ))⁻¹) ^ 2 := by
    nlinarith [hfour, sq_nonneg ((size : ℝ))⁻¹]
  rw [heq]
  nlinarith [hminor, hscaled, hinvPos,
    sq_nonneg (chartMultiplierAssembly activeSet activeWeight tightDir atomU atomV
      + 2 * ((size : ℝ))⁻¹ * (tightDir label atomU * tightDir label atomV))]

/-! ## Layer 6 — the aligned-wedge kill and the wedge bridge -/

/-- **THE ALIGNED-WEDGE KILL.**  A pair column whose basis wedges all
vanish dies at every frame.  The kernel direction passes through the
basis transpose, the capture aligns on the pair, the squeeze zeroes the
two shifted weights, and the parallel-pair field refuses.  This is the
strict generalization of the private-pair kill: the other columns can
carry the pair, if they restrict to it proportionally. -/
theorem RankFourFrame.false_of_vanishing_basis_wedges {crux : SixThreeCrux}
    (frame : RankFourFrame crux) (columnIndex : Fin 4)
    {atomU atomV : Fin 6} (hUV : atomU ≠ atomV)
    (hneU : frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0)
    (hneV : frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0)
    (hwedges : ∀ otherIndex : Fin 4,
      frame.tightDir (frame.basisLabel otherIndex) atomU
          * frame.tightDir (frame.basisLabel columnIndex) atomV
        - frame.tightDir (frame.basisLabel otherIndex) atomV
          * frame.tightDir (frame.basisLabel columnIndex) atomU = 0) : False := by
  classical
  have hdata := frame.hdata
  have hmem := frame.hmemAll columnIndex
  have hvalueNeg := frame.hvalueNeg
  set pairDir := frame.tightDir (frame.basisLabel columnIndex) with hdirDef
  have hbasisKernel : (tightBasisColumns frame.tightDir frame.basisLabel)ᵀ
      *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV = 0 :=
    basis_transpose_mulVec_pairKernelVec hUV _ _ hwedges
  have hassemblyKernel : chartMultiplierAssembly frame.activeSet frame.reducedWeight
      frame.tightDir *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV
      = 0 :=
    assembly_mulVec_of_basis_transpose_zero frame.hHform hbasisKernel
  have hcaptureKernel : ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
      *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV = 0 := by
    rw [← Matrix.mulVec_mulVec, hassemblyKernel, Matrix.mulVec_zero]
  have halignU : ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
          atomU atomU * pairDir atomV
      - ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
          atomU atomV * pairDir atomU = 0 := by
    have hentry := congrFun hcaptureKernel atomU
    rwa [mulVec_pairKernelVec_apply ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
      hUV (pairDir atomU) (pairDir atomV) atomU, Pi.zero_apply] at hentry
  have halignV : ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
          atomV atomU * pairDir atomV
      - ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
          atomV atomV * pairDir atomU = 0 := by
    have hentry := congrFun hcaptureKernel atomV
    rwa [mulVec_pairKernelVec_apply ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
      hUV (pairDir atomU) (pairDir atomV) atomV, Pi.zero_apply] at hentry
  have hunit : pairDir atomU ^ 2 + pairDir atomV ^ 2 = 1 :=
    pair_support_unit_read hdata hmem hUV hsupp
  have hquadRead : pairDir ⬝ᵥ (((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
        *ᵥ pairDir)
      = ((chartPointOfDesign crux.design).chart
          * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
          atomU atomU
        + ((chartPointOfDesign crux.design).chart
          * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
          atomV atomV := by
    rw [dotProduct_mulVec_of_pair_support ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
      hUV hsupp]
    linear_combination (-(pairDir atomV)) * halignU + (pairDir atomU) * halignV
      + (((chartPointOfDesign crux.design).chart
          * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
          atomU atomU
        + ((chartPointOfDesign crux.design).chart
          * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
          atomV atomV) * hunit
  have hdiagU := diagonal_projection_mul_multiplier_of_isChartStationaryData
    hdata atomU
  have hdiagV := diagonal_projection_mul_multiplier_of_isChartStationaryData
    hdata atomV
  have hrayleigh := capture_quadratic_le_of_isChartStationaryData hdata pairDir
  have henergy : pairDir ⬝ᵥ ((chartPointOfDesign crux.design).chart *ᵥ pairDir)
      = chartObjective (chartPointOfDesign crux.design)
        + ((chartPointOfDesign crux.design).weight atomU * pairDir atomU ^ 2
          + (chartPointOfDesign crux.design).weight atomV * pairDir atomV ^ 2) := by
    rw [tight_energy_read hdata hmem, pair_support_energy_read hUV hsupp]
  have hfloorU := capture_diagonal_nonneg_of_isChartStationaryData hdata atomU
  have hfloorV := capture_diagonal_nonneg_of_isChartStationaryData hdata atomV
  have htraceFloor := capture_trace_nonneg_of_isChartStationaryData hdata
  have hinv : (0 : ℝ) < (((6 : ℕ) : ℝ))⁻¹ := by norm_num
  have hsqU : (0 : ℝ) < pairDir atomU ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hneU))
  have hsqV : (0 : ℝ) < pairDir atomV ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hneV))
  have hbothZero : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomU = 0
      ∧ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomV = 0 := by
    rcases le_total ((chartPointOfDesign crux.design).weight atomU)
      ((chartPointOfDesign crux.design).weight atomV) with horder | horder
    · exact support_two_capture_squeeze hvalueNeg hinv htraceFloor hfloorU
        hfloorV hsqU.le hsqV hunit henergy
        (by rw [hquadRead, hdiagU, hdiagV]; ring) hrayleigh horder
    · have hswap := support_two_capture_squeeze hvalueNeg hinv htraceFloor
        hfloorV hfloorU hsqV.le hsqU (by linarith [hunit])
        (by rw [henergy]; ring)
        (by rw [hquadRead, hdiagU, hdiagV]; ring) hrayleigh horder
      exact ⟨hswap.2, hswap.1⟩
  exact frame.false_of_pair_shifted_weights_zero columnIndex hUV hneU hsupp
    hbothZero.1 hbothZero.2

/-- **THE WEDGE BRIDGE.**  The support-two closure follows from the
outer sharer kill with strictly positive shifted pair weights and one
nonzero basis wedge in hand.  Vanishing wedges die at the aligned-wedge
kill, and the zero propagation supplies the positives. -/
theorem rankFourSupportTwoClosed_of_wedge_outer_kill
    (killWedge : ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux)
      (columnIndex otherIndex : Fin 4) (atomU atomV atomT : Fin 6),
      (datumTightSupport frame.tightDir (frame.basisLabel columnIndex)).card = 2 →
      atomU ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0 →
      frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0 →
      (∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
        frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0) →
      otherIndex ≠ columnIndex →
      atomT ≠ atomU → atomT ≠ atomV →
      frame.tightDir (frame.basisLabel otherIndex) atomT ≠ 0 →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomU →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomV →
      ∀ wedgeIndex : Fin 4,
        frame.tightDir (frame.basisLabel wedgeIndex) atomU
            * frame.tightDir (frame.basisLabel columnIndex) atomV
          - frame.tightDir (frame.basisLabel wedgeIndex) atomV
            * frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0 →
      False) :
    RankFourSupportTwoClosed := by
  refine rankFourSupportTwoClosed_of_positive_shared_kill ?_
  intro crux frame columnIndex otherIndex atomU atomV atomT hcard hUV hneU hneV
    hsupp hneCol hTU hTV hneT hposU hposV
  by_cases hall : ∀ wedgeIndex : Fin 4,
      frame.tightDir (frame.basisLabel wedgeIndex) atomU
          * frame.tightDir (frame.basisLabel columnIndex) atomV
        - frame.tightDir (frame.basisLabel wedgeIndex) atomV
          * frame.tightDir (frame.basisLabel columnIndex) atomU = 0
  · exact frame.false_of_vanishing_basis_wedges columnIndex hUV hneU hneV
      hsupp hall
  · push Not at hall
    obtain ⟨wedgeIndex, hwedge⟩ := hall
    exact killWedge crux frame columnIndex otherIndex atomU atomV atomT hcard
      hUV hneU hneV hsupp hneCol hTU hTV hneT hposU hposV wedgeIndex hwedge

end Gtz

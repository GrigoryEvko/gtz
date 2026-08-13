import Gtz.Wave.PairWedgeCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The pair coupling calculus — the split diagonals and the separated sharer laws

The wedge bridge narrows the support-two closure to the outer sharer
kill with positive shifted pair weights and one nonzero basis wedge.
The floor probes of this session name the mechanism: the sharer rows and
the outside rows price every wedge through the gap couplings of the
pair.  This file lands that pricing calculus at the generic stationary
datum, thus the rank-four, rank-five, and rank-six outer-sharer bridges
all consume it.

The mechanism, in five layers:

1. **The split diagonals.**  The two pair rows of the pair column split
   the two diagonal gap entries through the complement excess: the left
   excess is the excess times the right square, and the right excess is
   the excess times the left square.  The cross entry follows in two
   scaled forms, division-free.
2. **The separated sharer laws.**  A sharer with the two pair atoms in
   its block obeys one law per pair row: the excess times a pair
   coordinate times the wedge is one third-atom coupling.  The aligned
   coupling annihilates, and the third tight row prices the third
   diagonal gap entry as the value plus the excess times the wedge
   square.
3. **The protrusion law.**  A both-pair sharer with a vanishing third
   coordinate has a vanishing wedge: the wedge lives on the protrusion.
4. **The one-atom sharer laws.**  A sharer with one pair atom couples
   the excess times its pair coordinate to its two outer couplings,
   scaled by a pair square.
5. **The kernel read and the demand.**  The kernel combination of any
   two gap rows at the pair reads the complement eigenvalue times the
   wedge plus the outer coupling sum — for every ambient vector.  The
   shared squeeze turns into the wedge energy demand: the wedge energy
   of the active set is at least the shifted pair mass minus the capped
   pair energy.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.pair_diagonal_balance` — the diagonal balance.
* `Gtz.pair_diagonal_split_left`, `Gtz.pair_diagonal_split_right` —
  **THE SPLIT DIAGONALS.**
* `Gtz.pair_cross_scaled_left`, `Gtz.pair_cross_scaled_right` — the
  scaled cross entries.
* `Gtz.bothPair_separated_left`, `Gtz.bothPair_separated_right` —
  **THE SEPARATED SHARER LAWS.**
* `Gtz.bothPair_aligned_annihilation` — the aligned coupling dies.
* `Gtz.bothPair_third_diagonal` — the third-diagonal pricing.
* `Gtz.pair_excess_pos` — the excess floor.
* `Gtz.bothPair_wedge_vanish_of_third_vanish` — **THE PROTRUSION LAW.**
* `Gtz.singlePair_scaled_left`, `Gtz.singlePair_scaled_right` — the
  one-atom sharer laws.
* `Gtz.gap_mulVec_entry` — the gap action entry.
* `Gtz.pair_kernel_gap_read` — **THE KERNEL READ.**
* `Gtz.wedge_energy_demand` — **THE WEDGE ENERGY DEMAND.**

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

/-! ## Layer 1 — the split diagonals -/

/-- **THE DIAGONAL BALANCE.**  The left excess weighted by the left
square equals the right excess weighted by the right square. -/
theorem pair_diagonal_balance
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    (chartStationaryGap projection weight atomU atomU - value)
        * tightDir label atomU ^ 2
      = (chartStationaryGap projection weight atomV atomV - value)
        * tightDir label atomV ^ 2 := by
  have hrowU := pair_row_left hdata hmem hUV hmemU hsupp
  have hrowV := pair_row_right hdata hmem hUV hmemV hsupp
  have hsymm := chartStationaryGap_entry_symm hdata atomU atomV
  linear_combination tightDir label atomU * hrowU - tightDir label atomV * hrowV
    - (tightDir label atomU * tightDir label atomV) * hsymm

/-- **THE LEFT SPLIT DIAGONAL.**  The left excess is the complement
excess times the right pair square. -/
theorem pair_diagonal_split_left
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomU atomU - value
      = (chartStationaryGap projection weight atomU atomU
          + chartStationaryGap projection weight atomV atomV - 2 * value)
        * tightDir label atomV ^ 2 := by
  have hAA := pair_diagonal_balance hdata hmem hUV hmemU hmemV hsupp
  have hunit := pair_support_unit_read hdata hmem hUV hsupp
  linear_combination hAA
    - (chartStationaryGap projection weight atomU atomU - value) * hunit

/-- **THE RIGHT SPLIT DIAGONAL.**  The right excess is the complement
excess times the left pair square. -/
theorem pair_diagonal_split_right
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomV atomV - value
      = (chartStationaryGap projection weight atomU atomU
          + chartStationaryGap projection weight atomV atomV - 2 * value)
        * tightDir label atomU ^ 2 := by
  have hAA := pair_diagonal_balance hdata hmem hUV hmemU hmemV hsupp
  have hunit := pair_support_unit_read hdata hmem hUV hsupp
  linear_combination -hAA
    - (chartStationaryGap projection weight atomV atomV - value) * hunit

/-- **THE LEFT SCALED CROSS.**  The cross entry times the right
coordinate, division-free. -/
theorem pair_cross_scaled_left
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomU atomV * tightDir label atomV
      = -((chartStationaryGap projection weight atomU atomU
            + chartStationaryGap projection weight atomV atomV - 2 * value)
          * (tightDir label atomU * tightDir label atomV ^ 2)) := by
  have hrowU := pair_row_left hdata hmem hUV hmemU hsupp
  have hsplitL := pair_diagonal_split_left hdata hmem hUV hmemU hmemV hsupp
  linear_combination hrowU - tightDir label atomU * hsplitL

/-- **THE RIGHT SCALED CROSS.**  The cross entry times the left
coordinate, division-free. -/
theorem pair_cross_scaled_right
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomU atomV * tightDir label atomU
      = -((chartStationaryGap projection weight atomU atomU
            + chartStationaryGap projection weight atomV atomV - 2 * value)
          * (tightDir label atomU ^ 2 * tightDir label atomV)) := by
  have hrowV := pair_row_right hdata hmem hUV hmemV hsupp
  have hsplitR := pair_diagonal_split_right hdata hmem hUV hmemU hmemV hsupp
  have hsymm := chartStationaryGap_entry_symm hdata atomU atomV
  linear_combination hrowV - tightDir label atomV * hsplitR
    + tightDir label atomU * hsymm

/-! ## Layer 2 — the separated sharer laws -/

/-- **THE LEFT SEPARATED LAW.**  For a sharer with the two pair atoms in
its block and one third atom, the left tight row alone prices the
excess times the right coordinate times the wedge as the negative left
third-atom coupling. -/
theorem bothPair_separated_left
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label sharer : activeIndex} (hmemLabel : label ∈ activeSet)
    (hmemSharer : sharer ∈ activeSet)
    {atomU atomV atomT : Fin size} (hUV : atomU ≠ atomV)
    (hUT : atomU ≠ atomT) (hVT : atomV ≠ atomT)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hneV : tightDir label atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hmemUs : atomU ∈ activeSubset sharer)
    (hsuppSharer : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0) :
    (chartStationaryGap projection weight atomU atomU
        + chartStationaryGap projection weight atomV atomV - 2 * value)
      * (tightDir label atomV
        * (tightDir sharer atomU * tightDir label atomV
          - tightDir sharer atomV * tightDir label atomU))
      = -(chartStationaryGap projection weight atomU atomT
          * tightDir sharer atomT) := by
  have hrowUs := hdata.tightDir_isTight sharer hmemSharer atomU hmemUs
  rw [mulVec_apply_of_triple_support _ hUV hUT hVT hsuppSharer atomU] at hrowUs
  have hsplitL := pair_diagonal_split_left hdata hmemLabel hUV hmemU hmemV hsupp
  have hcrossL := pair_cross_scaled_left hdata hmemLabel hUV hmemU hmemV hsupp
  have hscaled : tightDir label atomV
      * ((chartStationaryGap projection weight atomU atomU
            + chartStationaryGap projection weight atomV atomV - 2 * value)
          * (tightDir label atomV
            * (tightDir sharer atomU * tightDir label atomV
              - tightDir sharer atomV * tightDir label atomU))
        + chartStationaryGap projection weight atomU atomT
          * tightDir sharer atomT) = 0 := by
    linear_combination tightDir label atomV * hrowUs
      - (tightDir label atomV * tightDir sharer atomU) * hsplitL
      - tightDir sharer atomV * hcrossL
  have hinner := (mul_eq_zero.mp hscaled).resolve_left hneV
  linear_combination hinner

/-- **THE RIGHT SEPARATED LAW.**  The right tight row alone prices the
excess times the left coordinate times the wedge as the right third-atom
coupling. -/
theorem bothPair_separated_right
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label sharer : activeIndex} (hmemLabel : label ∈ activeSet)
    (hmemSharer : sharer ∈ activeSet)
    {atomU atomV atomT : Fin size} (hUV : atomU ≠ atomV)
    (hUT : atomU ≠ atomT) (hVT : atomV ≠ atomT)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hneU : tightDir label atomU ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hmemVs : atomV ∈ activeSubset sharer)
    (hsuppSharer : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0) :
    (chartStationaryGap projection weight atomU atomU
        + chartStationaryGap projection weight atomV atomV - 2 * value)
      * (tightDir label atomU
        * (tightDir sharer atomU * tightDir label atomV
          - tightDir sharer atomV * tightDir label atomU))
      = chartStationaryGap projection weight atomV atomT
        * tightDir sharer atomT := by
  have hrowVs := hdata.tightDir_isTight sharer hmemSharer atomV hmemVs
  rw [mulVec_apply_of_triple_support _ hUV hUT hVT hsuppSharer atomV] at hrowVs
  have hsplitR := pair_diagonal_split_right hdata hmemLabel hUV hmemU hmemV hsupp
  have hcrossR := pair_cross_scaled_right hdata hmemLabel hUV hmemU hmemV hsupp
  have hsymm := chartStationaryGap_entry_symm hdata atomU atomV
  have hscaled : tightDir label atomU
      * ((chartStationaryGap projection weight atomU atomU
            + chartStationaryGap projection weight atomV atomV - 2 * value)
          * (tightDir label atomU
            * (tightDir sharer atomU * tightDir label atomV
              - tightDir sharer atomV * tightDir label atomU))
        - chartStationaryGap projection weight atomV atomT
          * tightDir sharer atomT) = 0 := by
    linear_combination (-(tightDir label atomU)) * hrowVs
      + (tightDir label atomU * tightDir sharer atomV) * hsplitR
      + tightDir sharer atomU * hcrossR
      - (tightDir label atomU * tightDir sharer atomU) * hsymm
  have hinner := (mul_eq_zero.mp hscaled).resolve_left hneU
  linear_combination hinner

/-- **THE ALIGNED ANNIHILATION.**  The third-atom coupling of a
both-pair sharer is orthogonal to the pair direction: the aligned
combination times the third coordinate vanishes. -/
theorem bothPair_aligned_annihilation
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label sharer : activeIndex} (hmemLabel : label ∈ activeSet)
    (hmemSharer : sharer ∈ activeSet)
    {atomU atomV atomT : Fin size} (hUV : atomU ≠ atomV)
    (hUT : atomU ≠ atomT) (hVT : atomV ≠ atomT)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hneU : tightDir label atomU ≠ 0) (hneV : tightDir label atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hmemUs : atomU ∈ activeSubset sharer) (hmemVs : atomV ∈ activeSubset sharer)
    (hsuppSharer : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0) :
    (tightDir label atomU * chartStationaryGap projection weight atomU atomT
        + tightDir label atomV * chartStationaryGap projection weight atomV atomT)
      * tightDir sharer atomT = 0 := by
  have hsepL := bothPair_separated_left hdata hmemLabel hmemSharer hUV hUT hVT
    hmemU hmemV hneV hsupp hmemUs hsuppSharer
  have hsepR := bothPair_separated_right hdata hmemLabel hmemSharer hUV hUT hVT
    hmemU hmemV hneU hsupp hmemVs hsuppSharer
  linear_combination tightDir label atomU * hsepL
    - tightDir label atomV * hsepR

/-- **THE THIRD-DIAGONAL PRICING.**  The third tight row of a both-pair
sharer prices the third diagonal gap entry: the entry times the third
square is the value times the third square plus the excess times the
wedge square. -/
theorem bothPair_third_diagonal
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label sharer : activeIndex} (hmemLabel : label ∈ activeSet)
    (hmemSharer : sharer ∈ activeSet)
    {atomU atomV atomT : Fin size} (hUV : atomU ≠ atomV)
    (hUT : atomU ≠ atomT) (hVT : atomV ≠ atomT)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hneU : tightDir label atomU ≠ 0) (hneV : tightDir label atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hmemUs : atomU ∈ activeSubset sharer) (hmemVs : atomV ∈ activeSubset sharer)
    (hmemTs : atomT ∈ activeSubset sharer)
    (hsuppSharer : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0) :
    chartStationaryGap projection weight atomT atomT * tightDir sharer atomT ^ 2
      = value * tightDir sharer atomT ^ 2
        + (chartStationaryGap projection weight atomU atomU
            + chartStationaryGap projection weight atomV atomV - 2 * value)
          * (tightDir sharer atomU * tightDir label atomV
            - tightDir sharer atomV * tightDir label atomU) ^ 2 := by
  have hrowTs := hdata.tightDir_isTight sharer hmemSharer atomT hmemTs
  rw [mulVec_apply_of_triple_support _ hUV hUT hVT hsuppSharer atomT] at hrowTs
  have hsepL := bothPair_separated_left hdata hmemLabel hmemSharer hUV hUT hVT
    hmemU hmemV hneV hsupp hmemUs hsuppSharer
  have hsepR := bothPair_separated_right hdata hmemLabel hmemSharer hUV hUT hVT
    hmemU hmemV hneU hsupp hmemVs hsuppSharer
  have hsymmUT := chartStationaryGap_entry_symm hdata atomU atomT
  have hsymmVT := chartStationaryGap_entry_symm hdata atomV atomT
  linear_combination tightDir sharer atomT * hrowTs
    - tightDir sharer atomU * hsepL + tightDir sharer atomV * hsepR
    + (tightDir sharer atomU * tightDir sharer atomT) * hsymmUT
    + (tightDir sharer atomV * tightDir sharer atomT) * hsymmVT

/-! ## Layer 3 — the excess floor and the protrusion law -/

/-- **THE EXCESS FLOOR.**  Two positive diagonal gap entries and a
negative value make the complement excess strictly positive. -/
theorem pair_excess_pos {gapUU gapVV value : ℝ}
    (hfloorU : 0 < gapUU) (hfloorV : 0 < gapVV) (hvalueNeg : value < 0) :
    0 < gapUU + gapVV - 2 * value := by
  linarith

/-- **THE PROTRUSION LAW.**  A both-pair sharer with a vanishing third
coordinate has a vanishing wedge: the wedge lives on the protrusion. -/
theorem bothPair_wedge_vanish_of_third_vanish
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label sharer : activeIndex} (hmemLabel : label ∈ activeSet)
    (hmemSharer : sharer ∈ activeSet)
    {atomU atomV atomT : Fin size} (hUV : atomU ≠ atomV)
    (hUT : atomU ≠ atomT) (hVT : atomV ≠ atomT)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hneU : tightDir label atomU ≠ 0) (hneV : tightDir label atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hmemUs : atomU ∈ activeSubset sharer) (hmemVs : atomV ∈ activeSubset sharer)
    (hmemTs : atomT ∈ activeSubset sharer)
    (hsuppSharer : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0)
    (hexcessPos : 0 < chartStationaryGap projection weight atomU atomU
      + chartStationaryGap projection weight atomV atomV - 2 * value)
    (hthird : tightDir sharer atomT = 0) :
    tightDir sharer atomU * tightDir label atomV
      - tightDir sharer atomV * tightDir label atomU = 0 := by
  have hdiag := bothPair_third_diagonal hdata hmemLabel hmemSharer hUV hUT hVT
    hmemU hmemV hneU hneV hsupp hmemUs hmemVs hmemTs hsuppSharer
  rw [hthird] at hdiag
  have hsq : (tightDir sharer atomU * tightDir label atomV
      - tightDir sharer atomV * tightDir label atomU) ^ 2 = 0 := by
    have hzero : (chartStationaryGap projection weight atomU atomU
          + chartStationaryGap projection weight atomV atomV - 2 * value)
        * (tightDir sharer atomU * tightDir label atomV
          - tightDir sharer atomV * tightDir label atomU) ^ 2 = 0 := by
      linear_combination -hdiag
    rcases mul_eq_zero.mp hzero with hbad | hgood
    · exact absurd hbad (ne_of_gt hexcessPos)
    · exact hgood
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

/-! ## Layer 4 — the one-atom sharer laws -/

/-- **THE LEFT ONE-ATOM LAW.**  A sharer with the left pair atom and two
outer atoms couples the excess times the right pair square times its
pair coordinate to its two outer couplings. -/
theorem singlePair_scaled_left
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label sharer : activeIndex} (hmemLabel : label ∈ activeSet)
    (hmemSharer : sharer ∈ activeSet)
    {atomU atomV atomS atomT : Fin size} (hUV : atomU ≠ atomV)
    (hUS : atomU ≠ atomS) (hUT : atomU ≠ atomT) (hST : atomS ≠ atomT)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hmemUs : atomU ∈ activeSubset sharer)
    (hsuppSharer : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomS →
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0) :
    (chartStationaryGap projection weight atomU atomU
        + chartStationaryGap projection weight atomV atomV - 2 * value)
      * (tightDir label atomV ^ 2 * tightDir sharer atomU)
      + chartStationaryGap projection weight atomU atomS * tightDir sharer atomS
      + chartStationaryGap projection weight atomU atomT * tightDir sharer atomT
      = 0 := by
  have hrowUs := hdata.tightDir_isTight sharer hmemSharer atomU hmemUs
  rw [mulVec_apply_of_triple_support _ hUS hUT hST hsuppSharer atomU] at hrowUs
  have hsplitL := pair_diagonal_split_left hdata hmemLabel hUV hmemU hmemV hsupp
  linear_combination hrowUs - tightDir sharer atomU * hsplitL

/-- **THE RIGHT ONE-ATOM LAW.**  The mirror law at the right pair
atom. -/
theorem singlePair_scaled_right
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label sharer : activeIndex} (hmemLabel : label ∈ activeSet)
    (hmemSharer : sharer ∈ activeSet)
    {atomU atomV atomS atomT : Fin size} (hUV : atomU ≠ atomV)
    (hVS : atomV ≠ atomS) (hVT : atomV ≠ atomT) (hST : atomS ≠ atomT)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hmemVs : atomV ∈ activeSubset sharer)
    (hsuppSharer : ∀ atomIndex, atomIndex ≠ atomV → atomIndex ≠ atomS →
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0) :
    (chartStationaryGap projection weight atomU atomU
        + chartStationaryGap projection weight atomV atomV - 2 * value)
      * (tightDir label atomU ^ 2 * tightDir sharer atomV)
      + chartStationaryGap projection weight atomV atomS * tightDir sharer atomS
      + chartStationaryGap projection weight atomV atomT * tightDir sharer atomT
      = 0 := by
  have hrowVs := hdata.tightDir_isTight sharer hmemSharer atomV hmemVs
  rw [mulVec_apply_of_triple_support _ hVS hVT hST hsuppSharer atomV] at hrowVs
  have hsplitR := pair_diagonal_split_right hdata hmemLabel hUV hmemU hmemV hsupp
  linear_combination hrowVs - tightDir sharer atomV * hsplitR

/-! ## Layer 5 — the kernel read and the demand -/

/-- The gap action entry: the chart action minus the weighted
coordinate. -/
theorem gap_mulVec_entry (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (probe : Fin size → ℝ) (atomIndex : Fin size) :
    (chartStationaryGap projection weight *ᵥ probe) atomIndex
      = (projection *ᵥ probe) atomIndex - weight atomIndex * probe atomIndex := by
  rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply]
  congr 1
  show (∑ otherIndex : Fin size,
      Matrix.diagonal weight atomIndex otherIndex * probe otherIndex) = _
  rw [Finset.sum_eq_single atomIndex
    (fun otherIndex _ hne => by
      rw [Matrix.diagonal_apply_ne' _ hne, zero_mul])
    (fun hnot => absurd (Finset.mem_univ atomIndex) hnot)]
  rw [Matrix.diagonal_apply_eq]

/-- **THE KERNEL READ.**  The kernel combination of the two gap rows at
the pair, tested on any ambient vector, reads the complement eigenvalue
times the wedge plus the outer coupling sum. -/
theorem pair_kernel_gap_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (probe : Fin size → ℝ) :
    tightDir label atomV * (chartStationaryGap projection weight *ᵥ probe) atomU
        - tightDir label atomU
          * (chartStationaryGap projection weight *ᵥ probe) atomV
      = (chartStationaryGap projection weight atomU atomU
            + chartStationaryGap projection weight atomV atomV - value)
          * (probe atomU * tightDir label atomV
            - probe atomV * tightDir label atomU)
        + ∑ atomZ ∈ (Finset.univ.erase atomU).erase atomV,
            (tightDir label atomV * chartStationaryGap projection weight atomU atomZ
              - tightDir label atomU
                * chartStationaryGap projection weight atomV atomZ)
            * probe atomZ := by
  classical
  have hVU : atomV ∈ Finset.univ.erase atomU :=
    Finset.mem_erase.mpr ⟨Ne.symm hUV, Finset.mem_univ atomV⟩
  have hdecomp : ∀ rowVec : Fin size → ℝ,
      (∑ atomZ : Fin size, rowVec atomZ * probe atomZ)
        = rowVec atomU * probe atomU + rowVec atomV * probe atomV
          + ∑ atomZ ∈ (Finset.univ.erase atomU).erase atomV,
              rowVec atomZ * probe atomZ := by
    intro rowVec
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ atomU),
      ← Finset.sum_erase_add (Finset.univ.erase atomU) _ hVU]
    ring
  have hreadU : (chartStationaryGap projection weight *ᵥ probe) atomU
      = chartStationaryGap projection weight atomU atomU * probe atomU
        + chartStationaryGap projection weight atomU atomV * probe atomV
        + ∑ atomZ ∈ (Finset.univ.erase atomU).erase atomV,
            chartStationaryGap projection weight atomU atomZ * probe atomZ :=
    hdecomp (fun atomZ => chartStationaryGap projection weight atomU atomZ)
  have hreadV : (chartStationaryGap projection weight *ᵥ probe) atomV
      = chartStationaryGap projection weight atomV atomU * probe atomU
        + chartStationaryGap projection weight atomV atomV * probe atomV
        + ∑ atomZ ∈ (Finset.univ.erase atomU).erase atomV,
            chartStationaryGap projection weight atomV atomZ * probe atomZ :=
    hdecomp (fun atomZ => chartStationaryGap projection weight atomV atomZ)
  have hsplitL := pair_diagonal_split_left hdata hmem hUV hmemU hmemV hsupp
  have hsplitR := pair_diagonal_split_right hdata hmem hUV hmemU hmemV hsupp
  have hcrossL := pair_cross_scaled_left hdata hmem hUV hmemU hmemV hsupp
  have hcrossR := pair_cross_scaled_right hdata hmem hUV hmemU hmemV hsupp
  have hsymm := chartStationaryGap_entry_symm hdata atomU atomV
  have hunit := pair_support_unit_read hdata hmem hUV hsupp
  have hsumSplit : ∑ atomZ ∈ (Finset.univ.erase atomU).erase atomV,
        (tightDir label atomV * chartStationaryGap projection weight atomU atomZ
          - tightDir label atomU
            * chartStationaryGap projection weight atomV atomZ)
        * probe atomZ
      = tightDir label atomV
          * ∑ atomZ ∈ (Finset.univ.erase atomU).erase atomV,
              chartStationaryGap projection weight atomU atomZ * probe atomZ
        - tightDir label atomU
          * ∑ atomZ ∈ (Finset.univ.erase atomU).erase atomV,
              chartStationaryGap projection weight atomV atomZ * probe atomZ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun atomZ _ => by ring
  rw [hreadU, hreadV, hsumSplit]
  linear_combination (probe atomU * tightDir label atomV) * hsplitL
    - (probe atomV * tightDir label atomU) * hsplitR
    + probe atomV * hcrossL - probe atomU * hcrossR
    + (probe atomU * tightDir label atomU) * hsymm
    + ((chartStationaryGap projection weight atomU atomU
        + chartStationaryGap projection weight atomV atomV - 2 * value)
      * (probe atomU * tightDir label atomV - probe atomV * tightDir label atomU))
      * hunit

/-- **THE WEDGE ENERGY DEMAND.**  The shared squeeze in wedge form: the
wedge energy of the active set is at least the shifted pair mass over
the size minus the capped pair energy.  This inequality is the entry
point of every outer-sharer kill: with positive shifted pair weights the
demand is strictly positive, thus some active wedge survives. -/
theorem wedge_energy_demand
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    ((value + weight atomU) + (value + weight atomV)) * ((size : ℝ))⁻¹
        - (value + ((size : ℝ))⁻¹)
          * ((value + weight atomU) * tightDir label atomU ^ 2
            + (value + weight atomV) * tightDir label atomV ^ 2)
      ≤ ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * (tightDir label atomV * tightDir activeLabel atomU
            - tightDir label atomU * tightDir activeLabel atomV) ^ 2 := by
  have hsqueeze := shared_pair_squeeze_inequality hdata hmem hUV hsupp
  have henergy := wedge_energy_eq hdata hmem hUV hsupp
  have hsymm := assembly_entry_symm activeSet activeWeight tightDir atomU atomV
  have hWeq : ∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * (tightDir label atomV * tightDir activeLabel atomU
          - tightDir label atomU * tightDir activeLabel atomV) ^ 2
      = ((size : ℝ))⁻¹
        - (chartMultiplierAssembly activeSet activeWeight tightDir atomU atomV
            + chartMultiplierAssembly activeSet activeWeight tightDir atomV atomU)
          * (tightDir label atomU * tightDir label atomV) := by
    rw [henergy]
    linear_combination (-(tightDir label atomU * tightDir label atomV)) * hsymm
  linarith [hsqueeze, hWeq.le, hWeq.ge]

end Gtz

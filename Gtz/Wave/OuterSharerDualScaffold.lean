import Gtz.Wave.PairCouplingCalculus
import Gtz.Wave.ZeroLeakPair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The outer-sharer dual scaffold — the certificate consumers and the cap laws

The outer-sharer kill of the three support-two closures is a diagonal
Farkas certificate: a coefficient vector caps every active label through
its squared coordinates, and the capped average contradicts the constant
assembly diagonal.  The honest-manifold scan of this session confirms
the certificate shape at every witness of the full joint system, at two
values and five shapes, with an O(1) margin.  This file lands the two
consumers of such a certificate and the cap laws that price each label
class, all at the generic stationary datum.  Thus the rank-four, the
rank-five, and the rank-six bridges consume one supply.

The content, in three layers:

1. **The consumers.**  A coefficient vector with nonpositive caps on the
   active labels and a positive sum contradicts the assembly diagonal.
   The leak variant relaxes each cap by a nonnegative combination of the
   squared ambient leaks, and the leak budget prices the relaxation.
2. **The priced coupling.**  For a both-pair sharer the separated laws
   collapse the wedge coupling of the third atom, and the third-diagonal
   pricing turns the collapse into one square law: the squared wedge
   coupling is the excess times the third diagonal excess.  This law
   makes the type-two cap free for every candidate coefficient at most
   the excess split.
3. **The block quadratic reads.**  The one-pair outside form prices the
   outside part of the block quadratic of a one-atom sharer as the
   excess times a pair square times the squared pair coordinate.  The
   triple quadratic read is the generic block form of any active label.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.false_of_diagonal_certificate` — **THE DIAGONAL CONSUMER.**
* `Gtz.false_of_leak_certificate` — **THE LEAK CONSUMER.**
* `Gtz.bothPair_coupling_collapse` — the wedge coupling collapse.
* `Gtz.bothPair_coupling_square` — **THE PRICED COUPLING.**
* `Gtz.bothPair_coupling_priced` — the cancelled priced coupling.
* `Gtz.bothPair_aligned_of_third_ne` — the cancelled annihilation.
* `Gtz.triple_support_unit_read` — the triple unit read.
* `Gtz.triple_support_energy_read` — the triple energy read.
* `Gtz.tight_triple_quadratic_read` — the generic block quadratic.
* `Gtz.singlePair_outside_form_left`, `Gtz.singlePair_outside_form_right`
  — **THE ONE-PAIR OUTSIDE FORMS.**

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

/-! ## Layer 1 — the certificate consumers -/

/-- The dual pairing swap: the coefficient-weighted assembly diagonal is
the multiplier-weighted sum of the label caps. -/
theorem dual_pairing_swap (dualCoeff : Fin size → ℝ)
    (activeSet : Finset activeIndex) (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → (Fin size → ℝ)) :
    ∑ atomIndex : Fin size, dualCoeff atomIndex
        * chartMultiplierAssembly activeSet activeWeight tightDir atomIndex atomIndex
      = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * ∑ atomIndex : Fin size,
              dualCoeff atomIndex * tightDir activeLabel atomIndex ^ 2 := by
  calc ∑ atomIndex : Fin size, dualCoeff atomIndex
        * chartMultiplierAssembly activeSet activeWeight tightDir atomIndex atomIndex
      = ∑ atomIndex : Fin size, ∑ activeLabel ∈ activeSet,
          dualCoeff atomIndex
            * (activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2) := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rw [chartMultiplierAssembly_diagonal, Finset.mul_sum]
    _ = ∑ activeLabel ∈ activeSet, ∑ atomIndex : Fin size,
          dualCoeff atomIndex
            * (activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2) :=
        Finset.sum_comm
    _ = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * ∑ atomIndex : Fin size,
              dualCoeff atomIndex * tightDir activeLabel atomIndex ^ 2 := by
        refine Finset.sum_congr rfl fun activeLabel _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-- **THE DIAGONAL CONSUMER.**  A coefficient vector with nonpositive
caps on every positively weighted active label and a positive
coefficient sum contradicts the constant assembly diagonal.  Every
future outer-sharer certificate exits through this theorem. -/
theorem false_of_diagonal_certificate
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (dualCoeff : Fin size → ℝ)
    (hcap : ∀ activeLabel ∈ activeSet, 0 < activeWeight activeLabel →
      ∑ atomIndex : Fin size,
          dualCoeff atomIndex * tightDir activeLabel atomIndex ^ 2 ≤ 0)
    (hmargin : 0 < ∑ atomIndex : Fin size, dualCoeff atomIndex) :
    False := by
  have hswap := dual_pairing_swap dualCoeff activeSet activeWeight tightDir
  have hdiag : ∑ atomIndex : Fin size, dualCoeff atomIndex
        * chartMultiplierAssembly activeSet activeWeight tightDir atomIndex atomIndex
      = (∑ atomIndex : Fin size, dualCoeff atomIndex) * ((size : ℝ))⁻¹ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun atomIndex _ => by
      rw [hdata.assembly_diagonal atomIndex]
  have hpos : 0 < ∑ atomIndex : Fin size, dualCoeff atomIndex
      * chartMultiplierAssembly activeSet activeWeight tightDir atomIndex atomIndex := by
    rw [hdiag]
    exact mul_pos hmargin
      (inv_pos.mpr (size_cast_pos_of_isChartStationaryData hdata))
  have hnonpos : ∑ activeLabel ∈ activeSet, activeWeight activeLabel
      * ∑ atomIndex : Fin size,
          dualCoeff atomIndex * tightDir activeLabel atomIndex ^ 2 ≤ 0 := by
    refine Finset.sum_nonpos fun activeLabel hmem => ?_
    rcases (hdata.activeWeight_nonneg activeLabel hmem).lt_or_eq with hw | hw
    · calc activeWeight activeLabel
          * ∑ atomIndex : Fin size,
              dualCoeff atomIndex * tightDir activeLabel atomIndex ^ 2
        ≤ activeWeight activeLabel * 0 :=
          mul_le_mul_of_nonneg_left (hcap activeLabel hmem hw) hw.le
      _ = 0 := mul_zero _
    · rw [← hw, zero_mul]
  rw [hswap] at hpos
  exact absurd hpos (not_lt.mpr hnonpos)

/-- **THE LEAK CONSUMER.**  The caps relax by a nonnegative combination
of the squared ambient leaks.  The leak budget prices the relaxation as
the leak-coefficient average of the shifted weight products, and a
coefficient sum above that price contradicts the assembly diagonal. -/
theorem false_of_leak_certificate
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (dualCoeff leakCoeff : Fin size → ℝ)
    (hcap : ∀ activeLabel ∈ activeSet, 0 < activeWeight activeLabel →
      ∑ atomIndex : Fin size,
          dualCoeff atomIndex * tightDir activeLabel atomIndex ^ 2
        ≤ ∑ atomIndex : Fin size, leakCoeff atomIndex
            * chartTightLeak projection weight value (tightDir activeLabel)
                atomIndex ^ 2)
    (hmargin : ∑ atomIndex : Fin size, leakCoeff atomIndex
        * ((value + weight atomIndex) * (1 - value - weight atomIndex))
      < ∑ atomIndex : Fin size, dualCoeff atomIndex) :
    False := by
  have hswap := dual_pairing_swap dualCoeff activeSet activeWeight tightDir
  have hdiag : ∑ atomIndex : Fin size, dualCoeff atomIndex
        * chartMultiplierAssembly activeSet activeWeight tightDir atomIndex atomIndex
      = (∑ atomIndex : Fin size, dualCoeff atomIndex) * ((size : ℝ))⁻¹ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun atomIndex _ => by
      rw [hdata.assembly_diagonal atomIndex]
  have hleakSwap : ∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * ∑ atomIndex : Fin size, leakCoeff atomIndex
            * chartTightLeak projection weight value (tightDir activeLabel)
                atomIndex ^ 2
      = (∑ atomIndex : Fin size, leakCoeff atomIndex
          * ((value + weight atomIndex) * (1 - value - weight atomIndex)))
        * ((size : ℝ))⁻¹ := by
    calc ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * ∑ atomIndex : Fin size, leakCoeff atomIndex
              * chartTightLeak projection weight value (tightDir activeLabel)
                  atomIndex ^ 2
        = ∑ activeLabel ∈ activeSet, ∑ atomIndex : Fin size,
            leakCoeff atomIndex * (activeWeight activeLabel
              * chartTightLeak projection weight value (tightDir activeLabel)
                  atomIndex ^ 2) := by
          refine Finset.sum_congr rfl fun activeLabel _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun atomIndex _ => by ring
      _ = ∑ atomIndex : Fin size, ∑ activeLabel ∈ activeSet,
            leakCoeff atomIndex * (activeWeight activeLabel
              * chartTightLeak projection weight value (tightDir activeLabel)
                  atomIndex ^ 2) := Finset.sum_comm
      _ = ∑ atomIndex : Fin size, leakCoeff atomIndex
            * ((value + weight atomIndex) * (1 - value - weight atomIndex)
              * ((size : ℝ))⁻¹) := by
          refine Finset.sum_congr rfl fun atomIndex _ => ?_
          rw [← Finset.mul_sum,
            sum_activeWeight_mul_chartTightLeak_sq_of_isChartStationaryData
              hdata atomIndex]
      _ = (∑ atomIndex : Fin size, leakCoeff atomIndex
            * ((value + weight atomIndex) * (1 - value - weight atomIndex)))
          * ((size : ℝ))⁻¹ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun atomIndex _ => by ring
  have hcompare : ∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * ∑ atomIndex : Fin size,
            dualCoeff atomIndex * tightDir activeLabel atomIndex ^ 2
      ≤ ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * ∑ atomIndex : Fin size, leakCoeff atomIndex
              * chartTightLeak projection weight value (tightDir activeLabel)
                  atomIndex ^ 2 := by
    refine Finset.sum_le_sum fun activeLabel hmem => ?_
    rcases (hdata.activeWeight_nonneg activeLabel hmem).lt_or_eq with hw | hw
    · exact mul_le_mul_of_nonneg_left (hcap activeLabel hmem hw) hw.le
    · rw [← hw, zero_mul, zero_mul]
  have hsizeInv : 0 < ((size : ℝ))⁻¹ :=
    inv_pos.mpr (size_cast_pos_of_isChartStationaryData hdata)
  have hchain : (∑ atomIndex : Fin size, dualCoeff atomIndex) * ((size : ℝ))⁻¹
      ≤ (∑ atomIndex : Fin size, leakCoeff atomIndex
          * ((value + weight atomIndex) * (1 - value - weight atomIndex)))
        * ((size : ℝ))⁻¹ := by
    rw [← hdiag, ← hleakSwap, hswap]
    exact hcompare
  have hfinal := le_of_mul_le_mul_right hchain hsizeInv
  exact absurd hmargin (not_lt.mpr hfinal)

/-! ## Layer 2 — the priced coupling of a both-pair sharer -/

/-- **THE WEDGE COUPLING COLLAPSE.**  For a both-pair sharer the wedge
combination of the two third-atom couplings, scaled by the third
coordinate, is the negative excess times the sharer wedge. -/
theorem bothPair_coupling_collapse
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
    (tightDir label atomV * chartStationaryGap projection weight atomU atomT
        - tightDir label atomU * chartStationaryGap projection weight atomV atomT)
      * tightDir sharer atomT
      = -((chartStationaryGap projection weight atomU atomU
            + chartStationaryGap projection weight atomV atomV - 2 * value)
          * (tightDir sharer atomU * tightDir label atomV
            - tightDir sharer atomV * tightDir label atomU)) := by
  have hsepL := bothPair_separated_left hdata hmemLabel hmemSharer hUV hUT hVT
    hmemU hmemV hneV hsupp hmemUs hsuppSharer
  have hsepR := bothPair_separated_right hdata hmemLabel hmemSharer hUV hUT hVT
    hmemU hmemV hneU hsupp hmemVs hsuppSharer
  have hunit := pair_support_unit_read hdata hmemLabel hUV hsupp
  linear_combination tightDir label atomV * hsepL
    + tightDir label atomU * hsepR
    - ((chartStationaryGap projection weight atomU atomU
        + chartStationaryGap projection weight atomV atomV - 2 * value)
      * (tightDir sharer atomU * tightDir label atomV
        - tightDir sharer atomV * tightDir label atomU)) * hunit

/-- **THE PRICED COUPLING.**  The squared wedge coupling of the third
atom, scaled by the third square, is the excess times the third diagonal
excess times the third square.  On the type-two blocks this law makes
the cap free for every coefficient at most the excess split. -/
theorem bothPair_coupling_square
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
    (tightDir label atomV * chartStationaryGap projection weight atomU atomT
        - tightDir label atomU * chartStationaryGap projection weight atomV atomT) ^ 2
      * tightDir sharer atomT ^ 2
      = (chartStationaryGap projection weight atomU atomU
          + chartStationaryGap projection weight atomV atomV - 2 * value)
        * (chartStationaryGap projection weight atomT atomT - value)
        * tightDir sharer atomT ^ 2 := by
  have hcollapse := bothPair_coupling_collapse hdata hmemLabel hmemSharer hUV hUT
    hVT hmemU hmemV hneU hneV hsupp hmemUs hmemVs hsuppSharer
  have hprice := bothPair_third_diagonal hdata hmemLabel hmemSharer hUV hUT hVT
    hmemU hmemV hneU hneV hsupp hmemUs hmemVs hmemTs hsuppSharer
  linear_combination
    ((tightDir label atomV * chartStationaryGap projection weight atomU atomT
        - tightDir label atomU * chartStationaryGap projection weight atomV atomT)
      * tightDir sharer atomT
      - (chartStationaryGap projection weight atomU atomU
          + chartStationaryGap projection weight atomV atomV - 2 * value)
        * (tightDir sharer atomU * tightDir label atomV
          - tightDir sharer atomV * tightDir label atomU)) * hcollapse
    - (chartStationaryGap projection weight atomU atomU
        + chartStationaryGap projection weight atomV atomV - 2 * value) * hprice

/-- The cancelled priced coupling: a nonzero third coordinate prices the
squared wedge coupling exactly. -/
theorem bothPair_coupling_priced
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
    (hneT : tightDir sharer atomT ≠ 0) :
    (tightDir label atomV * chartStationaryGap projection weight atomU atomT
        - tightDir label atomU * chartStationaryGap projection weight atomV atomT) ^ 2
      = (chartStationaryGap projection weight atomU atomU
          + chartStationaryGap projection weight atomV atomV - 2 * value)
        * (chartStationaryGap projection weight atomT atomT - value) := by
  have hsquare := bothPair_coupling_square hdata hmemLabel hmemSharer hUV hUT hVT
    hmemU hmemV hneU hneV hsupp hmemUs hmemVs hmemTs hsuppSharer
  exact mul_right_cancel₀ (pow_ne_zero 2 hneT) hsquare

/-- The cancelled annihilation: a nonzero third coordinate annihilates
the aligned combination of the third-atom couplings. -/
theorem bothPair_aligned_of_third_ne
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
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0)
    (hneT : tightDir sharer atomT ≠ 0) :
    tightDir label atomU * chartStationaryGap projection weight atomU atomT
      + tightDir label atomV * chartStationaryGap projection weight atomV atomT
      = 0 := by
  have hannihilate := bothPair_aligned_annihilation hdata hmemLabel hmemSharer
    hUV hUT hVT hmemU hmemV hneU hneV hsupp hmemUs hmemVs hsuppSharer
  exact (mul_eq_zero.mp hannihilate).resolve_right hneT

/-! ## Layer 3 — the block quadratic reads -/

/-- The unit norm of a triple-supported direction collapses to the three
squares. -/
theorem triple_support_unit_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomA → atomIndex ≠ atomB →
      atomIndex ≠ atomC → tightDir label atomIndex = 0) :
    tightDir label atomA ^ 2 + tightDir label atomB ^ 2
      + tightDir label atomC ^ 2 = 1 := by
  classical
  have hunit : ∑ atomIndex : Fin size, tightDir label atomIndex ^ 2 = 1 := by
    rw [← dotProduct_self_eq_sum_sq, hdata.tightDir_unit label hmem]
  have htripleSum : ∑ atomIndex ∈ ({atomA, atomB, atomC} : Finset (Fin size)),
      tightDir label atomIndex ^ 2
      = ∑ atomIndex : Fin size, tightDir label atomIndex ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    have hne1 : atomIndex ≠ atomA := fun heq =>
      hnot (heq ▸ Finset.mem_insert_self _ _)
    have hne2 : atomIndex ≠ atomB := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hne3 : atomIndex ≠ atomC := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    rw [hsupp atomIndex hne1 hne2 hne3]
    ring
  have hBCset : atomB ∈ ({atomC} : Finset (Fin size)) → False := fun hmemB =>
    hBC (Finset.mem_singleton.mp hmemB)
  have hAset : atomA ∈ ({atomB, atomC} : Finset (Fin size)) → False := fun hmemA =>
    (Finset.mem_insert.mp hmemA).elim hAB fun hmemA' =>
      hAC (Finset.mem_singleton.mp hmemA')
  rw [← hunit, ← htripleSum, Finset.sum_insert hAset,
    Finset.sum_insert hBCset, Finset.sum_singleton]
  ring

/-- The coefficient-weighted energy of a triple-supported direction
collapses to the three atoms.  The cap of any candidate certificate
evaluates through this read. -/
theorem triple_support_energy_read
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC) {label : activeIndex}
    (hsupp : ∀ atomIndex, atomIndex ≠ atomA → atomIndex ≠ atomB →
      atomIndex ≠ atomC → tightDir label atomIndex = 0)
    (coeffVec : Fin size → ℝ) :
    ∑ atomIndex : Fin size, coeffVec atomIndex * tightDir label atomIndex ^ 2
      = coeffVec atomA * tightDir label atomA ^ 2
        + coeffVec atomB * tightDir label atomB ^ 2
        + coeffVec atomC * tightDir label atomC ^ 2 := by
  classical
  have htripleSum : ∑ atomIndex ∈ ({atomA, atomB, atomC} : Finset (Fin size)),
      coeffVec atomIndex * tightDir label atomIndex ^ 2
      = ∑ atomIndex : Fin size,
          coeffVec atomIndex * tightDir label atomIndex ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    have hne1 : atomIndex ≠ atomA := fun heq =>
      hnot (heq ▸ Finset.mem_insert_self _ _)
    have hne2 : atomIndex ≠ atomB := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hne3 : atomIndex ≠ atomC := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    rw [hsupp atomIndex hne1 hne2 hne3]
    ring
  have hBCset : atomB ∈ ({atomC} : Finset (Fin size)) → False := fun hmemB =>
    hBC (Finset.mem_singleton.mp hmemB)
  have hAset : atomA ∈ ({atomB, atomC} : Finset (Fin size)) → False := fun hmemA =>
    (Finset.mem_insert.mp hmemA).elim hAB fun hmemA' =>
      hAC (Finset.mem_singleton.mp hmemA')
  rw [← htripleSum, Finset.sum_insert hAset, Finset.sum_insert hBCset,
    Finset.sum_singleton]
  ring

/-- **THE GENERIC BLOCK QUADRATIC.**  The block quadratic form of the
shifted gap vanishes on every triple-supported active label: the three
diagonal excesses weigh the squares against twice the three off-diagonal
couplings. -/
theorem tight_triple_quadratic_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hmemA : atomA ∈ activeSubset label) (hmemB : atomB ∈ activeSubset label)
    (hmemC : atomC ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomA → atomIndex ≠ atomB →
      atomIndex ≠ atomC → tightDir label atomIndex = 0) :
    (chartStationaryGap projection weight atomA atomA - value)
        * tightDir label atomA ^ 2
      + (chartStationaryGap projection weight atomB atomB - value)
        * tightDir label atomB ^ 2
      + (chartStationaryGap projection weight atomC atomC - value)
        * tightDir label atomC ^ 2
      + 2 * (chartStationaryGap projection weight atomA atomB
          * tightDir label atomA * tightDir label atomB
        + chartStationaryGap projection weight atomA atomC
          * tightDir label atomA * tightDir label atomC
        + chartStationaryGap projection weight atomB atomC
          * tightDir label atomB * tightDir label atomC)
      = 0 := by
  have hrowA := hdata.tightDir_isTight label hmem atomA hmemA
  have hrowB := hdata.tightDir_isTight label hmem atomB hmemB
  have hrowC := hdata.tightDir_isTight label hmem atomC hmemC
  rw [mulVec_apply_of_triple_support _ hAB hAC hBC hsupp atomA] at hrowA
  rw [mulVec_apply_of_triple_support _ hAB hAC hBC hsupp atomB] at hrowB
  rw [mulVec_apply_of_triple_support _ hAB hAC hBC hsupp atomC] at hrowC
  have hsymmBA := chartStationaryGap_entry_symm hdata atomB atomA
  have hsymmCA := chartStationaryGap_entry_symm hdata atomC atomA
  have hsymmCB := chartStationaryGap_entry_symm hdata atomC atomB
  linear_combination tightDir label atomA * hrowA + tightDir label atomB * hrowB
    + tightDir label atomC * hrowC
    - (tightDir label atomB * tightDir label atomA) * hsymmBA
    - (tightDir label atomC * tightDir label atomA) * hsymmCA
    - (tightDir label atomC * tightDir label atomB) * hsymmCB

/-- **THE LEFT ONE-PAIR OUTSIDE FORM.**  For a sharer with the left pair
atom and two outer atoms, the outside part of the block quadratic is the
excess times the right pair square times the squared pair coordinate.
The outside caps of the one-pair blocks press against this form. -/
theorem singlePair_outside_form_left
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label sharer : activeIndex} (hmemLabel : label ∈ activeSet)
    (hmemSharer : sharer ∈ activeSet)
    {atomU atomV atomS atomT : Fin size} (hUV : atomU ≠ atomV)
    (hUS : atomU ≠ atomS) (hUT : atomU ≠ atomT) (hST : atomS ≠ atomT)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hmemUs : atomU ∈ activeSubset sharer) (hmemSs : atomS ∈ activeSubset sharer)
    (hmemTs : atomT ∈ activeSubset sharer)
    (hsuppSharer : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomS →
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0) :
    (chartStationaryGap projection weight atomS atomS - value)
        * tightDir sharer atomS ^ 2
      + 2 * chartStationaryGap projection weight atomS atomT
        * tightDir sharer atomS * tightDir sharer atomT
      + (chartStationaryGap projection weight atomT atomT - value)
        * tightDir sharer atomT ^ 2
      = (chartStationaryGap projection weight atomU atomU
          + chartStationaryGap projection weight atomV atomV - 2 * value)
        * (tightDir label atomV ^ 2 * tightDir sharer atomU ^ 2) := by
  have hrowS := hdata.tightDir_isTight sharer hmemSharer atomS hmemSs
  have hrowT := hdata.tightDir_isTight sharer hmemSharer atomT hmemTs
  rw [mulVec_apply_of_triple_support _ hUS hUT hST hsuppSharer atomS] at hrowS
  rw [mulVec_apply_of_triple_support _ hUS hUT hST hsuppSharer atomT] at hrowT
  have hscaledU := singlePair_scaled_left hdata hmemLabel hmemSharer hUV hUS hUT
    hST hmemU hmemV hsupp hmemUs hsuppSharer
  have hsymmSU := chartStationaryGap_entry_symm hdata atomS atomU
  have hsymmTU := chartStationaryGap_entry_symm hdata atomT atomU
  have hsymmTS := chartStationaryGap_entry_symm hdata atomT atomS
  linear_combination tightDir sharer atomS * hrowS + tightDir sharer atomT * hrowT
    - tightDir sharer atomU * hscaledU
    - (tightDir sharer atomS * tightDir sharer atomU) * hsymmSU
    - (tightDir sharer atomT * tightDir sharer atomU) * hsymmTU
    - (tightDir sharer atomT * tightDir sharer atomS) * hsymmTS

/-- **THE RIGHT ONE-PAIR OUTSIDE FORM.**  The mirror form at the right
pair atom. -/
theorem singlePair_outside_form_right
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label sharer : activeIndex} (hmemLabel : label ∈ activeSet)
    (hmemSharer : sharer ∈ activeSet)
    {atomU atomV atomS atomT : Fin size} (hUV : atomU ≠ atomV)
    (hVS : atomV ≠ atomS) (hVT : atomV ≠ atomT) (hST : atomS ≠ atomT)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hmemVs : atomV ∈ activeSubset sharer) (hmemSs : atomS ∈ activeSubset sharer)
    (hmemTs : atomT ∈ activeSubset sharer)
    (hsuppSharer : ∀ atomIndex, atomIndex ≠ atomV → atomIndex ≠ atomS →
      atomIndex ≠ atomT → tightDir sharer atomIndex = 0) :
    (chartStationaryGap projection weight atomS atomS - value)
        * tightDir sharer atomS ^ 2
      + 2 * chartStationaryGap projection weight atomS atomT
        * tightDir sharer atomS * tightDir sharer atomT
      + (chartStationaryGap projection weight atomT atomT - value)
        * tightDir sharer atomT ^ 2
      = (chartStationaryGap projection weight atomU atomU
          + chartStationaryGap projection weight atomV atomV - 2 * value)
        * (tightDir label atomU ^ 2 * tightDir sharer atomV ^ 2) := by
  have hrowS := hdata.tightDir_isTight sharer hmemSharer atomS hmemSs
  have hrowT := hdata.tightDir_isTight sharer hmemSharer atomT hmemTs
  rw [mulVec_apply_of_triple_support _ hVS hVT hST hsuppSharer atomS] at hrowS
  rw [mulVec_apply_of_triple_support _ hVS hVT hST hsuppSharer atomT] at hrowT
  have hscaledV := singlePair_scaled_right hdata hmemLabel hmemSharer hUV hVS hVT
    hST hmemU hmemV hsupp hmemVs hsuppSharer
  have hsymmSV := chartStationaryGap_entry_symm hdata atomS atomV
  have hsymmTV := chartStationaryGap_entry_symm hdata atomT atomV
  have hsymmTS := chartStationaryGap_entry_symm hdata atomT atomS
  linear_combination tightDir sharer atomS * hrowS + tightDir sharer atomT * hrowT
    - tightDir sharer atomV * hscaledV
    - (tightDir sharer atomS * tightDir sharer atomV) * hsymmSV
    - (tightDir sharer atomT * tightDir sharer atomV) * hsymmTV
    - (tightDir sharer atomT * tightDir sharer atomS) * hsymmTS

end Gtz

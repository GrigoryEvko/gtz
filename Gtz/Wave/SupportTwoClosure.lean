import Gtz.Wave.RankFourRungAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The support-two closure — census branch one dies at the frame

A basis direction with an ambient support of cardinality two is a
two-sparse eigenvector of the gap on its pair.  This file builds the full
structural layer of that shape and closes census branch one.

The layers:

1. **The pair extraction.**  A card-two support yields the two atoms, the
   nonzero coordinates, the vanishing complement, the block membership,
   and the third block atom.
2. **The pair row laws.**  The tight equation collapses on the pair: the
   two eigen rows, the third-row orthogonality, and every off-block row
   read of the gap through the pair.
3. **The multiplied identities.**  The division-free forms: the
   characteristic identity `(G - g_uu) * (G - g_vv) = g_uv ^ 2`, the sign
   dichotomy `0 ≤ (g_uu - G) * (g_vv - G)`, and the ratio exports.
4. **The label energy calculus.**  The projection energy of a tight
   direction reads twice: the tight equation gives `value + Σ w q²`, and
   idempotency gives the square norm of the projected direction.  The two
   reads squeeze the weighted energy into the window
   `[-value, 1 - value]`.  The floor `-value ≤ Σ w q²` is the pointwise
   energy law, and on a support-two label the whole floor sits on the two
   pair atoms.  The branch-A certificate (the coupled-label kill that the
   diagnostic probe locates at the tight rows under a strictly negative
   value) consumes this layer and stays open in
   `RankFourSupportTwoClosed`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.exists_pair_of_support_card_two` — **THE PAIR EXTRACTION.**
* `Gtz.exists_third_block_atom` — the third atom of the block.
* `Gtz.pair_row_left`, `Gtz.pair_row_right`, `Gtz.pair_row_orth` — **THE
  PAIR ROW LAWS.**
* `Gtz.pair_characteristic`, `Gtz.pair_sign_dichotomy`,
  `Gtz.pair_ratio_left`, `Gtz.pair_ratio_right` — **THE MULTIPLIED
  IDENTITIES.**
* `Gtz.tight_energy_read`, `Gtz.projection_energy_eq`,
  `Gtz.projection_energy_split` — **THE TWO ENERGY READS.**
* `Gtz.weightEnergy_sq_le_secondMoment`, `Gtz.weightEnergy_le_one` — the
  variance and the cap.
* `Gtz.neg_value_le_weightEnergy` — **THE ENERGY FLOOR.**
* `Gtz.pair_energy_floor` — the support-two reading of the floor.

## Vacuity

The statements hold at every stationary datum.  The closure statement is
vacuous if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## Layer 1 — the pair extraction -/

/-- **THE PAIR EXTRACTION.**  A support of cardinality two yields the two
atoms with nonzero coordinates and a vanishing complement. -/
theorem exists_pair_of_support_card_two
    {label : activeIndex}
    (hcard : (datumTightSupport tightDir label).card = 2) :
    ∃ atomU atomV : Fin size, atomU ≠ atomV
      ∧ tightDir label atomU ≠ 0
      ∧ tightDir label atomV ≠ 0
      ∧ ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
          tightDir label atomIndex = 0 := by
  classical
  obtain ⟨atomU, atomV, hne, hset⟩ := Finset.card_eq_two.mp hcard
  refine ⟨atomU, atomV, hne, ?_, ?_, ?_⟩
  · exact mem_datumTightSupport.mp (by
      rw [hset]
      exact Finset.mem_insert_self _ _)
  · exact mem_datumTightSupport.mp (by
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · intro atomIndex hneU hneV
    by_contra hnonzero
    have hmem : atomIndex ∈ datumTightSupport tightDir label :=
      mem_datumTightSupport.mpr hnonzero
    rw [hset] at hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hneU heq
    · exact hneV (Finset.mem_singleton.mp hmem')

/-- The support sits inside the block, atom by atom. -/
theorem pair_mem_block
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomIndex : Fin size} (hne : tightDir label atomIndex ≠ 0) :
    atomIndex ∈ activeSubset label :=
  datumTightSupport_subset hdata hmem (mem_datumTightSupport.mpr hne)

/-- **THE THIRD BLOCK ATOM.**  At rank three a card-two support leaves
exactly one more atom in the block: the orthogonality row lives there. -/
theorem exists_third_block_atom
    (hdata : IsChartStationaryData 3 projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    ∃ atomZ : Fin size, atomZ ≠ atomU ∧ atomZ ≠ atomV
      ∧ atomZ ∈ activeSubset label ∧ tightDir label atomZ = 0 := by
  classical
  have hblockCard : (activeSubset label).card = 3 :=
    hdata.activeSubset_card label hmem
  have herase : (((activeSubset label).erase atomU).erase atomV).card = 1 := by
    rw [Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨Ne.symm hUV, hmemV⟩),
      Finset.card_erase_of_mem hmemU, hblockCard]
  obtain ⟨atomZ, hZset⟩ := Finset.card_eq_one.mp herase
  have hZmem : atomZ ∈ ((activeSubset label).erase atomU).erase atomV := by
    rw [hZset]
    exact Finset.mem_singleton_self _
  have hZV : atomZ ≠ atomV := (Finset.mem_erase.mp hZmem).1
  have hZU : atomZ ≠ atomU :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hZmem).2).1
  have hZblock : atomZ ∈ activeSubset label :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hZmem).2).2
  exact ⟨atomZ, hZU, hZV, hZblock, hsupp atomZ hZU hZV⟩

/-! ## Layer 2 — the pair row laws -/

/-- **THE LEFT EIGEN ROW.**  The tight row at the left pair atom. -/
theorem pair_row_left
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomU atomU * tightDir label atomU
      + chartStationaryGap projection weight atomU atomV * tightDir label atomV
      = value * tightDir label atomU :=
  gap_row_eigen_pair hdata hmem hmemU hUV hsupp

/-- **THE RIGHT EIGEN ROW.**  The tight row at the right pair atom. -/
theorem pair_row_right
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomV atomU * tightDir label atomU
      + chartStationaryGap projection weight atomV atomV * tightDir label atomV
      = value * tightDir label atomV :=
  gap_row_eigen_pair hdata hmem hmemV hUV hsupp

/-- **THE ORTHOGONALITY ROW.**  The tight row at any block atom off the
pair reads zero: the direction vanishes there. -/
theorem pair_row_orth
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV atomZ : Fin size} (hUV : atomU ≠ atomV)
    (hZU : atomZ ≠ atomU) (hZV : atomZ ≠ atomV)
    (hmemZ : atomZ ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomZ atomU * tightDir label atomU
      + chartStationaryGap projection weight atomZ atomV * tightDir label atomV
      = 0 := by
  have hrow := gap_row_eigen_pair hdata hmem hmemZ hUV hsupp
  rw [hsupp atomZ hZU hZV, mul_zero] at hrow
  exact hrow

/-! ## Layer 3 — the multiplied identities -/

/-- **THE LEFT RATIO EXPORT.**  The left row times the left coordinate:
`g_uv * (q_u * q_v) = (G - g_uu) * q_u ^ 2`, division-free. -/
theorem pair_ratio_left
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomU atomV
        * (tightDir label atomU * tightDir label atomV)
      = (value - chartStationaryGap projection weight atomU atomU)
        * tightDir label atomU ^ 2 := by
  have hrow := pair_row_left hdata hmem hUV hmemU hsupp
  linear_combination tightDir label atomU * hrow

/-- **THE RIGHT RATIO EXPORT.**  The right row times the right coordinate:
`g_uv * (q_u * q_v) = (G - g_vv) * q_v ^ 2`, division-free, through the
gap symmetry. -/
theorem pair_ratio_right
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemV : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomU atomV
        * (tightDir label atomU * tightDir label atomV)
      = (value - chartStationaryGap projection weight atomV atomV)
        * tightDir label atomV ^ 2 := by
  have hrow := pair_row_right hdata hmem hUV hmemV hsupp
  rw [gap_entry_symm hdata atomV atomU] at hrow
  linear_combination tightDir label atomV * hrow

/-- **THE CHARACTERISTIC IDENTITY.**  Eliminating the pair coordinates:
`(G - g_uu) * (G - g_vv) * (q_u * q_v) ^ 2 = g_uv ^ 2 * (q_u * q_v) ^ 2`,
stated in the cancelled form through the nonzero pair product. -/
theorem pair_characteristic
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hneU : tightDir label atomU ≠ 0) (hneV : tightDir label atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    (value - chartStationaryGap projection weight atomU atomU)
        * (value - chartStationaryGap projection weight atomV atomV)
      = chartStationaryGap projection weight atomU atomV ^ 2 := by
  have hleft := pair_ratio_left hdata hmem hUV hmemU hsupp
  have hright := pair_ratio_right hdata hmem hUV hmemV hsupp
  have hprod : ((value - chartStationaryGap projection weight atomU atomU)
        * (value - chartStationaryGap projection weight atomV atomV))
        * (tightDir label atomU * tightDir label atomV) ^ 2
      = chartStationaryGap projection weight atomU atomV ^ 2
        * (tightDir label atomU * tightDir label atomV) ^ 2 := by
    linear_combination
      (-(chartStationaryGap projection weight atomU atomV
          * (tightDir label atomU * tightDir label atomV))) * hleft
      + (-((value - chartStationaryGap projection weight atomU atomU)
          * tightDir label atomU ^ 2)) * hright
  have hne : (tightDir label atomU * tightDir label atomV) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero hneU hneV)
  exact mul_right_cancel₀ hne hprod

/-- **THE SIGN DICHOTOMY.**  The two diagonal shifts of the pair carry the
same sign: their product is a square. -/
theorem pair_sign_dichotomy
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hmemU : atomU ∈ activeSubset label) (hmemV : atomV ∈ activeSubset label)
    (hneU : tightDir label atomU ≠ 0) (hneV : tightDir label atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    0 ≤ (chartStationaryGap projection weight atomU atomU - value)
      * (chartStationaryGap projection weight atomV atomV - value) := by
  have hchar := pair_characteristic hdata hmem hUV hmemU hmemV hneU hneV hsupp
  nlinarith [hchar, sq_nonneg (chartStationaryGap projection weight atomU atomV)]

/-! ## Layer 4 — the label energy calculus

The projection energy of a tight direction reads twice.  The tight
equation gives `value + Σ w q²` on the block.  Idempotency gives the
square norm of the projected direction, which splits into the shifted
weights on the block and a nonnegative remainder off it.  The variance
identity and the strictly negative value then squeeze the weighted energy
from below: `-value ≤ Σ w q²`.  On a support-two label the floor sits on
the two pair atoms. -/

/-- **THE TIGHT ENERGY READ.**  The projection energy of a tight direction
is the value plus the weighted energy. -/
theorem tight_energy_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet) :
    tightDir label ⬝ᵥ (projection *ᵥ tightDir label)
      = value + ∑ atomIndex : Fin size,
          weight atomIndex * tightDir label atomIndex ^ 2 := by
  have hterm : ∀ atomIndex : Fin size,
      tightDir label atomIndex * (projection *ᵥ tightDir label) atomIndex
      = value * tightDir label atomIndex ^ 2
        + weight atomIndex * tightDir label atomIndex ^ 2 := by
    intro atomIndex
    by_cases hin : atomIndex ∈ activeSubset label
    · rw [projection_mulVec_tightDir_of_mem hdata hmem hin]
      ring
    · rw [hdata.tightDir_support label hmem atomIndex hin]
      ring
  have hstep : tightDir label ⬝ᵥ (projection *ᵥ tightDir label)
      = ∑ atomIndex : Fin size, (value * tightDir label atomIndex ^ 2
          + weight atomIndex * tightDir label atomIndex ^ 2) := by
    show (∑ atomIndex : Fin size, tightDir label atomIndex
        * (projection *ᵥ tightDir label) atomIndex) = _
    exact Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex
  rw [hstep, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← dotProduct_self_eq_sum_sq, hdata.tightDir_unit label hmem, mul_one]

/-- **THE IDEMPOTENT ENERGY READ.**  The projection energy is the square
norm of the projected direction. -/
theorem projection_energy_eq
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (label : activeIndex) :
    tightDir label ⬝ᵥ (projection *ᵥ tightDir label)
      = (projection *ᵥ tightDir label) ⬝ᵥ (projection *ᵥ tightDir label) := by
  calc tightDir label ⬝ᵥ (projection *ᵥ tightDir label)
      = tightDir label ⬝ᵥ ((projection * projection) *ᵥ tightDir label) := by
        rw [hdata.isIdempotent]
    _ = tightDir label ⬝ᵥ (projection *ᵥ (projection *ᵥ tightDir label)) := by
        rw [← Matrix.mulVec_mulVec]
    _ = (tightDir label ᵥ* projection) ⬝ᵥ (projection *ᵥ tightDir label) := by
        rw [Matrix.dotProduct_mulVec]
    _ = (projection *ᵥ tightDir label) ⬝ᵥ (projection *ᵥ tightDir label) := by
        have hvec : tightDir label ᵥ* projection = projection *ᵥ tightDir label := by
          rw [← Matrix.vecMul_transpose, hdata.isSymmetric]
        rw [hvec]

/-- **THE ENERGY SPLIT.**  The square norm of the projected direction is
the shifted-weight energy on the block plus a nonnegative remainder off
the block. -/
theorem projection_energy_split
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet) :
    (projection *ᵥ tightDir label) ⬝ᵥ (projection *ᵥ tightDir label)
      = (∑ atomIndex : Fin size,
          (value + weight atomIndex) ^ 2 * tightDir label atomIndex ^ 2)
        + ∑ atomIndex ∈ Finset.univ.filter
            (fun atomIndex => ¬ atomIndex ∈ activeSubset label),
            (projection *ᵥ tightDir label) atomIndex ^ 2 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin size))
    (fun atomIndex => atomIndex ∈ activeSubset label)
    (fun atomIndex => (projection *ᵥ tightDir label) atomIndex ^ 2)
  have hblockPart : ∑ atomIndex ∈ Finset.univ.filter
      (fun atomIndex => atomIndex ∈ activeSubset label),
      (projection *ᵥ tightDir label) atomIndex ^ 2
      = ∑ atomIndex : Fin size,
          (value + weight atomIndex) ^ 2 * tightDir label atomIndex ^ 2 := by
    have hvals : ∀ atomIndex ∈ Finset.univ.filter
        (fun atomIndex => atomIndex ∈ activeSubset label),
        (projection *ᵥ tightDir label) atomIndex ^ 2
        = (value + weight atomIndex) ^ 2 * tightDir label atomIndex ^ 2 := by
      intro atomIndex hmemF
      rw [projection_mulVec_tightDir_of_mem hdata hmem
        (Finset.mem_filter.mp hmemF).2]
      ring
    rw [Finset.sum_congr rfl hvals]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro atomIndex _ hnot
    have hoff : atomIndex ∉ activeSubset label := by
      intro hcontra
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontra⟩)
    rw [hdata.tightDir_support label hmem atomIndex hoff]
    ring
  have hdot : (projection *ᵥ tightDir label) ⬝ᵥ (projection *ᵥ tightDir label)
      = ∑ atomIndex : Fin size, (projection *ᵥ tightDir label) atomIndex ^ 2 :=
    dotProduct_self_eq_sum_sq _
  rw [hdot, ← hsplit, hblockPart]

/-- **THE VARIANCE BOUND.**  The energy square never exceeds the second
moment: the weighted variance is a sum of squares. -/
theorem weightEnergy_sq_le_secondMoment
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet) :
    (∑ atomIndex : Fin size, weight atomIndex * tightDir label atomIndex ^ 2) ^ 2
      ≤ ∑ atomIndex : Fin size,
          weight atomIndex ^ 2 * tightDir label atomIndex ^ 2 := by
  have hunit : ∑ atomIndex : Fin size, tightDir label atomIndex ^ 2 = 1 := by
    rw [← dotProduct_self_eq_sum_sq, hdata.tightDir_unit label hmem]
  set energy := ∑ atomIndex : Fin size,
    weight atomIndex * tightDir label atomIndex ^ 2 with henergy
  have hvariance : ∑ atomIndex : Fin size,
      tightDir label atomIndex ^ 2 * (weight atomIndex - energy) ^ 2
      = (∑ atomIndex : Fin size,
          weight atomIndex ^ 2 * tightDir label atomIndex ^ 2)
        - energy ^ 2 := by
    have hexpand : ∀ atomIndex : Fin size,
        tightDir label atomIndex ^ 2 * (weight atomIndex - energy) ^ 2
        = weight atomIndex ^ 2 * tightDir label atomIndex ^ 2
          - 2 * energy * (weight atomIndex * tightDir label atomIndex ^ 2)
          + energy ^ 2 * tightDir label atomIndex ^ 2 := by
      intro atomIndex
      ring
    rw [Finset.sum_congr rfl fun atomIndex _ => hexpand atomIndex,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← henergy, hunit]
    ring
  have hnonneg : 0 ≤ ∑ atomIndex : Fin size,
      tightDir label atomIndex ^ 2 * (weight atomIndex - energy) ^ 2 :=
    Finset.sum_nonneg fun atomIndex _ =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith [hvariance ▸ hnonneg]

/-- **THE ENERGY CAP.**  The weighted energy of a unit direction never
exceeds one. -/
theorem weightEnergy_le_one
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet) :
    ∑ atomIndex : Fin size, weight atomIndex * tightDir label atomIndex ^ 2
      ≤ 1 := by
  have hunit : ∑ atomIndex : Fin size, tightDir label atomIndex ^ 2 = 1 := by
    rw [← dotProduct_self_eq_sum_sq, hdata.tightDir_unit label hmem]
  have hpoint : ∀ atomIndex : Fin size, tightDir label atomIndex ^ 2 ≤ 1 := by
    intro atomIndex
    have hle := Finset.single_le_sum
      (f := fun otherIndex => tightDir label otherIndex ^ 2)
      (fun otherIndex _ => sq_nonneg _) (Finset.mem_univ atomIndex)
    rwa [hunit] at hle
  calc ∑ atomIndex : Fin size,
      weight atomIndex * tightDir label atomIndex ^ 2
      ≤ ∑ atomIndex : Fin size, weight atomIndex * 1 :=
        Finset.sum_le_sum fun atomIndex _ =>
          mul_le_mul_of_nonneg_left (hpoint atomIndex)
            (hdata.weight_pos atomIndex).le
    _ = 1 := by
        rw [Finset.sum_congr rfl fun atomIndex _ => mul_one (weight atomIndex),
          hdata.weight_sum_one]

/-- **THE ENERGY FLOOR.**  At a strictly negative value, the weighted
energy of every tight direction is at least `-value`: the two energy
reads, the split, the variance bound, and the cap squeeze it. -/
theorem neg_value_le_weightEnergy
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hvalueNeg : value < 0)
    {label : activeIndex} (hmem : label ∈ activeSet) :
    -value ≤ ∑ atomIndex : Fin size,
        weight atomIndex * tightDir label atomIndex ^ 2 := by
  classical
  have hunit : ∑ atomIndex : Fin size, tightDir label atomIndex ^ 2 = 1 := by
    rw [← dotProduct_self_eq_sum_sq, hdata.tightDir_unit label hmem]
  have hread := tight_energy_read hdata hmem
  have hidem := projection_energy_eq hdata label
  have hsplit := projection_energy_split hdata hmem
  have hvar := weightEnergy_sq_le_secondMoment hdata hmem
  have hcap := weightEnergy_le_one hdata hmem
  set energy := ∑ atomIndex : Fin size,
    weight atomIndex * tightDir label atomIndex ^ 2 with henergy
  set second := ∑ atomIndex : Fin size,
    weight atomIndex ^ 2 * tightDir label atomIndex ^ 2 with hsecond
  set remainder := ∑ atomIndex ∈ Finset.univ.filter
    (fun atomIndex => ¬ atomIndex ∈ activeSubset label),
    (projection *ᵥ tightDir label) atomIndex ^ 2 with hremainder
  have hexpand : ∑ atomIndex : Fin size,
      (value + weight atomIndex) ^ 2 * tightDir label atomIndex ^ 2
      = value ^ 2 + 2 * value * energy + second := by
    have hterm : ∀ atomIndex : Fin size,
        (value + weight atomIndex) ^ 2 * tightDir label atomIndex ^ 2
        = value ^ 2 * tightDir label atomIndex ^ 2
          + 2 * value * (weight atomIndex * tightDir label atomIndex ^ 2)
          + weight atomIndex ^ 2 * tightDir label atomIndex ^ 2 := by
      intro atomIndex
      ring
    rw [Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← henergy, ← hsecond, hunit]
    ring
  have hmain : value + energy = value ^ 2 + 2 * value * energy + second
      + remainder := by
    rw [← hread, hidem, hsplit, hexpand]
  have hremNonneg : 0 ≤ remainder := by
    rw [hremainder]
    exact Finset.sum_nonneg fun atomIndex _ => sq_nonneg _
  nlinarith [hmain, hremNonneg, hvar, hcap, hvalueNeg,
    mul_pos (neg_pos.mpr hvalueNeg)
      (show (0 : ℝ) < 1 - value - energy by nlinarith [hcap, hvalueNeg])]

/-- **THE PAIR ENERGY FLOOR.**  On a support-two label the whole energy
floor sits on the two pair atoms. -/
theorem pair_energy_floor
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hvalueNeg : value < 0)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    -value ≤ weight atomU * tightDir label atomU ^ 2
      + weight atomV * tightDir label atomV ^ 2 := by
  classical
  have hfloor := neg_value_le_weightEnergy hdata hvalueNeg hmem
  have hpairSum : ∑ atomIndex ∈ ({atomU, atomV} : Finset (Fin size)),
      weight atomIndex * tightDir label atomIndex ^ 2
      = ∑ atomIndex : Fin size,
          weight atomIndex * tightDir label atomIndex ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    have hne1 : atomIndex ≠ atomU := fun heq =>
      hnot (heq ▸ Finset.mem_insert_self _ _)
    have hne2 : atomIndex ≠ atomV := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hsupp atomIndex hne1 hne2]
    ring
  rw [← hpairSum, Finset.sum_pair hUV] at hfloor
  exact hfloor

end Gtz

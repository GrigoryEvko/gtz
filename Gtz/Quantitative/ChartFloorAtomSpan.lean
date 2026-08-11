/-
# The floor atoms of a chart stationarity datum, and the span of the projected
# tight directions

Two rigid endpoints of the chart route are settled here, and both fall out of one
identity.

## The identity

`sum_activeWeight_mul_sq_projection_mulVec_tightDir`: at every atom,

    `∑_l mu_l * ((P u_l)_c)^2  =  (value + t_c) / size` .

It is the shipped sandwich `Gtz.projection_mul_multiplier_eq_sandwich_of_isChartStationaryData`
read as a quadratic form against the `c`-th column of the chart, closed by the shipped
forced diagonal `Gtz.diagonal_projection_mul_multiplier_of_isChartStationaryData`.  Both
sides are manifestly nonnegative sums, and splitting the left side at membership gives
the leak identity `sum_activeWeight_mul_sq_leak`,

    `∑_{l : c ∉ C_l} mu_l * (leak_l(c))^2  =  (value + t_c)(1 - value - t_c) / size` ,

with `(P u_l)_c` the off-block residual at `c`.

## Endpoint one: an atom at the weight floor

`Gtz.weight_ge_neg_value_of_isChartStationaryData` makes `-value` a lower bound on every
weight.  At an atom ATTAINING it the right side above is zero, so every summand is, and
`projection_mulVec_tightDir_eq_zero_of_weight_eq_neg_value` reads that as: **at a floor
atom every positively weighted active block has zero leak, whether or not it contains the
atom.**  So a floor atom kills the whole `c`-column of the projected tight directions at
once; the geometric content is that all of them are orthogonal to the chart column `P e_c`.

## Endpoint two: a block whose tight direction has zero leak

`weight_eq_neg_value_of_zeroLeak` runs the same 0-or-1 dichotomy the shipped
`Gtz.sq_value_add_weight_of_saturatedAtom` runs on the MULTIPLIER ROW, but on the TIGHT
DIRECTION, and from a different hypothesis: no saturation is assumed, only that one
block's off-block residual vanishes.  The conclusion is that every atom in the support of
that direction sits at the weight floor, and then
`projection_mulVec_eq_zero_of_zeroLeak` gives `P u_l = 0`, i.e. the direction lies in the
chart kernel.  On a design that reads as a linear dependence among the supported atoms,
so a support of size two is a PARALLEL PAIR.

## The closing theorem, and it needs no geometry

`false_of_projected_tightDir_collinear`: at a datum with `-1/size < value < 0` the
projected tight directions of the positively weighted active blocks are NEVER all
collinear.  The proof is an integrality argument.  If they all lie along a unit chart-fixed
`w`, the identity above forces `S * (w_y)^2 = (value + t_y)/size` at every atom with one
constant `S`, summing to `S = value + 1/size`; pairing `w` against a tight direction then
forces the count `|{y ∈ C_l : value + t_y ≠ 0}|` to equal `size * value + 1`, a real number
strictly between zero and one.  No integer lies there, so every scale vanishes, so `S = 0`,
contradicting `S = value + 1/size > 0`.

Both endpoints then close together: a floor atom makes every projected tight direction
orthogonal to `P e_c`, and at `(6,3)` two non-parallel floor atoms cut the three-dimensional
chart range down to a line, which is exactly the collinearity the theorem forbids.  That
last step is the one rung left open below, as the named hypothesis
`HasFloorNormal`; everything above it is discharged.

## What this does NOT do

It excludes no design and retires no obligation.  Every statement quantified over
`Gtz.SixThreeCrux` is VACUOUS if `Gtz.GtzWeighted 6 3` holds.  What is not vacuous is the
general layer: `Gtz.IsChartStationaryData` is inhabited at `Gtz.chartTetraProjection`
(value zero), at `Gtz.chartOctaProjection` (value `1/3`) and at
`Gtz.chartTwoBlockTripleProjection` (value `-1/6`), and the identity, the row law and the
leak identity were checked at all three plus the two `(4,2)` data before this file was
written.
-/
import Mathlib
import Gtz.Quantitative.ChartDisjointBlockExclusion
import Gtz.Quantitative.PrivateAtomQuantization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}
variable {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
  {value : ℝ} {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## L1: the chart is its own transpose, coordinatewise -/

/-- The chart entry is symmetric in its indices. -/
theorem projection_apply_comm_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (rowIndex colIndex : Fin size) :
    projection rowIndex colIndex = projection colIndex rowIndex := by
  have hentry := congrFun (congrFun hdata.isSymmetric colIndex) rowIndex
  rwa [Matrix.transpose_apply] at hentry

/-- Pairing a probe against the chart image of a vector is the same as pairing the chart
image of the probe against the vector. -/
theorem dotProduct_projection_mulVec_comm_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (firstVec secondVec : Fin size → ℝ) :
    firstVec ⬝ᵥ (projection *ᵥ secondVec) = (projection *ᵥ firstVec) ⬝ᵥ secondVec := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun firstIndex _ => Finset.sum_congr rfl fun secondIndex _ => ?_
  rw [projection_apply_comm_of_isChartStationaryData hdata secondIndex firstIndex]
  ring

/-! ## L2: THE MASTER IDENTITY -/

/-- **THE MASTER IDENTITY.**  At every atom,
`∑_l mu_l ((P u_l)_c)^2 = (value + t_c)/size`.

The sandwich makes `(P Xi)_cc` the quadratic form of the assembly against the `c`-th
column of the chart, the shipped expansion of that quadratic form turns it into a sum of
squared overlaps, and each overlap is the `c`-th coordinate of a projected tight
direction.  The forced diagonal closes it. -/
theorem sum_activeWeight_mul_sq_projection_mulVec_tightDir
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel * (projection *ᵥ tightDir activeLabel) atomIndex ^ 2
      = (value + weight atomIndex) * ((size : ℝ))⁻¹ := by
  classical
  have hcolumn : ((projection * chartMultiplierAssembly activeSet activeWeight tightDir)
      * projection) atomIndex atomIndex
      = (fun colIndex => projection atomIndex colIndex)
        ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir
              *ᵥ fun colIndex => projection atomIndex colIndex) := by
    have hleft : ((projection * chartMultiplierAssembly activeSet activeWeight tightDir)
        * projection) atomIndex atomIndex
        = ∑ secondIndex : Fin size, ∑ firstIndex : Fin size,
            projection atomIndex firstIndex
              * chartMultiplierAssembly activeSet activeWeight tightDir firstIndex secondIndex
              * projection atomIndex secondIndex := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun secondIndex _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun firstIndex _ => ?_
      rw [projection_apply_comm_of_isChartStationaryData hdata secondIndex atomIndex]
    have hright : (fun colIndex => projection atomIndex colIndex)
        ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir
              *ᵥ fun colIndex => projection atomIndex colIndex)
        = ∑ firstIndex : Fin size, ∑ secondIndex : Fin size,
            projection atomIndex firstIndex
              * chartMultiplierAssembly activeSet activeWeight tightDir firstIndex secondIndex
              * projection atomIndex secondIndex := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun firstIndex _ => Finset.sum_congr rfl fun secondIndex _ => by
        ring
    rw [hleft, hright, Finset.sum_comm]
  rw [dotProduct_mulVec_chartMultiplierAssembly] at hcolumn
  have hoverlap : ∀ activeLabel : activeIndex,
      tightDir activeLabel ⬝ᵥ (fun colIndex => projection atomIndex colIndex)
        = (projection *ᵥ tightDir activeLabel) atomIndex := by
    intro activeLabel
    simp only [dotProduct, Matrix.mulVec]
    exact Finset.sum_congr rfl fun colIndex _ => mul_comm _ _
  rw [← projection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata,
    diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomIndex] at hcolumn
  rw [hcolumn]
  exact Finset.sum_congr rfl fun activeLabel _ => by rw [hoverlap activeLabel]

/-! ## L3: endpoint one -- an atom at the weight floor -/

/-- **THE FLOOR-ATOM ROW LAW.**  At an atom whose weight ATTAINS the shipped floor
`-value`, every positively weighted active block has a vanishing `c`-coordinate in its
projected tight direction — the leak at `c` if the block misses `c`, and zero by
tightness if it contains it.

This needs no saturation: the atom is not assumed to lie in any active subset. -/
theorem projection_mulVec_tightDir_eq_zero_of_weight_eq_neg_value
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {atomIndex : Fin size} (hfloor : weight atomIndex = -value)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hpositive : 0 < activeWeight activeLabel) :
    (projection *ᵥ tightDir activeLabel) atomIndex = 0 := by
  classical
  have hmaster := sum_activeWeight_mul_sq_projection_mulVec_tightDir hdata atomIndex
  rw [hfloor] at hmaster
  have hvanish : ∑ otherLabel ∈ activeSet,
      activeWeight otherLabel * (projection *ᵥ tightDir otherLabel) atomIndex ^ 2 = 0 := by
    rw [hmaster]; ring
  have hnonneg : ∀ otherLabel ∈ activeSet,
      0 ≤ activeWeight otherLabel * (projection *ᵥ tightDir otherLabel) atomIndex ^ 2 :=
    fun otherLabel hother =>
      mul_nonneg (hdata.activeWeight_nonneg otherLabel hother) (sq_nonneg _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hvanish activeLabel hmem
  rcases mul_eq_zero.mp hterm with hzeroWeight | hzeroSquare
  · exact absurd hzeroWeight (ne_of_gt hpositive)
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzeroSquare

/-! ## L4: the leak identity -/

/-- **THE LEAK IDENTITY.**  Summing the master identity over the blocks that MISS the atom
gives `(value + t_c)(1 - value - t_c)/size`: the blocks containing the atom contribute
`(value + t_c)^2` times the assembly diagonal, which the simplex stationarity pins at
`1/size`. -/
theorem sum_activeWeight_mul_sq_leak
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) [DecidablePred
      fun activeLabel => atomIndex ∈ activeSubset activeLabel] :
    ∑ activeLabel ∈ activeSet.filter (fun activeLabel => atomIndex ∉ activeSubset activeLabel),
        activeWeight activeLabel * (projection *ᵥ tightDir activeLabel) atomIndex ^ 2
      = (value + weight atomIndex) * (1 - (value + weight atomIndex)) * ((size : ℝ))⁻¹ := by
  classical
  have hmaster := sum_activeWeight_mul_sq_projection_mulVec_tightDir hdata atomIndex
  have hsplit := Finset.sum_filter_add_sum_filter_not activeSet
    (fun activeLabel => atomIndex ∉ activeSubset activeLabel)
    (fun activeLabel => activeWeight activeLabel
      * (projection *ᵥ tightDir activeLabel) atomIndex ^ 2)
  have hinside : ∑ activeLabel ∈ activeSet.filter
        (fun activeLabel => ¬ atomIndex ∉ activeSubset activeLabel),
      activeWeight activeLabel * (projection *ᵥ tightDir activeLabel) atomIndex ^ 2
      = (value + weight atomIndex) ^ 2 * ((size : ℝ))⁻¹ := by
    have hrewrite : ∀ activeLabel ∈ activeSet.filter
          (fun activeLabel => ¬ atomIndex ∉ activeSubset activeLabel),
        activeWeight activeLabel * (projection *ᵥ tightDir activeLabel) atomIndex ^ 2
          = (value + weight atomIndex) ^ 2
            * (activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2) := by
      intro activeLabel hlabel
      rw [Finset.mem_filter] at hlabel
      rw [projection_mulVec_tightDir_of_mem hdata hlabel.1 (not_not.mp hlabel.2)]
      ring
    rw [Finset.sum_congr rfl hrewrite, ← Finset.mul_sum]
    congr 1
    have houtside : ∀ activeLabel ∈ activeSet,
        activeLabel ∉ activeSet.filter
            (fun otherLabel => ¬ atomIndex ∉ activeSubset otherLabel) →
          activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2 = 0 := by
      intro activeLabel hlabel hnotFilter
      have hnotMem : atomIndex ∉ activeSubset activeLabel := by
        by_contra hcontra
        exact hnotFilter (Finset.mem_filter.mpr ⟨hlabel, not_not.mpr hcontra⟩)
      rw [hdata.tightDir_support activeLabel hlabel atomIndex hnotMem]
      ring
    rw [Finset.sum_subset (Finset.filter_subset _ _) houtside,
      ← chartMultiplierAssembly_diagonal, hdata.assembly_diagonal atomIndex]
  rw [← hsplit, hinside] at hmaster
  linarith [hmaster]

/-! ## L5: endpoint two -- a block whose tight direction has zero leak -/

/-- The chart image of a tight direction, at EVERY atom, once the off-block residual is
known to vanish: it is the shifted weight diagonal applied to that direction. -/
theorem projection_mulVec_eq_shifted_of_zeroLeak
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hzeroLeak : ∀ atomIndex : Fin size, atomIndex ∉ activeSubset activeLabel →
      (projection *ᵥ tightDir activeLabel) atomIndex = 0) (atomIndex : Fin size) :
    (projection *ᵥ tightDir activeLabel) atomIndex
      = (value + weight atomIndex) * tightDir activeLabel atomIndex := by
  by_cases hmemSubset : atomIndex ∈ activeSubset activeLabel
  · exact projection_mulVec_tightDir_of_mem hdata hmem hmemSubset
  · rw [hzeroLeak atomIndex hmemSubset,
      hdata.tightDir_support activeLabel hmem atomIndex hmemSubset]
    ring

/-- **ZERO LEAK PINS THE SUPPORT AT THE WEIGHT FLOOR.**  If one active block's tight
direction has no off-block residual then every atom it is nonzero at has weight exactly
`-value`.

The chart is a symmetric idempotent, so `|P u|^2 = u ⬝ᵥ P u`; with zero leak both sides
are diagonal sums in `r_y = value + t_y`, giving `∑_y r_y (1 - r_y) u_y^2 = 0`.  The
shipped floor `0 ≤ r_y` and the shipped Naimark bound `r_y ≤ 1` make every summand
nonnegative, so each vanishes, and `r_y = 1` needs a weight above one. -/
theorem weight_eq_neg_value_of_zeroLeak
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hnegative : value < 0)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hzeroLeak : ∀ atomIndex : Fin size, atomIndex ∉ activeSubset activeLabel →
      (projection *ᵥ tightDir activeLabel) atomIndex = 0)
    {atomIndex : Fin size} (hsupported : tightDir activeLabel atomIndex ≠ 0) :
    weight atomIndex = -value := by
  classical
  have hshift := projection_mulVec_eq_shifted_of_zeroLeak hdata hmem hzeroLeak
  have hidempotent : projection *ᵥ (projection *ᵥ tightDir activeLabel)
      = projection *ᵥ tightDir activeLabel := by
    rw [Matrix.mulVec_mulVec, hdata.isIdempotent]
  have hnormEq : (projection *ᵥ tightDir activeLabel) ⬝ᵥ (projection *ᵥ tightDir activeLabel)
      = tightDir activeLabel ⬝ᵥ (projection *ᵥ tightDir activeLabel) := by
    rw [← dotProduct_projection_mulVec_comm_of_isChartStationaryData hdata
      (tightDir activeLabel) (projection *ᵥ tightDir activeLabel), hidempotent]
  have hleftSum : (projection *ᵥ tightDir activeLabel) ⬝ᵥ (projection *ᵥ tightDir activeLabel)
      = ∑ otherIndex : Fin size, (value + weight otherIndex) ^ 2
          * tightDir activeLabel otherIndex ^ 2 := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun otherIndex _ => by rw [hshift otherIndex]; ring
  have hrightSum : tightDir activeLabel ⬝ᵥ (projection *ᵥ tightDir activeLabel)
      = ∑ otherIndex : Fin size, (value + weight otherIndex)
          * tightDir activeLabel otherIndex ^ 2 := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun otherIndex _ => by rw [hshift otherIndex]; ring
  have hdefect : ∑ otherIndex : Fin size,
      ((value + weight otherIndex) * (1 - (value + weight otherIndex))
        * tightDir activeLabel otherIndex ^ 2) = 0 := by
    have hcombine : ∑ otherIndex : Fin size, (value + weight otherIndex)
          * tightDir activeLabel otherIndex ^ 2
        - ∑ otherIndex : Fin size, (value + weight otherIndex) ^ 2
          * tightDir activeLabel otherIndex ^ 2 = 0 := by
      rw [← hrightSum, ← hleftSum, hnormEq, sub_self]
    rw [← Finset.sum_sub_distrib] at hcombine
    rw [← hcombine]
    exact Finset.sum_congr rfl fun otherIndex _ => by ring
  have hnonneg : ∀ otherIndex ∈ (Finset.univ : Finset (Fin size)),
      0 ≤ (value + weight otherIndex) * (1 - (value + weight otherIndex))
        * tightDir activeLabel otherIndex ^ 2 := by
    intro otherIndex _
    have hlow : 0 ≤ value + weight otherIndex := by
      have := weight_ge_neg_value_of_isChartStationaryData hdata otherIndex
      linarith
    have hhigh : value + weight otherIndex ≤ 1 := by
      have := value_le_one_sub_weight_of_isChartStationaryData hdata otherIndex
      linarith
    exact mul_nonneg (mul_nonneg hlow (by linarith)) (sq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdefect atomIndex
    (Finset.mem_univ atomIndex)
  have hsquareNe : tightDir activeLabel atomIndex ^ 2 ≠ 0 := pow_ne_zero 2 hsupported
  have hfactor : (value + weight atomIndex) * (1 - (value + weight atomIndex)) = 0 := by
    rcases mul_eq_zero.mp hzero with hfirst | hsecond
    · exact hfirst
    · exact absurd hsecond hsquareNe
  have hbound : weight atomIndex ≤ 1 :=
    weight_le_one_of_sum_one hdata.weight_sum_one
      (fun otherIndex => (hdata.weight_pos otherIndex).le) atomIndex
  rcases mul_eq_zero.mp hfactor with hfloorRoot | honeRoot
  · linarith
  · linarith

/-- **ZERO LEAK PUTS THE TIGHT DIRECTION IN THE CHART KERNEL.**  On a design this is a
linear dependence among the atoms the direction is supported on, so a support of size two
is a parallel pair. -/
theorem projection_mulVec_eq_zero_of_zeroLeak
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hnegative : value < 0)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hzeroLeak : ∀ atomIndex : Fin size, atomIndex ∉ activeSubset activeLabel →
      (projection *ᵥ tightDir activeLabel) atomIndex = 0) :
    projection *ᵥ tightDir activeLabel = 0 := by
  funext atomIndex
  show (projection *ᵥ tightDir activeLabel) atomIndex = (0 : ℝ)
  rw [projection_mulVec_eq_shifted_of_zeroLeak hdata hmem hzeroLeak atomIndex]
  by_cases hsupported : tightDir activeLabel atomIndex = 0
  · rw [hsupported]; ring
  · rw [weight_eq_neg_value_of_zeroLeak hdata hnegative hmem hzeroLeak hsupported]
    ring

/-! ## L6: THE CLOSING THEOREM -- the projected tight directions are never collinear -/

/-- **THE PROJECTED TIGHT DIRECTIONS ARE NEVER COLLINEAR**, at any chart stationarity
datum whose value lies strictly inside the shipped window `-1/size < value < 0`.

Suppose every positively weighted active block satisfies `P u_l = s_l • w` for one
chart-fixed unit `w`.  The master identity then reads
`S * (w_y)^2 = (value + t_y)/size` at every atom, with the single constant
`S = ∑_l mu_l s_l^2`; summing over the atoms against `w ⬝ᵥ w = 1` and the weight sum
identifies `S = value + 1/size`, which the window makes STRICTLY POSITIVE.  Pairing `w`
against `u_l` gives `s_l` on the left and, coordinate by coordinate on the block,
`s_l / (size * S)` on each atom of the block whose shifted weight is nonzero — atoms with
`value + t_y = 0` contribute nothing because `w` vanishes there.  So a nonzero `s_l` forces

    `|{y ∈ C_l : value + t_y ≠ 0}|  =  size * value + 1` ,

a natural number equal to a real strictly between zero and one.  Hence every `s_l`
vanishes, hence `S = 0`, contradicting `S = value + 1/size > 0`. -/
theorem false_of_projected_tightDir_collinear
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hnegative : value < 0) (hinterior : -((size : ℝ))⁻¹ < value)
    (normal : Fin size → ℝ) (hfixed : projection *ᵥ normal = normal)
    (hunit : normal ⬝ᵥ normal = 1)
    (hcollinear : ∀ activeLabel ∈ activeSet, 0 < activeWeight activeLabel →
      ∃ scale : ℝ, projection *ᵥ tightDir activeLabel = scale • normal) :
    False := by
  classical
  have hsizeCast : (0 : ℝ) < (size : ℝ) := size_cast_pos_of_isChartStationaryData hdata
  have hsizeNe : ((size : ℝ)) ≠ 0 := ne_of_gt hsizeCast
  have hchoose : ∀ activeLabel : activeIndex, ∃ scale : ℝ,
      activeLabel ∈ activeSet → 0 < activeWeight activeLabel →
        projection *ᵥ tightDir activeLabel = scale • normal := by
    intro activeLabel
    by_cases hcase : activeLabel ∈ activeSet ∧ 0 < activeWeight activeLabel
    · obtain ⟨scale, hscale⟩ := hcollinear activeLabel hcase.1 hcase.2
      exact ⟨scale, fun _ _ => hscale⟩
    · exact ⟨0, fun hmem hpositive => absurd ⟨hmem, hpositive⟩ hcase⟩
  choose scaleOf hscaleOf using hchoose
  set spread : ℝ :=
    ∑ activeLabel ∈ activeSet, activeWeight activeLabel * scaleOf activeLabel ^ 2 with hspreadDef
  have hatom : ∀ atomIndex : Fin size,
      spread * normal atomIndex ^ 2 = (value + weight atomIndex) * ((size : ℝ))⁻¹ := by
    intro atomIndex
    rw [← sum_activeWeight_mul_sq_projection_mulVec_tightDir hdata atomIndex, hspreadDef,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun activeLabel hmem => ?_
    rcases eq_or_lt_of_le (hdata.activeWeight_nonneg activeLabel hmem) with hzero | hpositive
    · rw [← hzero]; ring
    · rw [hscaleOf activeLabel hmem hpositive]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have hnormSum : ∑ atomIndex : Fin size, normal atomIndex ^ 2 = 1 := by
    rw [← hunit, dotProduct]
    exact Finset.sum_congr rfl fun atomIndex _ => pow_two (normal atomIndex)
  have hspreadValue : spread = value + ((size : ℝ))⁻¹ := by
    have hsum : ∑ atomIndex : Fin size, spread * normal atomIndex ^ 2
        = ∑ atomIndex : Fin size, (value + weight atomIndex) * ((size : ℝ))⁻¹ :=
      Finset.sum_congr rfl fun atomIndex _ => hatom atomIndex
    rw [← Finset.mul_sum, hnormSum, mul_one, ← Finset.sum_mul, Finset.sum_add_distrib,
      hdata.weight_sum_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum
    rw [hsum]
    field_simp
  have hspreadPos : 0 < spread := by rw [hspreadValue]; linarith
  have hscaleDot : ∀ activeLabel ∈ activeSet, 0 < activeWeight activeLabel →
      scaleOf activeLabel = normal ⬝ᵥ tightDir activeLabel := by
    intro activeLabel hmem hpositive
    have hswap : normal ⬝ᵥ (projection *ᵥ tightDir activeLabel)
        = (projection *ᵥ normal) ⬝ᵥ tightDir activeLabel :=
      dotProduct_projection_mulVec_comm_of_isChartStationaryData hdata normal
        (tightDir activeLabel)
    rw [hfixed, hscaleOf activeLabel hmem hpositive, dotProduct_smul, smul_eq_mul, hunit,
      mul_one] at hswap
    exact hswap
  have hsizeInv : ((size : ℝ)) * ((size : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hsizeNe
  have hspreadNe : spread ≠ 0 := ne_of_gt hspreadPos
  have hproductNe : ((size : ℝ)) * spread ≠ 0 := mul_ne_zero hsizeNe hspreadNe
  have hscaleZero : ∀ activeLabel ∈ activeSet, 0 < activeWeight activeLabel →
      scaleOf activeLabel = 0 := by
    intro activeLabel hmem hpositive
    by_contra hne
    have hnormalVanish : ∀ atomIndex : Fin size, value + weight atomIndex = 0 →
        normal atomIndex = 0 := by
      intro atomIndex hshifted
      have hzero := hatom atomIndex
      rw [hshifted, zero_mul] at hzero
      have hsquare : normal atomIndex ^ 2 = 0 := by
        rcases mul_eq_zero.mp hzero with hspreadEq | hsquareEq
        · exact absurd hspreadEq hspreadNe
        · exact hsquareEq
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsquare
    have hsubsetSum : normal ⬝ᵥ tightDir activeLabel
        = ∑ atomIndex ∈ activeSubset activeLabel,
            normal atomIndex * tightDir activeLabel atomIndex := by
      rw [dotProduct]
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro atomIndex _ hnotMem
      rw [hdata.tightDir_support activeLabel hmem atomIndex hnotMem]
      ring
    have hfilterSum : ∑ atomIndex ∈ activeSubset activeLabel,
          normal atomIndex * tightDir activeLabel atomIndex
        = ∑ atomIndex ∈ (activeSubset activeLabel).filter
            (fun atomIndex => value + weight atomIndex ≠ 0),
          normal atomIndex * tightDir activeLabel atomIndex := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro atomIndex _ hnonzeroTerm hshifted
      rw [hnormalVanish atomIndex hshifted] at hnonzeroTerm
      exact hnonzeroTerm (by ring)
    have hshare : ∀ atomIndex ∈ (activeSubset activeLabel).filter
        (fun atomIndex => value + weight atomIndex ≠ 0),
        normal atomIndex * tightDir activeLabel atomIndex
          = scaleOf activeLabel * (((size : ℝ)) * spread)⁻¹ := by
      intro atomIndex hfiltered
      rw [Finset.mem_filter] at hfiltered
      have hshiftedNe : value + weight atomIndex ≠ 0 := hfiltered.2
      have htight := projection_mulVec_tightDir_of_mem hdata hmem hfiltered.1
      rw [hscaleOf activeLabel hmem hpositive] at htight
      have hcoordinate : (value + weight atomIndex) * tightDir activeLabel atomIndex
          = scaleOf activeLabel * normal atomIndex := by
        simpa only [Pi.smul_apply, smul_eq_mul] using htight.symm
      have hsquare : normal atomIndex ^ 2
          = (value + weight atomIndex) * (((size : ℝ)) * spread)⁻¹ := by
        refine mul_left_cancel₀ hspreadNe ?_
        rw [hatom atomIndex]
        field_simp
      refine mul_left_cancel₀ hshiftedNe ?_
      calc (value + weight atomIndex) * (normal atomIndex * tightDir activeLabel atomIndex)
          = normal atomIndex * ((value + weight atomIndex) * tightDir activeLabel atomIndex) := by
            ring
        _ = normal atomIndex * (scaleOf activeLabel * normal atomIndex) := by rw [hcoordinate]
        _ = scaleOf activeLabel * normal atomIndex ^ 2 := by ring
        _ = scaleOf activeLabel * ((value + weight atomIndex) * (((size : ℝ)) * spread)⁻¹) := by
            rw [hsquare]
        _ = (value + weight atomIndex) * (scaleOf activeLabel * (((size : ℝ)) * spread)⁻¹) := by
            ring
    have hcountEq := hscaleDot activeLabel hmem hpositive
    rw [hsubsetSum, hfilterSum, Finset.sum_congr rfl hshare, Finset.sum_const,
      nsmul_eq_mul] at hcountEq
    set blockCount : ℕ := ((activeSubset activeLabel).filter
      (fun atomIndex => value + weight atomIndex ≠ 0)).card with hblockCountDef
    have hfactor : scaleOf activeLabel
        * (1 - ((blockCount : ℝ)) * (((size : ℝ)) * spread)⁻¹) = 0 := by
      have hregroup : scaleOf activeLabel
          * (((blockCount : ℝ)) * (((size : ℝ)) * spread)⁻¹)
          = ((blockCount : ℝ)) * (scaleOf activeLabel * (((size : ℝ)) * spread)⁻¹) := by ring
      rw [mul_sub, mul_one, hregroup, ← hcountEq, sub_self]
    have hcancel : ((blockCount : ℝ)) = ((size : ℝ)) * spread := by
      rcases mul_eq_zero.mp hfactor with hzeroScale | hunitProduct
      · exact absurd hzeroScale hne
      · field_simp at hunitProduct
        linarith [hunitProduct]
    rw [hspreadValue] at hcancel
    have hexpand : ((blockCount : ℝ)) = ((size : ℝ)) * value + 1 := by
      rw [hcancel, mul_add, hsizeInv]
    have hupper : ((blockCount : ℝ)) < 1 := by
      rw [hexpand]
      nlinarith [hnegative, hsizeCast]
    have hlower : (0 : ℝ) < ((blockCount : ℝ)) := by
      have hscaled := mul_lt_mul_of_pos_left hinterior hsizeCast
      rw [mul_neg, hsizeInv] at hscaled
      rw [hexpand]
      linarith
    have hzeroCount : blockCount = 0 := by
      by_contra hnonzero
      have hone : (1 : ℝ) ≤ ((blockCount : ℝ)) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnonzero
      linarith
    rw [hzeroCount] at hlower
    simp at hlower
  have hspreadZero : spread = 0 := by
    rw [hspreadDef]
    refine Finset.sum_eq_zero fun activeLabel hmem => ?_
    rcases eq_or_lt_of_le (hdata.activeWeight_nonneg activeLabel hmem) with hzero | hpositive
    · rw [← hzero]; ring
    · rw [hscaleZero activeLabel hmem hpositive]; ring
  rw [hspreadZero] at hspreadPos
  exact lt_irrefl 0 hspreadPos

/-! ## L7: the named rung, and the two endpoints chained -/

/-- **THE ONE OPEN RUNG OF THIS SPINE.**  A unit chart-fixed vector that vanishes at every
atom sitting at the weight floor `-value`, and SPANS every chart-fixed vector that does.

At `rank = 3` supplying it is a rank count and nothing more.  The chart-fixed vectors
vanishing at two atoms form a subspace of dimension `rank - rank P[{firstAtom, secondAtom}]`,
so two floor atoms whose two-by-two chart block is nonsingular — on a design, two atoms
that are not parallel — leave exactly a line, and any unit vector on it serves.  The
degenerate alternative, that the floor atoms span the whole chart range, forces
`value = -1/size` through `Gtz.trace_projection_mul_multiplier_of_isChartStationaryData`
and is excluded by `Gtz.neg_inv_size_lt_value_of_isChartStationaryData`. -/
def HasFloorSpanningNormal (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) (normal : Fin size → ℝ) : Prop :=
  projection *ᵥ normal = normal ∧ normal ⬝ᵥ normal = 1
    ∧ (∀ atomIndex : Fin size, weight atomIndex = -value → normal atomIndex = 0)
    ∧ ∀ fixedVec : Fin size → ℝ, projection *ᵥ fixedVec = fixedVec →
        (∀ atomIndex : Fin size, weight atomIndex = -value → fixedVec atomIndex = 0) →
        ∃ scale : ℝ, fixedVec = scale • normal

/-- **THE ENDPOINT CHAIN.**  A chart stationarity datum strictly inside the shipped value
window admits no floor-spanning normal.

The row law puts every positively weighted projected tight direction inside the span, the
chart image of a tight direction is chart-fixed by idempotence, and the closing theorem
does the rest. -/
theorem false_of_hasFloorSpanningNormal
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hnegative : value < 0) (hinterior : -((size : ℝ))⁻¹ < value)
    {normal : Fin size → ℝ}
    (hnormal : HasFloorSpanningNormal projection weight value normal) :
    False := by
  obtain ⟨hfixed, hunit, _, hspan⟩ := hnormal
  refine false_of_projected_tightDir_collinear hdata hnegative hinterior normal hfixed hunit ?_
  intro activeLabel hmem hpositive
  refine hspan _ ?_ ?_
  · rw [Matrix.mulVec_mulVec, hdata.isIdempotent]
  · intro atomIndex hfloor
    exact projection_mulVec_tightDir_eq_zero_of_weight_eq_neg_value hdata hfloor hmem hpositive

/-- **THE TWO ENDPOINTS MEET.**  At an atom the zero-leak direction is supported at, EVERY
positively weighted active block already has a vanishing coordinate — the second endpoint
manufactures the first.  So one block with no off-block residual pins a whole column of
the projected tight directions to zero, at every atom of its support at once. -/
theorem projection_mulVec_tightDir_eq_zero_of_zeroLeak_of_supported
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hnegative : value < 0)
    {leakFreeLabel : activeIndex} (hleakFreeMem : leakFreeLabel ∈ activeSet)
    (hzeroLeak : ∀ atomIndex : Fin size, atomIndex ∉ activeSubset leakFreeLabel →
      (projection *ᵥ tightDir leakFreeLabel) atomIndex = 0)
    {atomIndex : Fin size} (hsupported : tightDir leakFreeLabel atomIndex ≠ 0)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hpositive : 0 < activeWeight activeLabel) :
    (projection *ᵥ tightDir activeLabel) atomIndex = 0 :=
  projection_mulVec_tightDir_eq_zero_of_weight_eq_neg_value hdata
    (weight_eq_neg_value_of_zeroLeak hdata hnegative hleakFreeMem hzeroLeak hsupported) hmem
    hpositive

end Gtz

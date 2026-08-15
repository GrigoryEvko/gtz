import Gtz.Design.StarOnlyLaw
import Gtz.Design.WallCollapse
import Gtz.Design.ChartReadingLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The star-corank closure platform

The corank-two wall lives only over the four vertex stars.  This module builds
the closure platform on that wall.

* `pointer_swaps_iff_singleton` — the swap quantifier of the wall data
  collapses to its singleton case: one inequality carries every selection
  through the pointer.
* `directionChartGap_sdiff` and `quadForm_on_kernel_of_sdiff` — the exchange
  bookkeeping: at a kernel probe of the wall tree, any other selection reads
  as its incoming boost energy minus its outgoing boost energy.
* `kFourGaugeStar_corankTwo_normalForm` — the wall normal form at the gauge
  star: a strictly positive scale and an axis with three positive pairwise
  products.
* `kFourStar_two_outside_mem_star` — two labels outside a star share a star.
* `corankTwo_star_candidate_readings` — **the double-pointer package**: a
  corank-two star wall hands a second star that reads strictly positively at
  both kernel directions of the wall tree.
* `KFourStarWallAtlasFires` and `kFourStarWall_empty_of_atlasFires` — the
  vacuity target: the probe reads the unsigned minor atlas FIRING at every
  sampled wall point (4000 of 4000; directed attack floor one cell, never
  zero), so the star-corank branch dies against the atlas silence of the A3
  antecedent stack once the target is proved.
-/

namespace Gtz

open Matrix

/-! ## 1. The singleton collapse of the swap quantifier -/

/-- The swap quantifier of the wall data collapses to its singleton case: a
positive singleton reading at the pointer already gives the positive reading
of every selection through the pointer. -/
theorem pointer_swaps_iff_singleton {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) {mass weight : Fin size → ℝ}
    (hmass : ∀ label, 0 ≤ mass label) (hweight : ∀ label, 0 < weight label)
    (pointer : Fin size) (probe : Fin 3 → ℝ) :
    (∀ swap : Finset (Fin size), pointer ∈ swap →
        0 < probe ⬝ᵥ (directionChartGap direction mass weight swap *ᵥ probe)) ↔
      0 < probe ⬝ᵥ
        (directionChartGap direction mass weight {pointer} *ᵥ probe) := by
  constructor
  · intro hall
    exact hall {pointer} (Finset.mem_singleton_self pointer)
  · intro hsingle swap hmem
    rw [dotProduct_directionChartGap_mulVec_eq] at hsingle ⊢
    rw [Finset.sum_singleton] at hsingle
    have hterm : ∀ label ∈ swap,
        0 ≤ mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 :=
      fun label _ =>
        mul_nonneg (div_nonneg (hmass label) (hweight label).le) (sq_nonneg _)
    have hsum : mass pointer / weight pointer * (direction pointer ⬝ᵥ probe) ^ 2
        ≤ ∑ label ∈ swap,
            mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 :=
      Finset.single_le_sum hterm hmem
    linarith

/-! ## 2. The exchange bookkeeping -/

/-- A boost sum reads at a probe as the boosted squared direction readings. -/
theorem boostSum_reading {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (part : Finset (Fin size))
    (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((∑ label ∈ part,
        (mass label / weight label) • atomMatrix (direction label)) *ᵥ probe)
      = ∑ label ∈ part,
          mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, dotProduct_atomMatrix_mulVec_pair,
    smul_eq_mul, pow_two]

/-- The gap difference of two selections is the boost sum over the exchanged
labels: incoming minus outgoing.  The mass side cancels. -/
theorem directionChartGap_sdiff {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (incoming outgoing : Finset (Fin size)) :
    directionChartGap direction mass weight incoming
        - directionChartGap direction mass weight outgoing
      = (∑ label ∈ incoming \ outgoing,
            (mass label / weight label) • atomMatrix (direction label))
        - ∑ label ∈ outgoing \ incoming,
            (mass label / weight label) • atomMatrix (direction label) := by
  set boost : Fin size → Matrix (Fin 3) (Fin 3) ℝ :=
    fun label => (mass label / weight label) • atomMatrix (direction label)
    with hboost
  have hout : (∑ label ∈ outgoing \ incoming, boost label)
      + ∑ label ∈ incoming, boost label
      = ∑ label ∈ outgoing ∪ incoming, boost label := by
    rw [← Finset.sum_union Finset.sdiff_disjoint,
      Finset.sdiff_union_self_eq_union]
  have hinc : (∑ label ∈ incoming \ outgoing, boost label)
      + ∑ label ∈ outgoing, boost label
      = ∑ label ∈ incoming ∪ outgoing, boost label := by
    rw [← Finset.sum_union Finset.sdiff_disjoint,
      Finset.sdiff_union_self_eq_union]
  rw [Finset.union_comm] at hout
  have hswap : (∑ label ∈ incoming, boost label)
      - ∑ label ∈ outgoing, boost label
      = (∑ label ∈ incoming \ outgoing, boost label)
        - ∑ label ∈ outgoing \ incoming, boost label := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm]
    exact hout.trans hinc.symm
  unfold directionChartGap
  calc (∑ label ∈ incoming, boost label)
        - (∑ label, mass label • atomMatrix (direction label))
        - ((∑ label ∈ outgoing, boost label)
          - ∑ label, mass label • atomMatrix (direction label))
      = (∑ label ∈ incoming, boost label)
        - ∑ label ∈ outgoing, boost label := by abel
    _ = _ := hswap

/-- **The kernel-probe exchange reading.**  At a kernel probe of the outgoing
selection, any other selection reads as the exchanged boosts alone: incoming
boost energy minus outgoing boost energy. -/
theorem quadForm_on_kernel_of_sdiff {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {incoming outgoing : Finset (Fin size)} {probe : Fin 3 → ℝ}
    (hker : directionChartGap direction mass weight outgoing *ᵥ probe = 0) :
    probe ⬝ᵥ (directionChartGap direction mass weight incoming *ᵥ probe)
      = (∑ label ∈ incoming \ outgoing,
            mass label / weight label * (direction label ⬝ᵥ probe) ^ 2)
        - ∑ label ∈ outgoing \ incoming,
            mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 := by
  have hkerRead : probe ⬝ᵥ
      (directionChartGap direction mass weight outgoing *ᵥ probe) = 0 := by
    rw [hker, dotProduct_zero]
  have hsplit : probe ⬝ᵥ
      (directionChartGap direction mass weight incoming *ᵥ probe)
      = probe ⬝ᵥ ((directionChartGap direction mass weight incoming
          - directionChartGap direction mass weight outgoing) *ᵥ probe) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, hkerRead, sub_zero]
  rw [hsplit, directionChartGap_sdiff, Matrix.sub_mulVec, dotProduct_sub,
    boostSum_reading, boostSum_reading]

/-! ## 3. The gauge-star wall normal form -/

/-- **The wall normal form.**  At the gauge star the corank-two package gives
a strictly positive scale and an axis whose three pairwise coordinate products
are positive: the axis is one-signed. -/
theorem kFourGaugeStar_corankTwo_normalForm (point : DirectionChartPoint 6)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef)
    (hdata : KFourTreeGapCorankTwoData point {3, 4, 5}) :
    ∃ (axis : Fin 3 → ℝ) (scale : ℝ),
      directionChartGap kFourDirection point.mass point.weight
          ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis ∧
      0 < scale ∧ 0 < axis 0 * axis 1 ∧ 0 < axis 0 * axis 2 ∧
      0 < axis 1 * axis 2 := by
  obtain ⟨tight, second, pointer, htightNe, hpointerOut, htightKer,
    hpointerReads, hsecondNe, hsecondKer, hpointerOrth, hnotCol⟩ := hdata
  have hsymm := directionChartGap_transpose kFourDirection point.mass
    point.weight ({3, 4, 5} : Finset (Fin 6))
  have hcrossNe : crossProduct tight second ≠ 0 := by
    intro hzero
    obtain ⟨ratio, hratio⟩ := eq_smul_of_crossProduct_eq_zero htightNe hzero
    exact hnotCol ⟨ratio, hratio⟩
  obtain ⟨scale, hscaleEq⟩ :=
    exists_rankOne_of_symm_twoKernel hsymm htightKer hsecondKer hcrossNe
  have hscaleNonneg : 0 ≤ scale :=
    scale_nonneg_of_posSemidef_smul_atom hpsd hcrossNe hscaleEq
  obtain ⟨c0, c1, c2, _, _, _⟩ := kFourCoeff_eq_of_rankOne hscaleEq
  have h0 := chartCoeff_neg_of_not_mem point
    (show (0 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6)) by decide)
  have h1 := chartCoeff_neg_of_not_mem point
    (show (1 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6)) by decide)
  have h2 := chartCoeff_neg_of_not_mem point
    (show (2 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6)) by decide)
  rw [c0] at h0
  rw [c1] at h1
  rw [c2] at h2
  have h0' : 0 < scale * (crossProduct tight second 0
      * crossProduct tight second 1) := by linarith
  have h1' : 0 < scale * (crossProduct tight second 0
      * crossProduct tight second 2) := by linarith
  have h2' : 0 < scale * (crossProduct tight second 1
      * crossProduct tight second 2) := by linarith
  have hscaleNe : scale ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h0'
    exact lt_irrefl 0 h0'
  have hscalePos : 0 < scale := lt_of_le_of_ne hscaleNonneg (Ne.symm hscaleNe)
  refine ⟨crossProduct tight second, scale, hscaleEq, hscalePos, ?_, ?_, ?_⟩
  · nlinarith [h0', hscalePos]
  · nlinarith [h1', hscalePos]
  · nlinarith [h2', hscalePos]

/-! ## 4. The shared star of the two pointers -/

/-- Two distinct labels outside a vertex star are edges of the opposite
triangle, and two triangle edges share a vertex: some star contains both. -/
theorem kFourStar_two_outside_mem_star :
    ∀ tree ∈ kFourStarList, ∀ pOne pTwo : Fin 6, pOne ∉ tree → pTwo ∉ tree →
      pOne ≠ pTwo → ∃ cand ∈ kFourStarList, pOne ∈ cand ∧ pTwo ∈ cand := by
  decide

/-! ## 5. The double-pointer candidate package -/

/-- **The double-pointer package.**  A corank-two star wall hands a second
vertex star that reads strictly positively at BOTH kernel directions of the
wall tree.  What separates this package from strictness of the candidate is
exactly the two-dimensional determinant condition and the axis reading — the
named residual of the closure. -/
theorem corankTwo_star_candidate_readings (point : DirectionChartPoint 6)
    {tree : Finset (Fin 6)} (hstar : tree ∈ kFourStarList)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hdata : KFourTreeGapCorankTwoData point tree) :
    ∃ cand ∈ kFourStarList, ∃ tight second : Fin 3 → ℝ,
      tight ≠ 0 ∧ second ≠ 0 ∧ (¬ ∃ ratio : ℝ, second = ratio • tight) ∧
      directionChartGap kFourDirection point.mass point.weight tree
          *ᵥ tight = 0 ∧
      directionChartGap kFourDirection point.mass point.weight tree
          *ᵥ second = 0 ∧
      0 < tight ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
          cand *ᵥ tight) ∧
      0 < second ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
          cand *ᵥ second) := by
  have hwindow := windowCorankTwo_of_kFourTreeGapCorankTwoData point hdata
  obtain ⟨pOne, pTwo, tight, second, hpOneOut, hpTwoOut, hneq, htightNe,
    hsecondNe, htightKer, hsecondKer, horth, hnotCol, hswapOne, hswapTwo⟩ :=
    corankTwo_exists_second_pointer point
      (kFourStarList_subset_treeList tree hstar) hweak hwindow
  obtain ⟨cand, hcandStar, hpOneMem, hpTwoMem⟩ :=
    kFourStar_two_outside_mem_star tree hstar pOne pTwo hpOneOut hpTwoOut
      (Ne.symm hneq)
  exact ⟨cand, hcandStar, tight, second, htightNe, hsecondNe, hnotCol,
    htightKer, hsecondKer, hswapOne cand hpOneMem, hswapTwo cand hpTwoMem⟩

/-! ## 6. The vacuity target -/

/-- **The vacuity target.**  At every exactly-sampled corank-two star wall
point the unsigned minor atlas FIRES (4000 of 4000; a directed attack on the
firing count reaches one cell and never zero).  This Prop names the closure
route: the star wall forces the atlas. -/
def KFourStarWallAtlasFires : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourStarList →
    (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef →
    KFourTreeGapCorankTwoData point tree →
    KFourAllTreeMinorAtlasCellFires point

/-- Against the atlas silence of the A3 antecedent stack, the vacuity target
empties the star-corank branch. -/
theorem kFourStarWall_empty_of_atlasFires (hlaw : KFourStarWallAtlasFires)
    (point : DirectionChartPoint 6)
    (hnotAtlas : ¬ KFourAllTreeMinorAtlasCellFires point)
    {tree : Finset (Fin 6)} (hstar : tree ∈ kFourStarList)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hdata : KFourTreeGapCorankTwoData point tree) : False :=
  hnotAtlas (hlaw point tree hstar hpsd hdata)

end Gtz

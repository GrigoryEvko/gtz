import Gtz.Wave.KFourTreeWindowCorankReduction
import Gtz.Quantitative.ZeroLeakCollinearClosure
import Gtz.Design.SphereExistence
import Gtz.Design.StratumSqueeze

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The star-only law of the corank-two wall

At the corank-two wall the tree gap kills two cross-independent directions, so
the gap is a nonnegative multiple of one rank-one atom.  The six chart
coefficients of that atom in the K4 direction basis have a closed form, and the
chart signs (positive on the tree, negative off it) admit that closed form only
when the tree is a vertex star.

* `exists_rankOne_of_symm_twoKernel` — a symmetric matrix that kills two
  cross-independent vectors is a scalar multiple of the atom of their cross
  product.
* `directionChartGap_eq_coeff_sum` — the chart gap is the coefficient sum
  `∑ c, chartCoeff c • atomMatrix (direction c)`, with `chartCoeff` positive
  on the selection and negative off it.
* `kFourCoeff_eq_of_rankOne` — at a rank-one gap the six coefficients read
  `(-z₀z₁, -z₀z₂, -z₁z₂, z₀σ, z₁σ, z₂σ)` up to the nonnegative scale.
* `kFourCorankTwo_tree_mem_starList` — **the star-only law**: a weak tree
  with the corank-two gap package is a vertex star.
* `kFourCorankTwo_not_path` — the corank-two wall is empty over the twelve
  path trees.
* `kFourWeakTreeGapCorankResidual_refine_star` — the residual's corank branch
  always carries a star.
-/

namespace Gtz

open Matrix

/-! ## 1. The rank-one extraction from a two-dimensional kernel -/

/-- A column of a symmetric matrix reads against a vector as the matrix action
on that vector. -/
theorem column_dot_eq_of_transpose {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : Gᵀ = G) (u : Fin 3 → ℝ) (col : Fin 3) :
    (fun row => G row col) ⬝ᵥ u = (G *ᵥ u) col := by
  simp only [dotProduct, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun row _ => ?_
  have hentry : G row col = G col row := by
    have := congrFun (congrFun hsymm row) col
    rw [Matrix.transpose_apply] at this
    exact this.symm
  rw [hentry]

/-- **The two-kernel rank collapse.**  A symmetric three-by-three matrix that
kills two cross-independent vectors is a scalar multiple of the rank-one atom
of their cross product. -/
theorem exists_rankOne_of_symm_twoKernel {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : Gᵀ = G) {kernelOne kernelTwo : Fin 3 → ℝ}
    (hone : G *ᵥ kernelOne = 0) (htwo : G *ᵥ kernelTwo = 0)
    (hcross : crossProduct kernelOne kernelTwo ≠ 0) :
    ∃ scale : ℝ, G = scale • atomMatrix (crossProduct kernelOne kernelTwo) := by
  set axis := crossProduct kernelOne kernelTwo with haxis
  have hcolumn : ∀ col : Fin 3, ∃ ratio : ℝ, (fun row => G row col) = ratio • axis := by
    intro col
    refine exists_smul_crossProduct_of_dotProduct_eq_zero hcross ?_ ?_
    · rw [column_dot_eq_of_transpose hsymm kernelOne col, hone]
      rfl
    · rw [column_dot_eq_of_transpose hsymm kernelTwo col, htwo]
      rfl
  choose ratio hratio using hcolumn
  obtain ⟨pivot, hpivot⟩ := Function.ne_iff.mp hcross
  rw [Pi.zero_apply] at hpivot
  refine ⟨ratio pivot / axis pivot, ?_⟩
  ext row col
  have hentry : G row col = ratio col * axis row := by
    have := congrFun (hratio col) row
    simpa [smul_eq_mul, mul_comm] using this
  have hswap : ratio col * axis pivot = ratio pivot * axis col := by
    have hfirst : G pivot col = ratio col * axis pivot := by
      have := congrFun (hratio col) pivot
      simpa [smul_eq_mul, mul_comm] using this
    have hsecond : G col pivot = ratio pivot * axis col := by
      have := congrFun (hratio pivot) col
      simpa [smul_eq_mul, mul_comm] using this
    have hsymmEntry : G pivot col = G col pivot := by
      have := congrFun (congrFun hsymm pivot) col
      rw [Matrix.transpose_apply] at this
      exact this.symm
    rw [← hfirst, hsymmEntry, hsecond]
  have hgoal : axis pivot * G row col = ratio pivot * axis col * axis row := by
    rw [hentry]
    linear_combination axis row * hswap
  simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  field_simp
  linear_combination hgoal

/-- The scale of a positive-semidefinite rank-one form is nonnegative. -/
theorem scale_nonneg_of_posSemidef_smul_atom {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : G.PosSemidef) {axis : Fin 3 → ℝ} {scale : ℝ}
    (hne : axis ≠ 0) (heq : G = scale • atomMatrix axis) : 0 ≤ scale := by
  have hform : 0 ≤ axis ⬝ᵥ (G *ᵥ axis) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 axis
    rwa [star_trivial] at h
  have hquad : axis ⬝ᵥ (G *ᵥ axis) = scale * (axis ⬝ᵥ axis) ^ 2 := by
    rw [heq, Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hpos : 0 < axis ⬝ᵥ axis := dotProduct_self_pos hne
  nlinarith [hform, hquad, pow_pos hpos 2]

/-! ## 2. The chart coefficient reading -/

/-- The membership coefficient of one direction in the chart gap. -/
noncomputable def chartCoeff {size : ℕ} (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (label : Fin size) : ℝ :=
  (if label ∈ selected then mass label / weight label else 0) - mass label

/-- The chart gap is the coefficient combination of the direction atoms. -/
theorem directionChartGap_eq_coeff_sum {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) :
    directionChartGap direction mass weight selected
      = ∑ label, chartCoeff mass weight selected label • atomMatrix (direction label) := by
  unfold directionChartGap chartCoeff
  have hsplit : ∀ label : Fin size,
      ((if label ∈ selected then mass label / weight label else 0) - mass label)
          • atomMatrix (direction label)
        = (if label ∈ selected then
            (mass label / weight label) • atomMatrix (direction label) else 0)
          - mass label • atomMatrix (direction label) := by
    intro label
    by_cases hmem : label ∈ selected
    · rw [if_pos hmem, if_pos hmem, sub_smul]
    · rw [if_neg hmem, if_neg hmem, sub_smul, zero_smul]
  rw [Finset.sum_congr rfl fun label _ => hsplit label, Finset.sum_sub_distrib,
    Finset.sum_ite_mem, Finset.univ_inter]

/-- Every chart weight is below one: the weights are a probability vector over
at least two labels. -/
theorem directionChartPoint_weight_lt_one (point : DirectionChartPoint 6)
    (label : Fin 6) : point.weight label < 1 := by
  have hsum := point.weight_sum_one
  have hsplit : ∑ l, point.weight l
      = point.weight label + ∑ l ∈ Finset.univ.erase label, point.weight l :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ label)).symm
  have hcard : (Finset.univ.erase label).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ label),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hrest : 0 < ∑ l ∈ Finset.univ.erase label, point.weight l :=
    Finset.sum_pos (fun l _ => point.weight_pos l) hcard
  linarith [hsum ▸ hsplit]

/-- On the selection the chart coefficient is strictly positive. -/
theorem chartCoeff_pos_of_mem (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} {label : Fin 6} (hmem : label ∈ selected) :
    0 < chartCoeff point.mass point.weight selected label := by
  unfold chartCoeff
  rw [if_pos hmem]
  have hm := point.mass_pos label
  have hw := point.weight_pos label
  have hlt := directionChartPoint_weight_lt_one point label
  have hdiv : point.mass label < point.mass label / point.weight label := by
    rw [lt_div_iff₀ hw]
    nlinarith
  linarith

/-- Off the selection the chart coefficient is strictly negative. -/
theorem chartCoeff_neg_of_not_mem (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} {label : Fin 6} (hmem : label ∉ selected) :
    chartCoeff point.mass point.weight selected label < 0 := by
  unfold chartCoeff
  rw [if_neg hmem, zero_sub, neg_lt, neg_zero]
  exact point.mass_pos label

/-! ## 3. The six K4 coefficients of a rank-one gap -/

/-- **The closed form.**  At a rank-one K4 chart gap `scale • zzᵀ` the six
chart coefficients are `(-z₀z₁, -z₀z₂, -z₁z₂, z₀σ, z₁σ, z₂σ)` scaled, with
`σ` the coordinate sum of the axis. -/
theorem kFourCoeff_eq_of_rankOne {mass weight : Fin 6 → ℝ}
    {selected : Finset (Fin 6)} {axis : Fin 3 → ℝ} {scale : ℝ}
    (heq : directionChartGap kFourDirection mass weight selected
      = scale • atomMatrix axis) :
    chartCoeff mass weight selected 0 = -(scale * (axis 0 * axis 1)) ∧
    chartCoeff mass weight selected 1 = -(scale * (axis 0 * axis 2)) ∧
    chartCoeff mass weight selected 2 = -(scale * (axis 1 * axis 2)) ∧
    chartCoeff mass weight selected 3
      = scale * (axis 0 * (axis 0 + axis 1 + axis 2)) ∧
    chartCoeff mass weight selected 4
      = scale * (axis 1 * (axis 0 + axis 1 + axis 2)) ∧
    chartCoeff mass weight selected 5
      = scale * (axis 2 * (axis 0 + axis 1 + axis 2)) := by
  have hsum := (directionChartGap_eq_coeff_sum kFourDirection mass weight selected).symm.trans heq
  have entry : ∀ i j : Fin 3,
      (∑ label, chartCoeff mass weight selected label
          * (kFourDirection label i * kFourDirection label j))
        = scale * (axis i * axis j) := by
    intro i j
    have := congrFun (congrFun hsum i) j
    simpa [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul, mul_assoc] using this
  have e01 := entry 0 1
  have e02 := entry 0 2
  have e12 := entry 1 2
  have e00 := entry 0 0
  have e11 := entry 1 1
  have e22 := entry 2 2
  simp only [Fin.sum_univ_six] at e01 e02 e12 e00 e11 e22
  simp [kFourDirection] at e01 e02 e12 e00 e11 e22
  refine ⟨by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
  · linear_combination e00 + e01 + e02
  · linear_combination e11 + e01 + e12
  · linear_combination e22 + e02 + e12

/-! ## 4. The star-only law -/

/-- **THE STAR-ONLY LAW.**  A weak spanning tree whose gap carries the
corank-two package is a vertex star: the rank-one closed form makes the chart
sign pattern (positive on the tree, negative off it) impossible at every path
tree. -/
theorem kFourCorankTwo_tree_mem_starList (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} (hsel : selected ∈ kFourSpanningTreeList)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosSemidef)
    (hdata : KFourTreeGapCorankTwoData point selected) :
    selected ∈ kFourStarList := by
  obtain ⟨tight, second, pointer, htightNe, hpointerOut, htightKer, hpointerReads,
    hsecondNe, hsecondKer, hpointerOrth, hnotCol⟩ := hdata
  have hsymm := directionChartGap_transpose kFourDirection point.mass point.weight selected
  have hcrossNe : crossProduct tight second ≠ 0 := by
    intro hzero
    obtain ⟨ratio, hratio⟩ := eq_smul_of_crossProduct_eq_zero htightNe hzero
    exact hnotCol ⟨ratio, hratio⟩
  obtain ⟨scale, hscaleEq⟩ :=
    exists_rankOne_of_symm_twoKernel hsymm htightKer hsecondKer hcrossNe
  have hscale : 0 ≤ scale :=
    scale_nonneg_of_posSemidef_smul_atom hpsd hcrossNe hscaleEq
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := kFourCoeff_eq_of_rankOne hscaleEq
  set A := crossProduct tight second 0 with hA
  set B := crossProduct tight second 1 with hB
  set Cz := crossProduct tight second 2 with hCz
  have hposMem : ∀ label ∈ selected,
      0 < chartCoeff point.mass point.weight selected label :=
    fun label hmem => chartCoeff_pos_of_mem point hmem
  have hnegOut : ∀ label, label ∉ selected →
      chartCoeff point.mass point.weight selected label < 0 :=
    fun label hmem => chartCoeff_neg_of_not_mem point hmem
  simp only [kFourSpanningTreeList, List.mem_cons, List.not_mem_nil, or_false] at hsel
  rcases hsel with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  -- the four stars
  · rw [h]; simp [kFourStarList]
  · rw [h]; simp [kFourStarList]
  · rw [h]; simp [kFourStarList]
  · rw [h]; simp [kFourStarList]
  -- {0, 1, 4}: the σ pair (B, Cz) against the off-tree product 2
  · exfalso
    have s2 := hnegOut 2 (by rw [h]; decide)
    have s4 := hposMem 4 (by rw [h]; decide)
    have s5 := hnegOut 5 (by rw [h]; decide)
    rw [c2] at s2; rw [c4] at s4; rw [c5] at s5
    nlinarith [mul_pos s4 (neg_pos.mpr s5),
      mul_nonneg (by linarith : (0:ℝ) ≤ scale * (B * Cz))
        (mul_nonneg hscale (sq_nonneg (A + B + Cz)))]
  -- {0, 1, 5}: the σ pair (B, Cz), in-tree σ label 5
  · exfalso
    have s2 := hnegOut 2 (by rw [h]; decide)
    have s4 := hnegOut 4 (by rw [h]; decide)
    have s5 := hposMem 5 (by rw [h]; decide)
    rw [c2] at s2; rw [c4] at s4; rw [c5] at s5
    nlinarith [mul_pos s5 (neg_pos.mpr s4),
      mul_nonneg (by linarith : (0:ℝ) ≤ scale * (B * Cz))
        (mul_nonneg hscale (sq_nonneg (A + B + Cz)))]
  -- {0, 2, 3}: the σ pair (A, Cz), in-tree σ label 3
  · exfalso
    have s1 := hnegOut 1 (by rw [h]; decide)
    have s3 := hposMem 3 (by rw [h]; decide)
    have s5 := hnegOut 5 (by rw [h]; decide)
    rw [c1] at s1; rw [c3] at s3; rw [c5] at s5
    nlinarith [mul_pos s3 (neg_pos.mpr s5),
      mul_nonneg (by linarith : (0:ℝ) ≤ scale * (A * Cz))
        (mul_nonneg hscale (sq_nonneg (A + B + Cz)))]
  -- {0, 2, 5}: the σ pair (A, Cz), in-tree σ label 5
  · exfalso
    have s1 := hnegOut 1 (by rw [h]; decide)
    have s3 := hnegOut 3 (by rw [h]; decide)
    have s5 := hposMem 5 (by rw [h]; decide)
    rw [c1] at s1; rw [c3] at s3; rw [c5] at s5
    nlinarith [mul_pos s5 (neg_pos.mpr s3),
      mul_nonneg (by linarith : (0:ℝ) ≤ scale * (A * Cz))
        (mul_nonneg hscale (sq_nonneg (A + B + Cz)))]
  -- {0, 3, 5}: one product positive, two negative
  · exfalso
    have s0 := hposMem 0 (by rw [h]; decide)
    have s1 := hnegOut 1 (by rw [h]; decide)
    have s2 := hnegOut 2 (by rw [h]; decide)
    rw [c0] at s0; rw [c1] at s1; rw [c2] at s2
    nlinarith [mul_pos (by linarith : (0:ℝ) < scale * (A * Cz))
        (by linarith : (0:ℝ) < scale * (B * Cz)),
      mul_nonneg (by linarith : (0:ℝ) ≤ -(scale * (A * B)))
        (mul_nonneg hscale (sq_nonneg Cz))]
  -- {0, 4, 5}: one product positive, two negative
  · exfalso
    have s0 := hposMem 0 (by rw [h]; decide)
    have s1 := hnegOut 1 (by rw [h]; decide)
    have s2 := hnegOut 2 (by rw [h]; decide)
    rw [c0] at s0; rw [c1] at s1; rw [c2] at s2
    nlinarith [mul_pos (by linarith : (0:ℝ) < scale * (A * Cz))
        (by linarith : (0:ℝ) < scale * (B * Cz)),
      mul_nonneg (by linarith : (0:ℝ) ≤ -(scale * (A * B)))
        (mul_nonneg hscale (sq_nonneg Cz))]
  -- {1, 2, 3}: the σ pair (A, B), in-tree σ label 3
  · exfalso
    have s0 := hnegOut 0 (by rw [h]; decide)
    have s3 := hposMem 3 (by rw [h]; decide)
    have s4 := hnegOut 4 (by rw [h]; decide)
    rw [c0] at s0; rw [c3] at s3; rw [c4] at s4
    nlinarith [mul_pos s3 (neg_pos.mpr s4),
      mul_nonneg (by linarith : (0:ℝ) ≤ scale * (A * B))
        (mul_nonneg hscale (sq_nonneg (A + B + Cz)))]
  -- {1, 2, 4}: the σ pair (A, B), in-tree σ label 4
  · exfalso
    have s0 := hnegOut 0 (by rw [h]; decide)
    have s3 := hnegOut 3 (by rw [h]; decide)
    have s4 := hposMem 4 (by rw [h]; decide)
    rw [c0] at s0; rw [c3] at s3; rw [c4] at s4
    nlinarith [mul_pos s4 (neg_pos.mpr s3),
      mul_nonneg (by linarith : (0:ℝ) ≤ scale * (A * B))
        (mul_nonneg hscale (sq_nonneg (A + B + Cz)))]
  -- {1, 3, 4}: product 1 positive, products 0 and 2 negative
  · exfalso
    have s0 := hnegOut 0 (by rw [h]; decide)
    have s1 := hposMem 1 (by rw [h]; decide)
    have s2 := hnegOut 2 (by rw [h]; decide)
    rw [c0] at s0; rw [c1] at s1; rw [c2] at s2
    nlinarith [mul_pos (by linarith : (0:ℝ) < scale * (A * B))
        (by linarith : (0:ℝ) < scale * (B * Cz)),
      mul_nonneg (by linarith : (0:ℝ) ≤ -(scale * (A * Cz)))
        (mul_nonneg hscale (sq_nonneg B))]
  -- {1, 4, 5}: product 1 positive, products 0 and 2 negative
  · exfalso
    have s0 := hnegOut 0 (by rw [h]; decide)
    have s1 := hposMem 1 (by rw [h]; decide)
    have s2 := hnegOut 2 (by rw [h]; decide)
    rw [c0] at s0; rw [c1] at s1; rw [c2] at s2
    nlinarith [mul_pos (by linarith : (0:ℝ) < scale * (A * B))
        (by linarith : (0:ℝ) < scale * (B * Cz)),
      mul_nonneg (by linarith : (0:ℝ) ≤ -(scale * (A * Cz)))
        (mul_nonneg hscale (sq_nonneg B))]
  -- {2, 3, 4}: product 2 positive, products 0 and 1 negative
  · exfalso
    have s0 := hnegOut 0 (by rw [h]; decide)
    have s1 := hnegOut 1 (by rw [h]; decide)
    have s2 := hposMem 2 (by rw [h]; decide)
    rw [c0] at s0; rw [c1] at s1; rw [c2] at s2
    nlinarith [mul_pos (by linarith : (0:ℝ) < scale * (A * B))
        (by linarith : (0:ℝ) < scale * (A * Cz)),
      mul_nonneg (by linarith : (0:ℝ) ≤ -(scale * (B * Cz)))
        (mul_nonneg hscale (sq_nonneg A))]
  -- {2, 3, 5}: product 2 positive, products 0 and 1 negative
  · exfalso
    have s0 := hnegOut 0 (by rw [h]; decide)
    have s1 := hnegOut 1 (by rw [h]; decide)
    have s2 := hposMem 2 (by rw [h]; decide)
    rw [c0] at s0; rw [c1] at s1; rw [c2] at s2
    nlinarith [mul_pos (by linarith : (0:ℝ) < scale * (A * B))
        (by linarith : (0:ℝ) < scale * (A * Cz)),
      mul_nonneg (by linarith : (0:ℝ) ≤ -(scale * (B * Cz)))
        (mul_nonneg hscale (sq_nonneg A))]

/-- **The relay.**  The corank-two wall is empty over the twelve path trees. -/
theorem kFourCorankTwo_not_path (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} (hsel : selected ∈ kFourSpanningTreeList)
    (hnotStar : selected ∉ kFourStarList)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosSemidef) :
    ¬ KFourTreeGapCorankTwoData point selected :=
  fun hdata => hnotStar (kFourCorankTwo_tree_mem_starList point hsel hpsd hdata)

/-- The corank branch of the gap residual always carries a vertex star. -/
theorem kFourWeakTreeGapCorankResidual_refine_star (point : DirectionChartPoint 6)
    (hres : KFourWeakTreeGapCorankResidual point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
      KFourTreeWindowData point tree ∧
      (KFourTreeWindowPivotWallData point tree ∨
        (KFourTreeGapCorankTwoData point tree ∧ tree ∈ kFourStarList)) := by
  obtain ⟨tree, htree, hweak, hwindow, hpivot | hcorank⟩ := hres
  · exact ⟨tree, htree, hweak, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hweak, hwindow, Or.inr
      ⟨hcorank, kFourCorankTwo_tree_mem_starList point htree hweak hcorank⟩⟩

end Gtz

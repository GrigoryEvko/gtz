import Gtz.Reduction.KFourTreeAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-
# P4: the K4 det floor -- `det W <= (tr W / 3)^3 <= 8/27`, hence
# `max_T det(B^{-1} S_T) >= 27/8`

Mechanization of the matroid lane's rung-11 law P4 (one-line theorem,
the M(K4) matroid-lane ledger) in its AM-GM form: on the weight simplex
the determinant of the reduced K4 weight Laplacian is at most `8/27` --
Hadamard's diagonal bound plus the cubic AM-GM on the trace, whose value
is `1 + (w3 + w4 + w5) <= 2` -- and therefore, by the matrix-tree
expansion `det B = sum_T (prod_T y)(prod_T w) <= (max_T prod_T y) det W`,
some spanning tree has `det(B^{-1} S_T) = (prod_T y)/det B >= 27/8`.

The campaign's sharp constant is `2/27` (log-concavity, rung 9 F1); this
file delivers the elementary `8/27` chain exactly as queued, which already
yields the floor `27/8` used by the rung-8 det-trace sketch.
-/

namespace Gtz

open Matrix

/-! ## The cubic AM-GM and the Hadamard-shape expansion -/

/-- Cubic AM-GM: `27 abc <= (a + b + c)^3` for nonnegative reals.  The
difference is `(a+b+c) * ((a-b)^2 + (b-c)^2 + (a-c)^2) / 2` plus
`3 * (a (b-c)^2 + b (a-c)^2 + c (a-b)^2)`, all nonnegative. -/
theorem twentySeven_mul_product_le_cube_sum (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
  nlinarith [mul_nonneg ha (sq_nonneg (b - c)), mul_nonneg hb (sq_nonneg (a - c)),
    mul_nonneg hc (sq_nonneg (a - b)),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (a - b)),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (b - c)),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (a - c))]

/-- The spanning-tree sum in Hadamard shape: diagonal product of the
reduced Laplacian minus four manifestly nonnegative correction terms. -/
theorem kFourSpanningTreeSum_eq_hadamardForm (weight : Fin 6 → ℝ) :
    kFourSpanningTreeSum weight
      = (weight 0 + weight 3 + weight 4) * (weight 1 + weight 3 + weight 5)
          * (weight 2 + weight 4 + weight 5)
        - (weight 0 + weight 3 + weight 4) * weight 5 ^ 2
        - (weight 1 + weight 3 + weight 5) * weight 4 ^ 2
        - (weight 2 + weight 4 + weight 5) * weight 3 ^ 2
        - 2 * (weight 3 * weight 4 * weight 5) := by
  simp only [kFourSpanningTreeSum, k4TreeTriples, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, kFourTreeWeightProduct]
  ring

/-- Hadamard's bound at the K4 Laplacian: the spanning-tree sum is at most
the diagonal product, for nonnegative weights. -/
theorem kFourSpanningTreeSum_le_diagonalProduct (weight : Fin 6 → ℝ)
    (hw : ∀ edge, 0 ≤ weight edge) :
    kFourSpanningTreeSum weight
      ≤ (weight 0 + weight 3 + weight 4) * (weight 1 + weight 3 + weight 5)
          * (weight 2 + weight 4 + weight 5) := by
  rw [kFourSpanningTreeSum_eq_hadamardForm]
  have hfirst : 0 ≤ (weight 0 + weight 3 + weight 4) * weight 5 ^ 2 :=
    mul_nonneg (by linarith [hw 0, hw 3, hw 4]) (sq_nonneg _)
  have hsecond : 0 ≤ (weight 1 + weight 3 + weight 5) * weight 4 ^ 2 :=
    mul_nonneg (by linarith [hw 1, hw 3, hw 5]) (sq_nonneg _)
  have hthird : 0 ≤ (weight 2 + weight 4 + weight 5) * weight 3 ^ 2 :=
    mul_nonneg (by linarith [hw 2, hw 4, hw 5]) (sq_nonneg _)
  have hfourth : 0 ≤ weight 3 * weight 4 * weight 5 :=
    mul_nonneg (mul_nonneg (hw 3) (hw 4)) (hw 5)
  linarith

/-- **P4, first inequality**: `det W <= (tr W / 3)^3` for the K4 weight
Laplacian with nonnegative weights -- Hadamard plus cubic AM-GM, no
spectral theory. -/
theorem det_kFourWeightLaplacian_le_cube_third_trace (weight : Fin 6 → ℝ)
    (hw : ∀ edge, 0 ≤ weight edge) :
    (kFourWeightLaplacian weight).det
      ≤ ((kFourWeightLaplacian weight).trace / 3) ^ 3 := by
  rw [det_kFourWeightLaplacian_eq_spanningTreeSum, Matrix.trace_fin_three,
    kFourWeightLaplacian_zero_zero, kFourWeightLaplacian_one_one,
    kFourWeightLaplacian_two_two]
  have hdiag := kFourSpanningTreeSum_le_diagonalProduct weight hw
  have hfirst : (0 : ℝ) ≤ weight 0 + weight 3 + weight 4 := by
    linarith [hw 0, hw 3, hw 4]
  have hsecond : (0 : ℝ) ≤ weight 1 + weight 3 + weight 5 := by
    linarith [hw 1, hw 3, hw 5]
  have hthird : (0 : ℝ) ≤ weight 2 + weight 4 + weight 5 := by
    linarith [hw 2, hw 4, hw 5]
  have hamgm := twentySeven_mul_product_le_cube_sum _ _ _ hfirst hsecond hthird
  have hcube : ((weight 0 + weight 3 + weight 4 + (weight 1 + weight 3 + weight 5)
      + (weight 2 + weight 4 + weight 5)) / 3) ^ 3
      = (weight 0 + weight 3 + weight 4 + (weight 1 + weight 3 + weight 5)
          + (weight 2 + weight 4 + weight 5)) ^ 3 / 27 := by ring
  rw [hcube]
  linarith

/-- **P4, the simplex cap**: on the weight simplex the spanning-tree sum
(equal to `det W` by matrix-tree) is at most `8/27`: the Laplacian trace
is `1 + (w3 + w4 + w5) <= 2`, so the AM-GM cube is at most `(2/3)^3`. -/
theorem kFourSpanningTreeSum_le_eightTwentySevenths (weight : Fin 6 → ℝ)
    (hw : ∀ edge, 0 ≤ weight edge) (hsum : ∑ edge, weight edge = 1) :
    kFourSpanningTreeSum weight ≤ 8 / 27 := by
  have hsix : weight 0 + weight 1 + weight 2 + weight 3 + weight 4
      + weight 5 = 1 := by
    simpa [Fin.sum_univ_six] using hsum
  have hdiag := kFourSpanningTreeSum_le_diagonalProduct weight hw
  have hfirst : (0 : ℝ) ≤ weight 0 + weight 3 + weight 4 := by
    linarith [hw 0, hw 3, hw 4]
  have hsecond : (0 : ℝ) ≤ weight 1 + weight 3 + weight 5 := by
    linarith [hw 1, hw 3, hw 5]
  have hthird : (0 : ℝ) ≤ weight 2 + weight 4 + weight 5 := by
    linarith [hw 2, hw 4, hw 5]
  have hamgm := twentySeven_mul_product_le_cube_sum _ _ _ hfirst hsecond hthird
  have htrace : weight 0 + weight 3 + weight 4 + (weight 1 + weight 3 + weight 5)
      + (weight 2 + weight 4 + weight 5) ≤ 2 := by
    linarith [hw 0, hw 1, hw 2]
  have htraceNonneg : (0 : ℝ) ≤ weight 0 + weight 3 + weight 4
      + (weight 1 + weight 3 + weight 5) + (weight 2 + weight 4 + weight 5) := by
    linarith
  have hcubeCap : (weight 0 + weight 3 + weight 4 + (weight 1 + weight 3 + weight 5)
      + (weight 2 + weight 4 + weight 5)) ^ 3 ≤ 8 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - (weight 0 + weight 3 + weight 4
        + (weight 1 + weight 3 + weight 5) + (weight 2 + weight 4 + weight 5)))
      (by nlinarith [sq_nonneg (weight 0 + weight 3 + weight 4
          + (weight 1 + weight 3 + weight 5) + (weight 2 + weight 4 + weight 5) + 1)] :
        (0 : ℝ) ≤ (weight 0 + weight 3 + weight 4 + (weight 1 + weight 3 + weight 5)
          + (weight 2 + weight 4 + weight 5)) ^ 2
          + 2 * (weight 0 + weight 3 + weight 4 + (weight 1 + weight 3 + weight 5)
            + (weight 2 + weight 4 + weight 5)) + 4)]
  linarith

/-- `det W <= 8/27` in Laplacian form. -/
theorem det_kFourWeightLaplacian_le_eightTwentySevenths (weight : Fin 6 → ℝ)
    (hw : ∀ edge, 0 ≤ weight edge) (hsum : ∑ edge, weight edge = 1) :
    (kFourWeightLaplacian weight).det ≤ 8 / 27 := by
  rw [det_kFourWeightLaplacian_eq_spanningTreeSum]
  exact kFourSpanningTreeSum_le_eightTwentySevenths weight hw hsum

/-! ## The det floor -/

/-- The mass tree sum factors through conductance and weight tree
products: `det B = sum_T (prod_T y)(prod_T w)` -- the rung-11 P4
expansion. -/
theorem kFourSpanningTreeSum_mass_expansion (conductance weight : Fin 6 → ℝ) :
    kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
      = (k4TreeTriples.map fun tree =>
          kFourTreeWeightProduct conductance tree
            * kFourTreeWeightProduct weight tree).sum := by
  simp only [kFourSpanningTreeSum, k4TreeTriples, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, kFourTreeWeightProduct]
  ring

/-- **P4, the det floor (division-free form).**  For positive conductances
and positive simplex weights, some spanning tree's conductance product
is at least `27/8` times the mass tree sum `det B`.  Scalar reading:
`max_T det(B^{-1} S_T) = max_T (prod_T y)/det B >= 27/8`. -/
theorem exists_tree_product_ge_twentySevenEighths_mul_detB
    (conductance weight : Fin 6 → ℝ)
    (hcond : ∀ edge, 0 < conductance edge) (hw : ∀ edge, 0 < weight edge)
    (hsum : ∑ edge, weight edge = 1) :
    ∃ tree ∈ k4TreeTriples,
      27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
        ≤ kFourTreeWeightProduct conductance tree := by
  by_contra hcon
  push Not at hcon
  have hdetPos : 0 < kFourSpanningTreeSum
      (fun edge => conductance edge * weight edge) :=
    kFourSpanningTreeSum_pos _ fun edge => mul_pos (hcond edge) (hw edge)
  have hcap := kFourSpanningTreeSum_le_eightTwentySevenths weight
    (fun edge => (hw edge).le) hsum
  have hscaledBound : ∀ tree ∈ k4TreeTriples,
      kFourTreeWeightProduct conductance tree * kFourTreeWeightProduct weight tree
        < 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
            * kFourTreeWeightProduct weight tree :=
    fun tree htree => mul_lt_mul_of_pos_right (hcon tree htree)
      (kFourTreeWeightProduct_pos weight hw tree)
  have hmassExpand : kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
      = kFourTreeWeightProduct conductance (0,1,2) * kFourTreeWeightProduct weight (0,1,2)
        + kFourTreeWeightProduct conductance (0,1,4) * kFourTreeWeightProduct weight (0,1,4)
        + kFourTreeWeightProduct conductance (0,1,5) * kFourTreeWeightProduct weight (0,1,5)
        + kFourTreeWeightProduct conductance (0,2,3) * kFourTreeWeightProduct weight (0,2,3)
        + kFourTreeWeightProduct conductance (0,2,5) * kFourTreeWeightProduct weight (0,2,5)
        + kFourTreeWeightProduct conductance (0,3,4) * kFourTreeWeightProduct weight (0,3,4)
        + kFourTreeWeightProduct conductance (0,3,5) * kFourTreeWeightProduct weight (0,3,5)
        + kFourTreeWeightProduct conductance (0,4,5) * kFourTreeWeightProduct weight (0,4,5)
        + kFourTreeWeightProduct conductance (1,2,3) * kFourTreeWeightProduct weight (1,2,3)
        + kFourTreeWeightProduct conductance (1,2,4) * kFourTreeWeightProduct weight (1,2,4)
        + kFourTreeWeightProduct conductance (1,3,4) * kFourTreeWeightProduct weight (1,3,4)
        + kFourTreeWeightProduct conductance (1,3,5) * kFourTreeWeightProduct weight (1,3,5)
        + kFourTreeWeightProduct conductance (1,4,5) * kFourTreeWeightProduct weight (1,4,5)
        + kFourTreeWeightProduct conductance (2,3,4) * kFourTreeWeightProduct weight (2,3,4)
        + kFourTreeWeightProduct conductance (2,3,5) * kFourTreeWeightProduct weight (2,3,5)
        + kFourTreeWeightProduct conductance (2,4,5) * kFourTreeWeightProduct weight (2,4,5) := by
    simp only [kFourSpanningTreeSum, k4TreeTriples, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, kFourTreeWeightProduct]
    ring
  have hweightExpand : kFourSpanningTreeSum weight
      = kFourTreeWeightProduct weight (0,1,2) + kFourTreeWeightProduct weight (0,1,4)
        + kFourTreeWeightProduct weight (0,1,5) + kFourTreeWeightProduct weight (0,2,3)
        + kFourTreeWeightProduct weight (0,2,5) + kFourTreeWeightProduct weight (0,3,4)
        + kFourTreeWeightProduct weight (0,3,5) + kFourTreeWeightProduct weight (0,4,5)
        + kFourTreeWeightProduct weight (1,2,3) + kFourTreeWeightProduct weight (1,2,4)
        + kFourTreeWeightProduct weight (1,3,4) + kFourTreeWeightProduct weight (1,3,5)
        + kFourTreeWeightProduct weight (1,4,5) + kFourTreeWeightProduct weight (2,3,4)
        + kFourTreeWeightProduct weight (2,3,5) + kFourTreeWeightProduct weight (2,4,5) := by
    simp only [kFourSpanningTreeSum, k4TreeTriples, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    ring
  have hproductExpand : 27 / 8
        * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
        * kFourSpanningTreeSum weight
      = 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (0,1,2)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (0,1,4)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (0,1,5)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (0,2,3)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (0,2,5)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (0,3,4)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (0,3,5)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (0,4,5)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (1,2,3)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (1,2,4)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (1,3,4)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (1,3,5)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (1,4,5)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (2,3,4)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (2,3,5)
        + 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourTreeWeightProduct weight (2,4,5) := by
    rw [hweightExpand]
    ring
  have hlt : kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
      < 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * kFourSpanningTreeSum weight := by
    rw [hproductExpand]
    linarith [hscaledBound (0, 1, 2) (by decide), hscaledBound (0, 1, 4) (by decide),
      hscaledBound (0, 1, 5) (by decide), hscaledBound (0, 2, 3) (by decide),
      hscaledBound (0, 2, 5) (by decide), hscaledBound (0, 3, 4) (by decide),
      hscaledBound (0, 3, 5) (by decide), hscaledBound (0, 4, 5) (by decide),
      hscaledBound (1, 2, 3) (by decide), hscaledBound (1, 2, 4) (by decide),
      hscaledBound (1, 3, 4) (by decide), hscaledBound (1, 3, 5) (by decide),
      hscaledBound (1, 4, 5) (by decide), hscaledBound (2, 3, 4) (by decide),
      hscaledBound (2, 3, 5) (by decide), hscaledBound (2, 4, 5) (by decide),
      hmassExpand.le, hmassExpand.ge]
  have hshrink : 27 / 8
        * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
        * kFourSpanningTreeSum weight
      ≤ 27 / 8 * kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * (8 / 27) :=
    mul_le_mul_of_nonneg_left hcap (by linarith)
  linarith

/-- The det floor with conductances written as `mass / weight`. -/
theorem exists_tree_massRatioProduct_ge_twentySevenEighths_mul_detB
    (mass weight : Fin 6 → ℝ)
    (hmass : ∀ edge, 0 < mass edge) (hw : ∀ edge, 0 < weight edge)
    (hsum : ∑ edge, weight edge = 1) :
    ∃ tree ∈ k4TreeTriples,
      27 / 8 * kFourSpanningTreeSum mass
        ≤ kFourTreeWeightProduct (fun edge => mass edge / weight edge) tree := by
  have hfun : (fun edge => mass edge / weight edge * weight edge) = mass :=
    funext fun edge => div_mul_cancel₀ (mass edge) (hw edge).ne'
  have hmain := exists_tree_product_ge_twentySevenEighths_mul_detB
    (fun edge => mass edge / weight edge) weight
    (fun edge => div_pos (hmass edge) (hw edge)) hw hsum
  rwa [hfun] at hmain

/-- **P4, ratio form**: some spanning tree has
`(prod_T (m/w)) / det B >= 27/8` -- the scalar value of
`det(B^{-1} S_T)` at that tree. -/
theorem exists_tree_detRatio_ge_twentySevenEighths (mass weight : Fin 6 → ℝ)
    (hmass : ∀ edge, 0 < mass edge) (hw : ∀ edge, 0 < weight edge)
    (hsum : ∑ edge, weight edge = 1) :
    ∃ tree ∈ k4TreeTriples,
      27 / 8 ≤ kFourTreeWeightProduct (fun edge => mass edge / weight edge) tree
          / (kFourWeightLaplacian mass).det := by
  obtain ⟨tree, htree, hbound⟩ :=
    exists_tree_massRatioProduct_ge_twentySevenEighths_mul_detB mass weight
      hmass hw hsum
  refine ⟨tree, htree, ?_⟩
  rw [det_kFourWeightLaplacian_eq_spanningTreeSum,
    le_div_iff₀ (kFourSpanningTreeSum_pos mass hmass)]
  linarith

end Gtz

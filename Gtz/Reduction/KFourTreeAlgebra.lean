import Gtz.Reduction.K4Diagonal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-
# K4 tree algebra: the spanning-tree sum, the reduced Laplacian, and the
# edge companion sums

Shared substrate for the M(K4) det-trace campaign laws (matroid lane,
rungs 8 and 11): the sixteen spanning-tree products, the reduced `3 x 3`
weight Laplacian in the `k4Drop` gauge of `Gtz.Reduction.K4Diagonal`
(vertex 0 grounded, edges `e0=(0,1) e1=(0,2) e2=(0,3) e3=(1,2) e4=(1,3)
e5=(2,3)`), the matrix-tree identity `det L(w) = sum_T prod_T w` as one
`ring` fact, and the per-edge companion sums
`F_c(w) = sum_{T containing c} prod_{T minus c} w` -- the derivative of the
tree sum along one edge weight, and the object the leverage identity
(campaign step alpha) equates with the adjugate pairing.

Every identity here is constraint-free (no simplex hypothesis): the
simplex enters only in the downstream inequality files.
-/

namespace Gtz

open Matrix

/-! ## Tree products and the spanning-tree sum -/

/-- The product of a weight vector over one spanning tree of K4. -/
def kFourTreeWeightProduct (weight : Fin 6 → ℝ)
    (tree : Fin 6 × Fin 6 × Fin 6) : ℝ :=
  weight tree.1 * weight tree.2.1 * weight tree.2.2

/-- The spanning-tree sum of K4: the sum of the sixteen tree weight
products.  By the matrix-tree identity below this IS the determinant of
the reduced weight Laplacian. -/
def kFourSpanningTreeSum (weight : Fin 6 → ℝ) : ℝ :=
  (k4TreeTriples.map (kFourTreeWeightProduct weight)).sum

theorem kFourTreeWeightProduct_pos (weight : Fin 6 → ℝ)
    (hw : ∀ edge, 0 < weight edge) (tree : Fin 6 × Fin 6 × Fin 6) :
    0 < kFourTreeWeightProduct weight tree :=
  mul_pos (mul_pos (hw tree.1) (hw tree.2.1)) (hw tree.2.2)

theorem kFourTreeWeightProduct_nonneg (weight : Fin 6 → ℝ)
    (hw : ∀ edge, 0 ≤ weight edge) (tree : Fin 6 × Fin 6 × Fin 6) :
    0 ≤ kFourTreeWeightProduct weight tree :=
  mul_nonneg (mul_nonneg (hw tree.1) (hw tree.2.1)) (hw tree.2.2)

/-- The spanning-tree sum of a strictly positive weight vector is strictly
positive: it is a sum of sixteen positive tree products. -/
theorem kFourSpanningTreeSum_pos (weight : Fin 6 → ℝ)
    (hw : ∀ edge, 0 < weight edge) :
    0 < kFourSpanningTreeSum weight := by
  have hterm := kFourTreeWeightProduct_pos weight hw
  simp only [kFourSpanningTreeSum, k4TreeTriples, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  linarith [hterm (0, 1, 2), hterm (0, 1, 4), hterm (0, 1, 5),
    hterm (0, 2, 3), hterm (0, 2, 5), hterm (0, 3, 4), hterm (0, 3, 5),
    hterm (0, 4, 5), hterm (1, 2, 3), hterm (1, 2, 4), hterm (1, 3, 4),
    hterm (1, 3, 5), hterm (1, 4, 5), hterm (2, 3, 4), hterm (2, 3, 5),
    hterm (2, 4, 5)]

/-! ## The reduced weight Laplacian in the `k4Drop` gauge -/

/-- Entries of the reduced K4 weight Laplacian, vertex 0 grounded: the
Gram matrix of the six `k4Drop` covectors weighted by `weight`. -/
def kFourWeightLaplacianEntry (weight : Fin 6 → ℝ) : Fin 3 → Fin 3 → ℝ
  | 0, 0 => weight 0 + weight 3 + weight 4
  | 0, 1 => -weight 3
  | 0, 2 => -weight 4
  | 1, 0 => -weight 3
  | 1, 1 => weight 1 + weight 3 + weight 5
  | 1, 2 => -weight 5
  | 2, 0 => -weight 4
  | 2, 1 => -weight 5
  | 2, 2 => weight 2 + weight 4 + weight 5

/-- The reduced `3 x 3` weight Laplacian of K4 in the `k4Drop` gauge. -/
def kFourWeightLaplacian (weight : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (kFourWeightLaplacianEntry weight)

theorem kFourWeightLaplacian_zero_zero (weight : Fin 6 → ℝ) :
    kFourWeightLaplacian weight 0 0 = weight 0 + weight 3 + weight 4 := rfl
theorem kFourWeightLaplacian_zero_one (weight : Fin 6 → ℝ) :
    kFourWeightLaplacian weight 0 1 = -weight 3 := rfl
theorem kFourWeightLaplacian_zero_two (weight : Fin 6 → ℝ) :
    kFourWeightLaplacian weight 0 2 = -weight 4 := rfl
theorem kFourWeightLaplacian_one_zero (weight : Fin 6 → ℝ) :
    kFourWeightLaplacian weight 1 0 = -weight 3 := rfl
theorem kFourWeightLaplacian_one_one (weight : Fin 6 → ℝ) :
    kFourWeightLaplacian weight 1 1 = weight 1 + weight 3 + weight 5 := rfl
theorem kFourWeightLaplacian_one_two (weight : Fin 6 → ℝ) :
    kFourWeightLaplacian weight 1 2 = -weight 5 := rfl
theorem kFourWeightLaplacian_two_zero (weight : Fin 6 → ℝ) :
    kFourWeightLaplacian weight 2 0 = -weight 4 := rfl
theorem kFourWeightLaplacian_two_one (weight : Fin 6 → ℝ) :
    kFourWeightLaplacian weight 2 1 = -weight 5 := rfl
theorem kFourWeightLaplacian_two_two (weight : Fin 6 → ℝ) :
    kFourWeightLaplacian weight 2 2 = weight 2 + weight 4 + weight 5 := rfl

/-- The Laplacian quadratic form is the weighted drop energy: this pins
`kFourWeightLaplacian` to the `k4Drop` gauge of the K4 diagonal bricks. -/
theorem dotProduct_kFourWeightLaplacian_mulVec (weight : Fin 6 → ℝ)
    (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (kFourWeightLaplacian weight).mulVec probe
      = ∑ edge, weight edge * k4Drop probe edge ^ 2 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_six,
    kFourWeightLaplacian_zero_zero, kFourWeightLaplacian_zero_one,
    kFourWeightLaplacian_zero_two, kFourWeightLaplacian_one_zero,
    kFourWeightLaplacian_one_one, kFourWeightLaplacian_one_two,
    kFourWeightLaplacian_two_zero, kFourWeightLaplacian_two_one,
    kFourWeightLaplacian_two_two, k4Drop_zero, k4Drop_one, k4Drop_two,
    k4Drop_three, k4Drop_four, k4Drop_five]
  ring

/-- **Matrix-tree at K4**, constraint-free: the determinant of the reduced
weight Laplacian is the sum of the sixteen spanning-tree weight products.
One `ring` closes it -- total unimodularity at the 3 x 3 instance. -/
theorem det_kFourWeightLaplacian_eq_spanningTreeSum (weight : Fin 6 → ℝ) :
    (kFourWeightLaplacian weight).det = kFourSpanningTreeSum weight := by
  simp only [kFourSpanningTreeSum, k4TreeTriples, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, kFourTreeWeightProduct,
    Matrix.det_fin_three, kFourWeightLaplacian_zero_zero,
    kFourWeightLaplacian_zero_one, kFourWeightLaplacian_zero_two,
    kFourWeightLaplacian_one_zero, kFourWeightLaplacian_one_one,
    kFourWeightLaplacian_one_two, kFourWeightLaplacian_two_zero,
    kFourWeightLaplacian_two_one, kFourWeightLaplacian_two_two]
  ring

/-! ## Edge companion sums -/

/-- The companion sum of one K4 edge: the sum, over the eight spanning
trees through that edge, of the product of the OTHER two edge weights --
`F_c(w) = sum_{T containing c} prod_{T minus c} w`, the object the
det-trace law's leverage identity pairs with the adjugate.  Stated by
explicit expansion; `weight_mul_kFourEdgeCompanionSum` validates it
against the tree list. -/
def kFourEdgeCompanionSum (weight : Fin 6 → ℝ) : Fin 6 → ℝ
  | 0 => weight 1 * weight 2 + weight 1 * weight 4 + weight 1 * weight 5
      + weight 2 * weight 3 + weight 2 * weight 5 + weight 3 * weight 4
      + weight 3 * weight 5 + weight 4 * weight 5
  | 1 => weight 0 * weight 2 + weight 0 * weight 4 + weight 0 * weight 5
      + weight 2 * weight 3 + weight 2 * weight 4 + weight 3 * weight 4
      + weight 3 * weight 5 + weight 4 * weight 5
  | 2 => weight 0 * weight 1 + weight 0 * weight 3 + weight 0 * weight 5
      + weight 1 * weight 3 + weight 1 * weight 4 + weight 3 * weight 4
      + weight 3 * weight 5 + weight 4 * weight 5
  | 3 => weight 0 * weight 2 + weight 0 * weight 4 + weight 0 * weight 5
      + weight 1 * weight 2 + weight 1 * weight 4 + weight 1 * weight 5
      + weight 2 * weight 4 + weight 2 * weight 5
  | 4 => weight 0 * weight 1 + weight 0 * weight 3 + weight 0 * weight 5
      + weight 1 * weight 2 + weight 1 * weight 3 + weight 1 * weight 5
      + weight 2 * weight 3 + weight 2 * weight 5
  | 5 => weight 0 * weight 1 + weight 0 * weight 2 + weight 0 * weight 3
      + weight 0 * weight 4 + weight 1 * weight 3 + weight 1 * weight 4
      + weight 2 * weight 3 + weight 2 * weight 4

/-- The spanning trees of K4 through one edge, read off the tree list. -/
def kFourTreesThroughEdge (edge : Fin 6) : List (Fin 6 × Fin 6 × Fin 6) :=
  k4TreeTriples.filter fun tree =>
    decide (tree.1 = edge ∨ tree.2.1 = edge ∨ tree.2.2 = edge)

theorem kFourTreesThroughEdge_zero : kFourTreesThroughEdge 0
    = [(0,1,2), (0,1,4), (0,1,5), (0,2,3), (0,2,5), (0,3,4), (0,3,5),
       (0,4,5)] := by decide
theorem kFourTreesThroughEdge_one : kFourTreesThroughEdge 1
    = [(0,1,2), (0,1,4), (0,1,5), (1,2,3), (1,2,4), (1,3,4), (1,3,5),
       (1,4,5)] := by decide
theorem kFourTreesThroughEdge_two : kFourTreesThroughEdge 2
    = [(0,1,2), (0,2,3), (0,2,5), (1,2,3), (1,2,4), (2,3,4), (2,3,5),
       (2,4,5)] := by decide
theorem kFourTreesThroughEdge_three : kFourTreesThroughEdge 3
    = [(0,2,3), (0,3,4), (0,3,5), (1,2,3), (1,3,4), (1,3,5), (2,3,4),
       (2,3,5)] := by decide
theorem kFourTreesThroughEdge_four : kFourTreesThroughEdge 4
    = [(0,1,4), (0,3,4), (0,4,5), (1,2,4), (1,3,4), (1,4,5), (2,3,4),
       (2,4,5)] := by decide
theorem kFourTreesThroughEdge_five : kFourTreesThroughEdge 5
    = [(0,1,5), (0,2,5), (0,3,5), (0,4,5), (1,3,5), (1,4,5), (2,3,5),
       (2,4,5)] := by decide

/-- **Validation of the companion sums against the tree list**: for every
edge, `w_c * F_c(w)` is the sum of the tree products over exactly the
spanning trees through that edge.  This is the bookkeeping half of the
campaign's leverage identity (step alpha). -/
theorem weight_mul_kFourEdgeCompanionSum (weight : Fin 6 → ℝ) :
    ∀ edge : Fin 6, weight edge * kFourEdgeCompanionSum weight edge
      = ((kFourTreesThroughEdge edge).map
          (kFourTreeWeightProduct weight)).sum
  | 0 => by
      rw [kFourTreesThroughEdge_zero]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        kFourTreeWeightProduct, kFourEdgeCompanionSum]
      ring
  | 1 => by
      rw [kFourTreesThroughEdge_one]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        kFourTreeWeightProduct, kFourEdgeCompanionSum]
      ring
  | 2 => by
      rw [kFourTreesThroughEdge_two]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        kFourTreeWeightProduct, kFourEdgeCompanionSum]
      ring
  | 3 => by
      rw [kFourTreesThroughEdge_three]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        kFourTreeWeightProduct, kFourEdgeCompanionSum]
      ring
  | 4 => by
      rw [kFourTreesThroughEdge_four]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        kFourTreeWeightProduct, kFourEdgeCompanionSum]
      ring
  | 5 => by
      rw [kFourTreesThroughEdge_five]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        kFourTreeWeightProduct, kFourEdgeCompanionSum]
      ring

/-- The companion sum of a nonnegative weight vector is nonnegative. -/
theorem kFourEdgeCompanionSum_nonneg (weight : Fin 6 → ℝ)
    (hw : ∀ edge, 0 ≤ weight edge) (edge : Fin 6) :
    0 ≤ kFourEdgeCompanionSum weight edge := by
  fin_cases edge <;>
    · simp only [kFourEdgeCompanionSum]
      have h01 := mul_nonneg (hw 0) (hw 1)
      have h02 := mul_nonneg (hw 0) (hw 2)
      have h03 := mul_nonneg (hw 0) (hw 3)
      have h04 := mul_nonneg (hw 0) (hw 4)
      have h05 := mul_nonneg (hw 0) (hw 5)
      have h12 := mul_nonneg (hw 1) (hw 2)
      have h13 := mul_nonneg (hw 1) (hw 3)
      have h14 := mul_nonneg (hw 1) (hw 4)
      have h15 := mul_nonneg (hw 1) (hw 5)
      have h23 := mul_nonneg (hw 2) (hw 3)
      have h24 := mul_nonneg (hw 2) (hw 4)
      have h25 := mul_nonneg (hw 2) (hw 5)
      have h34 := mul_nonneg (hw 3) (hw 4)
      have h35 := mul_nonneg (hw 3) (hw 5)
      have h45 := mul_nonneg (hw 4) (hw 5)
      linarith

/-- The tree quadratic `Q(T) = F_{c1} + F_{c2} + F_{c3}` of the det-trace
law: the sum of the companion sums of the three tree edges.  The SOS
identities of the campaign's step gamma show `Q(T) < 1` strictly on the
open weight simplex. -/
def kFourTreeQuadratic (weight : Fin 6 → ℝ)
    (tree : Fin 6 × Fin 6 × Fin 6) : ℝ :=
  kFourEdgeCompanionSum weight tree.1 + kFourEdgeCompanionSum weight tree.2.1
    + kFourEdgeCompanionSum weight tree.2.2

/-- The trace numerator `e1(T) * det B` of the det-trace law: with masses
`m = conductance * weight`, this is
`sum_{c in T} y_c * F_c(m) = trace(B^{-1} S_T) * det B` -- the closed
leverage form of the campaign's step alpha. -/
def kFourTraceNumerator (conductance weight : Fin 6 → ℝ)
    (tree : Fin 6 × Fin 6 × Fin 6) : ℝ :=
  conductance tree.1
      * kFourEdgeCompanionSum (fun edge => conductance edge * weight edge)
          tree.1
    + conductance tree.2.1
      * kFourEdgeCompanionSum (fun edge => conductance edge * weight edge)
          tree.2.1
    + conductance tree.2.2
      * kFourEdgeCompanionSum (fun edge => conductance edge * weight edge)
          tree.2.2

end Gtz

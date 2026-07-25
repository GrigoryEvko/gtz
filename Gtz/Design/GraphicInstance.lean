/-
# The graphic instance: weighted GTZ read on graphs and spanning trees

GTZ's weighted form asks for a `k`-subset of a weighted design whose atom sum
dominates the identity.  Restricting the design to come from a **connected
weighted multigraph** — atoms indexed by edges, rank = #vertices − 1, the
Parseval identity supplied by the graph Laplacian — turns the question into

> every connected weighted multigraph has a spanning tree `T` with
> `Σ_{e ∈ T} (w_e / t_e) b_e b_eᵀ  ⪰  Σ_{e ∈ E} w_e b_e b_eᵀ`,

with `b_e` the reduced incidence row of the edge, `w` the conductances and `t`
any probability weight on edges.  At the uniform weight `t ≡ 1/#E` the
inequality reads `#E · L_T ⪰ L` — the graphic matroid instance of GTZ at
`(n, k) = (#edges, #vertices − 1)`.

## What this file establishes

* `graphicDesign` — a genuine `WeightedDesign` from graph data.  Parseval is
  proved from the whitening of the Laplacian; nothing is assumed about the
  graph beyond ground-connectivity.
* `graphicDesign_dominates_iff` — **the dictionary**: `Dominates` on an edge
  subset is *exactly* the Loewner inequality above, with the whitening
  eliminated.  No square roots, no pseudo-inverses, no coordinate choice
  survives in the statement.
* `posDef_laplacianOn_iff_isGroundConnected` — the Laplacian of an edge subset
  is positive definite **iff** that subset connects every vertex to the ground
  vertex.  This is the spanning half of the graphic matroid, proved from the
  potential-difference (Dirichlet) form.
* `isSpanningTree_of_dominates`, `not_dominates_of_not_isGroundConnected`,
  `eq_zero_of_orthogonal_to_dominating` — every dominating subset of the right
  size is a spanning tree, both in the graph sense and in the linear-span
  (matroid) sense.  So the selection problem really is a spanning-tree problem.
* `cycleGraphData_dominates` / `cycleGraphData_not_posDef` — the `(k+1)`-cycle
  at unit conductance and uniform weight dominates on the path with margin
  **exactly zero**, proved here by telescoping Cauchy–Schwarz.  So the graphic
  boundary is *attained*: no strictly-positive certificate exists there either.
  This is the same mathematical content as `Gtz.corner_fiber_dominates`, but
  the identification (that the cycle's whitened atoms satisfy
  `HasExactCorner`, i.e. leverage `k` and pairwise dot `−1`) is **not** proved
  here — `Corner/` sits above `Design/` in the layer order.
* `completeFourData_dominates_strictly` — `K4`, the first non-series-parallel
  graph, at unit conductance and uniform weight: the star at the ground
  dominates with a *positive definite* gap, certified by the explicit
  sum of squares `2(u₀²+u₁²+u₂²) + (u₀+u₁+u₂)²`.  Slack where the cycle has
  none, at exactly the campaign's binding size `(6,3)`.
* `dominates_of_deleted_dominates` — light-edge deletion in Loewner form; the
  hypothesis `conductance e · b_e b_eᵀ ⪯ weight e · L` is the graph reading of
  the campaign's `leverage ≤ 1`.
* `laplacianOn_form_erase_of_orthogonal` — contraction as restriction to the
  subspace `b_e ⊥ u`.

## What this file does NOT establish

Graphic designs are a positive-codimension subfamily of all designs, so
`graphicGtz_of_gtzWeighted` runs one way only: a graphic counterexample would
refute GTZ outright, but a proof of `GraphicGtz` is **not** a proof of
`GtzWeighted`.  Treating it as one is a category error.

`IsSpanningTree` here is "ground-connected and of cardinality `vertexRank`".
That is the connected-plus-count characterisation of a spanning tree; its
equivalence with "connected and acyclic" is the standard counting theorem and
is **not** formalized here (no cycle datatype is introduced).

Contraction is stated only as the form identity on `b_e ⊥ u`.  The
rank-reducing reindexing of the vertex set — the step an induction on
`vertexRank` would actually consume — is not carried out, and neither is the
graphic/cographic transfer, which needs `Gtz.weighted_naimark_duality` from the
Reduction layer and therefore cannot live in `Design/`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {edgeCount vertexRank : ℕ}

/-! ## The graph substrate: reduced incidence and grounded potentials -/

/-- A finite multigraph on `vertexRank + 1` vertices with `edgeCount` edges,
given by its two endpoint maps.  The vertex `Fin.last vertexRank` is the
distinguished **ground** vertex, the one that reduced incidence coordinates
delete; loops and parallel edges are allowed. -/
structure MultigraphOnGround (edgeCount vertexRank : ℕ) where
  /-- The tail endpoint of each edge. -/
  edgeTail : Fin edgeCount → Fin (vertexRank + 1)
  /-- The head endpoint of each edge. -/
  edgeHead : Fin edgeCount → Fin (vertexRank + 1)

namespace MultigraphOnGround

/-- The reduced incidence row `b_e = chi_tail − chi_head` of an edge, read in
the `vertexRank` non-ground coordinates. -/
def edgeVector (graph : MultigraphOnGround edgeCount vertexRank)
    (edge : Fin edgeCount) : Fin vertexRank → ℝ :=
  fun coord =>
    (if graph.edgeTail edge = coord.castSucc then (1 : ℝ) else 0) -
      (if graph.edgeHead edge = coord.castSucc then (1 : ℝ) else 0)

end MultigraphOnGround

/-- A reduced potential on the non-ground vertices, extended by `0` at the
ground vertex.  Every quadratic form below is a sum of squared differences of
this function. -/
def groundedPotential (reducedPotential : Fin vertexRank → ℝ) :
    Fin (vertexRank + 1) → ℝ :=
  Fin.snoc reducedPotential 0

/-- The grounded potential at a non-ground vertex is the reduced potential. -/
theorem groundedPotential_castSucc (reducedPotential : Fin vertexRank → ℝ)
    (coord : Fin vertexRank) :
    groundedPotential reducedPotential coord.castSucc = reducedPotential coord := by
  rw [groundedPotential, Fin.snoc_castSucc]

/-- The grounded potential vanishes at the ground vertex. -/
theorem groundedPotential_last (reducedPotential : Fin vertexRank → ℝ) :
    groundedPotential reducedPotential (Fin.last vertexRank) = 0 := by
  rw [groundedPotential, Fin.snoc_last]

/-- Selecting one grounded coordinate: the indicator sum against a reduced
potential is the grounded potential at that vertex. -/
theorem sum_indicator_castSucc_mul (vertex : Fin (vertexRank + 1))
    (reducedPotential : Fin vertexRank → ℝ) :
    ∑ coord, (if vertex = coord.castSucc then (1 : ℝ) else 0) * reducedPotential coord
      = groundedPotential reducedPotential vertex := by
  induction vertex using Fin.lastCases with
  | last =>
      rw [groundedPotential, Fin.snoc_last]
      refine Finset.sum_eq_zero fun coord _ => ?_
      rw [if_neg (Fin.castSucc_lt_last coord).ne', zero_mul]
  | cast innerIndex =>
      rw [groundedPotential, Fin.snoc_castSucc]
      rw [Finset.sum_eq_single innerIndex]
      · rw [if_pos rfl, one_mul]
      · intro otherIndex _ hne
        rw [if_neg (fun heq => hne (Fin.castSucc_inj.mp heq).symm), zero_mul]
      · intro hnot
        exact absurd (Finset.mem_univ innerIndex) hnot

/-- **The edge form.**  Pairing an edge vector with a reduced potential gives
the potential drop across the edge. -/
theorem edgeVector_dotProduct (graph : MultigraphOnGround edgeCount vertexRank)
    (edge : Fin edgeCount) (reducedPotential : Fin vertexRank → ℝ) :
    graph.edgeVector edge ⬝ᵥ reducedPotential
      = groundedPotential reducedPotential (graph.edgeTail edge)
        - groundedPotential reducedPotential (graph.edgeHead edge) := by
  simp only [dotProduct, MultigraphOnGround.edgeVector, sub_mul]
  rw [Finset.sum_sub_distrib, sum_indicator_castSucc_mul, sum_indicator_castSucc_mul]

/-! ## Laplacians of edge subsets -/

/-- The weighted reduced Laplacian of an edge subset:
`Σ_{e ∈ edgeSet} conductance e · b_e b_eᵀ`. -/
def laplacianOn (graph : MultigraphOnGround edgeCount vertexRank)
    (conductance : Fin edgeCount → ℝ) (edgeSet : Finset (Fin edgeCount)) :
    Matrix (Fin vertexRank) (Fin vertexRank) ℝ :=
  ∑ edge ∈ edgeSet, conductance edge • atomMatrix (graph.edgeVector edge)

/-- A scaled atom's quadratic form is the scaled square of the pairing. -/
theorem atomMatrix_smul_form (scale : ℝ) (vec reducedPotential : Fin vertexRank → ℝ) :
    reducedPotential ⬝ᵥ ((scale • atomMatrix vec) *ᵥ reducedPotential)
      = scale * (vec ⬝ᵥ reducedPotential) ^ 2 := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
    vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    dotProduct_comm reducedPotential vec]
  ring

/-- Laplacians are symmetric. -/
theorem laplacianOn_transpose (graph : MultigraphOnGround edgeCount vertexRank)
    (conductance : Fin edgeCount → ℝ) (edgeSet : Finset (Fin edgeCount)) :
    (laplacianOn graph conductance edgeSet)ᵀ = laplacianOn graph conductance edgeSet := by
  rw [laplacianOn, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun edge _ => ?_
  rw [Matrix.transpose_smul,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix (graph.edgeVector edge)).1]

/-- **The Dirichlet form.**  The Laplacian's quadratic form is the conductance-
weighted sum of squared potential drops. -/
theorem laplacianOn_form (graph : MultigraphOnGround edgeCount vertexRank)
    (conductance : Fin edgeCount → ℝ) (edgeSet : Finset (Fin edgeCount))
    (reducedPotential : Fin vertexRank → ℝ) :
    reducedPotential ⬝ᵥ (laplacianOn graph conductance edgeSet *ᵥ reducedPotential)
      = ∑ edge ∈ edgeSet, conductance edge *
          (groundedPotential reducedPotential (graph.edgeTail edge)
            - groundedPotential reducedPotential (graph.edgeHead edge)) ^ 2 := by
  rw [laplacianOn, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun edge _ => ?_
  rw [atomMatrix_smul_form, edgeVector_dotProduct]

/-- Laplacians are positive semidefinite whenever the conductances are. -/
theorem posSemidef_laplacianOn (graph : MultigraphOnGround edgeCount vertexRank)
    {conductance : Fin edgeCount → ℝ} (hcond : ∀ edge, 0 ≤ conductance edge)
    (edgeSet : Finset (Fin edgeCount)) :
    (laplacianOn graph conductance edgeSet).PosSemidef := by
  refine Matrix.posSemidef_sum edgeSet fun edge _ => ?_
  exact (posSemidef_atomMatrix (graph.edgeVector edge)).smul (hcond edge)

/-! ## Connectivity, and the spanning half of the graphic matroid -/

/-- Two vertices are adjacent through an edge subset when some edge of the
subset joins them (in either orientation). -/
def IsEdgeAdjacent (graph : MultigraphOnGround edgeCount vertexRank)
    (edgeSet : Finset (Fin edgeCount))
    (leftVertex rightVertex : Fin (vertexRank + 1)) : Prop :=
  ∃ edge ∈ edgeSet,
    (graph.edgeTail edge = leftVertex ∧ graph.edgeHead edge = rightVertex) ∨
      (graph.edgeTail edge = rightVertex ∧ graph.edgeHead edge = leftVertex)

/-- Reachability through an edge subset: the reflexive–transitive closure of
adjacency. -/
def IsEdgeReachable (graph : MultigraphOnGround edgeCount vertexRank)
    (edgeSet : Finset (Fin edgeCount)) :
    Fin (vertexRank + 1) → Fin (vertexRank + 1) → Prop :=
  Relation.ReflTransGen (IsEdgeAdjacent graph edgeSet)

/-- Adjacency is symmetric by construction. -/
theorem isEdgeAdjacent_symm {graph : MultigraphOnGround edgeCount vertexRank}
    {edgeSet : Finset (Fin edgeCount)} {leftVertex rightVertex : Fin (vertexRank + 1)}
    (hadj : IsEdgeAdjacent graph edgeSet leftVertex rightVertex) :
    IsEdgeAdjacent graph edgeSet rightVertex leftVertex := by
  obtain ⟨edge, hmem, hcase⟩ := hadj
  exact ⟨edge, hmem, hcase.symm⟩

/-- Reachability is symmetric: walk the adjacency chain backwards. -/
theorem isEdgeReachable_symm {graph : MultigraphOnGround edgeCount vertexRank}
    {edgeSet : Finset (Fin edgeCount)} {source target : Fin (vertexRank + 1)}
    (hreach : IsEdgeReachable graph edgeSet source target) :
    IsEdgeReachable graph edgeSet target source := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ihead =>
      exact Relation.ReflTransGen.head (isEdgeAdjacent_symm hstep) ihead

/-- An edge of the subset joins its endpoints. -/
theorem isEdgeReachable_endpoints (graph : MultigraphOnGround edgeCount vertexRank)
    {edgeSet : Finset (Fin edgeCount)} {edge : Fin edgeCount} (hmem : edge ∈ edgeSet) :
    IsEdgeReachable graph edgeSet (graph.edgeTail edge) (graph.edgeHead edge) :=
  Relation.ReflTransGen.single ⟨edge, hmem, Or.inl ⟨rfl, rfl⟩⟩

/-- An edge subset **spans** when every vertex is reachable from the ground
vertex.  For a subset of cardinality `vertexRank` this is exactly spanning
connectivity of the corresponding subgraph. -/
def IsGroundConnected (graph : MultigraphOnGround edgeCount vertexRank)
    (edgeSet : Finset (Fin edgeCount)) : Prop :=
  ∀ vertex, IsEdgeReachable graph edgeSet (Fin.last vertexRank) vertex

/-- A **spanning tree** of the multigraph, in the connected-plus-count form:
`vertexRank` edges connecting every vertex to the ground.  (Equivalence with
"connected and acyclic" is the standard counting theorem, not formalized
here.) -/
def IsSpanningTree (graph : MultigraphOnGround edgeCount vertexRank)
    (edgeSet : Finset (Fin edgeCount)) : Prop :=
  IsGroundConnected graph edgeSet ∧ edgeSet.card = vertexRank

/-- A potential that is flat across every edge of the subset is constant along
reachability. -/
theorem groundedPotential_eq_of_reachable
    {graph : MultigraphOnGround edgeCount vertexRank}
    {edgeSet : Finset (Fin edgeCount)} {reducedPotential : Fin vertexRank → ℝ}
    (hflat : ∀ edge ∈ edgeSet,
      groundedPotential reducedPotential (graph.edgeTail edge)
        = groundedPotential reducedPotential (graph.edgeHead edge))
    {source target : Fin (vertexRank + 1)}
    (hreach : IsEdgeReachable graph edgeSet source target) :
    groundedPotential reducedPotential source = groundedPotential reducedPotential target := by
  induction hreach with
  | refl => rfl
  | tail _ hstep ihead =>
      obtain ⟨edge, hmem, hcase⟩ := hstep
      rcases hcase with ⟨htail, hhead⟩ | ⟨htail, hhead⟩
      · rw [ihead, ← htail, hflat edge hmem, hhead]
      · rw [ihead, ← hhead, ← hflat edge hmem, htail]

/-- **Connected ⟹ positive definite.**  If the subset reaches every vertex from
the ground, the Dirichlet form vanishes only at the zero potential. -/
theorem posDef_laplacianOn_of_isGroundConnected
    (graph : MultigraphOnGround edgeCount vertexRank)
    {conductance : Fin edgeCount → ℝ} (hcond : ∀ edge, 0 < conductance edge)
    {edgeSet : Finset (Fin edgeCount)} (hconn : IsGroundConnected graph edgeSet) :
    (laplacianOn graph conductance edgeSet).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (laplacianOn_transpose graph conductance edgeSet),
      fun reducedPotential hne => ?_⟩
  rw [star_trivial, laplacianOn_form]
  have hnn : ∀ edge ∈ edgeSet, 0 ≤ conductance edge *
      (groundedPotential reducedPotential (graph.edgeTail edge)
        - groundedPotential reducedPotential (graph.edgeHead edge)) ^ 2 :=
    fun edge _ => mul_nonneg (hcond edge).le (sq_nonneg _)
  rcases (Finset.sum_nonneg hnn).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp heq.symm
    have hflat : ∀ edge ∈ edgeSet,
        groundedPotential reducedPotential (graph.edgeTail edge)
          = groundedPotential reducedPotential (graph.edgeHead edge) := by
      intro edge hmem
      have hterm := hall edge hmem
      have hsq : (groundedPotential reducedPotential (graph.edgeTail edge)
          - groundedPotential reducedPotential (graph.edgeHead edge)) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hterm with hzero | hzero
        · exact absurd hzero (hcond edge).ne'
        · exact hzero
      have := pow_eq_zero_iff (n := 2) (by omega) |>.mp hsq
      linarith [this]
    refine hne (funext fun coord => ?_)
    have hval := groundedPotential_eq_of_reachable hflat (hconn coord.castSucc)
    rw [groundedPotential_last, groundedPotential_castSucc] at hval
    exact hval.symm

open scoped Classical in
/-- The indicator potential of the reachability component of a base vertex,
read on the non-ground coordinates.  This is the witness that disconnection
kills positive definiteness. -/
noncomputable def componentIndicator (graph : MultigraphOnGround edgeCount vertexRank)
    (edgeSet : Finset (Fin edgeCount)) (baseVertex : Fin (vertexRank + 1)) :
    Fin (vertexRank + 1) → ℝ :=
  fun vertex => if IsEdgeReachable graph edgeSet baseVertex vertex then 1 else 0

/-- The component indicator is `1` inside the component. -/
theorem componentIndicator_of_reachable
    {graph : MultigraphOnGround edgeCount vertexRank}
    {edgeSet : Finset (Fin edgeCount)} {baseVertex vertex : Fin (vertexRank + 1)}
    (hreach : IsEdgeReachable graph edgeSet baseVertex vertex) :
    componentIndicator graph edgeSet baseVertex vertex = 1 := by
  classical
  rw [componentIndicator, if_pos hreach]

/-- The component indicator is `0` outside the component. -/
theorem componentIndicator_of_not_reachable
    {graph : MultigraphOnGround edgeCount vertexRank}
    {edgeSet : Finset (Fin edgeCount)} {baseVertex vertex : Fin (vertexRank + 1)}
    (hreach : ¬ IsEdgeReachable graph edgeSet baseVertex vertex) :
    componentIndicator graph edgeSet baseVertex vertex = 0 := by
  classical
  rw [componentIndicator, if_neg hreach]

/-- **Positive definite ⟹ connected.**  A vertex outside the ground's component
carries the indicator potential, on which the Dirichlet form vanishes. -/
theorem isGroundConnected_of_posDef_laplacianOn
    (graph : MultigraphOnGround edgeCount vertexRank)
    {conductance : Fin edgeCount → ℝ}
    {edgeSet : Finset (Fin edgeCount)}
    (hpd : (laplacianOn graph conductance edgeSet).PosDef) :
    IsGroundConnected graph edgeSet := by
  by_contra hnot
  obtain ⟨badVertex, hbad⟩ := not_forall.mp hnot
  have hgroundOut : ¬ IsEdgeReachable graph edgeSet badVertex (Fin.last vertexRank) :=
    fun hreach => hbad (isEdgeReachable_symm hreach)
  set reducedIndicator : Fin vertexRank → ℝ :=
    fun coord => componentIndicator graph edgeSet badVertex coord.castSucc
    with hreducedIndicator
  have hgrounded : ∀ vertex : Fin (vertexRank + 1),
      groundedPotential reducedIndicator vertex
        = componentIndicator graph edgeSet badVertex vertex := by
    intro vertex
    induction vertex using Fin.lastCases with
    | last =>
        rw [groundedPotential_last, componentIndicator_of_not_reachable hgroundOut]
    | cast innerIndex =>
        rw [groundedPotential_castSucc, hreducedIndicator]
  have hflat : ∀ edge ∈ edgeSet,
      groundedPotential reducedIndicator (graph.edgeTail edge)
        = groundedPotential reducedIndicator (graph.edgeHead edge) := by
    intro edge hmem
    rw [hgrounded, hgrounded]
    by_cases htail : IsEdgeReachable graph edgeSet badVertex (graph.edgeTail edge)
    · rw [componentIndicator_of_reachable htail,
        componentIndicator_of_reachable (htail.trans (isEdgeReachable_endpoints graph hmem))]
    · rw [componentIndicator_of_not_reachable htail,
        componentIndicator_of_not_reachable
          (fun hhead => htail
            (hhead.trans (isEdgeReachable_symm (isEdgeReachable_endpoints graph hmem))))]
  have hne : reducedIndicator ≠ 0 := by
    intro hzero
    have hnone : ∀ vertex, ¬ IsEdgeReachable graph edgeSet badVertex vertex := by
      intro vertex
      induction vertex using Fin.lastCases with
      | last => exact hgroundOut
      | cast innerIndex =>
          intro hreach
          have hval : componentIndicator graph edgeSet badVertex innerIndex.castSucc = 0 :=
            congrFun hzero innerIndex
          rw [componentIndicator_of_reachable hreach] at hval
          exact one_ne_zero hval
    exact hnone badVertex Relation.ReflTransGen.refl
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hne
  rw [star_trivial, laplacianOn_form] at hpos
  have hzero : ∑ edge ∈ edgeSet, conductance edge *
      (groundedPotential reducedIndicator (graph.edgeTail edge)
        - groundedPotential reducedIndicator (graph.edgeHead edge)) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun edge hmem => ?_
    rw [hflat edge hmem, sub_self]
    ring
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- **The spanning dictionary**, both directions at once. -/
theorem posDef_laplacianOn_iff_isGroundConnected
    (graph : MultigraphOnGround edgeCount vertexRank)
    {conductance : Fin edgeCount → ℝ} (hcond : ∀ edge, 0 < conductance edge)
    (edgeSet : Finset (Fin edgeCount)) :
    (laplacianOn graph conductance edgeSet).PosDef ↔ IsGroundConnected graph edgeSet :=
  ⟨isGroundConnected_of_posDef_laplacianOn graph,
    posDef_laplacianOn_of_isGroundConnected graph hcond⟩

/-! ## The graphic weighted design -/

/-- The data of a **graphic weighted design**: a connected weighted multigraph
plus a probability weight on its edges.  Connectivity is stated as
ground-reachability through all edges; by
`posDef_laplacianOn_iff_isGroundConnected` this is exactly invertibility of the
reduced Laplacian, so nothing is smuggled in. -/
structure GraphDesignData (edgeCount vertexRank : ℕ) where
  /-- The underlying multigraph, with a distinguished ground vertex. -/
  graph : MultigraphOnGround edgeCount vertexRank
  /-- The edge conductances. -/
  conductance : Fin edgeCount → ℝ
  /-- Conductances are positive. -/
  conductance_pos : ∀ edge, 0 < conductance edge
  /-- The design weights on edges. -/
  weight : Fin edgeCount → ℝ
  /-- Design weights are positive. -/
  weight_pos : ∀ edge, 0 < weight edge
  /-- Design weights form a probability vector. -/
  weight_sum_one : ∑ edge, weight edge = 1
  /-- The graph is connected. -/
  isGroundConnected : IsGroundConnected graph Finset.univ

namespace GraphDesignData

variable (data : GraphDesignData edgeCount vertexRank)

/-- The full weighted reduced Laplacian `L = Σ_e w_e b_e b_eᵀ`. -/
def fullLaplacian : Matrix (Fin vertexRank) (Fin vertexRank) ℝ :=
  laplacianOn data.graph data.conductance Finset.univ

/-- The rescaled Laplacian of a selected edge set,
`Σ_{e ∈ edgeSet} (w_e / t_e) b_e b_eᵀ` — the left-hand side of the graphic
domination inequality. -/
noncomputable def selectedLaplacian (edgeSet : Finset (Fin edgeCount)) :
    Matrix (Fin vertexRank) (Fin vertexRank) ℝ :=
  laplacianOn data.graph (fun edge => data.conductance edge / data.weight edge) edgeSet

/-- Connectivity makes the full Laplacian positive definite. -/
theorem posDef_fullLaplacian : data.fullLaplacian.PosDef :=
  posDef_laplacianOn_of_isGroundConnected data.graph data.conductance_pos
    data.isGroundConnected

/-- The full Laplacian is symmetric. -/
theorem fullLaplacian_transpose : (data.fullLaplacian)ᵀ = data.fullLaplacian :=
  laplacianOn_transpose data.graph data.conductance Finset.univ

/-- The selected Laplacian is symmetric. -/
theorem selectedLaplacian_transpose (edgeSet : Finset (Fin edgeCount)) :
    (data.selectedLaplacian edgeSet)ᵀ = data.selectedLaplacian edgeSet :=
  laplacianOn_transpose data.graph _ edgeSet

/-- A whitener for the full Laplacian: `Rᵀ L R = I` with `R` invertible.  This
is the only place a choice is made, and it only changes the design by a
congruence. -/
noncomputable def whitener : Matrix (Fin vertexRank) (Fin vertexRank) ℝ :=
  Classical.choose (exists_congruence_to_one data.posDef_fullLaplacian)

theorem whitener_isUnit : IsUnit (data.whitener).det :=
  (Classical.choose_spec (exists_congruence_to_one data.posDef_fullLaplacian)).1

theorem whitener_spec :
    (data.whitener)ᵀ * data.fullLaplacian * data.whitener = 1 :=
  (Classical.choose_spec (exists_congruence_to_one data.posDef_fullLaplacian)).2

/-- The atom of an edge: the whitened incidence row scaled by `√(w_e / t_e)`. -/
noncomputable def graphicAtom (edge : Fin edgeCount) : Fin vertexRank → ℝ :=
  Real.sqrt (data.conductance edge / data.weight edge) •
    ((data.whitener)ᵀ *ᵥ data.graph.edgeVector edge)

/-- The atom matrix of an edge is the congruated incidence atom, scaled by the
conductance-to-weight ratio: the square roots cancel. -/
theorem atomMatrix_graphicAtom (edge : Fin edgeCount) :
    atomMatrix (data.graphicAtom edge)
      = (data.conductance edge / data.weight edge) •
        ((data.whitener)ᵀ * atomMatrix (data.graph.edgeVector edge) * data.whitener) := by
  rw [graphicAtom, atomMatrix_smul,
    Real.sq_sqrt (div_nonneg (data.conductance_pos edge).le (data.weight_pos edge).le),
    atomMatrix_conj, Matrix.transpose_transpose]

/-- Congruence commutes with the Laplacian sum. -/
theorem whitener_congr_laplacianOn (conductance : Fin edgeCount → ℝ)
    (edgeSet : Finset (Fin edgeCount)) :
    (data.whitener)ᵀ * laplacianOn data.graph conductance edgeSet * data.whitener
      = ∑ edge ∈ edgeSet, conductance edge •
          ((data.whitener)ᵀ * atomMatrix (data.graph.edgeVector edge) * data.whitener) := by
  rw [laplacianOn, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun edge _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- **The graphic weighted design.**  Atoms indexed by edges, weights the given
probability vector, Parseval supplied by the whitened Laplacian. -/
noncomputable def toWeightedDesign : WeightedDesign edgeCount vertexRank where
  atom := data.graphicAtom
  weight := data.weight
  weight_pos := data.weight_pos
  weight_sum_one := data.weight_sum_one
  isParseval := by
    have hstep : ∀ edge : Fin edgeCount,
        data.weight edge • atomMatrix (data.graphicAtom edge)
          = data.conductance edge •
            ((data.whitener)ᵀ * atomMatrix (data.graph.edgeVector edge) * data.whitener) := by
      intro edge
      rw [atomMatrix_graphicAtom, smul_smul, mul_div_cancel₀ _ (data.weight_pos edge).ne']
    calc ∑ edge, data.weight edge • atomMatrix (data.graphicAtom edge)
        = ∑ edge, data.conductance edge •
            ((data.whitener)ᵀ * atomMatrix (data.graph.edgeVector edge) * data.whitener) :=
          Finset.sum_congr rfl fun edge _ => hstep edge
      _ = (data.whitener)ᵀ * data.fullLaplacian * data.whitener := by
          rw [fullLaplacian, whitener_congr_laplacianOn]
      _ = 1 := data.whitener_spec

end GraphDesignData

/-- Shorthand: the weighted design of graph data. -/
noncomputable def graphicDesign (data : GraphDesignData edgeCount vertexRank) :
    WeightedDesign edgeCount vertexRank :=
  data.toWeightedDesign

/-- The design's weights are the graph data's weights, on the nose. -/
theorem graphicDesign_weight (data : GraphDesignData edgeCount vertexRank)
    (edge : Fin edgeCount) : (graphicDesign data).weight edge = data.weight edge := rfl

/-- The design's atom sum over a subset is the congruated selected Laplacian. -/
theorem graphicDesign_subsetSum (data : GraphDesignData edgeCount vertexRank)
    (edgeSet : Finset (Fin edgeCount)) :
    subsetSum (graphicDesign data) edgeSet
      = (data.whitener)ᵀ * data.selectedLaplacian edgeSet * data.whitener := by
  rw [subsetSum, GraphDesignData.selectedLaplacian,
    GraphDesignData.whitener_congr_laplacianOn]
  exact Finset.sum_congr rfl fun edge _ =>
    data.atomMatrix_graphicAtom edge

/-- **The dictionary.**  `Dominates` on an edge subset says exactly

`Σ_{e ∈ edgeSet} (w_e / t_e) b_e b_eᵀ  ⪰  Σ_{e} w_e b_e b_eᵀ`,

with the whitening removed.  No square roots, no pseudo-inverses, no choice of
coordinates survives in the statement. -/
theorem graphicDesign_dominates_iff (data : GraphDesignData edgeCount vertexRank)
    (edgeSet : Finset (Fin edgeCount)) :
    Dominates (graphicDesign data) edgeSet
      ↔ (data.selectedLaplacian edgeSet - data.fullLaplacian).PosSemidef := by
  have hsymm : (data.selectedLaplacian edgeSet - data.fullLaplacian)ᵀ
      = data.selectedLaplacian edgeSet - data.fullLaplacian := by
    rw [Matrix.transpose_sub, data.selectedLaplacian_transpose, data.fullLaplacian_transpose]
  have hsplit : (data.whitener)ᵀ * data.selectedLaplacian edgeSet * data.whitener - 1
      = (data.whitener)ᵀ * (data.selectedLaplacian edgeSet - data.fullLaplacian)
          * data.whitener := by
    rw [Matrix.mul_sub, Matrix.sub_mul, data.whitener_spec]
  rw [Dominates, graphicDesign_subsetSum, hsplit]
  exact (posSemidef_congr_right hsymm data.whitener_isUnit).symm

/-! ## Dominating subsets are spanning trees -/

/-- Domination forces the selected Laplacian to be positive definite. -/
theorem posDef_selectedLaplacian_of_dominates
    (data : GraphDesignData edgeCount vertexRank) {edgeSet : Finset (Fin edgeCount)}
    (hdom : Dominates (graphicDesign data) edgeSet) :
    (data.selectedLaplacian edgeSet).PosDef := by
  have hpsd := (graphicDesign_dominates_iff data edgeSet).mp hdom
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (data.selectedLaplacian_transpose edgeSet),
      fun reducedPotential hne => ?_⟩
  have hfull := (Matrix.posDef_iff_dotProduct_mulVec.mp data.posDef_fullLaplacian).2 hne
  have hgap := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 reducedPotential
  rw [star_trivial] at hfull hgap ⊢
  rw [Matrix.sub_mulVec, dotProduct_sub] at hgap
  linarith

/-- **Dominating subsets span.**  Every subset whose atoms dominate connects
every vertex to the ground: the selection problem is a spanning-subgraph
problem. -/
theorem isGroundConnected_of_dominates
    (data : GraphDesignData edgeCount vertexRank) {edgeSet : Finset (Fin edgeCount)}
    (hdom : Dominates (graphicDesign data) edgeSet) :
    IsGroundConnected data.graph edgeSet :=
  isGroundConnected_of_posDef_laplacianOn data.graph
    (posDef_selectedLaplacian_of_dominates data hdom)

/-- **Dominating subsets of the right size are spanning trees.**  Note the
cardinality conjunct is passed straight through from the hypothesis; the
content of this theorem is `isGroundConnected_of_dominates`. -/
theorem isSpanningTree_of_dominates
    (data : GraphDesignData edgeCount vertexRank) {edgeSet : Finset (Fin edgeCount)}
    (hcard : edgeSet.card = vertexRank)
    (hdom : Dominates (graphicDesign data) edgeSet) :
    IsSpanningTree data.graph edgeSet :=
  ⟨isGroundConnected_of_dominates data hdom, hcard⟩

/-- Disconnected subsets never dominate — the contrapositive reading, which is
what a search actually uses to prune. -/
theorem not_dominates_of_not_isGroundConnected
    (data : GraphDesignData edgeCount vertexRank) {edgeSet : Finset (Fin edgeCount)}
    (hdisconnected : ¬ IsGroundConnected data.graph edgeSet) :
    ¬ Dominates (graphicDesign data) edgeSet :=
  fun hdom => hdisconnected (isGroundConnected_of_dominates data hdom)

/-- **Dominating subsets are linearly spanning** in the matroid sense: no
nonzero potential is orthogonal to all their incidence rows. -/
theorem eq_zero_of_orthogonal_to_dominating
    (data : GraphDesignData edgeCount vertexRank) {edgeSet : Finset (Fin edgeCount)}
    (hdom : Dominates (graphicDesign data) edgeSet)
    {reducedPotential : Fin vertexRank → ℝ}
    (horth : ∀ edge ∈ edgeSet, data.graph.edgeVector edge ⬝ᵥ reducedPotential = 0) :
    reducedPotential = 0 := by
  by_contra hne
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp
    (posDef_selectedLaplacian_of_dominates data hdom)).2 hne
  rw [star_trivial, GraphDesignData.selectedLaplacian, laplacianOn_form] at hpos
  have hzero : ∑ edge ∈ edgeSet, (data.conductance edge / data.weight edge) *
      (groundedPotential reducedPotential (data.graph.edgeTail edge)
        - groundedPotential reducedPotential (data.graph.edgeHead edge)) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun edge hmem => ?_
    have := horth edge hmem
    rw [edgeVector_dotProduct] at this
    rw [this]
    ring
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-! ## The graphic instance of GTZ -/

/-- **Graphic GTZ at size `(edgeCount, vertexRank)`**: every connected weighted
multigraph with `edgeCount` edges and `vertexRank + 1` vertices has a
`vertexRank`-subset of edges that dominates.  By `isSpanningTree_of_dominates`
that subset is a spanning tree. -/
def GraphicGtz (edgeCount vertexRank : ℕ) : Prop :=
  ∀ data : GraphDesignData edgeCount vertexRank,
    ∃ edgeSet : Finset (Fin edgeCount), edgeSet.card = vertexRank ∧
      Dominates (graphicDesign data) edgeSet

/-- **The one-way bridge.**  Graphic designs are designs, so weighted GTZ
implies its graphic instance.  The converse is FALSE as an implication of
statements: graphic designs are a positive-codimension subfamily (a design is
graphic only if its Gram is congruent to a graphic matroid representation), so
a proof of `GraphicGtz` is *not* a proof of `GtzWeighted`.  What the graphic
instance does give is a refutation lane: a graphic counterexample refutes
`GtzWeighted` outright. -/
theorem graphicGtz_of_gtzWeighted (hgtz : GtzWeighted edgeCount vertexRank) :
    GraphicGtz edgeCount vertexRank :=
  fun data => hgtz (graphicDesign data)


/-! ## Base case: the `(k+1)`-cycle, at margin exactly zero -/

/-- The vertex of the cycle at a natural index, read modulo the vertex count. -/
def cycleVertex (vertexRank idx : ℕ) : Fin (vertexRank + 1) :=
  Fin.ofNat (vertexRank + 1) idx

/-- The cycle on `vertexRank + 1` vertices: edge `i` joins vertex `i` to vertex
`i + 1`, cyclically.  Its spanning trees are the `vertexRank + 1` paths. -/
def cycleGraph (vertexRank : ℕ) : MultigraphOnGround (vertexRank + 1) vertexRank where
  edgeTail := fun edge => edge
  edgeHead := fun edge => cycleVertex vertexRank (edge.val + 1)

/-- Natural indices below the vertex count survive the reduction modulo it. -/
theorem cycleVertex_val_of_le {vertexRank idx : ℕ} (hidx : idx ≤ vertexRank) :
    (cycleVertex vertexRank idx).val = idx :=
  Nat.mod_eq_of_lt (by omega)

/-- The non-closing edges of the cycle are the `Fin.castSucc` indices. -/
theorem cycleVertex_castSucc (vertexRank : ℕ) (innerIndex : Fin vertexRank) :
    cycleVertex vertexRank innerIndex.val = innerIndex.castSucc := by
  refine Fin.ext ?_
  rw [cycleVertex_val_of_le (le_of_lt innerIndex.isLt), Fin.val_castSucc]

/-- The ground vertex is the top index. -/
theorem cycleVertex_top (vertexRank : ℕ) :
    cycleVertex vertexRank vertexRank = Fin.last vertexRank := by
  refine Fin.ext ?_
  rw [cycleVertex_val_of_le (le_refl _), Fin.val_last]

/-- Index zero is vertex zero. -/
theorem cycleVertex_zero (vertexRank : ℕ) :
    cycleVertex vertexRank 0 = 0 := by
  refine Fin.ext ?_
  rw [cycleVertex_val_of_le (Nat.zero_le _)]
  rfl

/-- Successor of an index, cyclically: the head map of the cycle. -/
theorem cycleGraph_edgeHead_cycleVertex (vertexRank idx : ℕ) :
    (cycleGraph vertexRank).edgeHead (cycleVertex vertexRank idx)
      = cycleVertex vertexRank (idx + 1) := by
  refine Fin.ext ?_
  show ((cycleVertex vertexRank idx).val + 1) % (vertexRank + 1)
    = (idx + 1) % (vertexRank + 1)
  show (idx % (vertexRank + 1) + 1) % (vertexRank + 1) = (idx + 1) % (vertexRank + 1)
  exact Nat.mod_add_mod idx (vertexRank + 1) 1

/-- Every vertex of the cycle is reachable from vertex zero. -/
theorem cycleGraph_reachable_from_zero (vertexRank : ℕ) (vertex : Fin (vertexRank + 1)) :
    IsEdgeReachable (cycleGraph vertexRank) Finset.univ 0 vertex := by
  have hstep : ∀ steps : ℕ,
      IsEdgeReachable (cycleGraph vertexRank) Finset.univ 0 (cycleVertex vertexRank steps) := by
    intro steps
    induction steps with
    | zero =>
        rw [cycleVertex_zero]
        exact Relation.ReflTransGen.refl
    | succ previousStep ihead =>
        have hadj : IsEdgeAdjacent (cycleGraph vertexRank) Finset.univ
            (cycleVertex vertexRank previousStep)
            (cycleVertex vertexRank (previousStep + 1)) :=
          ⟨cycleVertex vertexRank previousStep, Finset.mem_univ _,
            Or.inl ⟨rfl, cycleGraph_edgeHead_cycleVertex vertexRank previousStep⟩⟩
        exact ihead.tail hadj
  have hreach := hstep vertex.val
  rwa [show cycleVertex vertexRank vertex.val = vertex from
    Fin.ext (cycleVertex_val_of_le (Nat.lt_succ_iff.mp vertex.isLt))] at hreach

/-- The cycle is connected. -/
theorem cycleGraph_isGroundConnected (vertexRank : ℕ) :
    IsGroundConnected (cycleGraph vertexRank) Finset.univ := fun vertex =>
  (isEdgeReachable_symm
      (cycleGraph_reachable_from_zero vertexRank (Fin.last vertexRank))).trans
    (cycleGraph_reachable_from_zero vertexRank vertex)

/-- **The cycle design**: unit conductances, uniform weight `1/(vertexRank+1)`.
The graphic reading of the campaign's zero-margin corner.  (The `HasExactCorner`
identification itself lives above this layer and is not proved here.) -/
noncomputable def cycleGraphData (vertexRank : ℕ) :
    GraphDesignData (vertexRank + 1) vertexRank where
  graph := cycleGraph vertexRank
  conductance := fun _ => 1
  conductance_pos := fun _ => one_pos
  weight := fun _ => ((vertexRank : ℝ) + 1)⁻¹
  weight_pos := fun _ => by positivity
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  isGroundConnected := cycleGraph_isGroundConnected vertexRank

/-- The cycle's grounded potential read along natural vertex indices. -/
def cycleNode (vertexRank : ℕ) (reducedPotential : Fin vertexRank → ℝ) (idx : ℕ) : ℝ :=
  groundedPotential reducedPotential (cycleVertex vertexRank idx)

/-- The potential vanishes at the ground vertex, index `vertexRank`. -/
theorem cycleNode_top (vertexRank : ℕ) (reducedPotential : Fin vertexRank → ℝ) :
    cycleNode vertexRank reducedPotential vertexRank = 0 := by
  rw [cycleNode, cycleVertex_top, groundedPotential_last]

/-- The potential drop across a non-closing edge. -/
theorem cycleDrop_castSucc (vertexRank : ℕ) (reducedPotential : Fin vertexRank → ℝ)
    (innerIndex : Fin vertexRank) :
    (cycleGraph vertexRank).edgeVector innerIndex.castSucc ⬝ᵥ reducedPotential
      = cycleNode vertexRank reducedPotential innerIndex.val
        - cycleNode vertexRank reducedPotential (innerIndex.val + 1) := by
  rw [edgeVector_dotProduct, cycleNode, cycleNode]
  have htail : (cycleGraph vertexRank).edgeTail innerIndex.castSucc
      = cycleVertex vertexRank innerIndex.val :=
    (cycleVertex_castSucc vertexRank innerIndex).symm
  have hhead : (cycleGraph vertexRank).edgeHead innerIndex.castSucc
      = cycleVertex vertexRank (innerIndex.val + 1) := by
    rw [← cycleVertex_castSucc vertexRank innerIndex,
      cycleGraph_edgeHead_cycleVertex]
  rw [htail, hhead]

/-- The potential drop across the closing edge, which the path omits. -/
theorem cycleDrop_last (vertexRank : ℕ) (reducedPotential : Fin vertexRank → ℝ) :
    (cycleGraph vertexRank).edgeVector (Fin.last vertexRank) ⬝ᵥ reducedPotential
      = - cycleNode vertexRank reducedPotential 0 := by
  rw [edgeVector_dotProduct, cycleNode]
  have htail : (cycleGraph vertexRank).edgeTail (Fin.last vertexRank)
      = Fin.last vertexRank := rfl
  have hhead : (cycleGraph vertexRank).edgeHead (Fin.last vertexRank)
      = cycleVertex vertexRank 0 := by
    rw [← cycleVertex_top vertexRank, cycleGraph_edgeHead_cycleVertex]
    refine Fin.ext ?_
    show (vertexRank + 1) % (vertexRank + 1) = 0 % (vertexRank + 1)
    rw [Nat.mod_self, Nat.zero_mod]
  rw [htail, hhead, groundedPotential_last, zero_sub]

/-- Summing over the path (all edges but the closing one) is summing over
`Fin vertexRank`. -/
theorem sum_erase_last_eq (vertexRank : ℕ) (summand : Fin (vertexRank + 1) → ℝ) :
    ∑ edge ∈ Finset.univ.erase (Fin.last vertexRank), summand edge
      = ∑ innerIndex : Fin vertexRank, summand innerIndex.castSucc := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_castSucc]
  ring

/-- **The cycle gap form.**  The Loewner gap of the path against the whole
cycle is `vertexRank · Σ(drop)² − (total drop)²` — a telescoping
Cauchy–Schwarz deficiency, and nothing else. -/
theorem cycleGap_form (vertexRank : ℕ) (reducedPotential : Fin vertexRank → ℝ) :
    reducedPotential ⬝ᵥ
        (((cycleGraphData vertexRank).selectedLaplacian
            (Finset.univ.erase (Fin.last vertexRank))
          - (cycleGraphData vertexRank).fullLaplacian) *ᵥ reducedPotential)
      = (vertexRank : ℝ) * (∑ idx ∈ Finset.range vertexRank,
            (cycleNode vertexRank reducedPotential idx
              - cycleNode vertexRank reducedPotential (idx + 1)) ^ 2)
        - (cycleNode vertexRank reducedPotential 0) ^ 2 := by
  have hweight : ∀ edge : Fin (vertexRank + 1),
      (cycleGraphData vertexRank).weight edge = ((vertexRank : ℝ) + 1)⁻¹ := fun _ => rfl
  have hgraph : (cycleGraphData vertexRank).graph = cycleGraph vertexRank := rfl
  have hcond : ∀ edge : Fin (vertexRank + 1),
      (cycleGraphData vertexRank).conductance edge = 1 := fun _ => rfl
  rw [Matrix.sub_mulVec, dotProduct_sub, GraphDesignData.selectedLaplacian,
    GraphDesignData.fullLaplacian, laplacianOn_form, laplacianOn_form]
  simp only [hweight, hgraph, hcond, one_div, inv_inv, one_mul]
  have hdrop : ∀ edge : Fin (vertexRank + 1),
      groundedPotential reducedPotential ((cycleGraph vertexRank).edgeTail edge)
        - groundedPotential reducedPotential ((cycleGraph vertexRank).edgeHead edge)
      = (cycleGraph vertexRank).edgeVector edge ⬝ᵥ reducedPotential := fun edge =>
    (edgeVector_dotProduct (cycleGraph vertexRank) edge reducedPotential).symm
  simp only [hdrop]
  rw [Fin.sum_univ_castSucc
    (f := fun edge : Fin (vertexRank + 1) =>
      ((cycleGraph vertexRank).edgeVector edge ⬝ᵥ reducedPotential) ^ 2)]
  rw [sum_erase_last_eq vertexRank
    (fun edge => ((vertexRank : ℝ) + 1) *
      ((cycleGraph vertexRank).edgeVector edge ⬝ᵥ reducedPotential) ^ 2)]
  simp only [cycleDrop_castSucc, cycleDrop_last]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (f := fun idx => (cycleNode vertexRank reducedPotential idx
      - cycleNode vertexRank reducedPotential (idx + 1)) ^ 2)]
  ring

/-- **The cycle dominates on the path.**  Domination is exactly the
Cauchy–Schwarz inequality applied to the telescoped potential drop. -/
theorem cycleGraphData_dominates (vertexRank : ℕ) :
    Dominates (graphicDesign (cycleGraphData vertexRank))
      (Finset.univ.erase (Fin.last vertexRank)) := by
  rw [graphicDesign_dominates_iff]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq ?_, fun reducedPotential => ?_⟩
  · rw [Matrix.transpose_sub, (cycleGraphData vertexRank).selectedLaplacian_transpose,
      (cycleGraphData vertexRank).fullLaplacian_transpose]
  · rw [star_trivial, cycleGap_form]
    have htelescope : ∑ idx ∈ Finset.range vertexRank,
        (cycleNode vertexRank reducedPotential idx
          - cycleNode vertexRank reducedPotential (idx + 1))
        = cycleNode vertexRank reducedPotential 0 := by
      rw [Finset.sum_range_sub' (fun idx => cycleNode vertexRank reducedPotential idx),
        cycleNode_top, sub_zero]
    have hcs : (∑ idx ∈ Finset.range vertexRank,
          (1 : ℝ) * (cycleNode vertexRank reducedPotential idx
            - cycleNode vertexRank reducedPotential (idx + 1))) ^ 2
        ≤ (∑ _idx ∈ Finset.range vertexRank, (1 : ℝ) ^ 2)
          * (∑ idx ∈ Finset.range vertexRank,
              (cycleNode vertexRank reducedPotential idx
                - cycleNode vertexRank reducedPotential (idx + 1)) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at hcs
    rw [htelescope] at hcs
    linarith

/-- The cardinality of the path is the rank: it really is a spanning tree. -/
theorem cycleGraphData_path_card (vertexRank : ℕ) :
    (Finset.univ.erase (Fin.last vertexRank)).card = vertexRank := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- **Margin exactly zero.**  The path does not dominate *strictly*: the
potential `idx ↦ vertexRank − idx` makes the gap form vanish.  So the graphic
boundary is attained already at the cycle, and no strictly-positive certificate
can exist there.  Stated for the path that drops the closing edge; the other
`vertexRank` paths are tight too by the cycle's rotational symmetry, which is
measured but not formalized. -/
theorem cycleGraphData_not_posDef (vertexRank : ℕ) (hrank : 1 ≤ vertexRank) :
    ¬ (subsetSum (graphicDesign (cycleGraphData vertexRank))
        (Finset.univ.erase (Fin.last vertexRank)) - 1).PosDef := by
  intro hpd
  have hsymm : ((cycleGraphData vertexRank).selectedLaplacian
        (Finset.univ.erase (Fin.last vertexRank))
      - (cycleGraphData vertexRank).fullLaplacian)ᵀ
      = (cycleGraphData vertexRank).selectedLaplacian
          (Finset.univ.erase (Fin.last vertexRank))
        - (cycleGraphData vertexRank).fullLaplacian := by
    rw [Matrix.transpose_sub, (cycleGraphData vertexRank).selectedLaplacian_transpose,
      (cycleGraphData vertexRank).fullLaplacian_transpose]
  have hsplit : ((cycleGraphData vertexRank).whitener)ᵀ
        * (cycleGraphData vertexRank).selectedLaplacian
            (Finset.univ.erase (Fin.last vertexRank))
        * (cycleGraphData vertexRank).whitener - 1
      = ((cycleGraphData vertexRank).whitener)ᵀ
        * ((cycleGraphData vertexRank).selectedLaplacian
            (Finset.univ.erase (Fin.last vertexRank))
          - (cycleGraphData vertexRank).fullLaplacian)
        * (cycleGraphData vertexRank).whitener := by
    rw [Matrix.mul_sub, Matrix.sub_mul, (cycleGraphData vertexRank).whitener_spec]
  rw [graphicDesign_subsetSum, hsplit] at hpd
  have hgap := (posDef_congr_right hsymm (cycleGraphData vertexRank).whitener_isUnit).mpr hpd
  set witness : Fin vertexRank → ℝ := fun coord => (vertexRank : ℝ) - (coord.val : ℝ)
    with hwitness
  have hnode : ∀ idx : ℕ, idx ≤ vertexRank →
      cycleNode vertexRank witness idx = (vertexRank : ℝ) - (idx : ℝ) := by
    intro idx hidx
    rcases Nat.lt_or_ge idx vertexRank with hlt | hge
    · have hidxfin : cycleVertex vertexRank idx = (⟨idx, hlt⟩ : Fin vertexRank).castSucc :=
        cycleVertex_castSucc vertexRank ⟨idx, hlt⟩
      rw [cycleNode, hidxfin, groundedPotential_castSucc, hwitness]
    · have hidxeq : idx = vertexRank := by omega
      rw [hidxeq, cycleNode_top]
      ring
  have hdiff : ∀ idx ∈ Finset.range vertexRank,
      (cycleNode vertexRank witness idx - cycleNode vertexRank witness (idx + 1)) ^ 2 = 1 := by
    intro idx hmem
    have hlt := Finset.mem_range.mp hmem
    rw [hnode idx (by omega), hnode (idx + 1) (by omega)]
    push_cast
    ring
  have hrealrank : (1 : ℝ) ≤ (vertexRank : ℝ) := by exact_mod_cast hrank
  have hwitnessNe : witness ≠ 0 := by
    intro hzero
    have hval : witness ⟨0, by omega⟩ = 0 := congrFun hzero _
    simp only [hwitness, Nat.cast_zero, sub_zero] at hval
    linarith
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hgap).2 hwitnessNe
  have hsum : ∑ idx ∈ Finset.range vertexRank,
      (cycleNode vertexRank witness idx - cycleNode vertexRank witness (idx + 1)) ^ 2
      = (vertexRank : ℝ) := by
    rw [Finset.sum_congr rfl hdiff, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hzeroNode : cycleNode vertexRank witness 0 = (vertexRank : ℝ) := by
    rw [hnode 0 (Nat.zero_le _)]
    norm_num
  rw [star_trivial, cycleGap_form, hsum, hzeroNode] at hform
  nlinarith [hform]

/-- The `(k+1)`-cycle instantiates graphic GTZ at size `(k+1, k)` with equality:
a dominating spanning tree exists, and its margin is zero. -/
theorem cycleGraphData_isSpanningTree (vertexRank : ℕ) :
    IsSpanningTree (cycleGraphData vertexRank).graph
      (Finset.univ.erase (Fin.last vertexRank)) :=
  isSpanningTree_of_dominates (cycleGraphData vertexRank)
    (cycleGraphData_path_card vertexRank) (cycleGraphData_dominates vertexRank)


/-! ## Deletion and contraction, in the form an induction would need -/

/-- Deleting an edge subtracts its atom from the Laplacian. -/
theorem laplacianOn_erase (graph : MultigraphOnGround edgeCount vertexRank)
    (conductance : Fin edgeCount → ℝ) (deletedEdge : Fin edgeCount) :
    laplacianOn graph conductance (Finset.univ.erase deletedEdge)
      = laplacianOn graph conductance Finset.univ
        - conductance deletedEdge • atomMatrix (graph.edgeVector deletedEdge) := by
  rw [laplacianOn, laplacianOn, Finset.sum_erase_eq_sub (Finset.mem_univ _)]

/-- **Light-edge deletion, in Loewner form.**  "Edge `e` is light" is
`conductance e · b_e b_eᵀ ⪯ weight e · L` — precisely the graph reading of the
campaign's light-atom condition `leverage ≤ 1`, since the leverage of edge `e`
is `(conductance e / weight e) · (effective resistance across e)`.  Under it,
any selection that dominates the *deleted* graph's Laplacian rescaled by
`(1 − weight e)⁻¹` already dominates the full one — so the deflation step
`(m+1, k) → (m, k)` transfers back. -/
theorem dominates_of_deleted_dominates
    (data : GraphDesignData edgeCount vertexRank) (lightEdge : Fin edgeCount)
    {selected : Matrix (Fin vertexRank) (Fin vertexRank) ℝ}
    (hweightLt : data.weight lightEdge < 1)
    (hlight : (data.weight lightEdge • data.fullLaplacian
        - data.conductance lightEdge
            • atomMatrix (data.graph.edgeVector lightEdge)).PosSemidef)
    (hdeleted : (selected - (1 - data.weight lightEdge)⁻¹ •
        laplacianOn data.graph data.conductance
          (Finset.univ.erase lightEdge)).PosSemidef) :
    (selected - data.fullLaplacian).PosSemidef := by
  have hpos : 0 < 1 - data.weight lightEdge := by linarith
  have hid : (1 - data.weight lightEdge)⁻¹ •
        laplacianOn data.graph data.conductance (Finset.univ.erase lightEdge)
      - data.fullLaplacian
      = (1 - data.weight lightEdge)⁻¹ • (data.weight lightEdge • data.fullLaplacian
        - data.conductance lightEdge
            • atomMatrix (data.graph.edgeVector lightEdge)) := by
    rw [laplacianOn_erase, ← GraphDesignData.fullLaplacian]
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hgap : ((1 - data.weight lightEdge)⁻¹ •
      laplacianOn data.graph data.conductance (Finset.univ.erase lightEdge)
      - data.fullLaplacian).PosSemidef := by
    rw [hid]
    exact hlight.smul (le_of_lt (inv_pos.mpr hpos))
  have hsplit : selected - data.fullLaplacian
      = (selected - (1 - data.weight lightEdge)⁻¹ •
          laplacianOn data.graph data.conductance (Finset.univ.erase lightEdge))
        + ((1 - data.weight lightEdge)⁻¹ •
            laplacianOn data.graph data.conductance (Finset.univ.erase lightEdge)
          - data.fullLaplacian) := by
    abel
  rw [hsplit]
  exact hdeleted.add hgap

/-- **Contraction as restriction.**  Contracting an edge identifies its
endpoints, i.e. restricts the potential space to `b_e ⊥ u`.  On that subspace
the contracted graph's Dirichlet form and the full one agree, because the
contracted edge contributes a zero drop.  This is the exact sense in which the
campaign's heavy-atom / duality step is graph contraction; the rank-reducing
reindexing of the vertex set is NOT carried out here. -/
theorem laplacianOn_form_erase_of_orthogonal
    (graph : MultigraphOnGround edgeCount vertexRank)
    (conductance : Fin edgeCount → ℝ) (contractedEdge : Fin edgeCount)
    {reducedPotential : Fin vertexRank → ℝ}
    (horth : graph.edgeVector contractedEdge ⬝ᵥ reducedPotential = 0) :
    reducedPotential ⬝ᵥ (laplacianOn graph conductance Finset.univ *ᵥ reducedPotential)
      = reducedPotential ⬝ᵥ
          (laplacianOn graph conductance (Finset.univ.erase contractedEdge)
            *ᵥ reducedPotential) := by
  rw [laplacianOn_form, laplacianOn_form, Finset.sum_erase_eq_sub (Finset.mem_univ _),
    ← edgeVector_dotProduct, horth]
  ring


/-! ## Base case: `K4` (the wheel `W_3`), the first non-series-parallel graph -/

/-- `K4` on four vertices with ground `3`.  Edges `0,1,2` are the star at the
ground; edges `3,4,5` are the triangle on the remaining three vertices. -/
def completeFourGraph : MultigraphOnGround 6 3 where
  edgeTail := ![0, 1, 2, 0, 0, 1]
  edgeHead := ![3, 3, 3, 1, 2, 2]

/-- The star at the ground vertex: a spanning tree of `K4`. -/
def completeFourStar : Finset (Fin 6) := {0, 1, 2}

theorem completeFourGraph_isGroundConnected :
    IsGroundConnected completeFourGraph Finset.univ := by
  intro vertex
  fin_cases vertex
  · exact Relation.ReflTransGen.single ⟨0, Finset.mem_univ _, Or.inr ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.single ⟨1, Finset.mem_univ _, Or.inr ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.single ⟨2, Finset.mem_univ _, Or.inr ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.refl

/-- **The `K4` design**: unit conductances, uniform weight `1/6`.  This is the
graphic instance of GTZ at exactly the campaign's binding size `(6, 3)`. -/
noncomputable def completeFourData : GraphDesignData 6 3 where
  graph := completeFourGraph
  conductance := fun _ => 1
  conductance_pos := fun _ => one_pos
  weight := fun _ => (6 : ℝ)⁻¹
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  isGroundConnected := completeFourGraph_isGroundConnected

theorem groundedPotential_four_zero (reducedPotential : Fin 3 → ℝ) :
    groundedPotential reducedPotential 0 = reducedPotential 0 := by
  rw [show (0 : Fin 4) = (0 : Fin 3).castSucc from rfl, groundedPotential_castSucc]

theorem groundedPotential_four_one (reducedPotential : Fin 3 → ℝ) :
    groundedPotential reducedPotential 1 = reducedPotential 1 := by
  rw [show (1 : Fin 4) = (1 : Fin 3).castSucc from rfl, groundedPotential_castSucc]

theorem groundedPotential_four_two (reducedPotential : Fin 3 → ℝ) :
    groundedPotential reducedPotential 2 = reducedPotential 2 := by
  rw [show (2 : Fin 4) = (2 : Fin 3).castSucc from rfl, groundedPotential_castSucc]

theorem groundedPotential_four_three (reducedPotential : Fin 3 → ℝ) :
    groundedPotential reducedPotential 3 = 0 := by
  rw [show (3 : Fin 4) = Fin.last 3 from rfl, groundedPotential_last]

/-- **The `K4` gap form has an explicit sum-of-squares certificate.**  The star
tree's Loewner gap against the whole of `K4` is
`2·(u₀² + u₁² + u₂²) + (u₀ + u₁ + u₂)²` — strictly positive off zero.  Compare
`cycleGap_form`, whose gap vanishes on a whole line: `K4` has slack where the
cycle has none. -/
theorem completeFourGap_form (reducedPotential : Fin 3 → ℝ) :
    reducedPotential ⬝ᵥ
        ((completeFourData.selectedLaplacian completeFourStar
          - completeFourData.fullLaplacian) *ᵥ reducedPotential)
      = 2 * (reducedPotential 0 ^ 2 + reducedPotential 1 ^ 2 + reducedPotential 2 ^ 2)
        + (reducedPotential 0 + reducedPotential 1 + reducedPotential 2) ^ 2 := by
  have hweight : ∀ edge : Fin 6, completeFourData.weight edge = (6 : ℝ)⁻¹ := fun _ => rfl
  have hcond : ∀ edge : Fin 6, completeFourData.conductance edge = 1 := fun _ => rfl
  have hgraph : completeFourData.graph = completeFourGraph := rfl
  rw [Matrix.sub_mulVec, dotProduct_sub, GraphDesignData.selectedLaplacian,
    GraphDesignData.fullLaplacian, laplacianOn_form, laplacianOn_form]
  simp only [hweight, hcond, hgraph, one_div, inv_inv]
  rw [show completeFourStar = insert (0 : Fin 6) (insert (1 : Fin 6) {(2 : Fin 6)}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Fin.sum_univ_six]
  have hfiveTail : (![0, 1, 2, 0, 0, 1] : Fin 6 → Fin 4) 5 = 1 := rfl
  have hfiveHead : (![3, 3, 3, 1, 2, 2] : Fin 6 → Fin 4) 5 = 2 := rfl
  simp only [completeFourGraph,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four,
    hfiveTail, hfiveHead,
    groundedPotential_four_zero, groundedPotential_four_one, groundedPotential_four_two,
    groundedPotential_four_three]
  ring

/-- **`K4` dominates strictly.**  The star at the ground vertex beats the full
Laplacian with a positive-definite gap: the graphic instance at `(6,3)` has
slack at `K4`, in contrast with the cycle. -/
theorem completeFourData_dominates_strictly :
    (completeFourData.selectedLaplacian completeFourStar
      - completeFourData.fullLaplacian).PosDef := by
  have hsymm : (completeFourData.selectedLaplacian completeFourStar
      - completeFourData.fullLaplacian)ᵀ
      = completeFourData.selectedLaplacian completeFourStar
        - completeFourData.fullLaplacian := by
    rw [Matrix.transpose_sub, completeFourData.selectedLaplacian_transpose,
      completeFourData.fullLaplacian_transpose]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun reducedPotential hne => ?_⟩
  rw [star_trivial, completeFourGap_form]
  have hsome : reducedPotential 0 ≠ 0 ∨ reducedPotential 1 ≠ 0 ∨ reducedPotential 2 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext fun coord => by fin_cases coord <;> simp [hall.1, hall.2.1, hall.2.2])
  rcases hsome with hzero | hone | htwo
  · nlinarith [sq_nonneg (reducedPotential 1), sq_nonneg (reducedPotential 2),
      sq_nonneg (reducedPotential 0 + reducedPotential 1 + reducedPotential 2),
      sq_pos_of_ne_zero hzero]
  · nlinarith [sq_nonneg (reducedPotential 0), sq_nonneg (reducedPotential 2),
      sq_nonneg (reducedPotential 0 + reducedPotential 1 + reducedPotential 2),
      sq_pos_of_ne_zero hone]
  · nlinarith [sq_nonneg (reducedPotential 0), sq_nonneg (reducedPotential 1),
      sq_nonneg (reducedPotential 0 + reducedPotential 1 + reducedPotential 2),
      sq_pos_of_ne_zero htwo]

/-- `K4`'s star is a dominating spanning tree: graphic GTZ holds at `K4`. -/
theorem completeFourData_dominates :
    Dominates (graphicDesign completeFourData) completeFourStar := by
  rw [graphicDesign_dominates_iff]
  exact completeFourData_dominates_strictly.posSemidef

theorem completeFourStar_card : completeFourStar.card = 3 := by decide

theorem completeFourData_isSpanningTree :
    IsSpanningTree completeFourData.graph completeFourStar :=
  isSpanningTree_of_dominates completeFourData completeFourStar_card
    completeFourData_dominates

end Gtz

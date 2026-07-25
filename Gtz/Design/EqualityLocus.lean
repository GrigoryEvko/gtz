/-
# The equality locus: graph-induced bundled cycles, exactly tight at every rank

GTZ's weighted form asks for a `k`-subset whose atom sum dominates the identity.
This file builds, at **every rank**, an explicit family of designs that dominate
with margin **exactly zero** — the equality cases every sharp-inequality proof
must be tight on — realizes them as *graphs*, and computes their leverages in
closed form.

## The family

Take the `(k+1)`-cycle and replace arc `j` by a **bundle** of `p_j ≥ 1` parallel
edges, `n = Σ_j p_j`.  Put the uniform design weight `1/n` on the `n` edges and
the **graph-induced conductance** `1/φ(p_j)`, `φ(x) = x(n − x)`, on every edge of
bundle `j`.  Then for every choice of one edge out of each of `k` of the `k+1`
bundles the selected `k`-subset dominates, and no `k`-subset dominates strictly.

Everything collapses to **one inequality**: writing `d_j` for the potential drop
across arc `j`, the Loewner gap of the transversal that omits arc `j₀` is exactly

```
      Σ_{j ≠ j₀} d_j² / p_j  −  (Σ_{j ≠ j₀} d_j)² / (Σ_{j ≠ j₀} p_j)
```

— Sedrakyan/Engel's form of Cauchy–Schwarz (`bundledCycle_gap_eq_engelDeficiency`),
nonnegative always and zero exactly on the ray `d_j ∝ p_j`.  That ray is realized
by an explicit potential (`bundleTightDrops`), which is why the margin is zero and
not merely small.

## PROVED here

* `bundledCycleData` / `bundledCycleDesign` — the bundled cycle with graph-induced
  conductance IS a `WeightedDesign`.  Parseval is inherited from `graphicDesign`
  (`Gtz.Design.GraphicInstance`); what is new is connectivity of the bundled cycle
  and positivity of `1/φ(p_j)`, which needs `0 < p_j < n` and hence `1 ≤ k`.
* `bundledCycle_gap_eq_engelDeficiency` — the exact gap identity above, for any
  edge set on which the bundle map is injective with image the complement of one
  arc.
* `bundledCycle_dominates`, `bundledCycleTree_dominates`,
  `bundledCycleTree_isSpanningTree` — the `⪰` half, on an explicit transversal.
* `bundledCycle_not_posDef` — the `≻`-fails half, for **every** `k`-subset, by a
  split on whether the bundle map is injective on it.  Both branches are
  discharged by one construction, `potentialOfDrops`, which realizes any zero-sum
  drop vector as a potential.
* `bundledCycle_isTie` — the two halves packaged as `Gtz.IsTie`: the value is
  exactly 1.
* `bundledCycle_leverage` — the closed form `|g_e|² = ((k−1)n + p)/(k p)` for an
  edge in an arc of size `p`, proved by exhibiting the transfer current as an
  explicit potential and checking `L y = b_e` against the polarized Dirichlet form.
  **The Laplacian is never inverted**; the solving potential is exhibited and
  checked.  (The whitener's inverse does appear, inside the shipped congruence
  kit `whitener_gram_mul_fullLaplacian` rests on.)
* `bundledCycle_leverage_identity_at_arcTotal` — that closed form satisfies the
  affine relation `k T ℓ = (k−1) + T` at the arc total `T = p/n`, i.e. the
  corank-one tie criterion of `Gtz.isTie_iff_leverage_identity`.  Two independent
  routes (pivot/Schur there, transfer current here) to the same number.
* `bundledCycle_projection_diagonal` — the same read on the shipped projection
  coordinates of `Gtz.LinAlg.ProjectionForm`: `P_ee = (k−1)/(k p) + 1/(k n)`.
* `bundledCycle_rankTwo_clusterMagnitude` — at `k = 2` that is `1/(2n) + 1/(2p)`;
  and `bundledCycle_atom_eq_of_sameBundle` says the atoms inside an arc are
  *equal*, not merely parallel.  So a rank-2 bundled cycle is exactly a
  three-cluster design with cluster sizes `(p, q, r)`, `p + q + r = n`, of the
  magnitudes the real `k = 2` equality criterion prescribes.
* `engelDeficiency_two`, `bundledCycle_gap_eq_squareQuotient` and its
  hypothesis-free form `bundledCycle_rankTwo_gap_squareQuotient` — at rank 2 the
  gap is the **exact rational square** `(d₁ p₂ − d₂ p₁)² / (p₁ p₂ (p₁ + p₂))`, so
  the slack off the tight ray is an explicit rational function of the drops, not
  merely a positive quantity.  The slack is quantified in the DROPS; no claim is
  made or implied about a slack constant uniform in the design's weights.
* `cycleBundlingWitness` — the plain `(k+1)`-cycle, an inhabitant of
  `CycleBundling (k+1) k` at every rank, so the universally quantified results
  above have a witness at every rank and not only at the sizes instantiated
  below.  `cycleBundlingWitness_isTie` and `cycleBundlingWitness_leverage` (the
  corner leverage is `k`) are the instantiations.
* Exact instances at the campaign's binding rank-3 sizes: `(6,3)` with arc sizes
  `(3,1,1,1)` and `(2,2,1,1)`, `(7,3)` with `(4,1,1,1)`, `(3,2,1,1)`, `(2,2,2,1)`,
  each an `IsTie`, with their leverages evaluated in the kernel.  Two rank-2
  instances at `(9,2)`, arc sizes `(7,1,1)` and `(4,3,2)`, with their cluster
  magnitudes `{8/63, 5/9}` and `{13/72, 2/9, 11/36}` evaluated in the kernel.

Reusable kit landed along the way, none of it specific to the cycle:
`graphicDesign_posDef_iff` (strict domination through the whitener — the `≻`
companion of the shipped `graphicDesign_dominates_iff`),
`whitener_gram_mul_fullLaplacian`, `graphicDesign_atom` /
`graphicAtom_eq_whitenedRow`, `edgeVector_congr`, and
`leverageOf_graphicAtom_of_solves`.  The polarized Dirichlet form
`laplacianOn_bilinear` was first proved here and now lives upstream in
`Gtz.Design.GraphicInstance`, where the shipped `laplacianOn_form` is derived
from it as its diagonal.

## Relation to what was already in the repo

`Gtz.Ties.SplitClassTieFamily` already exhibits the abstract tie stratum over the
whole open weight simplex at every size, by putting the corank-one atom of each
class on its members.  This file is not a re-proof of that: it is the **graphic
realization** of the rational points of that stratum — the class weights here are
forced to be `p_j / n` — together with the two things the abstract construction
does not give, namely the *reason* the margin vanishes (the Engel deficiency, an
identity in the arc drops) and the leverage in closed form.  The consistency of
the two is the content of `bundledCycle_leverage_identity_at_arcTotal`.

At `p_j ≡ 1`, `n = k + 1`, the underlying graph is the plain `(k+1)`-cycle of
`Gtz.cycleGraphData`, whose zero margin is `Gtz.cycleGraphData_not_posDef`.  That
the two designs coincide (the conductance differs by the constant `1/k`, which the
whitening absorbs) is NOT proved here — it is a remark, not a lemma.

## CITED, not proved here

* The identification of this family with Nesterenko's series-parallel construction
  (arXiv:2511.02387, Thm 3.1): the cycle with parallel bundles is the
  series-parallel graph whose matroid is `U(k, k+1)` with parallel extensions, and
  `1/φ(p)` is that paper's graph-induced weight on such a bundle.  The statement
  proved here is self-contained; only the attribution is cited.
* That at rank 2 the three-cluster condition with magnitudes `1/(2n) + 1/(2p_j)`
  **characterizes** the real equality locus (arXiv:2604.14050 Prop 1; the `k ≤ 2`
  theorem itself is Sengupta–Pautov, arXiv:2604.05944).  This file proves the
  designs built here *satisfy* that condition.  That nothing else does is cited,
  and is the half that does the work.  **Scope of that citation**: it is stated
  for `n × 2` matrices with orthonormal columns, i.e. for designs of UNIFORM
  weight `1/n`.  Every design in this file has uniform weight `1/n`, so the match
  is inside the cited scope — but nothing here, and nothing cited here, says
  anything about tight rank-2 designs of non-uniform weight.

## MEASURED, not proved here

* That the tight designs at `(6,3)` and `(7,3)` are exhausted by the
  series-parallel ones — 4 and 8 symmetry classes.  The bundled cycles below
  account for the `U(3,4)` classes; the diamond `M(K₄ − e)` classes are **not** in
  this family and are formalized nowhere.
* The exhaustive exact-rational leverage tables: `(6,3)` gives `{5/3, 13/3}` and
  `{7/3, 13/3}`; `(7,3)` gives `{3/2, 5}`, `{17/9, 8/3, 5}`, `{8/3, 5}`.  The
  closed form `((k−1)n + p)/(k p)` reproduces every one of them, and every
  distinct value in those tables is checked in the kernel below.

## Coverage limits

This is one family, not the locus.  It is the cycle matroid `U(k, k+1)` with
parallel extensions; the other rank-3 tight class, the diamond, needs genuine
series/parallel composition and is absent, as is every non-graphic design.

Nothing here bears on whether `GtzWeighted` is true.  A tie is a boundary point of
the feasible region; this file exhibits boundary points and proves they are
boundary points.  What that buys is an obstruction: `bundledCycle_not_posDef` says
no strictly-positive certificate can exist at these designs, at any rank, so any
proof of GTZ must be exactly tight on the whole family.

The bundle map is *data*, not a quotient: two bundlings differing by a relabelling
of edges give the same design up to permutation, and that identification is not
made.  `CycleBundling` therefore counts labelled bundlings, never symmetry classes,
and no counting statement is made or implied.  `CycleBundling edgeCount vertexRank`
is EMPTY when `edgeCount < vertexRank + 1`; `cycleBundlingWitness` inhabits it at
the smallest size for each rank.

This file sits in `Design/` but imports `Gtz.Certificates.ResidueDissolution` for
`IsTie`, so its import edge points one layer up.  That is deliberate — the tie is
the deliverable — and it introduces no cycle: `Certificates/` does not import
`Design/`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Design.GraphicInstance
import Gtz.Certificates.ResidueDissolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {edgeCount vertexRank : ℕ}

/-! ## Kit: strict domination through the whitener, and leverage without an inverse -/

/-- **Strict domination through the whitener.**  The `≻` companion of the shipped
`graphicDesign_dominates_iff`: a `k`-subset dominates *strictly* exactly when its
rescaled Laplacian beats the full one with a positive-definite gap.  This is what
turns "no certificate has slack" into a statement about graphs. -/
theorem graphicDesign_posDef_iff (data : GraphDesignData edgeCount vertexRank)
    (edgeSet : Finset (Fin edgeCount)) :
    (subsetSum (graphicDesign data) edgeSet - 1).PosDef
      ↔ (data.selectedLaplacian edgeSet - data.fullLaplacian).PosDef := by
  have hsymm : (data.selectedLaplacian edgeSet - data.fullLaplacian)ᵀ
      = data.selectedLaplacian edgeSet - data.fullLaplacian := by
    rw [Matrix.transpose_sub, data.selectedLaplacian_transpose, data.fullLaplacian_transpose]
  have hsplit : (data.whitener)ᵀ * data.selectedLaplacian edgeSet * data.whitener - 1
      = (data.whitener)ᵀ * (data.selectedLaplacian edgeSet - data.fullLaplacian)
          * data.whitener := by
    rw [Matrix.mul_sub, Matrix.sub_mul, data.whitener_spec]
  rw [graphicDesign_subsetSum, hsplit]
  exact (posDef_congr_right hsymm data.whitener_isUnit).symm

/-- The whitener's Gram is the inverse Laplacian: `R Rᵀ L = 1`.  Read off
`Rᵀ L R = 1` by cancelling `R` on the right. -/
theorem whitener_gram_mul_fullLaplacian (data : GraphDesignData edgeCount vertexRank) :
    data.whitener * (data.whitener)ᵀ * data.fullLaplacian = 1 := by
  have hcancel : data.whitener * ((data.whitener)ᵀ * data.fullLaplacian * data.whitener)
      * data.whitener⁻¹ = data.whitener * 1 * data.whitener⁻¹ := by
    rw [data.whitener_spec]
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ data.whitener_isUnit] at hcancel
  calc data.whitener * (data.whitener)ᵀ * data.fullLaplacian
      = data.whitener * (data.whitener)ᵀ * data.fullLaplacian
        * (data.whitener * data.whitener⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ data.whitener_isUnit, Matrix.mul_one]
    _ = data.whitener * ((data.whitener)ᵀ * data.fullLaplacian * data.whitener)
        * data.whitener⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := hcancel

/-- The design's atom at an edge is the graph data's atom, on the nose. -/
theorem graphicDesign_atom (data : GraphDesignData edgeCount vertexRank) (edge : Fin edgeCount) :
    (graphicDesign data).atom edge = data.graphicAtom edge := rfl

/-- The graph atom in coordinates: the whitened incidence row scaled by the square
root of the conductance-to-weight ratio.  Stated once; `graphicDesign_atom` names
the abstraction, this one names its unfolding. -/
theorem graphicAtom_eq_whitenedRow (data : GraphDesignData edgeCount vertexRank)
    (edge : Fin edgeCount) :
    data.graphicAtom edge
      = Real.sqrt (data.conductance edge / data.weight edge)
        • ((data.whitener)ᵀ *ᵥ data.graph.edgeVector edge) := rfl

/-- **Leverage without inverting the Laplacian.**  If `potential` solves
`L y = b_e` — the potential of a unit current injected across edge `e` — then the
design atom's leverage is the conductance-to-weight ratio times the drop of that
potential across `e`.  Every leverage computed in this file goes through this
lemma; the solving potential is always exhibited, never solved for.  (The
whitener's inverse does appear, inside the shipped congruence kit that
`whitener_gram_mul_fullLaplacian` rests on; what is never inverted is the
Laplacian.) -/
theorem leverageOf_graphicAtom_of_solves (data : GraphDesignData edgeCount vertexRank)
    (edge : Fin edgeCount) (potential : Fin vertexRank → ℝ)
    (hsolve : data.fullLaplacian *ᵥ potential = data.graph.edgeVector edge) :
    leverageOf ((graphicDesign data).atom edge)
      = (data.conductance edge / data.weight edge)
        * (data.graph.edgeVector edge ⬝ᵥ potential) := by
  have hratio : (0 : ℝ) ≤ data.conductance edge / data.weight edge :=
    div_nonneg (data.conductance_pos edge).le (data.weight_pos edge).le
  have hkey : (data.whitener * (data.whitener)ᵀ) *ᵥ data.graph.edgeVector edge = potential := by
    rw [← hsolve, Matrix.mulVec_mulVec, whitener_gram_mul_fullLaplacian, Matrix.one_mulVec]
  have hquad : ((data.whitener)ᵀ *ᵥ data.graph.edgeVector edge)
      ⬝ᵥ ((data.whitener)ᵀ *ᵥ data.graph.edgeVector edge)
      = data.graph.edgeVector edge ⬝ᵥ potential := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hkey,
      dotProduct_comm]
  rw [leverageOf, ← dotProduct_self_eq_sum_sq, graphicDesign_atom, graphicAtom_eq_whitenedRow,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Real.mul_self_sqrt hratio, hquad]

/-! ## The cyclic drop calculus

A potential on the `(k+1)`-cycle is determined, up to grounding, by its `k+1`
arc drops, and the drops are exactly the zero-sum vectors.  `potentialOfDrops`
inverts that dictionary; it is the single construction behind every witness below.
-/

/-- The potential drop across arc `position` of the `(k+1)`-cycle: the grounded
potential at `position` minus its value at the next vertex. -/
def cycleDropAt (potential : Fin vertexRank → ℝ) (position : Fin (vertexRank + 1)) : ℝ :=
  groundedPotential potential position - groundedPotential potential (position + 1)

/-- The zero potential has zero drops. -/
theorem groundedPotential_zero :
    groundedPotential (0 : Fin vertexRank → ℝ) = 0 := by
  funext position
  induction position using Fin.lastCases with
  | last => rw [groundedPotential_last]; rfl
  | cast coord => rw [groundedPotential_castSucc]; rfl

/-- The drops of the zero potential all vanish. -/
theorem cycleDropAt_zero (position : Fin (vertexRank + 1)) :
    cycleDropAt (0 : Fin vertexRank → ℝ) position = 0 := by
  rw [cycleDropAt, groundedPotential_zero]
  simp

/-- A potential with a nonzero drop is nonzero. -/
theorem ne_zero_of_cycleDropAt_ne_zero {potential : Fin vertexRank → ℝ}
    {position : Fin (vertexRank + 1)} (hdrop : cycleDropAt potential position ≠ 0) :
    potential ≠ 0 := by
  intro hzero
  rw [hzero, cycleDropAt_zero] at hdrop
  exact hdrop rfl

/-- **Drops telescope**: going once around the cycle returns to the start. -/
theorem sum_cycleDropAt_eq_zero (potential : Fin vertexRank → ℝ) :
    ∑ position : Fin (vertexRank + 1), cycleDropAt potential position = 0 := by
  have hshift : ∑ position : Fin (vertexRank + 1),
        groundedPotential potential (position + 1)
      = ∑ position : Fin (vertexRank + 1), groundedPotential potential position :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin (vertexRank + 1)))
      (fun position => groundedPotential potential (position + 1))
      (fun position => groundedPotential potential position)
      (fun _ => rfl)
  simp only [cycleDropAt]
  rw [Finset.sum_sub_distrib, hshift, sub_self]

/-- The partial sum of a drop vector over the first `bound` arcs. -/
def dropPrefix (drops : Fin (vertexRank + 1) → ℝ) (bound : ℕ) : ℝ :=
  ∑ idx ∈ Finset.range bound, drops (cycleVertex vertexRank idx)

/-- Reading a cycle index back as itself. -/
theorem cycleVertex_val_self (position : Fin (vertexRank + 1)) :
    cycleVertex vertexRank position.val = position :=
  Fin.ext (cycleVertex_val_of_le (Nat.lt_succ_iff.mp position.isLt))

theorem dropPrefix_zero (drops : Fin (vertexRank + 1) → ℝ) : dropPrefix drops 0 = 0 := by
  rw [dropPrefix, Finset.range_zero, Finset.sum_empty]

theorem dropPrefix_succ (drops : Fin (vertexRank + 1) → ℝ) (bound : ℕ) :
    dropPrefix drops (bound + 1) = dropPrefix drops bound + drops (cycleVertex vertexRank bound) := by
  rw [dropPrefix, dropPrefix, Finset.sum_range_succ]

/-- The full prefix is the total drop sum. -/
theorem dropPrefix_full (drops : Fin (vertexRank + 1) → ℝ) :
    dropPrefix drops (vertexRank + 1) = ∑ position, drops position := by
  rw [dropPrefix, ← Fin.sum_univ_eq_sum_range (fun idx => drops (cycleVertex vertexRank idx))]
  exact Finset.sum_congr rfl fun position _ => by rw [cycleVertex_val_self]

/-- On a zero-sum drop vector the prefix through the last arc is minus that arc. -/
theorem dropPrefix_last (drops : Fin (vertexRank + 1) → ℝ)
    (hsum : ∑ position, drops position = 0) :
    dropPrefix drops vertexRank = - drops (Fin.last vertexRank) := by
  have hstep := dropPrefix_succ drops vertexRank
  rw [dropPrefix_full drops, hsum, cycleVertex_top] at hstep
  linarith

/-- **The potential of a drop vector**: the grounded antiderivative, normalized so
the ground vertex sits at zero. -/
def potentialOfDrops (drops : Fin (vertexRank + 1) → ℝ) : Fin vertexRank → ℝ :=
  fun coord => - dropPrefix drops coord.val - drops (Fin.last vertexRank)

/-- The grounded reading of `potentialOfDrops`, valid at the ground vertex too —
that is exactly where the zero-sum hypothesis is spent. -/
theorem groundedPotential_potentialOfDrops (drops : Fin (vertexRank + 1) → ℝ)
    (hsum : ∑ position, drops position = 0) (position : Fin (vertexRank + 1)) :
    groundedPotential (potentialOfDrops drops) position
      = - dropPrefix drops position.val - drops (Fin.last vertexRank) := by
  induction position using Fin.lastCases with
  | last =>
      rw [groundedPotential_last, Fin.val_last, dropPrefix_last drops hsum]
      ring
  | cast coord =>
      rw [groundedPotential_castSucc, potentialOfDrops, Fin.val_castSucc]

/-- **The drop dictionary is onto**: every zero-sum drop vector is realized. -/
theorem cycleDropAt_potentialOfDrops (drops : Fin (vertexRank + 1) → ℝ)
    (hsum : ∑ position, drops position = 0) (position : Fin (vertexRank + 1)) :
    cycleDropAt (potentialOfDrops drops) position = drops position := by
  rw [cycleDropAt, groundedPotential_potentialOfDrops drops hsum,
    groundedPotential_potentialOfDrops drops hsum]
  by_cases hlast : position = Fin.last vertexRank
  · subst hlast
    rw [Fin.last_add_one]
    have hzeroVal : ((0 : Fin (vertexRank + 1))).val = 0 := rfl
    rw [hzeroVal, dropPrefix_zero, Fin.val_last, dropPrefix_last drops hsum]
    ring
  · have hlt : position < Fin.last vertexRank :=
      lt_of_le_of_ne (Fin.le_last position) hlast
    rw [Fin.val_add_one_of_lt hlt, dropPrefix_succ, cycleVertex_val_self]
    ring

/-! ## Bundlings of the cycle -/

/-- The number of edges in bundle `position`. -/
def bundleSize (bundleOf : Fin edgeCount → Fin (vertexRank + 1))
    (position : Fin (vertexRank + 1)) : ℕ :=
  (Finset.univ.filter (fun edge => bundleOf edge = position)).card

/-- **Summing a bundle-constant quantity over edges** is summing it over bundles
with multiplicity.  The only place fibers of the bundle map are counted. -/
theorem sum_of_bundleValue (bundleOf : Fin edgeCount → Fin (vertexRank + 1))
    (edgeSet : Finset (Fin edgeCount)) (bundleValue : Fin (vertexRank + 1) → ℝ) :
    ∑ edge ∈ edgeSet, bundleValue (bundleOf edge)
      = ∑ position, ((edgeSet.filter (fun edge => bundleOf edge = position)).card : ℝ)
          * bundleValue position := by
  classical
  calc ∑ edge ∈ edgeSet, bundleValue (bundleOf edge)
      = ∑ edge ∈ edgeSet, ∑ position,
          (if bundleOf edge = position then bundleValue position else 0) := by
        refine Finset.sum_congr rfl fun edge _ => ?_
        rw [Finset.sum_ite_eq Finset.univ (bundleOf edge) bundleValue,
          if_pos (Finset.mem_univ _)]
    _ = ∑ position, ∑ edge ∈ edgeSet,
          (if bundleOf edge = position then bundleValue position else 0) := Finset.sum_comm
    _ = ∑ position, ((edgeSet.filter (fun edge => bundleOf edge = position)).card : ℝ)
          * bundleValue position := by
        refine Finset.sum_congr rfl fun position _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- The bundle sizes sum to the edge count. -/
theorem sum_bundleSize_cast (bundleOf : Fin edgeCount → Fin (vertexRank + 1)) :
    ∑ position, (bundleSize bundleOf position : ℝ) = (edgeCount : ℝ) := by
  have hsum := sum_of_bundleValue bundleOf Finset.univ (fun _ => (1 : ℝ))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun position _ => by rw [mul_one]; rfl

/-- A **cycle bundling**: every edge is assigned to one of the `k+1` arcs of the
`(k+1)`-cycle, and no arc is left empty. -/
structure CycleBundling (edgeCount vertexRank : ℕ) where
  /-- The arc each edge belongs to. -/
  bundleOf : Fin edgeCount → Fin (vertexRank + 1)
  /-- Every arc carries at least one edge. -/
  hasEdgeInEveryBundle : ∀ position, ∃ edge, bundleOf edge = position

namespace CycleBundling

/-- Every bundle is nonempty. -/
theorem bundleSize_pos (bundling : CycleBundling edgeCount vertexRank)
    (position : Fin (vertexRank + 1)) :
    0 < bundleSize bundling.bundleOf position := by
  obtain ⟨edge, hedge⟩ := bundling.hasEdgeInEveryBundle position
  exact Finset.card_pos.mpr ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge⟩⟩

/-- With at least two arcs, no bundle exhausts the edge set. -/
theorem bundleSize_lt (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (position : Fin (vertexRank + 1)) :
    bundleSize bundling.bundleOf position < edgeCount := by
  have hcard : 1 < Fintype.card (Fin (vertexRank + 1)) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨other, hother⟩ := Fintype.exists_ne_of_one_lt_card hcard position
  obtain ⟨edge, hedge⟩ := bundling.hasEdgeInEveryBundle other
  have hnotmem :
      edge ∉ Finset.univ.filter (fun candidate => bundling.bundleOf candidate = position) := by
    intro hmem
    exact hother (hedge.symm.trans (Finset.mem_filter.mp hmem).2)
  have hss : (Finset.univ.filter (fun candidate => bundling.bundleOf candidate = position))
      ⊂ (Finset.univ : Finset (Fin edgeCount)) :=
    Finset.ssubset_univ_iff.mpr fun heq => hnotmem (by rw [heq]; exact Finset.mem_univ edge)
  have hlt := Finset.card_lt_card hss
  rwa [Finset.card_univ, Fintype.card_fin] at hlt

/-- With at least two arcs there is at least one edge. -/
theorem edgeCount_pos (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) : 0 < edgeCount :=
  lt_of_le_of_lt (Nat.zero_le _) (bundling.bundleSize_lt hrank 0)

/-- The graph-induced conductance of a bundle: `1 / φ(p)` with `φ(x) = x(n − x)`. -/
noncomputable def graphInducedWeight (bundling : CycleBundling edgeCount vertexRank)
    (position : Fin (vertexRank + 1)) : ℝ :=
  ((bundleSize bundling.bundleOf position : ℝ)
    * ((edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ)))⁻¹

/-- The complementary bundle size is positive. -/
theorem coBundleSize_pos (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (position : Fin (vertexRank + 1)) :
    0 < (edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ) := by
  have hlt := bundling.bundleSize_lt hrank position
  have : ((bundleSize bundling.bundleOf position : ℕ) : ℝ) < (edgeCount : ℝ) := by
    exact_mod_cast hlt
  linarith

/-- The bundle size is positive as a real. -/
theorem bundleSize_pos_cast (bundling : CycleBundling edgeCount vertexRank)
    (position : Fin (vertexRank + 1)) :
    (0 : ℝ) < (bundleSize bundling.bundleOf position : ℝ) := by
  exact_mod_cast bundling.bundleSize_pos position

theorem graphInducedWeight_pos (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (position : Fin (vertexRank + 1)) :
    0 < bundling.graphInducedWeight position := by
  rw [graphInducedWeight]
  exact inv_pos.mpr (mul_pos (bundling.bundleSize_pos_cast position)
    (bundling.coBundleSize_pos hrank position))

end CycleBundling

/-- **The plain `(k+1)`-cycle bundling**: one edge per arc, at every rank.  This
is the inhabitant that makes the universally quantified statements below
non-vacuous — `CycleBundling edgeCount vertexRank` is empty whenever
`edgeCount < vertexRank + 1`, since `hasEdgeInEveryBundle` needs an injection of
the arcs into the edges. -/
def cycleBundlingWitness (vertexRank : ℕ) : CycleBundling (vertexRank + 1) vertexRank where
  bundleOf := id
  hasEdgeInEveryBundle := fun position => ⟨position, rfl⟩

/-- Every arc of the plain cycle carries exactly one edge. -/
theorem cycleBundlingWitness_bundleSize (vertexRank : ℕ) (position : Fin (vertexRank + 1)) :
    bundleSize (cycleBundlingWitness vertexRank).bundleOf position = 1 := by
  simp [bundleSize, cycleBundlingWitness, Finset.filter_eq']

/-- The bundled `(k+1)`-cycle: arc `j` runs from vertex `j` to vertex `j+1`, and
every edge of bundle `j` runs along arc `j`. -/
def bundledCycleGraph (bundleOf : Fin edgeCount → Fin (vertexRank + 1)) :
    MultigraphOnGround edgeCount vertexRank where
  edgeTail := bundleOf
  edgeHead := fun edge => bundleOf edge + 1

/-- Two edges with the same endpoints carry the same incidence row. -/
theorem edgeVector_congr {graph : MultigraphOnGround edgeCount vertexRank}
    {leftEdge rightEdge : Fin edgeCount}
    (htail : graph.edgeTail leftEdge = graph.edgeTail rightEdge)
    (hhead : graph.edgeHead leftEdge = graph.edgeHead rightEdge) :
    graph.edgeVector leftEdge = graph.edgeVector rightEdge := by
  funext coord
  simp only [MultigraphOnGround.edgeVector, htail, hhead]

/-- Edges of the same bundle carry the same incidence row. -/
theorem bundledCycleGraph_edgeVector_congr (bundleOf : Fin edgeCount → Fin (vertexRank + 1))
    {leftEdge rightEdge : Fin edgeCount} (hsame : bundleOf leftEdge = bundleOf rightEdge) :
    (bundledCycleGraph bundleOf).edgeVector leftEdge
      = (bundledCycleGraph bundleOf).edgeVector rightEdge :=
  edgeVector_congr (graph := bundledCycleGraph bundleOf) hsame
    (by show bundleOf leftEdge + 1 = bundleOf rightEdge + 1; rw [hsame])

/-- **The edge form of the bundled cycle**: the drop across an edge is the drop
across its arc. -/
theorem bundledCycleGraph_edgeVector_dotProduct
    (bundleOf : Fin edgeCount → Fin (vertexRank + 1)) (edge : Fin edgeCount)
    (potential : Fin vertexRank → ℝ) :
    (bundledCycleGraph bundleOf).edgeVector edge ⬝ᵥ potential
      = cycleDropAt potential (bundleOf edge) := by
  rw [edgeVector_dotProduct]
  rfl

/-- Consecutive arcs are adjacent, since every bundle is nonempty. -/
theorem bundledCycle_reachable_from_zero (bundling : CycleBundling edgeCount vertexRank)
    (vertex : Fin (vertexRank + 1)) :
    IsEdgeReachable (bundledCycleGraph bundling.bundleOf) Finset.univ 0 vertex := by
  induction vertex using Fin.induction with
  | zero => exact Relation.ReflTransGen.refl
  | succ innerIndex ihead =>
      obtain ⟨edge, hedge⟩ := bundling.hasEdgeInEveryBundle innerIndex.castSucc
      have hadj : IsEdgeAdjacent (bundledCycleGraph bundling.bundleOf) Finset.univ
          innerIndex.castSucc innerIndex.succ := by
        refine ⟨edge, Finset.mem_univ _, Or.inl ⟨hedge, ?_⟩⟩
        show bundling.bundleOf edge + 1 = innerIndex.succ
        rw [hedge, Fin.coeSucc_eq_succ]
      exact ihead.tail hadj

/-- The bundled cycle is connected. -/
theorem bundledCycle_isGroundConnected (bundling : CycleBundling edgeCount vertexRank) :
    IsGroundConnected (bundledCycleGraph bundling.bundleOf) Finset.univ := fun vertex =>
  (isEdgeReachable_symm (bundledCycle_reachable_from_zero bundling (Fin.last vertexRank))).trans
    (bundledCycle_reachable_from_zero bundling vertex)

/-- **The graph-induced bundled-cycle data**: uniform design weight `1/n`, and
conductance `1/φ(p_j)` on every edge of bundle `j`. -/
noncomputable def bundledCycleData (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) : GraphDesignData edgeCount vertexRank where
  graph := bundledCycleGraph bundling.bundleOf
  conductance := fun edge => bundling.graphInducedWeight (bundling.bundleOf edge)
  conductance_pos := fun edge => bundling.graphInducedWeight_pos hrank _
  weight := fun _ => ((edgeCount : ℝ))⁻¹
  weight_pos := fun _ => by
    have := bundling.edgeCount_pos hrank
    have hpos : (0 : ℝ) < (edgeCount : ℝ) := by exact_mod_cast this
    exact inv_pos.mpr hpos
  weight_sum_one := by
    have hne : ((edgeCount : ℝ)) ≠ 0 := by
      have := bundling.edgeCount_pos hrank
      have hpos : (0 : ℝ) < (edgeCount : ℝ) := by exact_mod_cast this
      exact ne_of_gt hpos
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hne]
  isGroundConnected := bundledCycle_isGroundConnected bundling

/-- **The graph-induced bundled-cycle design.**  Parseval holds because
`graphicDesign` supplies it; this is a genuine `WeightedDesign` at every rank. -/
noncomputable def bundledCycleDesign (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) : WeightedDesign edgeCount vertexRank :=
  graphicDesign (bundledCycleData bundling hrank)

theorem bundledCycleDesign_weight (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (edge : Fin edgeCount) :
    (bundledCycleDesign bundling hrank).weight edge = ((edgeCount : ℝ))⁻¹ := rfl

/-- **Atoms inside a bundle are equal.**  Not merely parallel: the design's atom
depends on the edge only through its arc, so the atoms cluster into exactly
`k + 1` groups of identical vectors. -/
theorem bundledCycle_atom_eq_of_sameBundle (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) {leftEdge rightEdge : Fin edgeCount}
    (hsame : bundling.bundleOf leftEdge = bundling.bundleOf rightEdge) :
    (bundledCycleDesign bundling hrank).atom leftEdge
      = (bundledCycleDesign bundling hrank).atom rightEdge := by
  have hcond : (bundledCycleData bundling hrank).conductance leftEdge
      = (bundledCycleData bundling hrank).conductance rightEdge := by
    show bundling.graphInducedWeight (bundling.bundleOf leftEdge)
      = bundling.graphInducedWeight (bundling.bundleOf rightEdge)
    rw [hsame]
  have hvec : (bundledCycleData bundling hrank).graph.edgeVector leftEdge
      = (bundledCycleData bundling hrank).graph.edgeVector rightEdge :=
    bundledCycleGraph_edgeVector_congr bundling.bundleOf hsame
  rw [bundledCycleDesign, graphicDesign_atom, graphicDesign_atom, graphicAtom_eq_whitenedRow,
    graphicAtom_eq_whitenedRow, hcond, hvec,
    show (bundledCycleData bundling hrank).weight leftEdge
      = (bundledCycleData bundling hrank).weight rightEdge from rfl]

/-! ## The Dirichlet forms of the bundled cycle, read arc by arc -/

/-- The conductance the domination inequality actually sees is `n / φ(p)`. -/
theorem bundledCycleData_selected_conductance (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (edge : Fin edgeCount) :
    (bundledCycleData bundling hrank).conductance edge
        / (bundledCycleData bundling hrank).weight edge
      = (edgeCount : ℝ) * bundling.graphInducedWeight (bundling.bundleOf edge) := by
  show bundling.graphInducedWeight (bundling.bundleOf edge) / ((edgeCount : ℝ))⁻¹ = _
  rw [div_eq_mul_inv, inv_inv, mul_comm]

/-- **The selected Dirichlet form**, one term per selected edge. -/
theorem bundledCycle_selectedLaplacian_form (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (edgeSet : Finset (Fin edgeCount))
    (potential : Fin vertexRank → ℝ) :
    potential ⬝ᵥ ((bundledCycleData bundling hrank).selectedLaplacian edgeSet *ᵥ potential)
      = ∑ edge ∈ edgeSet, (edgeCount : ℝ)
          * bundling.graphInducedWeight (bundling.bundleOf edge)
          * (cycleDropAt potential (bundling.bundleOf edge)) ^ 2 := by
  rw [GraphDesignData.selectedLaplacian, laplacianOn_form]
  refine Finset.sum_congr rfl fun edge _ => ?_
  rw [show groundedPotential potential
        ((bundledCycleData bundling hrank).graph.edgeTail edge)
        - groundedPotential potential ((bundledCycleData bundling hrank).graph.edgeHead edge)
      = cycleDropAt potential (bundling.bundleOf edge) from rfl,
    bundledCycleData_selected_conductance]

/-- Summing a bundle-constant quantity over all edges. -/
theorem sum_of_bundleValue_univ (bundleOf : Fin edgeCount → Fin (vertexRank + 1))
    (bundleValue : Fin (vertexRank + 1) → ℝ) :
    ∑ edge, bundleValue (bundleOf edge)
      = ∑ position, (bundleSize bundleOf position : ℝ) * bundleValue position :=
  sum_of_bundleValue bundleOf Finset.univ bundleValue

/-- **The full Dirichlet form, polarized**: one term per arc, with the
`φ`-conductance collapsing the bundle multiplicity into `1 / (n − p_j)`. -/
theorem bundledCycle_fullLaplacian_bilinear (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (leftPotential rightPotential : Fin vertexRank → ℝ) :
    leftPotential ⬝ᵥ ((bundledCycleData bundling hrank).fullLaplacian *ᵥ rightPotential)
      = ∑ position, cycleDropAt leftPotential position * cycleDropAt rightPotential position
          / ((edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ)) := by
  rw [GraphDesignData.fullLaplacian, laplacianOn_bilinear]
  calc ∑ edge, (bundledCycleData bundling hrank).conductance edge
          * ((bundledCycleData bundling hrank).graph.edgeVector edge ⬝ᵥ leftPotential)
          * ((bundledCycleData bundling hrank).graph.edgeVector edge ⬝ᵥ rightPotential)
      = ∑ edge, (fun position => bundling.graphInducedWeight position
          * cycleDropAt leftPotential position * cycleDropAt rightPotential position)
          (bundling.bundleOf edge) :=
        Finset.sum_congr rfl fun edge _ => by
          rw [show (bundledCycleData bundling hrank).graph.edgeVector edge
              = (bundledCycleGraph bundling.bundleOf).edgeVector edge from rfl,
            bundledCycleGraph_edgeVector_dotProduct,
            bundledCycleGraph_edgeVector_dotProduct]
          rfl
    _ = ∑ position, (bundleSize bundling.bundleOf position : ℝ)
          * (bundling.graphInducedWeight position * cycleDropAt leftPotential position
            * cycleDropAt rightPotential position) :=
        sum_of_bundleValue_univ bundling.bundleOf
          (fun position => bundling.graphInducedWeight position
            * cycleDropAt leftPotential position * cycleDropAt rightPotential position)
    _ = ∑ position, cycleDropAt leftPotential position * cycleDropAt rightPotential position
          / ((edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ)) := by
        refine Finset.sum_congr rfl fun position _ => ?_
        have hsize := bundling.bundleSize_pos_cast position
        have hco := bundling.coBundleSize_pos hrank position
        rw [CycleBundling.graphInducedWeight]
        field_simp

/-- **The full Dirichlet form**: `Σ_j d_j² / (n − p_j)`. -/
theorem bundledCycle_fullLaplacian_form (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (potential : Fin vertexRank → ℝ) :
    potential ⬝ᵥ ((bundledCycleData bundling hrank).fullLaplacian *ᵥ potential)
      = ∑ position, (cycleDropAt potential position) ^ 2
          / ((edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ)) := by
  rw [bundledCycle_fullLaplacian_bilinear]
  exact Finset.sum_congr rfl fun position _ => by rw [← pow_two]

/-! ## The gap is the Engel deficiency -/

/-- **The exact gap identity.**  For an edge set carrying one edge from each arc
but `dropped`, the Loewner gap against the whole design is Sedrakyan/Engel's
deficiency in the arc drops.  Everything downstream — the `⪰` half, the
zero-margin half, the rank-2 slack — is read off this one line. -/
theorem bundledCycle_gap_eq_engelDeficiency (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) {edgeSet : Finset (Fin edgeCount)}
    {dropped : Fin (vertexRank + 1)}
    (hinj : Set.InjOn bundling.bundleOf ↑edgeSet)
    (himage : edgeSet.image bundling.bundleOf = Finset.univ.erase dropped)
    (potential : Fin vertexRank → ℝ) :
    potential ⬝ᵥ (((bundledCycleData bundling hrank).selectedLaplacian edgeSet
        - (bundledCycleData bundling hrank).fullLaplacian) *ᵥ potential)
      = (∑ position ∈ Finset.univ.erase dropped,
            (cycleDropAt potential position) ^ 2 / (bundleSize bundling.bundleOf position : ℝ))
        - (∑ position ∈ Finset.univ.erase dropped, cycleDropAt potential position) ^ 2
          / (∑ position ∈ Finset.univ.erase dropped,
              (bundleSize bundling.bundleOf position : ℝ)) := by
  have hselected : potential ⬝ᵥ
        ((bundledCycleData bundling hrank).selectedLaplacian edgeSet *ᵥ potential)
      = ∑ position ∈ Finset.univ.erase dropped, (edgeCount : ℝ)
          * bundling.graphInducedWeight position * (cycleDropAt potential position) ^ 2 := by
    rw [bundledCycle_selectedLaplacian_form]
    calc ∑ edge ∈ edgeSet, (edgeCount : ℝ)
            * bundling.graphInducedWeight (bundling.bundleOf edge)
            * (cycleDropAt potential (bundling.bundleOf edge)) ^ 2
        = ∑ position ∈ edgeSet.image bundling.bundleOf, (edgeCount : ℝ)
            * bundling.graphInducedWeight position * (cycleDropAt potential position) ^ 2 :=
          (Finset.sum_image (f := fun position => (edgeCount : ℝ)
            * bundling.graphInducedWeight position * (cycleDropAt potential position) ^ 2)
            hinj).symm
      _ = ∑ position ∈ Finset.univ.erase dropped, (edgeCount : ℝ)
            * bundling.graphInducedWeight position * (cycleDropAt potential position) ^ 2 := by
          rw [himage]
  have hfull : potential ⬝ᵥ
        ((bundledCycleData bundling hrank).fullLaplacian *ᵥ potential)
      = (∑ position ∈ Finset.univ.erase dropped, (cycleDropAt potential position) ^ 2
            / ((edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ)))
        + (cycleDropAt potential dropped) ^ 2
            / ((edgeCount : ℝ) - (bundleSize bundling.bundleOf dropped : ℝ)) := by
    rw [bundledCycle_fullLaplacian_form,
      ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ dropped)]
  have hsumdiff : (∑ position ∈ Finset.univ.erase dropped, (edgeCount : ℝ)
          * bundling.graphInducedWeight position * (cycleDropAt potential position) ^ 2)
        - (∑ position ∈ Finset.univ.erase dropped, (cycleDropAt potential position) ^ 2
            / ((edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ)))
      = ∑ position ∈ Finset.univ.erase dropped,
          (cycleDropAt potential position) ^ 2 / (bundleSize bundling.bundleOf position : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun position _ => ?_
    have hsize := bundling.bundleSize_pos_cast position
    have hco := bundling.coBundleSize_pos hrank position
    rw [CycleBundling.graphInducedWeight]
    field_simp
  have hdropSum : ∑ position ∈ Finset.univ.erase dropped, cycleDropAt potential position
      = - cycleDropAt potential dropped := by
    have htot := sum_cycleDropAt_eq_zero potential
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ dropped)] at htot
    linarith
  have hsizeSum : ∑ position ∈ Finset.univ.erase dropped,
        (bundleSize bundling.bundleOf position : ℝ)
      = (edgeCount : ℝ) - (bundleSize bundling.bundleOf dropped : ℝ) := by
    have htot := sum_bundleSize_cast bundling.bundleOf
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ dropped)] at htot
    linarith
  rw [Matrix.sub_mulVec, dotProduct_sub, hselected, hfull, hdropSum, hsizeSum, ← hsumdiff]
  ring

/-- **The gap is nonnegative** — Sedrakyan's lemma, applied once. -/
theorem bundledCycle_gap_nonneg (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) {edgeSet : Finset (Fin edgeCount)}
    {dropped : Fin (vertexRank + 1)}
    (hinj : Set.InjOn bundling.bundleOf ↑edgeSet)
    (himage : edgeSet.image bundling.bundleOf = Finset.univ.erase dropped)
    (potential : Fin vertexRank → ℝ) :
    0 ≤ potential ⬝ᵥ (((bundledCycleData bundling hrank).selectedLaplacian edgeSet
        - (bundledCycleData bundling hrank).fullLaplacian) *ᵥ potential) := by
  rw [bundledCycle_gap_eq_engelDeficiency bundling hrank hinj himage]
  have hengel := Finset.sq_sum_div_le_sum_sq_div (Finset.univ.erase dropped)
    (fun position => cycleDropAt potential position)
    (g := fun position => (bundleSize bundling.bundleOf position : ℝ))
    (fun position _ => bundling.bundleSize_pos_cast position)
  linarith

/-- **The bundled cycle dominates** on every bundle transversal. -/
theorem bundledCycle_dominates (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) {edgeSet : Finset (Fin edgeCount)}
    {dropped : Fin (vertexRank + 1)}
    (hinj : Set.InjOn bundling.bundleOf ↑edgeSet)
    (himage : edgeSet.image bundling.bundleOf = Finset.univ.erase dropped) :
    Dominates (bundledCycleDesign bundling hrank) edgeSet := by
  rw [bundledCycleDesign, graphicDesign_dominates_iff]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq ?_, fun potential => ?_⟩
  · rw [Matrix.transpose_sub, (bundledCycleData bundling hrank).selectedLaplacian_transpose,
      (bundledCycleData bundling hrank).fullLaplacian_transpose]
  · rw [star_trivial]
    exact bundledCycle_gap_nonneg bundling hrank hinj himage potential

/-! ## The transversals -/

/-- A choice of one edge out of each arc. -/
noncomputable def bundleSection (bundling : CycleBundling edgeCount vertexRank)
    (position : Fin (vertexRank + 1)) : Fin edgeCount :=
  Classical.choose (bundling.hasEdgeInEveryBundle position)

theorem bundleSection_spec (bundling : CycleBundling edgeCount vertexRank)
    (position : Fin (vertexRank + 1)) :
    bundling.bundleOf (bundleSection bundling position) = position :=
  Classical.choose_spec (bundling.hasEdgeInEveryBundle position)

theorem bundleSection_injective (bundling : CycleBundling edgeCount vertexRank) :
    Function.Injective (bundleSection bundling) := by
  intro leftPosition rightPosition heq
  have hleft := bundleSection_spec bundling leftPosition
  rw [heq, bundleSection_spec bundling rightPosition] at hleft
  exact hleft.symm

/-- **The spanning tree that omits arc `dropped`**: one edge from each surviving
arc. -/
noncomputable def bundledCycleTree (bundling : CycleBundling edgeCount vertexRank)
    (dropped : Fin (vertexRank + 1)) : Finset (Fin edgeCount) :=
  (Finset.univ.erase dropped).image (bundleSection bundling)

theorem bundledCycleTree_card (bundling : CycleBundling edgeCount vertexRank)
    (dropped : Fin (vertexRank + 1)) :
    (bundledCycleTree bundling dropped).card = vertexRank := by
  rw [bundledCycleTree, Finset.card_image_of_injective _ (bundleSection_injective bundling),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

theorem bundledCycleTree_injOn (bundling : CycleBundling edgeCount vertexRank)
    (dropped : Fin (vertexRank + 1)) :
    Set.InjOn bundling.bundleOf ↑(bundledCycleTree bundling dropped) := by
  intro leftEdge hleft rightEdge hright heq
  rw [bundledCycleTree, Finset.coe_image] at hleft hright
  obtain ⟨leftPosition, _, rfl⟩ := hleft
  obtain ⟨rightPosition, _, rfl⟩ := hright
  rw [bundleSection_spec, bundleSection_spec] at heq
  rw [heq]

theorem bundledCycleTree_image (bundling : CycleBundling edgeCount vertexRank)
    (dropped : Fin (vertexRank + 1)) :
    (bundledCycleTree bundling dropped).image bundling.bundleOf = Finset.univ.erase dropped := by
  rw [bundledCycleTree, Finset.image_image,
    show bundling.bundleOf ∘ bundleSection bundling = id from
      funext fun position => bundleSection_spec bundling position,
    Finset.image_id]

/-- The transversal dominates. -/
theorem bundledCycleTree_dominates (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (dropped : Fin (vertexRank + 1)) :
    Dominates (bundledCycleDesign bundling hrank) (bundledCycleTree bundling dropped) :=
  bundledCycle_dominates bundling hrank (bundledCycleTree_injOn bundling dropped)
    (bundledCycleTree_image bundling dropped)

/-- The transversal really is a spanning tree of the bundled cycle. -/
theorem bundledCycleTree_isSpanningTree (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (dropped : Fin (vertexRank + 1)) :
    IsSpanningTree (bundledCycleData bundling hrank).graph (bundledCycleTree bundling dropped) :=
  isSpanningTree_of_dominates (bundledCycleData bundling hrank)
    (bundledCycleTree_card bundling dropped) (bundledCycleTree_dominates bundling hrank dropped)

/-! ## The margin is exactly zero: no `k`-subset dominates strictly -/

/-- The tight drop vector: proportional to the bundle sizes off `dropped`, and
carrying the whole return current on `dropped`.  This is the ray on which
Sedrakyan's inequality is an equality. -/
noncomputable def bundleTightDrops (bundling : CycleBundling edgeCount vertexRank)
    (dropped : Fin (vertexRank + 1)) : Fin (vertexRank + 1) → ℝ :=
  fun position => if position = dropped
    then -((edgeCount : ℝ) - (bundleSize bundling.bundleOf dropped : ℝ))
    else (bundleSize bundling.bundleOf position : ℝ)

theorem sum_bundleTightDrops (bundling : CycleBundling edgeCount vertexRank)
    (dropped : Fin (vertexRank + 1)) :
    ∑ position, bundleTightDrops bundling dropped position = 0 := by
  have hoff : ∀ position ∈ Finset.univ.erase dropped,
      bundleTightDrops bundling dropped position
        = (bundleSize bundling.bundleOf position : ℝ) := by
    intro position hmem
    rw [bundleTightDrops, if_neg (Finset.ne_of_mem_erase hmem)]
  have hsize := sum_bundleSize_cast bundling.bundleOf
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ dropped)] at hsize
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ dropped),
    Finset.sum_congr rfl hoff, bundleTightDrops, if_pos rfl]
  linarith

theorem erase_nonempty_of_rank (hrank : 1 ≤ vertexRank) (dropped : Fin (vertexRank + 1)) :
    (Finset.univ.erase dropped).Nonempty := by
  refine Finset.card_pos.mp ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- The tight potential is nonzero: its drop across the omitted arc is the whole
return current. -/
theorem bundleTightPotential_ne_zero (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (dropped : Fin (vertexRank + 1)) :
    potentialOfDrops (bundleTightDrops bundling dropped) ≠ 0 := by
  refine ne_zero_of_cycleDropAt_ne_zero (position := dropped) ?_
  rw [cycleDropAt_potentialOfDrops _ (sum_bundleTightDrops bundling dropped), bundleTightDrops,
    if_pos rfl]
  exact neg_ne_zero.mpr (ne_of_gt (bundling.coBundleSize_pos hrank dropped))

/-- **The margin vanishes on the tight ray.**  The Engel deficiency is zero at
the drop vector proportional to the bundle sizes, so the domination above is not
strict — at any rank, for any bundle sizes. -/
theorem bundledCycle_gap_eq_zero_at_tight (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) {edgeSet : Finset (Fin edgeCount)}
    {dropped : Fin (vertexRank + 1)}
    (hinj : Set.InjOn bundling.bundleOf ↑edgeSet)
    (himage : edgeSet.image bundling.bundleOf = Finset.univ.erase dropped) :
    potentialOfDrops (bundleTightDrops bundling dropped) ⬝ᵥ
        (((bundledCycleData bundling hrank).selectedLaplacian edgeSet
          - (bundledCycleData bundling hrank).fullLaplacian)
        *ᵥ potentialOfDrops (bundleTightDrops bundling dropped)) = 0 := by
  have hoff : ∀ position ∈ Finset.univ.erase dropped,
      cycleDropAt (potentialOfDrops (bundleTightDrops bundling dropped)) position
        = (bundleSize bundling.bundleOf position : ℝ) := by
    intro position hmem
    rw [cycleDropAt_potentialOfDrops _ (sum_bundleTightDrops bundling dropped),
      bundleTightDrops, if_neg (Finset.ne_of_mem_erase hmem)]
  have hfirst : (∑ position ∈ Finset.univ.erase dropped,
        (cycleDropAt (potentialOfDrops (bundleTightDrops bundling dropped)) position) ^ 2
          / (bundleSize bundling.bundleOf position : ℝ))
      = ∑ position ∈ Finset.univ.erase dropped,
          (bundleSize bundling.bundleOf position : ℝ) := by
    refine Finset.sum_congr rfl fun position hmem => ?_
    rw [hoff position hmem, pow_two, mul_div_assoc,
      div_self (ne_of_gt (bundling.bundleSize_pos_cast position)), mul_one]
  have hsecond : (∑ position ∈ Finset.univ.erase dropped,
        cycleDropAt (potentialOfDrops (bundleTightDrops bundling dropped)) position)
      = ∑ position ∈ Finset.univ.erase dropped,
          (bundleSize bundling.bundleOf position : ℝ) :=
    Finset.sum_congr rfl hoff
  have hpos : (0 : ℝ) < ∑ position ∈ Finset.univ.erase dropped,
      (bundleSize bundling.bundleOf position : ℝ) :=
    Finset.sum_pos (fun position _ => bundling.bundleSize_pos_cast position)
      (erase_nonempty_of_rank hrank dropped)
  rw [bundledCycle_gap_eq_engelDeficiency bundling hrank hinj himage, hfirst, hsecond, pow_two,
    mul_div_assoc, div_self (ne_of_gt hpos), mul_one, sub_self]

/-- The separating drop vector for an edge set that misses two arcs: unit current
in at one missed arc and out at the other. -/
def bundleSeparatingDrops (firstMissed secondMissed : Fin (vertexRank + 1)) :
    Fin (vertexRank + 1) → ℝ :=
  fun position => (if position = firstMissed then (1 : ℝ) else 0)
    - (if position = secondMissed then (1 : ℝ) else 0)

theorem sum_bundleSeparatingDrops (firstMissed secondMissed : Fin (vertexRank + 1)) :
    ∑ position, bundleSeparatingDrops firstMissed secondMissed position = 0 := by
  simp only [bundleSeparatingDrops]
  rw [Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ firstMissed (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ secondMissed (fun _ => (1 : ℝ)),
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), sub_self]

theorem bundleSeparatingDrops_eq_zero {firstMissed secondMissed position : Fin (vertexRank + 1)}
    (hfirst : position ≠ firstMissed) (hsecond : position ≠ secondMissed) :
    bundleSeparatingDrops firstMissed secondMissed position = 0 := by
  rw [bundleSeparatingDrops, if_neg hfirst, if_neg hsecond, sub_self]

/-- **A `k`-subset missing two arcs does not dominate strictly** — it does not
dominate at all: the separating potential is annihilated by the selected
Laplacian while the full Laplacian is positive definite. -/
theorem bundledCycle_not_posDef_of_missesTwo (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) {edgeSet : Finset (Fin edgeCount)}
    {firstMissed secondMissed : Fin (vertexRank + 1)} (hdistinct : firstMissed ≠ secondMissed)
    (hfirst : firstMissed ∉ edgeSet.image bundling.bundleOf)
    (hsecond : secondMissed ∉ edgeSet.image bundling.bundleOf) :
    ¬ (subsetSum (bundledCycleDesign bundling hrank) edgeSet - 1).PosDef := by
  intro hposDef
  rw [bundledCycleDesign, graphicDesign_posDef_iff] at hposDef
  have hdrop : ∀ position,
      cycleDropAt (potentialOfDrops (bundleSeparatingDrops firstMissed secondMissed)) position
        = bundleSeparatingDrops firstMissed secondMissed position :=
    cycleDropAt_potentialOfDrops _ (sum_bundleSeparatingDrops firstMissed secondMissed)
  have hne_zero : potentialOfDrops (bundleSeparatingDrops firstMissed secondMissed) ≠ 0 := by
    refine ne_zero_of_cycleDropAt_ne_zero (position := firstMissed) ?_
    rw [hdrop, bundleSeparatingDrops, if_pos rfl, if_neg hdistinct]
    norm_num
  have hselected : potentialOfDrops (bundleSeparatingDrops firstMissed secondMissed) ⬝ᵥ
      ((bundledCycleData bundling hrank).selectedLaplacian edgeSet
        *ᵥ potentialOfDrops (bundleSeparatingDrops firstMissed secondMissed)) = 0 := by
    rw [bundledCycle_selectedLaplacian_form]
    refine Finset.sum_eq_zero fun edge hmem => ?_
    have hin : bundling.bundleOf edge ∈ edgeSet.image bundling.bundleOf :=
      Finset.mem_image_of_mem _ hmem
    have hfirstNe : bundling.bundleOf edge ≠ firstMissed := by
      intro heq; rw [heq] at hin; exact hfirst hin
    have hsecondNe : bundling.bundleOf edge ≠ secondMissed := by
      intro heq; rw [heq] at hin; exact hsecond hin
    rw [hdrop, bundleSeparatingDrops_eq_zero hfirstNe hsecondNe]
    ring
  have hfullPos : 0 < potentialOfDrops (bundleSeparatingDrops firstMissed secondMissed) ⬝ᵥ
      ((bundledCycleData bundling hrank).fullLaplacian
        *ᵥ potentialOfDrops (bundleSeparatingDrops firstMissed secondMissed)) := by
    have hres := (Matrix.posDef_iff_dotProduct_mulVec.mp
      (bundledCycleData bundling hrank).posDef_fullLaplacian).2 hne_zero
    rwa [star_trivial] at hres
  have hgap := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hne_zero
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hselected] at hgap
  linarith

/-- **No `k`-subset dominates strictly**, at any rank and for any bundle sizes.
Either the bundle map is injective on the subset — and then the subset misses
exactly one arc, and the tight ray kills the margin — or it is not, and then the
subset misses two arcs and fails to dominate at all. -/
theorem bundledCycle_not_posDef (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (edgeSet : Finset (Fin edgeCount))
    (hcard : edgeSet.card = vertexRank) :
    ¬ (subsetSum (bundledCycleDesign bundling hrank) edgeSet - 1).PosDef := by
  classical
  by_cases hinjCard : (edgeSet.image bundling.bundleOf).card = edgeSet.card
  · have hinj : Set.InjOn bundling.bundleOf ↑edgeSet := Finset.card_image_iff.mp hinjCard
    have himageCard : (edgeSet.image bundling.bundleOf).card = vertexRank := by
      rw [hinjCard, hcard]
    have hcomplCard : ((edgeSet.image bundling.bundleOf)ᶜ).card = 1 := by
      rw [Finset.card_compl, himageCard, Fintype.card_fin]
      omega
    obtain ⟨dropped, hdropped⟩ := Finset.card_eq_one.mp hcomplCard
    have himage : edgeSet.image bundling.bundleOf = Finset.univ.erase dropped := by
      rw [← Finset.compl_singleton, ← hdropped, compl_compl]
    intro hposDef
    rw [bundledCycleDesign, graphicDesign_posDef_iff] at hposDef
    have hgap := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2
      (bundleTightPotential_ne_zero bundling hrank dropped)
    rw [star_trivial, bundledCycle_gap_eq_zero_at_tight bundling hrank hinj himage] at hgap
    exact lt_irrefl 0 hgap
  · have hle := Finset.card_image_le (s := edgeSet) (f := bundling.bundleOf)
    have hcomplCard : 1 < ((edgeSet.image bundling.bundleOf)ᶜ).card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨firstMissed, hfirstMem, secondMissed, hsecondMem, hdistinct⟩ :=
      Finset.one_lt_card.mp hcomplCard
    exact bundledCycle_not_posDef_of_missesTwo bundling hrank hdistinct
      (Finset.mem_compl.mp hfirstMem) (Finset.mem_compl.mp hsecondMem)

/-- **The value is exactly 1.**  The two halves packaged as `Gtz.IsTie`: some
`k`-subset dominates, and none dominates strictly.  So the graph-induced bundled
cycle sits on the boundary of the `GtzWeighted` feasible region at every rank —
an obstruction to any strictly-positive certificate. -/
theorem bundledCycle_isTie (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) : IsTie (bundledCycleDesign bundling hrank) :=
  ⟨⟨bundledCycleTree bundling 0, bundledCycleTree_card bundling 0,
      bundledCycleTree_dominates bundling hrank 0⟩,
    fun edgeSet hcard => bundledCycle_not_posDef bundling hrank edgeSet hcard⟩

/-! ## The leverage of an arc, in closed form

The leverage of an edge is the conductance-to-weight ratio times the drop of the
unit-current potential across it.  On the bundled cycle that potential is
explicit: a constant circulating current plus one unit through the injected arc.
Nothing is inverted; the identification `L y = b_e` is checked against the
polarized Dirichlet form, where it collapses to the telescoping identity.
-/

/-- The circulating current of the unit injection across a bundle: `(n − p_a)/(k n)`. -/
noncomputable def bundleCurrentScale (bundling : CycleBundling edgeCount vertexRank)
    (source : Fin (vertexRank + 1)) : ℝ :=
  ((edgeCount : ℝ) - (bundleSize bundling.bundleOf source : ℝ))
    / ((vertexRank : ℝ) * (edgeCount : ℝ))

/-- The drops of the unit-current potential injected across arc `source`. -/
noncomputable def bundleCurrentDrops (bundling : CycleBundling edgeCount vertexRank)
    (source : Fin (vertexRank + 1)) : Fin (vertexRank + 1) → ℝ :=
  fun position =>
    ((if position = source then (1 : ℝ) else 0) - bundleCurrentScale bundling source)
      * ((edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ))

/-- The complementary bundle sizes sum to `k n` — the total cycle resistance. -/
theorem sum_coBundleSize (bundling : CycleBundling edgeCount vertexRank) :
    ∑ position, ((edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ))
      = (vertexRank : ℝ) * (edgeCount : ℝ) := by
  rw [Finset.sum_sub_distrib, sum_bundleSize_cast, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem sum_bundleCurrentDrops (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (source : Fin (vertexRank + 1)) :
    ∑ position, bundleCurrentDrops bundling source position = 0 := by
  have hrankNe : ((vertexRank : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (vertexRank : ℝ) := by exact_mod_cast hrank
    exact ne_of_gt this
  have hedgeNe : ((edgeCount : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (edgeCount : ℝ) := by exact_mod_cast bundling.edgeCount_pos hrank
    exact ne_of_gt this
  have hsplit : ∀ position : Fin (vertexRank + 1),
      bundleCurrentDrops bundling source position
        = (if position = source
            then ((edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ)) else 0)
          - bundleCurrentScale bundling source
            * ((edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ)) := by
    intro position
    rw [bundleCurrentDrops, sub_mul]
    congr 1
    split <;> ring
  rw [Finset.sum_congr rfl (fun position _ => hsplit position), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ source
      (fun position => (edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ)),
    if_pos (Finset.mem_univ _), ← Finset.mul_sum, sum_coBundleSize, bundleCurrentScale]
  field_simp
  ring

/-- **The unit-current potential really solves `L y = b_e`.**  Checked against
the polarized Dirichlet form, where every arc contributes `d_j(u) · ([j = a] − c)`
and the constant part is killed by telescoping. -/
theorem bundleCurrent_solves (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (edge : Fin edgeCount) :
    (bundledCycleData bundling hrank).fullLaplacian
        *ᵥ potentialOfDrops (bundleCurrentDrops bundling (bundling.bundleOf edge))
      = (bundledCycleData bundling hrank).graph.edgeVector edge := by
  refine dotProduct_eq _ _ fun testPotential => ?_
  have hedgeForm : (bundledCycleData bundling hrank).graph.edgeVector edge ⬝ᵥ testPotential
      = cycleDropAt testPotential (bundling.bundleOf edge) :=
    bundledCycleGraph_edgeVector_dotProduct bundling.bundleOf edge testPotential
  rw [dotProduct_comm ((bundledCycleData bundling hrank).fullLaplacian
      *ᵥ potentialOfDrops (bundleCurrentDrops bundling (bundling.bundleOf edge))) testPotential,
    bundledCycle_fullLaplacian_bilinear, hedgeForm]
  have hdrop : ∀ position,
      cycleDropAt
          (potentialOfDrops (bundleCurrentDrops bundling (bundling.bundleOf edge))) position
        = bundleCurrentDrops bundling (bundling.bundleOf edge) position :=
    cycleDropAt_potentialOfDrops _ (sum_bundleCurrentDrops bundling hrank _)
  have hterm : ∀ position : Fin (vertexRank + 1),
      cycleDropAt testPotential position
          * cycleDropAt
              (potentialOfDrops (bundleCurrentDrops bundling (bundling.bundleOf edge))) position
          / ((edgeCount : ℝ) - (bundleSize bundling.bundleOf position : ℝ))
        = (if position = bundling.bundleOf edge then cycleDropAt testPotential position else 0)
          - bundleCurrentScale bundling (bundling.bundleOf edge)
            * cycleDropAt testPotential position := by
    intro position
    have hco := ne_of_gt (bundling.coBundleSize_pos hrank position)
    rw [hdrop, bundleCurrentDrops]
    split
    · field_simp
    · field_simp
      ring
  rw [Finset.sum_congr rfl (fun position _ => hterm position), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ (bundling.bundleOf edge)
      (fun position => cycleDropAt testPotential position),
    if_pos (Finset.mem_univ _), ← Finset.mul_sum, sum_cycleDropAt_eq_zero, mul_zero, sub_zero]

/-- **The leverage closed form.**  An edge in an arc of size `p` has
`|g_e|² = ((k − 1) n + p) / (k p)`.  At `p ≡ 1`, `n = k + 1` this is `k`, the
`(k+1)`-cycle's corner leverage; at `k = 2` it is `n/(2p) + 1/2`. -/
theorem bundledCycle_leverage (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (edge : Fin edgeCount) :
    leverageOf ((bundledCycleDesign bundling hrank).atom edge)
      = (((vertexRank : ℝ) - 1) * (edgeCount : ℝ)
          + (bundleSize bundling.bundleOf (bundling.bundleOf edge) : ℝ))
        / ((vertexRank : ℝ) * (bundleSize bundling.bundleOf (bundling.bundleOf edge) : ℝ)) := by
  have hsize := bundling.bundleSize_pos_cast (bundling.bundleOf edge)
  have hco := bundling.coBundleSize_pos hrank (bundling.bundleOf edge)
  have hrankPos : (0 : ℝ) < (vertexRank : ℝ) := by exact_mod_cast hrank
  have hedgePos : (0 : ℝ) < (edgeCount : ℝ) := by
    exact_mod_cast bundling.edgeCount_pos hrank
  rw [bundledCycleDesign,
    leverageOf_graphicAtom_of_solves (bundledCycleData bundling hrank) edge _
      (bundleCurrent_solves bundling hrank edge),
    bundledCycleData_selected_conductance,
    show (bundledCycleData bundling hrank).graph.edgeVector edge
        ⬝ᵥ potentialOfDrops (bundleCurrentDrops bundling (bundling.bundleOf edge))
      = bundleCurrentDrops bundling (bundling.bundleOf edge) (bundling.bundleOf edge) from
      (bundledCycleGraph_edgeVector_dotProduct bundling.bundleOf edge _).trans
        (cycleDropAt_potentialOfDrops _ (sum_bundleCurrentDrops bundling hrank _) _),
    bundleCurrentDrops, if_pos rfl, bundleCurrentScale, CycleBundling.graphInducedWeight]
  field_simp
  ring

/-- **Cross-check against the corank-one tie criterion.**  Reading the arc as a
class and `p/n` as its total weight, the leverage above satisfies the affine
relation `k T ℓ = (k − 1) + T` that `Gtz.isTie_iff_leverage_identity` proves
characterizes ties at corank one.  The two computations are independent: that one
comes from the pivot/Schur identity at `m = k+1`, this one from the transfer
current on the cycle. -/
theorem bundledCycle_leverage_identity_at_arcTotal
    (bundling : CycleBundling edgeCount vertexRank) (hrank : 1 ≤ vertexRank)
    (edge : Fin edgeCount) :
    (vertexRank : ℝ)
        * ((bundleSize bundling.bundleOf (bundling.bundleOf edge) : ℝ) / (edgeCount : ℝ))
        * leverageOf ((bundledCycleDesign bundling hrank).atom edge)
      = ((vertexRank : ℝ) - 1)
        + (bundleSize bundling.bundleOf (bundling.bundleOf edge) : ℝ) / (edgeCount : ℝ) := by
  have hsize := bundling.bundleSize_pos_cast (bundling.bundleOf edge)
  have hrankPos : (0 : ℝ) < (vertexRank : ℝ) := by exact_mod_cast hrank
  have hedgePos : (0 : ℝ) < (edgeCount : ℝ) := by
    exact_mod_cast bundling.edgeCount_pos hrank
  rw [bundledCycle_leverage]
  field_simp

/-- **The leverage on the shipped projection coordinates**:
`P_ee = (k − 1)/(k p) + 1/(k n)`. -/
theorem bundledCycle_projection_diagonal (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) (edge : Fin edgeCount) :
    projectionOfDesign (bundledCycleDesign bundling hrank) edge edge
      = ((vertexRank : ℝ) - 1)
          / ((vertexRank : ℝ) * (bundleSize bundling.bundleOf (bundling.bundleOf edge) : ℝ))
        + 1 / ((vertexRank : ℝ) * (edgeCount : ℝ)) := by
  have hsize := bundling.bundleSize_pos_cast (bundling.bundleOf edge)
  have hrankPos : (0 : ℝ) < (vertexRank : ℝ) := by exact_mod_cast hrank
  have hedgePos : (0 : ℝ) < (edgeCount : ℝ) := by
    exact_mod_cast bundling.edgeCount_pos hrank
  rw [projectionOfDesign_diagonal, bundledCycleDesign_weight, bundledCycle_leverage]
  field_simp

/-- **The rank-2 cluster magnitude.**  At `k = 2` the projection diagonal is
`1/(2n) + 1/(2p)` for an edge in an arc of size `p`.  Combined with
`bundledCycle_atom_eq_of_sameBundle` — the atoms inside an arc are *equal* — a
rank-2 bundled cycle is exactly a three-cluster design of cluster sizes
`(p, q, r)`, `p + q + r = n`.  That is precisely the shape of the real `k = 2`
equality family (CITED: arXiv:2604.14050 Prop 1); that nothing else has it is
the cited theorem, not this one. -/
theorem bundledCycle_rankTwo_clusterMagnitude (bundling : CycleBundling edgeCount 2)
    (hrank : 1 ≤ 2) (edge : Fin edgeCount) :
    projectionOfDesign (bundledCycleDesign bundling hrank) edge edge
      = 1 / (2 * (edgeCount : ℝ))
        + 1 / (2 * (bundleSize bundling.bundleOf (bundling.bundleOf edge) : ℝ)) := by
  have hsize := bundling.bundleSize_pos_cast (bundling.bundleOf edge)
  have hedgePos : (0 : ℝ) < (edgeCount : ℝ) := by
    exact_mod_cast bundling.edgeCount_pos hrank
  rw [bundledCycle_projection_diagonal]
  norm_num
  field_simp
  ring

/-! ## The plain cycle, at every rank

Everything above is universally quantified over `CycleBundling`.  These three
instantiate it at `cycleBundlingWitness`, so the "at every rank" claims have a
kernel witness at every rank rather than only at the rank-3 sizes below. -/

/-- **A tie at every rank, witnessed.**  The plain `(k+1)`-cycle with uniform
weights is an exact tie for every `k ≥ 1`. -/
theorem cycleBundlingWitness_isTie (vertexRank : ℕ) (hrank : 1 ≤ vertexRank) :
    IsTie (bundledCycleDesign (cycleBundlingWitness vertexRank) hrank) :=
  bundledCycle_isTie _ hrank

/-- **The `(k+1)`-cycle's corner leverage is `k`** — the closed form at `p ≡ 1`,
`n = k + 1`. -/
theorem cycleBundlingWitness_leverage (vertexRank : ℕ) (hrank : 1 ≤ vertexRank)
    (edge : Fin (vertexRank + 1)) :
    leverageOf ((bundledCycleDesign (cycleBundlingWitness vertexRank) hrank).atom edge)
      = (vertexRank : ℝ) := by
  have hrankPos : (0 : ℝ) < (vertexRank : ℝ) := by exact_mod_cast hrank
  rw [bundledCycle_leverage, cycleBundlingWitness_bundleSize]
  push_cast
  field_simp
  ring

/-- The rank-2 cluster magnitude, on a concrete rank-2 bundling: the triangle
with three singleton arcs has `P_ee = 1/6 + 1/2`. -/
theorem cycleBundlingWitness_rankTwo_clusterMagnitude (edge : Fin 3) :
    projectionOfDesign (bundledCycleDesign (cycleBundlingWitness 2) (by norm_num)) edge edge
      = 1 / 6 + 1 / 2 := by
  rw [bundledCycle_rankTwo_clusterMagnitude, cycleBundlingWitness_bundleSize]
  norm_num

/-! ## Exact slack at rank 2 -/

/-- **The two-term Engel deficiency is an exact rational square.**  The
denominator is explicit, so the slack off the tight ray is quantified with a
rational constant, not merely bounded below. -/
theorem engelDeficiency_two (leftDrop rightDrop leftSize rightSize : ℝ)
    (hleft : 0 < leftSize) (hright : 0 < rightSize) :
    leftDrop ^ 2 / leftSize + rightDrop ^ 2 / rightSize
        - (leftDrop + rightDrop) ^ 2 / (leftSize + rightSize)
      = (leftDrop * rightSize - rightDrop * leftSize) ^ 2
        / (leftSize * rightSize * (leftSize + rightSize)) := by
  have hleftNe : leftSize ≠ 0 := ne_of_gt hleft
  have hrightNe : rightSize ≠ 0 := ne_of_gt hright
  have hsumNe : leftSize + rightSize ≠ 0 := by positivity
  field_simp
  ring

/-- **The gap of a two-arc transversal is an exact rational square.**  This is
the rank-2 case, where the tree spans exactly two arcs: the margin is
`(d₁ p₂ − d₂ p₁)² / (p₁ p₂ (p₁ + p₂))`, zero exactly on the ray `d₁ p₂ = d₂ p₁`
and strictly positive off it. -/
theorem bundledCycle_gap_eq_squareQuotient (bundling : CycleBundling edgeCount vertexRank)
    (hrank : 1 ≤ vertexRank) {edgeSet : Finset (Fin edgeCount)}
    {dropped firstArc secondArc : Fin (vertexRank + 1)}
    (hinj : Set.InjOn bundling.bundleOf ↑edgeSet)
    (himage : edgeSet.image bundling.bundleOf = Finset.univ.erase dropped)
    (hdistinct : firstArc ≠ secondArc)
    (hpair : Finset.univ.erase dropped = {firstArc, secondArc})
    (potential : Fin vertexRank → ℝ) :
    potential ⬝ᵥ (((bundledCycleData bundling hrank).selectedLaplacian edgeSet
        - (bundledCycleData bundling hrank).fullLaplacian) *ᵥ potential)
      = (cycleDropAt potential firstArc * (bundleSize bundling.bundleOf secondArc : ℝ)
          - cycleDropAt potential secondArc * (bundleSize bundling.bundleOf firstArc : ℝ)) ^ 2
        / ((bundleSize bundling.bundleOf firstArc : ℝ)
            * (bundleSize bundling.bundleOf secondArc : ℝ)
            * ((bundleSize bundling.bundleOf firstArc : ℝ)
              + (bundleSize bundling.bundleOf secondArc : ℝ))) := by
  rw [bundledCycle_gap_eq_engelDeficiency bundling hrank hinj himage, hpair,
    Finset.sum_pair hdistinct, Finset.sum_pair hdistinct, Finset.sum_pair hdistinct]
  exact engelDeficiency_two _ _ _ _ (bundling.bundleSize_pos_cast firstArc)
    (bundling.bundleSize_pos_cast secondArc)

/-- At rank 2 a transversal always spans exactly two arcs. -/
theorem exists_arcPair_rankTwo (dropped : Fin 3) :
    ∃ firstArc secondArc : Fin 3, firstArc ≠ secondArc ∧
      Finset.univ.erase dropped = {firstArc, secondArc} := by
  have hcard : (Finset.univ.erase dropped).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  obtain ⟨firstArc, secondArc, hdistinct, harcs⟩ := Finset.card_eq_two.mp hcard
  exact ⟨firstArc, secondArc, hdistinct, harcs⟩

/-- **The rank-2 slack, unconditionally.**  At rank 2 a transversal always spans
exactly two arcs, so the two-arc hypothesis of `bundledCycle_gap_eq_squareQuotient`
is never a hypothesis in substance: for every rank-2 bundling and every
transversal the margin IS the explicit rational square.  This is the statement
the file's rank-2 slack claim actually needs. -/
theorem bundledCycle_rankTwo_gap_squareQuotient {edgeCount : ℕ}
    (bundling : CycleBundling edgeCount 2) {edgeSet : Finset (Fin edgeCount)}
    {dropped : Fin 3} (hinj : Set.InjOn bundling.bundleOf ↑edgeSet)
    (himage : edgeSet.image bundling.bundleOf = Finset.univ.erase dropped)
    (potential : Fin 2 → ℝ) :
    ∃ firstArc secondArc : Fin 3, firstArc ≠ secondArc ∧
      potential ⬝ᵥ (((bundledCycleData bundling (by norm_num)).selectedLaplacian edgeSet
          - (bundledCycleData bundling (by norm_num)).fullLaplacian) *ᵥ potential)
        = (cycleDropAt potential firstArc * (bundleSize bundling.bundleOf secondArc : ℝ)
            - cycleDropAt potential secondArc * (bundleSize bundling.bundleOf firstArc : ℝ)) ^ 2
          / ((bundleSize bundling.bundleOf firstArc : ℝ)
              * (bundleSize bundling.bundleOf secondArc : ℝ)
              * ((bundleSize bundling.bundleOf firstArc : ℝ)
                + (bundleSize bundling.bundleOf secondArc : ℝ))) := by
  obtain ⟨firstArc, secondArc, hdistinct, hpair⟩ := exists_arcPair_rankTwo dropped
  exact ⟨firstArc, secondArc, hdistinct,
    bundledCycle_gap_eq_squareQuotient bundling (by norm_num) hinj himage hdistinct hpair
      potential⟩

/-! ## Exact instances at the campaign's binding rank-3 sizes

`(6,3)` and `(7,3)` are the sizes at which rank-3 GTZ binds.  The bundled cycles
below are the `U(3,4)` tight classes there — cycle matroid of the 4-cycle with
parallel extensions — and their leverages, computed in the kernel from
`bundledCycle_leverage`, reproduce the exhaustive exact-rational tables:
`(6,3)` gives `{5/3, 13/3}` and `{7/3, 13/3}`; `(7,3)` gives `{3/2, 5}`,
`{17/9, 8/3, 5}` and `{8/3, 5}`.  The diamond `M(K₄ − e)` tight classes at these
sizes are NOT bundled cycles and appear nowhere in this file.
-/

/-- `(6,3)`, arc sizes `(3,1,1,1)`. -/
def bundlingSixThreeHeavy : CycleBundling 6 3 where
  bundleOf := ![0, 0, 0, 1, 2, 3]
  hasEdgeInEveryBundle := by decide

/-- `(6,3)`, arc sizes `(2,2,1,1)`. -/
def bundlingSixThreePaired : CycleBundling 6 3 where
  bundleOf := ![0, 0, 1, 1, 2, 3]
  hasEdgeInEveryBundle := by decide

/-- `(7,3)`, arc sizes `(4,1,1,1)`. -/
def bundlingSevenThreeHeavy : CycleBundling 7 3 where
  bundleOf := ![0, 0, 0, 0, 1, 2, 3]
  hasEdgeInEveryBundle := by decide

/-- `(7,3)`, arc sizes `(3,2,1,1)`. -/
def bundlingSevenThreeMixed : CycleBundling 7 3 where
  bundleOf := ![0, 0, 0, 1, 1, 2, 3]
  hasEdgeInEveryBundle := by decide

/-- `(7,3)`, arc sizes `(2,2,2,1)`. -/
def bundlingSevenThreePaired : CycleBundling 7 3 where
  bundleOf := ![0, 0, 1, 1, 2, 2, 3]
  hasEdgeInEveryBundle := by decide

/-- The `(6,3)` design with arc sizes `(3,1,1,1)` is an exact tie. -/
theorem bundlingSixThreeHeavy_isTie :
    IsTie (bundledCycleDesign bundlingSixThreeHeavy (by norm_num)) :=
  bundledCycle_isTie bundlingSixThreeHeavy _

/-- The `(6,3)` design with arc sizes `(2,2,1,1)` is an exact tie. -/
theorem bundlingSixThreePaired_isTie :
    IsTie (bundledCycleDesign bundlingSixThreePaired (by norm_num)) :=
  bundledCycle_isTie bundlingSixThreePaired _

/-- The `(7,3)` design with arc sizes `(4,1,1,1)` is an exact tie. -/
theorem bundlingSevenThreeHeavy_isTie :
    IsTie (bundledCycleDesign bundlingSevenThreeHeavy (by norm_num)) :=
  bundledCycle_isTie bundlingSevenThreeHeavy _

/-- The `(7,3)` design with arc sizes `(3,2,1,1)` is an exact tie. -/
theorem bundlingSevenThreeMixed_isTie :
    IsTie (bundledCycleDesign bundlingSevenThreeMixed (by norm_num)) :=
  bundledCycle_isTie bundlingSevenThreeMixed _

/-- The `(7,3)` design with arc sizes `(2,2,2,1)` is an exact tie. -/
theorem bundlingSevenThreePaired_isTie :
    IsTie (bundledCycleDesign bundlingSevenThreePaired (by norm_num)) :=
  bundledCycle_isTie bundlingSevenThreePaired _

/-- `(6,3)`, `(3,1,1,1)`: the triple arc has leverage `5/3`. -/
theorem bundlingSixThreeHeavy_leverage_tripleArc :
    leverageOf ((bundledCycleDesign bundlingSixThreeHeavy (by norm_num)).atom 0) = 5 / 3 := by
  rw [bundledCycle_leverage,
    show bundleSize bundlingSixThreeHeavy.bundleOf (bundlingSixThreeHeavy.bundleOf 0) = 3 from
      by decide]
  norm_num

/-- `(6,3)`, `(3,1,1,1)`: a single arc has leverage `13/3`. -/
theorem bundlingSixThreeHeavy_leverage_singleArc :
    leverageOf ((bundledCycleDesign bundlingSixThreeHeavy (by norm_num)).atom 3) = 13 / 3 := by
  rw [bundledCycle_leverage,
    show bundleSize bundlingSixThreeHeavy.bundleOf (bundlingSixThreeHeavy.bundleOf 3) = 1 from
      by decide]
  norm_num

/-- `(6,3)`, `(2,2,1,1)`: a double arc has leverage `7/3`. -/
theorem bundlingSixThreePaired_leverage_doubleArc :
    leverageOf ((bundledCycleDesign bundlingSixThreePaired (by norm_num)).atom 0) = 7 / 3 := by
  rw [bundledCycle_leverage,
    show bundleSize bundlingSixThreePaired.bundleOf (bundlingSixThreePaired.bundleOf 0) = 2 from
      by decide]
  norm_num

/-- `(7,3)`, `(4,1,1,1)`: the quadruple arc has leverage `3/2`. -/
theorem bundlingSevenThreeHeavy_leverage_quadArc :
    leverageOf ((bundledCycleDesign bundlingSevenThreeHeavy (by norm_num)).atom 0) = 3 / 2 := by
  rw [bundledCycle_leverage,
    show bundleSize bundlingSevenThreeHeavy.bundleOf (bundlingSevenThreeHeavy.bundleOf 0) = 4 from
      by decide]
  norm_num

/-- `(7,3)`, `(4,1,1,1)`: a single arc has leverage `5`. -/
theorem bundlingSevenThreeHeavy_leverage_singleArc :
    leverageOf ((bundledCycleDesign bundlingSevenThreeHeavy (by norm_num)).atom 4) = 5 := by
  rw [bundledCycle_leverage,
    show bundleSize bundlingSevenThreeHeavy.bundleOf (bundlingSevenThreeHeavy.bundleOf 4) = 1 from
      by decide]
  norm_num

/-- `(7,3)`, `(3,2,1,1)`: the triple arc has leverage `17/9`. -/
theorem bundlingSevenThreeMixed_leverage_tripleArc :
    leverageOf ((bundledCycleDesign bundlingSevenThreeMixed (by norm_num)).atom 0) = 17 / 9 := by
  rw [bundledCycle_leverage,
    show bundleSize bundlingSevenThreeMixed.bundleOf (bundlingSevenThreeMixed.bundleOf 0) = 3 from
      by decide]
  norm_num

/-- `(7,3)`, `(3,2,1,1)`: the double arc has leverage `8/3`. -/
theorem bundlingSevenThreeMixed_leverage_doubleArc :
    leverageOf ((bundledCycleDesign bundlingSevenThreeMixed (by norm_num)).atom 3) = 8 / 3 := by
  rw [bundledCycle_leverage,
    show bundleSize bundlingSevenThreeMixed.bundleOf (bundlingSevenThreeMixed.bundleOf 3) = 2 from
      by decide]
  norm_num

/-- `(7,3)`, `(2,2,2,1)`: a double arc has leverage `8/3`. -/
theorem bundlingSevenThreePaired_leverage_doubleArc :
    leverageOf ((bundledCycleDesign bundlingSevenThreePaired (by norm_num)).atom 0) = 8 / 3 := by
  rw [bundledCycle_leverage,
    show bundleSize bundlingSevenThreePaired.bundleOf (bundlingSevenThreePaired.bundleOf 0) = 2 from
      by decide]
  norm_num

/-- `(7,3)`, `(2,2,2,1)`: the single arc has leverage `5`. -/
theorem bundlingSevenThreePaired_leverage_singleArc :
    leverageOf ((bundledCycleDesign bundlingSevenThreePaired (by norm_num)).atom 6) = 5 := by
  rw [bundledCycle_leverage,
    show bundleSize bundlingSevenThreePaired.bundleOf (bundlingSevenThreePaired.bundleOf 6) = 1 from
      by decide]
  norm_num

/-! ## Two rank-2 instances at `(9,2)`

A rank-2 bundled cycle is the triangle with parallel bundles `(p,q,r)`,
`p + q + r = n`, so at `n = 9` there is one per partition of `9` into three
positive parts — seven of them.  The two below are the classes whose cluster
magnitudes were recomputed independently (exact rational, two separate routes)
during the audit of Nesterenko's Table 1, whose `(9,2)` entry reads `6`.  Each is
an exact tie, and each atom's projection diagonal is `1/(2n) + 1/(2p)` — the real
`k = 2` equality criterion's cluster magnitude.  That these seven are pairwise
inequivalent, and hence that `6` undercounts, is MEASURED, not proved here: this
file exhibits designs, it does not count classes. -/

/-- `(9,2)`, arc sizes `(7,1,1)`. -/
def bundlingNineTwoHeavy : CycleBundling 9 2 where
  bundleOf := ![0, 0, 0, 0, 0, 0, 0, 1, 2]
  hasEdgeInEveryBundle := by decide

/-- `(9,2)`, arc sizes `(4,3,2)`. -/
def bundlingNineTwoSpread : CycleBundling 9 2 where
  bundleOf := ![0, 0, 0, 0, 1, 1, 1, 2, 2]
  hasEdgeInEveryBundle := by decide

/-- The `(9,2)` design with arc sizes `(7,1,1)` is an exact tie. -/
theorem bundlingNineTwoHeavy_isTie :
    IsTie (bundledCycleDesign bundlingNineTwoHeavy (by norm_num)) :=
  bundledCycle_isTie bundlingNineTwoHeavy _

/-- The `(9,2)` design with arc sizes `(4,3,2)` is an exact tie. -/
theorem bundlingNineTwoSpread_isTie :
    IsTie (bundledCycleDesign bundlingNineTwoSpread (by norm_num)) :=
  bundledCycle_isTie bundlingNineTwoSpread _

/-- `(9,2)`, `(7,1,1)`: the seven-fold arc has cluster magnitude `8/63`. -/
theorem bundlingNineTwoHeavy_cluster_sevenArc :
    projectionOfDesign (bundledCycleDesign bundlingNineTwoHeavy (by norm_num)) 0 0 = 8 / 63 := by
  rw [bundledCycle_rankTwo_clusterMagnitude,
    show bundleSize bundlingNineTwoHeavy.bundleOf (bundlingNineTwoHeavy.bundleOf 0) = 7 from
      by decide]
  norm_num

/-- `(9,2)`, `(7,1,1)`: a singleton arc has cluster magnitude `5/9`. -/
theorem bundlingNineTwoHeavy_cluster_singleArc :
    projectionOfDesign (bundledCycleDesign bundlingNineTwoHeavy (by norm_num)) 7 7 = 5 / 9 := by
  rw [bundledCycle_rankTwo_clusterMagnitude,
    show bundleSize bundlingNineTwoHeavy.bundleOf (bundlingNineTwoHeavy.bundleOf 7) = 1 from
      by decide]
  norm_num

/-- `(9,2)`, `(4,3,2)`: the four-fold arc has cluster magnitude `13/72`. -/
theorem bundlingNineTwoSpread_cluster_quadArc :
    projectionOfDesign (bundledCycleDesign bundlingNineTwoSpread (by norm_num)) 0 0 = 13 / 72 := by
  rw [bundledCycle_rankTwo_clusterMagnitude,
    show bundleSize bundlingNineTwoSpread.bundleOf (bundlingNineTwoSpread.bundleOf 0) = 4 from
      by decide]
  norm_num

/-- `(9,2)`, `(4,3,2)`: the triple arc has cluster magnitude `2/9`. -/
theorem bundlingNineTwoSpread_cluster_tripleArc :
    projectionOfDesign (bundledCycleDesign bundlingNineTwoSpread (by norm_num)) 4 4 = 2 / 9 := by
  rw [bundledCycle_rankTwo_clusterMagnitude,
    show bundleSize bundlingNineTwoSpread.bundleOf (bundlingNineTwoSpread.bundleOf 4) = 3 from
      by decide]
  norm_num

/-- `(9,2)`, `(4,3,2)`: the double arc has cluster magnitude `11/36`. -/
theorem bundlingNineTwoSpread_cluster_doubleArc :
    projectionOfDesign (bundledCycleDesign bundlingNineTwoSpread (by norm_num)) 7 7 = 11 / 36 := by
  rw [bundledCycle_rankTwo_clusterMagnitude,
    show bundleSize bundlingNineTwoSpread.bundleOf (bundlingNineTwoSpread.bundleOf 7) = 2 from
      by decide]
  norm_num

end Gtz

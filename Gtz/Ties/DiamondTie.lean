/-
# The diamond `M(K4 - e)`: the SECOND rank-three tie primitive

`Gtz.Design.EqualityLocus` builds the bundled-cycle tie family -- the matroid
`U(3,4)` with parallel extensions -- and records, as MEASURED and formalized
nowhere, that the rank-three equality locus has a second primitive: the diamond
`M(K4 - e)`.  This file supplies it, exactly and rationally, at `(5,3)`.

## What is proved here

* `diamondTieData` -- the diamond `K4 - e` (vertices `a,b,c,d`, the edge `cd`
  omitted, ground vertex `d`) as a `GraphDesignData 5 3`, with uniform design
  weight `1/5` and conductance `2` on the `ab` diagonal, `3` on each of the four
  rim edges `ac, ad, bc, bd`.
* `diamondGapForm` / `diamondTie_gapValue` -- the Loewner gap of a selected edge
  set, as one polynomial identity in the three reduced potentials.
* `diamondTieDesign_dominates` -- the star `{ab, ac, ad}` at `a` dominates,
  through the exact sum-of-squares
  `Q = (1/2)(2 y_b - 8 y_a + 3 y_c)^2 + (9/2) y_c^2`.
* `diamondTieDesign_no_strictDominator` -- NO three-subset dominates strictly.
  Ten explicit rational witnesses: the eight spanning trees carry a null vector
  of their (positive semidefinite, singular) gap form; the two circuits
  `{ab,ac,bc}` and `{ab,ad,bd}` carry a potential constant on the circuit's
  vertex set, where the gap form equals minus the full Dirichlet form, `-6`.
* `diamondTieDesign_isTie` -- the two halves packaged: the value is exactly `1`.

## Why the conductance is `(2; 3,3,3,3)` and not the cycle rule

The cycle family's graph-induced conductance is `1/(p(n-p))` on a bundle of `p`
parallel edges.  That rule is SPECIFIC TO THE CYCLE.  Applied to the diamond it
gives a strict dominator, not a tie [MEASURED: value `1.25` at `(5,3)` with
uniform conductance; `1.3650` at `(6,3)` and `1.4514 / 1.3159 / 1.5217` at
`(7,3)` for the rim-doubled classes].  The correct conductances are fixed by the
corank-one leverage criterion through the series-parallel structure: the three
`a`-to-`b` paths (the edge `ab`, and the two two-edge paths through `c` and `d`)
carry conductance `d` and `c/2` each, so `R_eff(ab) = 1/(c+d)` and the
projection coordinate `d/(c+d)` must equal `2/5`, forcing `3d = 2c`.  Scaling to
integers gives `(d, c) = (2, 3)`, and then `R_eff(ac) = 13/60`, so the rim
projection coordinate is `3 * 13/60 = 13/20` -- the four rim leverages are
`13/4` and the `ab` leverage is `2`, summing to `3` as the trace identity
requires.

## CITED, not proved here

The identification of this family as the OTHER rank-three tie primitive, and the
statement that every `(6,3)` and `(7,3)` tie class is a splitting of either a
bundled cycle or this diamond, is the equality-locus workflow's classification
(2-connected series-parallel multigraphs on four vertices modulo the matroid
automorphism group, order `8`: it fixes `ab` and permutes the rim preserving the
block partition `{ac,bc} | {ad,bd}`, the extra generators over the graph group
being the Whitney twists at the 2-separation `{a,b}`).  That classification is
NOT proved here.  What is proved here is that THIS design is a tie.

## MEASURED, not proved here

* The Naimark dual of this design is the `(5,2)` rank-two tie whose three
  parallel classes have sizes `(2,2,1)` -- the planar dual of `K4 - e` is the
  triangle with edge bundles `1, 2, 2`.  That is how the design was found; the
  proof below is self-contained and does not use it.
* Splitting this primitive gives the two `(6,3)` and the five `(7,3)` diamond tie
  classes, each an exact tie.  Only the `(5,3)` primitive is mechanized here.

## Scope

Nothing here bears on whether `GtzWeighted 5 3`, `GtzWeighted 7 3` or
`GtzWeightedAll 3` is true.  A tie is a boundary point of the feasible region;
this file exhibits one and proves it is one.  What it buys is the same
obstruction the cycle family buys, at a design the cycle family does not reach:
no strictly-positive certificate can exist here either.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.GraphicInstance
import Gtz.Design.EqualityLocus
import Gtz.Reduction.ExchangeInvariant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The graph -/

/-- The diamond `K4 - e`: vertices `a = 0`, `b = 1`, `c = 2` and the ground
vertex `d = 3`; edges `ab, ac, ad, bc, bd` in that order, the edge `cd` omitted. -/
def diamondGraph : MultigraphOnGround 5 3 where
  edgeTail := ![0, 0, 0, 1, 1]
  edgeHead := ![1, 2, 3, 2, 3]

theorem diamondGraph_isGroundConnected :
    IsGroundConnected diamondGraph Finset.univ := by
  have hgroundToFirst : IsEdgeAdjacent diamondGraph Finset.univ (Fin.last 3) 0 :=
    ⟨2, Finset.mem_univ _, Or.inr ⟨by decide, by decide⟩⟩
  have hfirstToSecond : IsEdgeAdjacent diamondGraph Finset.univ 0 1 :=
    ⟨0, Finset.mem_univ _, Or.inl ⟨by decide, by decide⟩⟩
  have hfirstToThird : IsEdgeAdjacent diamondGraph Finset.univ 0 2 :=
    ⟨1, Finset.mem_univ _, Or.inl ⟨by decide, by decide⟩⟩
  intro vertex
  fin_cases vertex
  · exact Relation.ReflTransGen.single hgroundToFirst
  · exact (Relation.ReflTransGen.single hgroundToFirst).tail hfirstToSecond
  · exact (Relation.ReflTransGen.single hgroundToFirst).tail hfirstToThird
  · exact Relation.ReflTransGen.refl

/-! ## The design -/

/-- The tie conductance of the diamond: `2` on the `ab` diagonal, `3` on each of
the four rim edges.  The cycle rule `1/(p(n-p))` does NOT produce a tie here. -/
def diamondConductance : Fin 5 → ℝ := ![2, 3, 3, 3, 3]

/-- The diamond design data: uniform design weight `1/5` on all five edges. -/
noncomputable def diamondTieData : GraphDesignData 5 3 where
  graph := diamondGraph
  conductance := diamondConductance
  conductance_pos := by
    intro edge
    fin_cases edge <;> norm_num [diamondConductance]
  weight := fun _ => (1 : ℝ) / 5
  weight_pos := fun _ => by norm_num
  weight_sum_one := by rw [Fin.sum_univ_five]; norm_num
  isGroundConnected := diamondGraph_isGroundConnected

/-- **The diamond tie design** at `(5,3)`. -/
noncomputable def diamondTieDesign : WeightedDesign 5 3 := graphicDesign diamondTieData

/-! ## The gap form -/

/-- The potential drop across each of the five edges, in the three reduced
coordinates (the ground vertex `d` carries potential zero). -/
def diamondDrop (potential : Fin 3 → ℝ) : Fin 5 → ℝ :=
  ![potential 0 - potential 1, potential 0 - potential 2, potential 0,
    potential 1 - potential 2, potential 1]

theorem groundedPotential_diamond_zero (potential : Fin 3 → ℝ) :
    groundedPotential potential 0 = potential 0 :=
  groundedPotential_castSucc potential 0

theorem groundedPotential_diamond_one (potential : Fin 3 → ℝ) :
    groundedPotential potential 1 = potential 1 :=
  groundedPotential_castSucc potential 1

theorem groundedPotential_diamond_two (potential : Fin 3 → ℝ) :
    groundedPotential potential 2 = potential 2 :=
  groundedPotential_castSucc potential 2

theorem groundedPotential_diamond_three (potential : Fin 3 → ℝ) :
    groundedPotential potential 3 = 0 :=
  groundedPotential_last potential

theorem diamondDrop_spec (potential : Fin 3 → ℝ) (edge : Fin 5) :
    groundedPotential potential (diamondGraph.edgeTail edge)
        - groundedPotential potential (diamondGraph.edgeHead edge)
      = diamondDrop potential edge := by
  have hzero := groundedPotential_diamond_zero potential
  have hone := groundedPotential_diamond_one potential
  have htwo := groundedPotential_diamond_two potential
  have hthree := groundedPotential_diamond_three potential
  fin_cases edge
  · show groundedPotential potential 0 - groundedPotential potential 1
        = potential 0 - potential 1
    rw [hzero, hone]
  · show groundedPotential potential 0 - groundedPotential potential 2
        = potential 0 - potential 2
    rw [hzero, htwo]
  · show groundedPotential potential 0 - groundedPotential potential 3 = potential 0
    rw [hzero, hthree, sub_zero]
  · show groundedPotential potential 1 - groundedPotential potential 2
        = potential 1 - potential 2
    rw [hone, htwo]
  · show groundedPotential potential 1 - groundedPotential potential 3 = potential 1
    rw [hone, hthree, sub_zero]

/-- Uniform weight `1/5` turns the selected conductance into `5` times the
conductance. -/
theorem diamondSelected_ratio (edge : Fin 5) :
    diamondTieData.conductance edge / diamondTieData.weight edge
      = 5 * diamondConductance edge := by
  show diamondConductance edge / ((1 : ℝ) / 5) = 5 * diamondConductance edge
  field_simp

/-- **The gap form of the diamond tie.**  Every domination question about this
design is this one identity, read at a different edge set. -/
theorem diamondGapForm (edgeSet : Finset (Fin 5)) (potential : Fin 3 → ℝ) :
    potential ⬝ᵥ ((diamondTieData.selectedLaplacian edgeSet
        - diamondTieData.fullLaplacian) *ᵥ potential)
      = (∑ edge ∈ edgeSet, 5 * diamondConductance edge * diamondDrop potential edge ^ 2)
        - ∑ edge, diamondConductance edge * diamondDrop potential edge ^ 2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub, GraphDesignData.selectedLaplacian,
    GraphDesignData.fullLaplacian, laplacianOn_form, laplacianOn_form]
  congr 1
  · refine Finset.sum_congr rfl fun edge _ => ?_
    rw [show (diamondTieData.graph) = diamondGraph from rfl, diamondDrop_spec,
      diamondSelected_ratio]
  · refine Finset.sum_congr rfl fun edge _ => ?_
    rw [show (diamondTieData.graph) = diamondGraph from rfl, diamondDrop_spec]
    rfl

/-- The full Dirichlet form, expanded in the reduced potentials. -/
theorem diamondFullForm (potential : Fin 3 → ℝ) :
    (∑ edge, diamondConductance edge * diamondDrop potential edge ^ 2)
      = 2 * (potential 0 - potential 1) ^ 2 + 3 * (potential 0 - potential 2) ^ 2
        + 3 * potential 0 ^ 2 + 3 * (potential 1 - potential 2) ^ 2 + 3 * potential 1 ^ 2 := by
  rw [Fin.sum_univ_five]
  simp only [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.tail_cons]

/-- The gap form at an explicit three-element edge set, fully expanded. -/
theorem diamondTie_gapValue (first second third : Fin 5)
    (hfs : first ≠ second) (hft : first ≠ third) (hst : second ≠ third)
    (potential : Fin 3 → ℝ) :
    potential ⬝ᵥ ((diamondTieData.selectedLaplacian {first, second, third}
        - diamondTieData.fullLaplacian) *ᵥ potential)
      = 5 * diamondConductance first * diamondDrop potential first ^ 2
        + 5 * diamondConductance second * diamondDrop potential second ^ 2
        + 5 * diamondConductance third * diamondDrop potential third ^ 2
        - (2 * (potential 0 - potential 1) ^ 2 + 3 * (potential 0 - potential 2) ^ 2
          + 3 * potential 0 ^ 2 + 3 * (potential 1 - potential 2) ^ 2
          + 3 * potential 1 ^ 2) := by
  rw [diamondGapForm, sum_over_triple _ hfs hft hst, diamondFullForm]

/-! ## The dominating half -/

/-- **The star at `a` dominates.**  The exact sum-of-squares decomposition
`Q = (1/2)(2 y_b - 8 y_a + 3 y_c)^2 + (9/2) y_c^2` -- singular, so the margin is
exactly zero and not merely nonnegative. -/
theorem diamondTieDesign_dominates : Dominates diamondTieDesign {0, 1, 2} := by
  rw [diamondTieDesign, graphicDesign_dominates_iff]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq ?_, fun potential => ?_⟩
  · rw [Matrix.transpose_sub, diamondTieData.selectedLaplacian_transpose,
      diamondTieData.fullLaplacian_transpose]
  · rw [star_trivial, diamondTie_gapValue 0 1 2 (by decide) (by decide) (by decide)]
    simp only [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    nlinarith [sq_nonneg (2 * potential 1 - 8 * potential 0 + 3 * potential 2),
      sq_nonneg (potential 2)]

/-! ## The no-strict-dominator half -/

/-- A nonzero direction on which the gap form is nonpositive refutes strict
domination. -/
theorem diamondTie_notPosDef_of_nonpositive {edgeSet : Finset (Fin 5)}
    {potential : Fin 3 → ℝ} (hne : potential ≠ 0)
    (hnonpos : potential ⬝ᵥ ((diamondTieData.selectedLaplacian edgeSet
        - diamondTieData.fullLaplacian) *ᵥ potential) ≤ 0) :
    ¬ (subsetSum diamondTieDesign edgeSet - 1).PosDef := by
  intro hposdef
  have hgap := (graphicDesign_posDef_iff diamondTieData edgeSet).mp hposdef
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hgap).2 hne
  rw [star_trivial] at hpos
  linarith

theorem notPosDef_congr {left right : Finset (Fin 5)} (heq : left = right)
    (hnot : ¬ (subsetSum diamondTieDesign right - 1).PosDef) :
    ¬ (subsetSum diamondTieDesign left - 1).PosDef := heq ▸ hnot

/-- spanning tree {ab, ac, ad}, the star at a. -/
theorem diamondTie_notPosDef_012 :
    ¬ (subsetSum diamondTieDesign {0, 1, 2} - 1).PosDef := by
  refine diamondTie_notPosDef_of_nonpositive (potential := ![1, 4, 0]) ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · rw [diamondTie_gapValue 0 1 2 (by decide) (by decide) (by decide)]
    norm_num [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]

/-- CIRCUIT {ab, ac, bc}: constant on {a,b,c}, gap = -6. -/
theorem diamondTie_notPosDef_013 :
    ¬ (subsetSum diamondTieDesign {0, 1, 3} - 1).PosDef := by
  refine diamondTie_notPosDef_of_nonpositive (potential := ![1, 1, 1]) ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · rw [diamondTie_gapValue 0 1 3 (by decide) (by decide) (by decide)]
    norm_num [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]

/-- spanning tree {ab, ac, bd}. -/
theorem diamondTie_notPosDef_014 :
    ¬ (subsetSum diamondTieDesign {0, 1, 4} - 1).PosDef := by
  refine diamondTie_notPosDef_of_nonpositive (potential := ![4, 1, 5]) ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · rw [diamondTie_gapValue 0 1 4 (by decide) (by decide) (by decide)]
    norm_num [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]

/-- spanning tree {ab, ad, bc}. -/
theorem diamondTie_notPosDef_023 :
    ¬ (subsetSum diamondTieDesign {0, 2, 3} - 1).PosDef := by
  refine diamondTie_notPosDef_of_nonpositive (potential := ![1, 4, 5]) ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · rw [diamondTie_gapValue 0 2 3 (by decide) (by decide) (by decide)]
    norm_num [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]

/-- CIRCUIT {ab, ad, bd}: constant on {a,b,d}, gap = -6. -/
theorem diamondTie_notPosDef_024 :
    ¬ (subsetSum diamondTieDesign {0, 2, 4} - 1).PosDef := by
  refine diamondTie_notPosDef_of_nonpositive (potential := ![0, 0, 1]) ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 2
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hentry
  · rw [diamondTie_gapValue 0 2 4 (by decide) (by decide) (by decide)]
    norm_num [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]

/-- spanning tree {ab, bc, bd}, the star at b. -/
theorem diamondTie_notPosDef_034 :
    ¬ (subsetSum diamondTieDesign {0, 3, 4} - 1).PosDef := by
  refine diamondTie_notPosDef_of_nonpositive (potential := ![4, 1, 0]) ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · rw [diamondTie_gapValue 0 3 4 (by decide) (by decide) (by decide)]
    norm_num [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]

/-- spanning tree {ac, ad, bc}. -/
theorem diamondTie_notPosDef_123 :
    ¬ (subsetSum diamondTieDesign {1, 2, 3} - 1).PosDef := by
  refine diamondTie_notPosDef_of_nonpositive (potential := ![2, 8, 5]) ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · rw [diamondTie_gapValue 1 2 3 (by decide) (by decide) (by decide)]
    norm_num [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]

/-- spanning tree {ac, ad, bd}. -/
theorem diamondTie_notPosDef_124 :
    ¬ (subsetSum diamondTieDesign {1, 2, 4} - 1).PosDef := by
  refine diamondTie_notPosDef_of_nonpositive (potential := ![3, -3, 5]) ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · rw [diamondTie_gapValue 1 2 4 (by decide) (by decide) (by decide)]
    norm_num [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]

/-- spanning tree {ac, bc, bd}. -/
theorem diamondTie_notPosDef_134 :
    ¬ (subsetSum diamondTieDesign {1, 3, 4} - 1).PosDef := by
  refine diamondTie_notPosDef_of_nonpositive (potential := ![8, 2, 5]) ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · rw [diamondTie_gapValue 1 3 4 (by decide) (by decide) (by decide)]
    norm_num [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]

/-- spanning tree {ad, bc, bd}. -/
theorem diamondTie_notPosDef_234 :
    ¬ (subsetSum diamondTieDesign {2, 3, 4} - 1).PosDef := by
  refine diamondTie_notPosDef_of_nonpositive (potential := ![-3, 3, 5]) ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · rw [diamondTie_gapValue 2 3 4 (by decide) (by decide) (by decide)]
    norm_num [diamondConductance, diamondDrop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]

/-- **No three-subset of the diamond design dominates STRICTLY.** -/
theorem diamondTieDesign_no_strictDominator {edgeSet : Finset (Fin 5)}
    (hcard : edgeSet.card = 3) :
    ¬ (subsetSum diamondTieDesign edgeSet - 1).PosDef := by
  obtain ⟨firstEdge, secondEdge, thirdEdge, hfirstSecond, hfirstThird, hsecondThird, rfl⟩ :=
    Finset.card_eq_three.mp hcard
  fin_cases firstEdge <;> fin_cases secondEdge <;> fin_cases thirdEdge <;>
    first
      | (exact absurd rfl hfirstSecond)
      | (exact absurd rfl hfirstThird)
      | (exact absurd rfl hsecondThird)
      | (exact notPosDef_congr (by decide) diamondTie_notPosDef_012)
      | (exact notPosDef_congr (by decide) diamondTie_notPosDef_013)
      | (exact notPosDef_congr (by decide) diamondTie_notPosDef_014)
      | (exact notPosDef_congr (by decide) diamondTie_notPosDef_023)
      | (exact notPosDef_congr (by decide) diamondTie_notPosDef_024)
      | (exact notPosDef_congr (by decide) diamondTie_notPosDef_034)
      | (exact notPosDef_congr (by decide) diamondTie_notPosDef_123)
      | (exact notPosDef_congr (by decide) diamondTie_notPosDef_124)
      | (exact notPosDef_congr (by decide) diamondTie_notPosDef_134)
      | (exact notPosDef_congr (by decide) diamondTie_notPosDef_234)

/-- **The diamond is an exact tie**: the star at `a` dominates, nothing
dominates strictly, so the value is exactly `1`. -/
theorem diamondTieDesign_isTie : IsTie diamondTieDesign :=
  ⟨⟨{0, 1, 2}, by decide, diamondTieDesign_dominates⟩,
    fun _ hcard => diamondTieDesign_no_strictDominator hcard⟩

end Gtz

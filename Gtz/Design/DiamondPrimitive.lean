/-
# The diamond primitive: `M(K4 − e)` as an exact `(5,3)` tie

The equality locus at rank three has exactly TWO primitives.  One is the
bundled cycle `U(3,4)` (`Gtz.bundledCycleDesign`, `Gtz.bundledCycle_isTie`).
This file lands the other one, which had no witness in the repository: the
graphic design of the DIAMOND, `K4` minus an edge, at uniform weights.

Coordinates.  Vertices `0,1,2` are the reduced ones and `3 = Fin.last 3` is the
ground; the five edges are

    0 : 1-2   (the spine, joining the two degree-three vertices)
    1 : 1-3   3 : 2-3     (the series pair through the degree-two vertex 3)
    2 : 1-4   4 : 2-4     (the series pair through the degree-two vertex 4)

with conductances `(2,3,3,3,3)` and uniform design weight `1/5`.  Those numbers
are not a guess: they are the unique tie conductance at uniform weights, forced
by `w_e = t_e / ((1 − t_e) c_e)` where `c` is the dual graph's tie conductance
`c_j ∝ 1 / (1 − T_j)` on the merged classes `T = (1/5, 2/5, 2/5)`.

What is PROVED here (kernel-checked, no `sorry`, no `native_decide`):

* `diamondDesign` is a genuine weighted `(5,3)` design — Parseval comes from
  `graphicDesign`, connectivity is discharged by hand;
* `diamondDesign_dominates_spine`: the subset `{1-2, 1-3, 1-4}` dominates
  weakly, by the exact sum of squares
  `2 · gap = (−8 x₀ + 2 x₁ + 3 x₂)² + 9 x₂²`;
* `diamondDesign_no_strictDominator`: NO three-subset dominates strictly —
  each of the ten subsets carries an explicit isotropic or negative direction
  (the eight spanning trees tie exactly, the two triangles are indefinite);
* `diamondDesign_isTie`: the two halves packaged as `Gtz.IsTie`.

MEASURED elsewhere, not claimed here: that this design is the second primitive
of the whole rank-three equality locus, and that its Naimark dual is the
`(5,2)` three-cluster design with parallel classes `(1,2,2)`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.GraphicInstance
import Gtz.Design.EqualityLocus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The graph, the data, the design -/

/-- `K4` minus the edge `{3,4}`, grounded at the last vertex. -/
def diamondGraph : MultigraphOnGround 5 3 where
  edgeTail := ![0, 0, 0, 1, 1]
  edgeHead := ![1, 2, 3, 2, 3]

/-- The diamond is connected: every vertex is reachable from the ground. -/
theorem diamondGraph_isGroundConnected :
    IsGroundConnected diamondGraph Finset.univ := by
  have groundToFirst : IsEdgeAdjacent diamondGraph Finset.univ (Fin.last 3) 0 :=
    ⟨2, Finset.mem_univ 2, Or.inr ⟨rfl, rfl⟩⟩
  have groundToSecond : IsEdgeAdjacent diamondGraph Finset.univ (Fin.last 3) 1 :=
    ⟨4, Finset.mem_univ 4, Or.inr ⟨rfl, rfl⟩⟩
  have firstToThird : IsEdgeAdjacent diamondGraph Finset.univ (0 : Fin 4) 2 :=
    ⟨1, Finset.mem_univ 1, Or.inl ⟨rfl, rfl⟩⟩
  intro vertex
  fin_cases vertex
  · exact Relation.ReflTransGen.single groundToFirst
  · exact Relation.ReflTransGen.single groundToSecond
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single groundToFirst) firstToThird
  · exact Relation.ReflTransGen.refl

/-- The diamond design data: the unique tie conductance at uniform weights. -/
noncomputable def diamondData : GraphDesignData 5 3 where
  graph := diamondGraph
  conductance := ![2, 3, 3, 3, 3]
  conductance_pos := by intro edge; fin_cases edge <;> norm_num
  weight := ![1/5, 1/5, 1/5, 1/5, 1/5]
  weight_pos := by intro edge; fin_cases edge <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons]
    norm_num
  isGroundConnected := diamondGraph_isGroundConnected

/-- The diamond weighted design at size `(5,3)`. -/
noncomputable def diamondDesign : WeightedDesign 5 3 := graphicDesign diamondData

/-! ## The gap form in potential drops -/

/-- The potential drops across the five edges, in closed form. -/
def diamondDrop (edge : Fin 5) (potential : Fin 3 → ℝ) : ℝ :=
  ![potential 0 - potential 1, potential 0 - potential 2, potential 0,
    potential 1 - potential 2, potential 1] edge

/-- The closed-form drops ARE the grounded potential differences. -/
theorem diamondDrop_eq_grounded (edge : Fin 5) (potential : Fin 3 → ℝ) :
    diamondDrop edge potential
      = groundedPotential potential (diamondData.graph.edgeTail edge)
        - groundedPotential potential (diamondData.graph.edgeHead edge) := by
  -- Lean v4.34 leaves `potential 2 = potential (Fin.castPred 2 _)` on two of the
  -- five edges. The two sides are definitionally equal, and `rfl` closes them.
  fin_cases edge <;>
    simp [diamondDrop, diamondData, diamondGraph, groundedPotential, Fin.snoc] <;>
    rfl

/-- **The gap form, selected minus full.** -/
theorem diamondGap_form (edgeSet : Finset (Fin 5)) (potential : Fin 3 → ℝ) :
    potential ⬝ᵥ ((diamondData.selectedLaplacian edgeSet
        - diamondData.fullLaplacian) *ᵥ potential)
      = (∑ edge ∈ edgeSet,
            5 * diamondData.conductance edge * diamondDrop edge potential ^ 2)
        - ∑ edge : Fin 5,
            diamondData.conductance edge * diamondDrop edge potential ^ 2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub, GraphDesignData.selectedLaplacian,
    GraphDesignData.fullLaplacian, laplacianOn_form, laplacianOn_form]
  refine congrArg₂ _ (Finset.sum_congr rfl fun edge _ => ?_)
    (Finset.sum_congr rfl fun edge _ => ?_)
  · have hweight : diamondData.weight edge = 1 / 5 := by
      fin_cases edge <;> rfl
    rw [diamondDrop_eq_grounded, hweight]; ring
  · rw [diamondDrop_eq_grounded]

/-- **The gap form over the whole edge set**, with the selection as an
indicator: the shape the ten case computations consume. -/
theorem diamondGap_form_indicator (edgeSet : Finset (Fin 5)) (potential : Fin 3 → ℝ) :
    potential ⬝ᵥ ((diamondData.selectedLaplacian edgeSet
        - diamondData.fullLaplacian) *ᵥ potential)
      = ∑ edge : Fin 5, ((if edge ∈ edgeSet then (5 : ℝ) else 0) - 1)
          * diamondData.conductance edge * diamondDrop edge potential ^ 2 := by
  have hsplit : ∑ edge ∈ edgeSet,
        5 * diamondData.conductance edge * diamondDrop edge potential ^ 2
      = ∑ edge : Fin 5, if edge ∈ edgeSet then
          5 * diamondData.conductance edge * diamondDrop edge potential ^ 2
        else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [diamondGap_form, hsplit, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun edge _ => ?_
  by_cases hmem : edge ∈ edgeSet
  · rw [if_pos hmem, if_pos hmem]; ring
  · rw [if_neg hmem, if_neg hmem]; ring

/-! ## The tie -/

/-- A nonzero direction with nonpositive gap form kills strict domination. -/
theorem diamondGap_not_posDef_of_direction {edgeSet : Finset (Fin 5)}
    {potential : Fin 3 → ℝ} (hnonzero : potential ≠ 0)
    (hnonpos : potential ⬝ᵥ ((diamondData.selectedLaplacian edgeSet
      - diamondData.fullLaplacian) *ᵥ potential) ≤ 0) :
    ¬ (diamondData.selectedLaplacian edgeSet - diamondData.fullLaplacian).PosDef := by
  intro hposDef
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hnonzero
  rw [star_trivial] at hpos
  linarith

/-- A vector with a nonzero leading coordinate is nonzero. -/
theorem diamondWitness_ne_zero (potential : Fin 3 → ℝ) (hlead : potential 0 ≠ 0) :
    potential ≠ 0 := fun hzero => hlead (by rw [hzero]; rfl)

/-- **The spine triple dominates weakly.**  The gap form is the exact sum of
squares `((−8 x₀ + 2 x₁ + 3 x₂)² + 9 x₂²) / 2`. -/
theorem diamondDesign_dominates_spine :
    Dominates diamondDesign ({0, 1, 2} : Finset (Fin 5)) := by
  rw [diamondDesign, graphicDesign_dominates_iff]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun potential => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sub, diamondData.selectedLaplacian_transpose,
      diamondData.fullLaplacian_transpose]
  · rw [star_trivial, diamondGap_form_indicator]
    norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton]
    nlinarith [sq_nonneg (-8 * potential 0 + 2 * potential 1 + 3 * potential 2),
      sq_nonneg (potential 2)]

/-- **No three-subset dominates strictly.** -/
theorem diamondDesign_no_strictDominator (edgeSet : Finset (Fin 5))
    (hcard : edgeSet.card = 3) :
    ¬ (subsetSum diamondDesign edgeSet - 1).PosDef := by
  rw [diamondDesign, graphicDesign_posDef_iff]
  have hcompl : edgeSetᶜ.card = 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  obtain ⟨first, second, hdistinct, hpair⟩ := Finset.card_eq_two.mp hcompl
  have hset : edgeSet = ({first, second} : Finset (Fin 5))ᶜ := by
    rw [← hpair, compl_compl]
  subst hset
  fin_cases first <;> fin_cases second
  · exact absurd rfl hdistinct
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![-3, 3, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![8, 2, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![3, -3, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![2, 8, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![-3, 3, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact absurd rfl hdistinct
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![4, 1, 0] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![3, 2, -3] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![1, 4, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![8, 2, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![4, 1, 0] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact absurd rfl hdistinct
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![4, 1, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![1, 1, 1] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![3, -3, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![3, 2, -3] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![4, 1, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact absurd rfl hdistinct
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![1, 4, 0] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![2, 8, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![1, 4, 5] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![1, 1, 1] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact diamondGap_not_posDef_of_direction (diamondWitness_ne_zero ![1, 4, 0] (by norm_num))
      (by rw [diamondGap_form_indicator]; norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.cons_val, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton])
  · exact absurd rfl hdistinct

/-- **The diamond is an exact tie at `(5,3)`.** -/
theorem diamondDesign_isTie : IsTie diamondDesign :=
  ⟨⟨{0, 1, 2}, by decide, diamondDesign_dominates_spine⟩,
    diamondDesign_no_strictDominator⟩

end Gtz

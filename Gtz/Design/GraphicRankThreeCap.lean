/-
# The graphic family at rank three is capped at six directions

The graphic slice of the campaign — designs whose atoms are whitened incidence rows
of a multigraph, `Gtz.graphicDesign` — is where several concrete instances live
(`Gtz.graphicKFourDesign`, `Gtz.graphicKFourSevenDesign`).  This file settles the
whole slice at rank three, and the answer is that it degenerates above size six.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `edgeTail_ne_edgeHead_of_allHeavy` — all-heavy graphic designs have NO LOOPS.  A
  loop makes the incidence row zero, hence the atom zero, hence the leverage `0`
  rather than `> 1`.
* `graphicRankThree_hasParallelPair` — THE CAP.  Every all-heavy graphic design on
  four vertices with more than six edges has a parallel pair, in the tree's own
  sense `Gtz.HasParallelPair`.  Four vertices carry only six loopless endpoint
  pairs and all-heaviness forbids loops, so the edges collide by pigeonhole and
  colliding endpoint keys give equal or opposite incidence rows.
* `graphicRankThree_exists_jointly_dead_pair` — the consequence, through the
  shipped pruning rule `Gtz.not_dominates_of_parallel`: no dominating triple of an
  all-heavy graphic rank-three design of size above six contains both members of
  the pair.  Such a design therefore carries at most six usable directions and
  lies inside the split / bundled locus the campaign already understands.  The
  graphic slice never reaches a genuine seventh direction.

The tree previously recorded this only in PROSE and only in special cases:
`Gtz/Design/PrimitiveTightClassification.lean` carries a CONJECTURE note about
simple SP-graphic matroids, and `Gtz/Quantitative/DecisionAtlasCellsSevenThree.lean`
a scope remark about one specific replicated instance.  The general theorem is new.

## NOT proved here

Nothing about non-graphic designs, and nothing at vertex ranks other than three.
The cap is a statement about the graphic SLICE; it closes that lane and says
nothing about `Gtz.GtzWeightedHeavy 7 3` itself.

Provenance: scratch report 19 (`graphic73`).  The scratch file consumed the shipped
`Gtz.not_dominates_of_parallel` rather than re-proving it; the equal-orientation
branch below likewise calls the shipped `Gtz.edgeVector_congr`
(`Gtz/Design/EqualityLocus.lean`) instead of repeating its `funext`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.GraphicInstance
import Gtz.Design.EqualityLocus
import Gtz.Reduction.Reductions
import Gtz.Reduction.RayleighCertificate
import Gtz.Ties.TotalTieCorankOne
import Gtz.Reduction.SplitTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## All-heavy graphic designs have no loops -/

/-- An all-heavy graphic design has no zero incidence row: a zero row makes the
atom zero, whose leverage is `0`, not `> 1`. -/
theorem edgeVector_ne_zero_of_allHeavy {edgeCount vertexRank : ℕ}
    (data : GraphDesignData edgeCount vertexRank)
    (hheavy : AllHeavy (graphicDesign data)) (edge : Fin edgeCount) :
    data.graph.edgeVector edge ≠ 0 := by
  intro hzero
  have hatomZero : (graphicDesign data).atom edge = 0 := by
    rw [graphicDesign_atom, graphicAtom_eq_whitenedRow, hzero, Matrix.mulVec_zero, smul_zero]
  have hlev := hheavy edge
  rw [hatomZero] at hlev
  simp only [leverageOf, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero] at hlev
  linarith

/-- Hence no loops: every edge of an all-heavy graphic design joins two
different vertices. -/
theorem edgeTail_ne_edgeHead_of_allHeavy {edgeCount vertexRank : ℕ}
    (data : GraphDesignData edgeCount vertexRank)
    (hheavy : AllHeavy (graphicDesign data)) (edge : Fin edgeCount) :
    data.graph.edgeTail edge ≠ data.graph.edgeHead edge := by
  intro hloop
  refine edgeVector_ne_zero_of_allHeavy data hheavy edge (funext fun coord => ?_)
  simp only [MultigraphOnGround.edgeVector, hloop, Pi.zero_apply, sub_self]

/-! ## The pigeonhole at four vertices -/

/-- The unordered endpoint pair of an edge, as an ordered pair. -/
def endpointKey {edgeCount vertexRank : ℕ} (graph : MultigraphOnGround edgeCount vertexRank)
    (edge : Fin edgeCount) : Fin (vertexRank + 1) × Fin (vertexRank + 1) :=
  (min (graph.edgeTail edge) (graph.edgeHead edge),
    max (graph.edgeTail edge) (graph.edgeHead edge))

/-- Four vertices carry exactly six loopless endpoint pairs. -/
theorem card_loopless_pairs_four :
    (Finset.univ.filter (fun pair : Fin 4 × Fin 4 => pair.1 < pair.2)).card = 6 := by decide

/-- Equal `min`/`max` at four vertices means equal or swapped endpoints. -/
theorem endpoints_eq_or_swapped :
    ∀ tailLeft headLeft tailRight headRight : Fin 4,
      tailLeft ≠ headLeft → tailRight ≠ headRight →
      min tailLeft headLeft = min tailRight headRight →
      max tailLeft headLeft = max tailRight headRight →
      (tailLeft = tailRight ∧ headLeft = headRight) ∨
        (tailLeft = headRight ∧ headLeft = tailRight) := by decide

/-- **More than six edges on four vertices collide.**  Under all-heaviness there
are no loops, so the edges map into the six loopless endpoint pairs. -/
theorem exists_same_endpointKey {edgeCount : ℕ} (hsize : 6 < edgeCount)
    (data : GraphDesignData edgeCount 3) (hheavy : AllHeavy (graphicDesign data)) :
    ∃ edgeLeft edgeRight : Fin edgeCount, edgeLeft ≠ edgeRight ∧
      endpointKey data.graph edgeLeft = endpointKey data.graph edgeRight := by
  have hmaps : ∀ edge ∈ (Finset.univ : Finset (Fin edgeCount)),
      endpointKey data.graph edge ∈
        Finset.univ.filter (fun pair : Fin 4 × Fin 4 => pair.1 < pair.2) := by
    intro edge _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, endpointKey]
    exact min_lt_max.mpr (edgeTail_ne_edgeHead_of_allHeavy data hheavy edge)
  have hcard : (Finset.univ.filter (fun pair : Fin 4 × Fin 4 => pair.1 < pair.2)).card
      < (Finset.univ : Finset (Fin edgeCount)).card := by
    rw [card_loopless_pairs_four, Finset.card_univ, Fintype.card_fin]
    exact hsize
  obtain ⟨edgeLeft, _, edgeRight, _, hne, hkey⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  exact ⟨edgeLeft, edgeRight, hne, hkey⟩

/-- Colliding endpoint keys give equal or opposite incidence rows.  The
equal-orientation branch is the shipped `Gtz.edgeVector_congr`; only the
swapped branch, where the row flips sign, is new. -/
theorem edgeVector_eq_or_neg_of_same_endpointKey {edgeCount : ℕ}
    (data : GraphDesignData edgeCount 3)
    (hheavy : AllHeavy (graphicDesign data)) {edgeLeft edgeRight : Fin edgeCount}
    (hkey : endpointKey data.graph edgeLeft = endpointKey data.graph edgeRight) :
    data.graph.edgeVector edgeLeft = data.graph.edgeVector edgeRight ∨
      data.graph.edgeVector edgeLeft = -data.graph.edgeVector edgeRight := by
  have hmin : min (data.graph.edgeTail edgeLeft) (data.graph.edgeHead edgeLeft)
      = min (data.graph.edgeTail edgeRight) (data.graph.edgeHead edgeRight) :=
    congrArg Prod.fst hkey
  have hmax : max (data.graph.edgeTail edgeLeft) (data.graph.edgeHead edgeLeft)
      = max (data.graph.edgeTail edgeRight) (data.graph.edgeHead edgeRight) :=
    congrArg Prod.snd hkey
  rcases endpoints_eq_or_swapped _ _ _ _
      (edgeTail_ne_edgeHead_of_allHeavy data hheavy edgeLeft)
      (edgeTail_ne_edgeHead_of_allHeavy data hheavy edgeRight) hmin hmax with
    ⟨htail, hhead⟩ | ⟨htail, hhead⟩
  · exact Or.inl (edgeVector_congr htail hhead)
  · refine Or.inr (funext fun coord => ?_)
    simp only [MultigraphOnGround.edgeVector, htail, hhead, Pi.neg_apply]
    ring

/-- **The parallel pair.**  Every all-heavy graphic rank-three design above size six
has two distinct edges whose atoms are proportional. -/
theorem graphicRankThree_exists_parallel_atoms {edgeCount : ℕ} (hsize : 6 < edgeCount)
    (data : GraphDesignData edgeCount 3)
    (hheavy : AllHeavy (graphicDesign data)) :
    ∃ edgeLeft edgeRight : Fin edgeCount, edgeLeft ≠ edgeRight ∧ ∃ scale : ℝ,
      (graphicDesign data).atom edgeRight = scale • (graphicDesign data).atom edgeLeft := by
  obtain ⟨edgeLeft, edgeRight, hne, hkey⟩ := exists_same_endpointKey hsize data hheavy
  have hleftPos : 0 < Real.sqrt (data.conductance edgeLeft / data.weight edgeLeft) :=
    Real.sqrt_pos.mpr (div_pos (data.conductance_pos edgeLeft) (data.weight_pos edgeLeft))
  set scaleLeft := Real.sqrt (data.conductance edgeLeft / data.weight edgeLeft) with hscaleLeft
  set scaleRight := Real.sqrt (data.conductance edgeRight / data.weight edgeRight) with hscaleRight
  refine ⟨edgeLeft, edgeRight, hne, ?_⟩
  rcases edgeVector_eq_or_neg_of_same_endpointKey data hheavy hkey with hvec | hvec
  · refine ⟨scaleRight / scaleLeft, ?_⟩
    rw [graphicDesign_atom, graphicDesign_atom, graphicAtom_eq_whitenedRow,
      graphicAtom_eq_whitenedRow, ← hscaleLeft, ← hscaleRight, ← hvec, smul_smul,
      div_mul_cancel₀ _ hleftPos.ne']
  · refine ⟨-(scaleRight / scaleLeft), ?_⟩
    have hleftNe : scaleLeft ≠ 0 := hleftPos.ne'
    have hcancel : -(scaleRight / scaleLeft) * scaleLeft = -scaleRight := by field_simp
    rw [graphicDesign_atom, graphicDesign_atom, graphicAtom_eq_whitenedRow,
      graphicAtom_eq_whitenedRow, ← hscaleLeft, ← hscaleRight, hvec, Matrix.mulVec_neg,
      smul_neg, smul_neg, smul_smul, hcancel, neg_smul, neg_neg]

/-- **THE GRAPHIC FAMILY AT RANK THREE DEGENERATES ABOVE SIZE SIX.**  Every
all-heavy graphic design on four vertices with more than six edges has a
parallel pair, in the tree's own sense `Gtz.HasParallelPair`: four vertices
carry only six loopless directions, and all-heaviness forbids loops. -/
theorem graphicRankThree_hasParallelPair {edgeCount : ℕ} (hsize : 6 < edgeCount)
    (data : GraphDesignData edgeCount 3)
    (hheavy : AllHeavy (graphicDesign data)) :
    HasParallelPair (graphicDesign data) := by
  obtain ⟨edgeLeft, edgeRight, hne, scale, hscale⟩ :=
    graphicRankThree_exists_parallel_atoms hsize data hheavy
  exact ⟨edgeLeft, edgeRight, scale, hne, hscale⟩

/-- **Two of the atoms are jointly dead.**  Feeding the parallel pair to the
shipped pruning rule `Gtz.not_dominates_of_parallel`: no dominating triple of an
all-heavy graphic rank-three design of size above six contains both.  So such a
design carries at most six usable directions and lies inside the split /
bundled locus the campaign already understands — the graphic slice never
reaches a genuine seventh direction. -/
theorem graphicRankThree_exists_jointly_dead_pair {edgeCount : ℕ} (hsize : 6 < edgeCount)
    (data : GraphDesignData edgeCount 3)
    (hheavy : AllHeavy (graphicDesign data)) :
    ∃ edgeLeft edgeRight : Fin edgeCount, edgeLeft ≠ edgeRight ∧
      ∀ selected : Finset (Fin edgeCount), selected.card = 3 →
        edgeLeft ∈ selected → edgeRight ∈ selected →
          ¬ Dominates (graphicDesign data) selected := by
  obtain ⟨edgeLeft, edgeRight, hne, scale, hscale⟩ :=
    graphicRankThree_exists_parallel_atoms hsize data hheavy
  exact ⟨edgeLeft, edgeRight, hne, fun selected hcard hmemLeft hmemRight =>
    not_dominates_of_parallel (graphicDesign data) selected hcard hmemLeft hmemRight hne hscale⟩

end Gtz

/-
# The series-parallel graphic cap at five elements

`Gtz/Design/PrimitiveTightClassification.lean:216-225` records, in PROSE only,
the sharpest structural conjecture of the rank-three campaign: every tie has an
SP-graphic direction matroid, and a SIMPLE rank-three SP-graphic matroid has at
most FIVE elements.  This file mechanizes the second half — THE CAP — as kernel
theorems stated against the tree's own vocabulary (`Gtz.GraphDesignData`,
`Gtz.graphicDesign`, `Gtz.HasParallelPair`, `Gtz.IsPrimitiveDesign`,
`Gtz.endpointKey`).  The cap needs NO analytic input: no Nesterenko premise, no
tie hypothesis, no `AllHeavy` — it is pure pigeonhole on the four-vertex ground.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `exists_graphicAtom_parallel_of_edgeVector_parallel` — the converse of the
  shipped `Gtz.exists_edgeVector_parallel_of_graphicAtom_parallel`
  (`Gtz/Reduction/SplitTransfer.lean:1980`): parallel incidence rows lift to
  parallel design atoms, at every vertex rank.
* `hasParallelPair_of_loop` — a loop zeroes its incidence row, hence its atom,
  and the zero atom is `0 •` any other atom: a graphic design with a loop and
  at least two edges has a parallel pair.
* `endpointKey_injective_of_not_hasParallelPair` — SIMPLICITY, DECODED: a
  parallel-free graphic rank-three design has no loops and no two edges on the
  same endpoint pair, so `Gtz.endpointKey` is injective.
* `edgeCount_le_six_of_not_hasParallelPair` — the ABSOLUTE simple cap: four
  vertices carry six loopless directions, so a parallel-free graphic
  rank-three design has at most SIX edges.  No size or heaviness hypothesis.
* `graphicRankThree_hasParallelPair_of_six_lt` — strengthens the shipped
  `Gtz.graphicRankThree_hasParallelPair`
  (`Gtz/Design/GraphicRankThreeCap.lean:179`) by DROPPING its `AllHeavy`
  hypothesis: that proof used all-heaviness only to exclude loops, and
  parallel-freeness excludes them for free in contrapositive form.
* `hasAllSixDirections_of_not_hasParallelPair` — the boundary case pinned
  down: a parallel-free graphic rank-three design on six or more edges covers
  ALL six directions — its support is `K4` up to conductances, weights, and
  orientation.
* `seriesParallelGraphic_cap_five` — **THE CAP.**  A parallel-free SP-graphic
  rank-three design has at most FIVE edges.  With
  `seriesParallelGraphic_cap_five_of_isPrimitiveDesign` restating it against
  `Gtz.IsPrimitiveDesign`, the exact hypothesis vocabulary of
  `PrimitiveTightClassification`.
* `seriesParallelGraphic_hasParallelPair_of_six_le` — the hinge-shaped
  contrapositive: at EVERY size `>= 6` an SP-graphic design has a parallel
  pair, which is the conclusion of `Gtz.HingeHoldsAtSize size 3` for such
  designs.  Relative to the shipped cap the new content is exactly size SIX,
  where the SP hypothesis replaces the pigeonhole.
* `diamondData_attains_cap` — SHARPNESS AT FIVE: the diamond `K4 − e`
  (`Gtz.diamondData`, five edges) is parallel-free
  (`Gtz.not_hasParallelPair_diamondDesign`, cited) and series-parallel
  (`diamondGraph_isSeriesParallelSupport`, kernel `decide`).
* `not_hasParallelPair_completeFourDesign` + `completeFourData_isPrimitive_hasAllSixDirections`
  — SHARPNESS OF THE SP HYPOTHESIS: `K4` itself (`Gtz.completeFourData`, six
  edges) is parallel-free and covers all six directions, so the cap at five
  genuinely needs series-parallelness and the absolute cap at six is attained.

## Definitional choice, RECORDED

The tree has NO series-parallel predicate: `Gtz/Reduction/SpCertificates.lean`
is an analytic energy kit for the diamond instance, and every other mention of
series-parallel graphs is prose.  This file therefore defines the predicate,
and the choice is forced by the tree's fixed four-vertex ground: a `K4` MINOR
of a multigraph on exactly four vertices needs four disjoint nonempty branch
sets, hence singleton branch sets, hence all six loopless endpoint pairs
present among the edges — and conversely six present directions ARE a `K4`
subgraph.  So on this ground, having a `K4` minor IS `HasAllSixDirections`,
and K4-minor-freeness — the standard characterization of series-parallel
(multi)graphs (Duffin 1965) — is its negation `IsSeriesParallelSupport`.
Loops and parallel edges never create `K4` minors, so the predicate needs no
simplicity side condition.  No inductive series/parallel construction predicate
is introduced: on a fixed four-vertex ground it would prove the same theorem
through strictly more machinery.

## CITED, not reproved

* `Gtz.endpointKey`, `Gtz.card_loopless_pairs_four`,
  `Gtz.endpoints_eq_or_swapped` (`Gtz/Design/GraphicRankThreeCap.lean`).
* `Gtz.edgeVector_congr`, `Gtz.graphicDesign_atom`,
  `Gtz.graphicAtom_eq_whitenedRow` (`Gtz/Design/EqualityLocus.lean`).
* `Gtz.exists_edgeVector_parallel_of_graphicAtom_parallel`,
  `Gtz.HasParallelPair`, `Gtz.not_hasParallelPair_diamondDesign`
  (`Gtz/Reduction/SplitTransfer.lean`).
* `Gtz.diamondGraph`, `Gtz.diamondData` (`Gtz/Design/DiamondPrimitive.lean`);
  `Gtz.completeFourGraph`, `Gtz.completeFourData`
  (`Gtz/Design/GraphicInstance.lean`).
* `Gtz.IsPrimitiveDesign` (`Gtz/Design/PrimitiveTightClassification.lean`);
  `Gtz.isPrimitiveDesign_iff_not_hasParallelPair`
  (`Gtz/Design/StratumEmptinessLedger.lean:994`) — the tree ALREADY carries the
  primitivity/parallel-pair bridge; an early draft of this file reproved it and
  the duplicate was removed in favor of the citation.

## NOT proved here

The OTHER half of the conjecture — that every tie's direction matroid is
SP-graphic — is analytic and remains open; this file supplies the structural
half it composes with.  Nothing here mentions ties, domination, or
`HingeHoldsAtSize` itself: composing the cap into the hinge requires a
design-level "is graphically represented" predicate the tree does not yet
carry, and inventing one belongs to the classification file, not here.
-/
import Mathlib
import Gtz.Design.GraphicInstance
import Gtz.Design.EqualityLocus
import Gtz.Design.GraphicRankThreeCap
import Gtz.Design.DiamondPrimitive
import Gtz.Reduction.SplitTransfer
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.StratumEmptinessLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The series-parallel predicate on the four-vertex ground -/

/-- The graph realizes all six loopless directions on the four-vertex ground.
On a fixed four-vertex ground this is exactly "has a `K4` minor": a `K4` minor
needs four disjoint nonempty branch sets, hence singletons, hence every one of
the six loopless endpoint pairs present among the edges; conversely six
present directions are a `K4` subgraph. -/
def HasAllSixDirections {edgeCount : ℕ} (graph : MultigraphOnGround edgeCount 3) : Prop :=
  ∀ pair : Fin 4 × Fin 4, pair.1 < pair.2 →
    ∃ edge : Fin edgeCount, endpointKey graph edge = pair

/-- The graph is series-parallel in the matroid-relevant sense: it has no `K4`
minor (Duffin 1965), which on the four-vertex ground is the negation of
`HasAllSixDirections`.  Loops and parallel edges never create `K4` minors, so
no simplicity side condition belongs here. -/
def IsSeriesParallelSupport {edgeCount : ℕ} (graph : MultigraphOnGround edgeCount 3) : Prop :=
  ¬ HasAllSixDirections graph

/-! ## Parallel edge vectors lift to parallel atoms -/

/-- **The converse of the shipped descent lemma**
`Gtz.exists_edgeVector_parallel_of_graphicAtom_parallel`: proportional reduced
incidence rows give proportional design atoms.  The atom is the whitened row
scaled by the positive factor `√(conductance/weight)`, so the ratio transports
with a positive correction. -/
theorem exists_graphicAtom_parallel_of_edgeVector_parallel {edgeCount vertexRank : ℕ}
    (data : GraphDesignData edgeCount vertexRank) (keptEdge dropEdge : Fin edgeCount)
    {scale : ℝ}
    (hrow : data.graph.edgeVector dropEdge = scale • data.graph.edgeVector keptEdge) :
    ∃ ratio : ℝ,
      (graphicDesign data).atom dropEdge = ratio • (graphicDesign data).atom keptEdge := by
  have hkeptPos : 0 < Real.sqrt (data.conductance keptEdge / data.weight keptEdge) :=
    Real.sqrt_pos.mpr (div_pos (data.conductance_pos keptEdge) (data.weight_pos keptEdge))
  refine ⟨Real.sqrt (data.conductance dropEdge / data.weight dropEdge) * scale
      / Real.sqrt (data.conductance keptEdge / data.weight keptEdge), ?_⟩
  rw [graphicDesign_atom, graphicDesign_atom, graphicAtom_eq_whitenedRow,
    graphicAtom_eq_whitenedRow, hrow, Matrix.mulVec_smul, smul_smul, smul_smul,
    div_mul_cancel₀ _ hkeptPos.ne']

/-! ## Loops force a parallel pair -/

/-- A loop zeroes the incidence row, hence the atom. -/
theorem graphicAtom_eq_zero_of_loop {edgeCount vertexRank : ℕ}
    (data : GraphDesignData edgeCount vertexRank) {loopEdge : Fin edgeCount}
    (hloop : data.graph.edgeTail loopEdge = data.graph.edgeHead loopEdge) :
    (graphicDesign data).atom loopEdge = 0 := by
  have hrowZero : data.graph.edgeVector loopEdge = 0 := by
    funext coord
    simp only [MultigraphOnGround.edgeVector, hloop, Pi.zero_apply, sub_self]
  rw [graphicDesign_atom, graphicAtom_eq_whitenedRow, hrowZero, Matrix.mulVec_zero, smul_zero]

/-- The zero atom of a loop is `0 •` any other atom, so a graphic design with a
loop and at least two edges has a parallel pair. -/
theorem hasParallelPair_of_loop {edgeCount vertexRank : ℕ} (hsize : 2 ≤ edgeCount)
    (data : GraphDesignData edgeCount vertexRank) {loopEdge : Fin edgeCount}
    (hloop : data.graph.edgeTail loopEdge = data.graph.edgeHead loopEdge) :
    HasParallelPair (graphicDesign data) := by
  haveI : Nontrivial (Fin edgeCount) := Fin.nontrivial_iff_two_le.mpr hsize
  obtain ⟨otherEdge, hne⟩ := exists_ne loopEdge
  exact ⟨otherEdge, loopEdge, 0, hne, by
    rw [graphicAtom_eq_zero_of_loop data hloop, zero_smul]⟩

/-- Contrapositive: a parallel-free graphic design with at least two edges has
no loops. -/
theorem edgeTail_ne_edgeHead_of_not_hasParallelPair {edgeCount vertexRank : ℕ}
    (hsize : 2 ≤ edgeCount) (data : GraphDesignData edgeCount vertexRank)
    (hprimitive : ¬ HasParallelPair (graphicDesign data)) (edge : Fin edgeCount) :
    data.graph.edgeTail edge ≠ data.graph.edgeHead edge :=
  fun hloop => hprimitive (hasParallelPair_of_loop hsize data hloop)

/-! ## Colliding endpoint keys force a parallel pair -/

/-- Colliding endpoint keys give equal or opposite incidence rows.  The same
statement as the shipped `Gtz.edgeVector_eq_or_neg_of_same_endpointKey`
(`Gtz/Design/GraphicRankThreeCap.lean:129`) with the `AllHeavy` hypothesis
replaced by the two loopless facts it was used to supply. -/
theorem edgeVector_eq_or_neg_of_same_endpointKey_of_loopless {edgeCount : ℕ}
    (graph : MultigraphOnGround edgeCount 3) {edgeLeft edgeRight : Fin edgeCount}
    (hleftLoopless : graph.edgeTail edgeLeft ≠ graph.edgeHead edgeLeft)
    (hrightLoopless : graph.edgeTail edgeRight ≠ graph.edgeHead edgeRight)
    (hkey : endpointKey graph edgeLeft = endpointKey graph edgeRight) :
    graph.edgeVector edgeLeft = graph.edgeVector edgeRight ∨
      graph.edgeVector edgeLeft = -graph.edgeVector edgeRight := by
  have hmin : min (graph.edgeTail edgeLeft) (graph.edgeHead edgeLeft)
      = min (graph.edgeTail edgeRight) (graph.edgeHead edgeRight) :=
    congrArg Prod.fst hkey
  have hmax : max (graph.edgeTail edgeLeft) (graph.edgeHead edgeLeft)
      = max (graph.edgeTail edgeRight) (graph.edgeHead edgeRight) :=
    congrArg Prod.snd hkey
  rcases endpoints_eq_or_swapped _ _ _ _ hleftLoopless hrightLoopless hmin hmax with
    ⟨htail, hhead⟩ | ⟨htail, hhead⟩
  · exact Or.inl (edgeVector_congr htail hhead)
  · refine Or.inr (funext fun coord => ?_)
    simp only [MultigraphOnGround.edgeVector, htail, hhead, Pi.neg_apply]
    ring

/-- **Simplicity, decoded.**  A parallel-free graphic rank-three design has an
injective endpoint-key map: two edges on the same endpoint pair would carry
equal-or-opposite rows, which lift to parallel atoms. -/
theorem endpointKey_injective_of_not_hasParallelPair {edgeCount : ℕ}
    (hsize : 2 ≤ edgeCount) (data : GraphDesignData edgeCount 3)
    (hprimitive : ¬ HasParallelPair (graphicDesign data)) :
    Function.Injective (endpointKey data.graph) := by
  intro edgeLeft edgeRight hkey
  by_contra hne
  have hleftLoopless :=
    edgeTail_ne_edgeHead_of_not_hasParallelPair hsize data hprimitive edgeLeft
  have hrightLoopless :=
    edgeTail_ne_edgeHead_of_not_hasParallelPair hsize data hprimitive edgeRight
  rcases edgeVector_eq_or_neg_of_same_endpointKey_of_loopless data.graph
      hleftLoopless hrightLoopless hkey with hrow | hrow
  · obtain ⟨ratio, hatom⟩ := exists_graphicAtom_parallel_of_edgeVector_parallel data
      edgeLeft edgeRight (scale := 1) (by rw [one_smul]; exact hrow.symm)
    exact hprimitive ⟨edgeLeft, edgeRight, ratio, hne, hatom⟩
  · obtain ⟨ratio, hatom⟩ := exists_graphicAtom_parallel_of_edgeVector_parallel data
      edgeLeft edgeRight (scale := -1) (by rw [neg_one_smul, hrow, neg_neg])
    exact hprimitive ⟨edgeLeft, edgeRight, ratio, hne, hatom⟩

/-! ## The pigeonhole ledger -/

/-- The endpoint keys of a parallel-free design land in the six loopless
pairs. -/
theorem endpointKey_image_subset_looplessPairs {edgeCount : ℕ}
    (hsize : 2 ≤ edgeCount) (data : GraphDesignData edgeCount 3)
    (hprimitive : ¬ HasParallelPair (graphicDesign data)) :
    Finset.univ.image (endpointKey data.graph)
      ⊆ Finset.univ.filter (fun pair : Fin 4 × Fin 4 => pair.1 < pair.2) := by
  intro pair hpairMem
  obtain ⟨edge, _, hedgeKey⟩ := Finset.mem_image.mp hpairMem
  subst hedgeKey
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, endpointKey]
  exact min_lt_max.mpr
    (edgeTail_ne_edgeHead_of_not_hasParallelPair hsize data hprimitive edge)

/-- Injectivity makes the key image as large as the edge set. -/
theorem card_endpointKey_image_of_not_hasParallelPair {edgeCount : ℕ}
    (hsize : 2 ≤ edgeCount) (data : GraphDesignData edgeCount 3)
    (hprimitive : ¬ HasParallelPair (graphicDesign data)) :
    (Finset.univ.image (endpointKey data.graph)).card = edgeCount := by
  rw [Finset.card_image_of_injective _
    (endpointKey_injective_of_not_hasParallelPair hsize data hprimitive),
    Finset.card_univ, Fintype.card_fin]

/-- **The absolute simple cap at six.**  A parallel-free graphic rank-three
design has at most six edges: four vertices carry only six loopless
directions.  No size, heaviness, or series-parallel hypothesis. -/
theorem edgeCount_le_six_of_not_hasParallelPair {edgeCount : ℕ}
    (data : GraphDesignData edgeCount 3)
    (hprimitive : ¬ HasParallelPair (graphicDesign data)) :
    edgeCount ≤ 6 := by
  by_cases hsize : 2 ≤ edgeCount
  · have hcardLe := Finset.card_le_card
      (endpointKey_image_subset_looplessPairs hsize data hprimitive)
    rwa [card_endpointKey_image_of_not_hasParallelPair hsize data hprimitive,
      card_loopless_pairs_four] at hcardLe
  · omega

/-- Strengthens the shipped cap `Gtz.graphicRankThree_hasParallelPair`
(`Gtz/Design/GraphicRankThreeCap.lean:179`) by dropping its `AllHeavy`
hypothesis: above six edges EVERY graphic rank-three design has a parallel
pair — all-heaviness was only excluding loops, and a loop is itself half of a
parallel pair. -/
theorem graphicRankThree_hasParallelPair_of_six_lt {edgeCount : ℕ} (hsize : 6 < edgeCount)
    (data : GraphDesignData edgeCount 3) :
    HasParallelPair (graphicDesign data) := by
  by_contra hprimitive
  exact absurd (edgeCount_le_six_of_not_hasParallelPair data hprimitive) (by omega)

/-- **The boundary case, pinned down.**  A parallel-free graphic rank-three
design on six or more edges covers ALL six directions: injectivity forces the
key image, a subset of the six loopless pairs, to have full cardinality. -/
theorem hasAllSixDirections_of_not_hasParallelPair {edgeCount : ℕ} (hsize : 6 ≤ edgeCount)
    (data : GraphDesignData edgeCount 3)
    (hprimitive : ¬ HasParallelPair (graphicDesign data)) :
    HasAllSixDirections data.graph := by
  have hsizeTwo : 2 ≤ edgeCount := by omega
  have himageEq : Finset.univ.image (endpointKey data.graph)
      = Finset.univ.filter (fun pair : Fin 4 × Fin 4 => pair.1 < pair.2) := by
    refine Finset.eq_of_subset_of_card_le
      (endpointKey_image_subset_looplessPairs hsizeTwo data hprimitive) ?_
    rw [card_endpointKey_image_of_not_hasParallelPair hsizeTwo data hprimitive,
      card_loopless_pairs_four]
    exact hsize
  intro pair hpairLt
  have hpairMem : pair ∈ Finset.univ.image (endpointKey data.graph) := by
    rw [himageEq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ pair, hpairLt⟩
  obtain ⟨edge, _, hedgeKey⟩ := Finset.mem_image.mp hpairMem
  exact ⟨edge, hedgeKey⟩

/-! ## The cap -/

/-- **THE SERIES-PARALLEL GRAPHIC CAP AT FIVE.**  A parallel-free (simple
direction matroid) series-parallel (no `K4` minor) graphic rank-three design
has at most FIVE edges.  This is the combinatorial half of the conjecture at
`Gtz/Design/PrimitiveTightClassification.lean:216-225`, and it is
unconditional: no analytic input enters. -/
theorem seriesParallelGraphic_cap_five {edgeCount : ℕ}
    (data : GraphDesignData edgeCount 3)
    (hprimitive : ¬ HasParallelPair (graphicDesign data))
    (hseriesParallel : IsSeriesParallelSupport data.graph) :
    edgeCount ≤ 5 := by
  by_contra hbig
  exact hseriesParallel
    (hasAllSixDirections_of_not_hasParallelPair (by omega) data hprimitive)

/-- The hinge-shaped contrapositive: at EVERY size at least six, a
series-parallel graphic rank-three design has a parallel pair — the conclusion
of `Gtz.HingeHoldsAtSize size 3` on the SP-graphic slice.  Relative to the
shipped `Gtz.graphicRankThree_hasParallelPair` the new content is exactly size
six, where the series-parallel hypothesis replaces the pigeonhole. -/
theorem seriesParallelGraphic_hasParallelPair_of_six_le {edgeCount : ℕ}
    (hsize : 6 ≤ edgeCount) (data : GraphDesignData edgeCount 3)
    (hseriesParallel : IsSeriesParallelSupport data.graph) :
    HasParallelPair (graphicDesign data) := by
  by_contra hprimitive
  exact hseriesParallel (hasAllSixDirections_of_not_hasParallelPair hsize data hprimitive)

/-! ## The bridge to `IsPrimitiveDesign` -/

/-- The cap in the classification file's own hypothesis vocabulary, through the
shipped bridge `Gtz.isPrimitiveDesign_iff_not_hasParallelPair`
(`Gtz/Design/StratumEmptinessLedger.lean:994`). -/
theorem seriesParallelGraphic_cap_five_of_isPrimitiveDesign {edgeCount : ℕ}
    (data : GraphDesignData edgeCount 3)
    (hprimitive : IsPrimitiveDesign (graphicDesign data))
    (hseriesParallel : IsSeriesParallelSupport data.graph) :
    edgeCount ≤ 5 :=
  seriesParallelGraphic_cap_five data
    ((isPrimitiveDesign_iff_not_hasParallelPair (graphicDesign data)).mp hprimitive)
    hseriesParallel

/-! ## Sharpness at five: the diamond -/

/-- The diamond misses the direction `{2, 3}`: it is series-parallel. -/
theorem diamondGraph_isSeriesParallelSupport : IsSeriesParallelSupport diamondGraph := by
  intro hcovers
  have hmissing : ¬ ∃ edge : Fin 5,
      endpointKey diamondGraph edge = ((2 : Fin 4), (3 : Fin 4)) := by decide
  exact hmissing (hcovers ((2 : Fin 4), (3 : Fin 4)) (by decide))

/-- **The cap is attained.**  The diamond `K4 − e` at five edges satisfies both
hypotheses of `seriesParallelGraphic_cap_five`: parallel-free (the shipped
`Gtz.not_hasParallelPair_diamondDesign`) and series-parallel. -/
theorem diamondData_attains_cap :
    ¬ HasParallelPair (graphicDesign diamondData)
      ∧ IsSeriesParallelSupport diamondData.graph :=
  ⟨not_hasParallelPair_diamondDesign, diamondGraph_isSeriesParallelSupport⟩

/-! ## Sharpness of the series-parallel hypothesis: `K4` -/

/-- `K4` covers all six directions, by kernel evaluation of the six endpoint
keys. -/
theorem completeFourGraph_hasAllSixDirections : HasAllSixDirections completeFourGraph := by
  show ∀ pair : Fin 4 × Fin 4, pair.1 < pair.2 →
    ∃ edge : Fin 6, endpointKey completeFourGraph edge = pair
  decide

/-- The six reduced incidence rows of `K4`, grounded at the last vertex: the
three edges into the ground are the standard basis, the three chords the
differences. -/
theorem completeFourEdgeVector_eq (edge : Fin 6) :
    completeFourData.graph.edgeVector edge
      = ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]] edge := by
  funext coord
  fin_cases edge <;> fin_cases coord <;>
    simp [completeFourData, completeFourGraph, MultigraphOnGround.edgeVector]

/-- **`K4` has no parallel pair.**  Its six incidence rows are pairwise
non-proportional, and proportional atoms would descend to proportional rows
through the shipped `Gtz.exists_edgeVector_parallel_of_graphicAtom_parallel`.
Same bash as the shipped `Gtz.not_hasParallelPair_diamondDesign`, one edge
larger. -/
theorem not_hasParallelPair_completeFourDesign :
    ¬ HasParallelPair (graphicDesign completeFourData) := by
  rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
  obtain ⟨scale, hrow⟩ :=
    exists_edgeVector_parallel_of_graphicAtom_parallel completeFourData
      keptLabel dropLabel hparallel
  rw [completeFourEdgeVector_eq, completeFourEdgeVector_eq] at hrow
  have hfirstCoord := congrFun hrow 0
  have hsecondCoord := congrFun hrow 1
  have hthirdCoord := congrFun hrow 2
  clear hrow hparallel
  fin_cases keptLabel <;> fin_cases dropLabel
  all_goals (try exact absurd rfl hdistinct)
  all_goals (try norm_num [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hfirstCoord)
  all_goals (try norm_num [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hsecondCoord)
  all_goals (try norm_num [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hthirdCoord)
  all_goals linarith

/-- **The series-parallel hypothesis is not droppable.**  `K4` at six edges is
parallel-free with all six directions present: the absolute cap at six is
attained, and only the `K4` minor stands between six and five. -/
theorem completeFourData_isPrimitive_hasAllSixDirections :
    ¬ HasParallelPair (graphicDesign completeFourData)
      ∧ HasAllSixDirections completeFourData.graph :=
  ⟨not_hasParallelPair_completeFourDesign, completeFourGraph_hasAllSixDirections⟩

end Gtz

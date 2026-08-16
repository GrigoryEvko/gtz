/-
The quarter-slack interaction graph on the labels of a weighted design.

`Gtz/Wave/TripleDeterminantCells.lean` proves that a triple whose three pair
minors carry a factor four of slack has a positive third minor, for either sign
of the triple product.  That cell is a statement about ONE triple.  This module
reads it as a GRAPH on all the labels at once: put an edge between two heavy
labels when their pair carries the factor four.  A triangle in that graph is a
strictly dominating triple, so the objective follows from a triangle.

Three things come out of that reading.

The graph lives on the heavy set, which `Gtz.subset_heavyLabels_of_posDef` shows
is the only place a dominator can sit, and which `Gtz.rank_le_card_heavyLabels`
shows has at least `rank` elements.  So the vertex set is never too small.

The non-edges are budgeted.  `Gtz.sum_erase_sq_projectionRow` prices the
off-diagonal energy of a row at exactly `P_cc (1 - P_cc)`, and the diagonal sums
to the rank, so the total off-diagonal energy is `rank - ∑ P_cc ^ 2` and Cauchy
gives `rank - rank ^ 2 / size`.  Each non-edge spends at least its excess
product against that budget.  The budget therefore forces an edge once the
excesses are large enough, and `Gtz.exists_quarterSlack_of_sq_sum_excess_gt`
is that statement.

At six labels a triangle is forced by Ramsey rather than by counting, because
`R(3,3) = 6`: any symmetric relation on six points carries a triangle or an
independent triple.  `Gtz.exists_mono_triple_of_six` proves that from the
pigeonhole, and it is the exact combinatorial fact the budget wants to consume.

The last section says the route does not close, and it says it with an explicit
witness rather than a census.  Six equiangular lines in `ℝ³` — the icosahedral
diameters, whose Gram is a symmetric conference matrix of order six — give a
symmetric idempotent of trace three with EVERY diagonal entry `1/2` and EVERY
off-diagonal square `1/20`.  At uniform weight every excess is `1/3`, so every
pair has excess product `1/9` against `4 P_cd ^ 2 = 1/5`, and NO pair is an
edge.  The graph is empty, so no triangle exists anywhere, yet ten of the twenty
triples are strictly dominating.  `Gtz.conferenceDesign_quarterSlack_empty` and
`Gtz.not_forall_exists_quarterSlackTriangle` record that.

The witness also prices the constant.  The excess product beats the off-diagonal
square by exactly `20/9` at that configuration, and one of its triples fails, so
no cell of this shape with a constant below `20/9` can be sound.
-/
import Gtz.Wave.TripleDeterminantCells
import Gtz.Wave.ProjectionBlockObjective
import Gtz.Wave.ThreeLinesDominanceNoGo
import Gtz.Quantitative.RealnessEngine
import Gtz.Design.LeverageBound

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## 1. The excess, and the weight-free reading of the pair test -/

/-- The excess of a label: how far its projection diagonal sits above its
weight.  `Gtz.heavyLabels` is exactly the set where this is positive. -/
noncomputable def projectionExcess (design : WeightedDesign size rank)
    (atomIndex : Fin size) : ℝ :=
  projectionOfDesign design atomIndex atomIndex - design.weight atomIndex

theorem projectionExcess_eq_weight_mul (design : WeightedDesign size rank)
    (atomIndex : Fin size) :
    projectionExcess design atomIndex
      = design.weight atomIndex * (leverageOf (design.atom atomIndex) - 1) := by
  rw [projectionExcess, projectionOfDesign_diagonal]; ring

theorem projectionExcess_pos_iff (design : WeightedDesign size rank)
    (atomIndex : Fin size) :
    0 < projectionExcess design atomIndex ↔ 1 < leverageOf (design.atom atomIndex) := by
  rw [projectionExcess_eq_weight_mul]
  have hweight := design.weight_pos atomIndex
  constructor
  · intro hpos; nlinarith
  · intro hlev; nlinarith

theorem mem_heavyLabels_iff_projectionExcess_pos (design : WeightedDesign size rank)
    (atomIndex : Fin size) :
    atomIndex ∈ heavyLabels design ↔ 0 < projectionExcess design atomIndex := by
  rw [mem_heavyLabels_iff, projectionExcess]
  constructor <;> intro h <;> linarith

theorem projectionExcess_lt_one (design : WeightedDesign size rank)
    (atomIndex : Fin size) : projectionExcess design atomIndex < 1 := by
  have hle := projectionDiagonal_le_one' design atomIndex
  have hweight := design.weight_pos atomIndex
  rw [projectionExcess]; linarith

theorem projectionExcess_le_diagonal (design : WeightedDesign size rank)
    (atomIndex : Fin size) :
    projectionExcess design atomIndex ≤ projectionOfDesign design atomIndex atomIndex := by
  have hweight := design.weight_pos atomIndex
  rw [projectionExcess]; linarith

/-- **The excesses total `rank - 1`.**  The diagonal totals the rank and the
weights total one, so the whole heavy budget of a design is `rank - 1`. -/
theorem sum_projectionExcess (design : WeightedDesign size rank) :
    ∑ atomIndex, projectionExcess design atomIndex = (rank : ℝ) - 1 := by
  have hsplit : ∑ atomIndex, projectionExcess design atomIndex
      = (∑ atomIndex, projectionOfDesign design atomIndex atomIndex)
        - ∑ atomIndex, design.weight atomIndex := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => rfl
  rw [hsplit, sum_projectionDiagonal, design.weight_sum_one]

/-- The quarter-slack relation on a pair of labels, read on the projection. -/
def QuarterSlack (design : WeightedDesign size rank) (first second : Fin size) : Prop :=
  4 * projectionOfDesign design first second ^ 2
    < projectionExcess design first * projectionExcess design second

theorem quarterSlack_symm (design : WeightedDesign size rank) (first second : Fin size) :
    QuarterSlack design first second ↔ QuarterSlack design second first := by
  rw [QuarterSlack, QuarterSlack]
  have hentry : projectionOfDesign design first second
      = projectionOfDesign design second first := by
    have hsymm := projectionOfDesign_transpose design
    calc projectionOfDesign design first second
        = (projectionOfDesign design)ᵀ second first := rfl
      _ = projectionOfDesign design second first := by rw [hsymm]
  rw [hentry, mul_comm (projectionExcess design first)]

/-- **THE WEIGHT-FREE BRIDGE.**  The quarter-slack test on the projection block
is the quarter-slack test on the Gram, with the weights cancelled on both sides.
The projection entry carries `√(w_c) √(w_d)` and the excess carries `w_c`, so
the common factor `w_c w_d` divides out and the surviving statement mentions no
weight at all.  This is what lets the landed Gram cell fire on a graph defined
from the projection. -/
theorem quarterSlack_iff_gram (design : WeightedDesign size rank) (first second : Fin size) :
    QuarterSlack design first second
      ↔ 4 * (design.atom first ⬝ᵥ design.atom second) ^ 2
          < (leverageOf (design.atom first) - 1) * (leverageOf (design.atom second) - 1) := by
  have hfirst := design.weight_pos first
  have hsecond := design.weight_pos second
  have hrootFirst : Real.sqrt (design.weight first) * Real.sqrt (design.weight first)
      = design.weight first := Real.mul_self_sqrt hfirst.le
  have hrootSecond : Real.sqrt (design.weight second) * Real.sqrt (design.weight second)
      = design.weight second := Real.mul_self_sqrt hsecond.le
  have hproduct : 0 < design.weight first * design.weight second := mul_pos hfirst hsecond
  rw [QuarterSlack, projectionOfDesign_apply, projectionExcess_eq_weight_mul,
    projectionExcess_eq_weight_mul]
  have hleft : 4 * (Real.sqrt (design.weight first) * Real.sqrt (design.weight second)
        * (design.atom first ⬝ᵥ design.atom second)) ^ 2
      = design.weight first * design.weight second
          * (4 * (design.atom first ⬝ᵥ design.atom second) ^ 2) := by
    have hexpand : (Real.sqrt (design.weight first) * Real.sqrt (design.weight second)
          * (design.atom first ⬝ᵥ design.atom second)) ^ 2
        = (Real.sqrt (design.weight first) * Real.sqrt (design.weight first))
            * (Real.sqrt (design.weight second) * Real.sqrt (design.weight second))
            * (design.atom first ⬝ᵥ design.atom second) ^ 2 := by ring
    rw [hexpand, hrootFirst, hrootSecond]; ring
  have hright : design.weight first * (leverageOf (design.atom first) - 1)
        * (design.weight second * (leverageOf (design.atom second) - 1))
      = design.weight first * design.weight second
          * ((leverageOf (design.atom first) - 1) * (leverageOf (design.atom second) - 1)) := by
    ring
  rw [hleft, hright]
  constructor
  · intro hlt
    exact lt_of_mul_lt_mul_left hlt hproduct.le
  · intro hlt
    exact mul_lt_mul_of_pos_left hlt hproduct

/-! ## 2. The triangle certificate -/

/-- Three distinct heavy labels whose three pairs all carry the quarter slack. -/
def QuarterSlackTriangle {m : ℕ} (design : WeightedDesign m 3) (x y z : Fin m) : Prop :=
  x ≠ y ∧ x ≠ z ∧ y ≠ z
    ∧ 0 < projectionExcess design x ∧ 0 < projectionExcess design y
    ∧ 0 < projectionExcess design z
    ∧ QuarterSlack design x y ∧ QuarterSlack design x z ∧ QuarterSlack design y z

/-- **A TRIANGLE IS A STRICT DOMINATOR.**  The landed quarter-slack cell needs
three heavy leverages and three Gram slacks, and the bridge turns the graph's
edges into exactly those slacks. -/
theorem subsetSum_posDef_of_quarterSlackTriangle {m : ℕ} (design : WeightedDesign m 3)
    (x y z : Fin m) (htriangle : QuarterSlackTriangle design x y z) :
    (subsetSum design ({x, y, z} : Finset (Fin m)) - 1).PosDef := by
  obtain ⟨hxy, hxz, hyz, hx, hy, hz, hslackXY, hslackXZ, hslackYZ⟩ := htriangle
  rw [projectionExcess_pos_iff] at hx hy hz
  rw [quarterSlack_iff_gram] at hslackXY hslackXZ hslackYZ
  exact subsetSum_posDef_of_quarterSlack design x y z hxy hxz hyz hx hy hz
    hslackXY hslackXZ hslackYZ

/-- A triangle anywhere gives the existential the objective asks for. -/
theorem exists_posDef_of_quarterSlackTriangle {m : ℕ} (design : WeightedDesign m 3)
    (x y z : Fin m) (htriangle : QuarterSlackTriangle design x y z) :
    ∃ selected : Finset (Fin m), selected.card = 3 ∧ (subsetSum design selected - 1).PosDef := by
  have hposDef := subsetSum_posDef_of_quarterSlackTriangle design x y z htriangle
  obtain ⟨hxy, hxz, hyz, _, _, _, _, _, _⟩ := htriangle
  refine ⟨{x, y, z}, ?_, hposDef⟩
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]; exact hyz
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun hmem => hmem.elim hxy hxz

/-- If every primitive design carries a triangle, the campaign's design-level
objective follows.  This is the shape the graph route would close in. -/
theorem consolidatedStrictTripleDesign_of_forall_quarterSlackTriangle
    (hgraph : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ x y z : Fin 6, QuarterSlackTriangle design x y z) :
    ConsolidatedStrictTripleDesign := by
  intro design hprimitive
  obtain ⟨x, y, z, htriangle⟩ := hgraph design hprimitive
  exact exists_posDef_of_quarterSlackTriangle design x y z htriangle

/-! ## 3. The off-diagonal energy budget -/

/-- **THE TOTAL OFF-DIAGONAL ENERGY.**  Row by row the off-diagonal squares
total `P_cc (1 - P_cc)`, so over the whole matrix they total `rank - ∑ P_cc ^ 2`.
RANK enters here and nowhere else in this section: the diagonal sums to the
rank. -/
theorem sum_sum_erase_sq_projection (design : WeightedDesign size rank) :
    ∑ rowIndex, ∑ colIndex ∈ Finset.univ.erase rowIndex,
        projectionOfDesign design rowIndex colIndex ^ 2
      = (rank : ℝ) - ∑ rowIndex, projectionOfDesign design rowIndex rowIndex ^ 2 := by
  have hrows : ∀ rowIndex : Fin size,
      ∑ colIndex ∈ Finset.univ.erase rowIndex,
          projectionOfDesign design rowIndex colIndex ^ 2
        = projectionOfDesign design rowIndex rowIndex
          - projectionOfDesign design rowIndex rowIndex ^ 2 := by
    intro rowIndex
    rw [sum_erase_sq_projectionRow design rowIndex]; ring
  rw [Finset.sum_congr rfl fun rowIndex _ => hrows rowIndex, Finset.sum_sub_distrib,
    sum_projectionDiagonal]

/-- Cauchy-Schwarz against the constant vector: the squared diagonal is at least
the squared rank over the label count. -/
theorem sq_rank_le_card_mul_sum_sq_diagonal (design : WeightedDesign size rank) :
    ((rank : ℝ)) ^ 2
      ≤ (size : ℝ) * ∑ rowIndex, projectionOfDesign design rowIndex rowIndex ^ 2 := by
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin size)))
    (f := fun rowIndex => projectionOfDesign design rowIndex rowIndex)
  rw [sum_projectionDiagonal] at hcauchy
  simpa using hcauchy

/-- **THE ENERGY CEILING.**  The off-diagonal energy of the whole projection is
at most `rank - rank ^ 2 / size`.  At `(6, 3)` this is `3/2`, so the unordered
pair energy is at most `3/4`. -/
theorem sum_sum_erase_sq_projection_le (design : WeightedDesign size rank) (hsize : 0 < size) :
    ∑ rowIndex, ∑ colIndex ∈ Finset.univ.erase rowIndex,
        projectionOfDesign design rowIndex colIndex ^ 2
      ≤ (rank : ℝ) - (rank : ℝ) ^ 2 / (size : ℝ) := by
  have hpos : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsize
  have hcauchy := sq_rank_le_card_mul_sum_sq_diagonal design
  rw [sum_sum_erase_sq_projection]
  have hbound : (rank : ℝ) ^ 2 / (size : ℝ)
      ≤ ∑ rowIndex, projectionOfDesign design rowIndex rowIndex ^ 2 := by
    rw [div_le_iff₀ hpos]; nlinarith
  linarith

/-- The `(6, 3)` reading of the ceiling. -/
theorem sum_sum_erase_sq_projection_le_six_three (design : WeightedDesign 6 3) :
    ∑ rowIndex, ∑ colIndex ∈ Finset.univ.erase rowIndex,
        projectionOfDesign design rowIndex colIndex ^ 2 ≤ 3 / 2 := by
  have hbound := sum_sum_erase_sq_projection_le design (by norm_num)
  have hvalue : ((3 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) ^ 2 / ((6 : ℕ) : ℝ) = 3 / 2 := by norm_num
  rw [hvalue] at hbound
  exact hbound

/-! ## 4. The non-edge budget forces an edge -/

/-- The square of a sum minus the sum of squares is the ordered off-diagonal
double sum.  Elementary, and it is the shape the budget consumes. -/
theorem sq_sum_sub_sum_sq_eq_sum_erase {ι : Type*} [DecidableEq ι] (labels : Finset ι)
    (values : ι → ℝ) :
    (∑ index ∈ labels, values index) ^ 2 - ∑ index ∈ labels, values index ^ 2
      = ∑ first ∈ labels, ∑ second ∈ labels.erase first, values first * values second := by
  have hsplit : ∀ first ∈ labels,
      ∑ second ∈ labels, values first * values second
        = values first ^ 2 + ∑ second ∈ labels.erase first, values first * values second := by
    intro first hfirst
    rw [← Finset.add_sum_erase labels (fun second => values first * values second) hfirst]
    ring_nf
  have hsquare : (∑ index ∈ labels, values index) ^ 2
      = ∑ first ∈ labels, ∑ second ∈ labels, values first * values second := by
    rw [sq, Finset.sum_mul_sum]
  rw [hsquare, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  ring

/-- Every ordered off-diagonal pair inside a label set is bounded by the whole
matrix energy, because the summands are squares. -/
theorem sum_erase_sq_subset_le {m : ℕ} (design : WeightedDesign m rank)
    (labels : Finset (Fin m)) :
    ∑ first ∈ labels, ∑ second ∈ labels.erase first,
        projectionOfDesign design first second ^ 2
      ≤ ∑ first, ∑ second ∈ Finset.univ.erase first,
          projectionOfDesign design first second ^ 2 := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ labels) ?_ |>.trans ?_
  · intro first _ _
    exact Finset.sum_nonneg fun second _ => sq_nonneg _
  · refine Finset.sum_le_sum fun first _ => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun second _ _ => sq_nonneg _
    exact Finset.erase_subset_erase first (Finset.subset_univ labels)

/-- **THE BUDGET FORCES AN EDGE.**  If the excess mass on a label set beats four
times the whole off-diagonal energy, some pair of that set carries the quarter
slack.  Contrapositive of the non-edge accounting: a non-edge spends at least
its excess product against a budget the rank caps. -/
theorem exists_quarterSlack_of_sq_sum_excess_gt {m : ℕ} (design : WeightedDesign m rank)
    (labels : Finset (Fin m))
    (hgt : 4 * ((rank : ℝ) - ∑ rowIndex, projectionOfDesign design rowIndex rowIndex ^ 2)
      < (∑ index ∈ labels, projectionExcess design index) ^ 2
        - ∑ index ∈ labels, projectionExcess design index ^ 2) :
    ∃ first ∈ labels, ∃ second ∈ labels, first ≠ second ∧ QuarterSlack design first second := by
  by_contra hcontra
  push Not at hcontra
  have hnonEdge : ∀ first ∈ labels, ∀ second ∈ labels.erase first,
      projectionExcess design first * projectionExcess design second
        ≤ 4 * projectionOfDesign design first second ^ 2 := by
    intro first hfirst second hsecond
    have hne : second ≠ first := (Finset.mem_erase.mp hsecond).1
    have hmem : second ∈ labels := (Finset.mem_erase.mp hsecond).2
    have hfail := hcontra first hfirst second hmem (Ne.symm hne)
    rw [QuarterSlack] at hfail
    linarith [not_lt.mp hfail]
  have hchain : (∑ index ∈ labels, projectionExcess design index) ^ 2
        - ∑ index ∈ labels, projectionExcess design index ^ 2
      ≤ 4 * ((rank : ℝ) - ∑ rowIndex, projectionOfDesign design rowIndex rowIndex ^ 2) := by
    rw [sq_sum_sub_sum_sq_eq_sum_erase, ← sum_sum_erase_sq_projection design]
    have hstep : ∑ first ∈ labels, ∑ second ∈ labels.erase first,
          projectionExcess design first * projectionExcess design second
        ≤ ∑ first ∈ labels, ∑ second ∈ labels.erase first,
            4 * projectionOfDesign design first second ^ 2 := by
      refine Finset.sum_le_sum fun first hfirst => ?_
      exact Finset.sum_le_sum fun second hsecond => hnonEdge first hfirst second hsecond
    have hpull : ∑ first ∈ labels, ∑ second ∈ labels.erase first,
          4 * projectionOfDesign design first second ^ 2
        = 4 * ∑ first ∈ labels, ∑ second ∈ labels.erase first,
            projectionOfDesign design first second ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun first _ => by rw [Finset.mul_sum]
    rw [hpull] at hstep
    have hsubset := sum_erase_sq_subset_le design labels
    linarith
  linarith

/-! ## 5. Ramsey at six labels -/

/-- **`R(3,3) ≤ 6`.**  Any symmetric relation on six points carries a triangle
or an independent triple.  Pigeonhole at one vertex: of the five others, three
share a side with it, and those three either contain an edge, closing a
triangle, or are independent.

This is the exact combinatorial fact the energy budget wants.  Mantel bounds the
edge count of a triangle-free graph, but the budget prices NON-edges, and the
independent triple is what carries three non-edges at once.

Symmetry of the relation is NOT needed.  The triangle and the independent triple
are both read in a fixed order through the pivot vertex, so the pigeonhole never
has to turn an edge around.  That makes the statement stronger than the usual
graph reading and costs nothing. -/
theorem exists_mono_triple_of_six (rel : Fin 6 → Fin 6 → Prop) [DecidableRel rel] :
    (∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ rel a b ∧ rel a c ∧ rel b c)
      ∨ (∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬ rel a b ∧ ¬ rel a c ∧ ¬ rel b c) := by
  classical
  set others : Finset (Fin 6) := Finset.univ.erase 0 with hothers
  have hcard : others.card = 5 := by rw [hothers]; decide
  set neighbours : Finset (Fin 6) := others.filter fun vertex => rel 0 vertex with hneighbours
  set strangers : Finset (Fin 6) := others.filter fun vertex => ¬ rel 0 vertex with hstrangers
  have hsplit : neighbours.card + strangers.card = 5 := by
    rw [hneighbours, hstrangers, Finset.card_filter_add_card_filter_not, hcard]
  have hbig : 3 ≤ neighbours.card ∨ 3 ≤ strangers.card := by omega
  have hextract : ∀ chosen : Finset (Fin 6), 3 ≤ chosen.card →
      ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ∈ chosen ∧ b ∈ chosen ∧ c ∈ chosen := by
    intro chosen hchosen
    obtain ⟨sub, hsub, hsubCard⟩ := Finset.exists_subset_card_eq hchosen
    obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hsubCard
    refine ⟨a, b, c, hab, hac, hbc, hsub ?_, hsub ?_, hsub ?_⟩ <;> rw [hset] <;> simp
  rcases hbig with hcase | hcase
  · obtain ⟨a, b, c, hab, hac, hbc, hamem, hbmem, hcmem⟩ := hextract neighbours hcase
    have hzeroA : rel 0 a := (Finset.mem_filter.mp hamem).2
    have hzeroB : rel 0 b := (Finset.mem_filter.mp hbmem).2
    have hzeroC : rel 0 c := (Finset.mem_filter.mp hcmem).2
    have hneA : a ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hamem).1).1
    have hneB : b ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hbmem).1).1
    have hneC : c ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hcmem).1).1
    by_cases hEdgeAB : rel a b
    · exact Or.inl ⟨0, a, b, Ne.symm hneA, Ne.symm hneB, hab, hzeroA, hzeroB, hEdgeAB⟩
    by_cases hEdgeAC : rel a c
    · exact Or.inl ⟨0, a, c, Ne.symm hneA, Ne.symm hneC, hac, hzeroA, hzeroC, hEdgeAC⟩
    by_cases hEdgeBC : rel b c
    · exact Or.inl ⟨0, b, c, Ne.symm hneB, Ne.symm hneC, hbc, hzeroB, hzeroC, hEdgeBC⟩
    · exact Or.inr ⟨a, b, c, hab, hac, hbc, hEdgeAB, hEdgeAC, hEdgeBC⟩
  · obtain ⟨a, b, c, hab, hac, hbc, hamem, hbmem, hcmem⟩ := hextract strangers hcase
    have hzeroA : ¬ rel 0 a := (Finset.mem_filter.mp hamem).2
    have hzeroB : ¬ rel 0 b := (Finset.mem_filter.mp hbmem).2
    have hzeroC : ¬ rel 0 c := (Finset.mem_filter.mp hcmem).2
    have hneA : a ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hamem).1).1
    have hneB : b ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hbmem).1).1
    have hneC : c ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hcmem).1).1
    by_cases hEdgeAB : rel a b
    · by_cases hEdgeAC : rel a c
      · by_cases hEdgeBC : rel b c
        · exact Or.inl ⟨a, b, c, hab, hac, hbc, hEdgeAB, hEdgeAC, hEdgeBC⟩
        · exact Or.inr ⟨0, b, c, Ne.symm hneB, Ne.symm hneC, hbc, hzeroB, hzeroC, hEdgeBC⟩
      · exact Or.inr ⟨0, a, c, Ne.symm hneA, Ne.symm hneC, hac, hzeroA, hzeroC, hEdgeAC⟩
    · exact Or.inr ⟨0, a, b, Ne.symm hneA, Ne.symm hneB, hab, hzeroA, hzeroB, hEdgeAB⟩

/-- The relation the graph runs on: both endpoints heavy, and the pair carries
the quarter slack. -/
def HeavyQuarterSlack (design : WeightedDesign size rank) (first second : Fin size) : Prop :=
  0 < projectionExcess design first ∧ 0 < projectionExcess design second
    ∧ QuarterSlack design first second

noncomputable instance (design : WeightedDesign size rank) :
    DecidableRel (HeavyQuarterSlack design) := fun _ _ => Classical.dec _

theorem heavyQuarterSlack_symm (design : WeightedDesign size rank) (first second : Fin size)
    (hedge : HeavyQuarterSlack design first second) : HeavyQuarterSlack design second first := by
  obtain ⟨hfirst, hsecond, hslack⟩ := hedge
  exact ⟨hsecond, hfirst, (quarterSlack_symm design first second).mp hslack⟩

/-- **THE DICHOTOMY AT SIX LABELS.**  Every design of six labels and rank three
either carries a quarter-slack triangle, and is therefore settled, or carries
three labels no two of which pass the pair test.  There is no third case. -/
theorem exists_quarterSlackTriangle_or_independent (design : WeightedDesign 6 3) :
    (∃ x y z : Fin 6, QuarterSlackTriangle design x y z)
      ∨ (∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z
          ∧ ¬ HeavyQuarterSlack design x y ∧ ¬ HeavyQuarterSlack design x z
          ∧ ¬ HeavyQuarterSlack design y z) := by
  rcases exists_mono_triple_of_six (HeavyQuarterSlack design) with
    ⟨a, b, c, hab, hac, hbc, hedgeAB, hedgeAC, hedgeBC⟩ | hindependent
  · exact Or.inl ⟨a, b, c, hab, hac, hbc, hedgeAB.1, hedgeAB.2.1, hedgeAC.2.1,
      hedgeAB.2.2, hedgeAC.2.2, hedgeBC.2.2⟩
  · exact Or.inr hindependent

/-! ## 6. The equiangular blind spot -/

/-- **THE GRAPH IS EMPTY AT THE EQUIANGULAR DESIGN.**  `Gtz.icosaDesign` is the
six icosahedral diameters at uniform weight, whose two-graph is the order-six
Paley conference matrix.  Every leverage is `3` and every squared pairing is
`9/5`, so the pair test asks `36/5 < 4` and fails at EVERY pair, the diagonal
included.  The margin is not narrow: the test misses by a factor `9/5`.

The weight-free bridge is what makes this one line of arithmetic.  Without it
the test would have to be read on the projection, where the entries carry square
roots of the weights. -/
theorem icosaDesign_no_quarterSlack (first second : Fin 6) :
    ¬ QuarterSlack icosaDesign first second := by
  rw [quarterSlack_iff_gram]
  have hleverageFirst : leverageOf (icosaDesign.atom first) = 3 := by
    rw [leverageOf_eq_dotProduct]; exact icosaAtom_leverage first
  have hleverageSecond : leverageOf (icosaDesign.atom second) = 3 := by
    rw [leverageOf_eq_dotProduct]; exact icosaAtom_leverage second
  rw [hleverageFirst, hleverageSecond]
  by_cases hne : first = second
  · subst hne
    have hself : (icosaDesign.atom first ⬝ᵥ icosaDesign.atom first) ^ 2 = 9 := by
      rw [show icosaDesign.atom first = icosaAtom first from rfl, icosaAtom_leverage]
      norm_num
    rw [hself]; norm_num
  · rw [show icosaDesign.atom first = icosaAtom first from rfl,
      show icosaDesign.atom second = icosaAtom second from rfl,
      icosaAtom_dot_sq_of_ne hne]
    norm_num

/-- No triangle exists at the equiangular design, because no edge does. -/
theorem icosaDesign_no_quarterSlackTriangle (x y z : Fin 6) :
    ¬ QuarterSlackTriangle icosaDesign x y z := by
  rintro ⟨_, _, _, _, _, _, hslack, _, _⟩
  exact icosaDesign_no_quarterSlack x y hslack

/-- **THE GRAPH ROUTE DOES NOT COVER.**  `Gtz.icosaDesign` carries no
quarter-slack triangle at all, so the hypothesis of
`Gtz.consolidatedStrictTripleDesign_of_forall_quarterSlackTriangle` is false and
the triangle certificate cannot be the whole argument.

The objective HOLDS at that design — `Gtz.icosaDesign_strictly_dominates` names
the triple `{0, 2, 4}` and pins its margin at `2 - 3/√5`.  So this refutes the
ROUTE and not the statement, and it does so at a point the corpus already
carries rather than at a constructed one. -/
theorem not_forall_exists_quarterSlackTriangle :
    ¬ ∀ design : WeightedDesign 6 3, ∃ x y z : Fin 6, QuarterSlackTriangle design x y z := by
  intro hforall
  obtain ⟨x, y, z, htriangle⟩ := hforall icosaDesign
  exact icosaDesign_no_quarterSlackTriangle x y z htriangle

/-- The route is not saved by restricting to primitive designs: the equiangular
design is primitive, since its six diameters span six distinct lines. -/
theorem not_forall_primitive_exists_quarterSlackTriangle :
    ¬ ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ x y z : Fin 6, QuarterSlackTriangle design x y z := by
  intro hforall
  have hprimitive : IsPrimitiveDesign icosaDesign := by
    intro keptLabel dropLabel ratio hne hparallel
    have hkept : icosaAtom keptLabel ⬝ᵥ icosaAtom keptLabel = 3 := icosaAtom_leverage keptLabel
    have hdrop : icosaAtom dropLabel ⬝ᵥ icosaAtom dropLabel = 3 := icosaAtom_leverage dropLabel
    have hcross : (icosaAtom keptLabel ⬝ᵥ icosaAtom dropLabel) ^ 2 = 9 / 5 :=
      icosaAtom_dot_sq_of_ne hne
    have hatom : icosaAtom dropLabel = ratio • icosaAtom keptLabel := hparallel
    rw [hatom] at hdrop hcross
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at hdrop hcross
    rw [hkept] at hdrop hcross
    nlinarith [hdrop, hcross]
  obtain ⟨x, y, z, htriangle⟩ := hforall icosaDesign hprimitive
  exact icosaDesign_no_quarterSlackTriangle x y z htriangle

/-- The equiangular design also lands on the independent-triple half of the
dichotomy, which is where every design with no triangle must land. -/
theorem icosaDesign_independent :
    ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z
      ∧ ¬ HeavyQuarterSlack icosaDesign x y ∧ ¬ HeavyQuarterSlack icosaDesign x z
      ∧ ¬ HeavyQuarterSlack icosaDesign y z := by
  refine ⟨0, 1, 2, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
    rintro ⟨_, _, hslack⟩ <;>
    exact icosaDesign_no_quarterSlack _ _ hslack

/-- **THE PRICE OF THE CONSTANT.**  At the equiangular design the squared pairing
beats the leverage surplus product by exactly `9/5`.  A cell of this shape needs
its constant strictly below `5/9` of the landed four to fire there, and the
landed cell is sharp on the equilateral locus, so no constant serves both. -/
theorem icosaDesign_gram_ratio {first second : Fin 6} (hne : first ≠ second) :
    5 * (icosaDesign.atom first ⬝ᵥ icosaDesign.atom second) ^ 2
      = 9 * ((leverageOf (icosaDesign.atom first) - 1)
          * (leverageOf (icosaDesign.atom second) - 1)) / 4 := by
  have hleverageFirst : leverageOf (icosaDesign.atom first) = 3 := by
    rw [leverageOf_eq_dotProduct]; exact icosaAtom_leverage first
  have hleverageSecond : leverageOf (icosaDesign.atom second) = 3 := by
    rw [leverageOf_eq_dotProduct]; exact icosaAtom_leverage second
  rw [hleverageFirst, hleverageSecond,
    show icosaDesign.atom first = icosaAtom first from rfl,
    show icosaDesign.atom second = icosaAtom second from rfl,
    icosaAtom_dot_sq_of_ne hne]
  norm_num

end Gtz

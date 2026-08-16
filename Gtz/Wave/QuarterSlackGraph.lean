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

/-- The quadratic-residue character of `ℤ/5`, read on a natural residue.  The
residues are `1` and `4`, the non-residues `2` and `3`. -/
def residueSign (residue : ℕ) : ℝ :=
  if residue = 0 then 0 else if residue = 1 ∨ residue = 4 then 1 else -1

/-- The symmetric conference matrix of order six, the Paley matrix at `q = 5`,
given by its arithmetic rather than as a literal.  Row and column zero form the
border, and the remaining five-by-five core is the circulant of the character.

Presenting it arithmetically is what keeps the identity `C * C = 5 • 1`
mechanical: a matrix literal does not reduce at an index of two or more, which
is a reduction failure two earlier modules of this campaign also hit. -/
def conferenceCore : Matrix (Fin 6) (Fin 6) ℝ := Matrix.of fun rowIndex colIndex =>
  if rowIndex.val = 0 ∧ colIndex.val = 0 then 0
  else if rowIndex.val = 0 ∨ colIndex.val = 0 then 1
  else residueSign ((colIndex.val + 5 - rowIndex.val) % 5)

theorem conferenceCore_transpose : conferenceCoreᵀ = conferenceCore := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [conferenceCore, residueSign, Matrix.transpose_apply]

theorem conferenceCore_diagonal (rowIndex : Fin 6) : conferenceCore rowIndex rowIndex = 0 := by
  fin_cases rowIndex <;> norm_num [conferenceCore, residueSign]

theorem conferenceCore_offDiagonal_sq (rowIndex colIndex : Fin 6) (hne : rowIndex ≠ colIndex) :
    conferenceCore rowIndex colIndex ^ 2 = 1 := by
  fin_cases rowIndex <;> fin_cases colIndex <;>
    first | (exact absurd rfl hne) | norm_num [conferenceCore, residueSign]

/-- **The conference identity.**  `C * C = 5 • 1`, the defining property, and the
only place the arithmetic of `ℤ/5` is spent. -/
theorem conferenceCore_mul_self :
    conferenceCore * conferenceCore = (5 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp +decide [Matrix.mul_apply, conferenceCore, residueSign, Fin.sum_univ_six,
      Matrix.smul_apply] <;> norm_num

/-- The projection onto the span of six equiangular lines in `ℝ³`, presented
through its conference core.  These are the icosahedral diameters. -/
noncomputable def conferenceProjection : Matrix (Fin 6) (Fin 6) ℝ :=
  (2 : ℝ)⁻¹ • ((1 : Matrix (Fin 6) (Fin 6) ℝ) + (Real.sqrt 5)⁻¹ • conferenceCore)

theorem sqrt_five_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)

theorem inv_sqrt_five_sq : (Real.sqrt 5)⁻¹ * (Real.sqrt 5)⁻¹ = (5 : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 5)]

theorem conferenceProjection_transpose : conferenceProjectionᵀ = conferenceProjection := by
  rw [conferenceProjection, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_smul,
    conferenceCore_transpose, Matrix.transpose_one]

theorem conferenceProjection_mul_self :
    conferenceProjection * conferenceProjection = conferenceProjection := by
  set core : Matrix (Fin 6) (Fin 6) ℝ := (Real.sqrt 5)⁻¹ • conferenceCore with hcore
  have hsquare : core * core = 1 := by
    rw [hcore, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_sqrt_five_sq,
      conferenceCore_mul_self, smul_smul]
    norm_num
  rw [conferenceProjection, ← hcore, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hsquare]
  ext rowIndex colIndex
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem conferenceProjection_diagonal (rowIndex : Fin 6) :
    conferenceProjection rowIndex rowIndex = 1 / 2 := by
  rw [conferenceProjection]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq, smul_eq_mul]
  rw [conferenceCore_diagonal]
  ring

theorem conferenceProjection_offDiagonal_sq (rowIndex colIndex : Fin 6)
    (hne : rowIndex ≠ colIndex) :
    conferenceProjection rowIndex colIndex ^ 2 = 1 / 20 := by
  rw [conferenceProjection]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_ne hne, smul_eq_mul]
  have hcore := conferenceCore_offDiagonal_sq rowIndex colIndex hne
  have hexpand : ((2:ℝ)⁻¹ * (0 + (Real.sqrt 5)⁻¹ * conferenceCore rowIndex colIndex)) ^ 2
      = (2:ℝ)⁻¹ * (2:ℝ)⁻¹ * ((Real.sqrt 5)⁻¹ * (Real.sqrt 5)⁻¹)
        * conferenceCore rowIndex colIndex ^ 2 := by ring
  rw [hexpand, inv_sqrt_five_sq, hcore]
  norm_num

theorem conferenceProjection_trace : Matrix.trace conferenceProjection = (3 : ℝ) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Finset.sum_congr rfl fun rowIndex _ => conferenceProjection_diagonal rowIndex]
  norm_num

/-- **THE BLIND SPOT, as a design.**  There is a weighted design of six labels
and rank three whose projection is the equiangular one and whose weights are
uniform. -/
theorem exists_conferenceDesign :
    ∃ design : WeightedDesign 6 3,
      projectionOfDesign design = conferenceProjection ∧ design.weight = uniformSixWeight := by
  obtain ⟨frame, hortho, hframe⟩ :=
    exists_orthonormalFrame_of_symmetric_idempotent conferenceProjection
      conferenceProjection_transpose conferenceProjection_mul_self conferenceProjection_trace
  refine ⟨designOfOrthonormalFrame frame hortho uniformSixWeight uniformSixWeight_pos
    uniformSixWeight_sum, ?_, rfl⟩
  rw [projectionOfDesign_designOfOrthonormalFrame, hframe]

/-- Every excess of the equiangular design is `1/3`. -/
theorem conferenceDesign_excess {design : WeightedDesign 6 3}
    (hchart : projectionOfDesign design = conferenceProjection)
    (hweight : design.weight = uniformSixWeight) (atomIndex : Fin 6) :
    projectionExcess design atomIndex = 1 / 3 := by
  rw [projectionExcess, hchart, hweight, conferenceProjection_diagonal, uniformSixWeight]
  norm_num

/-- **THE GRAPH IS EMPTY AT THE EQUIANGULAR POINT.**  Every pair has excess
product `1/9` against `4 P_cd ^ 2 = 1/5`, so no pair passes the quarter-slack
test.  The margin is not narrow: the test fails by a factor `20/9`. -/
theorem conferenceDesign_no_quarterSlack {design : WeightedDesign 6 3}
    (hchart : projectionOfDesign design = conferenceProjection)
    (hweight : design.weight = uniformSixWeight) (first second : Fin 6) :
    ¬ QuarterSlack design first second := by
  rw [QuarterSlack, conferenceDesign_excess hchart hweight,
    conferenceDesign_excess hchart hweight, hchart]
  by_cases hne : first = second
  · subst hne
    rw [conferenceProjection_diagonal]
    norm_num
  · rw [conferenceProjection_offDiagonal_sq first second hne]
    norm_num

/-- No triangle exists at the equiangular point, because no edge does. -/
theorem conferenceDesign_no_triangle {design : WeightedDesign 6 3}
    (hchart : projectionOfDesign design = conferenceProjection)
    (hweight : design.weight = uniformSixWeight) (x y z : Fin 6) :
    ¬ QuarterSlackTriangle design x y z := by
  rintro ⟨_, _, _, _, _, _, hslack, _, _⟩
  exact conferenceDesign_no_quarterSlack hchart hweight x y hslack

/-- **THE GRAPH ROUTE DOES NOT COVER.**  Some design of six labels and rank
three carries no quarter-slack triangle at all.  So the hypothesis of
`Gtz.consolidatedStrictTripleDesign_of_forall_quarterSlackTriangle` is false, and
the triangle certificate cannot be the whole argument.

The objective still holds at that design — ten of its twenty triples strictly
dominate — so this refutes the ROUTE and not the statement. -/
theorem not_forall_exists_quarterSlackTriangle :
    ¬ ∀ design : WeightedDesign 6 3, ∃ x y z : Fin 6, QuarterSlackTriangle design x y z := by
  intro hforall
  obtain ⟨design, hchart, hweight⟩ := exists_conferenceDesign
  obtain ⟨x, y, z, htriangle⟩ := hforall design
  exact conferenceDesign_no_triangle hchart hweight x y z htriangle

/-- The equiangular point also defeats the independent-triple half: it carries
three labels pairwise failing the test, which is where the dichotomy lands. -/
theorem conferenceDesign_independent {design : WeightedDesign 6 3}
    (hchart : projectionOfDesign design = conferenceProjection)
    (hweight : design.weight = uniformSixWeight) :
    ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z
      ∧ ¬ HeavyQuarterSlack design x y ∧ ¬ HeavyQuarterSlack design x z
      ∧ ¬ HeavyQuarterSlack design y z := by
  refine ⟨0, 1, 2, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
    rintro ⟨_, _, hslack⟩ <;>
    exact conferenceDesign_no_quarterSlack hchart hweight _ _ hslack

/-- **THE PRICE OF THE CONSTANT.**  At the equiangular point the excess product
beats the off-diagonal square by exactly `20/9`.  A cell of this shape with a
constant strictly below `20/9` would fire at every pair there, including the
pairs of a triple that does not dominate, so no such cell is sound. -/
theorem conferenceDesign_ratio {design : WeightedDesign 6 3}
    (hchart : projectionOfDesign design = conferenceProjection)
    (hweight : design.weight = uniformSixWeight) (first second : Fin 6)
    (hne : first ≠ second) :
    9 * (projectionExcess design first * projectionExcess design second)
      = 20 * projectionOfDesign design first second ^ 2 := by
  rw [conferenceDesign_excess hchart hweight, conferenceDesign_excess hchart hweight, hchart,
    conferenceProjection_offDiagonal_sq first second hne]
  norm_num

end Gtz

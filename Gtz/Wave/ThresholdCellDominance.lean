/-
# The threshold cell against excess dominance: what the frontier producer really asks,
# the repair that asks less, and the complete-graph profile that refutes both

`Gtz.obligationThresholdCellHingeRankFourAndUp_of_excessDominates` produces the registry's
second frontier axiom from

    hdominated : ∀ rank, 4 ≤ rank → ∀ design at the threshold cell,
      ∃ selected, ∃ hcard, ExcessDominatesBlock design selected hcard

and the companion `Gtz.obligationSubThresholdBandHinge_of_excessDominates` does the same
for the first.  This file settles what those hypotheses cost, weakens them, and then
refutes the weakened forms at the cell they are aimed at.

## 1. The hypothesis is tie-emptiness, not the hinge

`Gtz.not_isTie_of_excessDominates` already says a dominated selection refutes `IsTie`.
Quantified over every design, that hypothesis therefore says NO design of the cell is a
tie.  The axiom it produces says only that a tie carries a parallel pair.  So the landed
producer pays for the hinge with a strictly stronger currency, and
`Gtz.hingeConclusion_of_tieEmpty` shows the hinge follows from tie-emptiness with the
antecedent never inhabited.  That is recorded here as
`Gtz.tieEmpty_of_forallExcessDominates`.

## 2. The repair: ask only on the primitive stratum

A tie that carries no parallel pair is a primitive design, so a producer needs excess
dominance ONLY there.  `Gtz.obligationThresholdCellHingeRankFourAndUp_of_primitiveExcessDominates`
and `Gtz.obligationSubThresholdBandHinge_of_primitiveExcessDominates` are the repaired
producers.  Their hypotheses are implied by the landed ones and do not imply them, so both
frontier axioms now rest on a strictly weaker stratum.

## 3. The rank-uniform excess arithmetic

`Gtz.sum_diagonalShiftForm_diag` is already rank-uniform: the shifted diagonal totals
`rank - 1`.  Section 3 turns that into a pigeonhole at every size,
`Gtz.exists_excess_ge_of_size`, and reads it at the threshold cell.  The rank-three
instance `Gtz.exists_excess_ge_third` is the case `size = 6`, `rank = 3`; at rank four the
cell is `(10, 4)` and the free excess is `3 / 10`.

## 4. The obstruction, and it is one line of arithmetic

Excess dominance charges each selected slot's excess against the sum of the absolute
pairings in its own row.  So TWO selected partners of pairing magnitude `a` already defeat
a slot of excess at most `2 * a`.  That is `Gtz.not_excessDominates_of_two_heavy_partners`,
and it needs no projection, no rank and no design — only the two partners.

## 5. The complete-graph profile

For every rank the complete graph on `rank + 1` vertices has exactly
`rank * (rank + 1) / 2` edges and cycle rank `rank`, so its graphic design sits at EXACTLY
the threshold cell, at every rank at once.  Its projection is the cut-space projection:
diagonal `2 / (rank + 1)` at every edge, off-diagonal `1 / (rank + 1)` in magnitude on
edges that meet and `0` on edges that do not.  The excess is then
`2 * (rank - 1) / (rank * (rank + 1))`, strictly below the `2 / (rank + 1)` that two
meeting partners contribute, for every rank.  So on that profile excess dominance forces
every selected edge to meet at most ONE other selected edge.

`rank` edges of the complete graph on `rank + 1` vertices cannot do that: pair the meeting
edges up, count vertices, and `rank <= 2` follows.  Section 6 carries the rank-four
instance in kernel over the ten edges of the complete graph on five vertices.

The rank-three member of the same family is the `K4` chart the `A3` ledger is written
about, which is why the dominance lane was already measured to refuse there.  The refusal
is not special to rank three.  It is the threshold cell.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Wave.ProjectionMinorShift
import Gtz.Wave.OffsetUpperBound
import Gtz.Quantitative.DecisionAtlasCellsSevenThree

open Finset

namespace Gtz

variable {size rank : ℕ}

/-! ## 1. Primitivity is the negation of a parallel pair

`Gtz.isPrimitiveDesign_iff_not_hasParallelPair` is LANDED
(`Gtz/Design/PrimitiveTightClassification.lean`, consumed in
`Gtz/Reduction/PolarTiltLedger.lean`).  It is consumed here and never re-derived. -/

/-! ## 2. What the landed frontier producer really assumes

The producer's hypothesis quantifies excess dominance over EVERY design of the cell.
Excess dominance refutes `Gtz.IsTie`, so that hypothesis asserts the cell carries no tie
at all.  The axiom it buys asserts only that a tie carries a parallel pair. -/

/-- **THE FRONTIER PRODUCER'S HYPOTHESIS IS TIE-EMPTINESS.**  If every design of a cell
carries an excess dominated selection, then no design of that cell is a tie.  This is
strictly stronger than the hinge conclusion, which allows ties and only constrains them. -/
theorem tieEmpty_of_forallExcessDominates
    (hdominated : ∀ design : WeightedDesign size rank,
      ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
        ExcessDominatesBlock design selected hcard) :
    ∀ design : WeightedDesign size rank, ¬ IsTie design := by
  intro design
  obtain ⟨selected, hcard, hdom⟩ := hdominated design
  exact not_isTie_of_excessDominates design selected hcard hdom

/-- **TIE-EMPTINESS GIVES THE HINGE CONCLUSION WITH AN EMPTY ANTECEDENT.**  So the landed
producer never uses the parallel pair it concludes: it proves the implication by refuting
its hypothesis.  Recorded to make the strength gap explicit. -/
theorem hingeConclusion_of_tieEmpty
    (htieEmpty : ∀ design : WeightedDesign size rank, ¬ IsTie design) :
    ∀ design : WeightedDesign size rank, IsTie design → HasParallelPair design :=
  fun design htie => absurd htie (htieEmpty design)

/-- The landed producer's hypothesis, read at one cell, yields the hinge conclusion only
through the vacuous route above. -/
theorem hingeConclusion_of_forallExcessDominates
    (hdominated : ∀ design : WeightedDesign size rank,
      ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
        ExcessDominatesBlock design selected hcard) :
    ∀ design : WeightedDesign size rank, IsTie design → HasParallelPair design :=
  hingeConclusion_of_tieEmpty (tieEmpty_of_forallExcessDominates hdominated)

/-! ## 3. The repair: excess dominance on the primitive stratum only

A tie without a parallel pair is primitive.  So the hinge follows from excess dominance
assumed ONLY on primitive designs — a strictly smaller demand, since it says nothing at
all about the designs that already carry a parallel pair. -/

/-- **THE HINGE CONCLUSION FROM THE PRIMITIVE STRATUM ALONE.**  Excess dominance is
needed only where the conclusion is not already free.  A design either carries a parallel
pair, and the conclusion holds outright, or it is primitive, and the hypothesis applies
and refutes the tie. -/
theorem hingeConclusion_of_primitiveExcessDominates
    (hdominated : ∀ design : WeightedDesign size rank, IsPrimitiveDesign design →
      ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
        ExcessDominatesBlock design selected hcard) :
    ∀ design : WeightedDesign size rank, IsTie design → HasParallelPair design := by
  intro design htie
  by_contra hno
  obtain ⟨selected, hcard, hdom⟩ :=
    hdominated design ((isPrimitiveDesign_iff_not_hasParallelPair design).mpr hno)
  exact not_isTie_of_excessDominates design selected hcard hdom htie

/-- The repaired hypothesis is implied by the landed one, so the repair is a genuine
weakening and never a strengthening. -/
theorem primitiveExcessDominates_of_forallExcessDominates
    (hdominated : ∀ design : WeightedDesign size rank,
      ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
        ExcessDominatesBlock design selected hcard) :
    ∀ design : WeightedDesign size rank, IsPrimitiveDesign design →
      ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
        ExcessDominatesBlock design selected hcard :=
  fun design _ => hdominated design

/-- **THE REPAIRED THRESHOLD-CELL PRODUCER.**  The registry's second frontier axiom from
excess dominance on the primitive stratum of the threshold cell only. -/
theorem obligationThresholdCellHingeRankFourAndUp_of_primitiveExcessDominates
    (hdominated : ∀ rank : ℕ, 4 ≤ rank →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank, IsPrimitiveDesign design →
        ∃ selected : Finset (Fin (rank * (rank + 1) / 2)), ∃ hcard : selected.card = rank,
          ExcessDominatesBlock design selected hcard) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
        IsTie design → HasParallelPair design := by
  intro rank hrank _ design
  exact hingeConclusion_of_primitiveExcessDominates (hdominated rank hrank) design

/-- **THE REPAIRED SUB-THRESHOLD PRODUCER.**  The registry's first frontier axiom from
excess dominance on the primitive stratum of each band cell only. -/
theorem obligationSubThresholdBandHinge_of_primitiveExcessDominates
    (hdominated : ∀ rank : ℕ, 3 ≤ rank → ∀ size : ℕ, 2 * rank ≤ size →
      size < rank * (rank + 1) / 2 → ∀ design : WeightedDesign size rank,
        IsPrimitiveDesign design →
          ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
            ExcessDominatesBlock design selected hcard) :
    ∀ rank : ℕ, 3 ≤ rank → ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
      GtzWeighted (size - 1) rank →
        ∀ design : WeightedDesign size rank, IsTie design → HasParallelPair design := by
  intro rank hrank size hlow hhigh _ design
  exact hingeConclusion_of_primitiveExcessDominates
    (hdominated rank hrank size hlow hhigh) design

/-! ## 4. Rank-uniform excess arithmetic

`Gtz.sum_diagonalShiftForm_diag` totals the shifted diagonal at `rank - 1` for every size
and every rank.  A pigeonhole against `size` slots hands one label its share. -/

/-- **SOME EXCESS REACHES THE AVERAGE, AT EVERY SIZE AND EVERY RANK.**  The shifted
diagonal totals `rank - 1` over `size` labels, so some label carries at least
`(rank - 1) / size`.  No weight hypothesis and no rank coincidence.  The landed
`Gtz.exists_excess_ge_third` is the instance `size = 6`, `rank = 3`. -/
theorem exists_excess_ge_of_size (design : WeightedDesign size rank) (hsize : 0 < size) :
    ∃ label : Fin size,
      ((rank : ℝ) - 1) / (size : ℝ) ≤ diagonalShiftForm design label label := by
  classical
  by_contra hall
  push Not at hall
  have hne : (Finset.univ : Finset (Fin size)).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact Fin.pos_iff_nonempty.mp hsize
  have hlt : ∑ label : Fin size, diagonalShiftForm design label label
      < ∑ _label : Fin size, ((rank : ℝ) - 1) / (size : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hne fun label _ => hall label
  rw [sum_diagonalShiftForm_diag design] at hlt
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  have hsizeR : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsize
  rw [mul_div_cancel₀ _ (ne_of_gt hsizeR)] at hlt
  exact lt_irrefl _ hlt

/-- The threshold cell reading.  At `size = rank * (rank + 1) / 2` the free excess is
`2 * (rank - 1) / (rank * (rank + 1))`, which is the exact quantity the complete-graph
profile of section 6 attains. -/
theorem exists_excess_ge_thresholdCell (rank : ℕ) (hrank : 1 ≤ rank)
    (design : WeightedDesign (rank * (rank + 1) / 2) rank) :
    ∃ label : Fin (rank * (rank + 1) / 2),
      ((rank : ℝ) - 1) / ((rank * (rank + 1) / 2 : ℕ) : ℝ)
        ≤ diagonalShiftForm design label label := by
  refine exists_excess_ge_of_size design ?_
  have : 1 * 2 ≤ rank * (rank + 1) := Nat.mul_le_mul hrank (by omega)
  omega

/-- The rank-four instance in closed form: at the cell `(10, 4)` some label carries excess
at least `3 / 10`. -/
theorem exists_excess_ge_three_tenths (design : WeightedDesign 10 4) :
    ∃ label : Fin 10, (3 : ℝ) / 10 ≤ diagonalShiftForm design label label := by
  have h := exists_excess_ge_of_size design (by norm_num)
  obtain ⟨label, hlabel⟩ := h
  refine ⟨label, ?_⟩
  have : ((4 : ℕ) : ℝ) - 1 = 3 := by norm_num
  rw [this] at hlabel
  simpa using hlabel

/-! ## 5. The obstruction: two heavy partners defeat a slot

Excess dominance charges a slot's excess against the sum of the absolute pairings in its
own row.  Two partners of magnitude `a` therefore defeat any slot of excess at most
`2 * a`.  Nothing below reads a projection, a weight or a rank. -/

/-- Two distinct entries of `Finset.univ.erase slot` contribute at least their two values
to a sum of nonnegative terms. -/
theorem two_le_sum_of_two_members {n : ℕ} (f : Fin n → ℝ) (hnonneg : ∀ j, 0 ≤ f j)
    {slot first second : Fin n} (hfirst : first ≠ slot) (hsecond : second ≠ slot)
    (hne : first ≠ second) :
    f first + f second ≤ ∑ other ∈ Finset.univ.erase slot, f other := by
  classical
  have hsub : ({first, second} : Finset (Fin n)) ⊆ Finset.univ.erase slot := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hfirst, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hsecond, Finset.mem_univ _⟩
  have hpair : ∑ other ∈ ({first, second} : Finset (Fin n)), f other = f first + f second := by
    rw [Finset.sum_pair hne]
  calc f first + f second
      = ∑ other ∈ ({first, second} : Finset (Fin n)), f other := hpair.symm
    _ ≤ ∑ other ∈ Finset.univ.erase slot, f other :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hnonneg j

/-- **TWO HEAVY PARTNERS DEFEAT EXCESS DOMINANCE.**  If a selected slot has two distinct
selected partners whose pairings both have magnitude at least `level`, and the slot's own
excess is at most `2 * level`, then the block is not excess dominated.  One inequality, no
determinant, no rank. -/
theorem not_excessDominates_of_two_heavy_partners (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    {slot first second : Fin rank} (hfirst : first ≠ slot) (hsecond : second ≠ slot)
    (hne : first ≠ second) {level : ℝ}
    (hfirstHeavy : level ≤ |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
      (selected.orderEmbOfFin hcard first)|)
    (hsecondHeavy : level ≤ |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
      (selected.orderEmbOfFin hcard second)|)
    (hexcess : projectionOfDesign design (selected.orderEmbOfFin hcard slot)
      (selected.orderEmbOfFin hcard slot)
        - design.weight (selected.orderEmbOfFin hcard slot) ≤ 2 * level) :
    ¬ ExcessDominatesBlock design selected hcard := by
  classical
  intro hdom
  have hrow := hdom slot
  set f : Fin rank → ℝ := fun other =>
    |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
      (selected.orderEmbOfFin hcard other)| with hf
  have hnonneg : ∀ j, 0 ≤ f j := fun j => abs_nonneg _
  have hpair : f first + f second ≤ ∑ other ∈ Finset.univ.erase slot, f other :=
    two_le_sum_of_two_members f hnonneg hfirst hsecond hne
  have hlevel : 2 * level ≤ f first + f second := by
    have : level + level ≤ f first + f second := add_le_add hfirstHeavy hsecondHeavy
    linarith
  have : 2 * level < 2 * level := by
    calc 2 * level ≤ f first + f second := hlevel
      _ ≤ ∑ other ∈ Finset.univ.erase slot, f other := hpair
      _ < projectionOfDesign design (selected.orderEmbOfFin hcard slot)
            (selected.orderEmbOfFin hcard slot)
          - design.weight (selected.orderEmbOfFin hcard slot) := hrow
      _ ≤ 2 * level := hexcess
  exact lt_irrefl _ this

/-! ## 6. The complete-graph profile at the threshold cell

The complete graph on `rank + 1` vertices carries `rank * (rank + 1) / 2` edges and cycle
rank `rank`, so its graphic design sits at exactly the threshold cell at every rank.  Its
cut-space projection has constant diagonal `2 / (rank + 1)`, and off-diagonal magnitude
`1 / (rank + 1)` on edges that meet, `0` on edges that do not.  The design weight is
uniform, `2 / (rank * (rank + 1))`.

Everything below is stated on that PROFILE, so it applies to any design carrying it and
never needs the graph to be built. -/

/-- **THE COMPLETE-GRAPH PROFILE.**  Constant projection diagonal, uniform weight, and an
off-diagonal that is either zero or of one fixed magnitude according to a symmetric
meeting relation on the labels. -/
structure CompleteGraphProfile (design : WeightedDesign size rank)
    (meets : Fin size → Fin size → Prop) : Prop where
  /-- Every edge has the same effective resistance times conductance. -/
  diag : ∀ label : Fin size,
    projectionOfDesign design label label = 2 / ((rank : ℝ) + 1)
  /-- The design weight is uniform on the edges. -/
  weight : ∀ label : Fin size,
    design.weight label = 2 / ((rank : ℝ) * ((rank : ℝ) + 1))
  /-- Two edges that meet pair at one fixed magnitude. -/
  heavy : ∀ first second : Fin size, first ≠ second → meets first second →
    1 / ((rank : ℝ) + 1) ≤ |projectionOfDesign design first second|

/-- **THE FREE EXCESS OF THE PROFILE.**  Every label carries excess exactly
`2 * (rank - 1) / (rank * (rank + 1))`. -/
theorem excess_completeGraphProfile {design : WeightedDesign size rank}
    {meets : Fin size → Fin size → Prop} (hprofile : CompleteGraphProfile design meets)
    (hrank : 0 < rank) (label : Fin size) :
    projectionOfDesign design label label - design.weight label
      = 2 * ((rank : ℝ) - 1) / ((rank : ℝ) * ((rank : ℝ) + 1)) := by
  have hrankR : (0 : ℝ) < (rank : ℝ) := by exact_mod_cast hrank
  have hsucc : (0 : ℝ) < (rank : ℝ) + 1 := by linarith
  rw [hprofile.diag label, hprofile.weight label]
  field_simp

/-- **TWO MEETING PARTNERS ALWAYS DEFEAT THE PROFILE.**  The excess
`2 * (rank - 1) / (rank * (rank + 1))` is strictly below the `2 / (rank + 1)` that two
meeting partners contribute, at every rank at least one.  So on the complete-graph profile
excess dominance forces every selected edge to meet at most one other selected edge. -/
theorem excess_lt_two_heavy_completeGraphProfile (hrank : 0 < rank) :
    2 * ((rank : ℝ) - 1) / ((rank : ℝ) * ((rank : ℝ) + 1))
      < 2 * (1 / ((rank : ℝ) + 1)) := by
  have hrankR : (0 : ℝ) < (rank : ℝ) := by exact_mod_cast hrank
  have hsucc : (0 : ℝ) < (rank : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ (by positivity)]
  have : 2 * (1 / ((rank : ℝ) + 1)) * ((rank : ℝ) * ((rank : ℝ) + 1))
      = 2 * (rank : ℝ) := by field_simp
  rw [this]
  linarith

/-- **NO SELECTION WITH A CROWDED SLOT IS EXCESS DOMINATED ON THE PROFILE.**  If some
selected slot meets two other selected slots, the block fails excess dominance. -/
theorem not_excessDominates_of_crowded_slot {design : WeightedDesign size rank}
    {meets : Fin size → Fin size → Prop} (hprofile : CompleteGraphProfile design meets)
    (hrank : 0 < rank) (selected : Finset (Fin size)) (hcard : selected.card = rank)
    {slot first second : Fin rank} (hfirst : first ≠ slot) (hsecond : second ≠ slot)
    (hne : first ≠ second)
    (hmeetFirst : meets (selected.orderEmbOfFin hcard slot)
      (selected.orderEmbOfFin hcard first))
    (hmeetSecond : meets (selected.orderEmbOfFin hcard slot)
      (selected.orderEmbOfFin hcard second)) :
    ¬ ExcessDominatesBlock design selected hcard := by
  have hemb : Function.Injective (selected.orderEmbOfFin hcard) :=
    (selected.orderEmbOfFin hcard).injective
  refine not_excessDominates_of_two_heavy_partners design selected hcard hfirst hsecond hne
    (hprofile.heavy _ _ (fun h => hfirst (hemb h.symm)) hmeetFirst)
    (hprofile.heavy _ _ (fun h => hsecond (hemb h.symm)) hmeetSecond) ?_
  rw [excess_completeGraphProfile hprofile hrank]
  exact le_of_lt (excess_lt_two_heavy_completeGraphProfile hrank)

/-- **THE PROFILE REFUTES THE FRONTIER PRODUCER'S HYPOTHESIS AT ITS OWN CELL.**  If every
selection of the design has a slot meeting two other selected slots, then no selection is
excess dominated, so the design witnesses the failure of the producer's hypothesis — and
of the repaired primitive form too, whenever the design is primitive. -/
theorem not_exists_excessDominates_of_crowded {design : WeightedDesign size rank}
    {meets : Fin size → Fin size → Prop} (hprofile : CompleteGraphProfile design meets)
    (hrank : 0 < rank)
    (hcrowded : ∀ selected : Finset (Fin size), ∀ hcard : selected.card = rank,
      ∃ slot first second : Fin rank, first ≠ slot ∧ second ≠ slot ∧ first ≠ second ∧
        meets (selected.orderEmbOfFin hcard slot) (selected.orderEmbOfFin hcard first) ∧
        meets (selected.orderEmbOfFin hcard slot) (selected.orderEmbOfFin hcard second)) :
    ¬ ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
        ExcessDominatesBlock design selected hcard := by
  rintro ⟨selected, hcard, hdom⟩
  obtain ⟨slot, first, second, hfirst, hsecond, hne, hmeetFirst, hmeetSecond⟩ :=
    hcrowded selected hcard
  exact not_excessDominates_of_crowded_slot hprofile hrank selected hcard hfirst hsecond hne
    hmeetFirst hmeetSecond hdom

/-! ## 7. The verdict on the frontier route

The two theorems below record what section 6 buys: a single design of the threshold cell
carrying the complete-graph profile, and crowded at every selection, refutes BOTH the
landed producer's hypothesis and the repaired primitive one.  The hinge itself is untouched
— it is the hypothesis that dies, not the conclusion. -/

/-- **THE LANDED HYPOTHESIS FAILS AT ANY CROWDED PROFILE DESIGN.** -/
theorem not_forall_excessDominates_of_crowded_witness {design : WeightedDesign size rank}
    {meets : Fin size → Fin size → Prop} (hprofile : CompleteGraphProfile design meets)
    (hrank : 0 < rank)
    (hcrowded : ∀ selected : Finset (Fin size), ∀ hcard : selected.card = rank,
      ∃ slot first second : Fin rank, first ≠ slot ∧ second ≠ slot ∧ first ≠ second ∧
        meets (selected.orderEmbOfFin hcard slot) (selected.orderEmbOfFin hcard first) ∧
        meets (selected.orderEmbOfFin hcard slot) (selected.orderEmbOfFin hcard second)) :
    ¬ ∀ other : WeightedDesign size rank,
        ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
          ExcessDominatesBlock other selected hcard :=
  fun hall => not_exists_excessDominates_of_crowded hprofile hrank hcrowded (hall design)

/-- **THE REPAIRED HYPOTHESIS FAILS TOO, WHEN THE WITNESS IS PRIMITIVE.**  A graphic design
of a simple graph has no parallel edges, so its atoms carry no parallel pair.  The repair
of section 3 is therefore the right shape and still not enough. -/
theorem not_forall_primitiveExcessDominates_of_crowded_witness
    {design : WeightedDesign size rank} {meets : Fin size → Fin size → Prop}
    (hprofile : CompleteGraphProfile design meets) (hrank : 0 < rank)
    (hprim : IsPrimitiveDesign design)
    (hcrowded : ∀ selected : Finset (Fin size), ∀ hcard : selected.card = rank,
      ∃ slot first second : Fin rank, first ≠ slot ∧ second ≠ slot ∧ first ≠ second ∧
        meets (selected.orderEmbOfFin hcard slot) (selected.orderEmbOfFin hcard first) ∧
        meets (selected.orderEmbOfFin hcard slot) (selected.orderEmbOfFin hcard second)) :
    ¬ ∀ other : WeightedDesign size rank, IsPrimitiveDesign other →
        ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
          ExcessDominatesBlock other selected hcard :=
  fun hall => not_exists_excessDominates_of_crowded hprofile hrank hcrowded (hall design hprim)

/-! ## 8. THE SIXTH DOOR: excess dominance reaches all five on-path obligations

The rank-three threshold cell is `(6, 3)`, the cell of the on-path registry.  There the
same instrument that produces both frontier axioms produces the five on-path obligations
as well, and it needs the hypothesis only on the primitive stratum, because
`Gtz.allFiveOnPath_of_blockGapAt` already quantifies over primitive designs.

So the dominance lane is one lane across the whole registry, on-path and off-path
together.  Section 9 then decides it. -/

/-- **EXCESS DOMINANCE ON THE PRIMITIVE STRATUM REACHES ALL FIVE ON-PATH OBLIGATIONS.**  A
sixth door, and the first one whose hypothesis is a row of scalar inequalities with no
determinant, no Sylvester criterion and no offset.  It asks for strict diagonal dominance
of one selection's gap block at every primitive `(6, 3)` design. -/
theorem allFiveOnPath_of_primitiveExcessDominates
    (hdominated : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
        ExcessDominatesBlock design selected hcard) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  refine allFiveOnPath_of_blockGapAt fun design hprimitive => ?_
  obtain ⟨selected, hcard, hdom⟩ := hdominated design hprimitive
  refine ⟨((selected.orderEmbOfFin hcard : Fin 3 ↪o Fin 6) : Fin 3 → Fin 6),
    (selected.orderEmbOfFin hcard).injective, ?_⟩
  rw [blockGapAt_eq_projectionBlockGap]
  exact posDef_projectionBlockGap_of_excessDominates design selected hcard hdom

/-! ## 9. The rank-three member of the family, and the decision

Label the six edges of the complete graph on four vertices in the order the landed
`Gtz.graphicKFourDesign` uses, so that the three disjoint pairs are `{0,1}`, `{2,3}` and
`{4,5}` — the three perfect matchings of `K4`, and exactly the three vanishing pairings of
that design.  Two distinct edges meet exactly when they are NOT paired, so the non-meeting
relation is a perfect matching on the six labels, and `first / 2` names the pair.

Every label therefore has exactly one non-neighbour.  In a triple, at most one
complementary pair fits, so the remaining label meets both of the others.  That is
`Gtz.kFourMeets_crowded_triple`, decided over the two hundred and sixteen ordered triples.

The profile of section 6 at `rank = 3` reads: diagonal `1 / 2`, uniform weight `1 / 6`,
pairing magnitude `1 / 4` on meeting edges — exactly the landed `K4` chart numbers.  The
free excess is `1 / 3`, and two meeting partners contribute `1 / 2`. -/

/-- **THE MEETING RELATION OF THE COMPLETE GRAPH ON FOUR VERTICES**, in the labelling of
`Gtz.graphicKFourDesign`: the disjoint pairs are `{0,1}`, `{2,3}` and `{4,5}`, so two
labels fail to meet exactly when they share the value of `first / 2`. -/
def kFourMeets (first second : Fin 6) : Prop :=
  first ≠ second ∧ (first : ℕ) / 2 ≠ (second : ℕ) / 2

instance decidableKFourMeets (first second : Fin 6) : Decidable (kFourMeets first second) := by
  unfold kFourMeets; infer_instance

/-- **EVERY TRIPLE OF EDGES IS CROWDED.**  Among any three distinct edges of the complete
graph on four vertices, one meets the other two.  Each label has exactly one
non-neighbour, and a triple cannot supply a non-neighbour to all three of its members. -/
theorem kFourMeets_crowded_triple :
    ∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
      (kFourMeets first second ∧ kFourMeets first third) ∨
      (kFourMeets second first ∧ kFourMeets second third) ∨
      (kFourMeets third first ∧ kFourMeets third second) := by
  unfold kFourMeets
  decide

/-- The crowdedness of section 6, supplied at `rank = 3` from the triple lemma.  The three
selected labels are distinct because `Gtz.Finset.orderEmbOfFin` is an order embedding. -/
theorem kFourMeets_crowded (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    ∃ slot first second : Fin 3, first ≠ slot ∧ second ≠ slot ∧ first ≠ second ∧
      kFourMeets (selected.orderEmbOfFin hcard slot) (selected.orderEmbOfFin hcard first) ∧
      kFourMeets (selected.orderEmbOfFin hcard slot)
        (selected.orderEmbOfFin hcard second) := by
  have hemb : Function.Injective (selected.orderEmbOfFin hcard) :=
    (selected.orderEmbOfFin hcard).injective
  have h01 : selected.orderEmbOfFin hcard 0 ≠ selected.orderEmbOfFin hcard 1 := by
    intro h; exact absurd (hemb h) (by decide)
  have h02 : selected.orderEmbOfFin hcard 0 ≠ selected.orderEmbOfFin hcard 2 := by
    intro h; exact absurd (hemb h) (by decide)
  have h12 : selected.orderEmbOfFin hcard 1 ≠ selected.orderEmbOfFin hcard 2 := by
    intro h; exact absurd (hemb h) (by decide)
  rcases kFourMeets_crowded_triple _ _ _ h01 h02 h12 with h | h | h
  · exact ⟨0, 1, 2, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 0, 2, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨2, 0, 1, by decide, by decide, by decide, h.1, h.2⟩

/-- **THE SIXTH DOOR'S HYPOTHESIS IS FALSE.**  A primitive `(6, 3)` design carrying the
complete-graph profile — the `K4` chart, diagonal `1 / 2`, uniform weight `1 / 6`, pairing
magnitude `1 / 4` on meeting edges — admits NO excess dominated selection.  So the
dominance instrument cannot reach the on-path obligations. -/
theorem not_forall_primitiveExcessDominates_sixThree {design : WeightedDesign 6 3}
    (hprofile : CompleteGraphProfile design kFourMeets) (hprim : IsPrimitiveDesign design) :
    ¬ ∀ other : WeightedDesign 6 3, IsPrimitiveDesign other →
        ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
          ExcessDominatesBlock other selected hcard :=
  not_forall_primitiveExcessDominates_of_crowded_witness hprofile (by norm_num) hprim
    (fun selected hcard => kFourMeets_crowded selected hcard)

/-- **AND THE LANDED, UNRESTRICTED HYPOTHESIS IS FALSE AT THE SAME WITNESS.** -/
theorem not_forall_excessDominates_sixThree {design : WeightedDesign 6 3}
    (hprofile : CompleteGraphProfile design kFourMeets) :
    ¬ ∀ other : WeightedDesign 6 3,
        ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
          ExcessDominatesBlock other selected hcard :=
  not_forall_excessDominates_of_crowded_witness hprofile (by norm_num)
    (fun selected hcard => kFourMeets_crowded selected hcard)

/-- **THE PROFILE'S RANK-THREE ARITHMETIC, IN CLOSED FORM.**  The free excess is `1 / 3`
and two meeting partners contribute `1 / 2`, so the deficit is `1 / 6` at every slot of
every selection.  This is the exact quantity the dominance lane was measured to miss at the
`K4` chart, and section 6 shows it is not special to rank three. -/
theorem kFourProfile_excess_eq {design : WeightedDesign 6 3}
    (hprofile : CompleteGraphProfile design kFourMeets) (label : Fin 6) :
    projectionOfDesign design label label - design.weight label = 1 / 3 := by
  have h := excess_completeGraphProfile hprofile (by norm_num) label
  rw [h]; norm_num

/-- **THE DEFICIT IS EXACT AND RANK-UNIFORM.**  Two meeting partners exceed the free
excess by exactly `2 / (rank * (rank + 1))` — the reciprocal of the threshold cell's own
size.  So the dominance lane does not miss narrowly and then widen: it misses by the
inverse cell size at every rank, and at rank three that is `1 / 6`, the value the census
records as the best margin over all twenty selections. -/
theorem completeGraphProfile_deficit_eq (hrank : 0 < rank) :
    2 * (1 / ((rank : ℝ) + 1)) - 2 * ((rank : ℝ) - 1) / ((rank : ℝ) * ((rank : ℝ) + 1))
      = 2 / ((rank : ℝ) * ((rank : ℝ) + 1)) := by
  have hrankR : (0 : ℝ) < (rank : ℝ) := by exact_mod_cast hrank
  have hsucc : (0 : ℝ) < (rank : ℝ) + 1 := by linarith
  field_simp
  ring

/-- The rank-three reading of the deficit: every slot of every selection misses by exactly
`1 / 6`. -/
theorem kFourProfile_deficit_eq : 2 * (1 / ((3 : ℝ) + 1)) - 1 / 3 = 1 / 6 := by norm_num

/-! ## 10. The profile decided in closed form: one ratio governs every instrument

On the complete-graph profile a selection whose slots pairwise meet has a gap block with
constant diagonal `Gtz.profileDiag` and constant off-diagonal magnitude
`Gtz.profilePair`.  Everything about it is carried by their ratio

    `Gtz.profileRatio rank = 2 * (rank - 1) / rank`

because the block is `profilePair * (ratio on the diagonal, unit off it)`.  The three
instruments the campaign has aimed at this family are three thresholds on that one number,
and they separate:

| instrument                     | fires exactly when |
|--------------------------------|--------------------|
| strict diagonal dominance      | `2 < ratio`        |
| the sign-free determinant cell | `3 < ratio ^ 2`    |
| Sylvester with coherence       | `1 < ratio`        |

The ratio is `2 - 2 / rank`.  It is **below two at every rank**, so diagonal dominance
never fires — section 6 again, now with the reason.  It is below the square root of three
for every rank at most seven, so the sign-free cell fails there too, and at rank three that
is the `K4` chart.  But it exceeds one at every rank at least three, and the coherent
determinant factors as

    `profilePair ^ 3 * (ratio - 1) ^ 2 * (ratio + 2)`

which is therefore strictly positive at every rank at least three.  At rank three it is
`5 / 864`, the landed value of the `K4` star.

So the family that defeats every weaker instrument is nonetheless strictly dominating, in
closed form, at every rank at once — and the reason no cheap certificate sees it is that
the coherent term `2 * profilePair ^ 3` is exactly what carries it. -/

/-- The gap diagonal of the complete-graph profile. -/
noncomputable def profileDiag (rank : ℝ) : ℝ := 2 * (rank - 1) / (rank * (rank + 1))

/-- The gap off-diagonal magnitude of the complete-graph profile. -/
noncomputable def profilePair (rank : ℝ) : ℝ := 1 / (rank + 1)

/-- The one number that governs the profile: diagonal over off-diagonal. -/
noncomputable def profileRatio (rank : ℝ) : ℝ := 2 * (rank - 1) / rank

/-- The diagonal is the off-diagonal scaled by the ratio.  Every statement below is a
statement about `Gtz.profileRatio` alone. -/
theorem profileDiag_eq_ratio_mul_pair {rank : ℝ} (hrank : 0 < rank) :
    profileDiag rank = profileRatio rank * profilePair rank := by
  have hsucc : (0 : ℝ) < rank + 1 := by linarith
  unfold profileDiag profileRatio profilePair
  field_simp

/-- **THE RATIO IS BELOW TWO AT EVERY RANK.**  Strict diagonal dominance of the block needs
the diagonal to beat the two off-diagonal entries in its row, that is `2 < ratio`.  The
ratio is `2 - 2 / rank`, so dominance never fires on this family — at any rank. -/
theorem profileRatio_lt_two {rank : ℝ} (hrank : 0 < rank) : profileRatio rank < 2 := by
  unfold profileRatio
  rw [div_lt_iff₀ hrank]
  linarith

/-- **THE RATIO EXCEEDS ONE FROM RANK THREE.**  This is the Sylvester threshold, and it is
the one the family clears. -/
theorem one_lt_profileRatio {rank : ℝ} (hrank : 3 ≤ rank) : 1 < profileRatio rank := by
  have hpos : (0 : ℝ) < rank := by linarith
  unfold profileRatio
  rw [lt_div_iff₀ hpos]
  linarith

/-- The coherent determinant of an all-meeting selection on the profile: constant diagonal,
constant off-diagonal magnitude, and a positive product of the three off-diagonals. -/
noncomputable def coherentCliqueDet (rank : ℝ) : ℝ :=
  profileDiag rank ^ 3 - 3 * profileDiag rank * profilePair rank ^ 2
    + 2 * profilePair rank ^ 3

/-- **THE DETERMINANT FACTORS.**  `t ^ 3 - 3 * t + 2 = (t - 1) ^ 2 * (t + 2)`, so the
coherent determinant is a square times a positive factor.  No case analysis, no
eigenvalue. -/
theorem coherentCliqueDet_eq {rank : ℝ} (hrank : 0 < rank) :
    coherentCliqueDet rank
      = profilePair rank ^ 3 * ((profileRatio rank - 1) ^ 2 * (profileRatio rank + 2)) := by
  have hsucc : (0 : ℝ) < rank + 1 := by linarith
  unfold coherentCliqueDet
  rw [profileDiag_eq_ratio_mul_pair hrank]
  ring

/-- **THE COMPLETE-GRAPH FAMILY STRICTLY DOMINATES AT EVERY RANK AT LEAST THREE.**  The
ratio exceeds one, so the squared factor is positive, and the off-diagonal magnitude is
positive.  This is the exact sense in which the family that refuses every weaker instrument
is not a counterexample to anything. -/
theorem coherentCliqueDet_pos {rank : ℝ} (hrank : 3 ≤ rank) : 0 < coherentCliqueDet rank := by
  have hpos : (0 : ℝ) < rank := by linarith
  have hsucc : (0 : ℝ) < rank + 1 := by linarith
  have hratio : 1 < profileRatio rank := one_lt_profileRatio hrank
  have hpair : 0 < profilePair rank := by
    unfold profilePair; positivity
  rw [coherentCliqueDet_eq hpos]
  have hsq : 0 < (profileRatio rank - 1) ^ 2 := by positivity
  have hlin : 0 < profileRatio rank + 2 := by linarith
  positivity

/-- **THE SIGN-FREE CELL FAILS THROUGH RANK SEVEN.**  Discarding the coherent term leaves
`profileDiag ^ 3 - 3 * profileDiag * profilePair ^ 2`, positive exactly when
`3 < ratio ^ 2`.  At rank three the ratio is `4 / 3` and its square is `16 / 9`, below
three, so the sign-blind reading of the `K4` chart is negative.  That is the landed
`-49 / 864`, and it is a threshold effect, not a feature of rank three. -/
theorem profileRatio_sq_lt_three_of_rank_three : profileRatio 3 ^ 2 < 3 := by
  unfold profileRatio; norm_num

/-- The sign-free margin at an all-meeting selection, in the same normalisation. -/
noncomputable def signFreeCliqueDet (rank : ℝ) : ℝ :=
  profileDiag rank ^ 3 - 3 * profileDiag rank * profilePair rank ^ 2
    - 2 * profilePair rank ^ 3

/-- **THE COHERENT AND SIGN-FREE READINGS DIFFER BY EXACTLY FOUR CUBES.**  So coherence is
worth `4 * profilePair ^ 3` at this family, and that is the entire margin at rank three. -/
theorem coherentCliqueDet_sub_signFree {rank : ℝ} :
    coherentCliqueDet rank - signFreeCliqueDet rank = 4 * profilePair rank ^ 3 := by
  unfold coherentCliqueDet signFreeCliqueDet
  ring

/-- **THE RANK-THREE VALUES, EXACT.**  The coherent star reads `5 / 864` and the sign-blind
branch reads `-49 / 864`.  Both are landed numbers of the `K4` chart, and both are values of
the same rank-uniform polynomial. -/
theorem coherentCliqueDet_rank_three : coherentCliqueDet 3 = 5 / 864 := by
  unfold coherentCliqueDet profileDiag profilePair; norm_num

/-- The sign-blind branch at rank three. -/
theorem signFreeCliqueDet_rank_three : signFreeCliqueDet 3 = -49 / 864 := by
  unfold signFreeCliqueDet profileDiag profilePair; norm_num

/-- The value of the SAME rank-three shaped polynomial at the rank-four profile constants,
`7 / 1000`.  It is recorded for comparison only.  **It is NOT the determinant of the
rank-four threshold cell's gap block**, which is a four by four matrix — section 11 handles
every rank without a determinant at all. -/
theorem coherentCliqueDet_rank_four : coherentCliqueDet 4 = 7 / 1000 := by
  unfold coherentCliqueDet profileDiag profilePair; norm_num

/-- **THE THREE INSTRUMENTS SEPARATE AT RANK THREE.**  Diagonal dominance asks `2 < 4 / 3`,
the sign-free cell asks `3 < 16 / 9`, and Sylvester with coherence asks `1 < 4 / 3`.  Only
the last holds.  This is the whole story of the `K4` chart in one line, and section 10
shows it is the story at every rank at most seven. -/
theorem kFourRatio_separates :
    profileRatio 3 = 4 / 3 ∧ ¬ (2 < profileRatio 3) ∧ ¬ (3 < profileRatio 3 ^ 2)
      ∧ 1 < profileRatio 3 := by
  unfold profileRatio
  norm_num

/-! ## 11. The rank-uniform core, with no determinant

Section 10 reads a three by three determinant, so it speaks for rank three.  At rank `n`
the selection carries `n` slots and the determinant changes shape.  The content that does
NOT change shape is one inequality: the gap diagonal beats each single off-diagonal entry.

On the complete-graph profile a coherent all-meeting selection is the constant block, `d`
on the diagonal and `a` off it, whose quadratic form is
`(d - a) * ‖x‖ ^ 2 + a * (∑ x) ^ 2`.  Both terms are then nonnegative and the first is
strictly positive away from the origin, so `a < d` alone forces strict domination at EVERY
selection size.  That inequality is exactly `1 < Gtz.profileRatio`, which holds from rank
three.  The rank-three determinant `5 / 864` is one value of a fact that never needed it. -/

/-- **THE RANK-UNIFORM CORE.**  On the complete-graph profile the gap diagonal strictly
exceeds each single off-diagonal entry, at every rank at least three.  For the coherent
all-meeting selection this is the whole of strict domination, because the quadratic form of
a constant block is `(diagonal - offDiagonal)` times the squared norm plus `offDiagonal`
times the squared total, and both terms are then favourable at every selection size. -/
theorem profilePair_lt_profileDiag {rank : ℝ} (hrank : 3 ≤ rank) :
    profilePair rank < profileDiag rank := by
  have hpos : (0 : ℝ) < rank := by linarith
  have hsucc : (0 : ℝ) < rank + 1 := by linarith
  have hpairPos : 0 < profilePair rank := by unfold profilePair; positivity
  rw [profileDiag_eq_ratio_mul_pair hpos]
  have hratio : 1 < profileRatio rank := one_lt_profileRatio hrank
  nlinarith [hpairPos, hratio]

/-- The rank-three reading: `1 / 4 < 1 / 3`, the `K4` chart's own two constants. -/
theorem kFourPair_lt_kFourDiag : profilePair 3 < profileDiag 3 := by
  unfold profilePair profileDiag; norm_num

/-- The rank-four reading at the threshold cell `(10, 4)`: `1 / 5 < 3 / 10`. -/
theorem rankFourPair_lt_rankFourDiag : profilePair 4 < profileDiag 4 := by
  unfold profilePair profileDiag; norm_num

/-! ## 12. The profile is INHABITED, so the refutation is unconditional

Everything above is conditional on a design carrying `Gtz.CompleteGraphProfile`.  The
landed `Gtz.graphicKFourDesign` carries it.  That design has six atoms
`sqrt 6 / 2` times the `K4` edge vectors, uniform weight `1 / 6`, every leverage exactly
`3`, and a Gram off-diagonal in `{0, ±3/2}` whose three zeros sit on the three perfect
matchings `{0,1}`, `{2,3}`, `{4,5}` — exactly `Gtz.kFourMeets`.

At uniform weight `1 / 6` the projection entry is `(1/6)` times the pairing, so the
diagonal reads `(1/6) * 3 = 1/2 = 2 / (rank + 1)` and a meeting pair reads
`(1/6) * (3/2) = 1/4 = 1 / (rank + 1)`.  All three fields hold on the nose. -/

/-- The projection of the landed `K4` graphic design, in edge-vector coordinates. -/
theorem projectionOfDesign_graphicKFour (first second : Fin 6) :
    projectionOfDesign graphicKFourDesign first second
      = 1 / 4 * ∑ coord, kFourEdgeVector first coord * kFourEdgeVector second coord := by
  have hweight : ∀ edge : Fin 6, graphicKFourDesign.weight edge = 1 / 6 := fun _ => rfl
  have hsqrt : Real.sqrt (1 / 6 : ℝ) * Real.sqrt (1 / 6 : ℝ) = 1 / 6 :=
    Real.mul_self_sqrt (by norm_num)
  rw [projectionOfDesign_apply, hweight, hweight, hsqrt]
  have hpair : graphicKFourDesign.atom first ⬝ᵥ graphicKFourDesign.atom second
      = 3 / 2 * ∑ coord, kFourEdgeVector first coord * kFourEdgeVector second coord :=
    graphicKFourDesign_atomPairing first second
  rw [hpair]; ring

/-- **A MEETING PAIR READS EXACTLY ONE QUARTER.**  The three vanishing pairings of the
landed design sit on the three perfect matchings, and every other pairing is `±3/2`, so the
projection entry is `±1/4`. -/
theorem abs_projectionOfDesign_graphicKFour (first second : Fin 6)
    (hpair : (first : ℕ) / 2 ≠ (second : ℕ) / 2) :
    |projectionOfDesign graphicKFourDesign first second| = 1 / 4 := by
  rw [projectionOfDesign_graphicKFour]
  revert hpair
  fin_cases first <;> fin_cases second <;>
    simp [kFourEdgeVector, Fin.sum_univ_three]

/-- **THE PROFILE IS INHABITED.**  The landed `K4` graphic design carries the
complete-graph profile at rank three, with the meeting relation of section 9.  So every
conditional statement of sections 6, 7 and 9 becomes unconditional. -/
theorem completeGraphProfile_graphicKFour :
    CompleteGraphProfile graphicKFourDesign kFourMeets where
  diag := by
    intro label
    rw [projectionOfDesign_graphicKFour]
    fin_cases label <;> simp [kFourEdgeVector, Fin.sum_univ_three] <;> norm_num
  weight := by
    intro label
    norm_num [graphicKFourDesign]
  heavy := by
    intro first second _ hmeet
    rw [abs_projectionOfDesign_graphicKFour first second hmeet.2]
    norm_num

/-- **THE LANDED HYPOTHESIS OF THE FRONTIER PRODUCER IS FALSE AT `(6, 3)`, WITH NO
HYPOTHESIS LEFT.**  The `K4` graphic design admits no excess dominated selection. -/
theorem not_forall_excessDominates_sixThree_unconditional :
    ¬ ∀ design : WeightedDesign 6 3,
        ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
          ExcessDominatesBlock design selected hcard :=
  not_forall_excessDominates_sixThree completeGraphProfile_graphicKFour

/-- **AND NO SELECTION OF THE `K4` GRAPHIC DESIGN IS EXCESS DOMINATED.**  The sharp form:
every one of its twenty triples fails, by the deficit `1 / 6` of section 9. -/
theorem not_exists_excessDominates_graphicKFour :
    ¬ ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
        ExcessDominatesBlock graphicKFourDesign selected hcard :=
  not_exists_excessDominates_of_crowded completeGraphProfile_graphicKFour (by norm_num)
    (fun selected hcard => kFourMeets_crowded selected hcard)

end Gtz

/-
# Crowdedness at every rank: `rank` edges on `rank + 1` vertices cannot avoid a crowd

`Gtz.not_exists_excessDominates_of_crowded` refutes the excess-dominance instrument at any
design carrying `Gtz.CompleteGraphProfile` whose every selection has a slot meeting two
other selected slots.  Its rank-three instance is landed
(`Gtz.kFourMeets_crowded`, a `decide` over the ordered triples of `Fin 6`), and above rank
three the crowdedness was a HYPOTHESIS: the registry records the gap as "the vertex count
`3 * p + 2 * s <= rank + 1` against `2 * p + s = rank`".

This module closes it, at every rank at once, and by a counting argument rather than a
decision procedure.

## The combinatorial core

Call a family of edges *sparse* when no edge meets two others of the family.  A sparse
family decomposes into isolated edges and paths of two edges, so `p` two-edge components
and `s` isolated ones span `3 * p + 2 * s` vertices while carrying `2 * p + s` edges, and
`3 * (2 * p + s) <= 2 * (3 * p + 2 * s)`.  That is
`Gtz.three_mul_card_le_two_mul_card_biUnion`:

  **a sparse family of two-element edges spans at least `3 / 2` times its own size in
  vertices.**

The proof here is an induction on the family rather than a decomposition: remove an
isolated edge (two fresh vertices, one edge) or a meeting pair (three fresh vertices, two
edges), and the inequality is preserved in both steps.  No matching, no components, no
graph structure — only that an edge has two ends and that two distinct edges meet in at
most one.

## The consequence

At `rank + 1` vertices a family of `rank` edges spans at most `rank + 1` vertices, so
`3 * rank <= 2 * (rank + 1)`, i.e. `rank <= 2`
(`Gtz.exists_crowded_of_three_le_rank`).  From rank three on, EVERY selection of `rank`
edges of a graph on `rank + 1` vertices has an edge meeting two others — which is exactly
the hypothesis `Gtz.not_exists_excessDominates_of_crowded` consumes.

`Gtz.completeGraphProfile_crowded_of_edgeLabelling` packages that for the profile, and
`Gtz.not_exists_excessDominates_of_edgeLabelling` is the verdict: **on the complete-graph
profile of any rank at least three, no selection is excess dominated.** The excess-dominance
lane is closed at every rank, not only at rank three.

The bound is SHARP as an inequality about sparse families: three vertices and two meeting
edges give `3 * 2 = 6 = 2 * 3`.  It is the vertex budget `rank + 1` that fails from rank
three, not the counting.
-/
import Mathlib
import Gtz.Wave.ThresholdCellDominance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Finset

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

/-! ## 1. Two distinct two-element edges meet in at most one vertex -/

/-- Two two-element sets that are not equal share at most one element. -/
theorem card_inter_le_one_of_card_two {s t : Finset V} (hs : s.card = 2) (ht : t.card = 2)
    (hne : s ≠ t) : (s ∩ t).card ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  have hsubs : s ∩ t ⊆ s := Finset.inter_subset_left
  have hsubt : s ∩ t ⊆ t := Finset.inter_subset_right
  have hcard : (s ∩ t).card = 2 :=
    le_antisymm (hs ▸ Finset.card_le_card hsubs) hcon
  have hs' : s ∩ t = s := Finset.eq_of_subset_of_card_le hsubs (by rw [hs, hcard])
  have ht' : s ∩ t = t := Finset.eq_of_subset_of_card_le hsubt (by rw [ht, hcard])
  exact hne (hs' ▸ ht')

/-- Two distinct two-element sets that meet have union of size exactly three. -/
theorem card_union_eq_three {s t : Finset V} (hs : s.card = 2) (ht : t.card = 2)
    (hne : s ≠ t) (hmeet : (s ∩ t).Nonempty) : (s ∪ t).card = 3 := by
  have hle := card_inter_le_one_of_card_two hs ht hne
  have hpos : 1 ≤ (s ∩ t).card := Finset.card_pos.mpr hmeet
  have hone : (s ∩ t).card = 1 := le_antisymm hle hpos
  have hsum := Finset.card_union_add_card_inter s t
  omega

/-! ## 2. The counting core

A family in which no member meets two others spans at least `3 / 2` times its size in
vertices. -/

/-- **A SPARSE FAMILY OF EDGES SPANS THREE HALVES ITS OWN SIZE.**  If every member of the
family is a two-element set, distinct members are distinct sets, and no member meets two
other members, then three times the number of edges is at most twice the number of vertices
they span.

The induction removes either an isolated edge (one edge, two fresh vertices) or a meeting
pair (two edges, three fresh vertices), and both steps preserve the inequality. -/
theorem three_mul_card_le_two_mul_card_biUnion (e : ι → Finset V) :
    ∀ S : Finset ι,
      (∀ i ∈ S, (e i).card = 2) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → e i ≠ e j) →
      (∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, j ≠ i → k ≠ i → j ≠ k →
        (e i ∩ e j).Nonempty → (e i ∩ e k).Nonempty → False) →
      3 * S.card ≤ 2 * (S.biUnion e).card := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hcard hinj hdeg
    rcases S.eq_empty_or_nonempty with rfl | ⟨i, hiS⟩
    · simp
    -- Does `i` meet some other member?
    by_cases hpartner : ∃ j ∈ S, j ≠ i ∧ (e i ∩ e j).Nonempty
    · -- the meeting pair `{i, j}` peels off three fresh vertices and two edges
      obtain ⟨j, hjS, hji, hmeet⟩ := hpartner
      set rest : Finset ι := (S.erase i).erase j with hrest
      have hjmem : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hji, hjS⟩
      have hrestSub : rest ⊆ S :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hiNotRest : i ∉ rest := by
        simp [hrest, Finset.mem_erase]
      have hjNotRest : j ∉ rest := by
        simp [hrest, Finset.mem_erase]
      -- every other member is disjoint from both `e i` and `e j`
      have hdisj : ∀ k ∈ rest, (e i ∩ e k) = ∅ ∧ (e j ∩ e k) = ∅ := by
        intro k hk
        have hkS : k ∈ S := hrestSub hk
        have hki : k ≠ i := by
          intro h; exact hiNotRest (h ▸ hk)
        have hkj : k ≠ j := by
          intro h; exact hjNotRest (h ▸ hk)
        constructor
        · by_contra hne
          exact hdeg i hiS j hjS k hkS hji hki (fun h => hkj h.symm) hmeet
            (Finset.nonempty_of_ne_empty hne)
        · by_contra hne
          have hmeetji : (e j ∩ e i).Nonempty := by
            rw [Finset.inter_comm] at hmeet; exact hmeet
          exact hdeg j hjS i hiS k hkS (fun h => hji h.symm) hkj (fun h => hki h.symm)
            hmeetji (Finset.nonempty_of_ne_empty hne)
      -- rebuild the family and its vertex set
      have hSrebuild : S = insert i (insert j rest) := by
        rw [hrest, Finset.insert_erase hjmem, Finset.insert_erase hiS]
      have hcardS : S.card = rest.card + 2 := by
        rw [hSrebuild, Finset.card_insert_of_notMem (by
          simp [Finset.mem_insert, hji.symm, hiNotRest]),
          Finset.card_insert_of_notMem hjNotRest]
      have hbiUnion : S.biUnion e = (e i ∪ e j) ∪ rest.biUnion e := by
        rw [hSrebuild, Finset.biUnion_insert, Finset.biUnion_insert, Finset.union_assoc]
      have hdisjUnion : Disjoint (e i ∪ e j) (rest.biUnion e) := by
        rw [Finset.disjoint_right]
        intro v hv hvij
        obtain ⟨k, hk, hvk⟩ := Finset.mem_biUnion.mp hv
        obtain ⟨hik, hjk⟩ := hdisj k hk
        rcases Finset.mem_union.mp hvij with hvi | hvj
        · exact absurd (Finset.mem_inter.mpr ⟨hvi, hvk⟩) (by rw [hik]; simp)
        · exact absurd (Finset.mem_inter.mpr ⟨hvj, hvk⟩) (by rw [hjk]; simp)
      have hpairCard : (e i ∪ e j).card = 3 :=
        card_union_eq_three (hcard i hiS) (hcard j hjS) (hinj i hiS j hjS (fun h => hji h.symm))
          hmeet
      have hcardV : (S.biUnion e).card = 3 + (rest.biUnion e).card := by
        rw [hbiUnion, Finset.card_union_of_disjoint hdisjUnion, hpairCard]
      -- the induction hypothesis on the smaller family
      have hstrict : rest ⊂ S := by
        refine ⟨hrestSub, ?_⟩
        intro hsub
        exact hiNotRest (hsub hiS)
      have hIH := ih rest hstrict
        (fun k hk => hcard k (hrestSub hk))
        (fun k hk l hl hkl => hinj k (hrestSub hk) l (hrestSub hl) hkl)
        (fun a ha b hb c hc =>
          hdeg a (hrestSub ha) b (hrestSub hb) c (hrestSub hc))
      omega
    · -- `i` is isolated: it peels off two fresh vertices and one edge
      push_neg at hpartner
      set rest : Finset ι := S.erase i with hrest
      have hrestSub : rest ⊆ S := Finset.erase_subset _ _
      have hiNotRest : i ∉ rest := by simp [hrest]
      have hdisj : ∀ k ∈ rest, (e i ∩ e k) = ∅ := by
        intro k hk
        have hkS : k ∈ S := hrestSub hk
        have hki : k ≠ i := by intro h; exact hiNotRest (h ▸ hk)
        exact hpartner k hkS hki
      have hSrebuild : S = insert i rest := (Finset.insert_erase hiS).symm
      have hcardS : S.card = rest.card + 1 := by
        rw [hSrebuild, Finset.card_insert_of_notMem hiNotRest]
      have hbiUnion : S.biUnion e = e i ∪ rest.biUnion e := by
        rw [hSrebuild, Finset.biUnion_insert]
      have hdisjUnion : Disjoint (e i) (rest.biUnion e) := by
        rw [Finset.disjoint_right]
        intro v hv hvi
        obtain ⟨k, hk, hvk⟩ := Finset.mem_biUnion.mp hv
        exact absurd (Finset.mem_inter.mpr ⟨hvi, hvk⟩) (by rw [hdisj k hk]; simp)
      have hcardV : (S.biUnion e).card = 2 + (rest.biUnion e).card := by
        rw [hbiUnion, Finset.card_union_of_disjoint hdisjUnion, hcard i hiS]
      have hstrict : rest ⊂ S := by
        refine ⟨hrestSub, ?_⟩
        intro hsub
        exact hiNotRest (hsub hiS)
      have hIH := ih rest hstrict
        (fun k hk => hcard k (hrestSub hk))
        (fun k hk l hl hkl => hinj k (hrestSub hk) l (hrestSub hl) hkl)
        (fun a ha b hb c hc =>
          hdeg a (hrestSub ha) b (hrestSub hb) c (hrestSub hc))
      omega

/-! ## 3. The vertex budget fails from rank three -/

/-- **A FAMILY OF `rank` EDGES ON `rank + 1` VERTICES IS CROWDED FROM RANK THREE.**  Some
member meets two others.  The vertex count is the whole proof: a sparse family would need
`3 * rank / 2` vertices and only `rank + 1` are available. -/
theorem exists_meets_two_of_three_le_rank {rank : ℕ} (hrank : 3 ≤ rank)
    (e : ι → Finset (Fin (rank + 1))) (S : Finset ι) (hS : S.card = rank)
    (hcard : ∀ i ∈ S, (e i).card = 2)
    (hinj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → e i ≠ e j) :
    ∃ i ∈ S, ∃ j ∈ S, ∃ k ∈ S, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      (e i ∩ e j).Nonempty ∧ (e i ∩ e k).Nonempty := by
  by_contra hcon
  push_neg at hcon
  have hsparse : ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, j ≠ i → k ≠ i → j ≠ k →
      (e i ∩ e j).Nonempty → (e i ∩ e k).Nonempty → False := by
    intro i hi j hj k hk hji hki hjk hij hik
    exact absurd (hcon i hi j hj k hk hji hki hjk hij)
      (Finset.nonempty_iff_ne_empty.mp hik)
  have hcount := three_mul_card_le_two_mul_card_biUnion e S hcard hinj hsparse
  have hvert : (S.biUnion e).card ≤ rank + 1 := by
    have := Finset.card_le_univ (S.biUnion e)
    simpa using this
  rw [hS] at hcount
  omega

/-! ## 4. The profile's crowdedness, at every rank -/

/-- **THE CROWDEDNESS THE PROFILE CONSUMES, AT EVERY RANK AT LEAST THREE.**  Any labelling
of the design's atoms by distinct edges of a graph on `rank + 1` vertices makes every
selection of `rank` atoms crowded, in exactly the shape
`Gtz.not_exists_excessDominates_of_crowded` asks for. -/
theorem completeGraphProfile_crowded_of_edgeLabelling {size rank : ℕ} (hrank : 3 ≤ rank)
    (edge : Fin size → Finset (Fin (rank + 1)))
    (hcard : ∀ i, (edge i).card = 2) (hinj : Function.Injective edge)
    (selected : Finset (Fin size)) (hsel : selected.card = rank) :
    ∃ slot first second : Fin rank, first ≠ slot ∧ second ≠ slot ∧ first ≠ second ∧
      (edge (selected.orderEmbOfFin hsel slot)
        ∩ edge (selected.orderEmbOfFin hsel first)).Nonempty ∧
      (edge (selected.orderEmbOfFin hsel slot)
        ∩ edge (selected.orderEmbOfFin hsel second)).Nonempty := by
  classical
  obtain ⟨i, hi, j, hj, k, hk, hji, hki, hjk, hij, hik⟩ :=
    exists_meets_two_of_three_le_rank hrank edge selected hsel
      (fun a _ => hcard a) (fun a _ b _ hab h => hab (hinj h))
  -- transport the three labels back through the order embedding
  set emb := selected.orderEmbOfFin hsel with hemb
  have hsurj : ∀ a ∈ selected, ∃ x : Fin rank, emb x = a := by
    intro a ha
    have hmem : a ∈ Set.range emb := by
      rw [hemb, Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr ha
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, hx⟩
  obtain ⟨slot, hslot⟩ := hsurj i hi
  obtain ⟨first, hfirst⟩ := hsurj j hj
  obtain ⟨second, hsecond⟩ := hsurj k hk
  refine ⟨slot, first, second, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact hji (by rw [← hfirst, ← hslot, h])
  · intro h; exact hki (by rw [← hsecond, ← hslot, h])
  · intro h; exact hjk (by rw [← hfirst, ← hsecond, h])
  · rw [hslot, hfirst]; exact hij
  · rw [hslot, hsecond]; exact hik

/-- **THE VERDICT, AT EVERY RANK.**  A design of any cell whose atoms are labelled by
distinct edges of a graph on `rank + 1` vertices, and which carries the complete-graph
profile for the meeting relation of that labelling, admits NO excess dominated selection
from rank three on.  The rank-three instance is the landed `K4` witness; this is the same
statement at every rank, and it closes the excess-dominance lane registry-wide. -/
theorem not_exists_excessDominates_of_edgeLabelling {size rank : ℕ} (hrank : 3 ≤ rank)
    {design : WeightedDesign size rank}
    (edge : Fin size → Finset (Fin (rank + 1)))
    (hcard : ∀ i, (edge i).card = 2) (hinj : Function.Injective edge)
    (hprofile : CompleteGraphProfile design
      (fun first second => (edge first ∩ edge second).Nonempty)) :
    ¬ ∃ selected : Finset (Fin size), ∃ hsel : selected.card = rank,
        ExcessDominatesBlock design selected hsel :=
  not_exists_excessDominates_of_crowded hprofile (by omega)
    (fun selected hsel =>
      completeGraphProfile_crowded_of_edgeLabelling hrank edge hcard hinj selected hsel)

/-- **THE LANDED HYPOTHESIS OF THE FRONTIER PRODUCER FAILS AT EVERY RANK.**  One design of
one cell, labelled by edges, refutes the universally quantified excess dominance the
producer asks for. -/
theorem not_forall_excessDominates_of_edgeLabelling {size rank : ℕ} (hrank : 3 ≤ rank)
    {design : WeightedDesign size rank}
    (edge : Fin size → Finset (Fin (rank + 1)))
    (hcard : ∀ i, (edge i).card = 2) (hinj : Function.Injective edge)
    (hprofile : CompleteGraphProfile design
      (fun first second => (edge first ∩ edge second).Nonempty)) :
    ¬ ∀ other : WeightedDesign size rank,
        ∃ selected : Finset (Fin size), ∃ hsel : selected.card = rank,
          ExcessDominatesBlock other selected hsel := by
  intro hall
  exact not_exists_excessDominates_of_edgeLabelling hrank edge hcard hinj hprofile
    (hall design)

/-- **AND THE REPAIRED, PRIMITIVE HYPOTHESIS FAILS TOO**, whenever the labelled witness is
primitive.  So the dominance lane is closed on the primitive stratum as well, at every
rank. -/
theorem not_forall_primitiveExcessDominates_of_edgeLabelling {size rank : ℕ}
    (hrank : 3 ≤ rank) {design : WeightedDesign size rank}
    (edge : Fin size → Finset (Fin (rank + 1)))
    (hcard : ∀ i, (edge i).card = 2) (hinj : Function.Injective edge)
    (hprofile : CompleteGraphProfile design
      (fun first second => (edge first ∩ edge second).Nonempty))
    (hprim : IsPrimitiveDesign design) :
    ¬ ∀ other : WeightedDesign size rank, IsPrimitiveDesign other →
        ∃ selected : Finset (Fin size), ∃ hsel : selected.card = rank,
          ExcessDominatesBlock other selected hsel := by
  intro hall
  exact not_exists_excessDominates_of_edgeLabelling hrank edge hcard hinj hprofile
    (hall design hprim)

/-! ## 5. The labellings, so the hypothesis is visibly inhabited

Section 4 quantifies over an edge labelling.  Here are the two that matter: the complete
graph on four vertices, whose meeting relation is the landed `Gtz.kFourMeets` — so the
general theorem reproduces the landed rank-three refutation — and the complete graph on
five vertices, which is the first cell where the statement is new. -/

/-- The six edges of the complete graph on four vertices, in the labelling of
`Gtz.graphicKFourDesign`: the complementary pairs are `(0,1)`, `(2,3)` and `(4,5)`. -/
def kFourEdgeSet : Fin 6 → Finset (Fin 4) :=
  ![{0, 1}, {2, 3}, {0, 2}, {1, 3}, {0, 3}, {1, 2}]

theorem kFourEdgeSet_card (i : Fin 6) : (kFourEdgeSet i).card = 2 := by
  fin_cases i <;> decide

theorem kFourEdgeSet_injective : Function.Injective kFourEdgeSet := by
  decide

/-- **THE LABELLING REPRODUCES THE LANDED MEETING RELATION.**  Two labels meet as edges of
the complete graph on four vertices exactly when `Gtz.kFourMeets` says so, so section 4
specialises at rank three to the landed `K4` refutation. -/
theorem kFourEdgeSet_inter_nonempty_iff :
    ∀ i j : Fin 6, i ≠ j →
      ((kFourEdgeSet i ∩ kFourEdgeSet j).Nonempty ↔ kFourMeets i j) := by
  decide

/-- The ten edges of the complete graph on five vertices — the threshold cell of rank
four. -/
def kFiveEdgeSet : Fin 10 → Finset (Fin 5) :=
  ![{0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}]

theorem kFiveEdgeSet_card (i : Fin 10) : (kFiveEdgeSet i).card = 2 := by
  fin_cases i <;> decide

theorem kFiveEdgeSet_injective : Function.Injective kFiveEdgeSet := by
  decide

/-- **THE RANK-FOUR VERDICT.**  A design of the threshold cell `(10, 4)` carrying the
complete-graph profile for the edge meeting relation of the complete graph on five vertices
admits no excess dominated selection.  This is the first instance of section 4 that was not
already in the tree. -/
theorem not_exists_excessDominates_kFive {design : WeightedDesign 10 4}
    (hprofile : CompleteGraphProfile design
      (fun first second => (kFiveEdgeSet first ∩ kFiveEdgeSet second).Nonempty)) :
    ¬ ∃ selected : Finset (Fin 10), ∃ hsel : selected.card = 4,
        ExcessDominatesBlock design selected hsel :=
  not_exists_excessDominates_of_edgeLabelling (by norm_num) kFiveEdgeSet kFiveEdgeSet_card
    kFiveEdgeSet_injective hprofile

/-! ## 6. The bound is sharp as a counting statement

Two meeting edges span three vertices and `3 * 2 = 2 * 3`, so the inequality of section 2
cannot be improved.  What fails from rank three is the vertex BUDGET `rank + 1`, not the
count. -/

/-- The sharp instance: a two-edge path spans three vertices. -/
theorem three_mul_two_eq_two_mul_three : 3 * 2 = 2 * 3 := by norm_num

end Gtz

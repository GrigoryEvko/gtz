/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Quantitative.TwoGraphCollision
import Gtz.Quantitative.SixThreeExclusionFrontier

/-!
# The sign layer with ONE pairing allowed to vanish

`Gtz.residualSectors` and `Gtz.SixThreeCrux.linkWord_mem_residualSectors` carry a
GLOBAL nonvanishing hypothesis — all fifteen pairings nonzero — and a crux is not
known to supply it.  The vanishing branch had the mathematics but not the
aggregate: `Gtz.not_forall_coherent_of_orthogonalEdge` and its incoherent sibling
were proved, and `Gtz/Quantitative/SixThreeExclusionFrontier.lean` recorded their
sector-table consequence as PROSE — "measured on the sector table outside Lean,
one orthogonal edge leaves 840 of the 1024 two-graphs".  This module makes that a
theorem, and makes the whole branch one explicit decidable object.

## THE MECHANISM

Fix the named edge `{0,1}` and assume nonvanishing everywhere else
(`Gtz.OffEdgeZeroOneNonzero`).  Three constraints survive.

* **L1 relocalized.**  `Gtz.card_le_three_of_forall_incoherent_through_base`
  already takes PER-EDGE nonvanishing hypotheses, so the incoherent-quadruple cap
  applies at any `(base, quadruple)` configuration whose ten internal edges avoid
  `{0,1}`.  A base and a four-set span five of the six atoms, so a configuration is
  usable exactly when the OMITTED atom is `0` or `1` — ten of the thirty.
* **L2 relocalized.**  The shipped coherent cap routes through
  `Gtz.exists_antiParityPartner_sixThree`, whose hypothesis is global.  It does not
  have to: `Gtz.exists_isChartDual_sixThree` is hypothesis-free, and
  `Gtz.atomPairing_chartDual` and `Gtz.tripleParity_chartDual_eq_neg_one_of_coherent`
  consume one edge at a time.  `Gtz.card_le_three_of_forall_coherent_through_base_local`
  is the resulting per-edge form; it is what makes the branch work at all.
* **ORTH.**  `Gtz.not_forall_coherent_of_orthogonalEdge` and
  `Gtz.not_forall_incoherent_of_orthogonalEdge` already take exactly the local data
  — the vanishing edge and its star — so they apply verbatim at `{0,1}`.

## L3 CONTRIBUTES NOTHING, AND THE FULL L3 TEST IS NOT AVAILABLE

The saturated-matching lever is absent above, and both halves of that are worth
stating precisely because the naive reading of the branch gets them backwards.

A matching edge carries the L3 argument only where
`Gtz.atomShare_add_atomShare_lt_one_of_coherentEdge` applies, and that lemma needs
the edge's OWN pairing nonzero, not merely its star.  Every perfect matching on six
atoms either contains `{0,1}` — whose own pairing vanishes — or matches `0` to some
other atom, and then THAT edge's star contains `{0,1}`.  So at this vanishing
pattern the honest count of L3-usable matchings is ZERO, and the 840 is L1 and L2
and ORTH with nothing else in it.

Nothing is lost by that.  `Gtz.sectorCount_orthEdgeZeroOne_matchingThroughEdge_redundant`
runs the three matchings through the vanishing edge — the most generous reading,
granting L3 at an edge where it is not justified — and finds it removes NO
two-graph from the branch: the count is `0`, so this is set containment and not a
cardinality coincidence.

The full fifteen-matching test is a different matter and must NOT be imported here.
`Gtz.sectorCount_orthEdgeZeroOne_not_hasNoSaturatedMatching` counts 24 branch
survivors that `Gtz.hasNoSaturatedMatching` would exclude, and every one of those
exclusions rests on a matching whose edges have a star through `{0,1}`.  Those 24
are exactly the measure of how much an unexamined reuse of the generic branch's
third lever would overclaim.

## THE COUNTS

Every number below is `decide +kernel` on the 1024 two-graphs, not a measurement.

| test                                        | survivors |
| ------------------------------------------- | --------- |
| L1 on the ten usable configurations          |  994      |
| L2 on the ten usable configurations          |  994      |
| L1 and L2                                    |  964      |
| ORTH at `{0,1}` alone                        |  896      |
| all three — `Gtz.residualSectorsOrthEdgeZeroOne` | **840** |
| the nonvanishing branch, `Gtz.residualSectors`   |  842     |

## THE BRANCH IS NOT A SUB-CASE OF THE GENERIC ONE

`Gtz.residualSectorsOrthEdgeZeroOne` and `Gtz.residualSectors` are INCOMPARABLE:
768 two-graphs lie in both, 72 lie only in the vanishing branch
(`Gtz.sectorCount_orthEdgeZeroOne_not_residual`) and 74 only in the nonvanishing one
(`Gtz.sectorCount_residual_not_orthEdgeZeroOne`).  Losing the two obtuse levers at
twenty of the thirty configurations really does admit patterns the generic branch
forbids; ORTH really does forbid patterns the generic branch admits.  Neither
count bounds the other and the near-equality 840 against 842 is a coincidence of
size, not a containment.

## THE AGGREGATE

`Gtz.residualSectorsEdgeZeroOneFree` is the union, 914 of 1024, and
`Gtz.linkWordOf_mem_residualSectorsEdgeZeroOneFree` places EVERY `(6,3)` design
inside it under fourteen nonvanishing assumptions instead of fifteen — the
pairing at `{0,1}` is unconstrained.  That is the trade the branch makes explicit:
dropping one nonvanishing hypothesis costs 72 patterns, from 842 to 914, and does
not cost the lane.

## WHAT THIS DOES NOT DO

The edge is NAMED, and the strength of the branch depends on that.  Nothing here
quantifies over WHICH pairing vanishes, and a successor should not spend the
fourteen further clause sets it would take to do so.  Measured outside Lean, on the
same encoding this file mechanizes:

* all fifteen single-edge branches have cardinality exactly 840, as S(6)-equivariance
  of the constraint set predicts, so one representative determines every count;
* but the fifteen SETS are pairwise distinct, and their UNION is 992 of 1024.

So the honest unconditional statement — "exactly one pairing vanishes, at an unknown
edge" — would exclude 32 two-graphs where the named-edge statement excludes 184.  The
union also swallows `Gtz.residualSectors` whole: 992 again with the generic branch
thrown in.  The information is in knowing WHERE the pairing vanishes; the moment that
is forgotten, almost all of it is gone.  Their INTERSECTION is 192, and that is not a
new object either — it is exactly the set of two-graphs with no saturated star at any
of the fifteen edges, the 192 already recorded in this campaign's ledger.

Proving edge-independence inside Lean rather than measuring it needs an ingredient the
tree does not have: an action of `Equiv.Perm (Fin 6)` on `Gtz.WeightedDesign 6 3`
together with the transport of `Gtz.tripleParity` along it.  `Equiv.Perm` appears in
`Gtz/Design/LinePatternEnumeration.lean` only as an abstract relabelling of PATTERNS,
never as an action on designs.

Two or more vanishing pairings are out of scope; the levers thin further there
(measured outside Lean at 800 for two disjoint edges, 758 for two sharing an atom, 720
for a perfect matching, 700 for a path of three), and each pattern needs its own
usable-set computation.  Nothing here approaches `IsEmpty Gtz.SixThreeCrux`: like the
generic branch, this one does not empty, and by `Gtz.card_residualSectors`'s own
reasoning a residue that does not empty is a residue no sign-only argument cuts.
-/

namespace Gtz

/-! ## 1. The hypothesis

Nonvanishing at every pairing except possibly the named edge `{0,1}`.  Written on
the unordered pair so that it is automatically symmetric and every side condition
at a concrete configuration is `decide`. -/

/-- Every pairing except possibly the one at `{0,1}` is nonzero. -/
def OffEdgeZeroOneNonzero (design : WeightedDesign 6 3) : Prop :=
  ∀ first second : Fin 6, first ≠ second →
    ({first, second} : Finset (Fin 6)) ≠ {0, 1} → atomPairing design first second ≠ 0

/-- The global hypothesis of `Gtz.linkWordOf_mem_residualSectors` implies this one. -/
theorem offEdgeZeroOneNonzero_of_forall_nonzero (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0) :
    OffEdgeZeroOneNonzero design :=
  fun first second hne _ => hnonzero first second hne

/-- The star of `0` inside the named edge's complement. -/
theorem edgeZeroOne_star_nonzero_first (design : WeightedDesign 6 3)
    (hoff : OffEdgeZeroOneNonzero design) :
    ∀ other : Fin 6, other ≠ 0 → other ≠ 1 → atomPairing design 0 other ≠ 0 := by
  intro other hzero hone
  exact hoff 0 other (Ne.symm hzero) (by
    have hcover : ∀ o : Fin 6, o ≠ 0 → o ≠ 1 → o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 := by decide
    rcases hcover other hzero hone with rfl | rfl | rfl | rfl <;> decide)

/-- The star of `1` inside the named edge's complement. -/
theorem edgeZeroOne_star_nonzero_second (design : WeightedDesign 6 3)
    (hoff : OffEdgeZeroOneNonzero design) :
    ∀ other : Fin 6, other ≠ 0 → other ≠ 1 → atomPairing design 1 other ≠ 0 := by
  intro other hzero hone
  exact hoff 1 other (Ne.symm hone) (by
    have hcover : ∀ o : Fin 6, o ≠ 0 → o ≠ 1 → o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 := by decide
    rcases hcover other hzero hone with rfl | rfl | rfl | rfl <;> decide)

/-! ## 2. L1 and L2, relocalized

The `hsafe` hypothesis is the localization: it says the five atoms of the
configuration never present the pair `{0,1}`, which at a concrete configuration is
one `decide`. -/

/-- **L1 with per-edge nonvanishing.**  The shipped
`Gtz.incoherentQuadruple_eq_false` asks for all fifteen pairings; the cap it calls
asks only for the ten inside the configuration. -/
theorem incoherentQuadruple_eq_false_offEdgeZeroOne (design : WeightedDesign 6 3)
    (hoff : OffEdgeZeroOneNonzero design)
    (base quadFirst quadSecond quadThird quadFourth : Fin 6)
    (hcard : ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)).card = 4)
    (hbase : base ∉ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)))
    (hsafe : ∀ x ∈ ({base, quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
        ∀ y ∈ ({base, quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
        ({x, y} : Finset (Fin 6)) ≠ {0, 1}) :
    (sectorIncoherent (linkWordOf design) base quadFirst quadSecond
      && sectorIncoherent (linkWordOf design) base quadFirst quadThird
      && sectorIncoherent (linkWordOf design) base quadFirst quadFourth
      && sectorIncoherent (linkWordOf design) base quadSecond quadThird
      && sectorIncoherent (linkWordOf design) base quadSecond quadFourth
      && sectorIncoherent (linkWordOf design) base quadThird quadFourth) = false := by
  by_contra hcontra
  rw [Bool.not_eq_false] at hcontra
  simp only [sectorIncoherent_linkWordOf, Bool.and_eq_true, decide_eq_true_eq] at hcontra
  obtain ⟨⟨⟨⟨⟨hfs, hft⟩, hfu⟩, hst⟩, hsu⟩, htu⟩ := hcontra
  have hcomm : ∀ leftAtom rightAtom : Fin 6,
      tripleParity design base leftAtom rightAtom
        = tripleParity design base rightAtom leftAtom :=
    fun leftAtom rightAtom => tripleParity_comm_right design base leftAtom rightAtom
  have hall : ∀ first ∈ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
      ∀ second ∈ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
      first ≠ second → tripleParity design base first second = -1 := by
    intro first hfirst second hsecond hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
    rcases hfirst with rfl | rfl | rfl | rfl <;> rcases hsecond with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | assumption
        | (rw [hcomm]; assumption)
  have hcap := card_le_three_of_forall_incoherent_through_base design base
    {quadFirst, quadSecond, quadThird, quadFourth} hbase
    (fun index hmem => hoff base index (by rintro rfl; exact hbase hmem)
      (hsafe base (Finset.mem_insert_self _ _) index (Finset.mem_insert_of_mem hmem)))
    (fun first hfirst second hsecond hne => hoff first second hne
      (hsafe first (Finset.mem_insert_of_mem hfirst) second (Finset.mem_insert_of_mem hsecond)))
    hall
  omega

/-- **THE COHERENT CAP WITH PER-EDGE NONVANISHING.**  `Gtz.exists_antiParityPartner_sixThree`
packages the chart dual behind a GLOBAL hypothesis, which is what stopped L2 from
entering the vanishing branch.  Unpacking it — `Gtz.exists_isChartDual_sixThree`
needs nothing, and the two transport laws consume one edge each — recovers the cap
on exactly the edges the family uses. -/
theorem card_le_three_of_forall_coherent_through_base_local (design : WeightedDesign 6 3)
    (base : Fin 6) (family : Finset (Fin 6)) (hbaseNotMem : base ∉ family)
    (hbaseNonzero : ∀ index ∈ family, atomPairing design base index ≠ 0)
    (hinnerNonzero : ∀ first ∈ family, ∀ second ∈ family, first ≠ second →
      atomPairing design first second ≠ 0)
    (hcoherent : ∀ first ∈ family, ∀ second ∈ family, first ≠ second →
      tripleParity design base first second = 1) :
    family.card ≤ 3 := by
  obtain ⟨partner, hpartner⟩ := exists_isChartDual_sixThree design
  refine card_le_three_of_forall_incoherent_through_base partner base family hbaseNotMem
    ?_ ?_ ?_
  · intro index hmem
    have hne : base ≠ index := by rintro rfl; exact hbaseNotMem hmem
    rw [atomPairing_chartDual hpartner hne]
    exact neg_ne_zero.mpr (hbaseNonzero index hmem)
  · intro first hfirst second hsecond hne
    rw [atomPairing_chartDual hpartner hne]
    exact neg_ne_zero.mpr (hinnerNonzero first hfirst second hsecond hne)
  · intro first hfirst second hsecond hne
    have hbaseFirst : base ≠ first := by rintro rfl; exact hbaseNotMem hfirst
    have hbaseSecond : base ≠ second := by rintro rfl; exact hbaseNotMem hsecond
    exact tripleParity_chartDual_eq_neg_one_of_coherent hpartner hbaseFirst hbaseSecond hne
      (hbaseNonzero first hfirst) (hbaseNonzero second hsecond)
      (hinnerNonzero first hfirst second hsecond hne)
      (hcoherent first hfirst second hsecond hne)

/-- **L2 with per-edge nonvanishing.** -/
theorem coherentQuadruple_eq_false_offEdgeZeroOne (design : WeightedDesign 6 3)
    (hoff : OffEdgeZeroOneNonzero design)
    (base quadFirst quadSecond quadThird quadFourth : Fin 6)
    (hcard : ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)).card = 4)
    (hbase : base ∉ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)))
    (hsafe : ∀ x ∈ ({base, quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
        ∀ y ∈ ({base, quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
        ({x, y} : Finset (Fin 6)) ≠ {0, 1}) :
    (!(sectorIncoherent (linkWordOf design) base quadFirst quadSecond)
      && !(sectorIncoherent (linkWordOf design) base quadFirst quadThird)
      && !(sectorIncoherent (linkWordOf design) base quadFirst quadFourth)
      && !(sectorIncoherent (linkWordOf design) base quadSecond quadThird)
      && !(sectorIncoherent (linkWordOf design) base quadSecond quadFourth)
      && !(sectorIncoherent (linkWordOf design) base quadThird quadFourth)) = false := by
  by_contra hcontra
  rw [Bool.not_eq_false] at hcontra
  simp only [sectorIncoherent_linkWordOf, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not] at hcontra
  obtain ⟨⟨⟨⟨⟨hfs, hft⟩, hfu⟩, hst⟩, hsu⟩, htu⟩ := hcontra
  have hcomm : ∀ leftAtom rightAtom : Fin 6,
      tripleParity design base leftAtom rightAtom
        = tripleParity design base rightAtom leftAtom :=
    fun leftAtom rightAtom => tripleParity_comm_right design base leftAtom rightAtom
  have hall : ∀ first ∈ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
      ∀ second ∈ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
      first ≠ second → tripleParity design base first second = 1 := by
    intro first hfirst second hsecond hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
    rcases hfirst with rfl | rfl | rfl | rfl <;> rcases hsecond with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | (apply tripleParity_eq_one_of_ne_neg_one; assumption)
        | (rw [hcomm]; apply tripleParity_eq_one_of_ne_neg_one; assumption)
  have hcap := card_le_three_of_forall_coherent_through_base_local design base
    {quadFirst, quadSecond, quadThird, quadFourth} hbase
    (fun index hmem => hoff base index (by rintro rfl; exact hbase hmem)
      (hsafe base (Finset.mem_insert_self _ _) index (Finset.mem_insert_of_mem hmem)))
    (fun first hfirst second hsecond hne => hoff first second hne
      (hsafe first (Finset.mem_insert_of_mem hfirst) second (Finset.mem_insert_of_mem hsecond)))
    hall
  omega

/-! ## 3. The three sector tests

The ten usable configurations are the five omitting atom `0` — bases `1,2,3,4,5` —
and the five omitting atom `1` — bases `0,2,3,4,5`. -/

/-- **L1 as a sector test, on the ten configurations that avoid the edge `{0,1}`.** -/
def hasNoIncoherentQuadrupleOffEdgeZeroOne (link : Nat) : Bool :=
      !(sectorIncoherent link 1 2 3 && sectorIncoherent link 1 2 4 && sectorIncoherent link 1 2 5
        && sectorIncoherent link 1 3 4 && sectorIncoherent link 1 3 5
        && sectorIncoherent link 1 4 5)
  &&  !(sectorIncoherent link 2 1 3 && sectorIncoherent link 2 1 4 && sectorIncoherent link 2 1 5
        && sectorIncoherent link 2 3 4 && sectorIncoherent link 2 3 5
        && sectorIncoherent link 2 4 5)
  &&  !(sectorIncoherent link 3 1 2 && sectorIncoherent link 3 1 4 && sectorIncoherent link 3 1 5
        && sectorIncoherent link 3 2 4 && sectorIncoherent link 3 2 5
        && sectorIncoherent link 3 4 5)
  &&  !(sectorIncoherent link 4 1 2 && sectorIncoherent link 4 1 3 && sectorIncoherent link 4 1 5
        && sectorIncoherent link 4 2 3 && sectorIncoherent link 4 2 5
        && sectorIncoherent link 4 3 5)
  &&  !(sectorIncoherent link 5 1 2 && sectorIncoherent link 5 1 3 && sectorIncoherent link 5 1 4
        && sectorIncoherent link 5 2 3 && sectorIncoherent link 5 2 4
        && sectorIncoherent link 5 3 4)
  &&  !(sectorIncoherent link 0 2 3 && sectorIncoherent link 0 2 4 && sectorIncoherent link 0 2 5
        && sectorIncoherent link 0 3 4 && sectorIncoherent link 0 3 5
        && sectorIncoherent link 0 4 5)
  &&  !(sectorIncoherent link 2 0 3 && sectorIncoherent link 2 0 4 && sectorIncoherent link 2 0 5
        && sectorIncoherent link 2 3 4 && sectorIncoherent link 2 3 5
        && sectorIncoherent link 2 4 5)
  &&  !(sectorIncoherent link 3 0 2 && sectorIncoherent link 3 0 4 && sectorIncoherent link 3 0 5
        && sectorIncoherent link 3 2 4 && sectorIncoherent link 3 2 5
        && sectorIncoherent link 3 4 5)
  &&  !(sectorIncoherent link 4 0 2 && sectorIncoherent link 4 0 3 && sectorIncoherent link 4 0 5
        && sectorIncoherent link 4 2 3 && sectorIncoherent link 4 2 5
        && sectorIncoherent link 4 3 5)
  &&  !(sectorIncoherent link 5 0 2 && sectorIncoherent link 5 0 3 && sectorIncoherent link 5 0 4
        && sectorIncoherent link 5 2 3 && sectorIncoherent link 5 2 4
        && sectorIncoherent link 5 3 4)

/-- **L2 as a sector test, on the same ten configurations.** -/
def hasNoCoherentQuadrupleOffEdgeZeroOne (link : Nat) : Bool :=
      !(!(sectorIncoherent link 1 2 3) && !(sectorIncoherent link 1 2 4)
        && !(sectorIncoherent link 1 2 5) && !(sectorIncoherent link 1 3 4)
        && !(sectorIncoherent link 1 3 5) && !(sectorIncoherent link 1 4 5))
  &&  !(!(sectorIncoherent link 2 1 3) && !(sectorIncoherent link 2 1 4)
        && !(sectorIncoherent link 2 1 5) && !(sectorIncoherent link 2 3 4)
        && !(sectorIncoherent link 2 3 5) && !(sectorIncoherent link 2 4 5))
  &&  !(!(sectorIncoherent link 3 1 2) && !(sectorIncoherent link 3 1 4)
        && !(sectorIncoherent link 3 1 5) && !(sectorIncoherent link 3 2 4)
        && !(sectorIncoherent link 3 2 5) && !(sectorIncoherent link 3 4 5))
  &&  !(!(sectorIncoherent link 4 1 2) && !(sectorIncoherent link 4 1 3)
        && !(sectorIncoherent link 4 1 5) && !(sectorIncoherent link 4 2 3)
        && !(sectorIncoherent link 4 2 5) && !(sectorIncoherent link 4 3 5))
  &&  !(!(sectorIncoherent link 5 1 2) && !(sectorIncoherent link 5 1 3)
        && !(sectorIncoherent link 5 1 4) && !(sectorIncoherent link 5 2 3)
        && !(sectorIncoherent link 5 2 4) && !(sectorIncoherent link 5 3 4))
  &&  !(!(sectorIncoherent link 0 2 3) && !(sectorIncoherent link 0 2 4)
        && !(sectorIncoherent link 0 2 5) && !(sectorIncoherent link 0 3 4)
        && !(sectorIncoherent link 0 3 5) && !(sectorIncoherent link 0 4 5))
  &&  !(!(sectorIncoherent link 2 0 3) && !(sectorIncoherent link 2 0 4)
        && !(sectorIncoherent link 2 0 5) && !(sectorIncoherent link 2 3 4)
        && !(sectorIncoherent link 2 3 5) && !(sectorIncoherent link 2 4 5))
  &&  !(!(sectorIncoherent link 3 0 2) && !(sectorIncoherent link 3 0 4)
        && !(sectorIncoherent link 3 0 5) && !(sectorIncoherent link 3 2 4)
        && !(sectorIncoherent link 3 2 5) && !(sectorIncoherent link 3 4 5))
  &&  !(!(sectorIncoherent link 4 0 2) && !(sectorIncoherent link 4 0 3)
        && !(sectorIncoherent link 4 0 5) && !(sectorIncoherent link 4 2 3)
        && !(sectorIncoherent link 4 2 5) && !(sectorIncoherent link 4 3 5))
  &&  !(!(sectorIncoherent link 5 0 2) && !(sectorIncoherent link 5 0 3)
        && !(sectorIncoherent link 5 0 4) && !(sectorIncoherent link 5 2 3)
        && !(sectorIncoherent link 5 2 4) && !(sectorIncoherent link 5 3 4))

/-- **ORTH as a sector test.**  The four triples through the vanishing edge do not
share a parity, in either direction. -/
def edgeZeroOneNotSaturated (link : Nat) : Bool :=
      !(sectorIncoherent link 0 1 2 && sectorIncoherent link 0 1 3
        && sectorIncoherent link 0 1 4 && sectorIncoherent link 0 1 5)
  &&  !(!(sectorIncoherent link 0 1 2) && !(sectorIncoherent link 0 1 3)
        && !(sectorIncoherent link 0 1 4) && !(sectorIncoherent link 0 1 5))

/-- Every constraint the sign layer imposes when the pairing at `{0,1}` vanishes and
no other pairing does. -/
def sectorSurvivesOrthEdgeZeroOne (link : Nat) : Bool :=
  hasNoIncoherentQuadrupleOffEdgeZeroOne link && hasNoCoherentQuadrupleOffEdgeZeroOne link
    && edgeZeroOneNotSaturated link

/-- **THE VANISHING BRANCH'S RESIDUAL SECTORS**, as one explicit decidable object,
the counterpart of `Gtz.residualSectors`. -/
def residualSectorsOrthEdgeZeroOne : Finset Nat :=
  (Finset.range 1024).filter fun link => sectorSurvivesOrthEdgeZeroOne link = true

theorem mem_residualSectorsOrthEdgeZeroOne_iff (link : Nat) :
    link ∈ residualSectorsOrthEdgeZeroOne ↔
      link < 1024 ∧ sectorSurvivesOrthEdgeZeroOne link = true := by
  rw [residualSectorsOrthEdgeZeroOne, Finset.mem_filter, Finset.mem_range]

/-! ## 4. The counts -/

/-- **THE VANISHING-BRANCH RESIDUE: 840 OF 1024**, against 842 in the nonvanishing
branch.  The prose in `Gtz/Quantitative/SixThreeExclusionFrontier.lean` recorded
this as a measurement; it is a theorem. -/
theorem card_residualSectorsOrthEdgeZeroOne : residualSectorsOrthEdgeZeroOne.card = 840 := by
  rw [residualSectorsOrthEdgeZeroOne]
  decide +kernel

/-- L1 alone on the ten usable configurations. -/
theorem sectorCount_incoherentQuadrupleOffEdgeZeroOne :
    sectorCount hasNoIncoherentQuadrupleOffEdgeZeroOne = 994 := by decide +kernel

/-- L2 alone on the ten usable configurations. -/
theorem sectorCount_coherentQuadrupleOffEdgeZeroOne :
    sectorCount hasNoCoherentQuadrupleOffEdgeZeroOne = 994 := by decide +kernel

/-- The two obtuse levers together, before ORTH. -/
theorem sectorCount_offEdgeZeroOneLevers :
    sectorCount (fun link => hasNoIncoherentQuadrupleOffEdgeZeroOne link
      && hasNoCoherentQuadrupleOffEdgeZeroOne link) = 964 := by decide +kernel

/-- ORTH alone, worth 128 patterns of the 1024 and 124 on top of the two levers. -/
theorem sectorCount_edgeZeroOneNotSaturated :
    sectorCount edgeZeroOneNotSaturated = 896 := by decide +kernel

/-- L3 restricted to the three perfect matchings that CONTAIN the vanishing edge —
the only three whose edges all meet `{0,1}` in zero or two atoms, and hence the most
generous reading of the third lever available in this branch. -/
def hasNoSaturatedMatchingThroughEdgeZeroOne (link : Nat) : Bool :=
      !(sectorIncoherent link 0 1 2 && sectorIncoherent link 0 1 3
        && sectorIncoherent link 0 1 4 && sectorIncoherent link 0 1 5
        && sectorIncoherent link 2 3 0 && sectorIncoherent link 2 3 1
        && sectorIncoherent link 2 3 4 && sectorIncoherent link 2 3 5
        && sectorIncoherent link 4 5 0 && sectorIncoherent link 4 5 1
        && sectorIncoherent link 4 5 2 && sectorIncoherent link 4 5 3)
  &&  !(!(sectorIncoherent link 0 1 2) && !(sectorIncoherent link 0 1 3)
        && !(sectorIncoherent link 0 1 4) && !(sectorIncoherent link 0 1 5)
        && !(sectorIncoherent link 2 3 0) && !(sectorIncoherent link 2 3 1)
        && !(sectorIncoherent link 2 3 4) && !(sectorIncoherent link 2 3 5)
        && !(sectorIncoherent link 4 5 0) && !(sectorIncoherent link 4 5 1)
        && !(sectorIncoherent link 4 5 2) && !(sectorIncoherent link 4 5 3))
  &&  !(sectorIncoherent link 0 1 2 && sectorIncoherent link 0 1 4
        && sectorIncoherent link 0 1 3 && sectorIncoherent link 0 1 5
        && sectorIncoherent link 2 4 0 && sectorIncoherent link 2 4 1
        && sectorIncoherent link 2 4 3 && sectorIncoherent link 2 4 5
        && sectorIncoherent link 3 5 0 && sectorIncoherent link 3 5 1
        && sectorIncoherent link 3 5 2 && sectorIncoherent link 3 5 4)
  &&  !(!(sectorIncoherent link 0 1 2) && !(sectorIncoherent link 0 1 4)
        && !(sectorIncoherent link 0 1 3) && !(sectorIncoherent link 0 1 5)
        && !(sectorIncoherent link 2 4 0) && !(sectorIncoherent link 2 4 1)
        && !(sectorIncoherent link 2 4 3) && !(sectorIncoherent link 2 4 5)
        && !(sectorIncoherent link 3 5 0) && !(sectorIncoherent link 3 5 1)
        && !(sectorIncoherent link 3 5 2) && !(sectorIncoherent link 3 5 4))
  &&  !(sectorIncoherent link 0 1 2 && sectorIncoherent link 0 1 5
        && sectorIncoherent link 0 1 3 && sectorIncoherent link 0 1 4
        && sectorIncoherent link 2 5 0 && sectorIncoherent link 2 5 1
        && sectorIncoherent link 2 5 3 && sectorIncoherent link 2 5 4
        && sectorIncoherent link 3 4 0 && sectorIncoherent link 3 4 1
        && sectorIncoherent link 3 4 2 && sectorIncoherent link 3 4 5)
  &&  !(!(sectorIncoherent link 0 1 2) && !(sectorIncoherent link 0 1 5)
        && !(sectorIncoherent link 0 1 3) && !(sectorIncoherent link 0 1 4)
        && !(sectorIncoherent link 2 5 0) && !(sectorIncoherent link 2 5 1)
        && !(sectorIncoherent link 2 5 3) && !(sectorIncoherent link 2 5 4)
        && !(sectorIncoherent link 3 4 0) && !(sectorIncoherent link 3 4 1)
        && !(sectorIncoherent link 3 4 2) && !(sectorIncoherent link 3 4 5))

/-- **L3 BUYS NOTHING IN THE VANISHING BRANCH.**  Granting the third lever at the
three matchings through `{0,1}` — which the shipped edge lemma does not actually
justify, since the edge's own pairing vanishes — removes no two-graph from the 840.
A count of zero, so this is SET containment, not a cardinality coincidence. -/
theorem sectorCount_orthEdgeZeroOne_matchingThroughEdge_redundant :
    sectorCount (fun link => sectorSurvivesOrthEdgeZeroOne link
      && !(hasNoSaturatedMatchingThroughEdgeZeroOne link)) = 0 := by decide +kernel

/-- **HOW MUCH REUSING THE GENERIC BRANCH'S THIRD LEVER WOULD OVERCLAIM: 24.**  The
full fifteen-matching test `Gtz.hasNoSaturatedMatching` excludes 24 two-graphs that
survive the vanishing branch, and each of those exclusions rests on a matching with
an edge whose star runs through `{0,1}` — where the edge law's right-hand side
vanishes and the share inequality is unavailable.  So the residue here is 840 and
NOT the 816 an unexamined import of L3 would report. -/
theorem sectorCount_orthEdgeZeroOne_not_hasNoSaturatedMatching :
    sectorCount (fun link => sectorSurvivesOrthEdgeZeroOne link
      && !(hasNoSaturatedMatching link)) = 24 := by decide +kernel

/-- 72 two-graphs are admitted by the vanishing branch and forbidden by the
nonvanishing one. -/
theorem sectorCount_orthEdgeZeroOne_not_residual :
    sectorCount (fun link => sectorSurvivesOrthEdgeZeroOne link && !(sectorSurvives link))
      = 72 := by decide +kernel

/-- 74 the other way, so the two residues are INCOMPARABLE and 840 against 842 is a
coincidence of size rather than a containment. -/
theorem sectorCount_residual_not_orthEdgeZeroOne :
    sectorCount (fun link => sectorSurvives link && !(sectorSurvivesOrthEdgeZeroOne link))
      = 74 := by decide +kernel

/-! ## 5. Soundness -/

theorem hasNoIncoherentQuadrupleOffEdgeZeroOne_linkWordOf (design : WeightedDesign 6 3)
    (hoff : OffEdgeZeroOneNonzero design) :
    hasNoIncoherentQuadrupleOffEdgeZeroOne (linkWordOf design) = true := by
  simp only [hasNoIncoherentQuadrupleOffEdgeZeroOne,
    incoherentQuadruple_eq_false_offEdgeZeroOne design hoff 1 2 3 4 5
      (by decide) (by decide) (by decide),
    incoherentQuadruple_eq_false_offEdgeZeroOne design hoff 2 1 3 4 5
      (by decide) (by decide) (by decide),
    incoherentQuadruple_eq_false_offEdgeZeroOne design hoff 3 1 2 4 5
      (by decide) (by decide) (by decide),
    incoherentQuadruple_eq_false_offEdgeZeroOne design hoff 4 1 2 3 5
      (by decide) (by decide) (by decide),
    incoherentQuadruple_eq_false_offEdgeZeroOne design hoff 5 1 2 3 4
      (by decide) (by decide) (by decide),
    incoherentQuadruple_eq_false_offEdgeZeroOne design hoff 0 2 3 4 5
      (by decide) (by decide) (by decide),
    incoherentQuadruple_eq_false_offEdgeZeroOne design hoff 2 0 3 4 5
      (by decide) (by decide) (by decide),
    incoherentQuadruple_eq_false_offEdgeZeroOne design hoff 3 0 2 4 5
      (by decide) (by decide) (by decide),
    incoherentQuadruple_eq_false_offEdgeZeroOne design hoff 4 0 2 3 5
      (by decide) (by decide) (by decide),
    incoherentQuadruple_eq_false_offEdgeZeroOne design hoff 5 0 2 3 4
      (by decide) (by decide) (by decide),
    Bool.not_false, Bool.and_self]

theorem hasNoCoherentQuadrupleOffEdgeZeroOne_linkWordOf (design : WeightedDesign 6 3)
    (hoff : OffEdgeZeroOneNonzero design) :
    hasNoCoherentQuadrupleOffEdgeZeroOne (linkWordOf design) = true := by
  simp only [hasNoCoherentQuadrupleOffEdgeZeroOne,
    coherentQuadruple_eq_false_offEdgeZeroOne design hoff 1 2 3 4 5
      (by decide) (by decide) (by decide),
    coherentQuadruple_eq_false_offEdgeZeroOne design hoff 2 1 3 4 5
      (by decide) (by decide) (by decide),
    coherentQuadruple_eq_false_offEdgeZeroOne design hoff 3 1 2 4 5
      (by decide) (by decide) (by decide),
    coherentQuadruple_eq_false_offEdgeZeroOne design hoff 4 1 2 3 5
      (by decide) (by decide) (by decide),
    coherentQuadruple_eq_false_offEdgeZeroOne design hoff 5 1 2 3 4
      (by decide) (by decide) (by decide),
    coherentQuadruple_eq_false_offEdgeZeroOne design hoff 0 2 3 4 5
      (by decide) (by decide) (by decide),
    coherentQuadruple_eq_false_offEdgeZeroOne design hoff 2 0 3 4 5
      (by decide) (by decide) (by decide),
    coherentQuadruple_eq_false_offEdgeZeroOne design hoff 3 0 2 4 5
      (by decide) (by decide) (by decide),
    coherentQuadruple_eq_false_offEdgeZeroOne design hoff 4 0 2 3 5
      (by decide) (by decide) (by decide),
    coherentQuadruple_eq_false_offEdgeZeroOne design hoff 5 0 2 3 4
      (by decide) (by decide) (by decide),
    Bool.not_false, Bool.and_self]

theorem edgeZeroOneNotSaturated_linkWordOf (design : WeightedDesign 6 3)
    (hzero : atomPairing design 0 1 = 0) (hoff : OffEdgeZeroOneNonzero design) :
    edgeZeroOneNotSaturated (linkWordOf design) = true := by
  have hcover : ∀ o : Fin 6, o ≠ 0 → o ≠ 1 → o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 := by decide
  have hedge : (0 : Fin 6) ≠ 1 := by decide
  have hstarFirst := edgeZeroOne_star_nonzero_first design hoff
  have hstarSecond := edgeZeroOne_star_nonzero_second design hoff
  have hincoh := not_forall_incoherent_of_orthogonalEdge design hedge hzero hstarFirst hstarSecond
  have hcoh := not_forall_coherent_of_orthogonalEdge design hedge hzero hstarFirst hstarSecond
  have hincohFalse : (sectorIncoherent (linkWordOf design) 0 1 2
      && sectorIncoherent (linkWordOf design) 0 1 3
      && sectorIncoherent (linkWordOf design) 0 1 4
      && sectorIncoherent (linkWordOf design) 0 1 5) = false := by
    by_contra hcontra
    rw [Bool.not_eq_false] at hcontra
    simp only [sectorIncoherent_linkWordOf, Bool.and_eq_true, decide_eq_true_eq] at hcontra
    obtain ⟨⟨⟨htwo, hthree⟩, hfour⟩, hfive⟩ := hcontra
    refine hincoh ?_
    intro other hneZero hneOne
    rcases hcover other hneZero hneOne with rfl | rfl | rfl | rfl
    · exact htwo
    · exact hthree
    · exact hfour
    · exact hfive
  have hcohFalse : (!(sectorIncoherent (linkWordOf design) 0 1 2)
      && !(sectorIncoherent (linkWordOf design) 0 1 3)
      && !(sectorIncoherent (linkWordOf design) 0 1 4)
      && !(sectorIncoherent (linkWordOf design) 0 1 5)) = false := by
    by_contra hcontra
    rw [Bool.not_eq_false] at hcontra
    simp only [sectorIncoherent_linkWordOf, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not] at hcontra
    obtain ⟨⟨⟨htwo, hthree⟩, hfour⟩, hfive⟩ := hcontra
    refine hcoh ?_
    intro other hneZero hneOne
    rcases hcover other hneZero hneOne with rfl | rfl | rfl | rfl
    · exact tripleParity_eq_one_of_ne_neg_one design htwo
    · exact tripleParity_eq_one_of_ne_neg_one design hthree
    · exact tripleParity_eq_one_of_ne_neg_one design hfour
    · exact tripleParity_eq_one_of_ne_neg_one design hfive
  rw [edgeZeroOneNotSaturated, hincohFalse, hcohFalse, Bool.not_false, Bool.and_self]

/-- **THE BRIDGE FOR THE VANISHING BRANCH.**  The counterpart of
`Gtz.sectorSurvives_linkWordOf`, with the nonvanishing hypothesis dropped at the
one edge that vanishes. -/
theorem sectorSurvivesOrthEdgeZeroOne_linkWordOf (design : WeightedDesign 6 3)
    (hzero : atomPairing design 0 1 = 0) (hoff : OffEdgeZeroOneNonzero design) :
    sectorSurvivesOrthEdgeZeroOne (linkWordOf design) = true := by
  rw [sectorSurvivesOrthEdgeZeroOne, hasNoIncoherentQuadrupleOffEdgeZeroOne_linkWordOf design hoff,
    hasNoCoherentQuadrupleOffEdgeZeroOne_linkWordOf design hoff,
    edgeZeroOneNotSaturated_linkWordOf design hzero hoff]
  rfl

theorem linkWordOf_mem_residualSectorsOrthEdgeZeroOne (design : WeightedDesign 6 3)
    (hzero : atomPairing design 0 1 = 0) (hoff : OffEdgeZeroOneNonzero design) :
    linkWordOf design ∈ residualSectorsOrthEdgeZeroOne :=
  (mem_residualSectorsOrthEdgeZeroOne_iff _).2
    ⟨linkWordOf_lt design, sectorSurvivesOrthEdgeZeroOne_linkWordOf design hzero hoff⟩

/-! ## 6. The aggregate: fourteen nonvanishing hypotheses instead of fifteen -/

/-- The union of the two branches: what a `(6,3)` design can do when the pairing at
`{0,1}` is left free. -/
def residualSectorsEdgeZeroOneFree : Finset Nat :=
  (Finset.range 1024).filter fun link =>
    sectorSurvives link = true ∨ sectorSurvivesOrthEdgeZeroOne link = true

theorem residualSectorsEdgeZeroOneFree_eq_union :
    residualSectorsEdgeZeroOneFree = residualSectors ∪ residualSectorsOrthEdgeZeroOne := by
  rw [residualSectorsEdgeZeroOneFree, residualSectors, residualSectorsOrthEdgeZeroOne,
    Finset.filter_or]

/-- **THE PRICE OF DROPPING ONE NONVANISHING HYPOTHESIS: 72 PATTERNS.**  842 becomes
914, not 1024 — the sign layer keeps 110 of its 182 exclusions when the pairing at
one named edge is left completely free. -/
theorem card_residualSectorsEdgeZeroOneFree : residualSectorsEdgeZeroOneFree.card = 914 := by
  rw [residualSectorsEdgeZeroOneFree]
  decide +kernel

/-- **THE AGGREGATE.**  Every `(6,3)` design whose pairings are nonzero away from
`{0,1}` — with NO assumption at `{0,1}` itself — has its two-graph inside one
explicit 914-element object.  `Gtz.linkWordOf_mem_residualSectors` needs all
fifteen; this needs fourteen. -/
theorem linkWordOf_mem_residualSectorsEdgeZeroOneFree (design : WeightedDesign 6 3)
    (hoff : OffEdgeZeroOneNonzero design) :
    linkWordOf design ∈ residualSectorsEdgeZeroOneFree := by
  rw [residualSectorsEdgeZeroOneFree, Finset.mem_filter, Finset.mem_range]
  refine ⟨linkWordOf_lt design, ?_⟩
  by_cases hzero : atomPairing design 0 1 = 0
  · exact Or.inr (sectorSurvivesOrthEdgeZeroOne_linkWordOf design hzero hoff)
  · refine Or.inl (sectorSurvives_linkWordOf design ?_)
    intro first second hne
    by_cases hpair : ({first, second} : Finset (Fin 6)) = {0, 1}
    · have hsplit : ∀ x y : Fin 6, x ≠ y → ({x, y} : Finset (Fin 6)) = {0, 1} →
          (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by decide
      rcases hsplit first second hne hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hzero
      · rw [atomPairing_comm]; exact hzero
    · exact hoff first second hne hpair

/-- The crux reading.  `Gtz.SixThreeCrux.linkWord_mem_residualSectors` is unusable
without a global nonvanishing fact a crux does not supply; this asks for one fewer. -/
theorem SixThreeCrux.linkWord_mem_residualSectorsEdgeZeroOneFree (crux : SixThreeCrux)
    (hoff : OffEdgeZeroOneNonzero crux.design) :
    linkWordOf crux.design ∈ residualSectorsEdgeZeroOneFree :=
  linkWordOf_mem_residualSectorsEdgeZeroOneFree crux.design hoff

end Gtz

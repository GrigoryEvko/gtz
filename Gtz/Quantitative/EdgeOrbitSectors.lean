/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Quantitative.OrthogonalEdgeSectors

/-!
# The vanishing pairing at an UNKNOWN edge

`Gtz/Quantitative/OrthogonalEdgeSectors.lean` proves the sign layer's
vanishing branch at the NAMED edge `{0, 1}`, and its header says exactly what is
missing and exactly why nobody should brute-force it:

> The edge is NAMED, and the strength of the branch depends on that.  Nothing here
> quantifies over WHICH pairing vanishes, and a successor should not spend the
> fourteen further clause sets it would take to do so. [...] Proving edge-independence
> inside Lean rather than measuring it needs an ingredient the tree does not have: an
> action of `Equiv.Perm (Fin 6)` on `Gtz.WeightedDesign 6 3` together with the transport
> of `Gtz.tripleParity` along it.

Both halves of that are settled here, and neither costs a clause set — but the two
halves have different standing, and separating them matters.

The ACTION half was already false when written.  `Gtz.relabelDesign` is in the TRACKED
`Gtz/Ties/SelectionObstruction.lean`, with `Gtz.subsetSum_relabelDesign` and
`Gtz.dominates_relabelDesign_iff`, and `Gtz/Design/PrimitiveTightClassification.lean`
already transports `Gtz.atomBracket`, `Gtz.IsTie` and `Gtz.HasLinePattern` along it; the
companion claim that `Equiv.Perm` "appears in `Gtz/Design/LinePatternEnumeration.lean`
only as an abstract relabelling of PATTERNS, never as an action on designs" looked in
the pattern module and missed the design action one directory away.

The TRANSPORT half was accurate, and it is what is supplied here.  It is three `rfl`s:
`Gtz.atomPairing`, `Gtz.edgeSign` and `Gtz.tripleParity` are each defined from the one
below it by a formula that never mentions an index, so permuting the atoms permutes
them verbatim.

## THE ORBIT FORM

`Gtz.exists_relabel_linkWord_mem_residualSectorsOrthEdgeZeroOne` is the headline: a
design whose pairings are nonzero away from ONE edge, wherever that edge is, can be
relabelled so that its two-graph lands in the SAME 840-element object the named-edge
branch produces.  The relabelling is explicit — `Gtz.pairPerm`, two transpositions —
and the statement returns it, so a consumer knows which one.

This is strictly stronger than forgetting the edge.  A design with one vanishing
pairing at an unknown place has 184 two-graphs forbidden to it in the relabelled
frame, and only 32 forbidden in its own frame; that is the whole content of the
named-edge branch's warning that "the information is in knowing WHERE the pairing
vanishes".  Relabelling does not forget where — it moves the label.

## THE EDGE-FORGETTING FORM, FOR CONSUMERS WHO CANNOT RELABEL

`Gtz.unionEdgeBranchSectors` is the other side of that trade, and it needs the
abstract action.  `Gtz.relabelLinkWord` moves a two-graph rather than a design, and
`Gtz.linkWordOf_relabelDesign` says the two agree; the union of the fifteen edge
branches with the generic branch is then a computable 992-element object, and
`Gtz.linkWordOf_mem_unionEdgeBranchSectors` places every design with at most one
vanishing pairing inside it WITH NO RELABELLING IN THE CONCLUSION.

`Gtz.card_unionEdgeBranchSectors` is `decide +kernel` on the 1024 two-graphs.  It
mechanizes the measured "their UNION is 992 of 1024" of the named-edge header, and
the same header's "the union also swallows `Gtz.residualSectors` whole: 992 again
with the generic branch thrown in" — the definition here includes the generic branch
and still counts 992, so both measurements hold at once.

## WHAT IS NOT HERE

The per-edge CARDINALITIES are not landed.  `Gtz.card_edgeBranchSectors_zero_two` and
`Gtz.card_edgeBranchSectors_two_three` confirm the measured 840 at one edge sharing an
atom with `{0, 1}` and one edge disjoint from it — the two shapes the relabelling can
take — and `Gtz.edgeBranchSectors_zero_one` identifies the third, degenerate shape with
the shipped set outright.  The uniform statement over all thirty ordered edges was
built and MEASURED at over two minutes of kernel time in this rung's scratch; it was
dropped rather than charged to every future build, because the mathematically
load-bearing half is the orbit form above and that half needs no `decide` at all.

Nothing here approaches `IsEmpty Gtz.SixThreeCrux`.  The residue does not empty — 992
is larger than the 842 of the nonvanishing branch, not smaller — and a residue that
does not empty is a residue no sign-only argument cuts.  What the orbit form removes is
the FIFTEEN-FOLD case split, not the residue.
-/

namespace Gtz

/-! ## 1. The sign layer transports along the relabelling action

`Gtz.relabelDesign` reindexes atoms and weights together.  `Gtz.atomPairing` is a dot
product of two atoms, `Gtz.edgeSign` its sign and `Gtz.tripleParity` a product of three
edge signs, so each is carried along by definitional unfolding alone. -/

/-- Pairings transport: relabelling an atom index relabels the pairing. -/
theorem atomPairing_relabelDesign {size : ℕ} (design : WeightedDesign size 3)
    (relabel : Equiv.Perm (Fin size)) (atomFirst atomSecond : Fin size) :
    atomPairing (relabelDesign design relabel) atomFirst atomSecond
      = atomPairing design (relabel atomFirst) (relabel atomSecond) := rfl

/-- Edge signs transport. -/
theorem edgeSign_relabelDesign {size : ℕ} (design : WeightedDesign size 3)
    (relabel : Equiv.Perm (Fin size)) (atomFirst atomSecond : Fin size) :
    edgeSign (relabelDesign design relabel) atomFirst atomSecond
      = edgeSign design (relabel atomFirst) (relabel atomSecond) := rfl

/-- **THE TRANSPORT THE NAMED-EDGE BRANCH ASKED FOR.**  Triple parities transport. -/
theorem tripleParity_relabelDesign {size : ℕ} (design : WeightedDesign size 3)
    (relabel : Equiv.Perm (Fin size)) (first second third : Fin size) :
    tripleParity (relabelDesign design relabel) first second third
      = tripleParity design (relabel first) (relabel second) (relabel third) := rfl

/-- Leverages transport, at every rank. -/
theorem leverageOf_relabelDesign {size rank : ℕ} (design : WeightedDesign size rank)
    (relabel : Equiv.Perm (Fin size)) (atomIndex : Fin size) :
    leverageOf ((relabelDesign design relabel).atom atomIndex)
      = leverageOf (design.atom (relabel atomIndex)) := rfl

/-- Shares transport, at every rank. -/
theorem atomShare_relabelDesign {size rank : ℕ} (design : WeightedDesign size rank)
    (relabel : Equiv.Perm (Fin size)) (atomIndex : Fin size) :
    atomShare (relabelDesign design relabel) atomIndex
      = atomShare design (relabel atomIndex) := rfl

/-- All-heaviness is a relabelling invariant.  A consumer of the orbit form below
receives a RELABELLED design, and this is what says the crux field
`Gtz.SixThreeCrux.isAllHeavy` survives the move. -/
theorem allHeavy_relabelDesign_iff {size rank : ℕ} (design : WeightedDesign size rank)
    (relabel : Equiv.Perm (Fin size)) :
    AllHeavy (relabelDesign design relabel) ↔ AllHeavy design := by
  constructor
  · intro hheavy atomIndex
    have hshifted := hheavy (relabel.symm atomIndex)
    rwa [leverageOf_relabelDesign, Equiv.apply_symm_apply] at hshifted
  · intro hheavy atomIndex
    rw [leverageOf_relabelDesign]
    exact hheavy (relabel atomIndex)

/-- The sector decode of a relabelled design is the decode of the original at the
relabelled triple.  This rides `Gtz.sectorIncoherent_linkWordOf`, which is the
hypothesis-free dictionary between the Boolean layer and `Gtz.tripleParity`. -/
theorem sectorIncoherent_linkWordOf_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6)) (first second third : Fin 6) :
    sectorIncoherent (linkWordOf (relabelDesign design relabel)) first second third
      = sectorIncoherent (linkWordOf design)
          (relabel first) (relabel second) (relabel third) := by
  rw [sectorIncoherent_linkWordOf, sectorIncoherent_linkWordOf, tripleParity_relabelDesign]

/-! ## 2. Two-point transitivity, with an explicit witness

Everything below needs one permutation carrying the ordered pair `(0, 1)` onto the
free edge.  Two transpositions do it, and naming the witness lets the orbit-form
statements return it. -/

/-- The permutation carrying `0` to `targetFirst` and `1` to `targetSecond`. -/
def pairPerm (targetFirst targetSecond : Fin 6) : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 targetFirst * Equiv.swap 1 (Equiv.swap 0 targetFirst targetSecond)

theorem pairPerm_apply_one (targetFirst targetSecond : Fin 6) :
    pairPerm targetFirst targetSecond 1 = targetSecond := by
  rw [pairPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

theorem pairPerm_apply_zero {targetFirst targetSecond : Fin 6}
    (htarget : targetFirst ≠ targetSecond) :
    pairPerm targetFirst targetSecond 0 = targetFirst := by
  have hfix : (0 : Fin 6) ≠ Equiv.swap 0 targetFirst targetSecond := by
    by_cases hcase : targetSecond = (0 : Fin 6)
    · subst hcase
      rw [Equiv.swap_apply_left]
      exact fun hzero => htarget hzero.symm
    · rw [Equiv.swap_apply_of_ne_of_ne hcase (fun hto => htarget hto.symm)]
      exact fun hzero => hcase hzero.symm
  rw [pairPerm, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (by decide) hfix, Equiv.swap_apply_left]

/-- **TWO-POINT TRANSITIVITY.**  Every ordered pair of distinct atoms is the image of
`(0, 1)` under a relabelling. -/
theorem exists_pairPerm {targetFirst targetSecond : Fin 6}
    (htarget : targetFirst ≠ targetSecond) :
    ∃ relabel : Equiv.Perm (Fin 6), relabel 0 = targetFirst ∧ relabel 1 = targetSecond :=
  ⟨pairPerm targetFirst targetSecond, pairPerm_apply_zero htarget,
    pairPerm_apply_one targetFirst targetSecond⟩

/-! ## 3. Unordered pairs under a relabelling

The named-edge hypothesis is written on the unordered pair, so the transport needs
that a relabelling acts injectively on pairs. -/

theorem map_relabel_pair {size : ℕ} (relabel : Equiv.Perm (Fin size)) (first second : Fin size) :
    ({first, second} : Finset (Fin size)).map relabel.toEmbedding
      = {relabel first, relabel second} := by
  simp

theorem relabel_pair_eq_iff {size : ℕ} (relabel : Equiv.Perm (Fin size))
    (first second third fourth : Fin size) :
    ({relabel first, relabel second} : Finset (Fin size)) = {relabel third, relabel fourth}
      ↔ ({first, second} : Finset (Fin size)) = {third, fourth} := by
  rw [← map_relabel_pair, ← map_relabel_pair]
  exact ⟨fun hmapped => Finset.map_injective _ hmapped, fun hbase => by rw [hbase]⟩

/-- Two distinct atoms spanning a named pair are that pair in one of its two orders. -/
theorem pair_eq_pair_cases {size : ℕ} {first second edgeFirst edgeSecond : Fin size}
    (hne : first ≠ second)
    (heq : ({first, second} : Finset (Fin size)) = {edgeFirst, edgeSecond}) :
    (first = edgeFirst ∧ second = edgeSecond) ∨ (first = edgeSecond ∧ second = edgeFirst) := by
  have hfirst : first ∈ ({edgeFirst, edgeSecond} : Finset (Fin size)) := by
    rw [← heq]; simp
  have hsecond : second ∈ ({edgeFirst, edgeSecond} : Finset (Fin size)) := by
    rw [← heq]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  rcases hfirst with hfirstLeft | hfirstRight
  · rcases hsecond with hsecondLeft | hsecondRight
    · exact absurd (hfirstLeft.trans hsecondLeft.symm) hne
    · exact Or.inl ⟨hfirstLeft, hsecondRight⟩
  · rcases hsecond with hsecondLeft | hsecondRight
    · exact Or.inr ⟨hfirstRight, hsecondLeft⟩
    · exact absurd (hfirstRight.trans hsecondRight.symm) hne

/-! ## 4. The hypothesis at an arbitrary edge -/

/-- Every pairing except possibly the one at `{edgeFirst, edgeSecond}` is nonzero.  The
named-edge `Gtz.OffEdgeZeroOneNonzero` is the instance at `{0, 1}`. -/
def OffEdgeNonzero (design : WeightedDesign 6 3) (edgeFirst edgeSecond : Fin 6) : Prop :=
  ∀ first second : Fin 6, first ≠ second →
    ({first, second} : Finset (Fin 6)) ≠ {edgeFirst, edgeSecond} →
      atomPairing design first second ≠ 0

theorem offEdgeNonzero_zero_one_iff (design : WeightedDesign 6 3) :
    OffEdgeNonzero design 0 1 ↔ OffEdgeZeroOneNonzero design := Iff.rfl

theorem offEdgeNonzero_of_forall_nonzero (design : WeightedDesign 6 3)
    (edgeFirst edgeSecond : Fin 6)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0) :
    OffEdgeNonzero design edgeFirst edgeSecond :=
  fun first second hne _ => hnonzero first second hne

/-- **THE TRANSPORT OF THE HYPOTHESIS.**  A relabelling carrying `(0, 1)` onto the free
edge turns the arbitrary-edge hypothesis into the shipped named-edge one. -/
theorem offEdgeZeroOneNonzero_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6))
    (hoff : OffEdgeNonzero design (relabel 0) (relabel 1)) :
    OffEdgeZeroOneNonzero (relabelDesign design relabel) := by
  intro first second hne hpair
  rw [atomPairing_relabelDesign]
  refine hoff (relabel first) (relabel second) (fun heq => hne (relabel.injective heq)) ?_
  intro hmapped
  exact hpair ((relabel_pair_eq_iff relabel first second 0 1).1 hmapped)

theorem atomPairing_relabelDesign_pairPerm {design : WeightedDesign 6 3}
    {edgeFirst edgeSecond : Fin 6} (hne : edgeFirst ≠ edgeSecond) :
    atomPairing (relabelDesign design (pairPerm edgeFirst edgeSecond)) 0 1
      = atomPairing design edgeFirst edgeSecond := by
  rw [atomPairing_relabelDesign, pairPerm_apply_zero hne, pairPerm_apply_one]

theorem offEdgeZeroOneNonzero_relabelDesign_pairPerm {design : WeightedDesign 6 3}
    {edgeFirst edgeSecond : Fin 6} (hne : edgeFirst ≠ edgeSecond)
    (hoff : OffEdgeNonzero design edgeFirst edgeSecond) :
    OffEdgeZeroOneNonzero (relabelDesign design (pairPerm edgeFirst edgeSecond)) := by
  refine offEdgeZeroOneNonzero_relabelDesign design _ ?_
  rw [pairPerm_apply_zero hne, pairPerm_apply_one]
  exact hoff

/-! ## 5. The orbit form -/

/-- **THE HEADLINE.**  One vanishing pairing, at an UNKNOWN edge, still lands in the
canonical 840-element object — after an explicit relabelling that the statement
returns.  `Gtz.linkWordOf_mem_residualSectorsOrthEdgeZeroOne` is the `{0, 1}` case, and
no other case is computed: the relabelling reduces all fifteen to that one. -/
theorem exists_relabel_linkWord_mem_residualSectorsOrthEdgeZeroOne (design : WeightedDesign 6 3)
    {edgeFirst edgeSecond : Fin 6} (hne : edgeFirst ≠ edgeSecond)
    (hzero : atomPairing design edgeFirst edgeSecond = 0)
    (hoff : OffEdgeNonzero design edgeFirst edgeSecond) :
    ∃ relabel : Equiv.Perm (Fin 6), relabel 0 = edgeFirst ∧ relabel 1 = edgeSecond ∧
      linkWordOf (relabelDesign design relabel) ∈ residualSectorsOrthEdgeZeroOne :=
  ⟨pairPerm edgeFirst edgeSecond, pairPerm_apply_zero hne, pairPerm_apply_one _ _,
    linkWordOf_mem_residualSectorsOrthEdgeZeroOne _
      ((atomPairing_relabelDesign_pairPerm hne).trans hzero)
      (offEdgeZeroOneNonzero_relabelDesign_pairPerm hne hoff)⟩

/-- At most one pairing vanishes, at an unspecified edge.  Implied by full
nonvanishing, and implied by exactly one vanishing pairing. -/
def HasAtMostOneVanishingPairing (design : WeightedDesign 6 3) : Prop :=
  ∃ edgeFirst edgeSecond : Fin 6, edgeFirst ≠ edgeSecond ∧ OffEdgeNonzero design edgeFirst edgeSecond

theorem hasAtMostOneVanishingPairing_of_forall_nonzero (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0) :
    HasAtMostOneVanishingPairing design :=
  ⟨0, 1, by decide, offEdgeNonzero_of_forall_nonzero design 0 1 hnonzero⟩

/-- **THE AGGREGATE, IN ORBIT FORM.**  Fourteen nonvanishing hypotheses at an unknown
edge, and no hypothesis at all about the fifteenth. -/
theorem exists_relabel_linkWord_mem_residualSectorsEdgeZeroOneFree (design : WeightedDesign 6 3)
    (hatMostOne : HasAtMostOneVanishingPairing design) :
    ∃ relabel : Equiv.Perm (Fin 6),
      linkWordOf (relabelDesign design relabel) ∈ residualSectorsEdgeZeroOneFree := by
  obtain ⟨edgeFirst, edgeSecond, hne, hoff⟩ := hatMostOne
  exact ⟨pairPerm edgeFirst edgeSecond,
    linkWordOf_mem_residualSectorsEdgeZeroOneFree _
      (offEdgeZeroOneNonzero_relabelDesign_pairPerm hne hoff)⟩

/-- The crux reading.  `Gtz.SixThreeCrux.linkWord_mem_residualSectorsEdgeZeroOneFree`
needs the free edge to be `{0, 1}`; a crux supplies no such labelling. -/
theorem SixThreeCrux.exists_relabel_linkWord_mem_residualSectorsEdgeZeroOneFree
    (crux : SixThreeCrux) (hatMostOne : HasAtMostOneVanishingPairing crux.design) :
    ∃ relabel : Equiv.Perm (Fin 6),
      linkWordOf (relabelDesign crux.design relabel) ∈ residualSectorsEdgeZeroOneFree :=
  Gtz.exists_relabel_linkWord_mem_residualSectorsEdgeZeroOneFree crux.design hatMostOne

/-! ## 6. The induced action on two-graphs

The design action moves designs; the edge-forgetting statement needs the two-graph it
induces.  `Gtz.relabelLinkWord` reads the ten triples through atom `0` at the relabelled
atoms, and `Gtz.linkWordOf_relabelDesign` says that is exactly the two-graph of the
relabelled design. -/

/-- The relabelling action on two-graphs. -/
def relabelLinkWord (relabel : Equiv.Perm (Fin 6)) (link : Nat) : Nat :=
  packTenBits
    (sectorIncoherent link (relabel 0) (relabel 1) (relabel 2))
    (sectorIncoherent link (relabel 0) (relabel 1) (relabel 3))
    (sectorIncoherent link (relabel 0) (relabel 1) (relabel 4))
    (sectorIncoherent link (relabel 0) (relabel 1) (relabel 5))
    (sectorIncoherent link (relabel 0) (relabel 2) (relabel 3))
    (sectorIncoherent link (relabel 0) (relabel 2) (relabel 4))
    (sectorIncoherent link (relabel 0) (relabel 2) (relabel 5))
    (sectorIncoherent link (relabel 0) (relabel 3) (relabel 4))
    (sectorIncoherent link (relabel 0) (relabel 3) (relabel 5))
    (sectorIncoherent link (relabel 0) (relabel 4) (relabel 5))

/-- **THE TWO ACTIONS AGREE.**  Relabelling a design and then reading its two-graph is
relabelling its two-graph. -/
theorem linkWordOf_relabelDesign (design : WeightedDesign 6 3) (relabel : Equiv.Perm (Fin 6)) :
    linkWordOf (relabelDesign design relabel)
      = relabelLinkWord relabel (linkWordOf design) := by
  rw [relabelLinkWord]
  simp only [sectorIncoherent_linkWordOf]
  rfl

/-- A SELF-TEST of the encoding: at the edge `{0, 1}` the relabelling is the identity,
so the action is too.  `Gtz.pairPerm 0 1` is a product of two trivial transpositions. -/
theorem relabelLinkWord_pairPerm_zero_one :
    ∀ link < 1024, relabelLinkWord (pairPerm 0 1) link = link := by
  decide +kernel

/-! ## 7. The fifteen branches and their union -/

/-- The vanishing branch at the edge `{edgeFirst, edgeSecond}`, as the pullback of the
canonical branch along the action. -/
def edgeBranchSectors (edgeFirst edgeSecond : Fin 6) : Finset Nat :=
  (Finset.range 1024).filter fun link =>
    sectorSurvivesOrthEdgeZeroOne (relabelLinkWord (pairPerm edgeFirst edgeSecond) link) = true

/-- The branch at the canonical edge IS the shipped set. -/
theorem edgeBranchSectors_zero_one : edgeBranchSectors 0 1 = residualSectorsOrthEdgeZeroOne := by
  ext link
  rw [edgeBranchSectors, Finset.mem_filter, Finset.mem_range,
    mem_residualSectorsOrthEdgeZeroOne_iff]
  constructor
  · rintro ⟨hlt, hsurvives⟩
    exact ⟨hlt, by rwa [relabelLinkWord_pairPerm_zero_one link hlt] at hsurvives⟩
  · rintro ⟨hlt, hsurvives⟩
    exact ⟨hlt, by rwa [relabelLinkWord_pairPerm_zero_one link hlt]⟩

/-- The measured 840 at an edge SHARING an atom with the canonical one. -/
theorem card_edgeBranchSectors_zero_two : (edgeBranchSectors 0 2).card = 840 := by
  rw [edgeBranchSectors]
  decide +kernel

/-- The measured 840 at an edge DISJOINT from the canonical one. -/
theorem card_edgeBranchSectors_two_three : (edgeBranchSectors 2 3).card = 840 := by
  rw [edgeBranchSectors]
  decide +kernel

/-- A design lies in the branch at its own free edge, with no relabelling in the
conclusion. -/
theorem linkWordOf_mem_edgeBranchSectors (design : WeightedDesign 6 3)
    {edgeFirst edgeSecond : Fin 6} (hne : edgeFirst ≠ edgeSecond)
    (hzero : atomPairing design edgeFirst edgeSecond = 0)
    (hoff : OffEdgeNonzero design edgeFirst edgeSecond) :
    linkWordOf design ∈ edgeBranchSectors edgeFirst edgeSecond := by
  rw [edgeBranchSectors, Finset.mem_filter, Finset.mem_range]
  refine ⟨linkWordOf_lt design, ?_⟩
  rw [← linkWordOf_relabelDesign]
  exact sectorSurvivesOrthEdgeZeroOne_linkWordOf _
    ((atomPairing_relabelDesign_pairPerm hne).trans hzero)
    (offEdgeZeroOneNonzero_relabelDesign_pairPerm hne hoff)

/-- The fifteen branches together with the generic branch. -/
def unionEdgeBranchSectors : Finset Nat :=
  (Finset.range 1024).filter fun link =>
    sectorSurvives link = true ∨
      ∃ edgeFirst : Fin 6, ∃ edgeSecond : Fin 6, edgeFirst ≠ edgeSecond ∧
        sectorSurvivesOrthEdgeZeroOne (relabelLinkWord (pairPerm edgeFirst edgeSecond) link) = true

/-- **THE PRICE OF FORGETTING THE EDGE: 152 OF THE 184 EXCLUSIONS.**  The named-edge
branch keeps 840 of 1024; the orbit form keeps that number in the relabelled frame; the
edge-forgetting union keeps 992. -/
theorem card_unionEdgeBranchSectors : unionEdgeBranchSectors.card = 992 := by
  rw [unionEdgeBranchSectors]
  decide +kernel

/-- **THE UNCONDITIONAL EDGE-FORGETTING FORM.**  At most one vanishing pairing, at an
unknown edge, and NO relabelling in the conclusion. -/
theorem linkWordOf_mem_unionEdgeBranchSectors (design : WeightedDesign 6 3)
    (hatMostOne : HasAtMostOneVanishingPairing design) :
    linkWordOf design ∈ unionEdgeBranchSectors := by
  obtain ⟨edgeFirst, edgeSecond, hne, hoff⟩ := hatMostOne
  rw [unionEdgeBranchSectors, Finset.mem_filter, Finset.mem_range]
  refine ⟨linkWordOf_lt design, ?_⟩
  by_cases hzero : atomPairing design edgeFirst edgeSecond = 0
  · refine Or.inr ⟨edgeFirst, edgeSecond, hne, ?_⟩
    rw [← linkWordOf_relabelDesign]
    exact sectorSurvivesOrthEdgeZeroOne_linkWordOf _
      ((atomPairing_relabelDesign_pairPerm hne).trans hzero)
      (offEdgeZeroOneNonzero_relabelDesign_pairPerm hne hoff)
  · refine Or.inl (sectorSurvives_linkWordOf design ?_)
    intro first second hnePair
    by_cases hpair : ({first, second} : Finset (Fin 6)) = {edgeFirst, edgeSecond}
    · rcases pair_eq_pair_cases hnePair hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hzero
      · rw [atomPairing_comm]; exact hzero
    · exact hoff first second hnePair hpair

/-- The crux reading of the edge-forgetting form. -/
theorem SixThreeCrux.linkWord_mem_unionEdgeBranchSectors (crux : SixThreeCrux)
    (hatMostOne : HasAtMostOneVanishingPairing crux.design) :
    linkWordOf crux.design ∈ unionEdgeBranchSectors :=
  linkWordOf_mem_unionEdgeBranchSectors crux.design hatMostOne

/-! ## 8. Non-vacuity

The hypothesis of every statement above is inhabited by a shipped design.  This is
worth checking rather than assuming: a hypothesis quantifying over an unknown edge
could in principle be satisfiable at no design at all. -/

/-- `Gtz.icosaDesign` has all fifteen pairings nonzero — its squared pairings are all
`9 / 5` — hence at most one vanishing. -/
theorem hasAtMostOneVanishingPairing_icosaDesign :
    HasAtMostOneVanishingPairing icosaDesign := by
  refine hasAtMostOneVanishingPairing_of_forall_nonzero icosaDesign ?_
  intro first second hne hzero
  have hsquare := icosaDesign_atomPairing_sq_of_ne hne
  rw [hzero] at hsquare
  norm_num at hsquare

/-- The edge-forgetting form at a concrete design. -/
theorem linkWordOf_icosaDesign_mem_unionEdgeBranchSectors :
    linkWordOf icosaDesign ∈ unionEdgeBranchSectors :=
  linkWordOf_mem_unionEdgeBranchSectors icosaDesign hasAtMostOneVanishingPairing_icosaDesign

end Gtz

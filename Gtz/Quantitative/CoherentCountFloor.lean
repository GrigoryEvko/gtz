/-
# The sharp coherent count: a NUMBER for the two-graph at a base atom

`Gtz/Quantitative/SwitchingTwoGraph.lean` records, as a wall rather than an
omission, that its section 8 "does not produce a NUMBER -- no lower bound on how
many of the `20` triples at `m = 6`, or the `35` at `m = 7`, must be coherent",
and names two declined routes. This file executes route (i) and lands the number.

## The identity that makes it mechanical

Switching at a base atom by the shipped gauge `Gtz.switchSign` turns the
two-graph AT the base into the ordinary sign pattern of the switched design:

  `Gtz.edgeSign_baseSwitchedDesign :`
  `  edgeSign (baseSwitchedDesign D base) first second = tripleParity D base first second`

After switching, the sign of an off-base edge IS the parity of its triangle
through the base, so the coherence-through-`base` graph is DEFINITIONALLY the
positive-edge graph of `Gtz.baseSwitchedDesign D base`. The companion
`Gtz.edgeSign_baseSwitchedDesign_base` says every base edge switches to `-1`.
The identity needs no hypothesis on the base pairings at all -- the gauge
`Gtz.switchSign` is `-Gtz.edgeSign` on the nose
(`Gtz.switchSign_eq_neg_edgeSign`), including where the pairing vanishes and the
convention `sign 0 = +1` is in force. Only the OFF-BASE edge has to be nonzero,
because that is where `Gtz.edgeSign_switchedDesign` pays for the convention.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

**The four-set axiom, solved (section 1).**
`Gtz.tripleParity_eq_product_through_base`: the parity of ANY triangle is the
product of the three parities joining it to ANY base atom. The shipped
`Gtz.tripleParity_fourSet_product` states the same content as a product equal to
one; this is the form a consumer reads -- the whole two-graph is determined by its
star at a single vertex -- and it is hypothesis-free exactly as the shipped form is.

**The cap (section 3).** `Gtz.card_le_three_of_forall_incoherent_through_base`:
a base-avoiding family all of whose triangles through the base are incoherent has
at most THREE members. Via the identity, such a family is pairwise negative in
the switched design and negative against the base too, so
`Gtz.card_le_succ_of_isPairwiseObtuse_on` at `coord = Fin 3` caps
`{base} u family` at `3 + 1 = 4`. Sharp: the four tetrahedron vertices have every
triangle incoherent. The nonvanishing hypotheses are LOCAL -- the base edges to
the family and the edges inside it -- so the cap survives a design with
orthogonal pairs elsewhere.

**Greedy independence (section 2).** `Gtz.exists_independent_of_edges`, stated
for a bare `Finset` of ordered pairs with no graph structure and no symmetry
hypothesis: deleting one endpoint of one edge at a time leaves an edge-free
subset missing at most one vertex per edge. This is "a graph on `n` vertices with
`e` edges has an independent set of size at least `n - e`" in the only form the
count needs.

**The count (section 4).** `Gtz.coherentPairsThroughBase` is the `Finset` of
coherent triangles through a base, canonically oriented, and
`Gtz.card_coherentPairsThroughBase_ge_of_family` bounds its cardinality below by
`family.card - 3` for EVERY base-avoiding family with the local nonvanishing.
Taking the family to be everything gives `Gtz.card_coherentPairsThroughBase_ge`:

  `m - 4 <= (coherentPairsThroughBase D base).card`

-- `2` at `m = 6` and `3` at `m = 7`. The family form is the one that degrades
gracefully: dropping the atoms an orthogonality touches costs one coherent
triangle apiece rather than the whole count, which is
`Gtz.card_coherentPairsThroughBase_ge_of_erase` at `m - 5`.

**The global count (section 8).** Flags -- a base together with a coherent pair
through it -- fibre three-to-one over the coherent triangles, one flag per vertex,
so `Gtz.card_coherentTripleSets_ge` divides the summed per-base count:

  `m (m - 4) <= 3 * (coherentTripleSets D).card`

-- at least FOUR of the twenty triangles at `m = 6`
(`Gtz.four_le_card_coherentTripleSets_sixThree`) and SEVEN of the thirty-five at
`m = 7`. Determinacy of the fibre is the ordered-pair step
`Gtz.orderedPair_eq_of_pairFinset_eq`: the two non-base atoms of a flag are its
triangle with the base erased, written in increasing order.

**At a crux (sections 5-6).** Composing with the substrate's X0 squeeze:
`Gtz.SixThreeCrux.two_le_card_coherentPairsThroughBase_and_forall_negative` --
through every atom of a `(6,3)` crux whose pairings are all nonzero there are at
least TWO coherent triangles, and every one of them has a STRICTLY POSITIVE
oriented pairing product, a STRICTLY NEGATIVE sign-blind gap, and therefore a tie
leg strictly below twice that product. The `(7,3)` sibling is section 7, at three
triangles per atom.

**The vanishing-pairing branch (section 6), with content rather than a caveat.**
`Gtz.SixThreeCrux.pairMinor_neg_of_common_orthogonalPartner`: at a crux, an atom
orthogonal to TWO others forces those two to span an INCOMPATIBLE edge,
`pairMinor < 0`. The mechanism is that `excessGap` collapses to
`heavyExcess base * pairMinor` when two of its three pairings vanish, and the
squeeze makes it negative. So an orthogonality is not a hole in the argument: it
is edge-level structure of exactly the kind the two-graph collision consumes.
`Gtz.SixThreeCrux.two_le_card_coherentPairsThroughBase_or_exists_orthogonalPair`
states the resulting dichotomy with no hypothesis at all.

## NOT proved here

* The count says nothing about WHICH atoms the coherent triangles join, and the
  GLOBAL count of section 8 says nothing about their distribution. Neither is a
  covering statement, and neither produces a dominating triple.
* The count says nothing about WHICH two-graph a crux carries. The recorded
  enumeration of the sixteen isomorphism classes at six points has eight
  surviving every purely combinatorial constraint, with the icosahedral class
  sitting at five coherent triangles per vertex -- comfortably inside the band
  `[2, 8]` this file's bound and its dual would give. NOTHING here narrows that.
* Nothing here produces a dominating triple, bounds a pairing magnitude, or
  touches the chart. The count is a constraint on the sign pattern alone.
* The cap `3` is sharp and so is the count: the tetrahedron realises the cap, so
  `m - 4` cannot be raised by this route at any size.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.SixThreeCrux
import Gtz.Quantitative.SixThreeCruxSigns
import Gtz.Quantitative.SwitchingTwoGraph
import Gtz.LinAlg.SignForcing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The base gauge and the switching identity

`Gtz.switchSign` is the shipped vector-level gauge; read at the design level it is
exactly the negated edge sign, and that one line is what turns the two-graph at a
base into an ordinary sign pattern. -/

/-- The edge sign is `-1` exactly on a strictly negative pairing. The `+1` side is
the convention `sign 0 = +1`, so this is the only faithful reading of the sign. -/
theorem edgeSign_eq_neg_one_iff (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    edgeSign D atomFirst atomSecond = -1 ↔ atomPairing D atomFirst atomSecond < 0 := by
  rw [edgeSign]
  constructor
  · intro hsign
    by_contra hnonneg
    rw [if_pos (not_lt.mp hnonneg)] at hsign
    norm_num at hsign
  · intro hnegative
    rw [if_neg (not_le.mpr hnegative)]

/-- **THE GAUGE IS THE NEGATED EDGE SIGN.** Off the base, `Gtz.switchSign` is
`-Gtz.edgeSign` on the nose -- including at a vanishing pairing, where both sides
read `-1`. No nonvanishing hypothesis, which is why the identity below needs none
either. -/
theorem switchSign_eq_neg_edgeSign (D : WeightedDesign m 3) (base index : Fin m)
    (hne : index ≠ base) :
    switchSign D.atom base index = -edgeSign D base index := by
  have hfold : D.atom base ⬝ᵥ D.atom index = atomPairing D base index := rfl
  rw [switchSign, if_neg hne, hfold, edgeSign]
  rcases le_or_gt 0 (atomPairing D base index) with hnonneg | hnegative
  · rw [if_neg (not_lt.mpr hnonneg), if_pos hnonneg]
  · rw [if_pos hnegative, if_neg (not_le.mpr hnegative)]
    norm_num

/-- The design switched into the gauge of a chosen base atom: the shipped
`Gtz.switchedDesign` action driven by the shipped `Gtz.switchSign` gauge. Naming
the composite is what makes the identity below readable; it introduces no new
mathematics. -/
noncomputable def baseSwitchedDesign (D : WeightedDesign m 3) (base : Fin m) :
    WeightedDesign m 3 :=
  switchedDesign D (switchSign D.atom base) (switchSign_sq_eq_one D.atom base)

theorem baseSwitchedDesign_atom (D : WeightedDesign m 3) (base atomIndex : Fin m) :
    (baseSwitchedDesign D base).atom atomIndex
      = switchSign D.atom base atomIndex • D.atom atomIndex := rfl

/-- Every base edge switches to `-1`, hence to a strictly negative pairing. This is
where a vanishing base pairing genuinely costs something: the gauge cannot make
zero negative. -/
theorem edgeSign_baseSwitchedDesign_base (D : WeightedDesign m 3) (base : Fin m)
    {index : Fin m} (hne : index ≠ base) (hnonzero : atomPairing D base index ≠ 0) :
    edgeSign (baseSwitchedDesign D base) base index = -1 := by
  rw [baseSwitchedDesign,
    edgeSign_switchedDesign D (switchSign_sq_eq_one D.atom base) hnonzero,
    switchSign_base, switchSign_eq_neg_edgeSign D base index hne, one_mul]
  nlinarith [edgeSign_sq D base index]

/-- **THE SWITCHING IDENTITY.** In the gauge of a base atom, the sign of an
off-base edge IS the parity of its triangle through the base. So the
coherence-through-`base` graph on the other atoms is the positive-edge graph of
`Gtz.baseSwitchedDesign D base`, and every statement about incoherence at a base
becomes a statement about negative pairings of an honest design.

The two base signs cancel their own minus signs -- `(-e_bd)(-e_be) e_de` is
`e_bd e_be e_de` -- which is why the base edges need no nonvanishing hypothesis.
Only the off-base edge does, because that is where
`Gtz.edgeSign_switchedDesign` pays for `sign 0 = +1`. -/
theorem edgeSign_baseSwitchedDesign (D : WeightedDesign m 3) (base : Fin m)
    {first second : Fin m} (hfirst : first ≠ base) (hsecond : second ≠ base)
    (hfirstSecond : atomPairing D first second ≠ 0) :
    edgeSign (baseSwitchedDesign D base) first second
      = tripleParity D base first second := by
  rw [baseSwitchedDesign,
    edgeSign_switchedDesign D (switchSign_sq_eq_one D.atom base) hfirstSecond,
    switchSign_eq_neg_edgeSign D base first hfirst,
    switchSign_eq_neg_edgeSign D base second hsecond, tripleParity]
  ring

/-- **THE FOUR-SET AXIOM, SOLVED.** The parity of a triangle is the product of the
three parities joining it to any base atom whatever. Equivalent to the shipped
`Gtz.tripleParity_fourSet_product`, which states the same fact as a product equal
to one, but this is the form a consumer reads: the whole two-graph is determined by
its star at a single vertex. Hypothesis-free, exactly as the shipped form is.

The switching identity gives an independent derivation, since parity is a switching
invariant and the switched off-base signs ARE the base parities -- but that route
would need the off-base pairings nonzero, and this one needs nothing. -/
theorem tripleParity_eq_product_through_base (D : WeightedDesign m 3)
    (base first second third : Fin m) :
    tripleParity D first second third
      = tripleParity D base first second * tripleParity D base first third
        * tripleParity D base second third := by
  have hproduct := tripleParity_fourSet_product D base first second third
  have hsquare := tripleParity_sq D first second third
  linear_combination (-tripleParity D first second third) * hproduct
    + (tripleParity D base first second * tripleParity D base first third
      * tripleParity D base second third) * hsquare

/-! ## 2. Greedy independence

The only combinatorial input. Stated for a bare `Finset` of ordered pairs: no
graph structure, no symmetry, no irreflexivity. Deleting the first endpoint of one
edge kills at least that edge, so induction on the strict subset order over the
edge set gives an edge-free subset missing at most one vertex per edge. -/

/-- **GREEDY INDEPENDENCE.** Every finite vertex family has an edge-free subset
missing at most `edges.card` of its members. The `Finset` form of "a graph on `n`
vertices with `e` edges has an independent set of size at least `n - e`". -/
theorem exists_independent_of_edges {vertex : Type*} [DecidableEq vertex]
    (edges : Finset (vertex × vertex)) (family : Finset vertex) :
    ∃ indep : Finset vertex, indep ⊆ family ∧ family.card ≤ indep.card + edges.card
      ∧ ∀ first ∈ indep, ∀ second ∈ indep, (first, second) ∉ edges := by
  classical
  induction edges using Finset.strongInductionOn generalizing family with
  | _ edgeSet ih =>
    rcases Finset.eq_empty_or_nonempty edgeSet with rfl | ⟨someEdge, hsomeEdge⟩
    · exact ⟨family, Finset.Subset.refl _, by simp, by simp⟩
    · set removed : vertex := someEdge.1 with hremoved
      set smallerEdges : Finset (vertex × vertex) :=
        edgeSet.filter (fun pair => pair.1 ≠ removed ∧ pair.2 ≠ removed) with hsmallerEdges
      have hstrict : smallerEdges ⊂ edgeSet := by
        refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
          ⟨someEdge, hsomeEdge, ?_⟩
        rw [Finset.mem_filter]
        rintro ⟨-, hne, -⟩
        exact hne hremoved
      obtain ⟨indep, hsubset, hcard, hindep⟩ := ih smallerEdges hstrict (family.erase removed)
      have hcardStrict : smallerEdges.card < edgeSet.card := Finset.card_lt_card hstrict
      have hcardErase : family.card ≤ (family.erase removed).card + 1 := by
        rcases Finset.decidableMem removed family with hnotMem | hmem
        · rw [Finset.erase_eq_of_notMem hnotMem]; omega
        · rw [Finset.card_erase_of_mem hmem]
          have hpositive : 0 < family.card := Finset.card_pos.mpr ⟨removed, hmem⟩
          omega
      refine ⟨indep, hsubset.trans (Finset.erase_subset _ _), by omega, ?_⟩
      intro first hfirst second hsecond hmem
      have hfirstNe : first ≠ removed := Finset.ne_of_mem_erase (hsubset hfirst)
      have hsecondNe : second ≠ removed := Finset.ne_of_mem_erase (hsubset hsecond)
      exact hindep first hfirst second hsecond
        (by rw [Finset.mem_filter]; exact ⟨hmem, hfirstNe, hsecondNe⟩)

/-! ## 3. The cap: a totally incoherent neighbourhood has at most three members -/

/-- **THE INCOHERENT CAP.** A base-avoiding family whose triangles through the base
are ALL incoherent has at most three members, because the base gauge makes it
pairwise obtuse together with the base and the real obtuse bound in `R^3` is four.

Sharp: the four tetrahedron vertices have every triangle incoherent
(`Gtz.triangleProduct_tetraAtom_eq_neg_one`), so three off-base atoms can be
totally incoherent.

The nonvanishing hypotheses are LOCAL. A design with orthogonal pairs elsewhere
still gets the cap on any family they miss, which is what makes the count degrade
gracefully rather than vanish. -/
theorem card_le_three_of_forall_incoherent_through_base (D : WeightedDesign m 3)
    (base : Fin m) (family : Finset (Fin m)) (hbaseNotMem : base ∉ family)
    (hbaseNonzero : ∀ index ∈ family, atomPairing D base index ≠ 0)
    (hinnerNonzero : ∀ first ∈ family, ∀ second ∈ family, first ≠ second →
      atomPairing D first second ≠ 0)
    (hincoherent : ∀ first ∈ family, ∀ second ∈ family, first ≠ second →
      tripleParity D base first second = -1) :
    family.card ≤ 3 := by
  classical
  have hbaseEdge : ∀ index ∈ family, atomPairing (baseSwitchedDesign D base) base index < 0 := by
    intro index hmem
    refine (edgeSign_eq_neg_one_iff (baseSwitchedDesign D base) base index).mp ?_
    exact edgeSign_baseSwitchedDesign_base D base (fun heq => hbaseNotMem (heq ▸ hmem))
      (hbaseNonzero index hmem)
  have hinnerEdge : ∀ first ∈ family, ∀ second ∈ family, first ≠ second →
      atomPairing (baseSwitchedDesign D base) first second < 0 := by
    intro first hfirst second hsecond hdistinct
    refine (edgeSign_eq_neg_one_iff (baseSwitchedDesign D base) first second).mp ?_
    rw [edgeSign_baseSwitchedDesign D base (fun heq => hbaseNotMem (heq ▸ hfirst))
      (fun heq => hbaseNotMem (heq ▸ hsecond))
      (hinnerNonzero first hfirst second hsecond hdistinct)]
    exact hincoherent first hfirst second hsecond hdistinct
  have hobtuse : ∀ first ∈ insert base family, ∀ second ∈ insert base family, first ≠ second →
      (baseSwitchedDesign D base).atom first ⬝ᵥ (baseSwitchedDesign D base).atom second < 0 := by
    intro first hfirst second hsecond hdistinct
    rcases Finset.mem_insert.mp hfirst with rfl | hfirstFamily
    · rcases Finset.mem_insert.mp hsecond with rfl | hsecondFamily
      · exact absurd rfl hdistinct
      · exact hbaseEdge second hsecondFamily
    · rcases Finset.mem_insert.mp hsecond with rfl | hsecondFamily
      · have hflip := hbaseEdge first hfirstFamily
        rw [atomPairing_comm] at hflip
        exact hflip
      · exact hinnerEdge first hfirstFamily second hsecondFamily hdistinct
  have hcap : (insert base family).card ≤ Fintype.card (Fin 3) + 1 :=
    card_le_succ_of_isPairwiseObtuse_on (vec := (baseSwitchedDesign D base).atom)
      (insert base family) hobtuse
  rw [Finset.card_insert_of_notMem hbaseNotMem, Fintype.card_fin] at hcap
  omega

/-- **NO FOUR ATOMS ARE TOTALLY INCOHERENT AT A BASE.** The contrapositive of the
cap, and strictly sharper than the shipped `Gtz.exists_coherentTriple_through_atom`,
which needs a FIVE-atom window and locates only one triangle. -/
theorem exists_coherent_pair_of_four_avoiding_base (D : WeightedDesign m 3)
    (base : Fin m) (family : Finset (Fin m)) (hbaseNotMem : base ∉ family)
    (hbaseNonzero : ∀ index ∈ family, atomPairing D base index ≠ 0)
    (hinnerNonzero : ∀ first ∈ family, ∀ second ∈ family, first ≠ second →
      atomPairing D first second ≠ 0)
    (hcard : 4 ≤ family.card) :
    ∃ first ∈ family, ∃ second ∈ family, first ≠ second
      ∧ tripleParity D base first second = 1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hincoherent : ∀ first ∈ family, ∀ second ∈ family, first ≠ second →
      tripleParity D base first second = -1 := by
    intro first hfirst second hsecond hdistinct
    rcases tripleParity_eq_one_or_neg_one D base first second with hcoherent | hnot
    · exact absurd hcoherent (hnone first hfirst second hsecond hdistinct)
    · exact hnot
  have hcap := card_le_three_of_forall_incoherent_through_base D base family hbaseNotMem
    hbaseNonzero hinnerNonzero hincoherent
  omega

/-! ## 4. The count

The coherent triangles through a base, oriented canonically so that each is
counted once, and the lower bound on how many there are. -/

/-- The **coherent triangles through a base**, as ordered pairs with `first < second`
so that each unordered triangle appears exactly once. -/
noncomputable def coherentPairsThroughBase (D : WeightedDesign m 3) (base : Fin m) :
    Finset (Fin m × Fin m) :=
  @Finset.filter _ (fun pair => pair.1 ≠ base ∧ pair.2 ≠ base ∧ pair.1 < pair.2
    ∧ tripleParity D base pair.1 pair.2 = 1) (Classical.decPred _) Finset.univ

theorem mem_coherentPairsThroughBase_iff (D : WeightedDesign m 3) (base : Fin m)
    (pair : Fin m × Fin m) :
    pair ∈ coherentPairsThroughBase D base ↔ pair.1 ≠ base ∧ pair.2 ≠ base ∧ pair.1 < pair.2
      ∧ tripleParity D base pair.1 pair.2 = 1 := by
  classical
  simp only [coherentPairsThroughBase, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A member is a genuine coherent triangle: three distinct atoms, parity `+1`. -/
theorem tripleParity_eq_one_of_mem_coherentPairsThroughBase (D : WeightedDesign m 3)
    (base : Fin m) {pair : Fin m × Fin m} (hmem : pair ∈ coherentPairsThroughBase D base) :
    base ≠ pair.1 ∧ base ≠ pair.2 ∧ pair.1 ≠ pair.2
      ∧ tripleParity D base pair.1 pair.2 = 1 := by
  obtain ⟨hfirst, hsecond, horder, hparity⟩ :=
    (mem_coherentPairsThroughBase_iff D base pair).mp hmem
  exact ⟨Ne.symm hfirst, Ne.symm hsecond, ne_of_lt horder, hparity⟩

/-- **THE COUNT, in the form that degrades gracefully.** Every base-avoiding family
with the local nonvanishing contributes `family.card - 3` coherent triangles
through the base: greedy independence hands back an edge-free subset of the
coherence graph, and the cap says that subset has at most three members. -/
theorem card_coherentPairsThroughBase_ge_of_family (D : WeightedDesign m 3) (base : Fin m)
    (family : Finset (Fin m)) (hbaseNotMem : base ∉ family)
    (hbaseNonzero : ∀ index ∈ family, atomPairing D base index ≠ 0)
    (hinnerNonzero : ∀ first ∈ family, ∀ second ∈ family, first ≠ second →
      atomPairing D first second ≠ 0) :
    family.card - 3 ≤ (coherentPairsThroughBase D base).card := by
  classical
  obtain ⟨indep, hsubset, hcard, hindep⟩ :=
    exists_independent_of_edges (coherentPairsThroughBase D base) family
  have hincoherent : ∀ first ∈ indep, ∀ second ∈ indep, first ≠ second →
      tripleParity D base first second = -1 := by
    intro first hfirst second hsecond hdistinct
    have hfirstNe : first ≠ base := fun heq => hbaseNotMem (heq ▸ hsubset hfirst)
    have hsecondNe : second ≠ base := fun heq => hbaseNotMem (heq ▸ hsubset hsecond)
    rcases tripleParity_eq_one_or_neg_one D base first second with hcoherent | hnot
    · exfalso
      rcases lt_or_gt_of_ne hdistinct with hlow | hhigh
      · exact hindep first hfirst second hsecond
          ((mem_coherentPairsThroughBase_iff D base (first, second)).mpr
            ⟨hfirstNe, hsecondNe, hlow, hcoherent⟩)
      · refine hindep second hsecond first hfirst
          ((mem_coherentPairsThroughBase_iff D base (second, first)).mpr
            ⟨hsecondNe, hfirstNe, hhigh, ?_⟩)
        rw [← tripleParity_comm_right]
        exact hcoherent
    · exact hnot
  have hindepCard : indep.card ≤ 3 :=
    card_le_three_of_forall_incoherent_through_base D base indep
      (fun hmem => hbaseNotMem (hsubset hmem))
      (fun index hmem => hbaseNonzero index (hsubset hmem))
      (fun first hfirst second hsecond hdistinct =>
        hinnerNonzero first (hsubset hfirst) second (hsubset hsecond) hdistinct)
      hincoherent
  omega

/-- **THE SHARP COHERENT COUNT.** At least `m - 4` of the triangles through EVERY
atom of a rank-three design with pairwise nonzero pairings are coherent. `2` at
`m = 6`, `3` at `m = 7`.

This is the number the switching layer's wall asked for. It is sharp for this
route: the tetrahedron makes the cap `3` sharp. -/
theorem card_coherentPairsThroughBase_ge (D : WeightedDesign m 3) (base : Fin m)
    (hnonzero : ∀ first second : Fin m, first ≠ second → atomPairing D first second ≠ 0) :
    m - 4 ≤ (coherentPairsThroughBase D base).card := by
  classical
  have hfamilyCard : ((Finset.univ : Finset (Fin m)).erase base).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ base), Finset.card_univ, Fintype.card_fin]
  have hbound := card_coherentPairsThroughBase_ge_of_family D base
    ((Finset.univ : Finset (Fin m)).erase base) (Finset.notMem_erase base Finset.univ)
    (fun index hmem => hnonzero base index (Ne.symm (Finset.ne_of_mem_erase hmem)))
    (fun first _ second _ hdistinct => hnonzero first second hdistinct)
  rw [hfamilyCard] at hbound
  omega

/-- **THE COUNT WITH ONE ATOM DROPPED.** An orthogonality costs one coherent
triangle, not the whole count: deleting a single atom from the family leaves
`m - 5`, so at `(6,3)` an atom every orthogonality can be blamed on ONE other atom
still carries a coherent triangle. The nonvanishing is asked for only away from the
dropped atom. -/
theorem card_coherentPairsThroughBase_ge_of_erase (D : WeightedDesign m 3) (base drop : Fin m)
    (hdrop : drop ≠ base)
    (hbaseNonzero : ∀ index : Fin m, index ≠ base → index ≠ drop →
      atomPairing D base index ≠ 0)
    (hinnerNonzero : ∀ first second : Fin m, first ≠ base → second ≠ base → first ≠ drop →
      second ≠ drop → first ≠ second → atomPairing D first second ≠ 0) :
    m - 5 ≤ (coherentPairsThroughBase D base).card := by
  classical
  have hfamilyCard : ((((Finset.univ : Finset (Fin m)).erase base).erase drop)).card = m - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hdrop, Finset.mem_univ drop⟩),
      Finset.card_erase_of_mem (Finset.mem_univ base), Finset.card_univ, Fintype.card_fin]
    omega
  have hbound := card_coherentPairsThroughBase_ge_of_family D base
    (((Finset.univ : Finset (Fin m)).erase base).erase drop)
    (fun hmem => (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmem)) rfl)
    (fun index hmem => hbaseNonzero index
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmem)) (Finset.ne_of_mem_erase hmem))
    (fun first hfirst second hsecond hdistinct => hinnerNonzero first second
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hfirst))
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hsecond))
      (Finset.ne_of_mem_erase hfirst) (Finset.ne_of_mem_erase hsecond) hdistinct)
  rw [hfamilyCard] at hbound
  omega

/-- The `(6,3)` instance: two coherent triangles through every atom. -/
theorem two_le_card_coherentPairsThroughBase_sixThree (D : WeightedDesign 6 3) (base : Fin 6)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing D first second ≠ 0) :
    2 ≤ (coherentPairsThroughBase D base).card :=
  card_coherentPairsThroughBase_ge D base hnonzero

/-- The `(7,3)` instance: three coherent triangles through every atom. -/
theorem three_le_card_coherentPairsThroughBase_sevenThree (D : WeightedDesign 7 3)
    (base : Fin 7)
    (hnonzero : ∀ first second : Fin 7, first ≠ second → atomPairing D first second ≠ 0) :
    3 ≤ (coherentPairsThroughBase D base).card :=
  card_coherentPairsThroughBase_ge D base hnonzero

/-- **TWO DISTINCT COHERENT TRIANGLES, unpacked.** The readable form of the count
at `m >= 6`, for a consumer that wants the atoms rather than a cardinality. -/
theorem exists_two_coherentTriples_through_base (D : WeightedDesign m 3) (hsize : 6 ≤ m)
    (base : Fin m)
    (hnonzero : ∀ first second : Fin m, first ≠ second → atomPairing D first second ≠ 0) :
    ∃ firstPair secondPair : Fin m × Fin m, firstPair ≠ secondPair
      ∧ base ≠ firstPair.1 ∧ base ≠ firstPair.2 ∧ firstPair.1 ≠ firstPair.2
      ∧ tripleParity D base firstPair.1 firstPair.2 = 1
      ∧ base ≠ secondPair.1 ∧ base ≠ secondPair.2 ∧ secondPair.1 ≠ secondPair.2
      ∧ tripleParity D base secondPair.1 secondPair.2 = 1 := by
  have hcard := card_coherentPairsThroughBase_ge D base hnonzero
  have honeLt : 1 < (coherentPairsThroughBase D base).card := by omega
  obtain ⟨firstPair, hfirstMem, secondPair, hsecondMem, hdistinct⟩ :=
    Finset.one_lt_card.mp honeLt
  obtain ⟨hfirstOne, hfirstTwo, hfirstNe, hfirstParity⟩ :=
    tripleParity_eq_one_of_mem_coherentPairsThroughBase D base hfirstMem
  obtain ⟨hsecondOne, hsecondTwo, hsecondNe, hsecondParity⟩ :=
    tripleParity_eq_one_of_mem_coherentPairsThroughBase D base hsecondMem
  exact ⟨firstPair, secondPair, hdistinct, hfirstOne, hfirstTwo, hfirstNe, hfirstParity,
    hsecondOne, hsecondTwo, hsecondNe, hsecondParity⟩

/-- **A TWO-LINE REPROOF OF THE SHIPPED LOCATED CONSTRAINT.** The shipped
`Gtz.exists_coherentTriple_through_atom` routes through Lemma A and the four-set
axiom; the count reproves it, since `m - 4 >= 1` already at `m = 5`. The
shipped statement is kept -- it is the historical one and other files cite it. -/
theorem exists_coherentTriple_through_atom_of_count (D : WeightedDesign m 3) (hsize : 5 ≤ m)
    (base : Fin m)
    (hnonzero : ∀ first second : Fin m, first ≠ second → atomPairing D first second ≠ 0) :
    ∃ second third : Fin m, base ≠ second ∧ base ≠ third ∧ second ≠ third
      ∧ tripleParity D base second third = 1 := by
  have hcard := card_coherentPairsThroughBase_ge D base hnonzero
  obtain ⟨pair, hmem⟩ := Finset.card_pos.mp (by omega : 0 < (coherentPairsThroughBase D base).card)
  obtain ⟨hone, htwo, hne, hparity⟩ :=
    tripleParity_eq_one_of_mem_coherentPairsThroughBase D base hmem
  exact ⟨pair.1, pair.2, hone, htwo, hne, hparity⟩

/-! ## 5. The oriented product at a coherent triangle

A coherent triangle with nonvanishing pairings has a strictly POSITIVE oriented
product, not merely a `+1` parity. The shipped implication runs the other way. -/

/-- The parity reads the sign of the oriented product, so `+1` with a nonvanishing
product means the product is strictly positive. Converse of the shipped
`Gtz.tripleParity_eq_one_of_pos_atomPairingProduct`. -/
theorem pos_atomPairingProduct_of_tripleParity_eq_one (D : WeightedDesign m 3)
    {first second third : Fin m} (hparity : tripleParity D first second third = 1)
    (hnonzero : atomPairing D first second * atomPairing D first third
      * atomPairing D second third ≠ 0) :
    0 < atomPairing D first second * atomPairing D first third
      * atomPairing D second third := by
  have hcarry := tripleParity_mul_abs_atomPairingProduct D first second third
  rw [hparity, one_mul] at hcarry
  rcases lt_or_gt_of_ne hnonzero with hnegative | hpositive
  · exfalso
    rw [abs_of_neg hnegative] at hcarry
    linarith
  · exact hpositive

/-! ## 6. At a `(6,3)` crux

Composing the count with the substrate's X0 squeeze. Every coherent triangle of a
crux has a strictly negative sign-blind gap, so the count is a count of triangles
carrying that inequality. -/

namespace SixThreeCrux

/-- Every coherent triangle through a base atom of a crux carries the full X0
package: a strictly positive oriented product, a strictly negative sign-blind gap,
and hence a tie leg strictly below twice the product. -/
theorem forall_mem_coherentPairsThroughBase_negative (crux : SixThreeCrux) (base : Fin 6)
    (hnonzero : ∀ first second : Fin 6, first ≠ second →
      atomPairing crux.design first second ≠ 0)
    {pair : Fin 6 × Fin 6} (hmem : pair ∈ coherentPairsThroughBase crux.design base) :
    0 < atomPairing crux.design base pair.1 * atomPairing crux.design base pair.2
        * atomPairing crux.design pair.1 pair.2
      ∧ excessGap crux.design base pair.1 pair.2 < 0
      ∧ discriminantTie crux.design base pair.1 pair.2
        < 2 * (atomPairing crux.design base pair.1 * atomPairing crux.design base pair.2
          * atomPairing crux.design pair.1 pair.2) := by
  obtain ⟨hbaseFirst, hbaseSecond, hdistinct, hparity⟩ :=
    tripleParity_eq_one_of_mem_coherentPairsThroughBase crux.design base hmem
  have hproductNe : atomPairing crux.design base pair.1 * atomPairing crux.design base pair.2
      * atomPairing crux.design pair.1 pair.2 ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact hnonzero base pair.1 hbaseFirst
    · exact hnonzero base pair.2 hbaseSecond
    · exact hnonzero pair.1 pair.2 hdistinct
  have hpositive := pos_atomPairingProduct_of_tripleParity_eq_one crux.design hparity hproductNe
  have hgap := excessGap_neg_of_coherent crux hbaseFirst hbaseSecond hdistinct hparity
  refine ⟨hpositive, hgap, ?_⟩
  have hbridge := discriminantTie_eq_excessGap_add_parity crux.design base pair.1 pair.2
  rw [hparity, abs_of_pos hpositive] at hbridge
  linarith

/-- **THE X2 PACKAGE AT A `(6,3)` CRUX.** Through every atom whose pairings are all
nonzero there are at least TWO coherent triangles, and every coherent triangle
through it has a strictly positive oriented product, a strictly negative sign-blind
gap, and a tie leg strictly below twice that product. This is the statement the
excess-gap census and the two-graph collision consume. -/
theorem two_le_card_coherentPairsThroughBase_and_forall_negative (crux : SixThreeCrux)
    (base : Fin 6)
    (hnonzero : ∀ first second : Fin 6, first ≠ second →
      atomPairing crux.design first second ≠ 0) :
    2 ≤ (coherentPairsThroughBase crux.design base).card
      ∧ ∀ pair ∈ coherentPairsThroughBase crux.design base,
        0 < atomPairing crux.design base pair.1 * atomPairing crux.design base pair.2
            * atomPairing crux.design pair.1 pair.2
          ∧ excessGap crux.design base pair.1 pair.2 < 0
          ∧ discriminantTie crux.design base pair.1 pair.2
            < 2 * (atomPairing crux.design base pair.1 * atomPairing crux.design base pair.2
              * atomPairing crux.design pair.1 pair.2) :=
  ⟨two_le_card_coherentPairsThroughBase_sixThree crux.design base hnonzero,
    fun _ hmem => forall_mem_coherentPairsThroughBase_negative crux base hnonzero hmem⟩

/-! ### The vanishing-pairing branch

Not a caveat: an orthogonality at a crux is edge-level structure. -/

/-- **AN ORTHOGONAL PAIR KILLS THE TIE LEG OUTRIGHT.** Where a pairing vanishes the
parity has no vote, so the tie leg IS the sign-blind gap and the squeeze makes both
strictly negative. Four triangles per orthogonal edge at `(6,3)`. -/
theorem discriminantTie_neg_of_atomPairing_eq_zero (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hzero : atomPairing crux.design first second = 0
      ∨ atomPairing crux.design first third = 0
      ∨ atomPairing crux.design second third = 0) :
    discriminantTie crux.design first second third < 0 := by
  rw [discriminantTie_eq_excessGap_of_exists_atomPairing_eq_zero crux.design hzero]
  exact excessGap_neg_of_exists_atomPairing_eq_zero crux hfirstSecond hfirstThird
    hsecondThird hzero

/-- **THE QUANTITATIVE ORTHOGONAL BRANCH.** An orthogonal pair at a crux forces
every third atom's excess to be strictly dominated by the two surviving squared
pairings, weighted by the excesses of the orthogonal pair. This is `excessGap < 0`
with the vanishing pairing substituted, and it is the inequality the census
consumes on the orthogonal edges. -/
theorem heavyExcess_lt_of_orthogonalPair (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hzero : atomPairing crux.design first second = 0) :
    heavyExcess crux.design first * heavyExcess crux.design second
        * heavyExcess crux.design third
      < heavyExcess crux.design second * atomPairing crux.design first third ^ 2
        + heavyExcess crux.design first * atomPairing crux.design second third ^ 2 := by
  have hgap := excessGap_neg_of_exists_atomPairing_eq_zero crux hfirstSecond hfirstThird
    hsecondThird (Or.inl hzero)
  rw [excessGap, hzero] at hgap
  nlinarith [hgap]

/-- **AN ATOM ORTHOGONAL TO TWO OTHERS MAKES THEM AN INCOMPATIBLE EDGE.** With two
of the three pairings gone, `excessGap` collapses to `heavyExcess base * pairMinor`,
and the squeeze plus all-heaviness turn its negativity into `pairMinor < 0`.

So an orthogonality at a crux is not a hole in the sign argument: it produces
edge-level structure, in exactly the vocabulary the pair rung and the two-graph
collision read. Compare `Gtz.SixThreeCrux.hasNoOrthogonalTriple`, which forbids all
THREE pairings vanishing; this governs the case where two do. -/
theorem pairMinor_neg_of_common_orthogonalPartner (crux : SixThreeCrux)
    {base first second : Fin 6} (hbaseFirst : base ≠ first) (hbaseSecond : base ≠ second)
    (hfirstSecond : first ≠ second)
    (hzeroFirst : atomPairing crux.design base first = 0)
    (hzeroSecond : atomPairing crux.design base second = 0) :
    pairMinor crux.design first second < 0 := by
  have hgap := excessGap_neg_of_exists_atomPairing_eq_zero crux hbaseFirst hbaseSecond
    hfirstSecond (Or.inl hzeroFirst)
  rw [excessGap, hzeroFirst, hzeroSecond] at hgap
  have hheavy : (1:ℝ) < leverageOf (crux.design.atom base) := crux.isAllHeavy base
  have hexcess : 0 < heavyExcess crux.design base := by
    rw [heavyExcess]; linarith
  have hcollapse : heavyExcess crux.design base * pairMinor crux.design first second < 0 := by
    rw [pairMinor]; nlinarith [hgap]
  nlinarith [hcollapse, hexcess]

/-- **THE PER-ATOM DICHOTOMY, with no hypothesis at all.** Either the count holds at
this base, or the design carries an orthogonal pair -- and then
`Gtz.SixThreeCrux.discriminantTie_neg_of_atomPairing_eq_zero`,
`Gtz.SixThreeCrux.heavyExcess_lt_of_orthogonalPair` and
`Gtz.SixThreeCrux.pairMinor_neg_of_common_orthogonalPartner` say what that costs. -/
theorem two_le_card_coherentPairsThroughBase_or_exists_orthogonalPair (crux : SixThreeCrux)
    (base : Fin 6) :
    2 ≤ (coherentPairsThroughBase crux.design base).card
      ∨ ∃ first second : Fin 6, first ≠ second
        ∧ atomPairing crux.design first second = 0 := by
  by_cases hnonzero : ∀ first second : Fin 6, first ≠ second →
      atomPairing crux.design first second ≠ 0
  · exact Or.inl (two_le_card_coherentPairsThroughBase_sixThree crux.design base hnonzero)
  · push Not at hnonzero
    obtain ⟨first, second, hdistinct, hzero⟩ := hnonzero
    exact Or.inr ⟨first, second, hdistinct, hzero⟩

end SixThreeCrux

/-! ## 7. At a `(7,3)` crux

The squeeze at `(7,3)` is the same two lines as at `(6,3)` -- the parity-free gate
`Gtz.dominates_of_excessGap_nonneg_of_discriminantTie_nonneg` is stated at every
size -- and the count there is three rather than two. -/

namespace SevenThreeCrux

/-- The X0 squeeze at `(7,3)`: a nonnegative sign-blind gap forces a strictly
negative tie leg. -/
theorem discriminantTie_neg_of_excessGap_nonneg (crux : SevenThreeCrux)
    {first second third : Fin 7} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hgap : 0 ≤ excessGap crux.design first second third) :
    discriminantTie crux.design first second third < 0 :=
  lt_of_not_ge fun htie =>
    crux.hasNoDominatingTriple {first, second, third}
      (card_triple_eq_three hfirstSecond hfirstThird hsecondThird)
      (dominates_of_excessGap_nonneg_of_discriminantTie_nonneg crux.isAllHeavy hfirstSecond
        hfirstThird hsecondThird hgap htie)

/-- A COHERENT triangle of a `(7,3)` crux has a strictly negative sign-blind gap. -/
theorem excessGap_neg_of_coherent (crux : SevenThreeCrux) {first second third : Fin 7}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hparity : tripleParity crux.design first second third = 1) :
    excessGap crux.design first second third < 0 := by
  refine lt_of_not_ge fun hgap => ?_
  have htie := discriminantTie_neg_of_excessGap_nonneg crux hfirstSecond hfirstThird
    hsecondThird hgap
  rw [discriminantTie_eq_excessGap_add_parity, hparity] at htie
  have hmagnitude : (0:ℝ) ≤ |atomPairing crux.design first second
      * atomPairing crux.design first third * atomPairing crux.design second third| :=
    abs_nonneg _
  linarith

/-- **THE X2 PACKAGE AT A `(7,3)` CRUX.** Three coherent triangles through every
atom, each with a strictly negative sign-blind gap. -/
theorem three_le_card_coherentPairsThroughBase_and_forall_excessGap_neg
    (crux : SevenThreeCrux) (base : Fin 7)
    (hnonzero : ∀ first second : Fin 7, first ≠ second →
      atomPairing crux.design first second ≠ 0) :
    3 ≤ (coherentPairsThroughBase crux.design base).card
      ∧ ∀ pair ∈ coherentPairsThroughBase crux.design base,
        excessGap crux.design base pair.1 pair.2 < 0 := by
  refine ⟨three_le_card_coherentPairsThroughBase_sevenThree crux.design base hnonzero,
    fun pair hmem => ?_⟩
  obtain ⟨hbaseFirst, hbaseSecond, hdistinct, hparity⟩ :=
    tripleParity_eq_one_of_mem_coherentPairsThroughBase crux.design base hmem
  exact excessGap_neg_of_coherent crux hbaseFirst hbaseSecond hdistinct hparity

end SevenThreeCrux

/-! ## 8. The global count

Summing the per-base count over the atoms and dividing by three. A coherent
triangle is counted once at each of its three vertices, so the FLAGS -- a base
together with a coherent pair through it -- fibre three-to-one over the triangles,
and `Gtz.card_le_mul_card_image` converts the sum into a bound on the triangles
themselves. -/

/-- **THE SUMMED COUNT.** `Gtz.card_coherentPairsThroughBase_ge` added over the
atoms. -/
theorem sum_card_coherentPairsThroughBase_ge (D : WeightedDesign m 3)
    (hnonzero : ∀ first second : Fin m, first ≠ second → atomPairing D first second ≠ 0) :
    m * (m - 4) ≤ ∑ base : Fin m, (coherentPairsThroughBase D base).card := by
  have hbound : ∑ _base : Fin m, (m - 4) ≤ ∑ base : Fin m, (coherentPairsThroughBase D base).card :=
    Finset.sum_le_sum fun base _ => card_coherentPairsThroughBase_ge D base hnonzero
  simpa [Finset.sum_const, Finset.card_univ, mul_comm] using hbound

/-- The parity rotates: two shipped commutations in sequence. With
`Gtz.tripleParity_comm_left` and `Gtz.tripleParity_comm_right` this generates the
full symmetric group on the triple, which is why a coherent triangle is a property
of the three-element SET and not of an ordering. -/
theorem tripleParity_rotate (D : WeightedDesign m 3) (first second third : Fin m) :
    tripleParity D first second third = tripleParity D second third first := by
  rw [tripleParity_comm_left, tripleParity_comm_right]

/-- Two-element sets written in increasing order agree entrywise. The step that
makes a flag recoverable from its base and its triangle. -/
theorem orderedPair_eq_of_pairFinset_eq {first second third fourth : Fin m}
    (hleft : first < second) (hright : third < fourth)
    (hset : ({first, second} : Finset (Fin m)) = {third, fourth}) :
    first = third ∧ second = fourth := by
  classical
  have hfirstMem : first = third ∨ first = fourth := by
    have hmem : first ∈ ({third, fourth} : Finset (Fin m)) := by rw [← hset]; simp
    simpa using hmem
  have hsecondMem : second = third ∨ second = fourth := by
    have hmem : second ∈ ({third, fourth} : Finset (Fin m)) := by rw [← hset]; simp
    simpa using hmem
  have hthirdMem : third = first ∨ third = second := by
    have hmem : third ∈ ({first, second} : Finset (Fin m)) := by rw [hset]; simp
    simpa using hmem
  rcases hfirstMem with hfirstEq | hfirstEq
  · refine ⟨hfirstEq, ?_⟩
    rcases hsecondMem with hsecondEq | hsecondEq
    · exact absurd (hfirstEq.trans hsecondEq.symm) (ne_of_lt hleft)
    · exact hsecondEq
  · exfalso
    rcases hthirdMem with hthirdEq | hthirdEq
    · rw [hthirdEq, ← hfirstEq] at hright
      exact lt_irrefl _ hright
    · rw [hthirdEq, ← hfirstEq] at hright
      exact absurd hright (not_lt.mpr hleft.le)

/-- The **three-element subsets carrying a coherent triangle**. Stated with an
existential ordering because that is what a flag hands over; by
`Gtz.tripleParity_comm_left`, `Gtz.tripleParity_comm_right` and
`Gtz.tripleParity_rotate` the parity does not depend on the ordering, so the
predicate really is a property of the set. -/
noncomputable def coherentTripleSets (D : WeightedDesign m 3) : Finset (Finset (Fin m)) :=
  @Finset.filter _ (fun selected => ∃ first second third : Fin m,
      selected = {first, second, third} ∧ first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ tripleParity D first second third = 1) (Classical.decPred _) Finset.univ

theorem mem_coherentTripleSets_iff (D : WeightedDesign m 3) (selected : Finset (Fin m)) :
    selected ∈ coherentTripleSets D ↔ ∃ first second third : Fin m,
      selected = {first, second, third} ∧ first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ tripleParity D first second third = 1 := by
  classical
  simp only [coherentTripleSets, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The **coherent flags**: a base atom together with a coherent pair through it.
Its cardinality is the summed count, and it fibres three-to-one over the coherent
triangles. -/
noncomputable def coherentFlags (D : WeightedDesign m 3) :
    Finset ((_ : Fin m) × (Fin m × Fin m)) :=
  Finset.univ.sigma (fun base => coherentPairsThroughBase D base)

theorem card_coherentFlags (D : WeightedDesign m 3) :
    (coherentFlags D).card = ∑ base : Fin m, (coherentPairsThroughBase D base).card :=
  Finset.card_sigma _ _

/-- The three atoms of a flag. -/
def flagAtoms (flag : (_ : Fin m) × (Fin m × Fin m)) : Finset (Fin m) :=
  {flag.1, flag.2.1, flag.2.2}

theorem mem_coherentFlags_iff (D : WeightedDesign m 3)
    (flag : (_ : Fin m) × (Fin m × Fin m)) :
    flag ∈ coherentFlags D ↔ flag.2 ∈ coherentPairsThroughBase D flag.1 := by
  rw [coherentFlags, Finset.mem_sigma]
  exact ⟨fun hmem => hmem.2, fun hmem => ⟨Finset.mem_univ _, hmem⟩⟩

theorem image_flagAtoms_subset (D : WeightedDesign m 3) :
    (coherentFlags D).image flagAtoms ⊆ coherentTripleSets D := by
  classical
  intro selected hmem
  obtain ⟨flag, hflag, rfl⟩ := Finset.mem_image.mp hmem
  obtain ⟨hbaseFirst, hbaseSecond, hdistinct, hparity⟩ :=
    tripleParity_eq_one_of_mem_coherentPairsThroughBase D flag.1
      ((mem_coherentFlags_iff D flag).mp hflag)
  exact (mem_coherentTripleSets_iff D _).mpr
    ⟨flag.1, flag.2.1, flag.2.2, rfl, hbaseFirst, hbaseSecond, hdistinct, hparity⟩

/-- **THE FIBRE IS AT MOST THREE.** A flag over a given triangle is determined by
its base, and the triangle has three atoms. Determinacy is the ordered-pair step:
the two non-base atoms are the triangle with the base erased, and they are written
in increasing order. -/
theorem card_filter_flagAtoms_le_three (D : WeightedDesign m 3) (selected : Finset (Fin m))
    (hmem : selected ∈ (coherentFlags D).image flagAtoms) :
    ((coherentFlags D).filter (fun flag => flagAtoms flag = selected)).card ≤ 3 := by
  classical
  obtain ⟨witness, hwitness, hwitnessAtoms⟩ := Finset.mem_image.mp hmem
  have hwitnessData := tripleParity_eq_one_of_mem_coherentPairsThroughBase D witness.1
    ((mem_coherentFlags_iff D witness).mp hwitness)
  have hcardThree : selected.card = 3 := by
    rw [← hwitnessAtoms, flagAtoms]
    exact card_triple_eq_three hwitnessData.1 hwitnessData.2.1 hwitnessData.2.2.1
  have hmapsTo : ∀ flag ∈ (coherentFlags D).filter (fun flag => flagAtoms flag = selected),
      flag.1 ∈ selected := by
    intro flag hflag
    have hatoms := (Finset.mem_filter.mp hflag).2
    rw [← hatoms, flagAtoms]
    simp
  have hinjOn : ∀ leftFlag ∈ (coherentFlags D).filter (fun flag => flagAtoms flag = selected),
      ∀ rightFlag ∈ (coherentFlags D).filter (fun flag => flagAtoms flag = selected),
      leftFlag.1 = rightFlag.1 → leftFlag = rightFlag := by
    intro leftFlag hleft rightFlag hright hbase
    obtain ⟨hleftMem, hleftAtoms⟩ := Finset.mem_filter.mp hleft
    obtain ⟨hrightMem, hrightAtoms⟩ := Finset.mem_filter.mp hright
    obtain ⟨hleftOne, hleftTwo, hleftOrder, -⟩ :=
      (mem_coherentPairsThroughBase_iff D leftFlag.1 leftFlag.2).mp
        ((mem_coherentFlags_iff D leftFlag).mp hleftMem)
    obtain ⟨hrightOne, hrightTwo, hrightOrder, -⟩ :=
      (mem_coherentPairsThroughBase_iff D rightFlag.1 rightFlag.2).mp
        ((mem_coherentFlags_iff D rightFlag).mp hrightMem)
    have hleftNotMem : leftFlag.1 ∉ ({leftFlag.2.1, leftFlag.2.2} : Finset (Fin m)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact fun hcase => hcase.elim (fun heq => hleftOne heq.symm) (fun heq => hleftTwo heq.symm)
    have hrightNotMem : rightFlag.1 ∉ ({rightFlag.2.1, rightFlag.2.2} : Finset (Fin m)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact fun hcase => hcase.elim (fun heq => hrightOne heq.symm) (fun heq => hrightTwo heq.symm)
    have hpairEq : ({leftFlag.2.1, leftFlag.2.2} : Finset (Fin m))
        = {rightFlag.2.1, rightFlag.2.2} := by
      have hleftErase : ({leftFlag.2.1, leftFlag.2.2} : Finset (Fin m))
          = selected.erase leftFlag.1 := by
        rw [← hleftAtoms, flagAtoms, Finset.erase_insert hleftNotMem]
      have hrightErase : ({rightFlag.2.1, rightFlag.2.2} : Finset (Fin m))
          = selected.erase rightFlag.1 := by
        rw [← hrightAtoms, flagAtoms, Finset.erase_insert hrightNotMem]
      rw [hleftErase, hrightErase, hbase]
    obtain ⟨hone, htwo⟩ := orderedPair_eq_of_pairFinset_eq hleftOrder hrightOrder hpairEq
    exact Sigma.ext hbase (heq_of_eq (Prod.ext_iff.mpr ⟨hone, htwo⟩))
  have hbound := Finset.card_le_card_of_injOn (fun flag => flag.1)
    (fun flag hflag => hmapsTo flag hflag)
    (fun leftFlag hleft rightFlag hright hbase => hinjOn leftFlag hleft rightFlag hright hbase)
  omega

/-- **THE GLOBAL COUNT.** At least `m (m - 4) / 3` of the triangles of a rank-three
design with pairwise nonzero pairings are coherent. The per-base count summed over
the atoms, divided by the three-to-one fibring of flags over triangles. -/
theorem card_coherentTripleSets_ge (D : WeightedDesign m 3)
    (hnonzero : ∀ first second : Fin m, first ≠ second → atomPairing D first second ≠ 0) :
    m * (m - 4) ≤ 3 * (coherentTripleSets D).card := by
  classical
  have hsum := sum_card_coherentPairsThroughBase_ge D hnonzero
  have hflagCard := card_coherentFlags D
  have hfibre := Finset.card_le_mul_card_image (f := flagAtoms) (coherentFlags D) 3
    (fun selected hmem => card_filter_flagAtoms_le_three D selected hmem)
  have hsubset := Finset.card_le_card (image_flagAtoms_subset D)
  have hchain : (coherentFlags D).card ≤ 3 * (coherentTripleSets D).card :=
    le_trans hfibre (Nat.mul_le_mul_left 3 hsubset)
  rw [hflagCard] at hchain
  exact le_trans hsum hchain

/-- **FOUR OF THE TWENTY, at `(6,3)`.** -/
theorem four_le_card_coherentTripleSets_sixThree (D : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing D first second ≠ 0) :
    4 ≤ (coherentTripleSets D).card := by
  have hbound := card_coherentTripleSets_ge D hnonzero
  omega

/-- **SEVEN OF THE THIRTY-FIVE, at `(7,3)`.** -/
theorem seven_le_card_coherentTripleSets_sevenThree (D : WeightedDesign 7 3)
    (hnonzero : ∀ first second : Fin 7, first ≠ second → atomPairing D first second ≠ 0) :
    7 ≤ (coherentTripleSets D).card := by
  have hbound := card_coherentTripleSets_ge D hnonzero
  omega

end Gtz

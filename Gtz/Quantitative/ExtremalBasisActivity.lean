/-
# Basis activity at an extremal design: the splitting transfer, and the diamond

At a tie (`Gtz.IsTie`, the value is exactly `1`) some `k`-subset sits at
`lambda_min = 1` and none sits above it.  Which ones sit AT it?  Call a `k`-subset
ACTIVE when it dominates; `Gtz.Ties.TotalTieCorankOne` calls the tie TOTAL when
every basis of the direction matroid is active, and settles two halves of that
question.  Every non-basis is inactive at every design, tie or not
(`Gtz.not_dominates_of_commonOrthogonal`), so all the content is the basis half;
and at corank one the basis half is a theorem — `Gtz.corankOne_isTie_dominates`
proves EVERY `k`-subset of a corank-one tie dominates, `corankOne_isTie_det_ne_zero`
that every one of them is a basis, so the matroid is `U(k, k+1)` and the tie is
total.  That file's own boundary section records the rest as open: "Totality at
corank >= 2 is OPEN and is NOT a lemma one can land before the target."

This file does not touch that open statement.  It supplies the two things one can
have without it, and both are activity statements about designs the repository
already builds.

## The splitting transfer, over an ARBITRARY base

`Gtz.splitClassDesign` puts the corank-one atom of a class on every atom of that
class, and `Gtz.splitClassDesign_isTie` proves the result is a tie for an arbitrary
surjection and an arbitrary weight vector.  `Gtz.splitDesign`
(`Gtz.Reduction.SplitTransfer`) splits ONE atom in two and carries `IsTie` across
in both directions, so iterating it already gives "a splitting of a tie is a tie".
Neither says which subsets are active.

`parallelSplitDesign` is the simultaneous form over an arbitrary base design: any
`classOf : Fin splitSize -> Fin baseSize` and any positive weight vector whose class
totals are the base weights.  Parseval survives because atoms sharing a class share
their rank-one moment.  What is new is the ACTIVITY LAW
(`dominates_parallelSplitDesign_iff`): a `k`-subset upstairs dominates exactly when
it is class-injective AND its image dominates downstairs — the two ways of failing
are separated, and the non-injective failure is unconditional.  Composed with the
shipped corank-one totality it gives

  **every splitting of a corank-one tie has its active `k`-subsets EXACTLY its
  bases** (`dominates_parallelSplitDesign_iff_det_ne_zero_of_corankOne`),

at every size and every weight vector, not just at `m = k + 1`.  For the shipped
`splitClassDesign` this is `splitClassDesign_dominates_iff_det_ne_zero`; the two-line
half of it is `splitClassDesign_dominates_of_injOn`, which is
`Gtz.subsetSum_splitClassDesign_of_injOn` composed with
`Gtz.corankOne_isTie_dominates`.  Neither of those two is restated here.

## The diamond, all eight bases

`Gtz.Design.DiamondPrimitive` — "the surviving copy", per
`Gtz.Ties.StratumLocalCovering`; the twin `Gtz/Ties/DiamondTie.lean` is imported by
nothing and is deliberately outside `Gtz/Audit.lean` — builds the second rank-three
tie primitive, the graphic design of `K4 - e` at `(5,3)`, and proves it is a tie: ONE
triple dominates (the spine `{ab, ac, ad}`, by an exact sum of squares) and NO triple
dominates strictly (ten explicit directions).  Which of the ten triples dominate was
left open there, and `Dominates` is strictly more than the `¬ PosDef` those ten
directions give.

All eight spanning trees do, each by an exact two-square rational certificate
computed here as the pivots of an exact LDL decomposition; the two triangles
`{ab,ac,bc}` and `{ab,ad,bd}` do not, each by a strictly negative rational
direction.  So

  **the diamond tie is TOTAL** (`diamondDesign_isTotalTie`), and its active
  triples are exactly its bases (`diamondDesign_dominates_iff_isSpanningTree`),

which is the first total tie in the repository at corank two.  It is an instance,
not the open theorem: nothing here says every tie beyond corank one is total.

Composing the two parts splits the diamond into `(6,3)` and `(7,3)` classes —
designs no file had built — with their activity read off the base by the transfer
(`sixSplitDiamondDesign_isTie`, `sevenSplitDiamondDesign_isTie`, and the two
`_dominates_iff`).  The `(6,3)` one is NOT a splitting of any corank-one design, and
that is a theorem here rather than prose
(`not_eq_parallelSplitDesign_corankOne_sixSplitDiamondDesign`): five of its atoms are
the diamond's pairwise non-parallel directions, four classes cannot hold five
pairwise-distinct directions, and the shipped `Gtz.not_hasParallelPair_diamondDesign`
supplies the non-parallelism.  The same statement at `(7,3)` is not proved here.

## Scope

Nothing here bears on `GtzWeighted 6 3` or `GtzWeighted 7 3`.  A tie is a boundary
point of the feasible region; this file says which of its subsets touch the
boundary.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Ties.CorankOneTieCriterion
import Gtz.Ties.TotalTieCorankOne
import Gtz.Ties.SplitClassTieFamily
import Gtz.Design.DiamondPrimitive
import Gtz.Reduction.SplitTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## Parallel splitting over an arbitrary base design -/

/-- **A parallel splitting of a base design.**  Every atom upstairs carries the base
atom of its class; the weights are free apart from their class totals, which must be
the base weights.  Positivity of the base weights makes `classOf` surjective
automatically, so no surjectivity hypothesis is carried. -/
structure IsParallelSplitting {baseSize splitSize rank : ℕ}
    (base : WeightedDesign baseSize rank) (classOf : Fin splitSize → Fin baseSize)
    (weight : Fin splitSize → ℝ) : Prop where
  /-- The upstairs weights are positive. -/
  hasPositiveWeights : ∀ atomIndex, 0 < weight atomIndex
  /-- Each class carries exactly the base weight of its label. -/
  hasClassTotals : ∀ label : Fin baseSize,
    ∑ atomIndex ∈ Finset.univ.filter (fun c => classOf c = label), weight atomIndex
      = base.weight label

variable {baseSize splitSize rank : ℕ}

theorem sum_weight_eq_one_of_isParallelSplitting {base : WeightedDesign baseSize rank}
    {classOf : Fin splitSize → Fin baseSize} {weight : Fin splitSize → ℝ}
    (hsplit : IsParallelSplitting base classOf weight) : ∑ atomIndex, weight atomIndex = 1 := by
  rw [← Finset.sum_fiberwise Finset.univ classOf weight]
  rw [Finset.sum_congr rfl fun label _ => hsplit.hasClassTotals label]
  exact base.weight_sum_one

/-- **Splitting is onto.**  A missed label would have an empty fibre, hence class
total zero, contradicting positivity of the base weight there. -/
theorem surjective_classOf_of_isParallelSplitting {base : WeightedDesign baseSize rank}
    {classOf : Fin splitSize → Fin baseSize} {weight : Fin splitSize → ℝ}
    (hsplit : IsParallelSplitting base classOf weight) : Function.Surjective classOf := by
  intro label
  by_contra hmissed
  push Not at hmissed
  have hempty : Finset.univ.filter (fun c => classOf c = label) = (∅ : Finset (Fin splitSize)) :=
    Finset.filter_eq_empty_iff.mpr fun atomIndex _ => hmissed atomIndex
  have htotal := hsplit.hasClassTotals label
  rw [hempty, Finset.sum_empty] at htotal
  exact absurd htotal.symm (ne_of_gt (base.weight_pos label))

/-- **The parallel splitting of a design.**  Atoms are pulled back along `classOf`;
Parseval collapses fibrewise because the moment is constant on a class. -/
noncomputable def parallelSplitDesign (base : WeightedDesign baseSize rank)
    (classOf : Fin splitSize → Fin baseSize) (weight : Fin splitSize → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) : WeightedDesign splitSize rank where
  atom := fun atomIndex => base.atom (classOf atomIndex)
  weight := weight
  weight_pos := hsplit.hasPositiveWeights
  weight_sum_one := sum_weight_eq_one_of_isParallelSplitting hsplit
  isParseval := by
    rw [← Finset.sum_fiberwise Finset.univ classOf
      (fun atomIndex => weight atomIndex • atomMatrix (base.atom (classOf atomIndex))),
      ← base.isParseval]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [← hsplit.hasClassTotals label, Finset.sum_smul]
    refine Finset.sum_congr rfl fun atomIndex hmem => ?_
    rw [(Finset.mem_filter.mp hmem).2]

@[simp] theorem parallelSplitDesign_atom (base : WeightedDesign baseSize rank)
    (classOf : Fin splitSize → Fin baseSize) (weight : Fin splitSize → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) (atomIndex : Fin splitSize) :
    (parallelSplitDesign base classOf weight hsplit).atom atomIndex
      = base.atom (classOf atomIndex) := rfl

@[simp] theorem parallelSplitDesign_weight (base : WeightedDesign baseSize rank)
    (classOf : Fin splitSize → Fin baseSize) (weight : Fin splitSize → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) :
    (parallelSplitDesign base classOf weight hsplit).weight = weight := rfl

/-! ### Class-injective subsets carry the base Gram -/

/-- On a class-injective subset the atom sum is the base atom sum over the image
labels: the whole Loewner picture upstairs is the base picture, relabelled. -/
theorem subsetSum_parallelSplitDesign_of_injOn (base : WeightedDesign baseSize rank)
    (classOf : Fin splitSize → Fin baseSize) (weight : Fin splitSize → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) {C : Finset (Fin splitSize)}
    (hinjective : Set.InjOn classOf C) :
    subsetSum (parallelSplitDesign base classOf weight hsplit) C
      = subsetSum base (C.image classOf) := by
  rw [subsetSum, subsetSum, Finset.sum_image fun first hfirst second hsecond hequal =>
    hinjective hfirst hsecond hequal]
  rfl

theorem dominates_parallelSplitDesign_iff_of_injOn (base : WeightedDesign baseSize rank)
    (classOf : Fin splitSize → Fin baseSize) (weight : Fin splitSize → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) {C : Finset (Fin splitSize)}
    (hinjective : Set.InjOn classOf C) :
    Dominates (parallelSplitDesign base classOf weight hsplit) C
      ↔ Dominates base (C.image classOf) := by
  rw [Dominates, Dominates, subsetSum_parallelSplitDesign_of_injOn base classOf weight
    hsplit hinjective]

/-- A subset repeating a class carries two equal atoms. -/
theorem exists_repeated_class_of_not_injOn {classOf : Fin splitSize → Fin baseSize}
    {C : Finset (Fin splitSize)} (hnotInjective : ¬ Set.InjOn classOf C) :
    ∃ first ∈ C, ∃ second ∈ C, classOf first = classOf second ∧ first ≠ second := by
  by_contra hcontra
  refine hnotInjective fun first hfirst second hsecond hequal => ?_
  by_contra hdistinct
  exact hcontra ⟨first, Finset.mem_coe.mp hfirst, second, Finset.mem_coe.mp hsecond,
    hequal, hdistinct⟩

/-- **Repeating a class kills domination**, unconditionally: two equal atoms inside a
subset of size at most the rank leave a direction on which the gap form is negative. -/
theorem not_dominates_parallelSplitDesign_of_not_injOn (base : WeightedDesign baseSize rank)
    (classOf : Fin splitSize → Fin baseSize) (weight : Fin splitSize → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) {C : Finset (Fin splitSize)}
    (hcard : C.card ≤ rank) (hnotInjective : ¬ Set.InjOn classOf C) :
    ¬ Dominates (parallelSplitDesign base classOf weight hsplit) C := by
  obtain ⟨first, hfirst, second, hsecond, hequal, hdistinct⟩ :=
    exists_repeated_class_of_not_injOn hnotInjective
  refine not_dominates_of_repeated_atom_general _ hdistinct hfirst hsecond hcard ?_
  rw [parallelSplitDesign_atom, parallelSplitDesign_atom, hequal]

/-- **THE ACTIVITY LAW OF A SPLITTING.**  A subset of size at most the rank dominates
upstairs exactly when it is class-injective and its image dominates downstairs.  The
two failure modes are separated: the injective one is the base's business, the
non-injective one is unconditional. -/
theorem dominates_parallelSplitDesign_iff (base : WeightedDesign baseSize rank)
    (classOf : Fin splitSize → Fin baseSize) (weight : Fin splitSize → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) {C : Finset (Fin splitSize)}
    (hcard : C.card ≤ rank) :
    Dominates (parallelSplitDesign base classOf weight hsplit) C
      ↔ Set.InjOn classOf C ∧ Dominates base (C.image classOf) := by
  constructor
  · intro hdominates
    by_cases hinjective : Set.InjOn classOf C
    · exact ⟨hinjective, (dominates_parallelSplitDesign_iff_of_injOn base classOf weight
        hsplit hinjective).mp hdominates⟩
    · exact absurd hdominates (not_dominates_parallelSplitDesign_of_not_injOn base classOf
        weight hsplit hcard hinjective)
  · intro hpair
    exact (dominates_parallelSplitDesign_iff_of_injOn base classOf weight hsplit
      hpair.1).mpr hpair.2

/-! ### The splitting of a tie is a tie -/

/-- A section of `classOf` over a set of labels: distinct labels, distinct preimages,
and the image is the label set again. -/
theorem exists_injOn_preimage_of_surjective {classOf : Fin splitSize → Fin baseSize}
    (hsurjective : Function.Surjective classOf) (labelSet : Finset (Fin baseSize)) :
    ∃ C : Finset (Fin splitSize), C.card = labelSet.card ∧ Set.InjOn classOf C ∧
      C.image classOf = labelSet := by
  refine ⟨labelSet.image (Function.surjInv hsurjective), ?_, ?_, ?_⟩
  · exact Finset.card_image_of_injective _ (Function.injective_surjInv hsurjective)
  · intro first hfirst second hsecond hequal
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hfirst hsecond
    obtain ⟨firstLabel, _, hfirstEq⟩ := hfirst
    obtain ⟨secondLabel, _, hsecondEq⟩ := hsecond
    rw [← hfirstEq, ← hsecondEq] at hequal ⊢
    rw [Function.surjInv_eq hsurjective, Function.surjInv_eq hsurjective] at hequal
    rw [hequal]
  · rw [Finset.image_image,
      show classOf ∘ Function.surjInv hsurjective = id from
        funext fun label => Function.surjInv_eq hsurjective label,
      Finset.image_id]

/-- **A splitting of a tie is a tie**, over an arbitrary base.  The dominating subset
upstairs is a section of the base's; nothing dominates strictly because a
class-injective subset carries the base gap matrix and a class-repeating one is not
even weakly dominating.  For a single split this is the shipped
`Gtz.isTie_splitDesign_iff`; the content here is that the simultaneous form needs no
induction and comes with the activity law attached. -/
theorem parallelSplitDesign_isTie (base : WeightedDesign baseSize rank)
    (classOf : Fin splitSize → Fin baseSize) (weight : Fin splitSize → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) (hbase : IsTie base) :
    IsTie (parallelSplitDesign base classOf weight hsplit) := by
  obtain ⟨⟨labelSet, hlabelCard, hlabelDominates⟩, hnoStrict⟩ := hbase
  obtain ⟨C, hcard, hinjective, himage⟩ := exists_injOn_preimage_of_surjective
    (surjective_classOf_of_isParallelSplitting hsplit) labelSet
  refine ⟨⟨C, by rw [hcard, hlabelCard], ?_⟩, ?_⟩
  · rw [dominates_parallelSplitDesign_iff_of_injOn base classOf weight hsplit hinjective,
      himage]
    exact hlabelDominates
  · intro candidate hcandidateCard hposDef
    by_cases hcandidateInj : Set.InjOn classOf candidate
    · rw [Dominates, subsetSum_parallelSplitDesign_of_injOn base classOf weight hsplit
        hcandidateInj] at *
      exact hnoStrict (candidate.image classOf)
        (by rw [Finset.card_image_of_injOn hcandidateInj, hcandidateCard]) hposDef
    · exact not_dominates_parallelSplitDesign_of_not_injOn base classOf weight hsplit
        (le_of_eq hcandidateCard) hcandidateInj hposDef.posSemidef

/-! ### Activity is basis membership, at every splitting of a corank-one tie -/

/-- A class-repeating subset has two equal selected rows, so its selected-rows
determinant vanishes: it is not a basis of the direction matroid. -/
theorem det_subsetRowMatrix_parallelSplitDesign_eq_zero_of_not_injOn
    (base : WeightedDesign baseSize rank) (classOf : Fin splitSize → Fin baseSize)
    (weight : Fin splitSize → ℝ) (hsplit : IsParallelSplitting base classOf weight)
    {C : Finset (Fin splitSize)} (hcard : C.card = rank)
    (hnotInjective : ¬ Set.InjOn classOf C) :
    (subsetRowMatrix (parallelSplitDesign base classOf weight hsplit) C hcard).det = 0 := by
  obtain ⟨first, hfirst, second, hsecond, hequal, hdistinct⟩ :=
    exists_repeated_class_of_not_injOn hnotInjective
  obtain ⟨firstIndex, hfirstIndex⟩ := subsetPick_surjOn C hcard hfirst
  obtain ⟨secondIndex, hsecondIndex⟩ := subsetPick_surjOn C hcard hsecond
  refine Matrix.det_zero_of_row_eq (i := firstIndex) (j := secondIndex) ?_ ?_
  · intro hindexEqual
    exact hdistinct (by rw [← hfirstIndex, ← hsecondIndex, hindexEqual])
  · rw [subsetRowMatrix_row, subsetRowMatrix_row, hfirstIndex, hsecondIndex,
      parallelSplitDesign_atom, parallelSplitDesign_atom, hequal]

/-- **Class-injective is enough, at a corank-one base.**  Every `k`-subset meeting `k`
distinct classes of a split corank-one tie dominates — the image is a `k`-subset of the
base, and at corank one every one of those dominates. -/
theorem dominates_parallelSplitDesign_of_injOn_of_corankOne {rank splitSize : ℕ}
    (hrank : 1 ≤ rank) (base : WeightedDesign (rank + 1) rank) (hbase : IsTie base)
    (classOf : Fin splitSize → Fin (rank + 1)) (weight : Fin splitSize → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) {C : Finset (Fin splitSize)}
    (hcard : C.card = rank) (hinjective : Set.InjOn classOf C) :
    Dominates (parallelSplitDesign base classOf weight hsplit) C := by
  rw [dominates_parallelSplitDesign_iff_of_injOn base classOf weight hsplit hinjective]
  exact corankOne_isTie_dominates hrank base hbase
    (by rw [Finset.card_image_of_injOn hinjective, hcard])

/-- **EVERY BASIS IS ACTIVE, AT EVERY SPLITTING OF A CORANK-ONE TIE.**  A `k`-subset
of the splitting dominates exactly when it is a basis of the direction matroid.  The
shipped `Gtz.corankOne_isTie_dominates` is the case `splitSize = rank + 1`; this is
the same statement at every size and every weight vector, obtained by transfer and
not by re-proving anything about the base. -/
theorem dominates_parallelSplitDesign_iff_det_ne_zero_of_corankOne {rank splitSize : ℕ}
    (hrank : 1 ≤ rank) (base : WeightedDesign (rank + 1) rank) (hbase : IsTie base)
    (classOf : Fin splitSize → Fin (rank + 1)) (weight : Fin splitSize → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) {C : Finset (Fin splitSize)}
    (hcard : C.card = rank) :
    Dominates (parallelSplitDesign base classOf weight hsplit) C
      ↔ (subsetRowMatrix (parallelSplitDesign base classOf weight hsplit) C hcard).det ≠ 0 := by
  constructor
  · exact dominates_det_ne_zero _ C hcard
  · intro hdet
    have hinjective : Set.InjOn classOf C := by
      by_contra hnotInjective
      exact hdet (det_subsetRowMatrix_parallelSplitDesign_eq_zero_of_not_injOn base classOf
        weight hsplit hcard hnotInjective)
    exact dominates_parallelSplitDesign_of_injOn_of_corankOne hrank base hbase classOf weight
      hsplit hcard hinjective

/-- The same statement in its exact form: at a splitting of a corank-one tie every
basis sits at `lambda_min = 1` on the nose. -/
theorem exactlyTied_parallelSplitDesign_of_det_ne_zero_of_corankOne {rank splitSize : ℕ}
    (hrank : 1 ≤ rank) (base : WeightedDesign (rank + 1) rank) (hbase : IsTie base)
    (classOf : Fin splitSize → Fin (rank + 1)) (weight : Fin splitSize → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) {C : Finset (Fin splitSize)}
    (hcard : C.card = rank)
    (hdet : (subsetRowMatrix (parallelSplitDesign base classOf weight hsplit) C hcard).det ≠ 0) :
    Dominates (parallelSplitDesign base classOf weight hsplit) C ∧
      ¬ (subsetSum (parallelSplitDesign base classOf weight hsplit) C - 1).PosDef :=
  ⟨(dominates_parallelSplitDesign_iff_det_ne_zero_of_corankOne hrank base hbase classOf
      weight hsplit hcard).mpr hdet,
    (parallelSplitDesign_isTie base classOf weight hsplit hbase).2 C hcard⟩

/-! ### The shipped split-class family is a parallel splitting

`Gtz.splitClassDesign` puts on each atom the corank-one atom of its class evaluated at
the class totals; that is exactly the splitting of `Gtz.simplexTieDesign` along
`classOf`, so the two constructions are the same design and the activity law applies to
the shipped family verbatim. -/

theorem splitClass_isParallelSplitting {splitSize rank : ℕ} (hrank : 1 ≤ rank)
    (classOf : Fin splitSize → Fin (rank + 1)) (weight : Fin splitSize → ℝ)
    (hsurjective : Function.Surjective classOf) (hpos : ∀ atomIndex, 0 < weight atomIndex)
    (hsum : ∑ atomIndex, weight atomIndex = 1) :
    IsParallelSplitting (simplexTieDesign (classTotalWeight classOf weight) hrank
      (classTotalWeight_pos hsurjective hpos) (classTotalWeight_sum hsum)) classOf weight where
  hasPositiveWeights := hpos
  hasClassTotals := fun _ => rfl

theorem splitClassDesign_eq_parallelSplitDesign {splitSize rank : ℕ} (hrank : 1 ≤ rank)
    (classOf : Fin splitSize → Fin (rank + 1)) (weight : Fin splitSize → ℝ)
    (hsurjective : Function.Surjective classOf) (hpos : ∀ atomIndex, 0 < weight atomIndex)
    (hsum : ∑ atomIndex, weight atomIndex = 1) :
    splitClassDesign classOf weight hrank hsurjective hpos hsum
      = parallelSplitDesign (simplexTieDesign (classTotalWeight classOf weight) hrank
          (classTotalWeight_pos hsurjective hpos) (classTotalWeight_sum hsum)) classOf weight
          (splitClass_isParallelSplitting hrank classOf weight hsurjective hpos hsum) := rfl

/-- **Every class-injective `k`-subset of the split-class family dominates.**  Two
shipped steps: `Gtz.subsetSum_splitClassDesign_of_injOn` carries the subset sum down to
the corank-one section, and `Gtz.corankOne_isTie_dominates` says every `k`-subset there
dominates.  Neither is restated. -/
theorem splitClassDesign_dominates_of_injOn {splitSize rank : ℕ} (hrank : 1 ≤ rank)
    (classOf : Fin splitSize → Fin (rank + 1)) (weight : Fin splitSize → ℝ)
    (hsurjective : Function.Surjective classOf) (hpos : ∀ atomIndex, 0 < weight atomIndex)
    (hsum : ∑ atomIndex, weight atomIndex = 1) {C : Finset (Fin splitSize)}
    (hcard : C.card = rank) (hinjective : Set.InjOn classOf C) :
    Dominates (splitClassDesign classOf weight hrank hsurjective hpos hsum) C := by
  rw [Dominates, subsetSum_splitClassDesign_of_injOn classOf weight hrank hsurjective hpos
    hsum hinjective]
  exact corankOne_isTie_dominates hrank _
    (simplexTieDesign_isTie (classTotalWeight classOf weight) hrank
      (classTotalWeight_pos hsurjective hpos) (classTotalWeight_sum hsum))
    (by rw [Finset.card_image_of_injOn hinjective, hcard])

/-- **The split-class family has its active `k`-subsets exactly its bases**, at every
size, every partition and every weight vector.  The corank-one case `splitSize = rank+1`
is `Gtz.corankOne_isTie_det_ne_zero`; this is that statement transported along the
splitting. -/
theorem splitClassDesign_dominates_iff_det_ne_zero {splitSize rank : ℕ} (hrank : 1 ≤ rank)
    (classOf : Fin splitSize → Fin (rank + 1)) (weight : Fin splitSize → ℝ)
    (hsurjective : Function.Surjective classOf) (hpos : ∀ atomIndex, 0 < weight atomIndex)
    (hsum : ∑ atomIndex, weight atomIndex = 1) {C : Finset (Fin splitSize)}
    (hcard : C.card = rank) :
    Dominates (splitClassDesign classOf weight hrank hsurjective hpos hsum) C
      ↔ (subsetRowMatrix (splitClassDesign classOf weight hrank hsurjective hpos hsum)
          C hcard).det ≠ 0 := by
  rw [splitClassDesign_eq_parallelSplitDesign hrank classOf weight hsurjective hpos hsum]
  exact dominates_parallelSplitDesign_iff_det_ne_zero_of_corankOne hrank _
    (simplexTieDesign_isTie (classTotalWeight classOf weight) hrank
      (classTotalWeight_pos hsurjective hpos) (classTotalWeight_sum hsum))
    classOf weight _ hcard

/-- The exact form: every basis of a split-class design sits at `lambda_min = 1`. -/
theorem splitClassDesign_exactlyTied_of_injOn {splitSize rank : ℕ} (hrank : 1 ≤ rank)
    (classOf : Fin splitSize → Fin (rank + 1)) (weight : Fin splitSize → ℝ)
    (hsurjective : Function.Surjective classOf) (hpos : ∀ atomIndex, 0 < weight atomIndex)
    (hsum : ∑ atomIndex, weight atomIndex = 1) {C : Finset (Fin splitSize)}
    (hcard : C.card = rank) (hinjective : Set.InjOn classOf C) :
    Dominates (splitClassDesign classOf weight hrank hsurjective hpos hsum) C ∧
      ¬ (subsetSum (splitClassDesign classOf weight hrank hsurjective hpos hsum) C - 1).PosDef :=
  ⟨splitClassDesign_dominates_of_injOn hrank classOf weight hsurjective hpos hsum hcard
      hinjective,
    (splitClassDesign_isTie classOf weight hrank hsurjective hpos hsum).2 C hcard⟩

/-! ## The diamond at `(5,3)`: all eight bases are active

`Gtz.Design.DiamondPrimitive` proves the spine triple `{ab, ac, ad}` dominates and
that nothing dominates strictly.  The remaining seven spanning trees are here, each by
the exact two-square rational certificate of its gap form; the coefficients are the
pivots of an exact LDL decomposition of the gap matrix, so each certificate is an
identity, not an estimate.  The two triangles do not dominate: on the potential
constant along the triangle the gap form is the negative of the full Dirichlet form.
-/

/-- The gap-form evaluator shared by the eight certificates: expand the indicator form
at an explicit edge set. -/
theorem diamond_dominates_of_nonneg {edgeSet : Finset (Fin 5)}
    (hform : ∀ potential : Fin 3 → ℝ,
      0 ≤ potential ⬝ᵥ ((diamondData.selectedLaplacian edgeSet
        - diamondData.fullLaplacian) *ᵥ potential)) :
    Dominates diamondDesign edgeSet := by
  rw [diamondDesign, graphicDesign_dominates_iff]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun potential => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sub, diamondData.selectedLaplacian_transpose,
      diamondData.fullLaplacian_transpose]
  · rw [star_trivial]
    exact hform potential

/-- A STRICTLY negative direction refutes domination outright — the sharpening of
`Gtz.diamondGap_not_posDef_of_direction`, which refutes only STRICT domination. -/
theorem diamond_not_dominates_of_negative {edgeSet : Finset (Fin 5)}
    {potential : Fin 3 → ℝ}
    (hnegative : potential ⬝ᵥ ((diamondData.selectedLaplacian edgeSet
      - diamondData.fullLaplacian) *ᵥ potential) < 0) :
    ¬ Dominates diamondDesign edgeSet := by
  intro hdominates
  rw [diamondDesign, graphicDesign_dominates_iff] at hdominates
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 potential
  rw [star_trivial] at hnonneg
  linarith

theorem diamond_dominates_congr {left right : Finset (Fin 5)} (hsets : left = right)
    (hdominates : Dominates diamondDesign right) : Dominates diamondDesign left :=
  hsets ▸ hdominates

/-- spanning tree `{ab, ac, bd}`: `Q = (1/17)(17 y_a - 8 y_b - 12 y_c)^2 + (9/17)(5 y_b - y_c)^2`. -/
theorem diamondDesign_dominates_014 : Dominates diamondDesign ({0, 1, 4} : Finset (Fin 5)) :=
  diamond_dominates_of_nonneg fun potential => by
    rw [diamondGap_form_indicator]
    norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.cons_val, Finset.mem_insert,
      Finset.mem_singleton]
    nlinarith [sq_nonneg (17 * potential 0 - 8 * potential 1 - 12 * potential 2),
      sq_nonneg (5 * potential 1 - potential 2)]

/-- spanning tree `{ab, ad, bc}`: `Q = (1/17)(17 y_a - 8 y_b + 3 y_c)^2 + (9/17)(5 y_b - 4 y_c)^2`. -/
theorem diamondDesign_dominates_023 : Dominates diamondDesign ({0, 2, 3} : Finset (Fin 5)) :=
  diamond_dominates_of_nonneg fun potential => by
    rw [diamondGap_form_indicator]
    norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.cons_val, Finset.mem_insert,
      Finset.mem_singleton]
    nlinarith [sq_nonneg (17 * potential 0 - 8 * potential 1 + 3 * potential 2),
      sq_nonneg (5 * potential 1 - 4 * potential 2)]

/-- spanning tree `{ab, bc, bd}`, the star at `b`: `Q = (1/2)(2 y_a - 8 y_b + 3 y_c)^2 +
(9/2) y_c^2` — the mirror of the spine certificate under the Whitney twist. -/
theorem diamondDesign_dominates_034 : Dominates diamondDesign ({0, 3, 4} : Finset (Fin 5)) :=
  diamond_dominates_of_nonneg fun potential => by
    rw [diamondGap_form_indicator]
    norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.cons_val, Finset.mem_insert,
      Finset.mem_singleton]
    nlinarith [sq_nonneg (2 * potential 0 - 8 * potential 1 + 3 * potential 2),
      sq_nonneg (potential 2)]

/-- spanning tree `{ac, ad, bc}`: `Q = 6(y_a + y_b - 2 y_c)^2 + (4 y_a - y_b)^2`. -/
theorem diamondDesign_dominates_123 : Dominates diamondDesign ({1, 2, 3} : Finset (Fin 5)) :=
  diamond_dominates_of_nonneg fun potential => by
    rw [diamondGap_form_indicator]
    norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.cons_val, Finset.mem_insert,
      Finset.mem_singleton]
    nlinarith [sq_nonneg (potential 0 + potential 1 - 2 * potential 2),
      sq_nonneg (4 * potential 0 - potential 1)]

/-- spanning tree `{ac, ad, bd}`: `Q = (2/11)(11 y_a + y_b - 6 y_c)^2 + (3/11)(5 y_b + 3 y_c)^2`. -/
theorem diamondDesign_dominates_124 : Dominates diamondDesign ({1, 2, 4} : Finset (Fin 5)) :=
  diamond_dominates_of_nonneg fun potential => by
    rw [diamondGap_form_indicator]
    norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.cons_val, Finset.mem_insert,
      Finset.mem_singleton]
    nlinarith [sq_nonneg (11 * potential 0 + potential 1 - 6 * potential 2),
      sq_nonneg (5 * potential 1 + 3 * potential 2)]

/-- spanning tree `{ac, bc, bd}`: `Q = 6(y_a + y_b - 2 y_c)^2 + (y_a - 4 y_b)^2`. -/
theorem diamondDesign_dominates_134 : Dominates diamondDesign ({1, 3, 4} : Finset (Fin 5)) :=
  diamond_dominates_of_nonneg fun potential => by
    rw [diamondGap_form_indicator]
    norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.cons_val, Finset.mem_insert,
      Finset.mem_singleton]
    nlinarith [sq_nonneg (potential 0 + potential 1 - 2 * potential 2),
      sq_nonneg (potential 0 - 4 * potential 1)]

/-- spanning tree `{ad, bc, bd}`: `Q = (2/11)(y_a + 11 y_b - 6 y_c)^2 + (3/11)(5 y_a + 3 y_c)^2`. -/
theorem diamondDesign_dominates_234 : Dominates diamondDesign ({2, 3, 4} : Finset (Fin 5)) :=
  diamond_dominates_of_nonneg fun potential => by
    rw [diamondGap_form_indicator]
    norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.cons_val, Finset.mem_insert,
      Finset.mem_singleton]
    nlinarith [sq_nonneg (potential 0 + 11 * potential 1 - 6 * potential 2),
      sq_nonneg (5 * potential 0 + 3 * potential 2)]

/-! ### The two triangles are inactive -/

/-- CIRCUIT `{ab, ac, bc}`: at the potential constant on `{a,b,c}` the gap form is minus
the full Dirichlet form, `-6`. -/
theorem diamondDesign_not_dominates_013 :
    ¬ Dominates diamondDesign ({0, 1, 3} : Finset (Fin 5)) := by
  refine diamond_not_dominates_of_negative (potential := ![1, 1, 1]) ?_
  rw [diamondGap_form_indicator]
  norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons, Matrix.cons_val, Finset.mem_insert,
    Finset.mem_singleton]

/-- CIRCUIT `{ab, ad, bd}`: the same at the potential constant on `{a,b,d}`. -/
theorem diamondDesign_not_dominates_024 :
    ¬ Dominates diamondDesign ({0, 2, 4} : Finset (Fin 5)) := by
  refine diamond_not_dominates_of_negative (potential := ![0, 0, 1]) ?_
  rw [diamondGap_form_indicator]
  norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons, Matrix.cons_val, Finset.mem_insert,
    Finset.mem_singleton]

/-! ### The activity classification -/

/-- **Every triple but the two triangles dominates.**  Eight explicit certificates,
dispatched by the enumeration `Gtz.diamondDesign_no_strictDominator` uses on the other
side of the tie. -/
theorem diamondDesign_dominates_of_ne_circuits {edgeSet : Finset (Fin 5)}
    (hcard : edgeSet.card = 3) (hnotFirstCircuit : edgeSet ≠ {0, 1, 3})
    (hnotSecondCircuit : edgeSet ≠ {0, 2, 4}) : Dominates diamondDesign edgeSet := by
  obtain ⟨firstEdge, secondEdge, thirdEdge, hfirstSecond, hfirstThird, hsecondThird, rfl⟩ :=
    Finset.card_eq_three.mp hcard
  fin_cases firstEdge <;> fin_cases secondEdge <;> fin_cases thirdEdge <;>
    first
      | (exact absurd rfl hfirstSecond)
      | (exact absurd rfl hfirstThird)
      | (exact absurd rfl hsecondThird)
      | (exact absurd (by decide) hnotFirstCircuit)
      | (exact absurd (by decide) hnotSecondCircuit)
      | (exact diamond_dominates_congr (by decide) diamondDesign_dominates_spine)
      | (exact diamond_dominates_congr (by decide) diamondDesign_dominates_014)
      | (exact diamond_dominates_congr (by decide) diamondDesign_dominates_023)
      | (exact diamond_dominates_congr (by decide) diamondDesign_dominates_034)
      | (exact diamond_dominates_congr (by decide) diamondDesign_dominates_123)
      | (exact diamond_dominates_congr (by decide) diamondDesign_dominates_124)
      | (exact diamond_dominates_congr (by decide) diamondDesign_dominates_134)
      | (exact diamond_dominates_congr (by decide) diamondDesign_dominates_234)

/-- **THE DIAMOND'S ACTIVE TRIPLES, EXACTLY.**  A triple of the diamond design dominates
precisely when it is neither of the two triangles — eight of the ten. -/
theorem diamondDesign_dominates_iff {edgeSet : Finset (Fin 5)} (hcard : edgeSet.card = 3) :
    Dominates diamondDesign edgeSet ↔ edgeSet ≠ {0, 1, 3} ∧ edgeSet ≠ {0, 2, 4} := by
  constructor
  · intro hdominates
    exact ⟨fun hsets => diamondDesign_not_dominates_013 (hsets ▸ hdominates),
      fun hsets => diamondDesign_not_dominates_024 (hsets ▸ hdominates)⟩
  · intro hnotCircuit
    exact diamondDesign_dominates_of_ne_circuits hcard hnotCircuit.1 hnotCircuit.2

/-! ### The triangles are not spanning trees, so activity IS basis membership -/

/-- The triangle `{ab, ac, bc}` never reaches the ground: the potential constant `1` on
`{a,b,c}` is flat across all three of its edges yet differs from its grounded value. -/
theorem not_isGroundConnected_diamond_013 :
    ¬ IsGroundConnected diamondGraph ({0, 1, 3} : Finset (Fin 5)) := by
  intro hconnected
  have hflat : ∀ edge ∈ ({0, 1, 3} : Finset (Fin 5)),
      groundedPotential ![(1 : ℝ), 1, 1] (diamondData.graph.edgeTail edge)
        = groundedPotential ![(1 : ℝ), 1, 1] (diamondData.graph.edgeHead edge) := by
    intro edge hmem
    rw [← sub_eq_zero, ← diamondDrop_eq_grounded]
    fin_cases hmem <;> simp [diamondDrop, Matrix.cons_val]
  have hconstant := groundedPotential_eq_of_reachable hflat (hconnected 0)
  rw [groundedPotential_last, show (0 : Fin 4) = (0 : Fin 3).castSucc from rfl,
    groundedPotential_castSucc] at hconstant
  norm_num at hconstant

/-- The triangle `{ab, ad, bd}` never reaches the vertex `c`. -/
theorem not_isGroundConnected_diamond_024 :
    ¬ IsGroundConnected diamondGraph ({0, 2, 4} : Finset (Fin 5)) := by
  intro hconnected
  have hflat : ∀ edge ∈ ({0, 2, 4} : Finset (Fin 5)),
      groundedPotential ![(0 : ℝ), 0, 1] (diamondData.graph.edgeTail edge)
        = groundedPotential ![(0 : ℝ), 0, 1] (diamondData.graph.edgeHead edge) := by
    intro edge hmem
    rw [← sub_eq_zero, ← diamondDrop_eq_grounded]
    fin_cases hmem <;> simp [diamondDrop, Matrix.cons_val]
  have hconstant := groundedPotential_eq_of_reachable hflat (hconnected 2)
  rw [groundedPotential_last, show (2 : Fin 4) = (2 : Fin 3).castSucc from rfl,
    groundedPotential_castSucc] at hconstant
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hconstant

/-- **ACTIVITY IS BASIS MEMBERSHIP AT THE DIAMOND.**  A triple dominates exactly when it
is a spanning tree of `K4 - e`.  Forwards this is the shipped
`Gtz.isSpanningTree_of_dominates`; backwards it is the eight certificates, the two
triangles being the only triples that fail to reach the ground. -/
theorem diamondDesign_dominates_iff_isSpanningTree {edgeSet : Finset (Fin 5)}
    (hcard : edgeSet.card = 3) :
    Dominates diamondDesign edgeSet ↔ IsSpanningTree diamondGraph edgeSet := by
  constructor
  · intro hdominates
    exact isSpanningTree_of_dominates diamondData hcard hdominates
  · intro hspanning
    refine diamondDesign_dominates_of_ne_circuits hcard (fun hsets => ?_) fun hsets => ?_
    · exact not_isGroundConnected_diamond_013 (hsets ▸ hspanning.1)
    · exact not_isGroundConnected_diamond_024 (hsets ▸ hspanning.1)

/-- **THE DIAMOND TIE IS TOTAL.**  Every basis of its direction matroid sits at
`lambda_min = 1` exactly: it dominates, and it does not dominate strictly.  This is the
corank-two INSTANCE of the property `Gtz.Ties.TotalTieCorankOne` proves at corank one
and leaves open beyond it — an instance, not that theorem. -/
theorem diamondDesign_isTotalTie {edgeSet : Finset (Fin 5)} (hcard : edgeSet.card = 3)
    (hspanning : IsSpanningTree diamondGraph edgeSet) :
    Dominates diamondDesign edgeSet ∧ ¬ (subsetSum diamondDesign edgeSet - 1).PosDef :=
  ⟨(diamondDesign_dominates_iff_isSpanningTree hcard).mpr hspanning,
    diamondDesign_no_strictDominator edgeSet hcard⟩

/-! ## Splitting the diamond: exact ties at `(6,3)` and `(7,3)`

`Gtz.Design.DiamondPrimitive` mechanizes the `(5,3)` primitive and nothing above it, and
no module in the repository builds a splitting of it.  The transfer above supplies two,
with their activity attached: a triple upstairs dominates exactly when its three atoms
lie in three different classes and those classes form a spanning tree downstairs. -/

theorem diamondDesign_weight (edge : Fin 5) : diamondDesign.weight edge = 1 / 5 := by
  fin_cases edge <;> rfl

/-- Six atoms in the diamond's five classes: the spine is split in two. -/
def sixIntoFiveDiamond : Fin 6 → Fin 5 := ![0, 1, 2, 3, 4, 0]

/-- The split shares: the two spine copies carry `1/10` each. -/
noncomputable def sixSplitDiamondWeight : Fin 6 → ℝ := ![1/10, 1/5, 1/5, 1/5, 1/5, 1/10]

theorem sixSplitDiamond_isParallelSplitting :
    IsParallelSplitting diamondDesign sixIntoFiveDiamond sixSplitDiamondWeight where
  hasPositiveWeights := by
    intro atomIndex
    fin_cases atomIndex <;> simp [sixSplitDiamondWeight, Matrix.cons_val]
  hasClassTotals := by
    intro label
    rw [Finset.sum_filter, diamondDesign_weight]
    fin_cases label <;>
      simp [Fin.sum_univ_six, sixIntoFiveDiamond, sixSplitDiamondWeight, Matrix.cons_val,
        show (10 : ℝ)⁻¹ + 10⁻¹ = 5⁻¹ from by norm_num]

/-- **A `(6,3)` diamond class**: the diamond primitive with its spine split. -/
noncomputable def sixSplitDiamondDesign : WeightedDesign 6 3 :=
  parallelSplitDesign diamondDesign sixIntoFiveDiamond sixSplitDiamondWeight
    sixSplitDiamond_isParallelSplitting

/-- **The `(6,3)` diamond class is an exact tie.** -/
theorem sixSplitDiamondDesign_isTie : IsTie sixSplitDiamondDesign :=
  parallelSplitDesign_isTie diamondDesign sixIntoFiveDiamond sixSplitDiamondWeight
    sixSplitDiamond_isParallelSplitting diamondDesign_isTie

/-- **Its active triples, exactly**: three distinct classes forming a spanning tree. -/
theorem sixSplitDiamondDesign_dominates_iff {C : Finset (Fin 6)} (hcard : C.card = 3) :
    Dominates sixSplitDiamondDesign C ↔ Set.InjOn sixIntoFiveDiamond C ∧
      IsSpanningTree diamondGraph (C.image sixIntoFiveDiamond) := by
  rw [sixSplitDiamondDesign, dominates_parallelSplitDesign_iff diamondDesign
    sixIntoFiveDiamond sixSplitDiamondWeight sixSplitDiamond_isParallelSplitting
    (le_of_eq hcard)]
  constructor
  · intro hpair
    exact ⟨hpair.1, (diamondDesign_dominates_iff_isSpanningTree
      (by rw [Finset.card_image_of_injOn hpair.1, hcard])).mp hpair.2⟩
  · intro hpair
    exact ⟨hpair.1, (diamondDesign_dominates_iff_isSpanningTree
      (by rw [Finset.card_image_of_injOn hpair.1, hcard])).mpr hpair.2⟩

/-- Seven atoms in the diamond's five classes: the spine and one rim edge are split. -/
def sevenIntoFiveDiamond : Fin 7 → Fin 5 := ![0, 1, 2, 3, 4, 0, 1]

noncomputable def sevenSplitDiamondWeight : Fin 7 → ℝ :=
  ![1/10, 1/10, 1/5, 1/5, 1/5, 1/10, 1/10]

theorem sevenSplitDiamond_isParallelSplitting :
    IsParallelSplitting diamondDesign sevenIntoFiveDiamond sevenSplitDiamondWeight where
  hasPositiveWeights := by
    intro atomIndex
    fin_cases atomIndex <;> simp [sevenSplitDiamondWeight, Matrix.cons_val]
  hasClassTotals := by
    intro label
    rw [Finset.sum_filter, diamondDesign_weight]
    fin_cases label <;>
      simp [Fin.sum_univ_seven, sevenIntoFiveDiamond, sevenSplitDiamondWeight, Matrix.cons_val,
        show (10 : ℝ)⁻¹ + 10⁻¹ = 5⁻¹ from by norm_num]

/-- **A `(7,3)` diamond class**: the diamond primitive with two of its edges split. -/
noncomputable def sevenSplitDiamondDesign : WeightedDesign 7 3 :=
  parallelSplitDesign diamondDesign sevenIntoFiveDiamond sevenSplitDiamondWeight
    sevenSplitDiamond_isParallelSplitting

/-- **The `(7,3)` diamond class is an exact tie.** -/
theorem sevenSplitDiamondDesign_isTie : IsTie sevenSplitDiamondDesign :=
  parallelSplitDesign_isTie diamondDesign sevenIntoFiveDiamond sevenSplitDiamondWeight
    sevenSplitDiamond_isParallelSplitting diamondDesign_isTie

theorem sevenSplitDiamondDesign_dominates_iff {C : Finset (Fin 7)} (hcard : C.card = 3) :
    Dominates sevenSplitDiamondDesign C ↔ Set.InjOn sevenIntoFiveDiamond C ∧
      IsSpanningTree diamondGraph (C.image sevenIntoFiveDiamond) := by
  rw [sevenSplitDiamondDesign, dominates_parallelSplitDesign_iff diamondDesign
    sevenIntoFiveDiamond sevenSplitDiamondWeight sevenSplitDiamond_isParallelSplitting
    (le_of_eq hcard)]
  constructor
  · intro hpair
    exact ⟨hpair.1, (diamondDesign_dominates_iff_isSpanningTree
      (by rw [Finset.card_image_of_injOn hpair.1, hcard])).mp hpair.2⟩
  · intro hpair
    exact ⟨hpair.1, (diamondDesign_dominates_iff_isSpanningTree
      (by rw [Finset.card_image_of_injOn hpair.1, hcard])).mpr hpair.2⟩

/-- **The `(6,3)` diamond class has an inactive triple with three distinct classes.**  At
a splitting of a corank-one tie every class-injective triple dominates
(`dominates_parallelSplitDesign_of_injOn_of_corankOne`); here the lift of the triangle
`{ab, ac, bc}` is class-injective and does not.

This says nothing about ties at `(6,3)` in general: existence there is already
`Gtz.exists_isTie_six_three`, over every weight vector, in the corank-one family. -/
theorem exists_injOn_not_dominates_sixSplitDiamondDesign :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Set.InjOn sixIntoFiveDiamond C ∧
      ¬ Dominates sixSplitDiamondDesign C := by
  refine ⟨{0, 1, 3}, by decide, Finset.card_image_iff.mp (by decide), ?_⟩
  rw [sixSplitDiamondDesign, dominates_parallelSplitDesign_iff diamondDesign
    sixIntoFiveDiamond sixSplitDiamondWeight sixSplitDiamond_isParallelSplitting
    (by decide : ({0, 1, 3} : Finset (Fin 6)).card ≤ 3)]
  rintro ⟨-, hdominates⟩
  rw [show ({0, 1, 3} : Finset (Fin 6)).image sixIntoFiveDiamond = {0, 1, 3} from by decide]
    at hdominates
  exact diamondDesign_not_dominates_013 hdominates



/-- The five diamond directions sit on the first five atoms of the split. -/
theorem sixSplitDiamondDesign_atom_castSucc (atomIndex : Fin 5) :
    sixSplitDiamondDesign.atom atomIndex.castSucc = diamondDesign.atom atomIndex := by
  fin_cases atomIndex <;> rfl

/-- **THE `(6,3)` DIAMOND CLASS IS NOT A SPLITTING OF ANY CORANK-ONE DESIGN.**  Five of
its six atoms are the diamond's five directions, pairwise non-parallel by the shipped
`Gtz.not_hasParallelPair_diamondDesign`; a splitting into `rank + 1 = 4` classes has to
put two of those five in one class, and atoms in one class are EQUAL.  So the two
rank-three tie primitives stay apart after splitting: the diamond classes are outside
the classified corank-one family altogether, not merely different points of it. -/
theorem not_eq_parallelSplitDesign_corankOne_sixSplitDiamondDesign (base : WeightedDesign 4 3)
    (classOf : Fin 6 → Fin 4) (weight : Fin 6 → ℝ)
    (hsplit : IsParallelSplitting base classOf weight) :
    sixSplitDiamondDesign ≠ parallelSplitDesign base classOf weight hsplit := by
  intro hequal
  obtain ⟨first, second, hdistinct, hclass⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun index : Fin 5 => classOf index.castSucc)
      (by simp)
  refine not_hasParallelPair_diamondDesign ⟨first, second, 1, hdistinct, ?_⟩
  have hatom : ∀ index : Fin 5,
      diamondDesign.atom index = base.atom (classOf index.castSucc) := by
    intro index
    rw [← sixSplitDiamondDesign_atom_castSucc, hequal]
    rfl
  rw [one_smul, hatom first, hatom second, hclass]


end Gtz

/-
# The `(7,3)` tie locus around the split tetrahedron

`Gtz.Quantitative.DecisionAtlasSevenThree` builds the split-tetrahedron `(7,3)`
witness `splitSevenDesign` — exactly rational, exactly Parseval, every leverage
exactly `3` — and proves that `discriminantTie` sums to `-120` over the `35`
triples while its maximum is `0`, so averaging over triples is dead. This file
takes that object apart: where it comes from, what its boundary is, and which of
the campaign's tie laws survive at `m = 7`.

**It is a triple atom split of the regular tetrahedron.**
`tripleSplitTetraDesign_eq_splitSevenDesign` identifies the witness with
`replicatedDesign` applied three times to `tetraDesign` — halving the weight of
directions `0, 1, 2` in turn. Parseval and all-heaviness are then not
computations but inherited facts (`replicatedDesign_allHeavy`), and the witness
sits ON the size-monotonicity ladder of `Gtz.Reduction.RankFourWindow`: it is the
corank-one tetrahedron tie, pushed three rungs up to the size that carries the
whole of rank three.

**It is an exact tie, and nothing dominates strictly.** `splitSevenDesign_isTie`
is the first `IsTie` witness in the library at `(7,3)`. Three atoms carry at most
three of the four tetrahedron directions, and the missed direction is a null
direction of every `3`-subset's gap. Combined with the converse of the landed
rainbow lemma, `splitSevenDesign_dominates_iff_rainbowDirections` pins the
dominating triples EXACTLY: the `20` rainbow ones dominate, the `15`
direction-repeating ones do not, and none of the `35` dominates strictly.

**The tie is corank one, with a named spectrum.** At every rainbow triple the
three elementary symmetric functions of `Gram_T − I` are `(6, 9, 0)`, so its
characteristic polynomial factors as `lam (lam − 3)²`
(`splitSevenDesign_gapCharPoly_of_rainbowDirections`): the gap has spectrum
`{0, 3, 3}`, `Gram_T` has spectrum `{1, 4, 4}`, `sigma_min(Gram_T) = 1` and the
covering margin is exactly zero with corank exactly one.

**The corank-one tie law does NOT reach here.**
`isTie_iff_leverage_identity` decides `IsTie` at `m = k+1` by
`k t_c |g_c|² = (k−1) + t_c`; `leverage_identity_forces_corank_one` says no design
of any other size satisfies it. `splitSevenDesign_leverage_identity_fails`
exhibits the failure numerically — `9/8` against `17/8` — at a design that IS an
exact tie. So the `(7,3)` tie locus needs a different equation, and the one thing
that does transfer from the `(6,3)` analysis is the corank-one boundary
`4 P_cd² = a_c a_d`, which the witness satisfies on every rainbow pair
(`splitSevenDesign_pairingBoundary_of_differentDirection`) and violates on every
replica pair.

**Weight is invisible to the whole discriminant system.** `subsetSum`,
`Dominates`, `heavyExcess`, `atomPairing`, `discriminantTrace` and
`discriminantTie` depend on a design only through its atom family
(`dominates_congr_atom` and friends). So the three-parameter reweighting family
`splitSevenReweighted`, which redistributes weight inside each replica class,
consists entirely of exact ties with the very same `20` dominators and the very
same `-120` sum. At an asymmetric split it carries no stress certificate
(`exists_isTie_seven_without_stressCertificate`) — the `(7,3)` twin of the landed
`(6,3)` separation.

SCOPE, honestly. The numerics behind this file classify the all-heavy `(7,3)` tie
locus as exactly EIGHT reweighting orbits, one per rank-three series-parallel
matroid class on seven elements, each `6`-dimensional modulo `O(3)`. None of
that is mechanized here and none of it is proved anywhere: the exclusion of the
one non-series-parallel two-connected support (`K4`) is numerical only, and the
exclusion of non-graphic rank-three matroids rests on a blind search. What IS
mechanized is the single class the campaign already owned — `C4` with
multiplicities `(2,2,2,1)`, the witness's own — together with its exact
reweighting family. The measured claim that the `(6,3)` equations
`a_x a_y = 4 P_xy²` FAIL on five of the eight classes is likewise not mechanized;
here only the positive half is proved, on the witness's class, and the failure is
recorded as a caveat against reusing `Gtz.Ties.CorankOneTieCriterion` at `(7,3)`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.DecisionAtlasSevenThree
import Gtz.Reduction.RankFourWindow
import Gtz.Ties.TetrahedronCertifiedTie
import Gtz.Ties.SplitTetrahedronTie
import Gtz.Ties.CorankOneTieCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ### The discriminant system is weight-blind

Domination reads the unweighted atom sum, and every scalar of the discriminant
system is built from leverages and pairings. So two designs with the same atom
family are indistinguishable to the whole apparatus, however differently their
weight is distributed. This is what makes the reweighting directions of the tie
locus invisible to `DiscriminantCovering`, and it is the transport that carries
every fact proved at `splitSevenDesign` to its whole reweighting family. -/

section WeightBlind

variable {m : ℕ} {designLeft designRight : WeightedDesign m 3}

theorem subsetSum_congr_atom (hatom : designLeft.atom = designRight.atom)
    (C : Finset (Fin m)) : subsetSum designLeft C = subsetSum designRight C := by
  rw [subsetSum, subsetSum, hatom]

theorem dominates_congr_atom (hatom : designLeft.atom = designRight.atom)
    (C : Finset (Fin m)) : Dominates designLeft C ↔ Dominates designRight C := by
  rw [Dominates, Dominates, subsetSum_congr_atom hatom]

theorem allHeavy_congr_atom (hatom : designLeft.atom = designRight.atom) :
    AllHeavy designLeft ↔ AllHeavy designRight := by
  rw [AllHeavy, AllHeavy, hatom]

theorem isTie_congr_atom (hatom : designLeft.atom = designRight.atom) :
    IsTie designLeft ↔ IsTie designRight := by
  rw [IsTie, IsTie]
  constructor
  · rintro ⟨⟨C, hcard, hdominates⟩, hnoStrict⟩
    refine ⟨⟨C, hcard, (dominates_congr_atom hatom C).mp hdominates⟩, fun E hcardE hposDef => ?_⟩
    exact hnoStrict E hcardE (by rwa [subsetSum_congr_atom hatom])
  · rintro ⟨⟨C, hcard, hdominates⟩, hnoStrict⟩
    refine ⟨⟨C, hcard, (dominates_congr_atom hatom C).mpr hdominates⟩, fun E hcardE hposDef => ?_⟩
    exact hnoStrict E hcardE (by rwa [← subsetSum_congr_atom hatom])

theorem heavyExcess_congr_atom (hatom : designLeft.atom = designRight.atom)
    (atomIndex : Fin m) :
    heavyExcess designLeft atomIndex = heavyExcess designRight atomIndex := by
  rw [heavyExcess, heavyExcess, hatom]

theorem atomPairing_congr_atom (hatom : designLeft.atom = designRight.atom)
    (atomFirst atomSecond : Fin m) :
    atomPairing designLeft atomFirst atomSecond
      = atomPairing designRight atomFirst atomSecond := by
  rw [atomPairing, atomPairing, hatom]

theorem discriminantTrace_congr_atom (hatom : designLeft.atom = designRight.atom)
    (pivot pairFirst pairSecond : Fin m) :
    discriminantTrace designLeft pivot pairFirst pairSecond
      = discriminantTrace designRight pivot pairFirst pairSecond := by
  rw [discriminantTrace, discriminantTrace, heavyExcess_congr_atom hatom,
    heavyExcess_congr_atom hatom, heavyExcess_congr_atom hatom,
    atomPairing_congr_atom hatom, atomPairing_congr_atom hatom]

theorem discriminantTie_congr_atom (hatom : designLeft.atom = designRight.atom)
    (pivot pairFirst pairSecond : Fin m) :
    discriminantTie designLeft pivot pairFirst pairSecond
      = discriminantTie designRight pivot pairFirst pairSecond := by
  rw [discriminantTie, discriminantTie, heavyExcess_congr_atom hatom,
    heavyExcess_congr_atom hatom, heavyExcess_congr_atom hatom,
    atomPairing_congr_atom hatom, atomPairing_congr_atom hatom,
    atomPairing_congr_atom hatom]

end WeightBlind

/-! ### The witness is the regular tetrahedron, split three times

`replicatedDesign D which` halves the weight at `which` and gives the other half
to a fresh copy of the same vector. Applying it at directions `0`, `1`, `2` of
`tetraDesign` in turn walks `(4,3) → (5,3) → (6,3) → (7,3)` and lands exactly on
the campaign's `(7,3)` witness, weights `1/8, 1/8, 1/8, 1/4, 1/8, 1/8, 1/8`. -/

/-- The regular tetrahedron with directions `0, 1, 2` each split into two
equal-weight copies — three rungs of the size-monotonicity ladder. -/
noncomputable def tripleSplitTetraDesign : WeightedDesign 7 3 :=
  replicatedDesign (replicatedDesign (replicatedDesign tetraDesign 0) 1) 2

/-- The seven atoms of the triple split, read off the three `Fin.snoc` layers:
indices `0, 1, 2, 3` carry the four tetrahedron directions and `4, 5, 6`
replicate directions `0, 1, 2`. -/
theorem tripleSplitTetraDesign_atom (atomIndex : Fin 7) :
    tripleSplitTetraDesign.atom atomIndex = tetraAtom (splitSevenDirection atomIndex) := by
  fin_cases atomIndex
  · show (replicatedDesign (replicatedDesign (replicatedDesign tetraDesign 0) 1) 2).atom
        ((0 : Fin 6).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign (replicatedDesign tetraDesign 0) 1).atom ((0 : Fin 5).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign tetraDesign 0).atom ((0 : Fin 4).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    rfl
  · show (replicatedDesign (replicatedDesign (replicatedDesign tetraDesign 0) 1) 2).atom
        ((1 : Fin 6).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign (replicatedDesign tetraDesign 0) 1).atom ((1 : Fin 5).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign tetraDesign 0).atom ((1 : Fin 4).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    rfl
  · show (replicatedDesign (replicatedDesign (replicatedDesign tetraDesign 0) 1) 2).atom
        ((2 : Fin 6).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign (replicatedDesign tetraDesign 0) 1).atom ((2 : Fin 5).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign tetraDesign 0).atom ((2 : Fin 4).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    rfl
  · show (replicatedDesign (replicatedDesign (replicatedDesign tetraDesign 0) 1) 2).atom
        ((3 : Fin 6).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign (replicatedDesign tetraDesign 0) 1).atom ((3 : Fin 5).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign tetraDesign 0).atom ((3 : Fin 4).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    rfl
  · show (replicatedDesign (replicatedDesign (replicatedDesign tetraDesign 0) 1) 2).atom
        ((4 : Fin 6).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign (replicatedDesign tetraDesign 0) 1).atom ((4 : Fin 5).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign tetraDesign 0).atom (Fin.last 4) = _
    rw [replicatedDesign_atom_last]
    rfl
  · show (replicatedDesign (replicatedDesign (replicatedDesign tetraDesign 0) 1) 2).atom
        ((5 : Fin 6).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign (replicatedDesign tetraDesign 0) 1).atom (Fin.last 5) = _
    rw [replicatedDesign_atom_last]
    show (replicatedDesign tetraDesign 0).atom ((1 : Fin 4).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    rfl
  · show (replicatedDesign (replicatedDesign (replicatedDesign tetraDesign 0) 1) 2).atom
        (Fin.last 6) = _
    rw [replicatedDesign_atom_last]
    show (replicatedDesign (replicatedDesign tetraDesign 0) 1).atom ((2 : Fin 5).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    show (replicatedDesign tetraDesign 0).atom ((2 : Fin 4).castSucc) = _
    rw [replicatedDesign_atom_castSucc]
    rfl

/-- The seven weights of the triple split: the three split directions carry
`1/8` in each copy and the unsplit direction `3` keeps its `1/4`. -/
theorem tripleSplitTetraDesign_weight (atomIndex : Fin 7) :
    tripleSplitTetraDesign.weight atomIndex = splitSevenDesign.weight atomIndex := by
  fin_cases atomIndex <;>
    simp [tripleSplitTetraDesign, replicatedDesign, replicatedWeights, Fin.snoc,
      tetraDesign, splitSevenDesign, Function.update] <;>
    norm_num

/-- **THE WITNESS IS A TRIPLE ATOM SPLIT OF THE REGULAR TETRAHEDRON.** The
campaign's `(7,3)` object is not a new design: it is `tetraDesign` with three of
its four directions halved, so its Parseval identity, its weight sum and its
all-heaviness are inherited rather than computed, and it lies on the ladder that
carries `GtzWeighted 7 3` down to `GtzWeighted 4 3`. -/
theorem tripleSplitTetraDesign_eq_splitSevenDesign :
    tripleSplitTetraDesign = splitSevenDesign := by
  refine WeightedDesign.ext ?_ ?_
  · funext atomIndex
    rw [tripleSplitTetraDesign_atom, splitSevenDesign_atom]
  · funext atomIndex
    exact tripleSplitTetraDesign_weight atomIndex

/-- **All-heaviness by inheritance.** Splitting duplicates the atom VECTOR and
touches only its weight, so the leverage multiset never changes: three
applications of `replicatedDesign_allHeavy` carry the tetrahedron's all-heaviness
to the `(7,3)` witness without evaluating a single inner product. Rewriting along
`tripleSplitTetraDesign_eq_splitSevenDesign` re-derives the landed
`splitSevenDesign_allHeavy` from the tetrahedron alone. -/
theorem tripleSplitTetraDesign_allHeavy : AllHeavy tripleSplitTetraDesign :=
  replicatedDesign_allHeavy _ 2
    (replicatedDesign_allHeavy _ 1
      (replicatedDesign_allHeavy tetraDesign 0 tetraDesign_allHeavy))

/-! ### The witness is an exact tie: nothing dominates strictly

Four directions, three atoms: every `3`-subset misses a tetrahedron direction,
and the missed direction is a null direction of the subset's gap, because each
selected atom pairs with it to `(±1)² = 1` and `|v_d|² = 3`. This is the
tetrahedron's own tie argument, transported along the replica map. -/

/-- Three atoms cover at most three of the four tetrahedron directions. -/
theorem exists_unusedDirection_seven (atomOne atomTwo atomThree : Fin 7) :
    ∃ unusedDir : Fin 4, splitSevenDirection atomOne ≠ unusedDir
      ∧ splitSevenDirection atomTwo ≠ unusedDir
      ∧ splitSevenDirection atomThree ≠ unusedDir := by
  decide +revert

/-- The gap of any `3`-subset vanishes at every direction the subset does not
carry: three pairings of `(±1)² = 1` against `|v_d|² = 3`. -/
theorem splitSevenDesign_gapForm_zero_of_unusedDirection {C : Finset (Fin 7)}
    (hcard : C.card = 3) {unusedDir : Fin 4}
    (hunused : ∀ atomIndex ∈ C, splitSevenDirection atomIndex ≠ unusedDir) :
    tetraAtom unusedDir
        ⬝ᵥ ((subsetSum splitSevenDesign C - 1) *ᵥ tetraAtom unusedDir) = 0 := by
  rw [dominationGap_form]
  have hone : ∀ atomIndex ∈ C,
      (splitSevenDesign.atom atomIndex ⬝ᵥ tetraAtom unusedDir) ^ 2 = 1 := by
    intro atomIndex hmem
    rw [splitSevenDesign_atom]
    exact tetraAtom_dot_sq_of_ne (hunused atomIndex hmem)
  rw [Finset.sum_congr rfl hone, Finset.sum_const, hcard, tetraAtom_dot_self,
    nsmul_eq_mul]
  norm_num

/-- **No `3`-subset of the witness dominates strictly.** Every triple misses a
tetrahedron direction, and the gap form vanishes there. -/
theorem splitSevenDesign_no_strictDominator (C : Finset (Fin 7)) (hcard : C.card = 3) :
    ¬ (subsetSum splitSevenDesign C - 1).PosDef := by
  intro hposDef
  obtain ⟨atomOne, atomTwo, atomThree, honeTwo, honeThree, htwoThree, rfl⟩ :=
    Finset.card_eq_three.mp hcard
  obtain ⟨unusedDir, hdirOne, hdirTwo, hdirThree⟩ :=
    exists_unusedDirection_seven atomOne atomTwo atomThree
  have hunused : ∀ atomIndex ∈ ({atomOne, atomTwo, atomThree} : Finset (Fin 7)),
      splitSevenDirection atomIndex ≠ unusedDir := by
    intro atomIndex hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem
    · exact hdirOne
    rcases Finset.mem_insert.mp hmem with rfl | hmem
    · exact hdirTwo
    · exact (Finset.mem_singleton.mp hmem) ▸ hdirThree
  have hzero := splitSevenDesign_gapForm_zero_of_unusedDirection hcard hunused
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2
    (tetraAtom_ne_zero unusedDir)
  rw [star_trivial, hzero] at hpos
  exact lt_irrefl 0 hpos

/-- **THE `(7,3)` WITNESS IS AN EXACT TIE.** Some triple dominates and none
dominates strictly — the first `IsTie` witness in the library at the size that
carries the whole of rank three. The covering margin at this design is exactly
zero, not merely nonpositive: the maximum over the `35` triples is ATTAINED, at
each of the `20` rainbow ones. -/
theorem splitSevenDesign_isTie : IsTie splitSevenDesign :=
  ⟨⟨{0, 1, 2}, by decide, splitSevenDesign_dominates_zeroOneTwo⟩,
    splitSevenDesign_no_strictDominator⟩

/-- **Each of the `20` rainbow triples is itself a TIE**: it dominates weakly and
its gap is not positive definite. So the `20` are not merely dominators with a
zero determinant leg — they are exact equality cases, and the covering has no
slack anywhere at this design. -/
theorem splitSevenDesign_rainbowTriple_isTie {pivot pairFirst pairSecond : Fin 7}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond)
    (hdirPivotFirst : splitSevenDirection pivot ≠ splitSevenDirection pairFirst)
    (hdirPivotSecond : splitSevenDirection pivot ≠ splitSevenDirection pairSecond)
    (hdirPair : splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond) :
    Dominates splitSevenDesign {pivot, pairFirst, pairSecond}
      ∧ ¬ (subsetSum splitSevenDesign {pivot, pairFirst, pairSecond} - 1).PosDef := by
  refine ⟨splitSevenDesign_dominates_of_rainbowDirections hpivotFirst hpivotSecond
    hpairDistinct hdirPivotFirst hdirPivotSecond hdirPair,
    splitSevenDesign_no_strictDominator _ ?_⟩
  rw [Finset.card_insert_of_notMem (by simp [hpivotFirst, hpivotSecond]),
    Finset.card_insert_of_notMem (by simp [hpairDistinct]), Finset.card_singleton]

/-! ### The dominating triples are EXACTLY the twenty rainbow ones

The landed lemmas give the two values of `discriminantTie` and the domination of
rainbow triples. The converse — that a direction-repeating triple does NOT
dominate — closes the classification, and turns `rainbowTriplesSeven_card` into
an exact count of the dominating subsets. -/

/-- A triple repeating a direction fails to dominate: its tie leg is `-8`, and
the narrowing is an equivalence at an all-heavy pivot. -/
theorem splitSevenDesign_not_dominates_of_repeatedDirection
    {pivot pairFirst pairSecond : Fin 7} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hrepeat : splitSevenDirection pivot = splitSevenDirection pairFirst
        ∨ splitSevenDirection pivot = splitSevenDirection pairSecond
        ∨ splitSevenDirection pairFirst = splitSevenDirection pairSecond) :
    ¬ Dominates splitSevenDesign {pivot, pairFirst, pairSecond} := by
  intro hdominates
  have hlegs := (dominates_triple_iff_discriminantSystem splitSevenDesign hpivotFirst
    hpivotSecond hpairDistinct (splitSevenDesign_allHeavy pivot)).mp hdominates
  rw [splitSevenDesign_discriminantTie_of_repeatedDirection hpivotFirst hpivotSecond
    hpairDistinct hrepeat] at hlegs
  linarith [hlegs.2]

/-- **DOMINATION AT THE WITNESS IS EXACTLY RAINBOWNESS.** A triple of distinct
atoms dominates if and only if its three atoms carry three distinct tetrahedron
directions. With `rainbowTriplesSeven_card` and `repeatedTriplesSeven_card` this
says: exactly `20` of the `35` triples dominate, exactly `15` do not, and
`splitSevenDesign_no_strictDominator` says none of the `20` has any slack. -/
theorem splitSevenDesign_dominates_iff_rainbowDirections
    {pivot pairFirst pairSecond : Fin 7} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    Dominates splitSevenDesign {pivot, pairFirst, pairSecond}
      ↔ (splitSevenDirection pivot ≠ splitSevenDirection pairFirst
          ∧ splitSevenDirection pivot ≠ splitSevenDirection pairSecond
          ∧ splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond) := by
  constructor
  · intro hdominates
    refine ⟨fun hsame => ?_, fun hsame => ?_, fun hsame => ?_⟩
    · exact splitSevenDesign_not_dominates_of_repeatedDirection hpivotFirst
        hpivotSecond hpairDistinct (Or.inl hsame) hdominates
    · exact splitSevenDesign_not_dominates_of_repeatedDirection hpivotFirst
        hpivotSecond hpairDistinct (Or.inr (Or.inl hsame)) hdominates
    · exact splitSevenDesign_not_dominates_of_repeatedDirection hpivotFirst
        hpivotSecond hpairDistinct (Or.inr (Or.inr hsame)) hdominates
  · rintro ⟨hdirPivotFirst, hdirPivotSecond, hdirPair⟩
    exact splitSevenDesign_dominates_of_rainbowDirections hpivotFirst hpivotSecond
      hpairDistinct hdirPivotFirst hdirPivotSecond hdirPair

/-- The classification, read over the canonical index set of the `35` triples. -/
theorem splitSevenDesign_dominates_iff_hasRainbowDirections
    {triple : Fin 7 × Fin 7 × Fin 7} (hmem : triple ∈ increasingTriplesSeven) :
    Dominates splitSevenDesign {triple.1, triple.2.1, triple.2.2}
      ↔ HasRainbowDirections triple := by
  obtain ⟨hpivotFirst, hpivotSecond, hpairDistinct⟩ :=
    increasingTriplesSeven_distinct hmem
  exact splitSevenDesign_dominates_iff_rainbowDirections hpivotFirst hpivotSecond
    hpairDistinct

/-! ### The tie is corank one, with a named spectrum

At a rainbow triple the three elementary symmetric functions of `N_T = Gram_T − I`
are `e_1 = 6` (three heavy excesses of `2`), `e_2 = 9`
(`discriminantMinorSum`) and `e_3 = 0` (`discriminantTie`). The characteristic
polynomial therefore factors completely over the rationals. -/

/-- The first symmetric function of `Gram_T − I` is `6` at every triple: every
heavy excess of the witness is `2`. -/
theorem splitSevenDesign_excessSum (pivot pairFirst pairSecond : Fin 7) :
    heavyExcess splitSevenDesign pivot + heavyExcess splitSevenDesign pairFirst
        + heavyExcess splitSevenDesign pairSecond = 6 := by
  rw [splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess,
    splitSevenDesign_heavyExcess]
  norm_num

/-- The second symmetric function of `Gram_T − I` is `9` at every rainbow triple:
three `2·2 − (−1)² = 3` minors. -/
theorem splitSevenDesign_discriminantMinorSum_of_rainbowDirections
    {pivot pairFirst pairSecond : Fin 7}
    (hdirPivotFirst : splitSevenDirection pivot ≠ splitSevenDirection pairFirst)
    (hdirPivotSecond : splitSevenDirection pivot ≠ splitSevenDirection pairSecond)
    (hdirPair : splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond) :
    discriminantMinorSum splitSevenDesign pivot pairFirst pairSecond = 9 := by
  rw [discriminantMinorSum, splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess,
    splitSevenDesign_heavyExcess,
    splitSevenDesign_atomPairing_of_differentDirection hdirPivotFirst,
    splitSevenDesign_atomPairing_of_differentDirection hdirPivotSecond,
    splitSevenDesign_atomPairing_of_differentDirection hdirPair]
  norm_num

/-- **THE TIE IS CORANK ONE, WITH SPECTRUM `{0, 3, 3}`.** The characteristic
polynomial of `Gram_T − I` at a rainbow triple, written from its three elementary
symmetric functions `(6, 9, 0)`, factors as `lam (lam − 3)²` over the rationals.
Together with `splitSevenDesign_rainbowTriple_isTie`, which says the gap is
positive semidefinite and singular, that pins the spectrum: eigenvalues
`{0, 3, 3}`, kernel exactly one-dimensional, `Gram_T` with spectrum `{1, 4, 4}`,
`sigma_min(Gram_T) = 1` exactly, and a covering margin of zero with slack in
every direction but one. -/
theorem splitSevenDesign_gapCharPoly_of_rainbowDirections
    {pivot pairFirst pairSecond : Fin 7}
    (hdirPivotFirst : splitSevenDirection pivot ≠ splitSevenDirection pairFirst)
    (hdirPivotSecond : splitSevenDirection pivot ≠ splitSevenDirection pairSecond)
    (hdirPair : splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond)
    (eigenvalue : ℝ) :
    eigenvalue ^ 3
        - (heavyExcess splitSevenDesign pivot + heavyExcess splitSevenDesign pairFirst
            + heavyExcess splitSevenDesign pairSecond) * eigenvalue ^ 2
        + discriminantMinorSum splitSevenDesign pivot pairFirst pairSecond * eigenvalue
        - discriminantTie splitSevenDesign pivot pairFirst pairSecond
      = eigenvalue * (eigenvalue - 3) ^ 2 := by
  rw [splitSevenDesign_excessSum,
    splitSevenDesign_discriminantMinorSum_of_rainbowDirections hdirPivotFirst
      hdirPivotSecond hdirPair,
    splitSevenDesign_discriminantTie_of_rainbowDirections hdirPivotFirst
      hdirPivotSecond hdirPair]
  ring

/-! ### The corank-one boundary equation, and where it stops

`Gtz.Ties.CorankOneTieCriterion` analysed the `(6,3)` tie stratum through the
equation `4 P_cd² = a_c a_d` on all three pairs, with the normalized correlation
exactly `-1/2`. The witness satisfies it on every rainbow pair — it sits at a
CORNER of the symmetric-`1/2` radius box of `dominates_of_radiusBox`, which is
why the constant `4` of `dominates_of_dominantPairings` is sharp. It fails on
every replica pair by a factor of nine. -/

/-- **The rainbow pairs sit exactly ON the corank-one boundary**: `4 P² = a·a`,
i.e. normalized correlation `-1/2`, on every pair of atoms carrying different
tetrahedron directions. -/
theorem splitSevenDesign_pairingBoundary_of_differentDirection
    {atomFirst atomSecond : Fin 7}
    (hdifferent : splitSevenDirection atomFirst ≠ splitSevenDirection atomSecond) :
    4 * atomPairing splitSevenDesign atomFirst atomSecond ^ 2
      = heavyExcess splitSevenDesign atomFirst * heavyExcess splitSevenDesign atomSecond := by
  rw [splitSevenDesign_atomPairing_of_differentDirection hdifferent,
    splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess]
  norm_num

/-- The normalized pairing at a rainbow pair is exactly `-1/2` — sign included,
where the squared boundary equation above sees only the magnitude. All three
pairs of a rainbow triple carry it, so the normalized Gram of the gap is exactly
the `(6,3)` tie matrix `[[1,-1/2,-1/2],[-1/2,1,-1/2],[-1/2,-1/2,1]]`: corank one,
null vector `(1,1,1)`, recovered verbatim at `(7,3)`. -/
theorem splitSevenDesign_normalizedPairing_of_differentDirection
    {atomFirst atomSecond : Fin 7}
    (hdifferent : splitSevenDirection atomFirst ≠ splitSevenDirection atomSecond) :
    atomPairing splitSevenDesign atomFirst atomSecond
      = -(1/2) * heavyExcess splitSevenDesign atomFirst := by
  rw [splitSevenDesign_atomPairing_of_differentDirection hdifferent,
    splitSevenDesign_heavyExcess]
  norm_num

/-- **The boundary equation fails on replica pairs**, by a factor of nine:
`4 · 3² = 36` against `2 · 2 = 4`. So the equation is not a property of the
design but of its rainbow pairs, and the `15` failing triples are exactly the
ones that leave the box. -/
theorem splitSevenDesign_pairingBoundary_fails_of_sameDirection
    {atomFirst atomSecond : Fin 7}
    (hsame : splitSevenDirection atomFirst = splitSevenDirection atomSecond) :
    heavyExcess splitSevenDesign atomFirst * heavyExcess splitSevenDesign atomSecond
      < 4 * atomPairing splitSevenDesign atomFirst atomSecond ^ 2 := by
  rw [splitSevenDesign_atomPairing_of_sameDirection hsame, splitSevenDesign_heavyExcess,
    splitSevenDesign_heavyExcess]
  norm_num

/-! ### The corank-one tie law does not reach `(7,3)`

`isTie_iff_leverage_identity` decides `IsTie` at `m = k+1` by
`k t_c |g_c|² = (k−1) + t_c`, and `leverage_identity_forces_corank_one` shows the
identity is a corank-one law: no design of any other size satisfies it at every
atom. At `(7,3)` that is a hard negative, and the witness makes it concrete —
it IS an exact tie and it DOES fail the law, at every one of its six split
atoms. -/

/-- No `(7,3)` design satisfies the corank-one leverage identity at every atom —
`7 ≠ 3 + 1`. -/
theorem no_leverage_identity_at_seven_three (D : WeightedDesign 7 3) :
    ¬ ∀ atomIndex, ((3 : ℕ) : ℝ) * D.weight atomIndex * leverageOf (D.atom atomIndex)
      = (((3 : ℕ) : ℝ) - 1) + D.weight atomIndex := by
  intro hlaw
  have hforced := leverage_identity_forces_corank_one D (by norm_num) hlaw
  omega

/-- The failure, numerically: at atom `0` the law reads `3 · (1/8) · 3 = 9/8`
against `2 + 1/8 = 17/8`. -/
theorem splitSevenDesign_leverage_identity_fails :
    ((3 : ℕ) : ℝ) * splitSevenDesign.weight 0 * leverageOf (splitSevenDesign.atom 0)
      ≠ (((3 : ℕ) : ℝ) - 1) + splitSevenDesign.weight 0 := by
  rw [splitSevenDesign_leverage]
  simp only [splitSevenDesign, Matrix.cons_val_zero]
  norm_num

/-- **AN ALL-HEAVY `(7,3)` EXACT TIE THAT FAILS THE CORANK-ONE LAW.** The
criterion of `Gtz.Ties.CorankOneTieCriterion` sees none of the `(7,3)` tie locus,
so the equation governing ties at the size that carries rank three has a
different shape. The numerics behind this file say that shape is matroidal —
eight series-parallel classes, each a reweighting orbit — but nothing of that is
proved here; what is proved is that the corank-one equation is not it. -/
theorem exists_allHeavy_isTie_and_leverage_identity_fails_at_seven :
    ∃ D : WeightedDesign 7 3, AllHeavy D ∧ IsTie D ∧
      ¬ ∀ atomIndex, ((3 : ℕ) : ℝ) * D.weight atomIndex * leverageOf (D.atom atomIndex)
        = (((3 : ℕ) : ℝ) - 1) + D.weight atomIndex :=
  ⟨splitSevenDesign, splitSevenDesign_allHeavy, splitSevenDesign_isTie,
    no_leverage_identity_at_seven_three splitSevenDesign⟩

/-! ### The reweighting directions of the tie locus

Within each replica class the two atoms carry the SAME vector, so the class's
weight may be redistributed arbitrarily without disturbing Parseval. The
resulting three-parameter family has one atom family — hence, by weight
blindness, one discriminant system, one set of dominators and one `-120` sum.
These are the flat directions the numerics measure as invisible to the covering:
they move the design and leave every quantity the covering reads fixed. -/

section Reweighting

variable (splitZero splitOne splitTwo : ℝ)

/-- The reweighted split tetrahedron: directions `0, 1, 2` split their `1/4` as
`s + (1/4 − s)` independently, direction `3` keeps its `1/4`. At
`(1/8, 1/8, 1/8)` this is the campaign's witness. -/
noncomputable def splitSevenReweighted (hzeroPos : 0 < splitZero)
    (hzeroLt : splitZero < 1/4) (honePos : 0 < splitOne) (honeLt : splitOne < 1/4)
    (htwoPos : 0 < splitTwo) (htwoLt : splitTwo < 1/4) : WeightedDesign 7 3 where
  atom := splitSevenAtom
  weight := ![splitZero, splitOne, splitTwo, 1/4, 1/4 - splitZero, 1/4 - splitOne,
    1/4 - splitTwo]
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex
    · exact hzeroPos
    · exact honePos
    · exact htwoPos
    · exact (by norm_num : (0 : ℝ) < 1/4)
    · exact (by linarith : (0 : ℝ) < 1/4 - splitZero)
    · exact (by linarith : (0 : ℝ) < 1/4 - splitOne)
    · exact (by linarith : (0 : ℝ) < 1/4 - splitTwo)
  weight_sum_one := by
    simp only [Fin.sum_univ_seven, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    ring
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_seven, smul_eq_mul, splitSevenAtom, splitSevenDirection, tetraAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> simp <;> ring

variable (hzeroPos : 0 < splitZero) (hzeroLt : splitZero < 1/4)
  (honePos : 0 < splitOne) (honeLt : splitOne < 1/4) (htwoPos : 0 < splitTwo)
  (htwoLt : splitTwo < 1/4)

/-- Every member of the family carries the witness's own atoms. -/
theorem splitSevenReweighted_atom :
    (splitSevenReweighted splitZero splitOne splitTwo hzeroPos hzeroLt honePos honeLt
        htwoPos htwoLt).atom = splitSevenDesign.atom := rfl

/-- All-heaviness is an atom property, so it holds throughout the family. -/
theorem splitSevenReweighted_allHeavy :
    AllHeavy (splitSevenReweighted splitZero splitOne splitTwo hzeroPos hzeroLt honePos
      honeLt htwoPos htwoLt) :=
  (allHeavy_congr_atom (splitSevenReweighted_atom splitZero splitOne splitTwo hzeroPos
    hzeroLt honePos honeLt htwoPos htwoLt)).mpr splitSevenDesign_allHeavy

/-- The tie leg is unmoved by reweighting. -/
theorem splitSevenReweighted_discriminantTie (pivot pairFirst pairSecond : Fin 7) :
    discriminantTie (splitSevenReweighted splitZero splitOne splitTwo hzeroPos hzeroLt
        honePos honeLt htwoPos htwoLt) pivot pairFirst pairSecond
      = discriminantTie splitSevenDesign pivot pairFirst pairSecond :=
  discriminantTie_congr_atom (splitSevenReweighted_atom splitZero splitOne splitTwo
    hzeroPos hzeroLt honePos honeLt htwoPos htwoLt) pivot pairFirst pairSecond

/-- The trace leg is unmoved by reweighting. -/
theorem splitSevenReweighted_discriminantTrace (pivot pairFirst pairSecond : Fin 7) :
    discriminantTrace (splitSevenReweighted splitZero splitOne splitTwo hzeroPos hzeroLt
        honePos honeLt htwoPos htwoLt) pivot pairFirst pairSecond
      = discriminantTrace splitSevenDesign pivot pairFirst pairSecond :=
  discriminantTrace_congr_atom (splitSevenReweighted_atom splitZero splitOne splitTwo
    hzeroPos hzeroLt honePos honeLt htwoPos htwoLt) pivot pairFirst pairSecond

/-- **THE `-120` SUM IS CONSTANT ALONG THE REPLICA-SPLITTING DIRECTIONS.** Every
member of the family carries the same tie multiset — `20` zeros and `15` copies
of `-8` — so the averaging refutation holds along the whole flat direction, not
just at the symmetric point.

The qualifier is essential and is exactly where the numerics disagree with a
naive reading: only redistribution INSIDE a replica class is atom-preserving.
Changing the weight a DIRECTION carries forces the atoms to move to restore
Parseval, and the sum moves with them — the measurements report `-112` at the
uniform-weight points of the tie classes. So `e_3(N)` is a coordinate along the
tie locus, not an invariant of it. -/
theorem splitSevenReweighted_discriminantTie_sum :
    ∑ triple ∈ increasingTriplesSeven,
        discriminantTie (splitSevenReweighted splitZero splitOne splitTwo hzeroPos
          hzeroLt honePos honeLt htwoPos htwoLt) triple.1 triple.2.1 triple.2.2
      = -120 := by
  rw [Finset.sum_congr rfl fun triple _ =>
    splitSevenReweighted_discriminantTie splitZero splitOne splitTwo hzeroPos hzeroLt
      honePos honeLt htwoPos htwoLt triple.1 triple.2.1 triple.2.2]
  exact splitSevenDesign_discriminantTie_sum

/-- **Every member of the family is an exact tie**, with exactly the same `20`
dominating triples. -/
theorem splitSevenReweighted_isTie :
    IsTie (splitSevenReweighted splitZero splitOne splitTwo hzeroPos hzeroLt honePos
      honeLt htwoPos htwoLt) :=
  (isTie_congr_atom (splitSevenReweighted_atom splitZero splitOne splitTwo hzeroPos
    hzeroLt honePos honeLt htwoPos htwoLt)).mpr splitSevenDesign_isTie

theorem splitSevenReweighted_dominates_iff_rainbowDirections
    {pivot pairFirst pairSecond : Fin 7} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    Dominates (splitSevenReweighted splitZero splitOne splitTwo hzeroPos hzeroLt honePos
        honeLt htwoPos htwoLt) {pivot, pairFirst, pairSecond}
      ↔ (splitSevenDirection pivot ≠ splitSevenDirection pairFirst
          ∧ splitSevenDirection pivot ≠ splitSevenDirection pairSecond
          ∧ splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond) :=
  (dominates_congr_atom (splitSevenReweighted_atom splitZero splitOne splitTwo hzeroPos
      hzeroLt honePos honeLt htwoPos htwoLt) {pivot, pairFirst, pairSecond}).trans
    (splitSevenDesign_dominates_iff_rainbowDirections hpivotFirst hpivotSecond
      hpairDistinct)

/-- An asymmetric split of direction `0` gives duplicated atoms with unequal
weights, which no stress certificate can reproduce. -/
theorem splitSevenReweighted_noStressCertificate (hasymmetric : splitZero ≠ 1/8)
    {index : Type*} (family : Finset index) (dir : index → Fin 3 → ℝ)
    (coeff : index → ℝ)
    (hcert : ∀ atomIndex : Fin 7,
      ∑ i ∈ family, coeff i *
        ((splitSevenReweighted splitZero splitOne splitTwo hzeroPos hzeroLt honePos
          honeLt htwoPos htwoLt).atom atomIndex ⬝ᵥ dir i) ^ 2
      = (splitSevenReweighted splitZero splitOne splitTwo hzeroPos hzeroLt honePos
          honeLt htwoPos htwoLt).weight atomIndex) : False := by
  refine noStressCertificate_of_duplicate_atoms
    (splitSevenReweighted splitZero splitOne splitTwo hzeroPos hzeroLt honePos honeLt
      htwoPos htwoLt) (c := 0) (c' := 4) rfl ?_ family dir coeff hcert
  show splitZero ≠ 1/4 - splitZero
  intro heq
  exact hasymmetric (by linarith)

end Reweighting

/-- **EXACT `(7,3)` TIES WITHOUT A STRESS CERTIFICATE.** The `(6,3)` separation
of `Gtz.Ties.SplitTetrahedronTie` transports to the size that carries the whole
of rank three: an all-heavy exact tie whose `20` dominators are pinned, whose tie
values sum to `-120`, and which admits no stress certificate at all, because its
duplicated atoms carry unequal weights. Certificate existence is an invariant of
the merged `(4,3)` tetrahedron, not of the `(7,3)` atom list. -/
theorem exists_isTie_seven_without_stressCertificate :
    ∃ D : WeightedDesign 7 3, AllHeavy D ∧ IsTie D ∧
      (∑ triple ∈ increasingTriplesSeven,
        discriminantTie D triple.1 triple.2.1 triple.2.2 = -120) ∧
      ∀ {index : Type*} (family : Finset index) (dir : index → Fin 3 → ℝ)
        (coeff : index → ℝ), (∀ i ∈ family, 0 ≤ coeff i) →
        (∀ atomIndex : Fin 7,
          ∑ i ∈ family, coeff i * (D.atom atomIndex ⬝ᵥ dir i) ^ 2
            = D.weight atomIndex) → False := by
  refine ⟨splitSevenReweighted (1/6) (1/8) (1/8) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    splitSevenReweighted_allHeavy _ _ _ _ _ _ _ _ _,
    splitSevenReweighted_isTie _ _ _ _ _ _ _ _ _,
    splitSevenReweighted_discriminantTie_sum _ _ _ _ _ _ _ _ _, ?_⟩
  intro index family dir coeff _ hcert
  exact splitSevenReweighted_noStressCertificate _ _ _ _ _ _ _ _ _ (by norm_num)
    family dir coeff hcert

/-! ### The reading -/

/-- **THE `(7,3)` TIE BOUNDARY, IN ONE STATEMENT.** At the split-tetrahedron
witness — an all-heavy weighted `(7,3)` design got by splitting three directions
of the regular tetrahedron — the tie leg SUMS to `-120` over the `35` triples
while its MAXIMUM is exactly `0`, attained at exactly the `20` triples that
dominate; and no triple dominates strictly.

Read as a refutation: every functional monotone in the multiset of the `35` tie
values and vanishing on the constant-zero multiset — the sum `e_3(N)`, any
weighted average — is strictly negative at a design
where the covering nonetheless holds, so no averaging argument over
triples can prove `DiscriminantCovering 7`. Only a selection argument, which
names a triple, can close it.

Read as a rigidity statement: the maximum is attained, not approached, and the
maximizing triples are pinned by a purely combinatorial condition on directions,
so the boundary is a genuine corner rather than a degenerate tangency — at each
of the `20`, the gap `Gram_T − I` has characteristic polynomial `lam (lam − 3)²`
(`splitSevenDesign_gapCharPoly_of_rainbowDirections`), positive semidefinite with
corank exactly one. -/
theorem splitSevenDesign_tieBoundary_reading :
    AllHeavy splitSevenDesign
      ∧ IsTie splitSevenDesign
      ∧ (∑ triple ∈ increasingTriplesSeven,
          discriminantTie splitSevenDesign triple.1 triple.2.1 triple.2.2) = -120
      ∧ (∀ triple ∈ increasingTriplesSeven,
          discriminantTie splitSevenDesign triple.1 triple.2.1 triple.2.2 ≤ 0)
      ∧ (∀ triple ∈ increasingTriplesSeven,
          Dominates splitSevenDesign {triple.1, triple.2.1, triple.2.2}
            ↔ discriminantTie splitSevenDesign triple.1 triple.2.1 triple.2.2 = 0)
      ∧ (increasingTriplesSeven.filter HasRainbowDirections).card = 20 := by
  refine ⟨splitSevenDesign_allHeavy, splitSevenDesign_isTie,
    splitSevenDesign_discriminantTie_sum, fun triple hmem => ?_, fun triple hmem => ?_,
    rainbowTriplesSeven_card⟩
  · obtain ⟨hpivotFirst, hpivotSecond, hpairDistinct⟩ :=
      increasingTriplesSeven_distinct hmem
    exact splitSevenDesign_discriminantTie_nonpos hpivotFirst hpivotSecond hpairDistinct
  · obtain ⟨hpivotFirst, hpivotSecond, hpairDistinct⟩ :=
      increasingTriplesSeven_distinct hmem
    rw [splitSevenDesign_dominates_iff_rainbowDirections hpivotFirst hpivotSecond
      hpairDistinct]
    constructor
    · rintro ⟨hdirPivotFirst, hdirPivotSecond, hdirPair⟩
      exact splitSevenDesign_discriminantTie_of_rainbowDirections hdirPivotFirst
        hdirPivotSecond hdirPair
    · intro htieZero
      refine ⟨fun hsame => ?_, fun hsame => ?_, fun hsame => ?_⟩
      · rw [splitSevenDesign_discriminantTie_of_repeatedDirection hpivotFirst
          hpivotSecond hpairDistinct (Or.inl hsame)] at htieZero
        norm_num at htieZero
      · rw [splitSevenDesign_discriminantTie_of_repeatedDirection hpivotFirst
          hpivotSecond hpairDistinct (Or.inr (Or.inl hsame))] at htieZero
        norm_num at htieZero
      · rw [splitSevenDesign_discriminantTie_of_repeatedDirection hpivotFirst
          hpivotSecond hpairDistinct (Or.inr (Or.inr hsame))] at htieZero
        norm_num at htieZero

end Gtz

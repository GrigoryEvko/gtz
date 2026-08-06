/-
# The matroid stratification of the stress-free hinge

`Gtz.StressFreeHingeHoldsSixThree` is the sole remaining hypothesis of rank-three
GTZ (`Gtz.forall_gtzOriginal_rank_three_of_stressFreeHingeAlone`).  This file
stratifies it by the DIRECTION MATROID and empties four of the nine strata with
one law.

## The law

**THE PLANE-PAIR ESCAPE LAW.**  A stress-free `(6,3)` design admits no two atom
planes covering all six labels.  Two covering planes give a line-pair quadric
annihilating every atom, hence a nonzero stress
(`Gtz.exists_stress_of_twoPlanes`), which a stress-free design forbids outright.
The planes are read off the matroid: the plane of a pair of labels is spanned by
their atoms, its normal is `Gtz.bracketNormal`, and it is nonzero because a
stress-free design is primitive.

That turns a purely combinatorial, DECIDABLE condition on a line pattern —
`IsPlanePairCovered`, some two pairs of labels whose pattern lines cover every
label — into emptiness of the corresponding stress-free stratum.  The condition
is stable under relabelling, so it survives the enumeration interface, which
delivers patterns only up to a permutation.

## The stratification

Of the nine six-point classes of `Gtz.lineFamiliesSix`, exactly FOUR are plane-pair
covered and die:

* `#2` `[[0,1,2],[3,4,5]]` — two disjoint three-point lines;
* `#6` `[[0,1,2,3]]` — one four-point line (the second plane is spanned by the two
  labels off it, and needs no line of the pattern at all);
* `#7` `[[0,1,2,3],[0,4,5]]` — a four-point line and a three-point line;
* `#8` `[[0,1,2,3,4]]` — the near pencil (the second plane is spanned by the pole
  and any label of the long line).

and exactly FIVE survive:

* `#0` `[]` — `U(3,6)`, no dependent triple;
* `#1` `[[0,1,2]]` — one three-point line;
* `#3` `[[0,1,2],[0,3,4]]` — two three-point lines meeting;
* `#4` `[[0,1,2],[0,3,4],[1,3,5]]` — three three-point lines;
* `#5` `[[0,1,2],[0,3,4],[1,3,5],[2,4,5]]` — `M(K4)`, the complete quadrilateral.

`stressFreeHingeHoldsSixThree_of_residualFamilies` composes this into the target:
the stress-free hinge follows from the combinatorial completeness of
`Gtz.linePatternListSix` plus tie-freeness of those FIVE named matroid strata.
Nothing else.  This is the first time the hinge's residual is indexed by matroid
classes rather than by a single undifferentiated stratum.

## Independent cross-check against the tree's own stress census

The tree already sorts the same nine entries by stress structure, from the
opposite side, and the two sortings agree exactly:

* `Gtz.patternForcesStress_twoDisjointLines`, `_fourPointLine`,
  `_fourPointLineWithThreePointLine` prove that `#2`, `#6`, `#7` force a stress on
  every design of their stratum.  Those are three of the four killed here; the
  fourth, the near pencil `#8`, was already tie-free by
  `Gtz.stratumIsTieFree_nearPencilSixFamilyPattern`, so the law recovers it and
  extends the census by one entry.
* `Gtz.stratumIsStressFree_oneThreePointLine`, `_twoMeetingLines`, `_threeLines`,
  `_graphicKFour` prove that `#1`, `#3`, `#4`, `#5` are ENTIRELY stress-free — every
  design of those four strata lies in branch (i).  So four of the five survivors
  are not merely uncut, they are exactly the stress-free hinge's own domain, and
  `#0` is the single mixed class (`Gtz.stratumStressHasFullSupport_lineFree`; six
  points lie on a smooth conic on a codimension-one sublocus).

The two censuses were built independently — one by exhibiting covering plane pairs
per entry, one by the decidable condition below — and they partition the nine
entries identically.

## The control: the law is FALSE one size down

`isPlanePairCovered_diamondFamilyFive` is a `decide`: the diamond's matroid, the
two circuits `{0,1,3}` and `{0,2,4}` through the shared label `0`, IS plane-pair
covered at five labels.  The diamond is a genuine primitive `(5,3)` tie
(`Gtz.diamondDesign_isTie`, `Gtz.not_hasParallelPair_diamondDesign`), which is why
`Gtz.not_hingeHoldsAtSize_five_three` holds.  And the diamond is STRESS-FREE:
measured exactly outside Lean in rational arithmetic, its five
graphic edge vectors `(1,-1,0)`, `(1,0,-1)`, `(1,0,0)`, `(0,1,-1)`, `(0,1,0)` have
dependent triples exactly `{0,1,3}` and `{0,2,4}` and their five Veronese rows have
RANK FIVE in the six-dimensional space of symmetric three-by-three matrices —
stress-freeness is invariant under the common invertible whitener, so this decides
it for `Gtz.diamondDesign` itself.  A stress-free, plane-pair-covered, primitive
`(5,3)` TIE therefore exists, and the escape law is FALSE at five atoms.  It is not
a combinatorial fact about matroids: five atoms have room to be independent in a
six-dimensional space and six do not, and the proof below spends that dimension
count through `Gtz.exists_stress_of_twoPlanes`, which is stated at
`WeightedDesign 6 3` for exactly that reason.  The rank computation is MEASURED,
not mechanized; the combinatorial half of the control is the `decide` below.

## NOT proved here

* No stratum of the five survivors is emptied.  The residual is a hypothesis.
* `Gtz.LinearSpaceListIsComplete 6 Gtz.linePatternListSix` is not proved here
  either; it is the standing combinatorial input, true by the classical
  catalogue (A058731) and open in Lean.
* Nothing about seven labels.
-/
import Mathlib
import Gtz.Reduction.TrichotomyLedger
import Gtz.Design.LinePatternEnumeration
import Gtz.Ties.SpikeMatroidObstruction
import Gtz.Ties.SplitTetrahedronTie
import Gtz.Quantitative.WindowCofactorBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Gtz

open Matrix

/-! ## The plane-pair covering, combinatorially

The plane of a pair of distinct labels carries the two labels themselves and
every label the pattern makes dependent with them.  A pattern is COVERED when two
such planes exhaust the labels.  The two escape clauses `label = pivotFirst` and
`label = pivotSecond` are not decoration: on the design side a bracket with a
repeated slot vanishes identically, so the pivots always lie on their own plane,
and a covering that used that fact would be lost without them.  Entry `#6`, whose
second plane is spanned by the two labels off its four-point line and is not a
line of the pattern at all, is covered only through those clauses. -/

/-- Some two pairs of distinct labels have planes covering every label. -/
def IsPlanePairCovered {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∃ firstPivot secondPivot thirdPivot fourthPivot : Fin size,
    firstPivot ≠ secondPivot ∧ thirdPivot ≠ fourthPivot ∧
      ∀ label : Fin size,
        (label = firstPivot ∨ label = secondPivot ∨ pattern firstPivot secondPivot label) ∨
          (label = thirdPivot ∨ label = fourthPivot ∨ pattern thirdPivot fourthPivot label)

instance decidableIsPlanePairCovered {size : ℕ} (lines : List (List (Fin size))) :
    Decidable (IsPlanePairCovered (lineFamilyPattern lines)) := by
  unfold IsPlanePairCovered
  infer_instance

/-- **The covering is stable under relabelling.**  The enumeration interface
delivers a listed pattern composed with a permutation, so a filter that did not
transport would be unusable there. -/
theorem isPlanePairCovered_comp_relabel {size : ℕ} {pattern : LinePattern size}
    (hcovered : IsPlanePairCovered pattern) (relabel : Equiv.Perm (Fin size)) :
    IsPlanePairCovered (fun leftLabel midLabel rightLabel =>
      pattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  obtain ⟨firstPivot, secondPivot, thirdPivot, fourthPivot, hfirstDistinct, hsecondDistinct,
    hcover⟩ := hcovered
  refine ⟨relabel.symm firstPivot, relabel.symm secondPivot, relabel.symm thirdPivot,
    relabel.symm fourthPivot, ?_, ?_, fun label => ?_⟩
  · exact fun hequal => hfirstDistinct (by simpa using congrArg relabel hequal)
  · exact fun hequal => hsecondDistinct (by simpa using congrArg relabel hequal)
  · have hshifted := hcover (relabel label)
    simpa only [Equiv.apply_symm_apply, Equiv.eq_symm_apply] using hshifted

/-! ## The design side: the plane of a pair, and the escape law -/

/-- Every label on a pivot pair's plane pairs to zero against that pair's normal.
The two pivots are on their own plane because a repeated bracket slot vanishes;
every other member is there because the pattern says its bracket does. -/
theorem atom_dotProduct_bracketNormal_eq_zero_of_onPlane {size : ℕ}
    (design : WeightedDesign size 3) {pattern : LinePattern size}
    (hpattern : HasLinePattern design pattern)
    {pivotFirst pivotSecond : Fin size} (hpivotDistinct : pivotFirst ≠ pivotSecond)
    (label : Fin size)
    (honPlane : label = pivotFirst ∨ label = pivotSecond ∨ pattern pivotFirst pivotSecond label) :
    design.atom label ⬝ᵥ bracketNormal (design.atom pivotFirst) (design.atom pivotSecond) = 0 := by
  by_cases hisFirst : label = pivotFirst
  · subst hisFirst
    exact (atomBracket_eq_zero_iff_dotProduct_bracketNormal design label pivotSecond label).mp
      (tripleBracket_eq_zero_of_outerRepeat _ _)
  · by_cases hisSecond : label = pivotSecond
    · subst hisSecond
      exact (atomBracket_eq_zero_iff_dotProduct_bracketNormal design pivotFirst label label).mp
        (tripleBracket_eq_zero_of_tailRepeat _ _)
    · have hplane : pattern pivotFirst pivotSecond label := by
        rcases honPlane with hfirst | hsecond | hplane
        · exact absurd hfirst hisFirst
        · exact absurd hsecond hisSecond
        · exact hplane
      exact (atomBracket_eq_zero_iff_dotProduct_bracketNormal design pivotFirst pivotSecond
        label).mp
        ((hpattern pivotFirst pivotSecond label hpivotDistinct (Ne.symm hisFirst)
          (Ne.symm hisSecond)).mpr hplane)

/-- **THE PLANE-PAIR ESCAPE LAW.**  A stress-free `(6,3)` design has no two atom
planes covering all six labels.  A covering pair is a line-pair quadric through
every atom, hence a nonzero stress, and a stress-free design has none. -/
theorem not_isPlanePairCovered_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : ∀ stress : Fin 6 → ℝ,
      (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0)
    {pattern : LinePattern 6} (hpattern : HasLinePattern design pattern) :
    ¬ IsPlanePairCovered pattern := by
  rintro ⟨firstPivot, secondPivot, thirdPivot, fourthPivot, hfirstDistinct, hsecondDistinct,
    hcover⟩
  have hprimitive := isPrimitiveDesign_of_stressFree design hstressFree
  have hfirstNormalNe := bracketNormal_atom_ne_zero_of_isPrimitiveDesign (by omega) design
    hprimitive firstPivot secondPivot hfirstDistinct
  have hsecondNormalNe := bracketNormal_atom_ne_zero_of_isPrimitiveDesign (by omega) design
    hprimitive thirdPivot fourthPivot hsecondDistinct
  obtain ⟨stress, hstressNe, hstressZero⟩ :=
    exists_stress_of_twoPlanes design hfirstNormalNe hsecondNormalNe fun label => by
      rcases hcover label with hfirstPlane | hsecondPlane
      · exact Or.inl (by
          rw [dotProduct_comm]
          exact atom_dotProduct_bracketNormal_eq_zero_of_onPlane design hpattern hfirstDistinct
            label hfirstPlane)
      · exact Or.inr (by
          rw [dotProduct_comm]
          exact atom_dotProduct_bracketNormal_eq_zero_of_onPlane design hpattern hsecondDistinct
            label hsecondPlane)
  exact hstressNe (hstressFree stress hstressZero)

/-! ## The residual obligation, per matroid class

The enumeration interface hands back a listed pattern composed with a permutation,
so the obligation is stated with that permutation quantified.  A stress-free design
has no parallel pair, so on this branch the hinge's conclusion is unreachable and
the obligation is plain tie-emptiness. -/

/-- No stress-free `(6,3)` design realizing this class, under any relabelling, is
a tie. -/
def StressFreeStratumIsTieFree (pattern : LinePattern 6) : Prop :=
  ∀ (design : WeightedDesign 6 3) (relabel : Equiv.Perm (Fin 6)),
    (∀ stress : Fin 6 → ℝ, (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0) →
      HasLinePattern design (fun leftLabel midLabel rightLabel =>
        pattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) →
        ¬ IsTie design

/-- **A COVERED CLASS IS EMPTY OF STRESS-FREE DESIGNS**, so its obligation is
discharged without any reference to ties at all. -/
theorem stressFreeStratumIsTieFree_of_isPlanePairCovered {pattern : LinePattern 6}
    (hcovered : IsPlanePairCovered pattern) : StressFreeStratumIsTieFree pattern :=
  fun design relabel hstressFree hpattern _ =>
    not_isPlanePairCovered_of_stressFree design hstressFree hpattern
      (isPlanePairCovered_comp_relabel hcovered relabel)

/-! ## Which of the nine classes the filter kills

One `decide` per entry, so a failure names its entry. -/

/-- Entry `#2`, two disjoint three-point lines: covered by its own two lines. -/
theorem isPlanePairCovered_twoDisjointLines :
    IsPlanePairCovered (lineFamilyPattern [[(0 : Fin 6), 1, 2], [3, 4, 5]]) := by decide

/-- Entry `#6`, one four-point line: covered by that line and by the plane the two
labels off it span, which is not a line of the pattern. -/
theorem isPlanePairCovered_fourPointLine :
    IsPlanePairCovered (lineFamilyPattern [[(0 : Fin 6), 1, 2, 3]]) := by decide

/-- Entry `#7`, a four-point line and a three-point line: covered by its two
lines. -/
theorem isPlanePairCovered_fourPointLineWithThreePointLine :
    IsPlanePairCovered (lineFamilyPattern [[(0 : Fin 6), 1, 2, 3], [0, 4, 5]]) := by decide

/-- Entry `#8`, the near pencil: covered by the long line and by the plane the pole
spans with any label of it. -/
theorem isPlanePairCovered_nearPencilSix :
    IsPlanePairCovered (lineFamilyPattern [[(0 : Fin 6), 1, 2, 3, 4]]) := by decide

/-- Entry `#0`, `U(3,6)`: NOT covered.  With no dependent triple every plane holds
exactly two labels, and two planes reach four. -/
theorem not_isPlanePairCovered_lineFree :
    ¬ IsPlanePairCovered (lineFamilyPattern ([] : List (List (Fin 6)))) := by decide

/-- Entry `#1`, one three-point line: NOT covered. -/
theorem not_isPlanePairCovered_oneThreePointLine :
    ¬ IsPlanePairCovered (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by decide

/-- Entry `#3`, two three-point lines meeting: NOT covered — they share a label, so
together they reach five. -/
theorem not_isPlanePairCovered_twoMeetingLines :
    ¬ IsPlanePairCovered (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) := by decide

/-- Entry `#4`, three three-point lines: NOT covered. -/
theorem not_isPlanePairCovered_threeLines :
    ¬ IsPlanePairCovered (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]]) := by
  decide

/-- Entry `#5`, `M(K4)`: NOT covered.  Two triangles of `K4` share an edge, so any
two of its four lines reach five of the six edge labels. -/
theorem not_isPlanePairCovered_graphicKFour :
    ¬ IsPlanePairCovered
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]) := by decide

/-! ## The five surviving classes -/

/-- The five six-point matroid classes a stress-free design can realize: `U(3,6)`,
one three-point line, two meeting three-point lines, three three-point lines, and
`M(K4)`. -/
def stressFreeResidualFamiliesSix : List (List (List (Fin 6))) :=
  [ []
  , [[0, 1, 2]]
  , [[0, 1, 2], [0, 3, 4]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]] ]

theorem length_stressFreeResidualFamiliesSix : stressFreeResidualFamiliesSix.length = 5 := by
  decide

/-- **THE STRATIFICATION.**  Among the nine six-point classes, the uncovered ones
are exactly the five listed. -/
theorem not_isPlanePairCovered_iff_mem_stressFreeResidualFamiliesSix :
    ∀ lines ∈ lineFamiliesSix,
      (¬ IsPlanePairCovered (lineFamilyPattern lines) ↔
        lines ∈ stressFreeResidualFamiliesSix) := by
  intro lines hlines
  simp only [lineFamiliesSix, List.mem_cons, List.not_mem_nil, or_false] at hlines
  rcases hlines with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact iff_of_true not_isPlanePairCovered_lineFree (by decide)
  · exact iff_of_true not_isPlanePairCovered_oneThreePointLine (by decide)
  · exact iff_of_false (not_not_intro isPlanePairCovered_twoDisjointLines) (by decide)
  · exact iff_of_true not_isPlanePairCovered_twoMeetingLines (by decide)
  · exact iff_of_true not_isPlanePairCovered_threeLines (by decide)
  · exact iff_of_true not_isPlanePairCovered_graphicKFour (by decide)
  · exact iff_of_false (not_not_intro isPlanePairCovered_fourPointLine) (by decide)
  · exact iff_of_false (not_not_intro isPlanePairCovered_fourPointLineWithThreePointLine)
      (by decide)
  · exact iff_of_false (not_not_intro isPlanePairCovered_nearPencilSix) (by decide)

/-! ## The composition -/

/-- **THE STRESS-FREE HINGE FROM THE STRATIFICATION.**  Its inputs are the
combinatorial completeness of `Gtz.linePatternListSix` and tie-freeness of the
stress-free stratum of each entry the filter does not kill. -/
theorem stressFreeHingeHoldsSixThree_of_uncoveredResidual
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hresidual : ∀ lines ∈ lineFamiliesSix, ¬ IsPlanePairCovered (lineFamilyPattern lines) →
      StressFreeStratumIsTieFree (lineFamilyPattern lines)) :
    StressFreeHingeHoldsSixThree := by
  intro design hstressFree htie
  exfalso
  obtain ⟨pattern, hmem, relabel, hpattern⟩ :=
    patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete (by omega) linePatternListSix
      hcomplete design (isPrimitiveDesign_of_stressFree design hstressFree)
  obtain ⟨lines, hlines, hshape⟩ := List.mem_map.mp hmem
  subst hshape
  by_cases hcovered : IsPlanePairCovered (lineFamilyPattern lines)
  · exact stressFreeStratumIsTieFree_of_isPlanePairCovered hcovered design relabel hstressFree
      hpattern htie
  · exact hresidual lines hlines hcovered design relabel hstressFree hpattern htie

/-- **THE HEADLINE, at the five named classes.**  The last residual of rank-three
GTZ follows from the standing enumeration input plus tie-freeness of the
stress-free stratum of `U(3,6)`, of one three-point line, of two meeting
three-point lines, of three three-point lines, and of `M(K4)`.  Four of the nine
classes are gone. -/
theorem stressFreeHingeHoldsSixThree_of_residualFamilies
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hresidual : ∀ lines ∈ stressFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines)) :
    StressFreeHingeHoldsSixThree :=
  stressFreeHingeHoldsSixThree_of_uncoveredResidual hcomplete fun lines hlines huncovered =>
    hresidual lines
      ((not_isPlanePairCovered_iff_mem_stressFreeResidualFamiliesSix lines hlines).mp huncovered)

/-! ## Controls

Three things would make the above worthless: the filter could kill nothing, it
could kill everything, or it could be a combinatorial fact that must therefore
also hold at five labels — where the hinge is FALSE. -/

/-- The filter kills something: four of the nine entries. -/
theorem exists_isPlanePairCovered_mem_lineFamiliesSix :
    ∃ lines ∈ lineFamiliesSix, IsPlanePairCovered (lineFamilyPattern lines) :=
  ⟨[[0, 1, 2], [3, 4, 5]], by decide, isPlanePairCovered_twoDisjointLines⟩

/-- The filter does not kill everything: `M(K4)`, the sharpest open class, survives
it, so the residual of the headline is not vacuous. -/
theorem exists_not_isPlanePairCovered_mem_lineFamiliesSix :
    ∃ lines ∈ lineFamiliesSix, ¬ IsPlanePairCovered (lineFamilyPattern lines) :=
  ⟨[[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]], by decide, not_isPlanePairCovered_graphicKFour⟩

/-- **THE SIZE CONTROL.**  The diamond's matroid — two three-point circuits through
one shared label — IS plane-pair covered at FIVE labels.  The diamond is a genuine
primitive `(5,3)` tie (`Gtz.diamondDesign_isTie`,
`Gtz.not_hasParallelPair_diamondDesign`, whence
`Gtz.not_hingeHoldsAtSize_five_three`), so the escape law cannot be a statement
about matroids alone: it is a statement about six atoms in the six-dimensional
space of symmetric three-by-three matrices, and its proof spends that dimension
count inside `Gtz.exists_stress_of_twoPlanes`, which is stated at
`Gtz.WeightedDesign 6 3`. -/
theorem isPlanePairCovered_diamondFamilyFive :
    IsPlanePairCovered (lineFamilyPattern [[(0 : Fin 5), 1, 3], [0, 2, 4]]) := by decide

/-- The five-label diamond family is a legitimate spanning partial linear space, so
the control above is about a real matroid and not a mistranscription. -/
theorem isGoodLineFamily_diamondFamilyFive :
    IsGoodLineFamily [[(0 : Fin 5), 1, 3], [0, 2, 4]] := by decide

/-! ## The gating wall on `#0`, named and priced

`Gtz.forall_circuitWindow_traceInverse_eq_one_iff_layer_eq_zero` collapses the
residual on the general-position stratum onto ONE equation in the unweighted second
moment, `det N - 4 e_2(N) + 10 tr N - 20 = 0`.  It carries a second hypothesis
besides general position: EVERY `(rank+1)`-window has a positive definite gap.  No
producer of that hypothesis at a `(6,3)` tie exists in the tree.  This section says
exactly what it costs and exhibits a tie where it fails.

The criterion is one line of algebra.  A weakly dominating triple at a tie has a
TIGHT DIRECTION in the kernel of its gap (`Gtz.isTie_yields_tightDirection`).  Add a
fourth atom: the window gap's value at that direction is the old zero plus the added
atom's squared pairing.  So the window gap is positive definite only if the added
atom pairs NONZERO with the tight direction — the gating hypothesis is a
transversality demand on the atoms against every tight direction, and it is not
free. -/

/-- Adding one atom moves a gap's quadratic form by that atom's squared pairing. -/
theorem dotProduct_gap_insert_eq {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) {addedLabel : Fin size} (hfresh : addedLabel ∉ selected)
    (probe : Fin rank → ℝ) :
    probe ⬝ᵥ ((subsetSum design (insert addedLabel selected) - 1) *ᵥ probe)
      = probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe)
        + (design.atom addedLabel ⬝ᵥ probe) ^ 2 := by
  rw [subsetSum, Finset.sum_insert hfresh, ← subsetSum]
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add]
  rw [dotProduct_atomMatrix_mulVec]
  ring

/-- **THE GATING CRITERION.**  A window built from a weakly dominating triple by
adding an atom ORTHOGONAL to that triple's tight direction has a gap that is not
positive definite — the tight direction survives into the window. -/
theorem not_posDef_gap_insert_of_orthogonal_tightDirection {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    {addedLabel : Fin size} (hfresh : addedLabel ∉ selected)
    {tightDir : Fin rank → ℝ} (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design selected - 1) *ᵥ tightDir) = 0)
    (horthogonal : design.atom addedLabel ⬝ᵥ tightDir = 0) :
    ¬ (subsetSum design (insert addedLabel selected) - 1).PosDef := by
  intro hposDef
  have hvalue := dotProduct_gap_insert_eq design selected hfresh tightDir
  rw [htight, horthogonal] at hvalue
  have hpositive := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 htightNe
  rw [star_trivial, hvalue] at hpositive
  norm_num at hpositive

/-- **WHAT THE GATING HYPOTHESIS DEMANDS.**  If every window built on a weakly
dominating triple is gated, then no atom outside that triple is orthogonal to any of
its tight directions.  This is the named sub-obligation a producer of the gating
hypothesis has to discharge, and it is a transversality statement about the atoms,
not a positivity one. -/
theorem dotProduct_tightDirection_ne_zero_of_gated {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    {addedLabel : Fin size} (hfresh : addedLabel ∉ selected)
    {tightDir : Fin rank → ℝ} (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design selected - 1) *ᵥ tightDir) = 0)
    (hgated : (subsetSum design (insert addedLabel selected) - 1).PosDef) :
    design.atom addedLabel ⬝ᵥ tightDir ≠ 0 := fun horthogonal =>
  not_posDef_gap_insert_of_orthogonal_tightDirection design selected hfresh htightNe htight
    horthogonal hgated

/-- **THE GATING HYPOTHESIS IS NOT FREE AT A `(6,3)` TIE.**  The split-tetrahedron
design is a kernel-checked exact tie whose window `{2,3,4,5}` carries only the two duplicated
tetrahedron directions `v2` and `v3`; the direction `(0,1,1)` is orthogonal to both,
so the window gap takes the value `-2` there and is not positive definite — not even
positive semidefinite.

The design has parallel pairs, so it is not general position and this does not refute
the gating hypothesis in the form
`Gtz.forall_circuitWindow_traceInverse_eq_one_iff_layer_eq_zero` uses it.  What it
does settle is that gating is NOT a consequence of `Gtz.IsTie` alone: any producer
must spend general position, and by the criterion above it must in particular rule out
an atom orthogonal to a tight direction. -/
theorem exists_isTie_and_not_forall_window_posDef_sixThree :
    ∃ design : WeightedDesign 6 3, IsTie design ∧
      ∃ window : Finset (Fin 6), window.card = 4 ∧ ¬ (subsetSum design window - 1).PosDef := by
  refine ⟨splitTetraDesign (1/8) (1/8) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    splitTetraDesign_isTie (1/8) (1/8) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ({2, 3, 4, 5} : Finset (Fin 6)), by decide, ?_⟩
  intro hposDef
  have hnullPairing : ∀ dirIndex : Fin 4, dirIndex = 2 ∨ dirIndex = 3 →
      tetraAtom dirIndex ⬝ᵥ (![0, 1, 1] : Fin 3 → ℝ) = 0 := by
    rintro dirIndex (rfl | rfl) <;>
      norm_num [tetraAtom, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_three, Matrix.cons_val_four]
  have hvalue : (![0, 1, 1] : Fin 3 → ℝ) ⬝ᵥ
      ((subsetSum (splitTetraDesign (1/8) (1/8) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)) ({2, 3, 4, 5} : Finset (Fin 6)) - 1) *ᵥ ![0, 1, 1]) = -2 := by
    rw [show ({2, 3, 4, 5} : Finset (Fin 6)) = insert 2 (insert 3 (insert 4 {5})) from rfl,
      subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
      dotProduct_atomMatrix_mulVec_self, splitTetraDesign_atom, splitTetraAtom]
    rw [show splitTetraDirIndex 2 = 2 from rfl, show splitTetraDirIndex 3 = 2 from rfl,
      show splitTetraDirIndex 4 = 3 from rfl, show splitTetraDirIndex 5 = 3 from rfl,
      hnullPairing 2 (Or.inl rfl), hnullPairing 3 (Or.inr rfl)]
    norm_num [Matrix.one_mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_three, Matrix.cons_val_four]
  have hpositive := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2
    (show (![0, 1, 1] : Fin 3 → ℝ) ≠ 0 from fun hzero => by simpa using congrFun hzero 1)
  rw [star_trivial, hvalue] at hpositive
  norm_num at hpositive

/-! ## The seam: which survivors contain the diamond matroid on five labels

The `(5,3)` classification says every primitive `(5,3)` tie carries the
SHARED-LINE-PAIR matroid — two dependent triples through one common label, which
is the diamond `M(K4 - e)`, catalogue `simple_n05_r03_#2`.  So a six-point class
none of whose five-label restrictions carries that matroid has NO tie on any of its
six boundary faces, and the corank descent gives strict domination there for free.

This splits the five survivors in two, and the split is clean:

* `#0` `U(3,6)` and `#1` one three-point line carry NO shared line pair — they have
  fewer than two dependent triples to begin with, so no restriction can host a
  `(5,3)` tie;
* `#3`, `#4` and `#5` all DO.  Entry `#3` is the diamond matroid itself with one free
  label added, so its restriction that drops the free label IS the diamond on the
  nose; `#4` carries it three ways; `M(K4)` carries it on EVERY five-label
  restriction, since any two of its four triangles share exactly one edge and their
  union is five of the six edges.

So the danger in the stress-free hinge concentrates exactly on the classes
containing the diamond as a restriction, with `Gtz.diamondDesign` and
`Gtz.uniformTieParentDesign` as the realizations to test any argument against. -/

/-- Two dependent triples through one common label, on five distinct labels: the
diamond matroid `M(K4 - e)` as a restriction. -/
def HasSharedLinePairRestriction {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∃ sharedLabel firstLabel secondLabel thirdLabel fourthLabel : Fin size,
    sharedLabel ≠ firstLabel ∧ sharedLabel ≠ secondLabel ∧ sharedLabel ≠ thirdLabel ∧
      sharedLabel ≠ fourthLabel ∧ firstLabel ≠ secondLabel ∧ firstLabel ≠ thirdLabel ∧
        firstLabel ≠ fourthLabel ∧ secondLabel ≠ thirdLabel ∧ secondLabel ≠ fourthLabel ∧
          thirdLabel ≠ fourthLabel ∧
            pattern sharedLabel firstLabel secondLabel ∧
              pattern sharedLabel thirdLabel fourthLabel

instance decidableHasSharedLinePairRestriction {size : ℕ} (lines : List (List (Fin size))) :
    Decidable (HasSharedLinePairRestriction (lineFamilyPattern lines)) := by
  unfold HasSharedLinePairRestriction
  infer_instance

/-- `U(3,6)` carries no shared line pair: it has no dependent triple at all. -/
theorem not_hasSharedLinePairRestriction_lineFree :
    ¬ HasSharedLinePairRestriction (lineFamilyPattern ([] : List (List (Fin 6)))) := by decide

/-- One three-point line carries no shared line pair: it has only one dependent
triple and the configuration needs two. -/
theorem not_hasSharedLinePairRestriction_oneThreePointLine :
    ¬ HasSharedLinePairRestriction (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by decide

/-- Two meeting three-point lines ARE the diamond matroid plus one free label. -/
theorem hasSharedLinePairRestriction_twoMeetingLines :
    HasSharedLinePairRestriction (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) := by decide

/-- Three three-point lines carry the diamond on three different restrictions. -/
theorem hasSharedLinePairRestriction_threeLines :
    HasSharedLinePairRestriction
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]]) := by decide

/-- `M(K4)` carries the diamond on every five-label restriction. -/
theorem hasSharedLinePairRestriction_graphicKFour :
    HasSharedLinePairRestriction
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]) := by decide

/-- **THE SEAM, MECHANIZED.**  The `(5,3)` classification
(`EndpointSpike.sharedLinePairAtEveryTie_holds`) says every primitive `(5,3)`
tie carries two dependent triples through a common atom.  Read through the
predicate above: a primitive `(5,3)` design whose own dependence pattern has
no shared line pair is NOT a tie.  This is the exact statement a
weight-simplex certifier needs on the boundary faces of a fixed direction
class, and it is now one named Prop. -/
theorem not_isTie_of_not_hasSharedLinePairRestriction (bottomDesign : WeightedDesign 5 3)
    (hprimitive : IsPrimitiveDesign bottomDesign)
    (hnoPair : ¬ HasSharedLinePairRestriction (dependencePattern bottomDesign)) :
    ¬ IsTie bottomDesign := by
  intro htie
  obtain ⟨relabel, hfirstLine, hsecondLine⟩ := EndpointSpike.sharedLinePairAtEveryTie_holds bottomDesign
    hprimitive htie
  refine hnoPair ⟨relabel 0, relabel 1, relabel 2, relabel 3, relabel 4, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hfirstLine, hsecondLine⟩ <;>
    exact fun hequal => by simpa using relabel.injective hequal

/-- The two survivors with no diamond restriction: their boundary faces host no
`(5,3)` tie, so the corank descent reaches strict domination there. -/
def diamondFreeResidualFamiliesSix : List (List (List (Fin 6))) :=
  [ [], [[0, 1, 2]] ]

/-- The three survivors that do carry a diamond restriction: the hard stratum. -/
def diamondCarryingResidualFamiliesSix : List (List (List (Fin 6))) :=
  [ [[0, 1, 2], [0, 3, 4]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]] ]

/-- **THE SEAM.**  The five surviving classes split two to three by whether a
five-label restriction carries the diamond matroid. -/
theorem hasSharedLinePairRestriction_iff_mem_diamondCarrying :
    ∀ lines ∈ stressFreeResidualFamiliesSix,
      (HasSharedLinePairRestriction (lineFamilyPattern lines) ↔
        lines ∈ diamondCarryingResidualFamiliesSix) := by
  intro lines hlines
  simp only [stressFreeResidualFamiliesSix, List.mem_cons, List.not_mem_nil, or_false] at hlines
  rcases hlines with rfl | rfl | rfl | rfl | rfl
  · exact iff_of_false not_hasSharedLinePairRestriction_lineFree (by decide)
  · exact iff_of_false not_hasSharedLinePairRestriction_oneThreePointLine (by decide)
  · exact iff_of_true hasSharedLinePairRestriction_twoMeetingLines (by decide)
  · exact iff_of_true hasSharedLinePairRestriction_threeLines (by decide)
  · exact iff_of_true hasSharedLinePairRestriction_graphicKFour (by decide)

/-- The two lists exhaust the five survivors. -/
theorem stressFreeResidualFamiliesSix_eq_append :
    stressFreeResidualFamiliesSix
      = diamondFreeResidualFamiliesSix ++ diamondCarryingResidualFamiliesSix := by decide

/-- **THE HEADLINE, SPLIT AT THE SEAM.**  Two easy classes, whose boundary faces
host no `(5,3)` tie, and three hard ones, each containing the diamond matroid as a
five-label restriction. -/
theorem stressFreeHingeHoldsSixThree_of_seamSplit
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hdiamondFree : ∀ lines ∈ diamondFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines))
    (hdiamondCarrying : ∀ lines ∈ diamondCarryingResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines)) :
    StressFreeHingeHoldsSixThree := by
  refine stressFreeHingeHoldsSixThree_of_residualFamilies hcomplete fun lines hlines => ?_
  rw [stressFreeResidualFamiliesSix_eq_append, List.mem_append] at hlines
  rcases hlines with hfree | hcarrying
  · exact hdiamondFree lines hfree
  · exact hdiamondCarrying lines hcarrying

end Gtz

/-
# The six-point line-pattern enumeration, cut to five middle families

`Gtz.HingeHoldsAtSize 6 3` is the campaign's hinge at the open cell.  The shipped
`Gtz.hingeHoldsAtSize_of_linearSpaceEnumeration_sixThree` reduces it to two
inputs: the combinatorial completeness of `Gtz.linePatternListSix`, and one
tie-freeness statement per non-near-pencil entry of `Gtz.lineFamiliesSix`.  This
file attacks the FIRST input only.

## What is proved here, and what is still assumed

READ THIS BEFORE CITING ANYTHING BELOW.  Nothing in this file closes the
enumeration.  Every route to `Gtz.LinearSpaceListIsComplete 6 linePatternListSix`
offered here still takes explicit undischarged combinatorial hypotheses —
`Gtz.LinearSpaceThreePointLineCasesSix` with `Gtz.LinearSpaceFourPointLineCasesSix`,
or the coarser `Gtz.LinearSpaceMultiLineCasesSix`, or the coarsest
`Gtz.LinearSpaceMiddleCasesSix` — and every route to `Gtz.HingeHoldsAtSize 6 3`
additionally takes the eight tie-freeness obligations, which are untouched here.
The contribution is that those hypotheses now cover FIVE of the nine isomorphism
classes rather than all nine.

Four of the nine classes are discharged, ordered by longest line:

* `#0`, no dependent triple — `linearSpaceListIsComplete_six_lineFreeCase`;
* `#1`, one three-point line — `linearSpaceListIsComplete_six_singleLineCase`;
* `#6`, one four-point line — `linearSpaceListIsComplete_six_singleFourPointLineCase`;
* `#8`, a five-point line, the near pencil —
  `linearSpaceListIsComplete_six_nearPencilCase`.

`#0` and `#8` fall out of shipped material: the line-free pattern is literally
`False` on distinct triples, and
`Gtz.agreesOnDistinctTriples_nearPencil_of_forall_pattern_off_pole` pins the near
pencil size-generically, so the relabelling is a single transposition.  `#1` and
`#6` are proved here, from the case closer and the two soundness lemmas below.

The residual splits along the largest line:

* `LinearSpaceFourPointLineCasesSix` — a four-point line with a dependent triple
  outside it.  ONE class, catalogue `#7`;
* `LinearSpaceThreePointLineCasesSix` — no four-point line, and at least two
  three-point lines.  FOUR classes, catalogue `#2` through `#5`: two disjoint
  lines, two meeting, the triangle, and `M(K4)`.

`LinearSpaceMultiLineCasesSix` (six classes, `#2`–`#7`) and
`LinearSpaceMiddleCasesSix` (seven classes, `#1`–`#7`) are the shallower cuts,
kept because they are the natural statements of those cuts; everything stated
against them is derived from the five-class pair.

## Why this is combinatorics and nothing else

The analysis was already removed upstream.
`Gtz.patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete` turns the
purely combinatorial `Gtz.LinearSpaceListIsComplete` into the campaign's
`Gtz.PatternListIsCompleteUpToRelabel`, and the design side is discharged
unconditionally by `Gtz.isSpanningLinearSpacePattern_dependencePattern` from
`3 ≤ size` and `Gtz.IsPrimitiveDesign` alone.  So nothing below mentions a
`Gtz.WeightedDesign`, Parseval, a bracket, or a real number: the whole content is
about ternary relations on `Fin 6`.

## The transport kit, which is the reusable part

A structural case analysis names labels through existentials and must hand the
enumeration an `Equiv.Perm (Fin 6)`.  Four size-generic lemmas make that free:

* `lineFamilyPattern_map_iff` — relabelling a line family relabels its pattern;
* `agreesOnDistinctTriples_comp_relabel_of_forall` — pointwise facts at
  pulled-back indices become `Gtz.AgreesOnDistinctTriples`, with no case split;
* `isSpanningLinearSpacePattern_comp_relabel` — the three axioms are
  relabelling-invariant, so a case may normalize its labels first;
* `agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete` — agreement with
  a labelled family is exactly soundness plus completeness, which is the shape a
  structural case actually produces.  This one is AXIOM-FREE.

`exists_relabel_agreesOnDistinctTriples_of_labelledFamily` is the case closer:
it takes agreement with the pattern's OWN labelled line family and returns the
enumeration's existential, so a case never writes `Equiv.Perm`, never runs
`fin_cases` over a triple of indices, and never mentions a `Fin 6` numeral.
`forall_mem_threePointLine_pattern` and `forall_mem_fourPointLine_pattern`
discharge the soundness half for lines of three and four points, and
`exists_offLine_triple` and `exists_offFourPointLine_pair` supply the complement
of a named line.  Cases `#1` and `#6` are the two worked templates; a further
case differs from them only in which lines it names.

A recorded negative, found the expensive way: `Gtz.pattern_of_forall_pattern_pivot`
CANNOT prove four-point-line soundness.  It would need the degenerate value
`pattern pivotFirst pivotSecond pivotFirst`, which the three axioms do not supply
and which is false for the natural presentation of a line family.  The four-point
line has to go through `Gtz.IsSpanningLinearSpacePattern.hasLineClosure` twice.

## What is NOT here

* The five middle classes.  A human proof of all five is known: `#7` is the
  four-point line `L` plus one further line, which meets `L` in at most one point
  by the line law and must therefore be `{x} ∪ (Fin 6 \ L)` for a unique `x`; and
  `#2`–`#5` follow from two local incidence counts — at most two three-point
  lines through any label, since three would need six others and only five exist,
  hence at most four lines in all.  Neither is mechanized.
* Any tie-freeness statement.  That is gap 7b and lives in
  `Gtz.Quantitative.HingeStressNarrowing`.
* Seven points.  `Gtz.hingeHoldsAtSize_of_linearSpaceEnumeration_sevenThree`
  already carries the open `Gtz.GtzWeighted 6 3`, so the seven-point enumeration
  is not on the critical path, and a brute-force route there is roughly ten
  orders of magnitude out of reach.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.StratumEmptinessLedger
import Gtz.Design.NearPencilStrictDomination
import Gtz.Design.LinePatternEnumeration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Gtz

/-! ## Transport along a relabelling

Three size-generic lemmas.  The first moves a line family through a
permutation, the second turns pointwise facts stated at relabelled indices into
`Gtz.AgreesOnDistinctTriples` with NO case analysis, and the third says the
three combinatorial axioms are relabelling-invariant. -/

/-- Membership in a relabelled line is membership of the pulled-back label. -/
theorem mem_map_perm_iff {size : ℕ} (relabel : Equiv.Perm (Fin size))
    (line : List (Fin size)) (label : Fin size) :
    label ∈ line.map relabel ↔ relabel.symm label ∈ line := by
  constructor
  · intro hmem
    obtain ⟨source, hsource, himage⟩ := List.mem_map.mp hmem
    have hsymm : relabel.symm label = source := by
      rw [← himage, Equiv.symm_apply_apply]
    exact hsymm ▸ hsource
  · intro hmem
    exact List.mem_map.mpr ⟨relabel.symm label, hmem, Equiv.apply_symm_apply relabel label⟩

/-- **Relabelling a line family relabels its pattern.**  So a proof that a
pattern is the family of its OWN long lines transports to a statement about a
listed family without ever touching the pattern again. -/
theorem lineFamilyPattern_map_iff {size : ℕ} (lines : List (List (Fin size)))
    (relabel : Equiv.Perm (Fin size)) (leftLabel midLabel rightLabel : Fin size) :
    lineFamilyPattern (lines.map (List.map relabel)) leftLabel midLabel rightLabel ↔
      lineFamilyPattern lines (relabel.symm leftLabel) (relabel.symm midLabel)
        (relabel.symm rightLabel) := by
  constructor
  · rintro ⟨image, himage, hleft, hmid, hright⟩
    obtain ⟨line, hline, hshape⟩ := List.mem_map.mp himage
    subst hshape
    exact ⟨line, hline, (mem_map_perm_iff relabel line leftLabel).mp hleft,
      (mem_map_perm_iff relabel line midLabel).mp hmid,
      (mem_map_perm_iff relabel line rightLabel).mp hright⟩
  · rintro ⟨line, hline, hleft, hmid, hright⟩
    exact ⟨line.map relabel, List.mem_map.mpr ⟨line, hline, rfl⟩,
      (mem_map_perm_iff relabel line leftLabel).mpr hleft,
      (mem_map_perm_iff relabel line midLabel).mpr hmid,
      (mem_map_perm_iff relabel line rightLabel).mpr hright⟩

/-- **The relabelling bridge.**  Knowing the pattern at every distinct triple of
PULLED-BACK indices is exactly agreement with the relabelled base, and the proof
is `Gtz`-free: apply the hypothesis at the pushed-forward labels and cancel.  No
`fin_cases`, no enumeration — this is what makes each case of a structural
classification cost only its own twenty facts. -/
theorem agreesOnDistinctTriples_comp_relabel_of_forall {size : ℕ}
    {pattern basePattern : LinePattern size} (relabel : Equiv.Perm (Fin size))
    (hfacts : ∀ leftIndex midIndex rightIndex : Fin size,
      leftIndex ≠ midIndex → leftIndex ≠ rightIndex → midIndex ≠ rightIndex →
        (pattern (relabel.symm leftIndex) (relabel.symm midIndex) (relabel.symm rightIndex)
          ↔ basePattern leftIndex midIndex rightIndex)) :
    AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
      basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  have hshifted := hfacts (relabel leftLabel) (relabel midLabel) (relabel rightLabel)
    (fun hequal => hleftMid (relabel.injective hequal))
    (fun hequal => hleftRight (relabel.injective hequal))
    (fun hequal => hmidRight (relabel.injective hequal))
  simpa only [Equiv.symm_apply_apply] using hshifted

/-- **The three axioms are relabelling-invariant.**  A structural case analysis
may therefore normalize its labels first and reason at fixed indices. -/
theorem isSpanningLinearSpacePattern_comp_relabel {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern) (relabel : Equiv.Perm (Fin size)) :
    IsSpanningLinearSpacePattern (fun leftLabel midLabel rightLabel =>
      pattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  obtain ⟨hleftSwap, hrightSwap, hclosure, hspanning⟩ := haxioms
  refine ⟨fun leftLabel midLabel rightLabel hpattern => hleftSwap _ _ _ hpattern,
    fun leftLabel midLabel rightLabel hpattern => hrightSwap _ _ _ hpattern,
    fun pairFirst pairSecond thirdLabel fourthLabel hpairDistinct hthird hfourth =>
      hclosure _ _ _ _ (fun hequal => hpairDistinct (relabel.injective hequal)) hthird hfourth,
    ?_⟩
  obtain ⟨witnessLeft, witnessMid, witnessRight, hleftMid, hleftRight, hmidRight,
    hnotPattern⟩ := hspanning
  exact ⟨relabel.symm witnessLeft, relabel.symm witnessMid, relabel.symm witnessRight,
    fun hequal => hleftMid (relabel.symm.injective hequal),
    fun hequal => hleftRight (relabel.symm.injective hequal),
    fun hequal => hmidRight (relabel.symm.injective hequal),
    by simpa only [Equiv.apply_symm_apply] using hnotPattern⟩

/-! ## Manufacturing a permutation from six distinct labels

A structural case analysis produces labels through existentials; the enumeration
wants an `Equiv.Perm (Fin 6)`.  These two declarations are the whole bridge and
they are the piece the four-label proof avoided by using a transposition. -/

/-- Six distinct labels of `Fin 6` are all of `Fin 6`. -/
theorem eq_univ_of_six_distinct {slotZero slotOne slotTwo slotThree slotFour slotFive : Fin 6}
    (hcard : ({slotZero, slotOne, slotTwo, slotThree, slotFour, slotFive} :
      Finset (Fin 6)).card = 6) :
    ({slotZero, slotOne, slotTwo, slotThree, slotFour, slotFive} : Finset (Fin 6))
      = Finset.univ :=
  Finset.eq_univ_of_card _ (by simpa using hcard)

/-- The tabulated map of six labels. -/
def sixLabelMap (slotZero slotOne slotTwo slotThree slotFour slotFive : Fin 6) :
    Fin 6 → Fin 6 :=
  ![slotZero, slotOne, slotTwo, slotThree, slotFour, slotFive]

/-- Six pairwise distinct labels give an injective tabulated map. -/
theorem injective_sixLabelMap {slotZero slotOne slotTwo slotThree slotFour slotFive : Fin 6}
    (hpairwise : ∀ leftIndex rightIndex : Fin 6, leftIndex ≠ rightIndex →
      sixLabelMap slotZero slotOne slotTwo slotThree slotFour slotFive leftIndex ≠
        sixLabelMap slotZero slotOne slotTwo slotThree slotFour slotFive rightIndex) :
    Function.Injective (sixLabelMap slotZero slotOne slotTwo slotThree slotFour slotFive) := by
  intro leftIndex rightIndex hequal
  by_contra hne
  exact hpairwise leftIndex rightIndex hne hequal

/-- **The permutation named by six distinct labels**, sending index `i` to the
`i`-th label. -/
noncomputable def sixLabelPerm {slotZero slotOne slotTwo slotThree slotFour slotFive : Fin 6}
    (hinjective : Function.Injective
      (sixLabelMap slotZero slotOne slotTwo slotThree slotFour slotFive)) :
    Equiv.Perm (Fin 6) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinjective)

theorem sixLabelPerm_apply {slotZero slotOne slotTwo slotThree slotFour slotFive : Fin 6}
    (hinjective : Function.Injective
      (sixLabelMap slotZero slotOne slotTwo slotThree slotFour slotFive))
    (index : Fin 6) :
    sixLabelPerm hinjective index =
      sixLabelMap slotZero slotOne slotTwo slotThree slotFour slotFive index := rfl

/-- The inverse of the named permutation, at a named label. -/
theorem sixLabelPerm_symm_apply {slotZero slotOne slotTwo slotThree slotFour slotFive : Fin 6}
    (hinjective : Function.Injective
      (sixLabelMap slotZero slotOne slotTwo slotThree slotFour slotFive))
    (index : Fin 6) :
    (sixLabelPerm hinjective).symm
        (sixLabelMap slotZero slotOne slotTwo slotThree slotFour slotFive index) = index := by
  rw [← sixLabelPerm_apply hinjective index, Equiv.symm_apply_apply]

/-! ## The two extreme classes, closed

The nine six-point classes are ordered by their longest line: `#0` has none and
`#8` has a five-point line.  Both ends fall out of what is already shipped —
`#0` because the line-free pattern is literally `False` on distinct triples, and
`#8` because `Gtz.agreesOnDistinctTriples_nearPencil_of_forall_pattern_off_pole`
pins the near pencil size-generically and the relabelling is one transposition,
exactly as at four labels. -/

/-- Catalogue `#8` at six labels is the near pencil with pole `5`, on every
triple including the degenerate ones. -/
theorem lineFamilyPattern_nearPencilSixFamily_iff (leftLabel midLabel rightLabel : Fin 6) :
    lineFamilyPattern nearPencilSixFamily leftLabel midLabel rightLabel ↔
      nearPencilLinePattern (5 : Fin 6) leftLabel midLabel rightLabel := by
  revert leftLabel midLabel rightLabel
  decide

/-- The near-pencil entry transported to an arbitrary pole by one transposition. -/
theorem agreesOnDistinctTriples_nearPencilSixFamily_comp_swap (poleLabel : Fin 6) :
    AgreesOnDistinctTriples (nearPencilLinePattern poleLabel)
      (fun leftLabel midLabel rightLabel => lineFamilyPattern nearPencilSixFamily
        (Equiv.swap poleLabel 5 leftLabel) (Equiv.swap poleLabel 5 midLabel)
        (Equiv.swap poleLabel 5 rightLabel)) :=
  agreesOnDistinctTriples_of_forall fun leftLabel midLabel rightLabel _ _ _ =>
    ((lineFamilyPattern_nearPencilSixFamily_iff _ _ _).trans
      (nearPencilLinePattern_comp_swap_iff poleLabel 5 leftLabel midLabel rightLabel)).symm

/-- The line-free entry is in the list. -/
theorem lineFree_mem_linePatternListSix :
    lineFamilyPattern (size := 6) [] ∈ linePatternListSix :=
  List.mem_map.mpr ⟨[], by decide, rfl⟩

/-- The near-pencil entry is in the list. -/
theorem nearPencilSixFamily_mem_linePatternListSix :
    lineFamilyPattern nearPencilSixFamily ∈ linePatternListSix :=
  List.mem_map.mpr ⟨nearPencilSixFamily, by decide, rfl⟩

/-- **Class `#0`.**  A pattern with no dependent distinct triple is the line-free
entry, with the identity relabelling. -/
theorem linearSpaceListIsComplete_six_lineFreeCase {pattern : LinePattern 6}
    (hlineFree : ∀ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        ¬ pattern leftLabel midLabel rightLabel) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  refine ⟨lineFamilyPattern [], lineFree_mem_linePatternListSix, Equiv.refl _,
    agreesOnDistinctTriples_of_forall fun leftLabel midLabel rightLabel hleftMid hleftRight
      hmidRight => ⟨fun hpattern => absurd hpattern
        (hlineFree leftLabel midLabel rightLabel hleftMid hleftRight hmidRight), ?_⟩⟩
  rintro ⟨line, hline, -⟩
  exact absurd hline (by simp)

/-- **Class `#8`.**  A pattern all of whose off-pole distinct triples are
dependent is the near-pencil entry, relabelled by the transposition carrying the
pole to `5`. -/
theorem linearSpaceListIsComplete_six_nearPencilCase {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern) (poleLabel : Fin 6)
    (hoffPole : ∀ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        leftLabel ≠ poleLabel → midLabel ≠ poleLabel → rightLabel ≠ poleLabel →
          pattern leftLabel midLabel rightLabel) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) :=
  ⟨lineFamilyPattern nearPencilSixFamily, nearPencilSixFamily_mem_linePatternListSix,
    Equiv.swap poleLabel 5, agreesOnDistinctTriples_trans
      (agreesOnDistinctTriples_nearPencil_of_forall_pattern_off_pole haxioms poleLabel hoffPole)
      (agreesOnDistinctTriples_nearPencilSixFamily_comp_swap poleLabel)⟩

/-! ## The residual: the seven middle families

After the two ends, what is left is a pattern that HAS a dependent distinct
triple and is NOT a near pencil at any pole.  That is exactly the range of
longest-line sizes three and four, which is catalogue `#1` through `#7`. -/

/-- The open half of the six-point enumeration: seven classes, stated so that a
prover may assume both a dependent triple and the failure of every pole. -/
def LinearSpaceMiddleCasesSix : Prop :=
  ∀ pattern : LinePattern 6, IsSpanningLinearSpacePattern pattern →
    (∃ seedLeft seedMid seedRight : Fin 6, seedLeft ≠ seedMid ∧ seedLeft ≠ seedRight ∧
      seedMid ≠ seedRight ∧ pattern seedLeft seedMid seedRight) →
    (∀ poleLabel : Fin 6, ∃ gapLeft gapMid gapRight : Fin 6,
      gapLeft ≠ gapMid ∧ gapLeft ≠ gapRight ∧ gapMid ≠ gapRight ∧
        gapLeft ≠ poleLabel ∧ gapMid ≠ poleLabel ∧ gapRight ≠ poleLabel ∧
          ¬ pattern gapLeft gapMid gapRight) →
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel))

/-! ## The case closer, and the complement helper

A structural case ends by naming six labels and saying which triples of them the
pattern makes dependent.  `exists_relabel_agreesOnDistinctTriples_of_labelledFamily`
turns exactly that into the enumeration's existential, and it does so at the
LABEL level: a case never mentions `Fin 6` numerals, never runs `fin_cases` over
a triple of indices, and never builds a permutation.  `exists_offLine_triple`
supplies the three labels off a named line, which every middle case needs. -/

/-- Fifteen disequalities make the tabulated map injective. -/
theorem injective_sixLabelMap_of_pairwise
    {slotZero slotOne slotTwo slotThree slotFour slotFive : Fin 6}
    (hzeroOne : slotZero ≠ slotOne) (hzeroTwo : slotZero ≠ slotTwo)
    (hzeroThree : slotZero ≠ slotThree) (hzeroFour : slotZero ≠ slotFour)
    (hzeroFive : slotZero ≠ slotFive) (honeTwo : slotOne ≠ slotTwo)
    (honeThree : slotOne ≠ slotThree) (honeFour : slotOne ≠ slotFour)
    (honeFive : slotOne ≠ slotFive) (htwoThree : slotTwo ≠ slotThree)
    (htwoFour : slotTwo ≠ slotFour) (htwoFive : slotTwo ≠ slotFive)
    (hthreeFour : slotThree ≠ slotFour) (hthreeFive : slotThree ≠ slotFive)
    (hfourFive : slotFour ≠ slotFive) :
    Function.Injective (sixLabelMap slotZero slotOne slotTwo slotThree slotFour slotFive) := by
  intro leftIndex rightIndex hequal
  fin_cases leftIndex <;> fin_cases rightIndex <;> simp_all [sixLabelMap, Ne.symm]

/-- **The case closer.**  Agreement with the pattern's own labelled line family
becomes agreement with a LISTED family after relabelling. -/
theorem exists_relabel_agreesOnDistinctTriples_of_labelledFamily
    {pattern : LinePattern 6} {slotZero slotOne slotTwo slotThree slotFour slotFive : Fin 6}
    (hinjective : Function.Injective
      (sixLabelMap slotZero slotOne slotTwo slotThree slotFour slotFive))
    (lines : List (List (Fin 6)))
    (hagree : AgreesOnDistinctTriples pattern (lineFamilyPattern
      (lines.map (List.map (sixLabelMap slotZero slotOne slotTwo slotThree slotFour slotFive))))) :
    ∃ relabel : Equiv.Perm (Fin 6), AgreesOnDistinctTriples pattern
      (fun leftLabel midLabel rightLabel =>
        lineFamilyPattern lines (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  refine ⟨(sixLabelPerm hinjective).symm, fun leftLabel midLabel rightLabel hleftMid hleftRight
    hmidRight => (hagree leftLabel midLabel rightLabel hleftMid hleftRight hmidRight).trans ?_⟩
  exact lineFamilyPattern_map_iff lines (sixLabelPerm hinjective) leftLabel midLabel rightLabel

/-- **The three labels off a named line.**  Every middle case starts by naming a
long line and then needs the rest of `Fin 6`. -/
theorem exists_offLine_triple (lineFirst lineSecond lineThird : Fin 6)
    (hfirstSecond : lineFirst ≠ lineSecond) (hfirstThird : lineFirst ≠ lineThird)
    (hsecondThird : lineSecond ≠ lineThird) :
    ∃ offFirst offSecond offThird : Fin 6,
      offFirst ≠ offSecond ∧ offFirst ≠ offThird ∧ offSecond ≠ offThird ∧
      (∀ offLabel : Fin 6, offLabel = offFirst ∨ offLabel = offSecond ∨ offLabel = offThird →
        offLabel ≠ lineFirst ∧ offLabel ≠ lineSecond ∧ offLabel ≠ lineThird) ∧
      (∀ label : Fin 6, label = lineFirst ∨ label = lineSecond ∨ label = lineThird ∨
        label = offFirst ∨ label = offSecond ∨ label = offThird) := by
  classical
  have hlineCard : ({lineFirst, lineSecond, lineThird} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
      Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]
  have hcomplementCard :
      (({lineFirst, lineSecond, lineThird} : Finset (Fin 6))ᶜ).card = 3 := by
    rw [Finset.card_compl, hlineCard, Fintype.card_fin]
  obtain ⟨offFirst, offSecond, offThird, hoffFirstSecond, hoffFirstThird, hoffSecondThird,
    hcomplement⟩ := Finset.card_eq_three.mp hcomplementCard
  refine ⟨offFirst, offSecond, offThird, hoffFirstSecond, hoffFirstThird, hoffSecondThird,
    ?_, ?_⟩
  · intro offLabel hoffLabel
    have hmemComplement : offLabel ∈ (({lineFirst, lineSecond, lineThird} :
        Finset (Fin 6))ᶜ) := by
      rw [hcomplement]; rcases hoffLabel with rfl | rfl | rfl <;> simp
    have hnotLine : offLabel ∉ ({lineFirst, lineSecond, lineThird} : Finset (Fin 6)) :=
      Finset.mem_compl.mp hmemComplement
    simpa [not_or] using hnotLine
  · intro label
    by_cases hmemLine : label ∈ ({lineFirst, lineSecond, lineThird} : Finset (Fin 6))
    · have := hmemLine; simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
    · have hmemComplement : label ∈ (({lineFirst, lineSecond, lineThird} : Finset (Fin 6))ᶜ) :=
        Finset.mem_compl.mpr hmemLine
      rw [hcomplement] at hmemComplement
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemComplement
      tauto

/-! ## Catalogue `#1`, the worked template

The single-three-point-line class, closed end to end.  It is the pattern every
other middle case follows: name the line, take the complement, prove agreement
with the LABELLED family, hand it to the closer.  The only case analysis is the
twenty-seven-way `rcases` on which of three labels each slot is, and the six
surviving branches are the six slot orders of the one dependent triple. -/

/-- A pattern whose only dependent distinct triples are the orders of one named
triple agrees with that triple's labelled line family. -/
theorem agreesOnDistinctTriples_singleLabelledLine {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (lineFirst lineSecond lineThird : Fin 6) (hfirstSecond : lineFirst ≠ lineSecond)
    (hfirstThird : lineFirst ≠ lineThird) (hsecondThird : lineSecond ≠ lineThird)
    (hline : pattern lineFirst lineSecond lineThird)
    (honly : ∀ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel →
          (leftLabel = lineFirst ∨ leftLabel = lineSecond ∨ leftLabel = lineThird) ∧
          (midLabel = lineFirst ∨ midLabel = lineSecond ∨ midLabel = lineThird) ∧
          (rightLabel = lineFirst ∨ rightLabel = lineSecond ∨ rightLabel = lineThird)) :
    AgreesOnDistinctTriples pattern
      (lineFamilyPattern [[lineFirst, lineSecond, lineThird]]) := by
  obtain ⟨horderOne, horderTwo, horderThree, horderFour, horderFive, horderSix⟩ :=
    pattern_allSlotOrders haxioms lineFirst lineSecond lineThird hline
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  constructor
  · intro hpattern
    obtain ⟨hleftMem, hmidMem, hrightMem⟩ :=
      honly leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
    exact ⟨[lineFirst, lineSecond, lineThird], by simp, by simpa using hleftMem,
      by simpa using hmidMem, by simpa using hrightMem⟩
  · rintro ⟨line, hline', hleftMem, hmidMem, hrightMem⟩
    have hlineEq : line = [lineFirst, lineSecond, lineThird] := by simpa using hline'
    subst hlineEq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hleftMem hmidMem hrightMem
    rcases hleftMem with rfl | rfl | rfl <;> rcases hmidMem with rfl | rfl | rfl <;>
      rcases hrightMem with rfl | rfl | rfl <;> simp_all

/-- **Catalogue `#1`, closed.**  A pattern with exactly one long line, that line
having three points, is the single-line entry after relabelling. -/
theorem linearSpaceListIsComplete_six_singleLineCase {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (lineFirst lineSecond lineThird : Fin 6) (hfirstSecond : lineFirst ≠ lineSecond)
    (hfirstThird : lineFirst ≠ lineThird) (hsecondThird : lineSecond ≠ lineThird)
    (hline : pattern lineFirst lineSecond lineThird)
    (honly : ∀ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel →
          (leftLabel = lineFirst ∨ leftLabel = lineSecond ∨ leftLabel = lineThird) ∧
          (midLabel = lineFirst ∨ midLabel = lineSecond ∨ midLabel = lineThird) ∧
          (rightLabel = lineFirst ∨ rightLabel = lineSecond ∨ rightLabel = lineThird)) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  obtain ⟨offFirst, offSecond, offThird, hoffFirstSecond, hoffFirstThird, hoffSecondThird,
    hoffAvoidsLine, -⟩ := exists_offLine_triple lineFirst lineSecond lineThird hfirstSecond
      hfirstThird hsecondThird
  obtain ⟨hfirstOffFirst, hsecondOffFirst, hthirdOffFirst⟩ :=
    hoffAvoidsLine offFirst (Or.inl rfl)
  obtain ⟨hfirstOffSecond, hsecondOffSecond, hthirdOffSecond⟩ :=
    hoffAvoidsLine offSecond (Or.inr (Or.inl rfl))
  obtain ⟨hfirstOffThird, hsecondOffThird, hthirdOffThird⟩ :=
    hoffAvoidsLine offThird (Or.inr (Or.inr rfl))
  have hinjective := injective_sixLabelMap_of_pairwise (slotZero := lineFirst)
    (slotOne := lineSecond) (slotTwo := lineThird) (slotThree := offFirst)
    (slotFour := offSecond) (slotFive := offThird) hfirstSecond hfirstThird
    (Ne.symm hfirstOffFirst) (Ne.symm hfirstOffSecond) (Ne.symm hfirstOffThird)
    hsecondThird (Ne.symm hsecondOffFirst) (Ne.symm hsecondOffSecond)
    (Ne.symm hsecondOffThird) (Ne.symm hthirdOffFirst) (Ne.symm hthirdOffSecond)
    (Ne.symm hthirdOffThird) hoffFirstSecond hoffFirstThird hoffSecondThird
  obtain ⟨relabel, hrelabel⟩ := exists_relabel_agreesOnDistinctTriples_of_labelledFamily
    hinjective [[0, 1, 2]] (by
      have hmapped : ([[(0 : Fin 6), 1, 2]].map (List.map (sixLabelMap lineFirst lineSecond
          lineThird offFirst offSecond offThird))) = [[lineFirst, lineSecond, lineThird]] := rfl
      rw [hmapped]
      exact agreesOnDistinctTriples_singleLabelledLine haxioms lineFirst lineSecond lineThird
        hfirstSecond hfirstThird hsecondThird hline honly)
  exact ⟨lineFamilyPattern [[0, 1, 2]], List.mem_map.mpr ⟨[[0, 1, 2]], by decide, rfl⟩,
    relabel, hrelabel⟩

/-! ## The general agreement law, and line soundness

Two size-generic lemmas that between them remove all boilerplate from the seven
open cases.  The first says agreement with a labelled line family is exactly
SOUNDNESS (every triple inside a line is dependent) plus COMPLETENESS (every
dependent triple lies inside a line) — so a case's whole obligation is those two
sentences about its own labels.  The second discharges soundness for a
three-point line from a single dependent triple, which is what the pivot law
gives; cases `#1` through `#5` are built entirely out of three-point lines. -/

/-- **Agreement with a labelled family is soundness plus completeness.** -/
theorem agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete {size : ℕ}
    {pattern : LinePattern size} (lines : List (List (Fin size)))
    (hsound : ∀ line ∈ lines, ∀ leftLabel ∈ line, ∀ midLabel ∈ line, ∀ rightLabel ∈ line,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel)
    (hcomplete : ∀ leftLabel midLabel rightLabel : Fin size,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel →
          ∃ line ∈ lines, leftLabel ∈ line ∧ midLabel ∈ line ∧ rightLabel ∈ line) :
    AgreesOnDistinctTriples pattern (lineFamilyPattern lines) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  refine ⟨hcomplete leftLabel midLabel rightLabel hleftMid hleftRight hmidRight, ?_⟩
  rintro ⟨line, hline, hleft, hmid, hright⟩
  exact hsound line hline leftLabel hleft midLabel hmid rightLabel hright hleftMid hleftRight
    hmidRight

/-- **A three-point line is sound from one dependent triple.**  Twenty-seven
slot assignments; twenty-one carry a repeat and die on distinctness, the six
survivors are the slot orders. -/
theorem forall_mem_threePointLine_pattern {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (lineFirst lineSecond lineThird : Fin size)
    (hline : pattern lineFirst lineSecond lineThird) :
    ∀ leftLabel ∈ [lineFirst, lineSecond, lineThird],
      ∀ midLabel ∈ [lineFirst, lineSecond, lineThird],
        ∀ rightLabel ∈ [lineFirst, lineSecond, lineThird],
          leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
            pattern leftLabel midLabel rightLabel := by
  obtain ⟨horderOne, horderTwo, horderThree, horderFour, horderFive, horderSix⟩ :=
    pattern_allSlotOrders haxioms lineFirst lineSecond lineThird hline
  intro leftLabel hleftMem midLabel hmidMem rightLabel hrightMem hleftMid hleftRight hmidRight
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hleftMem hmidMem hrightMem
  rcases hleftMem with rfl | rfl | rfl <;> rcases hmidMem with rfl | rfl | rfl <;>
    rcases hrightMem with rfl | rfl | rfl <;> simp_all

/-- **A four-point line is sound.**  Two dependent triples sharing the pivot pair
give the other two by line closure, and the twenty-four slot orders follow.
`pattern_of_forall_pattern_pivot` cannot be used here: it would need the
DEGENERATE value `pattern pivotFirst pivotSecond pivotFirst`, which the axioms do
not supply and which is false for the natural presentation of a line pattern. -/
theorem forall_mem_fourPointLine_pattern {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (pivotFirst pivotSecond memberThird memberFourth : Fin size)
    (hpivotDistinct : pivotFirst ≠ pivotSecond)
    (hthird : pattern pivotFirst pivotSecond memberThird)
    (hfourth : pattern pivotFirst pivotSecond memberFourth) :
    ∀ leftLabel ∈ [pivotFirst, pivotSecond, memberThird, memberFourth],
      ∀ midLabel ∈ [pivotFirst, pivotSecond, memberThird, memberFourth],
        ∀ rightLabel ∈ [pivotFirst, pivotSecond, memberThird, memberFourth],
          leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
            pattern leftLabel midLabel rightLabel := by
  have hpivotThirdFourth : pattern pivotFirst memberThird memberFourth :=
    haxioms.hasLineClosure pivotFirst pivotSecond memberThird memberFourth hpivotDistinct
      hthird hfourth
  have hsecondThirdFourth : pattern pivotSecond memberThird memberFourth :=
    haxioms.hasLineClosure pivotSecond pivotFirst memberThird memberFourth
      (Ne.symm hpivotDistinct) (haxioms.isLeftSwapClosed _ _ _ hthird)
      (haxioms.isLeftSwapClosed _ _ _ hfourth)
  obtain ⟨hthirdOne, hthirdTwo, hthirdThree, hthirdFour, hthirdFive, hthirdSix⟩ :=
    pattern_allSlotOrders haxioms pivotFirst pivotSecond memberThird hthird
  obtain ⟨hfourthOne, hfourthTwo, hfourthThree, hfourthFour, hfourthFive, hfourthSix⟩ :=
    pattern_allSlotOrders haxioms pivotFirst pivotSecond memberFourth hfourth
  obtain ⟨hmixOne, hmixTwo, hmixThree, hmixFour, hmixFive, hmixSix⟩ :=
    pattern_allSlotOrders haxioms pivotFirst memberThird memberFourth hpivotThirdFourth
  obtain ⟨hlastOne, hlastTwo, hlastThree, hlastFour, hlastFive, hlastSix⟩ :=
    pattern_allSlotOrders haxioms pivotSecond memberThird memberFourth hsecondThirdFourth
  intro leftLabel hleftMem midLabel hmidMem rightLabel hrightMem hleftMid hleftRight hmidRight
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hleftMem hmidMem hrightMem
  rcases hleftMem with rfl | rfl | rfl | rfl <;> rcases hmidMem with rfl | rfl | rfl | rfl <;>
    rcases hrightMem with rfl | rfl | rfl | rfl <;> simp_all

/-! ## Catalogue `#6`, the single four-point line

The same template as `#1`, one point wider.  `forall_mem_fourPointLine_pattern`
supplies soundness, `agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete`
turns soundness plus completeness into agreement, and the case closer does the
rest.  The complement of a four-point line in `Fin 6` is a PAIR, which is why
this case needs its own complement helper. -/

/-- **The two labels off a named four-point line.** -/
theorem exists_offFourPointLine_pair (lineFirst lineSecond lineThird lineFourth : Fin 6)
    (hfirstSecond : lineFirst ≠ lineSecond) (hfirstThird : lineFirst ≠ lineThird)
    (hfirstFourth : lineFirst ≠ lineFourth) (hsecondThird : lineSecond ≠ lineThird)
    (hsecondFourth : lineSecond ≠ lineFourth) (hthirdFourth : lineThird ≠ lineFourth) :
    ∃ offFirst offSecond : Fin 6, offFirst ≠ offSecond ∧
      (∀ offLabel : Fin 6, offLabel = offFirst ∨ offLabel = offSecond →
        offLabel ≠ lineFirst ∧ offLabel ≠ lineSecond ∧ offLabel ≠ lineThird ∧
          offLabel ≠ lineFourth) := by
  classical
  have hlineCard :
      ({lineFirst, lineSecond, lineThird, lineFourth} : Finset (Fin 6)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird, hfirstFourth]),
      Finset.card_insert_of_notMem (by simp [hsecondThird, hsecondFourth]),
      Finset.card_insert_of_notMem (by simp [hthirdFourth]), Finset.card_singleton]
  have hcomplementCard :
      (({lineFirst, lineSecond, lineThird, lineFourth} : Finset (Fin 6))ᶜ).card = 2 := by
    rw [Finset.card_compl, hlineCard, Fintype.card_fin]
  obtain ⟨offFirst, offSecond, hoffDistinct, hcomplement⟩ :=
    Finset.card_eq_two.mp hcomplementCard
  refine ⟨offFirst, offSecond, hoffDistinct, fun offLabel hoffLabel => ?_⟩
  have hmemComplement : offLabel ∈
      (({lineFirst, lineSecond, lineThird, lineFourth} : Finset (Fin 6))ᶜ) := by
    rw [hcomplement]; rcases hoffLabel with rfl | rfl <;> simp
  have hnotLine : offLabel ∉
      ({lineFirst, lineSecond, lineThird, lineFourth} : Finset (Fin 6)) :=
    Finset.mem_compl.mp hmemComplement
  simpa [not_or] using hnotLine

/-- A pattern whose only dependent distinct triples lie inside one named
four-point line agrees with that line's labelled family. -/
theorem agreesOnDistinctTriples_singleLabelledFourPointLine {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (lineFirst lineSecond lineThird lineFourth : Fin 6)
    (hfirstSecond : lineFirst ≠ lineSecond)
    (hthird : pattern lineFirst lineSecond lineThird)
    (hfourth : pattern lineFirst lineSecond lineFourth)
    (honly : ∀ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel →
          (leftLabel = lineFirst ∨ leftLabel = lineSecond ∨ leftLabel = lineThird ∨
            leftLabel = lineFourth) ∧
          (midLabel = lineFirst ∨ midLabel = lineSecond ∨ midLabel = lineThird ∨
            midLabel = lineFourth) ∧
          (rightLabel = lineFirst ∨ rightLabel = lineSecond ∨ rightLabel = lineThird ∨
            rightLabel = lineFourth)) :
    AgreesOnDistinctTriples pattern
      (lineFamilyPattern [[lineFirst, lineSecond, lineThird, lineFourth]]) := by
  refine agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete
    [[lineFirst, lineSecond, lineThird, lineFourth]] ?_ ?_
  · intro line hline
    have hlineEq : line = [lineFirst, lineSecond, lineThird, lineFourth] := by simpa using hline
    subst hlineEq
    exact forall_mem_fourPointLine_pattern haxioms lineFirst lineSecond lineThird lineFourth
      hfirstSecond hthird hfourth
  · intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
    obtain ⟨hleftMem, hmidMem, hrightMem⟩ :=
      honly leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
    exact ⟨[lineFirst, lineSecond, lineThird, lineFourth], by simp, by simpa using hleftMem,
      by simpa using hmidMem, by simpa using hrightMem⟩

/-- **Catalogue `#6`, closed.**  A pattern whose dependent triples all lie inside
one four-point line is the single-four-point-line entry after relabelling. -/
theorem linearSpaceListIsComplete_six_singleFourPointLineCase {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (lineFirst lineSecond lineThird lineFourth : Fin 6)
    (hfirstSecond : lineFirst ≠ lineSecond) (hfirstThird : lineFirst ≠ lineThird)
    (hfirstFourth : lineFirst ≠ lineFourth) (hsecondThird : lineSecond ≠ lineThird)
    (hsecondFourth : lineSecond ≠ lineFourth) (hthirdFourth : lineThird ≠ lineFourth)
    (hthird : pattern lineFirst lineSecond lineThird)
    (hfourth : pattern lineFirst lineSecond lineFourth)
    (honly : ∀ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel →
          (leftLabel = lineFirst ∨ leftLabel = lineSecond ∨ leftLabel = lineThird ∨
            leftLabel = lineFourth) ∧
          (midLabel = lineFirst ∨ midLabel = lineSecond ∨ midLabel = lineThird ∨
            midLabel = lineFourth) ∧
          (rightLabel = lineFirst ∨ rightLabel = lineSecond ∨ rightLabel = lineThird ∨
            rightLabel = lineFourth)) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  obtain ⟨offFirst, offSecond, hoffDistinct, hoffAvoidsLine⟩ :=
    exists_offFourPointLine_pair lineFirst lineSecond lineThird lineFourth hfirstSecond
      hfirstThird hfirstFourth hsecondThird hsecondFourth hthirdFourth
  obtain ⟨hfirstOffFirst, hsecondOffFirst, hthirdOffFirst, hfourthOffFirst⟩ :=
    hoffAvoidsLine offFirst (Or.inl rfl)
  obtain ⟨hfirstOffSecond, hsecondOffSecond, hthirdOffSecond, hfourthOffSecond⟩ :=
    hoffAvoidsLine offSecond (Or.inr rfl)
  have hinjective := injective_sixLabelMap_of_pairwise (slotZero := lineFirst)
    (slotOne := lineSecond) (slotTwo := lineThird) (slotThree := lineFourth)
    (slotFour := offFirst) (slotFive := offSecond) hfirstSecond hfirstThird hfirstFourth
    (Ne.symm hfirstOffFirst) (Ne.symm hfirstOffSecond) hsecondThird hsecondFourth
    (Ne.symm hsecondOffFirst) (Ne.symm hsecondOffSecond) hthirdFourth
    (Ne.symm hthirdOffFirst) (Ne.symm hthirdOffSecond) (Ne.symm hfourthOffFirst)
    (Ne.symm hfourthOffSecond) hoffDistinct
  obtain ⟨relabel, hrelabel⟩ := exists_relabel_agreesOnDistinctTriples_of_labelledFamily
    hinjective [[0, 1, 2, 3]] (by
      have hmapped : ([[(0 : Fin 6), 1, 2, 3]].map (List.map (sixLabelMap lineFirst lineSecond
          lineThird lineFourth offFirst offSecond)))
            = [[lineFirst, lineSecond, lineThird, lineFourth]] := rfl
      rw [hmapped]
      exact agreesOnDistinctTriples_singleLabelledFourPointLine haxioms lineFirst lineSecond
        lineThird lineFourth hfirstSecond hthird hfourth honly)
  exact ⟨lineFamilyPattern [[0, 1, 2, 3]],
    List.mem_map.mpr ⟨[[0, 1, 2, 3]], by decide, rfl⟩, relabel, hrelabel⟩

/-! ## The assembly, and the residual cut to five classes

Four of the nine classes are discharged — `#0`, `#1`, `#6`, `#8` — and what is
left splits along the largest line.  `LinearSpaceFourPointLineCasesSix` is the
single class with a four-point line and something outside it, catalogue `#7`.
`LinearSpaceThreePointLineCasesSix` is the four classes whose every line has
exactly three points and which carry at least two of them: two disjoint, two
meeting, the triangle, and `M(K4)` — catalogue `#2` through `#5`.

Both are UNDISCHARGED.  The coarser residuals `LinearSpaceMultiLineCasesSix`
(six classes) and `LinearSpaceMiddleCasesSix` (seven classes) are kept because
they are the statements of the shallower cuts, and everything stated against them
is derived from the five-class pair. -/

/-- The four open classes whose lines all have exactly three points and which
carry at least two of them: catalogue `#2` through `#5`.  The near-pencil clause
is redundant here — a near pencil carries a four-point line — and is supplied
only because the assembly has it in hand and a weaker obligation is a better
one. -/
def LinearSpaceThreePointLineCasesSix : Prop :=
  ∀ pattern : LinePattern 6, IsSpanningLinearSpacePattern pattern →
    (∀ pivotFirst pivotSecond thirdLabel fourthLabel : Fin 6, pivotFirst ≠ pivotSecond →
      thirdLabel ≠ fourthLabel → thirdLabel ≠ pivotFirst → thirdLabel ≠ pivotSecond →
        fourthLabel ≠ pivotFirst → fourthLabel ≠ pivotSecond →
          pattern pivotFirst pivotSecond thirdLabel →
            ¬ pattern pivotFirst pivotSecond fourthLabel) →
    ∀ seedLeft seedMid seedRight : Fin 6, seedLeft ≠ seedMid → seedLeft ≠ seedRight →
      seedMid ≠ seedRight → pattern seedLeft seedMid seedRight →
        (∃ extraLeft extraMid extraRight : Fin 6, extraLeft ≠ extraMid ∧
          extraLeft ≠ extraRight ∧ extraMid ≠ extraRight ∧
            pattern extraLeft extraMid extraRight ∧
              ¬ ((extraLeft = seedLeft ∨ extraLeft = seedMid ∨ extraLeft = seedRight) ∧
                (extraMid = seedLeft ∨ extraMid = seedMid ∨ extraMid = seedRight) ∧
                (extraRight = seedLeft ∨ extraRight = seedMid ∨ extraRight = seedRight))) →
        (∀ poleLabel : Fin 6, ∃ gapLeft gapMid gapRight : Fin 6,
          gapLeft ≠ gapMid ∧ gapLeft ≠ gapRight ∧ gapMid ≠ gapRight ∧
            gapLeft ≠ poleLabel ∧ gapMid ≠ poleLabel ∧ gapRight ≠ poleLabel ∧
              ¬ pattern gapLeft gapMid gapRight) →
        ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
          AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
            basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel))

/-- The one open class with a four-point line and a dependent triple outside it:
catalogue `#7`, a four-point line meeting a three-point line.  The near-pencil
clause is NOT redundant here — a five-point line carries a four-point line and
triples outside it. -/
def LinearSpaceFourPointLineCasesSix : Prop :=
  ∀ pattern : LinePattern 6, IsSpanningLinearSpacePattern pattern →
    ∀ lineFirst lineSecond lineThird lineFourth : Fin 6, lineFirst ≠ lineSecond →
      lineFirst ≠ lineThird → lineFirst ≠ lineFourth → lineSecond ≠ lineThird →
        lineSecond ≠ lineFourth → lineThird ≠ lineFourth →
          pattern lineFirst lineSecond lineThird → pattern lineFirst lineSecond lineFourth →
    (∃ extraLeft extraMid extraRight : Fin 6, extraLeft ≠ extraMid ∧
      extraLeft ≠ extraRight ∧ extraMid ≠ extraRight ∧
        pattern extraLeft extraMid extraRight ∧
          ¬ ((extraLeft = lineFirst ∨ extraLeft = lineSecond ∨ extraLeft = lineThird ∨
              extraLeft = lineFourth) ∧
            (extraMid = lineFirst ∨ extraMid = lineSecond ∨ extraMid = lineThird ∨
              extraMid = lineFourth) ∧
            (extraRight = lineFirst ∨ extraRight = lineSecond ∨ extraRight = lineThird ∨
              extraRight = lineFourth))) →
    (∀ poleLabel : Fin 6, ∃ gapLeft gapMid gapRight : Fin 6,
      gapLeft ≠ gapMid ∧ gapLeft ≠ gapRight ∧ gapMid ≠ gapRight ∧
        gapLeft ≠ poleLabel ∧ gapMid ≠ poleLabel ∧ gapRight ≠ poleLabel ∧
          ¬ pattern gapLeft gapMid gapRight) →
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel))

/-- **The six-point enumeration, cut to five classes.**  CONDITIONAL on both
residuals; neither is proved anywhere.  What this theorem contributes is the
four-way peel — no dependent triple, one three-point line, one four-point line,
a near-pencil pole. -/
theorem linearSpaceListIsComplete_six_of_lineSizeCases
    (hthreePoint : LinearSpaceThreePointLineCasesSix)
    (hfourPoint : LinearSpaceFourPointLineCasesSix) :
    LinearSpaceListIsComplete 6 linePatternListSix := by
  classical
  intro pattern haxioms
  by_cases hlineFree : ∀ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        ¬ pattern leftLabel midLabel rightLabel
  · exact linearSpaceListIsComplete_six_lineFreeCase hlineFree
  · push Not at hlineFree
    obtain ⟨seedLeft, seedMid, seedRight, hseedLeftMid, hseedLeftRight, hseedMidRight, hseed⟩ :=
      hlineFree
    by_cases hnearPencil : ∃ poleLabel : Fin 6, ∀ leftLabel midLabel rightLabel : Fin 6,
        leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
          leftLabel ≠ poleLabel → midLabel ≠ poleLabel → rightLabel ≠ poleLabel →
            pattern leftLabel midLabel rightLabel
    · obtain ⟨poleLabel, hoffPole⟩ := hnearPencil
      exact linearSpaceListIsComplete_six_nearPencilCase haxioms poleLabel hoffPole
    · push Not at hnearPencil
      by_cases hfourPointLine : ∃ pivotFirst pivotSecond thirdLabel fourthLabel : Fin 6,
          pivotFirst ≠ pivotSecond ∧ thirdLabel ≠ fourthLabel ∧ thirdLabel ≠ pivotFirst ∧
            thirdLabel ≠ pivotSecond ∧ fourthLabel ≠ pivotFirst ∧ fourthLabel ≠ pivotSecond ∧
              pattern pivotFirst pivotSecond thirdLabel ∧
                pattern pivotFirst pivotSecond fourthLabel
      · obtain ⟨pivotFirst, pivotSecond, thirdLabel, fourthLabel, hpivotDistinct,
          hthirdFourth, hthirdPivotFirst, hthirdPivotSecond, hfourthPivotFirst,
          hfourthPivotSecond, hthird, hfourth⟩ := hfourPointLine
        by_cases honlyFour : ∀ leftLabel midLabel rightLabel : Fin 6,
            leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
              pattern leftLabel midLabel rightLabel →
                (leftLabel = pivotFirst ∨ leftLabel = pivotSecond ∨ leftLabel = thirdLabel ∨
                  leftLabel = fourthLabel) ∧
                (midLabel = pivotFirst ∨ midLabel = pivotSecond ∨ midLabel = thirdLabel ∨
                  midLabel = fourthLabel) ∧
                (rightLabel = pivotFirst ∨ rightLabel = pivotSecond ∨
                  rightLabel = thirdLabel ∨ rightLabel = fourthLabel)
        · exact linearSpaceListIsComplete_six_singleFourPointLineCase haxioms pivotFirst
            pivotSecond thirdLabel fourthLabel hpivotDistinct (Ne.symm hthirdPivotFirst)
            (Ne.symm hfourthPivotFirst) (Ne.symm hthirdPivotSecond)
            (Ne.symm hfourthPivotSecond) hthirdFourth hthird hfourth honlyFour
        · refine hfourPoint pattern haxioms pivotFirst pivotSecond thirdLabel fourthLabel
            hpivotDistinct (Ne.symm hthirdPivotFirst) (Ne.symm hfourthPivotFirst)
            (Ne.symm hthirdPivotSecond) (Ne.symm hfourthPivotSecond) hthirdFourth hthird
            hfourth ?_ hnearPencil
          by_contra hnoExtra
          refine honlyFour fun leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
            hdependent => ?_
          by_contra hinsideLine
          exact hnoExtra ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight,
            hdependent, hinsideLine⟩
      · by_cases honlySeed : ∀ leftLabel midLabel rightLabel : Fin 6,
            leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
              pattern leftLabel midLabel rightLabel →
                (leftLabel = seedLeft ∨ leftLabel = seedMid ∨ leftLabel = seedRight) ∧
                (midLabel = seedLeft ∨ midLabel = seedMid ∨ midLabel = seedRight) ∧
                (rightLabel = seedLeft ∨ rightLabel = seedMid ∨ rightLabel = seedRight)
        · exact linearSpaceListIsComplete_six_singleLineCase haxioms seedLeft seedMid seedRight
            hseedLeftMid hseedLeftRight hseedMidRight hseed honlySeed
        · refine hthreePoint pattern haxioms ?_ seedLeft seedMid seedRight hseedLeftMid
            hseedLeftRight hseedMidRight hseed ?_ hnearPencil
          · intro pivotFirst pivotSecond thirdLabel fourthLabel hpivotDistinct hthirdFourth
              hthirdPivotFirst hthirdPivotSecond hfourthPivotFirst hfourthPivotSecond hthird
              hfourth
            exact hfourPointLine ⟨pivotFirst, pivotSecond, thirdLabel, fourthLabel,
              hpivotDistinct, hthirdFourth, hthirdPivotFirst, hthirdPivotSecond,
              hfourthPivotFirst, hfourthPivotSecond, hthird, hfourth⟩
          · by_contra hnoExtra
            refine honlySeed fun leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
              hdependent => ?_
            by_contra hinsideSeed
            exact hnoExtra ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight,
              hdependent, hinsideSeed⟩

/-! ## The coarser residuals, derived

`LinearSpaceMultiLineCasesSix` is the six-class cut and `LinearSpaceMiddleCasesSix`
the seven-class one.  Both are strictly stronger hypotheses than the pair above,
so everything stated against them follows in one step. -/

/-- The open half of the six-point enumeration at the six-class cut: a dependent
triple, a second dependent triple outside the first, and no pole.  Catalogue `#2`
through `#7`. -/
def LinearSpaceMultiLineCasesSix : Prop :=
  ∀ pattern : LinePattern 6, IsSpanningLinearSpacePattern pattern →
    ∀ seedLeft seedMid seedRight : Fin 6, seedLeft ≠ seedMid → seedLeft ≠ seedRight →
      seedMid ≠ seedRight → pattern seedLeft seedMid seedRight →
        (∃ extraLeft extraMid extraRight : Fin 6, extraLeft ≠ extraMid ∧
          extraLeft ≠ extraRight ∧ extraMid ≠ extraRight ∧
            pattern extraLeft extraMid extraRight ∧
              ¬ ((extraLeft = seedLeft ∨ extraLeft = seedMid ∨ extraLeft = seedRight) ∧
                (extraMid = seedLeft ∨ extraMid = seedMid ∨ extraMid = seedRight) ∧
                (extraRight = seedLeft ∨ extraRight = seedMid ∨ extraRight = seedRight))) →
        (∀ poleLabel : Fin 6, ∃ gapLeft gapMid gapRight : Fin 6,
          gapLeft ≠ gapMid ∧ gapLeft ≠ gapRight ∧ gapMid ≠ gapRight ∧
            gapLeft ≠ poleLabel ∧ gapMid ≠ poleLabel ∧ gapRight ≠ poleLabel ∧
              ¬ pattern gapLeft gapMid gapRight) →
        ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
          AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
            basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel))

/-- The six-class residual gives the four-class one: drop the no-four-point-line
clause. -/
theorem linearSpaceThreePointLineCasesSix_of_multiLineCases
    (hmulti : LinearSpaceMultiLineCasesSix) : LinearSpaceThreePointLineCasesSix :=
  fun pattern haxioms _ seedLeft seedMid seedRight hseedLeftMid hseedLeftRight hseedMidRight
    hseed hextra hnoPole =>
    hmulti pattern haxioms seedLeft seedMid seedRight hseedLeftMid hseedLeftRight
      hseedMidRight hseed hextra hnoPole

/-- The six-class residual gives the one-class one: the four-point line's pivot
triple is a seed, and a triple outside the four-point line is outside it. -/
theorem linearSpaceFourPointLineCasesSix_of_multiLineCases
    (hmulti : LinearSpaceMultiLineCasesSix) : LinearSpaceFourPointLineCasesSix := by
  intro pattern haxioms lineFirst lineSecond lineThird lineFourth hfirstSecond hfirstThird
    hfirstFourth hsecondThird hsecondFourth hthirdFourth hthird _ hextra hnoPole
  obtain ⟨extraLeft, extraMid, extraRight, hextraLeftMid, hextraLeftRight, hextraMidRight,
    hextraDependent, hextraOutside⟩ := hextra
  refine hmulti pattern haxioms lineFirst lineSecond lineThird hfirstSecond hfirstThird
    hsecondThird hthird ⟨extraLeft, extraMid, extraRight, hextraLeftMid, hextraLeftRight,
      hextraMidRight, hextraDependent, ?_⟩ hnoPole
  intro hinsideSeed
  exact hextraOutside ⟨Or.imp id (Or.imp id Or.inl) hinsideSeed.1,
    Or.imp id (Or.imp id Or.inl) hinsideSeed.2.1,
    Or.imp id (Or.imp id Or.inl) hinsideSeed.2.2⟩

/-- **The six-point enumeration, cut to six classes.**  CONDITIONAL on
`LinearSpaceMultiLineCasesSix`. -/
theorem linearSpaceListIsComplete_six_of_multiLineCases
    (hmulti : LinearSpaceMultiLineCasesSix) :
    LinearSpaceListIsComplete 6 linePatternListSix :=
  linearSpaceListIsComplete_six_of_lineSizeCases
    (linearSpaceThreePointLineCasesSix_of_multiLineCases hmulti)
    (linearSpaceFourPointLineCasesSix_of_multiLineCases hmulti)

/-- The seven-class residual gives the six-class one: drop the extra triple. -/
theorem linearSpaceMultiLineCasesSix_of_middleCases (hmiddle : LinearSpaceMiddleCasesSix) :
    LinearSpaceMultiLineCasesSix :=
  fun pattern haxioms seedLeft seedMid seedRight hseedLeftMid hseedLeftRight hseedMidRight
    hseed _ hnoPole =>
    hmiddle pattern haxioms
      ⟨seedLeft, seedMid, seedRight, hseedLeftMid, hseedLeftRight, hseedMidRight, hseed⟩ hnoPole

/-- **The six-point enumeration, cut to its middle**, the coarsest form. -/
theorem linearSpaceListIsComplete_six_of_middleCases (hmiddle : LinearSpaceMiddleCasesSix) :
    LinearSpaceListIsComplete 6 linePatternListSix :=
  linearSpaceListIsComplete_six_of_multiLineCases
    (linearSpaceMultiLineCasesSix_of_middleCases hmiddle)

/-! ## The campaign-facing wrappers

`Gtz.patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete` and
`Gtz.hingeHoldsAtSize_of_linearSpaceEnumeration_sixThree` compose with each cut.
Every one of these is CONDITIONAL, and the hinge forms additionally take the
eight tie-freeness obligations, which this file does not touch. -/

/-- The enumeration hypothesis at six labels, from the five-class pair. -/
theorem patternListIsCompleteUpToRelabel_six_of_lineSizeCases
    (hthreePoint : LinearSpaceThreePointLineCasesSix)
    (hfourPoint : LinearSpaceFourPointLineCasesSix) :
    PatternListIsCompleteUpToRelabel 6 linePatternListSix :=
  patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete (by omega) _
    (linearSpaceListIsComplete_six_of_lineSizeCases hthreePoint hfourPoint)

/-- The enumeration hypothesis at six labels, from the six-class cut. -/
theorem patternListIsCompleteUpToRelabel_six_of_multiLineCases
    (hmulti : LinearSpaceMultiLineCasesSix) :
    PatternListIsCompleteUpToRelabel 6 linePatternListSix :=
  patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete (by omega) _
    (linearSpaceListIsComplete_six_of_multiLineCases hmulti)

/-- The enumeration hypothesis at six labels, from the seven-class cut. -/
theorem patternListIsCompleteUpToRelabel_six_of_middleCases
    (hmiddle : LinearSpaceMiddleCasesSix) :
    PatternListIsCompleteUpToRelabel 6 linePatternListSix :=
  patternListIsCompleteUpToRelabel_six_of_multiLineCases
    (linearSpaceMultiLineCasesSix_of_middleCases hmiddle)

/-- **The hinge at six points from five combinatorial classes and the ledger.**
ALL THREE hypotheses are undischarged.  `hthreePoint` is catalogue `#2`–`#5`,
`hfourPoint` is `#7`, and `hresidual` is the eight tie-freeness obligations of
gap 7b.  The contribution is that the combinatorial half no longer mentions `#0`,
`#1`, `#6` or `#8`. -/
theorem hingeHoldsAtSize_of_lineSizeCases_sixThree
    (hthreePoint : LinearSpaceThreePointLineCasesSix)
    (hfourPoint : LinearSpaceFourPointLineCasesSix)
    (hresidual : HingeStratumObligationSix) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_linearSpaceEnumeration_sixThree
    (linearSpaceListIsComplete_six_of_lineSizeCases hthreePoint hfourPoint) hresidual

/-- The six-class form of the hinge assembly. -/
theorem hingeHoldsAtSize_of_multiLineCases_sixThree (hmulti : LinearSpaceMultiLineCasesSix)
    (hresidual : HingeStratumObligationSix) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_lineSizeCases_sixThree
    (linearSpaceThreePointLineCasesSix_of_multiLineCases hmulti)
    (linearSpaceFourPointLineCasesSix_of_multiLineCases hmulti) hresidual

/-- The seven-class form of the hinge assembly. -/
theorem hingeHoldsAtSize_of_middleCases_sixThree (hmiddle : LinearSpaceMiddleCasesSix)
    (hresidual : HingeStratumObligationSix) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_multiLineCases_sixThree
    (linearSpaceMultiLineCasesSix_of_middleCases hmiddle) hresidual

/-! ## Non-vacuity

The four discharged cases are conditional theorems about an arbitrary pattern, so
their content is only as good as the satisfiability of their hypotheses.  Each is
witnessed by the catalogue entry it is supposed to recognise. -/

example : IsSpanningLinearSpacePattern (lineFamilyPattern (size := 6) []) ∧
    ∀ leftLabel midLabel rightLabel : Fin 6, leftLabel ≠ midLabel → leftLabel ≠ rightLabel →
      midLabel ≠ rightLabel → ¬ lineFamilyPattern (size := 6) [] leftLabel midLabel rightLabel := by
  refine ⟨isSpanningLinearSpacePattern_lineFamilyPattern (by decide), ?_⟩
  decide

example : IsSpanningLinearSpacePattern (lineFamilyPattern nearPencilSixFamily) ∧
    ∀ leftLabel midLabel rightLabel : Fin 6, leftLabel ≠ midLabel → leftLabel ≠ rightLabel →
      midLabel ≠ rightLabel → leftLabel ≠ 5 → midLabel ≠ 5 → rightLabel ≠ 5 →
        lineFamilyPattern nearPencilSixFamily leftLabel midLabel rightLabel := by
  refine ⟨isSpanningLinearSpacePattern_lineFamilyPattern (by decide), ?_⟩
  decide

example : IsSpanningLinearSpacePattern (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) ∧
    lineFamilyPattern [[(0 : Fin 6), 1, 2]] 0 1 2 ∧
    ∀ leftLabel midLabel rightLabel : Fin 6, leftLabel ≠ midLabel → leftLabel ≠ rightLabel →
      midLabel ≠ rightLabel → lineFamilyPattern [[(0 : Fin 6), 1, 2]] leftLabel midLabel rightLabel →
        (leftLabel = 0 ∨ leftLabel = 1 ∨ leftLabel = 2) ∧
        (midLabel = 0 ∨ midLabel = 1 ∨ midLabel = 2) ∧
        (rightLabel = 0 ∨ rightLabel = 1 ∨ rightLabel = 2) := by
  refine ⟨isSpanningLinearSpacePattern_lineFamilyPattern (by decide), by decide, ?_⟩
  decide

example : IsSpanningLinearSpacePattern (lineFamilyPattern [[(0 : Fin 6), 1, 2, 3]]) ∧
    lineFamilyPattern [[(0 : Fin 6), 1, 2, 3]] 0 1 2 ∧
    lineFamilyPattern [[(0 : Fin 6), 1, 2, 3]] 0 1 3 ∧
    ∀ leftLabel midLabel rightLabel : Fin 6, leftLabel ≠ midLabel → leftLabel ≠ rightLabel →
      midLabel ≠ rightLabel →
        lineFamilyPattern [[(0 : Fin 6), 1, 2, 3]] leftLabel midLabel rightLabel →
          (leftLabel = 0 ∨ leftLabel = 1 ∨ leftLabel = 2 ∨ leftLabel = 3) ∧
          (midLabel = 0 ∨ midLabel = 1 ∨ midLabel = 2 ∨ midLabel = 3) ∧
          (rightLabel = 0 ∨ rightLabel = 1 ∨ rightLabel = 2 ∨ rightLabel = 3) := by
  refine ⟨isSpanningLinearSpacePattern_lineFamilyPattern (by decide), by decide, by decide, ?_⟩
  decide

end Gtz

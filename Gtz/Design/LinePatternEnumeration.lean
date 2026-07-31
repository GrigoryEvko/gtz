/-
# The line-pattern enumeration: the two canonical lists, the analysis-free
# reduction of the campaign's enumeration hypothesis, and the exact residual

`Gtz.PatternListIsCompleteUpToRelabel` (`Gtz.Design.PrimitiveTightClassification`)
is the campaign's enumeration hypothesis, and
`Gtz.Design.StratumEmptinessLedger` records that it "remains unproved in Lean,
and no `List (LinePattern 6)` or `List (LinePattern 7)` exists anywhere in the
repository".  This file supplies both lists as data and cuts the hypothesis in
two, discharging the half that is linear algebra and isolating the half that is
combinatorics.

## PROVED here, kernel-checked, unconditional

* `lineFamilyPattern` — a `Gtz.LinePattern` presented by its LONG LINES, which is
  the form the classical catalogue is published in, together with the decidability
  instances that make every list-level check a `decide`.
* `lineFamiliesSix` / `linePatternListSix` (nine entries) and
  `lineFamiliesSeven` / `linePatternListSeven` (twenty-three entries) — **the two
  lists**, transcribed from the published catalogue (provenance below), one entry
  per isomorphism class.
* `IsGoodLineFamily`, `isSpanningLinearSpacePattern_lineFamilyPattern`,
  **`forall_isSpanningLinearSpacePattern_linePatternListSix`** and its size-seven
  sibling — every listed family is a genuine spanning partial linear space.  This
  is the transcription check: a family with two lines meeting in two points, or a
  family covering every triple, would fail it.
* `tripleBracket_eq_zero_of_forall_dotProduct_eq_zero`,
  `atomBracket_eq_zero_iff_dotProduct_bracketNormal`,
  **`atomBracket_lineClosure`** — the LINE-CLOSURE LAW for a primitive design:
  two dependent triples sharing their first two labels force one common normal
  that annihilates all four atoms, hence a third dependent triple.  Proved from
  `Gtz.bracketNormal` and `Gtz.bracketNormal_atom_ne_zero_of_isPrimitiveDesign`;
  primitivity enters only to make the normal nonzero.
* **`exists_basisTriple_of_isPrimitiveDesign`** — every primitive design on at
  least three labels has a BASIS triple.  This is the shipped
  `Gtz.exists_basisTriple_of_isTie` with the tie hypothesis removed: Parseval
  alone forbids a common normal, via `Gtz.eq_zero_of_forall_atom_dot_eq_zero`.
* `dependencePattern`, `hasLinePattern_dependencePattern`,
  **`isSpanningLinearSpacePattern_dependencePattern`** — the design's own
  dependence pattern realizes it on the nose and satisfies the three combinatorial
  axioms.  Every hypothesis is `3 <= size` plus primitivity; nothing analytic.
* `LinearSpaceListIsComplete` and
  **`patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete`** — the
  headline.  A purely combinatorial completeness statement about patterns implies
  the design-level enumeration hypothesis.  After this theorem the campaign's
  enumeration obligation contains NO analysis, no Parseval, no design: it is a
  statement about ternary relations on `Fin 6` and `Fin 7`.
* `agreesOnDistinctTriples_symm` / `_trans`, `isNearPencilClass_of_agrees`,
  `IsNearPencilFamily`, `isNearPencilClass_of_isNearPencilFamily`,
  `not_isNearPencilClass_of_not_isNearPencilFamily` — the recognizer bridge in the
  decidable form, so which listed entries the ledger's peel removes is a `decide`.
* **`isNearPencilFamily_iff_eq_nearPencilSixFamily`** / **`_SevenFamily`** — the peel
  removes EXACTLY ONE entry from each list.  The other eight and twenty-two survive
  it, so the residual hypothesis is not vacuous; `not_isNearPencilFamily_uniformSix`
  / `_Seven` and `not_isNearPencilClass_graphicKFourFamilyPattern` name three of the
  survivors, `U(3,6)`, `U(3,7)` and `M(K4)`.
* `not_isGoodLineFamily_overlappingLines`, `not_isGoodLineFamily_fullLine` — the
  family check has TEETH: it rejects two lines meeting in two labels and a family
  covering every triple, which are exactly the two shapes a mistranscribed line
  produces.
* `isFanoClass_fanoLineFamilyPattern` — canonical class thirteen at seven points
  IS `Gtz.fanoLinePattern`, on the nose with the identity relabelling, so the
  ledger's Fano peel fires on this list without a permutation search.
* `pattern_allSlotOrders` and **`pattern_of_forall_pattern_pivot`** — the LINE IS A
  CLIQUE law: three labels each dependent with one distinct pivot pair are
  dependent with each other, with no distinctness hypothesis on the three.  This
  is the workhorse a structural classification runs on, and it is size-generic.
* **`agreesOnDistinctTriples_nearPencil_of_forall_pattern_off_pole`** — the
  near-pencil case of the classification, size-generic: a spanning linear space in
  which every distinct triple avoiding one label is dependent is EXACTLY that
  label's near pencil.  So the near-pencil class is rigid — no triple through the
  pole can be dependent — which is what makes the discharged entry a single class.
* `swap_apply_eq_target_iff`, `nearPencilLinePattern_comp_swap_iff`,
  `lineFamiliesFour`, `linePatternListFour`, `linearSpaceListIsComplete_four` and
  **`patternListIsCompleteUpToRelabel_four`** — **the route closed at four labels**,
  and the first complete enumeration anywhere in the repository.  Four labels
  carry exactly two classes, `U(3,4)` and one three-point line, the second being
  the near pencil at that size, so the pieces above suffice and the relabelling is
  a single transposition.  The hinge's conclusion is FALSE at four labels
  (`not_hingeHoldsAtSize_four_three`), so this bears on the hinge not at all; what
  it establishes is that the reduction chain FIRES, and that
  `LinearSpaceListIsComplete` is a provable shape rather than a decorative one.
* `isPrimitiveDesign_tetraDesign`, **`not_hingeHoldsAtSize_four_three`** and
  `exists_hasLinePattern_relabel_tetraDesign` — the four-label enumeration is NOT
  VACUOUS, and the failure of the hinge at that size is now a theorem rather than a
  remark.  Both needed the primitivity of the tetrahedron, which the repository did
  not carry: `Gtz.not_hasParallelPair_diamondDesign` was the only primitivity
  witness anywhere, and it is a `(5,3)` design.
* `stratumIsTieFree_nearPencilSixFamilyPattern`,
  `stratumIsTieFree_nearPencilSevenFamilyPattern`,
  `stratumIsTieFree_fanoLineFamilyPattern` — the ledger's two peels cashed at the
  three entries they apply to, so the discharged classes are tie-freeness theorems
  about named list entries and not side conditions.
* `hasLinePattern_nearPencilSixFamilyPattern` / `_sevenFamilyPattern` — the two
  near-pencil entries are inhabited by the shipped exact rational designs
  `Gtz.nearPencilSixDesign` / `Gtz.nearPencilSevenDesign`, so the lists are not
  made of unrealizable patterns.
* **`hingeHoldsAtSize_of_linearSpaceEnumeration_sixThree`**,
  **`hingeHoldsAtSize_of_linearSpaceEnumeration_sevenThree`** — the ledger
  assemblies instantiated at these lists.  What they still take is exactly
  (i) the combinatorial completeness and (ii) per surviving family, tie-freeness
  among heavy designs.  Nothing else.

## HYPOTHESIS — the exact remaining gap, and it is finite

`LinearSpaceListIsComplete 6 linePatternListSix` and
`LinearSpaceListIsComplete 7 linePatternListSeven` are NOT proved here.  Each says:
every ternary relation on `Fin n` that is slot-symmetric, closed under the line
law, and spanning agrees on distinct triples with a relabelling of a listed
pattern.  Both are decidable propositions about a finite structure — there is no
undecidability wall.

Both are also TRUE, and the argument is short enough to state exactly.  A
canonicalization outside Lean, over all `6!` and all `7!` relabellings of each
entry's dependent-triple set, finds NINE distinct canonical forms among the nine
six-label entries and TWENTY-THREE among the twenty-three seven-label entries — so
these lists carry nine and twenty-three PAIRWISE NON-ISOMORPHIC classes.  The
classical count of simple rank-three matroids is exactly nine and twenty-three
(A058731; Blackburn-Crapo-Higgs 1973).  A list of nine pairwise-distinct classes,
in a universe with exactly nine classes, is complete.  So each hypothesis follows
from one citation plus one finite computation, and neither is a conjecture.

What is missing is a Lean proof, and the honest reason is measured, not guessed:

* Brute force over the distinct-triple Boolean vector is `2 ^ 20` cases at six
  points and `2 ^ 35` at seven.  Measured kernel throughput on this toolchain is
  about `10 ^ 5` to `10 ^ 6` decision steps per second (a 5040-case `decide` over
  `Equiv.Perm (Fin 7)` with an integer payload costs 76 s), and the axiom test
  alone is of order a hundred steps per case.  Six points is therefore hours at
  best and seven points is out of reach by ten orders of magnitude.
* Canonical-form reduction does not help the SWEEP: canonicalizing is cheap
  (about 253 000 permutation applications for the 352 labelled six-point strata),
  but the universally quantified sweep over non-solutions is what dominates, and
  canonicalization does not shrink it.
* The route that does work is the structural one — case on the maximal line size,
  then on the number of three-point lines — and at six points it is genuinely
  short on paper: max line size five forces the near pencil; four forces
  `[0123]` or `[0123,045]` because only two labels sit off the four-line; three
  forces at most four lines because three lines through one label already need
  seven labels.  Each step needs an explicit `Equiv.Perm` manufactured from
  existential incidence data, which is where the Lean cost sits.  That is the
  next lane's work, and it is bounded: nine cases at six points.

`agreesOnDistinctTriples_nearPencil_of_forall_pattern_off_pole` is the first of
those cases, landed size-generically.

## NOT PROVED, and not claimed

* No instance of `Gtz.GtzWeighted`, no tie-freeness of any open class, no
  `Gtz.HingeHoldsAtSize` unconditionally.  The two assemblies are implications.
* PAIRWISE NON-ISOMORPHISM of the entries is MEASURED, not mechanized.  It is not
  needed for the assemblies — a redundant list is still complete, and a repeated
  class only duplicates an obligation — but it IS what makes the completeness
  hypothesis true by citation, so it is a measured input and is flagged as one.
  What is mechanized instead is that every entry is a legitimate spanning partial
  linear space, which is the property a transcription error would break.
* Which of the twenty-three seven-point entries are NOT Fano classes is not
  proved.  It would need a relabelling-invariant, because the direct test is an
  existential over 5040 permutations per entry and 22 entries of that shape
  extrapolate past twenty-five minutes of kernel time from the measured 76 s
  single sweep.  The separating invariant, computed outside Lean, is the number of
  ordered distinct pairs lying on a long line: 42 for the Fano `#13`, and at most
  36 for every other seven-label entry, the runner-up being `F7 - e` at `#12` with
  36.  Not mechanized, so the seven-label assembly carries `¬ IsFanoClass` as a
  side condition, exactly as the shipped ledger does.
* Nothing here touches the twenty-nine open tie-freeness classes.  No entry moves
  from open to empty; what moves is the shape of the enumeration obligation.

## Provenance of the two lists — this is a TRANSCRIPTION, not a re-derivation

The counts are OEIS A058731 (nonisomorphic simple rank-three matroids on `n`
unlabelled points): `1, 2, 4, 9, 23` at `n = 4, ..., 7` after the offset, and the
labelled counts 352 and 8389 are A056642 minus one.  Published sources:
Blackburn, Crapo and Higgs, *A catalogue of combinatorial geometries*,
Math. Comp. 27 (1973) 155-166; Betten and Betten, *Linear spaces with at most 12
points*, J. Combin. Designs 7 (1999) 119-145.  Machine-readable form: Matsumoto's
*Database of Matroids* (2012), packaged as `matroid-database` and exposed in
SageMath as `matroids.AllMatroids(n, 3, 'simple')`.  The campaign's two
independent exact-rational sweeps reproduce these numbers; the numbers were
already in print in 1973, so the sweeps confirmed rather than discovered them.

A distinct triple is DEPENDENT exactly when it lies inside one of the listed
lines; labels are zero-indexed; every family below is checked here, in Lean, to be
a spanning partial linear space.  Two further cross-checks were run outside Lean
and both passed exactly:

* dependent-triple counts.  Entry by entry the count equals `C(n,3) - (bases)`
  against the catalogue's basis counts — at six labels
  `0, 1, 2, 2, 3, 4, 4, 5, 10` against bases `20, 19, 18, 18, 17, 16, 16, 15, 10`,
  and at seven labels
  `0, 1, 2, 2, 3, 3, 3, 4, 4, 5, 4, 5, 6, 7, 4, 5, 5, 6, 7, 8, 10, 11, 20`
  against bases
  `35, 34, 33, 33, 32, 32, 32, 31, 31, 30, 31, 30, 29, 28, 31, 30, 30, 29, 28, 27,`
  `25, 24, 15`.  A dropped or duplicated line would break this.
* pairwise non-isomorphism, by canonicalizing each entry's dependent-triple set
  over all `6!` and all `7!` relabellings: nine distinct canonical forms among
  nine entries, twenty-three among twenty-three.

## THE NAME DICTIONARY — the two indexings differ, and the collision is dangerous

The campaign's working `qNmM` labels are NOT the catalogue's indices.  Mapping,
fixed here before any list was written:

* the diamond `M(K4 - e)`, the primitive `(5,3)` tie of
  `Gtz.Design.DiamondPrimitive`, is catalogue class `simple_n05_r03_#2`,
  lines `[[0,1,2],[0,3,4]]`;
* near pencil at six points is `#8`, NOT `#3`; `M(K4)` is `#5`, NOT `#8`;
* near pencil at seven points is `#22`, NOT `#4`; the FANO `F7` is `#13`, NOT
  `#22`; the non-Fano `F7 - e` is `#12`, NOT `#21`.

The last line is the trap: the campaign's `q7m22` is the Fano while catalogue
`#22` is the near pencil, so transcribing the catalogue under the `q` names would
swap a discharged class for an open one.  Both discharged seven-point classes are
identified here by theorem — `isFanoClass_fanoLineFamilyPattern` at `#13` and
`isNearPencilFamily_nearPencilSevenFamily` at `#22` — so the dictionary is
mechanized, not merely documented.

## CITED, not reproved here

* `Gtz.LinePattern`, `Gtz.HasLinePattern`, `Gtz.StratumIsTieFree`,
  `Gtz.PatternListIsCompleteUpToRelabel`, `Gtz.IsPrimitiveDesign`,
  `Gtz.atomBracket`, `Gtz.tripleBracket`, `Gtz.bracketNormal`,
  `Gtz.tripleBracket_eq`, `Gtz.tripleBracket_eq_bracketNormal_dotProduct`,
  `Gtz.bracketNormal_atom_ne_zero_of_isPrimitiveDesign`, `Gtz.fanoLinePattern`
  (`Gtz.Design.PrimitiveTightClassification`).
* `Gtz.AgreesOnDistinctTriples`, `Gtz.hasLinePattern_of_agreesOnDistinctTriples`,
  `Gtz.IsNearPencilClass`, `Gtz.IsFanoClass`, `Gtz.IsRelabelOfOnDistinctTriples`,
  `Gtz.isNearPencilClass_iff_exists_pole`,
  `Gtz.StratumIsTieFreeAmongHeavy`,
  `Gtz.hingeHoldsAtSize_of_heavyResidualLedger_sixThree`,
  `Gtz.hingeHoldsAtSize_of_heavyResidualLedger_sevenThree`
  (`Gtz.Design.StratumEmptinessLedger`).
* `Gtz.nearPencilLinePattern` (`Gtz.Design.NearPencilStrictDomination`),
  `Gtz.nearPencilSixDesign`, `Gtz.nearPencilSevenDesign` and their
  `hasLinePattern` witnesses (`Gtz.Design.NearPencilTransport`).
* `Gtz.eq_zero_of_forall_atom_dot_eq_zero` (`Gtz.Reduction.Naimark`),
  `Gtz.HingeHoldsAtSize` (`Gtz.Reduction.SplitTransfer`).
* Non-representability of `F7` over the reals is already mechanized upstream in
  `Gtz.fanoBrackets_impossible`; nothing here reproves it.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.StratumEmptinessLedger
import Gtz.Design.NearPencilStrictDomination
import Gtz.Design.NearPencilTransport
import Gtz.Reduction.Naimark
import Gtz.Reduction.SplitTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Gtz

open Matrix

/-! ## Patterns presented by their long lines

The classical presentation of a rank-three simple matroid is its list of LONG
LINES — the maximal collinear sets of at least three points — because every other
pair of points spans a two-point line that carries no dependent triple.  A
distinct triple is dependent exactly when some listed line contains all three of
its labels, so a family of lines determines a `Gtz.LinePattern`, and that is the
form in which the two lists below are transcribed. -/

/-- The pattern whose dependent triples are those contained in a listed line.
Values on degenerate triples are whatever this formula gives; `Gtz.HasLinePattern`
never looks at them, and every comparison below runs through
`Gtz.AgreesOnDistinctTriples`. -/
def lineFamilyPattern {size : ℕ} (lines : List (List (Fin size))) : LinePattern size :=
  fun leftLabel midLabel rightLabel =>
    ∃ line ∈ lines, leftLabel ∈ line ∧ midLabel ∈ line ∧ rightLabel ∈ line

instance decidableLineFamilyPattern {size : ℕ} (lines : List (List (Fin size)))
    (leftLabel midLabel rightLabel : Fin size) :
    Decidable (lineFamilyPattern lines leftLabel midLabel rightLabel) := by
  unfold lineFamilyPattern
  infer_instance

instance decidableNearPencilLinePattern {size : ℕ}
    (poleLabel leftLabel midLabel rightLabel : Fin size) :
    Decidable (nearPencilLinePattern poleLabel leftLabel midLabel rightLabel) := by
  unfold nearPencilLinePattern
  infer_instance

/-- `Gtz.AgreesOnDistinctTriples` is definitionally the pointwise `Iff` on
distinct triples; this is the shape a `decide` produces. -/
theorem agreesOnDistinctTriples_of_forall {size : ℕ} {pattern basePattern : LinePattern size}
    (hpointwise : ∀ leftLabel midLabel rightLabel : Fin size,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        (pattern leftLabel midLabel rightLabel ↔ basePattern leftLabel midLabel rightLabel)) :
    AgreesOnDistinctTriples pattern basePattern := hpointwise

/-- Agreement on distinct triples is symmetric. -/
theorem agreesOnDistinctTriples_symm {size : ℕ} {pattern basePattern : LinePattern size}
    (hagree : AgreesOnDistinctTriples pattern basePattern) :
    AgreesOnDistinctTriples basePattern pattern :=
  fun leftLabel midLabel rightLabel hleftMid hleftRight hmidRight =>
    (hagree leftLabel midLabel rightLabel hleftMid hleftRight hmidRight).symm

/-- Agreement on distinct triples is transitive. -/
theorem agreesOnDistinctTriples_trans {size : ℕ}
    {pattern middlePattern basePattern : LinePattern size}
    (hfirst : AgreesOnDistinctTriples pattern middlePattern)
    (hsecond : AgreesOnDistinctTriples middlePattern basePattern) :
    AgreesOnDistinctTriples pattern basePattern :=
  fun leftLabel midLabel rightLabel hleftMid hleftRight hmidRight =>
    (hfirst leftLabel midLabel rightLabel hleftMid hleftRight hmidRight).trans
      (hsecond leftLabel midLabel rightLabel hleftMid hleftRight hmidRight)

/-! ## The three combinatorial axioms

A dependence pattern of a real primitive design satisfies three things, and all
three are proved below with no analysis beyond Parseval: it is symmetric in its
three slots, it obeys the LINE LAW (two dependent triples sharing their first two
labels force a third), and it is SPANNING (some distinct triple is independent).

Those three properties also CHARACTERIZE a spanning linear space — take the line
through a pair to be the pair together with every label dependent with it, and the
line law makes that well defined — which is why classifying such patterns is the
classical matroid count and not a question about the reals.  Only the forward
direction is used and only the forward direction is proved here; the converse is
standard and appears in this file as motivation, not as a step. -/

/-- The combinatorial shadow of a primitive rank-three design.  Slot symmetry is
stated with no distinctness hypothesis and the line law with only the shared pair
distinct, because that is what the design side actually delivers — the weaker the
hypotheses here, the more constrained the patterns a completeness statement has to
cover. -/
structure IsSpanningLinearSpacePattern {size : ℕ} (pattern : LinePattern size) : Prop where
  isLeftSwapClosed : ∀ leftLabel midLabel rightLabel : Fin size,
    pattern leftLabel midLabel rightLabel → pattern midLabel leftLabel rightLabel
  isRightSwapClosed : ∀ leftLabel midLabel rightLabel : Fin size,
    pattern leftLabel midLabel rightLabel → pattern leftLabel rightLabel midLabel
  hasLineClosure : ∀ pairFirst pairSecond thirdLabel fourthLabel : Fin size,
    pairFirst ≠ pairSecond → pattern pairFirst pairSecond thirdLabel →
      pattern pairFirst pairSecond fourthLabel → pattern pairFirst thirdLabel fourthLabel
  isSpanning : ∃ leftLabel midLabel rightLabel : Fin size,
    leftLabel ≠ midLabel ∧ leftLabel ≠ rightLabel ∧ midLabel ≠ rightLabel ∧
      ¬ pattern leftLabel midLabel rightLabel

/-- Rotating the three slots, from the two swap generators. -/
theorem pattern_rotate_of_isSpanningLinearSpacePattern {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (leftLabel midLabel rightLabel : Fin size)
    (hpattern : pattern leftLabel midLabel rightLabel) :
    pattern midLabel rightLabel leftLabel :=
  haxioms.isRightSwapClosed _ _ _ (haxioms.isLeftSwapClosed _ _ _ hpattern)

/-! ## The lists

Two families are recorded twice: once inside the flat list that the completeness
statement ranges over, and once under a name, so that the named identifications
below (near pencil, Fano) are statements about actual list entries. -/

/-- Catalogue class `simple_n06_r03_#8`: one five-point line, pole `5`. -/
def nearPencilSixFamily : List (List (Fin 6)) := [[0, 1, 2, 3, 4]]

/-- Catalogue class `simple_n06_r03_#5`, the graphic matroid `M(K4)`: the four
triangles of `K4` on six edge labels.  This is the campaign's `q6m8`, the sharpest
of the open six-point classes. -/
def graphicKFourFamily : List (List (Fin 6)) := [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]

/-- The nine isomorphism classes of spanning linear spaces on six labels, in
catalogue order `#0` through `#8`.  Line-size multisets: none, `{3}`, `{3,3}`
disjoint, `{3,3}` meeting, `{3,3,3}`, `{3,3,3,3}`, `{4}`, `{4,3}`, `{5}`. -/
def lineFamiliesSix : List (List (List (Fin 6))) :=
  [ []
  , [[0, 1, 2]]
  , [[0, 1, 2], [3, 4, 5]]
  , [[0, 1, 2], [0, 3, 4]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]
  , [[0, 1, 2, 3]]
  , [[0, 1, 2, 3], [0, 4, 5]]
  , [[0, 1, 2, 3, 4]] ]

/-- Catalogue class `simple_n07_r03_#13`, the Fano plane `PG(2,2)`. -/
def fanoLineFamily : List (List (Fin 7)) :=
  [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]]

/-- Catalogue class `simple_n07_r03_#12`, the non-Fano `F7 - e`: the Fano less the
line `[0,5,6]`.  The campaign's `q7m21`. -/
def fanoMinusLineFamily : List (List (Fin 7)) :=
  [[0, 1, 2], [0, 3, 4], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]]

/-- Catalogue class `simple_n07_r03_#22`: one six-point line, pole `6`. -/
def nearPencilSevenFamily : List (List (Fin 7)) := [[0, 1, 2, 3, 4, 5]]

/-- The twenty-three isomorphism classes of spanning linear spaces on seven
labels, in catalogue order `#0` through `#22`.  `#12` is `F7 - e`, `#13` is the
Fano, `#22` is the near pencil. -/
def lineFamiliesSeven : List (List (List (Fin 7))) :=
  [ []
  , [[0, 1, 2]]
  , [[0, 1, 2], [3, 4, 5]]
  , [[0, 1, 2], [0, 3, 4]]
  , [[0, 1, 2], [0, 3, 4], [1, 5, 6]]
  , [[0, 1, 2], [0, 3, 4], [0, 5, 6]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 6]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 3, 6]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 3, 6], [4, 5, 6]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 3, 6], [2, 4, 5]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]]
  , [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]]
  , [[0, 1, 2, 3]]
  , [[0, 1, 2, 3], [4, 5, 6]]
  , [[0, 1, 2, 3], [0, 4, 5]]
  , [[0, 1, 2, 3], [0, 4, 5], [1, 4, 6]]
  , [[0, 1, 2, 3], [0, 4, 5], [1, 4, 6], [2, 5, 6]]
  , [[0, 1, 2, 3], [0, 4, 5, 6]]
  , [[0, 1, 2, 3, 4]]
  , [[0, 1, 2, 3, 4], [0, 5, 6]]
  , [[0, 1, 2, 3, 4, 5]] ]

/-- The nine six-point patterns. -/
def linePatternListSix : List (LinePattern 6) := lineFamiliesSix.map lineFamilyPattern

/-- The twenty-three seven-point patterns. -/
def linePatternListSeven : List (LinePattern 7) := lineFamiliesSeven.map lineFamilyPattern

theorem length_lineFamiliesSix : lineFamiliesSix.length = 9 := by decide

theorem length_lineFamiliesSeven : lineFamiliesSeven.length = 23 := by decide

/-! ## Every listed family is a genuine spanning partial linear space

The catalogue's data is a list of lines, and a transcription error would show up
as two lines sharing two labels (which would make the pattern violate the line
law) or as a family covering every triple (which would make it non-spanning).
Both failure modes are excluded by one `decide` per list, through a decidable
condition on the FAMILY rather than on the pattern. -/

/-- Two listed lines sharing two distinct labels have the same labels.  This is
the partial-linear-space condition, and it is what makes the line law hold. -/
def IsPartialLinearSpaceFamily {size : ℕ} (lines : List (List (Fin size))) : Prop :=
  ∀ firstLine ∈ lines, ∀ secondLine ∈ lines, ∀ sharedFirst sharedSecond : Fin size,
    sharedFirst ≠ sharedSecond →
      sharedFirst ∈ firstLine → sharedSecond ∈ firstLine →
      sharedFirst ∈ secondLine → sharedSecond ∈ secondLine →
      ∀ label ∈ secondLine, label ∈ firstLine

/-- Some distinct triple avoids every listed line. -/
def IsSpanningFamily {size : ℕ} (lines : List (List (Fin size))) : Prop :=
  ∃ leftLabel midLabel rightLabel : Fin size,
    leftLabel ≠ midLabel ∧ leftLabel ≠ rightLabel ∧ midLabel ≠ rightLabel ∧
      ¬ lineFamilyPattern lines leftLabel midLabel rightLabel

/-- A family the catalogue could legitimately have printed. -/
def IsGoodLineFamily {size : ℕ} (lines : List (List (Fin size))) : Prop :=
  IsPartialLinearSpaceFamily lines ∧ IsSpanningFamily lines

instance decidableIsPartialLinearSpaceFamily {size : ℕ} (lines : List (List (Fin size))) :
    Decidable (IsPartialLinearSpaceFamily lines) := by
  unfold IsPartialLinearSpaceFamily
  infer_instance

instance decidableIsSpanningFamily {size : ℕ} (lines : List (List (Fin size))) :
    Decidable (IsSpanningFamily lines) := by
  unfold IsSpanningFamily
  infer_instance

instance decidableIsGoodLineFamily {size : ℕ} (lines : List (List (Fin size))) :
    Decidable (IsGoodLineFamily lines) := by
  unfold IsGoodLineFamily
  infer_instance

/-- **A good family's pattern satisfies the three axioms.**  Slot symmetry is a
reordering of one conjunction; the line law is exactly the partial-linear-space
condition applied to the two lines carrying the shared pair. -/
theorem isSpanningLinearSpacePattern_lineFamilyPattern {size : ℕ}
    {lines : List (List (Fin size))} (hgood : IsGoodLineFamily lines) :
    IsSpanningLinearSpacePattern (lineFamilyPattern lines) := by
  obtain ⟨hpartial, hspanning⟩ := hgood
  refine ⟨?_, ?_, ?_, hspanning⟩
  · rintro leftLabel midLabel rightLabel ⟨line, hline, hleft, hmid, hright⟩
    exact ⟨line, hline, hmid, hleft, hright⟩
  · rintro leftLabel midLabel rightLabel ⟨line, hline, hleft, hmid, hright⟩
    exact ⟨line, hline, hleft, hright, hmid⟩
  · rintro pairFirst pairSecond thirdLabel fourthLabel hpairDistinct
      ⟨thirdLine, hthirdLine, hthirdFirst, hthirdSecond, hthirdLabel⟩
      ⟨fourthLine, hfourthLine, hfourthFirst, hfourthSecond, hfourthLabel⟩
    exact ⟨thirdLine, hthirdLine, hthirdFirst, hthirdLabel,
      hpartial thirdLine hthirdLine fourthLine hfourthLine pairFirst pairSecond hpairDistinct
        hthirdFirst hthirdSecond hfourthFirst hfourthSecond fourthLabel hfourthLabel⟩

theorem forall_isGoodLineFamily_six : ∀ lines ∈ lineFamiliesSix, IsGoodLineFamily lines := by
  decide

theorem forall_isGoodLineFamily_seven : ∀ lines ∈ lineFamiliesSeven, IsGoodLineFamily lines := by
  decide

/-- **Every six-point entry is a spanning linear space.** -/
theorem forall_isSpanningLinearSpacePattern_linePatternListSix :
    ∀ pattern ∈ linePatternListSix, IsSpanningLinearSpacePattern pattern := by
  intro pattern hmem
  obtain ⟨lines, hlines, hshape⟩ := List.mem_map.mp hmem
  exact hshape ▸ isSpanningLinearSpacePattern_lineFamilyPattern
    (forall_isGoodLineFamily_six lines hlines)

/-- **Every seven-point entry is a spanning linear space.** -/
theorem forall_isSpanningLinearSpacePattern_linePatternListSeven :
    ∀ pattern ∈ linePatternListSeven, IsSpanningLinearSpacePattern pattern := by
  intro pattern hmem
  obtain ⟨lines, hlines, hshape⟩ := List.mem_map.mp hmem
  exact hshape ▸ isSpanningLinearSpacePattern_lineFamilyPattern
    (forall_isGoodLineFamily_seven lines hlines)

/-! ## The design side: the three axioms hold, unconditionally

Everything in this section is about a real primitive design and none of it
assumes a tie, a ledger entry, or `Gtz.GtzWeighted` at any size.  The engine is
`Gtz.bracketNormal`: the bracket of a fixed pair against a varying third slot is
a PAIRING, so all triples dependent with one pair share ONE normal, and
primitivity makes that normal nonzero. -/

/-- A repeated outer slot kills the bracket. -/
theorem tripleBracket_eq_zero_of_outerRepeat (leftVec midVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec leftVec = 0 := by
  simp only [tripleBracket_eq]; ring

/-- A repeated tail slot kills the bracket. -/
theorem tripleBracket_eq_zero_of_tailRepeat (leftVec midVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec midVec = 0 := by
  simp only [tripleBracket_eq]; ring

/-- **Three vectors orthogonal to one nonzero direction are dependent.**  The
matrix carrying them as rows kills that direction, so its determinant vanishes. -/
theorem tripleBracket_eq_zero_of_forall_dotProduct_eq_zero
    (leftVec midVec rightVec normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (hleft : leftVec ⬝ᵥ normalVec = 0) (hmid : midVec ⬝ᵥ normalVec = 0)
    (hright : rightVec ⬝ᵥ normalVec = 0) :
    tripleBracket leftVec midVec rightVec = 0 := by
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨normalVec, hnormalNe, ?_⟩
  funext rowIndex
  fin_cases rowIndex
  · simpa [Matrix.mulVec] using hleft
  · simpa [Matrix.mulVec] using hmid
  · simpa [Matrix.mulVec] using hright

/-- A triple is dependent exactly when its third atom is orthogonal to the first
pair's normal. -/
theorem atomBracket_eq_zero_iff_dotProduct_bracketNormal {size : ℕ} (D : WeightedDesign size 3)
    (pairFirst pairSecond thirdLabel : Fin size) :
    atomBracket D pairFirst pairSecond thirdLabel = 0 ↔
      D.atom thirdLabel ⬝ᵥ bracketNormal (D.atom pairFirst) (D.atom pairSecond) = 0 := by
  rw [atomBracket, tripleBracket_eq_bracketNormal_dotProduct, dotProduct_comm]

/-- **The line-closure law for a primitive design.**  Two dependent triples
sharing their first two labels put all four atoms in the plane orthogonal to that
pair's normal, so every triple among the four is dependent — here in the form the
combinatorial axiom asks for.  Only the shared pair needs to be distinct. -/
theorem atomBracket_lineClosure {size : ℕ} (hsize : 2 ≤ size) (D : WeightedDesign size 3)
    (hprimitive : IsPrimitiveDesign D)
    (pairFirst pairSecond thirdLabel fourthLabel : Fin size)
    (hpairDistinct : pairFirst ≠ pairSecond)
    (hthird : atomBracket D pairFirst pairSecond thirdLabel = 0)
    (hfourth : atomBracket D pairFirst pairSecond fourthLabel = 0) :
    atomBracket D pairFirst thirdLabel fourthLabel = 0 := by
  have hnormalNe := bracketNormal_atom_ne_zero_of_isPrimitiveDesign hsize D hprimitive
    pairFirst pairSecond hpairDistinct
  refine tripleBracket_eq_zero_of_forall_dotProduct_eq_zero _ _ _ _ hnormalNe ?_ ?_ ?_
  · exact (atomBracket_eq_zero_iff_dotProduct_bracketNormal D pairFirst pairSecond pairFirst).mp
      (tripleBracket_eq_zero_of_outerRepeat _ _)
  · exact (atomBracket_eq_zero_iff_dotProduct_bracketNormal D pairFirst pairSecond
      thirdLabel).mp hthird
  · exact (atomBracket_eq_zero_iff_dotProduct_bracketNormal D pairFirst pairSecond
      fourthLabel).mp hfourth

/-- **Every primitive design has a basis triple.**  If every distinct triple were
dependent, the first pair's normal would annihilate every atom, and Parseval
forbids that (`Gtz.eq_zero_of_forall_atom_dot_eq_zero`).  This is the shipped
`Gtz.exists_basisTriple_of_isTie` with the tie hypothesis deleted. -/
theorem exists_basisTriple_of_isPrimitiveDesign {size : ℕ} (hsize : 3 ≤ size)
    (D : WeightedDesign size 3) (hprimitive : IsPrimitiveDesign D) :
    ∃ leftLabel midLabel rightLabel : Fin size,
      leftLabel ≠ midLabel ∧ leftLabel ≠ rightLabel ∧ midLabel ≠ rightLabel ∧
        atomBracket D leftLabel midLabel rightLabel ≠ 0 := by
  by_contra hnoBasis
  push Not at hnoBasis
  set pairFirst : Fin size := ⟨0, by omega⟩ with hpairFirst
  set pairSecond : Fin size := ⟨1, by omega⟩ with hpairSecond
  have hpairDistinct : pairFirst ≠ pairSecond := by
    rw [hpairFirst, hpairSecond]
    exact fun hequal => by simpa using congrArg Fin.val hequal
  have hnormalNe := bracketNormal_atom_ne_zero_of_isPrimitiveDesign (by omega) D hprimitive
    pairFirst pairSecond hpairDistinct
  refine hnormalNe (eq_zero_of_forall_atom_dot_eq_zero D fun label => ?_)
  by_cases hfirst : label = pairFirst
  · rw [hfirst]
    exact (atomBracket_eq_zero_iff_dotProduct_bracketNormal D pairFirst pairSecond pairFirst).mp
      (tripleBracket_eq_zero_of_outerRepeat _ _)
  · by_cases hsecond : label = pairSecond
    · rw [hsecond]
      exact (atomBracket_eq_zero_iff_dotProduct_bracketNormal D pairFirst pairSecond
        pairSecond).mp (tripleBracket_eq_zero_of_tailRepeat _ _)
    · exact (atomBracket_eq_zero_iff_dotProduct_bracketNormal D pairFirst pairSecond label).mp
        (hnoBasis pairFirst pairSecond label hpairDistinct (Ne.symm hfirst) (Ne.symm hsecond))

/-- The design's own line pattern: the dependent triples, on the nose. -/
def dependencePattern {size : ℕ} (D : WeightedDesign size 3) : LinePattern size :=
  fun leftLabel midLabel rightLabel => atomBracket D leftLabel midLabel rightLabel = 0

/-- Every design realizes its own dependence pattern, by definition. -/
theorem hasLinePattern_dependencePattern {size : ℕ} (D : WeightedDesign size 3) :
    HasLinePattern D (dependencePattern D) :=
  fun _ _ _ _ _ _ => Iff.rfl

/-- **The design side of the enumeration, discharged.**  A primitive design's
dependence pattern satisfies all three combinatorial axioms.  Slot symmetry is
bracket antisymmetry, the line law is `atomBracket_lineClosure`, and spanning is
`exists_basisTriple_of_isPrimitiveDesign`.  No tie, no criticality, no
`Gtz.GtzWeighted` at any size. -/
theorem isSpanningLinearSpacePattern_dependencePattern {size : ℕ} (hsize : 3 ≤ size)
    (D : WeightedDesign size 3) (hprimitive : IsPrimitiveDesign D) :
    IsSpanningLinearSpacePattern (dependencePattern D) := by
  refine ⟨fun leftLabel midLabel rightLabel hpattern => ?_,
    fun leftLabel midLabel rightLabel hpattern => ?_,
    fun pairFirst pairSecond thirdLabel fourthLabel hpairDistinct hthird hfourth =>
      atomBracket_lineClosure (by omega) D hprimitive pairFirst pairSecond thirdLabel fourthLabel
        hpairDistinct hthird hfourth,
    exists_basisTriple_of_isPrimitiveDesign hsize D hprimitive⟩
  · show tripleBracket _ _ _ = 0
    rw [tripleBracket_swapLeft]
    exact neg_eq_zero.mpr hpattern
  · show tripleBracket _ _ _ = 0
    rw [tripleBracket_swapRight]
    exact neg_eq_zero.mpr hpattern

/-! ## The reduction: the enumeration hypothesis contains no analysis

`Gtz.PatternListIsCompleteUpToRelabel` quantifies over `Gtz.WeightedDesign`s, so
as stated it mixes Parseval with combinatorics.  The statement below quantifies
over ternary relations only.  The theorem after it says the second implies the
first, which is the point of this file: after it, the campaign's enumeration
obligation is a finite combinatorial fact about `Fin 6` and `Fin 7`. -/

/-- Every spanning linear space on `Fin size` is, up to relabelling, one of the
listed patterns.  Purely combinatorial: no design occurs in this statement. -/
def LinearSpaceListIsComplete (size : ℕ) (patterns : List (LinePattern size)) : Prop :=
  ∀ pattern : LinePattern size, IsSpanningLinearSpacePattern pattern →
    ∃ basePattern ∈ patterns, ∃ relabel : Equiv.Perm (Fin size),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel))

/-- **The reduction.**  Combinatorial completeness implies the campaign's
enumeration hypothesis.  The design contributes exactly one thing — that its
dependence pattern is a spanning linear space — and that is
`isSpanningLinearSpacePattern_dependencePattern`, proved unconditionally above. -/
theorem patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete {size : ℕ}
    (hsize : 3 ≤ size) (patterns : List (LinePattern size))
    (hcomplete : LinearSpaceListIsComplete size patterns) :
    PatternListIsCompleteUpToRelabel size patterns := by
  intro D hprimitive
  obtain ⟨basePattern, hmem, relabel, hagree⟩ := hcomplete (dependencePattern D)
    (isSpanningLinearSpacePattern_dependencePattern hsize D hprimitive)
  exact ⟨basePattern, hmem, relabel,
    hasLinePattern_of_agreesOnDistinctTriples (hasLinePattern_dependencePattern D) hagree⟩

/-! ## Which listed entries the ledger's peel removes

`Gtz.IsNearPencilClass` and `Gtz.IsFanoClass` quantify over permutations, which is
not something to `decide` at seven labels.  For a near pencil no search is needed:
`Gtz.isNearPencilClass_iff_exists_pole` reduces it to matching a POLE, and that is
a `decide` over `Fin size`. -/

/-- The near pencil, as a decidable condition on a line family. -/
def IsNearPencilFamily {size : ℕ} (lines : List (List (Fin size))) : Prop :=
  ∃ poleLabel : Fin size, ∀ leftLabel midLabel rightLabel : Fin size,
    leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
      (lineFamilyPattern lines leftLabel midLabel rightLabel ↔
        nearPencilLinePattern poleLabel leftLabel midLabel rightLabel)

instance decidableIsNearPencilFamily {size : ℕ} (lines : List (List (Fin size))) :
    Decidable (IsNearPencilFamily lines) := by
  unfold IsNearPencilFamily
  infer_instance

theorem isNearPencilClass_of_isNearPencilFamily {size : ℕ} {lines : List (List (Fin size))}
    (hfamily : IsNearPencilFamily lines) : IsNearPencilClass (lineFamilyPattern lines) := by
  obtain ⟨poleLabel, hagree⟩ := hfamily
  exact (isNearPencilClass_iff_exists_pole _).mpr ⟨poleLabel, hagree⟩

theorem not_isNearPencilClass_of_not_isNearPencilFamily {size : ℕ}
    {lines : List (List (Fin size))} (hnotFamily : ¬ IsNearPencilFamily lines) :
    ¬ IsNearPencilClass (lineFamilyPattern lines) := by
  intro hclass
  obtain ⟨poleLabel, hagree⟩ := (isNearPencilClass_iff_exists_pole _).mp hclass
  exact hnotFamily ⟨poleLabel, hagree⟩

theorem isNearPencilFamily_nearPencilSixFamily :
    IsNearPencilFamily nearPencilSixFamily := by decide

theorem isNearPencilFamily_nearPencilSevenFamily :
    IsNearPencilFamily nearPencilSevenFamily := by decide

/-- **The six-point peel removes exactly the catalogue's `#8`.**  So eight entries
survive it, `M(K4)` and the line-free `U(3,6)` among them, and the residual
hypothesis of the assembly below is not vacuous. -/
theorem isNearPencilFamily_iff_eq_nearPencilSixFamily :
    ∀ lines ∈ lineFamiliesSix, (IsNearPencilFamily lines ↔ lines = nearPencilSixFamily) := by
  decide

/-- **The seven-point peel removes exactly the catalogue's `#22`.**  Twenty-two
entries survive it; the Fano `#13` is peeled separately by
`isFanoClass_fanoLineFamilyPattern`, leaving twenty-one. -/
theorem isNearPencilFamily_iff_eq_nearPencilSevenFamily :
    ∀ lines ∈ lineFamiliesSeven, (IsNearPencilFamily lines ↔ lines = nearPencilSevenFamily) := by
  decide

/-- **Catalogue class `#13` IS `Gtz.fanoLinePattern`**, on the nose.  Reading label
`i` as the nonzero bit vector `i + 1` of the three-dimensional space over two
elements, a triple is a line exactly when the three vectors sum to zero, and that
is the shipped pattern's definition. -/
theorem agreesOnDistinctTriples_fanoLineFamily :
    AgreesOnDistinctTriples (lineFamilyPattern fanoLineFamily) fanoLinePattern :=
  agreesOnDistinctTriples_of_forall (by decide)

/-- **The Fano peel fires on this list with the identity relabelling.** -/
theorem isFanoClass_fanoLineFamilyPattern : IsFanoClass (lineFamilyPattern fanoLineFamily) :=
  ⟨Equiv.refl _, agreesOnDistinctTriples_fanoLineFamily⟩

/-! ## The three discharged entries, as statements about these list entries

The ledger's two peels are theorems about recognizers; here they are cashed at the
three list entries they apply to, so what is discharged is visible as tie-freeness
of a named pattern rather than as a side condition. -/

/-- Catalogue `#8` at six labels is tie-free, via the rank-two transport. -/
theorem stratumIsTieFree_nearPencilSixFamilyPattern :
    StratumIsTieFree (lineFamilyPattern nearPencilSixFamily) :=
  stratumIsTieFree_of_isNearPencilClass (by omega)
    (isNearPencilClass_of_isNearPencilFamily isNearPencilFamily_nearPencilSixFamily)

/-- Catalogue `#22` at seven labels is tie-free, via the rank-two transport. -/
theorem stratumIsTieFree_nearPencilSevenFamilyPattern :
    StratumIsTieFree (lineFamilyPattern nearPencilSevenFamily) :=
  stratumIsTieFree_of_isNearPencilClass (by omega)
    (isNearPencilClass_of_isNearPencilFamily isNearPencilFamily_nearPencilSevenFamily)

/-- Catalogue `#13` at seven labels is tie-free, because no seven vectors of
three-space realize the Fano plane. -/
theorem stratumIsTieFree_fanoLineFamilyPattern :
    StratumIsTieFree (lineFamilyPattern fanoLineFamily) :=
  stratumIsTieFree_of_isFanoClass isFanoClass_fanoLineFamilyPattern

/-! ## The near pencil is rigid — the one class settled combinatorially

This is the first of the nine cases a full six-point classification needs, and it
is proved size-generically.  If every distinct triple avoiding one label is
dependent, then NO triple through that label can be: a single such triple would
put the pole on the line of the other two, and then the line law drags every
label onto that line, contradicting spanning.  So the near pencil is exactly one
class and it is closed. -/

/-- All six slot orders of a dependent triple are dependent, from the two swap
generators. -/
theorem pattern_allSlotOrders {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (firstLabel midLabel lastLabel : Fin size)
    (hpattern : pattern firstLabel midLabel lastLabel) :
    pattern firstLabel midLabel lastLabel ∧ pattern firstLabel lastLabel midLabel ∧
      pattern midLabel firstLabel lastLabel ∧ pattern midLabel lastLabel firstLabel ∧
      pattern lastLabel firstLabel midLabel ∧ pattern lastLabel midLabel firstLabel := by
  have hswapRight := haxioms.isRightSwapClosed _ _ _ hpattern
  have hswapLeft := haxioms.isLeftSwapClosed _ _ _ hpattern
  exact ⟨hpattern, hswapRight, hswapLeft,
    haxioms.isRightSwapClosed _ _ _ hswapLeft,
    haxioms.isLeftSwapClosed _ _ _ hswapRight,
    haxioms.isRightSwapClosed _ _ _ (haxioms.isLeftSwapClosed _ _ _ hswapRight)⟩

/-- **A line is a clique.**  Three labels each dependent with one distinct pivot
pair are dependent with each other.  This is the workhorse of a structural
classification: it turns "these labels lie on a common line" into a dependence
statement about the labels themselves, with no distinctness hypothesis on them. -/
theorem pattern_of_forall_pattern_pivot {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (pivotFirst pivotSecond : Fin size) (hpivotDistinct : pivotFirst ≠ pivotSecond)
    (memberFirst memberSecond memberThird : Fin size)
    (hmemberFirst : pattern pivotFirst pivotSecond memberFirst)
    (hmemberSecond : pattern pivotFirst pivotSecond memberSecond)
    (hmemberThird : pattern pivotFirst pivotSecond memberThird) :
    pattern memberFirst memberSecond memberThird := by
  by_cases hfirstIsPivot : memberFirst = pivotFirst
  · rw [hfirstIsPivot]
    exact haxioms.hasLineClosure pivotFirst pivotSecond memberSecond memberThird hpivotDistinct
      hmemberSecond hmemberThird
  · exact haxioms.hasLineClosure memberFirst pivotFirst memberSecond memberThird hfirstIsPivot
      (haxioms.isLeftSwapClosed _ _ _ (haxioms.hasLineClosure pivotFirst pivotSecond memberFirst
        memberSecond hpivotDistinct hmemberFirst hmemberSecond))
      (haxioms.isLeftSwapClosed _ _ _ (haxioms.hasLineClosure pivotFirst pivotSecond memberFirst
        memberThird hpivotDistinct hmemberFirst hmemberThird))

/-- **The pole absorbs.**  One dependent triple through the pole makes every
distinct pair of off-pole labels dependent with the pole. -/
theorem pattern_pole_of_pattern_pole_seed {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern) (poleLabel : Fin size)
    (hoffPole : ∀ leftLabel midLabel rightLabel : Fin size,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        leftLabel ≠ poleLabel → midLabel ≠ poleLabel → rightLabel ≠ poleLabel →
          pattern leftLabel midLabel rightLabel)
    (seedFirst seedSecond : Fin size) (hseedFirstNe : seedFirst ≠ poleLabel)
    (hseedSecondNe : seedSecond ≠ poleLabel) (hseedDistinct : seedFirst ≠ seedSecond)
    (hseed : pattern poleLabel seedFirst seedSecond)
    (targetFirst targetSecond : Fin size) (htargetFirstNe : targetFirst ≠ poleLabel)
    (htargetSecondNe : targetSecond ≠ poleLabel) (htargetDistinct : targetFirst ≠ targetSecond) :
    pattern poleLabel targetFirst targetSecond := by
  have hseedLine : pattern seedFirst seedSecond poleLabel :=
    pattern_rotate_of_isSpanningLinearSpacePattern haxioms _ _ _ hseed
  have hthroughSeedFirst : ∀ farLabel : Fin size, farLabel ≠ seedFirst → farLabel ≠ poleLabel →
      pattern poleLabel seedFirst farLabel := by
    intro farLabel hfarSeedFirst hfarPole
    by_cases hfarSeedSecond : farLabel = seedSecond
    · rw [hfarSeedSecond]; exact hseed
    · have hplanar := hoffPole seedFirst seedSecond farLabel hseedDistinct
        (Ne.symm hfarSeedFirst) (Ne.symm hfarSeedSecond) hseedFirstNe hseedSecondNe hfarPole
      exact haxioms.isLeftSwapClosed _ _ _
        (haxioms.hasLineClosure seedFirst seedSecond poleLabel farLabel hseedDistinct
          hseedLine hplanar)
  by_cases hfirstIsSeed : targetFirst = seedFirst
  · rw [hfirstIsSeed]
    exact hthroughSeedFirst targetSecond
      (fun hequal => htargetDistinct (hfirstIsSeed.trans hequal.symm)) htargetSecondNe
  · by_cases hsecondIsSeed : targetSecond = seedFirst
    · rw [hsecondIsSeed]
      exact haxioms.isRightSwapClosed _ _ _
        (hthroughSeedFirst targetFirst hfirstIsSeed htargetFirstNe)
    · exact haxioms.hasLineClosure poleLabel seedFirst targetFirst targetSecond
        (Ne.symm hseedFirstNe)
        (hthroughSeedFirst targetFirst hfirstIsSeed htargetFirstNe)
        (hthroughSeedFirst targetSecond hsecondIsSeed htargetSecondNe)

/-- **No triple through the pole is dependent.**  The absorption above would make
every distinct triple dependent, and spanning forbids that. -/
theorem not_pattern_pole_of_forall_pattern_off_pole {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern) (poleLabel : Fin size)
    (hoffPole : ∀ leftLabel midLabel rightLabel : Fin size,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        leftLabel ≠ poleLabel → midLabel ≠ poleLabel → rightLabel ≠ poleLabel →
          pattern leftLabel midLabel rightLabel)
    (seedFirst seedSecond : Fin size) (hseedFirstNe : seedFirst ≠ poleLabel)
    (hseedSecondNe : seedSecond ≠ poleLabel) (hseedDistinct : seedFirst ≠ seedSecond) :
    ¬ pattern poleLabel seedFirst seedSecond := by
  intro hseed
  obtain ⟨witnessLeft, witnessMid, witnessRight, hleftMid, hleftRight, hmidRight, hnotPattern⟩ :=
    haxioms.isSpanning
  refine hnotPattern ?_
  by_cases hleftPole : witnessLeft = poleLabel
  · rw [hleftPole]
    exact pattern_pole_of_pattern_pole_seed haxioms poleLabel hoffPole seedFirst seedSecond
      hseedFirstNe hseedSecondNe hseedDistinct hseed witnessMid witnessRight
      (fun hequal => hleftMid (hleftPole.trans hequal.symm))
      (fun hequal => hleftRight (hleftPole.trans hequal.symm)) hmidRight
  · by_cases hmidPole : witnessMid = poleLabel
    · rw [hmidPole]
      exact haxioms.isLeftSwapClosed _ _ _
        (pattern_pole_of_pattern_pole_seed haxioms poleLabel hoffPole seedFirst seedSecond
          hseedFirstNe hseedSecondNe hseedDistinct hseed witnessLeft witnessRight hleftPole
          (fun hequal => hmidRight (hmidPole.trans hequal.symm)) hleftRight)
    · by_cases hrightPole : witnessRight = poleLabel
      · rw [hrightPole]
        exact pattern_rotate_of_isSpanningLinearSpacePattern haxioms _ _ _
          (pattern_pole_of_pattern_pole_seed haxioms poleLabel hoffPole seedFirst seedSecond
            hseedFirstNe hseedSecondNe hseedDistinct hseed witnessLeft witnessMid hleftPole
            hmidPole hleftMid)
      · exact hoffPole witnessLeft witnessMid witnessRight hleftMid hleftRight hmidRight
          hleftPole hmidPole hrightPole

/-- **The near pencil is exactly one class.**  A spanning linear space all of whose
off-pole distinct triples are dependent agrees on distinct triples with
`Gtz.nearPencilLinePattern` at that pole — so the pattern is pinned, not merely
contained. -/
theorem agreesOnDistinctTriples_nearPencil_of_forall_pattern_off_pole {size : ℕ}
    {pattern : LinePattern size} (haxioms : IsSpanningLinearSpacePattern pattern)
    (poleLabel : Fin size)
    (hoffPole : ∀ leftLabel midLabel rightLabel : Fin size,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        leftLabel ≠ poleLabel → midLabel ≠ poleLabel → rightLabel ≠ poleLabel →
          pattern leftLabel midLabel rightLabel) :
    AgreesOnDistinctTriples pattern (nearPencilLinePattern poleLabel) := by
  refine agreesOnDistinctTriples_of_forall fun leftLabel midLabel rightLabel hleftMid
    hleftRight hmidRight => ⟨fun hpattern => ⟨?_, ?_, ?_⟩, fun hnear =>
      hoffPole leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hnear.1 hnear.2.1
        hnear.2.2⟩
  · intro hleftPole
    exact not_pattern_pole_of_forall_pattern_off_pole haxioms poleLabel hoffPole midLabel
      rightLabel (fun hequal => hleftMid (hleftPole.trans hequal.symm))
      (fun hequal => hleftRight (hleftPole.trans hequal.symm)) hmidRight (hleftPole ▸ hpattern)
  · intro hmidPole
    exact not_pattern_pole_of_forall_pattern_off_pole haxioms poleLabel hoffPole leftLabel
      rightLabel (fun hequal => hleftMid (hequal.trans hmidPole.symm))
      (fun hequal => hmidRight (hmidPole.trans hequal.symm)) hleftRight
      (haxioms.isLeftSwapClosed _ _ _ (hmidPole ▸ hpattern))
  · intro hrightPole
    exact not_pattern_pole_of_forall_pattern_off_pole haxioms poleLabel hoffPole leftLabel
      midLabel (fun hequal => hleftRight (hequal.trans hrightPole.symm))
      (fun hequal => hmidRight (hequal.trans hrightPole.symm)) hleftMid
      (haxioms.isLeftSwapClosed _ _ _ (haxioms.isRightSwapClosed _ _ _
        (hrightPole ▸ hpattern)))

/-! ## The route, closed at four labels

Four labels carry exactly two classes: `U(3,4)` and one three-point line, and the
second is the near pencil at that size.  Everything above therefore closes at
`size = 4` outright, which is what makes
`patternListIsCompleteUpToRelabel_four` — the first complete enumeration in the
repository — unconditional.  The hinge's conclusion is FALSE here
(`Gtz.tetraDesign_isTie` is a primitive `(4,3)` tie), so this is a demonstration
that the reduction fires and not a step toward the hinge.

The relabelling is a single transposition, which is why no permutation has to be
manufactured from incidence data.  At six and seven labels that convenience is
gone, and it is exactly where the remaining work sits. -/

/-- Transposing hits the target only at the source. -/
theorem swap_apply_eq_target_iff {size : ℕ} (sourceLabel targetLabel label : Fin size) :
    Equiv.swap sourceLabel targetLabel label = targetLabel ↔ label = sourceLabel := by
  constructor
  · intro hswap
    have hback := congrArg (Equiv.swap sourceLabel targetLabel) hswap
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at hback
    exact hback
  · intro hlabel
    rw [hlabel, Equiv.swap_apply_left]

/-- Relabelling a near pencil by the transposition that moves its pole to a chosen
label is the chosen label's near pencil. -/
theorem nearPencilLinePattern_comp_swap_iff {size : ℕ}
    (poleLabel targetPole leftLabel midLabel rightLabel : Fin size) :
    nearPencilLinePattern targetPole (Equiv.swap poleLabel targetPole leftLabel)
        (Equiv.swap poleLabel targetPole midLabel) (Equiv.swap poleLabel targetPole rightLabel)
      ↔ nearPencilLinePattern poleLabel leftLabel midLabel rightLabel := by
  simp only [nearPencilLinePattern, ne_eq, swap_apply_eq_target_iff]

/-- The two isomorphism classes of spanning linear spaces on four labels:
`U(3,4)` and one three-point line. -/
def lineFamiliesFour : List (List (List (Fin 4))) := [[], [[0, 1, 2]]]

/-- The two four-label patterns. -/
def linePatternListFour : List (LinePattern 4) := lineFamiliesFour.map lineFamilyPattern

theorem length_lineFamiliesFour : lineFamiliesFour.length = 2 := by decide

theorem forall_isGoodLineFamily_four : ∀ lines ∈ lineFamiliesFour, IsGoodLineFamily lines := by
  decide

/-- At four labels the single-line class IS the near pencil with pole `3`. -/
theorem lineFamilyPattern_singleLineFour_iff (leftLabel midLabel rightLabel : Fin 4) :
    lineFamilyPattern [[0, 1, 2]] leftLabel midLabel rightLabel ↔
      nearPencilLinePattern (3 : Fin 4) leftLabel midLabel rightLabel := by
  revert leftLabel midLabel rightLabel
  decide

/-- The single-line entry, transported to an arbitrary pole by one transposition. -/
theorem agreesOnDistinctTriples_singleLineFour_comp_swap (poleLabel : Fin 4) :
    AgreesOnDistinctTriples (nearPencilLinePattern poleLabel)
      (fun leftLabel midLabel rightLabel => lineFamilyPattern [[0, 1, 2]]
        (Equiv.swap poleLabel 3 leftLabel) (Equiv.swap poleLabel 3 midLabel)
        (Equiv.swap poleLabel 3 rightLabel)) :=
  agreesOnDistinctTriples_of_forall fun leftLabel midLabel rightLabel _ _ _ =>
    ((lineFamilyPattern_singleLineFour_iff _ _ _).trans
      (nearPencilLinePattern_comp_swap_iff poleLabel 3 leftLabel midLabel rightLabel)).symm

/-- **At four labels one dependent triple pins the pole.**  The complement of a
three-element subset of `Fin 4` is a singleton, and every label off it is one of
the triple's three, so all six slot orders of the known dependent triple cover
every off-pole triple. -/
theorem exists_forall_pattern_off_pole_four {pattern : LinePattern 4}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (seedLeft seedMid seedRight : Fin 4) (hleftMid : seedLeft ≠ seedMid)
    (hleftRight : seedLeft ≠ seedRight) (hmidRight : seedMid ≠ seedRight)
    (hseed : pattern seedLeft seedMid seedRight) :
    ∃ poleLabel : Fin 4, ∀ leftLabel midLabel rightLabel : Fin 4,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        leftLabel ≠ poleLabel → midLabel ≠ poleLabel → rightLabel ≠ poleLabel →
          pattern leftLabel midLabel rightLabel := by
  classical
  have hseedCard : ({seedLeft, seedMid, seedRight} : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hleftMid, hleftRight]),
      Finset.card_insert_of_notMem (by simp [hmidRight]), Finset.card_singleton]
  have hcomplementCard : (({seedLeft, seedMid, seedRight} : Finset (Fin 4))ᶜ).card = 1 := by
    rw [Finset.card_compl, hseedCard, Fintype.card_fin]
  obtain ⟨poleLabel, hcomplement⟩ := Finset.card_eq_one.mp hcomplementCard
  have hcover : ∀ label : Fin 4, label ≠ poleLabel →
      label = seedLeft ∨ label = seedMid ∨ label = seedRight := by
    intro label hlabel
    have hnotComplement : label ∉ (({seedLeft, seedMid, seedRight} : Finset (Fin 4))ᶜ) := by
      rw [hcomplement]
      simpa using hlabel
    have hmemSeed : label ∈ ({seedLeft, seedMid, seedRight} : Finset (Fin 4)) := by
      by_contra hnotMem
      exact hnotComplement (Finset.mem_compl.mpr hnotMem)
    simpa using hmemSeed
  obtain ⟨orderOne, orderTwo, orderThree, orderFour, orderFive, orderSix⟩ :=
    pattern_allSlotOrders haxioms seedLeft seedMid seedRight hseed
  refine ⟨poleLabel, fun leftLabel midLabel rightLabel hlm hlr hmr hlp hmp hrp => ?_⟩
  rcases hcover leftLabel hlp with rfl | rfl | rfl <;>
    rcases hcover midLabel hmp with rfl | rfl | rfl <;>
    rcases hcover rightLabel hrp with rfl | rfl | rfl <;> simp_all

/-- **The enumeration at four labels, complete and kernel-checked.** -/
theorem linearSpaceListIsComplete_four : LinearSpaceListIsComplete 4 linePatternListFour := by
  classical
  intro pattern haxioms
  by_cases hlineFree : ∀ leftLabel midLabel rightLabel : Fin 4,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        ¬ pattern leftLabel midLabel rightLabel
  · refine ⟨lineFamilyPattern [], List.mem_map.mpr ⟨[], by decide, rfl⟩, Equiv.refl _,
      agreesOnDistinctTriples_of_forall fun leftLabel midLabel rightLabel hlm hlr hmr => ?_⟩
    refine ⟨fun hpattern => absurd hpattern (hlineFree leftLabel midLabel rightLabel hlm hlr hmr),
      ?_⟩
    rintro ⟨line, hline, -⟩
    exact absurd hline (by simp)
  · push Not at hlineFree
    obtain ⟨seedLeft, seedMid, seedRight, hleftMid, hleftRight, hmidRight, hseed⟩ := hlineFree
    obtain ⟨poleLabel, hoffPole⟩ := exists_forall_pattern_off_pole_four haxioms seedLeft seedMid
      seedRight hleftMid hleftRight hmidRight hseed
    exact ⟨lineFamilyPattern [[0, 1, 2]], List.mem_map.mpr ⟨[[0, 1, 2]], by decide, rfl⟩,
      Equiv.swap poleLabel 3, agreesOnDistinctTriples_trans
        (agreesOnDistinctTriples_nearPencil_of_forall_pattern_off_pole haxioms poleLabel hoffPole)
        (agreesOnDistinctTriples_singleLineFour_comp_swap poleLabel)⟩

/-- **The first complete enumeration in the repository.**  Every primitive `(4,3)`
design realizes, after relabelling, either the line-free pattern `U(3,4)` or the
single-line pattern.  Unconditional. -/
theorem patternListIsCompleteUpToRelabel_four :
    PatternListIsCompleteUpToRelabel 4 linePatternListFour :=
  patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete (by omega) _
    linearSpaceListIsComplete_four

/-- **The tetrahedron design is primitive.**  No two of the four directions
`(1,1,1)`, `(1,-1,-1)`, `(-1,1,-1)`, `(-1,-1,1)` are proportional, checked
coordinate by coordinate over the sixteen label pairs.  Stated because the section
above needs it twice and neither use was available: the enumeration at four labels
quantifies over primitive designs, so without an inhabitant it would be vacuous,
and the header's claim that the hinge fails at four labels needs the primitivity
half as well as `Gtz.tetraDesign_isTie`. -/
theorem isPrimitiveDesign_tetraDesign : IsPrimitiveDesign tetraDesign := by
  intro keptLabel dropLabel ratio _ hparallel
  have hcomponents : ∀ coordinate : Fin 3,
      tetraAtom dropLabel coordinate = ratio * tetraAtom keptLabel coordinate := by
    intro coordinate
    simpa [tetraDesign_atom, Pi.smul_apply, smul_eq_mul] using congrFun hparallel coordinate
  have hzero := hcomponents 0
  have hone := hcomponents 1
  have htwo := hcomponents 2
  fin_cases keptLabel <;> fin_cases dropLabel <;> simp_all [tetraAtom] <;> linarith

/-- **The hinge is FALSE at four labels**, the exact companion of
`Gtz.not_hingeHoldsAtSize_five_three`: the tetrahedron is a tie with no parallel
pair.  So the enumeration above settles the pattern classification at a size where
the hinge itself fails, which is why it is a demonstration that the reduction
fires and not a step toward `(6,3)` or `(7,3)`. -/
theorem not_hingeHoldsAtSize_four_three : ¬ HingeHoldsAtSize 4 3 := fun hhinge =>
  (isPrimitiveDesign_iff_not_hasParallelPair tetraDesign).mp isPrimitiveDesign_tetraDesign
    (hhinge tetraDesign tetraDesign_isTie)

/-- **The four-label enumeration is not vacuous.**  Cashed at the tetrahedron, the
only primitive design of that size the repository carries: it lands on a listed
pattern, so `patternListIsCompleteUpToRelabel_four` quantifies over a nonempty
domain. -/
theorem exists_hasLinePattern_relabel_tetraDesign :
    ∃ pattern ∈ linePatternListFour, ∃ relabel : Equiv.Perm (Fin 4),
      HasLinePattern tetraDesign (fun leftLabel midLabel rightLabel =>
        pattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) :=
  patternListIsCompleteUpToRelabel_four tetraDesign isPrimitiveDesign_tetraDesign

/-! ## The two near-pencil entries carry designs

`Gtz.Design.NearPencilTransport` ships exact rational near pencils at six and
seven labels.  They realize the catalogue entries `#8` and `#22` of the lists
above, so neither list is made of patterns nothing can satisfy. -/

/-- The six-point near-pencil entry is inhabited by `Gtz.nearPencilSixDesign`. -/
theorem hasLinePattern_nearPencilSixFamilyPattern :
    HasLinePattern nearPencilSixDesign (lineFamilyPattern nearPencilSixFamily) :=
  hasLinePattern_of_agreesOnDistinctTriples nearPencilSixDesign_hasLinePattern
    (agreesOnDistinctTriples_symm (agreesOnDistinctTriples_of_forall (by decide)))

/-- The seven-point near-pencil entry is inhabited by `Gtz.nearPencilSevenDesign`. -/
theorem hasLinePattern_nearPencilSevenFamilyPattern :
    HasLinePattern nearPencilSevenDesign (lineFamilyPattern nearPencilSevenFamily) :=
  hasLinePattern_of_agreesOnDistinctTriples nearPencilSevenDesign_hasLinePattern
    (agreesOnDistinctTriples_symm (agreesOnDistinctTriples_of_forall (by decide)))

/-! ## Controls: the transcription check has teeth and the peel is not total

Three failure modes would make the statements above worthless.  The family check
could accept anything, so that the two lists were never really validated; the
near-pencil peel could swallow the whole list, so that the residual hypothesis
were vacuous; and the lists could consist of patterns nothing satisfies.  All
three are refuted here. -/

/-- **The family check rejects two lines meeting in two labels** — the exact shape
a dropped label in a transcribed line would produce. -/
theorem not_isGoodLineFamily_overlappingLines :
    ¬ IsGoodLineFamily (size := 6) [[0, 1, 2], [0, 1, 3]] := by decide

/-- **The family check rejects a family covering every triple** — the shape a line
transcribed one label too long would produce. -/
theorem not_isGoodLineFamily_fullLine :
    ¬ IsGoodLineFamily (size := 6) [[0, 1, 2, 3, 4, 5]] := by decide

/-- **`M(K4)` survives the near-pencil peel.**  Catalogue `#5` at six labels, the
campaign's `q6m8` and the sharpest of the open classes, is not a near pencil, so
the residual hypothesis of the six-label assembly genuinely still owes it. -/
theorem not_isNearPencilFamily_graphicKFourFamily :
    ¬ IsNearPencilFamily graphicKFourFamily := by decide

theorem not_isNearPencilClass_graphicKFourFamilyPattern :
    ¬ IsNearPencilClass (lineFamilyPattern graphicKFourFamily) :=
  not_isNearPencilClass_of_not_isNearPencilFamily not_isNearPencilFamily_graphicKFourFamily

/-- **The line-free class survives the peel too**, at both hinge sizes — so
`U(3,6)` and `U(3,7)` remain in the residual, matching the ledger's own control
`Gtz.not_isNearPencilClass_lineFree`. -/
theorem not_isNearPencilFamily_uniformSix : ¬ IsNearPencilFamily (size := 6) [] := by decide

theorem not_isNearPencilFamily_uniformSeven : ¬ IsNearPencilFamily (size := 7) [] := by decide

/-! ## The assemblies, at these lists

What each theorem takes is exactly the residual: the combinatorial completeness of
the list, plus per surviving family a tie-freeness statement.  Everything that was
analysis is discharged. -/

/-- **The hinge at six points, from this list.**  The hypotheses are (i) the
combinatorial completeness of `linePatternListSix`, which is decidable and true by
the classical catalogue, and (ii) for each of the EIGHT families that is not the
near pencil, tie-freeness among designs of leverage at least one — the narrowing
the ledger's leverage floor already pays for.  Nothing else. -/
theorem hingeHoldsAtSize_of_linearSpaceEnumeration_sixThree
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hresidual : ∀ lines ∈ lineFamiliesSix, ¬ IsNearPencilFamily lines →
      StratumIsTieFreeAmongHeavy (lineFamilyPattern lines)) :
    HingeHoldsAtSize 6 3 := by
  refine hingeHoldsAtSize_of_heavyResidualLedger_sixThree linePatternListSix
    (patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete (by omega) _ hcomplete) ?_
  intro pattern hmem hnotNearPencil
  obtain ⟨lines, hlines, hshape⟩ := List.mem_map.mp hmem
  subst hshape
  exact hresidual lines hlines fun hfamily =>
    hnotNearPencil (isNearPencilClass_of_isNearPencilFamily hfamily)

/-- **The hinge at seven points, from this list.**  Both discharged classes are
peeled: the near pencil `#22` and the Fano `#13`.  So the residual is asked of
twenty-one families, and the only non-combinatorial input is the open
`Gtz.GtzWeighted 6 3` that buys the leverage floor one size up. -/
theorem hingeHoldsAtSize_of_linearSpaceEnumeration_sevenThree (hsixThree : GtzWeighted 6 3)
    (hcomplete : LinearSpaceListIsComplete 7 linePatternListSeven)
    (hresidual : ∀ lines ∈ lineFamiliesSeven, ¬ IsNearPencilFamily lines →
      ¬ IsFanoClass (lineFamilyPattern lines) →
        StratumIsTieFreeAmongHeavy (lineFamilyPattern lines)) :
    HingeHoldsAtSize 7 3 := by
  refine hingeHoldsAtSize_of_heavyResidualLedger_sevenThree hsixThree linePatternListSeven
    (patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete (by omega) _ hcomplete) ?_
  intro pattern hmem hnotNearPencil hnotFano
  obtain ⟨lines, hlines, hshape⟩ := List.mem_map.mp hmem
  subst hshape
  exact hresidual lines hlines
    (fun hfamily => hnotNearPencil (isNearPencilClass_of_isNearPencilFamily hfamily)) hnotFano

end Gtz

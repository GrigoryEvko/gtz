/-
# The sphere dichotomy: joining the bracket lane to the transversal-axis lane

## Read this before adding anything here

Most of what a first reading calls "the shadow theorem" is ALREADY SHIPPED, in
`Gtz/Design/TightAxisPairBudget.lean`, in the CROSS-PRODUCT vocabulary:

  * `Gtz.planarCompressionDesign` -- the rank-two compression along an
    orthonormal pair.  It is the SAME object as `Gtz.inPlaneRestriction`
    (`Gtz/Design/InPlaneRestriction.lean`); the two files landed the identical
    definition under two names, and `inPlaneRestriction_eq_planarCompressionDesign`
    below proves they are literally equal, by `rfl`.
  * `Gtz.planarCompression_pairBracket` -- the compression's `pairBracket` is
    `(e1 x e2) . (a x b)`, hypothesis-free Binet-Cauchy.
  * `Gtz.crossProduct_orthonormalFrame_eq_smul_axis` -- `e1 x e2` is the axis
    times a sign of square one.
  * `Gtz.exists_planeStrictPair_of_fourTransversal` and its frame-free form
    `Gtz.exists_planeStrictPair_of_transversalAxis` -- four atoms pairwise
    transversal to a unit axis force a pair of the ORIGINAL design that strictly
    over-covers the whole axis plane.

So the mechanism is landed.  What is NOT landed is the DICTIONARY.  The stratum
lane speaks in `Gtz.tripleBracket` (and `Gtz.atomBracket`, `Gtz.HasLinePattern`,
`Gtz.tripleBracket_eq_zero_of_spannedByPair`): a line pattern is a list of
vanishing triple brackets, and the fifteen exceptional planes of a six-atom
rank-three design are cut out by triple brackets.  The axis lane speaks in
`crossProduct _ _ . axis`.  Nothing in the tree connects the two, so a consumer
holding line-pattern axioms cannot reach the shipped plane-strict pair at all.

This file supplies that connection and re-exports the shipped mechanism in the
bracket vocabulary.

  * `tripleBracket_eq_crossProduct_dotProduct` -- the dictionary itself, a bare
    `ring` identity in nine variables.
  * `inPlaneRestriction_eq_planarCompressionDesign` -- the two compressions are
    one object, so every `planarCompressionDesign` result is an
    `inPlaneRestriction` result and conversely.
  * `pairBracket_inPlaneRestriction_eq_frameOrientation_mul_tripleBracket` -- the
    bridge as briefed: the rank-two bracket of two shadows IS the rank-three
    triple bracket of the two atoms against the normal, up to the frame's sign.
  * `pairBracket_inPlaneRestriction_eq_zero_iff_tripleBracket_eq_zero` -- the
    dichotomy proper.  Two shadows are parallel EXACTLY on the plane the two
    atoms span; off it they are not.  Both directions.
  * `exists_strictlyDominatingPair_inPlaneRestriction_of_sixTripleBrackets` and
    `exists_inPlane_strictlyDominatingPair_of_sixTripleBrackets` -- the template,
    in the bracket vocabulary, in restriction form and in geometric form.

No measure theory, no quantifier over the sphere, deliberately.  A consumer
chooses its own normal (a line normal, a cross-axis, a circle point) and
discharges the six bracket conditions from its own pattern axioms; the six
conditions are therefore left explicit.  No heaviness is used anywhere -- shadows
are shorter than their atoms and need not stay heavy, and nothing in the chain
asks them to.

**NON-VACUITY.**  `Gtz.tetraDesign` is a tie (`Gtz.tetraDesign_isTie`): no three
of its atoms dominate strictly.  Its shadow along the rational unit normal
`(2, 3, 6)/7` -- which misses all six of its planes, the six brackets coming out
`-6/7, 8/7, -2/7, 10/7, -16/7, 18/7` -- is NOT a tie.  So the template's
hypotheses are reachable and the rank drop genuinely buys strictness.
-/
import Mathlib
import Gtz.Design.InPlaneRestriction
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.TightAxisPairBudget
import Gtz.Ties.RankTwoHingeBridge
import Gtz.Ties.TetrahedronCertifiedTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## Part 0: the two lanes are the same lane -/

/-- **THE DICTIONARY.**  The scalar triple product of the stratum lane is the
cross product of the axis lane, tested against the third vector.  A bare
polynomial identity in nine variables -- no hypotheses, no frame.

This is the sentence the tree was missing.  Every transversality hypothesis of
`Gtz.exists_planeStrictPair_of_transversalAxis` is, verbatim, a nonvanishing
triple bracket, and every line pattern is a list of vanishing ones. -/
theorem tripleBracket_eq_crossProduct_dotProduct
    (leftVec rightVec probeVec : Fin 3 → ℝ) :
    tripleBracket leftVec rightVec probeVec
      = crossProduct leftVec rightVec ⬝ᵥ probeVec := by
  simp only [tripleBracket_eq, cross_apply, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- **The two shipped compressions are one object.**  `Gtz.inPlaneRestriction` and
`Gtz.planarCompressionDesign` were landed independently, in different files, with
the same atoms, the same weights and the same hypotheses; they are equal by
`rfl`.  Every result about either is a result about the other. -/
theorem inPlaneRestriction_eq_planarCompressionDesign (design : WeightedDesign size 3)
    (basisFirst basisSecond : Fin 3 → ℝ)
    (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1)
    (horth : basisFirst ⬝ᵥ basisSecond = 0) :
    inPlaneRestriction design basisFirst basisSecond hfirstUnit hsecondUnit horth
      = planarCompressionDesign design basisFirst basisSecond
          hfirstUnit hsecondUnit horth := rfl

/-! ## Part 1: (a) the bridge

The frame's orientation is the sign relating the two brackets; it is a genuine
sign, and the bridge is an equality up to it. -/

/-- **The orientation of an in-plane frame together with its normal**: the triple
bracket of the two basis vectors against the normal direction.  On an orthonormal
frame it is `+1` or `-1`, and swapping the two basis vectors flips it. -/
def frameOrientation (basisFirst basisSecond normalDirection : Fin 3 → ℝ) : ℝ :=
  tripleBracket basisFirst basisSecond normalDirection

/-- The orientation of an orthonormal frame squares to one.  Spends
`Gtz.crossProduct_orthonormalFrame_eq_smul_axis` through the dictionary. -/
theorem frameOrientation_sq_eq_one
    (basisFirst basisSecond normalDirection : Fin 3 → ℝ)
    (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1)
    (horth : basisFirst ⬝ᵥ basisSecond = 0)
    (hnormalUnit : normalDirection ⬝ᵥ normalDirection = 1)
    (hfirstNormal : basisFirst ⬝ᵥ normalDirection = 0)
    (hsecondNormal : basisSecond ⬝ᵥ normalDirection = 0) :
    frameOrientation basisFirst basisSecond normalDirection ^ 2 = 1 := by
  simp only [frameOrientation, tripleBracket_eq_crossProduct_dotProduct]
  exact (crossProduct_orthonormalFrame_eq_smul_axis hfirstUnit hsecondUnit hnormalUnit
    horth hfirstNormal hsecondNormal).2

/-- The orientation of an orthonormal frame is nonzero -- the only consequence of
`frameOrientation_sq_eq_one` the transfer lemma consumes. -/
theorem frameOrientation_ne_zero
    (basisFirst basisSecond normalDirection : Fin 3 → ℝ)
    (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1)
    (horth : basisFirst ⬝ᵥ basisSecond = 0)
    (hnormalUnit : normalDirection ⬝ᵥ normalDirection = 1)
    (hfirstNormal : basisFirst ⬝ᵥ normalDirection = 0)
    (hsecondNormal : basisSecond ⬝ᵥ normalDirection = 0) :
    frameOrientation basisFirst basisSecond normalDirection ≠ 0 := by
  intro hzero
  have hsquare := frameOrientation_sq_eq_one basisFirst basisSecond normalDirection
    hfirstUnit hsecondUnit horth hnormalUnit hfirstNormal hsecondNormal
  rw [hzero] at hsquare
  norm_num at hsquare

/-- The orientation is literally `+1` or `-1`, which is what "up to sign" means. -/
theorem frameOrientation_eq_one_or_eq_neg_one
    (basisFirst basisSecond normalDirection : Fin 3 → ℝ)
    (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1)
    (horth : basisFirst ⬝ᵥ basisSecond = 0)
    (hnormalUnit : normalDirection ⬝ᵥ normalDirection = 1)
    (hfirstNormal : basisFirst ⬝ᵥ normalDirection = 0)
    (hsecondNormal : basisSecond ⬝ᵥ normalDirection = 0) :
    frameOrientation basisFirst basisSecond normalDirection = 1
      ∨ frameOrientation basisFirst basisSecond normalDirection = -1 := by
  have hsquare := frameOrientation_sq_eq_one basisFirst basisSecond normalDirection
    hfirstUnit hsecondUnit horth hnormalUnit hfirstNormal hsecondNormal
  have hfactored : (frameOrientation basisFirst basisSecond normalDirection - 1)
      * (frameOrientation basisFirst basisSecond normalDirection + 1) = 0 := by
    linear_combination hsquare
  rcases mul_eq_zero.mp hfactored with hminus | hplus
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **THE BRIDGE.**  The rank-two `Gtz.pairBracket` of two shadows is the
rank-three `Gtz.tripleBracket` of the two atoms against the normal, times the
frame's sign.  This is the dictionary entry a rank-three consumer spends.

Proof: the two compressions are one object, the shipped Binet-Cauchy identity
`Gtz.planarCompression_pairBracket` reads the shadow bracket as
`(e1 x e2) . (a x b)`, the shipped
`Gtz.crossProduct_orthonormalFrame_eq_smul_axis` replaces `e1 x e2` by the signed
normal, and `tripleBracket_eq_crossProduct_dotProduct` translates both sides. -/
theorem pairBracket_inPlaneRestriction_eq_frameOrientation_mul_tripleBracket
    (design : WeightedDesign size 3)
    (basisFirst basisSecond normalDirection : Fin 3 → ℝ)
    (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1)
    (horth : basisFirst ⬝ᵥ basisSecond = 0)
    (hnormalUnit : normalDirection ⬝ᵥ normalDirection = 1)
    (hfirstNormal : basisFirst ⬝ᵥ normalDirection = 0)
    (hsecondNormal : basisSecond ⬝ᵥ normalDirection = 0)
    (leftLabel rightLabel : Fin size) :
    pairBracket (inPlaneRestriction design basisFirst basisSecond
        hfirstUnit hsecondUnit horth) leftLabel rightLabel
      = frameOrientation basisFirst basisSecond normalDirection
        * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
            normalDirection := by
  obtain ⟨hsignedNormal, -⟩ := crossProduct_orthonormalFrame_eq_smul_axis hfirstUnit
    hsecondUnit hnormalUnit horth hfirstNormal hsecondNormal
  have hexpand : crossProduct basisFirst basisSecond
        ⬝ᵥ crossProduct (design.atom leftLabel) (design.atom rightLabel)
      = (crossProduct basisFirst basisSecond ⬝ᵥ normalDirection)
        * (crossProduct (design.atom leftLabel) (design.atom rightLabel)
            ⬝ᵥ normalDirection) := by
    conv_lhs => rw [hsignedNormal]
    rw [smul_dotProduct, smul_eq_mul, dotProduct_comm normalDirection
      (crossProduct (design.atom leftLabel) (design.atom rightLabel))]
  rw [inPlaneRestriction_eq_planarCompressionDesign, planarCompression_pairBracket, hexpand]
  simp only [frameOrientation, tripleBracket_eq_crossProduct_dotProduct]

/-! ## Part 2: (b) the dichotomy

On the plane the two atoms span, their shadows are parallel; off it, they are
not.  Both directions, because the frame's sign is invertible. -/

/-- **THE DICHOTOMY.**  Two shadows are parallel EXACTLY when the normal lies in
the plane the two atoms span.  The exceptional set is therefore precisely the
union of the `binom(m, 2)` planes `span(a_c, a_d)` -- fifteen of them at six
atoms -- and nothing else. -/
theorem pairBracket_inPlaneRestriction_eq_zero_iff_tripleBracket_eq_zero
    (design : WeightedDesign size 3)
    (basisFirst basisSecond normalDirection : Fin 3 → ℝ)
    (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1)
    (horth : basisFirst ⬝ᵥ basisSecond = 0)
    (hnormalUnit : normalDirection ⬝ᵥ normalDirection = 1)
    (hfirstNormal : basisFirst ⬝ᵥ normalDirection = 0)
    (hsecondNormal : basisSecond ⬝ᵥ normalDirection = 0)
    (leftLabel rightLabel : Fin size) :
    pairBracket (inPlaneRestriction design basisFirst basisSecond
          hfirstUnit hsecondUnit horth) leftLabel rightLabel = 0
      ↔ tripleBracket (design.atom leftLabel) (design.atom rightLabel)
          normalDirection = 0 := by
  rw [pairBracket_inPlaneRestriction_eq_frameOrientation_mul_tripleBracket design
    basisFirst basisSecond normalDirection hfirstUnit hsecondUnit horth
    hnormalUnit hfirstNormal hsecondNormal]
  constructor
  · intro hproductZero
    rcases mul_eq_zero.mp hproductZero with horientationZero | hbracketZero
    · exact absurd horientationZero (frameOrientation_ne_zero basisFirst basisSecond
        normalDirection hfirstUnit hsecondUnit horth hnormalUnit hfirstNormal hsecondNormal)
    · exact hbracketZero
  · intro hbracketZero
    rw [hbracketZero, mul_zero]

/-- **The transfer in the band lane's own currency.**  Composing the dichotomy
with the shipped one-directional dictionary
`Gtz.unitPairGram_ne_one_of_pairBracket_ne_zero` puts a rank-three bracket
hypothesis into exactly the shape `Gtz.not_isTie_of_fourNonParallel` consumes. -/
theorem unitPairGram_inPlaneRestriction_ne_one_of_tripleBracket_ne_zero
    (design : WeightedDesign size 3)
    (basisFirst basisSecond normalDirection : Fin 3 → ℝ)
    (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1)
    (horth : basisFirst ⬝ᵥ basisSecond = 0)
    (hnormalUnit : normalDirection ⬝ᵥ normalDirection = 1)
    (hfirstNormal : basisFirst ⬝ᵥ normalDirection = 0)
    (hsecondNormal : basisSecond ⬝ᵥ normalDirection = 0)
    (leftLabel rightLabel : Fin size)
    (hbracket : tripleBracket (design.atom leftLabel) (design.atom rightLabel)
      normalDirection ≠ 0) :
    unitPairGram (inPlaneRestriction design basisFirst basisSecond
        hfirstUnit hsecondUnit horth) leftLabel rightLabel ≠ 1 :=
  unitPairGram_ne_one_of_pairBracket_ne_zero _ leftLabel rightLabel
    (fun hzero => hbracket
      ((pairBracket_inPlaneRestriction_eq_zero_iff_tripleBracket_eq_zero design
        basisFirst basisSecond normalDirection hfirstUnit hsecondUnit horth
        hnormalUnit hfirstNormal hsecondNormal leftLabel rightLabel).mp hzero))

/-! ## Part 3: (c) the template

Four labels, six bracket conditions, a strictly dominating in-plane pair.  Two
forms: the restriction form, which speaks about the rank-two shadow design and
is what `Gtz.IsTie` arguments consume, and the geometric form, which never
mentions the restriction and is what a rank-three consumer wants. -/

/-- **THE TEMPLATE, in restriction form.**  Four distinct labels whose six triple
brackets against a unit normal are nonzero force a STRICTLY dominating pair in
the in-plane restriction at that normal.

Every hypothesis is checkable by one polynomial evaluation.  No heaviness of the
atoms is required, and none is available.  The chain is the dichotomy, then the
hypothesis-free band theorem `Gtz.not_isTie_of_fourNonParallel`, then the
disjunction closure `Gtz.exists_strictlyDominatingPair_of_not_isTie` -- which is
where the PROVED rank-two case of weighted GTZ does its work. -/
theorem exists_strictlyDominatingPair_inPlaneRestriction_of_sixTripleBrackets
    (design : WeightedDesign size 3)
    (basisFirst basisSecond normalDirection : Fin 3 → ℝ)
    (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1)
    (horth : basisFirst ⬝ᵥ basisSecond = 0)
    (hnormalUnit : normalDirection ⬝ᵥ normalDirection = 1)
    (hfirstNormal : basisFirst ⬝ᵥ normalDirection = 0)
    (hsecondNormal : basisSecond ⬝ᵥ normalDirection = 0)
    (firstLabel secondLabel thirdLabel fourthLabel : Fin size)
    (hdistinctFirstSecond : firstLabel ≠ secondLabel)
    (hdistinctFirstThird : firstLabel ≠ thirdLabel)
    (hdistinctFirstFourth : firstLabel ≠ fourthLabel)
    (hdistinctSecondThird : secondLabel ≠ thirdLabel)
    (hdistinctSecondFourth : secondLabel ≠ fourthLabel)
    (hdistinctThirdFourth : thirdLabel ≠ fourthLabel)
    (hbracketFirstSecond : tripleBracket (design.atom firstLabel)
      (design.atom secondLabel) normalDirection ≠ 0)
    (hbracketFirstThird : tripleBracket (design.atom firstLabel)
      (design.atom thirdLabel) normalDirection ≠ 0)
    (hbracketFirstFourth : tripleBracket (design.atom firstLabel)
      (design.atom fourthLabel) normalDirection ≠ 0)
    (hbracketSecondThird : tripleBracket (design.atom secondLabel)
      (design.atom thirdLabel) normalDirection ≠ 0)
    (hbracketSecondFourth : tripleBracket (design.atom secondLabel)
      (design.atom fourthLabel) normalDirection ≠ 0)
    (hbracketThirdFourth : tripleBracket (design.atom thirdLabel)
      (design.atom fourthLabel) normalDirection ≠ 0) :
    ∃ dominatingPair : Finset (Fin size), dominatingPair.card = 2
      ∧ (subsetSum (inPlaneRestriction design basisFirst basisSecond
          hfirstUnit hsecondUnit horth) dominatingPair - 1).PosDef := by
  refine exists_strictlyDominatingPair_of_not_isTie _
    (not_isTie_of_fourNonParallel _ firstLabel secondLabel thirdLabel fourthLabel
      hdistinctFirstSecond hdistinctFirstThird hdistinctFirstFourth
      hdistinctSecondThird hdistinctSecondFourth hdistinctThirdFourth ?_ ?_ ?_ ?_ ?_ ?_) <;>
    exact unitPairGram_inPlaneRestriction_ne_one_of_tripleBracket_ne_zero design
      basisFirst basisSecond normalDirection hfirstUnit hsecondUnit horth
      hnormalUnit hfirstNormal hsecondNormal _ _ (by assumption)

/-- **THE TEMPLATE, in geometric form.**  The same six bracket conditions produce
two atoms of the ORIGINAL rank-three design whose readings STRICTLY over-cover
EVERY nonzero probe of the normal's plane.

No frame appears: only the unit normal the consumer chose.  This is the shipped
`Gtz.exists_planeStrictPair_of_transversalAxis` re-expressed through the
dictionary, and it is the strict sharpening of the shipped weak statement
`Gtz.exists_inPlane_dominating_pair`. -/
theorem exists_inPlane_strictlyDominatingPair_of_sixTripleBrackets
    (design : WeightedDesign size 3)
    {normalDirection : Fin 3 → ℝ}
    (hnormalUnit : normalDirection ⬝ᵥ normalDirection = 1)
    {firstLabel secondLabel thirdLabel fourthLabel : Fin size}
    (hdistinctFirstSecond : firstLabel ≠ secondLabel)
    (hdistinctFirstThird : firstLabel ≠ thirdLabel)
    (hdistinctFirstFourth : firstLabel ≠ fourthLabel)
    (hdistinctSecondThird : secondLabel ≠ thirdLabel)
    (hdistinctSecondFourth : secondLabel ≠ fourthLabel)
    (hdistinctThirdFourth : thirdLabel ≠ fourthLabel)
    (hbracketFirstSecond : tripleBracket (design.atom firstLabel)
      (design.atom secondLabel) normalDirection ≠ 0)
    (hbracketFirstThird : tripleBracket (design.atom firstLabel)
      (design.atom thirdLabel) normalDirection ≠ 0)
    (hbracketFirstFourth : tripleBracket (design.atom firstLabel)
      (design.atom fourthLabel) normalDirection ≠ 0)
    (hbracketSecondThird : tripleBracket (design.atom secondLabel)
      (design.atom thirdLabel) normalDirection ≠ 0)
    (hbracketSecondFourth : tripleBracket (design.atom secondLabel)
      (design.atom fourthLabel) normalDirection ≠ 0)
    (hbracketThirdFourth : tripleBracket (design.atom thirdLabel)
      (design.atom fourthLabel) normalDirection ≠ 0) :
    ∃ pairFirst pairSecond : Fin size, pairFirst ≠ pairSecond
      ∧ ∀ planarProbe : Fin 3 → ℝ, planarProbe ⬝ᵥ normalDirection = 0 →
          planarProbe ≠ 0 →
          planarProbe ⬝ᵥ planarProbe
            < (design.atom pairFirst ⬝ᵥ planarProbe) ^ 2
              + (design.atom pairSecond ⬝ᵥ planarProbe) ^ 2 :=
  exists_planeStrictPair_of_transversalAxis design hnormalUnit
    hdistinctFirstSecond hdistinctFirstThird hdistinctFirstFourth
    hdistinctSecondThird hdistinctSecondFourth hdistinctThirdFourth
    (by rw [← tripleBracket_eq_crossProduct_dotProduct]; exact hbracketFirstSecond)
    (by rw [← tripleBracket_eq_crossProduct_dotProduct]; exact hbracketFirstThird)
    (by rw [← tripleBracket_eq_crossProduct_dotProduct]; exact hbracketFirstFourth)
    (by rw [← tripleBracket_eq_crossProduct_dotProduct]; exact hbracketSecondThird)
    (by rw [← tripleBracket_eq_crossProduct_dotProduct]; exact hbracketSecondFourth)
    (by rw [← tripleBracket_eq_crossProduct_dotProduct]; exact hbracketThirdFourth)

/-! ## Part 4: non-vacuity -- the tetrahedron tie's shadow is not a tie

The frame is the rational orthonormal triple with denominator `7`.  Its normal
`(2, 3, 6)/7` misses all six planes `span(a_c, a_d)` of the tetrahedron: those
planes have normals `(0, 1, -1)`, `(1, 0, -1)`, `(1, -1, 0)`, `(1, 1, 0)`,
`(1, 0, 1)`, `(0, 1, 1)`, and `2, 3, 6` have pairwise distinct absolute values,
so none of the six pairings vanishes. -/

/-- First basis vector of the rational orthonormal frame used to shadow the
tetrahedron. -/
noncomputable def tetraGenericBasisFirst : Fin 3 → ℝ := ![6/7, 2/7, -3/7]

/-- Second basis vector of the same frame. -/
noncomputable def tetraGenericBasisSecond : Fin 3 → ℝ := ![-3/7, 6/7, -2/7]

/-- The normal of the same frame: a rational unit vector missing all six planes
spanned by pairs of tetrahedron atoms. -/
noncomputable def tetraGenericNormal : Fin 3 → ℝ := ![2/7, 3/7, 6/7]

theorem tetraGenericBasisFirst_unit :
    tetraGenericBasisFirst ⬝ᵥ tetraGenericBasisFirst = 1 := by
  norm_num [tetraGenericBasisFirst, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem tetraGenericBasisSecond_unit :
    tetraGenericBasisSecond ⬝ᵥ tetraGenericBasisSecond = 1 := by
  norm_num [tetraGenericBasisSecond, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem tetraGenericBasis_orth :
    tetraGenericBasisFirst ⬝ᵥ tetraGenericBasisSecond = 0 := by
  norm_num [tetraGenericBasisFirst, tetraGenericBasisSecond, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

theorem tetraGenericNormal_unit : tetraGenericNormal ⬝ᵥ tetraGenericNormal = 1 := by
  norm_num [tetraGenericNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem tetraGenericBasisFirst_orth_normal :
    tetraGenericBasisFirst ⬝ᵥ tetraGenericNormal = 0 := by
  norm_num [tetraGenericBasisFirst, tetraGenericNormal, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

theorem tetraGenericBasisSecond_orth_normal :
    tetraGenericBasisSecond ⬝ᵥ tetraGenericNormal = 0 := by
  norm_num [tetraGenericBasisSecond, tetraGenericNormal, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

/-- All six triple brackets of tetrahedron atom pairs against the generic normal
are nonzero: the normal sits on none of the six planes. -/
theorem tetraGenericNormal_tripleBracket_ne_zero (leftLabel rightLabel : Fin 4)
    (hdistinct : leftLabel ≠ rightLabel) :
    tripleBracket (tetraDesign.atom leftLabel) (tetraDesign.atom rightLabel)
      tetraGenericNormal ≠ 0 := by
  fin_cases leftLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hdistinct
      | norm_num [tripleBracket_eq, tetraDesign, tetraAtom, tetraGenericNormal,
          Matrix.cons_val_two]

/-- **THE TEMPLATE FIRES ON A SHIPPED FIXTURE.**  The tetrahedron's shadow along
the generic normal carries a strictly dominating pair. -/
theorem tetraShadow_exists_strictlyDominatingPair :
    ∃ dominatingPair : Finset (Fin 4), dominatingPair.card = 2
      ∧ (subsetSum (inPlaneRestriction tetraDesign tetraGenericBasisFirst
          tetraGenericBasisSecond tetraGenericBasisFirst_unit
          tetraGenericBasisSecond_unit tetraGenericBasis_orth)
          dominatingPair - 1).PosDef :=
  exists_strictlyDominatingPair_inPlaneRestriction_of_sixTripleBrackets tetraDesign
    tetraGenericBasisFirst tetraGenericBasisSecond tetraGenericNormal
    tetraGenericBasisFirst_unit tetraGenericBasisSecond_unit tetraGenericBasis_orth
    tetraGenericNormal_unit tetraGenericBasisFirst_orth_normal
    tetraGenericBasisSecond_orth_normal
    0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (tetraGenericNormal_tripleBracket_ne_zero 0 1 (by decide))
    (tetraGenericNormal_tripleBracket_ne_zero 0 2 (by decide))
    (tetraGenericNormal_tripleBracket_ne_zero 0 3 (by decide))
    (tetraGenericNormal_tripleBracket_ne_zero 1 2 (by decide))
    (tetraGenericNormal_tripleBracket_ne_zero 1 3 (by decide))
    (tetraGenericNormal_tripleBracket_ne_zero 2 3 (by decide))

/-- **THE RANK DROP BUYS STRICTNESS.**  `Gtz.tetraDesign` is a tie in `ℝ³` and its
shadow in the generic plane is NOT a tie.  So the shadow lane is not a restatement
of the parent problem: it strictly refines it on the very fixture the rank-three
campaign treats as its hardest small object. -/
theorem tetraDesign_isTie_and_not_isTie_tetraShadow :
    IsTie tetraDesign
      ∧ ¬ IsTie (inPlaneRestriction tetraDesign tetraGenericBasisFirst
          tetraGenericBasisSecond tetraGenericBasisFirst_unit
          tetraGenericBasisSecond_unit tetraGenericBasis_orth) := by
  refine ⟨tetraDesign_isTie, fun htie => ?_⟩
  obtain ⟨dominatingPair, hcard, hposDef⟩ := tetraShadow_exists_strictlyDominatingPair
  exact htie.2 dominatingPair hcard hposDef

/-- **AND THE GEOMETRIC FORM ON THE SAME FIXTURE.**  Two tetrahedron atoms
strictly over-cover every nonzero probe of the generic plane -- while no three of
them strictly dominate `ℝ³`. -/
theorem tetraShadow_exists_planeStrictPair :
    ∃ pairFirst pairSecond : Fin 4, pairFirst ≠ pairSecond
      ∧ ∀ planarProbe : Fin 3 → ℝ, planarProbe ⬝ᵥ tetraGenericNormal = 0 →
          planarProbe ≠ 0 →
          planarProbe ⬝ᵥ planarProbe
            < (tetraDesign.atom pairFirst ⬝ᵥ planarProbe) ^ 2
              + (tetraDesign.atom pairSecond ⬝ᵥ planarProbe) ^ 2 :=
  exists_inPlane_strictlyDominatingPair_of_sixTripleBrackets tetraDesign
    tetraGenericNormal_unit
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (tetraGenericNormal_tripleBracket_ne_zero 0 1 (by decide))
    (tetraGenericNormal_tripleBracket_ne_zero 0 2 (by decide))
    (tetraGenericNormal_tripleBracket_ne_zero 0 3 (by decide))
    (tetraGenericNormal_tripleBracket_ne_zero 1 2 (by decide))
    (tetraGenericNormal_tripleBracket_ne_zero 1 3 (by decide))
    (tetraGenericNormal_tripleBracket_ne_zero 2 3 (by decide))

end Gtz

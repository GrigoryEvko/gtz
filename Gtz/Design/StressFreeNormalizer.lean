/-
# Branch (i) of the `(6,3)` stress trichotomy: the normalizer quadric, the
selection-obstruction boundary, and the tight-axis mixed moment

Branch (i) of `Gtz.sixThree_stress_trichotomy` is the STRESS-FREE stratum, where
the six atom matrices are a basis of the symmetric `3x3` matrices.  This file
lands four unconditional facts about it and one general-rank law that the
rank-descent route needs.  Nothing here is a certificate: every statement is an
identity, a two-sided bound, or an explicit refutation.

## The normalizer quadric

A design's NORMALIZER FORM is a symmetric `W` with `g_c W g_c = 1` at every atom
— the quadric through all the atom tips.  Parseval alone forces `tr W = 1`
(`trace_eq_one_of_isNormalizerForm`), and then every gap matrix pairs with it to
the SAME number, `tr((S_C - 1) W) = |C| - 1`
(`trace_gap_mul_normalizerForm`): one linear functional, constant on the whole
subset layer.  Sandwiching `W` between multiples of the identity turns that into
a two-sided LEVERAGE BAND, `1/upper <= |g_c|^2 <= 1/lower`, valid at every atom
with no tie, no primitivity and no domination hypothesis
(`leverage_lower_of_normalizerForm_le`, `leverage_upper_of_le_normalizerForm`).

The band is SHARP, and its sharp case is the branch's calibration object: at
`Gtz.graphicKFourDesign` the normalizer form is `(1/3) . 1`
(`isNormalizerForm_graphicKFour`), the two bounds coincide, and the band
collapses to the single value `3` — exactly the leverage K4 carries
(`normalizerBand_collapses_at_graphicKFour`).  So "all six leverages equal" is
not a coincidence of K4's symmetry, it is the statement that its normalizer
quadric is a SPHERE.

On the stress-free stratum the form is unique whenever it exists
(`isNormalizerForm_unique_of_noConic`): two of them differ by a conic through all
six atom tips, and branch (i) is exactly the absence of one.  Existence there is
supplied by the Veronese grid of the sibling stress-free module and is
deliberately NOT rebuilt here.

## The label-free selection obstruction reaches branch (i) — at K4

`Gtz.exists_symmetry_with_no_fixed_dominatingSubset` refutes every
relabelling-invariant selection rule, and its shipped witness is
`Gtz.doubledTetrahedronDesign`, which repeats two atoms.  A repeated atom is a
stress on the nose (`doubledTetrahedron_hasStress`), so that witness is NOT
stress-free (`not_stressFree_doubledTetrahedronDesign`) and lies outside branch
(i).  It would be a mistake to read that as branch (i) being exempt.  It is not:
K4 supplies its own witness, and K4 is the branch's calibration object.

The orthogonal reflection `diag(1, 1, -1)` maps K4's atom family to itself,
realising the label involution `(2 3)(4 5)`
(`kFourReflection_mulVec_atom`), and the weights are constant so they are
preserved.  Exactly four triples are invariant under that involution —
`{0,2,3}`, `{0,4,5}`, `{1,2,3}`, `{1,4,5}`
(`kFourEdgeSwap_invariantTriple_cases`) — and NONE of them dominates: each has gap
determinant `-1` (`not_dominates_graphicKFour_invariantTriples`), while the four
triples that do dominate are the vertex stars, which the involution permutes in
two orbits of two.  So a single-valued selection rule computed from
relabelling-invariant data must return an invariant triple at K4 and must
therefore be wrong there
(`labelFreeSelection_fails_on_stressFree_graphicKFour`).

The obstruction is therefore not an artifact of repeated atoms: it survives on the
primitive stress-free stratum, at its sharpest point.  Nothing below proposes a
selection rule.

## Maximal volume is BLIND at K4

The classical Goreinov-Tyrtyshnikov selection rule is maximal volume: take the
subset maximising `det S_C`.  At K4 that rule cannot decide anything.  The star
`{0,2,4}` dominates strictly and the triple `{0,1,2}` does not, yet both have
`det S_C = 27/2` (`maxVolume_is_blind_at_graphicKFour`).  The reason is exact:
`det (S_C - 1) = det S_C - e2(S_C) + tr S_C - 1`
(`det_sub_one_three_eq_elementarySymmetric`), and at K4 all twenty triples share
`tr S_C = 9` while the sixteen bases share `det S_C = 27/2`, so the whole
discriminating content sits in the SECOND invariant, which the volume rule never
reads.  This is the volume-side twin of the two-invariant blindness already
recorded on this stratum, and it removes the oldest rule on the table — the one
the 1997 problem is named after.

## The tight-axis mixed moment

At a tie the dominating subset has a tight direction, and the tree already pins
its axis mass twice over (`Gtz.tightDirection_rayleigh_identity`,
`Gtz.tightDirection_subset_eq_weighted`).  What was missing is the CROSS term:
along the tight axis the selected atoms are exactly uncorrelated with every
direction orthogonal to it (`tightDirection_mixedMoment_eq_zero`), and so is the
whole weighted design (`parseval_mixedMoment_eq_zero`).  Those two are the moment
data a rank-two companion is built from — the analogue at a tight axis of the
planar mixed moment the two-pole lane spends to rescale a plane anisotropically.
Assembled as `tightAxis_companionMoments`, and read at a `(6,3)` tie as
`sixThree_tie_companionMoments`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.DiamondPrimitive
import Gtz.Design.NearPencilTransport
import Gtz.Reduction.RayleighCertificate
import Gtz.Quantitative.IsolatedBlockExclusion
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Quantitative.DecisionAtlasCellsSevenThree
import Gtz.Ties.SelectionObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Part 1: the normalizer quadric -/

/-- **The normalizer form of a design**: a symmetric matrix whose quadratic form
takes the value one at every atom.  Geometrically it is the quadric through all
the atom tips; on the stress-free stratum it exists and is unique, and it is the
only linear datum that treats all six atoms alike. -/
def IsNormalizerForm (design : WeightedDesign size rank)
    (normalizer : Matrix (Fin rank) (Fin rank) ℝ) : Prop :=
  normalizerᵀ = normalizer
    ∧ ∀ atomIndex, design.atom atomIndex ⬝ᵥ (normalizer *ᵥ design.atom atomIndex) = 1

/-- The trace pairing of a matrix with a rank-one atom is that matrix's quadratic
form at the atom's vector. -/
theorem trace_mul_atomMatrix (multiplier : Matrix (Fin rank) (Fin rank) ℝ)
    (vec : Fin rank → ℝ) :
    Matrix.trace (multiplier * atomMatrix vec) = vec ⬝ᵥ (multiplier *ᵥ vec) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, atomMatrix,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **PARSEVAL FIXES THE NORMALIZER'S TRACE AT ONE.**  Expanding the identity in
the design's own weighted atoms turns the trace into the weight sum.  No
stress-freeness, no size or rank hypothesis. -/
theorem trace_eq_one_of_isNormalizerForm (design : WeightedDesign size rank)
    {normalizer : Matrix (Fin rank) (Fin rank) ℝ}
    (hnormalizer : IsNormalizerForm design normalizer) :
    Matrix.trace normalizer = 1 := by
  have hexpand : Matrix.trace (normalizer * (1 : Matrix (Fin rank) (Fin rank) ℝ))
      = ∑ atomIndex, design.weight atomIndex := by
    conv_lhs => rw [← design.isParseval]
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_atomMatrix,
      hnormalizer.2 atomIndex, smul_eq_mul, mul_one]
  rw [Matrix.mul_one] at hexpand
  rw [hexpand, design.weight_sum_one]

/-- **ONE LINEAR FUNCTIONAL, CONSTANT ON THE WHOLE SUBSET LAYER.**  Every gap
matrix pairs with the normalizer form to its own cardinality minus one — the
subset enters only through how many atoms it holds, never through which.  At
`(6,3)` all twenty triples read exactly two. -/
theorem trace_gap_mul_normalizerForm (design : WeightedDesign size rank)
    {normalizer : Matrix (Fin rank) (Fin rank) ℝ}
    (hnormalizer : IsNormalizerForm design normalizer) (selected : Finset (Fin size)) :
    Matrix.trace ((subsetSum design selected - 1) * normalizer)
      = (selected.card : ℝ) - 1 := by
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul,
    trace_eq_one_of_isNormalizerForm design hnormalizer]
  congr 1
  have hterm : ∀ atomIndex ∈ selected,
      Matrix.trace (atomMatrix (design.atom atomIndex) * normalizer) = 1 := by
    intro atomIndex _
    rw [Matrix.trace_mul_comm, trace_mul_atomMatrix, hnormalizer.2 atomIndex]
  rw [subsetSum, Matrix.sum_mul, Matrix.trace_sum, Finset.sum_congr rfl hterm,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **THE LEVERAGE FLOOR FROM THE NORMALIZER QUADRIC.**  An upper Loewner bound
on the normalizer form is a lower bound on every leverage at once: the quadric
takes the value one at each atom tip, so a flatter quadric needs longer atoms. -/
theorem leverage_lower_of_normalizerForm_le (design : WeightedDesign size rank)
    {normalizer : Matrix (Fin rank) (Fin rank) ℝ}
    (hnormalizer : IsNormalizerForm design normalizer) {upper : ℝ}
    (hupper : (upper • (1 : Matrix (Fin rank) (Fin rank) ℝ) - normalizer).PosSemidef)
    (atomIndex : Fin size) :
    1 ≤ upper * leverageOf (design.atom atomIndex) := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hupper).2 (design.atom atomIndex)
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, hnormalizer.2 atomIndex,
    ← leverageOf_eq_dotProduct_self] at hform
  linarith

/-- **THE LEVERAGE CEILING FROM THE NORMALIZER QUADRIC.**  The mirror bound: a
lower Loewner bound on the form caps every leverage. -/
theorem leverage_upper_of_le_normalizerForm (design : WeightedDesign size rank)
    {normalizer : Matrix (Fin rank) (Fin rank) ℝ}
    (hnormalizer : IsNormalizerForm design normalizer) {lower : ℝ}
    (hlower : (normalizer - lower • (1 : Matrix (Fin rank) (Fin rank) ℝ)).PosSemidef)
    (atomIndex : Fin size) :
    lower * leverageOf (design.atom atomIndex) ≤ 1 := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hlower).2 (design.atom atomIndex)
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, hnormalizer.2 atomIndex,
    ← leverageOf_eq_dotProduct_self] at hform
  linarith

/-- **THE NORMALIZER FORM IS UNIQUE OFF THE CONIC LOCUS.**  Two of them differ by
a symmetric matrix vanishing at all the atom tips — a conic through the whole
configuration — and branch (i) of the stress trichotomy is exactly the absence of
one. -/
theorem isNormalizerForm_unique_of_noConic (design : WeightedDesign size rank)
    (hnoConic : ∀ conic : Matrix (Fin rank) (Fin rank) ℝ, conicᵀ = conic →
      (∀ atomIndex, design.atom atomIndex ⬝ᵥ (conic *ᵥ design.atom atomIndex) = 0) →
        conic = 0)
    {firstForm secondForm : Matrix (Fin rank) (Fin rank) ℝ}
    (hfirst : IsNormalizerForm design firstForm)
    (hsecond : IsNormalizerForm design secondForm) :
    firstForm = secondForm := by
  have hdifference : firstForm - secondForm = 0 := by
    refine hnoConic (firstForm - secondForm) ?_ ?_
    · rw [Matrix.transpose_sub, hfirst.1, hsecond.1]
    · intro atomIndex
      rw [Matrix.sub_mulVec, dotProduct_sub, hfirst.2 atomIndex, hsecond.2 atomIndex, sub_self]
  rwa [sub_eq_zero] at hdifference

/-! ## Part 2: the normalizer quadric of K4 is a sphere -/

/-- **K4'S NORMALIZER QUADRIC IS THE SPHERE `(1/3) . 1`.**  The design's six
leverages are all exactly three, so the isotropic form takes the value one at
every atom tip. -/
theorem isNormalizerForm_graphicKFour :
    IsNormalizerForm graphicKFourDesign ((1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
  refine ⟨by rw [Matrix.transpose_smul, Matrix.transpose_one], fun edge => ?_⟩
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
    ← leverageOf_eq_dotProduct_self, graphicKFourDesign_leverage]
  norm_num

/-- **THE BAND COLLAPSES AT K4**, which is why all six of its leverages agree.
Both Loewner bounds hold at the same value `1/3` — the quadric is a sphere — so
the floor and the ceiling pin every leverage to exactly three.  This is the sharp
case of `leverage_lower_of_normalizerForm_le` and
`leverage_upper_of_le_normalizerForm`; away from K4 the two bounds separate and
the band has width. -/
theorem normalizerBand_collapses_at_graphicKFour (edge : Fin 6) :
    1 ≤ (1 / 3 : ℝ) * leverageOf (graphicKFourDesign.atom edge)
      ∧ (1 / 3 : ℝ) * leverageOf (graphicKFourDesign.atom edge) ≤ 1 := by
  have hzero : ((1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - (1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
    rw [sub_self]
    exact Matrix.PosSemidef.zero
  exact ⟨leverage_lower_of_normalizerForm_le graphicKFourDesign isNormalizerForm_graphicKFour
      hzero edge,
    leverage_upper_of_le_normalizerForm graphicKFourDesign isNormalizerForm_graphicKFour
      hzero edge⟩

/-! ## Part 3: where the label-free selection obstruction's shipped witness sits -/

/-- The doubled tetrahedron repeats its first two atoms. -/
theorem doubledTetrahedron_atom_zero_eq_one :
    doubledTetrahedronDesign.atom 0 = doubledTetrahedronDesign.atom 1 := by
  funext coord
  fin_cases coord <;> rfl

/-- **THE OBSTRUCTION'S WITNESS CARRIES AN EXPLICIT STRESS.**  Atoms `0` and `1`
of `Gtz.doubledTetrahedronDesign` coincide, so the coefficient vector
`(1, -1, 0, 0, 0, 0)` annihilates the atom family. -/
theorem doubledTetrahedron_hasStress :
    (∑ atomIndex, (![1, -1, 0, 0, 0, 0] : Fin 6 → ℝ) atomIndex
        • atomMatrix (doubledTetrahedronDesign.atom atomIndex)) = 0 := by
  rw [Fin.sum_univ_six]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val,
    Matrix.tail_cons, zero_smul, add_zero, one_smul, neg_smul]
  rw [doubledTetrahedron_atom_zero_eq_one, add_neg_cancel]

/-- **THE OBSTRUCTION'S SHIPPED WITNESS IS NOT STRESS-FREE.**
`Gtz.exists_symmetry_with_no_fixed_dominatingSubset` refutes every
relabelling-invariant selection rule using `Gtz.doubledTetrahedronDesign`, and
that design's repeated atom pair is a stress on the nose, so it lies outside
branch (i).  Recorded to place the witness, NOT to exempt the branch — Part 3b
below produces a stress-free witness for the same obstruction. -/
theorem not_stressFree_doubledTetrahedronDesign :
    ¬ ∀ stressCoeff : Fin 6 → ℝ,
        (∑ atomIndex, stressCoeff atomIndex
            • atomMatrix (doubledTetrahedronDesign.atom atomIndex)) = 0 →
          stressCoeff = 0 := by
  intro hstressFree
  have hvanishes := hstressFree _ doubledTetrahedron_hasStress
  have hentry := congrFun hvanishes 0
  simp only [Matrix.cons_val_zero, Pi.zero_apply] at hentry
  exact one_ne_zero hentry

/-! ## Part 3b: K4 is a STRESS-FREE witness for the same obstruction -/

/-- The squared pairing of a K4 atom against any probe is rational: the irrational
scale only ever appears squared. -/
theorem sq_dotProduct_graphicKFourAtom (edge : Fin 6) (probe : Fin 3 → ℝ) :
    (graphicKFourDesign.atom edge ⬝ᵥ probe) ^ 2
      = 3 / 2 * (kFourEdgeVector edge ⬝ᵥ probe) ^ 2 := by
  have hdot : graphicKFourDesign.atom edge ⬝ᵥ probe
      = graphicKFourScale * (kFourEdgeVector edge ⬝ᵥ probe) := by
    rw [graphicKFourDesign_atom, dotProduct, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun coord _ => by rw [graphicKFourAtom]; ring
  rw [hdot, mul_pow, graphicKFourScale_sq]

/-- The reflection in the third coordinate.  It is orthogonal and it maps K4's six
root directions to themselves. -/
def kFourReflection : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![1, 1, -1]

/-- The label involution the reflection realizes: `(2 3)(4 5)`. -/
def kFourEdgeSwap : Fin 6 → Fin 6 :=
  ![0, 1, 3, 2, 5, 4]

/-- The reflection is orthogonal. -/
theorem kFourReflection_orthogonal : kFourReflection * kFourReflectionᵀ = 1 := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourReflection, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- The swap is an involution, so it is a genuine relabelling of the design. -/
theorem kFourEdgeSwap_involutive (edge : Fin 6) : kFourEdgeSwap (kFourEdgeSwap edge) = edge := by
  fin_cases edge <;> rfl

/-- **THE REFLECTION IS A SYMMETRY OF K4'S DESIGN.**  It carries every atom to the
atom of its swapped label, and the weights are constant, so the relabelling
`(2 3)(4 5)` preserves every invariant datum of the design. -/
theorem kFourReflection_mulVec_atom (edge : Fin 6) :
    kFourReflection *ᵥ graphicKFourDesign.atom edge
      = graphicKFourDesign.atom (kFourEdgeSwap edge) := by
  funext coord
  fin_cases edge <;> fin_cases coord <;>
    simp [kFourReflection, kFourEdgeSwap, graphicKFourDesign_atom, graphicKFourAtom,
      kFourEdgeVector, Matrix.mulVec, Matrix.diagonal_apply, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]

/-- The design's weights are invariant under the relabelling. -/
theorem kFourEdgeSwap_preserves_weight (edge : Fin 6) :
    graphicKFourDesign.weight (kFourEdgeSwap edge) = graphicKFourDesign.weight edge := rfl

/-- **EXACTLY FOUR TRIPLES ARE INVARIANT UNDER THE RELABELLING.**  Its orbits have
sizes `1, 1, 2, 2`, so an invariant triple is one fixed label plus one two-orbit. -/
theorem kFourEdgeSwap_invariantTriple_cases (selected : Finset (Fin 6))
    (hcard : selected.card = 3)
    (hinvariant : ∀ edge : Fin 6, edge ∈ selected ↔ kFourEdgeSwap edge ∈ selected) :
    selected = {0, 2, 3} ∨ selected = {0, 4, 5} ∨ selected = {1, 2, 3}
      ∨ selected = {1, 4, 5} := by
  revert hcard hinvariant
  revert selected
  decide

/-- Each invariant triple fails, by one explicit probe in the plane of the two
fixed labels. -/
theorem not_dominates_graphicKFour_invariantTriples :
    ¬ Dominates graphicKFourDesign {0, 2, 3} ∧ ¬ Dominates graphicKFourDesign {0, 4, 5}
      ∧ ¬ Dominates graphicKFourDesign {1, 2, 3} ∧ ¬ Dominates graphicKFourDesign {1, 4, 5} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine not_dominates_triple_of_negativeDirection graphicKFourDesign 0 2 3 (by decide)
      (by decide) (by decide) ![1, -3, 0] ?_
    rw [sq_dotProduct_graphicKFourAtom, sq_dotProduct_graphicKFourAtom,
      sq_dotProduct_graphicKFourAtom]
    simp [kFourEdgeVector, dotProduct, Fin.sum_univ_three]
    norm_num
  · refine not_dominates_triple_of_negativeDirection graphicKFourDesign 0 4 5 (by decide)
      (by decide) (by decide) ![-3, 1, 0] ?_
    rw [sq_dotProduct_graphicKFourAtom, sq_dotProduct_graphicKFourAtom,
      sq_dotProduct_graphicKFourAtom]
    simp [kFourEdgeVector, dotProduct, Fin.sum_univ_three]
    norm_num
  · refine not_dominates_triple_of_negativeDirection graphicKFourDesign 1 2 3 (by decide)
      (by decide) (by decide) ![1, 3, 0] ?_
    rw [sq_dotProduct_graphicKFourAtom, sq_dotProduct_graphicKFourAtom,
      sq_dotProduct_graphicKFourAtom]
    simp [kFourEdgeVector, dotProduct, Fin.sum_univ_three]
    norm_num
  · refine not_dominates_triple_of_negativeDirection graphicKFourDesign 1 4 5 (by decide)
      (by decide) (by decide) ![3, 1, 0] ?_
    rw [sq_dotProduct_graphicKFourAtom, sq_dotProduct_graphicKFourAtom,
      sq_dotProduct_graphicKFourAtom]
    simp [kFourEdgeVector, dotProduct, Fin.sum_univ_three]
    norm_num

/-- **NO LABEL-FREE SELECTION RULE WORKS ON THE STRESS-FREE STRATUM EITHER.**  K4
is stress-free, primitive, and the branch's calibration object, and it carries an
orthogonal symmetry — the reflection `diag(1,1,-1)`, realising the label
involution `(2 3)(4 5)` — under which NO invariant triple dominates, while the
four that do dominate are permuted in two orbits of two.

A single-valued selection rule computed from relabelling-invariant data has to
return an invariant triple here, so it returns a triple that does not dominate.
`Gtz.exists_symmetry_with_no_fixed_dominatingSubset` proves the same at
`Gtz.doubledTetrahedronDesign`, but that witness repeats an atom and is not
stress-free (`not_stressFree_doubledTetrahedronDesign`); this one is.  So the
obstruction is not an artifact of repeated atoms, and branch (i) has no exemption
from it.  What survives is EXISTENCE — `Gtz.StressFreeHingeHoldsSixThree` is an
existence statement and the obstruction does not touch it — and set-valued
selection: the four stars ARE an invariant set, just not an invariant triple. -/
theorem labelFreeSelection_fails_on_stressFree_graphicKFour :
    kFourReflection * kFourReflectionᵀ = 1
      ∧ (∀ edge : Fin 6, kFourReflection *ᵥ graphicKFourDesign.atom edge
          = graphicKFourDesign.atom (kFourEdgeSwap edge))
      ∧ (∀ edge : Fin 6,
          graphicKFourDesign.weight (kFourEdgeSwap edge) = graphicKFourDesign.weight edge)
      ∧ (∀ selected : Finset (Fin 6), selected.card = 3 →
          (∀ edge : Fin 6, edge ∈ selected ↔ kFourEdgeSwap edge ∈ selected) →
            ¬ Dominates graphicKFourDesign selected) := by
  refine ⟨kFourReflection_orthogonal, kFourReflection_mulVec_atom,
    kFourEdgeSwap_preserves_weight, fun selected hcard hinvariant => ?_⟩
  obtain ⟨hzeroTwoThree, hzeroFourFive, honeTwoThree, honeFourFive⟩ :=
    not_dominates_graphicKFour_invariantTriples
  rcases kFourEdgeSwap_invariantTriple_cases selected hcard hinvariant with
    hset | hset | hset | hset <;> rw [hset]
  · exact hzeroTwoThree
  · exact hzeroFourFive
  · exact honeTwoThree
  · exact honeFourFive

/-! ## Part 4: maximal volume is blind at K4 -/

/-- **THE GAP DETERMINANT IN THE VOLUME'S OWN INVARIANTS.**  For a `3x3` form,
`det (M - 1) = det M - e2(M) + e1(M) - 1`.  The volume rule reads only the first
term. -/
theorem det_sub_one_three_eq_elementarySymmetric (form : Matrix (Fin 3) (Fin 3) ℝ) :
    (form - 1).det
      = form.det
        - ((form 0 0 * form 1 1 - form 0 1 * form 1 0)
            + (form 0 0 * form 2 2 - form 0 2 * form 2 0)
            + (form 1 1 * form 2 2 - form 1 2 * form 2 1))
        + (form 0 0 + form 1 1 + form 2 2) - 1 := by
  simp only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.one_apply, Fin.reduceEq,
    if_true, if_false]
  ring

/-- Every entry of a K4 subset sum, as a rational sum over the selected edges. -/
theorem subsetSum_graphicKFour_apply (selected : Finset (Fin 6)) (rowIndex colIndex : Fin 3) :
    subsetSum graphicKFourDesign selected rowIndex colIndex
      = ∑ edge ∈ selected,
          3 / 2 * (kFourEdgeVector edge rowIndex * kFourEdgeVector edge colIndex) := by
  rw [subsetSum, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun edge _ => by
    rw [graphicKFourDesign_atom, atomMatrix_graphicKFourAtom_apply]

/-- The star triple's moment matrix at K4. -/
theorem subsetSum_graphicKFour_starTriple :
    subsetSum graphicKFourDesign {0, 2, 4}
      = !![3, 3 / 2, 3 / 2; 3 / 2, 3, 3 / 2; 3 / 2, 3 / 2, 3] := by
  ext rowIndex colIndex
  rw [subsetSum_graphicKFour_apply,
    show ({0, 2, 4} : Finset (Fin 6)) = insert 0 (insert 2 {4}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [kFourEdgeVector, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val,
      Matrix.tail_cons, Matrix.of_apply]

/-- The matching-pair triple's moment matrix at K4: a different matrix, the same
determinant. -/
theorem subsetSum_graphicKFour_matchingTriple :
    subsetSum graphicKFourDesign {0, 1, 2}
      = !![9 / 2, 0, 3 / 2; 0, 3, 0; 3 / 2, 0, 3 / 2] := by
  ext rowIndex colIndex
  rw [subsetSum_graphicKFour_apply,
    show ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 {2}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [kFourEdgeVector, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val,
      Matrix.tail_cons, Matrix.of_apply]

/-- The star triple of K4 dominates STRICTLY, by the three-invariant criterion:
its gap has `e1 = 6`, `e2 = 21/4`, `e3 = 5/4`. -/
theorem posDef_gap_graphicKFour_starTriple :
    (subsetSum graphicKFourDesign {0, 2, 4} - 1).PosDef := by
  rw [subsetSum_graphicKFour_starTriple]
  refine posDef_three_of_elementarySymmetric ?_ ?_ ?_ ?_
  · ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.transpose_apply, Matrix.sub_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.of_apply]
  · simp [Matrix.sub_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
    norm_num
  · simp [Matrix.sub_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
    norm_num
  · simp [Matrix.det_fin_three, Matrix.sub_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.of_apply]
    norm_num

/-- The matching-pair triple of K4 does NOT dominate: the probe `(1, 0, -3)` sees
moment `9` against norm `10`. -/
theorem not_dominates_graphicKFour_matchingTriple :
    ¬ Dominates graphicKFourDesign {0, 1, 2} := by
  refine not_dominates_triple_of_negativeDirection graphicKFourDesign 0 1 2 (by decide)
    (by decide) (by decide) ![1, 0, -3] ?_
  rw [sq_dotProduct_graphicKFourAtom, sq_dotProduct_graphicKFourAtom,
    sq_dotProduct_graphicKFourAtom]
  norm_num [kFourEdgeVector, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **MAXIMAL VOLUME IS BLIND AT K4.**  The 1997 problem's own selection heuristic
— take the subset of maximal `|det|` — cannot see the difference between a
dominating triple and a non-dominating one of the SAME design.  The star `{0,2,4}`
dominates strictly, the matching triple `{0,1,2}` does not, and both have moment
determinant exactly `27/2`.

So the volume rule joins the two-invariant chart in the blind column: not lossy,
BLIND.  The explanation is `det_sub_one_three_eq_elementarySymmetric` — at K4 the
first invariant is `9` on all twenty triples and the third is `27/2` on all
sixteen bases, so every bit of discriminating information sits in the second
invariant, which the volume never reads. -/
theorem maxVolume_is_blind_at_graphicKFour :
    (subsetSum graphicKFourDesign {0, 2, 4}).det = 27 / 2
      ∧ (subsetSum graphicKFourDesign {0, 1, 2}).det = 27 / 2
      ∧ (subsetSum graphicKFourDesign {0, 2, 4} - 1).PosDef
      ∧ ¬ Dominates graphicKFourDesign {0, 1, 2} := by
  refine ⟨?_, ?_, posDef_gap_graphicKFour_starTriple, not_dominates_graphicKFour_matchingTriple⟩
  · rw [subsetSum_graphicKFour_starTriple]
    simp [Matrix.det_fin_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
    norm_num
  · rw [subsetSum_graphicKFour_matchingTriple]
    simp [Matrix.det_fin_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
    norm_num

/-! ## Part 5: the tight-axis mixed moment -/

/-- **THE VECTOR MASS LAW AT A TIGHT AXIS.**  The shipped
`Gtz.tightDirection_subset_eq_weighted` equates the subset's axis mass with the
design's weighted one as SCALARS.  Both are in fact the same VECTOR — the axis
itself — because the tight direction is a unit eigenvector of the subset moment
and Parseval says the same of the whole design.  Pairing this against the axis
recovers the scalar law; pairing it against the orthogonal plane is the cross
moment below, so this single identity carries both. -/
theorem tightDirection_vectorMass_eq_weighted (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    {axis : Fin rank → ℝ}
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0) :
    ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) • design.atom atomIndex
      = ∑ atomIndex, (design.weight atomIndex * (design.atom atomIndex ⬝ᵥ axis))
          • design.atom atomIndex := by
  have hsubset : ∑ atomIndex ∈ selected,
      (design.atom atomIndex ⬝ᵥ axis) • design.atom atomIndex = axis := by
    rw [← subsetSum_mulVec_eq_sum]
    exact tightDirection_isEigenvector design hdominates htight
  have hweighted : ∑ atomIndex, (design.weight atomIndex * (design.atom atomIndex ⬝ᵥ axis))
      • design.atom atomIndex = axis := by
    have hparseval : (∑ atomIndex, design.weight atomIndex
          • atomMatrix (design.atom atomIndex)) *ᵥ axis = axis := by
      rw [design.isParseval, Matrix.one_mulVec]
    rw [Matrix.sum_mulVec] at hparseval
    have hterm : ∀ atomIndex : Fin size,
        (design.weight atomIndex • atomMatrix (design.atom atomIndex)) *ᵥ axis
          = (design.weight atomIndex * (design.atom atomIndex ⬝ᵥ axis))
              • design.atom atomIndex := by
      intro atomIndex
      rw [Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq, smul_smul,
        dotProduct_comm (design.atom atomIndex) axis]
    calc ∑ atomIndex, (design.weight atomIndex * (design.atom atomIndex ⬝ᵥ axis))
            • design.atom atomIndex
        = ∑ atomIndex, (design.weight atomIndex • atomMatrix (design.atom atomIndex)) *ᵥ axis :=
          Finset.sum_congr rfl fun atomIndex _ => (hterm atomIndex).symm
      _ = axis := hparseval
  rw [hsubset, hweighted]

/-- **THE TIGHT AXIS DECOUPLES THE DOMINATING SUBSET.**  A tight direction of a
dominating subset is a unit eigenvector of its moment matrix, so the selected
atoms have EXACTLY ZERO correlation between that axis and every direction
orthogonal to it.  This is the cross-moment a rank-two companion needs in order to
rescale the orthogonal plane anisotropically without breaking Parseval; the
axis-mass half is already shipped as `Gtz.tightDirection_rayleigh_identity`. -/
theorem tightDirection_mixedMoment_eq_zero (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    {axis : Fin rank → ℝ}
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0)
    {planar : Fin rank → ℝ} (horthogonal : planar ⬝ᵥ axis = 0) :
    ∑ atomIndex ∈ selected,
        (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar) = 0 := by
  have heigenvector := tightDirection_isEigenvector design hdominates htight
  have hpairing : (subsetSum design selected *ᵥ axis) ⬝ᵥ planar = 0 := by
    rw [heigenvector, dotProduct_comm]
    exact horthogonal
  rw [← subsetSum_mulVec_dotProduct_eq_sum]
  exact hpairing

/-- **THE DESIGN'S OWN CROSS MOMENT VANISHES TOO**, along every orthogonal pair of
directions and with no subset in sight: it is Parseval read off the diagonal. -/
theorem parseval_mixedMoment_eq_zero (design : WeightedDesign size rank)
    (axis planar : Fin rank → ℝ) (horthogonal : planar ⬝ᵥ axis = 0) :
    ∑ atomIndex, design.weight atomIndex
        * ((design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar)) = 0 := by
  have hexpand : ((∑ atomIndex, design.weight atomIndex
          • atomMatrix (design.atom atomIndex)) *ᵥ axis) ⬝ᵥ planar
      = ∑ atomIndex, design.weight atomIndex
          * ((design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar)) := by
    rw [Matrix.sum_mulVec, sum_dotProduct]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Matrix.smul_mulVec, smul_dotProduct, smul_eq_mul, atomMatrix, vecMulVec_mulVec_eq,
      smul_dotProduct, smul_eq_mul, dotProduct_comm (design.atom atomIndex) axis]
  rw [design.isParseval, Matrix.one_mulVec] at hexpand
  rw [← hexpand, dotProduct_comm]
  exact horthogonal

/-- **THE COMPANION MOMENTS AT A TIGHT AXIS**, assembled.  Given a dominating
subset with a tight direction, the four exact moments a reweighted rank-two
companion is built from: the subset's axis mass equals the axis norm, the design's
weighted axis mass equals it too, and BOTH cross moments against the orthogonal
plane vanish.  Every clause is an identity; none of them is a certificate, so none
of them degenerates at a tie — which is the point of taking this route rather than
a sharper inequality. -/
theorem tightAxis_companionMoments (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    {axis : Fin rank → ℝ}
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0)
    {planar : Fin rank → ℝ} (horthogonal : planar ⬝ᵥ axis = 0) :
    (∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2 = axis ⬝ᵥ axis)
      ∧ (∑ atomIndex, design.weight atomIndex * (design.atom atomIndex ⬝ᵥ axis) ^ 2
          = axis ⬝ᵥ axis)
      ∧ (∑ atomIndex ∈ selected,
          (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar) = 0)
      ∧ (∑ atomIndex, design.weight atomIndex
          * ((design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar)) = 0) :=
  ⟨tightDirection_rayleigh_identity design selected htight,
    parseval_weighted_sum_sq design axis,
    tightDirection_mixedMoment_eq_zero design hdominates htight horthogonal,
    parseval_mixedMoment_eq_zero design axis planar horthogonal⟩

/-- **THE TIGHT AXIS IS A LINEAR SYZYGY OF THE DIRECTIONS.**  Subtracting the two
sides of the vector mass law puts the six numbers `(1_C(c) - t_c)(g_c . w)` in the
kernel of the direction matrix.  Unlike a stress — a dependence among the atom
MATRICES, which branch (i) forbids outright — this is a dependence among the
direction VECTORS, and at rank three that kernel is three-dimensional at size six,
so no counting alone refutes it.  What the tie supplies is that the syzygy is
CARRIED BY THE GAP's own coordinates. -/
theorem tightAxis_syzygy (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    {axis : Fin rank → ℝ}
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0) :
    ∑ atomIndex, (((if atomIndex ∈ selected then (1 : ℝ) else 0) - design.weight atomIndex)
        * (design.atom atomIndex ⬝ᵥ axis)) • design.atom atomIndex = 0 := by
  classical
  have hsplit : ∀ atomIndex : Fin size,
      (((if atomIndex ∈ selected then (1 : ℝ) else 0) - design.weight atomIndex)
          * (design.atom atomIndex ⬝ᵥ axis)) • design.atom atomIndex
        = (if atomIndex ∈ selected then
              (design.atom atomIndex ⬝ᵥ axis) • design.atom atomIndex else 0)
          - (design.weight atomIndex * (design.atom atomIndex ⬝ᵥ axis))
              • design.atom atomIndex := by
    intro atomIndex
    by_cases hmember : atomIndex ∈ selected
    · rw [if_pos hmember, if_pos hmember, sub_mul, sub_smul, one_mul]
    · rw [if_neg hmember, if_neg hmember, sub_mul, sub_smul, zero_mul, zero_smul]
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, sub_eq_zero]
  exact tightDirection_vectorMass_eq_weighted design hdominates htight

/-- **THE TIE'S SYZYGY COEFFICIENTS ARE NOT ALL ZERO.**  On the selected side the
coefficient is `(1 - t_c)(g_c . w)`, and every weight of a design with at least two
atoms is strictly below one, so vanishing would force the whole axis mass of the
subset to vanish — contradicting `Gtz.tightDirection_rayleigh_identity`, which pins
it at the axis norm.  So the syzygy is a genuine nonzero kernel element. -/
theorem tightAxis_syzygyCoefficients_ne_zero (design : WeightedDesign size rank)
    (hsize : 2 ≤ size) {selected : Finset (Fin size)}
    {axis : Fin rank → ℝ} (haxisNe : axis ≠ 0)
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0) :
    ∃ atomIndex : Fin size,
      ((if atomIndex ∈ selected then (1 : ℝ) else 0) - design.weight atomIndex)
        * (design.atom atomIndex ⬝ᵥ axis) ≠ 0 := by
  classical
  by_contra hallZero
  push Not at hallZero
  have hmass := tightDirection_rayleigh_identity design selected htight
  have hvanishes : ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun atomIndex hmember => ?_
    have hcoefficient := hallZero atomIndex
    rw [if_pos hmember] at hcoefficient
    have hbelowOne : design.weight atomIndex < 1 := weight_lt_one design hsize atomIndex
    have hpairingZero : design.atom atomIndex ⬝ᵥ axis = 0 :=
      (mul_eq_zero.mp hcoefficient).resolve_left (by linarith)
    rw [hpairingZero]
    norm_num
  rw [hvanishes] at hmass
  exact haxisNe (by
    have hnormPos : 0 < axis ⬝ᵥ axis := dotProduct_self_pos haxisNe
    linarith)

/-- **THE COMPANION MOMENTS AT A `(6,3)` TIE.**  A tie supplies the dominating
triple and the tight direction (`Gtz.isTie_yields_tightDirection`), so the moment
data above is available at every tie of the cell with nothing assumed beyond the
tie itself.  This is the entry point of the rank-descent route on branch (i): the
plane orthogonal to the tight axis carries a genuine rank-two design, and these are
its moments. -/
theorem sixThree_tie_companionMoments (design : WeightedDesign 6 3) (htie : IsTie design) :
    ∃ (selected : Finset (Fin 6)) (axis : Fin 3 → ℝ),
      selected.card = 3 ∧ Dominates design selected ∧ axis ≠ 0
        ∧ (∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2 = axis ⬝ᵥ axis)
        ∧ (∑ atomIndex, design.weight atomIndex * (design.atom atomIndex ⬝ᵥ axis) ^ 2
            = axis ⬝ᵥ axis)
        ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 →
            (∑ atomIndex ∈ selected,
                (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar) = 0)
              ∧ (∑ atomIndex, design.weight atomIndex
                  * ((design.atom atomIndex ⬝ᵥ axis)
                      * (design.atom atomIndex ⬝ᵥ planar)) = 0) := by
  obtain ⟨selected, axis, hcard, hdominates, haxisNe, htight⟩ :=
    isTie_yields_tightDirection htie
  refine ⟨selected, axis, hcard, hdominates, haxisNe,
    tightDirection_rayleigh_identity design selected htight,
    parseval_weighted_sum_sq design axis, fun planar horthogonal => ?_⟩
  exact ⟨tightDirection_mixedMoment_eq_zero design hdominates htight horthogonal,
    parseval_mixedMoment_eq_zero design axis planar horthogonal⟩

/-! ## Part 6: the tight-axis exchange transport

The two-pole lane transports a rank-two companion back to rank three by
rescaling the probe plane anisotropically, which its vanishing planar mixed
moment licenses.  On branch (i) there is no distinguished plane and no pole to
bundle, but the tight axis of a weakly dominating subset supplies the same
licence in a stronger form: `tightDirection_mixedMoment_eq_zero` kills the cross
moment against EVERY orthogonal direction at once, not just one cross axis.

That turns the transport into an EXCHANGE.  Split a probe as `planar + s . axis`.
For any subset `T` the gap form reads

    P_T(planar) + 2 s M_T(planar) + s^2 (A_T - 1),

with `A_T` the axis mass, `M_T` the cross moment and `P_T` the planar excess, so
`A_T > 1` plus a discriminant bound is already positive definiteness
(`posDef_gap_of_axisSplit_coupling`) — no frame, no square root, no spectral
theorem.  Now take `T` to be the tight subset with one atom exchanged.  The tight
subset contributes `A = 1` exactly (`Gtz.tightDirection_rayleigh_identity`) and
`M = 0` exactly (the mixed moment), so both quantities collapse to the two
exchanged atoms alone and the discriminant bound becomes a two-atom gate whose
whole content is one PSD inequality on the plane
(`posDef_exchangeTriple_of_tightAxisGate`).

## Where it hands over

Put the dropped atom ON the plane.  Then the gate loses its dependence on the
inserted atom's axis component entirely and reads

    planar . planar  <  sum over the REMAINING PAIR of (g . planar)^2,

i.e. exactly "the tight subset's remaining pair dominates the plane STRICTLY"
(`posDef_exchangeTriple_of_planarPairStrict`).  That is a rank-two statement about
the compressed companion, and its failure is exactly the companion being a
rank-two TIE.  The companion's data is explicit and is recorded here for the lane
that owns the rank-two tie classification: its atoms are the planar shadows
`planarShadow axis (g_c)`, its weights are the design's ORIGINAL weights `t_c`
unchanged, and its leverages are `|g_c|^2 - (g_c . axis)^2`
(`planarShadow_leverage`).  No reweighting and no rescaling are needed — unlike
the two-pole companion, this one is the plain compression, because the axis is an
eigendirection rather than a tilted pole axis.

`TightAxisTransportResidual` names what is left.  It is phrased positively, with
no `IsTie` anywhere, in the shape of `Gtz.TwoPoleTransportResidual`.

## What the `(5,3)` diamond says about all of this — MEASURED, not claimed here

`Gtz.diamondDesign` is a kernel-checked primitive `(5,3)` TIE — one of two in
the tree, with `Gtz.uniformTieParentDesign` sharing the same dependent-triple
matroid — and the reason `Gtz.not_hingeHoldsAtSize_five_three` holds, so it is
the filter every step of this chain must survive.  Measured in exact rationals, by congruating the graphic
design through its whitener so that domination reads
`sum_{e in C} (cond_e / t_e) v_e v_e^T >= L`:

* the diamond has EIGHT weakly dominating triples and none strictly dominating;
* at every one of them, NO exchange fires — the gate of
  `posDef_exchangeTriple_of_tightAxisGate` is false for all fifteen
  (tight, drop, insert) combinations.  That is the required consistency: a firing
  exchange there would contradict the kernel-checked tie;
* but the compressed tight-axis companion's single-atom rank-two excess
  `2 t l - (1 + t)` IS strictly positive there — exactly `1/20`, at two atoms, at
  every one of the eight tight triples (companion leverages `25/8` against the
  threshold `3`).

So a strictly dominating PAIR of the companion does NOT by itself lift to a
dominating triple: the diamond exhibits the excess firing at a genuine tie.  The
coupling budget, not the planar pair, is the load-bearing half of the transport,
and it is where six-ness must enter.  Consistently, the hypothesis
`hdropOnPlane` of `posDef_exchangeTriple_of_planarPairStrict` fails at the
diamond outright: its five axis masses at a tight triple are
`3/4, 1/8, 1/8, 2, 2`, none of them zero, so no atom of a tight triple lies on
the plane.  That hypothesis is therefore not removable.

Note also the direction the threshold moves: `(1 + t) / (2 t)` is `3` at five
uniform atoms and `7/2` at six, so the single-atom excess test gets HARDER as the
size grows, while the companion's weighted leverage budget stays at
`sum_c t_c (|g_c|^2 - (g_c . axis)^2) = 2`.  A transport resting on that test
alone would be weaker at `(6,3)` than at `(5,3)`, which is the wrong direction.

## The gate's scalar budget, and the diamond sits exactly on its boundary

Whenever the planar excess form is positive definite the gate is a rank-one Schur
complement, so it collapses to a SCALAR budget: writing `N` for the planar
covector `a_d z_b - a_b z_d` and `Delta` for the tight triple's planar excess
form,

    spend(b, d)  :=  N^T Delta^{-1} N / (a_d^2 - a_b^2)   <   1.

Measured exactly at the diamond, over all eight tight triples and all six
exchanges of each — forty-eight in total, every one with positive axis excess,
and `Delta` positive definite at every tight triple — the spend takes exactly
three values: `1` with multiplicity thirty-six, `17/9` with multiplicity eight,
and `2` with multiplicity four.  The MINIMUM IS EXACTLY ONE.

So the diamond does not merely fail the gate, it sits precisely on the gate's
boundary, at equality, on three quarters of its exchanges — the same shape the
two-pole lane found, where its own budget fails only on an equality locus.  Two
consequences.  The gate cannot be weakened by any constant factor, since doing so
would refute the kernel-checked `(5,3)` tie.  And the equality is explained
rather than coincidental: `spend < 1`, `= 1`, `> 1` are exactly the gap of the
exchanged triple being definite, semidefinite-singular, indefinite, and thirty-six
of the diamond's forty-eight exchanges land on another of its eight weakly
dominating triples.

That last observation is also the honest limit of the gate:
`axisSplit_coupling_of_posDef_gap` shows the criterion is an EQUIVALENCE, so the
exchange gate is an exact re-expression of "the exchanged triple dominates
strictly", not a relaxation of it.  The transport is therefore a REGION SPLIT —
it restricts attention from all twenty triples to the exchange neighbours of a
tight one — and not a weakened certificate.  That is exactly the shape the
residual law demands, and it is why no sharper gate exists to look for.

Honest caveat on reach: the region discharged by the gate has not been measured
on branch (i), because no `(6,3)` tie or near-tie is available to measure it at.
No claim is made that the residual is thin.  What is claimed is that the
transport is unconditional, that it survives the `(5,3)` filter, and that its
planar half is a rank-TWO question with explicit data. -/

/-- The component of a vector orthogonal to a unit axis. -/
def planarShadow (axis vec : Fin rank → ℝ) : Fin rank → ℝ :=
  vec - (vec ⬝ᵥ axis) • axis

/-- **THE COMPANION'S LEVERAGE DATA.**  The planar shadow's squared length is the
atom's leverage minus its axis mass.  This is the quantity a rank-two tie
classification is stated in, and the companion's weights are the design's own. -/
theorem planarShadow_leverage {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (vec : Fin rank → ℝ) :
    planarShadow axis vec ⬝ᵥ planarShadow axis vec
      = leverageOf vec - (vec ⬝ᵥ axis) ^ 2 := by
  simp only [planarShadow, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, leverageOf_eq_dotProduct_self]
  rw [dotProduct_comm axis vec, hunit]
  ring

/-- The planar shadow is orthogonal to the axis. -/
theorem planarShadow_dotProduct_axis {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (vec : Fin rank → ℝ) : planarShadow axis vec ⬝ᵥ axis = 0 := by
  rw [planarShadow, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit]
  ring

/-- The gap matrix of a subset is Hermitian. -/
theorem isHermitian_subsetSum_sub_one (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    (subsetSum design selected - (1 : Matrix (Fin rank) (Fin rank) ℝ)).IsHermitian := by
  have hsymmetric : (subsetSum design selected)ᵀ = subsetSum design selected := by
    rw [subsetSum, Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    ext rowIndex colIndex
    simp [atomMatrix, Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]
  refine isHermitian_of_transpose_eq ?_
  rw [Matrix.transpose_sub, Matrix.transpose_one, hsymmetric]

/-- **THE AXIS-SPLIT DOMINATION CRITERION.**  Split every probe along a unit axis
and its orthogonal complement.  The gap form is then a quadratic in the axis
coordinate whose leading coefficient is the axis mass excess and whose
discriminant is the cross moment against the planar excess.  A positive leading
coefficient and a strictly negative discriminant, uniformly over the plane, are
positive definiteness.

No frame, no square root, no spectral theorem — and no domination hypothesis
either: this is the criterion, not a relaxation of it. -/
theorem posDef_gap_of_axisSplit_coupling (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (haxisExcess : 1 < ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2)
    (hcoupling : ∀ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      (∑ atomIndex ∈ selected,
          (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar)) ^ 2
        < ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1)
            * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
              - planar ⬝ᵥ planar)) :
    (subsetSum design selected - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_subsetSum_sub_one design selected, fun probe hprobeNe => ?_⟩
  rw [star_trivial, dominationGap_form]
  set axisCoord := probe ⬝ᵥ axis with haxisCoordDef
  set planarPart := probe - axisCoord • axis with hplanarDef
  have hplanarOrth : planarPart ⬝ᵥ axis = 0 := by
    rw [hplanarDef, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, haxisCoordDef]
    ring
  have hnormSplit : probe ⬝ᵥ probe = planarPart ⬝ᵥ planarPart + axisCoord ^ 2 := by
    rw [hplanarDef]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm axis probe, ← haxisCoordDef, hunit]
    ring
  have hterm : ∀ atomIndex : Fin size,
      (design.atom atomIndex ⬝ᵥ probe) ^ 2
        = (design.atom atomIndex ⬝ᵥ planarPart) ^ 2
          + 2 * axisCoord * ((design.atom atomIndex ⬝ᵥ axis)
              * (design.atom atomIndex ⬝ᵥ planarPart))
          + axisCoord ^ 2 * (design.atom atomIndex ⬝ᵥ axis) ^ 2 := by
    intro atomIndex
    have hlinear : design.atom atomIndex ⬝ᵥ probe
        = design.atom atomIndex ⬝ᵥ planarPart
          + axisCoord * (design.atom atomIndex ⬝ᵥ axis) := by
      rw [hplanarDef, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      ring
    rw [hlinear]
    ring
  rw [Finset.sum_congr rfl (fun atomIndex _ => hterm atomIndex), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnormSplit]
  by_cases hplanarZero : planarPart = 0
  · have haxisNe : axisCoord ≠ 0 := by
      intro hzero
      refine hprobeNe ?_
      have hrecover : probe = planarPart + axisCoord • axis := by rw [hplanarDef]; abel
      rw [hrecover, hplanarZero, hzero, zero_smul, add_zero]
    have haxisSqPos : 0 < axisCoord ^ 2 :=
      lt_of_le_of_ne (sq_nonneg axisCoord) (Ne.symm (pow_ne_zero 2 haxisNe))
    rw [hplanarZero]
    simp only [dotProduct_zero, mul_zero, Finset.sum_const_zero, zero_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, zero_add]
    nlinarith [haxisExcess, haxisSqPos]
  · have hcouplingAt := hcoupling planarPart hplanarOrth hplanarZero
    nlinarith [hcouplingAt, haxisExcess,
      sq_nonneg ((∑ atomIndex ∈ selected,
          (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planarPart))
        + axisCoord * ((∑ atomIndex ∈ selected,
            (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1))]

/-- Summing over a subset with one label exchanged. -/
theorem sum_exchangeSubset (selected : Finset (Fin size)) {dropLabel addLabel : Fin size}
    (hdrop : dropLabel ∈ selected) (haddNot : addLabel ∉ selected) (scoreFn : Fin size → ℝ) :
    ∑ atomIndex ∈ insert addLabel (selected.erase dropLabel), scoreFn atomIndex
      = (∑ atomIndex ∈ selected, scoreFn atomIndex) - scoreFn dropLabel
        + scoreFn addLabel := by
  classical
  rw [Finset.sum_insert (fun hmember => haddNot (Finset.mem_of_mem_erase hmember)),
    Finset.sum_erase_eq_sub hdrop]
  ring

/-- Exchanging one label preserves the cardinality. -/
theorem card_exchangeSubset (selected : Finset (Fin size)) {dropLabel addLabel : Fin size}
    (hdrop : dropLabel ∈ selected) (haddNot : addLabel ∉ selected) :
    (insert addLabel (selected.erase dropLabel)).card = selected.card := by
  classical
  have hpositive : 1 ≤ selected.card := Finset.card_pos.mpr ⟨dropLabel, hdrop⟩
  rw [Finset.card_insert_of_notMem (fun hmember => haddNot (Finset.mem_of_mem_erase hmember)),
    Finset.card_erase_of_mem hdrop]
  omega

/-- **THE TIGHT-AXIS EXCHANGE TRANSPORT.**  Exchange one atom of a weakly
dominating subset for one outside it.  Because the tight axis carries axis mass
exactly one and cross moment exactly zero on the original subset, both quantities
collapse onto the two exchanged atoms, and the axis-split criterion reduces to a
single gate involving only those two atoms and the subset's planar excess.

The gate is a POSITIVE claim about a design: no tie is assumed, and its conclusion
is strict domination, so it discharges an open region rather than relaxing a
certificate. -/
theorem posDef_exchangeTriple_of_tightAxisGate (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0)
    {dropLabel addLabel : Fin size} (hdrop : dropLabel ∈ selected)
    (haddNot : addLabel ∉ selected)
    (hexcess : (design.atom dropLabel ⬝ᵥ axis) ^ 2 < (design.atom addLabel ⬝ᵥ axis) ^ 2)
    (hgate : ∀ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      ((design.atom addLabel ⬝ᵥ axis) * (design.atom dropLabel ⬝ᵥ planar)
          - (design.atom dropLabel ⬝ᵥ axis) * (design.atom addLabel ⬝ᵥ planar)) ^ 2
        < ((design.atom addLabel ⬝ᵥ axis) ^ 2 - (design.atom dropLabel ⬝ᵥ axis) ^ 2)
            * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
              - planar ⬝ᵥ planar)) :
    (subsetSum design (insert addLabel (selected.erase dropLabel)) - 1).PosDef := by
  classical
  refine posDef_gap_of_axisSplit_coupling design _ hunit ?_ ?_
  · rw [sum_exchangeSubset selected hdrop haddNot,
      tightDirection_rayleigh_identity design selected htight, hunit]
    linarith [hexcess]
  · intro planar hplanarOrth hplanarNe
    rw [sum_exchangeSubset selected hdrop haddNot, sum_exchangeSubset selected hdrop haddNot,
      sum_exchangeSubset selected hdrop haddNot,
      tightDirection_rayleigh_identity design selected htight, hunit,
      tightDirection_mixedMoment_eq_zero design hdominates htight hplanarOrth]
    nlinarith [hgate planar hplanarOrth hplanarNe, hexcess]

/-- **THE HANDOVER FORM: the gate is a RANK-TWO statement.**  Drop an atom of the
tight subset that lies ON the plane.  Then the inserted atom's axis component
cancels out of the gate entirely, and what is left is

    `|planar|^2 < sum over the remaining pair of (g . planar)^2`,

that is: the tight subset's REMAINING PAIR dominates the plane STRICTLY.  Any
atom off the plane then completes it to a strictly dominating triple.

So the transport reduces to the compressed companion not being a rank-two tie.
The companion is the plain compression — atoms `planarShadow axis (g_c)`, weights
the design's own `t_c`, leverages `|g_c|^2 - (g_c . axis)^2`
(`planarShadow_leverage`) — no reweighting and no anisotropic rescaling, because
the tight axis is an eigendirection of the subset moment rather than a tilted pole
axis.  That data is what a rank-two tie classification consumes. -/
theorem posDef_exchangeTriple_of_planarPairStrict (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0)
    {dropLabel addLabel : Fin size} (hdrop : dropLabel ∈ selected)
    (haddNot : addLabel ∉ selected)
    (hdropOnPlane : design.atom dropLabel ⬝ᵥ axis = 0)
    (haddOffPlane : design.atom addLabel ⬝ᵥ axis ≠ 0)
    (hpairStrict : ∀ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < ∑ atomIndex ∈ selected.erase dropLabel, (design.atom atomIndex ⬝ᵥ planar) ^ 2) :
    (subsetSum design (insert addLabel (selected.erase dropLabel)) - 1).PosDef := by
  classical
  have haddSqPos : 0 < (design.atom addLabel ⬝ᵥ axis) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 haddOffPlane))
  refine posDef_exchangeTriple_of_tightAxisGate design hdominates hunit htight hdrop haddNot
    (by rw [hdropOnPlane]; simpa using haddSqPos) fun planar hplanarOrth hplanarNe => ?_
  have hpairAt := hpairStrict planar hplanarOrth hplanarNe
  rw [Finset.sum_erase_eq_sub hdrop] at hpairAt
  rw [hdropOnPlane]
  nlinarith [hpairAt, haddSqPos]

/-- **A DESIGN WITH A FIRING EXCHANGE IS NOT A TIE.**  The transport's conclusion
in the campaign's vocabulary. -/
theorem not_isTie_of_tightAxisGate (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hcard : selected.card = rank)
    (hdominates : Dominates design selected)
    {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0)
    {dropLabel addLabel : Fin size} (hdrop : dropLabel ∈ selected)
    (haddNot : addLabel ∉ selected)
    (hexcess : (design.atom dropLabel ⬝ᵥ axis) ^ 2 < (design.atom addLabel ⬝ᵥ axis) ^ 2)
    (hgate : ∀ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      ((design.atom addLabel ⬝ᵥ axis) * (design.atom dropLabel ⬝ᵥ planar)
          - (design.atom dropLabel ⬝ᵥ axis) * (design.atom addLabel ⬝ᵥ planar)) ^ 2
        < ((design.atom addLabel ⬝ᵥ axis) ^ 2 - (design.atom dropLabel ⬝ᵥ axis) ^ 2)
            * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
              - planar ⬝ᵥ planar)) :
    ¬ IsTie design := by
  classical
  intro htie
  refine htie.2 (insert addLabel (selected.erase dropLabel)) ?_
    (posDef_exchangeTriple_of_tightAxisGate design hdominates hunit htight hdrop haddNot
      hexcess hgate)
  rw [card_exchangeSubset selected hdrop haddNot, hcard]

/-! ### The exchange's insert choice is free

The gate has two hypotheses.  The first, an axis-mass excess between the two
exchanged atoms, is DISCHARGED outright: the axis Parseval identity forces an
atom outside the subset to carry axis mass at least the axis norm, while the
subset's own axis masses sum to exactly that norm and so have a small one.  Only
the coupling survives as a hypothesis. -/

/-- **THE INSERT CANDIDATE EXISTS.**  Some atom OUTSIDE a tight subset carries
axis mass at least the axis norm.  The subset's own axis masses sum to exactly the
norm (`Gtz.tightDirection_rayleigh_identity`), so each of them is at most the
norm; if the outside ones were all strictly under it, the weighted Parseval sum
would come in strictly below the norm it must equal. -/
theorem exists_outside_axisMass_ge (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hproper : selectedᶜ.Nonempty)
    {axis : Fin rank → ℝ}
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0) :
    ∃ addLabel ∈ selectedᶜ, axis ⬝ᵥ axis ≤ (design.atom addLabel ⬝ᵥ axis) ^ 2 := by
  classical
  by_contra hnone
  push Not at hnone
  have hinside : ∀ atomIndex ∈ selected,
      (design.atom atomIndex ⬝ᵥ axis) ^ 2 ≤ axis ⬝ᵥ axis := by
    intro atomIndex hmember
    rw [← tightDirection_rayleigh_identity design selected htight]
    exact Finset.single_le_sum (f := fun atomIndex => (design.atom atomIndex ⬝ᵥ axis) ^ 2)
      (fun _ _ => sq_nonneg _) hmember
  have hinsideSum : ∑ atomIndex ∈ selected,
        design.weight atomIndex * (design.atom atomIndex ⬝ᵥ axis) ^ 2
      ≤ ∑ atomIndex ∈ selected, design.weight atomIndex * (axis ⬝ᵥ axis) :=
    Finset.sum_le_sum fun atomIndex hmember =>
      mul_le_mul_of_nonneg_left (hinside atomIndex hmember) (design.weight_pos atomIndex).le
  have houtsideSum : ∑ atomIndex ∈ selectedᶜ,
        design.weight atomIndex * (design.atom atomIndex ⬝ᵥ axis) ^ 2
      < ∑ atomIndex ∈ selectedᶜ, design.weight atomIndex * (axis ⬝ᵥ axis) :=
    Finset.sum_lt_sum_of_nonempty hproper fun atomIndex hmember =>
      mul_lt_mul_of_pos_left (hnone atomIndex hmember) (design.weight_pos atomIndex)
  have hsplitLeft := Finset.sum_add_sum_compl selected
    (fun atomIndex => design.weight atomIndex * (design.atom atomIndex ⬝ᵥ axis) ^ 2)
  have hsplitRight := Finset.sum_add_sum_compl selected
    (fun atomIndex => design.weight atomIndex * (axis ⬝ᵥ axis))
  have huniverse : ∑ atomIndex : Fin size, design.weight atomIndex * (axis ⬝ᵥ axis)
      = axis ⬝ᵥ axis := by
    rw [← Finset.sum_mul, design.weight_sum_one, one_mul]
  have htotal := parseval_weighted_sum_sq design axis
  linarith [hsplitLeft, hsplitRight, huniverse, htotal, hinsideSum, houtsideSum]

/-- **THE DROP CANDIDATE EXISTS.**  Some atom INSIDE a tight subset carries axis
mass at most the axis norm divided by the subset's size: the subset's axis masses
sum to the norm, so the smallest is under the average. -/
theorem exists_inside_axisMass_le (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hnonempty : selected.Nonempty)
    {axis : Fin rank → ℝ}
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0) :
    ∃ dropLabel ∈ selected,
      (selected.card : ℝ) * (design.atom dropLabel ⬝ᵥ axis) ^ 2 ≤ axis ⬝ᵥ axis := by
  classical
  by_contra hnone
  push Not at hnone
  have hstrict : ∑ _atomIndex ∈ selected, (axis ⬝ᵥ axis)
      < ∑ atomIndex ∈ selected,
          (selected.card : ℝ) * (design.atom atomIndex ⬝ᵥ axis) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun atomIndex hmember => hnone atomIndex hmember
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
    tightDirection_rayleigh_identity design selected htight] at hstrict
  linarith

/-- **THE AXIS EXCESS IS FREE.**  Combining the two: at every tight subset of size
at least two with a nonempty complement there is an exchange whose axis excess is
at least `1 - 1/card` of the axis norm — at a triple, two thirds of it.  So the
`hexcess` hypothesis of `posDef_exchangeTriple_of_tightAxisGate` never has to be
assumed, and the transport's only surviving hypothesis is the COUPLING.

Insert candidates number `size - card`, which at a triple is `size - 3`: THREE at
size six against TWO at size five.  That ratio, three halves, is the only place
size enters the exchange so far, and it is not by itself an argument. -/
theorem exists_exchange_axisExcess (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hcardTwo : 2 ≤ selected.card)
    (hproper : selectedᶜ.Nonempty) {axis : Fin rank → ℝ} (haxisNe : axis ≠ 0)
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0) :
    ∃ dropLabel ∈ selected, ∃ addLabel : Fin size, addLabel ∉ selected
      ∧ (design.atom dropLabel ⬝ᵥ axis) ^ 2 < (design.atom addLabel ⬝ᵥ axis) ^ 2
      ∧ (1 - ((selected.card : ℝ))⁻¹) * (axis ⬝ᵥ axis)
          ≤ (design.atom addLabel ⬝ᵥ axis) ^ 2
            - (design.atom dropLabel ⬝ᵥ axis) ^ 2 := by
  classical
  have hnonempty : selected.Nonempty := Finset.card_pos.mp (by omega)
  have hnormPos : 0 < axis ⬝ᵥ axis := dotProduct_self_pos haxisNe
  have hcardPos : (0 : ℝ) < (selected.card : ℝ) := by
    have : (2 : ℝ) ≤ (selected.card : ℝ) := by exact_mod_cast hcardTwo
    linarith
  obtain ⟨dropLabel, hdrop, hdropSmall⟩ :=
    exists_inside_axisMass_le design hnonempty htight
  obtain ⟨addLabel, haddMem, haddBig⟩ :=
    exists_outside_axisMass_ge design hproper htight
  have hdropBound : (design.atom dropLabel ⬝ᵥ axis) ^ 2
      ≤ ((selected.card : ℝ))⁻¹ * (axis ⬝ᵥ axis) := by
    rw [inv_mul_eq_div, le_div_iff₀ hcardPos]
    linarith [hdropSmall]
  have hinvLt : ((selected.card : ℝ))⁻¹ * (axis ⬝ᵥ axis) < axis ⬝ᵥ axis := by
    have hinvSmall : ((selected.card : ℝ))⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      right
      have : (2 : ℝ) ≤ (selected.card : ℝ) := by exact_mod_cast hcardTwo
      linarith
    nlinarith [hnormPos, hinvSmall]
  exact ⟨dropLabel, hdrop, addLabel, Finset.mem_compl.mp haddMem, by linarith,
    by linarith⟩

/-! ### The criterion is an equivalence, so the gate is not a relaxation -/

/-- The gap form along an axis split, as an explicit quadratic in the axis
coordinate. -/
theorem gapForm_axisSplit (design : WeightedDesign size rank) (selected : Finset (Fin size))
    {axis planar : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1) (horth : planar ⬝ᵥ axis = 0)
    (coeff : ℝ) :
    (planar + coeff • axis) ⬝ᵥ ((subsetSum design selected - 1) *ᵥ (planar + coeff • axis))
      = ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2) - planar ⬝ᵥ planar)
        + 2 * coeff * (∑ atomIndex ∈ selected,
            (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar))
        + coeff ^ 2
            * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1) := by
  rw [dominationGap_form]
  have hnorm : (planar + coeff • axis) ⬝ᵥ (planar + coeff • axis)
      = planar ⬝ᵥ planar + coeff ^ 2 := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hunit, dotProduct_comm axis planar, horth]
    ring
  have hterm : ∀ atomIndex : Fin size,
      (design.atom atomIndex ⬝ᵥ (planar + coeff • axis)) ^ 2
        = (design.atom atomIndex ⬝ᵥ planar) ^ 2
          + 2 * coeff * ((design.atom atomIndex ⬝ᵥ axis)
              * (design.atom atomIndex ⬝ᵥ planar))
          + coeff ^ 2 * (design.atom atomIndex ⬝ᵥ axis) ^ 2 := by
    intro atomIndex
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun atomIndex _ => hterm atomIndex), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnorm]
  ring

/-- **THE AXIS-SPLIT CRITERION IS NECESSARY TOO.**  Testing the gap at the axis
gives the mass excess, and testing it at the minimising axis coordinate gives the
coupling bound.  So `posDef_gap_of_axisSplit_coupling` is an EQUIVALENCE, and the
exchange gate is an exact re-expression of "the exchanged subset dominates
strictly" rather than a relaxation of it.  That is why no sharper version of the
gate exists, and why the residual below is a region split rather than a weakened
certificate. -/
theorem axisSplit_coupling_of_posDef_gap (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    1 < (∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2)
      ∧ ∀ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
          (∑ atomIndex ∈ selected,
              (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar)) ^ 2
            < ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1)
                * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
                  - planar ⬝ᵥ planar) := by
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2
  have haxisNe : axis ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    exact one_ne_zero hunit.symm
  have hexcess : 1 < ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2 := by
    have hat := hform haxisNe
    rw [star_trivial, dominationGap_form, hunit] at hat
    linarith
  refine ⟨hexcess, fun planar horth hplanarNe => ?_⟩
  set axisMass := ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2
    with haxisMassDef
  set crossMoment := ∑ atomIndex ∈ selected,
    (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar) with hcrossDef
  set coeff := -(crossMoment / (axisMass - 1)) with hcoeffDef
  have hprobeNe : planar + coeff • axis ≠ 0 := by
    intro hzero
    have hpair := congrArg (fun vec => vec ⬝ᵥ axis) hzero
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at hpair
    rw [horth, hunit] at hpair
    have hcoeffZero : coeff = 0 := by linarith
    rw [hcoeffZero, zero_smul, add_zero] at hzero
    exact hplanarNe hzero
  have hdenom : (0 : ℝ) < axisMass - 1 := by rw [haxisMassDef]; linarith
  have hdenomNe : axisMass - 1 ≠ 0 := ne_of_gt hdenom
  have hat := hform hprobeNe
  rw [star_trivial] at hat
  have hrewrite : (planar + coeff • axis)
        ⬝ᵥ ((subsetSum design selected - 1) *ᵥ (planar + coeff • axis))
      = ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
          - planar ⬝ᵥ planar) - crossMoment ^ 2 / (axisMass - 1) := by
    rw [gapForm_axisSplit design selected hunit horth coeff, ← haxisMassDef, ← hcrossDef,
      hcoeffDef]
    field_simp
    ring
  rw [hrewrite, sub_pos, div_lt_iff₀ hdenom] at hat
  linarith [hat]

/-- **THE RESIDUAL OF BRANCH (i) AFTER THE TRANSPORT.**  Phrased positively, in
the shape of `Gtz.TwoPoleTransportResidual`: no `IsTie` appears, the discharged
region is excluded as a negative hypothesis, and the conclusion is the existence
of a strictly dominating triple.

The excluded region is every tight configuration at which SOME exchange fires;
`posDef_exchangeTriple_of_tightAxisGate` discharges it unconditionally, and
`posDef_exchangeTriple_of_planarPairStrict` identifies its rank-two content.

READ IT AS THE PROP, NOT AS A SENTENCE ABOUT TIES.  Paraphrasing it as "at a tie
every exchange spend is at least one" would be a TAUTOLOGY — a tie has no
strictly dominating triple, so by `axisSplit_coupling_of_posDef_gap` every spend
is at least one by definition.  What the Prop actually asks is the contrapositive
direction: that a tight configuration at which no exchange fires still has a
strictly dominating triple SOMEWHERE among the twenty, not merely among the nine
exchange neighbours.  That is a real claim, and
`not_tightAxisTransportResidual_five` shows it is FALSE at size five, so it is
not size-generic and any proof of it must use the sixth atom.

No claim is made about how large the discharged region is on branch (i): there is
no `(6,3)` stress-free tie or near-tie available to measure it against.  The two
`(6,3)` ties the tree owns — the split-tetrahedron family — carry a duplicated
atom, hence a stress, and so lie outside branch (i) entirely. -/
def TightAxisTransportResidual (size : ℕ) : Prop :=
  ∀ (design : WeightedDesign size 3) (selected : Finset (Fin size)) (axis : Fin 3 → ℝ),
    selected.card = 3 → Dominates design selected → axis ⬝ᵥ axis = 1 →
    axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0 →
    (∀ dropLabel ∈ selected, ∀ addLabel : Fin size, addLabel ∉ selected →
      (design.atom dropLabel ⬝ᵥ axis) ^ 2 < (design.atom addLabel ⬝ᵥ axis) ^ 2 →
      ¬ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
          ((design.atom addLabel ⬝ᵥ axis) * (design.atom dropLabel ⬝ᵥ planar)
              - (design.atom dropLabel ⬝ᵥ axis) * (design.atom addLabel ⬝ᵥ planar)) ^ 2
            < ((design.atom addLabel ⬝ᵥ axis) ^ 2 - (design.atom dropLabel ⬝ᵥ axis) ^ 2)
                * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
                  - planar ⬝ᵥ planar)) →
    ∃ dominatingTriple : Finset (Fin size), dominatingTriple.card = 3
      ∧ (subsetSum design dominatingTriple - 1).PosDef

/-- **AT EVERY `(6,3)` TIE THE TRANSPORT IS SET UP AND ONLY THE COUPLING IS
MISSING.**  The tie supplies a tight triple and a tight axis, and the axis
Parseval identity then supplies an exchange whose axis excess is at least two
thirds.  So `posDef_exchangeTriple_of_tightAxisGate` is applicable at every tie
with its first hypothesis already met; the sole remaining obstruction is the
COUPLING, uniformly over the plane.  That is branch (i)'s residual in its sharpest
form, and it is where size has to enter: a triple leaves `size - 3` insert
candidates, THREE at size six against TWO at size five. -/
theorem sixThree_exists_exchange_axisExcess_of_isTie (design : WeightedDesign 6 3)
    (htie : IsTie design) :
    ∃ (selected : Finset (Fin 6)) (axis : Fin 3 → ℝ),
      selected.card = 3 ∧ Dominates design selected ∧ axis ⬝ᵥ axis = 1
        ∧ axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0
        ∧ ∃ dropLabel ∈ selected, ∃ addLabel : Fin 6, addLabel ∉ selected
            ∧ (design.atom dropLabel ⬝ᵥ axis) ^ 2 < (design.atom addLabel ⬝ᵥ axis) ^ 2
            ∧ (2 : ℝ) / 3 ≤ (design.atom addLabel ⬝ᵥ axis) ^ 2
                - (design.atom dropLabel ⬝ᵥ axis) ^ 2 := by
  classical
  obtain ⟨selected, axis, hcard, hdominates, haxisNe, htight⟩ := isTie_yields_tightDirection htie
  have hnormPos : 0 < axis ⬝ᵥ axis := dotProduct_self_pos haxisNe
  have hsqrtPos : 0 < Real.sqrt (axis ⬝ᵥ axis) := Real.sqrt_pos.mpr hnormPos
  set unitAxis := (Real.sqrt (axis ⬝ᵥ axis))⁻¹ • axis with hunitAxisDef
  have hunit : unitAxis ⬝ᵥ unitAxis = 1 := by
    rw [hunitAxisDef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hnormPos.le]
    exact inv_mul_cancel₀ hnormPos.ne'
  have hunitNe : unitAxis ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    exact one_ne_zero hunit.symm
  have htightUnit : unitAxis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ unitAxis) = 0 := by
    rw [hunitAxisDef, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, htight]
    ring
  have hproper : selectedᶜ.Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    omega
  obtain ⟨dropLabel, hdrop, addLabel, haddNot, hstrict, hquantitative⟩ :=
    exists_exchange_axisExcess design (by omega) hproper hunitNe htightUnit
  refine ⟨selected, unitAxis, hcard, hdominates, hunit, htightUnit, dropLabel, hdrop,
    addLabel, haddNot, hstrict, ?_⟩
  rw [hcard, hunit] at hquantitative
  norm_num at hquantitative
  linarith [hquantitative]

/-- **NO TIE SURVIVES THE TRANSPORT PLUS ITS RESIDUAL.**  Either some exchange
fires — and then the transport returns a strictly dominating triple outright — or
the configuration falls into the residual, which returns one by hypothesis.  A tie
admits neither.  Stated at general size precisely so that
`not_tightAxisTransportResidual_five` can read it backwards. -/
theorem not_isTie_of_transportResidual {size : ℕ}
    (hresidual : TightAxisTransportResidual size)
    (design : WeightedDesign size 3) : ¬ IsTie design := by
  classical
  intro htie
  obtain ⟨selected, axis, hcard, hdominates, haxisNe, htight⟩ := isTie_yields_tightDirection htie
  have hnormPos : 0 < axis ⬝ᵥ axis := dotProduct_self_pos haxisNe
  set scale := (Real.sqrt (axis ⬝ᵥ axis))⁻¹ with hscaleDef
  have hsqrtPos : 0 < Real.sqrt (axis ⬝ᵥ axis) := Real.sqrt_pos.mpr hnormPos
  set unitAxis := scale • axis with hunitAxisDef
  have hunit : unitAxis ⬝ᵥ unitAxis = 1 := by
    rw [hunitAxisDef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hscaleDef,
      ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hnormPos.le]
    exact inv_mul_cancel₀ hnormPos.ne'
  have htightUnit : unitAxis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ unitAxis) = 0 := by
    rw [hunitAxisDef, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, htight]
    ring
  obtain ⟨dominatingTriple, hdominatingCard, hposDef⟩ :=
    hresidual design selected unitAxis hcard hdominates hunit htightUnit
      (fun dropLabel hdrop addLabel haddNot hexcess hgate =>
        htie.2 (insert addLabel (selected.erase dropLabel))
          (by rw [card_exchangeSubset selected hdrop haddNot, hcard])
          (posDef_exchangeTriple_of_tightAxisGate design hdominates hunit htightUnit hdrop
            haddNot hexcess hgate))
  exact htie.2 dominatingTriple hdominatingCard hposDef

/-- The `(6,3)` instance, the one branch (i) consumes. -/
theorem sixThree_not_isTie_of_transportResidual (hresidual : TightAxisTransportResidual 6)
    (design : WeightedDesign 6 3) : ¬ IsTie design :=
  not_isTie_of_transportResidual hresidual design

/-- **THE RESIDUAL IS FALSE AT SIZE FIVE, AND THAT IS WHY SIX IS LOAD-BEARING.**
`Gtz.diamondDesign` is a `(5,3)` tie, so it has a weakly dominating triple with a
tight axis; every exchange gate fails there for free, because a firing one would
hand back a strictly dominating triple by
`posDef_exchangeTriple_of_tightAxisGate`; and there is no strictly dominating
triple to conclude with.  So `TightAxisTransportResidual 5` is refuted outright.

This is the honest statement of what the residual asks: it is NOT a size-generic
claim that happens to be open at six, it is a claim that is FALSE at five, so any
proof of it must notice that there are six atoms.  The transport itself is
size-generic and correct at both sizes — it is the residual, the part still
unproved, that carries the whole burden of size. -/
theorem not_tightAxisTransportResidual_five : ¬ TightAxisTransportResidual 5 :=
  fun hresidual => not_isTie_of_transportResidual hresidual diamondDesign diamondDesign_isTie

/-! ## Part 7: the weakly dominating set, and the closure lever

The last unexplored lever was the exchange graph on triples: at the diamond the
weakly dominating set is almost everything and the spend-one exchanges stay
inside it, so one might hope a counting or connectivity argument on that graph
becomes unsatisfiable at twenty triples with degree nine.  It does not, and the
reason is a theorem rather than a measurement.

`axisSplit_coupling_of_posDef_gap` makes the criterion an equivalence, so
`spend < 1`, `= 1`, `> 1` are exactly the exchanged gap being definite,
semidefinite-singular, indefinite.  At a TIE no triple is definite, so a
spend-one exchange is precisely one that lands on another weakly dominating
triple.  CLOSURE OF THE WEAKLY DOMINATING SET UNDER SPEND-ONE EXCHANGES IS
THEREFORE A TAUTOLOGY, at every size, and carries no information at all.  Measured
to be safe: zero mismatches in 48 exchanges at the diamond and 48 more at the
`(6,3)` split tetrahedron.

What the same measurement DID turn up is a regularity across both known tie
families, at both sizes.  Half of it is the theorem below — a weakly dominating
subset has an invertible moment matrix, so it is independent.  The other half is
only MEASURED, and is stated here as a regularity and not as a claim: at both
known ties the converse also holds, so the weakly dominating set is EXACTLY the
independent set.

* `Gtz.diamondDesign`, `(5,3)`: 8 of 10 triples weakly dominate, and they are
  exactly the 8 bases; the 2 that fail are the two triangles.
* `Gtz.splitTetraDesign`, `(6,3)`, over its whole two-parameter family: 12 of 20
  triples weakly dominate, and they are exactly the 12 independent ones; the 8
  that fail all contain a duplicated atom.  Every one of its 48 exchanges with
  positive axis excess has spend exactly `1`.

So the boundary phenomenon is not special to `(5,3)`: minimum spend exactly one is
what a tie IS, at both sizes.  If the measured converse were a theorem, then a
branch-(i) tie in general position would have all twenty triples weakly
dominating, hence `sum_C det (S_C - 1) = 0`, which the layer-sum identity turns
into one explicit polynomial condition on the six directions.  That is the
sharpest constraint this lane can currently name, and it rests on an unproved
regularity, so it is recorded as a lead and not used. -/

/-- **A WEAKLY DOMINATING SUBSET IS INDEPENDENT.**  Its moment matrix dominates
the identity, so it is positive definite and in particular invertible: domination
can only happen at a basis.  This is the proved half of the regularity above. -/
theorem posDef_subsetSum_of_dominates (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected) :
    (subsetSum design selected).PosDef := by
  have hgapForm := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2
  have hsymmetric : (subsetSum design selected)ᵀ = subsetSum design selected := by
    rw [subsetSum, Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    ext rowIndex colIndex
    simp [atomMatrix, Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymmetric, fun probe hprobeNe => ?_⟩
  have hgapAt := hgapForm probe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec] at hgapAt
  have hnormPos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
  rw [star_trivial]
  linarith

/-- The determinant reading: a weakly dominating subset has strictly positive
moment determinant, so a subset with vanishing Gram determinant never dominates. -/
theorem det_subsetSum_pos_of_dominates (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected) :
    0 < (subsetSum design selected).det :=
  (posDef_subsetSum_of_dominates design hdominates).det_pos

end Gtz

import Gtz.Quantitative.CauchyBinetLayerSum
import Gtz.Quantitative.ProjectionBasisCoordinates
import Gtz.Reduction.ExchangeInvariant
import Gtz.Design.StressFreeStratum
import Gtz.Design.RhoNormalForm
import Gtz.Design.ConditionalLineHinge
import Gtz.Design.AllHeavyNegativeAggregate
import Gtz.Ties.NonUniformLeverageTie
import Gtz.Design.BalancedNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The gap determinant in projection-DPP basis coordinates

`Gtz.shadowDeterminant` is the projection-DPP mass `p_B = (∏_{i ∈ B} t_i) · [B]²` and
`Gtz.sum_shadowDeterminant_eq_one` says the twenty masses of a `(6,3)` design are a
probability distribution on bases.  What the tree did NOT have is the identity that makes
that coordinate compute the objects the covering problem is about:

    `det (S_T − 1) = Σ_{|B| = rank} p_B · ∏_{i ∈ B} λ_i^T` ,
    `λ_i^T = (1_T(i) − t_i) / t_i` ,

equivalently, weight-free,

    `det (S_T − 1) = Σ_{|B| = rank} (∏_{i ∈ B} (1_T(i) − t_i)) · [B]²` .

Both hold at EVERY `size`, EVERY `rank`, and EVERY subset `T` — no cardinality hypothesis
on `T`, no design hypothesis beyond Parseval, no distinctness.

## The one genuinely missing ingredient

`Gtz.sum_det_principalMinors_mul_transpose_comm` is Cauchy–Binet at every level for the
pair `A Aᵀ` / `Aᵀ A`.  The gap needs the same flip for `M N` / `N M` at INDEPENDENT
rectangular factors, because the coefficient diagonal sits between the two copies of the
frame.  `principalMinorTotal_mul_comm` supplies it; the proof is the same Weinstein–Aronszajn
coefficient extraction, and the transpose form is the special case `N = Mᵀ`.

With it, `det_transpose_mul_diagonal_mul` is the general statement — for any rectangular
`A` and any coefficient vector `c`,

    `det (Aᵀ diag(c) A) = Σ_{|B| = card col} (∏_{i ∈ B} c_i) · det (A Aᵀ)[B]` ,

and the two design forms are the two readings `A = scaledAtomRows` (whose Gram minors ARE
the shadow determinants, by definition) and `A = atomRowFrame` (whose Gram minors are the
bare squared brackets).  `Gtz.gap_eq_sum_indicator_sub_weight_smul` supplies the
coefficient vector.

## The refusal dictionary

The three centered inclusion moments of `Gtz.Quantitative.ProjectionBasisCoordinates` are
the three scalars of the campaign's refusal alphabet, each times a POSITIVE weight product:

    `centeredBasisFirst a       = t_a · gapExcessOf a`
    `centeredBasisPair a b      = t_a t_b · pairGapExcessOf a b`
    `centeredBasisTriple a b c  = t_a t_b t_c · discriminantTie a b c`

So the moment system and the scalar refusal system are the same system in different units,
`IsLivePair` is exactly "the first two moments are positive", and every sign statement
transfers in both directions with no loss.  That is what makes
`exists_posDef_cardThree_iff_centeredBasisMoments` and
`freePairMomentRefusal_iff_freePairMinorRefusal` iffs rather than one-way bridges.

## HONESTY

Nothing here is a criterion and nothing here can fire on a tie: every statement is an
identity or an iff between two presentations of one predicate.  In particular the
expansion does NOT decide domination — `Gtz.nonUniformLeverageTieDesign` has a triple of
gap determinant `+3` at inertia `(1, 0, 2)`, so a positive value of the right-hand side is
not positive definiteness.  The determinant is one of the three Sylvester legs and the
other two are `centeredBasisFirst` and `centeredBasisPair`.
-/

namespace Gtz

open Matrix

/-! ## Cauchy–Binet at every level, for independent rectangular factors -/

section RectangularFlip

variable {baseRing : Type*} [CommRing baseRing]
variable {rowIndex colIndex : Type*} [Fintype rowIndex] [DecidableEq rowIndex]
  [Fintype colIndex] [DecidableEq colIndex]

/-- **THE PRINCIPAL-MINOR TOTAL IS INVARIANT UNDER SWAPPING TWO RECTANGULAR FACTORS.**
For `M : rowIndex × colIndex` and `N : colIndex × rowIndex` the two square products have
the same total of `level`-sized principal minors, at every level:

    `Σ_{|I| = level} det (M N)[I]  =  Σ_{|J| = level} det (N M)[J]` .

`Gtz.sum_det_principalMinors_mul_transpose_comm` is the case `N = Mᵀ`.  The general case
is what a coefficient diagonal between two copies of a frame needs, and the proof is the
same: both totals are the `level`-th coefficient of a determinant over `baseRing[X]`, and
the two determinants agree by Weinstein–Aronszajn. -/
theorem principalMinorTotal_mul_comm (leftFactor : Matrix rowIndex colIndex baseRing)
    (rightFactor : Matrix colIndex rowIndex baseRing) (level : ℕ) :
    principalMinorTotal (leftFactor * rightFactor) level
      = principalMinorTotal (rightFactor * leftFactor) level := by
  have hleftMap : (leftFactor * rightFactor).map Polynomial.C
      = leftFactor.map Polynomial.C * rightFactor.map Polynomial.C :=
    Matrix.map_mul (f := (Polynomial.C : baseRing →+* Polynomial baseRing))
  have hrightMap : (rightFactor * leftFactor).map Polynomial.C
      = rightFactor.map Polynomial.C * leftFactor.map Polynomial.C :=
    Matrix.map_mul (f := (Polynomial.C : baseRing →+* Polynomial baseRing))
  have hgenerating :
      Matrix.det (1 + (Polynomial.X : Polynomial baseRing) •
          (leftFactor * rightFactor).map Polynomial.C)
        = Matrix.det (1 + (Polynomial.X : Polynomial baseRing) •
            (rightFactor * leftFactor).map Polynomial.C) := by
    rw [hleftMap, hrightMap, ← Matrix.smul_mul, ← Matrix.mul_smul]
    exact Matrix.det_one_add_mul_comm
      ((Polynomial.X : Polynomial baseRing) • leftFactor.map Polynomial.C)
      (rightFactor.map Polynomial.C)
  rw [principalMinorTotal_eq_coeff, principalMinorTotal_eq_coeff, hgenerating]

end RectangularFlip

/-! ## A diagonal factor pulls a product out of every principal minor -/

section DiagonalMinor

variable {baseRing : Type*} [CommRing baseRing]
variable {indexType : Type*} [Fintype indexType] [DecidableEq indexType]

/-- Left-multiplying by a diagonal scales each principal minor by the product of the
diagonal over the chosen index set. -/
theorem det_submatrix_diagonal_mul (coeff : indexType → baseRing)
    (form : Matrix indexType indexType baseRing) (chosen : Finset indexType) :
    ((Matrix.diagonal coeff * form).submatrix
        (Subtype.val : { index // index ∈ chosen } → indexType)
        (Subtype.val : { index // index ∈ chosen } → indexType)).det
      = (∏ index ∈ chosen, coeff index)
        * (form.submatrix
            (Subtype.val : { index // index ∈ chosen } → indexType)
            (Subtype.val : { index // index ∈ chosen } → indexType)).det := by
  have hfactor : (Matrix.diagonal coeff * form).submatrix
        (Subtype.val : { index // index ∈ chosen } → indexType)
        (Subtype.val : { index // index ∈ chosen } → indexType)
      = Matrix.diagonal (fun slot : { index // index ∈ chosen } => coeff slot.val)
        * form.submatrix
            (Subtype.val : { index // index ∈ chosen } → indexType)
            (Subtype.val : { index // index ∈ chosen } → indexType) := by
    ext leftSlot rightSlot
    rw [Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.diagonal_mul,
      Matrix.submatrix_apply]
  rw [hfactor, Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  exact Finset.prod_coe_sort chosen coeff

end DiagonalMinor

/-! ## The coefficient-weighted determinant of a rectangular frame -/

section WeightedFrameDeterminant

variable {baseRing : Type*} [CommRing baseRing]
variable {rowIndex colIndex : Type*} [Fintype rowIndex] [DecidableEq rowIndex]
  [Fintype colIndex] [DecidableEq colIndex]

/-- **CAUCHY–BINET WITH COEFFICIENTS.**  For a rectangular `A` and any coefficient vector
`c` indexed by the rows,

    `det (Aᵀ diag(c) A) = Σ_{|B| = card col} (∏_{i ∈ B} c_i) · det (A Aᵀ)[B]` .

At `c ≡ 1` this is classical Cauchy–Binet.  The coefficients are arbitrary ring elements —
no positivity, no square root, no invertibility. -/
theorem det_transpose_mul_diagonal_mul (rect : Matrix rowIndex colIndex baseRing)
    (coeff : rowIndex → baseRing) :
    (rectᵀ * Matrix.diagonal coeff * rect).det
      = ∑ chosen ∈ (Finset.univ : Finset rowIndex).powersetCard (Fintype.card colIndex),
          (∏ index ∈ chosen, coeff index)
            * ((rect * rectᵀ).submatrix
                (Subtype.val : { index // index ∈ chosen } → rowIndex)
                (Subtype.val : { index // index ∈ chosen } → rowIndex)).det := by
  have hasProduct : (rectᵀ * Matrix.diagonal coeff * rect).det
      = principalMinorTotal (rectᵀ * (Matrix.diagonal coeff * rect))
          (Fintype.card colIndex) := by
    rw [principalMinorTotal_card, Matrix.mul_assoc]
  rw [hasProduct, principalMinorTotal_mul_comm, Matrix.mul_assoc, principalMinorTotal]
  exact Finset.sum_congr rfl fun chosen _ =>
    det_submatrix_diagonal_mul coeff (rect * rectᵀ) chosen

/-- A coefficient-weighted frame product is the coefficient combination of the row atoms:
`Aᵀ diag(c) A = Σ_y c_y · (A_y) (A_y)ᵀ`. -/
theorem transpose_mul_diagonal_mul_eq_sum_atomMatrix {size rank : ℕ}
    (rect : Matrix (Fin size) (Fin rank) ℝ) (coeff : Fin size → ℝ) :
    rectᵀ * Matrix.diagonal coeff * rect
      = ∑ atomIndex, coeff atomIndex • atomMatrix (rect atomIndex) := by
  rw [Matrix.mul_assoc]
  ext rowCoord colCoord
  rw [Matrix.mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [Matrix.transpose_apply, Matrix.diagonal_mul, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul]
  ring

end WeightedFrameDeterminant

/-! ## The two design readings -/

section DesignExpansion

variable {size rank : ℕ}

/-- **The inclusion ratio** `λ_i^T = (1_T(i) − t_i)/t_i`: the centered basis-inclusion
indicator of the projection-DPP measure, divided by the weight.  It is `(1 − t_i)/t_i`
inside the subset and `−1` outside it. -/
noncomputable def inclusionRatio (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (atomIndex : Fin size) : ℝ :=
  ((if atomIndex ∈ selected then (1 : ℝ) else 0) - design.weight atomIndex)
    / design.weight atomIndex

theorem inclusionRatio_of_mem (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} {atomIndex : Fin size} (hmem : atomIndex ∈ selected) :
    inclusionRatio design selected atomIndex
      = (1 - design.weight atomIndex) / design.weight atomIndex := by
  rw [inclusionRatio, if_pos hmem]

theorem inclusionRatio_of_notMem (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} {atomIndex : Fin size} (hnotMem : atomIndex ∉ selected) :
    inclusionRatio design selected atomIndex = -1 := by
  rw [inclusionRatio, if_neg hnotMem, zero_sub,
    neg_div, div_self (design.weight_pos atomIndex).ne']

/-- Scaling by the inclusion ratio recovers the centered coefficient. -/
theorem weight_mul_inclusionRatio (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (atomIndex : Fin size) :
    inclusionRatio design selected atomIndex * design.weight atomIndex
      = (if atomIndex ∈ selected then (1 : ℝ) else 0) - design.weight atomIndex := by
  rw [inclusionRatio, div_mul_cancel₀ _ (design.weight_pos atomIndex).ne']

/-- The scaled frame with the inclusion-ratio diagonal between its two copies is exactly
the gap of the subset. -/
theorem transpose_mul_diagonal_inclusionRatio_mul_scaledAtomRows
    (design : WeightedDesign size rank) (selected : Finset (Fin size)) :
    (scaledAtomRows design)ᵀ * Matrix.diagonal (inclusionRatio design selected)
        * scaledAtomRows design
      = subsetSum design selected - 1 := by
  rw [transpose_mul_diagonal_mul_eq_sum_atomMatrix,
    gap_eq_sum_indicator_sub_weight_smul design selected]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [scaledAtomRows_row, atomMatrix_smul,
    Real.sq_sqrt (design.weight_pos atomIndex).le, smul_smul,
    weight_mul_inclusionRatio]

/-- **THE GAP EXPANSION IN PROJECTION-DPP BASIS COORDINATES.**  For every subset `T` of
every weighted design, at every size and every rank,

    `det (S_T − 1) = Σ_{|B| = rank} p_B · ∏_{i ∈ B} λ_i^T` ,

where `p_B = Gtz.shadowDeterminant` is the basis mass and `λ_i^T = (1_T(i) − t_i)/t_i` is
the inclusion ratio.  The sum is over ALL `rank`-subsets — the twenty bases at `(6,3)` —
and `T` is arbitrary: no cardinality hypothesis, no domination, no tightness.

Together with `Gtz.sum_shadowDeterminant_eq_one` this says the gap determinant is the
`p`-expectation of `∏_{i ∈ B} λ_i^T`, so every candidate determinant of the covering
problem is one linear functional of the twenty masses. -/
theorem det_subsetSum_sub_one_eq_sum_shadowDeterminant (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    (subsetSum design selected - 1).det
      = ∑ basis ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
          shadowDeterminant design basis
            * ∏ atomIndex ∈ basis, inclusionRatio design selected atomIndex := by
  rw [← transpose_mul_diagonal_inclusionRatio_mul_scaledAtomRows design selected,
    det_transpose_mul_diagonal_mul, Fintype.card_fin]
  refine Finset.sum_congr rfl fun basis _ => ?_
  rw [shadowDeterminant, projectionOfDesign, mul_comm]

/-- **THE GAP EXPANSION IN BARE SQUARED BRACKETS**, the weight-free reading:

    `det (S_T − 1) = Σ_{|B| = rank} (∏_{i ∈ B} (1_T(i) − t_i)) · [B]²` ,

with `[B]² = det (A Aᵀ)[B]` the squared bracket of the unweighted atom frame.  Same route,
the unscaled frame instead of the scaled one. -/
theorem det_subsetSum_sub_one_eq_sum_atomGramMinor (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    (subsetSum design selected - 1).det
      = ∑ basis ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
          (∏ atomIndex ∈ basis,
              ((if atomIndex ∈ selected then (1 : ℝ) else 0) - design.weight atomIndex))
            * ((atomGramMatrix design).submatrix
                (Subtype.val : { index // index ∈ basis } → Fin size)
                (Subtype.val : { index // index ∈ basis } → Fin size)).det := by
  have hframe : (atomRowFrame design)ᵀ
        * Matrix.diagonal
            (fun atomIndex =>
              (if atomIndex ∈ selected then (1 : ℝ) else 0) - design.weight atomIndex)
        * atomRowFrame design
      = subsetSum design selected - 1 := by
    rw [transpose_mul_diagonal_mul_eq_sum_atomMatrix,
      gap_eq_sum_indicator_sub_weight_smul design selected]
    rfl
  rw [← hframe, det_transpose_mul_diagonal_mul, Fintype.card_fin]
  refine Finset.sum_congr rfl fun basis _ => ?_
  rw [atomGramMatrix]

/-- **THE BRIDGE BETWEEN THE TWO READINGS.**  The projection-DPP mass is the weight
product times the squared bracket:  `p_B = (∏_{i ∈ B} t_i) · [B]²`.  The tree states this
along an injective enumeration (`Gtz.shadowDeterminant_eq_weightProduct_mul_detSq`); this
is the subset-indexed form, with no cardinality hypothesis. -/
theorem shadowDeterminant_eq_weightProduct_mul_atomGramMinor
    (design : WeightedDesign size rank) (basis : Finset (Fin size)) :
    shadowDeterminant design basis
      = (∏ atomIndex ∈ basis, design.weight atomIndex)
        * ((atomGramMatrix design).submatrix
            (Subtype.val : { index // index ∈ basis } → Fin size)
            (Subtype.val : { index // index ∈ basis } → Fin size)).det := by
  have hsplit : (projectionOfDesign design).submatrix
        (Subtype.val : { index // index ∈ basis } → Fin size)
        (Subtype.val : { index // index ∈ basis } → Fin size)
      = Matrix.diagonal (fun slot : { index // index ∈ basis } =>
            Real.sqrt (design.weight slot.val))
          * ((atomGramMatrix design).submatrix
              (Subtype.val : { index // index ∈ basis } → Fin size)
              (Subtype.val : { index // index ∈ basis } → Fin size))
          * Matrix.diagonal (fun slot : { index // index ∈ basis } =>
              Real.sqrt (design.weight slot.val)) := by
    ext leftSlot rightSlot
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply,
      Matrix.submatrix_apply, projectionOfDesign_apply, atomGramMatrix_apply]
    ring
  have hproduct : (∏ slot : { index // index ∈ basis }, Real.sqrt (design.weight slot.val))
        * ∏ slot : { index // index ∈ basis }, Real.sqrt (design.weight slot.val)
      = ∏ atomIndex ∈ basis, design.weight atomIndex := by
    rw [← Finset.prod_mul_distrib,
      Finset.prod_congr rfl fun slot _ =>
        Real.mul_self_sqrt (design.weight_pos slot.val).le]
    exact Finset.prod_coe_sort basis design.weight
  rw [shadowDeterminant, hsplit, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    mul_right_comm, hproduct]

end DesignExpansion

/-! ## The refusal dictionary: the centered moments ARE the scalar alphabet -/

section RefusalDictionary

variable {size : ℕ}

/-- Scaling by a strictly positive number preserves and reflects positivity. -/
theorem pos_scaled_iff_pos {scale value : ℝ} (hscale : 0 < scale) :
    0 < scale * value ↔ 0 < value := by
  rw [mul_pos_iff]
  constructor
  · rintro (⟨-, hvalue⟩ | ⟨hnegative, -⟩)
    · exact hvalue
    · exact absurd hnegative (not_lt.mpr hscale.le)
  · intro hvalue
    exact Or.inl ⟨hscale, hvalue⟩

/-- **THE FIRST LEG OF THE DICTIONARY.**  The first centered inclusion moment is the
atom's gap excess, scaled by its own weight. -/
theorem centeredBasisFirst_eq_weight_mul_gapExcess (design : WeightedDesign size 3)
    (first : Fin size) :
    centeredBasisFirst design first = design.weight first * gapExcessOf design first := by
  rw [centeredBasisFirst, projectionOfDesign_diagonal, gapExcessOf]
  ring

/-- **THE SECOND LEG.**  The second centered inclusion moment is Sylvester's two-by-two
leading minor of `Gram − 1` at the pair, scaled by the two weights. -/
theorem centeredBasisPair_eq_weightProduct_mul_pairGapExcess (design : WeightedDesign size 3)
    (first second : Fin size) :
    centeredBasisPair design first second
      = design.weight first * design.weight second * pairGapExcessOf design first second := by
  rw [centeredBasisPair, projectionPairMass_eq_weight_mul_crossAxisBudget,
    projectionOfDesign_diagonal, projectionOfDesign_diagonal, crossAxisBudget,
    pairGapExcessOf, gapExcessOf, gapExcessOf, gapPairingOf, atomPairing]
  ring

/-- **THE THIRD LEG.**  The third centered inclusion moment is the tie leg
`det (Gram − 1)`, scaled by the three weights. -/
theorem centeredBasisTriple_eq_weightProduct_mul_discriminantTie
    (design : WeightedDesign size 3) (first second third : Fin size)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    centeredBasisTriple design first second third
      = design.weight first * design.weight second * design.weight third
        * discriminantTie design first second third := by
  rw [centeredBasisTriple,
    ← weightProduct_mul_det_gap_eq_basisMarginals design first second third
      hfirstSecond hfirstThird hsecondThird,
    det_subsetSum_sub_one_eq_discriminantTie design hfirstSecond hfirstThird hsecondThird]

/-- The first moment and the gap excess have the same sign. -/
theorem centeredBasisFirst_pos_iff (design : WeightedDesign size 3) (first : Fin size) :
    0 < centeredBasisFirst design first ↔ 0 < gapExcessOf design first := by
  rw [centeredBasisFirst_eq_weight_mul_gapExcess]
  exact pos_scaled_iff_pos (design.weight_pos first)

/-- The second moment and the pair gap excess have the same sign. -/
theorem centeredBasisPair_pos_iff (design : WeightedDesign size 3) (first second : Fin size) :
    0 < centeredBasisPair design first second
      ↔ 0 < pairGapExcessOf design first second := by
  rw [centeredBasisPair_eq_weightProduct_mul_pairGapExcess]
  exact pos_scaled_iff_pos (mul_pos (design.weight_pos first) (design.weight_pos second))

/-- The third moment and the tie leg have the same sign. -/
theorem centeredBasisTriple_pos_iff (design : WeightedDesign size 3)
    (first second third : Fin size) (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    0 < centeredBasisTriple design first second third
      ↔ 0 < discriminantTie design first second third := by
  rw [centeredBasisTriple_eq_weightProduct_mul_discriminantTie design first second third
    hfirstSecond hfirstThird hsecondThird]
  exact pos_scaled_iff_pos
    (mul_pos (mul_pos (design.weight_pos first) (design.weight_pos second))
      (design.weight_pos third))

/-- **`IsLivePair` IS THE FIRST TWO MOMENTS.**  A pair is live exactly when the two
one-point centered moments and the two-point centered moment are strictly positive. -/
theorem isLivePair_iff_centeredBasisMoments (design : WeightedDesign size 3)
    (first second : Fin size) :
    IsLivePair design first second
      ↔ 0 < centeredBasisFirst design first ∧ 0 < centeredBasisFirst design second
        ∧ 0 < centeredBasisPair design first second := by
  rw [IsLivePair, centeredBasisFirst_pos_iff, centeredBasisFirst_pos_iff,
    centeredBasisPair_pos_iff]

end RefusalDictionary

/-! ## Strict domination as a statement about basis moments alone -/

section MomentDomination

variable {size : ℕ}

/-- **SOME CARD-THREE SUBSET IS STRICT, IN BASIS MOMENTS ALONE.**  Composing
`Gtz.tripleGap_posDef_iff_centeredBasisMoments` with the three-element decomposition of a
card-three subset turns the covering question into a purely moment-theoretic existential:
three distinct labels whose first, second and third centered inclusion moments are all
strictly positive.  No matrix, no direction, no determinant, and no cardinality
bookkeeping on the right. -/
theorem exists_posDef_cardThree_iff_centeredBasisMoments (design : WeightedDesign size 3) :
    (∃ selected : Finset (Fin size), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef)
      ↔ ∃ first second third : Fin size,
          first ≠ second ∧ first ≠ third ∧ second ≠ third
            ∧ 0 < centeredBasisFirst design first
            ∧ 0 < centeredBasisPair design first second
            ∧ 0 < centeredBasisTriple design first second third := by
  constructor
  · rintro ⟨selected, hcard, hposDef⟩
    obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hset⟩ :=
      Finset.card_eq_three.mp hcard
    subst hset
    obtain ⟨hfirst, hpair, htriple⟩ :=
      (tripleGap_posDef_iff_centeredBasisMoments design first second third
        hfirstSecond hfirstThird hsecondThird).mp hposDef
    exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
      hfirst, hpair, htriple⟩
  · rintro ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
      hfirst, hpair, htriple⟩
    refine ⟨{first, second, third}, ?_, ?_⟩
    · exact Finset.card_eq_three.mpr
        ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, rfl⟩
    · exact (tripleGap_posDef_iff_centeredBasisMoments design first second third
        hfirstSecond hfirstThird hsecondThird).mpr ⟨hfirst, hpair, htriple⟩

end MomentDomination

/-! ## The refusal system, restated in basis coordinates -/

section MomentRefusal

variable {size : ℕ}

/-- The first moment and the gap excess have the same sign, in nonpositive form. -/
theorem centeredBasisFirst_nonpos_iff (design : WeightedDesign size 3) (first : Fin size) :
    centeredBasisFirst design first ≤ 0 ↔ gapExcessOf design first ≤ 0 := by
  rw [← not_lt, ← not_lt, centeredBasisFirst_pos_iff]

/-- The second moment and the pair gap excess have the same sign, in nonpositive form. -/
theorem centeredBasisPair_nonpos_iff (design : WeightedDesign size 3)
    (first second : Fin size) :
    centeredBasisPair design first second ≤ 0
      ↔ pairGapExcessOf design first second ≤ 0 := by
  rw [← not_lt, ← not_lt, centeredBasisPair_pos_iff]

/-- The third moment and the tie leg have the same sign, in nonpositive form. -/
theorem centeredBasisTriple_nonpos_iff (design : WeightedDesign size 3)
    (first second third : Fin size) (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    centeredBasisTriple design first second third ≤ 0
      ↔ discriminantTie design first second third ≤ 0 := by
  rw [← not_lt, ← not_lt,
    centeredBasisTriple_pos_iff design first second third hfirstSecond hfirstThird
      hsecondThird]

/-- **THE WHOLE REFUSAL, IN CENTERED MOMENTS.**  Every ordered triple of distinct labels
fails at one of its three Sylvester legs, each leg read as a centered inclusion moment of
the projection-DPP basis distribution.  No matrix, no direction, no weight: the residual is
a pure sign system on the moments. -/
def CenteredMomentRefusal (design : WeightedDesign size 3) : Prop :=
  ∀ first second third : Fin size,
    first ≠ second → first ≠ third → second ≠ third →
      centeredBasisFirst design first ≤ 0
        ∨ centeredBasisPair design first second ≤ 0
        ∨ centeredBasisTriple design first second third ≤ 0

/-- **THE MOMENT REFUSAL IS EXACTLY "NO CARD-THREE SUBSET IS STRICT".**  The negation of
`exists_posDef_cardThree_iff_centeredBasisMoments`, spelled as a universally quantified
sign system.  Every `size`, no design hypothesis. -/
theorem centeredMomentRefusal_iff_no_posDef_cardThree (design : WeightedDesign size 3) :
    CenteredMomentRefusal design
      ↔ ∀ selected : Finset (Fin size), selected.card = 3 →
          ¬ (subsetSum design selected - 1).PosDef := by
  constructor
  · intro hrefusal selected hcard hposDef
    obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hset⟩ :=
      Finset.card_eq_three.mp hcard
    subst hset
    obtain ⟨hfirst, hpair, htriple⟩ :=
      (tripleGap_posDef_iff_centeredBasisMoments design first second third
        hfirstSecond hfirstThird hsecondThird).mp hposDef
    rcases hrefusal first second third hfirstSecond hfirstThird hsecondThird with
      hleg | hleg | hleg
    · exact absurd hfirst (not_lt.mpr hleg)
    · exact absurd hpair (not_lt.mpr hleg)
    · exact absurd htriple (not_lt.mpr hleg)
  · intro hnone first second third hfirstSecond hfirstThird hsecondThird
    by_cases hfirst : centeredBasisFirst design first ≤ 0
    · exact Or.inl hfirst
    by_cases hpair : centeredBasisPair design first second ≤ 0
    · exact Or.inr (Or.inl hpair)
    refine Or.inr (Or.inr ?_)
    by_contra htriple
    exact hnone {first, second, third}
      (Finset.card_eq_three.mpr
        ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, rfl⟩)
      ((tripleGap_posDef_iff_centeredBasisMoments design first second third
        hfirstSecond hfirstThird hsecondThird).mpr
          ⟨not_le.mp hfirst, not_le.mp hpair, not_le.mp htriple⟩)

/-- **THE FREE-PAIR REFUSAL IN BASIS COORDINATES.**  The exact transcription of
`Gtz.FreePairMinorRefusal` into centered inclusion moments: three free pairs, twelve
completions, two moment signs each. -/
def FreePairMomentRefusal (design : WeightedDesign 6 3) : Prop :=
  ∀ first second third : Fin 6,
    first ∈ ({3, 4, 5} : Finset (Fin 6)) → second ∈ ({3, 4, 5} : Finset (Fin 6)) →
      first ≠ second → first ≠ third → second ≠ third →
        centeredBasisPair design first second ≤ 0
          ∨ centeredBasisTriple design first second third ≤ 0

/-- **THE RESTATEMENT IS AN IFF, IN BOTH DIRECTIONS.**  The moment refusal and the landed
scalar refusal are the same predicate: the two legs differ by the positive weight products
`t_a t_b` and `t_a t_b t_c`, which change no sign.  Unconditional -- no dominating base, no
tight direction, no line-freeness. -/
theorem freePairMomentRefusal_iff_freePairMinorRefusal (design : WeightedDesign 6 3) :
    FreePairMomentRefusal design ↔ FreePairMinorRefusal design := by
  constructor
  · intro hrefusal first second third hfirst hsecond hfirstSecond hfirstThird hsecondThird
    rcases hrefusal first second third hfirst hsecond hfirstSecond hfirstThird
      hsecondThird with hpair | htriple
    · exact Or.inl ((centeredBasisPair_nonpos_iff design first second).mp hpair)
    · exact Or.inr ((centeredBasisTriple_nonpos_iff design first second third
        hfirstSecond hfirstThird hsecondThird).mp htriple)
  · intro hrefusal first second third hfirst hsecond hfirstSecond hfirstThird hsecondThird
    rcases hrefusal first second third hfirst hsecond hfirstSecond hfirstThird
      hsecondThird with hpair | htriple
    · exact Or.inl ((centeredBasisPair_nonpos_iff design first second).mpr hpair)
    · exact Or.inr ((centeredBasisTriple_nonpos_iff design first second third
        hfirstSecond hfirstThird hsecondThird).mpr htriple)

/-- **THE LANDED FAILURE CHARACTERISATION, WITH THE FREE-PAIR HALF IN MOMENTS.**
`Gtz.not_exists_posDef_cardThree_iff_freePairMinorRefusal` with its scalar conjunct
replaced by the basis-coordinate one. -/
theorem not_exists_posDef_cardThree_iff_freePairMomentRefusal (design : WeightedDesign 6 3)
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    (∀ selected : Finset (Fin 6), selected.card = 3 →
        ¬ (subsetSum design selected - 1).PosDef)
      ↔ ¬ TightLineOneSlotFamily design ∧ FreePairMomentRefusal design := by
  rw [freePairMomentRefusal_iff_freePairMinorRefusal]
  exact not_exists_posDef_cardThree_iff_freePairMinorRefusal design hdominates htightNe
    htight

/-- **THE WHOLE RESIDUAL IS A MOMENT SIGN SYSTEM.**  On the antecedent of the `(6,3)`
tight-line branch, the universally quantified moment refusal over ALL ordered triples is
equivalent to the landed split "no one-slot swap is strict, and every free pair refuses".
So the one-slot half is moment-expressible too, and the residual needs nothing outside the
twenty basis masses and the weights. -/
theorem centeredMomentRefusal_iff_oneSlotRefusal_and_freePairMomentRefusal
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    CenteredMomentRefusal design
      ↔ ¬ TightLineOneSlotFamily design ∧ FreePairMomentRefusal design := by
  rw [centeredMomentRefusal_iff_no_posDef_cardThree]
  exact not_exists_posDef_cardThree_iff_freePairMomentRefusal design hdominates htightNe
    htight

end MomentRefusal

/-! ## Satisfiability and contradictability, at landed designs -/

section MomentWitnesses

/-- Two equal atoms have pair gap excess `1 − 2·leverage`, so they are never a live pair
above leverage one half.  General size, general rank. -/
theorem pairGapExcessOf_of_atom_eq {size rank : ℕ} (design : WeightedDesign size rank)
    {first second : Fin size} (hatom : design.atom first = design.atom second) :
    pairGapExcessOf design first second = 1 - 2 * leverageOf (design.atom first) := by
  have hpairing : gapPairingOf design first second = leverageOf (design.atom first) := by
    rw [gapPairingOf, ← hatom, leverageOf_eq_dotProduct]
  have hexcess : gapExcessOf design second = leverageOf (design.atom first) - 1 := by
    rw [gapExcessOf, ← hatom]
  rw [pairGapExcessOf, hpairing, hexcess, gapExcessOf]
  ring

/-- **`CenteredMomentRefusal` IS INHABITED**, at the landed non-uniform-leverage tie.  Its
ten dominating triples and zero strict ones are exactly the refusal, read through
`centeredMomentRefusal_iff_no_posDef_cardThree`. -/
theorem centeredMomentRefusal_nonUniformLeverageTieDesign :
    CenteredMomentRefusal nonUniformLeverageTieDesign :=
  (centeredMomentRefusal_iff_no_posDef_cardThree nonUniformLeverageTieDesign).mpr
    nonUniformLeverageTieDesign_not_posDef_cardThree

/-- **`CenteredMomentRefusal` IS CONTRADICTABLE**, at the landed all-heavy design whose
free-pair row aggregate is negative: its triple `{1, 3, 5}` is strictly dominating. -/
theorem not_centeredMomentRefusal_allHeavyNegativeAggregateDesign :
    ¬ CenteredMomentRefusal allHeavyNegativeAggregateDesign := by
  rw [centeredMomentRefusal_iff_no_posDef_cardThree]
  intro hnone
  obtain ⟨selected, hcard, hposDef⟩ :=
    allHeavyNegativeAggregateDesign_exists_posDef_cardThree
  exact hnone selected hcard hposDef

/-- **`FreePairMomentRefusal` IS INHABITED**, at the same tie, and for a reason visible in
the moments: its three free atoms are equal, so every free pair has pair gap excess
`1 − 2 · 4/3 = −5/3` and the first disjunct fires at all twelve completions. -/
theorem freePairMomentRefusal_nonUniformLeverageTieDesign :
    FreePairMomentRefusal nonUniformLeverageTieDesign := by
  have hlight : ∀ label : Fin 6, label ∈ ({3, 4, 5} : Finset (Fin 6)) →
      nonUniformLeverageTieDesign.atom label = nonUniformLeverageTieDesign.atom 3 := by
    intro label hlabel
    fin_cases label
    · exact absurd hlabel (by decide)
    · exact absurd hlabel (by decide)
    · exact absurd hlabel (by decide)
    · rfl
    · rfl
    · rfl
  intro first second third hfirst hsecond hfirstSecond hfirstThird hsecondThird
  refine Or.inl
    ((centeredBasisPair_nonpos_iff nonUniformLeverageTieDesign first second).mpr ?_)
  have hatomEq : nonUniformLeverageTieDesign.atom first
      = nonUniformLeverageTieDesign.atom second :=
    (hlight first hfirst).trans (hlight second hsecond).symm
  have hleverage : leverageOf (nonUniformLeverageTieDesign.atom first) = 4 / 3 := by
    rw [hlight first hfirst, nonUniformLeverageTieDesign_leverage]
    norm_num
  rw [pairGapExcessOf_of_atom_eq nonUniformLeverageTieDesign hatomEq, hleverage]
  norm_num

/-- **`FreePairMomentRefusal` IS CONTRADICTABLE**, at the landed all-heavy design: its
strict triple `{1, 3, 5}` has two free labels, so the free pair `(3, 5)` has a strictly
positive two-point moment AND a strictly positive three-point moment at the completion
`1`.  Exact values, verified outside the kernel: `pairGapExcessOf 3 5 = 79/81` and
`discriminantTie 3 5 1 = 299/27`. -/
theorem not_freePairMomentRefusal_allHeavyNegativeAggregateDesign :
    ¬ FreePairMomentRefusal allHeavyNegativeAggregateDesign := by
  intro hrefusal
  have hset : ({3, 5, 1} : Finset (Fin 6)) = ({1, 3, 5} : Finset (Fin 6)) := by decide
  have hposDef : (subsetSum allHeavyNegativeAggregateDesign {3, 5, 1} - 1).PosDef := by
    rw [hset]
    exact allHeavyNegativeAggregateDesign_gap_oneThreeFive_posDef
  obtain ⟨-, hpair, htriple⟩ :=
    (tripleGap_posDef_iff_centeredBasisMoments allHeavyNegativeAggregateDesign 3 5 1
      (by decide) (by decide) (by decide)).mp hposDef
  rcases hrefusal 3 5 1 (by decide) (by decide) (by decide) (by decide) (by decide) with
    hleg | hleg
  · exact absurd hpair (not_lt.mpr hleg)
  · exact absurd htriple (not_lt.mpr hleg)

end MomentWitnesses


section TransportedFrame

/-!
## The transported frame: the refusal system needs no whitening

Every chart in this campaign starts from a linear transport of the atoms,
`u_y = transform *ᵥ atom y`, and then reads the covering problem off the
transported frame together with that frame's own weighted Gram
`G = ∑_y weight y • atomMatrix (u_y)`.  Parseval collapses that Gram to
`transform * transformᵀ`, and the resulting **transported frame gap** is a
CONGRUENCE of the ordinary gap:

    `∑_{y ∈ selected} atomMatrix (u_y) − G = transform * (S_selected − 1) * transformᵀ` .

Two consequences, and they are what make chart work exact.

* Weak and strict domination are read off the transported frame directly.
  Nothing has to be whitened, so a chart point with RATIONAL frame and RATIONAL
  weights decides the whole refusal system in exact rational arithmetic even
  when the design it represents has irrational atoms — the inverse square root
  `G^{-1/2}` never appears anywhere.
* The base chart of the `U(3,6)` residual (send the weakly dominating triple to
  the standard basis) is the instance `transform = (base atom matrix)⁻¹`, at
  which `G = (base Gram)⁻¹`, so "the base triple weakly dominates and is tight"
  reads `G ≤ 1` with eigenvalue exactly one.

Every ingredient was already landed — `Gtz.sum_smul_atomMatrix_mulVec_eq_conjugate`,
`Gtz.atomMatrix_conj`, `Gtz.posDef_congruence_iff`.  What was missing is the
STATEMENT: `Gtz/Design/BalancedNormalForm.lean:977-990` assembles exactly this
congruence INLINE inside one proof of one theorem, where no content census by
name can reach it.
-/

/-- The **transported frame gap**: the gap of `selected` computed entirely inside
the transported frame `u_y = transform *ᵥ atom y`, against that frame's own
weighted Gram.  No whitening and no square root. -/
def transportedFrameGap {size rank : ℕ} (design : WeightedDesign size rank)
    (transform : Matrix (Fin rank) (Fin rank) ℝ) (selected : Finset (Fin size)) :
    Matrix (Fin rank) (Fin rank) ℝ :=
  (∑ label ∈ selected, atomMatrix (transform *ᵥ design.atom label))
    - ∑ label, design.weight label • atomMatrix (transform *ᵥ design.atom label)

/-- **Parseval collapses the transported Gram.**  The weighted Gram of the
transported frame is `transform * transformᵀ`, whatever the design. -/
theorem transportedFrameGram_eq_conjugation {size rank : ℕ}
    (design : WeightedDesign size rank) (transform : Matrix (Fin rank) (Fin rank) ℝ) :
    ∑ label, design.weight label • atomMatrix (transform *ᵥ design.atom label)
      = transform * transformᵀ := by
  rw [sum_smul_atomMatrix_mulVec_eq_conjugate, design.isParseval, Matrix.mul_one]

/-- **The transported frame gap is a congruence of the gap.**  Any `size`, any
`rank`, any subset, any transform — invertibility is not needed for the identity,
only for the two transfer statements below. -/
theorem transportedFrameGap_eq_conjugatedGap {size rank : ℕ}
    (design : WeightedDesign size rank) (transform : Matrix (Fin rank) (Fin rank) ℝ)
    (selected : Finset (Fin size)) :
    transportedFrameGap design transform selected
      = transform * (subsetSum design selected - 1) * transformᵀ := by
  have hselected : ∑ label ∈ selected, atomMatrix (transform *ᵥ design.atom label)
      = transform * subsetSum design selected * transformᵀ := by
    have hstep := sum_smul_atomMatrix_mulVec_eq_conjugate transform design.atom
      (fun _ => (1 : ℝ)) selected
    simpa only [one_smul, subsetSum] using hstep
  rw [transportedFrameGap, hselected, transportedFrameGram_eq_conjugation,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]

/-- **Strict domination is a chart-invariant question.** -/
theorem posDef_transportedFrameGap_iff {size rank : ℕ}
    (design : WeightedDesign size rank) {transform : Matrix (Fin rank) (Fin rank) ℝ}
    (hunit : IsUnit transform.det) (selected : Finset (Fin size)) :
    (transportedFrameGap design transform selected).PosDef
      ↔ (subsetSum design selected - 1).PosDef := by
  have htransposeUnit : IsUnit (transformᵀ).det := by
    rw [Matrix.det_transpose]; exact hunit
  have hrewrite : transportedFrameGap design transform selected
      = (transformᵀ)ᵀ * (subsetSum design selected - 1) * transformᵀ := by
    rw [transportedFrameGap_eq_conjugatedGap, Matrix.transpose_transpose]
  rw [hrewrite]
  exact posDef_congruence_iff htransposeUnit

/-- **Weak domination is a chart-invariant question**, the `PosSemidef` twin, and
therefore the tree's `Dominates` predicate is chart-invariant. -/
theorem posSemidef_transportedFrameGap_iff {size rank : ℕ}
    (design : WeightedDesign size rank) {transform : Matrix (Fin rank) (Fin rank) ℝ}
    (hunit : IsUnit transform.det) (selected : Finset (Fin size)) :
    (transportedFrameGap design transform selected).PosSemidef
      ↔ Dominates design selected := by
  rw [transportedFrameGap_eq_conjugatedGap, Dominates]
  constructor
  · intro hconjugated
    have htransposeUnit : IsUnit (transformᵀ).det := by
      rw [Matrix.det_transpose]; exact hunit
    have hcancel : transform⁻¹ * (transform * (subsetSum design selected - 1) * transformᵀ)
        * (transform⁻¹)ᵀ = subsetSum design selected - 1 := by
      have hleftCancel : transform⁻¹
          * (transform * (subsetSum design selected - 1) * transformᵀ)
          = (subsetSum design selected - 1) * transformᵀ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit,
          Matrix.one_mul]
      rw [hleftCancel, Matrix.transpose_nonsing_inv, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ htransposeUnit, Matrix.mul_one]
    have htransported := hconjugated.mul_mul_conjTranspose_same (B := transform⁻¹)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at htransported
    rwa [hcancel] at htransported
  · intro hgap
    have htransported := hgap.mul_mul_conjTranspose_same (B := transform)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at htransported

end TransportedFrame

end Gtz

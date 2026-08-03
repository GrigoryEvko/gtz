/-
# The derivative identity, the product mixture, and the coefficient-aggregate dictionary

Two mixtures of characteristic polynomials live in this file, and the first thing
to fix is that they are DIFFERENT OBJECTS.

  * `subsetCharpolySum form selectionSize` — the flat sum of the characteristic
    polynomials of ALL principal submatrices of one square matrix of a given size.
    Abstract: an arbitrary index type, an arbitrary commutative ring, no design.
  * `productMixture design weight` — the PRODUCT-weighted mixture of the
    characteristic polynomials of the atom sums `S_T` of the `k`-subsets of a
    weighted design.

They are not two names for one thing.  The first is about principal submatrices of
a fixed matrix; the second is about the atom sums, which are `k × k` and are not
submatrices of anything.  The bridge between the two pictures is the chart pencil
`Gtz.det_chartGapMatrix_block`, which is shipped only at the DETERMINANT level, so
this file does not compose them and does not pretend to.

## What is proved

**THE DERIVATIVE IDENTITY, at general `(size, rank)`, over an arbitrary
commutative ring** (`subsetCharpolySum_eq_hasseDeriv_charpoly`):

    ∑_{|C| = k} charpoly (M restricted to C)  =  hasseDeriv (card − k) (charpoly M)

with the factorial form `factorial_smul_subsetCharpolySum` beside it.  No symmetry,
no field, no positivity, no rank hypothesis: it is a polynomial identity in the
entries, and the coefficient of `x^(k−j)` on either side is `(−1)^j` times the
same weighted total of `j × j` principal minors.  The whole content is Mathlib's
`Matrix.charpoly_coeff_eq_sum_minors`; what this file adds is the two
combinatorial reindexing steps Mathlib does not have in this shape — the
double-counting law `sum_powersetCard_sum_powersetCard` and the subtype-of-subtype
reindexing `sum_det_principalSubmatrix_subtype`.  The generating-function form
`subsetCharpolySum_eq_coeff_det_one_add_smul` reads the whole family off ONE
determinant over `R[X][Y]`.

**THE COEFFICIENT-AGGREGATE DICTIONARY** (`coeff_taylor_one_productMixture`,
`eval_productMixture_ne_zero_of_lt_one`).  Shifting the product mixture to one
turns every atom sum into its gap, `taylor_one_charpoly`:
`taylor 1 (charpoly N) = charpoly (N − 1)`.  Coefficient `index` of the shifted
mixture is then `(−1)^(rank − index)` times `gapMinorAggregate design weight
(rank − index)`, the weight-product-weighted total of the `(rank − index)`-sized
principal minors of the gaps.  Hence Descartes: if all `rank + 1` aggregates are
nonnegative and the order-zero one is strictly positive, the mixture has NO ROOT
strictly below one.

Two things about that implication are worth stating plainly.  It needs NO
real-rootedness — the sign argument bounds the value, not the roots — and it is
the only half of the mixture route that is unconditional.  The other half is the
pigeonhole, which is not mechanized anywhere and is carried here as a named `Prop`
in the repository's root-free convention (`DoesProductMixtureInterlaceAt`,
modelled on `Gtz.DoesMixtureInterlaceAt`).

**THE FAMILY SEPARATION** (`tiltedMixture_eq_sum_weightProduct_mul_det`).  The
shipped tilted mixture of `Gtz/Quantitative/ExpectedCharPolynomial.lean` is
volume-sampled: unfolding its shadow determinant shows it is the product mixture
at weight `tilt · t` TIMES a factor `det S_T` per subset.  The two families
therefore differ exactly on the linearly dependent subsets, where the
determinantal one assigns zero mass and the product one does not.  That single
factor is the whole difference between them, and it is why neither dominates the
other.

**THE TIE OBSTRUCTION** (`exists_root_productMixture_lt_one_of_odd`,
`not_hasProductMixtureCertificate_of_partialTie`).  At odd rank, on a design where
no gap determinant is positive and at least one is strictly negative, EVERY
strictly positive product weighting puts a root of the mixture inside `(0,1)`.
The mechanism is two signs and one intermediate value: `eval 0 < 0` because every
atom sum is positive semidefinite so its determinant is nonnegative and — by
`exists_pos_det_subsetSum`, which is the shadow determinants summing to one — at
least one is strictly positive, and `eval 1 > 0` because at odd rank
`det(1 − S_T) = −det(S_T − 1)`.  The profile is therefore the ONLY hypothesis
beyond odd rank.  Consequence:
`HasProductMixtureCertificate` — the exact product analogue of
`Gtz.EcpStar` — fails at any such design, so no formula `weight(design)` can
certify one.

## Scope, and what this file does NOT claim

`DoesProductMixtureInterlaceAt m k 1` is an IFF-TRAP and is documented as one:
`doesProductMixtureInterlaceAtOne_of_gtzWeighted` derives it from `GtzWeighted`
outright, exactly as `Gtz.doesMixtureInterlaceAtOne_of_gtzWeighted` does for the
volume-sampled family, because at level one the root hypothesis is discarded and
the conclusion is domination restated.  All the independent content sits at levels
strictly below one.

The tie obstruction's hypothesis bundle is EXACTLY the partial-tie profile: every
gap determinant nonpositive, one strictly negative.  It is satisfied by the
measured `(6,3)` tie at uniform weight `1/6` over `ℚ(√5)` — twelve of the twenty
gap determinants zero, four at `−1/54` and four at `−5/108` after clearing the
weight product, none positive — but that design is NOT mechanized anywhere in this
repository, so the theorem's non-vacuity in-kernel is OPEN and is recorded as such
rather than asserted.  A total tie (all gap determinants zero, as at
`Gtz.tetraDesign`) does NOT satisfy it, and indeed the certificate survives there,
which is why the strict clause is not decorative.

## Provenance of the consumed claims

  * The derivative identity is proved here, not assumed.  It is the uniform member
    of the family and it is R.C. Thompson's principal-minor theorem iterated; the
    campaign verified it symbolically at `(4,2)`, `(5,3)`, `(6,3)`, `(7,3)`,
    `(6,4)`, `(8,3)`, `(9,5)`, `(10,4)`, `(11,4)`, `(8,6)`, `(12,7)` before it was
    mechanized, and independently again at four further sizes.
  * Real-rootedness of the product mixture at every strictly positive weight, and
    the interlacing pigeonhole, are NOT proved here and NOT assumed here.  They are
    off-Lean: real-rootedness follows from real stability of
    `det(x·1 + diag(1/v) · y − W)` by the Borcea–Brändén preservers (differentiate
    in `y`, then specialise `y = 0`), and the pigeonhole is the
    Marcus–Spielman–Srivastava interlacing-family bound, already quoted with full
    provenance in `Gtz/Reduction/MixedCharPolynomial.lean`.  Both were screened at
    scale by exact rational arithmetic during the campaign with no failure, and the
    uniform-weight case of the pigeonhole is published (Ravichandran,
    arXiv:1609.04187, Theorem 2.3, with no isotropy hypothesis).  Only the
    pigeonhole is named as a `Prop` here, because only the pigeonhole is used.
  * The FULL common interlacing of the whole family — every nonnegative weighting,
    not merely the product ones — is FALSE, refuted during the campaign by exact
    counterexamples at the `(6,3)` design shape and by a four-by-four hand
    witness.  Nothing here quantifies over non-product weights.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.MixedCharPolynomial
import Gtz.Quantitative.ExpectedCharPolynomial
import Gtz.Quantitative.RungThreeAggregate
import Gtz.Quantitative.TiltConcentration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## The derivative identity, abstract

Everything in this section is about principal submatrices of one square matrix
over one commutative ring.  There is no design, no rank, no order and no field. -/

section AbstractMixture

variable {baseRing : Type*} [CommRing baseRing]
variable {indexType : Type*} [Fintype indexType] [DecidableEq indexType]

/-- **Double counting over `powersetCard`.**  Summing a set function over the
`inner`-element subsets of every `chosen`-element subset visits each
`inner`-element subset `(card − inner).choose (chosen − inner)` times. -/
theorem sum_powersetCard_sum_powersetCard
    (chosenCard innerCard : ℕ) (hInnerLe : innerCard ≤ chosenCard)
    (weightOfSubset : Finset indexType → baseRing) :
    ∑ chosen ∈ (Finset.univ : Finset indexType).powersetCard chosenCard,
        ∑ inner ∈ chosen.powersetCard innerCard, weightOfSubset inner
      = ((Fintype.card indexType - innerCard).choose (chosenCard - innerCard)) •
        ∑ inner ∈ (Finset.univ : Finset indexType).powersetCard innerCard,
          weightOfSubset inner := by
  have restrict : ∀ chosen : Finset indexType,
      chosen.powersetCard innerCard
        = ((Finset.univ : Finset indexType).powersetCard innerCard).filter (· ⊆ chosen) := by
    intro chosen
    ext inner
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  calc ∑ chosen ∈ (Finset.univ : Finset indexType).powersetCard chosenCard,
          ∑ inner ∈ chosen.powersetCard innerCard, weightOfSubset inner
      = ∑ chosen ∈ (Finset.univ : Finset indexType).powersetCard chosenCard,
          ∑ inner ∈ (Finset.univ : Finset indexType).powersetCard innerCard,
            if inner ⊆ chosen then weightOfSubset inner else 0 := by
        refine Finset.sum_congr rfl fun chosen _ => ?_
        rw [restrict chosen, Finset.sum_filter]
    _ = ∑ inner ∈ (Finset.univ : Finset indexType).powersetCard innerCard,
          ∑ chosen ∈ (Finset.univ : Finset indexType).powersetCard chosenCard,
            if inner ⊆ chosen then weightOfSubset inner else 0 := Finset.sum_comm
    _ = ∑ inner ∈ (Finset.univ : Finset indexType).powersetCard innerCard,
          ((Fintype.card indexType - innerCard).choose (chosenCard - innerCard)) •
            weightOfSubset inner := by
        refine Finset.sum_congr rfl fun inner hInner => ?_
        have hCard : inner.card = innerCard := (Finset.mem_powersetCard.mp hInner).2
        rw [← Finset.sum_filter, Finset.sum_const,
          Finset.card_filter_powersetCard_subset inner Finset.univ chosenCard
            (Finset.subset_univ _) (hCard ▸ hInnerLe)]
        simp [hCard, Finset.card_univ]
    _ = _ := (Finset.smul_sum).symm

omit [Fintype indexType] in
/-- Reindex the principal minors of a principal submatrix off the subtype: the
`inner`-sized principal minors of the block on `chosen` are the `inner`-sized
principal minors of the whole matrix taken over the subsets of `chosen`. -/
theorem sum_det_principalSubmatrix_subtype
    (form : Matrix indexType indexType baseRing) (chosen : Finset indexType) (innerCard : ℕ) :
    ∑ innerOnSubtype ∈
        (Finset.univ : Finset { index // index ∈ chosen }).powersetCard innerCard,
        (((form.submatrix (Subtype.val) (Subtype.val) :
              Matrix { index // index ∈ chosen } { index // index ∈ chosen }
                baseRing)).submatrix
            (Subtype.val : { slot // slot ∈ innerOnSubtype } → { index // index ∈ chosen })
            Subtype.val).det
      = ∑ inner ∈ chosen.powersetCard innerCard,
        (form.submatrix (Subtype.val : { index // index ∈ inner } → indexType)
          Subtype.val).det := by
  classical
  have hAttach : chosen.attach.map (Function.Embedding.subtype (· ∈ chosen)) = chosen :=
    Finset.attach_map_val
  have key : ∀ innerOnSubtype : Finset { index // index ∈ chosen },
      (((form.submatrix (Subtype.val) (Subtype.val) :
            Matrix { index // index ∈ chosen } { index // index ∈ chosen }
              baseRing)).submatrix
          (Subtype.val : { slot // slot ∈ innerOnSubtype } → { index // index ∈ chosen })
          Subtype.val).det
        = (form.submatrix
            (Subtype.val :
              { index // index ∈
                innerOnSubtype.map (Function.Embedding.subtype (· ∈ chosen)) } → indexType)
            Subtype.val).det := by
    intro innerOnSubtype
    set mapped : Finset indexType :=
      innerOnSubtype.map (Function.Embedding.subtype (· ∈ chosen)) with hMapped
    have hForward : ∀ slot : { slot // slot ∈ innerOnSubtype }, (slot.1 : indexType) ∈ mapped :=
      fun slot => Finset.mem_map_of_mem _ slot.2
    let toMapped : { slot // slot ∈ innerOnSubtype } → { index // index ∈ mapped } :=
      fun slot => ⟨slot.1.1, hForward slot⟩
    have hInj : Function.Injective toMapped := by
      intro leftSlot rightSlot hEqual
      have hValue : (leftSlot.1).val = (rightSlot.1).val :=
        congrArg (fun target : { index // index ∈ mapped } => target.val) hEqual
      exact Subtype.ext (Subtype.ext hValue)
    have hSurj : Function.Surjective toMapped := by
      rintro ⟨target, hTarget⟩
      rw [hMapped, Finset.mem_map] at hTarget
      obtain ⟨source, hSource, hEqual⟩ := hTarget
      exact ⟨⟨source, hSource⟩, Subtype.ext hEqual⟩
    let reindexEquiv : { slot // slot ∈ innerOnSubtype } ≃ { index // index ∈ mapped } :=
      Equiv.ofBijective toMapped ⟨hInj, hSurj⟩
    have hSub :
        (((form.submatrix (Subtype.val) (Subtype.val) :
              Matrix { index // index ∈ chosen } { index // index ∈ chosen }
                baseRing)).submatrix
            (Subtype.val : { slot // slot ∈ innerOnSubtype } → { index // index ∈ chosen })
            Subtype.val)
          = (form.submatrix (Subtype.val : { index // index ∈ mapped } → indexType)
              Subtype.val).submatrix reindexEquiv reindexEquiv := by
      ext leftSlot rightSlot; rfl
    rw [hSub, Matrix.det_submatrix_equiv_self]
  calc ∑ innerOnSubtype ∈
          (Finset.univ : Finset { index // index ∈ chosen }).powersetCard innerCard,
          (((form.submatrix (Subtype.val) (Subtype.val) :
                Matrix { index // index ∈ chosen } { index // index ∈ chosen }
                  baseRing)).submatrix
              (Subtype.val : { slot // slot ∈ innerOnSubtype } → { index // index ∈ chosen })
              Subtype.val).det
      = ∑ innerOnSubtype ∈
          (Finset.univ : Finset { index // index ∈ chosen }).powersetCard innerCard,
          (form.submatrix
            (Subtype.val :
              { index // index ∈
                innerOnSubtype.map (Function.Embedding.subtype (· ∈ chosen)) } → indexType)
            Subtype.val).det :=
        Finset.sum_congr rfl fun innerOnSubtype _ => key innerOnSubtype
    _ = ∑ inner ∈ chosen.powersetCard innerCard,
          (form.submatrix (Subtype.val : { index // index ∈ inner } → indexType)
            Subtype.val).det := by
        conv_rhs => rw [← hAttach, Finset.powersetCard_map, Finset.sum_map,
          ← Finset.univ_eq_attach]
        exact Finset.sum_congr rfl fun innerOnSubtype _ => rfl

/-- **THE UNIFORM MIXTURE, abstract.**  The flat sum of the characteristic
polynomials of all principal submatrices of a given size. -/
noncomputable def subsetCharpolySum (form : Matrix indexType indexType baseRing)
    (selectionSize : ℕ) : Polynomial baseRing :=
  ∑ chosen ∈ (Finset.univ : Finset indexType).powersetCard selectionSize,
    (form.submatrix (Subtype.val : { index // index ∈ chosen } → indexType)
      Subtype.val).charpoly

/-- The characteristic matrix of a principal submatrix is the principal submatrix
of the characteristic matrix. -/
theorem charmatrix_principalSubmatrix (form : Matrix indexType indexType baseRing)
    (chosen : Finset indexType) :
    (Matrix.charmatrix form).submatrix (Subtype.val : { index // index ∈ chosen } → indexType)
        (Subtype.val : { index // index ∈ chosen } → indexType)
      = Matrix.charmatrix (form.submatrix (Subtype.val : { index // index ∈ chosen } → indexType)
          (Subtype.val : { index // index ∈ chosen } → indexType)) := by
  refine Matrix.ext fun firstIndex secondIndex => ?_
  rw [Matrix.submatrix_apply, Matrix.charmatrix_apply, Matrix.charmatrix_apply,
    Matrix.submatrix_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  rcases eq_or_ne firstIndex secondIndex with hsame | hdistinct
  · rw [hsame, if_pos rfl, if_pos rfl]
  · rw [if_neg hdistinct, if_neg (fun hvalue => hdistinct (Subtype.ext hvalue))]

/-- **Generating function for the whole family.**  Every `subsetCharpolySum` is a
single coefficient of one determinant over `baseRing[X][Y]`: Mathlib's
`Matrix.coeff_det_one_add_X_smul_eq_sum_minors` applied over the polynomial ring,
with `charmatrix_principalSubmatrix` transporting the submatrix through. -/
theorem subsetCharpolySum_eq_coeff_det_one_add_smul
    (form : Matrix indexType indexType baseRing) (selectionSize : ℕ) :
    subsetCharpolySum form selectionSize
      = (Matrix.det (1 + (Polynomial.X : Polynomial (Polynomial baseRing)) •
          (Matrix.charmatrix form).map Polynomial.C)).coeff selectionSize := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors, subsetCharpolySum]
  refine Finset.sum_congr rfl fun chosen _ => ?_
  rw [charmatrix_principalSubmatrix, Matrix.charpoly]

/-- Evaluating the uniform mixture at a level: the total of the shifted
determinants of the principal submatrices. -/
theorem eval_subsetCharpolySum (form : Matrix indexType indexType baseRing)
    (selectionSize : ℕ) (level : baseRing) :
    (subsetCharpolySum form selectionSize).eval level
      = ∑ chosen ∈ (Finset.univ : Finset indexType).powersetCard selectionSize,
          (Matrix.scalar { index // index ∈ chosen } level
            - form.submatrix (Subtype.val : { index // index ∈ chosen } → indexType)
              Subtype.val).det := by
  rw [subsetCharpolySum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun chosen _ => ?_
  rw [Matrix.eval_charpoly]

/-- The constant coefficient of a characteristic polynomial is the determinant up
to the sign of the dimension.  Used to read the top-order coefficient aggregate
off the derivative identity. -/
theorem coeff_zero_charpoly (form : Matrix indexType indexType baseRing) :
    form.charpoly.coeff 0 = (-1) ^ (Fintype.card indexType) * form.det := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpoly, map_zero, zero_sub,
    Matrix.det_neg]

/-- **THE DERIVATIVE IDENTITY, at general `(size, rank)`.**  The sum of the
characteristic polynomials of all principal submatrices of a given size is the
Hasse derivative of the characteristic polynomial, of order the codimension.  No
symmetry, no field, no positivity: a polynomial identity in the entries. -/
theorem subsetCharpolySum_eq_hasseDeriv_charpoly
    (form : Matrix indexType indexType baseRing) (selectionSize : ℕ)
    (hSelectionLe : selectionSize ≤ Fintype.card indexType) :
    subsetCharpolySum form selectionSize
      = Polynomial.hasseDeriv (Fintype.card indexType - selectionSize) form.charpoly := by
  nontriviality baseRing
  classical
  rw [subsetCharpolySum]
  set totalCard : ℕ := Fintype.card indexType with hTotal
  ext degreeIndex
  rw [Polynomial.finsetSum_coeff, Polynomial.hasseDeriv_coeff]
  rcases le_or_gt degreeIndex selectionSize with hDeg | hDeg
  · have hBlockCoeff : ∀ chosen ∈ (Finset.univ : Finset indexType).powersetCard selectionSize,
        (form.submatrix (Subtype.val : { index // index ∈ chosen } → indexType)
            Subtype.val).charpoly.coeff degreeIndex
          = (-1) ^ (selectionSize - degreeIndex) *
            ∑ inner ∈ chosen.powersetCard (selectionSize - degreeIndex),
              (form.submatrix (Subtype.val : { index // index ∈ inner } → indexType)
                Subtype.val).det := by
      intro chosen hChosen
      have hCard : Fintype.card { index // index ∈ chosen } = selectionSize := by
        simp [Fintype.card_coe, (Finset.mem_powersetCard.mp hChosen).2]
      have hIndex :
          Fintype.card { index // index ∈ chosen } - (selectionSize - degreeIndex)
            = degreeIndex := by omega
      have hminors := Matrix.charpoly_coeff_eq_sum_minors
        (form.submatrix (Subtype.val : { index // index ∈ chosen } → indexType) Subtype.val)
        (selectionSize - degreeIndex) (by omega)
      rw [hIndex] at hminors
      rw [hminors, sum_det_principalSubmatrix_subtype]
    rw [Finset.sum_congr rfl hBlockCoeff, ← Finset.mul_sum,
      sum_powersetCard_sum_powersetCard (baseRing := baseRing) selectionSize
        (selectionSize - degreeIndex) (by omega)]
    have hCharCoeff : form.charpoly.coeff (degreeIndex + (totalCard - selectionSize))
        = (-1) ^ (selectionSize - degreeIndex) *
          ∑ inner ∈ (Finset.univ : Finset indexType).powersetCard (selectionSize - degreeIndex),
            (form.submatrix (Subtype.val : { index // index ∈ inner } → indexType)
              Subtype.val).det := by
      have hShift : degreeIndex + (totalCard - selectionSize)
          = Fintype.card indexType - (selectionSize - degreeIndex) := by omega
      rw [hShift]
      exact Matrix.charpoly_coeff_eq_sum_minors form (selectionSize - degreeIndex) (by omega)
    rw [hCharCoeff]
    have hChoose : (degreeIndex + (totalCard - selectionSize)).choose (totalCard - selectionSize)
        = (totalCard - (selectionSize - degreeIndex)).choose
            (selectionSize - (selectionSize - degreeIndex)) := by
      have hFirst : totalCard - (selectionSize - degreeIndex)
          = degreeIndex + (totalCard - selectionSize) := by omega
      have hSecond : selectionSize - (selectionSize - degreeIndex) = degreeIndex := by omega
      have hSym := Nat.choose_symm (n := degreeIndex + (totalCard - selectionSize))
        (k := degreeIndex) (Nat.le_add_right _ _)
      rw [hFirst, hSecond]
      simpa using hSym
    rw [hChoose, nsmul_eq_mul]
    ring
  · have hLeft : ∀ chosen ∈ (Finset.univ : Finset indexType).powersetCard selectionSize,
        (form.submatrix (Subtype.val : { index // index ∈ chosen } → indexType)
          Subtype.val).charpoly.coeff degreeIndex = 0 := by
      intro chosen hChosen
      have hCard : Fintype.card { index // index ∈ chosen } = selectionSize := by
        simp [Fintype.card_coe, (Finset.mem_powersetCard.mp hChosen).2]
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [Matrix.charpoly_natDegree_eq_dim, hCard]
      exact hDeg
    rw [Finset.sum_congr rfl hLeft, Finset.sum_const_zero]
    have hHigh : form.charpoly.coeff (degreeIndex + (totalCard - selectionSize)) = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [Matrix.charpoly_natDegree_eq_dim]
      omega
    rw [hHigh, mul_zero]

/-- The factorial form of the derivative identity:
`(card − k)! • (sum of block characteristic polynomials) = d^(card − k) (charpoly)`. -/
theorem factorial_smul_subsetCharpolySum (form : Matrix indexType indexType baseRing)
    (selectionSize : ℕ) (hSelectionLe : selectionSize ≤ Fintype.card indexType) :
    (Nat.factorial (Fintype.card indexType - selectionSize)) •
        subsetCharpolySum form selectionSize
      = (Polynomial.derivative)^[Fintype.card indexType - selectionSize] form.charpoly := by
  have hFactorial := congrFun (Polynomial.factorial_smul_hasseDeriv
    (R := baseRing) (k := Fintype.card indexType - selectionSize)) form.charpoly
  rw [subsetCharpolySum_eq_hasseDeriv_charpoly form selectionSize hSelectionLe, ← hFactorial]
  simp

end AbstractMixture

/-! ## Descartes at a level, general degree

The sign argument bounds the VALUE, not the roots: no real-rootedness hypothesis
appears anywhere in this section, and none is needed.  A polynomial whose Taylor
coefficients at `shift` alternate in sign, with a strictly positive top one,
cannot vanish anywhere strictly below `shift`. -/

section DescartesAtLevel

/-- **The sign argument.**  If the coefficients of `target` alternate in sign up to
`degreeBound`, with the top one strictly positive, then `(−1)^degreeBound · target`
is strictly positive at every negative level.  Rewriting term by term,
`(−1)^degreeBound · c_j · x^j = ((−1)^(degreeBound−j) c_j) · (−x)^j`, and every
factor on the right is nonnegative with the top one strictly positive. -/
theorem sign_mul_eval_pos_of_neg_of_alternatingCoeffs {target : Polynomial ℝ}
    {degreeBound : ℕ} {level : ℝ} (hdegree : target.natDegree ≤ degreeBound)
    (hlevel : level < 0) (hleading : 0 < target.coeff degreeBound)
    (hsigns : ∀ index : ℕ, 0 ≤ (-1 : ℝ) ^ (degreeBound - index) * target.coeff index) :
    0 < (-1 : ℝ) ^ degreeBound * target.eval level := by
  have hexpand : target.eval level
      = ∑ index ∈ Finset.range (degreeBound + 1), target.coeff index * level ^ index :=
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdegree) level
  have hterm : ∀ index ∈ Finset.range (degreeBound + 1),
      (-1 : ℝ) ^ degreeBound * (target.coeff index * level ^ index)
        = ((-1 : ℝ) ^ (degreeBound - index) * target.coeff index) * (-level) ^ index := by
    intro index hindex
    have hle : index ≤ degreeBound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hindex)
    have hsplit : (-1 : ℝ) ^ (degreeBound - index) * (-1 : ℝ) ^ index
        = (-1 : ℝ) ^ degreeBound := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [neg_pow, ← hsplit]
    ring
  rw [hexpand, Finset.mul_sum, Finset.sum_congr rfl hterm]
  refine Finset.sum_pos' (fun index _ => ?_) ⟨degreeBound, Finset.self_mem_range_succ _, ?_⟩
  · exact mul_nonneg (hsigns index) (pow_nonneg (by linarith) index)
  · have hzero : degreeBound - degreeBound = 0 := Nat.sub_self degreeBound
    rw [hzero, pow_zero, one_mul]
    exact mul_pos hleading (pow_pos (by linarith) degreeBound)

/-- **THE DICTIONARY, abstract.**  If the Taylor coefficients of `target` at
`shift` alternate in sign up to `degreeBound`, with the top one strictly positive,
then `target` has no root strictly below `shift`.  No real-rootedness is assumed:
the conclusion is about the value, and the sign argument delivers it directly. -/
theorem eval_ne_zero_of_lt_of_alternatingTaylorCoeffs {target : Polynomial ℝ}
    {degreeBound : ℕ} {shift level : ℝ} (hdegree : target.natDegree ≤ degreeBound)
    (hlevel : level < shift)
    (hleading : 0 < ((Polynomial.taylor shift) target).coeff degreeBound)
    (hsigns : ∀ index : ℕ,
      0 ≤ (-1 : ℝ) ^ (degreeBound - index) * ((Polynomial.taylor shift) target).coeff index) :
    target.eval level ≠ 0 := by
  have hshiftDegree : ((Polynomial.taylor shift) target).natDegree ≤ degreeBound := by
    rw [Polynomial.natDegree_taylor]; exact hdegree
  have hpos := sign_mul_eval_pos_of_neg_of_alternatingCoeffs
    (target := (Polynomial.taylor shift) target) (degreeBound := degreeBound)
    (level := level - shift) hshiftDegree (by linarith) hleading hsigns
  have hvalue : ((Polynomial.taylor shift) target).eval (level - shift) = target.eval level := by
    rw [Polynomial.taylor_eval]
    congr 1
    ring
  rw [hvalue] at hpos
  intro hzero
  rw [hzero, mul_zero] at hpos
  exact lt_irrefl 0 hpos

end DescartesAtLevel

/-! ## The product mixture over a weighted design -/

section ProductMixture

variable {m k : ℕ}

/-- **THE PRODUCT MIXTURE.**  The characteristic polynomials of the atom sums of
the `k`-subsets, mixed against a PRODUCT weighting — one scalar per atom, one
product per subset.  This is not the volume-sampled mixture of
`Gtz.mixedCharPoly`, and not the tilted mixture of `Gtz.tiltedMixture`: those two
carry the shadow determinant, which vanishes on every linearly dependent subset,
and this one does not.  See `tiltedMixture_eq_sum_weightProduct_mul_det` for the
exact difference. -/
noncomputable def productMixture (design : WeightedDesign m k) (weight : Fin m → ℝ) :
    Polynomial ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
    (∏ atomIndex ∈ selected, weight atomIndex) • (subsetSum design selected).charpoly

/-- The uniform member of the family is the flat sum of the block characteristic
polynomials. -/
theorem productMixture_uniform (design : WeightedDesign m k) :
    productMixture design (fun _ => 1)
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (subsetSum design selected).charpoly := by
  rw [productMixture]
  exact Finset.sum_congr rfl fun selected _ => by rw [Finset.prod_const_one, one_smul]

/-- **THE FAMILY SEPARATION.**  Unfolding the shadow determinant shows the shipped
tilted mixture is the product mixture at weight `tilt · t`, times one factor
`det S_T` per subset.  Since `det S_T = 0` exactly on the linearly dependent
subsets, the determinantal family assigns them zero mass and the product family
does not — which is the whole difference between the two, and the reason neither
dominates the other. -/
theorem tiltedMixture_eq_sum_weightProduct_mul_det (design : WeightedDesign m k)
    (tilt : Fin m → ℝ) :
    tiltedMixture design tilt
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          ((∏ atomIndex ∈ selected, tilt atomIndex * design.weight atomIndex)
            * (subsetSum design selected).det) • (subsetSum design selected).charpoly := by
  rw [tiltedMixture]
  refine Finset.sum_congr rfl fun selected hselected => ?_
  have hcard : selected.card = k := (Finset.mem_powersetCard.mp hselected).2
  rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum design hcard, Finset.prod_mul_distrib]
  ring_nf

/-- The mixture has degree at most the rank: every block is `k × k`. -/
theorem natDegree_productMixture_le (design : WeightedDesign m k) (weight : Fin m → ℝ) :
    (productMixture design weight).natDegree ≤ k := by
  rw [productMixture]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun selected _ => ?_
  refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- The top coefficient of the mixture is the total weight product: every block
characteristic polynomial is monic of degree the rank. -/
theorem coeff_productMixture_rank (design : WeightedDesign m k) (weight : Fin m → ℝ) :
    (productMixture design weight).coeff k
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          ∏ atomIndex ∈ selected, weight atomIndex := by
  rw [productMixture, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun selected _ => ?_
  have hmonic : (subsetSum design selected).charpoly.coeff k = 1 := by
    have hdegree : (subsetSum design selected).charpoly.natDegree = k := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have := (Matrix.charpoly_monic (subsetSum design selected)).coeff_natDegree
    rwa [hdegree] at this
  rw [Polynomial.coeff_smul, smul_eq_mul, hmonic, mul_one]

/-- **The shift to one turns an atom sum into its gap**: `taylor 1 (charpoly N) =
charpoly (N − 1)`, since `scalar (x+1) − N = scalar x − (N − 1)`. -/
theorem taylor_one_charpoly {indexType : Type*} [Fintype indexType] [DecidableEq indexType]
    (form : Matrix indexType indexType ℝ) :
    (Polynomial.taylor (1 : ℝ)) form.charpoly = (form - 1).charpoly := by
  refine Polynomial.funext fun level => ?_
  rw [Polynomial.taylor_eval, Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hshift : (Matrix.scalar indexType) (level + 1) - form
      = (Matrix.scalar indexType) level - (form - 1) := by
    rw [map_add, map_one]
    abel
  rw [hshift]

/-- The shifted mixture is the mixture of the GAP characteristic polynomials. -/
theorem taylor_one_productMixture (design : WeightedDesign m k) (weight : Fin m → ℝ) :
    (Polynomial.taylor (1 : ℝ)) (productMixture design weight)
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (∏ atomIndex ∈ selected, weight atomIndex)
            • (subsetSum design selected - 1).charpoly := by
  rw [productMixture, map_sum]
  exact Finset.sum_congr rfl fun selected _ => by rw [map_smul, taylor_one_charpoly]

/-- **THE COEFFICIENT AGGREGATE.**  The weight-product-weighted total, over the
`k`-subsets, of the `order`-sized principal minors of the gap `S_T − 1`.  At
`order = 0` it is the total weight product; at `order = k` it is the total of the
gap determinants, which at `weight = t` is the shipped `Gtz.rungThreeAggregate`. -/
noncomputable def gapMinorAggregate (design : WeightedDesign m k) (weight : Fin m → ℝ)
    (order : ℕ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
    (∏ atomIndex ∈ selected, weight atomIndex) *
      ∑ inner ∈ (Finset.univ : Finset (Fin k)).powersetCard order,
        ((subsetSum design selected - 1).submatrix
          (Subtype.val : { index // index ∈ inner } → Fin k) Subtype.val).det

/-- The order-zero aggregate is the total weight product. -/
theorem gapMinorAggregate_zero (design : WeightedDesign m k) (weight : Fin m → ℝ) :
    gapMinorAggregate design weight 0
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          ∏ atomIndex ∈ selected, weight atomIndex := by
  rw [gapMinorAggregate]
  refine Finset.sum_congr rfl fun selected _ => ?_
  rw [Finset.powersetCard_zero, Finset.sum_singleton]
  haveI : IsEmpty { index // index ∈ (∅ : Finset (Fin k)) } :=
    ⟨fun slot => absurd slot.2 (Finset.notMem_empty _)⟩
  rw [Matrix.det_isEmpty, mul_one]

/-- The top-order aggregate is the weighted total of the gap determinants. -/
theorem gapMinorAggregate_rank (design : WeightedDesign m k) (weight : Fin m → ℝ) :
    gapMinorAggregate design weight k
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (∏ atomIndex ∈ selected, weight atomIndex) * (subsetSum design selected - 1).det := by
  have hself : (Finset.univ : Finset (Fin k)).powersetCard k
      = {(Finset.univ : Finset (Fin k))} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp⟩
    · intro other hother
      exact Finset.eq_univ_of_card other (by simpa using (Finset.mem_powersetCard.mp hother).2)
  rw [gapMinorAggregate]
  refine Finset.sum_congr rfl fun selected _ => ?_
  rw [hself, Finset.sum_singleton]
  congr 1
  exact Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv Finset.mem_univ) _

/-- **CONSUMING THE SHIPPED `v = t` AGGREGATE.**  At the design's own weights and
top order the general aggregate IS `Gtz.rungThreeAggregate`; nothing is
redefined. -/
theorem gapMinorAggregate_weight_eq_rungThreeAggregate (design : WeightedDesign m k) :
    gapMinorAggregate design design.weight k = rungThreeAggregate design :=
  gapMinorAggregate_rank design design.weight

/-- **THE SIGN HYPOTHESES ARE CONSISTENT.**  Every aggregate is nonnegative as soon
as every `k`-subset dominates: a positive semidefinite gap has nonnegative
principal minors at every order.  This is a firing control on the shape of the
dictionary's hypothesis bundle, NOT a use of it — where the hypothesis is cheapest
to verify the conclusion is already free.  Its content is that the bundle is not
self-contradictory. -/
theorem gapMinorAggregate_nonneg_of_forall_dominates (design : WeightedDesign m k)
    (weight : Fin m → ℝ) (hweight : ∀ atomIndex, 0 ≤ weight atomIndex)
    (hdominates : ∀ selected : Finset (Fin m), selected.card = k → Dominates design selected)
    (order : ℕ) : 0 ≤ gapMinorAggregate design weight order := by
  refine Finset.sum_nonneg fun selected hselected => ?_
  have hcard : selected.card = k := (Finset.mem_powersetCard.mp hselected).2
  refine mul_nonneg (Finset.prod_nonneg fun atomIndex _ => hweight atomIndex) ?_
  exact Finset.sum_nonneg fun inner _ => ((hdominates selected hcard).submatrix _).det_nonneg

/-- **THE DICTIONARY.**  Coefficient `index` of the mixture shifted to one is
`(−1)^(rank − index)` times the aggregate of order `rank − index`.  This is
Mathlib's `Matrix.charpoly_coeff_eq_sum_minors` applied block by block, with the
weight products carried through the sum. -/
theorem coeff_taylor_one_productMixture (design : WeightedDesign m k) (weight : Fin m → ℝ)
    {index : ℕ} (hindex : index ≤ k) :
    ((Polynomial.taylor (1 : ℝ)) (productMixture design weight)).coeff index
      = (-1 : ℝ) ^ (k - index) * gapMinorAggregate design weight (k - index) := by
  rw [taylor_one_productMixture, Polynomial.finsetSum_coeff, gapMinorAggregate, Finset.mul_sum]
  refine Finset.sum_congr rfl fun selected _ => ?_
  rw [Polynomial.coeff_smul, smul_eq_mul]
  have hcard : Fintype.card (Fin k) = k := Fintype.card_fin k
  have hminors := Matrix.charpoly_coeff_eq_sum_minors
    (subsetSum design selected - 1) (k - index) (by omega)
  have hslot : Fintype.card (Fin k) - (k - index) = index := by omega
  rw [hslot] at hminors
  rw [hminors]
  ring

/-- **THE UNCONDITIONAL HALF OF THE MIXTURE ROUTE.**  If every coefficient
aggregate is nonnegative and the order-zero one is strictly positive, the product
mixture has NO root strictly below one.  No real-rootedness hypothesis: the sign
argument of `sign_mul_eval_pos_of_neg_of_alternatingCoeffs` bounds the value. -/
theorem eval_productMixture_ne_zero_of_lt_one (design : WeightedDesign m k)
    (weight : Fin m → ℝ) (hleading : 0 < gapMinorAggregate design weight 0)
    (hsigns : ∀ order : ℕ, order ≤ k → 0 ≤ gapMinorAggregate design weight order)
    {level : ℝ} (hlevel : level < 1) :
    (productMixture design weight).eval level ≠ 0 := by
  refine eval_ne_zero_of_lt_of_alternatingTaylorCoeffs (degreeBound := k) (shift := 1)
    (natDegree_productMixture_le design weight) hlevel ?_ ?_
  · rw [coeff_taylor_one_productMixture design weight (le_refl k), Nat.sub_self, pow_zero,
      one_mul]
    exact hleading
  · intro index
    rcases le_or_gt index k with hle | hgt
    · rw [coeff_taylor_one_productMixture design weight hle, ← mul_assoc, ← pow_add]
      have heven : Even ((k - index) + (k - index)) := ⟨k - index, rfl⟩
      rw [heven.neg_one_pow, one_mul]
      exact hsigns (k - index) (Nat.sub_le _ _)
    · have hzero : ((Polynomial.taylor (1 : ℝ)) (productMixture design weight)).coeff index = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        rw [Polynomial.natDegree_taylor]
        exact lt_of_le_of_lt (natDegree_productMixture_le design weight) hgt
      rw [hzero, mul_zero]

end ProductMixture

/-! ## The derivative identity lands on the shipped chart aggregate -/

section ChartBridge

variable {size rank : ℕ}

/-- **THE DERIVATIVE IDENTITY, ON THE CAMPAIGN'S OWN AGGREGATE.**  The shipped
rung-three aggregate is, up to the sign of the rank, ONE COEFFICIENT of a Hasse
derivative of the characteristic polynomial of the chart gap.  Composing
`subsetCharpolySum_eq_hasseDeriv_charpoly` at the chart with the shipped minor
reading `Gtz.rungThreeAggregate_eq_sum_det_chartGapMinor`, the abstract identity
becomes a statement about the design.  General in `(size, rank)`. -/
theorem rungThreeAggregate_eq_coeff_hasseDeriv_charpoly_chartGapMatrix
    (design : WeightedDesign size rank) (hrank : rank ≤ size) :
    rungThreeAggregate design
      = (-1 : ℝ) ^ rank *
        (Polynomial.hasseDeriv (size - rank) (chartGapMatrix design).charpoly).coeff 0 := by
  have hcard : Fintype.card (Fin size) = size := Fintype.card_fin size
  have hidentity := subsetCharpolySum_eq_hasseDeriv_charpoly (chartGapMatrix design) rank
    (by rw [hcard]; exact hrank)
  rw [hcard] at hidentity
  have hcoeff : (subsetCharpolySum (chartGapMatrix design) rank).coeff 0
      = (-1 : ℝ) ^ rank * rungThreeAggregate design := by
    rw [subsetCharpolySum, Polynomial.finsetSum_coeff,
      rungThreeAggregate_eq_sum_det_chartGapMinor, Finset.mul_sum]
    refine Finset.sum_congr rfl fun selected hselected => ?_
    have hblockCard : Fintype.card { index // index ∈ selected } = rank := by
      simp [Fintype.card_coe, (Finset.mem_powersetCard.mp hselected).2]
    rw [coeff_zero_charpoly, hblockCard]
  rw [hidentity] at hcoeff
  have heven : Even (rank + rank) := ⟨rank, rfl⟩
  rw [hcoeff, ← mul_assoc, ← pow_add, heven.neg_one_pow, one_mul]

end ChartBridge

/-! ## The pigeonhole, named, and the route assembled -/

section MixtureRoute

variable {m k : ℕ} [Nonempty (Fin k)]

/-- **The interlacing conclusion for the PRODUCT family, at a level.**  If the
product mixture at a strictly positive weighting has no root strictly below
`level`, some `k`-subset's least eigenvalue is at least `level`.  Stated root-free,
in the repository's convention (`Gtz.DoesMixtureInterlaceAt`), so that no
existence-of-a-real-root claim is smuggled in.

Not mechanized, and not mechanizable from what Mathlib carries: the two published
steps behind it are real stability of `det(x·1 + diag(1/v)·y − W)` under the
Borcea–Brändén preservers, which gives real-rootedness of the extracted
`y`-coefficient, and the Marcus–Spielman–Srivastava interlacing-family leaf bound.
Mathlib has neither real-stable polynomials nor interlacing families. -/
def DoesProductMixtureInterlaceAt (m k : ℕ) [Nonempty (Fin k)] (level : ℝ) : Prop :=
  ∀ (design : WeightedDesign m k) (weight : Fin m → ℝ), (∀ atomIndex, 0 < weight atomIndex) →
    (∀ below : ℝ, below < level → (productMixture design weight).eval below ≠ 0) →
      ∃ selected : Finset (Fin m), selected.card = k
        ∧ level ≤ lambdaMinMat (subsetSum design selected)

/-- **THE LEVEL-ONE INSTANCE IS AN IFF-TRAP.**  `DoesProductMixtureInterlaceAt m k
1` follows from `GtzWeighted m k` outright, because at level one the root
hypothesis is discarded and the conclusion is domination restated
(`Gtz.dominates_iff_one_le_lambdaMinMat`).  The same holds of the volume-sampled
family (`Gtz.doesMixtureInterlaceAtOne_of_gtzWeighted`).  All the independent
content of the predicate sits at levels strictly below one. -/
theorem doesProductMixtureInterlaceAtOne_of_gtzWeighted (hgtz : GtzWeighted m k) :
    DoesProductMixtureInterlaceAt m k 1 := by
  intro design _ _ _
  obtain ⟨selected, hcard, hdominates⟩ := hgtz design
  exact ⟨selected, hcard, (dominates_iff_one_le_lambdaMinMat design selected).mp hdominates⟩

/-- **THE ROUTE, assembled at general `(size, rank)`.**  Nonnegative coefficient
aggregates plus the pigeonhole give a dominating `k`-subset.  The first hypothesis
is discharged unconditionally by `eval_productMixture_ne_zero_of_lt_one`; the
second is the named `Prop` and is the only thing consumed beyond it. -/
theorem exists_dominates_of_productMixtureInterlaces
    (hinterlace : DoesProductMixtureInterlaceAt m k 1) (design : WeightedDesign m k)
    (weight : Fin m → ℝ) (hweight : ∀ atomIndex, 0 < weight atomIndex)
    (hleading : 0 < gapMinorAggregate design weight 0)
    (hsigns : ∀ order : ℕ, order ≤ k → 0 ≤ gapMinorAggregate design weight order) :
    ∃ selected : Finset (Fin m), selected.card = k ∧ Dominates design selected := by
  obtain ⟨selected, hcard, hlevel⟩ := hinterlace design weight hweight
    (fun below hbelow => eval_productMixture_ne_zero_of_lt_one design weight hleading hsigns
      hbelow)
  exact ⟨selected, hcard, (dominates_iff_one_le_lambdaMinMat design selected).mpr hlevel⟩

/-- The `(6,3)` reading of the route: three aggregates and the pigeonhole. -/
theorem exists_dominates_sixThree_of_productMixtureInterlaces
    (hinterlace : DoesProductMixtureInterlaceAt 6 3 1) (design : WeightedDesign 6 3)
    (weight : Fin 6 → ℝ) (hweight : ∀ atomIndex, 0 < weight atomIndex)
    (hleading : 0 < gapMinorAggregate design weight 0)
    (hsigns : ∀ order : ℕ, order ≤ 3 → 0 ≤ gapMinorAggregate design weight order) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected :=
  exists_dominates_of_productMixtureInterlaces hinterlace design weight hweight hleading hsigns

end MixtureRoute

/-! ## The tie obstruction: no positive weighting certifies a partial tie -/

section TieObstruction

variable {m k : ℕ}

/-- The mixture at a level is the weighted total of the shifted block
determinants. -/
theorem eval_productMixture (design : WeightedDesign m k) (weight : Fin m → ℝ) (level : ℝ) :
    (productMixture design weight).eval level
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (∏ atomIndex ∈ selected, weight atomIndex)
            * ((Matrix.scalar (Fin k)) level - subsetSum design selected).det := by
  rw [productMixture, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun selected _ => ?_
  rw [Polynomial.eval_smul, Matrix.eval_charpoly, smul_eq_mul]

/-- At zero the mixture is `(−1)^rank` times the weighted total of the atom-sum
determinants — all of which are nonnegative, the atom sums being positive
semidefinite. -/
theorem eval_zero_productMixture (design : WeightedDesign m k) (weight : Fin m → ℝ) :
    (productMixture design weight).eval 0
      = (-1 : ℝ) ^ k * ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (∏ atomIndex ∈ selected, weight atomIndex) * (subsetSum design selected).det := by
  rw [eval_productMixture, Finset.mul_sum]
  refine Finset.sum_congr rfl fun selected _ => ?_
  have hmatrix : (Matrix.scalar (Fin k)) (0 : ℝ) - subsetSum design selected
      = -subsetSum design selected := by
    rw [map_zero, zero_sub]
  rw [hmatrix, Matrix.det_neg, Fintype.card_fin]
  ring

/-- At one the mixture is `(−1)^rank` times the weighted total of the GAP
determinants. -/
theorem eval_one_productMixture (design : WeightedDesign m k) (weight : Fin m → ℝ) :
    (productMixture design weight).eval 1
      = (-1 : ℝ) ^ k * ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (∏ atomIndex ∈ selected, weight atomIndex)
            * (subsetSum design selected - 1).det := by
  rw [eval_productMixture, Finset.mul_sum]
  refine Finset.sum_congr rfl fun selected _ => ?_
  have hmatrix : (Matrix.scalar (Fin k)) (1 : ℝ) - subsetSum design selected
      = -(subsetSum design selected - 1) := by
    rw [map_one]
    abel
  rw [hmatrix, Matrix.det_neg, Fintype.card_fin]
  ring

/-- **THE PARTIAL-TIE PROFILE.**  No `k`-subset has a positive gap determinant and
at least one has a strictly negative one.  A design with a strictly dominating
subset violates the first clause (a positive definite gap has positive
determinant); a TOTAL tie, where every gap determinant vanishes, violates the
second.  So this is exactly the intermediate stratum. -/
def IsPartialTie (design : WeightedDesign m k) : Prop :=
  (∀ selected : Finset (Fin m), selected.card = k → (subsetSum design selected - 1).det ≤ 0)
    ∧ ∃ selected : Finset (Fin m), selected.card = k
        ∧ (subsetSum design selected - 1).det < 0

/-- **EVERY DESIGN HAS A NONSINGULAR `k`-SUBSET.**  Composition of two shipped
facts and nothing else: the volume-sampling masses cannot all vanish
(`Gtz.exists_shadowDeterminant_pos`, from `Gtz.sum_shadowDeterminant_eq_one`), and
positive mass forces a nonsingular atom sum
(`Gtz.detSubsetSum_pos_of_shadowDeterminant_pos`).  Geometrically: the atoms span,
because the weighted Parseval sum is the identity.  Stated here only because the
tie obstruction needs the existential form. -/
theorem exists_pos_det_subsetSum (design : WeightedDesign m k) :
    ∃ selected : Finset (Fin m), selected.card = k ∧ 0 < (subsetSum design selected).det := by
  obtain ⟨selected, hselected, hmass⟩ := exists_shadowDeterminant_pos design
  have hcard : selected.card = k := (Finset.mem_powersetCard.mp hselected).2
  exact ⟨selected, hcard, detSubsetSum_pos_of_shadowDeterminant_pos design hcard hmass⟩

/-- **THE TIE OBSTRUCTION.**  At odd rank, on a partial tie carrying at least one
nonsingular atom sum, EVERY strictly positive product weighting puts a root of the
mixture strictly inside `(0,1)`.  Two signs and one intermediate value:
`eval 0 < 0` because atom sums are positive semidefinite so their determinants are
nonnegative and the odd rank flips the total, and `eval 1 > 0` because the same
flip turns the nonpositive gap determinants into a positive total. -/
theorem exists_root_productMixture_lt_one_of_odd (design : WeightedDesign m k)
    (weight : Fin m → ℝ) (hodd : Odd k) (hweight : ∀ atomIndex, 0 < weight atomIndex)
    (htie : IsPartialTie design) :
    ∃ level : ℝ, 0 < level ∧ level < 1 ∧ (productMixture design weight).eval level = 0 := by
  classical
  obtain ⟨hnonpos, tieWitness, htieCard, htieNeg⟩ := htie
  obtain ⟨nonsingularWitness, hnonsingularCard, hnonsingularPos⟩ := exists_pos_det_subsetSum design
  have hprod : ∀ selected : Finset (Fin m), 0 < ∏ atomIndex ∈ selected, weight atomIndex :=
    fun selected => Finset.prod_pos fun atomIndex _ => hweight atomIndex
  have hsign : (-1 : ℝ) ^ k = -1 := hodd.neg_one_pow
  -- value at zero
  have hzeroSum : 0 < ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      (∏ atomIndex ∈ selected, weight atomIndex) * (subsetSum design selected).det := by
    refine Finset.sum_pos' (fun selected _ => ?_) ⟨nonsingularWitness, ?_, ?_⟩
    · exact mul_nonneg (hprod selected).le (posSemidef_subsetSum design selected).det_nonneg
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hnonsingularCard⟩
    · exact mul_pos (hprod nonsingularWitness) hnonsingularPos
  have hbelow : (productMixture design weight).eval 0 < 0 := by
    rw [eval_zero_productMixture, hsign]
    linarith
  -- value at one
  have honeSum : ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      (∏ atomIndex ∈ selected, weight atomIndex) * (subsetSum design selected - 1).det < 0 := by
    have hcompare : ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (∏ atomIndex ∈ selected, weight atomIndex) * (subsetSum design selected - 1).det
          < ∑ _selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k, (0 : ℝ) := by
      refine Finset.sum_lt_sum (fun selected hselected => ?_) ⟨tieWitness, ?_, ?_⟩
      · have hcard : selected.card = k := (Finset.mem_powersetCard.mp hselected).2
        exact mul_nonpos_of_nonneg_of_nonpos (hprod selected).le (hnonpos selected hcard)
      · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, htieCard⟩
      · exact mul_neg_of_pos_of_neg (hprod tieWitness) htieNeg
    simpa using hcompare
  have habove : 0 < (productMixture design weight).eval 1 := by
    rw [eval_one_productMixture, hsign]
    linarith
  -- intermediate value
  have hcontinuous : ContinuousOn (fun level : ℝ => (productMixture design weight).eval level)
      (Set.Icc 0 1) := (productMixture design weight).continuous_aeval.continuousOn
  have hmember : (0 : ℝ) ∈ Set.Icc ((productMixture design weight).eval 0)
      ((productMixture design weight).eval 1) := ⟨hbelow.le, habove.le⟩
  obtain ⟨level, hlevelMem, hlevelValue⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcontinuous hmember
  have hvalue : (productMixture design weight).eval level = 0 := hlevelValue
  refine ⟨level, ?_, ?_, hvalue⟩
  · rcases hlevelMem.1.lt_or_eq with hstrict | hzero
    · exact hstrict
    · rw [← hzero] at hvalue
      rw [hvalue] at hbelow
      exact absurd hbelow (lt_irrefl 0)
  · rcases hlevelMem.2.lt_or_eq with hstrict | hone
    · exact hstrict
    · rw [hone] at hvalue
      rw [hvalue] at habove
      exact absurd habove (lt_irrefl 0)

/-- **THE PRODUCT ANALOGUE OF `Gtz.EcpStar`.**  For every design there is a
strictly positive product weighting whose mixture has no root strictly below one.
This is the predicate a formula `weight(design)` would have to witness. -/
def HasProductMixtureCertificate (m k : ℕ) : Prop :=
  ∀ design : WeightedDesign m k, ∃ weight : Fin m → ℝ, (∀ atomIndex, 0 < weight atomIndex)
    ∧ ∀ level : ℝ, level < 1 → (productMixture design weight).eval level ≠ 0

/-- **THE REFUTATION RECORD.**  A partial tie at odd rank with a nonsingular atom
sum admits NO certificate: every strictly positive weighting fails, so no formula
`weight(design)` can work there.  This is the general form of the campaign's
`(6,3)` finding — at the uniform-weight `ℚ(√5)` tie twelve of the twenty gap
determinants vanish, eight are strictly negative and none is positive, so the
hypotheses hold and the certificate cannot exist.

The hypothesis bundle is stated as a hypothesis, not asserted: no design
satisfying it is mechanized in this repository (the `ℚ(√5)` tie is not), so the
in-kernel non-vacuity of this statement is OPEN.  A TOTAL tie does not satisfy it
— `Gtz.tetraDesign` has every gap determinant zero, and there the mixture does
have a certificate — which is why the strict clause of `IsPartialTie` carries
weight. -/
theorem not_hasProductMixtureCertificate_of_partialTie (design : WeightedDesign m k)
    (hodd : Odd k) (htie : IsPartialTie design) :
    ¬ ∃ weight : Fin m → ℝ, (∀ atomIndex, 0 < weight atomIndex)
        ∧ ∀ level : ℝ, level < 1 → (productMixture design weight).eval level ≠ 0 := by
  rintro ⟨weight, hweight, hnoRoot⟩
  obtain ⟨level, -, hlevelLt, hlevelRoot⟩ :=
    exists_root_productMixture_lt_one_of_odd design weight hodd hweight htie
  exact hnoRoot level hlevelLt hlevelRoot

/-- The same in the predicate shape: a single partial-tie design at odd rank
refutes the whole certificate predicate at its size. -/
theorem not_hasProductMixtureCertificate_of_exists_partialTie (hodd : Odd k)
    (hwitness : ∃ design : WeightedDesign m k, IsPartialTie design) :
    ¬ HasProductMixtureCertificate m k := by
  rintro hcertificate
  obtain ⟨design, htie⟩ := hwitness
  exact not_hasProductMixtureCertificate_of_partialTie design hodd htie (hcertificate design)

end TieObstruction

end Gtz

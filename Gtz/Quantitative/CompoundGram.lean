/-
# The off-diagonal maximal compound: the cross-bracket layer at general `(size, rank)`

The tree already carries the DIAGONAL Cauchy--Binet reading of a maximal minor of a
Gram matrix, twice over: `Gtz.det_projectionBlock_eq_sq_volume`
(`Gtz/Reduction/MaximalVolume.lean:243`) reads it as a squared volume, and
`Gtz.shadowDeterminant_eq_weightProduct_mul_detSq`
(`Gtz/Reduction/ExchangeInvariant.lean:1129`) factors the weights out of it.  What
it does not carry is the OFF-DIAGONAL one, and that is the whole content of the
compound layer: for two rank-many picks `L`, `R` of a frame `A`,

    det ((A Aᵀ)[L, R])  =  det A_L * det A_R,

so the `C(m,k) x C(m,k)` table of maximal minors of `A Aᵀ` is the OUTER SQUARE of
the bracket vector -- an outer product, hence of rank at most one.  Squaring the
cross law makes it square-root free: the squared cross minor is the product of the
two principal minors, i.e. the Cauchy--Schwarz bound on shadow determinants is an
EQUALITY, and the residual real datum is exactly the SIGN of the cross minor.

Everything below is at general `(size, rank)` over an arbitrary commutative ring
wherever the statement allows it; nothing mentions 6, 3, or any particular cell.

## What lands, and what deliberately does not

LANDS: the cross factorisation `submatrix_mul_transpose_cross`, the cross
determinant `det_submatrix_mul_transpose_cross`, the rank-one compound table
`detCrossTable_eq_vecMulVec` and its design instance
`detCrossTable_projection_eq_vecMulVec`, the square-root-free cross law
`sq_det_submatrix_projection_cross` with its shadow-determinant form, and the
weight-factored sign law `det_submatrix_projection_cross_eq`.

DOES NOT LAND, and the reasons are R6 and utility respectively.

* `det Gram_C = (det A_C)^2` -- the DIAGONAL half of the cross law -- is NOT
  restated.  It is `Gtz.det_projectionBlock_eq_sq_volume`.  Here it is the
  `leftPick = rightPick` case of `det_submatrix_mul_transpose_cross`.

* A `chirotope` DEFINITION is NOT introduced, and this is a judgement rather than
  an oversight.  A definition earns its keep by having a consumer, and the
  measured verdict on the oriented-matroid layer is that it has none: the
  chirotope of a weighted design is a function of the RAW atom directions alone
  (whitening multiplies every bracket by `det(F^{-1/2}) > 0`), so it is
  weight-blind while near-cruxness is weight-driven; a census of about 6.2 million
  exact integer designs found all four reorientation classes of uniform `OM(3,6)`
  reaching the near-crux stratum at essentially equal rates; and every shipped
  `(6,3)` tie is NON-uniform (7 or 8 of the 20 brackets vanish), so the uniform
  classification does not even see the equality locus that boundary condition B2
  forces any exact proof to survive.  The identities below are the reusable part
  of that layer -- they are Gram-level, square-root-free and rank-generic -- and a
  bare chirotope definition on top of them would be clutter.  If a consumer ever
  appears, `det_submatrix_projection_cross_eq` is the theorem it needs: fixing one
  nonvanishing reference pick recovers every bracket sign from the projection form
  alone, because the positive weight factors never interfere.

## Measured scope (measurements, not theorems; recorded for calibration)

Uniform `OM(3,6)` has exactly 4 reorientation classes, of orbit sizes
3840 / 7680 / 11520 / 768 and stabiliser orders 12 / 6 / 4 / 60, together covering
all 23808 labelled uniform chirotopes; `Gtz.icosaDesign` sits in the stabiliser-60
class.  Goodman--Pollack: every rank-3 oriented matroid on at most 8 elements is
realizable, so at `(6,3)` and `(7,3)` the chirotope carries no realizability
obstruction and can only stratify.  These are cited from the campaign's census and
from the literature; nothing below depends on them.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.MaximalVolume
import Gtz.Reduction.ExchangeInvariant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The cross block of a Gram matrix -/

/-- **The cross block of `A Aᵀ` factors.**  The general-ring, general-shape
statement behind every bracket identity: an off-diagonal block of a Gram matrix is
the product of the two selected row blocks.  The DIAGONAL case
(`leftPick = rightPick`, over the reals, at square shape) is the shipped
`Gtz.submatrix_mul_transpose_eq` (`Gtz/LinAlg/ProjectionForm.lean:358`); this is
that lemma with the two picks allowed to differ. -/
theorem submatrix_mul_transpose_cross {Scalar : Type*} [CommRing Scalar]
    {rows cols left right : Type*} [Fintype cols]
    (frame : Matrix rows cols Scalar) (leftPick : left → rows)
    (rightPick : right → rows) :
    (frame * frameᵀ).submatrix leftPick rightPick
      = frame.submatrix leftPick id * (frame.submatrix rightPick id)ᵀ := by
  ext leftIndex rightIndex
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id]

/-- **The cross maximal minor is the product of the two brackets**:
`det ((A Aᵀ)[L, R]) = det A_L * det A_R`, over any commutative ring at any rank.
At `leftPick = rightPick` this is the squared-volume law
`Gtz.det_projectionBlock_eq_sq_volume`, which is why that statement is not
restated here. -/
theorem det_submatrix_mul_transpose_cross {Scalar : Type*} [CommRing Scalar]
    {rows : Type*} (frame : Matrix rows (Fin rank) Scalar)
    (leftPick rightPick : Fin rank → rows) :
    ((frame * frameᵀ).submatrix leftPick rightPick).det
      = (frame.submatrix leftPick id).det * (frame.submatrix rightPick id).det := by
  rw [submatrix_mul_transpose_cross, Matrix.det_mul, Matrix.det_transpose]

/-- **THE COMPOUND IS AN OUTER PRODUCT.**  The whole table of maximal cross minors,
indexed by any enumeration of the picks, is the outer square of the bracket vector.
This is the `Lambda^rank` rank-one statement: any two rows of the table are
proportional, which is what makes the sign of a single reference bracket determine
every other bracket sign. -/
theorem detCrossTable_eq_vecMulVec {Scalar : Type*} [CommRing Scalar]
    {rows picks : Type*} (frame : Matrix rows (Fin rank) Scalar)
    (enumerate : picks → Fin rank → rows) :
    (Matrix.of fun leftPick rightPick =>
        ((frame * frameᵀ).submatrix (enumerate leftPick) (enumerate rightPick)).det)
      = Matrix.vecMulVec (fun pick => (frame.submatrix (enumerate pick) id).det)
          (fun pick => (frame.submatrix (enumerate pick) id).det) := by
  ext leftPick rightPick
  rw [Matrix.of_apply, det_submatrix_mul_transpose_cross, Matrix.vecMulVec_apply]

/-! ## The cross law on a weighted design -/

/-- The compound table of the PROJECTION FORM of a weighted design is the outer
square of the SCALED bracket vector -- the design instance of
`detCrossTable_eq_vecMulVec`.  The scaled bracket is the unscaled one times the
square roots of the selected weights; `det_submatrix_projection_cross_eq` separates
the two factors. -/
theorem detCrossTable_projection_eq_vecMulVec (D : WeightedDesign size rank)
    {picks : Type*} (enumerate : picks → Fin rank → Fin size) :
    (Matrix.of fun leftPick rightPick =>
        ((projectionOfDesign D).submatrix (enumerate leftPick)
          (enumerate rightPick)).det)
      = Matrix.vecMulVec
          (fun pick => ((scaledAtomRows D).submatrix (enumerate pick) id).det)
          (fun pick => ((scaledAtomRows D).submatrix (enumerate pick) id).det) := by
  rw [projectionOfDesign, detCrossTable_eq_vecMulVec]

/-- **THE SQUARE-ROOT-FREE CROSS LAW.**  The square of an off-diagonal maximal minor
of the projection form is the product of the two principal maximal minors.  So the
Cauchy--Schwarz bound relating shadow determinants is an IDENTITY, and the residual
real datum is exactly the SIGN of the cross minor.  No square roots, no eigenvalues,
any `(size, rank)`. -/
theorem sq_det_submatrix_projection_cross (D : WeightedDesign size rank)
    (leftPick rightPick : Fin rank → Fin size) :
    (((projectionOfDesign D).submatrix leftPick rightPick).det) ^ 2
      = ((projectionOfDesign D).submatrix leftPick leftPick).det
        * ((projectionOfDesign D).submatrix rightPick rightPick).det := by
  rw [projectionOfDesign, det_submatrix_mul_transpose_cross,
    det_submatrix_mul_transpose_cross, det_submatrix_mul_transpose_cross]
  ring

/-- The same law on the tree's own score: the squared cross minor is the product of
the two shadow determinants.  Stated multiplicatively to stay division-free. -/
theorem sq_det_submatrix_projection_cross_shadow (D : WeightedDesign size rank)
    {leftSelected rightSelected : Finset (Fin size)}
    (leftPick rightPick : Fin rank → Fin size)
    (hleftInj : Function.Injective leftPick) (hrightInj : Function.Injective rightPick)
    (hleftImage : Finset.image leftPick Finset.univ = leftSelected)
    (hrightImage : Finset.image rightPick Finset.univ = rightSelected) :
    (((projectionOfDesign D).submatrix leftPick rightPick).det) ^ 2
      = shadowDeterminant D leftSelected * shadowDeterminant D rightSelected := by
  rw [shadowDeterminant_eq_det_submatrix D leftPick hleftInj hleftImage,
    shadowDeterminant_eq_det_submatrix D rightPick hrightInj hrightImage,
    sq_det_submatrix_projection_cross]

/-- **BRACKET-SIGN RECOVERY.**  The cross minor of the projection form is the product
of the two atom brackets times a strictly positive weight factor, so it has the SAME
SIGN as the product of the two brackets: the weights never interfere.  Fixing one
reference pick with a nonvanishing bracket therefore recovers every bracket sign from
the projection form alone.  The diagonal case is
`Gtz.shadowDeterminant_eq_weightProduct_mul_detSq`. -/
theorem det_submatrix_projection_cross_eq (D : WeightedDesign size rank)
    (leftPick rightPick : Fin rank → Fin size) :
    ((projectionOfDesign D).submatrix leftPick rightPick).det
      = (∏ index, Real.sqrt (D.weight (leftPick index)))
        * (∏ index, Real.sqrt (D.weight (rightPick index)))
        * ((selectedAtomRows D leftPick).det * (selectedAtomRows D rightPick).det) := by
  rw [projectionOfDesign, det_submatrix_mul_transpose_cross,
    submatrix_scaledAtomRows_eq, submatrix_scaledAtomRows_eq, Matrix.det_mul,
    Matrix.det_mul, sqrtWeightDiagonal, sqrtWeightDiagonal, Matrix.det_diagonal,
    Matrix.det_diagonal]
  ring

/-- The weight factor in the cross law is strictly positive, so the sign statement in
`det_submatrix_projection_cross_eq` is a genuine sign statement and not a vacuous
one.  This is the non-vacuity control for the bracket-sign reading. -/
theorem prod_sqrt_weight_pos (D : WeightedDesign size rank)
    (pick : Fin rank → Fin size) :
    0 < ∏ index, Real.sqrt (D.weight (pick index)) :=
  Finset.prod_pos fun index _ => Real.sqrt_pos.mpr (D.weight_pos (pick index))

end Gtz

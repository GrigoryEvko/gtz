/-
# Past U6: the abstract mirror, the degeneracy classification, and a uniform margin

`Gtz.Quantitative.EqualShareSixThree` closes U6: every equal-share `(6,3)` design
has a triple whose direction Gram has least eigenvalue at least `1/3`.  Three
questions were left open there, and this file settles all three.  Two of the
answers contradict what the campaign expected, so they are stated as headlines
rather than as remarks.

## 1.  The abstract theorem needs no side condition (S3 of the brief)

`EqualShareSixThree` landed the abstract combinatorial core unconditionally but
could only reach the positive-semidefinite conclusion for a triple assumed
COHERENT, and its docstring records the obstruction: the mirror in the form
`det J[K] = -det J[K-complement]`, which it identified with Jacobi's
complementary-minor identity, present in neither this repository nor mathlib.

Jacobi is not needed.  For a symmetric involution blocked as `A`, `B`, `D` the
relations `A^2 + B B^T = 1`, `A B + B D = 0`, `B^T B + D^2 = 1` give

    tr(A^3) = tr A - tr(A B B^T) = tr A + tr(B D B^T)
            = tr A + tr((B^T B) D) = tr A + tr D - tr(D^3),

so `tr(A^3) + tr(D^3) = 0` whenever both blocks are traceless
(`Gtz.trace_cube_add_trace_cube_of_blockRelations`); and the same three relations
give `tr(A^2) - tr(D^2) = |left| - |right|`
(`Gtz.trace_square_sub_trace_square_of_blockRelations`).  A traceless `3 x 3` has
`tr(N^3) = 3 det N`, and a hollow one has `tr(N^2) = 2 sigma` and `det N = 2 P`,
so on a `3-3` split of a hollow symmetric involution the two trace laws ARE the
pen's mirror: `sigma` is preserved and `P` is negated.  No determinant, no
invertible cross block, no factorisation of the projection, and both laws hold at
arbitrary block sizes over an arbitrary commutative ring.

Consequently `Gtz.IsHollowInvolution.exists_posSemidef_twoThirds_shift` holds for
EVERY hollow symmetric involution on `Fin 6`, with no coherence hypothesis and no
realizability hypothesis.  Realizability was never the issue: a hollow symmetric
involution on `Fin 6` is exactly `Gamma - 1` for a unit-norm tight frame of six
vectors in `R^3`, because `M^2 = 1` and `tr M = 0` force `(M + 1)/2` to be a
rank-three projection with constant diagonal `1/2`.  What the proof consumes is
the norm cap, and the norm cap is available abstractly.

## 2.  The tightness guess was wrong, and the true margin is uniform (S1)

The campaign expected `4/9` to be tight on the coplanar locus and asked for a
`delta` vanishing there.  There is no such phenomenon: `4/9` is not tight
anywhere, and

    `Gtz.exists_signFreeTripleResidual_le_two_fifths`

improves the combinatorial core from `4/9` to `2/5`, uniformly, with no
hypothesis beyond nonnegativity and the norm cap `(C2)`.  The gap `2/45` is
absolute.  Two shipped estimates that were already sharp make this free:

* the light branch's exact bound `h <= max (2 r^2) (3 r^2 - 3 r^3)`, and
* the heavy branch's exact bound `h <= max (3 r^2 - 3 r^3) (1 - 5 r^2 + 10 r^4)`
  (`Gtz.sub_le_max_of_heavyBounds`, new here), which is the same endpoint
  argument run at the cap rather than at `4/9`.

The two curves cross at `r^2 = 1/5`, where both equal `2/5` exactly, whereas the
pen's four-case split put the seam at `r^2 = 2/9` — the top of the light branch's
range, the one point where the light bound is `4/9` on the nose — and therefore
threw the margin away.  Moving the seam to the crossing recovers it.  The constant `2/5` is optimal for this method:
`Gtz.signFreeTripleResidual_lightExtremal` and
`Gtz.signFreeTripleResidual_heavyExtremal` exhibit, at `m = 1/5`, a light
triangle `(1/5, 1/5, 0)` and a cap-saturating heavy triangle `(1/5, 1/5, 9/25)`
both sitting at `h = 2/5` on the nose.  That pair is the precise obstruction: no
argument using only the maximum-minimum root, the product floor and the cap can
go below `2/5`.

A second exact fact does the bookkeeping: the cap forces `r <= 1/2`, by the
factorisation `2 r^3 + 3 r^2 - 1 = (2r - 1)(r + 1)^2`
(`Gtz.root_le_half_of_capBound`).  So the heavy branch's range is the sliver
`[1/5, 1/4]` and the two branches between them exhaust `r >= 0`.

The design consequence is `Gtz.exists_dominating_triple_with_margin`: every
equal-share `(6,3)` design has a triple with `lambda_min(Gamma[C]) >= 9/25`, so
`sum_{c in C} g_c g_c^T ⪰ (27/25) 1` — an eight percent margin over domination,
where `(6,3)` before had none.  In particular no equal-share `(6,3)` design
attains the U6 threshold, so the equality locus the campaign asked to classify is
EMPTY: `Gtz.exists_orientedTripleResidual_le_two_fifths`, and the shifted block is
positive DEFINITE (`Gtz.exists_posDef_shift_of_isEqualShare`).  For calibration,
the numerical infimum of `max_C lambda_min(Gamma[C])` over the stratum is about
`0.4122`, so `9/25 = 0.36` covers roughly ninety percent of the distance from
`1/3` to the truth.

## 3.  The degeneracy classification (S2)

`||M[T]|| = 1` — equivalently, one of the two positive-semidefinite compressions
`1 - M[T]`, `1 + M[T]` is singular — holds exactly when `T` or its complement is
degenerate, where a triple is DEGENERATE when its three unit directions are
linearly dependent, i.e. when `det Gamma[T] = 0`.  Since `det Gamma[T] = det(1 + M[T])`
by definition and `det(1 - M[T]) = det Gamma[T-complement]` by the mirror
(`Gtz.IsHollowInvolution.det_one_sub_submatrix_eq_det_one_add_compl`), the
classification is a rewriting of the mirror, and it comes with its scalar face:
the cap `sigma + 2|P| <= 1` is TIGHT at `T` exactly when `T` or its complement is
degenerate (`Gtz.IsHollowInvolution.normCap_eq_one_iff_degenerate`).

The repository keeps no spectra, so `||M[T]|| = 1` is never stated; the two
determinant vanishings say the same thing, given the two shipped
positive-semidefinite compressions.  At the stratum degeneracy is singularity of
the triple's own atom sum, so the classification reads
`Gtz.normCap_eq_one_iff_det_subsetSum_eq_zero`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.Quantitative.EqualShareSixThree
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Quantitative.WeightProductFloor

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## 1. Block relations for a symmetric involution

A symmetric involution compressed along two picks that jointly enumerate the
index type satisfies the three block relations of a `2 x 2` block involution.
Nothing here uses `Fin`, cardinalities or a splitting into two equal halves: the
picks may be into arbitrary types, and the only coupling is the sum-splitting
hypothesis. -/

/-- The upper block relation `A A + B B^T = 1`. -/
theorem upperBlockRelation_of_squareEqOne {index leftSlot rightSlot : Type*} [Fintype index]
    [DecidableEq index] [Fintype leftSlot] [DecidableEq leftSlot] [Fintype rightSlot]
    {invol : Matrix index index ℝ} (hsymmetric : involᵀ = invol) (hsquare : invol * invol = 1)
    {leftPick : leftSlot → index} {rightPick : rightSlot → index}
    (hleftInjective : Function.Injective leftPick)
    (hsplit : ∀ summand : index → ℝ, ∑ position, summand position
      = ∑ slot, summand (leftPick slot) + ∑ slot, summand (rightPick slot)) :
    invol.submatrix leftPick leftPick * invol.submatrix leftPick leftPick
        + invol.submatrix leftPick rightPick * (invol.submatrix leftPick rightPick)ᵀ = 1 := by
  have hcomm : ∀ rowIndex colIndex : index, invol colIndex rowIndex = invol rowIndex colIndex :=
    fun rowIndex colIndex => congrFun (congrFun hsymmetric rowIndex) colIndex
  ext leftRow leftCol
  have hentry : ∑ position, invol (leftPick leftRow) position * invol position (leftPick leftCol)
      = if leftPick leftRow = leftPick leftCol then 1 else 0 := by
    have hproduct := congrFun (congrFun hsquare (leftPick leftRow)) (leftPick leftCol)
    rwa [Matrix.mul_apply, Matrix.one_apply] at hproduct
  have hsum := hsplit fun position =>
    invol (leftPick leftRow) position * invol position (leftPick leftCol)
  rw [hentry] at hsum
  have hcross : ∑ slot, invol (leftPick leftRow) (rightPick slot)
        * invol (leftPick leftCol) (rightPick slot)
      = ∑ slot, invol (leftPick leftRow) (rightPick slot)
        * invol (rightPick slot) (leftPick leftCol) :=
    Finset.sum_congr rfl fun slot _ => by rw [← hcomm (leftPick leftCol) (rightPick slot)]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.one_apply]
  rw [hcross, ← hsum]
  simp only [hleftInjective.eq_iff]

/-- The cross block relation `A B + B D = 0`. -/
theorem crossBlockRelation_of_squareEqOne {index leftSlot rightSlot : Type*} [Fintype index]
    [DecidableEq index] [Fintype leftSlot] [Fintype rightSlot]
    {invol : Matrix index index ℝ} (hsquare : invol * invol = 1)
    {leftPick : leftSlot → index} {rightPick : rightSlot → index}
    (hdisjoint : ∀ (leftIndex : leftSlot) (rightIndex : rightSlot),
      leftPick leftIndex ≠ rightPick rightIndex)
    (hsplit : ∀ summand : index → ℝ, ∑ position, summand position
      = ∑ slot, summand (leftPick slot) + ∑ slot, summand (rightPick slot)) :
    invol.submatrix leftPick leftPick * invol.submatrix leftPick rightPick
        + invol.submatrix leftPick rightPick * invol.submatrix rightPick rightPick = 0 := by
  ext leftRow rightCol
  have hentry : ∑ position, invol (leftPick leftRow) position * invol position (rightPick rightCol)
      = if leftPick leftRow = rightPick rightCol then 1 else 0 := by
    have hproduct := congrFun (congrFun hsquare (leftPick leftRow)) (rightPick rightCol)
    rwa [Matrix.mul_apply, Matrix.one_apply] at hproduct
  have hsum := hsplit fun position =>
    invol (leftPick leftRow) position * invol position (rightPick rightCol)
  rw [hentry, if_neg (hdisjoint leftRow rightCol)] at hsum
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.zero_apply]
  rw [← hsum]

/-- The lower block relation `B^T B + D D = 1`. -/
theorem lowerBlockRelation_of_squareEqOne {index leftSlot rightSlot : Type*} [Fintype index]
    [DecidableEq index] [Fintype leftSlot] [Fintype rightSlot] [DecidableEq rightSlot]
    {invol : Matrix index index ℝ} (hsymmetric : involᵀ = invol) (hsquare : invol * invol = 1)
    {leftPick : leftSlot → index} {rightPick : rightSlot → index}
    (hrightInjective : Function.Injective rightPick)
    (hsplit : ∀ summand : index → ℝ, ∑ position, summand position
      = ∑ slot, summand (leftPick slot) + ∑ slot, summand (rightPick slot)) :
    (invol.submatrix leftPick rightPick)ᵀ * invol.submatrix leftPick rightPick
        + invol.submatrix rightPick rightPick * invol.submatrix rightPick rightPick = 1 := by
  have hcomm : ∀ rowIndex colIndex : index, invol colIndex rowIndex = invol rowIndex colIndex :=
    fun rowIndex colIndex => congrFun (congrFun hsymmetric rowIndex) colIndex
  ext rightRow rightCol
  have hentry : ∑ position,
        invol (rightPick rightRow) position * invol position (rightPick rightCol)
      = if rightPick rightRow = rightPick rightCol then 1 else 0 := by
    have hproduct := congrFun (congrFun hsquare (rightPick rightRow)) (rightPick rightCol)
    rwa [Matrix.mul_apply, Matrix.one_apply] at hproduct
  have hsum := hsplit fun position =>
    invol (rightPick rightRow) position * invol position (rightPick rightCol)
  rw [hentry] at hsum
  have hcross : ∑ slot, invol (leftPick slot) (rightPick rightRow)
        * invol (leftPick slot) (rightPick rightCol)
      = ∑ slot, invol (rightPick rightRow) (leftPick slot)
        * invol (leftPick slot) (rightPick rightCol) :=
    Finset.sum_congr rfl fun slot _ => by rw [hcomm (rightPick rightRow) (leftPick slot)]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.one_apply]
  rw [hcross, ← hsum]
  simp only [hrightInjective.eq_iff]

/-! ## 2. The two trace laws

These are the whole mirror.  Both hold over an arbitrary commutative ring at
arbitrary block sizes; neither mentions a determinant, a spectrum, or an
invertibility hypothesis on the cross block. -/

/-- **THE CUBIC TRACE LAW.**  A symmetric involution's two traceless diagonal
blocks have opposite cube traces.  The pen's mirror `P_(C-complement) = -P_C` is
this identity read through `tr(N^3) = 3 det N` at size three. -/
theorem trace_cube_add_trace_cube_of_blockRelations {ring : Type*} [CommRing ring]
    {leftSlot rightSlot : Type*} [Fintype leftSlot] [Fintype rightSlot]
    [DecidableEq leftSlot] [DecidableEq rightSlot]
    {upperBlock : Matrix leftSlot leftSlot ring} {crossBlock : Matrix leftSlot rightSlot ring}
    {lowerBlock : Matrix rightSlot rightSlot ring}
    (hupper : upperBlock * upperBlock + crossBlock * crossBlockᵀ = 1)
    (hcross : upperBlock * crossBlock + crossBlock * lowerBlock = 0)
    (hlower : crossBlockᵀ * crossBlock + lowerBlock * lowerBlock = 1)
    (htraceUpper : upperBlock.trace = 0) (htraceLower : lowerBlock.trace = 0) :
    (upperBlock * upperBlock * upperBlock).trace
      + (lowerBlock * lowerBlock * lowerBlock).trace = 0 := by
  have hupperSquare : upperBlock * upperBlock = 1 - crossBlock * crossBlockᵀ := by
    rw [← hupper]; abel
  have hlowerCross : crossBlockᵀ * crossBlock = 1 - lowerBlock * lowerBlock := by
    rw [← hlower]; abel
  have hcrossNeg : upperBlock * crossBlock = -(crossBlock * lowerBlock) := by
    rw [eq_neg_iff_add_eq_zero]; exact hcross
  have hcubeUpper : upperBlock * upperBlock * upperBlock
      = upperBlock + crossBlock * lowerBlock * crossBlockᵀ :=
    calc upperBlock * upperBlock * upperBlock
        = upperBlock * (upperBlock * upperBlock) := by rw [mul_assoc]
      _ = upperBlock * (1 - crossBlock * crossBlockᵀ) := by rw [hupperSquare]
      _ = upperBlock - upperBlock * crossBlock * crossBlockᵀ := by
            rw [mul_sub, mul_one, Matrix.mul_assoc]
      _ = upperBlock + crossBlock * lowerBlock * crossBlockᵀ := by
            rw [hcrossNeg, Matrix.neg_mul, sub_neg_eq_add]
  have htraceCross : (crossBlock * lowerBlock * crossBlockᵀ).trace
      = -(lowerBlock * lowerBlock * lowerBlock).trace :=
    calc (crossBlock * lowerBlock * crossBlockᵀ).trace
        = (crossBlockᵀ * (crossBlock * lowerBlock)).trace :=
          Matrix.trace_mul_comm (crossBlock * lowerBlock) crossBlockᵀ
      _ = (crossBlockᵀ * crossBlock * lowerBlock).trace := by rw [Matrix.mul_assoc]
      _ = ((1 - lowerBlock * lowerBlock) * lowerBlock).trace := by rw [hlowerCross]
      _ = (lowerBlock - lowerBlock * lowerBlock * lowerBlock).trace := by rw [sub_mul, one_mul]
      _ = -(lowerBlock * lowerBlock * lowerBlock).trace := by
            rw [Matrix.trace_sub, htraceLower]; ring
  rw [hcubeUpper, Matrix.trace_add, htraceUpper, htraceCross]
  ring

/-- **THE QUADRATIC TRACE LAW.**  A symmetric involution's two diagonal blocks
have square traces differing by the difference of the block sizes.  At a balanced
split this is the pen's `sigma_(C-complement) = sigma_C`, obtained without the
row law and without any hypothesis on the traces. -/
theorem trace_square_sub_trace_square_of_blockRelations {ring : Type*} [CommRing ring]
    {leftSlot rightSlot : Type*} [Fintype leftSlot] [Fintype rightSlot]
    [DecidableEq leftSlot] [DecidableEq rightSlot]
    {upperBlock : Matrix leftSlot leftSlot ring} {crossBlock : Matrix leftSlot rightSlot ring}
    {lowerBlock : Matrix rightSlot rightSlot ring}
    (hupper : upperBlock * upperBlock + crossBlock * crossBlockᵀ = 1)
    (hlower : crossBlockᵀ * crossBlock + lowerBlock * lowerBlock = 1) :
    (upperBlock * upperBlock).trace - (lowerBlock * lowerBlock).trace
      = (Fintype.card leftSlot : ring) - (Fintype.card rightSlot : ring) := by
  have hupperTrace : (upperBlock * upperBlock).trace + (crossBlock * crossBlockᵀ).trace
      = (Fintype.card leftSlot : ring) := by
    rw [← Matrix.trace_add, hupper, Matrix.trace_one]
  have hlowerTrace : (crossBlockᵀ * crossBlock).trace + (lowerBlock * lowerBlock).trace
      = (Fintype.card rightSlot : ring) := by
    rw [← Matrix.trace_add, hlower, Matrix.trace_one]
  have hswap : (crossBlock * crossBlockᵀ).trace = (crossBlockᵀ * crossBlock).trace :=
    Matrix.trace_mul_comm crossBlock crossBlockᵀ
  rw [← hupperTrace, ← hlowerTrace, hswap]
  ring

/-! ## 3. The hollow `3 x 3` block, traced

`tr(N) = 0`, `tr(N^2) = 2 sigma`, `tr(N^3) = 6 P`.  The last two are what turn the
two trace laws into statements about `sigma` and `P`. -/

theorem trace_hollowMatrixThree (edgeFirst edgeSecond edgeThird : ℝ) :
    (hollowMatrixThree edgeFirst edgeSecond edgeThird).trace = 0 := by
  simp [hollowMatrixThree, Matrix.trace_fin_three]

theorem trace_square_hollowMatrixThree (edgeFirst edgeSecond edgeThird : ℝ) :
    (hollowMatrixThree edgeFirst edgeSecond edgeThird
        * hollowMatrixThree edgeFirst edgeSecond edgeThird).trace
      = 2 * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2) := by
  simp [hollowMatrixThree, Matrix.trace_fin_three]
  ring

theorem trace_cube_hollowMatrixThree (edgeFirst edgeSecond edgeThird : ℝ) :
    (hollowMatrixThree edgeFirst edgeSecond edgeThird
        * hollowMatrixThree edgeFirst edgeSecond edgeThird
        * hollowMatrixThree edgeFirst edgeSecond edgeThird).trace
      = 6 * (edgeFirst * edgeSecond * edgeThird) := by
  simp [hollowMatrixThree, Matrix.trace_fin_three]
  ring

/-! ## 4. The abstract mirror on `Fin 6`

Three distinct indices and a bijective completion give a `3-3` split; the block
relations then hold, and the two trace laws read off `sigma` and `P`. -/

/-- Three pairwise distinct values enumerate injectively. -/
theorem injective_three_of_ne {carrier : Type*} {firstValue secondValue thirdValue : carrier}
    (hfirstSecond : firstValue ≠ secondValue) (hfirstThird : firstValue ≠ thirdValue)
    (hsecondThird : secondValue ≠ thirdValue) :
    Function.Injective ![firstValue, secondValue, thirdValue] := by
  intro leftSlot rightSlot hvalue
  fin_cases leftSlot <;> fin_cases rightSlot <;>
    first
      | rfl
      | exact absurd hvalue (by assumption)
      | exact absurd hvalue.symm (by assumption)

/-- Splitting a sum over `Fin 6` along a `3-3` enumeration. -/
theorem sum_split_of_bijective_six {additive : Type*} [AddCommMonoid additive]
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    (summand : Fin 6 → additive) :
    ∑ position, summand position
      = ∑ slot, summand (![first, second, third] slot)
        + ∑ slot, summand (![fourth, fifth, sixth] slot) := by
  rw [← Fintype.sum_bijective ![first, second, third, fourth, fifth, sixth] hbijective
    (fun slot => summand (![first, second, third, fourth, fifth, sixth] slot)) summand
    (fun _ => rfl)]
  simp [Fin.sum_univ_six, Fin.sum_univ_three, add_assoc]

namespace IsHollowInvolution

variable {invol : Matrix (Fin 6) (Fin 6) ℝ}

/-- The three pairwise distinctness facts a `3-3` split's right half carries. -/
theorem ne_of_bijective_six {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    {leftSlot rightSlot : Fin 6} (hslot : leftSlot ≠ rightSlot) :
    ![first, second, third, fourth, fifth, sixth] leftSlot
      ≠ ![first, second, third, fourth, fifth, sixth] rightSlot :=
  fun hvalue => hslot (hbijective.1 hvalue)

/-- **THE ABSTRACT MIRROR, `sigma` HALF.**  On a `3-3` split of a hollow symmetric
involution the two triangles carry the same square sum. -/
theorem tripleSigma_compl_eq (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    invol fourth fifth ^ 2 + invol fourth sixth ^ 2 + invol fifth sixth ^ 2
      = invol first second ^ 2 + invol first third ^ 2 + invol second third ^ 2 := by
  have hsplit := sum_split_of_bijective_six (additive := ℝ) hbijective
  have hleftInjective : Function.Injective ![first, second, third] :=
    injective_three_of_ne (ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 1))
      (ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 2))
      (ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 2))
  have hrightInjective : Function.Injective ![fourth, fifth, sixth] :=
    injective_three_of_ne (ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 4))
      (ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 5))
      (ne_of_bijective_six hbijective (by decide : (4 : Fin 6) ≠ 5))
  have hupper := upperBlockRelation_of_squareEqOne hinvol.symmetric hinvol.square_eq_one
    hleftInjective hsplit
  have hlower := lowerBlockRelation_of_squareEqOne hinvol.symmetric hinvol.square_eq_one
    hrightInjective hsplit
  have hleftBlock := hinvol.submatrix_three_eq_hollowMatrixThree first second third
  have hrightBlock := hinvol.submatrix_three_eq_hollowMatrixThree fourth fifth sixth
  have htrace := trace_square_sub_trace_square_of_blockRelations hupper hlower
  rw [hleftBlock, hrightBlock, trace_square_hollowMatrixThree, trace_square_hollowMatrixThree]
    at htrace
  simp only [Fintype.card_fin] at htrace
  linarith

/-- **THE ABSTRACT MIRROR, `P` HALF.**  On a `3-3` split of a hollow symmetric
involution the two oriented triangle products are negatives.  This is what
`Gtz.Quantitative.EqualShareSixThree` could not reach; the proof is the cubic
trace law, and it needs neither Jacobi's identity nor an invertible cross
block. -/
theorem tripleProduct_compl_eq_neg (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    invol fourth fifth * invol fourth sixth * invol fifth sixth
      = -(invol first second * invol first third * invol second third) := by
  have hsplit := sum_split_of_bijective_six (additive := ℝ) hbijective
  have hleftInjective : Function.Injective ![first, second, third] :=
    injective_three_of_ne (ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 1))
      (ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 2))
      (ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 2))
  have hrightInjective : Function.Injective ![fourth, fifth, sixth] :=
    injective_three_of_ne (ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 4))
      (ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 5))
      (ne_of_bijective_six hbijective (by decide : (4 : Fin 6) ≠ 5))
  have hdisjoint : ∀ leftSlot rightSlot : Fin 3,
      ![first, second, third] leftSlot ≠ ![fourth, fifth, sixth] rightSlot := by
    intro leftSlot rightSlot
    fin_cases leftSlot <;> fin_cases rightSlot <;>
      first
        | exact ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 3)
        | exact ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 4)
        | exact ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 5)
        | exact ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 3)
        | exact ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 4)
        | exact ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 5)
        | exact ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 3)
        | exact ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 4)
        | exact ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 5)
  have hupper := upperBlockRelation_of_squareEqOne hinvol.symmetric hinvol.square_eq_one
    hleftInjective hsplit
  have hcross := crossBlockRelation_of_squareEqOne hinvol.square_eq_one hdisjoint hsplit
  have hlower := lowerBlockRelation_of_squareEqOne hinvol.symmetric hinvol.square_eq_one
    hrightInjective hsplit
  have hleftBlock := hinvol.submatrix_three_eq_hollowMatrixThree first second third
  have hrightBlock := hinvol.submatrix_three_eq_hollowMatrixThree fourth fifth sixth
  have htraceUpper : (invol.submatrix ![first, second, third] ![first, second, third]).trace = 0 := by
    rw [hleftBlock, trace_hollowMatrixThree]
  have htraceLower :
      (invol.submatrix ![fourth, fifth, sixth] ![fourth, fifth, sixth]).trace = 0 := by
    rw [hrightBlock, trace_hollowMatrixThree]
  have htrace := trace_cube_add_trace_cube_of_blockRelations hupper hcross hlower htraceUpper
    htraceLower
  rw [hleftBlock, hrightBlock, trace_cube_hollowMatrixThree, trace_cube_hollowMatrixThree]
    at htrace
  linarith

/-- On either side of a `3-3` split the oriented product is nonnegative — the
coherent side of the mirror pair, abstractly. -/
theorem exists_nonneg_tripleProduct_of_split (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    0 ≤ invol first second * invol first third * invol second third
      ∨ 0 ≤ invol fourth fifth * invol fourth sixth * invol fifth sixth := by
  rcases le_or_gt 0 (invol first second * invol first third * invol second third) with
    hnonneg | hnegative
  · exact Or.inl hnonneg
  · exact Or.inr (by rw [hinvol.tripleProduct_compl_eq_neg hbijective]; linarith)

end IsHollowInvolution

/-! ## 5. The degeneracy classification

A triple is DEGENERATE when `det Gamma[T] = det(1 + M[T])` vanishes — for a design
this says the three unit directions are linearly dependent, i.e. coplanar.  The
mirror identifies `det(1 - M[T])` with the complement's `det Gamma`, so the two
positive-semidefinite compressions of the involution sandwich are singular
exactly at the two sides of the split, and the cap is tight exactly when one of
them is. -/

namespace IsHollowInvolution

variable {invol : Matrix (Fin 6) (Fin 6) ℝ}

/-- **THE DEGENERACY TRANSFER.**  The lower compression's determinant at a triple
IS the upper compression's determinant at the complementary triple. -/
theorem det_one_sub_submatrix_eq_det_one_add_compl (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - invol.submatrix ![first, second, third] ![first, second, third]).det
      = ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        + invol.submatrix ![fourth, fifth, sixth] ![fourth, fifth, sixth]).det := by
  have hsigma := hinvol.tripleSigma_compl_eq hbijective
  have hproduct := hinvol.tripleProduct_compl_eq_neg hbijective
  rw [hinvol.submatrix_three_eq_hollowMatrixThree first second third,
    hinvol.submatrix_three_eq_hollowMatrixThree fourth fifth sixth,
    ← one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ),
    show hollowMatrixThree (invol first second) (invol first third) (invol second third)
      = hollowSymmetricThree (invol first second) (invol first third) (invol second third) from rfl,
    show hollowMatrixThree (invol fourth fifth) (invol fourth sixth) (invol fifth sixth)
      = hollowSymmetricThree (invol fourth fifth) (invol fourth sixth) (invol fifth sixth) from rfl,
    det_smul_one_sub_hollowSymmetricThree, det_smul_one_add_hollowSymmetricThree]
  rw [hsigma, hproduct]
  ring

/-- **THE CAP'S EQUALITY LOCUS.**  `sigma_T + 2|P_T| = 1` exactly when `T` or its
complement is degenerate.  Equivalently, since both compressions of the
involution sandwich are positive semidefinite, the operator norm of `M[T]` reaches
one exactly on the degenerate locus — which is the statement the campaign wanted,
written without spectra. -/
theorem normCap_eq_one_iff_degenerate (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    invol first second ^ 2 + invol first third ^ 2 + invol second third ^ 2
        + 2 * |invol first second * invol first third * invol second third| = 1
      ↔ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
            + invol.submatrix ![first, second, third] ![first, second, third]).det = 0
        ∨ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
            + invol.submatrix ![fourth, fifth, sixth] ![fourth, fifth, sixth]).det = 0 := by
  have hfirstSecond : first ≠ second :=
    ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 1)
  have hfirstThird : first ≠ third :=
    ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 2)
  have hsecondThird : second ≠ third :=
    ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 2)
  have hcapScalar := hinvol.normCap_triple hfirstSecond hfirstThird hsecondThird
  have hupperDet : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      + invol.submatrix ![first, second, third] ![first, second, third]).det
      = 1 - (invol first second ^ 2 + invol first third ^ 2 + invol second third ^ 2)
        + 2 * (invol first second * invol first third * invol second third) := by
    rw [hinvol.submatrix_three_eq_hollowMatrixThree first second third,
      ← one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ),
      show hollowMatrixThree (invol first second) (invol first third) (invol second third)
        = hollowSymmetricThree (invol first second) (invol first third)
          (invol second third) from rfl, det_smul_one_add_hollowSymmetricThree]
    ring
  have hlowerDet : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      + invol.submatrix ![fourth, fifth, sixth] ![fourth, fifth, sixth]).det
      = 1 - (invol first second ^ 2 + invol first third ^ 2 + invol second third ^ 2)
        - 2 * (invol first second * invol first third * invol second third) := by
    rw [← hinvol.det_one_sub_submatrix_eq_det_one_add_compl hbijective,
      hinvol.submatrix_three_eq_hollowMatrixThree first second third,
      ← one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ),
      show hollowMatrixThree (invol first second) (invol first third) (invol second third)
        = hollowSymmetricThree (invol first second) (invol first third)
          (invol second third) from rfl, det_smul_one_sub_hollowSymmetricThree]
    ring
  rw [hupperDet, hlowerDet]
  rcases abs_cases (invol first second * invol first third * invol second third) with
    ⟨habs, hsign⟩ | ⟨habs, hsign⟩ <;> rw [habs] at hcapScalar ⊢
  · exact ⟨fun htight => Or.inr (by linarith), by rintro (hupper | hlower) <;> linarith⟩
  · exact ⟨fun htight => Or.inl (by linarith), by rintro (hupper | hlower) <;> linarith⟩

end IsHollowInvolution

/-! ## 6. The heavy branch's exact bound

The pen's Case 3 checks the failure quadratic at the two endpoints of
`[3m, 1 - 2 m^{3/2}]` against the threshold `4/9`.  Run at an arbitrary threshold
the same endpoint argument returns the exact value
`max (3m - 3 m^{3/2}) (1 - 5m + 10 m^2)`, and the second branch is the cap-tight
configuration `(m, m, 1 - 2m - 4m^2 + ...)` written in the root coordinate.  This
is the heavy half's margin in closed form, matching the shipped light half. -/

/-- **THE EXACT HEAVY-BRANCH BOUND, sqrt-free.**  Given a heavy triangle's data
`(sigma, q)` with `q >= r^3`, product floor `r^4 (sigma - 2 r^2) <= q^2` and cap
`sigma + 2 q <= 1`, the residual obeys
`sigma - 3q <= max (3r^2 - 3r^3) (1 - 5r^2 + 10r^4)`. -/
theorem sub_le_max_of_heavyBounds {rootBound edgeSum productRoot : ℝ}
    (hrootNonneg : 0 ≤ rootBound) (hproductRootNonneg : 0 ≤ productRoot)
    (hcube : rootBound ^ 3 ≤ productRoot)
    (hfloor : rootBound ^ 4 * (edgeSum - 2 * rootBound ^ 2) ≤ productRoot ^ 2)
    (hcap : edgeSum + 2 * productRoot ≤ 1) :
    edgeSum - 3 * productRoot
      ≤ max (3 * rootBound ^ 2 - 3 * rootBound ^ 3)
          (1 - 5 * rootBound ^ 2 + 10 * rootBound ^ 4) := by
  set upperValue : ℝ := max (3 * rootBound ^ 2 - 3 * rootBound ^ 3)
    (1 - 5 * rootBound ^ 2 + 10 * rootBound ^ 4) with hupperDef
  have hleftBranch : 3 * rootBound ^ 2 - 3 * rootBound ^ 3 ≤ upperValue := le_max_left _ _
  have hrightBranch : 1 - 5 * rootBound ^ 2 + 10 * rootBound ^ 4 ≤ upperValue := le_max_right _ _
  rcases le_or_gt productRoot (rootBound ^ 2 - 2 * rootBound ^ 4) with hsmall | hlarge
  · rcases eq_or_lt_of_le hrootNonneg with hzero | hpositive
    · rw [← hzero] at hrightBranch
      norm_num at hrightBranch
      linarith
    · have hfourth : (0 : ℝ) < rootBound ^ 4 := by positivity
      have hendpoints := quadratic_nonpos_of_endpoints_nonpos (leadCoeff := 1)
        (linearCoeff := -(3 * rootBound ^ 4))
        (constCoeff := 2 * rootBound ^ 6 - rootBound ^ 4 * upperValue)
        (lower := rootBound ^ 3) (upper := rootBound ^ 2 - 2 * rootBound ^ 4)
        (point := productRoot) (by norm_num)
        (by nlinarith [mul_nonneg hfourth.le (sub_nonneg.mpr hleftBranch)])
        (by nlinarith [mul_nonneg hfourth.le (sub_nonneg.mpr hrightBranch)])
        hcube hsmall
      have hscaled : rootBound ^ 4 * (edgeSum - 3 * productRoot - upperValue)
          ≤ rootBound ^ 4 * 0 := by nlinarith [hendpoints, hfloor]
      linarith [le_of_mul_le_mul_left hscaled hfourth]
  · nlinarith [hrightBranch, hlarge, hcap]

/-- The exact heavy-branch bound at a triangle of weights. -/
theorem signFreeTripleResidual_le_max_of_heavyTriangle {rootBound firstWeight secondWeight
    thirdWeight : ℝ} (hrootNonneg : 0 ≤ rootBound) (hfirst : rootBound ^ 2 ≤ firstWeight)
    (hsecond : rootBound ^ 2 ≤ secondWeight) (hthird : rootBound ^ 2 ≤ thirdWeight)
    (hcap : firstWeight + secondWeight + thirdWeight
      + 2 * Real.sqrt (firstWeight * secondWeight * thirdWeight) ≤ 1) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight
      ≤ max (3 * rootBound ^ 2 - 3 * rootBound ^ 3)
          (1 - 5 * rootBound ^ 2 + 10 * rootBound ^ 4) := by
  have hsquareNonneg : (0 : ℝ) ≤ rootBound ^ 2 := sq_nonneg rootBound
  have hproductNonneg : (0 : ℝ) ≤ firstWeight * secondWeight * thirdWeight :=
    mul_nonneg (mul_nonneg (le_trans hsquareNonneg hfirst) (le_trans hsquareNonneg hsecond))
      (le_trans hsquareNonneg hthird)
  have hrootSquare : Real.sqrt (firstWeight * secondWeight * thirdWeight) ^ 2
      = firstWeight * secondWeight * thirdWeight := Real.sq_sqrt hproductNonneg
  have hfloor := rootProductFloor_le_edgeProduct_of_sq_le hfirst hsecond hthird
  rw [← hrootSquare] at hfloor
  exact sub_le_max_of_heavyBounds hrootNonneg (Real.sqrt_nonneg _)
    (pow_three_le_sqrt_edgeProduct hrootNonneg hfirst hsecond hthird) hfloor hcap

/-! ## 7. The two branch estimates at the crossing, and `r <= 1/2` -/

/-- **THE CAP FORCES `r <= 1/2`.**  A heavy triangle's own data give
`3 r^2 + 2 r^3 <= 1`, and `2 r^3 + 3 r^2 - 1 = (2r - 1)(r + 1)^2` factors exactly,
so the maximum-minimum weight of any capped weight system is at most `1/4`. -/
theorem root_le_half_of_capBound {rootBound : ℝ} (hrootNonneg : 0 ≤ rootBound)
    (hcap : 3 * rootBound ^ 2 + 2 * rootBound ^ 3 ≤ 1) : rootBound ≤ 1 / 2 := by
  nlinarith [sq_nonneg (rootBound + 1), hrootNonneg]

/-- Below the crossing `r^2 = 1/5` the light branch already delivers `2/5`. -/
theorem lightBranch_le_two_fifths {rootBound : ℝ} (hrootNonneg : 0 ≤ rootBound)
    (hlow : 5 * rootBound ^ 2 ≤ 1) :
    max (2 * rootBound ^ 2) (3 * rootBound ^ 2 - 3 * rootBound ^ 3) ≤ 2 / 5 := by
  refine max_le (by linarith) ?_
  rcases le_or_gt (3 * rootBound) 1 with hsmall | hbig
  · nlinarith [pow_nonneg hrootNonneg 3, sq_nonneg rootBound]
  · nlinarith [hlow, hbig, hrootNonneg]

/-- Above the crossing the heavy branch delivers `2/5`.  Its second term is a
quadratic in `r^2` with roots exactly `1/5` and `3/10`, and the cap keeps `r^2`
inside `[1/5, 1/4]`. -/
theorem heavyBranch_le_two_fifths {rootBound : ℝ} (hrootNonneg : 0 ≤ rootBound)
    (hhigh : 1 ≤ 5 * rootBound ^ 2) (hhalf : rootBound ≤ 1 / 2) :
    max (3 * rootBound ^ 2 - 3 * rootBound ^ 3) (1 - 5 * rootBound ^ 2 + 10 * rootBound ^ 4)
      ≤ 2 / 5 := by
  refine max_le ?_ ?_
  · nlinarith [hrootNonneg, hhalf, sq_nonneg (2 * rootBound - 1)]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ rootBound ^ 2 - 1 / 5)
      (by nlinarith : (0 : ℝ) ≤ 3 / 10 - rootBound ^ 2)]

/-! ## 8. The combinatorial core with margin -/

/-- **`(W6)`-WITH-CAP, WITH MARGIN.**  A nonnegative weight function on the six
atoms obeying `(C2)` has a triangle with sign-free residual at most `2/5`.

The pen's constant was `4/9`; the gap `2/45` is uniform, needs no extra
hypothesis, and comes entirely from moving the light-versus-heavy seam from the
pen's `r^2 = 2/9` to the crossing `r^2 = 1/5` where the two exact branch bounds
meet. -/
theorem exists_signFreeTripleResidual_le_two_fifths (weightOf : Fin 6 → Fin 6 → ℝ)
    (hnonneg : ∀ first second, 0 ≤ weightOf first second)
    (hcap : ∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
      weightOf first second + weightOf first third + weightOf second third
        + 2 * Real.sqrt (weightOf first second * weightOf first third
          * weightOf second third) ≤ 1) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      signFreeTripleResidual (weightOf first second) (weightOf first third)
        (weightOf second third) ≤ 2 / 5 := by
  obtain ⟨lightFirst, lightSecond, lightThird, hlightOneTwo, hlightOneThree, hlightTwoThree,
    hlightOne, hlightTwo, hlightThree⟩ := exists_lightTriple weightOf
  obtain ⟨heavyFirst, heavySecond, heavyThird, hheavyOneTwo, hheavyOneThree, hheavyTwoThree,
    hheavyOne, hheavyTwo, hheavyThree⟩ := exists_heavyTriple weightOf
  have hrootNonneg : (0 : ℝ) ≤ Real.sqrt (maxMinWeight weightOf) := Real.sqrt_nonneg _
  have hroot : Real.sqrt (maxMinWeight weightOf) ^ 2 = maxMinWeight weightOf :=
    Real.sq_sqrt (maxMinWeight_nonneg hnonneg)
  rw [← hroot] at hlightOne hlightTwo hlightThree hheavyOne hheavyTwo hheavyThree
  have hheavyCap := hcap heavyFirst heavySecond heavyThird hheavyOneTwo hheavyOneThree
    hheavyTwoThree
  have hcubeRoot := pow_three_le_sqrt_edgeProduct hrootNonneg hheavyOne hheavyTwo hheavyThree
  have hhalf : Real.sqrt (maxMinWeight weightOf) ≤ 1 / 2 :=
    root_le_half_of_capBound hrootNonneg (by linarith)
  rcases le_or_gt (5 * Real.sqrt (maxMinWeight weightOf) ^ 2) 1 with hlow | hhigh
  · refine ⟨lightFirst, lightSecond, lightThird, hlightOneTwo, hlightOneThree, hlightTwoThree,
      le_trans (signFreeTripleResidual_le_max_of_lightTriangle hrootNonneg
        (hnonneg lightSecond lightThird) hlightOne hlightTwo hlightThree) ?_⟩
    exact lightBranch_le_two_fifths hrootNonneg hlow
  · refine ⟨heavyFirst, heavySecond, heavyThird, hheavyOneTwo, hheavyOneThree, hheavyTwoThree,
      le_trans (signFreeTripleResidual_le_max_of_heavyTriangle hrootNonneg hheavyOne hheavyTwo
        hheavyThree hheavyCap) ?_⟩
    exact heavyBranch_le_two_fifths hrootNonneg hhigh.le hhalf

/-! ## 9. Why `2/5` and not less: the extremal pair

At the crossing `m = 1/5` both branch bounds are attained, each by a triangle
satisfying every hypothesis its branch uses and neither violating the cap.  So no
argument built from the maximum-minimum root, the product floor and the cap alone
can improve `2/5`: this is the precise obstruction, the analogue of the tight
weight system that pins `4/9` for the uncapped statement.  Whether a single weight
system carries both triangles at once is not claimed here, and going below `2/5`
would need an input the argument does not currently use — the row law, or the cap's
slack at the saturating heavy triangle. -/

/-- The light extremal at the crossing: `(1/5, 1/5, 0)` has `h = 2/5`, all edges
at most `1/5`, and cap slack `3/5`. -/
theorem signFreeTripleResidual_lightExtremal :
    signFreeTripleResidual (1 / 5) (1 / 5) 0 = 2 / 5 := by
  rw [signFreeTripleResidual, show (1 / 5 : ℝ) * (1 / 5) * 0 = 0 from by ring, Real.sqrt_zero]
  ring

/-- The heavy extremal at the crossing: `(1/5, 1/5, 9/25)` has all edges at least
`1/5`, saturates the cap `sigma + 2 sqrt p = 1`, and has `h = 2/5`. -/
theorem signFreeTripleResidual_heavyExtremal :
    signFreeTripleResidual (1 / 5) (1 / 5) (9 / 25) = 2 / 5 := by
  rw [signFreeTripleResidual,
    show (1 / 5 : ℝ) * (1 / 5) * (9 / 25) = (3 / 25 : ℝ) ^ 2 from by ring,
    Real.sqrt_sq (by norm_num)]
  norm_num

theorem normCap_heavyExtremal :
    (1 / 5 : ℝ) + 1 / 5 + 9 / 25
      + 2 * Real.sqrt ((1 / 5 : ℝ) * (1 / 5) * (9 / 25)) = 1 := by
  rw [show (1 / 5 : ℝ) * (1 / 5) * (9 / 25) = (3 / 25 : ℝ) ^ 2 from by ring,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- **THE OTHER END OF THE HEAVY BRANCH IS ALSO ATTAINED.**  At the largest root the
cap allows, `r = 1/2`, both terms of the heavy bound equal `3/8`. -/
theorem heavyBranch_at_half :
    max (3 * (1 / 2 : ℝ) ^ 2 - 3 * (1 / 2 : ℝ) ^ 3)
      (1 - 5 * (1 / 2 : ℝ) ^ 2 + 10 * (1 / 2 : ℝ) ^ 4) = 3 / 8 := by
  norm_num

/-- And the `K4` graphic `(6,3)` design sits there: its twelve nonzero edge weights
are `1/4`, its maximum-minimum weight is `1/4`, and its star triples have
`h = 3/8` exactly — so the heavy branch is sharp at the top of its range as well
as at the crossing. -/
theorem signFreeTripleResidual_kFourStarWeights :
    signFreeTripleResidual (1 / 4) (1 / 4) (1 / 4) = 3 / 8 := by
  rw [signFreeTripleResidual,
    show (1 / 4 : ℝ) * (1 / 4) * (1 / 4) = (1 / 8 : ℝ) ^ 2 from by ring,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-! ## 10. Quantitative U6 at the stratum

The mirror step of `Gtz.Quantitative.EqualShareSixThree` is stated at the fixed
threshold `4/9`; the argument never uses the value, so it is restated here for an
arbitrary threshold and then run at `2/5`. -/

/-- **THE MIRROR STEP, at any threshold, exposing coherence.**  A triangle with
`h <= threshold` certifies the criterion `sigma - 3P <= threshold` on the coherent
side of its `3-3` split, and the coherence of that side is part of the conclusion:
below `4/9` the criterion alone no longer implies the sign, so the margin argument
needs it. -/
theorem exists_coherent_orientedTripleResidual_le (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) {threshold : ℝ} {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hresidual : triangleResidual D first second third ≤ threshold) :
    ∃ leftIndex middleIndex rightIndex : Fin 6,
      leftIndex ≠ middleIndex ∧ leftIndex ≠ rightIndex ∧ middleIndex ≠ rightIndex ∧
        0 ≤ directionTripleProduct D leftIndex middleIndex rightIndex ∧
        orientedTripleResidual D leftIndex middleIndex rightIndex ≤ threshold := by
  by_cases hcoherent : 0 ≤ directionTripleProduct D first second third
  · refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcoherent, ?_⟩
    rwa [triangleResidual_eq_orientedTripleResidual_of_coherent D hcoherent] at hresidual
  obtain ⟨fourth, fifth, sixth, hbijective⟩ :=
    exists_bijective_completion_of_distinct hfirstSecond hfirstThird hsecondThird
  have huniform : ∀ atomIndex : Fin 6, atomShare D atomIndex = 1 / 2 := fun atomIndex => by
    rw [hequal.atomShare_eq atomIndex]; norm_num
  have hinjective : Function.Injective ![first, second, third, fourth, fifth, sixth] :=
    hbijective.1
  have hfourthFifth : fourth ≠ fifth := fun hvalue => by
    have := hinjective (a₁ := 3) (a₂ := 4) (by simpa using hvalue); exact absurd this (by decide)
  have hfourthSixth : fourth ≠ sixth := fun hvalue => by
    have := hinjective (a₁ := 3) (a₂ := 5) (by simpa using hvalue); exact absurd this (by decide)
  have hfifthSixth : fifth ≠ sixth := fun hvalue => by
    have := hinjective (a₁ := 4) (a₂ := 5) (by simpa using hvalue); exact absurd this (by decide)
  have hsigma := directionTripleSigma_compl_eq D huniform hbijective
  have hproduct := directionTripleProduct_compl_eq_neg D huniform hbijective
  rw [not_le] at hcoherent
  refine ⟨fourth, fifth, sixth, hfourthFifth, hfourthSixth, hfifthSixth,
    by rw [hproduct]; linarith, ?_⟩
  rw [orientedTripleResidual_eq_sigma_sub, hsigma, hproduct]
  rw [triangleResidual, edgeWeight, edgeWeight, edgeWeight, signFreeTripleResidual_sq_eq_min]
    at hresidual
  rw [directionTripleSigma, directionTripleProduct]
  have hmin : min (directionGram D first second ^ 2 + directionGram D first third ^ 2
        + directionGram D second third ^ 2
      - 3 * (directionGram D first second * directionGram D first third
        * directionGram D second third))
      (directionGram D first second ^ 2 + directionGram D first third ^ 2
        + directionGram D second third ^ 2
      + 3 * (directionGram D first second * directionGram D first third
        * directionGram D second third)) ≤ threshold := hresidual
  have hother : directionGram D first second ^ 2 + directionGram D first third ^ 2
      + directionGram D second third ^ 2
      + 3 * (directionGram D first second * directionGram D first third
        * directionGram D second third) ≤ threshold := by
    rw [directionTripleProduct] at hcoherent
    rcases min_le_iff.mp hmin with hleft | hright
    · linarith
    · exact hright
  linarith

/-- **`(W6)`-WITH-MARGIN AT THE STRATUM.** -/
theorem exists_triangleResidual_le_two_fifths (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      triangleResidual D first second third ≤ 2 / 5 :=
  exists_signFreeTripleResidual_le_two_fifths (edgeWeight D) (edgeWeight_nonneg D)
    fun _ _ _ hfirstSecond hfirstThird hsecondThird =>
      edgeWeight_normCap_sqrt D hequal hfirstSecond hfirstThird hsecondThird

/-- **THE CRITERION AT A SUBCRITICAL LEVEL.**  The pen's `(C1)` reads
`sigma - 3P <= level^2` once the level is written where `4/9` used to be: for
`level` between `1/2` and `2/3`, a coherent triangle under the involution cap with
`sigma - 3P <= level^2` has `level 1 + N ⪰ 0`, hence
`lambda_min(1 + N) >= 1 - level`.  At `level = 2/3` this is U6 verbatim, and the
margin argument of this section runs it at `level = 16/25`. -/
theorem posSemidef_smul_one_add_hollowSymmetricThree_of_criterion_le_sq
    {level edgeFirst edgeSecond edgeThird : ℝ} (hlevelLow : 1 / 2 ≤ level)
    (hlevelHigh : level ≤ 2 / 3)
    (hcap : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef)
    (hcoherent : 0 ≤ edgeFirst * edgeSecond * edgeThird)
    (hcriterion : edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2
      - 3 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 2) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef := by
  rw [← one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ)] at hcap
  refine (posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper
    (by linarith) (by linarith) hcap).mpr ?_
  nlinarith [hcriterion, hcoherent, hlevelLow, hlevelHigh]

/-- The direction Gram compressed at a triple is `1` plus the hollow block. -/
theorem directionGramMatrix_submatrix_three_eq_one_add_hollowMatrixThree {m : ℕ}
    (D : WeightedDesign m 3) (hpositive : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex))
    {firstIndex secondIndex thirdIndex : Fin m} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
        ![firstIndex, secondIndex, thirdIndex]
      = (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowMatrixThree (directionGram D firstIndex secondIndex)
          (directionGram D firstIndex thirdIndex) (directionGram D secondIndex thirdIndex) := by
  have hpick : Function.Injective ![firstIndex, secondIndex, thirdIndex] :=
    injective_three_of_ne hfirstSecond hfirstThird hsecondThird
  have hblock := correlationInvolution_submatrix_three_eq_hollowMatrixThree D hpositive
    hfirstSecond hfirstThird hsecondThird
  rw [← hblock, correlationInvolution, show (directionGramMatrix D - 1).submatrix
      ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex]
      = (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
          ![firstIndex, secondIndex, thirdIndex]
        - (1 : Matrix (Fin m) (Fin m) ℝ).submatrix ![firstIndex, secondIndex, thirdIndex]
          ![firstIndex, secondIndex, thirdIndex] from rfl,
    Matrix.submatrix_one _ hpick]
  abel

/-- **QUANTITATIVE U6, THE HEADLINE.**  Every equal-share `(6,3)` design has a
triple whose direction Gram has least eigenvalue at least `9/25`, strictly above
the U6 threshold `1/3`.  Equivalently, the triple's own atoms resolve at
`(27/25) 1`: an eight percent margin over domination.

For calibration the stratum's numerical infimum of `max_C lambda_min(Gamma[C])` is
near `0.4122`, so `9/25` is about ninety percent of the way from `1/3` to the
truth. -/
theorem exists_nine_twentyfifths_le_lambdaMinMat_of_isEqualShare (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      (9 / 25 : ℝ) ≤ lambdaMinMat ((directionGramMatrix D).submatrix
        ![first, second, third] ![first, second, third]) := by
  obtain ⟨lightFirst, lightSecond, lightThird, hlightOneTwo, hlightOneThree, hlightTwoThree,
    hresidual⟩ := exists_triangleResidual_le_two_fifths D hequal
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcoherent,
    hcriterion⟩ := exists_coherent_orientedTripleResidual_le D hequal hlightOneTwo
      hlightOneThree hlightTwoThree hresidual
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  have hpositive : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    hequal.leverage_pos (by norm_num) atomIndex
  have hpick : Function.Injective ![first, second, third] :=
    injective_three_of_ne hfirstSecond hfirstThird hsecondThird
  have hinvol := isHollowInvolution_correlationInvolution_six D hequal
  have hcap := hinvol.posSemidef_one_sub_submatrix ![first, second, third] hpick
  rw [correlationInvolution_submatrix_three_eq_hollowMatrixThree D hpositive hfirstSecond
    hfirstThird hsecondThird] at hcap
  rw [directionTripleProduct] at hcoherent
  rw [orientedTripleResidual_eq_sigma_sub, directionTripleSigma, directionTripleProduct]
    at hcriterion
  have hshift := posSemidef_smul_one_add_hollowSymmetricThree_of_criterion_le_sq
    (level := 16 / 25) (by norm_num) (by norm_num) hcap hcoherent (by nlinarith [hcriterion])
  have hshape : (directionGramMatrix D).submatrix ![first, second, third]
        ![first, second, third] - (9 / 25 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = (16 / 25 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowMatrixThree (directionGram D first second) (directionGram D first third)
          (directionGram D second third) := by
    rw [directionGramMatrix_submatrix_three_eq_one_add_hollowMatrixThree D hpositive
      hfirstSecond hfirstThird hsecondThird]
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> ring
  have hsymmetric : ((directionGramMatrix D).submatrix ![first, second, third]
      ![first, second, third])ᵀ = (directionGramMatrix D).submatrix ![first, second, third]
        ![first, second, third] := by
    ext rowIndex colIndex
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
    exact directionGram_comm D _ _
  rw [le_lambdaMinMat_iff_posSemidef_sub_smul_one _ hsymmetric, hshape]
  exact hshift

/-- **U6 IS NEVER TIGHT.**  Every equal-share `(6,3)` design has a triple whose
criterion value is at most `2/5 = 4/9 - 2/45`, so the U6 threshold `4/9` is
attained by no member of the stratum and the equality locus the campaign expected
to classify is EMPTY. -/
theorem exists_orientedTripleResidual_le_two_fifths (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      orientedTripleResidual D first second third ≤ 2 / 5 := by
  obtain ⟨lightFirst, lightSecond, lightThird, hlightOneTwo, hlightOneThree, hlightTwoThree,
    hresidual⟩ := exists_triangleResidual_le_two_fifths D hequal
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, _, hcriterion⟩ :=
    exists_coherent_orientedTripleResidual_le D hequal hlightOneTwo hlightOneThree
      hlightTwoThree hresidual
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcriterion⟩

/-- **THE MARGIN ON THE FRAME SIDE.**  The dominating triple's own atoms resolve
at `(27/25) 1`, not merely at `1`: an eight percent Loewner margin over
domination, uniform over the stratum.  This is the least-eigenvalue statement
carried across the `AB`-versus-`BA` transfer at the level `9/25` and rescaled by
the common leverage. -/
theorem exists_dominating_triple_with_margin (D : WeightedDesign 6 3) (hequal : IsEqualShare D) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      (subsetSum D {first, second, third}
        - ((27 : ℝ) / 25) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hlambda⟩ :=
    exists_nine_twentyfifths_le_lambdaMinMat_of_isEqualShare D hequal
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  have hsymmetric : ((directionGramMatrix D).submatrix ![first, second, third]
      ![first, second, third])ᵀ = (directionGramMatrix D).submatrix ![first, second, third]
        ![first, second, third] := by
    ext rowIndex colIndex
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
    exact directionGram_comm D _ _
  have hgram := (le_lambdaMinMat_iff_posSemidef_sub_smul_one _ hsymmetric (9 / 25)).mp hlambda
  have hframe : (directionFrame D ![first, second, third])ᵀ
        * directionFrame D ![first, second, third]
      = (directionGramMatrix D).submatrix ![first, second, third] ![first, second, third] := by
    ext slotRow slotCol
    rw [transpose_mul_directionFrame_apply]
    rfl
  rw [← hframe] at hgram
  have hcoordinate := (posSemidef_transpose_mul_sub_smul_one_comm
    (directionFrame D ![first, second, third]) (by norm_num : (0 : ℝ) < 9 / 25)).mp hgram
  have hscaled := hcoordinate.smul (by norm_num : (0 : ℝ) ≤ 3)
  rw [subsetSum_triple_eq_smul_directionFrame_mul_transpose D hequal.leverage_eq_three
    (by norm_num) hfirstSecond hfirstThird hsecondThird]
  convert hscaled using 1
  rw [smul_sub, smul_smul]
  norm_num

/-- **STRICT DOMINATION WITH A UNIFORM MARGIN.**  The criterion value `2/5` is
strictly below `4/9`, so the shifted block is positive DEFINITE, not merely
semidefinite: `lambda_min(Gamma[C]) > 1/3` at some triple of every member of the
stratum. -/
theorem exists_posDef_shift_of_isEqualShare (D : WeightedDesign 6 3) (hequal : IsEqualShare D) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree (directionGram D first second) (directionGram D first third)
          (directionGram D second third)).PosDef := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcriterion⟩ :=
    exists_orientedTripleResidual_le_two_fifths D hequal
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    posDef_of_orientedTripleResidual_lt_four_ninths D hequal hfirstSecond hfirstThird
      hsecondThird (by linarith)⟩

/-! ## 11. The degeneracy classification at the stratum

A triple of an equal-share design is DEGENERATE exactly when its three unit
directions are linearly dependent — coplanar — and that is exactly when the
triple's own atom sum is singular, since the atom sum is the leverage-scaled frame
operator and the frame operator's determinant is the direction Gram's.  So the
abstract classification of §5 reads, at the stratum: the norm cap is tight at a
triple exactly when that triple or its complement is coplanar. -/

/-- The atom sum's determinant is the direction Gram's, scaled by the cube of the
common leverage. -/
theorem det_subsetSum_triple_eq_smul_det_directionGramMatrix (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    (subsetSum D {first, second, third}).det
      = 27 * ((directionGramMatrix D).submatrix ![first, second, third]
          ![first, second, third]).det := by
  have hframe : (directionFrame D ![first, second, third])ᵀ
        * directionFrame D ![first, second, third]
      = (directionGramMatrix D).submatrix ![first, second, third] ![first, second, third] := by
    ext slotRow slotCol
    rw [transpose_mul_directionFrame_apply]
    rfl
  rw [subsetSum_triple_eq_smul_directionFrame_mul_transpose D hequal.leverage_eq_three
    (by norm_num) hfirstSecond hfirstThird hsecondThird, Matrix.det_smul,
    Matrix.det_mul_comm, hframe]
  norm_num

/-- **THE COPLANAR CLASSIFICATION AT THE STRATUM.**  The norm cap `(C2)` is tight
at a triple exactly when that triple or its complement is degenerate, i.e. has a
singular atom sum.  Since both compressions of the involution sandwich are
positive semidefinite with determinants `1 - sigma + 2P` and `1 - sigma - 2P`, this
is the spectra-free reading of `||M[T]|| = 1`. -/
theorem normCap_eq_one_iff_det_subsetSum_eq_zero (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    directionGram D first second ^ 2 + directionGram D first third ^ 2
        + directionGram D second third ^ 2
      + 2 * |directionGram D first second * directionGram D first third
          * directionGram D second third| = 1
      ↔ (subsetSum D {first, second, third}).det = 0
        ∨ (subsetSum D {fourth, fifth, sixth}).det = 0 := by
  have hpositive : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    hequal.leverage_pos (by norm_num) atomIndex
  have hinvol := isHollowInvolution_correlationInvolution_six D hequal
  have hfirstSecond : first ≠ second :=
    IsHollowInvolution.ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 1)
  have hfirstThird : first ≠ third :=
    IsHollowInvolution.ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 2)
  have hsecondThird : second ≠ third :=
    IsHollowInvolution.ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 2)
  have hfourthFifth : fourth ≠ fifth :=
    IsHollowInvolution.ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 4)
  have hfourthSixth : fourth ≠ sixth :=
    IsHollowInvolution.ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 5)
  have hfifthSixth : fifth ≠ sixth :=
    IsHollowInvolution.ne_of_bijective_six hbijective (by decide : (4 : Fin 6) ≠ 5)
  have hleftShape : (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + (correlationInvolution D).submatrix ![first, second, third] ![first, second, third]
      = (directionGramMatrix D).submatrix ![first, second, third] ![first, second, third] := by
    rw [correlationInvolution_submatrix_three_eq_hollowMatrixThree D hpositive hfirstSecond
      hfirstThird hsecondThird,
      directionGramMatrix_submatrix_three_eq_one_add_hollowMatrixThree D hpositive hfirstSecond
      hfirstThird hsecondThird]
  have hrightShape : (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + (correlationInvolution D).submatrix ![fourth, fifth, sixth] ![fourth, fifth, sixth]
      = (directionGramMatrix D).submatrix ![fourth, fifth, sixth] ![fourth, fifth, sixth] := by
    rw [correlationInvolution_submatrix_three_eq_hollowMatrixThree D hpositive hfourthFifth
      hfourthSixth hfifthSixth,
      directionGramMatrix_submatrix_three_eq_one_add_hollowMatrixThree D hpositive hfourthFifth
      hfourthSixth hfifthSixth]
  have hclassification := hinvol.normCap_eq_one_iff_degenerate hbijective
  rw [correlationInvolution_apply_of_ne D hfirstSecond,
    correlationInvolution_apply_of_ne D hfirstThird,
    correlationInvolution_apply_of_ne D hsecondThird, hleftShape, hrightShape]
    at hclassification
  rw [hclassification, det_subsetSum_triple_eq_smul_det_directionGramMatrix D hequal
    hfirstSecond hfirstThird hsecondThird,
    det_subsetSum_triple_eq_smul_det_directionGramMatrix D hequal hfourthFifth hfourthSixth
    hfifthSixth]
  constructor
  · rintro (hleft | hright)
    · exact Or.inl (by rw [hleft]; ring)
    · exact Or.inr (by rw [hright]; ring)
  · rintro (hleft | hright)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

/-! ## 12. Quantitative U6 on an arbitrary hollow symmetric involution

The abstract statement the assembly could not close.  With the mirror of §4 the
coherent side is available abstractly, so the conclusion is unconditional: no
coherence hypothesis, and no realizability hypothesis either. -/

namespace IsHollowInvolution

variable {invol : Matrix (Fin 6) (Fin 6) ℝ}

/-- The combinatorial core with margin, abstractly. -/
theorem exists_signFreeTripleResidual_le_two_fifths (hinvol : IsHollowInvolution invol) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      signFreeTripleResidual (invol first second ^ 2) (invol first third ^ 2)
        (invol second third ^ 2) ≤ 2 / 5 :=
  Gtz.exists_signFreeTripleResidual_le_two_fifths (fun first second => invol first second ^ 2)
    (fun _ _ => sq_nonneg _)
    fun _ _ _ hfirstSecond hfirstThird hsecondThird =>
      hinvol.normCap_sqrt hfirstSecond hfirstThird hsecondThird

/-- **THE ABSTRACT MIRROR STEP.**  A triangle with `h <= threshold` certifies the
criterion on the coherent side of its `3-3` split. -/
theorem exists_coherent_criterion_le (hinvol : IsHollowInvolution invol) {threshold : ℝ}
    {first second third : Fin 6} (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hresidual : signFreeTripleResidual (invol first second ^ 2) (invol first third ^ 2)
      (invol second third ^ 2) ≤ threshold) :
    ∃ leftIndex middleIndex rightIndex : Fin 6,
      leftIndex ≠ middleIndex ∧ leftIndex ≠ rightIndex ∧ middleIndex ≠ rightIndex ∧
        0 ≤ invol leftIndex middleIndex * invol leftIndex rightIndex
            * invol middleIndex rightIndex ∧
        invol leftIndex middleIndex ^ 2 + invol leftIndex rightIndex ^ 2
            + invol middleIndex rightIndex ^ 2
          - 3 * (invol leftIndex middleIndex * invol leftIndex rightIndex
            * invol middleIndex rightIndex) ≤ threshold := by
  rw [signFreeTripleResidual_sq_eq_min] at hresidual
  by_cases hcoherent : 0 ≤ invol first second * invol first third * invol second third
  · refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcoherent, ?_⟩
    rcases min_le_iff.mp hresidual with hleft | hright
    · exact hleft
    · linarith
  obtain ⟨fourth, fifth, sixth, hbijective⟩ :=
    exists_bijective_completion_of_distinct hfirstSecond hfirstThird hsecondThird
  have hinjective : Function.Injective ![first, second, third, fourth, fifth, sixth] :=
    hbijective.1
  have hfourthFifth : fourth ≠ fifth := fun hvalue => by
    have := hinjective (a₁ := 3) (a₂ := 4) (by simpa using hvalue); exact absurd this (by decide)
  have hfourthSixth : fourth ≠ sixth := fun hvalue => by
    have := hinjective (a₁ := 3) (a₂ := 5) (by simpa using hvalue); exact absurd this (by decide)
  have hfifthSixth : fifth ≠ sixth := fun hvalue => by
    have := hinjective (a₁ := 4) (a₂ := 5) (by simpa using hvalue); exact absurd this (by decide)
  have hsigma := hinvol.tripleSigma_compl_eq hbijective
  have hproduct := hinvol.tripleProduct_compl_eq_neg hbijective
  rw [not_le] at hcoherent
  refine ⟨fourth, fifth, sixth, hfourthFifth, hfourthSixth, hfifthSixth, by
    rw [hproduct]; linarith, ?_⟩
  rw [hsigma, hproduct]
  rcases min_le_iff.mp hresidual with hleft | hright
  · linarith
  · linarith

/-- **U6, ABSTRACTLY AND UNCONDITIONALLY.**  Every hollow symmetric involution on
`Fin 6` has three distinct indices whose compression satisfies
`M[C] + (2/3) 1 ⪰ 0`, with the improved margin `M[C] + (16/25) 1 ⪰ 0`.

This is the statement `Gtz.Quantitative.EqualShareSixThree` had to weaken by a
coherence hypothesis.  Both the norm cap and the mirror are available on the
abstract object, so nothing is assumed about realizability — which is in any case
automatic, `(M + 1)/2` being a rank-three projection of constant diagonal `1/2`
whenever `M` is a hollow symmetric involution on `Fin 6`. -/
theorem exists_posSemidef_marginShift (hinvol : IsHollowInvolution invol) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      (((16 : ℝ) / 25) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + invol.submatrix ![first, second, third] ![first, second, third]).PosSemidef := by
  obtain ⟨lightFirst, lightSecond, lightThird, hlightOneTwo, hlightOneThree, hlightTwoThree,
    hresidual⟩ := hinvol.exists_signFreeTripleResidual_le_two_fifths
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcoherent,
    hcriterion⟩ := hinvol.exists_coherent_criterion_le hlightOneTwo hlightOneThree
      hlightTwoThree hresidual
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  have hpick : Function.Injective ![first, second, third] :=
    injective_three_of_ne hfirstSecond hfirstThird hsecondThird
  have hcap := hinvol.posSemidef_one_sub_submatrix ![first, second, third] hpick
  rw [hinvol.submatrix_three_eq_hollowMatrixThree first second third] at hcap ⊢
  exact posSemidef_smul_one_add_hollowSymmetricThree_of_criterion_le_sq (level := 16 / 25)
    (by norm_num) (by norm_num) hcap hcoherent (by nlinarith [hcriterion])

/-- The abstract U6 conclusion at the pen's own level `2/3`. -/
theorem exists_posSemidef_twoThirds_shift (hinvol : IsHollowInvolution invol) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + invol.submatrix ![first, second, third] ![first, second, third]).PosSemidef := by
  obtain ⟨lightFirst, lightSecond, lightThird, hlightOneTwo, hlightOneThree, hlightTwoThree,
    hresidual⟩ := hinvol.exists_signFreeTripleResidual_le_two_fifths
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcoherent,
    hcriterion⟩ := hinvol.exists_coherent_criterion_le hlightOneTwo hlightOneThree
      hlightTwoThree hresidual
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  have hpick : Function.Injective ![first, second, third] :=
    injective_three_of_ne hfirstSecond hfirstThird hsecondThird
  have hcap := hinvol.posSemidef_one_sub_submatrix ![first, second, third] hpick
  rw [hinvol.submatrix_three_eq_hollowMatrixThree first second third] at hcap ⊢
  exact posSemidef_smul_one_add_hollowSymmetricThree_of_criterion_le_sq (level := 2 / 3)
    (by norm_num) (by norm_num) hcap hcoherent (by nlinarith [hcriterion])

end IsHollowInvolution

end Gtz

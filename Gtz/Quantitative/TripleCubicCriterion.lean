/-
# The triple cubic criterion: a hollow symmetric `3 x 3` decided by ONE sign,
and the exact price of the norm cap

The object is a hollow symmetric real `3 x 3` matrix `N` — symmetric with zero
diagonal — with off-diagonal entries `(a, b, c)` in the slots `(0,1)`, `(0,2)`,
`(1,2)`.  Two scalars carry everything:

    sigma  =  a^2 + b^2 + c^2        (the edge-square sum)
    P      =  a * b * c              (the oriented triangle product)

`N` arises in the campaign as the gap `Gamma[C] - 1` of a triple `C` of a rank-three
design, read in DIRECTION-COSINE coordinates: `Gamma` is the Gram of the unit
directions, so its diagonal is one and `N` is hollow.  Domination of the triple
at the equal-share stratum is `lambda_min(Gamma[C]) >= 1/3`, i.e.
`(2/3) . 1 + N` positive semidefinite.  This file decides that, and every
sibling question, from `sigma` and `P` alone.

## What is proved

* **S3, the characteristic polynomial.**  `charpoly_hollowSymmetricThree` :
  `charpoly(N) = X^3 - sigma X - 2P`.  Trace zero, second elementary symmetric
  function `-sigma`, determinant `2P`.  Two shifted determinants come with it:
  `det(level . 1 + N) = level^3 - level sigma + 2P` and
  `det(level . 1 - N) = level^3 - level sigma - 2P`.

* **The cap-free baseline.**  `posSemidef_smul_one_add_hollowSymmetricThree_iff` :
  for `level > 0`, `(level . 1 + N)` is positive semidefinite IFF the three edge
  conditions `a^2 <= level^2`, `b^2 <= level^2`, `c^2 <= level^2` hold AND
  `level sigma - 2P <= level^3`.  This is the shipped elliptope criterion
  (`posSemidef_correlationMatrixThree_iff`) pulled back along the homogenisation
  `level . 1 + N = level . correlationMatrixThree (a/level) (b/level) (c/level)`.
  All four conjuncts are load-bearing without a cap.

* **(C1), the criterion, as an IFF.**
  `posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper` : under
  the UPPER norm cap `(cap . 1 - N)` positive semidefinite and `cap <= 2 * level`,

      (level . 1 + N) positive semidefinite   <->   level sigma - 2P <= level^3.

  What the cap buys is exactly the deletion of the three edge conjuncts.  At
  `cap = 1`, `level = 2/3` this is the pen's `sigma - 3P <= 4/9`
  (`posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper`),
  and the parameterised form lets the `(7,3)` layer instantiate `cap = 4/3` with
  no re-derivation.

* **(C2), the norm-cap inequality.**  `mul_squareSum_add_two_mul_abs_product_le_of_spectralCap` :
  both halves of the cap give `cap sigma + 2 |P| <= cap^3`, i.e. at `cap = 1` the
  pen's `sigma + 2|P| <= 1` (`squareSum_add_two_mul_abs_product_le_one`).  This is
  two applications of `Matrix.PosSemidef.det_nonneg` and nothing else.

* **(C3), the heavy cell, COHERENT SIDE ONLY.**
  `determinantCriterion_of_spectralCapUpper_of_heavyProduct` : the criterion holds
  as soon as `level * cap * (cap - level) <= 2P`.  At `cap = 1`, `level = 2/3` the
  threshold is `P >= 1/9` (`posSemidef_twoThirds_of_spectralCapUpper_of_ninth_le_product`).
  The hypothesis is on `P`, not on `|P|`: on the incoherent side the bound runs the
  wrong way and the statement is FALSE — see the refutation below.

## Where the cap is spent, exactly

The criterion's forward direction is cap-FREE
(`determinantCriterion_of_posSemidef_smul_one_add_hollowSymmetricThree`: positive
semidefinite implies nonnegative determinant, at every `level >= 0`).  The backward
direction is cap-free too, once one has the second elementary symmetric function
of `level . 1 + N`, which is `3 level^2 - sigma`
(`posSemidef_smul_one_add_hollowSymmetricThree_of_squareSum_le`).  So the ENTIRE
consumption of the cap is one scalar step,

    squareSum_le_three_mul_sq_of_spectralCapUpper :  sigma <= 3 level^2,

and even that step uses only the UPPER half `(cap . 1 - N) >= 0`; the lower half
never enters (C1).  Its mechanism is a cancellation: adding the cap determinant
`cap sigma + 2P <= cap^3` to the criterion `level sigma - 2P <= level^3` kills `P`
outright and leaves `(level + cap) sigma <= level^3 + cap^3`
(`add_mul_squareSum_le_of_spectralCapUpper_of_determinantCriterion`), whence
`sigma <= level^2 - level cap + cap^2`; and

    3 level^2 (level + cap) - (level^3 + cap^3)  =  (2 level - cap) (level + cap)^2,

so `cap <= 2 * level` is exactly what turns that into `sigma <= 3 level^2`.  This is
the hinge on which every transfer of the cell to another size turns: a cell proved
at cap `c` transfers to a threshold `level` iff `c <= 2 * level`.

## Two refutations, both exactly rational

* **The cap is not removable.**  `exists_hollowSymmetricThree_criterion_without_posSemidef` :
  at `a = b = c = 1` one has `sigma - 3P = 0 <= 4/9` while `(2/3) . 1 + N` is NOT
  positive semidefinite.  This is the pen's rogue branch made explicit — `N` has
  spectrum `(2, -1, -1)`, two eigenvalues at `-1 < -2/3` and one at `2 > 4/3` — and
  it is excluded by the cap and by nothing else
  (`not_posSemidef_one_sub_hollowSymmetricThree_one_one_one`).

* **`cap <= 2 * level` is SHARP.**  `exists_hollowSymmetricThree_capSharpness` : for
  every `level > 0` and every `cap > 2 * level`, the matrix with
  `a = b = c = cap/2` carries the cap at `cap` in BOTH directions, satisfies the
  criterion (because `level^3 - 3 h^2 level + 2 h^3 = (level - h)^2 (level + 2h)`),
  and fails to be positive semidefinite.  So the threshold cannot be relaxed by any
  amount, and at `cap = 2 * level` the theorem still holds.

* **(C3) two-sided is FALSE.**
  `exists_spectralCapped_hollowSymmetricThree_incoherent_heavy_not_posSemidef` : at
  `a = b = c = -1/2` the cap holds in both directions (`det(1 + N) = 0` exactly, so
  the cap is TIGHT), `|P| = 1/8 >= 1/9`, and yet `sigma - 3P = 9/8 > 4/9` — more than
  twice the threshold — and `(2/3) . 1 + N` is not positive semidefinite.  This is not
  an artificial point: flipping one atom's direction carries it to the three edges of
  a `K4` triangle, i.e. to the INCOHERENT side of a mirror pair of the `K4` graphic
  `(6,3)` design, whose coherent side `a = b = c = 1/2` dominates with
  `lambda_min(Gamma) = 1/2`.  Reading (C3) with `|P|` on both sides therefore refutes
  itself inside the campaign's own witness.

## What this file does NOT prove

The norm cap is an INPUT here, never a conclusion: every statement below takes
`(cap . 1 - N)` positive semidefinite as a hypothesis.  Producing it — from the
involution law `M^2 = 1` of the equal-share stratum, by the Loewner sandwich and
compression — belongs to the involution layer.  Nor is anything here about designs:
the file is design-free, and the identification of `N` with a triple's direction-Gram
gap is the assembly layer's step, made one rewrite long by
`eq_hollowSymmetricThree_of_transpose_eq_of_diagonal_eq_zero` and the entry-indexed
wrappers.

## The bridge to the shipped rho layer

`correlationMatrixThree_eq_one_add_hollowSymmetricThree` identifies the shipped
unit-diagonal correlation matrix as the case `level = 1`, and
`posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_iff_correlationMatrixThree`
is the `rho = (3/2) gamma` dictionary of the equal-share stratum, stated as an
equivalence of positive semidefiniteness rather than asserted as a change of
coordinates.  Consumers holding an abstract symmetric hollow form rather than the
constructor should enter through
`eq_hollowSymmetricThree_of_transpose_eq_of_diagonal_eq_zero` or through the
entry-indexed wrappers at the end of the file, which take the three entry
equations as `rfl`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ElliptopeInterval
import Gtz.LinAlg.ProjectionForm
import Gtz.Design.RhoNormalForm
import Gtz.Reduction.MixedCharPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## The object: a hollow symmetric `3 x 3` and its normal form -/

/-- The **hollow symmetric `3 x 3`** with off-diagonal entries
`(edgeFirst, edgeSecond, edgeThird)` in the slots `(0,1)`, `(0,2)`, `(1,2)`.  The
slot convention matches `Gtz.correlationMatrixThree`, so the two differ only on the
diagonal: `correlationMatrixThree r1 r2 r3 = 1 + hollowSymmetricThree r1 r2 r3`. -/
def hollowSymmetricThree (edgeFirst edgeSecond edgeThird : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, edgeFirst, edgeSecond;
     edgeFirst, 0, edgeThird;
     edgeSecond, edgeThird, 0]

theorem hollowSymmetricThree_transpose (edgeFirst edgeSecond edgeThird : ℝ) :
    (hollowSymmetricThree edgeFirst edgeSecond edgeThird)ᵀ
      = hollowSymmetricThree edgeFirst edgeSecond edgeThird := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> rfl

/-- **Every symmetric `3 x 3` with zero diagonal is one of these.**  The entry point
for consumers holding an abstract gap matrix rather than the constructor. -/
theorem eq_hollowSymmetricThree_of_transpose_eq_of_diagonal_eq_zero
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    (hdiagonal : ∀ index : Fin 3, form index index = 0) :
    form = hollowSymmetricThree (form 0 1) (form 0 2) (form 1 2) := by
  have hflipFirst : form 1 0 = form 0 1 := by
    conv_lhs => rw [← hsymmetric]
    rfl
  have hflipSecond : form 2 0 = form 0 2 := by
    conv_lhs => rw [← hsymmetric]
    rfl
  have hflipThird : form 2 1 = form 1 2 := by
    conv_lhs => rw [← hsymmetric]
    rfl
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [hollowSymmetricThree, hdiagonal, hflipFirst, hflipSecond, hflipThird]

/-- The shifted matrix `level . 1 + N`, written out.  Every determinant below is
computed from this form. -/
theorem smul_one_add_hollowSymmetricThree (level edgeFirst edgeSecond edgeThird : ℝ) :
    level • (1 : Matrix (Fin 3) (Fin 3) ℝ) + hollowSymmetricThree edgeFirst edgeSecond edgeThird
      = !![level, edgeFirst, edgeSecond;
           edgeFirst, level, edgeThird;
           edgeSecond, edgeThird, level] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [hollowSymmetricThree]

/-- Subtracting a hollow matrix is adding its negation entrywise: this is how the
two halves of the norm cap become one statement. -/
theorem smul_one_sub_hollowSymmetricThree (level edgeFirst edgeSecond edgeThird : ℝ) :
    level • (1 : Matrix (Fin 3) (Fin 3) ℝ) - hollowSymmetricThree edgeFirst edgeSecond edgeThird
      = level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree (-edgeFirst) (-edgeSecond) (-edgeThird) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [hollowSymmetricThree]

theorem smul_one_add_hollowSymmetricThree_transpose (level edgeFirst edgeSecond edgeThird : ℝ) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird)ᵀ
      = level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird := by
  rw [smul_one_add_hollowSymmetricThree]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> rfl

/-- **The shipped correlation matrix is the case `level = 1`.**  The bridge from this
file to `Gtz.Design.RhoNormalForm` and the whole elliptope layer. -/
theorem correlationMatrixThree_eq_one_add_hollowSymmetricThree
    (rhoFirst rhoSecond rhoThird : ℝ) :
    correlationMatrixThree rhoFirst rhoSecond rhoThird
      = (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree rhoFirst rhoSecond rhoThird := by
  rw [smul_one_add_hollowSymmetricThree]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> rfl

/-! ## S3: trace, second symmetric function, determinant, characteristic polynomial

The whole file rests on the three coefficient identities below.  For a hollow
symmetric `3 x 3` the trace vanishes, the sum of the `2 x 2` principal minors is
`-sigma`, and the determinant is `2P`. -/

theorem trace_hollowSymmetricThree (edgeFirst edgeSecond edgeThird : ℝ) :
    (hollowSymmetricThree edgeFirst edgeSecond edgeThird).trace = 0 := by
  rw [Matrix.trace_fin_three]
  simp [hollowSymmetricThree]

/-- **The shifted determinant.**  `det(level . 1 + N) = level^3 - level sigma + 2P`. -/
theorem det_smul_one_add_hollowSymmetricThree (level edgeFirst edgeSecond edgeThird : ℝ) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird).det
      = level ^ 3 - level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
        + 2 * (edgeFirst * edgeSecond * edgeThird) := by
  rw [smul_one_add_hollowSymmetricThree, Matrix.det_fin_three]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **The reflected shifted determinant.**  `det(level . 1 - N) = level^3 - level sigma - 2P`;
only the sign of `P` moves, which is the whole content of the mirror at the level of
determinants. -/
theorem det_smul_one_sub_hollowSymmetricThree (level edgeFirst edgeSecond edgeThird : ℝ) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - hollowSymmetricThree edgeFirst edgeSecond edgeThird).det
      = level ^ 3 - level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
        - 2 * (edgeFirst * edgeSecond * edgeThird) := by
  rw [smul_one_sub_hollowSymmetricThree, det_smul_one_add_hollowSymmetricThree]
  ring

/-- **S3.  The characteristic polynomial of a hollow symmetric `3 x 3`.**
`charpoly(N) = X^3 - sigma X - 2P`.  Both missing coefficients are forced: the
`X^2` coefficient is minus the trace, which is zero because the diagonal is, and the
constant term is minus the determinant `2P`. -/
theorem charpoly_hollowSymmetricThree (edgeFirst edgeSecond edgeThird : ℝ) :
    (hollowSymmetricThree edgeFirst edgeSecond edgeThird).charpoly
      = Polynomial.X ^ 3
        - Polynomial.C (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2) * Polynomial.X
        - Polynomial.C (2 * (edgeFirst * edgeSecond * edgeThird)) := by
  have htrace : hollowSymmetricThree edgeFirst edgeSecond edgeThird 0 0
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird 1 1
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird 2 2 = 0 := by
    simp [hollowSymmetricThree]
  have hsecond : hollowSymmetricThree edgeFirst edgeSecond edgeThird 0 0
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 1 1
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird 0 1
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 1 0
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird 0 0
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 2 2
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird 0 2
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 2 0
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird 1 1
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 2 2
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird 1 2
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 2 1
      = -(edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2) := by
    simp only [hollowSymmetricThree, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
    ring
  have hthird : hollowSymmetricThree edgeFirst edgeSecond edgeThird 0 0
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 1 1
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 2 2
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird 0 0
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 1 2
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 2 1
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird 0 1
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 1 0
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 2 2
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird 0 1
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 1 2
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 2 0
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird 0 2
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 1 0
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 2 1
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird 0 2
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 1 1
        * hollowSymmetricThree edgeFirst edgeSecond edgeThird 2 0
      = 2 * (edgeFirst * edgeSecond * edgeThird) := by
    simp only [hollowSymmetricThree, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
    ring
  rw [charpoly_fin_three_expand, htrace, hsecond, hthird, map_zero, map_neg]
  ring

/-- The characteristic polynomial evaluated at a level: `f(level) = det(level . 1 - N)`,
which is the cubic `level^3 - sigma level - 2P` the pen writes.  The tie condition
`f(-level) <= 0` of (C1) is `det(level . 1 + N) >= 0` read through this. -/
theorem eval_charpoly_hollowSymmetricThree (level edgeFirst edgeSecond edgeThird : ℝ) :
    (hollowSymmetricThree edgeFirst edgeSecond edgeThird).charpoly.eval level
      = level ^ 3 - (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2) * level
        - 2 * (edgeFirst * edgeSecond * edgeThird) := by
  rw [charpoly_hollowSymmetricThree]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_C]

/-! ## The elementary-symmetric positive-semidefiniteness criterion at `3 x 3`

Mathlib has Sylvester in leading-minor form and this repository has it in
all-principal-minor form (`Gtz.posSemidef_three_of_principalMinors`).  Neither
closes (C1): the all-minors criterion demands each `2 x 2` principal minor of
`level . 1 + N` be nonnegative, i.e. every edge square be at most `level^2`, which
is exactly the conjunct the cap is supposed to make free.  What is needed instead is
the elementary-symmetric form — a symmetric `3 x 3` whose three elementary symmetric
functions are nonnegative is positive semidefinite — and that is not in Mathlib.  It
is proved here from the scalar core, which is the matrix-free sibling of the shipped
`Gtz.nonneg_of_elementarySymmetric_nonneg`. -/

/-- **The scalar core.**  A real root of `X^3 - e1 X^2 + e2 X - e3` with all three
coefficients `e1, e2, e3` nonnegative is itself nonnegative: were it negative, the
identity `root^3 = e1 root^2 - e2 root + e3` would put a strictly negative number
equal to a sum of three nonnegative ones. -/
theorem nonneg_of_cubicRoot_of_elementarySymmetric_nonneg
    {root firstSymmetric secondSymmetric thirdSymmetric : ℝ}
    (hfirst : 0 ≤ firstSymmetric) (hsecond : 0 ≤ secondSymmetric)
    (hthird : 0 ≤ thirdSymmetric)
    (hroot : root ^ 3 = firstSymmetric * root ^ 2 - secondSymmetric * root + thirdSymmetric) :
    0 ≤ root := by
  by_contra hnegative
  rw [not_le] at hnegative
  nlinarith [hroot, mul_nonneg hfirst (sq_nonneg root),
    mul_nonneg hsecond (neg_pos.mpr hnegative).le,
    mul_pos (mul_pos (neg_pos.mpr hnegative) (neg_pos.mpr hnegative)) (neg_pos.mpr hnegative)]

/-- **The scalar core, strict.**  A real root of `X^3 - e1 X^2 + e2 X - e3` with `e1`
and `e2` nonnegative and `e3` strictly positive is strictly positive. -/
theorem pos_of_cubicRoot_of_elementarySymmetric_pos
    {root firstSymmetric secondSymmetric thirdSymmetric : ℝ}
    (hfirst : 0 ≤ firstSymmetric) (hsecond : 0 ≤ secondSymmetric)
    (hthird : 0 < thirdSymmetric)
    (hroot : root ^ 3 = firstSymmetric * root ^ 2 - secondSymmetric * root + thirdSymmetric) :
    0 < root := by
  by_contra hnonpositive
  rw [not_lt] at hnonpositive
  nlinarith [hroot, mul_nonneg hfirst (sq_nonneg root),
    mul_nonneg hsecond (neg_nonneg.mpr hnonpositive),
    mul_nonneg (mul_nonneg (neg_nonneg.mpr hnonpositive) (neg_nonneg.mpr hnonpositive))
      (neg_nonneg.mpr hnonpositive)]

/-- **Positive semidefiniteness from the three elementary symmetric functions, rank
three.**  No strictness, no leading-minor ordering, no degeneracy gap.  Every
eigenvalue is a root of the characteristic polynomial, whose coefficients are the
three elementary symmetric functions of the entries; the scalar core does the rest. -/
theorem posSemidef_three_of_elementarySymmetric {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymmetric : formᵀ = form)
    (hfirst : 0 ≤ form 0 0 + form 1 1 + form 2 2)
    (hsecond : 0 ≤ (form 0 0 * form 1 1 - form 0 1 * form 1 0)
        + (form 0 0 * form 2 2 - form 0 2 * form 2 0)
        + (form 1 1 * form 2 2 - form 1 2 * form 2 1))
    (hthird : 0 ≤ form.det) : form.PosSemidef := by
  have hhermitian : form.IsHermitian := isHermitian_of_transpose_eq hsymmetric
  refine hhermitian.posSemidef_iff_eigenvalues_nonneg.mpr fun eigenIndex => ?_
  set eigenvalue : ℝ := hhermitian.eigenvalues eigenIndex with heigenvalue
  have hroot : ((Matrix.scalar (Fin 3)) eigenvalue - form).det = 0 := by
    rw [← Matrix.eval_charpoly, hhermitian.charpoly_eq, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ eigenIndex) (by simp [heigenvalue])
  rw [Matrix.det_fin_three] at hroot
  simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Fin.reduceEq,
    if_true, if_false, zero_sub] at hroot
  rw [Matrix.det_fin_three] at hthird
  refine nonneg_of_cubicRoot_of_elementarySymmetric_nonneg hfirst hsecond hthird ?_
  linear_combination hroot

/-- **Positive definiteness from the three elementary symmetric functions, rank
three.**  The strict twin, needed by the strict-domination layer. -/
theorem posDef_three_of_elementarySymmetric {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymmetric : formᵀ = form)
    (hfirst : 0 ≤ form 0 0 + form 1 1 + form 2 2)
    (hsecond : 0 ≤ (form 0 0 * form 1 1 - form 0 1 * form 1 0)
        + (form 0 0 * form 2 2 - form 0 2 * form 2 0)
        + (form 1 1 * form 2 2 - form 1 2 * form 2 1))
    (hthird : 0 < form.det) : form.PosDef := by
  have hhermitian : form.IsHermitian := isHermitian_of_transpose_eq hsymmetric
  refine hhermitian.posDef_iff_eigenvalues_pos.mpr fun eigenIndex => ?_
  set eigenvalue : ℝ := hhermitian.eigenvalues eigenIndex with heigenvalue
  have hroot : ((Matrix.scalar (Fin 3)) eigenvalue - form).det = 0 := by
    rw [← Matrix.eval_charpoly, hhermitian.charpoly_eq, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ eigenIndex) (by simp [heigenvalue])
  rw [Matrix.det_fin_three] at hroot
  simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Fin.reduceEq,
    if_true, if_false, zero_sub] at hroot
  rw [Matrix.det_fin_three] at hthird
  refine pos_of_cubicRoot_of_elementarySymmetric_pos hfirst hsecond hthird ?_
  linear_combination hroot

/-! ## The cap-free baseline: the full entrywise criterion

Homogenising by the level turns `level . 1 + N` into a scalar multiple of the
shipped unit-diagonal correlation matrix, so the shipped elliptope criterion applies
verbatim.  Its four conjuncts are the honest statement of what has to be checked with
no cap in hand. -/

/-- Scaling a hollow symmetric form scales its three entries. -/
theorem smul_hollowSymmetricThree (scale edgeFirst edgeSecond edgeThird : ℝ) :
    scale • hollowSymmetricThree edgeFirst edgeSecond edgeThird
      = hollowSymmetricThree (scale * edgeFirst) (scale * edgeSecond) (scale * edgeThird) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [hollowSymmetricThree]

/-- The homogenisation.  For `level` nonzero, `level . 1 + N` is `level` times the
unit-diagonal correlation matrix of the rescaled entries. -/
theorem smul_one_add_hollowSymmetricThree_eq_smul_correlationMatrixThree
    {level : ℝ} (hlevel : level ≠ 0) (edgeFirst edgeSecond edgeThird : ℝ) :
    level • (1 : Matrix (Fin 3) (Fin 3) ℝ) + hollowSymmetricThree edgeFirst edgeSecond edgeThird
      = level • correlationMatrixThree (edgeFirst / level) (edgeSecond / level)
          (edgeThird / level) := by
  have hcancel : ∀ entry : ℝ, level * (entry / level) = entry := by
    intro entry
    field_simp
  rw [correlationMatrixThree_eq_one_add_hollowSymmetricThree, smul_add, smul_smul,
    smul_hollowSymmetricThree, mul_one, hcancel, hcancel, hcancel]

/-- The elliptope bracket of the rescaled entries is the shifted determinant divided
by `level^3`. -/
theorem elliptopeBracket_div_eq_det_div
    {level : ℝ} (hlevel : level ≠ 0) (edgeFirst edgeSecond edgeThird : ℝ) :
    elliptopeBracket (edgeFirst / level) (edgeSecond / level) (edgeThird / level)
      = (level ^ 3 - level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
          + 2 * (edgeFirst * edgeSecond * edgeThird)) / level ^ 3 := by
  rw [elliptopeBracket]
  field_simp
  ring

/-- **The cap-free criterion, complete.**  For `level > 0` the shifted form is
positive semidefinite exactly when the three edge squares are at most `level^2` and
the shifted determinant is nonnegative.  All four conjuncts are load-bearing: the
determinant conjunct alone is the rogue branch, refuted at the end of this file. -/
theorem posSemidef_smul_one_add_hollowSymmetricThree_iff
    {level : ℝ} (hlevel : 0 < level) (edgeFirst edgeSecond edgeThird : ℝ) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
      ↔ edgeFirst ^ 2 ≤ level ^ 2 ∧ edgeSecond ^ 2 ≤ level ^ 2 ∧ edgeThird ^ 2 ≤ level ^ 2
        ∧ level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
            - 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3 := by
  have hcube : (0 : ℝ) < level ^ 3 := by positivity
  have hsquare : (0 : ℝ) < level ^ 2 := by positivity
  rw [smul_one_add_hollowSymmetricThree_eq_smul_correlationMatrixThree hlevel.ne',
    posSemidef_smul_iff hlevel, posSemidef_correlationMatrixThree_iff,
    elliptopeBracket_div_eq_det_div hlevel.ne']
  have hedge : ∀ entry : ℝ, (entry / level) ^ 2 ≤ 1 ↔ entry ^ 2 ≤ level ^ 2 := by
    intro entry
    rw [div_pow, div_le_one hsquare]
  rw [hedge, hedge, hedge]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [le_div_iff₀ hcube, zero_mul]
  constructor <;> intro hbound <;> linarith

/-- The same criterion for the reflected form `level . 1 - N`, which is how the norm
cap presents itself. -/
theorem posSemidef_smul_one_sub_hollowSymmetricThree_iff
    {level : ℝ} (hlevel : 0 < level) (edgeFirst edgeSecond edgeThird : ℝ) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
      ↔ edgeFirst ^ 2 ≤ level ^ 2 ∧ edgeSecond ^ 2 ≤ level ^ 2 ∧ edgeThird ^ 2 ≤ level ^ 2
        ∧ level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
            + 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3 := by
  rw [smul_one_sub_hollowSymmetricThree,
    posSemidef_smul_one_add_hollowSymmetricThree_iff hlevel]
  constructor
  · rintro ⟨hfirst, hsecond, hthird, hdeterminant⟩
    exact ⟨by nlinarith [hfirst], by nlinarith [hsecond], by nlinarith [hthird], by nlinarith⟩
  · rintro ⟨hfirst, hsecond, hthird, hdeterminant⟩
    exact ⟨by nlinarith [hfirst], by nlinarith [hsecond], by nlinarith [hthird], by nlinarith⟩

/-- **The `rho = (3/2) gamma` dictionary of the equal-share stratum.**  At threshold
`2/3` the shifted form is positive semidefinite exactly when the correlation matrix
of the entries scaled by `3/2` is.  This is the coordinate change between the pen's
direction cosines and the repository's `Gtz.normalizedPairing`, stated as an
equivalence rather than asserted. -/
theorem posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_iff_correlationMatrixThree
    (edgeFirst edgeSecond edgeThird : ℝ) :
    ((2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
      ↔ (correlationMatrixThree (3 * edgeFirst / 2) (3 * edgeSecond / 2)
          (3 * edgeThird / 2)).PosSemidef := by
  have hlevel : (0 : ℝ) < 2 / 3 := by norm_num
  have hrescale : ∀ entry : ℝ, entry / (2 / 3 : ℝ) = 3 * entry / 2 := by
    intro entry
    ring
  rw [smul_one_add_hollowSymmetricThree_eq_smul_correlationMatrixThree hlevel.ne',
    posSemidef_smul_iff hlevel, hrescale, hrescale, hrescale]

/-- **The bracket dictionary of the equal-share stratum.**  The shipped elliptope
bracket evaluated at the rescaled entries IS the criterion residual, scaled by `9/4`:
`bracket(3a/2, 3b/2, 3c/2) = (9/4)(4/9 - sigma + 3P)`.  So `0 <= bracket` and
`sigma - 3P <= 4/9` are literally the same inequality, and every lemma of
`Gtz.LinAlg.ElliptopeInterval` applies to the criterion after this rewrite. -/
theorem elliptopeBracket_threeHalves_eq_criterionResidual
    (edgeFirst edgeSecond edgeThird : ℝ) :
    elliptopeBracket (3 * edgeFirst / 2) (3 * edgeSecond / 2) (3 * edgeThird / 2)
      = 9 / 4 * (4 / 9 - (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
        + 3 * (edgeFirst * edgeSecond * edgeThird)) := by
  rw [elliptopeBracket]
  ring

/-! ## (C1) split into its two halves, before the cap enters

The forward direction is a determinant sign and needs nothing.  The backward
direction needs the second elementary symmetric function `3 level^2 - sigma` and
nothing else.  The cap enters between them, and only there. -/

/-- **The forward direction, cap-free.**  Positive semidefiniteness forces the
criterion at every level. -/
theorem determinantCriterion_of_posSemidef_smul_one_add_hollowSymmetricThree
    {level edgeFirst edgeSecond edgeThird : ℝ}
    (hpsd : (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      - 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3 := by
  have hdeterminant := hpsd.det_nonneg
  rw [det_smul_one_add_hollowSymmetricThree] at hdeterminant
  linarith

/-- **The backward direction, cap-free.**  With the second elementary symmetric
function supplied as `sigma <= 3 level^2`, the criterion alone gives positive
semidefiniteness.  This is where `posSemidef_three_of_elementarySymmetric` is spent. -/
theorem posSemidef_smul_one_add_hollowSymmetricThree_of_squareSum_le
    {level edgeFirst edgeSecond edgeThird : ℝ} (hlevel : 0 ≤ level)
    (hsquareSum : edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2 ≤ 3 * level ^ 2)
    (hcriterion : level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      - 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef := by
  have hdeterminant : (0 : ℝ) ≤ (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird).det := by
    rw [det_smul_one_add_hollowSymmetricThree]
    linarith
  rw [smul_one_add_hollowSymmetricThree] at hdeterminant ⊢
  refine posSemidef_three_of_elementarySymmetric ?_ ?_ ?_ hdeterminant
  · ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> rfl
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
    linarith
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
    nlinarith [hsquareSum]

/-! ## (C2): what the norm cap says about `sigma` and `P`

Two determinant signs, nothing else.  Only the upper half is used by (C1) and (C3);
the lower half is needed exactly for the absolute-value form. -/

/-- The upper cap forces its own level to be nonnegative — read off the diagonal, so
`0 <= cap` never has to be carried as a hypothesis. -/
theorem nonneg_of_posSemidef_smul_one_sub_hollowSymmetricThree
    {cap edgeFirst edgeSecond edgeThird : ℝ}
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    0 ≤ cap := by
  have hdiagonal := hcap.diag_nonneg (i := 0)
  simpa [hollowSymmetricThree, Matrix.one_apply] using hdiagonal

/-- **(C2), upper half.**  `cap sigma + 2P <= cap^3`. -/
theorem mul_squareSum_add_two_mul_product_le_of_spectralCapUpper
    {cap edgeFirst edgeSecond edgeThird : ℝ}
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    cap * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      + 2 * (edgeFirst * edgeSecond * edgeThird) ≤ cap ^ 3 := by
  have hdeterminant := hcap.det_nonneg
  rw [det_smul_one_sub_hollowSymmetricThree] at hdeterminant
  linarith

/-- **(C2), lower half.**  `cap sigma - 2P <= cap^3`. -/
theorem mul_squareSum_sub_two_mul_product_le_of_spectralCapLower
    {cap edgeFirst edgeSecond edgeThird : ℝ}
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    cap * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      - 2 * (edgeFirst * edgeSecond * edgeThird) ≤ cap ^ 3 :=
  determinantCriterion_of_posSemidef_smul_one_add_hollowSymmetricThree hcap

/-- **(C2).**  Both halves of the cap give `cap sigma + 2|P| <= cap^3`.  Every root of
the cubic lies in `[-cap, cap]`, so the cubic is nonnegative at `cap` and nonpositive
at `-cap`, and those two signs are exactly these two inequalities. -/
theorem mul_squareSum_add_two_mul_abs_product_le_of_spectralCap
    {cap edgeFirst edgeSecond edgeThird : ℝ}
    (hupper : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef)
    (hlower : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    cap * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      + 2 * |edgeFirst * edgeSecond * edgeThird| ≤ cap ^ 3 := by
  have hupperBound := mul_squareSum_add_two_mul_product_le_of_spectralCapUpper hupper
  have hlowerBound := mul_squareSum_sub_two_mul_product_le_of_spectralCapLower hlower
  rcases abs_cases (edgeFirst * edgeSecond * edgeThird) with ⟨habs, _⟩ | ⟨habs, _⟩ <;>
    rw [habs] <;> linarith

/-- **(C2) at the involution cap `cap = 1`**, in the pen's own form
`sigma + 2|P| <= 1`.  The hypotheses are the two Loewner facts a symmetric involution
delivers by compression, with no scalar multiplication in sight. -/
theorem squareSum_add_two_mul_abs_product_le_one
    {edgeFirst edgeSecond edgeThird : ℝ}
    (hupper : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef)
    (hlower : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2
      + 2 * |edgeFirst * edgeSecond * edgeThird| ≤ 1 := by
  rw [← one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ)] at hupper hlower
  have hbound := mul_squareSum_add_two_mul_abs_product_le_of_spectralCap hupper hlower
  linarith [hbound]

/-! ## The hinge: the single step of (C1) that consumes the cap -/

/-- **The `P`-cancelling addition.**  Adding the upper cap determinant to the
criterion annihilates the oriented product and leaves a pure statement about
`sigma`.  Division-free, and no positivity hypothesis at all. -/
theorem add_mul_squareSum_le_of_spectralCapUpper_of_determinantCriterion
    {cap level edgeFirst edgeSecond edgeThird : ℝ}
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef)
    (hcriterion : level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      - 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3) :
    (level + cap) * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      ≤ level ^ 3 + cap ^ 3 := by
  have hcapBound := mul_squareSum_add_two_mul_product_le_of_spectralCapUpper hcap
  nlinarith [hcapBound, hcriterion]

/-- **THE HINGE.**  `sigma <= 3 level^2`, the second elementary symmetric function of
`level . 1 + N`, is available as soon as the criterion holds and the UPPER norm cap
satisfies `cap <= 2 * level`.  This is the unique place in the whole criterion where
the cap is consumed, and the lower half of the cap is never used.  The mechanism is
the factorisation

    3 level^2 (level + cap) - (level^3 + cap^3) = (2 level - cap) (level + cap)^2,

whose sign is governed by `cap <= 2 * level` alone.  `exists_hollowSymmetricThree_capSharpness`
shows the threshold cannot be relaxed. -/
theorem squareSum_le_three_mul_sq_of_spectralCapUpper
    {cap level edgeFirst edgeSecond edgeThird : ℝ} (hlevel : 0 < level)
    (hcapLe : cap ≤ 2 * level)
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef)
    (hcriterion : level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      - 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3) :
    edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2 ≤ 3 * level ^ 2 := by
  have hcapNonneg := nonneg_of_posSemidef_smul_one_sub_hollowSymmetricThree hcap
  have hsumPos : 0 < level + cap := by linarith
  have hsum := add_mul_squareSum_le_of_spectralCapUpper_of_determinantCriterion hcap hcriterion
  have hfactor : (level + cap) * (3 * level ^ 2)
      = level ^ 3 + cap ^ 3 + (2 * level - cap) * (level + cap) ^ 2 := by ring
  have hslack : 0 ≤ (2 * level - cap) * (level + cap) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  refine le_of_mul_le_mul_left ?_ hsumPos
  rw [hfactor]
  linarith

/-! ## (C1): the criterion, as an equivalence -/

/-- **(C1), the criterion, general cap.**  For a hollow symmetric `3 x 3` whose
UPPER norm cap is `cap` with `cap <= 2 * level`,

    (level . 1 + N) positive semidefinite   <->   level sigma - 2P <= level^3.

The forward direction is a determinant sign; the backward direction is the
elementary-symmetric criterion, whose only missing input is `sigma <= 3 level^2`, and
that input is exactly what the hinge extracts from the cap.  Instantiate `cap = 1`,
`level = 2/3` for the equal-share `(6,3)` stratum and `cap = 4/3` for `(7,3)`. -/
theorem posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper
    {cap level edgeFirst edgeSecond edgeThird : ℝ} (hlevel : 0 < level)
    (hcapLe : cap ≤ 2 * level)
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
      ↔ level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
          - 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3 := by
  refine ⟨determinantCriterion_of_posSemidef_smul_one_add_hollowSymmetricThree, fun hcriterion => ?_⟩
  exact posSemidef_smul_one_add_hollowSymmetricThree_of_squareSum_le hlevel.le
    (squareSum_le_three_mul_sq_of_spectralCapUpper hlevel hcapLe hcap hcriterion) hcriterion

/-- **(C1) at the equal-share `(6,3)` stratum**, in the pen's own normalisation:
the involution cap `cap = 1`, the threshold `level = 2/3`, and the criterion
`sigma - 3P <= 4/9`.  The hypothesis is the compression of the involution sandwich,
stated with no scalar multiplication so that it matches what `1 - M[C]` delivers. -/
theorem posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper
    {edgeFirst edgeSecond edgeThird : ℝ}
    (hcap : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    ((2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
      ↔ edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2
          - 3 * (edgeFirst * edgeSecond * edgeThird) ≤ 4 / 9 := by
  rw [← one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ)] at hcap
  rw [posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper (by norm_num)
    (by norm_num) hcap]
  constructor <;> intro hbound <;> nlinarith [hbound]

/-- **The reflected criterion, for the other side of a mirror pair.**  Applying (C1)
to `-N` exchanges the two halves of the cap and flips the sign of the oriented
product, leaving `sigma` untouched.  A consumer holding the complementary triple of a
`3-3` split gets its criterion from here without re-deriving anything. -/
theorem posSemidef_smul_one_sub_hollowSymmetricThree_iff_of_spectralCapLower
    {cap level edgeFirst edgeSecond edgeThird : ℝ} (hlevel : 0 < level)
    (hcapLe : cap ≤ 2 * level)
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
      ↔ level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
          + 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3 := by
  have hreflect : cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree (-edgeFirst) (-edgeSecond) (-edgeThird)
      = cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird := by
    rw [smul_one_sub_hollowSymmetricThree, neg_neg, neg_neg, neg_neg]
  rw [smul_one_sub_hollowSymmetricThree,
    posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper hlevel hcapLe
      (by rw [hreflect]; exact hcap)]
  constructor <;> intro hbound <;> nlinarith [hbound]

/-- **(C1), strict.**  Under the same cap, positive DEFINITENESS is the strict
criterion.  The hinge runs verbatim with one strict inequality, giving
`sigma < 3 level^2`, and the strict elementary-symmetric criterion closes it.  This is
what the strict-domination layer consumes. -/
theorem posDef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper
    {cap level edgeFirst edgeSecond edgeThird : ℝ} (hlevel : 0 < level)
    (hcapLe : cap ≤ 2 * level)
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosDef
      ↔ level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
          - 2 * (edgeFirst * edgeSecond * edgeThird) < level ^ 3 := by
  constructor
  · intro hposDef
    have hdeterminant := hposDef.det_pos
    rw [det_smul_one_add_hollowSymmetricThree] at hdeterminant
    linarith
  · intro hcriterion
    have hcapNonneg := nonneg_of_posSemidef_smul_one_sub_hollowSymmetricThree hcap
    have hsumPos : 0 < level + cap := by linarith
    have hcapBound := mul_squareSum_add_two_mul_product_le_of_spectralCapUpper hcap
    have hsum : (level + cap) * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
        < level ^ 3 + cap ^ 3 := by nlinarith [hcapBound, hcriterion]
    have hfactor : (level + cap) * (3 * level ^ 2)
        = level ^ 3 + cap ^ 3 + (2 * level - cap) * (level + cap) ^ 2 := by ring
    have hslack : 0 ≤ (2 * level - cap) * (level + cap) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hsquareSum : edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2 < 3 * level ^ 2 := by
      refine lt_of_mul_lt_mul_left ?_ hsumPos.le
      rw [hfactor]
      linarith
    have hdeterminant : (0 : ℝ) < (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird).det := by
      rw [det_smul_one_add_hollowSymmetricThree]
      linarith
    rw [smul_one_add_hollowSymmetricThree] at hdeterminant ⊢
    refine posDef_three_of_elementarySymmetric ?_ ?_ ?_ hdeterminant
    · ext rowIndex colIndex
      fin_cases rowIndex <;> fin_cases colIndex <;> rfl
    · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.of_apply]
      linarith
    · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.of_apply]
      nlinarith [hsquareSum]

/-! ### The cell transfer: which caps reach which thresholds

The hinge `cap <= 2 * level` is the whole transfer law, and it is sharp
(`exists_hollowSymmetricThree_capSharpness`).  Two consequences are recorded here so
that the sizes above six do not have to re-derive them.

On the uniform equal-leverage rank-three stratum at size `size`, the direction Gram
satisfies `Gamma^2 = (size/3) Gamma`, so `M = Gamma - 1` satisfies
`M^2 = (size/3 - 2) M + (size/3 - 1)`; the quadratic factors as
`(x - (size/3 - 1))(x + 1)`, so the spectrum of `M` is contained in
`{size/3 - 1, -1}` and the cap is `size/3 - 1` — one at `size = 6`, four thirds at
`size = 7`.  Both facts below are the arithmetic of that reading, kernel-checked; the
design-level quadratic itself belongs to the involution layer. -/

/-- The quadratic satisfied by `M` on the uniform equal-leverage stratum factors with
roots `size/3 - 1` and `-1`.  At `size = 6` the roots are `1` and `-1`: the
involution. -/
theorem uniformStratumQuadratic_factor (size root : ℝ) :
    root ^ 2 - (size / 3 - 2) * root - (size / 3 - 1)
      = (root - (size / 3 - 1)) * (root + 1) := by ring

/-- **The transfer boundary is `size = 7`.**  With threshold `2/3` the hinge allows a
cap of at most `4/3`, and the uniform stratum's cap `size/3 - 1` clears that bound
exactly up to size seven.  So the cubic criterion is available at `(6,3)` and at
`(7,3)` — the campaign's frontier — and at no larger size on that stratum. -/
theorem uniformStratumCap_le_hinge_iff_size_le_seven (size : ℝ) :
    size / 3 - 1 ≤ 2 * (2 / 3) ↔ size ≤ 7 := by
  constructor <;> intro hbound <;> linarith

/-- **(C1) at the `(7,3)` cap `4/3`.**  The instantiation the rank-three frontier
needs, with the threshold left free above `2/3`; at `level = 2/3` the hinge holds with
equality, which is exactly why seven is the last size this criterion reaches. -/
theorem posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapFourThirds
    {level edgeFirst edgeSecond edgeThird : ℝ} (hlevel : 2 / 3 ≤ level)
    (hcap : ((4 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
      ↔ level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
          - 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3 :=
  posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper (by linarith)
    (by linarith) hcap

/-! ## (C3): the heavy cell, on the coherent side only -/

/-- **(C3), general cap.**  The criterion holds as soon as the oriented product
clears `level * cap * (cap - level) / 2`.  Proof: the upper cap gives
`cap sigma <= cap^3 - 2P`, and

    cap (level^3 - level sigma + 2P)
      = level (cap^3 - cap sigma - 2P) + (level + cap) (2P - level cap (cap - level)),

so both summands are nonnegative and `cap > 0` divides out.  Only the upper half of
the cap is used.  The hypothesis is on `P`, NOT on `|P|` — see
`exists_spectralCapped_hollowSymmetricThree_incoherent_heavy_not_posSemidef`. -/
theorem determinantCriterion_of_spectralCapUpper_of_heavyProduct
    {cap level edgeFirst edgeSecond edgeThird : ℝ} (hcapPos : 0 < cap) (hlevel : 0 < level)
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef)
    (hheavy : level * cap * (cap - level) ≤ 2 * (edgeFirst * edgeSecond * edgeThird)) :
    level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      - 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3 := by
  have hcapBound := mul_squareSum_add_two_mul_product_le_of_spectralCapUpper hcap
  have hleft : 0 ≤ level * (cap ^ 3
      - (cap * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
        + 2 * (edgeFirst * edgeSecond * edgeThird))) :=
    mul_nonneg hlevel.le (by linarith)
  have hright : 0 ≤ (level + cap) * (2 * (edgeFirst * edgeSecond * edgeThird)
      - level * cap * (cap - level)) :=
    mul_nonneg (by linarith) (by linarith)
  have hproduct : 0 ≤ cap * (level ^ 3
      - (level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
        - 2 * (edgeFirst * edgeSecond * edgeThird))) := by nlinarith [hleft, hright]
  nlinarith [hproduct, hcapPos]

/-- **(C3), general cap, in Loewner form.** -/
theorem posSemidef_smul_one_add_hollowSymmetricThree_of_spectralCapUpper_of_heavyProduct
    {cap level edgeFirst edgeSecond edgeThird : ℝ} (hcapPos : 0 < cap) (hlevel : 0 < level)
    (hcapLe : cap ≤ 2 * level)
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef)
    (hheavy : level * cap * (cap - level) ≤ 2 * (edgeFirst * edgeSecond * edgeThird)) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef :=
  (posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper hlevel hcapLe hcap).mpr
    (determinantCriterion_of_spectralCapUpper_of_heavyProduct hcapPos hlevel hcap hheavy)

/-- **(C3) at the equal-share `(6,3)` stratum: the heavy cell `P >= 1/9`.**  The
threshold `level cap (cap - level) / 2` becomes `(2/3)(1)(1/3)/2 = 1/9` exactly. -/
theorem posSemidef_twoThirds_of_spectralCapUpper_of_ninth_le_product
    {edgeFirst edgeSecond edgeThird : ℝ}
    (hcap : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef)
    (hheavy : 1 / 9 ≤ edgeFirst * edgeSecond * edgeThird) :
    ((2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef := by
  rw [← one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ)] at hcap
  refine posSemidef_smul_one_add_hollowSymmetricThree_of_spectralCapUpper_of_heavyProduct
    (by norm_num) (by norm_num) (by norm_num) hcap ?_
  linarith

/-- **(C3) in the pen's `|P|` phrasing, with the coherence hypothesis made explicit.**
The magnitude reading is legitimate ONLY together with `0 <= P`; the two-sided
reading is refuted below. -/
theorem posSemidef_twoThirds_of_spectralCapUpper_of_coherent_of_ninth_le_abs_product
    {edgeFirst edgeSecond edgeThird : ℝ}
    (hcap : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef)
    (hcoherent : 0 ≤ edgeFirst * edgeSecond * edgeThird)
    (hheavy : 1 / 9 ≤ |edgeFirst * edgeSecond * edgeThird|) :
    ((2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef := by
  refine posSemidef_twoThirds_of_spectralCapUpper_of_ninth_le_product hcap ?_
  rwa [abs_of_nonneg hcoherent] at hheavy

/-! ## Calibration

Three reference configurations, checked against the criterion rather than asserted.
The tetrahedral tripod is the TIE, the `K4` star is comfortably inside and saturates
(C2), and the icosahedral coherent triple is inside the criterion but OUTSIDE the
heavy cell (C3) — which is precisely why (C3) alone does not decide the equal-share
stratum and a squeeze is needed. -/

/-- **The tetrahedral tripod is the tie.**  Three unit directions pairwise at
`cos = -1/3` give `sigma - 3P = 1/3 + 1/9 = 4/9` exactly. -/
theorem criterion_hollowSymmetricThree_negThird_eq_fourNinths :
    (-(1 / 3 : ℝ)) ^ 2 + (-(1 / 3 : ℝ)) ^ 2 + (-(1 / 3 : ℝ)) ^ 2
      - 3 * ((-(1 / 3 : ℝ)) * (-(1 / 3 : ℝ)) * (-(1 / 3 : ℝ))) = 4 / 9 := by norm_num

/-- The tie sits on the positive-semidefinite boundary: the shifted determinant is
exactly zero, so `lambda_min(Gamma) = 1/3` on the nose. -/
theorem det_twoThirds_smul_one_add_hollowSymmetricThree_negThird :
    (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree (-(1 / 3)) (-(1 / 3)) (-(1 / 3))).det = 0 := by
  rw [det_smul_one_add_hollowSymmetricThree]
  norm_num

theorem posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_negThird :
    (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree (-(1 / 3)) (-(1 / 3)) (-(1 / 3))).PosSemidef := by
  rw [posSemidef_smul_one_add_hollowSymmetricThree_iff (by norm_num : (0 : ℝ) < 2 / 3)]
  norm_num

/-- **The `K4` star.**  Three unit directions pairwise at `cos = 1/2` give
`sigma - 3P = 3/8`, comfortably below `4/9`, and `lambda_min(Gamma) = 1/2`. -/
theorem criterion_hollowSymmetricThree_half_eq_threeEighths :
    ((1 : ℝ) / 2) ^ 2 + ((1 : ℝ) / 2) ^ 2 + ((1 : ℝ) / 2) ^ 2
      - 3 * (((1 : ℝ) / 2) * ((1 : ℝ) / 2) * ((1 : ℝ) / 2)) = 3 / 8 := by norm_num

theorem posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_half :
    (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree (1 / 2) (1 / 2) (1 / 2)).PosSemidef := by
  rw [posSemidef_smul_one_add_hollowSymmetricThree_iff (by norm_num : (0 : ℝ) < 2 / 3)]
  norm_num

/-- **(C2) is TIGHT at the `K4` star**: `sigma + 2|P| = 3/4 + 1/4 = 1`.  Equivalently
`+1` is an eigenvalue of the star's `M`, which is the statement that the complementary
`K4` triangle is linearly dependent. -/
theorem squareSum_add_two_mul_abs_product_hollowSymmetricThree_half_eq_one :
    ((1 : ℝ) / 2) ^ 2 + ((1 : ℝ) / 2) ^ 2 + ((1 : ℝ) / 2) ^ 2
      + 2 * |((1 : ℝ) / 2) * ((1 : ℝ) / 2) * ((1 : ℝ) / 2)| = 1 := by
  rw [show ((1 : ℝ) / 2) * ((1 : ℝ) / 2) * ((1 : ℝ) / 2) = 1 / 8 by norm_num,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)]
  norm_num

/-- The `K4` star lies in the heavy cell: `P = 1/8 >= 1/9`, so (C3) fires there. -/
theorem heavyProduct_hollowSymmetricThree_half :
    (1 : ℝ) / 9 ≤ ((1 : ℝ) / 2) * ((1 : ℝ) / 2) * ((1 : ℝ) / 2) := by norm_num

/-- **The icosahedral coherent triple satisfies the criterion.**  At the equiangular
value `cos = 1/sqrt 5` one has `sigma = 3/5` and `P = sqrt 5 / 25`, and
`3/5 - 3 sqrt 5 / 25 <= 4/9` because `35 <= 27 sqrt 5`. -/
theorem criterion_hollowSymmetricThree_equiangularFifth :
    (Real.sqrt 5 / 5) ^ 2 + (Real.sqrt 5 / 5) ^ 2 + (Real.sqrt 5 / 5) ^ 2
      - 3 * ((Real.sqrt 5 / 5) * (Real.sqrt 5 / 5) * (Real.sqrt 5 / 5)) ≤ 4 / 9 := by
  have hsquare : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpositive : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [hsquare, hpositive]

/-- **... but it is OUTSIDE the heavy cell.**  `P = sqrt 5 / 25 < 1/9`, because
`9 sqrt 5 < 25`.  So (C3) does not fire at the icosahedron even though the criterion
holds there with room to spare, and the heavy cell is strictly weaker than the
criterion it certifies. -/
theorem not_heavyProduct_hollowSymmetricThree_equiangularFifth :
    (Real.sqrt 5 / 5) * (Real.sqrt 5 / 5) * (Real.sqrt 5 / 5) < 1 / 9 := by
  have hsquare : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpositive : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [hsquare, hpositive]

/-! ## Refutations

Three exactly rational witnesses.  The first shows the cap cannot be dropped from
(C1); the second shows the threshold `cap <= 2 * level` cannot be relaxed; the third
shows the magnitude reading of (C3) is false without coherence. -/

/-- The rogue configuration `a = b = c = 1` satisfies the criterion `sigma - 3P <= 4/9`
with room to spare — its value is `0`. -/
theorem criterion_hollowSymmetricThree_one_one_one :
    (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 - 3 * ((1 : ℝ) * 1 * 1) ≤ 4 / 9 := by norm_num

/-- ... and yet it is not positive semidefinite at the threshold `2/3`: its edge
squares are `1`, far above `(2/3)^2`.  This is the pen's rogue branch, where the
determinant is nonnegative because TWO eigenvalues have dropped below `-2/3`. -/
theorem not_posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_one_one_one :
    ¬ (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree 1 1 1).PosSemidef := by
  rw [posSemidef_smul_one_add_hollowSymmetricThree_iff (by norm_num : (0 : ℝ) < 2 / 3)]
  rintro ⟨hfirst, -, -, -⟩
  norm_num at hfirst

/-- The rogue configuration is excluded by the norm cap and by nothing else: its
upper cap at level one fails, because `det(1 - N) = 1 - 3 - 2 = -4 < 0`. -/
theorem not_posSemidef_one_sub_hollowSymmetricThree_one_one_one :
    ¬ ((1 : Matrix (Fin 3) (Fin 3) ℝ) - hollowSymmetricThree 1 1 1).PosSemidef := by
  rw [← one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ),
    posSemidef_smul_one_sub_hollowSymmetricThree_iff (by norm_num : (0 : ℝ) < 1)]
  rintro ⟨-, -, -, hdeterminant⟩
  norm_num at hdeterminant

/-- **The cap is not removable from (C1).**  Without a norm-cap hypothesis the
criterion `sigma - 3P <= 4/9` does NOT imply positive semidefiniteness at `2/3`. -/
theorem exists_hollowSymmetricThree_criterion_without_posSemidef :
    ∃ edgeFirst edgeSecond edgeThird : ℝ,
      edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2
          - 3 * (edgeFirst * edgeSecond * edgeThird) ≤ 4 / 9
        ∧ ¬ (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
            + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
        ∧ ¬ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
            - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef :=
  ⟨1, 1, 1, criterion_hollowSymmetricThree_one_one_one,
    not_posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_one_one_one,
    not_posSemidef_one_sub_hollowSymmetricThree_one_one_one⟩

/-- **The hinge threshold `cap <= 2 * level` is SHARP.**  For every threshold
`level > 0` and every `cap > 2 * level`, the equilateral configuration
`a = b = c = cap/2` carries the cap at `cap` in both directions, satisfies the
criterion — because `level^3 - 3 h^2 level + 2 h^3 = (level - h)^2 (level + 2h)` is a
square times a positive factor — and is NOT positive semidefinite at `level`.  So no
relaxation of the hinge is possible, at any level, by any amount. -/
theorem exists_hollowSymmetricThree_capSharpness {cap level : ℝ} (hlevel : 0 < level)
    (hcapGt : 2 * level < cap) :
    ∃ edgeFirst edgeSecond edgeThird : ℝ,
      (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
          - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
        ∧ (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)
            + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
        ∧ level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
            - 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3
        ∧ ¬ (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
            + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef := by
  have hcapPos : 0 < cap := by linarith
  refine ⟨cap / 2, cap / 2, cap / 2, ?_, ?_, ?_, ?_⟩
  · rw [posSemidef_smul_one_sub_hollowSymmetricThree_iff hcapPos]
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rw [posSemidef_smul_one_add_hollowSymmetricThree_iff hcapPos]
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · nlinarith [sq_nonneg (level - cap / 2), mul_nonneg (sq_nonneg (level - cap / 2))
      (by linarith : (0 : ℝ) ≤ level + cap)]
  · rw [posSemidef_smul_one_add_hollowSymmetricThree_iff hlevel]
    rintro ⟨hfirst, -, -, -⟩
    nlinarith [hfirst]

/-- The `K4` incoherent triple `a = b = c = -1/2` carries the involution cap in both
directions; the lower half is TIGHT, `det(1 + N) = 0`. -/
theorem posSemidef_one_sub_hollowSymmetricThree_negHalf :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree (-(1 / 2)) (-(1 / 2)) (-(1 / 2))).PosSemidef := by
  rw [← one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ),
    posSemidef_smul_one_sub_hollowSymmetricThree_iff (by norm_num : (0 : ℝ) < 1)]
  norm_num

theorem posSemidef_one_add_hollowSymmetricThree_negHalf :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree (-(1 / 2)) (-(1 / 2)) (-(1 / 2))).PosSemidef := by
  rw [← one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ),
    posSemidef_smul_one_add_hollowSymmetricThree_iff (by norm_num : (0 : ℝ) < 1)]
  norm_num

/-- **(C3) READ WITH `|P|` ON BOTH SIDES IS FALSE.**  At `a = b = c = -1/2` the norm
cap holds in both directions, `|P| = 1/8 >= 1/9`, the product is strictly negative,
and the criterion fails badly: `sigma - 3P = 9/8`, more than twice `4/9`.  The
configuration is not artificial — flipping one atom's direction carries it to the
three edges of a `K4` triangle, the incoherent side of a mirror pair of the `K4`
graphic `(6,3)` design, whose coherent side `a = b = c = 1/2` dominates
(`posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_half`).  So the two-sided
reading refutes itself inside the campaign's own witness, and the coherence hypothesis
of `posSemidef_twoThirds_of_spectralCapUpper_of_coherent_of_ninth_le_abs_product`
cannot be dropped. -/
theorem exists_spectralCapped_hollowSymmetricThree_incoherent_heavy_not_posSemidef :
    ∃ edgeFirst edgeSecond edgeThird : ℝ,
      ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
        ∧ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
            + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef
        ∧ 1 / 9 ≤ |edgeFirst * edgeSecond * edgeThird|
        ∧ edgeFirst * edgeSecond * edgeThird < 0
        ∧ 4 / 9 < edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2
            - 3 * (edgeFirst * edgeSecond * edgeThird)
        ∧ ¬ (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
            + hollowSymmetricThree edgeFirst edgeSecond edgeThird).PosSemidef := by
  refine ⟨-(1 / 2), -(1 / 2), -(1 / 2), posSemidef_one_sub_hollowSymmetricThree_negHalf,
    posSemidef_one_add_hollowSymmetricThree_negHalf, ?_, by norm_num, by norm_num, ?_⟩
  · rw [show (-(1 / 2 : ℝ)) * (-(1 / 2 : ℝ)) * (-(1 / 2 : ℝ)) = -(1 / 8) by norm_num]
    rw [abs_of_nonpos (by norm_num : (-(1 / 8) : ℝ) ≤ 0)]
    norm_num
  · rw [posSemidef_smul_one_add_hollowSymmetricThree_iff (by norm_num : (0 : ℝ) < 2 / 3)]
    rintro ⟨-, -, -, hdeterminant⟩
    norm_num at hdeterminant

/-! ## Entry-indexed wrappers

Consumers hold an abstract symmetric hollow form — the compression `M[C]` of a
design's direction Gram minus the identity — not the constructor.  These wrappers
take the three entry equations, which are `rfl` when the consumer is content with
`form 0 1` and its siblings as names. -/

/-- **(C1) for an abstract hollow symmetric form.** -/
theorem posSemidef_smul_one_add_iff_of_hollow_of_entries
    {form : Matrix (Fin 3) (Fin 3) ℝ} {cap level edgeFirst edgeSecond edgeThird : ℝ}
    (hsymmetric : formᵀ = form) (hdiagonal : ∀ index : Fin 3, form index index = 0)
    (hfirst : form 0 1 = edgeFirst) (hsecond : form 0 2 = edgeSecond)
    (hthird : form 1 2 = edgeThird)
    (hlevel : 0 < level) (hcapLe : cap ≤ 2 * level)
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ) - form).PosSemidef) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ) + form).PosSemidef
      ↔ level * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
          - 2 * (edgeFirst * edgeSecond * edgeThird) ≤ level ^ 3 := by
  have hform : form = hollowSymmetricThree edgeFirst edgeSecond edgeThird := by
    rw [eq_hollowSymmetricThree_of_transpose_eq_of_diagonal_eq_zero hsymmetric hdiagonal,
      hfirst, hsecond, hthird]
  rw [hform] at hcap ⊢
  exact posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper hlevel hcapLe hcap

/-- **(C2) for an abstract hollow symmetric form.** -/
theorem mul_squareSum_add_two_mul_abs_product_le_of_hollow_of_entries
    {form : Matrix (Fin 3) (Fin 3) ℝ} {cap edgeFirst edgeSecond edgeThird : ℝ}
    (hsymmetric : formᵀ = form) (hdiagonal : ∀ index : Fin 3, form index index = 0)
    (hfirst : form 0 1 = edgeFirst) (hsecond : form 0 2 = edgeSecond)
    (hthird : form 1 2 = edgeThird)
    (hupper : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ) - form).PosSemidef)
    (hlower : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ) + form).PosSemidef) :
    cap * (edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2)
      + 2 * |edgeFirst * edgeSecond * edgeThird| ≤ cap ^ 3 := by
  have hform : form = hollowSymmetricThree edgeFirst edgeSecond edgeThird := by
    rw [eq_hollowSymmetricThree_of_transpose_eq_of_diagonal_eq_zero hsymmetric hdiagonal,
      hfirst, hsecond, hthird]
  rw [hform] at hupper hlower
  exact mul_squareSum_add_two_mul_abs_product_le_of_spectralCap hupper hlower

/-- **(C3) for an abstract hollow symmetric form.** -/
theorem posSemidef_smul_one_add_of_hollow_of_entries_of_heavyProduct
    {form : Matrix (Fin 3) (Fin 3) ℝ} {cap level edgeFirst edgeSecond edgeThird : ℝ}
    (hsymmetric : formᵀ = form) (hdiagonal : ∀ index : Fin 3, form index index = 0)
    (hfirst : form 0 1 = edgeFirst) (hsecond : form 0 2 = edgeSecond)
    (hthird : form 1 2 = edgeThird)
    (hcapPos : 0 < cap) (hlevel : 0 < level) (hcapLe : cap ≤ 2 * level)
    (hcap : (cap • (1 : Matrix (Fin 3) (Fin 3) ℝ) - form).PosSemidef)
    (hheavy : level * cap * (cap - level) ≤ 2 * (edgeFirst * edgeSecond * edgeThird)) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ) + form).PosSemidef := by
  have hform : form = hollowSymmetricThree edgeFirst edgeSecond edgeThird := by
    rw [eq_hollowSymmetricThree_of_transpose_eq_of_diagonal_eq_zero hsymmetric hdiagonal,
      hfirst, hsecond, hthird]
  rw [hform] at hcap ⊢
  exact posSemidef_smul_one_add_hollowSymmetricThree_of_spectralCapUpper_of_heavyProduct
    hcapPos hlevel hcapLe hcap hheavy

end Gtz

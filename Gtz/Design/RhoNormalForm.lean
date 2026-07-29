/-
# The rho normal form: domination of a triple IS positive semidefiniteness of a
# unit-diagonal `3 x 3` correlation matrix

`Gtz.Quantitative.GoodTripleGraph` already owns the SCALAR half of this reading:
`normalizedPairing` is the correlation `rho_cd = p_cd / sqrt(x_c x_d)`,
`elliptopeBracket` is the cubic `1 - r1^2 - r2^2 - r3^2 + 2 r1 r2 r3`, and
`discriminantTie_eq_excessProduct_mul_elliptopeBracket` factors the leverages out of
the tie leg completely. What was missing is the MATRIX statement underneath: that
the whole gap of a triple is a positive-diagonal congruence of a unit-diagonal
correlation matrix, so domination and the elliptope are the same object seen in two
coordinate systems. This file supplies it, at three levels of generality.

**One notational correction, made once and used throughout.** The congruence
`S_C - I = D^(1/2) R_C D^(1/2)` with `D = diag(x_a,x_b,x_c)` is about the GRAM gap
of the triple, not about the frame gap `subsetSum C - 1`, and the two are genuinely
different matrices. Writing `M` for the `3 x 3` matrix whose columns are the three
atoms, `subsetSum C = M M^T` acts on coordinate space and its diagonal entries are
coordinate sums, while `M^T M - 1` acts on slot space and has the excesses on the
diagonal and the pairings off it — that second matrix is the one the congruence is
an identity about. At the regular tetrahedron the frame gap is
`[[2,-1,1],[-1,2,1],[1,1,2]]` and the Gram gap is `[[2,-1,-1],[-1,2,-1],[-1,-1,2]]`:
same determinant `0`, different entries. The two are interchangeable for everything
this campaign asks — `posSemidef_transpose_mul_sub_one_comm` transfers the Loewner
condition and Weinstein-Aronszajn (`det_subsetSum_sub_one_eq_discriminantTie`)
transfers the determinant — and both transfers are proved here, so nothing is lost;
but the congruence itself is stated about the Gram gap, where it is true on the nose.

**The normalisation, at every dimension.** For any real square `form` with strictly
positive diagonal, `correlationOf form` divides entry `(i,j)` by
`sqrt(form i i * form j j)` and `diagonalSqrtScaling form` is `diag(sqrt(form i i))`.
Then `eq_congr_correlationOf` says `form = S^T C S` verbatim, and since `S` is
invertible the three transfers are immediate:
`posSemidef_iff_posSemidef_correlationOf`, `posDef_iff_posDef_correlationOf`, and
`det_eq_prod_diagonal_mul_det_correlationOf` — `det form = (prod of the diagonal)
times det of the correlation`. The last one is the general form of the shipped
leverage factor-out: it holds at every size, with no design in sight.

**The rho matrix of a triple.** `tripleGapMatrix` is the `3 x 3` gap in the triple's
own six scalars (excesses on the diagonal, pairings off it). Three facts pin it:
`tripleGapMatrix_eq_gram_sub_one` identifies it with `M^T M - 1`,
`det_tripleGapMatrix` says its determinant is exactly `discriminantTie`, and
`dominates_triple_iff_posSemidef_tripleGapMatrix` says domination of the triple is
its positive semidefiniteness — with NO heaviness hypothesis at all, only that the
three indices are distinct. Feeding it to the normalisation gives
`correlationOf_tripleGapMatrix`: the correlation of the gap is the unit-diagonal
matrix of the three `normalizedPairing`s, so `tripleGapMatrix_eq_congr_correlationMatrixThree`
is the congruence `D^(1/2) R_C D^(1/2)` with `D = diag(x_a,x_b,x_c)`, and
`dominates_triple_iff_posSemidef_correlationMatrixThree` is "C dominates iff `R_C` is PSD".
Those need only the three excesses positive — strictly weaker than `AllHeavy D`,
which is a hypothesis on the whole design.

**The determinant is not the elliptope.** `posSemidef_correlationMatrixThree_iff` states the
honest membership criterion: `R` is PSD iff `r^2 <= 1` on each of the three edges AND
`0 <= elliptopeBracket`. Dropping the edge conjunct is not a stylistic choice:
`elliptopeBracket (3/2) (3/2) 1 = 0` exactly, and that point is NOT positive
semidefinite (`not_posSemidef_correlationMatrixThree_of_incompatible_boundary`). So the
edge conditions survive even on the determinant's own zero set, where a naive reading
would expect them to be forced.

**Amplification.** Write `u_c = g_c / |g_c|` for the direction (`atomUnitDirection`),
`gamma_cd = <u_c, u_d>` for the genuine cosine (`directionCosine`), and
`A_c = sqrt(ell_c / x_c)` for the amplification (`amplification`). Then
`normalizedPairing_eq_amplification_mul_directionCosine` reads
`rho_cd = A_c A_d cos(phi_cd)`, with `amplification_sq_eq_one_add_inv_heavyExcess`
giving `A^2 = 1 + 1/x` and `one_lt_amplification` giving `A > 1` at every heavy atom.
So `rho` is the direction cosine AMPLIFIED, never damped
(`abs_directionCosine_le_abs_normalizedPairing`), and compatibility `|rho| <= 1` is a
genuine ANGLE constraint that tightens as the excesses shrink. `directionCosine` is a
cosine in the honest sense: `atomUnitDirection_dotProduct_self` normalises it and
`abs_directionCosine_le_one` is Cauchy-Schwarz.

**Calibration at the regular tetrahedron.** Every leverage is `3`, so `x = 2`,
`share = t * ell = 3/4`, `A^2 = 3/2`, `gamma = -1/3`, and
`rho = A^2 gamma = (3/2)(-1/3) = -1/2` on all three edges of `{0,1,2}`
(`tetraDesign_normalizedPairing_zeroOne` and siblings). The Mercedes point
`(-1/2,-1/2,-1/2)` has `elliptopeBracket = 0` exactly: the tetrahedron's correlation
matrix is positive semidefinite and singular
(`tetraDesign_posSemidef_correlationMatrixThree`,
`tetraDesign_not_posDef_correlationMatrixThree`), sitting ON the elliptope boundary rather
than inside it. That is the same zero the repo already records as
`tetraDesign_discriminantTie = 0`, now read in the coordinates where the leverages
have been divided out.

**The tie locus, exactly.** `IsTiedTriple` is the per-triple reading of `Gtz.IsTie`:
the triple dominates but not strictly. `isTiedTriple_iff_dominates_and_discriminantTie_eq_zero`
turns that into a single polynomial equation, and
`isTiedTriple_iff_isCompatibleTriangle_and_elliptopeBracket_eq_zero` puts it in rho
coordinates: **a triple ties iff its three correlations are compatible and the
elliptope determinant vanishes.** The tie locus is the compatible part of the
determinant's zero set — Cayley's nodal cubic surface, intersected with the cube. The
`(3/2,3/2,1)` witness above shows the compatible part is a proper part.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.PrincipalMinorsThree
import Gtz.Reduction.SplitTransfer
import Gtz.Certificates.ResidueDissolution
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.GoodTripleGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m dim : ℕ}

/-! ### The correlation normalisation of a positive-diagonal form, at every dimension -/

/-- The **diagonal square-root scaling** `diag(sqrt(form i i))` of a form. For a form
with positive diagonal this is the invertible congruence that normalises the diagonal
to one. -/
noncomputable def diagonalSqrtScaling (form : Matrix (Fin dim) (Fin dim) ℝ) :
    Matrix (Fin dim) (Fin dim) ℝ :=
  Matrix.diagonal fun index => Real.sqrt (form index index)

/-- The **correlation matrix** of a form: entry `(i,j)` divided by
`sqrt(form i i * form j j)`. On a positive diagonal it is unit-diagonal, and it is
the coordinate system in which `normalizedPairing` lives. -/
noncomputable def correlationOf (form : Matrix (Fin dim) (Fin dim) ℝ) :
    Matrix (Fin dim) (Fin dim) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    form rowIndex colIndex / Real.sqrt (form rowIndex rowIndex * form colIndex colIndex)

theorem correlationOf_apply (form : Matrix (Fin dim) (Fin dim) ℝ)
    (rowIndex colIndex : Fin dim) :
    correlationOf form rowIndex colIndex
      = form rowIndex colIndex
          / Real.sqrt (form rowIndex rowIndex * form colIndex colIndex) := rfl

/-- The correlation matrix has unit diagonal wherever the form's diagonal is
positive. -/
theorem correlationOf_diagonal_eq_one {form : Matrix (Fin dim) (Fin dim) ℝ}
    {index : Fin dim} (hpos : 0 < form index index) :
    correlationOf form index index = 1 := by
  rw [correlationOf_apply, show form index index * form index index
      = form index index ^ 2 from by ring, Real.sqrt_sq hpos.le,
    div_self (ne_of_gt hpos)]

/-- Normalisation preserves symmetry. -/
theorem correlationOf_transpose {form : Matrix (Fin dim) (Fin dim) ℝ}
    (hsymmetric : formᵀ = form) : (correlationOf form)ᵀ = correlationOf form := by
  ext rowIndex colIndex
  have hentry : form colIndex rowIndex = form rowIndex colIndex := by
    conv_lhs => rw [← hsymmetric]
    rfl
  rw [Matrix.transpose_apply, correlationOf_apply, correlationOf_apply, hentry,
    mul_comm (form colIndex colIndex) (form rowIndex rowIndex)]

theorem diagonalSqrtScaling_transpose (form : Matrix (Fin dim) (Fin dim) ℝ) :
    (diagonalSqrtScaling form)ᵀ = diagonalSqrtScaling form :=
  Matrix.diagonal_transpose _

/-- A positive diagonal makes the scaling invertible — the determinant is a product
of strictly positive square roots. -/
theorem isUnit_det_diagonalSqrtScaling {form : Matrix (Fin dim) (Fin dim) ℝ}
    (hpos : ∀ index, 0 < form index index) :
    IsUnit (diagonalSqrtScaling form).det := by
  rw [diagonalSqrtScaling, Matrix.det_diagonal]
  exact (Finset.prod_pos fun index _ => Real.sqrt_pos.mpr (hpos index)).ne'.isUnit

/-- **THE CONGRUENCE, at every dimension.** A form with strictly positive diagonal is
`S^T C S` for `S = diag(sqrt(form i i))` and `C` its correlation matrix. This is
`D^(1/2) R D^(1/2)` with the design stripped away: the identity is about positive
diagonals, not about designs, and not about rank three. -/
theorem eq_congr_correlationOf {form : Matrix (Fin dim) (Fin dim) ℝ}
    (hpos : ∀ index, 0 < form index index) :
    form = (diagonalSqrtScaling form)ᵀ * correlationOf form * diagonalSqrtScaling form := by
  rw [diagonalSqrtScaling_transpose]
  ext rowIndex colIndex
  have hrowNe : Real.sqrt (form rowIndex rowIndex) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hpos rowIndex))
  have hcolNe : Real.sqrt (form colIndex colIndex) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hpos colIndex))
  simp only [diagonalSqrtScaling, Matrix.mul_diagonal, Matrix.diagonal_mul,
    correlationOf_apply, Real.sqrt_mul (hpos rowIndex).le]
  field_simp

/-- **Congruence transfers positive semidefiniteness**: a positive-diagonal form is
PSD exactly when its correlation matrix is. No square roots of matrices, no spectra —
only the invertible diagonal substitution. -/
theorem posSemidef_iff_posSemidef_correlationOf {form : Matrix (Fin dim) (Fin dim) ℝ}
    (hsymmetric : formᵀ = form) (hpos : ∀ index, 0 < form index index) :
    form.PosSemidef ↔ (correlationOf form).PosSemidef := by
  have hcongr := posSemidef_congr_right (X := correlationOf form)
    (P := diagonalSqrtScaling form) (correlationOf_transpose hsymmetric)
    (isUnit_det_diagonalSqrtScaling hpos)
  rw [← eq_congr_correlationOf hpos] at hcongr
  exact hcongr.symm

/-- The definite version of the same transfer. -/
theorem posDef_iff_posDef_correlationOf {form : Matrix (Fin dim) (Fin dim) ℝ}
    (hsymmetric : formᵀ = form) (hpos : ∀ index, 0 < form index index) :
    form.PosDef ↔ (correlationOf form).PosDef := by
  have hcongr := posDef_congr_right (X := correlationOf form)
    (P := diagonalSqrtScaling form) (correlationOf_transpose hsymmetric)
    (isUnit_det_diagonalSqrtScaling hpos)
  rw [← eq_congr_correlationOf hpos] at hcongr
  exact hcongr.symm

/-- **The diagonal factors out of the determinant, at every dimension.** The shipped
`discriminantTie_eq_excessProduct_mul_elliptopeBracket` is this identity at `dim = 3`
on the gap of a triple; here it is with no design and no rank. -/
theorem det_eq_prod_diagonal_mul_det_correlationOf
    {form : Matrix (Fin dim) (Fin dim) ℝ} (hpos : ∀ index, 0 < form index index) :
    form.det = (∏ index, form index index) * (correlationOf form).det := by
  have hsplit : (∏ index, form index index)
      = (∏ index, Real.sqrt (form index index)) * ∏ index, Real.sqrt (form index index) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun index _ => (Real.mul_self_sqrt (hpos index).le).symm
  conv_lhs => rw [eq_congr_correlationOf hpos]
  rw [Matrix.det_mul, Matrix.det_mul, diagonalSqrtScaling_transpose, diagonalSqrtScaling,
    Matrix.det_diagonal, hsplit]
  ring

/-! ### The unit-diagonal `3 x 3` correlation matrix of three reals -/

/-- The **correlation matrix `R` of three reals**: unit diagonal, off-diagonal
`(r1, r2, r3)` in the slots `(0,1)`, `(0,2)`, `(1,2)`. This slot convention matches
`discriminantTie_eq_excessProduct_mul_elliptopeBracket`, where the third argument is
the edge NOT touching the pivot. -/
def correlationMatrixThree (rhoFirst rhoSecond rhoThird : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, rhoFirst, rhoSecond;
     rhoFirst, 1, rhoThird;
     rhoSecond, rhoThird, 1]

theorem correlationMatrixThree_transpose (rhoFirst rhoSecond rhoThird : ℝ) :
    (correlationMatrixThree rhoFirst rhoSecond rhoThird)ᵀ
      = correlationMatrixThree rhoFirst rhoSecond rhoThird := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> rfl

/-- **`elliptopeBracket` IS a determinant.** The shipped cubic is the determinant of
the unit-diagonal correlation matrix — the identification the file header of
`GoodTripleGraph` asserts in prose and nothing in the repo carried. -/
theorem det_correlationMatrixThree (rhoFirst rhoSecond rhoThird : ℝ) :
    (correlationMatrixThree rhoFirst rhoSecond rhoThird).det
      = elliptopeBracket rhoFirst rhoSecond rhoThird := by
  rw [Matrix.det_fin_three, elliptopeBracket]
  simp only [correlationMatrixThree, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **THE HONEST ELLIPTOPE MEMBERSHIP CRITERION.** A unit-diagonal symmetric `3 x 3`
is positive semidefinite iff each off-diagonal entry has square at most one AND the
elliptope bracket is nonnegative. Both conjuncts are load-bearing: the bracket alone
is only the determinant half. Forward by three explicit test vectors
`(1,-r1,0)`, `(1,0,-r2)`, `(0,1,-r3)` plus `PosSemidef.det_nonneg`; backward by
`posSemidef_three_of_principalMinors`, whose seven minors are exactly `1,1,1`, the
three `1 - r^2`, and the bracket. -/
theorem posSemidef_correlationMatrixThree_iff (rhoFirst rhoSecond rhoThird : ℝ) :
    (correlationMatrixThree rhoFirst rhoSecond rhoThird).PosSemidef
      ↔ rhoFirst ^ 2 ≤ 1 ∧ rhoSecond ^ 2 ≤ 1 ∧ rhoThird ^ 2 ≤ 1
        ∧ 0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird := by
  constructor
  · intro hpsd
    have hquad := (posSemidef_iff_quadForm_nonneg _
      (correlationMatrixThree_transpose rhoFirst rhoSecond rhoThird)).mp hpsd
    have hentry : ∀ testVec : Fin 3 → ℝ,
        testVec ⬝ᵥ (correlationMatrixThree rhoFirst rhoSecond rhoThird *ᵥ testVec)
          = testVec 0 ^ 2 + testVec 1 ^ 2 + testVec 2 ^ 2
            + 2 * rhoFirst * testVec 0 * testVec 1
            + 2 * rhoSecond * testVec 0 * testVec 2
            + 2 * rhoThird * testVec 1 * testVec 2 := by
      intro testVec
      rw [quadForm_three_eq (correlationMatrixThree_transpose rhoFirst rhoSecond rhoThird)]
      simp only [correlationMatrixThree, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
      ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hgoal := hquad ![1, -rhoFirst, 0]
      rw [hentry] at hgoal
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at hgoal
      nlinarith [hgoal]
    · have hgoal := hquad ![1, 0, -rhoSecond]
      rw [hentry] at hgoal
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at hgoal
      nlinarith [hgoal]
    · have hgoal := hquad ![0, 1, -rhoThird]
      rw [hentry] at hgoal
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at hgoal
      nlinarith [hgoal]
    · rw [← det_correlationMatrixThree]
      exact hpsd.det_nonneg
  · rintro ⟨hfirst, hsecond, hthird, hbracket⟩
    have hdeterminant : 0 ≤ (correlationMatrixThree rhoFirst rhoSecond rhoThird).det := by
      rw [det_correlationMatrixThree]
      exact hbracket
    refine posSemidef_three_of_principalMinors
      (correlationMatrixThree_transpose rhoFirst rhoSecond rhoThird) ?_ ?_ ?_ ?_ ?_ ?_
      hdeterminant <;>
    · simp only [correlationMatrixThree, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
      linarith

/-- **The edge conjunct survives on the determinant's own zero set.** At
`(3/2, 3/2, 1)` the elliptope bracket vanishes exactly, yet the matrix is not
positive semidefinite. So "the bracket is zero" is strictly weaker than "the triple
ties", and the compatibility conjunct of
`isTiedTriple_iff_isCompatibleTriangle_and_elliptopeBracket_eq_zero` cannot be
dropped. -/
theorem elliptopeBracket_incompatible_boundary :
    elliptopeBracket (3 / 2) (3 / 2) 1 = 0 := by
  rw [elliptopeBracket]
  norm_num

theorem not_posSemidef_correlationMatrixThree_of_incompatible_boundary :
    ¬ (correlationMatrixThree (3 / 2) (3 / 2) 1).PosSemidef := by
  intro hpsd
  have hedge := ((posSemidef_correlationMatrixThree_iff (3 / 2) (3 / 2) 1).mp hpsd).1
  norm_num at hedge

/-! ### The `3 x 3` gap matrix of an ordered triple -/

/-- The **gap matrix of an ordered triple**: the heavy excesses on the diagonal, the
atom pairings off it. This is `Gram(C) - I` written in the triple's own six scalars,
the object `dominates_triple_iff_discriminantSystem` decides by two polynomial
inequalities. -/
def tripleGapMatrix (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![heavyExcess D pivot, atomPairing D pivot pairFirst, atomPairing D pivot pairSecond;
     atomPairing D pivot pairFirst, heavyExcess D pairFirst,
       atomPairing D pairFirst pairSecond;
     atomPairing D pivot pairSecond, atomPairing D pairFirst pairSecond,
       heavyExcess D pairSecond]

theorem tripleGapMatrix_transpose (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    (tripleGapMatrix D pivot pairFirst pairSecond)ᵀ
      = tripleGapMatrix D pivot pairFirst pairSecond := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> rfl

/-- The gap matrix is `M^T M - 1` for the triple's column matrix — the diagonal
entries are leverages minus one, the off-diagonal ones are raw inner products. -/
theorem tripleGapMatrix_eq_gram_sub_one (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    tripleGapMatrix D pivot pairFirst pairSecond
      = (tripleMatrix D pivot pairFirst pairSecond)ᵀ
          * tripleMatrix D pivot pairFirst pairSecond - 1 := by
  ext slotRow slotCol
  rw [Matrix.sub_apply, tripleMatrix_transpose_mul_apply]
  fin_cases slotRow <;> fin_cases slotCol <;>
    simp [tripleGapMatrix, tripleAtom, heavyExcess, atomPairing, leverageOf,
      dotProduct_self_eq_sum_sq] <;>
    exact dotProduct_comm _ _

/-- **The tie leg IS the gap determinant.** `discriminantTie` was defined as a cubic
in the six scalars; it is literally `det(Gram - I)`. -/
theorem det_tripleGapMatrix (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) :
    (tripleGapMatrix D pivot pairFirst pairSecond).det
      = discriminantTie D pivot pairFirst pairSecond := by
  rw [Matrix.det_fin_three, discriminantTie]
  simp only [tripleGapMatrix, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **The frame gap and the Gram gap have the same determinant**, by
Weinstein-Aronszajn: `det(M M^T - 1) = det(M^T M - 1)`. Hence the tie leg is the
determinant of the object domination is actually about. -/
theorem det_subsetSum_sub_one_eq_discriminantTie (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    (subsetSum D {pivot, pairFirst, pairSecond} - 1).det
      = discriminantTie D pivot pairFirst pairSecond := by
  rw [← det_tripleGapMatrix D pivot pairFirst pairSecond,
    tripleGapMatrix_eq_gram_sub_one,
    ← tripleMatrix_mul_transpose D hpivotFirst hpivotSecond hpairDistinct]
  have hnegDet : ∀ block : Matrix (Fin 3) (Fin 3) ℝ,
      (block - 1).det = -((1 - block).det) := by
    intro block
    rw [show block - 1 = -(1 - block) from (neg_sub 1 block).symm, Matrix.det_neg]
    norm_num
  rw [hnegDet, hnegDet,
    Matrix.det_one_sub_mul_comm (tripleMatrix D pivot pairFirst pairSecond)
      (tripleMatrix D pivot pairFirst pairSecond)ᵀ]

/-- **Domination of a triple IS positive semidefiniteness of its gap matrix.** No
heaviness anywhere: only the three indices being distinct, so the selected subset
really has three elements. This is strictly weaker in hypotheses than
`dominates_triple_iff_discriminantSystem`, which needs the pivot heavy. -/
theorem dominates_triple_iff_posSemidef_tripleGapMatrix (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond}
      ↔ (tripleGapMatrix D pivot pairFirst pairSecond).PosSemidef := by
  rw [Dominates, ← tripleMatrix_mul_transpose D hpivotFirst hpivotSecond hpairDistinct,
    tripleGapMatrix_eq_gram_sub_one]
  exact (posSemidef_transpose_mul_sub_one_comm
    (tripleMatrix D pivot pairFirst pairSecond)).symm

/-- The definite twin: a triple dominates STRICTLY iff its gap matrix is positive
definite. -/
theorem posDef_subsetSum_sub_one_iff_posDef_tripleGapMatrix (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    (subsetSum D {pivot, pairFirst, pairSecond} - 1).PosDef
      ↔ (tripleGapMatrix D pivot pairFirst pairSecond).PosDef := by
  rw [← tripleMatrix_mul_transpose D hpivotFirst hpivotSecond hpairDistinct,
    tripleGapMatrix_eq_gram_sub_one]
  exact (posDef_transpose_mul_sub_one_comm
    (tripleMatrix D pivot pairFirst pairSecond)).symm

/-! ### The rho normal form -/

/-- The scaling `D^(1/2) = diag(sqrt(x_a), sqrt(x_b), sqrt(x_c))` of the congruence,
written directly in the three excesses. -/
noncomputable def excessSqrtDiagonal (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![Real.sqrt (heavyExcess D pivot), Real.sqrt (heavyExcess D pairFirst),
    Real.sqrt (heavyExcess D pairSecond)]

theorem excessSqrtDiagonal_transpose (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    (excessSqrtDiagonal D pivot pairFirst pairSecond)ᵀ
      = excessSqrtDiagonal D pivot pairFirst pairSecond :=
  Matrix.diagonal_transpose _

theorem excessSqrtDiagonal_eq_diagonalSqrtScaling (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    excessSqrtDiagonal D pivot pairFirst pairSecond
      = diagonalSqrtScaling (tripleGapMatrix D pivot pairFirst pairSecond) := by
  rw [excessSqrtDiagonal, diagonalSqrtScaling]
  congr 1
  funext index
  fin_cases index <;> rfl

/-- **The correlation of the gap is the matrix of normalized pairings.** The general
normalisation, applied to the triple's gap, reproduces the shipped
`normalizedPairing` on the nose — no new coordinate is being introduced. -/
theorem correlationOf_tripleGapMatrix (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotPos : 0 < heavyExcess D pivot)
    (hfirstPos : 0 < heavyExcess D pairFirst) (hsecondPos : 0 < heavyExcess D pairSecond) :
    correlationOf (tripleGapMatrix D pivot pairFirst pairSecond)
      = correlationMatrixThree (normalizedPairing D pivot pairFirst)
          (normalizedPairing D pivot pairSecond)
          (normalizedPairing D pairFirst pairSecond) := by
  have hselfDiv : ∀ value : ℝ, 0 < value → value / Real.sqrt (value * value) = 1 := by
    intro value hvalue
    rw [show value * value = value ^ 2 from by ring, Real.sqrt_sq hvalue.le,
      div_self (ne_of_gt hvalue)]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, correlationOf, correlationMatrixThree,
      tripleGapMatrix, normalizedPairing, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons] <;>
    first
      | rfl
      | exact hselfDiv _ hpivotPos
      | exact hselfDiv _ hfirstPos
      | exact hselfDiv _ hsecondPos
      | rw [mul_comm]

/-- The three diagonal entries of the gap matrix are the three excesses, so a
heavy triple gives a positive-diagonal form. -/
theorem tripleGapMatrix_diagonal_pos (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotPos : 0 < heavyExcess D pivot)
    (hfirstPos : 0 < heavyExcess D pairFirst) (hsecondPos : 0 < heavyExcess D pairSecond)
    (index : Fin 3) : 0 < tripleGapMatrix D pivot pairFirst pairSecond index index := by
  fin_cases index
  · exact hpivotPos
  · exact hfirstPos
  · exact hsecondPos

/-- **THE NORMAL FORM.** `Gram(C) - I = D^(1/2) R_C D^(1/2)` with
`D = diag(x_a, x_b, x_c)` and `R_C` the unit-diagonal matrix of the three normalized
pairings. The scaling is symmetric, so no transpose appears. The gap on the left is
the GRAM gap, not the frame gap `subsetSum C - 1`; see the file header — the two
carry the same Loewner status and the same determinant, both proved here, but only
this one has the excesses on its diagonal. -/
theorem tripleGapMatrix_eq_congr_correlationMatrixThree (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotPos : 0 < heavyExcess D pivot)
    (hfirstPos : 0 < heavyExcess D pairFirst) (hsecondPos : 0 < heavyExcess D pairSecond) :
    tripleGapMatrix D pivot pairFirst pairSecond
      = excessSqrtDiagonal D pivot pairFirst pairSecond
          * correlationMatrixThree (normalizedPairing D pivot pairFirst)
              (normalizedPairing D pivot pairSecond)
              (normalizedPairing D pairFirst pairSecond)
          * excessSqrtDiagonal D pivot pairFirst pairSecond := by
  conv_lhs =>
    rw [eq_congr_correlationOf
      (tripleGapMatrix_diagonal_pos D hpivotPos hfirstPos hsecondPos)]
  rw [← excessSqrtDiagonal_eq_diagonalSqrtScaling, excessSqrtDiagonal_transpose,
    excessSqrtDiagonal_eq_diagonalSqrtScaling,
    correlationOf_tripleGapMatrix D hpivotPos hfirstPos hsecondPos,
    ← excessSqrtDiagonal_eq_diagonalSqrtScaling]

/-- **T1, THE EQUIVALENCE.** A triple of distinct atoms with positive excesses
dominates exactly when its unit-diagonal correlation matrix is positive
semidefinite. Congruence by an invertible diagonal cannot change the sign of a
quadratic form, so the leverages are irrelevant to domination once the correlations
are known — the whole content of the covering lives on three numbers per triple.
Note the hypotheses are LOCAL: only the three atoms of the triple need be heavy,
where `dominates_triple_iff_isElliptopeGoodTriangle` asks for `AllHeavy D`. -/
theorem dominates_triple_iff_posSemidef_correlationMatrixThree (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotPos : 0 < heavyExcess D pivot) (hfirstPos : 0 < heavyExcess D pairFirst)
    (hsecondPos : 0 < heavyExcess D pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond}
      ↔ (correlationMatrixThree (normalizedPairing D pivot pairFirst)
          (normalizedPairing D pivot pairSecond)
          (normalizedPairing D pairFirst pairSecond)).PosSemidef := by
  rw [dominates_triple_iff_posSemidef_tripleGapMatrix D hpivotFirst hpivotSecond
      hpairDistinct,
    posSemidef_iff_posSemidef_correlationOf (tripleGapMatrix_transpose D pivot pairFirst
      pairSecond) (tripleGapMatrix_diagonal_pos D hpivotPos hfirstPos hsecondPos),
    correlationOf_tripleGapMatrix D hpivotPos hfirstPos hsecondPos]

/-- The definite twin: strict domination is positive definiteness of the correlation
matrix — the interior of the elliptope. -/
theorem posDef_subsetSum_sub_one_iff_posDef_correlationMatrixThree (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotPos : 0 < heavyExcess D pivot) (hfirstPos : 0 < heavyExcess D pairFirst)
    (hsecondPos : 0 < heavyExcess D pairSecond) :
    (subsetSum D {pivot, pairFirst, pairSecond} - 1).PosDef
      ↔ (correlationMatrixThree (normalizedPairing D pivot pairFirst)
          (normalizedPairing D pivot pairSecond)
          (normalizedPairing D pairFirst pairSecond)).PosDef := by
  rw [posDef_subsetSum_sub_one_iff_posDef_tripleGapMatrix D hpivotFirst hpivotSecond
      hpairDistinct,
    posDef_iff_posDef_correlationOf (tripleGapMatrix_transpose D pivot pairFirst
      pairSecond) (tripleGapMatrix_diagonal_pos D hpivotPos hfirstPos hsecondPos),
    correlationOf_tripleGapMatrix D hpivotPos hfirstPos hsecondPos]

/-- **Domination in scalar rho coordinates, with the edge conditions named.** The
shipped `dominates_triple_iff_isElliptopeGoodTriangle` with `AllHeavy D` replaced by
the three excesses of the triple, and with the tie leg replaced by the bracket. -/
theorem dominates_triple_iff_isCompatibleTriangle_and_elliptopeBracket_nonneg
    (D : WeightedDesign m 3) {pivot pairFirst pairSecond : Fin m}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) (hpivotPos : 0 < heavyExcess D pivot)
    (hfirstPos : 0 < heavyExcess D pairFirst) (hsecondPos : 0 < heavyExcess D pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond}
      ↔ IsCompatibleTriangle D pivot pairFirst pairSecond
        ∧ 0 ≤ elliptopeBracket (normalizedPairing D pivot pairFirst)
            (normalizedPairing D pivot pairSecond)
            (normalizedPairing D pairFirst pairSecond) := by
  have hcompatFirst : IsCompatiblePair D pivot pairFirst
      ↔ normalizedPairing D pivot pairFirst ^ 2 ≤ 1 := by
    rw [IsCompatiblePair, pairMinor, normalizedPairing_sq D hpivotPos hfirstPos,
      div_le_iff₀ (mul_pos hpivotPos hfirstPos)]
    constructor <;> intro hbound <;> linarith
  have hcompatSecond : IsCompatiblePair D pivot pairSecond
      ↔ normalizedPairing D pivot pairSecond ^ 2 ≤ 1 := by
    rw [IsCompatiblePair, pairMinor, normalizedPairing_sq D hpivotPos hsecondPos,
      div_le_iff₀ (mul_pos hpivotPos hsecondPos)]
    constructor <;> intro hbound <;> linarith
  have hcompatPair : IsCompatiblePair D pairFirst pairSecond
      ↔ normalizedPairing D pairFirst pairSecond ^ 2 ≤ 1 := by
    rw [IsCompatiblePair, pairMinor, normalizedPairing_sq D hfirstPos hsecondPos,
      div_le_iff₀ (mul_pos hfirstPos hsecondPos)]
    constructor <;> intro hbound <;> linarith
  rw [dominates_triple_iff_posSemidef_correlationMatrixThree D hpivotFirst hpivotSecond
      hpairDistinct hpivotPos hfirstPos hsecondPos,
    posSemidef_correlationMatrixThree_iff, IsCompatibleTriangle, hcompatFirst, hcompatSecond,
    hcompatPair]
  tauto

/-! ### Amplification: `rho` is the direction cosine, amplified -/

/-- The **unit direction** `u_c = g_c / |g_c|` of an atom. -/
noncomputable def atomUnitDirection (D : WeightedDesign m 3) (atomIndex : Fin m) : Fin 3 → ℝ :=
  (Real.sqrt (leverageOf (D.atom atomIndex)))⁻¹ • D.atom atomIndex

/-- The **direction cosine** `gamma_cd = <u_c, u_d> = p_cd / sqrt(ell_c ell_d)`: the
genuine angle between two atoms, with the leverages divided out rather than the
excesses. -/
noncomputable def directionCosine (D : WeightedDesign m 3)
    (atomFirst atomSecond : Fin m) : ℝ :=
  atomPairing D atomFirst atomSecond
    / Real.sqrt (leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond))

/-- The **amplification** `A_c = sqrt(ell_c / x_c)` of a heavy atom. -/
noncomputable def amplification (D : WeightedDesign m 3) (atomIndex : Fin m) : ℝ :=
  Real.sqrt (leverageOf (D.atom atomIndex) / heavyExcess D atomIndex)

theorem leverage_eq_heavyExcess_add_one (D : WeightedDesign m 3) (atomIndex : Fin m) :
    leverageOf (D.atom atomIndex) = heavyExcess D atomIndex + 1 := by
  rw [heavyExcess]
  ring

theorem leverage_pos_of_heavyExcess_pos {D : WeightedDesign m 3} {atomIndex : Fin m}
    (hpos : 0 < heavyExcess D atomIndex) : 0 < leverageOf (D.atom atomIndex) := by
  rw [leverage_eq_heavyExcess_add_one]
  linarith

/-- `A^2 = ell / x`, the defining identity. -/
theorem amplification_sq {D : WeightedDesign m 3} {atomIndex : Fin m}
    (hpos : 0 < heavyExcess D atomIndex) :
    amplification D atomIndex ^ 2
      = leverageOf (D.atom atomIndex) / heavyExcess D atomIndex := by
  rw [amplification, Real.sq_sqrt]
  exact div_nonneg (leverage_pos_of_heavyExcess_pos hpos).le hpos.le

/-- `A^2 = 1 + 1/x`: the amplification blows up as the excess collapses. -/
theorem amplification_sq_eq_one_add_inv_heavyExcess {D : WeightedDesign m 3}
    {atomIndex : Fin m} (hpos : 0 < heavyExcess D atomIndex) :
    amplification D atomIndex ^ 2 = 1 + (heavyExcess D atomIndex)⁻¹ := by
  rw [amplification_sq hpos, leverage_eq_heavyExcess_add_one]
  field_simp

/-- **The amplification is a genuine amplification**: strictly greater than one at
every heavy atom, and blowing up as the excess goes to zero. -/
theorem one_lt_amplification {D : WeightedDesign m 3} {atomIndex : Fin m}
    (hpos : 0 < heavyExcess D atomIndex) : 1 < amplification D atomIndex := by
  have hsquare := amplification_sq_eq_one_add_inv_heavyExcess hpos
  have hnonneg : 0 ≤ amplification D atomIndex := Real.sqrt_nonneg _
  have hinv : 0 < (heavyExcess D atomIndex)⁻¹ := inv_pos.mpr hpos
  nlinarith [hsquare, hnonneg, hinv]

theorem amplification_eq_sqrt_div {D : WeightedDesign m 3} {atomIndex : Fin m}
    (hpos : 0 < heavyExcess D atomIndex) :
    amplification D atomIndex
      = Real.sqrt (leverageOf (D.atom atomIndex)) / Real.sqrt (heavyExcess D atomIndex) := by
  rw [amplification, Real.sqrt_div (leverage_pos_of_heavyExcess_pos hpos).le]

/-- The unit direction really is a unit vector. -/
theorem atomUnitDirection_dotProduct_self {D : WeightedDesign m 3} {atomIndex : Fin m}
    (hpos : 0 < leverageOf (D.atom atomIndex)) :
    atomUnitDirection D atomIndex ⬝ᵥ atomUnitDirection D atomIndex = 1 := by
  have hsqrtNe : Real.sqrt (leverageOf (D.atom atomIndex)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hsquare : Real.sqrt (leverageOf (D.atom atomIndex))
      * Real.sqrt (leverageOf (D.atom atomIndex)) = leverageOf (D.atom atomIndex) :=
    Real.mul_self_sqrt hpos.le
  have hself : D.atom atomIndex ⬝ᵥ D.atom atomIndex = leverageOf (D.atom atomIndex) :=
    (dotProduct_self_eq_sum_sq (D.atom atomIndex)).trans rfl
  rw [atomUnitDirection, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hself]
  field_simp
  linarith [hsquare]

/-- **The direction cosine is an inner product of unit vectors.** -/
theorem atomUnitDirection_dotProduct {D : WeightedDesign m 3} {atomFirst atomSecond : Fin m}
    (hfirstPos : 0 < leverageOf (D.atom atomFirst))
    (hsecondPos : 0 < leverageOf (D.atom atomSecond)) :
    atomUnitDirection D atomFirst ⬝ᵥ atomUnitDirection D atomSecond
      = directionCosine D atomFirst atomSecond := by
  have hfirstNe : Real.sqrt (leverageOf (D.atom atomFirst)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hfirstPos)
  have hsecondNe : Real.sqrt (leverageOf (D.atom atomSecond)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hsecondPos)
  rw [atomUnitDirection, atomUnitDirection, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, directionCosine, Real.sqrt_mul hfirstPos.le, atomPairing]
  field_simp

/-- **Cauchy-Schwarz**: the direction cosine is a cosine. -/
theorem abs_directionCosine_le_one {D : WeightedDesign m 3} {atomFirst atomSecond : Fin m}
    (hfirstPos : 0 < leverageOf (D.atom atomFirst))
    (hsecondPos : 0 < leverageOf (D.atom atomSecond)) :
    |directionCosine D atomFirst atomSecond| ≤ 1 := by
  have hcauchy : atomPairing D atomFirst atomSecond ^ 2
      ≤ leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond) := by
    have hraw := dotProduct_sq_le_mul (D.atom atomFirst) (D.atom atomSecond)
    rwa [dotProduct_self_eq_sum_sq (D.atom atomFirst),
      dotProduct_self_eq_sum_sq (D.atom atomSecond), ← leverageOf, ← leverageOf,
      ← atomPairing] at hraw
  have hsqrtPos : 0 < Real.sqrt (leverageOf (D.atom atomFirst)
      * leverageOf (D.atom atomSecond)) :=
    Real.sqrt_pos.mpr (mul_pos hfirstPos hsecondPos)
  have hsqrtSq : Real.sqrt (leverageOf (D.atom atomFirst)
        * leverageOf (D.atom atomSecond)) ^ 2
      = leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond) :=
    Real.sq_sqrt (mul_pos hfirstPos hsecondPos).le
  rw [directionCosine, abs_div, abs_of_pos hsqrtPos, div_le_one hsqrtPos]
  nlinarith [hcauchy, hsqrtSq, hsqrtPos, sq_abs (atomPairing D atomFirst atomSecond),
    abs_nonneg (atomPairing D atomFirst atomSecond)]

/-- **T1, THE AMPLIFICATION IDENTITY.** `rho_cd = A_c A_d cos(phi_cd)`: the
normalized pairing is the direction cosine scaled by the two amplifications. The
excesses enter only through `A`, so the correlation coordinate is the angle
coordinate stretched by a factor that depends on nothing but the two leverages. -/
theorem normalizedPairing_eq_amplification_mul_directionCosine (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirstPos : 0 < heavyExcess D atomFirst)
    (hsecondPos : 0 < heavyExcess D atomSecond) :
    normalizedPairing D atomFirst atomSecond
      = amplification D atomFirst * amplification D atomSecond
          * directionCosine D atomFirst atomSecond := by
  have hfirstLev : 0 < leverageOf (D.atom atomFirst) :=
    leverage_pos_of_heavyExcess_pos hfirstPos
  have hsecondLev : 0 < leverageOf (D.atom atomSecond) :=
    leverage_pos_of_heavyExcess_pos hsecondPos
  have hfirstExcessNe : Real.sqrt (heavyExcess D atomFirst) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hfirstPos)
  have hsecondExcessNe : Real.sqrt (heavyExcess D atomSecond) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hsecondPos)
  have hfirstLevNe : Real.sqrt (leverageOf (D.atom atomFirst)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hfirstLev)
  have hsecondLevNe : Real.sqrt (leverageOf (D.atom atomSecond)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hsecondLev)
  rw [normalizedPairing, directionCosine, amplification_eq_sqrt_div hfirstPos,
    amplification_eq_sqrt_div hsecondPos, Real.sqrt_mul hfirstPos.le,
    Real.sqrt_mul hfirstLev.le]
  field_simp

/-- **`rho` never damps the angle.** Since both amplifications exceed one, the
correlation coordinate dominates the cosine in absolute value. So a pair that is
compatible in `rho` was already compatible in angle, and the converse can fail —
which is why compatibility is a real constraint on heavy designs and vacuous on
directions. -/
theorem abs_directionCosine_le_abs_normalizedPairing (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirstPos : 0 < heavyExcess D atomFirst)
    (hsecondPos : 0 < heavyExcess D atomSecond) :
    |directionCosine D atomFirst atomSecond| ≤ |normalizedPairing D atomFirst atomSecond| := by
  have hfirstAmp := one_lt_amplification hfirstPos
  have hsecondAmp := one_lt_amplification hsecondPos
  have hproduct : 1 < amplification D atomFirst * amplification D atomSecond := by
    nlinarith [hfirstAmp, hsecondAmp]
  rw [normalizedPairing_eq_amplification_mul_directionCosine D hfirstPos hsecondPos,
    abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < amplification D atomFirst),
    abs_of_pos (by linarith : (0 : ℝ) < amplification D atomSecond)]
  nlinarith [abs_nonneg (directionCosine D atomFirst atomSecond), hproduct]

/-- **The amplification is a hard ceiling on the correlation.** Since the direction
cosine never exceeds one in absolute value, `|rho_cd| <= A_c A_d`, a bound in the two
leverages alone: no pair of a heavy design can correlate beyond
`sqrt(ell_c ell_d / (x_c x_d))`, whatever the geometry. At leverage three the ceiling
is `(3/2)`, which is exactly the value the repo records at a replicated atom. -/
theorem abs_normalizedPairing_le_amplification_product (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirstPos : 0 < heavyExcess D atomFirst)
    (hsecondPos : 0 < heavyExcess D atomSecond) :
    |normalizedPairing D atomFirst atomSecond|
      ≤ amplification D atomFirst * amplification D atomSecond := by
  have hfirstAmp := one_lt_amplification hfirstPos
  have hsecondAmp := one_lt_amplification hsecondPos
  have hcosine := abs_directionCosine_le_one (leverage_pos_of_heavyExcess_pos hfirstPos)
    (leverage_pos_of_heavyExcess_pos hsecondPos)
  have hampProduct : 0 < amplification D atomFirst * amplification D atomSecond :=
    mul_pos (by linarith) (by linarith)
  rw [normalizedPairing_eq_amplification_mul_directionCosine D hfirstPos hsecondPos,
    abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < amplification D atomFirst),
    abs_of_pos (by linarith : (0 : ℝ) < amplification D atomSecond)]
  nlinarith [hcosine, hampProduct]

/-- **The ceiling is attained exactly at a parallel pair.** Two atoms carrying the
same vector have `rho = ell / x = A^2` on the nose, so the bound above is sharp and
the repo's `not_isCompatiblePair_of_atom_eq` is the statement that `A > 1`. -/
theorem normalizedPairing_eq_amplification_product_of_atom_eq (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hsame : D.atom atomFirst = D.atom atomSecond)
    (hfirstPos : 0 < heavyExcess D atomFirst) :
    normalizedPairing D atomFirst atomSecond
      = amplification D atomFirst * amplification D atomSecond := by
  have hleverage : leverageOf (D.atom atomSecond) = leverageOf (D.atom atomFirst) := by
    rw [hsame]
  have hexcess : heavyExcess D atomSecond = heavyExcess D atomFirst := by
    rw [heavyExcess, heavyExcess, hleverage]
  have hpairing : atomPairing D atomFirst atomSecond = leverageOf (D.atom atomFirst) := by
    rw [atomPairing, ← hsame, leverageOf, ← dotProduct_self_eq_sum_sq]
  have hamplification : amplification D atomSecond = amplification D atomFirst := by
    rw [amplification, amplification, hleverage, hexcess]
  have hsqrtSquare : Real.sqrt (heavyExcess D atomFirst * heavyExcess D atomFirst)
      = heavyExcess D atomFirst := by
    rw [show heavyExcess D atomFirst * heavyExcess D atomFirst = heavyExcess D atomFirst ^ 2
        from by ring, Real.sqrt_sq hfirstPos.le]
  rw [normalizedPairing, hpairing, hexcess, hsqrtSquare, hamplification, ← sq,
    amplification_sq hfirstPos]

/-! ### Calibration at the regular tetrahedron -/

/-- Every tetrahedron atom carries share `t * ell = 3/4`. -/
theorem tetraDesign_share (atomIndex : Fin 4) :
    tetraDesign.weight atomIndex * leverageOf (tetraDesign.atom atomIndex) = 3 / 4 := by
  rw [tetraDesign_leverage]
  norm_num [tetraDesign]

/-- The tetrahedral amplification is `A^2 = 3/2` — leverage `3` over excess `2`. -/
theorem tetraDesign_amplification_sq (atomIndex : Fin 4) :
    amplification tetraDesign atomIndex ^ 2 = 3 / 2 := by
  have hpos : 0 < heavyExcess tetraDesign atomIndex := by
    rw [tetraDesign_heavyExcess]; norm_num
  rw [amplification_sq hpos, tetraDesign_leverage, tetraDesign_heavyExcess]

/-- The tetrahedral direction cosine is `-1/3`, the classical value. -/
theorem tetraDesign_directionCosine_zeroOne :
    directionCosine tetraDesign 0 1 = -(1 / 3) := by
  rw [directionCosine, tetraDesign_atomPairing_zeroOne, tetraDesign_leverage,
    tetraDesign_leverage, show (3 : ℝ) * 3 = 3 ^ 2 from by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- **The Mercedes point.** `rho = A^2 gamma = (3/2)(-1/3) = -1/2` on every edge of
the tetrahedral triple `{0,1,2}`. -/
theorem tetraDesign_normalizedPairing_zeroOne :
    normalizedPairing tetraDesign 0 1 = -(1 / 2) := by
  rw [normalizedPairing, tetraDesign_atomPairing_zeroOne, tetraDesign_heavyExcess,
    tetraDesign_heavyExcess, show (2 : ℝ) * 2 = 2 ^ 2 from by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem tetraDesign_normalizedPairing_zeroTwo :
    normalizedPairing tetraDesign 0 2 = -(1 / 2) := by
  rw [normalizedPairing, tetraDesign_atomPairing_zeroTwo, tetraDesign_heavyExcess,
    tetraDesign_heavyExcess, show (2 : ℝ) * 2 = 2 ^ 2 from by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem tetraDesign_normalizedPairing_oneTwo :
    normalizedPairing tetraDesign 1 2 = -(1 / 2) := by
  rw [normalizedPairing, tetraDesign_atomPairing_oneTwo, tetraDesign_heavyExcess,
    tetraDesign_heavyExcess, show (2 : ℝ) * 2 = 2 ^ 2 from by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The tetrahedron's correlation matrix is the Mercedes matrix. -/
theorem tetraDesign_correlationMatrixThree :
    correlationMatrixThree (normalizedPairing tetraDesign 0 1) (normalizedPairing tetraDesign 0 2)
        (normalizedPairing tetraDesign 1 2)
      = correlationMatrixThree (-(1 / 2)) (-(1 / 2)) (-(1 / 2)) := by
  rw [tetraDesign_normalizedPairing_zeroOne, tetraDesign_normalizedPairing_zeroTwo,
    tetraDesign_normalizedPairing_oneTwo]

/-- **The tetrahedron sits ON the elliptope boundary.** The Mercedes bracket is
exactly zero — the same zero the repo records as `tetraDesign_discriminantTie = 0`,
now with the leverages divided out. -/
theorem tetraDesign_elliptopeBracket_eq_zero :
    elliptopeBracket (normalizedPairing tetraDesign 0 1) (normalizedPairing tetraDesign 0 2)
      (normalizedPairing tetraDesign 1 2) = 0 := by
  rw [tetraDesign_normalizedPairing_zeroOne, tetraDesign_normalizedPairing_zeroTwo,
    tetraDesign_normalizedPairing_oneTwo, elliptopeBracket]
  norm_num

/-- The Mercedes matrix is positive semidefinite: the tetrahedral triple dominates. -/
theorem tetraDesign_posSemidef_correlationMatrixThree :
    (correlationMatrixThree (normalizedPairing tetraDesign 0 1)
      (normalizedPairing tetraDesign 0 2) (normalizedPairing tetraDesign 1 2)).PosSemidef := by
  refine (posSemidef_correlationMatrixThree_iff _ _ _).mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [tetraDesign_normalizedPairing_zeroOne]; norm_num
  · rw [tetraDesign_normalizedPairing_zeroTwo]; norm_num
  · rw [tetraDesign_normalizedPairing_oneTwo]; norm_num
  · rw [tetraDesign_elliptopeBracket_eq_zero]

/-- It is NOT positive definite: the boundary is reached, not crossed. -/
theorem tetraDesign_not_posDef_correlationMatrixThree :
    ¬ (correlationMatrixThree (normalizedPairing tetraDesign 0 1)
      (normalizedPairing tetraDesign 0 2) (normalizedPairing tetraDesign 1 2)).PosDef := by
  intro hposDef
  have hdet : (correlationMatrixThree (normalizedPairing tetraDesign 0 1)
      (normalizedPairing tetraDesign 0 2) (normalizedPairing tetraDesign 1 2)).det = 0 := by
    rw [det_correlationMatrixThree, tetraDesign_elliptopeBracket_eq_zero]
  exact (tetraDesign_posSemidef_correlationMatrixThree.posDef_iff_det_ne_zero.mp hposDef) hdet

/-! ### The tie locus of a triple -/

/-- A triple **ties**: it dominates, but not strictly. This is the per-triple reading
of `Gtz.IsTie`, whose second clause is exactly `¬ PosDef` at every `k`-subset. -/
def IsTiedTriple (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) : Prop :=
  Dominates D {pivot, pairFirst, pairSecond}
    ∧ ¬ (subsetSum D {pivot, pairFirst, pairSecond} - 1).PosDef

/-- **The tie locus is the vanishing of the tie leg.** A dominating triple fails to
dominate strictly exactly when its gap determinant is zero, and that determinant is
`discriminantTie`. Only distinctness is used. -/
theorem isTiedTriple_iff_dominates_and_discriminantTie_eq_zero (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    IsTiedTriple D pivot pairFirst pairSecond
      ↔ Dominates D {pivot, pairFirst, pairSecond}
        ∧ discriminantTie D pivot pairFirst pairSecond = 0 := by
  rw [IsTiedTriple]
  constructor
  · rintro ⟨hdominates, hnotStrict⟩
    refine ⟨hdominates, ?_⟩
    rw [← det_subsetSum_sub_one_eq_discriminantTie D hpivotFirst hpivotSecond hpairDistinct]
    by_contra hnonzero
    exact hnotStrict (hdominates.posDef_iff_det_ne_zero.mpr hnonzero)
  · rintro ⟨hdominates, hzero⟩
    refine ⟨hdominates, ?_⟩
    intro hposDef
    refine (hdominates.posDef_iff_det_ne_zero.mp hposDef) ?_
    rw [det_subsetSum_sub_one_eq_discriminantTie D hpivotFirst hpivotSecond hpairDistinct]
    exact hzero

/-- **THE TIE LOCUS IN RHO COORDINATES.** A triple of distinct heavy atoms ties
exactly when its three correlations are compatible and the elliptope determinant
vanishes. So the tie locus is the compatible part of Cayley's nodal cubic surface,
and nothing else: the leverages are invisible to it. The compatibility conjunct is
NOT redundant — `elliptopeBracket_incompatible_boundary` together with
`not_posSemidef_correlationMatrixThree_of_incompatible_boundary` exhibits a point of the
bracket's zero set that is not even positive semidefinite. -/
theorem isTiedTriple_iff_isCompatibleTriangle_and_elliptopeBracket_eq_zero
    (D : WeightedDesign m 3) {pivot pairFirst pairSecond : Fin m}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) (hpivotPos : 0 < heavyExcess D pivot)
    (hfirstPos : 0 < heavyExcess D pairFirst) (hsecondPos : 0 < heavyExcess D pairSecond) :
    IsTiedTriple D pivot pairFirst pairSecond
      ↔ IsCompatibleTriangle D pivot pairFirst pairSecond
        ∧ elliptopeBracket (normalizedPairing D pivot pairFirst)
            (normalizedPairing D pivot pairSecond)
            (normalizedPairing D pairFirst pairSecond) = 0 := by
  have hexcessProductPos : 0 < heavyExcess D pivot * heavyExcess D pairFirst
      * heavyExcess D pairSecond := mul_pos (mul_pos hpivotPos hfirstPos) hsecondPos
  have hfactor := discriminantTie_eq_excessProduct_mul_elliptopeBracket D hpivotPos
    hfirstPos hsecondPos
  rw [isTiedTriple_iff_dominates_and_discriminantTie_eq_zero D hpivotFirst hpivotSecond
      hpairDistinct,
    dominates_triple_iff_isCompatibleTriangle_and_elliptopeBracket_nonneg D hpivotFirst
      hpivotSecond hpairDistinct hpivotPos hfirstPos hsecondPos, hfactor,
    mul_eq_zero]
  constructor
  · rintro ⟨⟨hcompatible, _⟩, hzero⟩
    refine ⟨hcompatible, ?_⟩
    rcases hzero with hbad | hgood
    · exact absurd hbad (ne_of_gt hexcessProductPos)
    · exact hgood
  · rintro ⟨hcompatible, hzero⟩
    exact ⟨⟨hcompatible, le_of_eq hzero.symm⟩, Or.inr hzero⟩

/-- The name is honest: at an exact tie no subset dominates strictly, so every
dominating triple of a tied design is a tied triple. -/
theorem isTiedTriple_of_isTie {D : WeightedDesign m 3} (htie : IsTie D)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hdominates : Dominates D {pivot, pairFirst, pairSecond}) :
    IsTiedTriple D pivot pairFirst pairSecond := by
  refine ⟨hdominates, htie.2 _ ?_⟩
  rw [Finset.card_insert_of_notMem (by simp [hpivotFirst, hpivotSecond]),
    Finset.card_insert_of_notMem (by simp [hpairDistinct]), Finset.card_singleton]

/-- **AT AN EXACT TIE EVERY DOMINATING TRIPLE SITS ON THE ELLIPTOPE BOUNDARY.** The
tie boundary of `GtzWeighted` is, triple by triple, the zero set of the elliptope
determinant in rho coordinates — the leverages having been divided out. This is why
the tetrahedron, its splits and the `(7,3)` tie all read `-1/2` on their tight edges:
they are the same Mercedes point of the same cubic surface. -/
theorem elliptopeBracket_eq_zero_of_isTie_of_dominates {D : WeightedDesign m 3}
    (htie : IsTie D) {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotPos : 0 < heavyExcess D pivot) (hfirstPos : 0 < heavyExcess D pairFirst)
    (hsecondPos : 0 < heavyExcess D pairSecond)
    (hdominates : Dominates D {pivot, pairFirst, pairSecond}) :
    elliptopeBracket (normalizedPairing D pivot pairFirst)
      (normalizedPairing D pivot pairSecond)
      (normalizedPairing D pairFirst pairSecond) = 0 :=
  ((isTiedTriple_iff_isCompatibleTriangle_and_elliptopeBracket_eq_zero D hpivotFirst
    hpivotSecond hpairDistinct hpivotPos hfirstPos hsecondPos).mp
      (isTiedTriple_of_isTie htie hpivotFirst hpivotSecond hpairDistinct hdominates)).2

/-- **The tetrahedron ties on `{0,1,2}`, read in rho coordinates.** Compatibility is
`|−1/2| ≤ 1` on each edge and the Mercedes bracket is zero, so the general tie
criterion fires at the campaign's sharpest object. -/
theorem tetraDesign_isTiedTriple : IsTiedTriple tetraDesign 0 1 2 := by
  have hpos : ∀ atomIndex : Fin 4, 0 < heavyExcess tetraDesign atomIndex := by
    intro atomIndex
    rw [tetraDesign_heavyExcess]
    norm_num
  refine (isTiedTriple_iff_isCompatibleTriangle_and_elliptopeBracket_eq_zero tetraDesign
    (by decide) (by decide) (by decide) (hpos 0) (hpos 1) (hpos 2)).mpr
    ⟨⟨?_, ?_, ?_⟩, tetraDesign_elliptopeBracket_eq_zero⟩
  · rw [IsCompatiblePair, pairMinor, tetraDesign_heavyExcess, tetraDesign_heavyExcess,
      tetraDesign_atomPairing_zeroOne]
    norm_num
  · rw [IsCompatiblePair, pairMinor, tetraDesign_heavyExcess, tetraDesign_heavyExcess,
      tetraDesign_atomPairing_zeroTwo]
    norm_num
  · rw [IsCompatiblePair, pairMinor, tetraDesign_heavyExcess, tetraDesign_heavyExcess,
      tetraDesign_atomPairing_oneTwo]
    norm_num

end Gtz

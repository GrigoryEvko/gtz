import Gtz.Wave.KFourBoostProductRefuter

/-!
# The isotropic star cell: the sharp root-free spectral shift at `M(K4)`

`Gtz.quadForm_kFourStarGap` reads the canonical star's chart gap as the heavy tree
masses on the squared coordinates less the cycle energy of the three off-tree edges.
In matrix form that is `D - L`, with `D` the diagonal of heavy tree masses and `L`
the Laplacian of a triangle whose edge weights are the off-tree masses `m 2`, `m 4`,
`m 5`.

## The shift

`D` dominates `T * 1` for `T` the least heavy tree mass, so `D - L` dominates
`T * 1 - L`, and the latter is positive definite exactly when `T` beats the largest
eigenvalue of `L`.  A triangle Laplacian has spectrum `0` and
`(a + b + c) +- sqrt (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a)`, so the test is

  `slack > 0`  and  `laplacianDiscriminant a b c < slack ^ 2`,   `slack = T - (a + b + c)`

and **no square root appears in either conjunct**.  That is the point: the campaign's
exact-rational discipline survives a spectral argument, because the spectral radius
enters only through the discriminant of the characteristic quadratic.

## Why it is root free, in one identity

`Gtz.det_isotropicShiftMatrix` computes the whole determinant of the shifted matrix
as `(slack + a + b + c) * (slack ^ 2 - laplacianDiscriminant a b c)`, so the third
Sylvester minor IS the second conjunct up to a positive factor.  The second minor is
the delicate one, and it turns on the `ring` identity

  `laplacianDiscriminant a b c * (b + c) ^ 2 - (a * (b + c) - (b ^ 2 + c ^ 2)) ^ 2
     = (b - c) ^ 2 * (b * c + a * (b + c))`

(`Gtz.discriminant_mul_sq_sub_sq`), whose right side is manifestly non-negative and
vanishes exactly when `b = c`.  **The second minor is therefore tight, and it is tight
precisely on the locus where two off-tree masses agree.**

## Sharpness

`Gtz.posDef_isotropicShiftMatrix_iff` is an EQUIVALENCE, so on the locus where the
three heavy tree masses agree the cell is not merely sufficient but exact.  On the
equilateral locus of the star -- all three off-tree masses one -- it reads
`min h > 3`, against `min h > 4` for the landed diagonal-dominance cell
`Gtz.posDef_kFourStarGap_of_diagonalDominant` and `min h > 2` for the landed
necessary condition.  `Gtz.starEquilateral_sharp_constant` puts the truth at
`min h > 3`, so **this cell closes the window from the top and the constant three is
attained.**

## The two cells are incomparable

They are not nested.  `Gtz.exists_isotropic_not_dominant` and
`Gtz.exists_dominant_not_isotropic` are exact integer witnesses both ways.  Diagonal
dominance charges each heavy mass against its own two incident edges, so it tolerates
one small heavy mass at a low-degree vertex; the isotropic cell charges the LEAST
heavy mass against the whole spectrum, so it tolerates a badly unbalanced triangle.

## Scope

Section 1 and section 2 are rank free and generic in the ambient size: they are
statements about a symmetric `3 x 3` matrix and three scalars.  RANK enters only in
section 3, through `Gtz.posDef_finThree_iff_leadingMinors` at selection size equal to
the ambient three and through the star congruence of
`Gtz.posDef_directionChartGap_star_iff`, whose basis is a spanning tree of the
rank-three graphic matroid.
-/

namespace Gtz

open scoped Matrix

/-! ## 1. The discriminant of the triangle Laplacian -/

/-- The discriminant of the characteristic quadratic of a triangle Laplacian with
edge weights `edgeA`, `edgeB`, `edgeC`.  Its square root is the deviation of the two
non-zero eigenvalues from their common mean `edgeA + edgeB + edgeC`. -/
noncomputable def laplacianDiscriminant (edgeA edgeB edgeC : ℝ) : ℝ :=
  edgeA ^ 2 + edgeB ^ 2 + edgeC ^ 2 - edgeA * edgeB - edgeB * edgeC - edgeC * edgeA

theorem laplacianDiscriminant_eq (edgeA edgeB edgeC : ℝ) :
    laplacianDiscriminant edgeA edgeB edgeC
      = edgeA ^ 2 + edgeB ^ 2 + edgeC ^ 2
        - edgeA * edgeB - edgeB * edgeC - edgeC * edgeA := rfl

/-- The discriminant is half the sum of the three squared edge gaps. -/
theorem two_mul_laplacianDiscriminant (edgeA edgeB edgeC : ℝ) :
    2 * laplacianDiscriminant edgeA edgeB edgeC
      = (edgeA - edgeB) ^ 2 + (edgeB - edgeC) ^ 2 + (edgeC - edgeA) ^ 2 := by
  rw [laplacianDiscriminant]; ring

theorem laplacianDiscriminant_nonneg (edgeA edgeB edgeC : ℝ) :
    0 ≤ laplacianDiscriminant edgeA edgeB edgeC := by
  nlinarith [sq_nonneg (edgeA - edgeB), sq_nonneg (edgeB - edgeC), sq_nonneg (edgeC - edgeA),
    two_mul_laplacianDiscriminant edgeA edgeB edgeC]

/-- The discriminant vanishes exactly on the equilateral locus. -/
theorem laplacianDiscriminant_eq_zero_iff (edgeA edgeB edgeC : ℝ) :
    laplacianDiscriminant edgeA edgeB edgeC = 0 ↔ edgeA = edgeB ∧ edgeB = edgeC := by
  constructor
  · intro hzero
    have hsum := two_mul_laplacianDiscriminant edgeA edgeB edgeC
    rw [hzero] at hsum
    have hab : (edgeA - edgeB) ^ 2 = 0 := by
      nlinarith [sq_nonneg (edgeA - edgeB), sq_nonneg (edgeB - edgeC), sq_nonneg (edgeC - edgeA)]
    have hbc : (edgeB - edgeC) ^ 2 = 0 := by
      nlinarith [sq_nonneg (edgeA - edgeB), sq_nonneg (edgeB - edgeC), sq_nonneg (edgeC - edgeA)]
    exact ⟨by nlinarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hab],
      by nlinarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hbc]⟩
  · rintro ⟨hab, hbc⟩
    subst hab; subst hbc; rw [laplacianDiscriminant]; ring

theorem laplacianDiscriminant_rotate (edgeA edgeB edgeC : ℝ) :
    laplacianDiscriminant edgeA edgeB edgeC = laplacianDiscriminant edgeB edgeC edgeA := by
  rw [laplacianDiscriminant, laplacianDiscriminant]; ring

theorem laplacianDiscriminant_swap (edgeA edgeB edgeC : ℝ) :
    laplacianDiscriminant edgeA edgeB edgeC = laplacianDiscriminant edgeB edgeA edgeC := by
  rw [laplacianDiscriminant, laplacianDiscriminant]; ring

/-- **THE ENGINE.**  The discriminant beats the squared offset that the second
Sylvester minor produces, by exactly a non-negative square times a positive weight.
Every root-free step below is this identity. -/
theorem discriminant_mul_sq_sub_sq (edgeA edgeB edgeC : ℝ) :
    laplacianDiscriminant edgeA edgeB edgeC * (edgeB + edgeC) ^ 2
        - (edgeA * (edgeB + edgeC) - (edgeB ^ 2 + edgeC ^ 2)) ^ 2
      = (edgeB - edgeC) ^ 2 * (edgeB * edgeC + edgeA * (edgeB + edgeC)) := by
  rw [laplacianDiscriminant]; ring

/-! ## 2. The isotropic shift, and its exact positivity test -/

/-- The matrix `T * 1 - L` for a triangle Laplacian `L` with edge weights `edgeA`
between slots `0` and `1`, `edgeB` between `0` and `2`, `edgeC` between `1` and `2`,
written in terms of the slack `slack = T - (edgeA + edgeB + edgeC)`.  Each diagonal
entry is the slack plus the weight of the OPPOSITE edge. -/
noncomputable def isotropicShiftMatrix (slack edgeA edgeB edgeC : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of
    ![![slack + edgeC, edgeA, edgeB],
      ![edgeA, slack + edgeB, edgeC],
      ![edgeB, edgeC, slack + edgeA]]

@[simp] theorem isotropicShiftMatrix_zero_zero (slack edgeA edgeB edgeC : ℝ) :
    isotropicShiftMatrix slack edgeA edgeB edgeC 0 0 = slack + edgeC := rfl

@[simp] theorem isotropicShiftMatrix_zero_one (slack edgeA edgeB edgeC : ℝ) :
    isotropicShiftMatrix slack edgeA edgeB edgeC 0 1 = edgeA := rfl

@[simp] theorem isotropicShiftMatrix_zero_two (slack edgeA edgeB edgeC : ℝ) :
    isotropicShiftMatrix slack edgeA edgeB edgeC 0 2 = edgeB := rfl

@[simp] theorem isotropicShiftMatrix_one_one (slack edgeA edgeB edgeC : ℝ) :
    isotropicShiftMatrix slack edgeA edgeB edgeC 1 1 = slack + edgeB := rfl

@[simp] theorem isotropicShiftMatrix_one_two (slack edgeA edgeB edgeC : ℝ) :
    isotropicShiftMatrix slack edgeA edgeB edgeC 1 2 = edgeC := rfl

@[simp] theorem isotropicShiftMatrix_two_two (slack edgeA edgeB edgeC : ℝ) :
    isotropicShiftMatrix slack edgeA edgeB edgeC 2 2 = slack + edgeA := rfl

theorem isotropicShiftMatrix_symm (slack edgeA edgeB edgeC : ℝ) :
    (isotropicShiftMatrix slack edgeA edgeB edgeC)ᵀ
      = isotropicShiftMatrix slack edgeA edgeB edgeC := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [isotropicShiftMatrix, Matrix.transpose_apply]

/-- The shifted matrix is the scalar third minor at the shifted surpluses. -/
theorem det_isotropicShiftMatrix_eq_tripleDetForm (slack edgeA edgeB edgeC : ℝ) :
    (isotropicShiftMatrix slack edgeA edgeB edgeC).det
      = tripleDetForm (slack + edgeC) (slack + edgeB) (slack + edgeA) edgeA edgeB edgeC := by
  rw [isotropicShiftMatrix, Matrix.det_fin_three, tripleDetForm]
  simp [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **THE DETERMINANT IS THE TEST.**  The whole third Sylvester minor of the shifted
matrix factors as the shifted trace against the discriminant gap.  No square root, no
eigenvalue, and the second factor is exactly the cell's second conjunct. -/
theorem det_isotropicShiftMatrix (slack edgeA edgeB edgeC : ℝ) :
    (isotropicShiftMatrix slack edgeA edgeB edgeC).det
      = (slack + edgeA + edgeB + edgeC)
        * (slack ^ 2 - laplacianDiscriminant edgeA edgeB edgeC) := by
  rw [det_isotropicShiftMatrix_eq_tripleDetForm, tripleDetForm, laplacianDiscriminant]
  ring

/-- The third Sylvester minor of the shifted matrix, written in the exact shape
`Gtz.posDef_finThree_iff_leadingMinors` produces, equals the shifted trace against the
discriminant gap. -/
theorem isotropicShift_thirdMinor_eq (slack edgeA edgeB edgeC : ℝ) :
    (slack + edgeC) * (slack + edgeB) * (slack + edgeA) - (slack + edgeC) * edgeC ^ 2
        - edgeA ^ 2 * (slack + edgeA) + 2 * edgeA * edgeB * edgeC
        - edgeB ^ 2 * (slack + edgeB)
      = (slack + edgeA + edgeB + edgeC)
        * (slack ^ 2 - laplacianDiscriminant edgeA edgeB edgeC) := by
  rw [laplacianDiscriminant]; ring

/-- The second Sylvester minor splits as the cell's own gap plus a residual that the
engine identity controls. -/
theorem isotropicShift_minorTwo_split (slack edgeA edgeB edgeC : ℝ) :
    (slack + edgeC) * (slack + edgeB) - edgeA ^ 2
      = (slack ^ 2 - laplacianDiscriminant edgeA edgeB edgeC)
        + (edgeB ^ 2 + edgeC ^ 2 + (slack - edgeA) * (edgeB + edgeC)) := by
  rw [laplacianDiscriminant]; ring

/-- The residual of the second minor is non-negative under the cell's hypotheses.
This is where `Gtz.discriminant_mul_sq_sub_sq` is spent, and it is TIGHT: the bound
is an equality when `edgeB = edgeC` and the slack sits on the discriminant. -/
theorem isotropicShift_residual_nonneg {slack edgeA edgeB edgeC : ℝ}
    (hslack : 0 < slack) (hA : 0 ≤ edgeA) (hB : 0 ≤ edgeB) (hC : 0 ≤ edgeC)
    (hdisc : laplacianDiscriminant edgeA edgeB edgeC ≤ slack ^ 2) :
    0 ≤ edgeB ^ 2 + edgeC ^ 2 + (slack - edgeA) * (edgeB + edgeC) := by
  rcases le_or_gt (edgeA * (edgeB + edgeC) - (edgeB ^ 2 + edgeC ^ 2)) 0 with hsmall | hbig
  · nlinarith [mul_nonneg hslack.le (by linarith : (0:ℝ) ≤ edgeB + edgeC)]
  · have hsum : 0 < edgeB + edgeC := by nlinarith [sq_nonneg edgeB, sq_nonneg edgeC]
    have hkey := discriminant_mul_sq_sub_sq edgeA edgeB edgeC
    have hprod : 0 ≤ (edgeB - edgeC) ^ 2 * (edgeB * edgeC + edgeA * (edgeB + edgeC)) := by
      have : 0 ≤ edgeB * edgeC + edgeA * (edgeB + edgeC) := by positivity
      positivity
    have hdiscsq : (edgeA * (edgeB + edgeC) - (edgeB ^ 2 + edgeC ^ 2)) ^ 2
        ≤ laplacianDiscriminant edgeA edgeB edgeC * (edgeB + edgeC) ^ 2 := by linarith
    have hslacksq : (edgeA * (edgeB + edgeC) - (edgeB ^ 2 + edgeC ^ 2)) ^ 2
        ≤ slack ^ 2 * (edgeB + edgeC) ^ 2 := by
      have hpos : (0:ℝ) ≤ (edgeB + edgeC) ^ 2 := sq_nonneg _
      nlinarith [hdiscsq, mul_le_mul_of_nonneg_right hdisc hpos]
    nlinarith [hslacksq, mul_pos hslack hsum, hbig]

/-- The principal minor on slots `{0,2}`, split the same way.  The discriminant is
symmetric, so the split is the slot-`{0,1}` split with the first two edges swapped. -/
theorem isotropicShift_minorZeroTwo_split (slack edgeA edgeB edgeC : ℝ) :
    (slack + edgeC) * (slack + edgeA) - edgeB ^ 2
      = (slack ^ 2 - laplacianDiscriminant edgeA edgeB edgeC)
        + (edgeA ^ 2 + edgeC ^ 2 + (slack - edgeB) * (edgeA + edgeC)) := by
  rw [laplacianDiscriminant]; ring

/-- The principal minor on slots `{1,2}`, split the same way. -/
theorem isotropicShift_minorOneTwo_split (slack edgeA edgeB edgeC : ℝ) :
    (slack + edgeB) * (slack + edgeA) - edgeC ^ 2
      = (slack ^ 2 - laplacianDiscriminant edgeA edgeB edgeC)
        + (edgeA ^ 2 + edgeB ^ 2 + (slack - edgeC) * (edgeA + edgeB)) := by
  rw [laplacianDiscriminant]; ring

/-- **ALL THREE PRINCIPAL `2 x 2` MINORS, NOT ONLY THE LEADING ONE.**  The residual
bound is symmetric under the permutations that fix the discriminant, so the same two
conjuncts control every `2 x 2` principal minor.  The two off-leading minors are what
the Loewner comparison needs, and the leading minor alone does not supply them. -/
theorem isotropicShift_minorZeroTwo_pos {slack edgeA edgeB edgeC : ℝ}
    (hslack : 0 < slack) (hA : 0 ≤ edgeA) (hB : 0 ≤ edgeB) (hC : 0 ≤ edgeC)
    (hdisc : laplacianDiscriminant edgeA edgeB edgeC ≤ slack ^ 2) :
    edgeB ^ 2 ≤ (slack + edgeC) * (slack + edgeA) := by
  have hres := isotropicShift_residual_nonneg (slack := slack) (edgeA := edgeB)
    (edgeB := edgeA) (edgeC := edgeC) hslack hB hA hC
    (by rw [laplacianDiscriminant_swap]; exact hdisc)
  have hsplit := isotropicShift_minorZeroTwo_split slack edgeA edgeB edgeC
  linarith

theorem isotropicShift_minorOneTwo_pos {slack edgeA edgeB edgeC : ℝ}
    (hslack : 0 < slack) (hA : 0 ≤ edgeA) (hB : 0 ≤ edgeB) (hC : 0 ≤ edgeC)
    (hdisc : laplacianDiscriminant edgeA edgeB edgeC ≤ slack ^ 2) :
    edgeC ^ 2 ≤ (slack + edgeB) * (slack + edgeA) := by
  have hres := isotropicShift_residual_nonneg (slack := slack) (edgeA := edgeC)
    (edgeB := edgeA) (edgeC := edgeB) hslack hC hA hB
    (by rw [laplacianDiscriminant_rotate]; exact hdisc)
  have hsplit := isotropicShift_minorOneTwo_split slack edgeA edgeB edgeC
  linarith

/-- **THE ISOTROPIC CELL.**  A positive slack whose square beats the Laplacian
discriminant forces the shifted matrix positive definite.  Root free, division free,
eigenvalue free. -/
theorem posDef_isotropicShiftMatrix {slack edgeA edgeB edgeC : ℝ}
    (hslack : 0 < slack) (hA : 0 ≤ edgeA) (hB : 0 ≤ edgeB) (hC : 0 ≤ edgeC)
    (hdisc : laplacianDiscriminant edgeA edgeB edgeC < slack ^ 2) :
    (isotropicShiftMatrix slack edgeA edgeB edgeC).PosDef := by
  rw [posDef_finThree_iff_leadingMinors _ (isotropicShiftMatrix_symm slack edgeA edgeB edgeC)]
  refine ⟨by simp; linarith, ?_, ?_⟩
  · have hsplit := isotropicShift_minorTwo_split slack edgeA edgeB edgeC
    have hres := isotropicShift_residual_nonneg hslack hA hB hC hdisc.le
    simp only [isotropicShiftMatrix_zero_zero, isotropicShiftMatrix_one_one,
      isotropicShiftMatrix_zero_one]
    linarith
  · simp only [isotropicShiftMatrix_zero_zero, isotropicShiftMatrix_zero_one,
      isotropicShiftMatrix_zero_two, isotropicShiftMatrix_one_one,
      isotropicShiftMatrix_one_two, isotropicShiftMatrix_two_two]
    have hprod : 0 < (slack + edgeA + edgeB + edgeC)
        * (slack ^ 2 - laplacianDiscriminant edgeA edgeB edgeC) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [isotropicShift_thirdMinor_eq slack edgeA edgeB edgeC, hprod]

/-- The determinant clause is NECESSARY as well: positive definiteness forces the
slack squared past the discriminant.  The shifted trace is positive because the first
leading minor is, so the determinant's sign is the second factor's sign. -/
theorem laplacianDiscriminant_lt_sq_of_posDef {slack edgeA edgeB edgeC : ℝ}
    (hA : 0 ≤ edgeA) (hB : 0 ≤ edgeB)
    (hpd : (isotropicShiftMatrix slack edgeA edgeB edgeC).PosDef) :
    laplacianDiscriminant edgeA edgeB edgeC < slack ^ 2 := by
  rw [posDef_finThree_iff_leadingMinors _ (isotropicShiftMatrix_symm slack edgeA edgeB edgeC)]
    at hpd
  obtain ⟨hone, _, hthree⟩ := hpd
  simp only [isotropicShiftMatrix_zero_zero, isotropicShiftMatrix_zero_one,
    isotropicShiftMatrix_zero_two, isotropicShiftMatrix_one_one,
    isotropicShiftMatrix_one_two, isotropicShiftMatrix_two_two] at hone hthree
  have htrace : 0 < slack + edgeA + edgeB + edgeC := by linarith
  nlinarith [isotropicShift_thirdMinor_eq slack edgeA edgeB edgeC, hthree, htrace]

/-- **THE SLACK IS FORCED POSITIVE, AND THE CERTIFICATE IS ONE IDENTITY.**  A
non-positive slack cannot survive the first two leading minors together with the
determinant clause.  Four times the discriminant gap is

  `(2 * edgeA - trace) ^ 2 + 3 * (edgeB - edgeC) ^ 2 + 4 * (-slack) * (trace - 2 * edgeA)`

with `trace = (slack + edgeB) + (slack + edgeC)`, and the last factor is non-negative
because the second leading minor forces `2 * edgeA` below the trace.  Every term is a
square or a product of non-negatives, so **no square root and no eigenvalue appears in
the necessity half either.** -/
theorem pos_slack_of_leadingMinors {slack edgeA edgeB edgeC : ℝ}
    (hA : 0 ≤ edgeA) (hone : 0 < slack + edgeC)
    (htwo : 0 < (slack + edgeC) * (slack + edgeB) - edgeA ^ 2)
    (hdisc : laplacianDiscriminant edgeA edgeB edgeC < slack ^ 2) :
    0 < slack := by
  rcases le_or_gt slack 0 with hnonpos | hpos
  · exfalso
    have hu : 0 < slack + edgeB := by nlinarith [sq_nonneg edgeA]
    have hsum : 0 < (slack + edgeB) + (slack + edgeC) := by linarith
    have hamgm : 4 * ((slack + edgeC) * (slack + edgeB))
        ≤ ((slack + edgeB) + (slack + edgeC)) ^ 2 := by
      nlinarith [sq_nonneg (edgeB - edgeC)]
    have hgap : 0 ≤ (slack + edgeB) + (slack + edgeC) - 2 * edgeA := by
      rcases le_or_gt (2 * edgeA) ((slack + edgeB) + (slack + edgeC)) with hle | hlt
      · linarith
      · exfalso; nlinarith [htwo, hamgm, hsum, hA, hlt]
    have hslackgap : 0 ≤ (-slack) * ((slack + edgeB) + (slack + edgeC) - 2 * edgeA) :=
      mul_nonneg (by linarith) hgap
    rw [laplacianDiscriminant] at hdisc
    nlinarith [hslackgap, sq_nonneg (2 * edgeA - 2 * slack - edgeB - edgeC),
      sq_nonneg (edgeB - edgeC)]
  · exact hpos

/-- **THE ISOTROPIC CELL IS AN EQUIVALENCE.**  At non-negative edge weights the two
conjuncts are exactly positive definiteness of the shifted matrix.  So on the locus
where the three diagonal entries of the unshifted matrix agree the cell is not merely
sufficient -- it decides. -/
theorem posDef_isotropicShiftMatrix_iff {slack edgeA edgeB edgeC : ℝ}
    (hA : 0 ≤ edgeA) (hB : 0 ≤ edgeB) (hC : 0 ≤ edgeC) :
    (isotropicShiftMatrix slack edgeA edgeB edgeC).PosDef
      ↔ 0 < slack ∧ laplacianDiscriminant edgeA edgeB edgeC < slack ^ 2 := by
  constructor
  · intro hpd
    have hdisc := laplacianDiscriminant_lt_sq_of_posDef hA hB hpd
    refine ⟨?_, hdisc⟩
    rw [posDef_finThree_iff_leadingMinors _ (isotropicShiftMatrix_symm slack edgeA edgeB edgeC)]
      at hpd
    obtain ⟨hone, htwo, _⟩ := hpd
    simp only [isotropicShiftMatrix_zero_zero, isotropicShiftMatrix_one_one,
      isotropicShiftMatrix_zero_one] at hone htwo
    exact pos_slack_of_leadingMinors hA hone htwo hdisc
  · rintro ⟨hslack, hdisc⟩
    exact posDef_isotropicShiftMatrix hslack hA hB hC hdisc

/-- The isotropic cell dominates any matrix whose diagonal beats the shift.  This is
the Loewner step that lets a bound on the LEAST heavy tree mass decide the star. -/
theorem posDef_of_isotropicShift_le {slack edgeA edgeB edgeC diagX diagY diagZ : ℝ}
    (hslack : 0 < slack) (hA : 0 ≤ edgeA) (hB : 0 ≤ edgeB) (hC : 0 ≤ edgeC)
    (hdisc : laplacianDiscriminant edgeA edgeB edgeC < slack ^ 2)
    (hX : slack + edgeC ≤ diagX) (hY : slack + edgeB ≤ diagY) (hZ : slack + edgeA ≤ diagZ) :
    0 < tripleDetForm diagX diagY diagZ edgeA edgeB edgeC := by
  have hbase := posDef_isotropicShiftMatrix hslack hA hB hC hdisc
  rw [posDef_finThree_iff_leadingMinors _ (isotropicShiftMatrix_symm slack edgeA edgeB edgeC)]
    at hbase
  obtain ⟨hone, htwo, hthree⟩ := hbase
  simp only [isotropicShiftMatrix_zero_zero, isotropicShiftMatrix_one_one,
    isotropicShiftMatrix_zero_one, isotropicShiftMatrix_zero_two,
    isotropicShiftMatrix_one_two, isotropicShiftMatrix_two_two] at hone htwo hthree
  have hbasedet : 0 < tripleDetForm (slack + edgeC) (slack + edgeB) (slack + edgeA)
      edgeA edgeB edgeC := by rw [tripleDetForm]; nlinarith [hthree]
  have hXpos : 0 < diagX := by linarith
  have hYpos : 0 < diagY := by linarith
  have hZpos : 0 < diagZ := by linarith
  have hstepZ : tripleDetForm (slack + edgeC) (slack + edgeB) (slack + edgeA) edgeA edgeB edgeC
      ≤ tripleDetForm (slack + edgeC) (slack + edgeB) diagZ edgeA edgeB edgeC := by
    rw [tripleDetForm, tripleDetForm]; nlinarith [htwo]
  -- The two off-leading principal minors are what the comparison needs.  The leading
  -- minor alone cannot supply them, and that is the reason the naive chain fails.
  have hZminor : edgeB ^ 2 ≤ (slack + edgeC) * diagZ := by
    have h02 := isotropicShift_minorZeroTwo_pos hslack hA hB hC hdisc.le
    have hmono : (slack + edgeC) * (slack + edgeA) ≤ (slack + edgeC) * diagZ :=
      mul_le_mul_of_nonneg_left hZ (by linarith)
    linarith
  have hYZminor : edgeC ^ 2 ≤ diagY * diagZ := by
    have h12 := isotropicShift_minorOneTwo_pos hslack hA hB hC hdisc.le
    have hstep : (slack + edgeB) * (slack + edgeA) ≤ diagY * (slack + edgeA) :=
      mul_le_mul_of_nonneg_right hY (by linarith)
    have hstep' : diagY * (slack + edgeA) ≤ diagY * diagZ :=
      mul_le_mul_of_nonneg_left hZ (by linarith)
    linarith
  have hstepY : tripleDetForm (slack + edgeC) (slack + edgeB) diagZ edgeA edgeB edgeC
      ≤ tripleDetForm (slack + edgeC) diagY diagZ edgeA edgeB edgeC := by
    rw [tripleDetForm, tripleDetForm]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ diagY - (slack + edgeB))
      (by linarith : (0:ℝ) ≤ (slack + edgeC) * diagZ - edgeB ^ 2)]
  have hstepX : tripleDetForm (slack + edgeC) diagY diagZ edgeA edgeB edgeC
      ≤ tripleDetForm diagX diagY diagZ edgeA edgeB edgeC := by
    rw [tripleDetForm, tripleDetForm]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ diagX - (slack + edgeC))
      (by linarith : (0:ℝ) ≤ diagY * diagZ - edgeC ^ 2)]
  linarith

/-! ## 3. The star cell -/

/-- The isotropic slack of the canonical star: the least heavy tree mass, less the
total off-tree mass. -/
noncomputable def starIsotropicSlack (mass weight : Fin 6 → ℝ) : ℝ :=
  min (mass 0 * (1 - weight 0) / weight 0)
      (min (mass 1 * (1 - weight 1) / weight 1) (mass 3 * (1 - weight 3) / weight 3))
    - (mass 2 + mass 4 + mass 5)

theorem starIsotropicSlack_le_zero (mass weight : Fin 6 → ℝ) :
    starIsotropicSlack mass weight + mass 4
      ≤ mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 5 := by
  have hmin : min (mass 0 * (1 - weight 0) / weight 0)
      (min (mass 1 * (1 - weight 1) / weight 1) (mass 3 * (1 - weight 3) / weight 3))
      ≤ mass 0 * (1 - weight 0) / weight 0 := min_le_left _ _
  rw [starIsotropicSlack]; linarith

theorem starIsotropicSlack_le_one (mass weight : Fin 6 → ℝ) :
    starIsotropicSlack mass weight + mass 5
      ≤ mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 4 := by
  have hmin : min (mass 0 * (1 - weight 0) / weight 0)
      (min (mass 1 * (1 - weight 1) / weight 1) (mass 3 * (1 - weight 3) / weight 3))
      ≤ mass 1 * (1 - weight 1) / weight 1 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  rw [starIsotropicSlack]; linarith

theorem starIsotropicSlack_le_three (mass weight : Fin 6 → ℝ) :
    starIsotropicSlack mass weight + mass 2
      ≤ mass 3 * (1 - weight 3) / weight 3 - mass 4 - mass 5 := by
  have hmin : min (mass 0 * (1 - weight 0) / weight 0)
      (min (mass 1 * (1 - weight 1) / weight 1) (mass 3 * (1 - weight 3) / weight 3))
      ≤ mass 3 * (1 - weight 3) / weight 3 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  rw [starIsotropicSlack]; linarith

/-- **THE ISOTROPIC STAR CELL.**  If the least heavy tree mass beats the total
off-tree mass by a slack whose square passes the Laplacian discriminant of the three
off-tree masses, the canonical star's third minor is positive.

The three off-tree masses enter the cell only through their sum and their
discriminant, so the cell reads a two-number summary of the triangle -- which is why
it is exact when the three heavy masses agree. -/
theorem tripleDetForm_star_of_isotropic (mass weight : Fin 6 → ℝ)
    (h2 : 0 ≤ mass 2) (h4 : 0 ≤ mass 4) (h5 : 0 ≤ mass 5)
    (hslack : 0 < starIsotropicSlack mass weight)
    (hdisc : laplacianDiscriminant (mass 2) (mass 4) (mass 5)
      < starIsotropicSlack mass weight ^ 2) :
    0 < tripleDetForm
        (mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4)
        (mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 5)
        (mass 3 * (1 - weight 3) / weight 3 - mass 4 - mass 5)
        (mass 2) (mass 4) (mass 5) := by
  refine posDef_of_isotropicShift_le hslack h2 h4 h5 hdisc ?_ ?_ ?_
  · have := starIsotropicSlack_le_zero mass weight; linarith
  · have := starIsotropicSlack_le_one mass weight; linarith
  · have := starIsotropicSlack_le_three mass weight; linarith

/-- The second leading minor of the star under the same hypotheses. -/
theorem starMinorTwo_of_isotropic (mass weight : Fin 6 → ℝ)
    (h2 : 0 ≤ mass 2) (h4 : 0 ≤ mass 4) (h5 : 0 ≤ mass 5)
    (hslack : 0 < starIsotropicSlack mass weight)
    (hdisc : laplacianDiscriminant (mass 2) (mass 4) (mass 5)
      < starIsotropicSlack mass weight ^ 2) :
    0 < (mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4)
        * (mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 5) - mass 2 ^ 2 := by
  have hsplit := isotropicShift_minorTwo_split (starIsotropicSlack mass weight)
    (mass 2) (mass 4) (mass 5)
  have hres := isotropicShift_residual_nonneg hslack h2 h4 h5 hdisc.le
  have hX := starIsotropicSlack_le_zero mass weight
  have hY := starIsotropicSlack_le_one mass weight
  have hbase : 0 < (starIsotropicSlack mass weight + mass 5)
      * (starIsotropicSlack mass weight + mass 4) - mass 2 ^ 2 := by linarith
  nlinarith [hX, hY, hbase, hslack, h4, h5]

/-- **THE CELL AT THE CANONICAL STAR.**  Positive definiteness of the star's gap
matrix from the two isotropic conjuncts alone. -/
theorem posDef_kFourStarGap_of_isotropic (mass weight : Fin 6 → ℝ)
    (h2 : 0 ≤ mass 2) (h4 : 0 ≤ mass 4) (h5 : 0 ≤ mass 5)
    (hslack : 0 < starIsotropicSlack mass weight)
    (hdisc : laplacianDiscriminant (mass 2) (mass 4) (mass 5)
      < starIsotropicSlack mass weight ^ 2) :
    (kFourStarGap mass weight).PosDef := by
  rw [posDef_kFourStarGap_iff]
  refine ⟨?_, starMinorTwo_of_isotropic mass weight h2 h4 h5 hslack hdisc,
    tripleDetForm_star_of_isotropic mass weight h2 h4 h5 hslack hdisc⟩
  have := starIsotropicSlack_le_zero mass weight
  linarith

/-- **THE CELL AT THE CHART.**  The same two conjuncts make the canonical star of the
`M(K4)` chart a strict dominator. -/
theorem posDef_directionChartGap_star_of_isotropic (mass weight : Fin 6 → ℝ)
    (h0 : weight 0 ≠ 0) (h1 : weight 1 ≠ 0) (h3 : weight 3 ≠ 0)
    (h2 : 0 ≤ mass 2) (h4 : 0 ≤ mass 4) (h5 : 0 ≤ mass 5)
    (hslack : 0 < starIsotropicSlack mass weight)
    (hdisc : laplacianDiscriminant (mass 2) (mass 4) (mass 5)
      < starIsotropicSlack mass weight ^ 2) :
    (directionChartGap kFourDirection mass weight {0, 1, 3}).PosDef := by
  rw [posDef_directionChartGap_star_iff mass weight h0 h1 h3]
  exact posDef_kFourStarGap_of_isotropic mass weight h2 h4 h5 hslack hdisc

/-! ## 4. Sharpness on the equilateral locus, and the constant three -/

/-- On the equilateral locus the discriminant vanishes, so the cell reads exactly
`slack > 0`, that is least heavy tree mass above three. -/
theorem laplacianDiscriminant_one : laplacianDiscriminant 1 1 1 = 0 := by
  rw [laplacianDiscriminant]; ring

/-- **THE CONSTANT THREE IS ATTAINED.**  At unit off-tree masses the isotropic cell
fires exactly when the least heavy tree mass passes three, which
`Gtz.starEquilateral_sharp_constant` identifies as the truth.  The landed diagonal
dominance cell asks for four, and the landed necessary condition asks for two, so
this cell closes the window from the top. -/
theorem isotropicShift_equilateral_iff (slack : ℝ) :
    (isotropicShiftMatrix slack 1 1 1).PosDef ↔ 0 < slack := by
  rw [posDef_isotropicShiftMatrix_iff (by norm_num) (by norm_num) (by norm_num),
    laplacianDiscriminant_one]
  constructor
  · rintro ⟨hpos, -⟩; exact hpos
  · intro hpos; exact ⟨hpos, by positivity⟩

/-- The equilateral shift at slack `p - 1` is the star's equilateral third minor:
the two readings agree, and both put the threshold at surplus one. -/
theorem det_isotropicShift_equilateral (slack : ℝ) :
    (isotropicShiftMatrix slack 1 1 1).det = (slack + 3) * slack ^ 2 := by
  rw [det_isotropicShiftMatrix, laplacianDiscriminant_one]; ring

/-! ## 5. The two star cells are incomparable -/

/-- The isotropic cell fires where diagonal dominance fails: heavy masses `53, 75,
30` against off-tree masses `6, 9, 10`.  The slack is `5` and the discriminant is
`13`, so `25 > 13` and the cell fires, while the third diagonal entry `11` does not
beat its incident total `19`. -/
theorem exists_isotropic_not_dominant :
    laplacianDiscriminant 6 9 10 < (5:ℝ) ^ 2 ∧ (0:ℝ) < 5
      ∧ ¬ ((9:ℝ) + 10 < 30 - 9 - 10) := by
  refine ⟨by rw [laplacianDiscriminant]; norm_num, by norm_num, by norm_num⟩

/-- The isotropic cell at that witness really does produce a positive third minor. -/
theorem isotropic_witness_tripleDetForm_pos :
    0 < tripleDetForm (53 - 6 - 9) (75 - 6 - 10) (30 - 9 - 10) 6 9 10 := by
  refine posDef_of_isotropicShift_le (slack := 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ (by norm_num) (by norm_num) (by norm_num)
  rw [laplacianDiscriminant]; norm_num

/-- Diagonal dominance fires where the isotropic cell fails: heavy masses `28, 73,
58` against off-tree masses `2, 6, 12`.  Every diagonal entry beats twice its
incident total, while the slack is `8` and the discriminant is `76`, so `64 < 76`. -/
theorem exists_dominant_not_isotropic :
    ((2:ℝ) + 6 < 28 - 2 - 6) ∧ ((2:ℝ) + 12 < 73 - 2 - 12) ∧ ((6:ℝ) + 12 < 58 - 6 - 12)
      ∧ ¬ (laplacianDiscriminant 2 6 12 < (8:ℝ) ^ 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  rw [laplacianDiscriminant]; norm_num

/-- Diagonal dominance at that witness really does produce a positive third minor,
so neither cell subsumes the other. -/
theorem dominant_witness_tripleDetForm_pos :
    0 < tripleDetForm (28 - 2 - 6) (73 - 2 - 12) (58 - 6 - 12) 2 6 12 :=
  tripleDetForm_pos_of_dominant _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-! ## 6. What the cell reads -/

/-- The cell is a two-number summary of the triangle: the total off-tree mass and the
discriminant.  Two triangles with the same sum and the same discriminant are decided
identically at every heavy profile, even though their individual edge weights differ.
This is the precise sense in which the isotropic cell is coarser than Sylvester and
sharper than dominance. -/
theorem isotropicShift_reads_sum_and_discriminant
    {edgeA edgeB edgeC edgeA' edgeB' edgeC' slack : ℝ}
    (hsum : edgeA + edgeB + edgeC = edgeA' + edgeB' + edgeC')
    (hdisc : laplacianDiscriminant edgeA edgeB edgeC
      = laplacianDiscriminant edgeA' edgeB' edgeC') :
    (isotropicShiftMatrix slack edgeA edgeB edgeC).det
      = (isotropicShiftMatrix slack edgeA' edgeB' edgeC').det := by
  rw [det_isotropicShiftMatrix, det_isotropicShiftMatrix, hdisc]
  have : slack + edgeA + edgeB + edgeC = slack + edgeA' + edgeB' + edgeC' := by linarith
  rw [this]

/-- The discriminant is bounded by the squared total, with equality exactly when two
of the three edges vanish.  So the cell's second conjunct is never harder than
`slack > total off-tree mass`, and the two conjuncts collapse to one at a degenerate
triangle. -/
theorem laplacianDiscriminant_le_sq_sum {edgeA edgeB edgeC : ℝ}
    (hA : 0 ≤ edgeA) (hB : 0 ≤ edgeB) (hC : 0 ≤ edgeC) :
    laplacianDiscriminant edgeA edgeB edgeC ≤ (edgeA + edgeB + edgeC) ^ 2 := by
  rw [laplacianDiscriminant]
  nlinarith [mul_nonneg hA hB, mul_nonneg hB hC, mul_nonneg hC hA]

end Gtz

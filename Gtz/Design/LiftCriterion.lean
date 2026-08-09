import Gtz.Design.NormalSchurClosure
import Gtz.Design.TightAxisPairBudget
import Gtz.Design.StressCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The lift criterion at rank three

A pair `C` of labels and a unit normal `n` are given.  Write `h_y := a_y ⬝ᵥ n`
for the normal reading of an atom and `s_y := a_y - h_y n` for its shadow in the
plane `n^⊥`.  The **shadow Gram** `Gamma_{yz} := s_y ⬝ᵥ s_z = a_y ⬝ᵥ a_z - h_y h_z`
is what `Gtz.shadowPairing` computes, and `Delta := Gamma - 1` restricted to the
pair is the gap of the pair in the rank-two shadow design (`Gtz.inPlaneRestriction`
carries the same weights, so this is literally the shadow design's gap).

**The criterion.**  Suppose the pair strictly dominates the shadow, i.e. `Delta`
is positive definite on the pair.  Then for every third label `x`,

  `(subsetSum D (C ∪ {x}) - 1)` is positive definite  ⟺  `0 < liftMarginOf ...`

and the margin is a single polynomial in the shadow Gram entries and the three
normal readings.  It is the `d`-cleared form of `(a_x ⬝ᵥ Q)^2 - (1 + sigma_x) * kappa`
with `Q := n - H⁻¹ r`, `sigma_x := s_x^T H⁻¹ s_x`, `kappa := 1 + eta^T Delta⁻¹ eta`;
no matrix inverse survives the clearing.

**Why one determinant.**  Put the normal LAST in an orthonormal frame.  The first
two leading Sylvester minors of the triple gap are then free consequences of
`Delta > 0`, so positive definiteness of the whole `3x3` collapses to the sign of
the determinant, and `Gtz.shadowGapDeterminantOf_mul_gapDeterminant_eq_liftMarginOf`
converts that sign to the criterion.

**The barrier.**  `Gtz.sum_weight_mul_liftMargin_eq_neg` computes the weighted
average of the margin over ALL labels of the design in closed form; it is
strictly negative whenever the criterion is defined.  So Parseval averaging can
never produce the completing atom — a third barrier alongside the landed
pair-averaging (TieRowLaw) and split-tetrahedron barriers.

**Sharpness.**  The regular tetrahedron, a genuine tie, sits exactly on the
boundary: `Gtz.tetraDesign_liftMargin_eq_zero`.
-/

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## Part 0: two-by-two sign lemmas -/

/-- A positive leading entry and a positive determinant force the other diagonal
entry positive. -/
theorem pos_second_of_pos_first_of_pos_det {firstEntry crossEntry secondEntry : ℝ}
    (hfirst : 0 < firstEntry) (hdet : 0 < firstEntry * secondEntry - crossEntry ^ 2) :
    0 < secondEntry := by
  nlinarith [hfirst, hdet, sq_nonneg crossEntry]

/-- A positive trace and a positive determinant force both diagonal entries
positive. -/
theorem pos_diagonal_of_pos_trace_of_pos_det {cornerEntry crossEntry diagEntry : ℝ}
    (htrace : 0 < cornerEntry + diagEntry)
    (hdet : 0 < cornerEntry * diagEntry - crossEntry ^ 2) :
    0 < cornerEntry ∧ 0 < diagEntry := by
  constructor
  · nlinarith [htrace, hdet, sq_nonneg crossEntry]
  · nlinarith [htrace, hdet, sq_nonneg crossEntry]

/-- The adjugate form of a positive definite symmetric two-by-two is
nonnegative. -/
theorem nonneg_adjugateForm_of_pos_det {cornerEntry crossEntry diagEntry
    probeOne probeTwo : ℝ} (hdiag : 0 < diagEntry)
    (hdet : 0 < cornerEntry * diagEntry - crossEntry ^ 2) :
    0 ≤ diagEntry * probeOne ^ 2 - 2 * crossEntry * probeOne * probeTwo
      + cornerEntry * probeTwo ^ 2 := by
  nlinarith [hdiag, hdet, sq_nonneg (diagEntry * probeOne - crossEntry * probeTwo),
    mul_nonneg hdet.le (sq_nonneg probeTwo)]

/-! ## Part 1: the criterion's scalar vocabulary -/

/-- The shadow-gap determinant of a pair, read off the pair's shadow Gram.  It is
`det (Gamma - 1)`, and it also equals `det H` for the plane operator
`H := Σ_c s_c s_cᵀ - 1` (`Gtz.shadowGapDeterminantOf_eq_planeGapDeterminant`). -/
def shadowGapDeterminantOf (shadowFirstNorm shadowCross shadowSecondNorm : ℝ) : ℝ :=
  (shadowFirstNorm - 1) * (shadowSecondNorm - 1) - shadowCross ^ 2

/-- The pair's normal demand `d * kappa`, cleared by the shadow-gap
determinant. -/
def liftDemandOf (shadowFirstNorm shadowCross shadowSecondNorm heightFirst
    heightSecond : ℝ) : ℝ :=
  shadowGapDeterminantOf shadowFirstNorm shadowCross shadowSecondNorm
    + (heightFirst * ((shadowSecondNorm - 1) * heightFirst - shadowCross * heightSecond)
      + heightSecond * ((shadowFirstNorm - 1) * heightSecond - shadowCross * heightFirst))

/-- The third atom's shadow leverage `d * (1 + sigma_x)`, cleared by the
shadow-gap determinant. -/
def liftLeverageOf (shadowFirstNorm shadowCross shadowSecondNorm shadowFirstThird
    shadowSecondThird shadowThirdNorm : ℝ) : ℝ :=
  shadowGapDeterminantOf shadowFirstNorm shadowCross shadowSecondNorm
    + (shadowFirstNorm + shadowSecondNorm - 1) * shadowThirdNorm
    - shadowFirstThird ^ 2 - shadowSecondThird ^ 2

/-- The third atom's reading `d * (a_x ⬝ᵥ Q)` along the lift direction, cleared
by the shadow-gap determinant. -/
def liftReadingOf (shadowFirstNorm shadowCross shadowSecondNorm shadowFirstThird
    shadowSecondThird heightFirst heightSecond heightThird : ℝ) : ℝ :=
  heightThird * shadowGapDeterminantOf shadowFirstNorm shadowCross shadowSecondNorm
    - (heightFirst * ((shadowSecondNorm - 1) * shadowFirstThird
          - shadowCross * shadowSecondThird)
      + heightSecond * ((shadowFirstNorm - 1) * shadowSecondThird
          - shadowCross * shadowFirstThird))

/-- **The lift margin.**  `d^2 * ((a_x ⬝ᵥ Q)^2 - (1 + sigma_x) * kappa)`, a
polynomial in the shadow Gram of the three atoms and their three normal
readings. -/
def liftMarginOf (shadowFirstNorm shadowCross shadowSecondNorm shadowFirstThird
    shadowSecondThird shadowThirdNorm heightFirst heightSecond heightThird : ℝ) : ℝ :=
  liftReadingOf shadowFirstNorm shadowCross shadowSecondNorm shadowFirstThird
      shadowSecondThird heightFirst heightSecond heightThird ^ 2
    - liftLeverageOf shadowFirstNorm shadowCross shadowSecondNorm shadowFirstThird
        shadowSecondThird shadowThirdNorm
      * liftDemandOf shadowFirstNorm shadowCross shadowSecondNorm heightFirst heightSecond

/-! ## Part 2: the core polynomial identity, in plane coordinates -/

/-- **THE LIFT IDENTITY.**  In an orthonormal frame whose third vector is the
normal, the shadow-gap determinant times the determinant of the triple gap IS the
lift margin.  A polynomial identity in the nine coordinates; no hypothesis, no
inverse, no square root. -/
theorem shadowGapDeterminantOf_mul_gapDeterminant_eq_liftMarginOf
    (firstPlaneOne firstPlaneTwo secondPlaneOne secondPlaneTwo thirdPlaneOne thirdPlaneTwo
      heightFirst heightSecond heightThird : ℝ) :
    shadowGapDeterminantOf (firstPlaneOne ^ 2 + firstPlaneTwo ^ 2)
        (firstPlaneOne * secondPlaneOne + firstPlaneTwo * secondPlaneTwo)
        (secondPlaneOne ^ 2 + secondPlaneTwo ^ 2)
      * ((firstPlaneOne ^ 2 + secondPlaneOne ^ 2 + thirdPlaneOne ^ 2 - 1)
            * (firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 + thirdPlaneTwo ^ 2 - 1)
            * (heightFirst ^ 2 + heightSecond ^ 2 + heightThird ^ 2 - 1)
          - (firstPlaneOne ^ 2 + secondPlaneOne ^ 2 + thirdPlaneOne ^ 2 - 1)
            * (firstPlaneTwo * heightFirst + secondPlaneTwo * heightSecond
                + thirdPlaneTwo * heightThird) ^ 2
          - (firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo
                + thirdPlaneOne * thirdPlaneTwo) ^ 2
            * (heightFirst ^ 2 + heightSecond ^ 2 + heightThird ^ 2 - 1)
          + 2 * (firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo
                + thirdPlaneOne * thirdPlaneTwo)
            * (firstPlaneOne * heightFirst + secondPlaneOne * heightSecond
                + thirdPlaneOne * heightThird)
            * (firstPlaneTwo * heightFirst + secondPlaneTwo * heightSecond
                + thirdPlaneTwo * heightThird)
          - (firstPlaneOne * heightFirst + secondPlaneOne * heightSecond
                + thirdPlaneOne * heightThird) ^ 2
            * (firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 + thirdPlaneTwo ^ 2 - 1))
      = liftMarginOf (firstPlaneOne ^ 2 + firstPlaneTwo ^ 2)
          (firstPlaneOne * secondPlaneOne + firstPlaneTwo * secondPlaneTwo)
          (secondPlaneOne ^ 2 + secondPlaneTwo ^ 2)
          (firstPlaneOne * thirdPlaneOne + firstPlaneTwo * thirdPlaneTwo)
          (secondPlaneOne * thirdPlaneOne + secondPlaneTwo * thirdPlaneTwo)
          (thirdPlaneOne ^ 2 + thirdPlaneTwo ^ 2)
          heightFirst heightSecond heightThird := by
  simp only [liftMarginOf, liftReadingOf, liftLeverageOf, liftDemandOf, shadowGapDeterminantOf]
  ring

/-- **F2.**  The shadow-gap determinant of the pair, computed from the shadow
Gram `Gamma - 1`, equals the determinant of the plane operator
`H = Σ_c s_c s_cᵀ - 1`.  For a square matrix `A`, `AᵀA` and `AAᵀ` have equal
characteristic polynomials; at `2x2` this is a `ring` identity. -/
theorem shadowGapDeterminantOf_eq_planeGapDeterminant
    (firstPlaneOne firstPlaneTwo secondPlaneOne secondPlaneTwo : ℝ) :
    shadowGapDeterminantOf (firstPlaneOne ^ 2 + firstPlaneTwo ^ 2)
        (firstPlaneOne * secondPlaneOne + firstPlaneTwo * secondPlaneTwo)
        (secondPlaneOne ^ 2 + secondPlaneTwo ^ 2)
      = (firstPlaneOne ^ 2 + secondPlaneOne ^ 2 - 1)
          * (firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 - 1)
        - (firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo) ^ 2 := by
  simp only [shadowGapDeterminantOf]
  ring

/-- The trace of the plane operator equals the trace of the shadow gap. -/
theorem planeGapTrace_eq_shadowGapTrace
    (firstPlaneOne firstPlaneTwo secondPlaneOne secondPlaneTwo : ℝ) :
    (firstPlaneOne ^ 2 + secondPlaneOne ^ 2 - 1) + (firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 - 1)
      = (firstPlaneOne ^ 2 + firstPlaneTwo ^ 2 - 1)
        + (secondPlaneOne ^ 2 + secondPlaneTwo ^ 2 - 1) := by
  ring

/-- The lift leverage IS the second leading minor of the triple gap in the
normal-last frame.  This is the step that makes two of the three Sylvester
conditions free. -/
theorem liftLeverageOf_eq_blockMinor
    (firstPlaneOne firstPlaneTwo secondPlaneOne secondPlaneTwo thirdPlaneOne
      thirdPlaneTwo : ℝ) :
    liftLeverageOf (firstPlaneOne ^ 2 + firstPlaneTwo ^ 2)
        (firstPlaneOne * secondPlaneOne + firstPlaneTwo * secondPlaneTwo)
        (secondPlaneOne ^ 2 + secondPlaneTwo ^ 2)
        (firstPlaneOne * thirdPlaneOne + firstPlaneTwo * thirdPlaneTwo)
        (secondPlaneOne * thirdPlaneOne + secondPlaneTwo * thirdPlaneTwo)
        (thirdPlaneOne ^ 2 + thirdPlaneTwo ^ 2)
      = (firstPlaneOne ^ 2 + secondPlaneOne ^ 2 + thirdPlaneOne ^ 2 - 1)
          * (firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 + thirdPlaneTwo ^ 2 - 1)
        - (firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo
            + thirdPlaneOne * thirdPlaneTwo) ^ 2 := by
  simp only [liftLeverageOf, shadowGapDeterminantOf]
  ring

/-- The lift leverage, split as shadow-gap determinant plus the adjugate form of
the plane operator at the third shadow. -/
theorem liftLeverageOf_eq_shadowGapDeterminantOf_add_adjugateForm
    (firstPlaneOne firstPlaneTwo secondPlaneOne secondPlaneTwo thirdPlaneOne
      thirdPlaneTwo : ℝ) :
    liftLeverageOf (firstPlaneOne ^ 2 + firstPlaneTwo ^ 2)
        (firstPlaneOne * secondPlaneOne + firstPlaneTwo * secondPlaneTwo)
        (secondPlaneOne ^ 2 + secondPlaneTwo ^ 2)
        (firstPlaneOne * thirdPlaneOne + firstPlaneTwo * thirdPlaneTwo)
        (secondPlaneOne * thirdPlaneOne + secondPlaneTwo * thirdPlaneTwo)
        (thirdPlaneOne ^ 2 + thirdPlaneTwo ^ 2)
      = shadowGapDeterminantOf (firstPlaneOne ^ 2 + firstPlaneTwo ^ 2)
          (firstPlaneOne * secondPlaneOne + firstPlaneTwo * secondPlaneTwo)
          (secondPlaneOne ^ 2 + secondPlaneTwo ^ 2)
        + ((firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 - 1) * thirdPlaneOne ^ 2
          - 2 * (firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo)
              * thirdPlaneOne * thirdPlaneTwo
          + (firstPlaneOne ^ 2 + secondPlaneOne ^ 2 - 1) * thirdPlaneTwo ^ 2) := by
  simp only [liftLeverageOf, shadowGapDeterminantOf]
  ring

/-! ## Part 3: the criterion in plane coordinates -/

/-- **THE LIFT CRITERION, plane-coordinate form.**  With the normal LAST in an
orthonormal frame, positive definiteness of the triple gap is EXACTLY positivity
of the lift margin, provided the pair strictly dominates the shadow. -/
theorem posDef_planeGapMatrix_iff_pos_liftMarginOf
    (firstPlaneOne firstPlaneTwo secondPlaneOne secondPlaneTwo thirdPlaneOne thirdPlaneTwo
      heightFirst heightSecond heightThird : ℝ)
    (hshadowCorner : 0 < firstPlaneOne ^ 2 + firstPlaneTwo ^ 2 - 1)
    (hshadowDet : 0 < shadowGapDeterminantOf (firstPlaneOne ^ 2 + firstPlaneTwo ^ 2)
        (firstPlaneOne * secondPlaneOne + firstPlaneTwo * secondPlaneTwo)
        (secondPlaneOne ^ 2 + secondPlaneTwo ^ 2)) :
    (!![firstPlaneOne ^ 2 + secondPlaneOne ^ 2 + thirdPlaneOne ^ 2 - 1,
          firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo
            + thirdPlaneOne * thirdPlaneTwo,
          firstPlaneOne * heightFirst + secondPlaneOne * heightSecond
            + thirdPlaneOne * heightThird;
        firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo
            + thirdPlaneOne * thirdPlaneTwo,
          firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 + thirdPlaneTwo ^ 2 - 1,
          firstPlaneTwo * heightFirst + secondPlaneTwo * heightSecond
            + thirdPlaneTwo * heightThird;
        firstPlaneOne * heightFirst + secondPlaneOne * heightSecond
            + thirdPlaneOne * heightThird,
          firstPlaneTwo * heightFirst + secondPlaneTwo * heightSecond
            + thirdPlaneTwo * heightThird,
          heightFirst ^ 2 + heightSecond ^ 2 + heightThird ^ 2 - 1]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef
      ↔ 0 < liftMarginOf (firstPlaneOne ^ 2 + firstPlaneTwo ^ 2)
          (firstPlaneOne * secondPlaneOne + firstPlaneTwo * secondPlaneTwo)
          (secondPlaneOne ^ 2 + secondPlaneTwo ^ 2)
          (firstPlaneOne * thirdPlaneOne + firstPlaneTwo * thirdPlaneTwo)
          (secondPlaneOne * thirdPlaneOne + secondPlaneTwo * thirdPlaneTwo)
          (thirdPlaneOne ^ 2 + thirdPlaneTwo ^ 2)
          heightFirst heightSecond heightThird := by
  have hshadowDetPlain : 0 < (firstPlaneOne ^ 2 + firstPlaneTwo ^ 2 - 1)
      * (secondPlaneOne ^ 2 + secondPlaneTwo ^ 2 - 1)
      - (firstPlaneOne * secondPlaneOne + firstPlaneTwo * secondPlaneTwo) ^ 2 := by
    simpa only [shadowGapDeterminantOf] using hshadowDet
  have hshadowSecond : 0 < secondPlaneOne ^ 2 + secondPlaneTwo ^ 2 - 1 :=
    pos_second_of_pos_first_of_pos_det hshadowCorner hshadowDetPlain
  have hplaneDet : 0 < (firstPlaneOne ^ 2 + secondPlaneOne ^ 2 - 1)
      * (firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 - 1)
      - (firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo) ^ 2 := by
    rw [← shadowGapDeterminantOf_eq_planeGapDeterminant]
    exact hshadowDet
  have hplaneTrace : 0 < (firstPlaneOne ^ 2 + secondPlaneOne ^ 2 - 1)
      + (firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 - 1) := by
    rw [planeGapTrace_eq_shadowGapTrace]
    linarith [hshadowCorner, hshadowSecond]
  obtain ⟨hplaneCorner, hplaneDiag⟩ :=
    pos_diagonal_of_pos_trace_of_pos_det hplaneTrace hplaneDet
  have hcornerMinor : 0 < firstPlaneOne ^ 2 + secondPlaneOne ^ 2 + thirdPlaneOne ^ 2 - 1 := by
    nlinarith [hplaneCorner, sq_nonneg thirdPlaneOne]
  have hadjugate : 0 ≤ (firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 - 1) * thirdPlaneOne ^ 2
      - 2 * (firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo)
          * thirdPlaneOne * thirdPlaneTwo
      + (firstPlaneOne ^ 2 + secondPlaneOne ^ 2 - 1) * thirdPlaneTwo ^ 2 :=
    nonneg_adjugateForm_of_pos_det hplaneDiag hplaneDet
  have hblockMinor : 0 < (firstPlaneOne ^ 2 + secondPlaneOne ^ 2 + thirdPlaneOne ^ 2 - 1)
        * (firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 + thirdPlaneTwo ^ 2 - 1)
      - (firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo
          + thirdPlaneOne * thirdPlaneTwo) ^ 2 := by
    rw [← liftLeverageOf_eq_blockMinor,
      liftLeverageOf_eq_shadowGapDeterminantOf_add_adjugateForm]
    linarith [hshadowDet, hadjugate]
  have hidentity := shadowGapDeterminantOf_mul_gapDeterminant_eq_liftMarginOf
    firstPlaneOne firstPlaneTwo secondPlaneOne secondPlaneTwo thirdPlaneOne thirdPlaneTwo
    heightFirst heightSecond heightThird
  rw [leadingMinors_pos_iff_posDef_fin_three]
  constructor
  · rintro ⟨-, -, hgapDet⟩
    have hproduct := mul_pos hshadowDet hgapDet
    rw [hidentity] at hproduct
    exact hproduct
  · intro hmargin
    refine ⟨hcornerMinor, hblockMinor, ?_⟩
    have hproduct : 0 < shadowGapDeterminantOf (firstPlaneOne ^ 2 + firstPlaneTwo ^ 2)
        (firstPlaneOne * secondPlaneOne + firstPlaneTwo * secondPlaneTwo)
        (secondPlaneOne ^ 2 + secondPlaneTwo ^ 2)
      * ((firstPlaneOne ^ 2 + secondPlaneOne ^ 2 + thirdPlaneOne ^ 2 - 1)
            * (firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 + thirdPlaneTwo ^ 2 - 1)
            * (heightFirst ^ 2 + heightSecond ^ 2 + heightThird ^ 2 - 1)
          - (firstPlaneOne ^ 2 + secondPlaneOne ^ 2 + thirdPlaneOne ^ 2 - 1)
            * (firstPlaneTwo * heightFirst + secondPlaneTwo * heightSecond
                + thirdPlaneTwo * heightThird) ^ 2
          - (firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo
                + thirdPlaneOne * thirdPlaneTwo) ^ 2
            * (heightFirst ^ 2 + heightSecond ^ 2 + heightThird ^ 2 - 1)
          + 2 * (firstPlaneOne * firstPlaneTwo + secondPlaneOne * secondPlaneTwo
                + thirdPlaneOne * thirdPlaneTwo)
            * (firstPlaneOne * heightFirst + secondPlaneOne * heightSecond
                + thirdPlaneOne * heightThird)
            * (firstPlaneTwo * heightFirst + secondPlaneTwo * heightSecond
                + thirdPlaneTwo * heightThird)
          - (firstPlaneOne * heightFirst + secondPlaneOne * heightSecond
                + thirdPlaneOne * heightThird) ^ 2
            * (firstPlaneTwo ^ 2 + secondPlaneTwo ^ 2 + thirdPlaneTwo ^ 2 - 1)) := by
      rw [hidentity]
      exact hmargin
    nlinarith [hproduct, hshadowDet]

/-! ## Part 4: the orthonormal frame bridge -/

/-- The orthogonal matrix whose rows are an orthonormal frame of `R^3`. -/
def frameRowMatrix (frameOne frameTwo frameAxis : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![frameOne, frameTwo, frameAxis]

/-- The Gram entry of the frame matrix against its own transpose. -/
theorem frameRowMatrix_mul_transpose_apply (frameOne frameTwo frameAxis : Fin 3 → ℝ)
    (rowIndex colIndex : Fin 3) :
    (frameRowMatrix frameOne frameTwo frameAxis
        * (frameRowMatrix frameOne frameTwo frameAxis)ᵀ) rowIndex colIndex
      = (![frameOne, frameTwo, frameAxis] rowIndex)
        ⬝ᵥ (![frameOne, frameTwo, frameAxis] colIndex) := by
  rw [Matrix.mul_apply, dotProduct]
  exact Finset.sum_congr rfl fun summandIndex _ => by
    rw [Matrix.transpose_apply]
    rfl

/-- An orthonormal frame gives an orthogonal row matrix. -/
theorem frameRowMatrix_mul_transpose_eq_one {frameOne frameTwo frameAxis : Fin 3 → ℝ}
    (hOneOne : frameOne ⬝ᵥ frameOne = 1) (hTwoTwo : frameTwo ⬝ᵥ frameTwo = 1)
    (hAxisAxis : frameAxis ⬝ᵥ frameAxis = 1) (hOneTwo : frameOne ⬝ᵥ frameTwo = 0)
    (hOneAxis : frameOne ⬝ᵥ frameAxis = 0) (hTwoAxis : frameTwo ⬝ᵥ frameAxis = 0) :
    frameRowMatrix frameOne frameTwo frameAxis
        * (frameRowMatrix frameOne frameTwo frameAxis)ᵀ = 1 := by
  have hTwoOne : frameTwo ⬝ᵥ frameOne = 0 := by rw [dotProduct_comm]; exact hOneTwo
  have hAxisOne : frameAxis ⬝ᵥ frameOne = 0 := by rw [dotProduct_comm]; exact hOneAxis
  have hAxisTwo : frameAxis ⬝ᵥ frameTwo = 0 := by rw [dotProduct_comm]; exact hTwoAxis
  ext rowIndex colIndex
  rw [frameRowMatrix_mul_transpose_apply]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [hOneOne, hTwoTwo, hAxisAxis, hOneTwo, hOneAxis, hTwoAxis,
      hTwoOne, hAxisOne, hAxisTwo]

/-- Conjugating by the frame reads the quadratic form on frame rows. -/
theorem frameRowMatrix_conj_apply (frameOne frameTwo frameAxis : Fin 3 → ℝ)
    (target : Matrix (Fin 3) (Fin 3) ℝ) (rowIndex colIndex : Fin 3) :
    (frameRowMatrix frameOne frameTwo frameAxis * target
        * (frameRowMatrix frameOne frameTwo frameAxis)ᵀ) rowIndex colIndex
      = (![frameOne, frameTwo, frameAxis] rowIndex)
        ⬝ᵥ (target *ᵥ (![frameOne, frameTwo, frameAxis] colIndex)) := by
  simp only [frameRowMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- **Completeness of the frame, bilinear form.**  Every inner product splits
into its three frame coordinates. -/
theorem dotProduct_eq_frameCoordinateSum {frameOne frameTwo frameAxis : Fin 3 → ℝ}
    (hOneOne : frameOne ⬝ᵥ frameOne = 1) (hTwoTwo : frameTwo ⬝ᵥ frameTwo = 1)
    (hAxisAxis : frameAxis ⬝ᵥ frameAxis = 1) (hOneTwo : frameOne ⬝ᵥ frameTwo = 0)
    (hOneAxis : frameOne ⬝ᵥ frameAxis = 0) (hTwoAxis : frameTwo ⬝ᵥ frameAxis = 0)
    (leftVec rightVec : Fin 3 → ℝ) :
    leftVec ⬝ᵥ rightVec
      = (leftVec ⬝ᵥ frameOne) * (rightVec ⬝ᵥ frameOne)
        + (leftVec ⬝ᵥ frameTwo) * (rightVec ⬝ᵥ frameTwo)
        + (leftVec ⬝ᵥ frameAxis) * (rightVec ⬝ᵥ frameAxis) := by
  conv_lhs =>
    rw [orthonormalFrame_expansion hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis hTwoAxis leftVec]
  rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, dotProduct_comm frameOne rightVec,
    dotProduct_comm frameTwo rightVec, dotProduct_comm frameAxis rightVec]

/-! ## Part 5: the criterion on a design -/

/-- The normal reading `h_y = a_y ⬝ᵥ n` of an atom. -/
def normalReading (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (label : Fin size) : ℝ :=
  design.atom label ⬝ᵥ normalVec

/-- The shadow Gram entry `Gamma_{yz} = s_y ⬝ᵥ s_z` of two atoms, where
`s_y = a_y - h_y n` is the shadow of `a_y` in the plane orthogonal to a UNIT
normal.  No frame appears: the shadow Gram is basis free. -/
def shadowPairing (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (leftLabel rightLabel : Fin size) : ℝ :=
  design.atom leftLabel ⬝ᵥ design.atom rightLabel
    - normalReading design normalVec leftLabel * normalReading design normalVec rightLabel

/-- The shadow-gap determinant of a pair at a normal: `det (Gamma - 1)` on the
pair.  Positivity of this together with positivity of the corner says the pair
STRICTLY dominates in the rank-two shadow design at that normal. -/
def shadowGapDeterminant (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond : Fin size) : ℝ :=
  shadowGapDeterminantOf (shadowPairing design normalVec pairFirst pairFirst)
    (shadowPairing design normalVec pairFirst pairSecond)
    (shadowPairing design normalVec pairSecond pairSecond)

/-- **The lift margin of a triple at a normal.** -/
def liftMargin (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond thirdLabel : Fin size) : ℝ :=
  liftMarginOf (shadowPairing design normalVec pairFirst pairFirst)
    (shadowPairing design normalVec pairFirst pairSecond)
    (shadowPairing design normalVec pairSecond pairSecond)
    (shadowPairing design normalVec pairFirst thirdLabel)
    (shadowPairing design normalVec pairSecond thirdLabel)
    (shadowPairing design normalVec thirdLabel thirdLabel)
    (normalReading design normalVec pairFirst)
    (normalReading design normalVec pairSecond)
    (normalReading design normalVec thirdLabel)

/-- The shadow pairing, read in a frame whose third vector is the normal: the
normal coordinate cancels and only the two plane coordinates survive. -/
theorem shadowPairing_eq_planeCoordinates (design : WeightedDesign size 3)
    {frameOne frameTwo normalVec : Fin 3 → ℝ}
    (hOneOne : frameOne ⬝ᵥ frameOne = 1) (hTwoTwo : frameTwo ⬝ᵥ frameTwo = 1)
    (hAxisAxis : normalVec ⬝ᵥ normalVec = 1) (hOneTwo : frameOne ⬝ᵥ frameTwo = 0)
    (hOneAxis : frameOne ⬝ᵥ normalVec = 0) (hTwoAxis : frameTwo ⬝ᵥ normalVec = 0)
    (leftLabel rightLabel : Fin size) :
    shadowPairing design normalVec leftLabel rightLabel
      = (design.atom leftLabel ⬝ᵥ frameOne) * (design.atom rightLabel ⬝ᵥ frameOne)
        + (design.atom leftLabel ⬝ᵥ frameTwo) * (design.atom rightLabel ⬝ᵥ frameTwo) := by
  rw [shadowPairing, normalReading, normalReading,
    dotProduct_eq_frameCoordinateSum hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis hTwoAxis
      (design.atom leftLabel) (design.atom rightLabel)]
  ring

/-- **The frame bridge.**  The gap of a triple is positive definite exactly when
its coordinate matrix in an orthonormal frame is: conjugation by an orthogonal
matrix is an invertible congruence. -/
theorem posDef_tripleGap_iff_posDef_frameGapMatrix (design : WeightedDesign size 3)
    {frameOne frameTwo frameAxis : Fin 3 → ℝ}
    (hOneOne : frameOne ⬝ᵥ frameOne = 1) (hTwoTwo : frameTwo ⬝ᵥ frameTwo = 1)
    (hAxisAxis : frameAxis ⬝ᵥ frameAxis = 1) (hOneTwo : frameOne ⬝ᵥ frameTwo = 0)
    (hOneAxis : frameOne ⬝ᵥ frameAxis = 0) (hTwoAxis : frameTwo ⬝ᵥ frameAxis = 0)
    (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel) :
    (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef
      ↔ (!![(design.atom pairFirst ⬝ᵥ frameOne) ^ 2
              + (design.atom pairSecond ⬝ᵥ frameOne) ^ 2
              + (design.atom thirdLabel ⬝ᵥ frameOne) ^ 2 - 1,
            (design.atom pairFirst ⬝ᵥ frameOne) * (design.atom pairFirst ⬝ᵥ frameTwo)
              + (design.atom pairSecond ⬝ᵥ frameOne) * (design.atom pairSecond ⬝ᵥ frameTwo)
              + (design.atom thirdLabel ⬝ᵥ frameOne) * (design.atom thirdLabel ⬝ᵥ frameTwo),
            (design.atom pairFirst ⬝ᵥ frameOne) * (design.atom pairFirst ⬝ᵥ frameAxis)
              + (design.atom pairSecond ⬝ᵥ frameOne) * (design.atom pairSecond ⬝ᵥ frameAxis)
              + (design.atom thirdLabel ⬝ᵥ frameOne) * (design.atom thirdLabel ⬝ᵥ frameAxis);
          (design.atom pairFirst ⬝ᵥ frameOne) * (design.atom pairFirst ⬝ᵥ frameTwo)
              + (design.atom pairSecond ⬝ᵥ frameOne) * (design.atom pairSecond ⬝ᵥ frameTwo)
              + (design.atom thirdLabel ⬝ᵥ frameOne) * (design.atom thirdLabel ⬝ᵥ frameTwo),
            (design.atom pairFirst ⬝ᵥ frameTwo) ^ 2
              + (design.atom pairSecond ⬝ᵥ frameTwo) ^ 2
              + (design.atom thirdLabel ⬝ᵥ frameTwo) ^ 2 - 1,
            (design.atom pairFirst ⬝ᵥ frameTwo) * (design.atom pairFirst ⬝ᵥ frameAxis)
              + (design.atom pairSecond ⬝ᵥ frameTwo) * (design.atom pairSecond ⬝ᵥ frameAxis)
              + (design.atom thirdLabel ⬝ᵥ frameTwo) * (design.atom thirdLabel ⬝ᵥ frameAxis);
          (design.atom pairFirst ⬝ᵥ frameOne) * (design.atom pairFirst ⬝ᵥ frameAxis)
              + (design.atom pairSecond ⬝ᵥ frameOne) * (design.atom pairSecond ⬝ᵥ frameAxis)
              + (design.atom thirdLabel ⬝ᵥ frameOne) * (design.atom thirdLabel ⬝ᵥ frameAxis),
            (design.atom pairFirst ⬝ᵥ frameTwo) * (design.atom pairFirst ⬝ᵥ frameAxis)
              + (design.atom pairSecond ⬝ᵥ frameTwo) * (design.atom pairSecond ⬝ᵥ frameAxis)
              + (design.atom thirdLabel ⬝ᵥ frameTwo) * (design.atom thirdLabel ⬝ᵥ frameAxis),
            (design.atom pairFirst ⬝ᵥ frameAxis) ^ 2
              + (design.atom pairSecond ⬝ᵥ frameAxis) ^ 2
              + (design.atom thirdLabel ⬝ᵥ frameAxis) ^ 2 - 1]
        : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  classical
  have hTwoOne : frameTwo ⬝ᵥ frameOne = 0 := by rw [dotProduct_comm]; exact hOneTwo
  have hAxisOne : frameAxis ⬝ᵥ frameOne = 0 := by rw [dotProduct_comm]; exact hOneAxis
  have hAxisTwo : frameAxis ⬝ᵥ frameTwo = 0 := by rw [dotProduct_comm]; exact hTwoAxis
  have hframeGram := frameRowMatrix_mul_transpose_eq_one hOneOne hTwoTwo hAxisAxis
    hOneTwo hOneAxis hTwoAxis
  have hdetMul : (frameRowMatrix frameOne frameTwo frameAxis).det
      * ((frameRowMatrix frameOne frameTwo frameAxis)ᵀ).det = 1 := by
    rw [← Matrix.det_mul, hframeGram, Matrix.det_one]
  have hdetUnit : IsUnit ((frameRowMatrix frameOne frameTwo frameAxis)ᵀ).det := by
    refine isUnit_iff_ne_zero.mpr fun hzero => ?_
    rw [hzero, mul_zero] at hdetMul
    exact zero_ne_one hdetMul
  have hsymm := transpose_subsetSum_sub_one design
    ({pairFirst, pairSecond, thirdLabel} : Finset (Fin size))
  have hsumTriple : forall probeLeft probeRight : Fin 3 → ℝ,
      probeLeft ⬝ᵥ ((subsetSum design {pairFirst, pairSecond, thirdLabel} - 1)
          *ᵥ probeRight)
        = (design.atom pairFirst ⬝ᵥ probeLeft) * (design.atom pairFirst ⬝ᵥ probeRight)
          + (design.atom pairSecond ⬝ᵥ probeLeft) * (design.atom pairSecond ⬝ᵥ probeRight)
          + (design.atom thirdLabel ⬝ᵥ probeLeft) * (design.atom thirdLabel ⬝ᵥ probeRight)
          - probeLeft ⬝ᵥ probeRight := by
    intro probeLeft probeRight
    rw [dominationGap_form_pair, Finset.sum_insert (by simp [hFirstSecond, hFirstThird]),
      Finset.sum_insert (by simp [hSecondThird]), Finset.sum_singleton]
    ring
  have hmatrix : frameRowMatrix frameOne frameTwo frameAxis
        * (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1)
        * (frameRowMatrix frameOne frameTwo frameAxis)ᵀ
      = !![(design.atom pairFirst ⬝ᵥ frameOne) ^ 2
              + (design.atom pairSecond ⬝ᵥ frameOne) ^ 2
              + (design.atom thirdLabel ⬝ᵥ frameOne) ^ 2 - 1,
            (design.atom pairFirst ⬝ᵥ frameOne) * (design.atom pairFirst ⬝ᵥ frameTwo)
              + (design.atom pairSecond ⬝ᵥ frameOne) * (design.atom pairSecond ⬝ᵥ frameTwo)
              + (design.atom thirdLabel ⬝ᵥ frameOne) * (design.atom thirdLabel ⬝ᵥ frameTwo),
            (design.atom pairFirst ⬝ᵥ frameOne) * (design.atom pairFirst ⬝ᵥ frameAxis)
              + (design.atom pairSecond ⬝ᵥ frameOne) * (design.atom pairSecond ⬝ᵥ frameAxis)
              + (design.atom thirdLabel ⬝ᵥ frameOne) * (design.atom thirdLabel ⬝ᵥ frameAxis);
          (design.atom pairFirst ⬝ᵥ frameOne) * (design.atom pairFirst ⬝ᵥ frameTwo)
              + (design.atom pairSecond ⬝ᵥ frameOne) * (design.atom pairSecond ⬝ᵥ frameTwo)
              + (design.atom thirdLabel ⬝ᵥ frameOne) * (design.atom thirdLabel ⬝ᵥ frameTwo),
            (design.atom pairFirst ⬝ᵥ frameTwo) ^ 2
              + (design.atom pairSecond ⬝ᵥ frameTwo) ^ 2
              + (design.atom thirdLabel ⬝ᵥ frameTwo) ^ 2 - 1,
            (design.atom pairFirst ⬝ᵥ frameTwo) * (design.atom pairFirst ⬝ᵥ frameAxis)
              + (design.atom pairSecond ⬝ᵥ frameTwo) * (design.atom pairSecond ⬝ᵥ frameAxis)
              + (design.atom thirdLabel ⬝ᵥ frameTwo) * (design.atom thirdLabel ⬝ᵥ frameAxis);
          (design.atom pairFirst ⬝ᵥ frameOne) * (design.atom pairFirst ⬝ᵥ frameAxis)
              + (design.atom pairSecond ⬝ᵥ frameOne) * (design.atom pairSecond ⬝ᵥ frameAxis)
              + (design.atom thirdLabel ⬝ᵥ frameOne) * (design.atom thirdLabel ⬝ᵥ frameAxis),
            (design.atom pairFirst ⬝ᵥ frameTwo) * (design.atom pairFirst ⬝ᵥ frameAxis)
              + (design.atom pairSecond ⬝ᵥ frameTwo) * (design.atom pairSecond ⬝ᵥ frameAxis)
              + (design.atom thirdLabel ⬝ᵥ frameTwo) * (design.atom thirdLabel ⬝ᵥ frameAxis),
            (design.atom pairFirst ⬝ᵥ frameAxis) ^ 2
              + (design.atom pairSecond ⬝ᵥ frameAxis) ^ 2
              + (design.atom thirdLabel ⬝ᵥ frameAxis) ^ 2 - 1] := by
    ext rowIndex colIndex
    rw [frameRowMatrix_conj_apply, hsumTriple]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [hOneOne, hTwoTwo, hAxisAxis, hOneTwo, hOneAxis, hTwoAxis,
        hTwoOne, hAxisOne, hAxisTwo] <;> ring
  rw [posDef_congr_right hsymm hdetUnit, Matrix.transpose_transpose, hmatrix]

/-- The shadow pairing of an atom with itself, in plane coordinates. -/
theorem shadowPairing_self_eq_planeCoordinates (design : WeightedDesign size 3)
    {frameOne frameTwo normalVec : Fin 3 → ℝ}
    (hOneOne : frameOne ⬝ᵥ frameOne = 1) (hTwoTwo : frameTwo ⬝ᵥ frameTwo = 1)
    (hAxisAxis : normalVec ⬝ᵥ normalVec = 1) (hOneTwo : frameOne ⬝ᵥ frameTwo = 0)
    (hOneAxis : frameOne ⬝ᵥ normalVec = 0) (hTwoAxis : frameTwo ⬝ᵥ normalVec = 0)
    (label : Fin size) :
    shadowPairing design normalVec label label
      = (design.atom label ⬝ᵥ frameOne) ^ 2 + (design.atom label ⬝ᵥ frameTwo) ^ 2 := by
  rw [shadowPairing_eq_planeCoordinates design hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis
    hTwoAxis label label]
  ring

/-- **THE LIFT CRITERION AT RANK THREE.**  Let the pair `{pairFirst, pairSecond}`
strictly dominate the shadow design at a unit normal -- that is, its shadow gap
`Delta` is positive definite, recorded here by its corner and its determinant.
Then for EVERY third label the triple gap is positive definite exactly when the
lift margin is positive.  An equivalence, not a sufficient condition; and the
right-hand side is one polynomial in the shadow Gram of the three atoms together
with their three normal readings. -/
theorem posDef_tripleGap_iff_pos_liftMargin (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hshadowCorner : 0 < shadowPairing design normalVec pairFirst pairFirst - 1)
    (hshadowDet : 0 < shadowGapDeterminant design normalVec pairFirst pairSecond) :
    (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef
      ↔ 0 < liftMargin design normalVec pairFirst pairSecond thirdLabel := by
  obtain ⟨frameOne, frameTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  have hselfFirst := shadowPairing_self_eq_planeCoordinates design hOneOne hTwoTwo hunit
    hOneTwo hOneAxis hTwoAxis pairFirst
  have hselfSecond := shadowPairing_self_eq_planeCoordinates design hOneOne hTwoTwo hunit
    hOneTwo hOneAxis hTwoAxis pairSecond
  have hselfThird := shadowPairing_self_eq_planeCoordinates design hOneOne hTwoTwo hunit
    hOneTwo hOneAxis hTwoAxis thirdLabel
  have hcrossPair := shadowPairing_eq_planeCoordinates design hOneOne hTwoTwo hunit
    hOneTwo hOneAxis hTwoAxis pairFirst pairSecond
  have hcrossFirstThird := shadowPairing_eq_planeCoordinates design hOneOne hTwoTwo hunit
    hOneTwo hOneAxis hTwoAxis pairFirst thirdLabel
  have hcrossSecondThird := shadowPairing_eq_planeCoordinates design hOneOne hTwoTwo hunit
    hOneTwo hOneAxis hTwoAxis pairSecond thirdLabel
  rw [hselfFirst] at hshadowCorner
  simp only [shadowGapDeterminant, hselfFirst, hcrossPair, hselfSecond] at hshadowDet
  rw [posDef_tripleGap_iff_posDef_frameGapMatrix design hOneOne hTwoTwo hunit hOneTwo
    hOneAxis hTwoAxis pairFirst pairSecond thirdLabel hFirstSecond hFirstThird hSecondThird]
  simp only [liftMargin, normalReading, hselfFirst, hcrossPair, hselfSecond,
    hcrossFirstThird, hcrossSecondThird, hselfThird]
  exact posDef_planeGapMatrix_iff_pos_liftMarginOf
    (design.atom pairFirst ⬝ᵥ frameOne) (design.atom pairFirst ⬝ᵥ frameTwo)
    (design.atom pairSecond ⬝ᵥ frameOne) (design.atom pairSecond ⬝ᵥ frameTwo)
    (design.atom thirdLabel ⬝ᵥ frameOne) (design.atom thirdLabel ⬝ᵥ frameTwo)
    (design.atom pairFirst ⬝ᵥ normalVec) (design.atom pairSecond ⬝ᵥ normalVec)
    (design.atom thirdLabel ⬝ᵥ normalVec) hshadowCorner hshadowDet

/-! ## Part 6: the pieces of the margin, on a design -/

/-- The reading of an arbitrary label along the lift direction, cleared. -/
def liftReading (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond label : Fin size) : ℝ :=
  liftReadingOf (shadowPairing design normalVec pairFirst pairFirst)
    (shadowPairing design normalVec pairFirst pairSecond)
    (shadowPairing design normalVec pairSecond pairSecond)
    (shadowPairing design normalVec pairFirst label)
    (shadowPairing design normalVec pairSecond label)
    (normalReading design normalVec pairFirst)
    (normalReading design normalVec pairSecond)
    (normalReading design normalVec label)

/-- The shadow leverage of an arbitrary label, cleared. -/
def liftLeverage (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond label : Fin size) : ℝ :=
  liftLeverageOf (shadowPairing design normalVec pairFirst pairFirst)
    (shadowPairing design normalVec pairFirst pairSecond)
    (shadowPairing design normalVec pairSecond pairSecond)
    (shadowPairing design normalVec pairFirst label)
    (shadowPairing design normalVec pairSecond label)
    (shadowPairing design normalVec label label)

/-- The pair's normal demand, cleared.  It does NOT depend on the third label. -/
def liftDemand (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond : Fin size) : ℝ :=
  liftDemandOf (shadowPairing design normalVec pairFirst pairFirst)
    (shadowPairing design normalVec pairFirst pairSecond)
    (shadowPairing design normalVec pairSecond pairSecond)
    (normalReading design normalVec pairFirst)
    (normalReading design normalVec pairSecond)

/-- The margin splits as reading squared minus leverage times demand. -/
theorem liftMargin_eq_reading_sq_sub (design : WeightedDesign size 3)
    (normalVec : Fin 3 → ℝ) (pairFirst pairSecond label : Fin size) :
    liftMargin design normalVec pairFirst pairSecond label
      = liftReading design normalVec pairFirst pairSecond label ^ 2
        - liftLeverage design normalVec pairFirst pairSecond label
          * liftDemand design normalVec pairFirst pairSecond := rfl

/-! ## Part 7: F3, the pair reads itself through the shadow gap alone -/

/-- **F3, first member.**  At the FIRST member of the pair the reading collapses
to minus the first component of `adj(Delta) eta` -- no third-label data at all. -/
theorem liftReadingOf_at_pairFirst (shadowFirstNorm shadowCross shadowSecondNorm
    heightFirst heightSecond : ℝ) :
    liftReadingOf shadowFirstNorm shadowCross shadowSecondNorm shadowFirstNorm shadowCross
        heightFirst heightSecond heightFirst
      = -((shadowSecondNorm - 1) * heightFirst - shadowCross * heightSecond) := by
  simp only [liftReadingOf, shadowGapDeterminantOf]
  ring

/-- **F3, second member.** -/
theorem liftReadingOf_at_pairSecond (shadowFirstNorm shadowCross shadowSecondNorm
    heightFirst heightSecond : ℝ) :
    liftReadingOf shadowFirstNorm shadowCross shadowSecondNorm shadowCross shadowSecondNorm
        heightFirst heightSecond heightSecond
      = -((shadowFirstNorm - 1) * heightSecond - shadowCross * heightFirst) := by
  simp only [liftReadingOf, shadowGapDeterminantOf]
  ring

/-- **F3, leverage at the first member**: `d * (1 + sigma_c) = 2d + (adj Delta)_cc`. -/
theorem liftLeverageOf_at_pairFirst (shadowFirstNorm shadowCross shadowSecondNorm : ℝ) :
    liftLeverageOf shadowFirstNorm shadowCross shadowSecondNorm shadowFirstNorm shadowCross
        shadowFirstNorm
      = 2 * shadowGapDeterminantOf shadowFirstNorm shadowCross shadowSecondNorm
        + (shadowSecondNorm - 1) := by
  simp only [liftLeverageOf, shadowGapDeterminantOf]
  ring

/-- **F3, leverage at the second member.** -/
theorem liftLeverageOf_at_pairSecond (shadowFirstNorm shadowCross shadowSecondNorm : ℝ) :
    liftLeverageOf shadowFirstNorm shadowCross shadowSecondNorm shadowCross shadowSecondNorm
        shadowSecondNorm
      = 2 * shadowGapDeterminantOf shadowFirstNorm shadowCross shadowSecondNorm
        + (shadowFirstNorm - 1) := by
  simp only [liftLeverageOf, shadowGapDeterminantOf]
  ring

/-! ## Part 8: F8, the line-normal collapse -/

/-- **F8, scalar form.**  When both members of the pair have vanishing normal
reading the margin factors: the demand is exactly the shadow-gap determinant. -/
theorem liftMarginOf_of_heights_eq_zero (shadowFirstNorm shadowCross shadowSecondNorm
    shadowFirstThird shadowSecondThird shadowThirdNorm heightThird : ℝ) :
    liftMarginOf shadowFirstNorm shadowCross shadowSecondNorm shadowFirstThird
        shadowSecondThird shadowThirdNorm 0 0 heightThird
      = shadowGapDeterminantOf shadowFirstNorm shadowCross shadowSecondNorm
        * (heightThird ^ 2
              * shadowGapDeterminantOf shadowFirstNorm shadowCross shadowSecondNorm
            - liftLeverageOf shadowFirstNorm shadowCross shadowSecondNorm shadowFirstThird
                shadowSecondThird shadowThirdNorm) := by
  simp only [liftMarginOf, liftReadingOf, liftDemandOf]
  ring

/-- **F8 as a criterion.**  At a normal that both pair members are orthogonal to,
the lift criterion reads simply `h_x^2 > 1 + sigma_x`, in cleared form. -/
theorem pos_liftMarginOf_iff_of_heights_eq_zero {shadowFirstNorm shadowCross shadowSecondNorm
    shadowFirstThird shadowSecondThird shadowThirdNorm heightThird : ℝ}
    (hshadowDet : 0 < shadowGapDeterminantOf shadowFirstNorm shadowCross shadowSecondNorm) :
    0 < liftMarginOf shadowFirstNorm shadowCross shadowSecondNorm shadowFirstThird
        shadowSecondThird shadowThirdNorm 0 0 heightThird
      ↔ liftLeverageOf shadowFirstNorm shadowCross shadowSecondNorm shadowFirstThird
            shadowSecondThird shadowThirdNorm
          < heightThird ^ 2
            * shadowGapDeterminantOf shadowFirstNorm shadowCross shadowSecondNorm := by
  rw [liftMarginOf_of_heights_eq_zero]
  constructor
  · intro hpos
    nlinarith [hpos, hshadowDet]
  · intro hlt
    exact mul_pos hshadowDet (by linarith)

/-- **THE LINE-NORMAL COLLAPSE, on a design.**  If both members of the pair are
orthogonal to the unit normal -- the geometry of a line stratum read at its own
line normal -- then the criterion loses the whole `kappa` factor and becomes a
comparison of the third atom's squared normal reading against its shadow
leverage. -/
theorem posDef_tripleGap_iff_lineNormalCollapse (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hFirstHeight : normalReading design normalVec pairFirst = 0)
    (hSecondHeight : normalReading design normalVec pairSecond = 0)
    (hshadowCorner : 0 < shadowPairing design normalVec pairFirst pairFirst - 1)
    (hshadowDet : 0 < shadowGapDeterminant design normalVec pairFirst pairSecond) :
    (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef
      ↔ liftLeverage design normalVec pairFirst pairSecond thirdLabel
        < normalReading design normalVec thirdLabel ^ 2
          * shadowGapDeterminant design normalVec pairFirst pairSecond := by
  have hdetPlain : 0 < shadowGapDeterminantOf
      (shadowPairing design normalVec pairFirst pairFirst)
      (shadowPairing design normalVec pairFirst pairSecond)
      (shadowPairing design normalVec pairSecond pairSecond) := hshadowDet
  rw [posDef_tripleGap_iff_pos_liftMargin design hunit pairFirst pairSecond thirdLabel
    hFirstSecond hFirstThird hSecondThird hshadowCorner hshadowDet]
  simp only [liftMargin, liftLeverage, shadowGapDeterminant, hFirstHeight, hSecondHeight]
  exact pos_liftMarginOf_iff_of_heights_eq_zero hdetPlain

/-- **THE LINE-NORMAL OBSTRUCTION, named.**  At a normal an atom is orthogonal
to, that atom's shadow self-pairing IS its leverage.  So the corner hypothesis of
the collapse says the pair member is STRICTLY heavy; an atom of leverage exactly
one can never sit in a pair whose shadow gap is positive definite at its own line
normal.  This is why the line-normal route is silent on the canonical
critical-atom fixtures. -/
theorem shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero
    (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ) (label : Fin size)
    (hzero : normalReading design normalVec label = 0) :
    shadowPairing design normalVec label label = leverageOf (design.atom label) := by
  simp only [shadowPairing, hzero, mul_zero, sub_zero, leverageOf, dotProduct]
  exact Finset.sum_congr rfl fun coord _ => (sq (design.atom label coord)).symm

/-- Every nonzero vector normalises to a unit vector with the same orthogonal
complement, so the line normals produced by the stratum lemmas feed the collapse
directly. -/
theorem exists_unitNormal_of_ne_zero {vec : Fin 3 → ℝ} (hne : vec ≠ 0) :
    ∃ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1
      ∧ ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ vec = 0 → probe ⬝ᵥ unitNormal = 0 := by
  have hnormPos : 0 < vec ⬝ᵥ vec := dotProduct_self_pos hne
  refine ⟨(Real.sqrt (vec ⬝ᵥ vec))⁻¹ • vec, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← mul_inv, Real.mul_self_sqrt hnormPos.le]
    exact inv_mul_cancel₀ hnormPos.ne'
  · intro probe hzero
    rw [dotProduct_smul, hzero, smul_eq_mul, mul_zero]

/-! ## Part 9: F7, the averaging barrier -/

/-- Self dot product is leverage. -/
theorem dotProduct_self_eq_leverageOf {rank : ℕ} (vec : Fin rank → ℝ) :
    vec ⬝ᵥ vec = leverageOf vec := by
  simp only [dotProduct, leverageOf]
  exact Finset.sum_congr rfl fun coord _ => (sq (vec coord)).symm

/-- The shadow Gram is symmetric. -/
theorem shadowPairing_comm (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (leftLabel rightLabel : Fin size) :
    shadowPairing design normalVec leftLabel rightLabel
      = shadowPairing design normalVec rightLabel leftLabel := by
  simp only [shadowPairing, normalReading,
    dotProduct_comm (design.atom leftLabel) (design.atom rightLabel)]
  ring

/-- The shadow `s_y = a_y - h_y n` of an atom. -/
def shadowVector (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (label : Fin size) : Fin 3 → ℝ :=
  design.atom label - normalReading design normalVec label • normalVec

/-- An atom reads a shadow through the shadow Gram. -/
theorem dotProduct_atom_shadowVector (design : WeightedDesign size 3)
    (normalVec : Fin 3 → ℝ) (shadowLabel probeLabel : Fin size) :
    design.atom probeLabel ⬝ᵥ shadowVector design normalVec shadowLabel
      = shadowPairing design normalVec shadowLabel probeLabel := by
  simp only [shadowVector, shadowPairing, normalReading, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, dotProduct_comm (design.atom probeLabel) (design.atom shadowLabel)]

/-- A shadow is orthogonal to the unit normal. -/
theorem dotProduct_shadowVector_normal (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1) (label : Fin size) :
    shadowVector design normalVec label ⬝ᵥ normalVec = 0 := by
  simp only [shadowVector, normalReading, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit]
  ring

/-- Two shadows pair through the shadow Gram. -/
theorem dotProduct_shadowVector_shadowVector (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (leftLabel rightLabel : Fin size) :
    shadowVector design normalVec leftLabel ⬝ᵥ shadowVector design normalVec rightLabel
      = shadowPairing design normalVec leftLabel rightLabel := by
  simp only [shadowVector, shadowPairing, normalReading, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, hunit,
    dotProduct_comm normalVec (design.atom rightLabel)]
  ring

/-- The first component of `adj(Delta) eta`; by F3 it is minus the pair's own
reading at its first member. -/
def liftAdjugateFirst (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond : Fin size) : ℝ :=
  (shadowPairing design normalVec pairSecond pairSecond - 1)
      * normalReading design normalVec pairFirst
    - shadowPairing design normalVec pairFirst pairSecond
      * normalReading design normalVec pairSecond

/-- The second component of `adj(Delta) eta`. -/
def liftAdjugateSecond (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond : Fin size) : ℝ :=
  (shadowPairing design normalVec pairFirst pairFirst - 1)
      * normalReading design normalVec pairSecond
    - shadowPairing design normalVec pairFirst pairSecond
      * normalReading design normalVec pairFirst

/-- **THE LIFT DIRECTION**, cleared by the shadow-gap determinant: `d * Q` for
`Q = n - H` inverse applied to `r`.  Built from the normal and the two pair
shadows, with the adjugate coefficients; no inverse is taken. -/
def liftDirection (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond : Fin size) : Fin 3 → ℝ :=
  shadowGapDeterminant design normalVec pairFirst pairSecond • normalVec
    - liftAdjugateFirst design normalVec pairFirst pairSecond
      • shadowVector design normalVec pairFirst
    - liftAdjugateSecond design normalVec pairFirst pairSecond
      • shadowVector design normalVec pairSecond

/-- **The reading IS a dot product.**  Every label's cleared reading is its atom
paired against the single lift direction -- which is exactly what makes Parseval
applicable to the margin. -/
theorem dotProduct_atom_liftDirection (design : WeightedDesign size 3)
    (normalVec : Fin 3 → ℝ) (pairFirst pairSecond label : Fin size) :
    design.atom label ⬝ᵥ liftDirection design normalVec pairFirst pairSecond
      = liftReading design normalVec pairFirst pairSecond label := by
  simp only [liftDirection, liftReading, liftReadingOf, liftAdjugateFirst, liftAdjugateSecond,
    shadowGapDeterminant, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    dotProduct_atom_shadowVector, normalReading]
  ring

/-- Total weighted shadow trace: the shadow of a rank-three design at a unit
normal is a rank-two Parseval frame, so its total leverage is `2`. -/
theorem sum_weight_mul_shadowPairing_self (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1) :
    (∑ label, design.weight label * shadowPairing design normalVec label label) = 2 := by
  have hexpand : (∑ label, design.weight label * shadowPairing design normalVec label label)
      = (∑ label, design.weight label * leverageOf (design.atom label))
        - (∑ label, design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun label _ => ?_
    simp only [shadowPairing, normalReading, dotProduct_self_eq_leverageOf]
    ring
  rw [hexpand, sum_weighted_leverage,
    ← dotProduct_self_eq_sum_weight_mul_sq design normalVec, hunit]
  norm_num

/-- Parseval on a shadow: the weighted average of squared shadow pairings against
one fixed label returns that label's own shadow leverage. -/
theorem sum_weight_mul_shadowPairing_sq (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1) (fixedLabel : Fin size) :
    (∑ label, design.weight label * shadowPairing design normalVec fixedLabel label ^ 2)
      = shadowPairing design normalVec fixedLabel fixedLabel := by
  rw [Finset.sum_congr rfl fun label _ =>
      by rw [← dotProduct_atom_shadowVector design normalVec fixedLabel label],
    ← dotProduct_self_eq_sum_weight_mul_sq design (shadowVector design normalVec fixedLabel),
    dotProduct_shadowVector_shadowVector design hunit fixedLabel fixedLabel]

/-- Parseval at the lift direction. -/
theorem sum_weight_mul_liftReading_sq (design : WeightedDesign size 3)
    (normalVec : Fin 3 → ℝ) (pairFirst pairSecond : Fin size) :
    (∑ label, design.weight label
        * liftReading design normalVec pairFirst pairSecond label ^ 2)
      = liftDirection design normalVec pairFirst pairSecond
        ⬝ᵥ liftDirection design normalVec pairFirst pairSecond := by
  rw [Finset.sum_congr rfl fun label _ =>
      by rw [← dotProduct_atom_liftDirection design normalVec pairFirst pairSecond label],
    ← dotProduct_self_eq_sum_weight_mul_sq design
      (liftDirection design normalVec pairFirst pairSecond)]

/-- The weighted average of the shadow leverage over all labels. -/
theorem sum_weight_mul_liftLeverage (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (pairFirst pairSecond : Fin size) :
    (∑ label, design.weight label
        * liftLeverage design normalVec pairFirst pairSecond label)
      = shadowGapDeterminant design normalVec pairFirst pairSecond
        + (shadowPairing design normalVec pairFirst pairFirst
            + shadowPairing design normalVec pairSecond pairSecond - 2) := by
  have hexpand : (∑ label, design.weight label
        * liftLeverage design normalVec pairFirst pairSecond label)
      = shadowGapDeterminant design normalVec pairFirst pairSecond
          * (∑ label, design.weight label)
        + (shadowPairing design normalVec pairFirst pairFirst
            + shadowPairing design normalVec pairSecond pairSecond - 1)
          * (∑ label, design.weight label * shadowPairing design normalVec label label)
        - (∑ label, design.weight label
            * shadowPairing design normalVec pairFirst label ^ 2)
        - (∑ label, design.weight label
            * shadowPairing design normalVec pairSecond label ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun label _ => ?_
    simp only [liftLeverage, liftLeverageOf, shadowGapDeterminant]
    ring
  rw [hexpand, design.weight_sum_one, sum_weight_mul_shadowPairing_self design hunit,
    sum_weight_mul_shadowPairing_sq design hunit pairFirst,
    sum_weight_mul_shadowPairing_sq design hunit pairSecond]
  ring

/-- **THE AVERAGING BARRIER (F7).**  The weighted average of the lift margin over
ALL labels of the design is this closed form.  Averaging cannot produce the
completing atom: whenever the criterion is even defined the average is strictly
negative, so no Parseval argument over the whole design can exhibit a label with
positive margin.  Third barrier of the campaign, alongside the landed
pair-averaging law and the split-tetrahedron surplus. -/
theorem sum_weight_mul_liftMargin_eq_neg (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (pairFirst pairSecond : Fin size) :
    (∑ label, design.weight label * liftMargin design normalVec pairFirst pairSecond label)
      = -(shadowGapDeterminant design normalVec pairFirst pairSecond
          * ((shadowPairing design normalVec pairFirst pairFirst - 1)
              + (shadowPairing design normalVec pairSecond pairSecond - 1)
            + normalReading design normalVec pairFirst ^ 2
            + normalReading design normalVec pairSecond ^ 2)) := by
  have hsplit : (∑ label, design.weight label
        * liftMargin design normalVec pairFirst pairSecond label)
      = (∑ label, design.weight label
          * liftReading design normalVec pairFirst pairSecond label ^ 2)
        - liftDemand design normalVec pairFirst pairSecond
          * (∑ label, design.weight label
              * liftLeverage design normalVec pairFirst pairSecond label) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [liftMargin_eq_reading_sq_sub]
    ring
  rw [hsplit, sum_weight_mul_liftReading_sq, sum_weight_mul_liftLeverage design hunit]
  simp only [liftDirection, liftDemand, liftDemandOf, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, hunit,
    dotProduct_shadowVector_normal design hunit,
    dotProduct_comm normalVec (shadowVector design normalVec pairFirst),
    dotProduct_comm normalVec (shadowVector design normalVec pairSecond),
    dotProduct_shadowVector_shadowVector design hunit,
    shadowPairing_comm design normalVec pairSecond pairFirst,
    liftAdjugateFirst, liftAdjugateSecond, shadowGapDeterminant, shadowGapDeterminantOf]
  ring

/-- The barrier, as a strict sign.  Whenever the pair strictly dominates the
shadow the whole design averages to a strictly negative margin. -/
theorem sum_weight_mul_liftMargin_neg (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (pairFirst pairSecond : Fin size)
    (hshadowCorner : 0 < shadowPairing design normalVec pairFirst pairFirst - 1)
    (hshadowDet : 0 < shadowGapDeterminant design normalVec pairFirst pairSecond) :
    (∑ label, design.weight label * liftMargin design normalVec pairFirst pairSecond label)
      < 0 := by
  have hdetPlain : 0 < shadowGapDeterminantOf
      (shadowPairing design normalVec pairFirst pairFirst)
      (shadowPairing design normalVec pairFirst pairSecond)
      (shadowPairing design normalVec pairSecond pairSecond) := hshadowDet
  have hshadowSecond : 0 < shadowPairing design normalVec pairSecond pairSecond - 1 :=
    pos_second_of_pos_first_of_pos_det hshadowCorner
      (by simpa only [shadowGapDeterminantOf] using hdetPlain)
  rw [sum_weight_mul_liftMargin_eq_neg design hunit]
  have hfactor : 0 < (shadowPairing design normalVec pairFirst pairFirst - 1)
      + (shadowPairing design normalVec pairSecond pairSecond - 1)
      + normalReading design normalVec pairFirst ^ 2
      + normalReading design normalVec pairSecond ^ 2 := by
    nlinarith [hshadowCorner, hshadowSecond,
      sq_nonneg (normalReading design normalVec pairFirst),
      sq_nonneg (normalReading design normalVec pairSecond)]
  simpa using mul_pos hshadowDet hfactor

/-! ## Part 10: sharpness at the regular tetrahedron -/

/-- Distinct tetrahedron vertices pair to `-1`. -/
theorem tetraAtom_dotProduct_of_ne {leftIndex rightIndex : Fin 4} (hne : leftIndex ≠ rightIndex) :
    tetraAtom leftIndex ⬝ᵥ tetraAtom rightIndex = -1 := by
  fin_cases leftIndex <;> fin_cases rightIndex <;>
    simp_all [tetraAtom, dotProduct, Fin.sum_univ_three]

/-- The unit normal through the fourth tetrahedron vertex. -/
noncomputable def tetraSharpnessNormal : Fin 3 → ℝ := (Real.sqrt 3)⁻¹ • tetraAtom 3

theorem tetraSharpnessNormal_dotProduct_self :
    tetraSharpnessNormal ⬝ᵥ tetraSharpnessNormal = 1 := by
  rw [tetraSharpnessNormal, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    tetraAtom_dot_self, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

/-- The three remaining vertices all read the same negative height. -/
theorem tetraSharpnessNormal_normalReading {label : Fin 4} (hne : label ≠ 3) :
    normalReading tetraDesign tetraSharpnessNormal label = -(Real.sqrt 3)⁻¹ := by
  have hatom : tetraDesign.atom label = tetraAtom label := rfl
  rw [normalReading, hatom, tetraSharpnessNormal, dotProduct_smul, smul_eq_mul,
    tetraAtom_dotProduct_of_ne hne]
  ring

/-- Each remaining vertex has shadow leverage `8/3`. -/
theorem tetraSharpnessNormal_shadowPairing_self {label : Fin 4} (hne : label ≠ 3) :
    shadowPairing tetraDesign tetraSharpnessNormal label label = 8 / 3 := by
  have hatom : tetraDesign.atom label = tetraAtom label := rfl
  have hsq : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = 3⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [shadowPairing, hatom, tetraAtom_dot_self,
    tetraSharpnessNormal_normalReading hne]
  linear_combination -hsq

/-- Distinct remaining vertices have shadow pairing `-4/3`. -/
theorem tetraSharpnessNormal_shadowPairing_cross {leftLabel rightLabel : Fin 4}
    (hleftRight : leftLabel ≠ rightLabel) (hleft : leftLabel ≠ 3) (hright : rightLabel ≠ 3) :
    shadowPairing tetraDesign tetraSharpnessNormal leftLabel rightLabel = -(4 / 3) := by
  have hatomLeft : tetraDesign.atom leftLabel = tetraAtom leftLabel := rfl
  have hatomRight : tetraDesign.atom rightLabel = tetraAtom rightLabel := rfl
  have hsq : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = 3⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [shadowPairing, hatomLeft, hatomRight, tetraAtom_dotProduct_of_ne hleftRight,
    tetraSharpnessNormal_normalReading hleft, tetraSharpnessNormal_normalReading hright]
  linear_combination -hsq

/-- The pair `{0,1}` strictly dominates the tetrahedron's shadow at this normal:
its shadow-gap determinant is exactly `1`. -/
theorem tetraDesign_shadowGapDeterminant_eq_one :
    shadowGapDeterminant tetraDesign tetraSharpnessNormal 0 1 = 1 := by
  rw [shadowGapDeterminant, tetraSharpnessNormal_shadowPairing_self (by decide),
    tetraSharpnessNormal_shadowPairing_cross (by decide) (by decide) (by decide),
    tetraSharpnessNormal_shadowPairing_self (by decide), shadowGapDeterminantOf]
  norm_num

/-- The corner of the tetrahedron's shadow gap at this normal is `5/3`. -/
theorem tetraDesign_shadowPairing_corner_pos :
    0 < shadowPairing tetraDesign tetraSharpnessNormal 0 0 - 1 := by
  rw [tetraSharpnessNormal_shadowPairing_self (by decide)]
  norm_num

/-- **SHARPNESS.**  At the regular tetrahedron -- a genuine tie -- with the
normal through the fourth vertex and the pair `{0,1}`, the lift margin of the
completing atom is EXACTLY ZERO.  The tie sits precisely on the boundary of the
criterion, so the criterion is not a dressed-up tautology: it is sharp. -/
theorem tetraDesign_liftMargin_eq_zero :
    liftMargin tetraDesign tetraSharpnessNormal 0 1 2 = 0 := by
  have hsq : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = 3⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [liftMargin, tetraSharpnessNormal_shadowPairing_self (by decide : (0 : Fin 4) ≠ 3),
    tetraSharpnessNormal_shadowPairing_cross (by decide : (0 : Fin 4) ≠ 1) (by decide)
      (by decide),
    tetraSharpnessNormal_shadowPairing_self (by decide : (1 : Fin 4) ≠ 3),
    tetraSharpnessNormal_shadowPairing_cross (by decide : (0 : Fin 4) ≠ 2) (by decide)
      (by decide),
    tetraSharpnessNormal_shadowPairing_cross (by decide : (1 : Fin 4) ≠ 2) (by decide)
      (by decide),
    tetraSharpnessNormal_shadowPairing_self (by decide : (2 : Fin 4) ≠ 3),
    tetraSharpnessNormal_normalReading (by decide : (0 : Fin 4) ≠ 3),
    tetraSharpnessNormal_normalReading (by decide : (1 : Fin 4) ≠ 3),
    tetraSharpnessNormal_normalReading (by decide : (2 : Fin 4) ≠ 3)]
  simp only [liftMarginOf, liftReadingOf, liftLeverageOf, liftDemandOf, shadowGapDeterminantOf]
  linear_combination (27 : ℝ) * hsq

/-- **NON-VACUITY, through the criterion.**  The tetrahedron's triple `{0,1,2}`
does not strictly dominate -- rederived here from the lift criterion alone, at a
normal where the criterion's hypothesis genuinely holds. -/
theorem tetraDesign_not_posDef_tripleGap :
    ¬ (subsetSum tetraDesign {0, 1, 2} - 1).PosDef := by
  intro hposDef
  have hmargin := (posDef_tripleGap_iff_pos_liftMargin tetraDesign
    tetraSharpnessNormal_dotProduct_self 0 1 2 (by decide) (by decide) (by decide)
    tetraDesign_shadowPairing_corner_pos
    (by rw [tetraDesign_shadowGapDeterminant_eq_one]; norm_num)).mp hposDef
  rw [tetraDesign_liftMargin_eq_zero] at hmargin
  exact lt_irrefl 0 hmargin

/-! ## Part 11: the plug, and coverage -/

/-- **THE PLUG.**  The shape every rank-three obligation asks for -- a card-three
subset whose gap is positive definite -- produced from ONE positive lift margin
at ONE normal.  This is the entry point for the strike lanes. -/
theorem exists_posDef_cardThree_of_pos_liftMargin (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hshadowCorner : 0 < shadowPairing design normalVec pairFirst pairFirst - 1)
    (hshadowDet : 0 < shadowGapDeterminant design normalVec pairFirst pairSecond)
    (hmargin : 0 < liftMargin design normalVec pairFirst pairSecond thirdLabel) :
    ∃ selected : Finset (Fin size), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef :=
  ⟨{pairFirst, pairSecond, thirdLabel},
    card_labelTriple_eq_three hFirstSecond hFirstThird hSecondThird,
    (posDef_tripleGap_iff_pos_liftMargin design hunit pairFirst pairSecond thirdLabel
      hFirstSecond hFirstThird hSecondThird hshadowCorner hshadowDet).mpr hmargin⟩

/-- A vanishing shadow leverage forces a vanishing shadow vector. -/
theorem shadowVector_eq_zero_of_shadowPairing_self_eq_zero (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1) (label : Fin size)
    (hflat : shadowPairing design normalVec label label = 0) :
    shadowVector design normalVec label = 0 :=
  eq_zero_of_dotProduct_self_eq_zero
    (by rw [dotProduct_shadowVector_shadowVector design hunit]; exact hflat)

/-- A flat atom pairs to zero with every shadow. -/
theorem shadowPairing_eq_zero_of_flat (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1) (otherLabel label : Fin size)
    (hflat : shadowPairing design normalVec label label = 0) :
    shadowPairing design normalVec otherLabel label = 0 := by
  rw [← dotProduct_shadowVector_shadowVector design hunit otherLabel label,
    shadowVector_eq_zero_of_shadowPairing_self_eq_zero design hunit label hflat,
    dotProduct_zero]

/-- An atom parallel to the unit normal is flat: its shadow leverage vanishes.
So the flatness hypothesis of the coverage theorem is met at the normal through
any nonzero atom of the triple. -/
theorem shadowPairing_self_eq_zero_of_normal_parallel (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1) (label : Fin size)
    {scale : ℝ} (hparallel : normalVec = scale • design.atom label) :
    shadowPairing design normalVec label label = 0 := by
  have hscale : scale * (scale * (design.atom label ⬝ᵥ design.atom label)) = 1 := by
    rw [hparallel, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hunit
    exact hunit
  have hreading : normalReading design normalVec label
      = scale * (design.atom label ⬝ᵥ design.atom label) := by
    rw [normalReading, hparallel, dotProduct_smul, smul_eq_mul]
  rw [shadowPairing, hreading]
  linear_combination (-(design.atom label ⬝ᵥ design.atom label)) * hscale

/-- **COVERAGE: the criterion has no blind spot.**  Take any strictly dominating
triple and any unit normal at which the third member is flat -- for instance the
normal through that member itself.  Then the OTHER two strictly dominate the
shadow, so the criterion's hypothesis holds and, being an equivalence, the
criterion fires.  Every strictly dominating triple is therefore visible, at three
distinct normals.  The flip side, which the strike lanes must keep in view: the
criterion is an exact reformulation of positive definiteness, not a relaxation --
its value is the collapse to ONE determinant, not extra reach. -/
theorem shadowGap_pos_of_posDef_tripleGap_of_flatThird (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hflat : shadowPairing design normalVec thirdLabel thirdLabel = 0)
    (hposDef : (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef) :
    0 < shadowPairing design normalVec pairFirst pairFirst - 1
      ∧ 0 < shadowGapDeterminant design normalVec pairFirst pairSecond := by
  obtain ⟨frameOne, frameTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  have hatomParallel : design.atom thirdLabel
      = normalReading design normalVec thirdLabel • normalVec := by
    have hzero := shadowVector_eq_zero_of_shadowPairing_self_eq_zero design hunit thirdLabel hflat
    rw [shadowVector, sub_eq_zero] at hzero
    exact hzero
  have hthirdOne : design.atom thirdLabel ⬝ᵥ frameOne = 0 := by
    rw [hatomParallel, smul_dotProduct, smul_eq_mul,
      dotProduct_comm normalVec frameOne, hOneAxis, mul_zero]
  have hthirdTwo : design.atom thirdLabel ⬝ᵥ frameTwo = 0 := by
    rw [hatomParallel, smul_dotProduct, smul_eq_mul,
      dotProduct_comm normalVec frameTwo, hTwoAxis, mul_zero]
  have hframePosDef := (posDef_tripleGap_iff_posDef_frameGapMatrix design hOneOne hTwoTwo hunit
    hOneTwo hOneAxis hTwoAxis pairFirst pairSecond thirdLabel hFirstSecond hFirstThird
    hSecondThird).mp hposDef
  have hcornerMinor := posDef_fin_three_corner_pos hframePosDef
  have hblockMinor := posDef_fin_three_blockMinor_pos hframePosDef
  rw [hthirdOne] at hcornerMinor
  rw [hthirdOne, hthirdTwo] at hblockMinor
  have hplaneCorner : 0 < (design.atom pairFirst ⬝ᵥ frameOne) ^ 2
      + (design.atom pairSecond ⬝ᵥ frameOne) ^ 2 - 1 := by nlinarith [hcornerMinor]
  have hplaneDet : 0 < ((design.atom pairFirst ⬝ᵥ frameOne) ^ 2
        + (design.atom pairSecond ⬝ᵥ frameOne) ^ 2 - 1)
      * ((design.atom pairFirst ⬝ᵥ frameTwo) ^ 2
        + (design.atom pairSecond ⬝ᵥ frameTwo) ^ 2 - 1)
      - ((design.atom pairFirst ⬝ᵥ frameOne) * (design.atom pairFirst ⬝ᵥ frameTwo)
        + (design.atom pairSecond ⬝ᵥ frameOne)
          * (design.atom pairSecond ⬝ᵥ frameTwo)) ^ 2 := by nlinarith [hblockMinor]
  have hplaneDiag : 0 < (design.atom pairFirst ⬝ᵥ frameTwo) ^ 2
      + (design.atom pairSecond ⬝ᵥ frameTwo) ^ 2 - 1 :=
    pos_second_of_pos_first_of_pos_det hplaneCorner hplaneDet
  have hselfFirst := shadowPairing_self_eq_planeCoordinates design hOneOne hTwoTwo hunit
    hOneTwo hOneAxis hTwoAxis pairFirst
  have hselfSecond := shadowPairing_self_eq_planeCoordinates design hOneOne hTwoTwo hunit
    hOneTwo hOneAxis hTwoAxis pairSecond
  have hcrossPair := shadowPairing_eq_planeCoordinates design hOneOne hTwoTwo hunit
    hOneTwo hOneAxis hTwoAxis pairFirst pairSecond
  have hshadowDet : 0 < shadowGapDeterminant design normalVec pairFirst pairSecond := by
    rw [shadowGapDeterminant, hselfFirst, hcrossPair, hselfSecond,
      shadowGapDeterminantOf_eq_planeGapDeterminant]
    exact hplaneDet
  refine ⟨?_, hshadowDet⟩
  have hshadowDetPlain : 0 < (shadowPairing design normalVec pairFirst pairFirst - 1)
      * (shadowPairing design normalVec pairSecond pairSecond - 1)
      - shadowPairing design normalVec pairFirst pairSecond ^ 2 := by
    simpa only [shadowGapDeterminant, shadowGapDeterminantOf] using hshadowDet
  have htrace : 0 < (shadowPairing design normalVec pairFirst pairFirst - 1)
      + (shadowPairing design normalVec pairSecond pairSecond - 1) := by
    rw [hselfFirst, hselfSecond, ← planeGapTrace_eq_shadowGapTrace]
    linarith [hplaneCorner, hplaneDiag]
  exact (pos_diagonal_of_pos_trace_of_pos_det htrace hshadowDetPlain).1


/-- Every nonzero vector normalises to a unit vector PARALLEL to it. -/
theorem exists_unitNormal_parallel_of_ne_zero {vec : Fin 3 → ℝ} (hne : vec ≠ 0) :
    ∃ (unitNormal : Fin 3 → ℝ) (scale : ℝ), unitNormal ⬝ᵥ unitNormal = 1
      ∧ unitNormal = scale • vec := by
  have hnormPos : 0 < vec ⬝ᵥ vec := dotProduct_self_pos hne
  refine ⟨(Real.sqrt (vec ⬝ᵥ vec))⁻¹ • vec, (Real.sqrt (vec ⬝ᵥ vec))⁻¹, ?_, rfl⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt hnormPos.le]
  exact inv_mul_cancel₀ hnormPos.ne'

/-- **COVERAGE, packaged.**  Every strictly dominating triple with a nonzero
third atom is SEEN by the criterion, at the unit normal through that atom: the
other two strictly dominate the shadow there and the margin is positive. -/
theorem exists_pos_liftMargin_of_posDef_tripleGap (design : WeightedDesign size 3)
    (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel) (hthirdNe : design.atom thirdLabel ≠ 0)
    (hposDef : (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef) :
    ∃ normalVec : Fin 3 → ℝ, normalVec ⬝ᵥ normalVec = 1
      ∧ 0 < shadowPairing design normalVec pairFirst pairFirst - 1
      ∧ 0 < shadowGapDeterminant design normalVec pairFirst pairSecond
      ∧ 0 < liftMargin design normalVec pairFirst pairSecond thirdLabel := by
  obtain ⟨normalVec, scale, hunit, hparallel⟩ := exists_unitNormal_parallel_of_ne_zero hthirdNe
  have hflat := shadowPairing_self_eq_zero_of_normal_parallel design hunit thirdLabel hparallel
  obtain ⟨hcorner, hdet⟩ := shadowGap_pos_of_posDef_tripleGap_of_flatThird design hunit
    pairFirst pairSecond thirdLabel hFirstSecond hFirstThird hSecondThird hflat hposDef
  exact ⟨normalVec, hunit, hcorner, hdet,
    (posDef_tripleGap_iff_pos_liftMargin design hunit pairFirst pairSecond thirdLabel
      hFirstSecond hFirstThird hSecondThird hcorner hdet).mp hposDef⟩

end Gtz

/-
# The plane branch: one determinant sign per completion of a plane-strict pair

`Gtz.UThreeSixPlaneTenCandidateBranch` asks, for every line-free off-conic design
whose base triple `{0,1,2}` dominates with a two-dimensional tight space, that one
of ten explicit triples be a strict dominator.  The landed hinge
`Gtz.exists_free_pairPlaneStrict_of_planeBranch` hands over a free PAIR
`{strongLabel, otherLabel} ⊆ {3,4,5}` whose gap is strictly positive on the whole
tight plane -- the plane being the orthogonal complement of an explicit unit
`axis`, supplied together with an orthonormal frame `pOne, pTwo, axis`.

This file turns that pair into a decision procedure with a single sign in it.

## The hyperplane Sylvester criterion

A symmetric `3 x 3` form which is strictly positive on the plane orthogonal to a
unit axis has at least two positive directions, so its determinant alone decides
definiteness: `posDef_of_planePositive_of_det_pos`, and the packaged equivalence
`posDef_iff_det_pos_of_planePositive`.  The proof is the frame congruence already
in the tree (`Gtz.frameGram_eq_one`, `Gtz.frameCongruence_entry`,
`Gtz.det_eq_framePairing_det`) followed by the tree's own Sylvester criterion
`Gtz.posDef_finThree_iff_reindexedLeadingMinors`.  No eigenvalue, no inertia
theory, no Schur complement.

## Every plane-strict pair is live, so there is no easy branch

`pairGap_det_neg_of_pairPlaneStrict` proves that a plane-strict free pair's gap
determinant is ALWAYS strictly negative: a card-two gap in rank three is negative
on any direction orthogonal to both selected atoms, and such a direction always
exists.  So the tempting split on the sign of that determinant has an empty easy
side.  This is a refutation of a plausible-looking route, proved rather than
measured, and it is why the file carries no case analysis on that sign.

## What the pair does buy: one determinant sign per completion

For a plane-strict pair, EVERY completion is decided by a single determinant sign
(`posDef_gap_iff_det_pos_of_pairPlaneStrict`), equivalently by one adjugate
reading (`posDef_gap_iff_adjugateReading_gt_of_pairPlaneStrict`).  Two consequences:

  * `exists_liveRefusingPair_of_not_planeBranchTenCandidate` -- failure of the
    branch forces the hinge pair to be live AND all four of its completions to
    have nonpositive determinant.  A necessary condition in determinants only.
  * `uThreeSixPlaneTenCandidateBranch_of_strictPairCompletionSelector` -- the whole
    branch follows from `PlaneBranchStrictPairCompletionSelector`: SOME free pair
    dominating the tight plane has a completion of strictly positive determinant.
    The pair is quantified existentially on purpose; the universal form is refuted
    by the campaign's exact numerics.
-/
import Mathlib
import Gtz.Design.FreePairPlane
import Gtz.Design.PlaneBranchNormalForm
import Gtz.Design.TightAntecedentMining
import Gtz.Ties.CriticalTieMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## The hyperplane Sylvester criterion -/

/-- **Non-vacuity guard.**  The hypothesis bundle used throughout this section is
satisfiable: the identity form with the coordinate frame meets every clause, so
none of the criteria below is vacuously true. -/
theorem exists_planePositive_witness :
    ∃ (form : Matrix (Fin 3) (Fin 3) ℝ) (pOne pTwo axis : Fin 3 → ℝ),
      formᵀ = form ∧ pOne ⬝ᵥ pOne = 1 ∧ pTwo ⬝ᵥ pTwo = 1 ∧ axis ⬝ᵥ axis = 1
        ∧ pOne ⬝ᵥ pTwo = 0 ∧ pOne ⬝ᵥ axis = 0 ∧ pTwo ⬝ᵥ axis = 0
        ∧ (∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
            0 < planar ⬝ᵥ (form *ᵥ planar))
        ∧ 0 < form.det := by
  refine ⟨1, ![1, 0, 0], ![0, 1, 0], ![0, 0, 1], Matrix.transpose_one,
    by simp [dotProduct, Fin.sum_univ_three],
    by simp [dotProduct, Fin.sum_univ_three],
    by simp [dotProduct, Fin.sum_univ_three],
    by simp [dotProduct, Fin.sum_univ_three],
    by simp [dotProduct, Fin.sum_univ_three],
    by simp [dotProduct, Fin.sum_univ_three], ?_,
    by rw [Matrix.det_one]; norm_num⟩
  intro planar _hplanarPerp hplanarNe
  rw [Matrix.one_mulVec]
  exact dotProduct_self_pos hplanarNe

/-- **The plane minor of a plane-positive form is strictly positive.**  Read in
the frame's basis of the plane, it is the determinant of the restricted form. -/
theorem planeMinor_pos_of_planePositive
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    (hplane : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ (form *ᵥ planar)) :
    0 < (pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
      - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2 := by
  have hOneNe : pOne ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hOneOne
    norm_num at hOneOne
  have hcornerPos : 0 < pOne ⬝ᵥ (form *ᵥ pOne) := hplane pOne hOneAxis hOneNe
  have hcrossSymm : pTwo ⬝ᵥ (form *ᵥ pOne) = pOne ⬝ᵥ (form *ᵥ pTwo) :=
    symmPairing_comm hsymmetric pTwo pOne
  set corner := pOne ⬝ᵥ (form *ᵥ pOne) with hcornerDef
  set cross := pOne ⬝ᵥ (form *ᵥ pTwo) with hcrossDef
  set second := pTwo ⬝ᵥ (form *ᵥ pTwo) with hsecondDef
  have hcombinationPerp : (cross • pOne + (-corner) • pTwo) ⬝ᵥ axis = 0 := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hOneAxis, hTwoAxis]
    ring
  have hcombinationNorm : (cross • pOne + (-corner) • pTwo)
      ⬝ᵥ (cross • pOne + (-corner) • pTwo) = cross ^ 2 + corner ^ 2 := by
    have hTwoOne : pTwo ⬝ᵥ pOne = 0 := by
      rw [dotProduct_comm]
      exact hOneTwo
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hOneOne, hTwoTwo, hOneTwo, hTwoOne]
    ring
  have hcombinationNe : cross • pOne + (-corner) • pTwo ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hcombinationNorm
    nlinarith [sq_nonneg cross, hcornerPos]
  have hvalue : (cross • pOne + (-corner) • pTwo)
      ⬝ᵥ (form *ᵥ (cross • pOne + (-corner) • pTwo))
      = corner * (corner * second - cross ^ 2) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hcrossSymm]
    ring
  have hpositive := hplane _ hcombinationPerp hcombinationNe
  rw [hvalue] at hpositive
  nlinarith [hcornerPos, hpositive]

/-- **A form positive on a coordinate-free plane is definite as soon as its
determinant is.**  The plane is the orthogonal complement of the unit `axis` of
an orthonormal frame; positivity there supplies the first two leading minors of
the frame congruence, and the determinant supplies the third.  No eigenvalue, no
inertia theory, no Schur complement. -/
theorem posDef_of_planePositive_of_det_pos
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    (hplane : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ (form *ᵥ planar))
    (hdet : 0 < form.det) :
    form.PosDef := by
  have hOneNe : pOne ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hOneOne
    norm_num at hOneOne
  have hcornerPos : 0 < pOne ⬝ᵥ (form *ᵥ pOne) := hplane pOne hOneAxis hOneNe
  have hblockPos := planeMinor_pos_of_planePositive hsymmetric hOneOne hTwoTwo
    hOneTwo hOneAxis hTwoAxis hplane
  have hgram := frameGram_eq_one hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis hTwoAxis
  have hdetProduct : (Matrix.of ![pOne, pTwo, axis] : Matrix (Fin 3) (Fin 3) ℝ).det
      * ((Matrix.of ![pOne, pTwo, axis] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ).det = 1 := by
    rw [← Matrix.det_mul, hgram, Matrix.det_one]
  have hframeDetNe :
      ((Matrix.of ![pOne, pTwo, axis] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ).det ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hdetProduct
    norm_num at hdetProduct
  have hframeUnit :
      IsUnit (((Matrix.of ![pOne, pTwo, axis] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ).det) :=
    isUnit_iff_ne_zero.mpr hframeDetNe
  have hcongruence := posDef_congr_right (X := form)
    (P := (Matrix.of ![pOne, pTwo, axis] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) hsymmetric
    hframeUnit
  rw [Matrix.transpose_transpose] at hcongruence
  rw [hcongruence]
  have hcongruatedSymmetric :
      (Matrix.of ![pOne, pTwo, axis] * form
          * (Matrix.of ![pOne, pTwo, axis] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ)ᵀ
        = Matrix.of ![pOne, pTwo, axis] * form
          * (Matrix.of ![pOne, pTwo, axis] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsymmetric,
      Matrix.mul_assoc]
  rw [posDef_finThree_iff_reindexedLeadingMinors _ hcongruatedSymmetric
    (Equiv.refl (Fin 3))]
  simp only [Equiv.refl_apply, frameCongruence_entry, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  refine ⟨hcornerPos, hblockPos, ?_⟩
  have hdetFrame := hdet
  rw [det_eq_framePairing_det hsymmetric hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis
    hTwoAxis] at hdetFrame
  nlinarith [hdetFrame]

/-- **On the plane, definiteness is one determinant sign.** -/
theorem posDef_iff_det_pos_of_planePositive
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    (hplane : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ (form *ᵥ planar)) :
    form.PosDef ↔ 0 < form.det :=
  ⟨fun hposDef => hposDef.det_pos, fun hdet =>
    posDef_of_planePositive_of_det_pos hsymmetric hOneOne hTwoTwo hAxisAxis hOneTwo
      hOneAxis hTwoAxis hplane hdet⟩

/-- **A singular plane-positive form is semidefinite with a one-dimensional
kernel.**  Every vector splits, along the kernel direction, into a planar part
carrying the whole quadratic value; so the value is strictly positive off the
kernel line and zero on it.  The plane hypothesis is what supplies the direction
complementary to the kernel, and the whole argument is one explicit
decomposition -- no rank counting, no dimension theory. -/
theorem quadForm_split_of_planePositive_of_kernelVector
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    {axis : Fin 3 → ℝ}
    (hplane : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ (form *ᵥ planar))
    {kernelVector : Fin 3 → ℝ} (hkernelNe : kernelVector ≠ 0)
    (hkernel : form *ᵥ kernelVector = 0) :
    ∀ vec : Fin 3 → ℝ,
      0 < vec ⬝ᵥ (form *ᵥ vec)
        ∨ (vec ⬝ᵥ (form *ᵥ vec) = 0 ∧ ∃ ratio : ℝ, vec = ratio • kernelVector) := by
  have hkernelAxis : kernelVector ⬝ᵥ axis ≠ 0 := by
    intro hzero
    have hpositive := hplane kernelVector hzero hkernelNe
    rw [hkernel, dotProduct_zero] at hpositive
    exact lt_irrefl 0 hpositive
  · intro vec
    set ratio := (vec ⬝ᵥ axis) / (kernelVector ⬝ᵥ axis) with hratioDef
    set residual := vec - ratio • kernelVector with hresidualDef
    have hresidualPerp : residual ⬝ᵥ axis = 0 := by
      rw [hresidualDef, sub_dotProduct, smul_dotProduct, smul_eq_mul, hratioDef]
      field_simp
      ring
    have hresidualImage : form *ᵥ residual = form *ᵥ vec := by
      rw [hresidualDef, Matrix.mulVec_sub, Matrix.mulVec_smul, hkernel, smul_zero,
        sub_zero]
    have hkernelPairing : kernelVector ⬝ᵥ (form *ᵥ vec) = 0 := by
      rw [symmPairing_comm hsymmetric kernelVector vec, hkernel, dotProduct_zero]
    have hresidualValue : residual ⬝ᵥ (form *ᵥ residual) = vec ⬝ᵥ (form *ᵥ vec) := by
      rw [hresidualImage, hresidualDef, sub_dotProduct, smul_dotProduct, smul_eq_mul,
        hkernelPairing]
      ring
    rcases eq_or_ne residual 0 with hzero | hnonzero
    · exact Or.inr ⟨by rw [← hresidualValue, hzero, zero_dotProduct],
        ratio, eq_of_sub_eq_zero (hresidualDef.symm.trans hzero)⟩
    · left
      rw [← hresidualValue]
      exact hplane residual hresidualPerp hnonzero

/-- Any rank-one bump not orthogonal to the kernel of a singular plane-positive
form makes it definite. -/
theorem posDef_add_atomMatrix_of_planePositive_of_kernelVector
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    {axis : Fin 3 → ℝ}
    (hplane : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ (form *ᵥ planar))
    {kernelVector : Fin 3 → ℝ} (hkernelNe : kernelVector ≠ 0)
    (hkernel : form *ᵥ kernelVector = 0)
    {probe : Fin 3 → ℝ} (hprobe : probe ⬝ᵥ kernelVector ≠ 0) :
    (form + atomMatrix probe).PosDef := by
  have hsplit := quadForm_split_of_planePositive_of_kernelVector hsymmetric hplane
    hkernelNe hkernel
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vec hvecNe => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_add, hsymmetric, atomMatrix, Matrix.transpose_vecMulVec]
  · rw [star_trivial]
    have hexpand : vec ⬝ᵥ ((form + atomMatrix probe) *ᵥ vec)
        = vec ⬝ᵥ (form *ᵥ vec) + (probe ⬝ᵥ vec) ^ 2 := by
      rw [Matrix.add_mulVec, dotProduct_add, dotProduct_atomMatrix_mulVec_self]
    rw [hexpand]
    rcases hsplit vec with hpositive | ⟨hzero, ratio, hvec⟩
    · nlinarith [sq_nonneg (probe ⬝ᵥ vec)]
    · rw [hzero, zero_add]
      have hratioNe : ratio ≠ 0 := by
        intro hratioZero
        rw [hratioZero, zero_smul] at hvec
        exact hvecNe hvec
      have hprobeValue : probe ⬝ᵥ vec = ratio * (probe ⬝ᵥ kernelVector) := by
        rw [hvec, dotProduct_smul, smul_eq_mul]
      rw [hprobeValue]
      exact lt_of_le_of_ne (sq_nonneg _)
        (Ne.symm (pow_ne_zero 2 (mul_ne_zero hratioNe hprobe)))

/-- **One negative direction forces a negative determinant.**  For a
plane-positive form the determinant cannot be positive (that would make the form
definite) and cannot vanish (that would make it semidefinite), so a single
strictly negative direction pins the sign. -/
theorem det_neg_of_planePositive_of_negativeDirection
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    (hplane : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ (form *ᵥ planar))
    {witness : Fin 3 → ℝ} (hwitness : witness ⬝ᵥ (form *ᵥ witness) < 0) :
    form.det < 0 := by
  have hwitnessNe : witness ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct] at hwitness
    exact lt_irrefl 0 hwitness
  rcases lt_trichotomy form.det 0 with hnegative | hvanishing | hpositive
  · exact hnegative
  · exfalso
    obtain ⟨kernelVector, hkernelNe, hkernel⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hvanishing
    rcases quadForm_split_of_planePositive_of_kernelVector hsymmetric hplane hkernelNe
      hkernel witness with hpositiveValue | ⟨hzeroValue, _⟩
    · linarith
    · linarith
  · exfalso
    have hposDef := posDef_of_planePositive_of_det_pos hsymmetric hOneOne hTwoTwo
      hAxisAxis hOneTwo hOneAxis hTwoAxis hplane hpositive
    have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hwitnessNe
    rw [star_trivial] at hvalue
    linarith

/-! ## The hinge pair, read as a quadratic form -/

/-- The pair gap's quadratic form is the two atom readings minus the square norm. -/
theorem quadForm_pairGap_eq_readings_sub_normSq
    {size : ℕ} (design : WeightedDesign size 3) {strongLabel otherLabel : Fin size}
    (hlabelNe : strongLabel ≠ otherLabel) (planar : Fin 3 → ℝ) :
    planar ⬝ᵥ ((subsetSum design ({strongLabel, otherLabel} : Finset (Fin size)) - 1)
        *ᵥ planar)
      = (design.atom strongLabel ⬝ᵥ planar) ^ 2
        + (design.atom otherLabel ⬝ᵥ planar) ^ 2 - planar ⬝ᵥ planar := by
  rw [Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum, Matrix.one_mulVec,
    Finset.sum_pair hlabelNe]
  simp only [momentCoord]

/-- Plane-strictness of a free pair, restated as plane-positivity of its gap. -/
theorem pairGap_planePositive_of_pairPlaneStrict
    {size : ℕ} (design : WeightedDesign size 3) {axis : Fin 3 → ℝ}
    {strongLabel otherLabel : Fin size} (hlabelNe : strongLabel ≠ otherLabel)
    (hpairStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2) :
    ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ ((subsetSum design
        ({strongLabel, otherLabel} : Finset (Fin size)) - 1) *ᵥ planar) := by
  intro planar hplanarPerp hplanarNe
  rw [quadForm_pairGap_eq_readings_sub_normSq design hlabelNe planar]
  linarith [hpairStrict planar hplanarPerp hplanarNe]

/-- **THE HINGE PAIR IS ALWAYS LIVE, so the nonnegative-determinant branch below
is EMPTY.**  A card-two gap in rank three is negative on every direction
orthogonal to both selected atoms, and such a direction always exists; with
plane-positivity that pins the determinant strictly negative.  Consequently
`exists_posDef_cardThree_of_pairPlaneStrict_of_det_nonneg` and
`planeBranchTenCandidate_of_pairPlaneStrict_of_det_nonneg` fire on nothing, and
the live case is the whole plane branch. -/
theorem pairGap_det_neg_of_pairPlaneStrict
    (design : WeightedDesign 6 3)
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    {strongLabel otherLabel : Fin 6} (hlabelNe : strongLabel ≠ otherLabel)
    (hpairStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2) :
    (subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6)) - 1).det < 0 := by
  have hrowVanishes :
      (Matrix.of ![design.atom strongLabel, design.atom otherLabel,
        (0 : Fin 3 → ℝ)] : Matrix (Fin 3) (Fin 3) ℝ).det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero 2 ?_
    intro coordinate
    simp
  obtain ⟨witness, hwitnessNe, hwitnessKernel⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hrowVanishes
  have hstrongReading : design.atom strongLabel ⬝ᵥ witness = 0 := by
    have hcomponent := congrFun hwitnessKernel 0
    simpa [Matrix.mulVec] using hcomponent
  have hotherReading : design.atom otherLabel ⬝ᵥ witness = 0 := by
    have hcomponent := congrFun hwitnessKernel 1
    simpa [Matrix.mulVec] using hcomponent
  have hvalue := quadForm_pairGap_eq_readings_sub_normSq design hlabelNe witness
  rw [hstrongReading, hotherReading] at hvalue
  have hnormPos : 0 < witness ⬝ᵥ witness := dotProduct_self_pos hwitnessNe
  refine det_neg_of_planePositive_of_negativeDirection
    (transpose_subsetSum_sub_one design _) hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis
    hTwoAxis (pairGap_planePositive_of_pairPlaneStrict design hlabelNe hpairStrict)
    (witness := witness) ?_
  rw [hvalue]
  nlinarith

/-- Adjoining one atom to a selected set adds its rank-one reading to the gap's
quadratic form. -/
theorem quadForm_insertGap_eq_reading_add
    {size rank : ℕ} (design : WeightedDesign size rank) {thirdLabel : Fin size}
    {selected : Finset (Fin size)} (hthirdNotMem : thirdLabel ∉ selected)
    (probe : Fin rank → ℝ) :
    probe ⬝ᵥ ((subsetSum design (insert thirdLabel selected) - 1) *ᵥ probe)
      = (design.atom thirdLabel ⬝ᵥ probe) ^ 2
        + probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) := by
  have hsum : subsetSum design (insert thirdLabel selected)
      = atomMatrix (design.atom thirdLabel) + subsetSum design selected := by
    rw [subsetSum, subsetSum, Finset.sum_insert hthirdNotMem]
  rw [hsum, show atomMatrix (design.atom thirdLabel) + subsetSum design selected - 1
      = atomMatrix (design.atom thirdLabel) + (subsetSum design selected - 1) from by
        abel, Matrix.add_mulVec, dotProduct_add, dotProduct_atomMatrix_mulVec_self]

/-- Adjoining one atom to a selected set adds its rank-one atom to the gap. -/
theorem insertGap_eq_gap_add_atomMatrix
    {size rank : ℕ} (design : WeightedDesign size rank) {thirdLabel : Fin size}
    {selected : Finset (Fin size)} (hthirdNotMem : thirdLabel ∉ selected) :
    subsetSum design (insert thirdLabel selected) - 1
      = (subsetSum design selected - 1) + atomMatrix (design.atom thirdLabel) := by
  rw [subsetSum, subsetSum, Finset.sum_insert hthirdNotMem]
  abel

/-- **The rank-one determinant update at size three.**  Adjoining an atom raises
a determinant by exactly that atom's adjugate reading.  Purely an expansion of a
`3 x 3` determinant, so it holds for every form. -/
theorem det_add_atomMatrix_fin_three (form : Matrix (Fin 3) (Fin 3) ℝ)
    (vec : Fin 3 → ℝ) :
    (form + atomMatrix vec).det = form.det + vec ⬝ᵥ (form.adjugate *ᵥ vec) := by
  simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, atomMatrix,
    Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **The adjugate reading along the axis is the plane minor.**  Bumping a form
by the axis atom raises its determinant by the adjugate reading, and in the frame
that bump only touches the axis corner, so it raises the determinant by the plane
minor instead.  Comparing the two computations identifies them. -/
theorem adjugateReading_axis_eq_planeMinor
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0) :
    axis ⬝ᵥ (form.adjugate *ᵥ axis)
      = (pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
        - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2 := by
  have haxisOne : axis ⬝ᵥ pOne = 0 := by
    rw [dotProduct_comm]
    exact hOneAxis
  have haxisTwo : axis ⬝ᵥ pTwo = 0 := by
    rw [dotProduct_comm]
    exact hTwoAxis
  have hbumpSymmetric : (form + atomMatrix axis)ᵀ = form + atomMatrix axis := by
    rw [Matrix.transpose_add, hsymmetric, atomMatrix, Matrix.transpose_vecMulVec]
  have hbumpPairing : ∀ leftVec rightVec : Fin 3 → ℝ,
      leftVec ⬝ᵥ ((form + atomMatrix axis) *ᵥ rightVec)
        = leftVec ⬝ᵥ (form *ᵥ rightVec) + (axis ⬝ᵥ leftVec) * (axis ⬝ᵥ rightVec) := by
    intro leftVec rightVec
    rw [Matrix.add_mulVec, dotProduct_add, atomMatrix_mulVec_eq_smul, dotProduct_smul,
      smul_eq_mul, dotProduct_comm leftVec axis]
    ring
  have hbumpDet := det_eq_framePairing_det hbumpSymmetric hOneOne hTwoTwo hAxisAxis
    hOneTwo hOneAxis hTwoAxis
  rw [det_add_atomMatrix_fin_three] at hbumpDet
  simp only [hbumpPairing, haxisOne, haxisTwo, hAxisAxis] at hbumpDet
  have hformDet := det_eq_framePairing_det hsymmetric hOneOne hTwoTwo hAxisAxis
    hOneTwo hOneAxis hTwoAxis
  linear_combination hbumpDet - hformDet

/-- **The completing direction always exists.**  For a plane-positive form the
adjugate is strictly positive along the axis, so the plane branch's residual is
never the absence of a good direction: it is only whether one of the design's own
atoms reaches that direction. -/
theorem adjugateReading_axis_pos_of_planePositive
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    (hplane : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ (form *ᵥ planar)) :
    0 < axis ⬝ᵥ (form.adjugate *ᵥ axis) := by
  rw [adjugateReading_axis_eq_planeMinor hsymmetric hOneOne hTwoTwo hAxisAxis hOneTwo
    hOneAxis hTwoAxis]
  exact planeMinor_pos_of_planePositive hsymmetric hOneOne hTwoTwo hOneTwo hOneAxis
    hTwoAxis hplane

/-- Under domination, no nonzero vector is orthogonal to every selected atom:
the gap's quadratic form would be the negative square norm there. -/
theorem exists_mem_dotProduct_ne_zero_of_dominates
    {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hdominates : Dominates design selected)
    {vec : Fin rank → ℝ} (hvecNe : vec ≠ 0) :
    ∃ label ∈ selected, design.atom label ⬝ᵥ vec ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hreadings : ∑ atomIndex ∈ selected, momentCoord design atomIndex vec = 0 :=
    Finset.sum_eq_zero fun atomIndex hmember => by
      simp only [momentCoord, hnone atomIndex hmember]
      ring
  have hvalue : vec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ vec) = -(vec ⬝ᵥ vec) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum, Matrix.one_mulVec,
      hreadings]
    ring
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 vec
  rw [star_trivial, hvalue] at hnonneg
  have hnormPos : 0 < vec ⬝ᵥ vec := dotProduct_self_pos hvecNe
  linarith

/-- A base label and a free label are never equal. -/
theorem baseLabel_ne_freeLabel {baseLabel freeLabel : Fin 6}
    (hbase : baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hfree : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    baseLabel ≠ freeLabel := by
  fin_cases hbase <;> fin_cases hfree <;> decide

/-! ## The hinge pair decides its four completions by one determinant -/

/-- **Every completion of the hinge pair is decided by its determinant alone.**
The pair gap is positive on the tight plane, hence so is the completed gap, and
the hyperplane criterion applies. -/
theorem posDef_gap_iff_det_pos_of_pairPlaneStrict
    (design : WeightedDesign 6 3)
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    {strongLabel otherLabel thirdLabel : Fin 6}
    (hlabelNe : strongLabel ≠ otherLabel)
    (hthirdNotMem : thirdLabel ∉ ({strongLabel, otherLabel} : Finset (Fin 6)))
    (hpairStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2) :
    (subsetSum design ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6))
        - 1).PosDef
      ↔ 0 < (subsetSum design ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6))
        - 1).det := by
  refine posDef_iff_det_pos_of_planePositive
    (transpose_subsetSum_sub_one design _) hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis
    hTwoAxis ?_
  intro planar hplanarPerp hplanarNe
  have hpair := hpairStrict planar hplanarPerp hplanarNe
  have hsplit := quadForm_insertGap_eq_reading_add design hthirdNotMem planar
  have hpairValue := quadForm_pairGap_eq_readings_sub_normSq design hlabelNe planar
  have hshape : ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6))
      = insert thirdLabel ({strongLabel, otherLabel} : Finset (Fin 6)) := rfl
  rw [hshape, hsplit, hpairValue]
  nlinarith [sq_nonneg (design.atom thirdLabel ⬝ᵥ planar)]

/-- **The completion test, fully explicit.**  A completion of the hinge pair is a
strict dominator exactly when the completing atom's adjugate reading exceeds the
pair gap's determinant deficit.  On the live side the deficit is positive, so this
is the whole content of the plane branch. -/
theorem posDef_gap_iff_adjugateReading_gt_of_pairPlaneStrict
    (design : WeightedDesign 6 3)
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    {strongLabel otherLabel thirdLabel : Fin 6}
    (hlabelNe : strongLabel ≠ otherLabel)
    (hthirdNotMem : thirdLabel ∉ ({strongLabel, otherLabel} : Finset (Fin 6)))
    (hpairStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2) :
    (subsetSum design ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6))
        - 1).PosDef
      ↔ -((subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6)) - 1).det)
        < design.atom thirdLabel
          ⬝ᵥ (((subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6))
              - 1).adjugate) *ᵥ design.atom thirdLabel) := by
  rw [posDef_gap_iff_det_pos_of_pairPlaneStrict design hOneOne hTwoTwo hAxisAxis
      hOneTwo hOneAxis hTwoAxis hlabelNe hthirdNotMem hpairStrict,
    show ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6))
      = insert thirdLabel ({strongLabel, otherLabel} : Finset (Fin 6)) from rfl,
    insertGap_eq_gap_add_atomMatrix design hthirdNotMem,
    det_add_atomMatrix_fin_three]
  constructor <;> intro hsign <;> linarith

/-- **Failure of the plane branch forces a live hinge pair whose every completion
has nonpositive determinant.**  This is the exact residual, in determinants only:
no matrix definiteness survives on either side.  The hinge pair itself is live
by `pairGap_det_neg_of_pairPlaneStrict`, and each of its four completions is
refused because on the plane a positive determinant already means strict
domination. -/
theorem exists_liveRefusingPair_of_not_planeBranchTenCandidate
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6)))
    (hfail : ¬ PlaneBranchTenCandidate design) :
    ∃ (pOne pTwo axis : Fin 3 → ℝ) (strongLabel otherLabel : Fin 6),
      pOne ⬝ᵥ pOne = 1
        ∧ pTwo ⬝ᵥ pTwo = 1
        ∧ axis ⬝ᵥ axis = 1
        ∧ pOne ⬝ᵥ pTwo = 0
        ∧ pOne ⬝ᵥ axis = 0
        ∧ pTwo ⬝ᵥ axis = 0
        ∧ strongLabel ≠ otherLabel
        ∧ strongLabel ∈ ({3, 4, 5} : Finset (Fin 6))
        ∧ otherLabel ∈ ({3, 4, 5} : Finset (Fin 6))
        ∧ (∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
            planar ⬝ᵥ planar
              < (design.atom strongLabel ⬝ᵥ planar) ^ 2
                + (design.atom otherLabel ⬝ᵥ planar) ^ 2)
        ∧ (subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6)) - 1).det < 0
        ∧ ∀ thirdLabel : Fin 6,
            thirdLabel ∉ ({strongLabel, otherLabel} : Finset (Fin 6)) →
              (subsetSum design
                ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6)) - 1).det ≤ 0 := by
  obtain ⟨pOne, pTwo, axis, strongLabel, otherLabel, hOneOne, hTwoTwo, hAxisAxis,
    hOneTwo, hOneAxis, hTwoAxis, hlabelNe, hstrongFree, hotherFree, hpairStrict⟩ :=
    exists_free_pairPlaneStrict_of_planeBranch design hdominates hfree
  have hlive := pairGap_det_neg_of_pairPlaneStrict design hOneOne hTwoTwo hAxisAxis
    hOneTwo hOneAxis hTwoAxis hlabelNe hpairStrict
  refine ⟨pOne, pTwo, axis, strongLabel, otherLabel, hOneOne, hTwoTwo, hAxisAxis,
    hOneTwo, hOneAxis, hTwoAxis, hlabelNe, hstrongFree, hotherFree, hpairStrict,
    hlive, ?_⟩
  intro thirdLabel hthirdNotMem
  by_contra hdetPos
  push Not at hdetPos
  have hposDef := (posDef_gap_iff_det_pos_of_pairPlaneStrict design hOneOne hTwoTwo
    hAxisAxis hOneTwo hOneAxis hTwoAxis hlabelNe hthirdNotMem hpairStrict).mpr hdetPos
  have hcard : ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6)).card = 3 := by
    rw [show ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6))
      = insert thirdLabel ({strongLabel, otherLabel} : Finset (Fin 6)) from rfl,
      Finset.card_insert_of_notMem hthirdNotMem, Finset.card_pair hlabelNe]
  exact hfail ((exists_posDef_cardThree_iff_planeBranchTenCandidate design hdominates
    hfree).mp ⟨_, hcard, hposDef⟩)

/-! ## The residual: one determinant sign, existentially over the free pairs -/

/-- **The residual side condition of the plane branch, in determinants only.**
Some free pair strictly dominating the whole tight plane has a completion whose
gap determinant is strictly positive.  No matrix definiteness occurs in the
statement: by `posDef_gap_iff_det_pos_of_pairPlaneStrict` one polynomial sign
decides each completion.

The pair is quantified EXISTENTIALLY on purpose.  The universal reading -- every
plane-strict free pair completes -- is refuted by the campaign's exact rational
censuses, which exhibit plane-strict free pairs all four of whose completions
fail; so any proof must SELECT among the free pairs rather than take the one the
hinge happens to hand over. -/
def PlaneBranchStrictPairCompletionSelector : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6)) →
    ∃ (pOne pTwo axis : Fin 3 → ℝ) (strongLabel otherLabel thirdLabel : Fin 6),
      pOne ⬝ᵥ pOne = 1
        ∧ pTwo ⬝ᵥ pTwo = 1
        ∧ axis ⬝ᵥ axis = 1
        ∧ pOne ⬝ᵥ pTwo = 0
        ∧ pOne ⬝ᵥ axis = 0
        ∧ pTwo ⬝ᵥ axis = 0
        ∧ strongLabel ≠ otherLabel
        ∧ thirdLabel ∉ ({strongLabel, otherLabel} : Finset (Fin 6))
        ∧ (∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
            planar ⬝ᵥ planar
              < (design.atom strongLabel ⬝ᵥ planar) ^ 2
                + (design.atom otherLabel ⬝ᵥ planar) ^ 2)
        ∧ 0 < (subsetSum design
            ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6)) - 1).det

/-- **THE PLANE BRANCH FROM ONE DETERMINANT SIGN.**  The ten-candidate branch
follows from the selector: the hyperplane criterion upgrades the selector's single
determinant sign to strict domination, and the landed card-three equivalence turns
that into the branch.  The hinge is not used here -- the selector already carries
its own plane-strict pair. -/
theorem uThreeSixPlaneTenCandidateBranch_of_strictPairCompletionSelector
    (hselector : PlaneBranchStrictPairCompletionSelector) :
    UThreeSixPlaneTenCandidateBranch := by
  intro design hlineFree hoffConic hdominates hfree
  obtain ⟨pOne, pTwo, axis, strongLabel, otherLabel, thirdLabel, hOneOne, hTwoTwo,
    hAxisAxis, hOneTwo, hOneAxis, hTwoAxis, hlabelNe, hthirdNotMem, hpairStrict,
    hdetPos⟩ := hselector design hlineFree hoffConic hdominates hfree
  have hposDef := (posDef_gap_iff_det_pos_of_pairPlaneStrict design hOneOne hTwoTwo
    hAxisAxis hOneTwo hOneAxis hTwoAxis hlabelNe hthirdNotMem hpairStrict).mpr hdetPos
  have hcard : ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6)).card = 3 := by
    rw [show ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6))
      = insert thirdLabel ({strongLabel, otherLabel} : Finset (Fin 6)) from rfl,
      Finset.card_insert_of_notMem hthirdNotMem, Finset.card_pair hlabelNe]
  exact (exists_posDef_cardThree_iff_planeBranchTenCandidate design hdominates
    hfree).mp ⟨_, hcard, hposDef⟩

/-! ## An orthonormal frame from a bare unit axis

`posDef_of_planePositive_of_det_pos` asks the caller for a whole orthonormal
frame.  The frame is not extra data: a unit axis of `R^3` determines one, so the
criterion holds with the axis alone.  The construction is the cross product,
twice, seeded by whichever coordinate vector is not parallel to the axis --
and the three squared cross norms `1 - axis i ^ 2` sum to `2`, so such a
coordinate always exists. -/

/-- **Every unit axis of `R^3` completes to an orthonormal frame.** -/
theorem exists_orthonormalFrame_of_unitAxis {axis : Fin 3 → ℝ}
    (hAxisAxis : axis ⬝ᵥ axis = 1) :
    ∃ pOne pTwo : Fin 3 → ℝ,
      pOne ⬝ᵥ pOne = 1 ∧ pTwo ⬝ᵥ pTwo = 1 ∧ pOne ⬝ᵥ pTwo = 0
        ∧ pOne ⬝ᵥ axis = 0 ∧ pTwo ⬝ᵥ axis = 0 := by
  have hcoordinateSum : axis 0 * axis 0 + axis 1 * axis 1 + axis 2 * axis 2 = 1 := by
    have hexpanded := hAxisAxis
    simp only [dotProduct, Fin.sum_univ_three] at hexpanded
    linarith
  have hexistsShort : ∃ coordinate : Fin 3, axis coordinate ^ 2 < 1 := by
    by_contra hnone
    push Not at hnone
    nlinarith [hnone 0, hnone 1, hnone 2, hcoordinateSum]
  obtain ⟨coordinate, hshort⟩ := hexistsShort
  have hseedNorm : (Pi.single coordinate (1 : ℝ)) ⬝ᵥ (Pi.single coordinate (1 : ℝ)) = 1 := by
    rw [single_dotProduct, Pi.single_eq_same, mul_one]
  have haxisSeed : axis ⬝ᵥ (Pi.single coordinate (1 : ℝ)) = axis coordinate := by
    rw [dotProduct_single, mul_one]
  have hrawNorm : (crossProduct axis (Pi.single coordinate (1 : ℝ)))
      ⬝ᵥ (crossProduct axis (Pi.single coordinate (1 : ℝ))) = 1 - axis coordinate ^ 2 := by
    rw [planarCross_self_dot, hAxisAxis, hseedNorm, haxisSeed]
    ring
  have hrawLeverage : 0 < leverageOf (crossProduct axis (Pi.single coordinate (1 : ℝ))) := by
    rw [leverageOf_eq_dotProduct_self, hrawNorm]
    linarith
  have hOneOne :
      unitDirection (crossProduct axis (Pi.single coordinate (1 : ℝ)))
        ⬝ᵥ unitDirection (crossProduct axis (Pi.single coordinate (1 : ℝ))) = 1 :=
    unitDirection_dotProduct_self hrawLeverage
  have hOneAxis :
      unitDirection (crossProduct axis (Pi.single coordinate (1 : ℝ))) ⬝ᵥ axis = 0 := by
    have hrawAxis : (crossProduct axis (Pi.single coordinate (1 : ℝ))) ⬝ᵥ axis = 0 := by
      rw [dotProduct_comm]
      exact planarCross_probe_dot axis (Pi.single coordinate (1 : ℝ))
    rw [unitDirection, smul_dotProduct, hrawAxis, smul_eq_mul, mul_zero]
  have hAxisOne :
      axis ⬝ᵥ unitDirection (crossProduct axis (Pi.single coordinate (1 : ℝ))) = 0 := by
    rw [dotProduct_comm]
    exact hOneAxis
  refine ⟨unitDirection (crossProduct axis (Pi.single coordinate (1 : ℝ))),
    crossProduct axis (unitDirection (crossProduct axis (Pi.single coordinate (1 : ℝ)))),
    hOneOne, ?_, ?_, hOneAxis, ?_⟩
  · rw [planarCross_self_dot, hAxisAxis, hOneOne, hAxisOne]
    ring
  · exact planarCross_seed_dot axis
      (unitDirection (crossProduct axis (Pi.single coordinate (1 : ℝ))))
  · rw [dotProduct_comm]
    exact planarCross_probe_dot axis
      (unitDirection (crossProduct axis (Pi.single coordinate (1 : ℝ))))

/-- **The hyperplane Sylvester criterion, from the axis alone.**  No frame has
to be supplied: a symmetric `3 x 3` form strictly positive on the orthogonal
complement of a unit axis is definite exactly when its determinant is. -/
theorem posDef_of_planePositive_of_det_pos_of_unitAxis
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    {axis : Fin 3 → ℝ} (hAxisAxis : axis ⬝ᵥ axis = 1)
    (hplane : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ (form *ᵥ planar))
    (hdet : 0 < form.det) :
    form.PosDef := by
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormalFrame_of_unitAxis hAxisAxis
  exact posDef_of_planePositive_of_det_pos hsymmetric hOneOne hTwoTwo hAxisAxis hOneTwo
    hOneAxis hTwoAxis hplane hdet

/-- The packaged equivalence with only a unit axis as data. -/
theorem posDef_iff_det_pos_of_planePositive_of_unitAxis
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    {axis : Fin 3 → ℝ} (hAxisAxis : axis ⬝ᵥ axis = 1)
    (hplane : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ (form *ᵥ planar)) :
    form.PosDef ↔ 0 < form.det :=
  ⟨fun hposDef => hposDef.det_pos, fun hdet =>
    posDef_of_planePositive_of_det_pos_of_unitAxis hsymmetric hAxisAxis hplane hdet⟩

/-! ## The tight plane, and the free triple's strict over-reading on it

The plane branch's tight space is a plane, so the whole orthogonal complement of
the frame axis is tight -- `isTightDirectionOf_add_smul` plus the frame
resolution.  At a tight direction the landed
`Gtz.dominatorComplement_strictly_overcovers_tightDirection` says the atoms
outside the dominator strictly over-read it.  For `U(3,6)` those atoms are
exactly the free triple, so the FREE TRIPLE GAP IS STRICTLY POSITIVE ON THE
WHOLE TIGHT PLANE, unconditionally.  With the hyperplane criterion above, the
complement candidate is therefore decided by a single determinant sign. -/

/-- Under domination, every direction orthogonal to the axis of an orthonormal
frame whose other two members are tight is itself tight. -/
theorem isTightDirectionOf_of_dotProduct_frameAxis_eq_zero
    {size : ℕ} (design : WeightedDesign size 3) (selected : Finset (Fin size))
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    (hdominates : Dominates design selected)
    (hOneTight : IsTightDirectionOf design selected pOne)
    (hTwoTight : IsTightDirectionOf design selected pTwo)
    {planar : Fin 3 → ℝ} (hplanarPerp : planar ⬝ᵥ axis = 0) :
    IsTightDirectionOf design selected planar := by
  have hexpand := orthonormalFrame_expansion hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis
    hTwoAxis planar
  rw [hplanarPerp, zero_smul, add_zero] at hexpand
  have hcombination := isTightDirectionOf_add_smul design selected hdominates hOneTight
    hTwoTight (planar ⬝ᵥ pOne) (planar ⬝ᵥ pTwo)
  rwa [← hexpand] at hcombination

/-- **The free triple strictly over-reads every tight direction of the base
triple.**  A `U(3,6)` reading of the landed general theorem
`Gtz.dominatorComplement_strictly_overcovers_tightDirection`: the complement of
`{0,1,2}` is `{3,4,5}`. -/
theorem freeTripleReading_gt_normSq_of_isTightDirection
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    tightDir ⬝ᵥ tightDir
      < (design.atom 3 ⬝ᵥ tightDir) ^ 2 + (design.atom 4 ⬝ᵥ tightDir) ^ 2
        + (design.atom 5 ⬝ᵥ tightDir) ^ 2 := by
  have hover := dominatorComplement_strictly_overcovers_tightDirection design
    ({0, 1, 2} : Finset (Fin 6)) tightDir (by decide) htightNe htight
  rw [show (({0, 1, 2} : Finset (Fin 6)))ᶜ = ({3, 4, 5} : Finset (Fin 6)) from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hover
  linarith

/-- **The free-triple gap is strictly positive at every nonzero tight
direction.**  This is the complement candidate's half of plane positivity, and
it needs no line-freeness, no off-conicity and no domination. -/
theorem freeTripleGap_quadForm_pos_of_isTightDirection
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    0 < tightDir ⬝ᵥ ((subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1) *ᵥ tightDir) := by
  have hreading := freeTripleReading_gt_normSq_of_isTightDirection design htightNe htight
  have hform : tightDir ⬝ᵥ ((subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1) *ᵥ tightDir)
      = (design.atom 3 ⬝ᵥ tightDir) ^ 2 + (design.atom 4 ⬝ᵥ tightDir) ^ 2
        + (design.atom 5 ⬝ᵥ tightDir) ^ 2 - tightDir ⬝ᵥ tightDir := by
    rw [Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum, quadForm_one,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [momentCoord]
    ring
  rw [hform]
  linarith

/-! ## The complement candidate is one determinant sign, and the easy side closes -/

/-- **THE FREE-TRIPLE GAP IS PLANE POSITIVE ON THE PLANE BRANCH.**  The tight
space is the orthogonal complement of the frame axis, and the free triple
strictly over-reads every direction of it. -/
theorem exists_unitAxis_freeTripleGap_planePositive_of_planeBranch
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ axis : Fin 3 → ℝ, axis ⬝ᵥ axis = 1
      ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
          0 < planar ⬝ᵥ ((subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1) *ᵥ planar) := by
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneTight, hTwoTight⟩ :=
    exists_orthonormal_tightPair_of_hasFreeTightDirection design hdominates hfree
  have hAxisAxis : crossProduct pOne pTwo ⬝ᵥ crossProduct pOne pTwo = 1 := by
    rw [planarCross_self_dot, hOneOne, hTwoTwo, hOneTwo]
    ring
  have hOneAxis : pOne ⬝ᵥ crossProduct pOne pTwo = 0 := planarCross_probe_dot pOne pTwo
  have hTwoAxis : pTwo ⬝ᵥ crossProduct pOne pTwo = 0 := planarCross_seed_dot pOne pTwo
  refine ⟨crossProduct pOne pTwo, hAxisAxis, fun planar hplanarPerp hplanarNe => ?_⟩
  have htight := isTightDirectionOf_of_dotProduct_frameAxis_eq_zero design
    ({0, 1, 2} : Finset (Fin 6)) hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis hTwoAxis
    hdominates hOneTight hTwoTight hplanarPerp
  exact freeTripleGap_quadForm_pos_of_isTightDirection design hplanarNe htight

/-- **The complement candidate is decided by ONE determinant sign, with no
selection and no hinge pair.**  Contrast
`posDef_gap_iff_det_pos_of_pairPlaneStrict`, which first has to be handed a
plane-strict pair; here plane positivity is a theorem. -/
theorem posDef_freeTripleGap_iff_det_pos_of_planeBranch
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef
      ↔ 0 < (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).det := by
  obtain ⟨axis, hAxisAxis, hplane⟩ :=
    exists_unitAxis_freeTripleGap_planePositive_of_planeBranch design hdominates hfree
  exact posDef_iff_det_pos_of_planePositive_of_unitAxis
    (transpose_subsetSum_sub_one design _) hAxisAxis hplane

/-- **THE EASY SUB-BRANCH IS CLOSED.**  Whenever the free-triple gap has positive
determinant the ten-candidate disjunction holds, with no further hypothesis.
The sign is an explicit polynomial in the original atoms -- no normal form, no
transport, no selection among the free pairs. -/
theorem planeBranchTenCandidate_of_freeTripleGap_det_pos
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6)))
    (hdet : 0 < (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).det) :
    PlaneBranchTenCandidate design := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))))
  exact (posDef_freeTripleGap_iff_det_pos_of_planeBranch design hdominates hfree).mpr hdet

/-- **The residual side, as one explicit sign.**  Failure of the plane branch
forces the free-triple gap to have nonpositive determinant. -/
theorem freeTripleGap_det_nonpos_of_not_planeBranchTenCandidate
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6)))
    (hfail : ¬ PlaneBranchTenCandidate design) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).det ≤ 0 := by
  by_contra hpositive
  push Not at hpositive
  exact hfail (planeBranchTenCandidate_of_freeTripleGap_det_pos design hdominates hfree
    hpositive)

/-- **The inertia of the free-triple gap on the residual side.**  It is strictly
positive on a two-dimensional plane and has nonpositive determinant, so it has
exactly two positive directions and one nonpositive one.  This is the structural
half of the measured dichotomy: the residual can never be reached with a
free-triple gap of three negative or two nonpositive directions. -/
theorem freeTripleGap_planePositive_and_det_nonpos_of_not_planeBranchTenCandidate
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6)))
    (hfail : ¬ PlaneBranchTenCandidate design) :
    ∃ axis : Fin 3 → ℝ, axis ⬝ᵥ axis = 1
      ∧ (∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
          0 < planar ⬝ᵥ ((subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1) *ᵥ planar))
      ∧ (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).det ≤ 0 := by
  obtain ⟨axis, hAxisAxis, hplane⟩ :=
    exists_unitAxis_freeTripleGap_planePositive_of_planeBranch design hdominates hfree
  exact ⟨axis, hAxisAxis, hplane,
    freeTripleGap_det_nonpos_of_not_planeBranchTenCandidate design hdominates hfree hfail⟩

/-! ## A second sub-branch closed outright: a tight base triple -/

/-- **When the base triple is already a resolution of the identity the complement
wins outright.**  Every direction is then tight, so the free triple strictly
over-reads all of them.  No domination, no free tight direction, no
nondegeneracy is needed. -/
theorem posDef_freeTripleGap_of_baseSubsetSum_eq_one
    (design : WeightedDesign 6 3)
    (hbase : subsetSum design ({0, 1, 2} : Finset (Fin 6)) = 1) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one design _), ?_⟩
  intro probe hprobeNe
  rw [star_trivial]
  have htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) probe := by
    show probe ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probe) = 0
    rw [hbase, sub_self, Matrix.zero_mulVec, dotProduct_zero]
  exact freeTripleGap_quadForm_pos_of_isTightDirection design hprobeNe htight

/-- The ten-candidate disjunction on a design whose base triple resolves the
identity, unconditionally. -/
theorem planeBranchTenCandidate_of_baseSubsetSum_eq_one
    (design : WeightedDesign 6 3)
    (hbase : subsetSum design ({0, 1, 2} : Finset (Fin 6)) = 1) :
    PlaneBranchTenCandidate design := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))))
  exact posDef_freeTripleGap_of_baseSubsetSum_eq_one design hbase

/-! ## The residual, now confined to the hard side

`PlaneBranchStrictPairCompletionSelector` asks for a good completion at EVERY
design of the branch.  The easy sub-branch above discharges it whenever the
free-triple determinant is positive, so the residual only has to be supplied
where that determinant is nonpositive.  The hard-side statement is therefore
strictly weaker -- `hardSideCompletionSelector_of_strictPairCompletionSelector`
proves the implication -- and still delivers the branch. -/

/-- **The plane branch's residual, restricted to the hard side.**  Identical to
`PlaneBranchStrictPairCompletionSelector` except that it is only required of
designs whose free-triple gap has nonpositive determinant. -/
def PlaneBranchHardSideCompletionSelector : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6)) →
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).det ≤ 0 →
    ∃ (pOne pTwo axis : Fin 3 → ℝ) (strongLabel otherLabel thirdLabel : Fin 6),
      pOne ⬝ᵥ pOne = 1
        ∧ pTwo ⬝ᵥ pTwo = 1
        ∧ axis ⬝ᵥ axis = 1
        ∧ pOne ⬝ᵥ pTwo = 0
        ∧ pOne ⬝ᵥ axis = 0
        ∧ pTwo ⬝ᵥ axis = 0
        ∧ strongLabel ≠ otherLabel
        ∧ thirdLabel ∉ ({strongLabel, otherLabel} : Finset (Fin 6))
        ∧ (∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
            planar ⬝ᵥ planar
              < (design.atom strongLabel ⬝ᵥ planar) ^ 2
                + (design.atom otherLabel ⬝ᵥ planar) ^ 2)
        ∧ 0 < (subsetSum design
            ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6)) - 1).det

/-- **THE PLANE BRANCH FROM THE HARD-SIDE RESIDUAL.**  The easy side is closed
by the free-triple determinant; the hard side is exactly what the residual
supplies. -/
theorem uThreeSixPlaneTenCandidateBranch_of_hardSideCompletionSelector
    (hselector : PlaneBranchHardSideCompletionSelector) :
    UThreeSixPlaneTenCandidateBranch := by
  intro design hlineFree hoffConic hdominates hfree
  rcases lt_or_ge 0 ((subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).det) with
    hdetPos | hdetNonpos
  · exact planeBranchTenCandidate_of_freeTripleGap_det_pos design hdominates hfree hdetPos
  obtain ⟨pOne, pTwo, axis, strongLabel, otherLabel, thirdLabel, hOneOne, hTwoTwo,
    hAxisAxis, hOneTwo, hOneAxis, hTwoAxis, hlabelNe, hthirdNotMem, hpairStrict,
    hdetPos⟩ := hselector design hlineFree hoffConic hdominates hfree hdetNonpos
  have hposDef := (posDef_gap_iff_det_pos_of_pairPlaneStrict design hOneOne hTwoTwo
    hAxisAxis hOneTwo hOneAxis hTwoAxis hlabelNe hthirdNotMem hpairStrict).mpr hdetPos
  have hcard : ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6)).card = 3 := by
    rw [show ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6))
      = insert thirdLabel ({strongLabel, otherLabel} : Finset (Fin 6)) from rfl,
      Finset.card_insert_of_notMem hthirdNotMem, Finset.card_pair hlabelNe]
  exact (exists_posDef_cardThree_iff_planeBranchTenCandidate design hdominates
    hfree).mp ⟨_, hcard, hposDef⟩

/-- The hard-side residual is genuinely weaker: it is implied by the residual
that quantifies over every design of the branch. -/
theorem hardSideCompletionSelector_of_strictPairCompletionSelector
    (hselector : PlaneBranchStrictPairCompletionSelector) :
    PlaneBranchHardSideCompletionSelector :=
  fun design hlineFree hoffConic hdominates hfree _hdetNonpos =>
    hselector design hlineFree hoffConic hdominates hfree

/-- **The hard-side residual with the completion confined to the base triple.**
On the hard side a free completion of a free pair is the complement candidate
itself, whose determinant is nonpositive by assumption; so nothing is lost by
asking the completing label to be a base label.  Each free pair then has three
completions to test instead of four. -/
def PlaneBranchHardSideBaseCompletionSelector : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6)) →
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).det ≤ 0 →
    ∃ (pOne pTwo axis : Fin 3 → ℝ) (strongLabel otherLabel baseLabel : Fin 6),
      pOne ⬝ᵥ pOne = 1
        ∧ pTwo ⬝ᵥ pTwo = 1
        ∧ axis ⬝ᵥ axis = 1
        ∧ pOne ⬝ᵥ pTwo = 0
        ∧ pOne ⬝ᵥ axis = 0
        ∧ pTwo ⬝ᵥ axis = 0
        ∧ strongLabel ≠ otherLabel
        ∧ strongLabel ∈ ({3, 4, 5} : Finset (Fin 6))
        ∧ otherLabel ∈ ({3, 4, 5} : Finset (Fin 6))
        ∧ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6))
        ∧ (∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
            planar ⬝ᵥ planar
              < (design.atom strongLabel ⬝ᵥ planar) ^ 2
                + (design.atom otherLabel ⬝ᵥ planar) ^ 2)
        ∧ 0 < (subsetSum design
            ({baseLabel, strongLabel, otherLabel} : Finset (Fin 6)) - 1).det

/-- The plane branch from the base-completion form of the hard-side residual. -/
theorem uThreeSixPlaneTenCandidateBranch_of_hardSideBaseCompletionSelector
    (hselector : PlaneBranchHardSideBaseCompletionSelector) :
    UThreeSixPlaneTenCandidateBranch := by
  intro design hlineFree hoffConic hdominates hfree
  rcases lt_or_ge 0 ((subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).det) with
    hdetPos | hdetNonpos
  · exact planeBranchTenCandidate_of_freeTripleGap_det_pos design hdominates hfree hdetPos
  obtain ⟨pOne, pTwo, axis, strongLabel, otherLabel, baseLabel, hOneOne, hTwoTwo,
    hAxisAxis, hOneTwo, hOneAxis, hTwoAxis, hlabelNe, hstrongFree, hotherFree, hbaseMem,
    hpairStrict, hdetPos⟩ := hselector design hlineFree hoffConic hdominates hfree
      hdetNonpos
  have hbaseNotMem : baseLabel ∉ ({strongLabel, otherLabel} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨baseLabel_ne_freeLabel hbaseMem hstrongFree,
      baseLabel_ne_freeLabel hbaseMem hotherFree⟩
  have hposDef := (posDef_gap_iff_det_pos_of_pairPlaneStrict design hOneOne hTwoTwo
    hAxisAxis hOneTwo hOneAxis hTwoAxis hlabelNe hbaseNotMem hpairStrict).mpr hdetPos
  have hcard : ({baseLabel, strongLabel, otherLabel} : Finset (Fin 6)).card = 3 := by
    rw [show ({baseLabel, strongLabel, otherLabel} : Finset (Fin 6))
      = insert baseLabel ({strongLabel, otherLabel} : Finset (Fin 6)) from rfl,
      Finset.card_insert_of_notMem hbaseNotMem, Finset.card_pair hlabelNe]
  exact (exists_posDef_cardThree_iff_planeBranchTenCandidate design hdominates
    hfree).mp ⟨_, hcard, hposDef⟩

/-! ## The base-completion budget, exactly

`adjugateReading_axis_pos_of_planePositive` says a completing DIRECTION always
exists; what it does not say is how the design's own atoms read that direction.
The base triple answers this exactly.  Under domination with a two-dimensional
tight space the base gap is one rank-one atom on the frame axis
(`Gtz.dominationGap_eq_axisAtom_of_orthonormal_tightPair`), so the base triple
resolves the identity plus that atom, and every quadratic form's three base
readings sum to its trace plus the base gap scale times its axis reading.

Applied to the adjugate of a free pair's gap this is the exact budget of the
pair's three base completions.  It is a CONSERVATION LAW, not a decision
procedure: the campaign's barriers -- pair averaging, tie surplus, the lift
deficit, the flat-pair complement average -- all say a budget of this shape
cannot by itself close the branch, and an explicit open slab where every
aggregate of this kind fails is known.  What the identity does supply is a
sufficient criterion in the original coordinates, with the base gap scale
appearing for the first time as an explicit summand. -/

/-- **THE DOMINATOR READING BUDGET.**  A dominator with a two-dimensional tight
space reads every form's trace, plus its own gap scale times the form's reading
along the frame axis.  Exact, division free, and true of every form. -/
theorem sum_dominatorReading_eq_trace_add_baseGapScale_mul_axisReading
    {size : ℕ} (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (form : Matrix (Fin 3) (Fin 3) ℝ)
    {pOne pTwo : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hdominates : Dominates design selected)
    (hOneTight : IsTightDirectionOf design selected pOne)
    (hTwoTight : IsTightDirectionOf design selected pTwo) :
    ∑ label ∈ selected, design.atom label ⬝ᵥ (form *ᵥ design.atom label)
      = Matrix.trace form
        + (crossProduct pOne pTwo ⬝ᵥ ((subsetSum design selected - 1)
              *ᵥ crossProduct pOne pTwo))
          * (crossProduct pOne pTwo ⬝ᵥ (form *ᵥ crossProduct pOne pTwo)) := by
  have hrankOne : subsetSum design selected - 1
      = (crossProduct pOne pTwo ⬝ᵥ ((subsetSum design selected - 1)
            *ᵥ crossProduct pOne pTwo)) • atomMatrix (crossProduct pOne pTwo) :=
    dominationGap_eq_axisAtom_of_orthonormal_tightPair design selected pOne pTwo
      hOneOne hTwoTwo hOneTwo hdominates hOneTight hTwoTight
  have hsum : subsetSum design selected
      = 1 + (crossProduct pOne pTwo ⬝ᵥ ((subsetSum design selected - 1)
            *ᵥ crossProduct pOne pTwo)) • atomMatrix (crossProduct pOne pTwo) := by
    rw [← hrankOne]
    abel
  have haxisTrace : Matrix.trace (form * atomMatrix (crossProduct pOne pTwo))
      = crossProduct pOne pTwo ⬝ᵥ (form *ᵥ crossProduct pOne pTwo) := by
    rw [Matrix.trace_mul_comm]
    exact atomMatrix_trace_pairing form (crossProduct pOne pTwo)
  rw [← trace_mul_subsetSum]
  conv_lhs => rw [hsum]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, haxisTrace, smul_eq_mul]

/-- **The three base completions of a free pair, budgeted exactly.**  Each
completion raises the pair gap's determinant by that base atom's adjugate
reading, and the three readings are budgeted by the law above. -/
theorem sum_baseCompletionDet_eq_pairAdjugateBudget
    (design : WeightedDesign 6 3)
    {pOne pTwo : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hOneTight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) pOne)
    (hTwoTight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) pTwo)
    {strongLabel otherLabel : Fin 6}
    (hstrongFree : strongLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hotherFree : otherLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    (subsetSum design ({0, strongLabel, otherLabel} : Finset (Fin 6)) - 1).det
        + (subsetSum design ({1, strongLabel, otherLabel} : Finset (Fin 6)) - 1).det
        + (subsetSum design ({2, strongLabel, otherLabel} : Finset (Fin 6)) - 1).det
      = 3 * (subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6)) - 1).det
        + Matrix.trace
            ((subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6)) - 1).adjugate)
        + (crossProduct pOne pTwo
              ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1)
                *ᵥ crossProduct pOne pTwo))
          * (crossProduct pOne pTwo
              ⬝ᵥ ((subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6))
                  - 1).adjugate *ᵥ crossProduct pOne pTwo)) := by
  have hcompletion : ∀ baseLabel : Fin 6, baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)) →
      (subsetSum design ({baseLabel, strongLabel, otherLabel} : Finset (Fin 6)) - 1).det
        = (subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6)) - 1).det
          + design.atom baseLabel
            ⬝ᵥ ((subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6))
                - 1).adjugate *ᵥ design.atom baseLabel) := by
    intro baseLabel hbaseMem
    have hbaseNotMem : baseLabel ∉ ({strongLabel, otherLabel} : Finset (Fin 6)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨baseLabel_ne_freeLabel hbaseMem hstrongFree,
        baseLabel_ne_freeLabel hbaseMem hotherFree⟩
    rw [show ({baseLabel, strongLabel, otherLabel} : Finset (Fin 6))
      = insert baseLabel ({strongLabel, otherLabel} : Finset (Fin 6)) from rfl,
      insertGap_eq_gap_add_atomMatrix design hbaseNotMem, det_add_atomMatrix_fin_three]
  have hbudget := sum_dominatorReading_eq_trace_add_baseGapScale_mul_axisReading design
    ({0, 1, 2} : Finset (Fin 6))
    ((subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6)) - 1).adjugate)
    hOneOne hTwoTwo hOneTwo hdominates hOneTight hTwoTight
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hbudget
  rw [hcompletion 0 (by decide), hcompletion 1 (by decide), hcompletion 2 (by decide)]
  linarith [hbudget]

/-- **A sufficient criterion for the plane branch, in original coordinates.**
When a free pair's base-completion budget is positive one of the three base
completions has positive determinant.  On a plane-strict pair that determinant
sign IS strict domination, so the branch follows.  This is a SUFFICIENT
condition only: the budget can be nonpositive at designs where a completion
still fires. -/
theorem exists_baseCompletion_det_pos_of_pairAdjugateBudget_pos
    (design : WeightedDesign 6 3)
    {pOne pTwo : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hOneTight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) pOne)
    (hTwoTight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) pTwo)
    {strongLabel otherLabel : Fin 6}
    (hstrongFree : strongLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hotherFree : otherLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hbudget : 0 < 3 * (subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6)) - 1).det
      + Matrix.trace
          ((subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6)) - 1).adjugate)
      + (crossProduct pOne pTwo
            ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1)
              *ᵥ crossProduct pOne pTwo))
        * (crossProduct pOne pTwo
            ⬝ᵥ ((subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6))
                - 1).adjugate *ᵥ crossProduct pOne pTwo))) :
    ∃ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      0 < (subsetSum design ({baseLabel, strongLabel, otherLabel} : Finset (Fin 6))
        - 1).det := by
  by_contra hnone
  push Not at hnone
  have hzero := hnone 0 (by decide)
  have hone := hnone 1 (by decide)
  have htwo := hnone 2 (by decide)
  have hidentity := sum_baseCompletionDet_eq_pairAdjugateBudget design hOneOne hTwoTwo
    hOneTwo hdominates hOneTight hTwoTight hstrongFree hotherFree
  linarith

/-- **The plane branch from a plane-strict free pair with a positive base
budget.**  Combines the budget criterion with the one-determinant test. -/
theorem planeBranchTenCandidate_of_pairPlaneStrict_of_pairAdjugateBudget_pos
    (design : WeightedDesign 6 3)
    {pOne pTwo : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6)))
    (hOneTight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) pOne)
    (hTwoTight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) pTwo)
    {strongLabel otherLabel : Fin 6}
    (hstrongFree : strongLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hotherFree : otherLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hlabelNe : strongLabel ≠ otherLabel)
    (hpairStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ crossProduct pOne pTwo = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2)
    (hbudget : 0 < 3 * (subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6)) - 1).det
      + Matrix.trace
          ((subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6)) - 1).adjugate)
      + (crossProduct pOne pTwo
            ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1)
              *ᵥ crossProduct pOne pTwo))
        * (crossProduct pOne pTwo
            ⬝ᵥ ((subsetSum design ({strongLabel, otherLabel} : Finset (Fin 6))
                - 1).adjugate *ᵥ crossProduct pOne pTwo))) :
    PlaneBranchTenCandidate design := by
  obtain ⟨baseLabel, hbaseMem, hdetPos⟩ :=
    exists_baseCompletion_det_pos_of_pairAdjugateBudget_pos design hOneOne hTwoTwo hOneTwo
      hdominates hOneTight hTwoTight hstrongFree hotherFree hbudget
  have hAxisAxis : crossProduct pOne pTwo ⬝ᵥ crossProduct pOne pTwo = 1 := by
    rw [planarCross_self_dot, hOneOne, hTwoTwo, hOneTwo]
    ring
  have hOneAxis : pOne ⬝ᵥ crossProduct pOne pTwo = 0 := planarCross_probe_dot pOne pTwo
  have hTwoAxis : pTwo ⬝ᵥ crossProduct pOne pTwo = 0 := planarCross_seed_dot pOne pTwo
  have hbaseNotMem : baseLabel ∉ ({strongLabel, otherLabel} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨baseLabel_ne_freeLabel hbaseMem hstrongFree,
      baseLabel_ne_freeLabel hbaseMem hotherFree⟩
  have hposDef := (posDef_gap_iff_det_pos_of_pairPlaneStrict design hOneOne hTwoTwo
    hAxisAxis hOneTwo hOneAxis hTwoAxis hlabelNe hbaseNotMem hpairStrict).mpr hdetPos
  have hcard : ({baseLabel, strongLabel, otherLabel} : Finset (Fin 6)).card = 3 := by
    rw [show ({baseLabel, strongLabel, otherLabel} : Finset (Fin 6))
      = insert baseLabel ({strongLabel, otherLabel} : Finset (Fin 6)) from rfl,
      Finset.card_insert_of_notMem hbaseNotMem, Finset.card_pair hlabelNe]
  exact (exists_posDef_cardThree_iff_planeBranchTenCandidate design hdominates
    hfree).mp ⟨_, hcard, hposDef⟩

/-! ## The hard side loses one completion per free pair

A free completion of a free pair is the complement candidate itself, so on the
hard side each of the three free pairs has only its three BASE completions left
to test -- exactly the nine distance-two candidates and nothing else. -/

/-- Three distinct free labels are the free triple. -/
theorem freeTriple_eq_of_three_distinct_freeLabels
    {firstLabel secondLabel thirdLabel : Fin 6}
    (hfirst : firstLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hsecond : secondLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hthird : thirdLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hfirstSecond : firstLabel ≠ secondLabel)
    (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    ({firstLabel, secondLabel, thirdLabel} : Finset (Fin 6))
      = ({3, 4, 5} : Finset (Fin 6)) := by
  revert hfirstSecond hfirstThird hsecondThird
  fin_cases hfirst <;> fin_cases hsecond <;> fin_cases hthird <;> decide

/-- A label outside the free triple is a base label. -/
theorem mem_baseTriple_of_not_mem_freeTriple {label : Fin 6}
    (hnotFree : label ∉ ({3, 4, 5} : Finset (Fin 6))) :
    label ∈ ({0, 1, 2} : Finset (Fin 6)) := by
  revert hnotFree
  fin_cases label <;> decide

/-- **On the hard side a free completion of a free pair is refused.**  It is the
complement candidate itself. -/
theorem freeCompletion_det_nonpos_of_hardSide
    (design : WeightedDesign 6 3)
    {strongLabel otherLabel thirdLabel : Fin 6}
    (hstrongFree : strongLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hotherFree : otherLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hthirdFree : thirdLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hlabelNe : strongLabel ≠ otherLabel)
    (hthirdNotMem : thirdLabel ∉ ({strongLabel, otherLabel} : Finset (Fin 6)))
    (hdetNonpos : (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).det ≤ 0) :
    (subsetSum design ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6))
      - 1).det ≤ 0 := by
  have hthirdStrong : thirdLabel ≠ strongLabel := by
    intro hequal
    exact hthirdNotMem (by rw [hequal]; exact Finset.mem_insert_self _ _)
  have hthirdOther : thirdLabel ≠ otherLabel := by
    intro hequal
    exact hthirdNotMem (by
      rw [hequal]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rwa [freeTriple_eq_of_three_distinct_freeLabels hthirdFree hstrongFree hotherFree
    hthirdStrong hthirdOther hlabelNe]

/-- **The hard-side residual asked of a FREE pair.**  The hinge always hands
over a plane-strict pair of free labels, so this is the shape the branch's own
machinery produces; the completing label is left unconstrained. -/
def PlaneBranchHardSideFreePairSelector : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6)) →
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).det ≤ 0 →
    ∃ (pOne pTwo axis : Fin 3 → ℝ) (strongLabel otherLabel thirdLabel : Fin 6),
      pOne ⬝ᵥ pOne = 1
        ∧ pTwo ⬝ᵥ pTwo = 1
        ∧ axis ⬝ᵥ axis = 1
        ∧ pOne ⬝ᵥ pTwo = 0
        ∧ pOne ⬝ᵥ axis = 0
        ∧ pTwo ⬝ᵥ axis = 0
        ∧ strongLabel ≠ otherLabel
        ∧ strongLabel ∈ ({3, 4, 5} : Finset (Fin 6))
        ∧ otherLabel ∈ ({3, 4, 5} : Finset (Fin 6))
        ∧ thirdLabel ∉ ({strongLabel, otherLabel} : Finset (Fin 6))
        ∧ (∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
            planar ⬝ᵥ planar
              < (design.atom strongLabel ⬝ᵥ planar) ^ 2
                + (design.atom otherLabel ⬝ᵥ planar) ^ 2)
        ∧ 0 < (subsetSum design
            ({thirdLabel, strongLabel, otherLabel} : Finset (Fin 6)) - 1).det

/-- **On the hard side a free-pair residual is already a base-completion
residual.**  A completing label of a free pair cannot itself be free there: the
resulting triple would be the complement candidate, whose determinant is
nonpositive by assumption.  So each free pair has THREE completions left to
test, not four, and those three are exactly the nine distance-two candidates. -/
theorem hardSideBaseCompletionSelector_of_hardSideFreePairSelector
    (hselector : PlaneBranchHardSideFreePairSelector) :
    PlaneBranchHardSideBaseCompletionSelector := by
  intro design hlineFree hoffConic hdominates hfree hdetNonpos
  obtain ⟨pOne, pTwo, axis, strongLabel, otherLabel, thirdLabel, hOneOne, hTwoTwo,
    hAxisAxis, hOneTwo, hOneAxis, hTwoAxis, hlabelNe, hstrongFree, hotherFree,
    hthirdNotMem, hpairStrict, hdetPos⟩ :=
    hselector design hlineFree hoffConic hdominates hfree hdetNonpos
  have hthirdBase : thirdLabel ∈ ({0, 1, 2} : Finset (Fin 6)) := by
    refine mem_baseTriple_of_not_mem_freeTriple fun hthirdFree => ?_
    have hrefused := freeCompletion_det_nonpos_of_hardSide design hstrongFree hotherFree
      hthirdFree hlabelNe hthirdNotMem hdetNonpos
    linarith
  exact ⟨pOne, pTwo, axis, strongLabel, otherLabel, thirdLabel, hOneOne, hTwoTwo,
    hAxisAxis, hOneTwo, hOneAxis, hTwoAxis, hlabelNe, hstrongFree, hotherFree,
    hthirdBase, hpairStrict, hdetPos⟩

end Gtz

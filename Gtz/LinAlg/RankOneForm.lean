/-
# The rank-one form of a positive semidefinite matrix, produced

`Gtz/Quantitative/InteriorExclusion.lean` carries a DISCLOSURE.  Its exclusion
`Gtz.value_eq_rank_of_rankOneMultiplier` takes the EXPLICIT rank-one form
`multiplierMatrix = scale • atomMatrix unitDir` as a hypothesis, and the file
states in writing that "the passage from `Matrix.rank <= 1` to that form is a
spectral fact and is NOT mechanized here".

`Gtz.exists_rankOne_of_symm_twoKernel` (`Gtz/Design/StarOnlyLaw.lean`) produces
the form, but only at size three and only from two kernel vectors with a nonzero
cross product.  Mathlib has no bridge either: it carries no `rank_le_one_iff` and
no outer-product characterization of a rank-one matrix.

This module produces the form at every size, from a division-free hypothesis.
The hypothesis is that every two-by-two minor vanishes, which is a polynomial
identity a certificate can carry, and not a spectral statement.

The route is elementary and uses no eigenvalue.  A vanishing two-by-two minor on
rows `(r, j)` and columns `(c, j)` reads `M r c * M j j = M r j * M j c`.  When
the diagonal entry `M j j` is not zero, that equation solves for every entry of
the matrix in terms of one column.  When every diagonal entry is zero, positive
semidefiniteness alone forces the matrix to vanish.

The scale that comes out is nonnegative, and the classification is an
equivalence: a positive semidefinite matrix with vanishing minors IS an atom
matrix, with the scale absorbed into the axis by a square root.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.StarOnlyLaw

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## 1. The quadratic form of a positive semidefinite matrix

The corpus reads positive semidefiniteness through
`Matrix.posSemidef_iff_dotProduct_mulVec`.  These two lemmas package that
reading and the standard basis plumbing, which is the step that makes the
Cauchy-Schwarz bound below cheap. -/

/-- The quadratic form of a positive semidefinite matrix is nonnegative. -/
theorem quadForm_nonneg_of_posSemidef_rankOne {mat : Matrix (Fin size) (Fin size) ℝ}
    (hpsd : mat.PosSemidef) (probe : Fin size → ℝ) :
    0 ≤ probe ⬝ᵥ (mat *ᵥ probe) := by
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
  rwa [star_trivial] at h

/-- A positive semidefinite matrix is symmetric. -/
theorem symm_of_posSemidef {mat : Matrix (Fin size) (Fin size) ℝ}
    (hpsd : mat.PosSemidef) (row col : Fin size) : mat col row = mat row col := by
  have h := hpsd.1.apply row col
  simpa using h

/-- The quadratic form of a matrix between two standard basis vectors reads off
the single entry they select. -/
theorem single_pair_dotProduct_mulVec (mat : Matrix (Fin size) (Fin size) ℝ)
    (first second : Fin size) (scaleFirst scaleSecond : ℝ) :
    (Pi.single first scaleFirst) ⬝ᵥ (mat *ᵥ (Pi.single second scaleSecond))
      = scaleFirst * scaleSecond * mat first second := by
  simp only [dotProduct, Matrix.mulVec, Pi.single_apply, ite_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The quadratic form at a two-term standard combination.  This is the plumbing
that makes the discriminant argument available. -/
theorem quadForm_pair (mat : Matrix (Fin size) (Fin size) ℝ)
    (first second : Fin size) (scaleFirst scaleSecond : ℝ) :
    (Pi.single first scaleFirst + Pi.single second scaleSecond)
        ⬝ᵥ (mat *ᵥ (Pi.single first scaleFirst + Pi.single second scaleSecond))
      = scaleFirst * scaleFirst * mat first first
        + scaleFirst * scaleSecond * (mat first second + mat second first)
        + scaleSecond * scaleSecond * mat second second := by
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    single_pair_dotProduct_mulVec, single_pair_dotProduct_mulVec,
    single_pair_dotProduct_mulVec, single_pair_dotProduct_mulVec]
  ring

/-! ## 2. Cauchy-Schwarz for a positive semidefinite matrix

The off-diagonal entry of a positive semidefinite matrix is bounded by the two
diagonal entries it sits between.  The proof is the discriminant of the
quadratic form restricted to the plane those two coordinates span. -/

/-- **CAUCHY-SCHWARZ ON THE ENTRIES.**  An off-diagonal entry of a positive
semidefinite matrix is bounded by the product of its two diagonal entries. -/
theorem posSemidef_offDiag_sq_le {mat : Matrix (Fin size) (Fin size) ℝ}
    (hpsd : mat.PosSemidef) (row col : Fin size) :
    (mat row col) ^ 2 ≤ mat row row * mat col col := by
  have hsymm := symm_of_posSemidef hpsd row col
  have hquad : ∀ step : ℝ,
      0 ≤ mat row row * (step * step) + (2 * mat row col) * step + mat col col := by
    intro step
    have h := quadForm_nonneg_of_posSemidef_rankOne hpsd
      (Pi.single row step + Pi.single col (1 : ℝ))
    rw [quadForm_pair] at h
    rw [hsymm] at h
    nlinarith [h]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- A zero diagonal entry annihilates its whole row. -/
theorem posSemidef_offDiag_eq_zero_of_diag_eq_zero
    {mat : Matrix (Fin size) (Fin size) ℝ} (hpsd : mat.PosSemidef)
    {row : Fin size} (hzero : mat row row = 0) (col : Fin size) :
    mat row col = 0 := by
  have hbound := posSemidef_offDiag_sq_le hpsd row col
  rw [hzero, zero_mul] at hbound
  nlinarith [sq_nonneg (mat row col)]

/-- **A POSITIVE SEMIDEFINITE MATRIX WITH ZERO DIAGONAL IS ZERO.**  This is the
degenerate branch of the rank-one extraction below. -/
theorem eq_zero_of_posSemidef_of_diag_eq_zero
    {mat : Matrix (Fin size) (Fin size) ℝ} (hpsd : mat.PosSemidef)
    (hdiag : ∀ label, mat label label = 0) : mat = 0 := by
  ext row col
  exact posSemidef_offDiag_eq_zero_of_diag_eq_zero hpsd (hdiag row) col

/-! ## 3. The vanishing minor hypothesis and the rank-one engine

A matrix has rank at most one exactly when every two-by-two minor vanishes.  The
predicate below states that condition directly, without the rank API, so it is a
polynomial identity that a certificate can carry. -/

/-- **EVERY TWO-BY-TWO MINOR VANISHES.**  The division-free form of the condition
"rank at most one". -/
def MinorVanishes (mat : Matrix (Fin size) (Fin size) ℝ) : Prop :=
  ∀ rowOne rowTwo colOne colTwo : Fin size,
    mat rowOne colOne * mat rowTwo colTwo = mat rowOne colTwo * mat rowTwo colOne

/-- **THE RANK-ONE ENGINE.**  A symmetric matrix whose two-by-two minors vanish,
and which has one nonzero diagonal entry, is the atom matrix of the column at
that entry, scaled by the inverse of the entry.  No eigenvalue and no spectral
theorem appear. -/
theorem eq_smul_atomMatrix_of_minorVanishes
    {mat : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : ∀ row col, mat col row = mat row col)
    (hminor : MinorVanishes mat) {pivot : Fin size} (hpivot : mat pivot pivot ≠ 0) :
    mat = (mat pivot pivot)⁻¹ • atomMatrix (fun row => mat row pivot) := by
  ext row col
  have hkey : mat row col * mat pivot pivot = mat row pivot * mat col pivot := by
    have h := hminor row pivot col pivot
    rw [hsymm col pivot] at h
    linarith [h]
  simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  field_simp
  linarith [hkey]

/-! ## 4. The producer

The two branches combine.  Either every diagonal entry vanishes and the matrix is
zero, or one does not and the engine fires.  The scale is nonnegative in both
branches, because a positive semidefinite matrix has a nonnegative diagonal. -/

/-- **THE WALL FORM, PRODUCED, AT EVERY SIZE.**  A positive semidefinite matrix
whose two-by-two minors vanish is a nonnegative multiple of an atom matrix.  This
is the passage that `Gtz/Quantitative/InteriorExclusion.lean` records as not
mechanized, and that Mathlib does not carry. -/
theorem exists_rankOne_of_posSemidef_of_minorVanishes
    {mat : Matrix (Fin size) (Fin size) ℝ} (hpsd : mat.PosSemidef)
    (hminor : MinorVanishes mat) :
    ∃ (axis : Fin size → ℝ) (scale : ℝ), 0 ≤ scale ∧ mat = scale • atomMatrix axis := by
  by_cases hdiag : ∃ pivot, mat pivot pivot ≠ 0
  · obtain ⟨pivot, hpivot⟩ := hdiag
    have hpos : 0 < mat pivot pivot :=
      lt_of_le_of_ne hpsd.diag_nonneg (Ne.symm hpivot)
    refine ⟨fun row => mat row pivot, (mat pivot pivot)⁻¹, le_of_lt (inv_pos.mpr hpos), ?_⟩
    exact eq_smul_atomMatrix_of_minorVanishes (symm_of_posSemidef hpsd) hminor hpivot
  · refine ⟨0, 0, le_refl 0, ?_⟩
    have hall : ∀ label, mat label label = 0 := by
      intro label
      by_contra hcon
      exact hdiag ⟨label, hcon⟩
    rw [eq_zero_of_posSemidef_of_diag_eq_zero hpsd hall, zero_smul]

/-- The atom matrix of any vector has vanishing minors.  This is the converse
half of the classification. -/
theorem minorVanishes_smul_atomMatrix (axis : Fin size → ℝ) (scale : ℝ) :
    MinorVanishes (scale • atomMatrix axis) := by
  intro rowOne rowTwo colOne colTwo
  simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-- A nonnegative multiple of an atom matrix is positive semidefinite.  The atom
matrix itself is already positive semidefinite in the corpus, so this only adds
the scale. -/
theorem posSemidef_smul_atomMatrix {scale : ℝ} (hscale : 0 ≤ scale)
    (axis : Fin size → ℝ) : (scale • atomMatrix axis).PosSemidef :=
  (posSemidef_atomMatrix axis).smul hscale

/-- **THE CLASSIFICATION.**  A matrix is positive semidefinite with vanishing
two-by-two minors exactly when it is a nonnegative multiple of an atom matrix. -/
theorem posSemidef_minorVanishes_iff {mat : Matrix (Fin size) (Fin size) ℝ} :
    (mat.PosSemidef ∧ MinorVanishes mat)
      ↔ ∃ (axis : Fin size → ℝ) (scale : ℝ), 0 ≤ scale ∧ mat = scale • atomMatrix axis := by
  constructor
  · rintro ⟨hpsd, hminor⟩
    exact exists_rankOne_of_posSemidef_of_minorVanishes hpsd hminor
  · rintro ⟨axis, scale, hscale, rfl⟩
    exact ⟨posSemidef_smul_atomMatrix hscale axis, minorVanishes_smul_atomMatrix axis scale⟩

/-! ## 5. The scale absorbed into the axis

The scale is nonnegative, so its square root can be pushed into the axis.  The
form then has no scale at all. -/

/-- **THE SCALE-FREE FORM.**  A positive semidefinite matrix with vanishing
minors IS an atom matrix. -/
theorem exists_atomMatrix_of_posSemidef_of_minorVanishes
    {mat : Matrix (Fin size) (Fin size) ℝ} (hpsd : mat.PosSemidef)
    (hminor : MinorVanishes mat) :
    ∃ axis : Fin size → ℝ, mat = atomMatrix axis := by
  obtain ⟨axis, scale, hscale, hform⟩ :=
    exists_rankOne_of_posSemidef_of_minorVanishes hpsd hminor
  refine ⟨Real.sqrt scale • axis, ?_⟩
  rw [hform]
  ext row col
  simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul]
  have hsq : Real.sqrt scale * Real.sqrt scale = scale := Real.mul_self_sqrt hscale
  linear_combination (-(axis row * axis col)) * hsq

/-! ## 6. The bridge to the size-three two-kernel law

`Gtz.exists_rankOne_of_symm_twoKernel` extracts the same form at size three from
two kernel directions.  Its hypothesis implies the minor hypothesis here, so the
general law of this module subsumes it. -/

/-- The minor hypothesis follows from the explicit form, hence from any route
that produces the form.  This closes the loop with the size-three law. -/
theorem minorVanishes_of_eq_smul_atomMatrix
    {mat : Matrix (Fin size) (Fin size) ℝ} {axis : Fin size → ℝ} {scale : ℝ}
    (hform : mat = scale • atomMatrix axis) : MinorVanishes mat := by
  rw [hform]
  exact minorVanishes_smul_atomMatrix axis scale

/-- A positive semidefinite matrix produced by the size-three two-kernel law has
vanishing minors, so the two routes agree. -/
theorem minorVanishes_of_symm_twoKernel {mat : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : matᵀ = mat) {kernelOne kernelTwo : Fin 3 → ℝ}
    (hone : mat *ᵥ kernelOne = 0) (htwo : mat *ᵥ kernelTwo = 0)
    (hcross : crossProduct kernelOne kernelTwo ≠ 0) : MinorVanishes mat := by
  obtain ⟨scale, hform⟩ :=
    exists_rankOne_of_symm_twoKernel hsymm hone htwo hcross
  exact minorVanishes_of_eq_smul_atomMatrix hform

end Gtz

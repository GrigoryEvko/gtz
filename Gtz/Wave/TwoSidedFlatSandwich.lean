/-
# The two-sided sandwich on the flat stratum

`Gtz.min_det_blockGapAt_one_sub_of_flat` reads the sign-free margin of a triple as
the minimum of the two gap determinants of the complementation involution.  A
certificate that reads only diagonal gaps and squared pairings cannot separate the
two sides, so it fires only where BOTH gap blocks are positive definite.  This file
decides whether that two-sided region is inhabited on the flat stratum.

The answer is YES, and the witness is primitive.  `Gtz.orthoPairProjection` is the
`(6,3)` analogue of the landed `Gtz.orthogonalPairInvolution` (which is the `(4,2)`
case): a rank-three projection whose Seidel involution `2 * P - 1` is block
antidiagonal with an orthogonal `3 x 3` corner.  Its first three labels are pairwise
orthogonal atoms, so the gap block there is `(1/3) * 1` and BOTH sides are positive
definite with determinant exactly `1/27`.

The decision procedure behind that is exact and division free.  Writing `q` for the
triple's pairing energy and `p` for its cross term, at a flat form and uniform
weight

  `216 * det (gap block)      = 8 - 72 * q + 432 * p`
  `216 * det (dual gap block) = 8 - 72 * q - 432 * p`

so the sign-free margin is `(8 - 72 * q - 432 * |p|) / 216`.  Two consequences.  The
sign-free margin on the flat stratum is capped by `1/27`, attained EXACTLY at
`q = p = 0`, so the witness is the global maximizer.  And the same polynomial is the
landed `Gtz.elliptopeBracket` at the rescaling `rho = 3 * P_cd`, which is why five
forks kept flagging `Gtz/LinAlg/ElliptopeInterval.lean`: that file decides
realizability of a correlation triple, this file decides two-sided domination, and
the two questions share one cubic at two different scalings.

The campaign has been trying to make the threshold small.  The witness maximizes it
(`q = 0` gives the largest threshold `19` in the landed flat law
`Gtz.projThresholdAt_eq_iff_energy_eq_of_flat`) and wins on the bracket instead.
-/
import Gtz.Wave.ComplementDualLane
import Gtz.LinAlg.ElliptopeInterval

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## 1. The two invariants of a triple -/

/-- The pairing energy of a selected triple: the sum of the three squared
off-diagonal entries. -/
noncomputable def flatPairEnergy (form : Matrix (Fin size) (Fin size) ℝ)
    (pick : Fin 3 → Fin size) : ℝ :=
  form (pick 0) (pick 1) ^ 2 + form (pick 0) (pick 2) ^ 2 + form (pick 1) (pick 2) ^ 2

/-- The cross term of a selected triple: the product of the three off-diagonal
entries.  Its SIGN is what a sign-blind certificate cannot read. -/
noncomputable def flatTripleCross (form : Matrix (Fin size) (Fin size) ℝ)
    (pick : Fin 3 → Fin size) : ℝ :=
  form (pick 0) (pick 1) * form (pick 0) (pick 2) * form (pick 1) (pick 2)

theorem flatPairEnergy_nonneg (form : Matrix (Fin size) (Fin size) ℝ)
    (pick : Fin 3 → Fin size) : 0 ≤ flatPairEnergy form pick := by
  unfold flatPairEnergy; positivity

/-- The complementation involution negates every off-diagonal entry, so it fixes the
energy. -/
theorem flatPairEnergy_one_sub (form : Matrix (Fin size) (Fin size) ℝ)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick) :
    flatPairEnergy (1 - form) pick = flatPairEnergy form pick := by
  have h01 : (1 - form) (pick 0) (pick 1) = -form (pick 0) (pick 1) := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (fun heq => by simpa using hinj heq)]; ring
  have h02 : (1 - form) (pick 0) (pick 2) = -form (pick 0) (pick 2) := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (fun heq => by simpa using hinj heq)]; ring
  have h12 : (1 - form) (pick 1) (pick 2) = -form (pick 1) (pick 2) := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (fun heq => by simpa using hinj heq)]; ring
  unfold flatPairEnergy; rw [h01, h02, h12]; ring

/-- The complementation involution flips the SIGN of the cross term.  This is the
one quantity the two sides disagree on. -/
theorem flatTripleCross_one_sub (form : Matrix (Fin size) (Fin size) ℝ)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick) :
    flatTripleCross (1 - form) pick = -flatTripleCross form pick := by
  have h01 : (1 - form) (pick 0) (pick 1) = -form (pick 0) (pick 1) := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (fun heq => by simpa using hinj heq)]; ring
  have h02 : (1 - form) (pick 0) (pick 2) = -form (pick 0) (pick 2) := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (fun heq => by simpa using hinj heq)]; ring
  have h12 : (1 - form) (pick 1) (pick 2) = -form (pick 1) (pick 2) := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (fun heq => by simpa using hinj heq)]; ring
  unfold flatTripleCross; rw [h01, h02, h12]; ring

/-! ## 2. The determinant law on the flat stratum -/

section FlatDeterminant

variable {form : Matrix (Fin size) (Fin size) ℝ}

/-- Every diagonal entry of the gap block at uniform weight is one third. -/
theorem blockGapAt_flat_diag {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hflat6 : IsFlatDiagonal form6)
    (pick : Fin 3 → Fin 6) (slot : Fin 3) :
    blockGapAt form6 sixthWeight pick slot slot = 1 / 3 := by
  rw [blockGapAt_apply_diag, hflat6, sixthWeight]; norm_num

/-- **THE FLAT DETERMINANT LAW.**  At a flat symmetric form and uniform weight the
gap block determinant is a fixed affine function of the pairing energy and the cross
term, with no division and no eigenvalue.  Every landed flat number is a value of
this one polynomial. -/
theorem twoHundredSixteen_mul_det_blockGapAt_of_flat
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    (pick : Fin 3 → Fin 6) :
    216 * (blockGapAt form6 sixthWeight pick).det
      = 8 - 72 * flatPairEnergy form6 pick + 432 * flatTripleCross form6 pick := by
  have hd : ∀ slot : Fin 3, blockGapAt form6 sixthWeight pick slot slot = 1 / 3 := by
    intro slot; rw [blockGapAt_apply_diag, hflat, sixthWeight]; norm_num
  have ho : ∀ {a b : Fin 3}, a ≠ b →
      blockGapAt form6 sixthWeight pick a b = form6 (pick a) (pick b) := by
    intro a b hne; exact blockGapAt_apply_offDiag _ _ _ hne
  have hs : ∀ a b : Fin 6, form6 b a = form6 a b := by
    intro a b; conv_lhs => rw [← hsymm]
    rfl
  rw [Matrix.det_fin_three]
  rw [hd 0, hd 1, hd 2, ho (by decide : (0 : Fin 3) ≠ 1), ho (by decide : (0 : Fin 3) ≠ 2),
    ho (by decide : (1 : Fin 3) ≠ 0), ho (by decide : (1 : Fin 3) ≠ 2),
    ho (by decide : (2 : Fin 3) ≠ 0), ho (by decide : (2 : Fin 3) ≠ 1)]
  rw [hs (pick 0) (pick 1), hs (pick 0) (pick 2), hs (pick 1) (pick 2)]
  unfold flatPairEnergy flatTripleCross
  ring

/-- The dual side, obtained by flipping the cross term. -/
theorem twoHundredSixteen_mul_det_blockGapAt_one_sub_of_flat
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick) :
    216 * (blockGapAt (1 - form6) sixthWeight pick).det
      = 8 - 72 * flatPairEnergy form6 pick - 432 * flatTripleCross form6 pick := by
  have hsymm' : (1 - form6)ᵀ = 1 - form6 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymm]
  rw [twoHundredSixteen_mul_det_blockGapAt_of_flat hsymm' (isFlatDiagonal_one_sub hflat) pick,
    flatPairEnergy_one_sub form6 hinj, flatTripleCross_one_sub form6 hinj]
  ring

/-- **The sign-free margin, in closed form.**  Composing the two sides with the
landed minimum law turns the campaign's central quantity into one polynomial in the
energy and the absolute cross term. -/
theorem twoHundredSixteen_mul_min_det_of_flat
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick) :
    216 * min (blockGapAt form6 sixthWeight pick).det
        (blockGapAt (1 - form6) sixthWeight pick).det
      = 8 - 72 * flatPairEnergy form6 pick - 432 * |flatTripleCross form6 pick| := by
  rcases abs_cases (flatTripleCross form6 pick) with ⟨habs, hsign⟩ | ⟨habs, hsign⟩
  · rw [habs, min_eq_right, twoHundredSixteen_mul_det_blockGapAt_one_sub_of_flat hsymm hflat hinj]
    have h1 := twoHundredSixteen_mul_det_blockGapAt_of_flat hsymm hflat pick
    have h2 := twoHundredSixteen_mul_det_blockGapAt_one_sub_of_flat hsymm hflat hinj
    nlinarith [h1, h2, hsign]
  · rw [habs, min_eq_left, twoHundredSixteen_mul_det_blockGapAt_of_flat hsymm hflat pick]
    · ring
    · have h1 := twoHundredSixteen_mul_det_blockGapAt_of_flat hsymm hflat pick
      have h2 := twoHundredSixteen_mul_det_blockGapAt_one_sub_of_flat hsymm hflat hinj
      nlinarith [h1, h2, hsign]

/-- **THE UNIVERSAL CAP ON THE FLAT STRATUM.**  The sign-free margin of any triple of
any flat symmetric form is at most `1/27`.  Both correction terms are nonnegative, so
the bound needs no hypothesis beyond flatness. -/
theorem min_det_of_flat_le_one_twentySeventh
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick) :
    min (blockGapAt form6 sixthWeight pick).det
        (blockGapAt (1 - form6) sixthWeight pick).det ≤ 1 / 27 := by
  have h := twoHundredSixteen_mul_min_det_of_flat hsymm hflat hinj
  have he := flatPairEnergy_nonneg form6 pick
  have ha : 0 ≤ |flatTripleCross form6 pick| := abs_nonneg _
  linarith

/-- **The cap is attained EXACTLY at a decoupled triple.**  Equality forces both the
energy and the cross term to vanish, so the maximizer of the sign-free margin on the
flat stratum is a triple of pairwise orthogonal atoms and nothing else. -/
theorem flatPairEnergy_eq_zero_of_min_det_eq
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (heq : min (blockGapAt form6 sixthWeight pick).det
        (blockGapAt (1 - form6) sixthWeight pick).det = 1 / 27) :
    flatPairEnergy form6 pick = 0 := by
  have h := twoHundredSixteen_mul_min_det_of_flat hsymm hflat hinj
  rw [heq] at h
  have he := flatPairEnergy_nonneg form6 pick
  have ha : 0 ≤ |flatTripleCross form6 pick| := abs_nonneg _
  linarith

/-- The same equality kills the cross term. -/
theorem flatTripleCross_eq_zero_of_min_det_eq
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (heq : min (blockGapAt form6 sixthWeight pick).det
        (blockGapAt (1 - form6) sixthWeight pick).det = 1 / 27) :
    flatTripleCross form6 pick = 0 := by
  have h := twoHundredSixteen_mul_min_det_of_flat hsymm hflat hinj
  rw [heq] at h
  have he := flatPairEnergy_nonneg form6 pick
  have ha : 0 ≤ |flatTripleCross form6 pick| := abs_nonneg _
  have : |flatTripleCross form6 pick| = 0 := by linarith
  exact abs_eq_zero.mp this

end FlatDeterminant

/-! ## 3. The elliptope bridge

The flat gap determinant is the landed `Gtz.elliptopeBracket` at the rescaling
`rho = 3 * P_cd`.  That file was written to decide REALIZABILITY of a correlation
triple (`det Gram >= 0`); the same cubic at a different scaling decides TWO-SIDED
DOMINATION.  Five forks flagged the file as unexploited without finding the
connection, so the bridge is recorded explicitly here. -/

/-- **THE BRIDGE.**  Twenty-seven times the flat gap determinant is the elliptope
bracket of the tripled off-diagonal entries. -/
theorem twentySeven_mul_det_blockGapAt_eq_elliptopeBracket
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    (pick : Fin 3 → Fin 6) :
    27 * (blockGapAt form6 sixthWeight pick).det
      = elliptopeBracket (3 * form6 (pick 0) (pick 1)) (3 * form6 (pick 0) (pick 2))
          (3 * form6 (pick 1) (pick 2)) := by
  have h := twoHundredSixteen_mul_det_blockGapAt_of_flat hsymm hflat pick
  rw [elliptopeBracket]
  unfold flatPairEnergy flatTripleCross at h
  nlinarith [h]

/-- **A SHARP SUFFICIENT CELL, read off the landed elliptope bound.**  If every
off-diagonal entry of the triple has absolute value at most one sixth then the gap
determinant is nonnegative.  The constant one sixth is ATTAINED: at
`x = y = z = 1/6` with a negative cross term the determinant is exactly zero. -/
theorem det_blockGapAt_nonneg_of_abs_le_sixth
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    (pick : Fin 3 → Fin 6)
    (h01 : (form6 (pick 0) (pick 1)) ^ 2 ≤ 1 / 36)
    (h02 : (form6 (pick 0) (pick 2)) ^ 2 ≤ 1 / 36)
    (h12 : (form6 (pick 1) (pick 2)) ^ 2 ≤ 1 / 36) :
    0 ≤ (blockGapAt form6 sixthWeight pick).det := by
  have hb := elliptopeBracket_nonneg_of_sq_le_quarter
    (rhoFirst := 3 * form6 (pick 0) (pick 1)) (rhoSecond := 3 * form6 (pick 0) (pick 2))
    (rhoThird := 3 * form6 (pick 1) (pick 2)) (by nlinarith [h01]) (by nlinarith [h02])
    (by nlinarith [h12])
  have h := twentySeven_mul_det_blockGapAt_eq_elliptopeBracket hsymm hflat pick
  linarith

/-- The sharpness witness for the constant one sixth, at the scalar layer. -/
theorem elliptopeBracket_half_eq_zero : elliptopeBracket (1 / 2) (1 / 2) (-(1 / 2)) = 0 := by
  rw [elliptopeBracket]; norm_num

/-! ## 4. The block antidiagonal construction

`Gtz.orthogonalPairInvolution` is the `(4,2)` hollow involution `[[0, R], [R', 0]]`
with `R` in `O(2)`, and the corpus records that up to relabelling those are a copy of
`O(2)`.  The `(6,3)` analogue is built here for the first time.  Its Seidel matrix is
block antidiagonal with an orthogonal `3 x 3` corner, so the projection is
`(1/2) * (1 + S)` and the first three labels carry pairwise orthogonal atoms. -/

/-- Eighteen times the witness projection, as an integer-valued arithmetic function.
Matrix literals do not reduce past index two in this corpus, so the entries are given
by nested comparisons on `Fin.val`. -/
def orthoPairEntry (row col : ℕ) : ℤ :=
  if row = col then 9
  else if row < 3 then
    (if col < 3 then 0
     else if row = 0 then (if col = 3 then 8 else if col = 4 then -4 else 1)
     else if row = 1 then (if col = 3 then 1 else if col = 4 then 4 else 8)
     else (if col = 3 then -4 else if col = 4 then -7 else 4))
  else if col < 3 then
    (if col = 0 then (if row = 3 then 8 else if row = 4 then -4 else 1)
     else if col = 1 then (if row = 3 then 1 else if row = 4 then 4 else 8)
     else (if row = 3 then -4 else if row = 4 then -7 else 4))
  else 0

/-- The witness: a rank-three symmetric idempotent on six labels whose Seidel
involution is block antidiagonal with the rational orthogonal corner
`(1/9) * !![8, 1, -4; -4, 4, -7; 1, 8, 4]`. -/
noncomputable def orthoPairProjection : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun row col => (orthoPairEntry row.val col.val : ℝ) / 18

theorem orthoPairProjection_apply (row col : Fin 6) :
    orthoPairProjection row col = (orthoPairEntry row.val col.val : ℝ) / 18 := rfl

theorem orthoPairProjection_symm : orthoPairProjectionᵀ = orthoPairProjection := by
  ext row col
  rw [Matrix.transpose_apply, orthoPairProjection_apply, orthoPairProjection_apply]
  fin_cases row <;> fin_cases col <;> norm_num [orthoPairEntry]

theorem orthoPairProjection_mul_self : orthoPairProjection * orthoPairProjection
    = orthoPairProjection := by
  ext row col
  rw [Matrix.mul_apply, Fin.sum_univ_six]
  simp only [orthoPairProjection_apply]
  fin_cases row <;> fin_cases col <;> norm_num [orthoPairEntry]

/-- The witness is flat: every leverage is one half, so it lies on the crux
stratum. -/
theorem isFlatDiagonal_orthoPairProjection : IsFlatDiagonal orthoPairProjection := by
  intro label
  rw [orthoPairProjection_apply]
  fin_cases label <;> norm_num [orthoPairEntry]

theorem trace_orthoPairProjection : Matrix.trace orthoPairProjection = 3 := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_six, orthoPairProjection_apply]
  norm_num [orthoPairEntry]

/-- **No two atoms are parallel.**  A parallel pair would force the squared entry to
equal the product of the two diagonal entries, that is the integer entry to be plus
or minus nine, and no off-diagonal entry of the witness is. -/
theorem orthoPairProjection_no_parallel (row col : Fin 6) (hne : row ≠ col) :
    orthoPairProjection row col ^ 2
      ≠ orthoPairProjection row row * orthoPairProjection col col := by
  simp only [orthoPairProjection_apply]
  fin_cases row <;> fin_cases col <;> simp_all <;> norm_num [orthoPairEntry]

/-! ## 5. The refutation

The first three labels of the witness are pairwise orthogonal, so both invariants of
that triple vanish and BOTH gap blocks are `(1/3) * 1`. -/

/-- The decoupled selection. -/
def decoupledPick : Fin 3 → Fin 6 := fun slot => ⟨slot.val, by omega⟩

theorem decoupledPick_injective : Function.Injective decoupledPick := by
  intro a b hab
  have h : (decoupledPick a).val = (decoupledPick b).val := by rw [hab]
  simp only [decoupledPick] at h
  exact Fin.ext h

theorem flatPairEnergy_orthoPairProjection :
    flatPairEnergy orthoPairProjection decoupledPick = 0 := by
  unfold flatPairEnergy decoupledPick
  simp only [orthoPairProjection_apply]
  norm_num [orthoPairEntry]

theorem flatTripleCross_orthoPairProjection :
    flatTripleCross orthoPairProjection decoupledPick = 0 := by
  unfold flatTripleCross decoupledPick
  simp only [orthoPairProjection_apply]
  norm_num [orthoPairEntry]

/-- The primal gap determinant at the decoupled triple is exactly `1/27`, the
universal cap. -/
theorem det_blockGapAt_orthoPairProjection :
    (blockGapAt orthoPairProjection sixthWeight decoupledPick).det = 1 / 27 := by
  have h := twoHundredSixteen_mul_det_blockGapAt_of_flat orthoPairProjection_symm
    isFlatDiagonal_orthoPairProjection decoupledPick
  rw [flatPairEnergy_orthoPairProjection, flatTripleCross_orthoPairProjection] at h
  linarith

/-- The dual gap determinant is the same number, because the cross term vanishes. -/
theorem det_blockGapAt_one_sub_orthoPairProjection :
    (blockGapAt (1 - orthoPairProjection) sixthWeight decoupledPick).det = 1 / 27 := by
  have h := twoHundredSixteen_mul_det_blockGapAt_one_sub_of_flat orthoPairProjection_symm
    isFlatDiagonal_orthoPairProjection decoupledPick_injective
  rw [flatPairEnergy_orthoPairProjection, flatTripleCross_orthoPairProjection] at h
  linarith

/-- Every entry of the decoupled gap block is that of `(1/3) * 1`. -/
theorem blockGapAt_orthoPairProjection_eq :
    blockGapAt orthoPairProjection sixthWeight decoupledPick
      = (1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b
  rcases eq_or_ne a b with rfl | hne
  · rw [blockGapAt_apply_diag, isFlatDiagonal_orthoPairProjection, sixthWeight]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    norm_num
  · rw [blockGapAt_apply_offDiag _ _ _ hne]
    rw [Matrix.smul_apply, Matrix.one_apply_ne hne]
    unfold decoupledPick
    simp only [orthoPairProjection_apply, smul_eq_mul, mul_zero]
    fin_cases a <;> fin_cases b <;> simp_all <;> norm_num [orthoPairEntry]

/-- The dual block agrees with the primal one, because the off-diagonal entries that
the involution would negate are all zero. -/
theorem blockGapAt_one_sub_orthoPairProjection_eq :
    blockGapAt (1 - orthoPairProjection) sixthWeight decoupledPick
      = (1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b
  rcases eq_or_ne a b with rfl | hne
  · rw [blockGapAt_one_sub_diag_of_flat isFlatDiagonal_orthoPairProjection,
      blockGapAt_apply_diag, isFlatDiagonal_orthoPairProjection, sixthWeight]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    norm_num
  · rw [blockGapAt_one_sub_offDiag _ _ decoupledPick_injective hne,
      blockGapAt_apply_offDiag _ _ _ hne]
    rw [Matrix.smul_apply, Matrix.one_apply_ne hne]
    unfold decoupledPick
    simp only [orthoPairProjection_apply, smul_eq_mul, mul_zero, neg_eq_zero]
    fin_cases a <;> fin_cases b <;> simp_all <;> norm_num [orthoPairEntry]

/-- A positive multiple of the identity is positive definite. -/
theorem posDef_third_smul_one :
    ((1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef := by
  refine Matrix.PosDef.smul ?_ (by norm_num : (0:ℝ) < 1/3)
  exact Matrix.PosDef.one

/-- **THE REFUTATION.**  Two-sided domination DOES occur on the flat stratum.  Both
gap blocks of the decoupled triple are positive definite, so the ceiling hoped for by
the complementation involution is FALSE. -/
theorem posDef_both_orthoPairProjection :
    (blockGapAt orthoPairProjection sixthWeight decoupledPick).PosDef
      ∧ (blockGapAt (1 - orthoPairProjection) sixthWeight decoupledPick).PosDef := by
  constructor
  · rw [blockGapAt_orthoPairProjection_eq]; exact posDef_third_smul_one
  · rw [blockGapAt_one_sub_orthoPairProjection_eq]; exact posDef_third_smul_one

/-- Stated as the existence the ceiling would have had to exclude. -/
theorem exists_flat_posDef_both :
    ∃ form6 : Matrix (Fin 6) (Fin 6) ℝ, form6ᵀ = form6 ∧ form6 * form6 = form6 ∧
      IsFlatDiagonal form6 ∧ ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        (blockGapAt form6 sixthWeight pick).PosDef
          ∧ (blockGapAt (1 - form6) sixthWeight pick).PosDef :=
  ⟨orthoPairProjection, orthoPairProjection_symm, orthoPairProjection_mul_self,
    isFlatDiagonal_orthoPairProjection, decoupledPick, decoupledPick_injective,
    posDef_both_orthoPairProjection⟩

/-- **The flat stratum is NOT uniformly hard.**  The graphic point admits no
two-sided triple (`Gtz.not_posDef_both_kfourEdgeProjection`) while the witness does,
and both are flat.  So flatness alone does not characterize the crux, and the
campaign's identification of the equal-share locus with the hard case is wrong. -/
theorem flat_stratum_not_uniform :
    (∃ form6 : Matrix (Fin 6) (Fin 6) ℝ, IsFlatDiagonal form6 ∧
        ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
          (blockGapAt form6 sixthWeight pick).PosDef
            ∧ (blockGapAt (1 - form6) sixthWeight pick).PosDef)
      ∧ (∀ pick : Fin 3 → Fin 6, Function.Injective pick →
          ¬((blockGapAt kfourEdgeProjection sixthWeight pick).PosDef
            ∧ (blockGapAt (1 - kfourEdgeProjection) sixthWeight pick).PosDef)) := by
  refine ⟨⟨orthoPairProjection, isFlatDiagonal_orthoPairProjection, decoupledPick,
    decoupledPick_injective, posDef_both_orthoPairProjection⟩, ?_⟩
  intro pick hinj
  exact not_posDef_both_kfourEdgeProjection hinj

/-! ## 6. Reaching the registry

The gap block is definitionally the block that decides strict domination, so a
selection rule stated in these coordinates lands on the five on-path obligations
through the shipped bridge. -/

/-- The decoupled cell: a triple whose energy and absolute cross term are small
enough has a positive definite gap block.  This is the sign-free margin condition
written in the two flat invariants, with no division. -/
theorem posDef_blockGapAt_of_flat_of_small
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    (pick : Fin 3 → Fin 6)
    (henergy : 72 * flatPairEnergy form6 pick + 432 * |flatTripleCross form6 pick| < 8)
    (hpair : ∀ a b : Fin 3, a ≠ b → (form6 (pick a) (pick b)) ^ 2 < 1 / 9) :
    (blockGapAt form6 sixthWeight pick).PosDef := by
  have hdet : 0 < (blockGapAt form6 sixthWeight pick).det := by
    have h := twoHundredSixteen_mul_det_blockGapAt_of_flat hsymm hflat pick
    have habs : -|flatTripleCross form6 pick| ≤ flatTripleCross form6 pick := neg_abs_le _
    linarith
  have hsymmB : (blockGapAt form6 sixthWeight pick)ᵀ = blockGapAt form6 sixthWeight pick :=
    blockGapAt_transpose hsymm _ _
  have hB : ∀ a b : Fin 3, blockGapAt form6 sixthWeight pick b a
      = blockGapAt form6 sixthWeight pick a b := by
    intro a b; conv_lhs => rw [← hsymmB]
    rfl
  have hd := blockGapAt_flat_diag hflat pick
  rw [Matrix.det_fin_three, hB 0 1, hB 0 2, hB 1 2] at hdet
  refine (posDef_finThree_iff_leadingMinors _ hsymmB).mpr ⟨?_, ?_, ?_⟩
  · rw [hd 0]; norm_num
  · rw [hd 0, hd 1, blockGapAt_apply_offDiag _ _ _ (by decide : (0 : Fin 3) ≠ 1)]
    have := hpair 0 1 (by decide)
    linarith
  · rw [hd 0, hd 1, hd 2] at hdet ⊢
    ring_nf at hdet ⊢
    linarith

/-- **THE PLUCKER WEIGHT IN THE SAME TWO INVARIANTS.**  The determinantal measure
that carries the mass floor lane is another value of the same pair, so the mass lane
and the gap lane read one point of the plane `(energy, cross)`. -/
theorem det_submatrix_of_flat
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    (pick : Fin 3 → Fin 6) :
    (form6.submatrix pick pick).det
      = 1 / 8 - flatPairEnergy form6 pick / 2 + 2 * flatTripleCross form6 pick := by
  have hs : ∀ a b : Fin 6, form6 b a = form6 a b := by
    intro a b; conv_lhs => rw [← hsymm]
    rfl
  rw [Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply]
  rw [hflat (pick 0), hflat (pick 1), hflat (pick 2), hs (pick 0) (pick 1),
    hs (pick 0) (pick 2), hs (pick 1) (pick 2)]
  unfold flatPairEnergy flatTripleCross
  ring

/-- **AN INDEPENDENT PROOF OF THE FLAT THRESHOLD LAW.**  Subtracting the two
determinant formulas cancels the cross term identically and leaves `19 - 36 * energy`.
The sibling lane derived that from threshold vocabulary.  Here it falls out of two
determinant expansions with no threshold anywhere, which is a genuinely different
proof of the same law. -/
theorem twoHundredSixteen_mul_det_sub_det_of_flat
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    (pick : Fin 3 → Fin 6) :
    216 * ((form6.submatrix pick pick).det - (blockGapAt form6 sixthWeight pick).det)
      = 19 - 36 * flatPairEnergy form6 pick := by
  have h1 := det_submatrix_of_flat hsymm hflat pick
  have h2 := twoHundredSixteen_mul_det_blockGapAt_of_flat hsymm hflat pick
  rw [h1]; linarith

/-- **THE COMPLETE DECISION PROCEDURE ON THE FLAT STRATUM.**  At a flat symmetric
form and uniform weight, strict domination at a triple is EXACTLY one square bound
plus one cubic inequality in the two invariants.  Division free, root free, and an
equivalence rather than a cell. -/
theorem posDef_blockGapAt_of_flat_iff
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    (pick : Fin 3 → Fin 6) :
    (blockGapAt form6 sixthWeight pick).PosDef
      ↔ (form6 (pick 0) (pick 1)) ^ 2 < 1 / 9
        ∧ 0 < 8 - 72 * flatPairEnergy form6 pick + 432 * flatTripleCross form6 pick := by
  have hsymmB : (blockGapAt form6 sixthWeight pick)ᵀ = blockGapAt form6 sixthWeight pick :=
    blockGapAt_transpose hsymm _ _
  have hB : ∀ a b : Fin 3, blockGapAt form6 sixthWeight pick b a
      = blockGapAt form6 sixthWeight pick a b := by
    intro a b; conv_lhs => rw [← hsymmB]
    rfl
  have hd := blockGapAt_flat_diag hflat pick
  have hlaw := twoHundredSixteen_mul_det_blockGapAt_of_flat hsymm hflat pick
  have hoff : blockGapAt form6 sixthWeight pick 0 1 = form6 (pick 0) (pick 1) :=
    blockGapAt_apply_offDiag _ _ _ (by decide)
  rw [posDef_finThree_iff_leadingMinors _ hsymmB]
  constructor
  · rintro ⟨-, hminor, hthird⟩
    refine ⟨?_, ?_⟩
    · rw [hd 0, hd 1, hoff] at hminor; linarith
    · have hdet : 0 < (blockGapAt form6 sixthWeight pick).det := by
        rw [Matrix.det_fin_three, hB 0 1, hB 0 2, hB 1 2]
        rw [hd 0, hd 1, hd 2] at hthird ⊢
        ring_nf at hthird ⊢
        linarith
      linarith
  · rintro ⟨hsq, hcubic⟩
    have hdet : 0 < (blockGapAt form6 sixthWeight pick).det := by linarith
    rw [Matrix.det_fin_three, hB 0 1, hB 0 2, hB 1 2] at hdet
    refine ⟨by rw [hd 0]; norm_num, ?_, ?_⟩
    · rw [hd 0, hd 1, hoff]; linarith
    · rw [hd 0, hd 1, hd 2] at hdet ⊢
      ring_nf at hdet ⊢
      linarith

/-- The witness passes the mass floor that the graphic point refutes: its decoupled
triple carries Plucker weight one eighth against the refuted level `17/270`. -/
theorem det_submatrix_orthoPairProjection :
    (orthoPairProjection.submatrix decoupledPick decoupledPick).det = 1 / 8 := by
  rw [det_submatrix_of_flat orthoPairProjection_symm isFlatDiagonal_orthoPairProjection,
    flatPairEnergy_orthoPairProjection, flatTripleCross_orthoPairProjection]
  norm_num

/-- **THE MAXIMIZER, AS AN EQUIVALENCE.**  The sign-free margin of a flat triple
attains the universal cap exactly when the triple is decoupled. -/
theorem min_det_eq_one_twentySeventh_iff
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick) :
    min (blockGapAt form6 sixthWeight pick).det
        (blockGapAt (1 - form6) sixthWeight pick).det = 1 / 27
      ↔ flatPairEnergy form6 pick = 0 ∧ flatTripleCross form6 pick = 0 := by
  constructor
  · intro heq
    exact ⟨flatPairEnergy_eq_zero_of_min_det_eq hsymm hflat hinj heq,
      flatTripleCross_eq_zero_of_min_det_eq hsymm hflat hinj heq⟩
  · rintro ⟨he, hp⟩
    have h := twoHundredSixteen_mul_min_det_of_flat hsymm hflat hinj
    rw [he, hp] at h
    simp only [abs_zero] at h
    linarith

/-- The decoupled triple of the witness attains the cap. -/
theorem min_det_orthoPairProjection :
    min (blockGapAt orthoPairProjection sixthWeight decoupledPick).det
      (blockGapAt (1 - orthoPairProjection) sixthWeight decoupledPick).det = 1 / 27 :=
  (min_det_eq_one_twentySeventh_iff orthoPairProjection_symm
    isFlatDiagonal_orthoPairProjection decoupledPick_injective).mpr
    ⟨flatPairEnergy_orthoPairProjection, flatTripleCross_orthoPairProjection⟩

/-! ### The complementary triple

Two laws proved elsewhere for a hollow involution say that the pairing energy is
invariant under complementation of the triple and the cross term exactly reverses
sign.  Fed into the two determinant formulas above they collapse the whole
involution: the DUAL gap block at a triple has the determinant of the PRIMAL gap
block at the COMPLEMENTARY triple.  The laws are taken as hypotheses here so this
composes with either vocabulary without importing one. -/

/-- **THE COMPLEMENTATION COLLAPSE.**  The dual side at a triple is the primal side
at its complement.  So the complementation involution on gap blocks is the
complementation involution on triples, and the twenty triples pair into ten. -/
theorem det_blockGapAt_one_sub_eq_det_blockGapAt_compl
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    {pick pickCompl : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (henergy : flatPairEnergy form6 pickCompl = flatPairEnergy form6 pick)
    (hcross : flatTripleCross form6 pickCompl = -flatTripleCross form6 pick) :
    (blockGapAt (1 - form6) sixthWeight pick).det
      = (blockGapAt form6 sixthWeight pickCompl).det := by
  have h1 := twoHundredSixteen_mul_det_blockGapAt_one_sub_of_flat hsymm hflat hinj
  have h2 := twoHundredSixteen_mul_det_blockGapAt_of_flat hsymm hflat pickCompl
  rw [henergy, hcross] at h2
  linarith

/-- **THE SIGN-FREE MARGIN IS A STATEMENT ABOUT TEN PAIRS.**  It is the minimum of
the two ORDINARY gap determinants at a triple and its complement, with no
complementation of the form anywhere.  The campaign's central quantity therefore
never needed the dual projection at all. -/
theorem min_det_eq_min_over_complementary_pair
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    {pick pickCompl : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (henergy : flatPairEnergy form6 pickCompl = flatPairEnergy form6 pick)
    (hcross : flatTripleCross form6 pickCompl = -flatTripleCross form6 pick) :
    min (blockGapAt form6 sixthWeight pick).det
        (blockGapAt (1 - form6) sixthWeight pick).det
      = min (blockGapAt form6 sixthWeight pick).det
        (blockGapAt form6 sixthWeight pickCompl).det := by
  rw [det_blockGapAt_one_sub_eq_det_blockGapAt_compl hsymm hflat hinj henergy hcross]

/-- **THE REFRAMING.**  A sign-blind certificate fires at a triple exactly when that
triple AND its complement both dominate.  So the class is not blind to a sign, it is
demanding a pair — which is why it is silent wherever the two halves disagree. -/
theorem posDef_both_iff_det_pos_pair
    {form6 : Matrix (Fin 6) (Fin 6) ℝ} (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6)
    {pick pickCompl : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (henergy : flatPairEnergy form6 pickCompl = flatPairEnergy form6 pick)
    (hcross : flatTripleCross form6 pickCompl = -flatTripleCross form6 pick) :
    (0 < (blockGapAt form6 sixthWeight pick).det
        ∧ 0 < (blockGapAt (1 - form6) sixthWeight pick).det)
      ↔ (0 < (blockGapAt form6 sixthWeight pick).det
        ∧ 0 < (blockGapAt form6 sixthWeight pickCompl).det) := by
  rw [det_blockGapAt_one_sub_eq_det_blockGapAt_compl hsymm hflat hinj henergy hcross]

/-- At the witness both hypotheses hold outright, because the complementary triple is
the second orthogonal triple and both invariants vanish on each side. -/
theorem flatPairEnergy_orthoPairProjection_compl :
    flatPairEnergy orthoPairProjection (fun slot => ⟨slot.val + 3, by omega⟩) = 0 := by
  unfold flatPairEnergy
  simp only [orthoPairProjection_apply]
  norm_num [orthoPairEntry]

theorem flatTripleCross_orthoPairProjection_compl :
    flatTripleCross orthoPairProjection (fun slot => ⟨slot.val + 3, by omega⟩) = 0 := by
  unfold flatTripleCross
  simp only [orthoPairProjection_apply]
  norm_num [orthoPairEntry]

/-- **THE OBLIGATION BRIDGE.**  A selection rule in the flat invariants that fires at
every primitive design carries all five on-path obligations, through the shipped
`Gtz.allFiveOnPath_of_blockGapAt`. -/
theorem allFiveOnPath_of_flatInvariantCell
    (hexists : ∀ D : WeightedDesign 6 3, IsPrimitiveDesign D →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        (blockGapAt (projectionOfDesign D) D.weight pick).PosDef) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  allFiveOnPath_of_blockGapAt hexists

/-- **THE FIRST ON-PATH OBLIGATION, reached explicitly.**  A1 is the line-free
stratum, the one the registry sequences last and the one carrying four moduli.  A
selection rule in the gap-block coordinates discharges it on its own. -/
theorem baseTripleTight_of_flatInvariantCell
    (hexists : ∀ D : WeightedDesign 6 3, IsPrimitiveDesign D →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        (blockGapAt (projectionOfDesign D) D.weight pick).PosDef) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual :=
  (allFiveOnPath_of_flatInvariantCell hexists).1

/-- The `M(K4)` obligation, the moduli-zero end of the same chain. -/
theorem kFourKnifeBand_of_flatInvariantCell
    (hexists : ∀ D : WeightedDesign 6 3, IsPrimitiveDesign D →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        (blockGapAt (projectionOfDesign D) D.weight pick).PosDef) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  (allFiveOnPath_of_flatInvariantCell hexists).2.2.2.2

/-- **The flat-stratum reading of the selection hypothesis.**  At a flat design the
antecedent of the obligation bridge becomes one polynomial inequality per design, by
the decision procedure above.  So on that stratum the five obligations reduce to a
statement with no matrix, no eigenvalue and no determinant in it. -/
theorem blockGapAt_posDef_of_flat_design
    (D : WeightedDesign 6 3) (hflat : IsFlatDiagonal (projectionOfDesign D))
    (huniform : D.weight = sixthWeight) (pick : Fin 3 → Fin 6)
    (hsq : (projectionOfDesign D (pick 0) (pick 1)) ^ 2 < 1 / 9)
    (hcubic : 0 < 8 - 72 * flatPairEnergy (projectionOfDesign D) pick
      + 432 * flatTripleCross (projectionOfDesign D) pick) :
    (blockGapAt (projectionOfDesign D) D.weight pick).PosDef := by
  rw [huniform]
  exact (posDef_blockGapAt_of_flat_iff (projectionOfDesign_transpose D) hflat pick).mpr
    ⟨hsq, hcubic⟩

end Gtz

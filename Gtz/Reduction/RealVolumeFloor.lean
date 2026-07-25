/-
# The rank floor `α_k(ℝ) ≥ 1/k` — a lower bound with no dependence on the size

GTZ asks for a `k`-subset with `S_C ⪰ I`.  Nothing in the repo lower-bounds the
best achievable level at all: the classical maximal-volume theory gives
`σ_min² ≥ 1/(k(m−k)+1)`, which DECAYS with the number of atoms and therefore says
nothing uniform in `m`.  This file proves the first size-free floor:

    every weighted `(m, k)`-design has a `k`-subset `C` with `S_C ⪰ (1/k)·I`,

for every `m` and every `k`, with no hypothesis whatsoever.  Together with the
trivial ceiling (`Dominates` means level `1`) this brackets the sharp real
constant: `1/k ≤ α_k(ℝ) ≤ 1`.

## Where the size-independence comes from

Classically one counts the Frobenius norm of the solve matrix `B = A·A_pick⁻¹`
row by row: `k` selected rows contribute `1` each and `m−k` unselected rows
contribute at most `k` each, giving `‖B‖_F² ≤ k(m−k)+k` — the count is over ALL
rows, so the size enters and never leaves.

The design's weights kill it.  At a maximal-volume pick every solve coefficient
is in `[−1, 1]` (`abs_solveMatrix_le_one_of_maximalVolume`, on the unselected
rows, and `solveMatrix_submatrix_pick`, on the selected ones), so EVERY row
satisfies `‖B_r‖² ≤ k` — one bound, uniform in `r`.  Parseval then averages the
rows against the weights instead of summing them, and `Σ_c t_c = 1` collapses the
row count to a single factor of `k`:

    |x|²  =  Σ_c t_c (g_c · x)²          (Parseval, `dotProduct_self_eq_sum_weight_mul_sq`)
          ≤  Σ_c t_c · ‖B_c‖² · (xᵀ S_C x)   (Cauchy–Schwarz on `g_c = Σ_j B_cj g_{c_j}`)
          ≤  k · (xᵀ S_C x).

Both `m` and the individual weights are gone.  The measured content of the middle
line is the exact identity `Σ_c t_c ‖B_c‖² = tr(S_C⁻¹)`, verified numerically to
80 digits; the mechanized chain only needs the inequality.

## The pick must be maximal-volume for the UNSCALED atoms

`ProjectionForm` works with the scaled frame `V` (rows `√t_c · g_c`), whose
columns are orthonormal, and `MaximalVolume`'s existence lemma is stated there.
But the `[−1, 1]` bound applies to the solve matrix of whatever matrix was
maximized, and the chain above needs it for the UNSCALED system `g_c = Σ_j B_cj
g_{c_j}`.  Maximizing the wrong determinant breaks the bound badly: measured
`max |B_unscaled| = 580` at the pick maximizing the scaled volume, against the
exact bound `1` at the pick maximizing the unscaled one.  So the file maximizes
`|det|` over the unscaled atoms and uses the scaled frame only to supply a
NONSINGULAR pick (`exists_injective_pick_det_atomRowMatrix_ne_zero`), which is
scale-invariant because the two selected blocks differ by a positive diagonal.
`MaximalVolume`'s own `exists_maximalVolume_pick` cannot be reused directly for
the same reason — it derives its witness from Pythagoras, which needs orthonormal
columns — so `exists_maximalVolumePick_of_witness` restates it with the witness
as a hypothesis.

## Sharpness

`1/k` is essentially attained BY THIS SELECTION RULE: adversarial search drives
`k·λ_min` at the maximal-volume pick down to `1.004` at `(5,2)` and `1.075` at
`(7,3)`, the extremal configurations being the ones where the selected set
carries vanishing weight.  That is exactly what the free sharpening
`gtzWeightedFloor_selected_weight` says — the floor improves to
`1/(k − (k−1)·t(C))`, and degrades to `1/k` precisely as `t(C) → 0`.

`1/k` is NOT the sharp constant `α_k(ℝ)` of the problem: at `k = 2` this file
gives `1/2` where `gtz_rank_two` gives the truth `1`.  The gap is a defect of the
maximal-volume SELECTION RULE, not of the estimate — on the same extremal designs
the best subset achieves level `1.00003`.  What the floor buys is that it holds
at every rank, unconditionally, where GTZ itself is open from `k = 3` on.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.MaximalVolume

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The unscaled atoms as one matrix -/

/-- The design's atoms as the rows of one `m × k` matrix — the object whose row
selections are being volume-maximized.  Unlike `scaledAtomRows` its columns are
NOT orthonormal; that is the point (see the header). -/
def atomRowMatrix (D : WeightedDesign m k) : Matrix (Fin m) (Fin k) ℝ :=
  Matrix.of fun atomIndex coord => D.atom atomIndex coord

/-- A row of the atom matrix is the atom. -/
theorem atomRowMatrix_row (D : WeightedDesign m k) (atomIndex : Fin m) :
    atomRowMatrix D atomIndex = D.atom atomIndex := rfl

/-- A selected row of the atom matrix is the selected atom. -/
theorem selectedFrameRows_atomRowMatrix (D : WeightedDesign m k) (pick : Fin k → Fin m)
    (selectedIndex : Fin k) :
    selectedFrameRows (atomRowMatrix D) pick selectedIndex = D.atom (pick selectedIndex) := rfl

/-- **Scaling is a positive diagonal congruence on selections**: the scaled
selected block is the square-rooted weight diagonal times the unscaled one.  This
is why nonsingularity of a pick does not depend on which of the two matrices is
being looked at. -/
theorem selectedFrameRows_scaledAtomRows (D : WeightedDesign m k) (pick : Fin k → Fin m) :
    selectedFrameRows (scaledAtomRows D) pick
      = sqrtWeightDiagonal D pick * selectedFrameRows (atomRowMatrix D) pick := by
  ext rowIndex colIndex
  rw [sqrtWeightDiagonal, Matrix.diagonal_mul]
  rfl

/-- **Some selection of the unscaled atoms is nonsingular.**  Pythagoras applies
to the scaled frame, whose columns are orthonormal by Parseval; the positive
diagonal then transfers the nonvanishing determinant to the unscaled block. -/
theorem exists_injective_pick_det_atomRowMatrix_ne_zero (D : WeightedDesign m k) :
    ∃ pick : Fin k → Fin m,
      Function.Injective pick ∧ (selectedFrameRows (atomRowMatrix D) pick).det ≠ 0 := by
  obtain ⟨pick, hinj, hscaledDet⟩ :=
    exists_injective_pick_det_ne_zero (scaledAtomRows D) (transpose_mul_scaledAtomRows D)
  refine ⟨pick, hinj, fun hzero => hscaledDet ?_⟩
  rw [selectedFrameRows_scaledAtomRows, Matrix.det_mul, hzero, mul_zero]

/-! ## A maximal-volume selection of an arbitrary frame -/

/-- **The maximal-volume selection, from a nonsingular witness.**  Same statement
as `exists_maximalVolume_pick`, with the witness supplied instead of derived: the
committed version obtains it from Pythagoras and therefore needs orthonormal
columns, which the unscaled atom matrix does not have. -/
theorem exists_maximalVolumePick_of_witness {frameSize selectionRank : ℕ}
    (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    {witnessPick : Fin selectionRank → Fin frameSize}
    (hwitnessInj : Function.Injective witnessPick)
    (hwitnessDet : (selectedFrameRows frame witnessPick).det ≠ 0) :
    ∃ pick : Fin selectionRank → Fin frameSize, Function.Injective pick ∧
      (selectedFrameRows frame pick).det ≠ 0 ∧
      ∀ other : Fin selectionRank → Fin frameSize, Function.Injective other →
        |(selectedFrameRows frame other).det| ≤ |(selectedFrameRows frame pick).det| := by
  classical
  set injectivePicks : Finset (Fin selectionRank → Fin frameSize) :=
    Finset.univ.filter fun pick => Function.Injective pick with hpicksDef
  have hwitnessMem : witnessPick ∈ injectivePicks := by
    rw [hpicksDef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hwitnessInj⟩
  obtain ⟨bestPick, hbestMem, hbest⟩ :=
    Finset.exists_max_image injectivePicks
      (fun pick => |(selectedFrameRows frame pick).det|) ⟨witnessPick, hwitnessMem⟩
  have hbestInj : Function.Injective bestPick := by
    rw [hpicksDef, Finset.mem_filter] at hbestMem
    exact hbestMem.2
  refine ⟨bestPick, hbestInj, ?_, fun other hotherInj => ?_⟩
  · intro hzero
    have hwitnessLe := hbest witnessPick hwitnessMem
    rw [hzero, abs_zero] at hwitnessLe
    exact absurd (abs_nonpos_iff.mp hwitnessLe) hwitnessDet
  · exact hbest other (by rw [hpicksDef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hotherInj⟩)

/-- **Maximality bounds EVERY solve coefficient by one**, selected rows included.
On the unselected rows this is `abs_solveMatrix_le_one_of_maximalVolume`; on the
selected rows the solve matrix is the identity, whose entries are `0` and `1`.
The uniformity over all rows is what lets Parseval average the rows below. -/
theorem abs_solveMatrix_le_one_of_maximalVolume_row {frameSize selectionRank : ℕ}
    (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize) (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows frame pick).det)
    (hmax : ∀ other : Fin selectionRank → Fin frameSize, Function.Injective other →
      |(selectedFrameRows frame other).det| ≤ |(selectedFrameRows frame pick).det|)
    (rowIndex : Fin frameSize) (colIndex : Fin selectionRank) :
    |solveMatrix frame pick rowIndex colIndex| ≤ 1 := by
  classical
  by_cases hselected : ∃ selectedIndex, pick selectedIndex = rowIndex
  · obtain ⟨selectedIndex, hselectedEq⟩ := hselected
    have hidentity := congrArg
      (fun block : Matrix (Fin selectionRank) (Fin selectionRank) ℝ => block selectedIndex colIndex)
      (solveMatrix_submatrix_pick frame pick hunit)
    simp only [Matrix.submatrix_apply, id] at hidentity
    rw [← hselectedEq, hidentity]
    rcases eq_or_ne selectedIndex colIndex with hdiag | hoff
    · rw [hdiag, Matrix.one_apply_eq, abs_one]
    · rw [Matrix.one_apply_ne hoff, abs_zero]
      norm_num
  · push_neg at hselected
    exact abs_solveMatrix_le_one_of_maximalVolume frame pick hinj hunit hmax rowIndex
      hselected colIndex

/-! ## Quadratic forms of atoms, of Parseval, and of a selection -/

/-- The quadratic form of an atom is the squared projection: `xᵀ(g gᵀ)x = ⟨g, x⟩²`. -/
theorem dotProduct_atomMatrix_mulVec (g x : Fin k → ℝ) :
    x ⬝ᵥ (atomMatrix g *ᵥ x) = (g ⬝ᵥ x) ^ 2 := by
  simp only [atomMatrix, Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply, pow_two,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun leftCoord _ => Finset.sum_congr rfl fun rightCoord _ => by ring

/-- **Parseval as a quadratic form**: the squared length of any direction is the
weighted average of its squared atom projections. -/
theorem dotProduct_self_eq_sum_weight_mul_sq (D : WeightedDesign m k) (x : Fin k → ℝ) :
    x ⬝ᵥ x = ∑ atomIndex, D.weight atomIndex * (D.atom atomIndex ⬝ᵥ x) ^ 2 := by
  have hidentity : x ⬝ᵥ ((1 : Matrix (Fin k) (Fin k) ℝ) *ᵥ x) = x ⬝ᵥ x := by
    rw [Matrix.one_mulVec]
  rw [← hidentity, ← D.isParseval, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]

/-- The quadratic form of a selection's atom sum, enumerated along the pick. -/
theorem dotProduct_subsetSum_mulVec (D : WeightedDesign m k) (pick : Fin k → Fin m)
    (hinj : Function.Injective pick) (x : Fin k → ℝ) :
    x ⬝ᵥ (subsetSum D (Finset.image pick Finset.univ) *ᵥ x)
      = ∑ selectedIndex, (D.atom (pick selectedIndex) ⬝ᵥ x) ^ 2 := by
  classical
  rw [subsetSum, Finset.sum_image fun left _ right _ hlr => hinj hlr, Matrix.sum_mulVec,
    dotProduct_sum]
  exact Finset.sum_congr rfl fun selectedIndex _ => dotProduct_atomMatrix_mulVec _ _

/-- The selection's quadratic form is nonnegative — it is a sum of squares. -/
theorem sum_sq_selected_nonneg (D : WeightedDesign m k) (pick : Fin k → Fin m) (x : Fin k → ℝ) :
    0 ≤ ∑ selectedIndex, (D.atom (pick selectedIndex) ⬝ᵥ x) ^ 2 :=
  Finset.sum_nonneg fun selectedIndex _ => sq_nonneg _

/-- The atom sum of any subset is symmetric. -/
theorem transpose_subsetSum (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    (subsetSum D selected)ᵀ = subsetSum D selected := by
  rw [subsetSum, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [atomMatrix, Matrix.transpose_vecMulVec]

/-! ## The row estimate and the floor -/

/-- **The row estimate.**  At a maximal-volume pick every atom's squared
projection is at most `k` times the selection's quadratic form: expand the atom
in the selected basis, apply Cauchy–Schwarz, and use that each of the `k`
coefficients has modulus at most one. -/
theorem sq_dotProduct_le_rank_mul_selected (D : WeightedDesign m k) (pick : Fin k → Fin m)
    (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (atomRowMatrix D) pick).det)
    (hmax : ∀ other : Fin k → Fin m, Function.Injective other →
      |(selectedFrameRows (atomRowMatrix D) other).det|
        ≤ |(selectedFrameRows (atomRowMatrix D) pick).det|)
    (atomIndex : Fin m) (x : Fin k → ℝ) :
    (D.atom atomIndex ⬝ᵥ x) ^ 2
      ≤ (k : ℝ) * ∑ selectedIndex, (D.atom (pick selectedIndex) ⬝ᵥ x) ^ 2 := by
  set solveCoefficients := solveMatrix (atomRowMatrix D) pick with hsolveDef
  have hexpansion : D.atom atomIndex
      = ∑ selectedIndex, solveCoefficients atomIndex selectedIndex • D.atom (pick selectedIndex) :=
    frameRow_eq_solveCombination (atomRowMatrix D) pick hunit atomIndex
  have hprojection : D.atom atomIndex ⬝ᵥ x
      = ∑ selectedIndex,
          solveCoefficients atomIndex selectedIndex * (D.atom (pick selectedIndex) ⬝ᵥ x) := by
    conv_lhs => rw [hexpansion]
    rw [sum_dotProduct]
    exact Finset.sum_congr rfl fun selectedIndex _ => by rw [smul_dotProduct, smul_eq_mul]
  have hcauchySchwarz := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun selectedIndex => solveCoefficients atomIndex selectedIndex)
    (fun selectedIndex => D.atom (pick selectedIndex) ⬝ᵥ x)
  have hcoefficientBound :
      ∑ selectedIndex, solveCoefficients atomIndex selectedIndex ^ 2 ≤ (k : ℝ) := by
    have hentrywise : ∀ selectedIndex ∈ (Finset.univ : Finset (Fin k)),
        solveCoefficients atomIndex selectedIndex ^ 2 ≤ (1 : ℝ) := fun selectedIndex _ =>
      (sq_le_one_iff_abs_le_one _).mpr
        (abs_solveMatrix_le_one_of_maximalVolume_row (atomRowMatrix D) pick hinj hunit hmax
          atomIndex selectedIndex)
    calc ∑ selectedIndex, solveCoefficients atomIndex selectedIndex ^ 2
        ≤ ∑ _selectedIndex : Fin k, (1 : ℝ) := Finset.sum_le_sum hentrywise
      _ = (k : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  calc (D.atom atomIndex ⬝ᵥ x) ^ 2
      = (∑ selectedIndex,
          solveCoefficients atomIndex selectedIndex
            * (D.atom (pick selectedIndex) ⬝ᵥ x)) ^ 2 := by rw [hprojection]
    _ ≤ (∑ selectedIndex, solveCoefficients atomIndex selectedIndex ^ 2)
          * ∑ selectedIndex, (D.atom (pick selectedIndex) ⬝ᵥ x) ^ 2 := hcauchySchwarz
    _ ≤ (k : ℝ) * ∑ selectedIndex, (D.atom (pick selectedIndex) ⬝ᵥ x) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefficientBound (sum_sq_selected_nonneg D pick x)

/-- **Parseval averages the row estimate.**  Summing the row estimate against the
weights, the total weight `1` replaces the row count: `|x|² ≤ k · xᵀ S_C x`, with
neither the size nor the individual weights surviving. -/
theorem dotProduct_self_le_rank_mul_selected (D : WeightedDesign m k) (pick : Fin k → Fin m)
    (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (atomRowMatrix D) pick).det)
    (hmax : ∀ other : Fin k → Fin m, Function.Injective other →
      |(selectedFrameRows (atomRowMatrix D) other).det|
        ≤ |(selectedFrameRows (atomRowMatrix D) pick).det|)
    (x : Fin k → ℝ) :
    x ⬝ᵥ x ≤ (k : ℝ) * ∑ selectedIndex, (D.atom (pick selectedIndex) ⬝ᵥ x) ^ 2 := by
  rw [dotProduct_self_eq_sum_weight_mul_sq D x]
  calc ∑ atomIndex, D.weight atomIndex * (D.atom atomIndex ⬝ᵥ x) ^ 2
      ≤ ∑ atomIndex, D.weight atomIndex
          * ((k : ℝ) * ∑ selectedIndex, (D.atom (pick selectedIndex) ⬝ᵥ x) ^ 2) :=
        Finset.sum_le_sum fun atomIndex _ =>
          mul_le_mul_of_nonneg_left
            (sq_dotProduct_le_rank_mul_selected D pick hinj hunit hmax atomIndex x)
            (D.weight_pos atomIndex).le
    _ = (k : ℝ) * ∑ selectedIndex, (D.atom (pick selectedIndex) ⬝ᵥ x) ^ 2 := by
        rw [← Finset.sum_mul, D.weight_sum_one, one_mul]

/-- The floor statement at a general level: every design has a `k`-subset whose
atom sum dominates `level · I`.  `GtzWeighted` is the case `level = 1`. -/
def GtzWeightedFloor (m k : ℕ) (level : ℝ) : Prop :=
  ∀ D : WeightedDesign m k, ∃ C : Finset (Fin m), C.card = k ∧
    (subsetSum D C - level • 1).PosSemidef

/-- **THE RANK FLOOR.**  Every weighted `(m, k)`-design has a `k`-subset whose
atom sum dominates `(1/k)·I` — for every size, every rank, no hypothesis.  The
selection is the maximal-volume pick of the UNSCALED atoms; the level is
size-free because Parseval averages the rows against weights totalling one
instead of counting them. -/
theorem gtzWeightedFloor_inv_rank (m k : ℕ) : GtzWeightedFloor m k ((k : ℝ))⁻¹ := by
  classical
  intro D
  obtain ⟨witnessPick, hwitnessInj, hwitnessDet⟩ :=
    exists_injective_pick_det_atomRowMatrix_ne_zero D
  obtain ⟨pick, hinj, hdet, hmax⟩ :=
    exists_maximalVolumePick_of_witness (atomRowMatrix D) hwitnessInj hwitnessDet
  have hunit : IsUnit (selectedFrameRows (atomRowMatrix D) pick).det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨Finset.image pick Finset.univ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq ?_, fun x => ?_⟩
    · rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, transpose_subsetSum]
    · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul, smul_eq_mul, dotProduct_subsetSum_mulVec D pick hinj]
      have hselectedNonneg := sum_sq_selected_nonneg D pick x
      rcases Nat.eq_zero_or_pos k with hrankZero | hrankPos
      · subst hrankZero
        simp only [Nat.cast_zero, inv_zero, zero_mul, sub_zero]
        exact hselectedNonneg
      · have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrankPos
        have hmaster := dotProduct_self_le_rank_mul_selected D pick hinj hunit hmax x
        rw [sub_nonneg, inv_mul_le_iff₀ hrankReal] at *
        nlinarith [hmaster, hrankReal]

/-- **The floor in the original 1997 coordinates**: every `n × k` matrix with
orthonormal columns has a `k`-row submatrix `B` with `BᵀB ⪰ (1/k)·I`, i.e.
`σ_min(B) ≥ 1/√k`.  The classical maximal-volume bound is `1/√(k(n−k)+1)`, which
is worse as soon as `n > k + 1`; GTZ conjectures `1/√n`, which is better as soon
as `n > k`.  So this floor and the conjecture are incomparable in general and the
floor is the stronger statement exactly when `n > k`… in the regime `n ≤ k`,
vacuous.  Its content is that SOME size-free level exists at all. -/
theorem exists_rowPick_posSemidef_sub_inv_rank {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin k) ℝ) (hortho : Aᵀ * A = 1) :
    ∃ rowPick : Fin k → Fin n, Function.Injective rowPick ∧
      ((A.submatrix rowPick id)ᵀ * (A.submatrix rowPick id) - ((k : ℝ))⁻¹ • 1).PosSemidef := by
  classical
  obtain ⟨C, hcard, hpsd⟩ := gtzWeightedFloor_inv_rank n k (rowDesign hn A hortho)
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨C.orderEmbOfFin hcard, (C.orderEmbOfFin hcard).injective, ?_⟩
  have himage : Finset.univ.image (C.orderEmbOfFin hcard) = C := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  have hsubmatrix : (A.submatrix (C.orderEmbOfFin hcard) id)ᵀ
        * (A.submatrix (C.orderEmbOfFin hcard) id)
      = ∑ atomIndex ∈ C, atomMatrix (A atomIndex) := by
    rw [transpose_mul_self_eq_sum_rows]
    conv_rhs => rw [← himage]
    rw [Finset.sum_image fun left _ right _ hlr => (C.orderEmbOfFin hcard).injective hlr]
    rfl
  have hsubset : subsetSum (rowDesign hn A hortho) C
      = (n : ℝ) • ∑ atomIndex ∈ C, atomMatrix (A atomIndex) := by
    rw [subsetSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    show atomMatrix (Real.sqrt (n : ℝ) • A atomIndex) = (n : ℝ) • atomMatrix (A atomIndex)
    rw [atomMatrix_smul, Real.sq_sqrt hnReal.le]
  have hrescale : (A.submatrix (C.orderEmbOfFin hcard) id)ᵀ
        * (A.submatrix (C.orderEmbOfFin hcard) id) - ((k : ℝ))⁻¹ • 1
      = (n : ℝ)⁻¹ • (subsetSum (rowDesign hn A hortho) C - ((k : ℝ))⁻¹ • 1) := by
    rw [hsubmatrix, hsubset, smul_sub, smul_smul, inv_mul_cancel₀ hnReal.ne', one_smul, smul_smul,
      smul_smul]
    congr 2
    ring
  rw [hrescale]
  exact hpsd.smul (inv_pos.mpr hnReal).le

end Gtz

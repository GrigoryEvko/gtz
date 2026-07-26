/-
# The branch-transfer constants: what a merge and a drop cost, exactly

The Covered+ induction on the size `m` runs three branches — merge a near-parallel
pair, drop a light atom, or work in the spread-with-floor region.  The first two
both take an `(m,k)`-design to an `(m−1,k)`-design by *deleting a Parseval defect
and re-whitening*, so both pay the same currency, and this file computes that
currency in closed form.

## The one master inequality

`whitenedPullback_form_ge`.  Let `defect` be any matrix whose quadratic form is
capped by `bound`, let `R` whiten `1 − defect` (`Rᵀ(1−defect)R = 1`), and suppose
the conjugated atom family `Rᵀ·g_c` has Rayleigh floor `level` on `C`.  Then the
RAW family has Rayleigh floor `level·(1 − bound)` on `C`.  Both branches are
instances:

* DROP atom `e`: `defect = t_e·A_e`, and its cap is the atom's **share**
  `s_e = t_e·|g_e|²` (`dropFrameDefect_form_le`).  So a downstairs triple pulls
  back with the factor `1 − s_e`; after the weight renormalisation `t_c/(1−t_e)`
  this is exactly `kappa_e = (1−s_e)/(1−t_e)`, i.e. `1 − t_e(ℓ_e−1)/(1−t_e)`.
* MERGE the pair `(a,b)` into the weight-averaged atom of summed weight:
  `defect = mergeFrameDefect`, and `mergeFrameDefect_eq` computes it EXACTLY as
  the reduced-mass rank-one matrix
  `(t_a t_b/(t_a+t_b))·(g_a−g_b)(g_a−g_b)ᵀ`, whose cap is
  `(t_a t_b/(t_a+t_b))·|g_a−g_b|²`.

## PROVED here

* `mergeFrameDefect_eq` — the exact merge identity (a Huygens–Steiner split of a
  two-point second moment about its weighted mean).  Rank one, PSD, and it
  vanishes exactly when the two atoms are EQUAL
  (`mergeFrameDefect_eq_zero_of_atoms_eq`) — the exact-split control, at which
  the merge reproduces the smaller design and every branch constant is zero.
* `exists_parallelAtoms_with_positive_mergeFrameDefect` — the CORRECTIVE.  Angular
  near-parallelism is NOT the right trigger: two atoms that are *exactly*
  parallel (`⟨g_a,g_b⟩² = ℓ_a ℓ_b`, i.e. `delta = 0`) but of different lengths
  leave a strictly positive defect.  The branch must be triggered by
  `|g_a − g_b|`, not by the angle.
* `whitenedPullback_form_ge` — the master transfer inequality, generic in the
  atom family, the subset, and the defect.
* `drop_pullback_form_ge`, `merge_pullback_form_ge` — the two instances.
* `dropWeight_sum_one`, `dropWhitened_parseval` — the dropped-and-renormalised
  family really is a `(m−1,k)`-design (the repo's `whitened_parseval` supplies
  Parseval for the unnormalised weights; these add the weight-sum-one repair,
  which rescales the atoms by `sqrt(1−t_e)`).
* `atomShare`, `sum_atomShare_eq_rank`, `exists_atomShare_le_rank_div_size` — the
  share of an atom is its classical leverage score, the shares sum to the rank,
  and hence SOME atom has share at most `k/m`.  This is the pigeonhole that
  bounds how cheap the drop branch can possibly be made: at `(7,3)` the cheapest
  available drop still costs at least the `3/7` ceiling's worth in the worst
  case, so "the lightest atom" is the wrong selector — the least-SHARE atom is
  the right one, and even it is not free.

## MEASURED elsewhere, not proved here

The tightness of the two caps, the typical (as opposed to worst-case) loss, and
the size of the constants on the tie families are numerical findings and are NOT
claimed by any statement below.  What is claimed is exactly what is proved: the
defect identity, the caps, and the transfer inequality they feed.

Nothing here bears on whether `GtzWeighted` is true.  These are the exchange
rates the induction must pay, computed exactly, in whichever direction the
induction eventually runs.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Design.MarginTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The generic congruence collapse

Both branches conjugate the whole atom family by the same whitener, so both need
the same two facts: the conjugated form at `R⁻¹ w` is the raw form at `w`, and the
length of `R⁻¹ w` reads the defect.  These are `Gtz.margin_transfer` freed from
the `WeightedDesign` packaging so that a merged family — which is not the atom
family of any design until it has been whitened — can use them too.
-/

/-- Conjugating every atom by `Rᵀ` is congruence of the subset sum. -/
theorem sum_atomMatrix_conj (atom : Fin m → (Fin k → ℝ))
    (R : Matrix (Fin k) (Fin k) ℝ) (selected : Finset (Fin m)) :
    (∑ c ∈ selected, atomMatrix (Rᵀ *ᵥ atom c))
      = Rᵀ * (∑ c ∈ selected, atomMatrix (atom c)) * R := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by
    rw [atomMatrix_conj, Matrix.transpose_transpose]

/-- **The congruence collapse**: the conjugated family's form at the preimage
`R⁻¹ w` is the raw family's form at `w`, exactly. -/
theorem conjugatedFamily_form_at_preimage (atom : Fin m → (Fin k → ℝ))
    {R : Matrix (Fin k) (Fin k) ℝ} (hRdet : IsUnit R.det)
    (selected : Finset (Fin m)) (probe : Fin k → ℝ) :
    (R⁻¹ *ᵥ probe) ⬝ᵥ ((∑ c ∈ selected, atomMatrix (Rᵀ *ᵥ atom c)) *ᵥ (R⁻¹ *ᵥ probe))
      = probe ⬝ᵥ ((∑ c ∈ selected, atomMatrix (atom c)) *ᵥ probe) := by
  rw [sum_atomMatrix_conj]
  have hcollapse : (Rᵀ * (∑ c ∈ selected, atomMatrix (atom c)) * R) *ᵥ (R⁻¹ *ᵥ probe)
      = Rᵀ *ᵥ ((∑ c ∈ selected, atomMatrix (atom c)) *ᵥ probe) := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_assoc (Rᵀ * ∑ c ∈ selected, atomMatrix (atom c)) R R⁻¹,
      Matrix.mul_nonsing_inv R hRdet, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  rw [hcollapse, dotProduct_comm, dotProduct_mulVec_transpose, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv R hRdet, Matrix.one_mulVec, dotProduct_comm]

/-- **The preimage length reads the defect**: `⟨R⁻¹w, R⁻¹w⟩ = ⟨w, (1−defect)w⟩`. -/
theorem preimage_length_eq_defect_form {defect R : Matrix (Fin k) (Fin k) ℝ}
    (hRdet : IsUnit R.det) (hwhiten : Rᵀ * (1 - defect) * R = 1) (probe : Fin k → ℝ) :
    (R⁻¹ *ᵥ probe) ⬝ᵥ (R⁻¹ *ᵥ probe) = probe ⬝ᵥ ((1 - defect) *ᵥ probe) := by
  have hRTdet : IsUnit Rᵀ.det := by rwa [Matrix.det_transpose]
  have hgram : (1 : Matrix (Fin k) (Fin k) ℝ) - defect = (Rᵀ)⁻¹ * R⁻¹ := by
    have hpush := congrArg (fun M => (Rᵀ)⁻¹ * M * R⁻¹) hwhiten
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Rᵀ hRTdet,
      Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv R hRdet, Matrix.mul_one,
      Matrix.mul_one] at hpush
    exact hpush
  rw [hgram, ← Matrix.mulVec_mulVec, ← Matrix.transpose_nonsing_inv,
    ← dotProduct_mulVec_transpose]
  exact dotProduct_comm _ _

/-- **THE MASTER BRANCH-TRANSFER INEQUALITY.**  If the family conjugated by the
whitener of `1 − defect` has Rayleigh floor `level` on `selected`, then the raw
family has Rayleigh floor `level·(1 − bound)` there, where `bound` caps the
defect's form.  Every quantitative cost of the merge and drop branches is this
one inequality at a different `defect`. -/
theorem whitenedPullback_form_ge (atom : Fin m → (Fin k → ℝ))
    (selected : Finset (Fin m)) {defect R : Matrix (Fin k) (Fin k) ℝ} {bound level : ℝ}
    (hRdet : IsUnit R.det) (hwhiten : Rᵀ * (1 - defect) * R = 1)
    (hdefectCap : ∀ probe : Fin k → ℝ,
      probe ⬝ᵥ (defect *ᵥ probe) ≤ bound * (probe ⬝ᵥ probe))
    (hlevelNonneg : 0 ≤ level)
    (hdown : ∀ preimage : Fin k → ℝ, level * (preimage ⬝ᵥ preimage)
      ≤ preimage ⬝ᵥ ((∑ c ∈ selected, atomMatrix (Rᵀ *ᵥ atom c)) *ᵥ preimage))
    (probe : Fin k → ℝ) :
    level * ((1 - bound) * (probe ⬝ᵥ probe))
      ≤ probe ⬝ᵥ ((∑ c ∈ selected, atomMatrix (atom c)) *ᵥ probe) := by
  have hlength := preimage_length_eq_defect_form hRdet hwhiten probe
  have hcap := hdefectCap probe
  have hexpand : probe ⬝ᵥ ((1 - defect) *ᵥ probe)
      = probe ⬝ᵥ probe - probe ⬝ᵥ (defect *ᵥ probe) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
  have hlengthGe : (1 - bound) * (probe ⬝ᵥ probe)
      ≤ (R⁻¹ *ᵥ probe) ⬝ᵥ (R⁻¹ *ᵥ probe) := by
    rw [hlength, hexpand]
    nlinarith [hcap]
  have hstep := hdown (R⁻¹ *ᵥ probe)
  rw [conjugatedFamily_form_at_preimage atom hRdet selected probe] at hstep
  nlinarith [mul_le_mul_of_nonneg_left hlengthGe hlevelNonneg]

/-! ## The merge branch: the defect is a reduced-mass rank-one matrix -/

/-- **The canonical merge of two atoms**: the weight-averaged direction, which
will carry the summed weight `t_a + t_b`. -/
noncomputable def mergedAtom (weightLeft weightRight : ℝ) (atomLeft atomRight : Fin k → ℝ) :
    Fin k → ℝ :=
  (weightLeft + weightRight)⁻¹ • (weightLeft • atomLeft + weightRight • atomRight)

/-- **The Parseval defect the merge leaves behind**: what the two atoms
contributed to the frame operator, minus what the merged atom contributes. -/
noncomputable def mergeFrameDefect (weightLeft weightRight : ℝ)
    (atomLeft atomRight : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  weightLeft • atomMatrix atomLeft + weightRight • atomMatrix atomRight
    - (weightLeft + weightRight)
      • atomMatrix (mergedAtom weightLeft weightRight atomLeft atomRight)

/-- **The exact merge identity.**  The defect is the reduced mass times the
rank-one atom of the DIFFERENCE of the two vectors:
`t_a A_a + t_b A_b − (t_a+t_b) A_h = (t_a t_b/(t_a+t_b))·(g_a−g_b)(g_a−g_b)ᵀ`.
It is positive semidefinite (a rank-one atom scaled by a positive number), it is
zero exactly on the equal-vector locus, and it does NOT see the angle between the
atoms except through the difference. -/
theorem mergeFrameDefect_eq {weightLeft weightRight : ℝ} (atomLeft atomRight : Fin k → ℝ)
    (hleftPos : 0 < weightLeft) (hrightPos : 0 < weightRight) :
    mergeFrameDefect weightLeft weightRight atomLeft atomRight
      = (weightLeft * weightRight / (weightLeft + weightRight))
        • atomMatrix (atomLeft - atomRight) := by
  have hsumNe : weightLeft + weightRight ≠ 0 := by positivity
  ext rowIndex colIndex
  simp only [mergeFrameDefect, mergedAtom, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  field_simp
  ring

/-- **The exact-split control**: merging two EQUAL atoms leaves no defect, so the
merged family is already a design and every branch constant vanishes. -/
theorem mergeFrameDefect_eq_zero_of_atoms_eq {weightLeft weightRight : ℝ}
    (atomLeft atomRight : Fin k → ℝ) (hleftPos : 0 < weightLeft)
    (hrightPos : 0 < weightRight) (hsame : atomLeft = atomRight) :
    mergeFrameDefect weightLeft weightRight atomLeft atomRight = 0 := by
  rw [mergeFrameDefect_eq atomLeft atomRight hleftPos hrightPos, hsame, sub_self]
  simp [atomMatrix]

/-- **The merge defect's cap**: its form is bounded by the reduced mass times the
leverage of the difference vector. -/
theorem mergeFrameDefect_form_le {weightLeft weightRight : ℝ}
    (atomLeft atomRight : Fin k → ℝ) (hleftPos : 0 < weightLeft)
    (hrightPos : 0 < weightRight) (probe : Fin k → ℝ) :
    probe ⬝ᵥ (mergeFrameDefect weightLeft weightRight atomLeft atomRight *ᵥ probe)
      ≤ (weightLeft * weightRight / (weightLeft + weightRight))
          * leverageOf (atomLeft - atomRight) * (probe ⬝ᵥ probe) := by
  have hmassNonneg : (0 : ℝ) ≤ weightLeft * weightRight / (weightLeft + weightRight) := by
    positivity
  have hcap := atom_form_le_leverage (atomLeft - atomRight) probe
  rw [mergeFrameDefect_eq atomLeft atomRight hleftPos hrightPos, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcap hmassNonneg

/-- **The corrective**: angular parallelism is the WRONG merge trigger.  These two
atoms are exactly parallel — their pairing squared equals the product of their
leverages, so the near-parallelism parameter `delta` is `0` — and yet the merge
defect's form is strictly positive.  What controls the merge is `|g_a − g_b|`,
which the angle does not bound because the two leverages may differ. -/
theorem exists_parallelAtoms_with_positive_mergeFrameDefect :
    ∃ (weightLeft weightRight : ℝ) (atomLeft atomRight probe : Fin 3 → ℝ),
      0 < weightLeft ∧ 0 < weightRight ∧
      (atomLeft ⬝ᵥ atomRight) ^ 2 = leverageOf atomLeft * leverageOf atomRight ∧
      0 < probe ⬝ᵥ
        (mergeFrameDefect weightLeft weightRight atomLeft atomRight *ᵥ probe) := by
  refine ⟨1 / 2, 1 / 2, ![2, 0, 0], ![1, 0, 0], ![1, 0, 0], by norm_num, by norm_num, ?_, ?_⟩
  · norm_num [leverageOf, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · rw [mergeFrameDefect_eq _ _ (by norm_num) (by norm_num), Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, atom_form_eq_sq]
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **The merge branch's pullback**: a Rayleigh floor downstairs, on the merged
and whitened family, transfers upstairs at the cost of the merge defect's cap. -/
theorem merge_pullback_form_ge (atom : Fin m → (Fin k → ℝ)) (selected : Finset (Fin m))
    {weightLeft weightRight : ℝ} (atomLeft atomRight : Fin k → ℝ)
    (hleftPos : 0 < weightLeft) (hrightPos : 0 < weightRight)
    {R : Matrix (Fin k) (Fin k) ℝ} (hRdet : IsUnit R.det)
    (hwhiten : Rᵀ * (1 - mergeFrameDefect weightLeft weightRight atomLeft atomRight) * R = 1)
    {level : ℝ} (hlevelNonneg : 0 ≤ level)
    (hdown : ∀ preimage : Fin k → ℝ, level * (preimage ⬝ᵥ preimage)
      ≤ preimage ⬝ᵥ ((∑ c ∈ selected, atomMatrix (Rᵀ *ᵥ atom c)) *ᵥ preimage))
    (probe : Fin k → ℝ) :
    level * ((1 - (weightLeft * weightRight / (weightLeft + weightRight))
        * leverageOf (atomLeft - atomRight)) * (probe ⬝ᵥ probe))
      ≤ probe ⬝ᵥ ((∑ c ∈ selected, atomMatrix (atom c)) *ᵥ probe) :=
  whitenedPullback_form_ge atom selected hRdet hwhiten
    (fun probeInner => by
      have := mergeFrameDefect_form_le atomLeft atomRight hleftPos hrightPos probeInner
      linarith)
    hlevelNonneg hdown probe

/-! ## The drop branch: the defect is the atom's share -/

/-- **The share of an atom** — its weight times its leverage.  This is the
classical leverage score: it is the diagonal of the design's projection form
(`Gtz.projectionOfDesign_diagonal`), so it is an invariant of the atom's row in
any orthonormal basis of the column space, independent of the weights. -/
def atomShare (D : WeightedDesign m k) (atomIndex : Fin m) : ℝ :=
  D.weight atomIndex * leverageOf (D.atom atomIndex)

/-- The shares sum to the rank. -/
theorem sum_atomShare_eq_rank (D : WeightedDesign m k) :
    ∑ atomIndex, atomShare D atomIndex = (k : ℝ) :=
  sum_weight_mul_leverage D

/-- **The share pigeonhole**: some atom has share at most `k/m`.  So no selector
can find an atom whose drop is cheaper than the `k/m` ceiling in general — at
`(7,3)` the guaranteed cheapest share is `3/7`, which is not small. -/
theorem exists_atomShare_le_rank_div_size (D : WeightedDesign m k) (hsize : 0 < m) :
    ∃ atomIndex : Fin m, atomShare D atomIndex ≤ (k : ℝ) / (m : ℝ) := by
  have hsizeNe : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hsize.ne'
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hsize)
  have haverage : (m : ℝ) * ((k : ℝ) / (m : ℝ)) = (k : ℝ) := by field_simp
  by_contra hcontra
  simp only [not_exists, not_le] at hcontra
  have hstrict : ∑ _atomIndex : Fin m, (k : ℝ) / (m : ℝ)
      < ∑ atomIndex, atomShare D atomIndex :=
    Finset.sum_lt_sum_of_nonempty hnonempty (fun atomIndex _ => hcontra atomIndex)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, haverage,
    sum_atomShare_eq_rank D] at hstrict
  exact lt_irrefl _ hstrict

/-- **The drop defect's cap** is exactly the atom's share. -/
theorem dropFrameDefect_form_le (D : WeightedDesign m k) (dropped : Fin m)
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((D.weight dropped • atomMatrix (D.atom dropped)) *ᵥ probe)
      ≤ atomShare D dropped * (probe ⬝ᵥ probe) := by
  have hcap := atom_form_le_leverage (D.atom dropped) probe
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomShare, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcap (D.weight_pos dropped).le

/-- **The drop branch's pullback**: a Rayleigh floor downstairs, on the whitened
family that survives the drop, transfers upstairs at the cost of the dropped
atom's SHARE.  Combined with the weight renormalisation `t_c/(1−t_e)` this is the
transfer factor `kappa_e = (1−s_e)/(1−t_e) = 1 − t_e(ℓ_e−1)/(1−t_e)`. -/
theorem drop_pullback_form_ge (D : WeightedDesign m k) (dropped : Fin m)
    (selected : Finset (Fin m)) {R : Matrix (Fin k) (Fin k) ℝ} (hRdet : IsUnit R.det)
    (hwhiten : Rᵀ * (1 - D.weight dropped • atomMatrix (D.atom dropped)) * R = 1)
    {level : ℝ} (hlevelNonneg : 0 ≤ level)
    (hdown : ∀ preimage : Fin k → ℝ, level * (preimage ⬝ᵥ preimage)
      ≤ preimage ⬝ᵥ ((∑ c ∈ selected, atomMatrix (Rᵀ *ᵥ D.atom c)) *ᵥ preimage))
    (probe : Fin k → ℝ) :
    level * ((1 - atomShare D dropped) * (probe ⬝ᵥ probe))
      ≤ probe ⬝ᵥ (subsetSum D selected *ᵥ probe) :=
  whitenedPullback_form_ge D.atom selected hRdet hwhiten
    (dropFrameDefect_form_le D dropped) hlevelNonneg hdown probe

/-! ## The dropped design really is a design -/

/-- The renormalised weights of the dropped family sum to one. -/
theorem dropWeight_sum_one (D : WeightedDesign m k) (dropped : Fin m)
    (hbelowOne : D.weight dropped < 1) :
    ∑ c ∈ Finset.univ.erase dropped, D.weight c / (1 - D.weight dropped) = 1 := by
  have hgapNe : (1 : ℝ) - D.weight dropped ≠ 0 := by linarith
  have hsum := Finset.sum_erase_add Finset.univ D.weight (Finset.mem_univ dropped)
  rw [D.weight_sum_one] at hsum
  rw [← Finset.sum_div, show ∑ c ∈ Finset.univ.erase dropped, D.weight c
      = 1 - D.weight dropped from by linarith, div_self hgapNe]

/-- **The dropped-and-whitened family is a genuine design**: with the atoms
rescaled by `sqrt(1−t_e)` to absorb the weight renormalisation, Parseval holds on
the nose.  The unnormalised half is the repo's `whitened_parseval`; the scaling is
what makes the weights sum to one at the same time. -/
theorem dropWhitened_parseval (D : WeightedDesign m k) (dropped : Fin m)
    {R : Matrix (Fin k) (Fin k) ℝ}
    (hwhiten : Rᵀ * (1 - D.weight dropped • atomMatrix (D.atom dropped)) * R = 1)
    (hbelowOne : D.weight dropped < 1) :
    ∑ c ∈ Finset.univ.erase dropped,
        (D.weight c / (1 - D.weight dropped))
          • atomMatrix (Real.sqrt (1 - D.weight dropped) • (Rᵀ *ᵥ D.atom c)) = 1 := by
  have hgapPos : (0 : ℝ) < 1 - D.weight dropped := by linarith
  have hgapNe : (1 : ℝ) - D.weight dropped ≠ 0 := ne_of_gt hgapPos
  have hsq : Real.sqrt (1 - D.weight dropped) ^ 2 = 1 - D.weight dropped :=
    Real.sq_sqrt hgapPos.le
  calc ∑ c ∈ Finset.univ.erase dropped,
        (D.weight c / (1 - D.weight dropped))
          • atomMatrix (Real.sqrt (1 - D.weight dropped) • (Rᵀ *ᵥ D.atom c))
      = ∑ c ∈ Finset.univ.erase dropped, D.weight c • atomMatrix (Rᵀ *ᵥ D.atom c) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [atomMatrix_smul, hsq, smul_smul, div_mul_cancel₀ _ hgapNe]
    _ = 1 := whitened_parseval D dropped hwhiten

end Gtz

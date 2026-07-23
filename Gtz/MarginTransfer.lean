/-
# The margin-transfer lemma: silence prices the whitened sub-design

The z-mass workflow's Z3 engine (triple-verified: build 22 141 + audit
188 040 fp instances, 0 violations, plus the hand proof). Removing one atom
from a weighted design and whitening by `W = I − t_e·A_e` produces a genuine
design on the remaining atoms, and every triple that fails to dominate in the
big design transfers a QUANTIFIED near-failure to the sub-design: the failing
direction `w` maps to `v = R⁻¹w` with

* form value preserved exactly — `⟨v, S′_C v⟩ = ⟨w, S_C w⟩ < 1`, and
* length shrunk by exactly the removed atom's share —
  `⟨v,v⟩ = ⟨w,w⟩ − t_e·⟨w, A_e w⟩`,

so the sub-design's Rayleigh quotient at `v` is under `1/(1 − t_e·ℓ_e)` for
unit `w`: silence of the 6-design forces `Φ₅ − 1 < t_e(ℓ_e−1)/(1−t_e·ℓ_e)`.
This is the reduction that prices the heaviest-atom collar `τ₀ᵉ` through the
kernel-checked (5,3) theorem; the whitening matrix exists by PsdKit's
`exists_congruence_to_one`.
-/
import Mathlib
import Gtz.PsdKit
import Gtz.CornerResolvent
import Gtz.ResolventPerturbation

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- Conjugating an atom: `(M·g)(M·g)ᵀ = M·(g gᵀ)·Mᵀ`. -/
theorem atomMatrix_conjugate (M : Matrix (Fin k) (Fin k) ℝ) (g : Fin k → ℝ) :
    atomMatrix (M *ᵥ g) = M * atomMatrix g * Mᵀ := by
  ext firstIndex secondIndex
  simp only [atomMatrix, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun outerIndex _ => ?_
  refine Finset.sum_congr rfl fun innerIndex _ => ?_
  ring

/-- The quadratic form of an atom is the squared overlap. -/
theorem atom_form_eq_sq (g w : Fin k → ℝ) :
    w ⬝ᵥ (atomMatrix g *ᵥ w) = (g ⬝ᵥ w) ^ 2 := by
  rw [atomMatrix, vecMulVec_mulVec_general, dotProduct_smul, smul_eq_mul,
    dotProduct_comm w g]
  ring

/-- The atom form is capped by the leverage: `⟨w, A_g w⟩ ≤ ℓ_g·⟨w,w⟩`. -/
theorem atom_form_le_leverage (g w : Fin k → ℝ) :
    w ⬝ᵥ (atomMatrix g *ᵥ w) ≤ leverageOf g * (w ⬝ᵥ w) := by
  rw [atom_form_eq_sq]
  have hcs := dotProduct_sq_le_mul g w
  have hlev : leverageOf g = g ⬝ᵥ g := by
    rw [leverageOf, dotProduct_self_eq_sum_sq]
  rw [hlev]
  exact hcs

/-- The Parseval identity with one atom split off. -/
theorem parseval_erase (D : WeightedDesign m k) (e : Fin m) :
    ∑ c ∈ Finset.univ.erase e, D.weight c • atomMatrix (D.atom c)
      = 1 - D.weight e • atomMatrix (D.atom e) := by
  have hsum := Finset.sum_erase_add Finset.univ
    (fun c => D.weight c • atomMatrix (D.atom c)) (Finset.mem_univ e)
  rw [D.isParseval] at hsum
  exact eq_sub_of_add_eq hsum

/-- **The whitened sub-design is a genuine design**: with `RᵀWR = 1` for
`W = I − t_e·A_e`, the atoms `Rᵀ·g_c` (c ≠ e) with the original weights
resolve the identity. -/
theorem whitened_parseval (D : WeightedDesign m k) (e : Fin m)
    {R : Matrix (Fin k) (Fin k) ℝ}
    (hwhiten : Rᵀ * (1 - D.weight e • atomMatrix (D.atom e)) * R = 1) :
    ∑ c ∈ Finset.univ.erase e,
        D.weight c • atomMatrix (Rᵀ *ᵥ D.atom c) = 1 := by
  have hconjugate : ∀ c, D.weight c • atomMatrix (Rᵀ *ᵥ D.atom c)
      = Rᵀ * (D.weight c • atomMatrix (D.atom c)) * R := by
    intro c
    rw [atomMatrix_conjugate, Matrix.transpose_transpose,
      Matrix.mul_smul, Matrix.smul_mul]
  calc ∑ c ∈ Finset.univ.erase e, D.weight c • atomMatrix (Rᵀ *ᵥ D.atom c)
      = Rᵀ * (∑ c ∈ Finset.univ.erase e,
          D.weight c • atomMatrix (D.atom c)) * R := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        exact Finset.sum_congr rfl fun c _ => hconjugate c
    _ = 1 := by rw [parseval_erase, hwhiten]

/-- **The margin-transfer lemma**: a triple failing to dominate in the big
design transfers to the whitened sub-design with the form value PRESERVED and
the length shrunk by exactly the removed atom's share along the failing
direction. Silence of the big design prices the sub-design's optimality. -/
theorem margin_transfer (D : WeightedDesign m k) (e : Fin m)
    {R : Matrix (Fin k) (Fin k) ℝ} (hRdet : IsUnit R.det)
    (hwhiten : Rᵀ * (1 - D.weight e • atomMatrix (D.atom e)) * R = 1)
    (C : Finset (Fin m)) (w : Fin k → ℝ) :
    (R⁻¹ *ᵥ w) ⬝ᵥ ((∑ c ∈ C, atomMatrix (Rᵀ *ᵥ D.atom c)) *ᵥ (R⁻¹ *ᵥ w))
        = w ⬝ᵥ (subsetSum D C *ᵥ w)
      ∧ (R⁻¹ *ᵥ w) ⬝ᵥ (R⁻¹ *ᵥ w)
        = w ⬝ᵥ w - D.weight e * (w ⬝ᵥ (atomMatrix (D.atom e) *ᵥ w)) := by
  have hRTdet : IsUnit Rᵀ.det := by rwa [Matrix.det_transpose]
  constructor
  · -- the form value is preserved under the congruence
    have hsumConj : (∑ c ∈ C, atomMatrix (Rᵀ *ᵥ D.atom c))
        = Rᵀ * subsetSum D C * R := by
      rw [subsetSum, Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by
        rw [atomMatrix_conjugate, Matrix.transpose_transpose]
    rw [hsumConj]
    have hcollapse : (Rᵀ * subsetSum D C * R) *ᵥ (R⁻¹ *ᵥ w)
        = Rᵀ *ᵥ (subsetSum D C *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (Rᵀ * subsetSum D C) R R⁻¹,
        Matrix.mul_nonsing_inv R hRdet, Matrix.mul_one,
        ← Matrix.mulVec_mulVec]
    rw [hcollapse, dotProduct_comm, dotProduct_mulVec_transpose,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv R hRdet,
      Matrix.one_mulVec, dotProduct_comm]
  · -- the length reads the whitening matrix
    have hW : (1 : Matrix (Fin k) (Fin k) ℝ)
        - D.weight e • atomMatrix (D.atom e) = (Rᵀ)⁻¹ * R⁻¹ := by
      have hpush := congrArg (fun M => (Rᵀ)⁻¹ * M * R⁻¹) hwhiten
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul Rᵀ hRTdet, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv R hRdet, Matrix.mul_one, Matrix.mul_one]
        at hpush
      exact hpush
    have hexpand : w ⬝ᵥ ((1 - D.weight e • atomMatrix (D.atom e)) *ᵥ w)
        = w ⬝ᵥ w - D.weight e * (w ⬝ᵥ (atomMatrix (D.atom e) *ᵥ w)) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hstep : (R⁻¹ *ᵥ w) ⬝ᵥ (R⁻¹ *ᵥ w)
        = w ⬝ᵥ (((Rᵀ)⁻¹ * R⁻¹) *ᵥ w) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.transpose_nonsing_inv,
        ← dotProduct_mulVec_transpose]
      exact dotProduct_comm _ _
    rw [hstep, ← hW, hexpand]

/-- **The priced failure**: for a unit failing direction under a heavy but
sub-critical removed atom, the whitened sub-design carries a direction of
form value under one and length at least `1 − t_e·ℓ_e > 0` — the
division-free shape of `Φ_sub − 1 < t_e(ℓ_e−1)/(1−t_e·ℓ_e)`. -/
theorem margin_transfer_priced (D : WeightedDesign m k) (e : Fin m)
    {R : Matrix (Fin k) (Fin k) ℝ} (hRdet : IsUnit R.det)
    (hwhiten : Rᵀ * (1 - D.weight e • atomMatrix (D.atom e)) * R = 1)
    (C : Finset (Fin m)) (w : Fin k → ℝ) (hunit : w ⬝ᵥ w = 1)
    (hfail : w ⬝ᵥ (subsetSum D C *ᵥ w) < 1) :
    (R⁻¹ *ᵥ w) ⬝ᵥ ((∑ c ∈ C, atomMatrix (Rᵀ *ᵥ D.atom c)) *ᵥ (R⁻¹ *ᵥ w)) < 1
      ∧ 1 - D.weight e * leverageOf (D.atom e)
        ≤ (R⁻¹ *ᵥ w) ⬝ᵥ (R⁻¹ *ᵥ w) := by
  obtain ⟨hform, hlength⟩ := margin_transfer D e hRdet hwhiten C w
  refine ⟨by rwa [hform], ?_⟩
  rw [hlength, hunit]
  have hcap := atom_form_le_leverage (D.atom e) w
  rw [hunit, mul_one] at hcap
  have hweightNonneg := (D.weight_pos e).le
  nlinarith [hcap, hweightNonneg]

end Gtz

/-
# The rank-one Schur lemma: N − ggᵀ ⪰ 0 ⟺ gᵀN⁻¹g ≤ 1 (N ≻ 0)

The certificate's pivot step (ratpigeon Cor. 2.2): dropping an atom from a PD
base set dominates iff its pivot value is ≤ 1. Informally one line by congruence
with N^{1/2}; here proven by POLARIZATION over dotProduct — no matrix square
roots and no Schur-block API.

MECHANIZATION RESIDUALS discovered here (recorded, worked around):
* R-MECH-1: Mathlib v4.32 has NO Cauchy eigenvalue interlacing (needed later by
  the cap criterion's signature bookkeeping).
* R-MECH-2: Mathlib v4.32 has NO PSD Schur-complement block criterion
  (`SchurComplement.lean` carries only determinant/inverse material) — hence the
  hand polarization below.
-/
import Mathlib
import Gtz.Basic
import Gtz.Sanity

namespace Gtz

open Matrix

variable {k : ℕ}

/-- (vecMulVec a b) *ᵥ y = (b ⬝ᵥ y) • a. -/
theorem vecMulVec_mulVec_eq (a b y : Fin k → ℝ) :
    (Matrix.vecMulVec a b) *ᵥ y = (b ⬝ᵥ y) • a := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Symmetric matrices give a symmetric bilinear form. -/
theorem dot_mulVec_comm {N : Matrix (Fin k) (Fin k) ℝ} (hNT : Nᵀ = N)
    (a b : Fin k → ℝ) : a ⬝ᵥ (N *ᵥ b) = b ⬝ᵥ (N *ᵥ a) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hsymm : N j i = N i j := by
    have h := congrFun (congrFun hNT i) j
    rw [Matrix.transpose_apply] at h
    exact h
  rw [hsymm]; ring

/-- A real PosDef matrix is symmetric (its Hermitian-ness, star-trivially). -/
theorem PosDef.transpose_eq {N : Matrix (Fin k) (Fin k) ℝ} (hN : N.PosDef) :
    Nᵀ = N := by
  ext i j
  have h := congrFun (congrFun hN.1 i) j
  rw [Matrix.conjTranspose_apply] at h
  simpa using h

/-- Over ℝ, symmetry is Hermitian-ness. -/
theorem isHermitian_of_transpose_eq {M : Matrix (Fin k) (Fin k) ℝ}
    (h : Mᵀ = M) : M.IsHermitian := by
  show Mᴴ = M
  ext i j
  rw [Matrix.conjTranspose_apply, star_trivial]
  exact congrFun (congrFun h i) j

/-- Over ℝ, Hermitian-ness is symmetry. -/
theorem transpose_eq_of_isHermitian {M : Matrix (Fin k) (Fin k) ℝ}
    (h : M.IsHermitian) : Mᵀ = M := by
  ext i j
  have hh := congrFun (congrFun h i) j
  rw [Matrix.conjTranspose_apply] at hh
  simpa using hh

/-- **Rank-one Schur.** For N ≻ 0: N − ggᵀ ⪰ 0 ⟺ gᵀN⁻¹g ≤ 1. -/
theorem posSemidef_sub_vecMulVec_iff (N : Matrix (Fin k) (Fin k) ℝ)
    (hN : N.PosDef) (g : Fin k → ℝ) :
    (N - Matrix.vecMulVec g g).PosSemidef ↔ g ⬝ᵥ (N⁻¹ *ᵥ g) ≤ 1 := by
  have hdet : IsUnit N.det := isUnit_iff_ne_zero.mpr (ne_of_gt hN.det_pos)
  have hNT : Nᵀ = N := PosDef.transpose_eq hN
  set v : Fin k → ℝ := N⁻¹ *ᵥ g with hv
  have hNv : N *ᵥ v = g := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
  set q : ℝ := g ⬝ᵥ (N⁻¹ *ᵥ g) with hq
  have hqv : v ⬝ᵥ (N *ᵥ v) = q := by rw [hNv, hq, hv, dotProduct_comm]
  -- the quadratic form of N − ggᵀ
  have hquad : ∀ y : Fin k → ℝ,
      star y ⬝ᵥ ((N - Matrix.vecMulVec g g) *ᵥ y)
        = y ⬝ᵥ (N *ᵥ y) - (g ⬝ᵥ y) ^ 2 := by
    intro y
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, vecMulVec_mulVec_eq,
      dotProduct_smul, smul_eq_mul, dotProduct_comm y g]
    ring
  -- N's quadratic form is nonnegative
  have hNquad : ∀ y : Fin k → ℝ, 0 ≤ y ⬝ᵥ (N *ᵥ y) := by
    intro y
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hN.posSemidef).2 y
    rwa [star_trivial] at h
  have hq0 : 0 ≤ q := hqv ▸ hNquad v
  -- polarization: (g ⬝ᵥ y)² ≤ q · yᵀNy
  have hCS : ∀ y : Fin k → ℝ, (g ⬝ᵥ y) ^ 2 ≤ q * (y ⬝ᵥ (N *ᵥ y)) := by
    intro y
    rcases eq_or_lt_of_le hq0 with hq0' | hqpos
    · -- q = 0 forces v = 0 hence g = 0
      have hv0 : v = 0 := by
        by_contra hv0
        have := (Matrix.posDef_iff_dotProduct_mulVec.mp hN).2 hv0
        rw [star_trivial, hqv] at this
        exact absurd hq0'.symm (ne_of_gt this)
      have hg0 : g = 0 := by rw [← hNv, hv0, Matrix.mulVec_zero]
      simp [hg0, ← hq0']
    · set c : ℝ := g ⬝ᵥ y with hc
      have hz := hNquad (q • y - c • v)
      have hexp : (q • y - c • v) ⬝ᵥ (N *ᵥ (q • y - c • v))
          = q * q * (y ⬝ᵥ (N *ᵥ y)) - q * c * (y ⬝ᵥ (N *ᵥ v))
            - c * q * (v ⬝ᵥ (N *ᵥ y)) + c * c * (v ⬝ᵥ (N *ᵥ v)) := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
          sub_dotProduct, smul_dotProduct, smul_dotProduct,
          dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul,
          dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          smul_eq_mul, smul_eq_mul]
        ring
      have hyv : y ⬝ᵥ (N *ᵥ v) = c := by rw [hNv, dotProduct_comm, hc]
      have hvy : v ⬝ᵥ (N *ᵥ y) = c := by
        rw [dot_mulVec_comm hNT v y, hNv, dotProduct_comm, hc]
      rw [hexp, hyv, hvy, hqv] at hz
      -- hz : 0 ≤ q·q·A − q·c·c − c·q·c + c·c·q = q(qA − c²)
      nlinarith [hz, hqpos]
  constructor
  · -- PSD ⟹ q ≤ 1 : test the form at y = v
    intro hpsd
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 v
    rw [hquad v, hqv] at h
    have hgv : g ⬝ᵥ v = q := by rw [hq, hv]
    rw [hgv] at h
    -- h : 0 ≤ q − q²  = q(1−q); if q > 1 this is negative
    nlinarith [h]
  · -- q ≤ 1 ⟹ PSD
    intro hle
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun y => ?_⟩
    · exact hN.1.sub (posSemidef_atomMatrix g).1
    · rw [hquad y]
      nlinarith [hCS y, hNquad y, hq0]

end Gtz

/-
# The rank-one Schur lemma: N − ggᵀ ⪰ 0 ⟺ gᵀN⁻¹g ≤ 1 (N ≻ 0)

The certificate's pivot step (ratpigeon Cor. 2.2): dropping an atom from a PD
base set dominates iff its pivot value is ≤ 1. Informally one line by congruence
with N^{1/2}; here proven by POLARIZATION over dotProduct — no matrix square
roots and no Schur-block API.

The strict twin `posDef_sub_vecMulVec_iff` (N − ggᵀ ≻ 0 ⟺ gᵀN⁻¹g < 1) rides on the
weak form: forward, q = 1 would kill the gap form at N⁻¹g; backward, the weak form
at g/√s with s = (1+q)/2 ∈ (q, 1) leaves the margin (1−s)·yᵀNy off zero.

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

/-- The product of two rank-one operators contracts through the middle. -/
theorem vecMulVec_mul_vecMulVec (leftVec innerLeft innerRight rightVec : Fin k → ℝ) :
    Matrix.vecMulVec leftVec innerLeft * Matrix.vecMulVec innerRight rightVec
      = (innerLeft ⬝ᵥ innerRight) • Matrix.vecMulVec leftVec rightVec := by
  ext rowIndex colIndex
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
    smul_eq_mul, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun index _ => by ring

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

/-- **Strict rank-one Schur.** For N ≻ 0: N − ggᵀ ≻ 0 ⟺ gᵀN⁻¹g < 1 — the strict twin
of `posSemidef_sub_vecMulVec_iff`, separating "dropping an atom dominates" from
"dominates strictly". Both directions ride on the weak form:

* forward: the weak form gives q ≤ 1; were q = 1, the gap form at the solution
  vector N⁻¹g would be q − q² = 0, contradicting definiteness;
* backward: the weak form at the RESCALED vector g/√s with s = (1+q)/2 ∈ (q, 1)
  gives (g ⬝ᵥ y)² ≤ s·⟨y, Ny⟩ for every y, so the gap form keeps the margin
  (1−s)·⟨y, Ny⟩ > 0 off zero. No new polarization argument. -/
theorem posDef_sub_vecMulVec_iff (N : Matrix (Fin k) (Fin k) ℝ)
    (hN : N.PosDef) (g : Fin k → ℝ) :
    (N - Matrix.vecMulVec g g).PosDef ↔ g ⬝ᵥ (N⁻¹ *ᵥ g) < 1 := by
  have hdet : IsUnit N.det := isUnit_iff_ne_zero.mpr (ne_of_gt hN.det_pos)
  have hquadNonneg : ∀ y : Fin k → ℝ, 0 ≤ y ⬝ᵥ (N *ᵥ y) := by
    intro y
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hN.posSemidef).2 y
    rwa [star_trivial] at h
  have hquadPos : ∀ y : Fin k → ℝ, y ≠ 0 → 0 < y ⬝ᵥ (N *ᵥ y) := by
    intro y hy
    have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hN).2 hy
    rwa [star_trivial] at h
  have hform : ∀ v y : Fin k → ℝ,
      y ⬝ᵥ ((N - Matrix.vecMulVec v v) *ᵥ y) = y ⬝ᵥ (N *ᵥ y) - (v ⬝ᵥ y) ^ 2 := by
    intro v y
    rw [Matrix.sub_mulVec, dotProduct_sub, vecMulVec_mulVec_eq, dotProduct_smul,
      smul_eq_mul, dotProduct_comm y v]
    ring
  have hherm : (N - Matrix.vecMulVec g g).IsHermitian :=
    hN.1.sub (posSemidef_atomMatrix g).1
  have hpivotNonneg : 0 ≤ g ⬝ᵥ (N⁻¹ *ᵥ g) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hN.inv.posSemidef).2 g
    rwa [star_trivial] at h
  constructor
  · intro hpd
    have hweak : g ⬝ᵥ (N⁻¹ *ᵥ g) ≤ 1 :=
      (posSemidef_sub_vecMulVec_iff N hN g).mp hpd.posSemidef
    rcases lt_or_eq_of_le hweak with hlt | heq
    · exact hlt
    · exfalso
      have hsolves : N *ᵥ (N⁻¹ *ᵥ g) = g := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
      have hsolQuad : (N⁻¹ *ᵥ g) ⬝ᵥ (N *ᵥ (N⁻¹ *ᵥ g)) = g ⬝ᵥ (N⁻¹ *ᵥ g) := by
        rw [hsolves, dotProduct_comm]
      have hsolNe : (N⁻¹ *ᵥ g) ≠ 0 := by
        intro hzero
        have hg : g = 0 := by rw [← hsolves, hzero, Matrix.mulVec_zero]
        rw [hg, zero_dotProduct] at heq
        norm_num at heq
      have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hsolNe
      rw [star_trivial, hform g, hsolQuad, dotProduct_comm g (N⁻¹ *ᵥ g),
        dotProduct_comm (N⁻¹ *ᵥ g) g, heq] at hpos
      norm_num at hpos
  · intro hlt
    have hscalePos : (0 : ℝ) < (1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2 := by linarith
    have hscaleLt : (1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2 < 1 := by linarith
    have hpivotLe : g ⬝ᵥ (N⁻¹ *ᵥ g) ≤ (1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2 := by linarith
    have hfactorSq : ((Real.sqrt ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2))⁻¹) ^ 2
        = ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hscalePos.le]
    have hrescaled : (N - Matrix.vecMulVec
        ((Real.sqrt ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2))⁻¹ • g)
        ((Real.sqrt ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2))⁻¹ • g)).PosSemidef := by
      refine (posSemidef_sub_vecMulVec_iff N hN _).mpr ?_
      have hval : ((Real.sqrt ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2))⁻¹ • g)
            ⬝ᵥ (N⁻¹ *ᵥ ((Real.sqrt ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2))⁻¹ • g))
          = ((Real.sqrt ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2))⁻¹) ^ 2 * (g ⬝ᵥ (N⁻¹ *ᵥ g)) := by
        rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
          smul_eq_mul]
        ring
      rw [hval, hfactorSq, inv_mul_eq_div, div_le_one hscalePos]
      exact hpivotLe
    have hbound : ∀ y : Fin k → ℝ,
        (g ⬝ᵥ y) ^ 2 ≤ ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2) * (y ⬝ᵥ (N *ᵥ y)) := by
      intro y
      have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hrescaled).2 y
      rw [star_trivial,
        hform ((Real.sqrt ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2))⁻¹ • g) y,
        smul_dotProduct, smul_eq_mul, mul_pow, hfactorSq] at h
      rw [← sub_nonneg]
      have hscaleNe : ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2) ≠ 0 := ne_of_gt hscalePos
      have hexpand : ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2) * (y ⬝ᵥ (N *ᵥ y)) - (g ⬝ᵥ y) ^ 2
          = ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2)
            * ((y ⬝ᵥ (N *ᵥ y)) - ((1 + g ⬝ᵥ (N⁻¹ *ᵥ g)) / 2)⁻¹ * (g ⬝ᵥ y) ^ 2) := by
        field_simp
      rw [hexpand]
      exact mul_nonneg hscalePos.le (by linarith [h])
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hherm, fun y hy => ?_⟩
    rw [star_trivial, hform g]
    have h1 := hbound y
    have h2 := hquadPos y hy
    nlinarith [h1, h2, hscaleLt]

end Gtz

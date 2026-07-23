/-
# Branch (b): the cap criterion, de-spectralized

For an invertible symmetric N of signature (k−1, 1), the rank-one completion
N + ggᵀ is PSD iff the cap value gᵀN⁻¹g is ≤ −1. Proven at k=3 in
`gtz_proof_gtz3_ratpigeon.md` §4, general k in `gtz_proof_gtz_allk_lift.md`
§4.3 — informally via det(N + ggᵀ) = det N·(1 + gᵀN⁻¹g) and Weyl interlacing.

MECHANIZATION (resolving R-MECH-1 by reformulation, diary §§62–63): the
signature hypothesis is stated WITHOUT eigenvalues, as a witness pair — a
negative direction w together with positive semidefiniteness on its
N-orthogonal complement. This is exactly signature (k−1,1) for invertible
symmetric N (an eigenbasis produces the witness; the complement-transfer lemma
forbids more negativity), and it is the form in which the certificate layer
constructs gates. No interlacing, no eigenvalues, no determinant identity:

* `psd_on_complement_transfer` — the negative direction is interchangeable:
  if N ⪰ 0 on w^⊥N and sᵀNs < 0, then N ⪰ 0 on s^⊥N (Cauchy–Schwarz for the
  restricted PSD form via `discrim_le_zero`, then a division-free
  rearrangement);
* (⇐) with s := N⁻¹g one has sᵀNs = q ≤ −1 < 0, so N ⪰ 0 on s^⊥N; splitting
  any v = βs + v₁ with v₁ ⊥ g gives vᵀ(N+ggᵀ)v = β²·q(1+q) + v₁ᵀNv₁ ≥ 0;
* (⇒) testing at s gives q(1+q) ≥ 0; testing at w and at explicit
  destabilizing combinations of s and w excludes q ≥ 0.
-/
import Mathlib
import Gtz.Basic
import Gtz.Sanity
import Gtz.SchurRankOne
import Gtz.TraceIdentity

namespace Gtz

open Matrix

variable {k : ℕ}

/-- **Complement transfer.** If the symmetric form of N is nonnegative on the
N-orthogonal complement of one negative direction, it is nonnegative on the
N-orthogonal complement of EVERY negative direction. -/
theorem psd_on_complement_transfer {N : Matrix (Fin k) (Fin k) ℝ}
    (hNT : Nᵀ = N) {w : Fin k → ℝ} (hw : w ⬝ᵥ (N *ᵥ w) < 0)
    (hWpsd : ∀ v, v ⬝ᵥ (N *ᵥ w) = 0 → 0 ≤ v ⬝ᵥ (N *ᵥ v))
    {s : Fin k → ℝ} (hs : s ⬝ᵥ (N *ᵥ s) < 0) :
    ∀ v, v ⬝ᵥ (N *ᵥ s) = 0 → 0 ≤ v ⬝ᵥ (N *ᵥ v) := by
  have hbilin : ∀ x y : Fin k → ℝ, x ⬝ᵥ (N *ᵥ y) = y ⬝ᵥ (N *ᵥ x) :=
    fun x y => dot_mulVec_comm hNT x y
  intro v hvs
  have hwne : w ⬝ᵥ (N *ᵥ w) ≠ 0 := hw.ne
  set gam : ℝ := (v ⬝ᵥ (N *ᵥ w)) / (w ⬝ᵥ (N *ᵥ w)) with hgam
  set u : Fin k → ℝ := v - gam • w with hu
  set del : ℝ := (s ⬝ᵥ (N *ᵥ w)) / (w ⬝ᵥ (N *ᵥ w)) with hdel
  set s0 : Fin k → ℝ := s - del • w with hs0
  have hgamw : gam * (w ⬝ᵥ (N *ᵥ w)) = v ⬝ᵥ (N *ᵥ w) := by
    rw [hgam]
    exact div_mul_cancel₀ _ hwne
  have hdelw : del * (w ⬝ᵥ (N *ᵥ w)) = s ⬝ᵥ (N *ᵥ w) := by
    rw [hdel]
    exact div_mul_cancel₀ _ hwne
  have huW : u ⬝ᵥ (N *ᵥ w) = 0 := by
    rw [hu, sub_dotProduct, smul_dotProduct, smul_eq_mul, hgamw, sub_self]
  have hs0W : s0 ⬝ᵥ (N *ᵥ w) = 0 := by
    rw [hs0, sub_dotProduct, smul_dotProduct, smul_eq_mul, hdelw, sub_self]
  -- the generic quadratic expansion against w
  have hquad : ∀ (x : Fin k → ℝ) (c : ℝ),
      (x - c • w) ⬝ᵥ (N *ᵥ (x - c • w))
      = x ⬝ᵥ (N *ᵥ x) - 2 * c * (x ⬝ᵥ (N *ᵥ w))
        + c ^ 2 * (w ⬝ᵥ (N *ᵥ w)) := by
    intro x c
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
      dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hbilin w x]
    ring
  have hvu : v ⬝ᵥ (N *ᵥ v)
      = u ⬝ᵥ (N *ᵥ u) + gam ^ 2 * (w ⬝ᵥ (N *ᵥ w)) := by
    have h := hquad v gam
    rw [← hu] at h
    linear_combination (-1 : ℝ) * h + (-2 * gam) * hgamw
  have hss : s ⬝ᵥ (N *ᵥ s)
      = s0 ⬝ᵥ (N *ᵥ s0) + del ^ 2 * (w ⬝ᵥ (N *ᵥ w)) := by
    have h := hquad s del
    rw [← hs0] at h
    linear_combination (-1 : ℝ) * h + (-2 * del) * hdelw
  -- the constraint v ⊥N s in split coordinates
  have hvdec : v = u + gam • w := by rw [hu]; abel
  have hsdec : s = s0 + del • w := by rw [hs0]; abel
  have hcross : u ⬝ᵥ (N *ᵥ s0) + gam * del * (w ⬝ᵥ (N *ᵥ w)) = 0 := by
    have hexp : v ⬝ᵥ (N *ᵥ s)
        = u ⬝ᵥ (N *ᵥ s0) + gam * del * (w ⬝ᵥ (N *ᵥ w))
          + del * (u ⬝ᵥ (N *ᵥ w)) + gam * (s0 ⬝ᵥ (N *ᵥ w)) := by
      rw [hvdec, hsdec]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
        dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [hbilin w s0]
      ring
    rw [hexp, huW, hs0W] at hvs
    linarith [hvs]
  -- Cauchy–Schwarz for the W-restricted PSD form, via the discriminant
  have hApos : 0 ≤ u ⬝ᵥ (N *ᵥ u) := hWpsd u huW
  have hS0pos : 0 ≤ s0 ⬝ᵥ (N *ᵥ s0) := hWpsd s0 hs0W
  have hCS : (u ⬝ᵥ (N *ᵥ s0)) ^ 2
      ≤ (u ⬝ᵥ (N *ᵥ u)) * (s0 ⬝ᵥ (N *ᵥ s0)) := by
    have hquadW : ∀ lam : ℝ,
        0 ≤ (s0 ⬝ᵥ (N *ᵥ s0)) * (lam * lam)
          + (2 * (u ⬝ᵥ (N *ᵥ s0))) * lam + u ⬝ᵥ (N *ᵥ u) := by
      intro lam
      have hmem : (u + lam • s0) ⬝ᵥ (N *ᵥ w) = 0 := by
        rw [add_dotProduct, smul_dotProduct, huW, hs0W, smul_eq_mul]
        ring
      have h := hWpsd (u + lam • s0) hmem
      have hexp : (u + lam • s0) ⬝ᵥ (N *ᵥ (u + lam • s0))
          = (s0 ⬝ᵥ (N *ᵥ s0)) * (lam * lam)
            + (2 * (u ⬝ᵥ (N *ᵥ s0))) * lam + u ⬝ᵥ (N *ᵥ u) := by
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
          dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        rw [hbilin s0 u]
        ring
      rwa [hexp] at h
    have hdisc := discrim_le_zero hquadW
    rw [discrim] at hdisc
    nlinarith [hdisc]
  -- δ²·(−wᵀNw) is positive (δ = 0 would make s nonnegative)
  have hdel2 : 0 < del ^ 2 * (-(w ⬝ᵥ (N *ᵥ w))) := by
    rcases eq_or_ne del 0 with h0 | hne
    · exfalso
      rw [h0] at hss
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_mul, add_zero] at hss
      linarith [hss, hS0pos, hs]
    · have hd2 : 0 < del ^ 2 := by positivity
      nlinarith [hd2, hw]
  -- the mixed-term square is pinned by the constraint
  have hsq : (u ⬝ᵥ (N *ᵥ s0)) ^ 2
      = gam ^ 2 * del ^ 2 * (w ⬝ᵥ (N *ᵥ w)) ^ 2 := by
    linear_combination
      (u ⬝ᵥ (N *ᵥ s0) - gam * del * (w ⬝ᵥ (N *ᵥ w))) * hcross
  -- division-free rearrangement: A·δ²a ≥ γ²δ²a² and δ²a > S₀ finish
  have hkey : gam ^ 2 * del ^ 2 * (w ⬝ᵥ (N *ᵥ w)) ^ 2
      ≤ (u ⬝ᵥ (N *ᵥ u)) * (s0 ⬝ᵥ (N *ᵥ s0)) := by
    rw [← hsq]
    exact hCS
  have hS0le : s0 ⬝ᵥ (N *ᵥ s0) ≤ del ^ 2 * (-(w ⬝ᵥ (N *ᵥ w))) := by
    linarith [hss, hs]
  have hAS : (u ⬝ᵥ (N *ᵥ u)) * (s0 ⬝ᵥ (N *ᵥ s0))
      ≤ (u ⬝ᵥ (N *ᵥ u)) * (del ^ 2 * (-(w ⬝ᵥ (N *ᵥ w)))) :=
    mul_le_mul_of_nonneg_left hS0le hApos
  have hgoal : 0 ≤ u ⬝ᵥ (N *ᵥ u) + gam ^ 2 * (w ⬝ᵥ (N *ᵥ w)) := by
    nlinarith [hkey, hAS, hdel2]
  rw [hvu]
  exact hgoal

/-- **The cap criterion, de-spectralized** (branch b of the certificate).
N symmetric and invertible with a signature witness — a negative direction on
whose N-orthogonal complement N is PSD (= signature (k−1,1)): the rank-one
completion N + ggᵀ is PSD iff the cap value gᵀN⁻¹g is ≤ −1. -/
theorem cap_criterion {N : Matrix (Fin k) (Fin k) ℝ}
    (hNT : Nᵀ = N) (hdet : IsUnit N.det)
    {w : Fin k → ℝ} (hw : w ⬝ᵥ (N *ᵥ w) < 0)
    (hWpsd : ∀ v, v ⬝ᵥ (N *ᵥ w) = 0 → 0 ≤ v ⬝ᵥ (N *ᵥ v))
    (g : Fin k → ℝ) :
    (N + Matrix.vecMulVec g g).PosSemidef ↔ g ⬝ᵥ (N⁻¹ *ᵥ g) ≤ -1 := by
  have hbilin : ∀ x y : Fin k → ℝ, x ⬝ᵥ (N *ᵥ y) = y ⬝ᵥ (N *ᵥ x) :=
    fun x y => dot_mulVec_comm hNT x y
  set s : Fin k → ℝ := N⁻¹ *ᵥ g with hsdef
  have hNs : N *ᵥ s = g := by
    rw [hsdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet,
      Matrix.one_mulVec]
  have hq : s ⬝ᵥ (N *ᵥ s) = g ⬝ᵥ (N⁻¹ *ᵥ g) := by
    rw [hNs, ← hsdef, dotProduct_comm]
  have hgs : g ⬝ᵥ s = s ⬝ᵥ (N *ᵥ s) := by
    rw [← hNs]
    exact dotProduct_comm _ _
  have hsNw : s ⬝ᵥ (N *ᵥ w) = g ⬝ᵥ w := by
    rw [hbilin s w, hNs, dotProduct_comm]
  have hvT : (Matrix.vecMulVec g g)ᵀ = Matrix.vecMulVec g g :=
    transpose_eq_of_isHermitian (posSemidef_atomMatrix g).1
  have hsumT : (N + Matrix.vecMulVec g g)ᵀ = N + Matrix.vecMulVec g g := by
    rw [Matrix.transpose_add, hNT, hvT]
  have hformeq : ∀ v : Fin k → ℝ, v ⬝ᵥ ((N + Matrix.vecMulVec g g) *ᵥ v)
      = v ⬝ᵥ (N *ᵥ v) + (g ⬝ᵥ v) ^ 2 := by
    intro v
    rw [Matrix.add_mulVec, dotProduct_add, vecMulVec_mulVec_eq,
      dotProduct_smul, smul_eq_mul, dotProduct_comm v g]
    ring
  constructor
  · -- PSD ⟹ the cap is ≤ −1
    intro hpsd
    have hform : ∀ v : Fin k → ℝ,
        0 ≤ v ⬝ᵥ (N *ᵥ v) + (g ⬝ᵥ v) ^ 2 := by
      intro v
      have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 v
      rwa [star_trivial, hformeq v] at h
    have hats := hform s
    rw [hgs, hq] at hats
    have hatw := hform w
    by_contra hgt
    rw [not_le] at hgt
    have hq0 : 0 ≤ g ⬝ᵥ (N⁻¹ *ᵥ g) := by nlinarith [hats]
    have hgw2 : 0 < (g ⬝ᵥ w) ^ 2 := by nlinarith [hatw, hw]
    have hgwne : g ⬝ᵥ w ≠ 0 := by
      intro h0
      rw [h0] at hgw2
      simp at hgw2
    rcases hq0.lt_or_eq with hqpos | hqzero
    · -- q > 0: v = w − ((g·w)/q)·s kills the g-part but stays N-negative
      set lam : ℝ := (g ⬝ᵥ w) / (g ⬝ᵥ (N⁻¹ *ᵥ g)) with hlam
      have hlamq : lam * (g ⬝ᵥ (N⁻¹ *ᵥ g)) = g ⬝ᵥ w := by
        rw [hlam]
        exact div_mul_cancel₀ _ hqpos.ne'
      have hcontr := hform (w - lam • s)
      have hgv : g ⬝ᵥ (w - lam • s) = 0 := by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hgs, hq, hlamq,
          sub_self]
      have hNv : (w - lam • s) ⬝ᵥ (N *ᵥ (w - lam • s))
          = w ⬝ᵥ (N *ᵥ w) - 2 * lam * (g ⬝ᵥ w)
            + lam ^ 2 * (g ⬝ᵥ (N⁻¹ *ᵥ g)) := by
        simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
          dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        rw [hbilin w s, hsNw, hq]
        ring
      rw [hgv, hNv] at hcontr
      -- the value is wᵀNw − (g·w)²/q < 0
      have hsub : lam ^ 2 * (g ⬝ᵥ (N⁻¹ *ᵥ g)) = lam * (g ⬝ᵥ w) := by
        rw [show lam ^ 2 = lam * lam from sq lam, mul_assoc, hlamq]
      have hlampos : 0 < lam * (g ⬝ᵥ w) := by
        have : lam * (g ⬝ᵥ w) * (g ⬝ᵥ (N⁻¹ *ᵥ g)) = (g ⬝ᵥ w) ^ 2 := by
          linear_combination (g ⬝ᵥ w) * hlamq
        nlinarith [hgw2, hqpos, this]
      nlinarith [hcontr, hsub, hw, hlampos]
    · -- q = 0: the form is affine in α along α·s + w with nonzero slope
      set alp : ℝ := -((g ⬝ᵥ w) ^ 2 + w ⬝ᵥ (N *ᵥ w) + 1) / (2 * (g ⬝ᵥ w))
        with halp
      have hcontr := hform (alp • s + w)
      have hgv : g ⬝ᵥ (alp • s + w) = g ⬝ᵥ w := by
        rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hgs, hq, ← hqzero]
        ring
      have hNv : (alp • s + w) ⬝ᵥ (N *ᵥ (alp • s + w))
          = 2 * alp * (g ⬝ᵥ w) + w ⬝ᵥ (N *ᵥ w) := by
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
          dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        rw [hbilin w s, hsNw, hq, ← hqzero]
        ring
      rw [hgv, hNv] at hcontr
      have hval : 2 * alp * (g ⬝ᵥ w)
          = -((g ⬝ᵥ w) ^ 2 + w ⬝ᵥ (N *ᵥ w) + 1) := by
        rw [halp]
        field_simp
      nlinarith [hcontr, hval]
  · -- q ≤ −1 ⟹ PSD
    intro hle
    have hsneg : s ⬝ᵥ (N *ᵥ s) < 0 := by
      rw [hq]
      linarith
    have hSpsd := psd_on_complement_transfer hNT hw hWpsd hsneg
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hsumT, fun v => ?_⟩
    rw [star_trivial, hformeq v]
    have hqne : s ⬝ᵥ (N *ᵥ s) ≠ 0 := hsneg.ne
    set bet : ℝ := (v ⬝ᵥ (N *ᵥ s)) / (s ⬝ᵥ (N *ᵥ s)) with hbet
    set v1 : Fin k → ℝ := v - bet • s with hv1
    have hbets : bet * (s ⬝ᵥ (N *ᵥ s)) = v ⬝ᵥ (N *ᵥ s) := by
      rw [hbet]
      exact div_mul_cancel₀ _ hqne
    have hv1s : v1 ⬝ᵥ (N *ᵥ s) = 0 := by
      rw [hv1, sub_dotProduct, smul_dotProduct, smul_eq_mul, hbets, sub_self]
    have hv1psd := hSpsd v1 hv1s
    have hvdec : v = v1 + bet • s := by rw [hv1]; abel
    have hgv1 : g ⬝ᵥ v1 = 0 := by
      rw [← hNs, dotProduct_comm]
      exact hv1s
    have hgv : g ⬝ᵥ v = bet * (s ⬝ᵥ (N *ᵥ s)) := by
      rw [hvdec, dotProduct_add, hgv1, zero_add, dotProduct_smul, smul_eq_mul,
        hgs]
    have hNv : v ⬝ᵥ (N *ᵥ v)
        = bet ^ 2 * (s ⬝ᵥ (N *ᵥ s)) + v1 ⬝ᵥ (N *ᵥ v1) := by
      rw [hvdec]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
        dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [hbilin s v1, hv1s]
      ring
    have hqle : s ⬝ᵥ (N *ᵥ s) ≤ -1 := by
      rw [hq]
      exact hle
    have hqq : 0 ≤ (s ⬝ᵥ (N *ᵥ s)) * (1 + s ⬝ᵥ (N *ᵥ s)) := by
      nlinarith [hqle, sq_nonneg (1 + s ⬝ᵥ (N *ᵥ s))]
    rw [hNv, hgv]
    nlinarith [hv1psd, mul_nonneg (sq_nonneg bet) hqq]

/-- The cap in trace form, as the certificate layer consumes it. -/
theorem cap_criterion_trace {N : Matrix (Fin k) (Fin k) ℝ}
    (hNT : Nᵀ = N) (hdet : IsUnit N.det)
    {w : Fin k → ℝ} (hw : w ⬝ᵥ (N *ᵥ w) < 0)
    (hWpsd : ∀ v, v ⬝ᵥ (N *ᵥ w) = 0 → 0 ≤ v ⬝ᵥ (N *ᵥ v))
    (g : Fin k → ℝ) :
    (N + Matrix.vecMulVec g g).PosSemidef ↔
      Matrix.trace (N⁻¹ * Matrix.vecMulVec g g) ≤ -1 := by
  rw [cap_criterion hNT hdet hw hWpsd g, mul_vecMulVec_eq,
    Matrix.trace_vecMulVec, dotProduct_comm]

end Gtz

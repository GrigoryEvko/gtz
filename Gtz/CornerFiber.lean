/-
# Theorem B_k: the exact (k+1)-cycle corner fiber closes at every rank

The zero-margin extremal of the entire problem is the (k+1)-cycle: k+1 vectors
h_i ∈ ℝᵏ with |h_i|² = k, ⟨h_i, h_j⟩ = −1 (the regular simplex at leverage k).
This file proves, for every design containing these exact heavies — any weights,
any extras, any rank, any size:

1. `simplex_sum_eq_zero`      — Σ h_i = 0 (from the Gram alone);
2. `simplex_frame_operator`   — Σ h_i h_iᵀ = (k+1)·I. Structural proof, no
   spectral theory: the frame operator satisfies S² = (k+1)S (Gram algebra), so
   the symmetric remainder R = (k+1)I − S obeys R² = (k+1)R, hence is PSD by
   polarization (`posSemidef_of_sq_eq_smul`), with trace 0 — and a PSD matrix
   of trace zero is zero;
3. `corner_balance_forced`    — Σ_e t_e(ℓ_e − k) = 0 (audit F1, diary §52);
4. `corner_fiber_dominates`   — **Theorem B_k**: S_Q − I = k·I ≻ 0, every
   pivot is ℓ_e/k, the outsiders' excess vanishes by the forced balance, and
   the tie-pigeonhole fires — ρ = 1 exactly on the wall at every rank.

Proven informally: k=3 `gtz_proof_gtz3_ratpigeon.md` §5 (3/3 audits), general k
`gtz_proof_gtz_allk_lift.md` §2.4 (2/2 audits, with the F1 case-split
correction). Here the pigeonhole needs only 1 ≤ k.
-/
import Mathlib
import Gtz.Basic
import Gtz.Sanity
import Gtz.SchurRankOne
import Gtz.TraceIdentity

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- a bᵀ summed over the right argument. -/
theorem vecMulVec_sum_right {ι : Type*} (a : Fin k → ℝ) (s : Finset ι)
    (v : ι → Fin k → ℝ) :
    Matrix.vecMulVec a (∑ j ∈ s, v j) = ∑ j ∈ s, Matrix.vecMulVec a (v j) := by
  ext p q
  simp [Matrix.vecMulVec_apply, Matrix.sum_apply, Finset.sum_apply, Finset.mul_sum]

/-- Product of two atoms: (a aᵀ)(b bᵀ) = ⟨a,b⟩ · (a bᵀ). -/
theorem atomMatrix_mul_atomMatrix (a b : Fin k → ℝ) :
    atomMatrix a * atomMatrix b = (a ⬝ᵥ b) • Matrix.vecMulVec a b := by
  rw [atomMatrix, atomMatrix, mul_vecMulVec_eq, vecMulVec_mulVec_eq,
    Matrix.smul_vecMulVec]

/-- A symmetric real matrix whose square is a positive multiple of itself is
PSD — polarization through the square: c·⟨x, Rx⟩ = ⟨Rx, Rx⟩ ≥ 0. No spectral
theory. -/
theorem posSemidef_of_sq_eq_smul {R : Matrix (Fin k) (Fin k) ℝ} {c : ℝ}
    (hRT : Rᵀ = R) (hR2 : R * R = c • R) (hc : 0 < c) : R.PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hRT, fun x => ?_⟩
  rw [star_trivial]
  have hkey : c * (x ⬝ᵥ (R *ᵥ x)) = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by
    calc c * (x ⬝ᵥ (R *ᵥ x)) = x ⬝ᵥ (c • (R *ᵥ x)) := by
          rw [dotProduct_smul, smul_eq_mul]
      _ = x ⬝ᵥ ((c • R) *ᵥ x) := by rw [Matrix.smul_mulVec]
      _ = x ⬝ᵥ ((R * R) *ᵥ x) := by rw [← hR2]
      _ = x ⬝ᵥ (R *ᵥ (R *ᵥ x)) := by rw [← Matrix.mulVec_mulVec]
      _ = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := dot_mulVec_comm hRT x (R *ᵥ x)
  have hsq : 0 ≤ (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun t _ => mul_self_nonneg _
  nlinarith [hkey, hsq, hc]

/-- The k+1 simplex vectors at leverage k sum to zero — from the Gram alone:
|Σ h_i|² telescopes to (k+1)·k − (k+1)·k = 0, and a real vector of zero norm
is zero. -/
theorem simplex_sum_eq_zero (hvec : Fin (k + 1) → (Fin k → ℝ))
    (hdiag : ∀ i, hvec i ⬝ᵥ hvec i = (k : ℝ))
    (hoff : ∀ i j, i ≠ j → hvec i ⬝ᵥ hvec j = -1) :
    ∑ i, hvec i = 0 := by
  have hnorm : (∑ i, hvec i) ⬝ᵥ (∑ i, hvec i) = 0 := by
    rw [sum_dotProduct]
    have hrowsum : ∀ i : Fin (k + 1), hvec i ⬝ᵥ (∑ j, hvec j) = 0 := by
      intro i
      rw [dotProduct_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag i]
      have hoffsum : ∑ j ∈ Finset.univ.erase i, hvec i ⬝ᵥ hvec j
          = ∑ _j ∈ Finset.univ.erase i, (-1 : ℝ) :=
        Finset.sum_congr rfl fun j hj => hoff i j (Finset.ne_of_mem_erase hj).symm
      rw [hoffsum, Finset.sum_const, nsmul_eq_mul,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      push_cast
      ring
    exact Finset.sum_eq_zero fun i _ => hrowsum i
  funext t
  have hsq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun s _ => mul_self_nonneg ((∑ i, hvec i) s))).mp
    (by simpa [dotProduct] using hnorm)
  simpa using mul_self_eq_zero.mp (hsq t (Finset.mem_univ t))

/-- **The simplex frame identity**: k+1 vectors in ℝᵏ with Gram diagonal k and
off-diagonal −1 form a tight frame, Σ h_i h_iᵀ = (k+1)·I. Structural proof:
each row of S·S collapses to (k+1)·h_i h_iᵀ by the Gram and Σh = 0, so
S² = (k+1)S; the symmetric remainder R = (k+1)I − S then satisfies
R² = (k+1)R, is PSD by polarization, and has trace zero — hence R = 0. -/
theorem simplex_frame_operator (hvec : Fin (k + 1) → (Fin k → ℝ))
    (hdiag : ∀ i, hvec i ⬝ᵥ hvec i = (k : ℝ))
    (hoff : ∀ i j, i ≠ j → hvec i ⬝ᵥ hvec j = -1) :
    ∑ i, atomMatrix (hvec i) = ((k : ℝ) + 1) • 1 := by
  have hsum0 : ∑ i, hvec i = 0 := simplex_sum_eq_zero hvec hdiag hoff
  have hesum : ∀ i : Fin (k + 1),
      ∑ j ∈ Finset.univ.erase i, hvec j = -(hvec i) := by
    intro i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hsum0]
    exact zero_sub _
  -- Gram algebra, row by row: A_i · S = (k+1) · A_i
  have hrow : ∀ i : Fin (k + 1),
      atomMatrix (hvec i) * ∑ j, atomMatrix (hvec j)
        = ((k : ℝ) + 1) • atomMatrix (hvec i) := by
    intro i
    calc atomMatrix (hvec i) * ∑ j, atomMatrix (hvec j)
        = ∑ j, (hvec i ⬝ᵥ hvec j) • Matrix.vecMulVec (hvec i) (hvec j) := by
          rw [Matrix.mul_sum]
          exact Finset.sum_congr rfl fun j _ => atomMatrix_mul_atomMatrix _ _
      _ = (hvec i ⬝ᵥ hvec i) • Matrix.vecMulVec (hvec i) (hvec i)
            + ∑ j ∈ Finset.univ.erase i,
                (hvec i ⬝ᵥ hvec j) • Matrix.vecMulVec (hvec i) (hvec j) :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      _ = (k : ℝ) • Matrix.vecMulVec (hvec i) (hvec i)
            + ∑ j ∈ Finset.univ.erase i,
                (-1 : ℝ) • Matrix.vecMulVec (hvec i) (hvec j) := by
          rw [hdiag i]
          congr 1
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hoff i j (Finset.ne_of_mem_erase hj).symm]
      _ = (k : ℝ) • Matrix.vecMulVec (hvec i) (hvec i)
            - Matrix.vecMulVec (hvec i) (∑ j ∈ Finset.univ.erase i, hvec j) := by
          simp only [neg_one_smul]
          rw [Finset.sum_neg_distrib, ← vecMulVec_sum_right, ← sub_eq_add_neg]
      _ = (k : ℝ) • Matrix.vecMulVec (hvec i) (hvec i)
            - Matrix.vecMulVec (hvec i) (-(hvec i)) := by rw [hesum i]
      _ = ((k : ℝ) + 1) • atomMatrix (hvec i) := by
          rw [show -(hvec i) = (-1 : ℝ) • (hvec i) from (neg_one_smul ℝ _).symm,
            Matrix.vecMulVec_smul, neg_one_smul, sub_neg_eq_add]
          simp only [atomMatrix]
          module
  have hS2 : (∑ i, atomMatrix (hvec i)) * ∑ i, atomMatrix (hvec i)
      = ((k : ℝ) + 1) • ∑ i, atomMatrix (hvec i) := by
    rw [Finset.sum_mul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => hrow i
  -- the remainder R = (k+1)·I − S: symmetric, R² = (k+1)·R, trace 0 ⟹ R = 0
  have hSpsd : (∑ i, atomMatrix (hvec i)).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ => posSemidef_atomMatrix _
  have hST : (∑ i, atomMatrix (hvec i))ᵀ = ∑ i, atomMatrix (hvec i) :=
    transpose_eq_of_isHermitian hSpsd.1
  have hRT : (((k : ℝ) + 1) • 1 - ∑ i, atomMatrix (hvec i))ᵀ
      = ((k : ℝ) + 1) • 1 - ∑ i, atomMatrix (hvec i) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hST]
  have hR2 : (((k : ℝ) + 1) • 1 - ∑ i, atomMatrix (hvec i))
        * (((k : ℝ) + 1) • 1 - ∑ i, atomMatrix (hvec i))
      = ((k : ℝ) + 1) • (((k : ℝ) + 1) • 1 - ∑ i, atomMatrix (hvec i)) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      hS2, smul_sub]
    module
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hRpsd : (((k : ℝ) + 1) • 1 - ∑ i, atomMatrix (hvec i)).PosSemidef :=
    posSemidef_of_sq_eq_smul hRT hR2 hkpos
  have htrS : Matrix.trace (∑ i, atomMatrix (hvec i)) = ((k : ℝ) + 1) * k := by
    rw [Matrix.trace_sum]
    have hterm : ∀ i : Fin (k + 1),
        Matrix.trace (atomMatrix (hvec i)) = (k : ℝ) := by
      intro i
      rw [trace_atomMatrix, leverageOf, ← hdiag i, dotProduct]
      exact Finset.sum_congr rfl fun t _ => pow_two _
    calc ∑ i, Matrix.trace (atomMatrix (hvec i))
        = ∑ _i : Fin (k + 1), (k : ℝ) := Finset.sum_congr rfl fun i _ => hterm i
      _ = ((k : ℝ) + 1) * k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have htrR : Matrix.trace (((k : ℝ) + 1) • 1 - ∑ i, atomMatrix (hvec i)) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, htrS, smul_eq_mul,
      Fintype.card_fin]
    ring
  have hR0 := hRpsd.trace_eq_zero_iff.mp htrR
  exact (sub_eq_zero.mp hR0).symm

/-- The exact-corner hypothesis: an injective embedding of k+1 simplex heavies
at leverage k (Gram: diagonal k, off-diagonal −1) into the design. -/
def HasExactCorner (D : WeightedDesign m k) (emb : Fin (k + 1) → Fin m) : Prop :=
  Function.Injective emb ∧
    (∀ i, leverageOf (D.atom (emb i)) = k) ∧
    (∀ i j, i ≠ j → ∑ t, D.atom (emb i) t * D.atom (emb j) t = -1)

section Corner

variable (D : WeightedDesign m k) (emb : Fin (k + 1) → Fin m)

/-- Gram diagonal in dot-product form. -/
theorem corner_dot_diag (hc : HasExactCorner D emb) (i : Fin (k + 1)) :
    D.atom (emb i) ⬝ᵥ D.atom (emb i) = (k : ℝ) := by
  have h := hc.2.1 i
  rw [leverageOf] at h
  rw [dotProduct, ← h]
  exact Finset.sum_congr rfl fun t _ => (pow_two _).symm

/-- Gram off-diagonal in dot-product form. -/
theorem corner_dot_off (hc : HasExactCorner D emb) {i j : Fin (k + 1)} (hij : i ≠ j) :
    D.atom (emb i) ⬝ᵥ D.atom (emb j) = -1 :=
  hc.2.2 i j hij

/-- The corner heavies sum to zero. -/
theorem corner_heavies_sum_zero (hc : HasExactCorner D emb) :
    ∑ i, D.atom (emb i) = 0 :=
  simplex_sum_eq_zero (fun i => D.atom (emb i)) (corner_dot_diag D emb hc)
    (fun _ _ hij => corner_dot_off D emb hc hij)

/-- **The corner frame operator is (k+1)·I** — the subset sum over the embedded
corner equals the simplex tight frame. -/
theorem corner_subsetSum_eq (hc : HasExactCorner D emb) :
    subsetSum D (Finset.univ.image emb) = ((k : ℝ) + 1) • 1 := by
  have himg : subsetSum D (Finset.univ.image emb)
      = ∑ i, atomMatrix (D.atom (emb i)) := by
    rw [subsetSum]
    exact Finset.sum_image fun x _ y _ h => hc.1 h
  rw [himg]
  exact simplex_frame_operator (fun i => D.atom (emb i)) (corner_dot_diag D emb hc)
    (fun _ _ hij => corner_dot_off D emb hc hij)

/-- **The forced balance** (audit F1, diary §52): at the exact corner fiber the
extras' weighted leverage-excess vanishes identically — pure trace algebra.
Consequently the Q₀-pigeonhole always fires at the tie. -/
theorem corner_balance_forced (hc : HasExactCorner D emb) :
    ∑ e ∈ (Finset.univ.image emb)ᶜ, D.weight e * (leverageOf (D.atom e) - k) = 0 := by
  obtain ⟨hinj, hlev, -⟩ := hc
  -- trace of Parseval: Σ_c t_c ℓ_c = k
  have htrace : ∑ c, D.weight c * leverageOf (D.atom c) = (k : ℝ) := by
    have h := congrArg Matrix.trace D.isParseval
    simpa [Matrix.trace_sum, Matrix.trace_smul, trace_atomMatrix, smul_eq_mul,
      Matrix.trace_one, Fintype.card_fin] using h
  have hsplitL : ∑ c ∈ Finset.univ.image emb, D.weight c * leverageOf (D.atom c)
      + ∑ c ∈ (Finset.univ.image emb)ᶜ, D.weight c * leverageOf (D.atom c) = (k : ℝ) := by
    rw [Finset.sum_add_sum_compl]; exact htrace
  have hsplitW : ∑ c ∈ Finset.univ.image emb, D.weight c
      + ∑ c ∈ (Finset.univ.image emb)ᶜ, D.weight c = 1 := by
    rw [Finset.sum_add_sum_compl]; exact D.weight_sum_one
  -- the corner heavies have leverage exactly k
  have hins : ∑ c ∈ Finset.univ.image emb, D.weight c * leverageOf (D.atom c)
      = (k : ℝ) * ∑ c ∈ Finset.univ.image emb, D.weight c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hcS => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcS
    rw [hlev i]; ring
  have hgoal : ∑ e ∈ (Finset.univ.image emb)ᶜ, D.weight e * (leverageOf (D.atom e) - k)
      = (∑ e ∈ (Finset.univ.image emb)ᶜ, D.weight e * leverageOf (D.atom e))
        - (k : ℝ) * ∑ e ∈ (Finset.univ.image emb)ᶜ, D.weight e := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [hgoal,
    show ∑ e ∈ (Finset.univ.image emb)ᶜ, D.weight e
        = 1 - ∑ c ∈ Finset.univ.image emb, D.weight c by linarith [hsplitW]]
  ring_nf
  ring_nf at hins hsplitL
  linarith [hsplitL, hins]

/-- **Theorem B_k.** The exact (k+1)-cycle corner fiber of weighted (m,k)
closes: every design containing the exact simplex heavies has a dominating
k-subset — drawn from the corner itself. S_Q − I = k·I is PD, every pivot is
ℓ/k, the outsiders' excess vanishes by the forced balance, and the
tie-pigeonhole fires: ρ = 1 exactly on the wall, at every rank and size. -/
theorem corner_fiber_dominates (hk : 1 ≤ k) (hc : HasExactCorner D emb) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates D C := by
  have hk0 : 0 < k := hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hS := corner_subsetSum_eq D emb hc
  have hcard : (Finset.univ.image emb).card = k + 1 := by
    rw [Finset.card_image_of_injective _ hc.1, Finset.card_univ, Fintype.card_fin]
  -- the shifted corner frame is the scalar matrix k·I ≻ 0
  have hsub : subsetSum D (Finset.univ.image emb) - 1
      = (k : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [hS]
    module
  have hQpd : (subsetSum D (Finset.univ.image emb) - 1).PosDef := by
    rw [hsub]
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
    · exact isHermitian_of_transpose_eq
        (by rw [Matrix.transpose_smul, Matrix.transpose_one])
    · rw [star_trivial, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
        smul_eq_mul]
      have hxne : ∃ t, x t ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hx (funext hall)
      obtain ⟨t, ht⟩ := hxne
      have hxx : 0 < x ⬝ᵥ x := by
        simp only [dotProduct]
        exact Finset.sum_pos' (fun s _ => mul_self_nonneg _)
          ⟨t, Finset.mem_univ t, mul_self_pos.mpr ht⟩
      exact mul_pos hkpos hxx
  -- the inverse is k⁻¹·I, so every pivot is leverage/k
  have hNinv : (subsetSum D (Finset.univ.image emb) - 1)⁻¹
      = (k : ℝ)⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    apply Matrix.inv_eq_left_inv
    rw [hsub, smul_mul_assoc, one_mul, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hkpos), one_smul]
  have hpivot : ∀ e, pivot D (Finset.univ.image emb) e
      = leverageOf (D.atom e) / k := by
    intro e
    simp only [pivot]
    rw [hNinv, smul_mul_assoc, one_mul, Matrix.trace_smul, smul_eq_mul,
      trace_atomMatrix]
    ring
  -- the outsiders' excess is k⁻¹ times the forced balance: zero
  have houtside : ∑ e ∈ (Finset.univ.image emb)ᶜ,
      D.weight e * (pivot D (Finset.univ.image emb) e - 1) ≤ 0 := by
    have hbal := corner_balance_forced D emb hc
    have heq : ∑ e ∈ (Finset.univ.image emb)ᶜ,
        D.weight e * (pivot D (Finset.univ.image emb) e - 1)
        = (k : ℝ)⁻¹ * ∑ e ∈ (Finset.univ.image emb)ᶜ,
            D.weight e * (leverageOf (D.atom e) - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [hpivot e]
      field_simp
    rw [heq, hbal, mul_zero]
  obtain ⟨d, hd, hdom⟩ :=
    pigeonhole D hk (Finset.univ.image emb) hQpd hcard houtside
  refine ⟨(Finset.univ.image emb).erase d, ?_, hdom⟩
  rw [Finset.card_erase_of_mem hd, hcard]
  omega

end Corner

end Gtz

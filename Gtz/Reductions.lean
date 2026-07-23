/-
# The reduction architecture: base ranks, the canonical list, and the endgame

The campaign's theorem-grade skeleton (diary §§42–52):

* rank 1 = pigeonhole; rank 2 = Sengupta–Pautov (arXiv:2604.05944), weighted form
  via atom replication + density;
* Theorem L (canonical list, `gtz_proof_gtz_allk_lift.md` §3.4): via crystallization
  M(s) = s(s+1)/2 + 1 and Naimark duality, GTZ for ALL n and ALL k is equivalent to
  the finite-per-rank list { weighted (m,s) : s ≥ 2, 2s ≤ m ≤ s(s+1)/2 + 1 };
* the binding residue: closing weighted (6,3) and (7,3) closes rank 3 for all n and
  co-rank ≤ 3 for every k. Weighted (6,3) is the single binding object of the
  hierarchy (diary §45, §52).

STATUS: statements (roadmap targets); proofs pending. `gtz_rank_one` is the
recommended first full end-to-end exercise of the definitions.
-/
import Mathlib
import Gtz.Basic
import Gtz.Sanity
import Gtz.Crystallization
import Gtz.Naimark
import Gtz.Deflation
import Gtz.RankTwo

namespace Gtz

open Matrix

/-- Rank 1 is the pigeonhole: Σ t_c g_c² = 1 with Σ t_c = 1 forces some g_c² ≥ 1. -/
theorem gtz_rank_one : GtzWeightedAll 1 := by
  intro m D
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- no atoms cannot resolve the identity: Parseval is contradictory
    subst hm
    have hp := D.isParseval
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hp
    have hentry := congrArg (fun M => M 0 0) hp
    simp at hentry
  · -- scalar Parseval at the (0,0) entry
    have hscalar : ∑ c, D.weight c * (D.atom c 0 * D.atom c 0) = 1 := by
      have h := congrArg (fun M => M 0 0) D.isParseval
      simpa [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply, Matrix.one_apply,
        Matrix.smul_apply, smul_eq_mul] using h
    -- pigeonhole: some atom has squared length ≥ 1
    have hex : ∃ c, 1 ≤ D.atom c 0 * D.atom c 0 := by
      by_contra hno
      push Not at hno
      have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
        Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)
      have hlt : ∑ c, D.weight c * (D.atom c 0 * D.atom c 0) < ∑ c, D.weight c := by
        refine Finset.sum_lt_sum_of_nonempty hne fun c _ => ?_
        nlinarith [hno c, D.weight_pos c]
      rw [hscalar, D.weight_sum_one] at hlt
      exact lt_irrefl 1 hlt
    obtain ⟨c, hc⟩ := hex
    refine ⟨{c}, Finset.card_singleton c, ?_⟩
    -- the 1×1 block g² − 1 is a nonnegative multiple of the identity
    have hmat : subsetSum D {c} - 1
        = (D.atom c 0 * D.atom c 0 - 1) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i j
      have hi : i = 0 := Subsingleton.elim i 0
      have hj : j = 0 := Subsingleton.elim j 0
      subst hi; subst hj
      simp [subsetSum, atomMatrix, Matrix.vecMulVec_apply,
        Matrix.smul_apply, smul_eq_mul]
    rw [Dominates, hmat]
    exact Matrix.PosSemidef.one.smul (by linarith)

/-- A design's atoms span, so its size is at least its rank: the evaluation
map u ↦ (⟨g_c, u⟩)_c is injective into ℝᵐ. -/
theorem rank_le_of_design (D : WeightedDesign m k) : k ≤ m := by
  let evalAtoms : (Fin k → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun u c => D.atom c ⬝ᵥ u
      map_add' := fun u v => by
        funext c
        simp [dotProduct_add]
      map_smul' := fun r u => by
        funext c
        simp [dotProduct_smul] }
  have hker : ∀ u, evalAtoms u = 0 → u = 0 := fun u hu =>
    eq_zero_of_forall_atom_dot_eq_zero D fun c => congrFun hu c
  have hinj : Function.Injective evalAtoms :=
    LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi, Module.finrank_pi, Fintype.card_fin,
    Fintype.card_fin] at hle

/-- At m = k the whole design dominates: S − I = Σ (1−t_c)·g_cg_cᵀ ⪰ 0. -/
theorem gtzWeighted_square (k : ℕ) : GtzWeighted k k := by
  intro D
  refine ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin], ?_⟩
  have hsub : subsetSum D Finset.univ - 1
      = ∑ c, (1 - D.weight c) • atomMatrix (D.atom c) := by
    rw [subsetSum, ← D.isParseval, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [sub_smul, one_smul]
  show (subsetSum D Finset.univ - 1).PosSemidef
  rw [hsub]
  refine Matrix.posSemidef_sum Finset.univ fun c _ => ?_
  have hle1 : D.weight c ≤ 1 := by
    rw [← D.weight_sum_one]
    exact Finset.single_le_sum (fun c' _ => (D.weight_pos c').le)
      (Finset.mem_univ c)
  exact (posSemidef_atomMatrix (D.atom c)).smul (by linarith)

/-- **Duality descent**: weighted GTZ at the complementary rank m − k gives
weighted GTZ at (m, k) — the dominating co-rank subset complements back. -/
theorem gtzWeighted_of_dual_rank (hk : 1 ≤ k) (hkm : k + 1 ≤ m)
    (hdual : GtzWeighted m (m - k)) : GtzWeighted m k := by
  intro D
  obtain ⟨Ddual, -, hdualiff⟩ := weighted_naimark_duality hk hkm D
  obtain ⟨Cdual, hCdualcard, hCdualdom⟩ := hdual Ddual
  refine ⟨Cdualᶜ, ?_, ?_⟩
  · rw [Finset.card_compl, Fintype.card_fin, hCdualcard]
    omega
  · rw [hdualiff Cdualᶜ
      (by rw [Finset.card_compl, Fintype.card_fin, hCdualcard]; omega),
      compl_compl]
    exact hCdualdom

/-- **Rank 2 is proven**: the weighted Sengupta–Pautov theorem, by strong
induction on the size. A light atom (leverage ≤ 1) deflates one size down
(`dominating_of_light_atom`); an all-heavy design contains a dominating pair
outright (`exists_dominating_pair_of_heavy`, the de-spectralized Case-B
pairing — finite sums and squares, no spectral theorem, no Perron–Frobenius). -/
theorem gtz_rank_two : GtzWeightedAll 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro D
    have hm2 : 2 ≤ m := rank_le_of_design D
    by_cases hlight : ∃ d, leverageOf (D.atom d) ≤ 1
    · obtain ⟨d, hd⟩ := hlight
      obtain ⟨mpred, rfl⟩ : ∃ mpred, m = mpred + 1 := ⟨m - 1, by omega⟩
      exact dominating_of_light_atom D (by omega) (ih mpred (by omega)) d hd
    · push Not at hlight
      exact exists_dominating_pair_of_heavy D hlight

/-- **Rank 2 collapses to the single weighted case (4,2)**: crystallization
caps the support at M(2) = 4; below it the ledger is vacuous m ≤ 1, the
square m = 2, and duality descent to rank 1 at m = 3. -/
theorem gtz_rank_two_of_four_two (h42 : GtzWeighted 4 2) :
    GtzWeightedAll 2 := by
  refine crystallization 2 fun m hm => ?_
  norm_num at hm
  interval_cases m
  · exact fun D => absurd (rank_le_of_design D) (by omega)
  · exact fun D => absurd (rank_le_of_design D) (by omega)
  · exact gtzWeighted_square 2
  · exact gtzWeighted_of_dual_rank (by omega) (by omega) (gtz_rank_one 3)
  · exact h42

/-- **The two binding cases close rank 3** (rank 2 is now a theorem):
crystallization at k = 3 has M(3) = 7, and the ledger below 6 is
vacuous m ≤ 2, the square m = 3, duality descent to rank 1 at m = 4 and to
the PROVEN rank 2 at m = 5. -/
theorem rank_three_of_the_two_residuals
    (h63 : GtzWeighted 6 3) (h73 : GtzWeighted 7 3) :
    GtzWeightedAll 3 := by
  refine crystallization 3 fun m hm => ?_
  norm_num at hm
  interval_cases m
  · exact fun D => absurd (rank_le_of_design D) (by omega)
  · exact fun D => absurd (rank_le_of_design D) (by omega)
  · exact fun D => absurd (rank_le_of_design D) (by omega)
  · exact gtzWeighted_square 3
  · exact gtzWeighted_of_dual_rank (by omega) (by omega) (gtz_rank_one 4)
  · exact gtzWeighted_of_dual_rank (by omega) (by omega) (gtz_rank_two 5)
  · exact h63
  · exact h73

/-- **Theorem L (the canonical list).** GTZ at every rank and size follows from
the finite-per-rank canonical list — the master reduction of the program.
Strong induction on the rank: below the rank there are no designs, at the rank
the square dominates, between k and 2k the duality descends to a smaller rank,
and the canonical window 2k ≤ m ≤ M(k) is the hypothesis. Rank 2 needs no
separate theorem: it IS the list entry (4,2). -/
theorem gtz_of_canonical_list
    (hlist : ∀ s m', 2 ≤ s → 2 * s ≤ m' → m' ≤ s * (s + 1) / 2 + 1 →
      GtzWeighted m' s) :
    ∀ k, 1 ≤ k → GtzWeightedAll k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases eq_or_lt_of_le hk with hk1 | hk2
    · rw [← hk1]
      exact gtz_rank_one
    · refine crystallization k fun m hm => ?_
      rcases lt_or_ge m k with hmk | hmk
      · exact fun D => absurd (rank_le_of_design D) (by omega)
      · rcases eq_or_lt_of_le hmk with hmk1 | hmk2
        · rw [← hmk1]
          exact gtzWeighted_square k
        · rcases lt_or_ge m (2 * k) with hm2k | hm2k
          · exact gtzWeighted_of_dual_rank hk (by omega)
              (ih (m - k) (by omega) (by omega) m)
          · exact hlist k m hk2 hm2k hm

/-- The row design of an orthonormal-column matrix: rows scaled by √n at
uniform weights 1/n. Parseval is exactly AᵀA = I through the frame dictionary. -/
noncomputable def rowDesign {n k : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin k) ℝ)
    (hortho : Aᵀ * A = 1) : WeightedDesign n k where
  atom r := Real.sqrt (n : ℝ) • A r
  weight _ := (n : ℝ)⁻¹
  weight_pos _ := inv_pos.mpr (by exact_mod_cast hn)
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hn.ne')
  isParseval := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    calc ∑ r, (n : ℝ)⁻¹ • atomMatrix (Real.sqrt (n : ℝ) • A r)
        = ∑ r, atomMatrix (A r) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [atomMatrix_smul, Real.sq_sqrt hnR.le, smul_smul,
            inv_mul_cancel₀ (ne_of_gt hnR), one_smul]
      _ = 1 := by rw [← transpose_mul_self_eq_sum_rows, hortho]

/-- The weighted ⟹ original bridge (t = 1/n specialization plus the standard
frame dictionary): weighted GTZ at rank k gives the 1997 statement for all n.
The dominating subset C enumerates as the row pick via `Finset.orderEmbOfFin`,
and BᵀB − (1/n)·I = (1/n)·(S_C − I) transfers PSD by nonnegative scaling. -/
theorem original_of_weighted_single {n k : ℕ} (h : GtzWeighted n k)
    (hn : 0 < n) : GtzOriginal n k := by
  intro A hortho
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨C, hcard, hdom⟩ := h (rowDesign hn A hortho)
  refine ⟨C.orderEmbOfFin hcard, (C.orderEmbOfFin hcard).injective, ?_⟩
  -- the picked block is the subset atom sum of the unscaled rows
  have himage : Finset.univ.image (C.orderEmbOfFin hcard) = C := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Finset.range_orderEmbOfFin]
  have hsubmatrix : (A.submatrix (C.orderEmbOfFin hcard) id)ᵀ
        * (A.submatrix (C.orderEmbOfFin hcard) id)
      = ∑ r ∈ C, atomMatrix (A r) := by
    rw [transpose_mul_self_eq_sum_rows]
    conv_rhs => rw [← himage]
    rw [Finset.sum_image fun x _ y _ hxy => (C.orderEmbOfFin hcard).injective hxy]
    rfl
  -- the design's subset sum is n times that
  have hsubset : subsetSum (rowDesign hn A hortho) C
      = (n : ℝ) • ∑ r ∈ C, atomMatrix (A r) := by
    rw [subsetSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    show atomMatrix (Real.sqrt (n : ℝ) • A r) = (n : ℝ) • atomMatrix (A r)
    rw [atomMatrix_smul, Real.sq_sqrt hnR.le]
  -- BᵀB − (1/n)·I = (1/n)·(S_C − I)
  have hfinal : (A.submatrix (C.orderEmbOfFin hcard) id)ᵀ
        * (A.submatrix (C.orderEmbOfFin hcard) id) - (n : ℝ)⁻¹ • 1
      = (n : ℝ)⁻¹ • (subsetSum (rowDesign hn A hortho) C - 1) := by
    rw [hsubmatrix, hsubset, smul_sub, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hnR), one_smul]
  have hdomPsd : (subsetSum (rowDesign hn A hortho) C - 1).PosSemidef := hdom
  rw [hfinal]
  exact hdomPsd.smul (inv_pos.mpr hnR).le

/-- **The full characterization**: weighted GTZ at every rank is EQUIVALENT to
the finite canonical list — instantiation forward, Theorem L back. -/
theorem gtz_iff_canonical_list :
    (∀ k, 1 ≤ k → GtzWeightedAll k) ↔
      (∀ s m', 2 ≤ s → 2 * s ≤ m' → m' ≤ s * (s + 1) / 2 + 1 →
        GtzWeighted m' s) := by
  constructor
  · intro h s m' hs _ _
    exact h s (by omega) m'
  · exact gtz_of_canonical_list

/-- **Rank 3 is EXACTLY the two binding cases** — the frontier, as an iff. -/
theorem rank_three_iff_the_two_residuals :
    GtzWeightedAll 3 ↔ GtzWeighted 6 3 ∧ GtzWeighted 7 3 :=
  ⟨fun h => ⟨h 6, h 7⟩, fun ⟨h63, h73⟩ => rank_three_of_the_two_residuals h63 h73⟩

/-- The all-sizes form of the bridge. -/
theorem original_of_weighted (k : ℕ) (h : GtzWeightedAll k) :
    ∀ n, 0 < n → GtzOriginal n k := fun n hn =>
  original_of_weighted_single (h n) hn

/-- **The original 1997 statement at rank 1, all sizes.** -/
theorem gtz_original_rank_one (n : ℕ) (hn : 0 < n) : GtzOriginal n 1 :=
  original_of_weighted 1 gtz_rank_one n hn

/-- **The original 1997 statement at rank 2, all sizes** — the
Sengupta–Pautov theorem, fully formalized through its weighted
generalization. -/
theorem gtz_original_rank_two (n : ℕ) (hn : 0 < n) : GtzOriginal n 2 :=
  original_of_weighted 2 gtz_rank_two n hn

/-- **The endgame statement**: the finite canonical list closes the ORIGINAL
1997 problem for every matrix shape — GtzOriginal n k for all n ≥ 1, k ≥ 1,
unconditionally, given the list. The surviving list entries beyond the proven
rank ≤ 2 are (6,3), (7,3) and the windows 2s ≤ m ≤ s(s+1)/2 + 1 for s ≥ 4. -/
theorem gtz_original_of_canonical_list
    (hlist : ∀ s m', 2 ≤ s → 2 * s ≤ m' → m' ≤ s * (s + 1) / 2 + 1 →
      GtzWeighted m' s) :
    ∀ n k, 1 ≤ k → 0 < n → GtzOriginal n k := fun n k hk hn =>
  original_of_weighted k (gtz_of_canonical_list hlist k hk) n hn

/-- **Co-rank 1 is unconditional at every rank**: duality descent to the
pigeonhole. -/
theorem gtzWeighted_corank_one (k : ℕ) (hk : 1 ≤ k) :
    GtzWeighted (k + 1) k :=
  gtzWeighted_of_dual_rank hk (by omega)
    (by simpa using gtz_rank_one (k + 1))

/-- **Co-rank 2 is unconditional at every rank ≥ 2**: descent to the proven
rank 2 (at k = 2 it IS rank 2). -/
theorem gtzWeighted_corank_two (k : ℕ) (hk : 2 ≤ k) :
    GtzWeighted (k + 2) k := by
  rcases eq_or_lt_of_le hk with hk2 | hk3
  · rw [← hk2]
    exact gtz_rank_two 4
  · refine gtzWeighted_of_dual_rank (by omega) (by omega) ?_
    have h2 : k + 2 - k = 2 := by omega
    rw [h2]
    exact gtz_rank_two (k + 2)

/-- **The original 1997 statement on the whole solved boundary**: squares. -/
theorem gtz_original_square (n : ℕ) (hn : 0 < n) : GtzOriginal n n :=
  original_of_weighted_single (gtzWeighted_square n) hn

/-- Original form, co-rank 1: every (k+1)×k orthonormal-column matrix. -/
theorem gtz_original_corank_one (k : ℕ) (hk : 1 ≤ k) :
    GtzOriginal (k + 1) k :=
  original_of_weighted_single (gtzWeighted_corank_one k hk) (by omega)

/-- Original form, co-rank 2: every (k+2)×k orthonormal-column matrix. -/
theorem gtz_original_corank_two (k : ℕ) (hk : 2 ≤ k) :
    GtzOriginal (k + 2) k :=
  original_of_weighted_single (gtzWeighted_corank_two k hk) (by omega)

/-- **GTZ 1997 holds completely up to five rows**: for every n ≤ 5 and every
feasible rank, the original statement is a theorem — because k ≤ 5 forces
k ∈ {1, 2} or k ≥ n − 2, all on the proven boundary. The first open case is
exactly (n, k) = (6, 3). -/
theorem gtz_original_of_le_five (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hn : n ≤ 5) : GtzOriginal n k := by
  have hn0 : 0 < n := by omega
  rcases le_or_gt k 2 with hk2 | hk3
  · interval_cases k
    · exact gtz_original_rank_one n hn0
    · exact gtz_original_rank_two n hn0
  · -- k ≥ 3 and n ≤ 5 put us on the co-rank ≤ 2 boundary
    have hcorank : n = k ∨ n = k + 1 ∨ n = k + 2 := by omega
    rcases hcorank with h | h | h
    · subst h
      exact gtz_original_square n hn0
    · subst h
      exact gtz_original_corank_one k (by omega)
    · subst h
      exact gtz_original_corank_two k (by omega)

/-- The weighted analogue: every design with at most five atoms dominates,
at every rank. -/
theorem gtzWeighted_of_le_five (m k : ℕ) (hk : 1 ≤ k) (hm : m ≤ 5) :
    GtzWeighted m k := by
  intro D
  have hkm : k ≤ m := rank_le_of_design D
  rcases le_or_gt k 2 with hk2 | hk3
  · interval_cases k
    · exact gtz_rank_one m D
    · exact gtz_rank_two m D
  · have hcorank : m = k ∨ m = k + 1 ∨ m = k + 2 := by omega
    rcases hcorank with h | h | h
    · subst h
      exact gtzWeighted_square m D
    · subst h
      exact gtzWeighted_corank_one k (by omega) D
    · subst h
      exact gtzWeighted_corank_two k (by omega) D

end Gtz

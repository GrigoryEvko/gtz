/-
# Theorem N: the general-m weighted Naimark duality

For every weighted (m,k) design there is a dual weighted (m, m−k) design with
the SAME weights such that a k-subset C dominates in the primal iff its
complement Cᶜ dominates in the dual. Informally proven in four reversible
congruence steps (`gtz_proof_gtz_allk_lift.md` §3.2, audited twice; 2.9·10⁸
machine-validated subset instances).

Mechanized route (sqrt of MATRICES eliminated; only scalar square roots):

* W := Σ (1−t_c)·g_cg_cᵀ ≻ 0 (elementary: its form vanishing forces the
  Parseval form to vanish); whitening R with RᵀWR = I (`exists_congruence_to_one`,
  the C*-factorization);
* co-atoms h_c := Rᵀg_c, co-design A := [√(1−t_c)·h_cᵀ] with AᵀA = I;
  orthonormal completion [A | B] (`exists_orthonormal_completion`);
* dual design G_c := (√t_c)⁻¹·(row c of B), same weights — Parseval is BᵀB = I
  through the frame dictionary;
* the chain, for |C| = k (all steps two-sided):
  S_C − I = W − S_{Cᶜ}                                  (Parseval algebra)
  ⪰ 0 ⟺ I − YᵀY ⪰ 0                                    (congruence by R)
       ⟺ I − YYᵀ ⪰ 0                                    (CS transfer, PsdKit)
       ⟺ D_s|_{Cᶜ} − (AAᵀ)|_{Cᶜ} ⪰ 0                    (diagonal congruence √s)
       ⟺ (BBᵀ)|_{Cᶜ} − D_t|_{Cᶜ} ⪰ 0                    (completeness AAᵀ+BBᵀ=I)
       ⟺ ZZᵀ − I ⪰ 0                                    (diagonal congruence 1/√t)
       ⟺ ZᵀZ − I ⪰ 0 = S′_{Cᶜ} − I ⪰ 0                  (square transfer, PsdKit)
  where Y (resp. Z) stacks the rows h_e (resp. G_e) over e ∈ Cᶜ.

WARNING (recorded refutation, do not "simplify"): completing the primal
Parseval matrix V = [√t_c·g_cᵀ] instead of the co-design A FAILS already at
(m,k) = (2,1); the two coincide only at uniform weights.
-/
import Mathlib
import Gtz.Basic
import Gtz.Sanity
import Gtz.SchurRankOne
import Gtz.TraceIdentity
import Gtz.PsdKit
import Gtz.Completion
import Gtz.Crystallization

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- ab ᵀ times a matrix from the right: (a bᵀ)·P = a·(Pᵀb)ᵀ. -/
theorem vecMulVec_mul (a b : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ) :
    Matrix.vecMulVec a b * P = Matrix.vecMulVec a (Pᵀ *ᵥ b) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec,
    Matrix.transpose_apply, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Conjugating an atom: Pᵀ·(g gᵀ)·P = (Pᵀg)(Pᵀg)ᵀ. -/
theorem transpose_mul_atomMatrix_mul (P : Matrix (Fin k) (Fin k) ℝ)
    (g : Fin k → ℝ) :
    Pᵀ * atomMatrix g * P = atomMatrix (Pᵀ *ᵥ g) := by
  rw [atomMatrix, atomMatrix, mul_vecMulVec_eq, vecMulVec_mul]

/-- The quadratic form of a weighted atom sum: Σ w_c·(g_c ⬝ᵥ u)². -/
theorem dot_weighted_atoms_mulVec (w : Fin m → ℝ) (g : Fin m → (Fin k → ℝ))
    (u : Fin k → ℝ) :
    u ⬝ᵥ ((∑ c, w c • atomMatrix (g c)) *ᵥ u) = ∑ c, w c * (g c ⬝ᵥ u) ^ 2 := by
  have hterm : ∀ c, u ⬝ᵥ ((w c • atomMatrix (g c)) *ᵥ u)
      = w c * (g c ⬝ᵥ u) ^ 2 := by
    intro c
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, dotProduct_comm u (g c)]
    ring
  calc u ⬝ᵥ ((∑ c, w c • atomMatrix (g c)) *ᵥ u)
      = ∑ c, u ⬝ᵥ ((w c • atomMatrix (g c)) *ᵥ u) := by
        rw [← dotProduct_sum]
        congr 1
        ext j
        simp [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply,
          Finset.sum_comm (γ := Fin k), Finset.sum_mul]
    _ = ∑ c, w c * (g c ⬝ᵥ u) ^ 2 := Finset.sum_congr rfl fun c _ => hterm c

/-- Every weight of a design with at least two atoms is < 1. -/
theorem weight_lt_one (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    D.weight c < 1 := by
  obtain ⟨cother, hcother⟩ := Fintype.exists_ne_of_one_lt_card
    (by simp only [Fintype.card_fin]; omega) c
  have hsum := Finset.sum_erase_add Finset.univ D.weight (Finset.mem_univ c)
  rw [D.weight_sum_one] at hsum
  have hpos : 0 < ∑ x ∈ Finset.univ.erase c, D.weight x :=
    Finset.sum_pos' (fun x _ => (D.weight_pos x).le)
      ⟨cother, Finset.mem_erase.mpr ⟨hcother, Finset.mem_univ cother⟩,
        D.weight_pos cother⟩
  linarith

/-- Vectors annihilating every atom are zero — the atoms of a design span
(Parseval's form is |u|²). -/
theorem eq_zero_of_forall_atom_dot_eq_zero (D : WeightedDesign m k)
    {u : Fin k → ℝ} (hdots : ∀ c, D.atom c ⬝ᵥ u = 0) : u = 0 := by
  have hparse := congrArg (fun M => u ⬝ᵥ (M *ᵥ u)) D.isParseval
  simp only [Matrix.one_mulVec] at hparse
  rw [dot_weighted_atoms_mulVec] at hparse
  have hzero : u ⬝ᵥ u = 0 := by
    rw [← hparse]
    exact Finset.sum_eq_zero fun c _ => by rw [hdots c]; ring
  funext t
  have hsq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun s _ => mul_self_nonneg (u s))).mp hzero
  simpa using mul_self_eq_zero.mp (hsq t (Finset.mem_univ t))

/-- The co-Parseval operator W = Σ (1−t_c)·g_cg_cᵀ is positive definite:
its form vanishing forces every ⟨g_c, u⟩ to vanish, and then Parseval's form
says |u|² = 0. -/
theorem coParseval_posDef (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (∑ c, (1 - D.weight c) • atomMatrix (D.atom c)).PosDef := by
  have hspos : ∀ c, 0 < 1 - D.weight c := fun c => by
    linarith [weight_lt_one D hm c]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun u hu => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom c)).1]
  · rw [star_trivial, dot_weighted_atoms_mulVec]
    have hnn : ∀ c ∈ Finset.univ,
        0 ≤ (1 - D.weight c) * (D.atom c ⬝ᵥ u) ^ 2 := fun c _ =>
      mul_nonneg (hspos c).le (sq_nonneg _)
    rcases (Finset.sum_nonneg hnn).lt_or_eq with hlt | heq
    · exact hlt
    · -- zero form: every ⟨g_c, u⟩ = 0, contradicting Parseval at u ≠ 0
      exfalso
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp heq.symm
      have hdots : ∀ c, D.atom c ⬝ᵥ u = 0 := by
        intro c
        have hc := hall c (Finset.mem_univ c)
        have := (hspos c).ne'
        have hsq : (D.atom c ⬝ᵥ u) ^ 2 = 0 := by
          rcases mul_eq_zero.mp hc with h | h
          · exact absurd h this
          · exact h
        exact pow_eq_zero_iff (n := 2) (by omega) |>.mp hsq
      exact hu (eq_zero_of_forall_atom_dot_eq_zero D hdots)

/-- **Theorem N (weighted Naimark duality).** Every weighted (m,k) design has a
dual (m, m−k) design with the same weights, flipping domination of
complementary subsets. -/
theorem weighted_naimark_duality (hk : 1 ≤ k) (hkm : k + 1 ≤ m)
    (D : WeightedDesign m k) :
    ∃ Ddual : WeightedDesign m (m - k),
      (∀ c, Ddual.weight c = D.weight c) ∧
      ∀ C : Finset (Fin m), C.card = k →
        (Dominates D C ↔ Dominates Ddual Cᶜ) := by
  have hm2 : 2 ≤ m := by omega
  have hspos : ∀ c, 0 < 1 - D.weight c := fun c => by
    linarith [weight_lt_one D hm2 c]
  -- the whitening of the co-Parseval operator
  obtain ⟨R, hRdet, hRWR⟩ := exists_congruence_to_one (coParseval_posDef D hm2)
  -- the co-design matrix A = [√(1−t_c)·(Rᵀg_c)ᵀ]
  set Amat : Matrix (Fin m) (Fin k) ℝ :=
    Matrix.of (fun c j =>
      Real.sqrt (1 - D.weight c) * (Rᵀ *ᵥ D.atom c) j) with hAmat
  have hconj : Rᵀ * (∑ c, (1 - D.weight c) • atomMatrix (D.atom c)) * R
      = ∑ c, (1 - D.weight c) • atomMatrix (Rᵀ *ᵥ D.atom c) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, transpose_mul_atomMatrix_mul]
  have hAA : Amatᵀ * Amat = 1 := by
    rw [← hRWR, hconj]
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hAmat, Matrix.of_apply,
      Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show Real.sqrt (1 - D.weight c) * (Rᵀ *ᵥ D.atom c) i
          * (Real.sqrt (1 - D.weight c) * (Rᵀ *ᵥ D.atom c) j)
        = (Real.sqrt (1 - D.weight c) * Real.sqrt (1 - D.weight c))
          * ((Rᵀ *ᵥ D.atom c) i * (Rᵀ *ᵥ D.atom c) j) from by ring,
      Real.mul_self_sqrt (hspos c).le]
  -- the orthonormal completion and the dual design
  obtain ⟨B, hBB, hAB, hcomplete⟩ := exists_orthonormal_completion Amat hAA
  have htpos : ∀ c, 0 < Real.sqrt (D.weight c) := fun c =>
    Real.sqrt_pos.mpr (D.weight_pos c)
  refine ⟨{ atom := fun c => (Real.sqrt (D.weight c))⁻¹ • (fun j => B c j)
            weight := D.weight
            weight_pos := D.weight_pos
            weight_sum_one := D.weight_sum_one
            isParseval := ?_ }, fun c => rfl, ?_⟩
  · -- dual Parseval: Σ t_c·G_cG_cᵀ = BᵀB = 1
    calc ∑ c, D.weight c
          • atomMatrix ((Real.sqrt (D.weight c))⁻¹ • (fun j => B c j))
        = ∑ c, atomMatrix (fun j => B c j) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [atomMatrix_smul, smul_smul, inv_pow,
            Real.sq_sqrt (D.weight_pos c).le,
            mul_inv_cancel₀ (D.weight_pos c).ne', one_smul]
      _ = 1 := by rw [← transpose_mul_self_eq_sum_rows, hBB]
  · -- the four congruences, subset by subset
    intro C hC
    have hCc : Cᶜ.card = m - k := by
      rw [Finset.card_compl, Fintype.card_fin, hC]
    -- the complement enumeration and the two stacked row matrices
    set embed : Fin (m - k) → Fin m :=
      fun i => ((Cᶜ.orderIsoOfFin hCc) i).val with hembed
    have hembmem : ∀ i, embed i ∈ Cᶜ := fun i => ((Cᶜ.orderIsoOfFin hCc) i).2
    set Y : Matrix (Fin (m - k)) (Fin k) ℝ :=
      Matrix.of (fun i j => (Rᵀ *ᵥ D.atom (embed i)) j) with hY
    set Z : Matrix (Fin (m - k)) (Fin (m - k)) ℝ :=
      Matrix.of (fun i j => (Real.sqrt (D.weight (embed i)))⁻¹ * B (embed i) j)
      with hZ
    -- STEP 0: the complement dictionary S_C − 1 = W − S_{Cᶜ}
    have hL1 : subsetSum D C - 1
        = (∑ c, (1 - D.weight c) • atomMatrix (D.atom c)) - subsetSum D Cᶜ := by
      have hp := D.isParseval
      rw [← Finset.sum_add_sum_compl C
        (fun c => D.weight c • atomMatrix (D.atom c))] at hp
      have hsplitW : ∑ c, (1 - D.weight c) • atomMatrix (D.atom c)
          = (∑ c ∈ C, (1 - D.weight c) • atomMatrix (D.atom c))
            + ∑ c ∈ Cᶜ, (1 - D.weight c) • atomMatrix (D.atom c) :=
        (Finset.sum_add_sum_compl C _).symm
      have hsub : ∀ S : Finset (Fin m),
          ∑ c ∈ S, (1 - D.weight c) • atomMatrix (D.atom c)
          = (∑ c ∈ S, atomMatrix (D.atom c))
            - ∑ c ∈ S, D.weight c • atomMatrix (D.atom c) := by
        intro S
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => by rw [sub_smul, one_smul]
      rw [subsetSum, subsetSum, hsplitW, hsub C, hsub Cᶜ, ← hp]
      abel
    -- STEP 1: congruence by the whitening R
    have hWS_symm : ((∑ c, (1 - D.weight c) • atomMatrix (D.atom c))
        - subsetSum D Cᶜ)ᵀ
        = (∑ c, (1 - D.weight c) • atomMatrix (D.atom c)) - subsetSum D Cᶜ := by
      rw [Matrix.transpose_sub, Matrix.transpose_sum, subsetSum,
        Matrix.transpose_sum]
      congr 1
      · exact Finset.sum_congr rfl fun c _ => by
          rw [Matrix.transpose_smul,
            transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom c)).1]
      · exact Finset.sum_congr rfl fun c _ =>
          transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom c)).1
    have hRconj : Rᵀ * ((∑ c, (1 - D.weight c) • atomMatrix (D.atom c))
          - subsetSum D Cᶜ) * R
        = 1 - Yᵀ * Y := by
      have hYY : Yᵀ * Y = ∑ e ∈ Cᶜ, atomMatrix (Rᵀ *ᵥ D.atom e) := by
        rw [transpose_mul_self_eq_sum_rows,
          ← sum_orderIsoOfFin Cᶜ hCc (fun e => atomMatrix (Rᵀ *ᵥ D.atom e))]
        exact Finset.sum_congr rfl fun i _ =>
          congrArg atomMatrix (funext fun j => by simp [hY, hembed])
      have hRS : Rᵀ * subsetSum D Cᶜ * R
          = ∑ e ∈ Cᶜ, atomMatrix (Rᵀ *ᵥ D.atom e) := by
        rw [subsetSum, Matrix.mul_sum, Matrix.sum_mul]
        exact Finset.sum_congr rfl fun e _ => transpose_mul_atomMatrix_mul R _
      rw [Matrix.mul_sub, Matrix.sub_mul, hRWR, hRS, hYY]
    -- STEP 2 matrices: the A-row and B-row Gram formulas
    have hArow : ∀ c e, (Amat * Amatᵀ) c e
        = Real.sqrt (1 - D.weight c) * Real.sqrt (1 - D.weight e)
          * ((Rᵀ *ᵥ D.atom c) ⬝ᵥ (Rᵀ *ᵥ D.atom e)) := by
      intro c e
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hAmat, Matrix.of_apply,
        dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hYrow : ∀ i i', (Y * Yᵀ) i i'
        = (Rᵀ *ᵥ D.atom (embed i)) ⬝ᵥ (Rᵀ *ᵥ D.atom (embed i')) := by
      intro i i'
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hY, Matrix.of_apply,
        dotProduct]
    have hBrow : ∀ i i', (Z * Zᵀ) i i'
        = (Real.sqrt (D.weight (embed i)))⁻¹
          * (Real.sqrt (D.weight (embed i')))⁻¹
          * ∑ j, B (embed i) j * B (embed i') j := by
      intro i i'
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hZ, Matrix.of_apply,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    -- the embedding is injective, so identity entries restrict cleanly
    have hembinj : Function.Injective embed := fun i i' hii' =>
      (Cᶜ.orderIsoOfFin hCc).toEquiv.injective (Subtype.val_injective hii')
    -- STEP 2: diagonal congruence by √s carries 1 − YYᵀ to D_s − (AAᵀ)|_{Cᶜ}
    have hdiagS : (Matrix.diagonal
          (fun i => Real.sqrt (1 - D.weight (embed i))))ᵀ
          * (1 - Y * Yᵀ)
          * Matrix.diagonal (fun i => Real.sqrt (1 - D.weight (embed i)))
        = Matrix.diagonal (fun i => 1 - D.weight (embed i))
          - Matrix.of (fun i i' => (Amat * Amatᵀ) (embed i) (embed i')) := by
      rw [Matrix.diagonal_transpose]
      ext i i'
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply,
        Matrix.of_apply]
      rw [hYrow i i', hArow (embed i) (embed i')]
      rcases eq_or_ne i i' with rfl | hne
      · rw [if_pos rfl, if_pos rfl]
        have hss := Real.mul_self_sqrt (hspos (embed i)).le
        linear_combination hss
      · rw [if_neg hne, if_neg hne]
        ring
    -- STEP 3: completeness swaps the A-block for the B-block
    have hcompl_entry : ∀ i i',
        (Amat * Amatᵀ) (embed i) (embed i') + (B * Bᵀ) (embed i) (embed i')
          = if i = i' then 1 else 0 := by
      intro i i'
      have hce := congrFun (congrFun hcomplete (embed i)) (embed i')
      rw [Matrix.add_apply, Matrix.one_apply] at hce
      rwa [if_congr ⟨fun h => hembinj h, fun h => h ▸ rfl⟩ rfl rfl] at hce
    have hL6 : Matrix.diagonal (fun i => 1 - D.weight (embed i))
          - Matrix.of (fun i i' => (Amat * Amatᵀ) (embed i) (embed i'))
        = Matrix.of (fun i i' => (B * Bᵀ) (embed i) (embed i'))
          - Matrix.diagonal (fun i => D.weight (embed i)) := by
      ext i i'
      simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply]
      have hce := hcompl_entry i i'
      rcases eq_or_ne i i' with rfl | hne
      · rw [if_pos rfl] at hce
        rw [if_pos rfl, if_pos rfl]
        linarith
      · rw [if_neg hne] at hce
        rw [if_neg hne, if_neg hne]
        linarith
    -- STEP 4: diagonal congruence by 1/√t carries it to ZZᵀ − 1
    have hdiagT : (Matrix.diagonal
          (fun i => (Real.sqrt (D.weight (embed i)))⁻¹))ᵀ
          * (Matrix.of (fun i i' => (B * Bᵀ) (embed i) (embed i'))
              - Matrix.diagonal (fun i => D.weight (embed i)))
          * Matrix.diagonal (fun i => (Real.sqrt (D.weight (embed i)))⁻¹)
        = Z * Zᵀ - 1 := by
      rw [Matrix.diagonal_transpose]
      ext i i'
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply,
        Matrix.of_apply]
      rw [hBrow i i',
        show (B * Bᵀ) (embed i) (embed i')
            = ∑ j, B (embed i) j * B (embed i') j from by
          simp [Matrix.mul_apply, Matrix.transpose_apply]]
      rcases eq_or_ne i i' with rfl | hne
      · rw [if_pos rfl, if_pos rfl]
        have htt := Real.mul_self_sqrt (D.weight_pos (embed i)).le
        have htne := (htpos (embed i)).ne'
        have hinv1 : (Real.sqrt (D.weight (embed i)))⁻¹ * D.weight (embed i)
            * (Real.sqrt (D.weight (embed i)))⁻¹ = 1 := by
          rw [show (Real.sqrt (D.weight (embed i)))⁻¹ * D.weight (embed i)
                * (Real.sqrt (D.weight (embed i)))⁻¹
              = D.weight (embed i) * (Real.sqrt (D.weight (embed i))
                  * Real.sqrt (D.weight (embed i)))⁻¹ from by
            rw [mul_inv]; ring,
            htt, mul_inv_cancel₀ (D.weight_pos (embed i)).ne']
        linear_combination (-1 : ℝ) * hinv1
      · rw [if_neg hne, if_neg hne]
        ring
    -- STEP 5: the dual dictionary ZᵀZ = S′_{Cᶜ}
    have hZZdual : Zᵀ * Z = ∑ e ∈ Cᶜ,
        atomMatrix ((Real.sqrt (D.weight e))⁻¹ • (fun j => B e j)) := by
      rw [transpose_mul_self_eq_sum_rows, ← sum_orderIsoOfFin Cᶜ hCc
        (fun e => atomMatrix ((Real.sqrt (D.weight e))⁻¹ • (fun j => B e j)))]
      refine Finset.sum_congr rfl fun i _ => congrArg atomMatrix (funext fun j => ?_)
      simp [hZ, hembed, Pi.smul_apply, smul_eq_mul]
    -- symmetry and determinant side conditions for the congruences
    have hXsymm1 : (1 - Y * Yᵀ)ᵀ = 1 - Y * Yᵀ := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
        Matrix.transpose_transpose]
    have hBBT : (B * Bᵀ)ᵀ = B * Bᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    have hXsymm2 : (Matrix.of (fun i i' => (B * Bᵀ) (embed i) (embed i'))
          - Matrix.diagonal (fun i => D.weight (embed i)))ᵀ
        = Matrix.of (fun i i' => (B * Bᵀ) (embed i) (embed i'))
          - Matrix.diagonal (fun i => D.weight (embed i)) := by
      rw [Matrix.transpose_sub, Matrix.diagonal_transpose]
      congr 1
      ext i i'
      rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
      have hsym := congrFun (congrFun hBBT (embed i)) (embed i')
      rw [Matrix.transpose_apply] at hsym
      exact hsym
    have hdetS : IsUnit (Matrix.diagonal
        (fun i => Real.sqrt (1 - D.weight (embed i)))).det := by
      rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr fun i _ =>
        (Real.sqrt_pos.mpr (hspos (embed i))).ne'
    have hdetT : IsUnit (Matrix.diagonal
        (fun i => (Real.sqrt (D.weight (embed i)))⁻¹)).det := by
      rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr fun i _ =>
        inv_ne_zero (htpos (embed i)).ne'
    -- the assembled two-sided chain
    constructor
    · intro hdom
      have h1 : ((∑ c, (1 - D.weight c) • atomMatrix (D.atom c))
          - subsetSum D Cᶜ).PosSemidef := by
        have hstart : (subsetSum D C - 1).PosSemidef := hdom
        rwa [hL1] at hstart
      have h2 : (1 - Yᵀ * Y).PosSemidef := by
        rw [← hRconj]
        exact (posSemidef_congr_right hWS_symm hRdet).mp h1
      have h3 : (1 - Y * Yᵀ).PosSemidef :=
        (posSemidef_one_sub_transpose_comm Y).mp h2
      have h4 : (Matrix.of (fun i i' => (B * Bᵀ) (embed i) (embed i'))
          - Matrix.diagonal (fun i => D.weight (embed i))).PosSemidef := by
        have hcongr := (posSemidef_congr_right hXsymm1 hdetS).mp h3
        rwa [hdiagS, hL6] at hcongr
      have h5 : (Z * Zᵀ - 1).PosSemidef := by
        have hcongr := (posSemidef_congr_right hXsymm2 hdetT).mp h4
        rwa [hdiagT] at hcongr
      have h6 : (Zᵀ * Z - 1).PosSemidef :=
        (posSemidef_transpose_mul_sub_one_comm Z).mpr h5
      show ((∑ e ∈ Cᶜ, atomMatrix ((Real.sqrt (D.weight e))⁻¹
          • (fun j => B e j))) - 1).PosSemidef
      rwa [← hZZdual]
    · intro hdom
      have h6 : (Zᵀ * Z - 1).PosSemidef := by
        have hstart : ((∑ e ∈ Cᶜ, atomMatrix ((Real.sqrt (D.weight e))⁻¹
            • (fun j => B e j))) - 1).PosSemidef := hdom
        rwa [← hZZdual] at hstart
      have h5 : (Z * Zᵀ - 1).PosSemidef :=
        (posSemidef_transpose_mul_sub_one_comm Z).mp h6
      have h4 : (Matrix.of (fun i i' => (B * Bᵀ) (embed i) (embed i'))
          - Matrix.diagonal (fun i => D.weight (embed i))).PosSemidef :=
        (posSemidef_congr_right hXsymm2 hdetT).mpr (by rw [hdiagT]; exact h5)
      have h3 : (1 - Y * Yᵀ).PosSemidef :=
        (posSemidef_congr_right hXsymm1 hdetS).mpr
          (by rw [hdiagS, hL6]; exact h4)
      have h2 : (1 - Yᵀ * Y).PosSemidef :=
        (posSemidef_one_sub_transpose_comm Y).mpr h3
      have h1 : ((∑ c, (1 - D.weight c) • atomMatrix (D.atom c))
          - subsetSum D Cᶜ).PosSemidef :=
        (posSemidef_congr_right hWS_symm hRdet).mpr (by rw [hRconj]; exact h2)
      show (subsetSum D C - 1).PosSemidef
      rw [hL1]
      exact h1

end Gtz
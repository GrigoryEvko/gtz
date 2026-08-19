import Gtz.Wave.FourSetCoweightCap
import Gtz.LinAlg.DepthTwoDowndate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The five-set pair floor: a tie read at the ten pairs of one anchor

A five-set of a `(6,3)` design misses one atom, and each of its ten pairs is
one DOUBLE rank-one downdate away from the five-set's gap.  At a tie every
double downdate is a refused triple, so `Gtz.not_posDef_sub_two_vecMulVec_iff`
converts each pair into a reading law of the inverse gap
(`Gtz.tie_fiveSet_pair_reading`): the first reading reaches one, or the
`B⁻¹`-Gram minor of the pair gives way.  Cauchy–Schwarz in the inverse gap
metric collapses the disjunction into one unconditional floor
(`Gtz.tie_fiveSet_pair_floor`):

  **every pair of a strictly dominating five-set of a tie reads the inverse
  gap at least at one in total: `r_a + r_b ≥ 1`.**

This is the first law of the campaign that reads MANY informative refusals
through ONE positive matrix: with the anchor `univ \ {e}` at a corank-two
corner, the ten pairs carry the complement refusal, six one-inside refusals
and three census refusals simultaneously.  Measured on 4000 random corner
configurations, the joint pair system is infeasible at every real corner
sampled while the complex corner-tie witness satisfies it — the pair SYSTEM
(not the floor) is where a real certificate must dig, and the phases of the
`B⁻¹`-Gram are the realness that separates.

## The anchor exists

The anchor's gap must be positive definite, and one hypothesis buys it with
no tie: an atom of leverage at most one leaves a strictly dominating
complement (`Gtz.complement_erase_posDef_of_leverage_le_one`).  Parseval pays
every direction through the coweights of the remaining atoms, and the light
atom cannot absorb more than its own weight.  At a corank-two corner whose
gap axis some inside atom reads at zero — the residual degenerate stratum
`Z1` — that inside atom is unit, so the anchor of the five-set machine is
positive definite outright (`Gtz.corner_oneAxisZero_fiveSet_posDef`).
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. Cauchy–Schwarz for a positive semidefinite form -/

/-- **Cauchy–Schwarz in a positive semidefinite metric.**  The cross reading of
two vectors against a PSD form is dominated by their self readings. -/
theorem psd_form_cross_sq_le {N : Matrix (Fin k) (Fin k) ℝ} (hN : N.PosSemidef)
    (a b : Fin k → ℝ) :
    (a ⬝ᵥ (N *ᵥ b)) ^ 2 ≤ (a ⬝ᵥ (N *ᵥ a)) * (b ⬝ᵥ (N *ᵥ b)) := by
  have hsymm : Nᵀ = N := transpose_eq_of_isHermitian hN.1
  have hcross : b ⬝ᵥ (N *ᵥ a) = a ⬝ᵥ (N *ᵥ b) := by
    rw [dotProduct_mulVec a N b, ← hsymm, Matrix.vecMul_transpose,
      dotProduct_comm, hsymm]
  have hquad : ∀ s : ℝ, 0 ≤ (a ⬝ᵥ (N *ᵥ a)) * (s * s)
      + (2 * (a ⬝ᵥ (N *ᵥ b))) * s + b ⬝ᵥ (N *ᵥ b) := by
    intro s
    have hread := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hN).2 (s • a + b)
    rw [star_trivial] at hread
    have hexp : (s • a + b) ⬝ᵥ (N *ᵥ (s • a + b))
        = (a ⬝ᵥ (N *ᵥ a)) * (s * s) + (2 * (a ⬝ᵥ (N *ᵥ b))) * s + b ⬝ᵥ (N *ᵥ b) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
        add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      linear_combination s * hcross
    rwa [hexp] at hread
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-! ## 2. The double downdate of a five-set is a refused triple -/

/-- Erasing two atoms from a five-set leaves a triple whose gap is the double
rank-one downdate of the five-set gap. -/
theorem subsetSum_erase_erase_sub_one (D : WeightedDesign m 3)
    (F : Finset (Fin m)) {a b : Fin m} (ha : a ∈ F) (hb : b ∈ F) (hab : a ≠ b) :
    subsetSum D ((F.erase a).erase b) - 1
      = ((subsetSum D F - 1) - Matrix.vecMulVec (D.atom a) (D.atom a))
        - Matrix.vecMulVec (D.atom b) (D.atom b) := by
  rw [subsetSum_erase_sub_one_rankOne D (F.erase a)
      (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩),
    subsetSum_erase_sub_one_rankOne D F ha]

/-- **THE FIVE-SET PAIR READING.**  At a tie, every pair of a strictly
dominating five-set obeys the depth-two refusal disjunction: the first
reading reaches one, or the inverse-gap Gram minor of the pair gives way. -/
theorem tie_fiveSet_pair_reading (D : WeightedDesign m 3) (htie : IsTie D)
    (F : Finset (Fin m)) (hF : F.card = 5)
    (hPD : (subsetSum D F - 1).PosDef)
    {a b : Fin m} (ha : a ∈ F) (hb : b ∈ F) (hab : a ≠ b) :
    1 ≤ D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a)
      ∨ (1 - D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a))
          * (1 - D.atom b ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom b))
        ≤ (D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom b)) ^ 2 := by
  classical
  have hcard : ((F.erase a).erase b).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩),
      Finset.card_erase_of_mem ha, hF]
  have hrefuse := htie.2 ((F.erase a).erase b) hcard
  rw [subsetSum_erase_erase_sub_one D F ha hb hab] at hrefuse
  exact (not_posDef_sub_two_vecMulVec_iff (subsetSum D F - 1) hPD
    (D.atom a) (D.atom b)).mp hrefuse

/-- **THE FIVE-SET PAIR FLOOR.**  At a tie, every pair of a strictly
dominating five-set reads the inverse gap at least at one in total.  The
heavy branch of the pair reading is one reading alone; the minor branch
collapses through Cauchy–Schwarz in the inverse metric. -/
theorem tie_fiveSet_pair_floor (D : WeightedDesign m 3) (htie : IsTie D)
    (F : Finset (Fin m)) (hF : F.card = 5)
    (hPD : (subsetSum D F - 1).PosDef)
    {a b : Fin m} (ha : a ∈ F) (hb : b ∈ F) (hab : a ≠ b) :
    1 ≤ D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a)
      + D.atom b ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom b) := by
  have hInv : ((subsetSum D F - 1)⁻¹).PosSemidef := hPD.inv.posSemidef
  have hra : 0 ≤ D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a) := by
    have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hInv).2 (D.atom a)
    rwa [star_trivial] at this
  have hrb : 0 ≤ D.atom b ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom b) := by
    have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hInv).2 (D.atom b)
    rwa [star_trivial] at this
  rcases tie_fiveSet_pair_reading D htie F hF hPD ha hb hab with hheavy | hminor
  · linarith
  · have hcs := psd_form_cross_sq_le hInv (D.atom a) (D.atom b)
    nlinarith [hminor, hcs, hra, hrb]

/-! ## 3. A light-leverage atom leaves a strictly dominating complement -/

/-- **An atom of leverage at most one leaves a strictly dominating
complement**, with no tie hypothesis: Parseval pays every direction through
the coweights of the remaining atoms, and the light atom cannot absorb more
than its own weight along any direction. -/
theorem complement_erase_posDef_of_leverage_le_one (D : WeightedDesign m 3)
    (hm : 3 ≤ m) {x : Fin m} (hlev : D.atom x ⬝ᵥ D.atom x ≤ 1) :
    (subsetSum D ((univ : Finset (Fin m)).erase x) - 1).PosDef := by
  classical
  set E : Finset (Fin m) := (univ : Finset (Fin m)).erase x with hE
  have hEne : E.Nonempty := by
    rw [hE, ← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, Fintype.card_fin]
    omega
  -- the coweight ratio floor over the complement
  set ratios : Finset ℝ := E.image (fun a => (1 - D.weight a) / D.weight a)
    with hratios
  have hratne : ratios.Nonempty := hEne.image _
  set rho : ℝ := ratios.min' hratne with hrho
  obtain ⟨astar, hastar, hastarval⟩ := Finset.mem_image.mp (ratios.min'_mem hratne)
  have hpairs : ∀ a ∈ E, D.weight a + D.weight x < 1 := by
    intro a haE
    have hax : a ≠ x := Finset.ne_of_mem_erase haE
    -- a third atom exists because 3 ≤ m
    have hthird : ∃ c : Fin m, c ≠ a ∧ c ≠ x := by
      by_contra hcon
      push Not at hcon
      have hsub : (univ : Finset (Fin m)) ⊆ {a, x} := by
        intro c _
        by_cases hca : c = a
        · simp [hca]
        · simp [hcon c hca]
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      have hcard2 : ({a, x} : Finset (Fin m)).card ≤ 2 :=
        Finset.card_insert_le _ _ |>.trans (by simp)
      omega
    obtain ⟨c, hca, hcx⟩ := hthird
    have hsplit : D.weight a + D.weight x + D.weight c ≤ ∑ e, D.weight e := by
      have hsubset : ({a, x, c} : Finset (Fin m)) ⊆ univ := Finset.subset_univ _
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun e _ _ => (D.weight_pos e).le)
      rw [sum_triple_eq hax (Ne.symm hca) (Ne.symm hcx)] at hsum
      linarith [hsum]
    have := D.weight_sum_one
    linarith [D.weight_pos c]
  have hrho_gt : D.weight x < rho * (1 - D.weight x) := by
    have hxc : (0 : ℝ) < 1 - D.weight x := by
      have := hpairs astar hastar
      linarith [D.weight_pos astar]
    have hstar : D.weight x / (1 - D.weight x)
        < (1 - D.weight astar) / D.weight astar := by
      rw [div_lt_div_iff₀ hxc (D.weight_pos astar)]
      have := hpairs astar hastar
      nlinarith [D.weight_pos astar, D.weight_pos x]
    have : D.weight x / (1 - D.weight x) < rho := by
      rw [hrho, ← hastarval]
      exact hstar
    calc D.weight x = (D.weight x / (1 - D.weight x)) * (1 - D.weight x) :=
          (div_mul_cancel₀ _ (ne_of_gt hxc)).symm
      _ < rho * (1 - D.weight x) := mul_lt_mul_of_pos_right this hxc
  have hrhod : ∀ a ∈ E, rho * D.weight a ≤ 1 - D.weight a := by
    intro a haE
    have hle : rho ≤ (1 - D.weight a) / D.weight a :=
      ratios.min'_le _ (Finset.mem_image_of_mem _ haE)
    calc rho * D.weight a ≤ ((1 - D.weight a) / D.weight a) * D.weight a :=
          mul_le_mul_of_nonneg_right hle (D.weight_pos a).le
      _ = 1 - D.weight a := div_mul_cancel₀ _ (ne_of_gt (D.weight_pos a))
  have hrhopos : 0 < rho := by
    rw [hrho, ← hastarval]
    have := hpairs astar hastar
    exact div_pos (by linarith [D.weight_pos x]) (D.weight_pos astar)
  -- assemble positive definiteness
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D _), fun zv hzv => ?_⟩
  rw [star_trivial, quadForm_subsetSum_sub_one]
  have hZpos : 0 < zv ⬝ᵥ zv := dotProduct_self_pos hzv
  have hxread : (D.atom x ⬝ᵥ zv) ^ 2 ≤ zv ⬝ᵥ zv := by
    have hcs := dotProduct_sq_le_mul (D.atom x) zv
    nlinarith [hcs, hZpos, hlev]
  have hpar : D.weight x * (D.atom x ⬝ᵥ zv) ^ 2
      + ∑ a ∈ E, D.weight a * (D.atom a ⬝ᵥ zv) ^ 2 = zv ⬝ᵥ zv := by
    have htotal := sum_weight_read_sq D zv
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)] at htotal
    exact htotal
  have hlow : ∀ a ∈ E, rho * (D.weight a * (D.atom a ⬝ᵥ zv) ^ 2)
      ≤ (1 - D.weight a) * (D.atom a ⬝ᵥ zv) ^ 2 := by
    intro a haE
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hrhod a haE) (sq_nonneg _)
  have hsumlow : rho * ∑ a ∈ E, D.weight a * (D.atom a ⬝ᵥ zv) ^ 2
      ≤ ∑ a ∈ E, (1 - D.weight a) * (D.atom a ⬝ᵥ zv) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hlow
  have hexpand : ∑ a ∈ E, (D.atom a ⬝ᵥ zv) ^ 2 - zv ⬝ᵥ zv
      = ∑ a ∈ E, (1 - D.weight a) * (D.atom a ⬝ᵥ zv) ^ 2
        - D.weight x * (D.atom x ⬝ᵥ zv) ^ 2 := by
    have hsplit : ∑ a ∈ E, (D.atom a ⬝ᵥ zv) ^ 2
        = ∑ a ∈ E, (1 - D.weight a) * (D.atom a ⬝ᵥ zv) ^ 2
          + ∑ a ∈ E, D.weight a * (D.atom a ⬝ᵥ zv) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [hsplit]
    linarith [hpar]
  rw [hexpand]
  have hchain : rho * (zv ⬝ᵥ zv) - (1 + rho) * (D.weight x * (D.atom x ⬝ᵥ zv) ^ 2)
      ≤ ∑ a ∈ E, (1 - D.weight a) * (D.atom a ⬝ᵥ zv) ^ 2
        - D.weight x * (D.atom x ⬝ᵥ zv) ^ 2 := by
    have := hsumlow
    nlinarith [hpar]
  have hfinal : 0 < rho * (zv ⬝ᵥ zv)
      - (1 + rho) * (D.weight x * (D.atom x ⬝ᵥ zv) ^ 2) := by
    have hb : (1 + rho) * (D.weight x * (D.atom x ⬝ᵥ zv) ^ 2)
        ≤ (1 + rho) * D.weight x * (zv ⬝ᵥ zv) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      exact mul_le_mul_of_nonneg_left hxread (D.weight_pos x).le
    have hcoeff : 0 < rho - (1 + rho) * D.weight x := by nlinarith [hrho_gt]
    nlinarith [hb, hZpos, hcoeff]
  linarith [hchain, hfinal]

/-! ## 4. The anchor of the residual degenerate stratum -/

/-- **The five-set anchor of the `Z1` stratum is positive definite, with no
tie.**  At a corank-two corner whose gap axis one inside atom reads at zero,
that atom is unit, so its erased complement dominates strictly and the
five-set pair machine applies to the remaining five atoms. -/
theorem corner_oneAxisZero_fiveSet_posDef (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    (subsetSum D ((univ : Finset (Fin 6)).erase x) - 1).PosDef := by
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hcard : ({x, y, z} : Finset (Fin 6)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin 6)) := by simp
  have hexX := corner_heavyExcess_axis D _ hcard hlam hunit hgap hx
  simp only [heavyExcess] at hexX
  rw [hax, show leverageOf (D.atom x) = D.atom x ⬝ᵥ D.atom x from
    (dotProduct_self_eq_sum_sq (D.atom x)).symm] at hexX
  have hlev : D.atom x ⬝ᵥ D.atom x = 1 := by
    have hcancel := mul_left_cancel₀ (ne_of_gt hone)
      (show (1 + lam) * (D.atom x ⬝ᵥ D.atom x - 1) = (1 + lam) * 0 by
        rw [mul_zero]
        nlinarith [hexX])
    linarith
  exact complement_erase_posDef_of_leverage_le_one D (by norm_num) hlev.le

end Gtz

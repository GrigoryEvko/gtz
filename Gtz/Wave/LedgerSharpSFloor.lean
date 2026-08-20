import Gtz.Wave.MomentProbeRelations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The exact coweight ledger of the heavy-inside cell and the sharpened
# S-floor

The excluded-pair excess `S = t_x(r_x − 1) + t_z(r_z − 1)` of the surviving
four-set is not merely nonnegative at a tie: it EQUALS the coweighted total
of the member excesses (`Gtz.corner_oneAxisZero_heavyInside_ledger_identity`):

  `S = (1 − t_y)(r_y − 1) + Σ_{d ∈ Cᶜ} (1 − t_d)(r_d − 1)` .

This is the landed reading ledger of the four-set, written at the corner with
its complement `{x, z}` evaluated.  It is an identity — no tie, no cell.

## The sharpened S-floor

At a tie the three outside excesses are nonnegative, so the identity floors
`S` by the inside term alone, and the cell's own self-read
(`Gtz.corner_oneAxisZero_heavyInside_selfRead`) turns that into the cross
reading (`Gtz.corner_oneAxisZero_heavyInside_sFloor_sharp`):

  `(1 − t_y) · ρ² ≤ S · (1 + r_z)` ,  `ρ = g_yᵀA_y⁻¹g_z` .

This is strictly sharper than the landed odds-level S-floor
(`Gtz.corner_oneAxisZero_heavyInside_sFloor`), whose coefficient is
`1 − t*` with `t*` the LARGEST member weight: since `t_y ≤ t*`, the
coefficient here is the larger one, and the two agree exactly when the
surviving inside atom is the heaviest member.  The gain is the whole
difference between charging the excess to the worst member and charging it
to the atom that actually carries it.

## The measured shape

Over a near-roof sample of the region `{cell H, S ≥ 0}` the deficit
`1 − min_d r_d` tracks the EXCLUDED weight total `t_x + t_z` more tightly
than any other candidate factor (ratio spread `1.8·10²` against `2·10⁵` for
the axis-share factors), with measured infimum `0.045`.  The ledger identity
is the exact reason: `S` is built from exactly the excluded pair, and the
member excesses that pay for it are coweighted.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The exact coweight ledger at the corner -/

/-- **THE HEAVY-INSIDE LEDGER IDENTITY.**  The excluded-pair excess of the
surviving four-set equals the coweighted total of the member excesses:

  `t_x(r_x − 1) + t_z(r_z − 1)
     = (1 − t_y)(r_y − 1) + Σ_{d ∈ Cᶜ} (1 − t_d)(r_d − 1)` .

An identity: the landed reading ledger with the complement evaluated at the
corner.  No tie and no cell hypothesis. -/
theorem corner_oneAxisZero_heavyInside_ledger_identity (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    D.weight x
        * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom x) - 1)
      + D.weight z
        * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z) - 1)
      = (1 - D.weight y)
          * (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom y) - 1)
        + ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
            (1 - D.weight d)
              * (D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                  - 1)⁻¹ *ᵥ D.atom d) - 1) := by
  classical
  set K : Finset (Fin 6) := (({x, y, z} : Finset (Fin 6))ᶜ) with hK
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D (insert y K) - 1 with hA
  have hyK : y ∉ K := by rw [hK]; simp
  have hKcard : K.card = 3 := by
    rw [hK]; exact card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)
  -- the landed ledger of the four-set
  have hledger := subset_reading_ledger D (insert y K) hAy
  -- the complement of the four-set is the excluded pair {x, z}
  have hcompl : ((insert y K)ᶜ : Finset (Fin 6)) = {x, z} := by
    rw [hK, Finset.compl_insert, compl_compl]
    ext a
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hay, rfl | h⟩
      · exact Or.inl rfl
      · rcases h with rfl | rfl
        · exact absurd rfl hay
        · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hxy, Or.inl rfl⟩
      · exact ⟨Ne.symm hyz, Or.inr (Or.inr rfl)⟩
  have hxz' : x ∉ ({z} : Finset (Fin 6)) := by simp [hxz]
  rw [hcompl, Finset.sum_insert hxz', Finset.sum_singleton] at hledger
  -- split the member side at y
  have hmem : ∑ a ∈ insert y K, (1 - D.weight a) * (D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a))
      = (1 - D.weight y) * (D.atom y ⬝ᵥ (A⁻¹ *ᵥ D.atom y))
        + ∑ d ∈ K, (1 - D.weight d) * (D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d)) := by
    rw [Finset.sum_insert hyK]
  rw [← hA, hmem] at hledger
  have hones : ∑ _d ∈ K, (1 : ℝ) = 3 := by
    rw [Finset.sum_const, hKcard]; norm_num
  have hweights : ∑ d ∈ K, D.weight d
      = 1 - D.weight x - D.weight y - D.weight z := by
    have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6)) D.weight
    rw [D.weight_sum_one, sum_triple_eq hxy hxz hyz] at hsplit
    rw [hK]; linarith
  -- expand the excess sums into the raw sums
  have hexp : ∑ d ∈ K, (1 - D.weight d) * (D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d) - 1)
      = (∑ d ∈ K, (1 - D.weight d) * (D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d)))
        - (∑ _d ∈ K, (1 : ℝ)) + ∑ d ∈ K, D.weight d := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hexp, hones, hweights]
  linarith [hledger]

/-! ## 2. The sharpened S-floor -/

/-- **THE SHARPENED S-FLOOR.**  At a heavy-inside tie the excluded-pair
excess is floored by the squared cross reading with the coweight of the
SURVIVING INSIDE ATOM:

  `(1 − t_y) · ρ² ≤ S · (1 + r_z)` .

Route: the ledger identity turns the outside floors into `S ≥ (1−t_y)(r_y−1)`
and the cell's self-read turns `r_y − 1` into `ρ²/(1+r_z)`.  Strictly sharper
than the landed odds-level S-floor, whose coefficient `1 − t*` uses the
largest member weight instead of `t_y`. -/
theorem corner_oneAxisZero_heavyInside_sFloor_sharp (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    (1 - D.weight y)
        * (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z)) ^ 2
      ≤ (D.weight x
            * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom x) - 1)
          + D.weight z
            * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z) - 1))
        * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z)) := by
  classical
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hident := corner_oneAxisZero_heavyInside_ledger_identity D hxy hxz hyz hAy
  -- the outside floors of the tie
  have hfloors := (corner_oneAxisZero_heavyInside_isTie_iff D hxy hxz hyz hlam
    hunit hgap hax haz hnotz).mp htie
  have hm : 2 ≤ (6 : ℕ) := by norm_num
  have houts : (0 : ℝ)
      ≤ ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          (1 - D.weight d)
            * (D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom d) - 1) := by
    refine Finset.sum_nonneg fun d hd => ?_
    have hco : (0 : ℝ) ≤ 1 - D.weight d := by
      linarith [weight_lt_one D hm d]
    have hfl := hfloors d hd
    exact mul_nonneg hco (by linarith)
  -- the self-read of the cell
  have hself := corner_oneAxisZero_heavyInside_selfRead D hxy hxz hyz hlam
    hunit hgap hax haz hnotz
  have hrz0 : 0 ≤ D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hAy.inv.posSemidef).2
      (D.atom z)
    rwa [star_trivial] at h
  have hco : (0 : ℝ) ≤ 1 - D.weight y := by
    linarith [weight_lt_one D hm y]
  have hmul := mul_le_mul_of_nonneg_left hself hco
  nlinarith [hident, houts, hmul, hrz0]

end Gtz

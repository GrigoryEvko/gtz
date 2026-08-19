import Gtz.Wave.GhostBlockCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The row law of the six-set pivots, and the ghost pivot bound

The pivot matrix of the six-set gap is a co-weighted projection
(`Gtz.pivot_coweight_projection`), so each of its rows carries the identity
`P_ff = Σ_c (1−t_c) P_fc²`.  At the corank-two corner the outside part of
that row is priced exactly by `Gtz.outside_row_mass`, and the two readings
combine into the ROW LAW (`Gtz.inside_row_law`):

  `Σ_{e ∈ C} (1 − t_e)·P_fe²  =  lam·η_f²  +  Σ_{d ∉ C} t_d·P_fd²` ,

with `η_f := uᵀ W⁻¹ g_f` the atom's cross reading against the gap
direction.  The law says the co-weighted INSIDE row mass of any atom is the
spike it carries on the gap direction plus its weighted outside row mass —
an exact accounting with no inequality spent.

Dropping the other inside terms on the left and pricing the right by the
largest outside weight turns the law into a quadratic inequality for the
diagonal pivot (`Gtz.ghost_pivot_quadratic`):

  `(1 − t_f)·P_ff²  ≤  (1 − ω)·lam·η_f²  +  ω·P_ff` ,  `ω := max_{d ∉ C} t_d` .

Both roots of that quadratic sit below one half as soon as the spike is
small against the outside weight budget, which gives the ghost pivot bound
`2·P_ff < 1` (`Gtz.ghost_pivot_lt_half`) — the first of the four conditions
of `Gtz.GhostBlockShort`, hence a step of the non-planar closure through
`Gtz.corankTwoNonplanar_absurd_of_ghostBlock`.

Everything quantifies over the complement triple, so nothing here can be
stated at `(5,3)`.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-- **The row law.**  The co-weighted inside row mass of an atom is its
spike on the gap direction plus its weighted outside row mass. -/
theorem inside_row_law (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (f : Fin m) :
    ∑ e ∈ C, (1 - D.weight e) * sixSetPivot D f e ^ 2
      = lam * (u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f)) ^ 2
        + ∑ d ∈ Cᶜ, D.weight d * sixSetPivot D f d ^ 2 := by
  classical
  have hsymm : ∀ c : Fin m, D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f)
      = sixSetPivot D f c := fun c => (sixSetPivot_comm D f c) ▸ rfl
  have hproj := pivot_coweight_projection D hPD f f
  have hsq : ∀ c : Fin m,
      (1 - D.weight c)
          * ((D.atom f ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c))
            * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f)))
        = (1 - D.weight c) * sixSetPivot D f c ^ 2 := by
    intro c
    rw [hsymm c, show D.atom f ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c)
      = sixSetPivot D f c from rfl]
    ring
  simp only [hsq] at hproj
  rw [← Finset.sum_add_sum_compl C] at hproj
  have hmass := outside_row_mass D C hgap hPD (D.atom f)
  simp only [hsymm] at hmass
  have hsplit : ∑ d ∈ Cᶜ, (1 - D.weight d) * sixSetPivot D f d ^ 2
      = ∑ d ∈ Cᶜ, sixSetPivot D f d ^ 2
        - ∑ d ∈ Cᶜ, D.weight d * sixSetPivot D f d ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hsplit, hmass] at hproj
  have hff : D.atom f ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f)
      = sixSetPivot D f f := rfl
  rw [hff] at hproj
  linarith [hproj]

/-- **The ghost pivot quadratic.**  Dropping the other inside terms and
pricing the outside row by the largest outside weight. -/
theorem ghost_pivot_quadratic (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (hm : 2 ≤ m)
    {f : Fin m} (hf : f ∈ C) {ω : ℝ} (hω : ∀ d ∈ Cᶜ, D.weight d ≤ ω)
    (hω1 : ω ≤ 1) :
    (1 - D.weight f) * sixSetPivot D f f ^ 2
      ≤ (1 - ω) * (lam * (u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f)) ^ 2)
        + ω * sixSetPivot D f f := by
  classical
  have hrow := inside_row_law D C hgap hPD f
  have hmass := outside_row_mass D C hgap hPD (D.atom f)
  have hsymm : ∀ c : Fin m, D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f)
      = sixSetPivot D f c := fun c => (sixSetPivot_comm D f c) ▸ rfl
  simp only [hsymm] at hmass
  -- the inside sum dominates its diagonal term
  have hleft : (1 - D.weight f) * sixSetPivot D f f ^ 2
      ≤ ∑ e ∈ C, (1 - D.weight e) * sixSetPivot D f e ^ 2 := by
    refine Finset.single_le_sum
      (f := fun e => (1 - D.weight e) * sixSetPivot D f e ^ 2)
      (fun e _ => mul_nonneg ?_ (sq_nonneg _)) hf
    linarith [design_weight_lt_one D hm e]
  -- the outside sum is priced by the largest outside weight
  have hright : ∑ d ∈ Cᶜ, D.weight d * sixSetPivot D f d ^ 2
      ≤ ω * ∑ d ∈ Cᶜ, sixSetPivot D f d ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun d hd =>
      mul_le_mul_of_nonneg_right (hω d hd) (sq_nonneg _)
  rw [hmass] at hright
  linarith [hrow, hleft, hright]

/-- **The ghost pivot bound.**  When the spike is small against the outside
weight budget, both roots of the quadratic sit below one half, so the
diagonal pivot does. -/
theorem ghost_pivot_lt_half (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (hm : 2 ≤ m) (hlam : 0 ≤ lam)
    {f : Fin m} (hf : f ∈ C) {ω : ℝ} (hω0 : 0 ≤ ω)
    (hω : ∀ d ∈ Cᶜ, D.weight d ≤ ω) (hω1 : ω ≤ 1)
    (hspike : 4 * ((1 - ω)
          * (lam * (u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f)) ^ 2))
        < 1 - D.weight f - 2 * ω) :
    2 * sixSetPivot D f f < 1 := by
  have hquad := ghost_pivot_quadratic D C hgap hPD hm hf hω hω1
  set a : ℝ := sixSetPivot D f f with ha
  set μ : ℝ := (1 - ω)
    * (lam * (u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f)) ^ 2) with hμ
  by_contra hcon
  push_neg at hcon
  have hhalf : (1 : ℝ) / 2 ≤ a := by linarith
  have hμ0 : 0 ≤ μ := by
    rw [hμ]
    exact mul_nonneg (by linarith) (mul_nonneg hlam (sq_nonneg _))
  have hgapω : ω < 1 - D.weight f := by linarith
  have hprod : 0 ≤ (a - 1 / 2) * ((1 - D.weight f) * (a + 1 / 2) - ω) := by
    refine mul_nonneg (by linarith) ?_
    nlinarith [hhalf, hgapω, hω0,
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - D.weight f)
        (by linarith : (0:ℝ) ≤ a - 1 / 2)]
  have hkey : 0 ≤ 4 * (1 - D.weight f) * a ^ 2 - 4 * ω * a + 2 * ω
      - (1 - D.weight f) := by nlinarith [hprod]
  linarith [hquad, hspike, hkey]

end Gtz

import Gtz.Wave.OppositeHornWedgeCap
import Gtz.Wave.CornerGapWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The scalar system of a corank-two corner

The two-inside cap `Gtz.corner_twoInside_bracket_cap_sum` is a genuine
inequality, but its right-hand side is a sum over the complement and therefore
not yet comparable with the corner scalars.  This module closes every one of
those sums, so the cap becomes a polynomial inequality in the SEVEN scalars

  `e_x, e_y, e_z` (heavy excesses),  `t_x, t_y, t_z` (inside weights),  `λ` .

Four exact closures, each from Parseval read at one probe.

* **The outside leverage total** (`corner_outside_leverage_total`).  Parseval's
  trace gives `Σ_a t_aℓ_a = 3`, so the complement carries
  `Σ_{d∈Cᶜ} t_dℓ_d = 3 − t_xℓ_x − t_yℓ_y − t_zℓ_z`.

* **The outside pairing mass** (`corner_outside_pairing_sq_total`).  Parseval
  read at the atom `g_x` gives `Σ_a t_a P_{xa}² = ℓ_x`, and the rank-one gap
  turns the two inside pair minors into excess products:

    `Σ_{d∈Cᶜ} t_d P_{xd}² = ℓ_x − t_xℓ_x² − t_y e_xe_y − t_z e_xe_z` .

* **The outside wedge total** (`corner_outside_wedge_total`), the previous two
  combined:

    `Σ_{d∈Cᶜ} t_d·w_{xd} = ℓ_x·(3 − t_xℓ_x − t_yℓ_y − t_zℓ_z)
        − (ℓ_x − t_xℓ_x² − t_y e_xe_y − t_z e_xe_z)` .

* **The axis weight cap** (`corner_axis_weight_cap`).  Parseval read at the gap
  axis `u` gives `Σ_a t_a(g_a·u)² = 1`, and the landed
  `Gtz.corner_heavyExcess_axis` converts the inside part, so the inside weights
  cannot carry too much excess:

    `(1+λ)·(t_xe_x + t_ye_y + t_ze_z) ≤ λ` ,

  with the exact remainder `corner_outside_axis_mass` naming what the outside
  carries.  Measured minimum of the slack over 10560 corners: `7.3e-4`.

The headline is `corner_twoInside_cap_closed`: the two-inside cap in the seven
scalars, with no sums left.  Measured worst violation `−1.7e-6` over 10560
generic corners, so it is a sharp constraint on the corner's scalar data alone,
tie-free, and independent of the informative-triple budget which is an identity.
That makes it the first inequality this arm owns that constrains the corner
without passing through the refusals.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The outside leverage total -/

/-- **THE OUTSIDE LEVERAGE TOTAL.**  Parseval's trace splits at the corner. -/
theorem corner_outside_leverage_total (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d * leverageOf (D.atom d)
      = 3 - (D.weight x * leverageOf (D.atom x)
        + D.weight y * leverageOf (D.atom y)
        + D.weight z * leverageOf (D.atom z)) := by
  classical
  have htot := sum_weighted_leverage D
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun c => D.weight c * leverageOf (D.atom c))
  rw [sum_triple_eq hxy hxz hyz] at hsplit
  norm_num at htot
  linarith [hsplit, htot]

/-! ## 2. The outside pairing mass -/

/-- **THE OUTSIDE PAIRING MASS.**  Parseval read at one inside atom, with the
two inside pair minors replaced by excess products through the rank-one gap. -/
theorem corner_outside_pairing_sq_total (D : WeightedDesign m 3)
    {x y z : Fin m} {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d * atomPairing D x d ^ 2
      = leverageOf (D.atom x)
        - D.weight x * leverageOf (D.atom x) ^ 2
        - D.weight y * (heavyExcess D x * heavyExcess D y)
        - D.weight z * (heavyExcess D x * heavyExcess D z) := by
  classical
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hz : z ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hread := sum_weight_read_sq D (D.atom x)
  have hconv : ∀ a : Fin m,
      D.weight a * (D.atom a ⬝ᵥ D.atom x) ^ 2
        = D.weight a * atomPairing D x a ^ 2 := by
    intro a
    rw [atomPairing, dotProduct_comm]
  rw [Finset.sum_congr rfl (fun a _ => hconv a)] at hread
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun a => D.weight a * atomPairing D x a ^ 2)
  rw [sum_triple_eq hxy hxz hyz, hread] at hsplit
  have hxx : atomPairing D x x = leverageOf (D.atom x) := by
    rw [atomPairing, leverageOf_eq_dotProduct]
  have hmxy := corner_inside_pairMinor_eq_zero D ({x, y, z} : Finset (Fin m))
    hcard hlam hunit hgap hx hy hxy
  have hmxz := corner_inside_pairMinor_eq_zero D ({x, y, z} : Finset (Fin m))
    hcard hlam hunit hgap hx hz hxz
  have hlev : D.atom x ⬝ᵥ D.atom x = leverageOf (D.atom x) :=
    (leverageOf_eq_dotProduct _).symm
  rw [hxx, hlev] at hsplit
  linear_combination hsplit + D.weight y * hmxy + D.weight z * hmxz

/-- **THE OUTSIDE WEDGE TOTAL.**  The weighted wedge of one inside atom against
the complement, in corner scalars. -/
theorem corner_outside_wedge_total (D : WeightedDesign m 3)
    {x y z : Fin m} {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * pairBracketSq (D.atom x) (D.atom d)
      = leverageOf (D.atom x)
          * (3 - (D.weight x * leverageOf (D.atom x)
            + D.weight y * leverageOf (D.atom y)
            + D.weight z * leverageOf (D.atom z)))
        - (leverageOf (D.atom x)
          - D.weight x * leverageOf (D.atom x) ^ 2
          - D.weight y * (heavyExcess D x * heavyExcess D y)
          - D.weight z * (heavyExcess D x * heavyExcess D z)) := by
  classical
  have hlevtot := corner_outside_leverage_total D hxy hxz hyz
  have hpair := corner_outside_pairing_sq_total D hlam hunit hgap hxy hxz hyz
  have hexp : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d * pairBracketSq (D.atom x) (D.atom d)
      = leverageOf (D.atom x)
          * (∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
            D.weight d * leverageOf (D.atom d))
        - ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.weight d * atomPairing D x d ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by
      simp only [pairBracketSq, atomPairing]; ring
  rw [hexp, hlevtot, hpair]

/-! ## 3. The axis weight cap -/

/-- **THE OUTSIDE AXIS MASS.**  Parseval at the gap axis, with the inside part
converted by the landed excess–axis law. -/
theorem corner_outside_axis_mass (D : WeightedDesign m 3) {x y z : Fin m}
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    lam * ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (D.atom d ⬝ᵥ u) ^ 2
      = lam - (1 + lam) * (D.weight x * heavyExcess D x
        + D.weight y * heavyExcess D y + D.weight z * heavyExcess D z) := by
  classical
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := card_triple_eq hxy hxz hyz
  have hread := sum_weight_read_sq D u
  rw [hunit] at hread
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun a => D.weight a * (D.atom a ⬝ᵥ u) ^ 2)
  rw [sum_triple_eq hxy hxz hyz, hread] at hsplit
  have hax := corner_heavyExcess_axis D ({x, y, z} : Finset (Fin m)) hcard hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m)))
  have hay := corner_heavyExcess_axis D ({x, y, z} : Finset (Fin m)) hcard hlam
    hunit hgap (by simp : y ∈ ({x, y, z} : Finset (Fin m)))
  have haz := corner_heavyExcess_axis D ({x, y, z} : Finset (Fin m)) hcard hlam
    hunit hgap (by simp : z ∈ ({x, y, z} : Finset (Fin m)))
  linear_combination lam * hsplit + D.weight x * hax + D.weight y * hay
    + D.weight z * haz

/-- **THE AXIS WEIGHT CAP.**  The inside weights of a corank-two corner cannot
carry more than `λ/(1+λ)` of excess:

  `(1+λ)·(t_xe_x + t_ye_y + t_ze_z) ≤ λ` .

The complement's axis mass is nonnegative, and Parseval at the axis totals one.
Measured slack minimum `7.3e-4` over 10560 corners — a tight constraint. -/
theorem corner_axis_weight_cap (D : WeightedDesign m 3) {x y z : Fin m}
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (1 + lam) * (D.weight x * heavyExcess D x
        + D.weight y * heavyExcess D y
        + D.weight z * heavyExcess D z) ≤ lam := by
  classical
  have hmass := corner_outside_axis_mass D hlam hunit hgap hxy hxz hyz
  have hnn : 0 ≤ ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d * (D.atom d ⬝ᵥ u) ^ 2 :=
    Finset.sum_nonneg fun d _ => mul_nonneg (D.weight_pos d).le (sq_nonneg _)
  nlinarith [hmass, hnn, hlam]

/-! ## 4. The two-inside cap, closed -/

/-- **THE TWO-INSIDE CAP IN CORNER SCALARS.**  Every sum is closed, so the cap
of `Gtz.corner_twoInside_bracket_cap_sum` becomes a polynomial inequality in the
heavy excesses, the inside weights and the scale.  Tie-free, and measured with
worst violation `−1.7e-6` over 10560 generic corners. -/
theorem corner_twoInside_cap_closed (D : WeightedDesign m 3) {x y z : Fin m}
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam)
      ≤ (leverageOf (D.atom x) + leverageOf (D.atom y) - 1)
          * (3 - (D.weight x * leverageOf (D.atom x)
            + D.weight y * leverageOf (D.atom y)
            + D.weight z * leverageOf (D.atom z)))
        - (leverageOf (D.atom x) - D.weight x * leverageOf (D.atom x) ^ 2
          - D.weight y * (heavyExcess D x * heavyExcess D y)
          - D.weight z * (heavyExcess D x * heavyExcess D z))
        - (leverageOf (D.atom y) - D.weight y * leverageOf (D.atom y) ^ 2
          - D.weight x * (heavyExcess D x * heavyExcess D y)
          - D.weight z * (heavyExcess D y * heavyExcess D z)) := by
  classical
  have hcap := corner_twoInside_bracket_cap_sum D hlam hunit hgap hxy hxz hyz
  have hgapYX : subsetSum D ({y, x, z} : Finset (Fin m)) - 1
      = lam • atomMatrix u := by
    rw [show ({y, x, z} : Finset (Fin m)) = ({x, y, z} : Finset (Fin m)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
    exact hgap
  have hcomplYX : (({y, x, z} : Finset (Fin m))ᶜ)
      = (({x, y, z} : Finset (Fin m))ᶜ) := by
    rw [show ({y, x, z} : Finset (Fin m)) = ({x, y, z} : Finset (Fin m)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
  have hwx := corner_outside_wedge_total D hlam hunit hgap hxy hxz hyz
  have hwy := corner_outside_wedge_total D hlam hunit hgapYX (Ne.symm hxy) hyz hxz
  rw [hcomplYX] at hwy
  have hlevtot := corner_outside_leverage_total D hxy hxz hyz
  -- split the summed cap into its three closed pieces
  have hsplit : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d * (pairBracketSq (D.atom x) (D.atom d)
        + pairBracketSq (D.atom y) (D.atom d) - leverageOf (D.atom d))
      = (∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.weight d * pairBracketSq (D.atom x) (D.atom d))
        + (∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.weight d * pairBracketSq (D.atom y) (D.atom d))
        - ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.weight d * leverageOf (D.atom d) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hsplit, hwx, hwy, hlevtot] at hcap
  have hlx : leverageOf (D.atom x) = 1 + heavyExcess D x := by
    simp only [heavyExcess]; ring
  have hly : leverageOf (D.atom y) = 1 + heavyExcess D y := by
    simp only [heavyExcess]; ring
  nlinarith [hcap, hlx, hly]

end Gtz

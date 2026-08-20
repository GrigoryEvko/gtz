import Gtz.Wave.OneAxisZeroRefusalBudget
import Gtz.Wave.ExcludedAtomLedger
import Gtz.Reduction.MaximalVolume

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The anchor laws of the one-zero corner: the x-resolution, the reading cap,
# and the per-atom tie floor

The zero atom `x` of a `Z1` corner is unit and orthogonal to the two other
inside atoms (`Gtz.corner_oneAxisZero_xOrthogonal`).  Weighted Parseval then
makes `x` an exact eigenvector of the weighted outside mass: the outside atoms
resolve `(1 − t_x) • x` by themselves
(`Gtz.corner_oneAxisZero_outside_xResolve`), and their weighted squared
`x`-readings total exactly `1 − t_x`
(`Gtz.corner_oneAxisZero_outside_xMass`).  This is the per-atom directional
control of the outside family in the erased direction — the quantity every
aggregate law of the stratum so far has thrown away.

## The coweighted reading cap

At the erase-`x` anchor `B`, the reading ledger and the trace identity meet
the diagonal-below-trace bound of the erased unit atom and give a structural
CAP, with no tie and at every size
(`Gtz.corner_oneAxisZero_coweight_reading_cap`):

  `Σ_{a≠x} (1 − t_a − t_x) · r_a ≤ 3 (1 − t_x)` ,  `r_a = g_aᵀ B⁻¹ g_a` .

The exact remainder is `t_x (tr B⁻¹ − r_x) ≥ 0` — the same remainder as the
deficiency floor, spent on the readings instead of the deficiencies.

## The per-atom tie floor

A tie pushes the anchor readings UP through the pair floors while the cap
holds them DOWN, and the tension closes into a per-atom law
(`Gtz.corner_oneAxisZero_tie_reading_floor`): at a `(6,3)` tie with a `Z1`
corner, EVERY anchored atom obeys

  `t_a ≤ 2 · r_a · (1 − t_x + t_a)` .

The pair floors alone permit `r_a = 0` at one atom, and the cap alone permits
it at all five.  Their combination is the first per-atom lower bound of the
stratum, and it degenerates exactly as the weight `t_a` collapses — the
`(5,3)` boundary limit demands that.

## The cell dispatch

The four-set dichotomy and the two cell collapses of
`Gtz.Wave.OneAxisZeroRefusalBudget` compose into one dispatch
(`Gtz.corner_oneAxisZero_tie_cell_dispatch`): a `Z1` tie inhabits exactly one
of three floor systems — three outside floors at `A_y` when `A_z` fails,
three at `A_z` when `A_y` fails (`Gtz.corner_oneAxisZero_heavyInside_isTie_iff'`,
the relabelled collapse), or seven floors when both four-sets hold.  A proof
of the coverage residual can enter by cells and consume the floors directly.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The zero atom is orthogonal to the other inside atoms -/

/-- **The `Z1` orthogonality.**  The zero atom of the corner is orthogonal to
the two axis-carrying inside atoms: the corner pins every inside pairing to an
axis product, and the zero atom's axis reading vanishes. -/
theorem corner_oneAxisZero_xOrthogonal (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    D.atom x ⬝ᵥ D.atom y = 0 ∧ D.atom x ⬝ᵥ D.atom z = 0 := by
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hz : z ∈ ({x, y, z} : Finset (Fin m)) := by simp
  constructor
  · have hpair := corner_atomPairing_axis D _ hcard hlam hunit hgap hx hy hxy
    rw [hax] at hpair
    have h0 : (1 + lam) * atomPairing D x y = 0 := by rw [hpair]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (ne_of_gt hone)
    · simpa only [atomPairing] using h
  · have hpair := corner_atomPairing_axis D _ hcard hlam hunit hgap hx hz hxz
    rw [hax] at hpair
    have h0 : (1 + lam) * atomPairing D x z = 0 := by rw [hpair]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (ne_of_gt hone)
    · simpa only [atomPairing] using h

/-! ## 2. The outside atoms resolve the zero atom exactly -/

/-- **THE `x`-RESOLUTION.**  The outside atoms of a `Z1` corner resolve the
zero atom with total coefficient `1 − t_x`: weighted Parseval read at `x`
loses its three inside terms to the orthogonality and the unit leverage.
The `u`- and `w`-components of this identity are the cross-cancellation laws
of the outside family in the erased direction. -/
theorem corner_oneAxisZero_outside_xResolve (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        (D.weight d * (D.atom d ⬝ᵥ D.atom x)) • D.atom d
      = (1 - D.weight x) • D.atom x := by
  obtain ⟨hPxy, hPxz⟩ :=
    corner_oneAxisZero_xOrthogonal D hxy hxz hyz hlam hunit hgap hax
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  have hres := weighted_resolve D (D.atom x)
  rw [← Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
      (fun c => (D.weight c * (D.atom c ⬝ᵥ D.atom x)) • D.atom c),
    sum_triple_eq hxy hxz hyz, hlev,
    dotProduct_comm (D.atom y) (D.atom x), hPxy,
    dotProduct_comm (D.atom z) (D.atom x), hPxz] at hres
  simp only [mul_zero, zero_smul, add_zero, mul_one] at hres
  rw [sub_smul, one_smul]
  exact eq_sub_of_add_eq' hres

/-- **The `x`-mass identity.**  The weighted squared `x`-readings of the
outside atoms total exactly `1 − t_x`. -/
theorem corner_oneAxisZero_outside_xMass (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (D.atom d ⬝ᵥ D.atom x) ^ 2
      = 1 - D.weight x := by
  obtain ⟨hPxy, hPxz⟩ :=
    corner_oneAxisZero_xOrthogonal D hxy hxz hyz hlam hunit hgap hax
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  have hpar := parseval_read_corner_split D hxy hxz hyz (D.atom x)
  rw [hlev, dotProduct_comm (D.atom y) (D.atom x), hPxy,
    dotProduct_comm (D.atom z) (D.atom x), hPxz] at hpar
  nlinarith [hpar]

/-! ## 3. The coweighted reading cap of the anchor -/

/-- **THE COWEIGHTED READING CAP.**  At the erase-`x` anchor of a `Z1` corner
the coweighted readings are capped at `3(1 − t_x)`, with no tie hypothesis and
at every size from three atoms on.  The ledger prices the coweighted readings
at `3 + t_x r_x`, the trace identity prices the raw readings at `3 + tr B⁻¹`,
and the unit atom's reading sits below the trace. -/
theorem corner_oneAxisZero_coweight_reading_cap (D : WeightedDesign m 3)
    (hm : 3 ≤ m) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    ∑ a ∈ (univ : Finset (Fin m)).erase x,
        (1 - D.weight a - D.weight x)
          * (D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
              *ᵥ D.atom a))
      ≤ 3 * (1 - D.weight x) := by
  classical
  set F : Finset (Fin m) := (univ : Finset (Fin m)).erase x with hF
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  have hPD : (subsetSum D F - 1).PosDef :=
    complement_erase_posDef_of_leverage_le_one D hm hlev.le
  set B : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hB
  have hdet : IsUnit B.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have hcompl : (Fᶜ : Finset (Fin m)) = {x} := by
    rw [hF, Finset.compl_erase, Finset.compl_univ]
    rfl
  have hledger := subset_reading_ledger D F hPD
  rw [hcompl, Finset.sum_singleton, ← hB] at hledger
  have htrace : ∑ a ∈ F, D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a)
      = 3 + Matrix.trace B⁻¹ := by
    have hSF : subsetSum D F = B + 1 := by rw [hB]; abel
    have hexp := sum_subset_quadForm_eq_trace D F B⁻¹
    rw [hSF, Matrix.mul_add, Matrix.trace_add, Matrix.nonsing_inv_mul B hdet,
      Matrix.trace_one, Matrix.mul_one] at hexp
    rw [hexp, Fintype.card_fin]
    norm_num
  have hcap : D.atom x ⬝ᵥ (B⁻¹ *ᵥ D.atom x) ≤ Matrix.trace B⁻¹ := by
    have h := quadForm_le_trace_mul_dotProduct hPD.inv.posSemidef (D.atom x)
    rw [hlev, mul_one] at h
    exact h
  have hsplit : ∑ a ∈ F, (1 - D.weight a - D.weight x)
        * (D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a))
      = ∑ a ∈ F, (1 - D.weight a) * (D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a))
        - D.weight x * ∑ a ∈ F, D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsplit, hledger, htrace]
  nlinarith [hcap, D.weight_pos x]

/-! ## 4. The per-atom reading floor of a tie -/

/-- **THE PER-ATOM READING FLOOR.**  At a `(6,3)` tie with a `Z1` corner,
every anchored atom reads the anchor's inverse gap at least at
`t_a / (2(1 − t_x + t_a))`: the tie's pair floors push the other four
readings up, the coweighted cap holds the total down, and the atom's own
weight survives the cancellation.  The pair floors alone permit a zero
reading, and the cap alone permits five. -/
theorem corner_oneAxisZero_tie_reading_floor (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    {a : Fin 6} (ha : a ∈ (univ : Finset (Fin 6)).erase x) :
    D.weight a
      ≤ 2 * (D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom a))
        * (1 - D.weight x + D.weight a) := by
  classical
  set F : Finset (Fin 6) := (univ : Finset (Fin 6)).erase x with hF
  have hPD : (subsetSum D F - 1).PosDef :=
    corner_oneAxisZero_fiveSet_posDef D hxy hxz hyz hlam hunit hgap hax
  set B : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hB
  have hFcard : F.card = 5 := by
    rw [hF, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  have hcap := corner_oneAxisZero_coweight_reading_cap D (by norm_num)
    hxy hxz hyz hlam hunit hgap hax
  rw [← hF, ← hB] at hcap
  have hInv : (B⁻¹).PosSemidef := hPD.inv.posSemidef
  have hnn : ∀ c : Fin 6, 0 ≤ D.atom c ⬝ᵥ (B⁻¹ *ᵥ D.atom c) := by
    intro c
    have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hInv).2 (D.atom c)
    rwa [star_trivial] at this
  have hcw : ∀ c ∈ F, 0 ≤ 1 - D.weight c - D.weight x := by
    intro c hc
    have := sixWeight_pair_lt_one D (Finset.ne_of_mem_erase hc)
    linarith
  have hpair : ∀ c ∈ F.erase a,
      1 - (D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a)) ≤ D.atom c ⬝ᵥ (B⁻¹ *ᵥ D.atom c) := by
    intro c hc
    have hcF := Finset.mem_of_mem_erase hc
    have hca : c ≠ a := Finset.ne_of_mem_erase hc
    have := tie_fiveSet_pair_floor D htie F hFcard hPD hcF ha hca
    rw [← hB] at this
    linarith
  set ra : ℝ := D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a) with hra
  have hlow : (1 - D.weight a - D.weight x) * ra
      + (1 - ra) * ∑ c ∈ F.erase a, (1 - D.weight c - D.weight x)
      ≤ ∑ c ∈ F, (1 - D.weight c - D.weight x)
          * (D.atom c ⬝ᵥ (B⁻¹ *ᵥ D.atom c)) := by
    rw [← Finset.add_sum_erase F _ ha, ← hra]
    have hterm : ∀ c ∈ F.erase a,
        (1 - D.weight c - D.weight x) * (1 - ra)
          ≤ (1 - D.weight c - D.weight x)
              * (D.atom c ⬝ᵥ (B⁻¹ *ᵥ D.atom c)) := fun c hc =>
      mul_le_mul_of_nonneg_left (hpair c hc) (hcw c (Finset.mem_of_mem_erase hc))
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul] at hsum
    linarith [hsum]
  have hones : ∑ _c ∈ F, (1 : ℝ) = 5 := by
    rw [Finset.sum_const, hFcard]
    norm_num
  have hweights : ∑ c ∈ F, D.weight c = 1 - D.weight x := by
    have := Finset.add_sum_erase (univ : Finset (Fin 6)) D.weight (Finset.mem_univ x)
    rw [D.weight_sum_one] at this
    rw [hF]
    linarith
  have hcwsum : ∑ c ∈ F, (1 - D.weight c - D.weight x) = 4 * (1 - D.weight x) := by
    have hexp : ∑ c ∈ F, (1 - D.weight c - D.weight x)
        = (∑ _c ∈ F, (1 : ℝ)) - (∑ c ∈ F, D.weight c)
          - D.weight x * (∑ _c ∈ F, (1 : ℝ)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [hexp, hones, hweights]
    ring
  have hcwerase : ∑ c ∈ F.erase a, (1 - D.weight c - D.weight x)
      = 4 * (1 - D.weight x) - (1 - D.weight a - D.weight x) := by
    have := Finset.add_sum_erase F (fun c => 1 - D.weight c - D.weight x) ha
    rw [hcwsum] at this
    linarith
  rw [hcwerase] at hlow
  nlinarith [hcap, hlow, hnn a, D.weight_pos a, D.weight_pos x]

/-! ## 5. The relabelled heavy-inside collapse -/

/-- **The heavy-inside collapse, `y` and `z` exchanged.**  When the four-set
through `y` fails, the tie condition of the `Z1` corner is the three outside
floors at the four-set through `z`. -/
theorem corner_oneAxisZero_heavyInside_isTie_iff' (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (hay : D.atom y ⬝ᵥ u ≠ 0)
    (hnoty : ¬ (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    IsTie D ↔ ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ
        ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d) := by
  have hset : ({x, z, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) := by
    ext c
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hmain := corner_oneAxisZero_heavyInside_isTie_iff D hxz hxy (Ne.symm hyz)
    hlam hunit (by rw [hset]; exact hgap) hax hay
    (by rw [hset]; exact hnoty)
  rwa [hset] at hmain

/-! ## 6. The cell dispatch of a `Z1` tie -/

/-- **THE CELL DISPATCH.**  A `(6,3)` tie with a `Z1` proper corner inhabits
exactly one of three floor systems: three outside floors at the surviving
four-set when the other fails — in either order — or seven floors when both
four-sets hold.  The dichotomy excludes the double failure.  A proof of the
coverage residual can enter here and refute the floors cell by cell. -/
theorem corner_oneAxisZero_tie_cell_dispatch (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (hay : D.atom y ⬝ᵥ u ≠ 0)
    (haz : D.atom z ⬝ᵥ u ≠ 0) :
    (¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef
      ∧ ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          1 ≤ D.atom d ⬝ᵥ
            ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom d))
    ∨ (¬ (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef
      ∧ ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          1 ≤ D.atom d ⬝ᵥ
            ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom d))
    ∨ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef
      ∧ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef
      ∧ (1 ≤ D.atom y ⬝ᵥ
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom y))
      ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          1 ≤ D.atom d ⬝ᵥ
            ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom d))
      ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          1 ≤ D.atom d ⬝ᵥ
            ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom d))) := by
  classical
  by_cases hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef
  · by_cases hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef
    · right; right
      obtain ⟨h1, h2, h3⟩ := (corner_oneAxisZero_bothLight_isTie_iff D hxy hxz hyz
        hlam.le hunit hgap hax hAy hAz).mp htie
      exact ⟨hAy, hAz, h1, h2, h3⟩
    · left
      exact ⟨hAz, (corner_oneAxisZero_heavyInside_isTie_iff D hxy hxz hyz hlam
        hunit hgap hax haz hAz).mp htie⟩
  · by_cases hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef
    · right; left
      exact ⟨hAy, (corner_oneAxisZero_heavyInside_isTie_iff' D hxy hxz hyz hlam
        hunit hgap hax hay hAy).mp htie⟩
    · rcases corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax haz
        with h | h
      · exact absurd h hAz
      · exact absurd h hAy

end Gtz

import Gtz.Wave.OneAxisZeroDowndateOdds
import Gtz.Design.LineBranchFreePairAdjugateBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The erased deflation of the surviving four-set, and the member
# determinant floors

Measured at 512 bits, every stored survivor of the sharpened `Z1` clause
system fails the tie's raw pair clauses ONLY at the inside–outside pairs
`(z, d)`, and the outside atom whose floor holds is always the one that
carries the erased mass: its four-set reading is forced by pure
Cauchy–Schwarz in the erased direction.  This module lands that mechanism
in kernel, together with the member determinant floors that the same
diagnosis selects.

## The erased deflation

For a positive definite `A` the inverse dominates the rank-one deflation
along any probe `v` (`Gtz.psd_inv_deflation`):

  `A⁻¹ ⪰ (vᵀAv)⁻¹ · vvᵀ` ,

the deflated form kills `A *ᵥ v` exactly (`Gtz.psd_inv_deflation_mulVec`),
and the reading floor is the two-sided Cauchy–Schwarz
(`Gtz.deflation_reading_sq_le`):

  `(q ⬝ᵥ v)² ≤ (qᵀA⁻¹q)·(vᵀAv)` .

Because the deflated form is singular, the deflated Gram of ANY three
vectors is singular (`Gtz.deflated_gram_det_eq_zero`) — the rank-two
collapse of the `Z1` floor system, in kernel form.

## The erased energy of the four-set

At a `Z1` corner the erased atom `g_x` is orthogonal to both axis-carrying
inside atoms, so the four-set `A_y` reads it exactly at the outside mass
(`Gtz.corner_oneAxisZero_fourSet_erased_energy`):

  `g_xᵀ A_y g_x = g_xᵀ M_o g_x − 1 = Σ_d (q_d ⬝ᵥ g_x)² − 1 > 0` ,

positive by the landed erased over-read.  Cauchy–Schwarz then floors every
`A_y⁻¹` reading by its erased component
(`Gtz.corner_oneAxisZero_erased_reading_floor`), and an outside atom that
carries at least the whole erased energy has its tie floor for FREE — with
no tie (`Gtz.corner_oneAxisZero_erased_floor_free`).  At most one outside
atom can be that heavy once the energy passes one
(`Gtz.corner_oneAxisZero_erased_two_heavy_bound`).  Measured: at every
stored survivor the free-floor bound is nearly exact
(`r_d = 1.03575` against `ξ_d²/kxx = 1.03448` at the fork-21 survivor).

## The member determinant floors

A tie refuses every triple inside a dominating four-set, so every member's
removal determinant is nonpositive (`Gtz.tie_fourSet_member_det_nonpos`):

  `det(S_{F∖a} − 1) ≤ 0` for every `a ∈ F` .

The rank-one removal ledger (`Gtz.det_sub_atomMatrix_fin_three`,
`Gtz.subset_removal_det_ledger`) turns the four member floors into the
exact total `Σ_{a∈F} det(A_F − G_a) = det A_F − tr adj A_F`
(`Gtz.fourSet_member_det_total`), and dropping one pivot member gives the
PIVOT FLOOR (`Gtz.tie_fourSet_pivot_det_floor`):

  `det A_F ≤ tr adj A_F + det(S_{F∖e} − 1)` .

On the heavy-inside cell at `e = y` the pivot term is the outside gap
`det K ≤ 0` (landed), so the pivot floor strictly sharpens the landed
trace floor; the sharpened tie condition extends losslessly
(`Gtz.corner_oneAxisZero_heavyInside_isTie_iff_memberDet`), and the
both-light cell carries the member family at BOTH four-sets
(`Gtz.corner_oneAxisZero_bothLight_isTie_iff_memberDet`).  The member floor
at `a = y` is `det(S_{Cᶜ} − 1) ≤ 0`: the kernel form of the complement
split that removes the `Mo − 1 ≻ 0` share of the both-light cell.

## Calibration

The stored survivors violate the member family in 512-bit arithmetic
(`det(A_y − G_d) = 12.54, 36.61 > 0` at the fork-21 survivor).  The witness
satisfies all three outside member clauses in exact rationals
(`−2856/625, −5076/625, −1284/125`) and fails the `y`-member clause at
`det(S_{{3,4,5}} − 1) = 27 > 0`
(`Gtz.oneAxisZeroWitness_not_isTie_by_memberDet`) — a third, member-route
refutation of the witness tie.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The erased deflation instrument -/

/-- **THE INVERSE DEFLATION.**  A positive definite matrix's inverse
dominates the rank-one deflation along any probe: `A⁻¹ ⪰ (vᵀAv)⁻¹·vvᵀ`.
The probe `v = 0` degenerates to `A⁻¹ ⪰ 0`. -/
theorem psd_inv_deflation {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.PosDef) (v : Fin k → ℝ) :
    (A⁻¹ - (v ⬝ᵥ (A *ᵥ v))⁻¹ • Matrix.vecMulVec v v).PosSemidef := by
  have hAT : Aᵀ = A := PosDef.transpose_eq hA
  have hinvT : (A⁻¹)ᵀ = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hAT]
  have hInv : (A⁻¹).PosSemidef := hA.inv.posSemidef
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun q => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hinvT,
      show (Matrix.vecMulVec v v)ᵀ = Matrix.vecMulVec v v from
        transpose_eq_of_isHermitian (posSemidef_atomMatrix v).1]
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, vecMulVec_mulVec_eq, dotProduct_smul,
      smul_eq_mul]
    by_cases hv : v = 0
    · have hq0 : q ⬝ᵥ (A⁻¹ *ᵥ q) ≥ 0 := by
        have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hInv).2 q
        rwa [star_trivial] at h
      rw [hv]
      simp only [dotProduct_zero, zero_dotProduct, Matrix.mulVec_zero,
        mul_zero, _root_.inv_zero]
      linarith
    · have hE : 0 < v ⬝ᵥ (A *ᵥ v) := by
        have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hA).2 hv
        rwa [star_trivial] at h
      -- Cauchy–Schwarz at the inverse metric with the probes q and A v
      have hcs := psd_form_cross_sq_le hInv q (A *ᵥ v)
      have hqv : q ⬝ᵥ (A⁻¹ *ᵥ (A *ᵥ v)) = q ⬝ᵥ v := by
        rw [Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)),
          Matrix.one_mulVec]
      have hvv : (A *ᵥ v) ⬝ᵥ (A⁻¹ *ᵥ (A *ᵥ v)) = v ⬝ᵥ (A *ᵥ v) := by
        rw [Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)),
          Matrix.one_mulVec, dotProduct_comm]
      rw [hqv, hvv] at hcs
      have hqx : q ⬝ᵥ v = v ⬝ᵥ q := dotProduct_comm q v
      have hdiv : (v ⬝ᵥ (A *ᵥ v))⁻¹ * (v ⬝ᵥ q * (q ⬝ᵥ v))
          ≤ q ⬝ᵥ (A⁻¹ *ᵥ q) := by
        rw [← hqx, show q ⬝ᵥ v * (q ⬝ᵥ v) = (q ⬝ᵥ v) ^ 2 from (sq (q ⬝ᵥ v)).symm]
        rw [inv_mul_le_iff₀ hE, mul_comm]
        exact hcs
      linarith
/-- **The deflated form kills the image probe.**  The inverse deflation
annihilates `A *ᵥ v` exactly: the deflation drops the rank. -/
theorem psd_inv_deflation_mulVec {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.PosDef) (v : Fin k → ℝ) :
    (A⁻¹ - (v ⬝ᵥ (A *ᵥ v))⁻¹ • Matrix.vecMulVec v v) *ᵥ (A *ᵥ v) = 0 := by
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet,
    Matrix.one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec_eq]
  by_cases hv : v = 0
  · rw [hv]
    simp
  · have hE : 0 < v ⬝ᵥ (A *ᵥ v) := by
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hA).2 hv
      rwa [star_trivial] at h
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hE), one_smul, sub_self]

/-- **THE DEFLATION READING FLOOR.**  Cauchy–Schwarz between the inverse
reading and the direct energy: `(q ⬝ᵥ v)² ≤ (qᵀA⁻¹q)·(vᵀAv)`. -/
theorem deflation_reading_sq_le {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.PosDef) (q v : Fin k → ℝ) :
    (q ⬝ᵥ v) ^ 2 ≤ (q ⬝ᵥ (A⁻¹ *ᵥ q)) * (v ⬝ᵥ (A *ᵥ v)) := by
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hcs := psd_form_cross_sq_le hA.inv.posSemidef q (A *ᵥ v)
  have hqv : q ⬝ᵥ (A⁻¹ *ᵥ (A *ᵥ v)) = q ⬝ᵥ v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec]
  have hvv : (A *ᵥ v) ⬝ᵥ (A⁻¹ *ᵥ (A *ᵥ v)) = v ⬝ᵥ (A *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet,
      Matrix.one_mulVec, dotProduct_comm]
  rwa [hqv, hvv] at hcs

/-- **THE DEFLATED GRAM COLLAPSES.**  The deflated form is singular, so the
deflated Gram matrix of ANY three vectors has zero determinant: the whole
deflated floor system of the `Z1` stratum lives on a rank-two form. -/
theorem deflated_gram_det_eq_zero {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.PosDef) {v : Fin 3 → ℝ} (hv : v ≠ 0) (q : Fin 3 → Fin 3 → ℝ) :
    (Matrix.of fun i j : Fin 3 =>
      q i ⬝ᵥ ((A⁻¹ - (v ⬝ᵥ (A *ᵥ v))⁻¹ • Matrix.vecMulVec v v) *ᵥ q j)).det
      = 0 := by
  set Dm : Matrix (Fin 3) (Fin 3) ℝ :=
    A⁻¹ - (v ⬝ᵥ (A *ᵥ v))⁻¹ • Matrix.vecMulVec v v with hDm
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  -- the deflated form is singular
  have hAv : A *ᵥ v ≠ 0 := by
    intro h0
    refine hv ?_
    calc v = A⁻¹ *ᵥ (A *ᵥ v) := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet,
            Matrix.one_mulVec]
      _ = 0 := by rw [h0, Matrix.mulVec_zero]
  have hDdet : Dm.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp
      ⟨A *ᵥ v, hAv, psd_inv_deflation_mulVec hA v⟩
  -- the Gram factors through the vector matrix
  set Q : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun r c => q c r with hQ
  have hfact : (Matrix.of fun i j : Fin 3 => q i ⬝ᵥ (Dm *ᵥ q j))
      = Qᵀ * Dm * Q := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.mulVec, dotProduct, hQ, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => by
      ring
  rw [hfact, Matrix.det_mul, Matrix.det_mul, hDdet, mul_zero, zero_mul]

/-! ## 2. The erased energy of the surviving four-set -/

/-- **THE ERASED ENERGY OF THE FOUR-SET.**  At a `Z1` corner the four-set
through `y` reads the erased atom exactly at the outside mass: the inside
atoms are orthogonal to `g_x` and its leverage is one. -/
theorem corner_oneAxisZero_fourSet_erased_energy (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)
        *ᵥ D.atom x)
      = D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) *ᵥ D.atom x)
        - 1 := by
  classical
  have hyK : y ∉ (({x, y, z} : Finset (Fin m))ᶜ) := by simp
  have hsplit : subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ))
      = atomMatrix (D.atom y) + subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) := by
    rw [subsetSum, subsetSum, Finset.sum_insert hyK]
  have hyx : D.atom y ⬝ᵥ D.atom x = 0 := by
    rw [dotProduct_comm]
    exact (corner_oneAxisZero_xOrthogonal D hxy hxz hyz hlam hunit hgap hax).1
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  rw [hsplit, Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub,
    dotProduct_add, Matrix.one_mulVec, hlev,
    show atomMatrix (D.atom y) = Matrix.vecMulVec (D.atom y) (D.atom y) from rfl,
    vecMulVec_mulVec_eq, hyx, zero_smul, dotProduct_zero]
  ring

/-- **The erased energy is positive** — the strict over-read at the sharpest
weight cap, with no cap hypotheses: the outside weight total is a legal cap. -/
theorem corner_oneAxisZero_fourSet_erased_energy_pos (D : WeightedDesign m 3)
    (hm : 4 ≤ m) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    0 < D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) *ᵥ D.atom x)
        - 1 := by
  classical
  set ms : ℝ := ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d with hmsdef
  have hKne : ((({x, y, z} : Finset (Fin m))ᶜ)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, card_triple_eq hxy hxz hyz,
      Fintype.card_fin]
    omega
  have hms : 0 < ms := Finset.sum_pos (fun d _ => D.weight_pos d) hKne
  have hmd : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d ≤ ms :=
    fun d hd => Finset.single_le_sum (fun e _ => (D.weight_pos e).le) hd
  have hmx : ms + D.weight x < 1 := by
    have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m)) D.weight
    rw [D.weight_sum_one, sum_triple_eq hxy hxz hyz] at hsplit
    have hy := D.weight_pos y
    have hz := D.weight_pos z
    rw [hmsdef]
    linarith
  have h := corner_oneAxisZero_erased_overRead_strict D hxy hxz hyz hlam hunit
    hgap hax hms hmx hmd
  linarith

/-- **THE ERASED READING FLOOR.**  Every `A_y⁻¹` reading is floored by its
erased component against the outside erased mass:

  `(q ⬝ᵥ g_x)² ≤ (qᵀ A_y⁻¹ q) · (g_xᵀ M_o g_x − 1)` .

Tie-free: this is the deflation Cauchy–Schwarz at the erased probe. -/
theorem corner_oneAxisZero_erased_reading_floor (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef)
    (q : Fin 3 → ℝ) :
    (q ⬝ᵥ D.atom x) ^ 2
      ≤ (q ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
            *ᵥ q))
        * (D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
              *ᵥ D.atom x) - 1) := by
  have hfloor := deflation_reading_sq_le hAy q (D.atom x)
  rwa [corner_oneAxisZero_fourSet_erased_energy D hxy hxz hyz hlam hunit hgap
    hax] at hfloor

/-- **THE FREE FLOOR.**  An outside atom that carries at least the whole
erased energy has its four-set tie floor with NO tie: one of the three
heavy-inside clauses is unconditional on the heavy-erased subcell.  At the
stored fork-21 survivor the bound is nearly exact: `r_d = 1.03575` against
`ξ_d²/(g_xᵀM_og_x − 1) = 1.03448`. -/
theorem corner_oneAxisZero_erased_floor_free (D : WeightedDesign m 3)
    (hm : 4 ≤ m) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef)
    {q : Fin 3 → ℝ}
    (hheavy : D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
          *ᵥ D.atom x) - 1
        ≤ (q ⬝ᵥ D.atom x) ^ 2) :
    1 ≤ q ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
        *ᵥ q) := by
  have hE := corner_oneAxisZero_fourSet_erased_energy_pos D hm hxy hxz hyz hlam
    hunit hgap hax
  have hfloor := corner_oneAxisZero_erased_reading_floor D hxy hxz hyz hlam
    hunit hgap hax hAy q
  nlinarith [hE, hfloor, hheavy]

/-- **The erased mass splits over the outside atoms**: the outside erased
energy is the square sum of the erased components minus one. -/
theorem corner_oneAxisZero_erased_mass_split (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) *ᵥ D.atom x) - 1
      = ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ D.atom x) ^ 2
        - 1 := by
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  have hquad := quadForm_subsetSum_sub_one D (({x, y, z} : Finset (Fin m))ᶜ)
    (D.atom x)
  have hstep : D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) - 1)
      *ᵥ D.atom x)
      = D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) *ᵥ D.atom x)
        - 1 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hlev]
  rw [← hstep, hquad, hlev]

/-- **AT MOST ONE HEAVY-ERASED ATOM.**  When the erased energy passes one,
two distinct outside atoms cannot both carry it: the free floor is a
single-atom privilege.  This is the measured survivor geometry — exactly one
outside atom rides the erased direction. -/
theorem corner_oneAxisZero_erased_two_heavy_bound (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    {d e : Fin m} (hd : d ∈ (({x, y, z} : Finset (Fin m))ᶜ))
    (he : e ∈ (({x, y, z} : Finset (Fin m))ᶜ)) (hde : d ≠ e)
    (hdheavy : D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
          *ᵥ D.atom x) - 1
        ≤ (D.atom d ⬝ᵥ D.atom x) ^ 2)
    (heheavy : D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
          *ᵥ D.atom x) - 1
        ≤ (D.atom e ⬝ᵥ D.atom x) ^ 2) :
    D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) *ᵥ D.atom x) - 1
      ≤ 1 := by
  classical
  have hsplit := corner_oneAxisZero_erased_mass_split D hxy hxz hyz hlam hunit
    hgap hax
  have hpair : (D.atom d ⬝ᵥ D.atom x) ^ 2 + (D.atom e ⬝ᵥ D.atom x) ^ 2
      ≤ ∑ c ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom c ⬝ᵥ D.atom x) ^ 2 := by
    have hsub : ({d, e} : Finset (Fin m)) ⊆ (({x, y, z} : Finset (Fin m))ᶜ) := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hd
      · rw [Finset.mem_singleton.mp hc]
        exact he
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun c _ _ => sq_nonneg (D.atom c ⬝ᵥ D.atom x))
    rwa [Finset.sum_insert (by simp [hde]), Finset.sum_singleton] at hsum
  nlinarith [hsplit, hpair, hdheavy, heheavy]

/-! ## 3. The member determinant floors -/

/-- **THE SUBSET REMOVAL LEDGER.**  Over any label subset the removal
determinants total the subset count against the base determinant minus one
adjugate trace against the subset's unweighted mass. -/
theorem subset_removal_det_ledger (D : WeightedDesign m 3)
    (S : Finset (Fin m)) (N : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ a ∈ S, (N - atomMatrix (D.atom a)).det
      = (S.card : ℝ) * N.det - Matrix.trace (N.adjugate * subsetSum D S) := by
  have hterm : ∀ a ∈ S, (N - atomMatrix (D.atom a)).det
      = N.det - D.atom a ⬝ᵥ (N.adjugate *ᵥ D.atom a) := fun a _ =>
    det_sub_atomMatrix_fin_three N (D.atom a)
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, subsetSum, Matrix.mul_sum, Matrix.trace_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ =>
    (trace_mul_atomMatrix N.adjugate (D.atom a)).symm

/-- **THE FOUR-MEMBER REMOVAL TOTAL.**  Over a card-4 subset with base at its
own gap, the four removal determinants total the gap determinant minus its
adjugate trace — an identity, no tie. -/
theorem fourSet_member_det_total (D : WeightedDesign m 3)
    (F : Finset (Fin m)) (hF : F.card = 4) :
    ∑ a ∈ F, ((subsetSum D F - 1) - atomMatrix (D.atom a)).det
      = (subsetSum D F - 1).det
        - Matrix.trace (subsetSum D F - 1).adjugate := by
  set N : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hN
  have hledger := subset_removal_det_ledger D F N
  have hmass : subsetSum D F = N + 1 := by rw [hN]; abel
  have htr : Matrix.trace (N.adjugate * subsetSum D F)
      = 3 * N.det + Matrix.trace N.adjugate := by
    rw [hmass, Matrix.mul_add, Matrix.trace_add, Matrix.adjugate_mul,
      Matrix.trace_smul, Matrix.trace_one, Matrix.mul_one]
    simp only [smul_eq_mul, Fintype.card_fin]
    ring
  rw [hledger, htr, hF]
  push_cast
  ring

/-- **THE MEMBER DETERMINANT FLOOR.**  At a tie, every member of a strictly
dominating four-set has nonpositive removal determinant: the triple that
drops the member is refused, and the member's atom completes it back to the
dominating four-set. -/
theorem tie_fourSet_member_det_nonpos (D : WeightedDesign m 3)
    (htie : IsTie D) (F : Finset (Fin m)) (hF : F.card = 4)
    (hPD : (subsetSum D F - 1).PosDef) {a : Fin m} (ha : a ∈ F) :
    (subsetSum D (F.erase a) - 1).det ≤ 0 := by
  have hT : (F.erase a).card = 3 := by
    rw [Finset.card_erase_of_mem ha, hF]
  have hnot := htie.2 (F.erase a) hT
  have hdown : subsetSum D (F.erase a) - 1
      = (subsetSum D F - 1) - atomMatrix (D.atom a) := by
    rw [subsetSum_erase_sub_one_rankOne D F ha,
      show atomMatrix (D.atom a) = Matrix.vecMulVec (D.atom a) (D.atom a)
        from rfl]
  have hcomplete : (subsetSum D (F.erase a) - 1) + atomMatrix (D.atom a)
      = subsetSum D F - 1 := by
    rw [hdown]
    abel
  refine det_nonpos_of_not_posDef_of_add_atomMatrix_posDef
    (p := D.atom a) ?_ hnot
  rw [hcomplete]
  exact hPD

/-- **THE PIVOT DETERMINANT FLOOR.**  At a tie, dropping one pivot member
from the removal total floors the four-set determinant by its adjugate trace
plus the pivot's own removal determinant:

  `det(S_F − 1) ≤ tr adj(S_F − 1) + det(S_{F∖e} − 1)` .

Averaged over the pivot this is the landed trace floor; at the heavy-inside
pivot `e = y` the removal term is the outside gap determinant, nonpositive
on the cell, so the pivot floor strictly sharpens the trace floor there. -/
theorem tie_fourSet_pivot_det_floor (D : WeightedDesign m 3)
    (htie : IsTie D) (F : Finset (Fin m)) (hF : F.card = 4)
    (hPD : (subsetSum D F - 1).PosDef) {e : Fin m} (he : e ∈ F) :
    (subsetSum D F - 1).det
      ≤ Matrix.trace (subsetSum D F - 1).adjugate
        + (subsetSum D (F.erase e) - 1).det := by
  classical
  have htotal := fourSet_member_det_total D F hF
  have hpivot := Finset.add_sum_erase F
    (fun a => ((subsetSum D F - 1) - atomMatrix (D.atom a)).det) he
  have hrest : ∑ a ∈ F.erase e,
      ((subsetSum D F - 1) - atomMatrix (D.atom a)).det ≤ 0 := by
    refine Finset.sum_nonpos fun a ha => ?_
    have haF := Finset.mem_of_mem_erase ha
    have hval := tie_fourSet_member_det_nonpos D htie F hF hPD haF
    rwa [subsetSum_erase_sub_one_rankOne D F haF] at hval
  have hedet : ((subsetSum D F - 1) - atomMatrix (D.atom e)).det
      = (subsetSum D (F.erase e) - 1).det := by
    rw [subsetSum_erase_sub_one_rankOne D F he,
      show atomMatrix (D.atom e) = Matrix.vecMulVec (D.atom e) (D.atom e)
        from rfl]
  linarith [htotal, hpivot, hrest, hedet]

/-! ## 4. The heavy-inside cell carries the member family -/

/-- **THE HEAVY-INSIDE MEMBER FLOORS.**  At a `Z1` tie in the heavy-inside
cell every outside atom's removal determinant at the surviving four-set is
nonpositive, and the pivot floor at `y` caps the four-set determinant by its
adjugate trace plus the outside gap determinant. -/
theorem corner_oneAxisZero_heavyInside_member_det_floor (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
          - atomMatrix (D.atom d)).det ≤ 0)
    ∧ (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det
        ≤ Matrix.trace (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1).adjugate
          + (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).det := by
  classical
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hF : (insert y (({x, y, z} : Finset (Fin 6))ᶜ)).card = 4 := by
    rw [Finset.card_insert_of_notMem hyK,
      card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)]
  constructor
  · intro d hd
    have hdF : d ∈ insert y (({x, y, z} : Finset (Fin 6))ᶜ) :=
      Finset.mem_insert_of_mem hd
    have hval := tie_fourSet_member_det_nonpos D htie _ hF hAy hdF
    rwa [subsetSum_erase_sub_one_rankOne D _ hdF] at hval
  · have hpivot := tie_fourSet_pivot_det_floor D htie _ hF hAy
      (Finset.mem_insert_self y _)
    rwa [Finset.erase_insert hyK] at hpivot

/-- **The tie condition of the heavy-inside cell, sharpened by the member
determinant floors.**  Lossless: the member clauses are tie-necessary and the
three landed floors already rebuild the tie. -/
theorem corner_oneAxisZero_heavyInside_isTie_iff_memberDet (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    IsTie D ↔
      ((∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        1 ≤ D.atom d ⬝ᵥ
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom d))
      ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
              - atomMatrix (D.atom d)).det ≤ 0)
      ∧ (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det
          ≤ Matrix.trace (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1).adjugate
            + (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).det) := by
  constructor
  · intro htie
    have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
      (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
        haz).resolve_left hnotz
    obtain ⟨hmember, hpivot⟩ := corner_oneAxisZero_heavyInside_member_det_floor
      D htie hxy hxz hyz hAy
    exact ⟨(corner_oneAxisZero_heavyInside_isTie_iff D hxy hxz hyz hlam hunit
      hgap hax haz hnotz).mp htie, hmember, hpivot⟩
  · rintro ⟨hfloors, -, -⟩
    exact (corner_oneAxisZero_heavyInside_isTie_iff D hxy hxz hyz hlam hunit
      hgap hax haz hnotz).mpr hfloors

/-! ## 5. The both-light cell carries the member family at both four-sets -/

/-- **THE BOTH-LIGHT MEMBER FLOORS.**  At a `Z1` tie with both four-sets
positive definite, the member determinant family holds at BOTH: every
outside removal determinant is nonpositive at each four-set, and the member
floor at the inside pivot is the complement determinant `det(S_{Cᶜ} − 1) ≤ 0`
— the kernel shadow of the complement refusal that empties the
`S_{Cᶜ} − 1 ≻ 0` share of the cell. -/
theorem corner_oneAxisZero_bothLight_member_det_floor (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
          - atomMatrix (D.atom d)).det ≤ 0)
    ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
            - atomMatrix (D.atom d)).det ≤ 0)
    ∧ (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).det ≤ 0 := by
  classical
  have hswap : ({x, z, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) :=
    triple_swap_eq
  have hyfam := corner_oneAxisZero_heavyInside_member_det_floor D htie hxy hxz
    hyz hAy
  have hzfam := corner_oneAxisZero_heavyInside_member_det_floor D htie hxz hxy
    (Ne.symm hyz) (by rw [hswap]; exact hAz)
  refine ⟨hyfam.1, ?_, ?_⟩
  · intro d hd
    have hd' : d ∈ (({x, z, y} : Finset (Fin 6))ᶜ) := by
      rw [hswap]
      exact hd
    have h := hzfam.1 d hd'
    rwa [hswap] at h
  · have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
    have hF : (insert y (({x, y, z} : Finset (Fin 6))ᶜ)).card = 4 := by
      rw [Finset.card_insert_of_notMem hyK,
        card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)]
    have hval := tie_fourSet_member_det_nonpos D htie _ hF hAy
      (Finset.mem_insert_self y _)
    rwa [Finset.erase_insert hyK] at hval

/-- **The tie condition of the both-light cell, sharpened by the member
determinant floors at both four-sets.**  Lossless over the landed seven
floors. -/
theorem corner_oneAxisZero_bothLight_isTie_iff_memberDet (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    IsTie D ↔
      ((1 ≤ D.atom y ⬝ᵥ
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom y))
      ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          1 ≤ D.atom d ⬝ᵥ
            ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom d))
      ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          1 ≤ D.atom d ⬝ᵥ
            ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom d))
      ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
              - atomMatrix (D.atom d)).det ≤ 0)
      ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
              - atomMatrix (D.atom d)).det ≤ 0)
      ∧ (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).det ≤ 0) := by
  constructor
  · intro htie
    obtain ⟨hy7, hyfl, hzfl⟩ := (corner_oneAxisZero_bothLight_isTie_iff D hxy
      hxz hyz hlam hunit hgap hax hAy hAz).mp htie
    obtain ⟨hym, hzm, hK⟩ := corner_oneAxisZero_bothLight_member_det_floor D
      htie hxy hxz hyz hAy hAz
    exact ⟨hy7, hyfl, hzfl, hym, hzm, hK⟩
  · rintro ⟨hy7, hyfl, hzfl, -, -, -⟩
    exact (corner_oneAxisZero_bothLight_isTie_iff D hxy hxz hyz hlam hunit
      hgap hax hAy hAz).mpr ⟨hy7, hyfl, hzfl⟩

/-! ## 6. The witness fails the member family at the inside pivot -/

/-- The complement determinant of the witness is `27`: the outside triple
over-dominates with margin three in every direction. -/
theorem oneAxisZeroWitness_complement_det :
    (subsetSum oneAxisZeroWitness ({3, 4, 5} : Finset (Fin 6)) - 1).det = 27 := by
  rw [oneAxisZeroWitness_compl_form]
  rw [show ((3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      = !![3, 0, 0; 0, 3, 0; 0, 0, 3] from by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]]
  rw [Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- **The witness is not a tie, by the member determinant route.**  The
four-set through atom `1` dominates strictly, so at a tie the member floor
at the pivot `1` would force `det(S_{{3,4,5}} − 1) ≤ 0`; the determinant is
`27` in exact rationals. -/
theorem oneAxisZeroWitness_not_isTie_by_memberDet :
    ¬ IsTie oneAxisZeroWitness := by
  intro htie
  have hcompl : ((({0, 1, 2} : Finset (Fin 6))ᶜ) : Finset (Fin 6)) = {3, 4, 5} := by
    decide
  have hF : (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)).card = 4 := by
    rw [hcompl]
    decide
  have hmem : (1 : Fin 6) ∈ insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ) :=
    Finset.mem_insert_self 1 _
  have hval := tie_fourSet_member_det_nonpos oneAxisZeroWitness htie _ hF
    (oneAxisZeroWitness_fourSet_posDef (Or.inl rfl)) hmem
  have herase : (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)).erase 1
      = ({3, 4, 5} : Finset (Fin 6)) := by
    rw [hcompl]
    decide
  rw [herase, oneAxisZeroWitness_complement_det] at hval
  norm_num at hval

/-! ## 7. The outside member clauses hold at the witness, exactly -/

/-- The removal determinant of the witness four-set at the outside atom `3`:
`−2856/625`. -/
theorem oneAxisZeroWitness_memberDet_three :
    ((subsetSum oneAxisZeroWitness (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1)
        - atomMatrix (oneAxisZeroWitness.atom 3)).det = -(2856 / 625) := by
  have hM : subsetSum oneAxisZeroWitness
        (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
        - atomMatrix (oneAxisZeroWitness.atom 3)
      = !![-(184 / 625), 0, 84 / 125; 0, 3, 0; 84 / 125, 0, 91 / 25] := by
    rw [oneAxisZeroWitness_fourSet_form]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [atomMatrix, Matrix.vecMulVec_apply, oneAxisZeroWitness_atom,
        oneAxisZeroWitnessAtom, Matrix.one_apply, Matrix.cons_val_two]
  rw [hM, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The removal determinant of the witness four-set at the outside atom `4`:
`−5076/625`. -/
theorem oneAxisZeroWitness_memberDet_four :
    ((subsetSum oneAxisZeroWitness (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1)
        - atomMatrix (oneAxisZeroWitness.atom 4)).det = -(5076 / 625) := by
  have hM : subsetSum oneAxisZeroWitness
        (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
        - atomMatrix (oneAxisZeroWitness.atom 4)
      = !![2316 / 625, 0, 84 / 125; 0, 39 / 25, -(48 / 25);
          84 / 125, -(48 / 25), 27 / 25] := by
    rw [oneAxisZeroWitness_fourSet_form]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [atomMatrix, Matrix.vecMulVec_apply, oneAxisZeroWitness_atom,
        oneAxisZeroWitnessAtom, Matrix.one_apply, Matrix.cons_val_two]
  rw [hM, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The removal determinant of the witness four-set at the outside atom `5`:
`−1284/125`.  All three outside member clauses hold at the witness: the
member family refutes the witness only at the inside pivot. -/
theorem oneAxisZeroWitness_memberDet_five :
    ((subsetSum oneAxisZeroWitness (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1)
        - atomMatrix (oneAxisZeroWitness.atom 5)).det = -(1284 / 125) := by
  have hM : subsetSum oneAxisZeroWitness
        (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
        - atomMatrix (oneAxisZeroWitness.atom 5)
      = !![2316 / 625, 0, 84 / 125; 0, 11 / 25, 48 / 25;
          84 / 125, 48 / 25, 11 / 5] := by
    rw [oneAxisZeroWitness_fourSet_form]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [atomMatrix, Matrix.vecMulVec_apply, oneAxisZeroWitness_atom,
        oneAxisZeroWitnessAtom, Matrix.one_apply, Matrix.cons_val_two]
  rw [hM, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-! ## 8. The heavy-erased reduction of the tie condition -/

/-- **THE HEAVY-ERASED REDUCTION.**  On the heavy-inside cell, when one
outside atom carries at least the whole erased energy, its floor is free and
the tie condition collapses to the TWO floors of the other outside atoms:
one of the ten raw pair clauses of the anchor leaves the system for
nothing.  At the fork-21 survivor the heavy atom exists (`ξ²/kxx = 1.035`),
so the residual fight there is a two-floor fight. -/
theorem corner_oneAxisZero_heavyInside_isTie_iff_heavyErased
    (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    {d : Fin 6} (_hd : d ∈ (({x, y, z} : Finset (Fin 6))ᶜ))
    (hheavy : D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
          *ᵥ D.atom x) - 1
        ≤ (D.atom d ⬝ᵥ D.atom x) ^ 2) :
    IsTie D ↔ ∀ e ∈ (({x, y, z} : Finset (Fin 6))ᶜ), e ≠ d →
      1 ≤ D.atom e ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom e) := by
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  rw [corner_oneAxisZero_heavyInside_isTie_iff D hxy hxz hyz hlam hunit hgap
    hax haz hnotz]
  constructor
  · intro hfloors e he _
    exact hfloors e he
  · intro htwo e he
    by_cases hed : e = d
    · rw [hed]
      exact corner_oneAxisZero_erased_floor_free D (by norm_num) hxy hxz hyz
        hlam.le hunit hgap hax hAy hheavy
    · exact htwo e he hed

/-! ## 9. The deflated moment rails of the four-set -/

/-- **The deflated reading split**, definitional: every four-set reading is
its deflated reading plus the erased share.  The identity that moves the
floors into the deflated arena, losslessly. -/
theorem corner_oneAxisZero_deflated_reading_split (D : WeightedDesign m 3)
    (hm : 4 ≤ m) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (q : Fin 3 → ℝ) :
    q ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹ *ᵥ q)
      = q ⬝ᵥ (((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
            - (D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
                  *ᵥ D.atom x) - 1)⁻¹
              • Matrix.vecMulVec (D.atom x) (D.atom x)) *ᵥ q)
        + (q ⬝ᵥ D.atom x) ^ 2
          / (D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
              *ᵥ D.atom x) - 1) := by
  have hE := corner_oneAxisZero_fourSet_erased_energy_pos D hm hxy hxz hyz hlam
    hunit hgap hax
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    show D.atom x ⬝ᵥ q = q ⬝ᵥ D.atom x from dotProduct_comm _ _]
  field_simp
  ring

/-- **THE DEFLATED OUTSIDE TOTAL.**  The three deflated outside readings of
the four-set total exactly

  `Σ_d q_dᵀD_y q_d = 2 + tr A_y⁻¹ − r_y(A_y) − 1/kxx` :

the unweighted moment rail of the deflated floor system.  An identity given
the four-set dominates — no tie. -/
theorem corner_oneAxisZero_deflated_outside_total (D : WeightedDesign m 3)
    (hm : 4 ≤ m) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.atom d ⬝ᵥ
          (((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
              - (D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
                    *ᵥ D.atom x) - 1)⁻¹
                • Matrix.vecMulVec (D.atom x) (D.atom x)) *ᵥ D.atom d)
      = 2 + Matrix.trace (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ))
              - 1)⁻¹
        - D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ))
              - 1)⁻¹ *ᵥ D.atom y)
        - (D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
              *ᵥ D.atom x) - 1)⁻¹ := by
  classical
  set A : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1 with hA
  set E : ℝ := D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
    *ᵥ D.atom x) - 1 with hEdef
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hAy.det_pos)
  have hyK : y ∉ (({x, y, z} : Finset (Fin m))ᶜ) := by simp
  have hsplit : ∀ d : Fin m,
      D.atom d ⬝ᵥ ((A⁻¹ - E⁻¹ • Matrix.vecMulVec (D.atom x) (D.atom x))
          *ᵥ D.atom d)
        = D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d)
          - E⁻¹ * (D.atom d ⬝ᵥ D.atom x) ^ 2 := by
    intro d
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      show D.atom x ⬝ᵥ D.atom d = D.atom d ⬝ᵥ D.atom x from dotProduct_comm _ _]
    ring
  rw [Finset.sum_congr rfl fun d _ => hsplit d, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  have htr : Matrix.trace (A⁻¹ * subsetSum D (({x, y, z} : Finset (Fin m))ᶜ))
      = ∑ a ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a) := by
    rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun a _ => trace_mul_atomMatrix A⁻¹ (D.atom a)
  have hMo : subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
      = A + 1 - atomMatrix (D.atom y) := by
    rw [hA, subsetSum, subsetSum, Finset.sum_insert hyK]
    abel
  have houtside : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d)
      = 3 + Matrix.trace A⁻¹ - D.atom y ⬝ᵥ (A⁻¹ *ᵥ D.atom y) := by
    have h := htr
    rw [hMo, Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add,
      Matrix.nonsing_inv_mul A hdet, Matrix.trace_one, Matrix.mul_one,
      trace_mul_atomMatrix, Fintype.card_fin] at h
    rw [← h]
    norm_num
  have hmass := corner_oneAxisZero_erased_mass_split D hxy hxz hyz hlam hunit
    hgap hax
  have hsum2 : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ D.atom x) ^ 2
      = E + 1 := by
    rw [hEdef]
    linarith [hmass]
  have hEpos : 0 < E := by
    rw [hEdef]
    exact corner_oneAxisZero_fourSet_erased_energy_pos D hm hxy hxz hyz hlam
      hunit hgap hax
  have hEE : E⁻¹ * (E + 1) = 1 + E⁻¹ := by
    field_simp
  rw [houtside, hsum2, hEE]
  ring

/-- **THE DEFLATED PARSEVAL.**  The full weighted trace of the deflated form
is the inverse trace minus the inverse erased energy:

  `Σ_c t_c g_cᵀD_y g_c = tr A_y⁻¹ − 1/kxx` ,

because Parseval reads the erased direction at exactly one.  An identity —
no tie, no positivity: the weighted moment rail of the deflated floor
system. -/
theorem corner_oneAxisZero_deflated_parseval (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    ∑ c, D.weight c
        * (D.atom c ⬝ᵥ
          (((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
              - (D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
                    *ᵥ D.atom x) - 1)⁻¹
                • Matrix.vecMulVec (D.atom x) (D.atom x)) *ᵥ D.atom c))
      = Matrix.trace (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ))
            - 1)⁻¹
        - (D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
              *ᵥ D.atom x) - 1)⁻¹ := by
  classical
  set A : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1 with hA
  set E : ℝ := D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
    *ᵥ D.atom x) - 1 with hEdef
  have hterm : ∀ c : Fin m, D.weight c
      * (D.atom c ⬝ᵥ ((A⁻¹ - E⁻¹ • Matrix.vecMulVec (D.atom x) (D.atom x))
          *ᵥ D.atom c))
      = D.weight c * (D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c))
        - E⁻¹ * (D.weight c * (D.atom c ⬝ᵥ D.atom x) ^ 2) := by
    intro c
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      show D.atom x ⬝ᵥ D.atom c = D.atom c ⬝ᵥ D.atom x from dotProduct_comm _ _]
    ring
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  have hfull : ∑ c, D.weight c * (D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c))
      = Matrix.trace A⁻¹ := by
    have htr : Matrix.trace (A⁻¹ * ∑ c, D.weight c • atomMatrix (D.atom c))
        = ∑ c, D.weight c * (D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c)) := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_smul_comm, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
    rw [← htr, D.isParseval, Matrix.mul_one]
  have hxlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  have hxmass : ∑ c, D.weight c * (D.atom c ⬝ᵥ D.atom x) ^ 2 = 1 := by
    rw [sum_weight_read_sq D (D.atom x), hxlev]
  rw [hfull, hxmass, mul_one]

end Gtz

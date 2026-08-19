import Gtz.Wave.GhostBlockCore
import Gtz.Wave.SixSetGapUniversal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The weighted ghost deficit: the four-set descent consumed at full strength

`Gtz.not_isTie_of_ghost_readings_lt` closes a four-set when BOTH ghost readings
sit below one.  That is more than the descent supplies.  The descent
(`Gtz.tie_forces_ghost_reading`) forces only the WEIGHTED statement

  `Σ_f t_f ≤ Σ_f t_f · x_f` ,

so a single weighted combination falling short already refutes the tie.  One
ghost reading may exceed one, provided the other is small enough and the weights
say so.

## The readings, in multiplied form

Two applications of the Sherman–Morrison reading (`Gtz.downdate_reading`)
express a ghost reading through the ghost block of six-set pivots alone.  With
`a = P_ff`, `b = P_hh`, `c = P_fh` and `Δ = (1−a)(1−b) − c²`,

  `x_f · Δ = a(1−b) + c²` ,

stated MULTIPLIED so that no inverse survives into the algebra
(`Gtz.ghostReading_mul_det`); the scalar core `Gtz.ghostReading_scalar` is three
`linear_combination` steps against the two inverse relations.  Positivity of `Δ`
together with `a < 1` is exactly positive definiteness of the four-set gap
(`Gtz.posDef_sub_two_vecMulVec_iff`), and `Gtz.sixSetGap_posDef` makes the
six-set gap positive definite with no hypothesis at all.

Clearing the denominator turns the descent into a POLYNOMIAL refutation
(`Gtz.not_isTie_of_weightedGhostDeficit`)

  `t_f·(a(1−b) + c²) + t_h·(b(1−a) + c²) < (t_f + t_h)·Δ` ,

with no inverse, no eigenvalue, and no reading of a four-set metric anywhere.
It is implied by `Gtz.GhostBlockShort` but strictly weaker, so it is the widest
dispatch surface the corank-two corner has.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The scalar core -/

/-- **The ghost reading, multiplied out.**  Three `linear_combination` steps
against the two inverse relations.  No division appears. -/
theorem ghostReading_scalar {a b c ib ir r : ℝ}
    (h1 : ib * (1 - b) = 1) (h2 : ir * (1 - r) = 1) (h3 : r = a + ib * c ^ 2) :
    (r + ir * r ^ 2) * ((1 - a) * (1 - b) - c ^ 2) = a * (1 - b) + c ^ 2 := by
  have hA : (r + ir * r ^ 2) * (1 - r) = r := by linear_combination r ^ 2 * h2
  have hB : (1 - r) * (1 - b) = (1 - a) * (1 - b) - c ^ 2 := by
    linear_combination (-(1 - b)) * h3 - c ^ 2 * h1
  have hC : r * (1 - b) = a * (1 - b) + c ^ 2 := by
    linear_combination (1 - b) * h3 + c ^ 2 * h1
  calc (r + ir * r ^ 2) * ((1 - a) * (1 - b) - c ^ 2)
      = (r + ir * r ^ 2) * ((1 - r) * (1 - b)) := by rw [hB]
    _ = ((r + ir * r ^ 2) * (1 - r)) * (1 - b) := by ring
    _ = r * (1 - b) := by rw [hA]
    _ = a * (1 - b) + c ^ 2 := hC

/-! ## 2. The reading of a ghost through its block -/

/-- **The ghost reading through the block.**  The reading of a ghost atom in the
four-set metric, multiplied by the block determinant. -/
theorem ghostReading_mul_det (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    {e f h : Fin 6} (he : e ∈ C) (hfh : f ≠ h) (herase : C.erase e = {f, h})
    (hb : sixSetPivot D h h < 1)
    (hdet : (1 - sixSetPivot D f f) * (1 - sixSetPivot D h h)
      - sixSetPivot D f h ^ 2 ≠ 0) :
    D.atom f ⬝ᵥ ((subsetSum D (insert e Cᶜ) - 1)⁻¹ *ᵥ D.atom f)
        * ((1 - sixSetPivot D f f) * (1 - sixSetPivot D h h)
          - sixSetPivot D f h ^ 2)
      = sixSetPivot D f f * (1 - sixSetPivot D h h) + sixSetPivot D f h ^ 2 := by
  classical
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  simp only [sixSetPivot] at hb hdet ⊢
  set W : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D Finset.univ - 1 with hW
  have hcomm : D.atom h ⬝ᵥ (W⁻¹ *ᵥ D.atom f) = D.atom f ⬝ᵥ (W⁻¹ *ᵥ D.atom h) := by
    have hWs : Wᵀ = W := transpose_subsetSum_sub_one D Finset.univ
    exact dot_mulVec_comm (by rw [Matrix.transpose_nonsing_inv, hWs]) _ _
  have hbpos : (0:ℝ) < 1 - D.atom h ⬝ᵥ (W⁻¹ *ᵥ D.atom h) := by linarith
  have hN : (W - Matrix.vecMulVec (D.atom h) (D.atom h)).PosDef :=
    (posDef_sub_vecMulVec_iff W hPD (D.atom h)).mpr hb
  -- the first peel: the reading of `f` after removing `h`
  have h3 : D.atom f ⬝ᵥ ((W - Matrix.vecMulVec (D.atom h) (D.atom h))⁻¹ *ᵥ D.atom f)
      = D.atom f ⬝ᵥ (W⁻¹ *ᵥ D.atom f)
        + (1 - D.atom h ⬝ᵥ (W⁻¹ *ᵥ D.atom h))⁻¹
          * (D.atom f ⬝ᵥ (W⁻¹ *ᵥ D.atom h)) ^ 2 := by
    rw [downdate_reading W hPD (D.atom h) (D.atom f) (ne_of_lt hb), hcomm]
  have h1 : (1 - D.atom h ⬝ᵥ (W⁻¹ *ᵥ D.atom h))⁻¹
      * (1 - D.atom h ⬝ᵥ (W⁻¹ *ᵥ D.atom h)) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hbpos)
  -- the intermediate reading misses one, because the determinant does not vanish
  have hrne : (1 : ℝ)
      - D.atom f ⬝ᵥ ((W - Matrix.vecMulVec (D.atom h) (D.atom h))⁻¹ *ᵥ D.atom f) ≠ 0 := by
    intro hzero
    apply hdet
    have hB : (1 - D.atom f ⬝ᵥ ((W - Matrix.vecMulVec (D.atom h) (D.atom h))⁻¹ *ᵥ D.atom f))
          * (1 - D.atom h ⬝ᵥ (W⁻¹ *ᵥ D.atom h))
        = (1 - D.atom f ⬝ᵥ (W⁻¹ *ᵥ D.atom f))
            * (1 - D.atom h ⬝ᵥ (W⁻¹ *ᵥ D.atom h))
          - (D.atom f ⬝ᵥ (W⁻¹ *ᵥ D.atom h)) ^ 2 := by
      linear_combination (-(1 - D.atom h ⬝ᵥ (W⁻¹ *ᵥ D.atom h))) * h3
        - (D.atom f ⬝ᵥ (W⁻¹ *ᵥ D.atom h)) ^ 2 * h1
    rw [← hB, hzero, zero_mul]
  have h2 : (1 - D.atom f
        ⬝ᵥ ((W - Matrix.vecMulVec (D.atom h) (D.atom h))⁻¹ *ᵥ D.atom f))⁻¹
      * (1 - D.atom f
        ⬝ᵥ ((W - Matrix.vecMulVec (D.atom h) (D.atom h))⁻¹ *ᵥ D.atom f)) = 1 :=
    inv_mul_cancel₀ hrne
  -- the second peel: remove `f` as well, and apply the scalar core
  have hshape : subsetSum D (insert e Cᶜ) - 1
      = (W - Matrix.vecMulVec (D.atom h) (D.atom h))
        - Matrix.vecMulVec (D.atom f) (D.atom f) := by
    rw [fourSetGap_eq_sixSet_downdate D C he hfh herase, hW]
    abel
  rw [hshape, downdate_reading _ hN (D.atom f) (D.atom f) (by
    intro hone
    exact hrne (by rw [hone]; ring))]
  exact ghostReading_scalar h1 h2 h3

/-! ## 3. The polynomial refutation -/

/-- **The weighted ghost deficit refutes the tie.**  If the ghost block is
nondegenerate and the weighted ghost readings fall short of the ghost weight,
the design is not a tie.  Everything is polynomial in the ghost block, and the
six-set gap needs no hypothesis. -/
theorem not_isTie_of_weightedGhostDeficit (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {e f h : Fin 6} (he : e ∈ C)
    (hfh : f ≠ h) (herase : C.erase e = {f, h})
    (ha : sixSetPivot D f f < 1) (hb : sixSetPivot D h h < 1)
    (hdet : 0 < (1 - sixSetPivot D f f) * (1 - sixSetPivot D h h)
      - sixSetPivot D f h ^ 2)
    (hdeficit :
      D.weight f * (sixSetPivot D f f * (1 - sixSetPivot D h h)
          + sixSetPivot D f h ^ 2)
        + D.weight h * (sixSetPivot D h h * (1 - sixSetPivot D f f)
          + sixSetPivot D f h ^ 2)
        < (D.weight f + D.weight h)
          * ((1 - sixSetPivot D f f) * (1 - sixSetPivot D h h)
            - sixSetPivot D f h ^ 2)) :
    ¬ IsTie D := by
  classical
  intro htie
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  -- the four-set gap is positive definite
  have haU : D.atom f ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f) < 1 := by
    simpa only [sixSetPivot] using ha
  have hcrossU : (D.atom f ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom h)) ^ 2
      < (1 - D.atom f ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f))
        * (1 - D.atom h ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom h)) := by
    have hd := hdet
    simp only [sixSetPivot] at hd
    linarith
  have hfour : (subsetSum D (insert e Cᶜ) - 1).PosDef := by
    rw [fourSetGap_eq_sixSet_downdate D C he hfh herase]
    exact (posDef_sub_two_vecMulVec_iff _ hPD (D.atom f) (D.atom h)).mpr
      ⟨haU, hcrossU⟩
  -- the descent forces the weighted readings to reach the ghost weight
  have hforced := tie_forces_ghost_reading D htie C hcard he hfour
  rw [herase, Finset.sum_insert (by simp [hfh]), Finset.sum_singleton,
    Finset.sum_insert (by simp [hfh]), Finset.sum_singleton] at hforced
  -- both readings, multiplied out
  have hxf := ghostReading_mul_det D C he hfh herase hb (ne_of_gt hdet)
  have herase' : C.erase e = {h, f} := by rw [herase, Finset.pair_comm]
  have hdet' : (1 - sixSetPivot D h h) * (1 - sixSetPivot D f f)
      - sixSetPivot D h f ^ 2 ≠ 0 := by
    rw [sixSetPivot_comm D h f]
    intro hzero
    exact (ne_of_gt hdet) (by linear_combination hzero)
  have hxh := ghostReading_mul_det D C he (Ne.symm hfh) herase' ha hdet'
  rw [sixSetPivot_comm D h f] at hxh
  -- multiply the descent by the positive determinant and substitute
  have hmul := mul_le_mul_of_nonneg_right hforced (le_of_lt hdet)
  have hsplit : (D.weight f
        * (D.atom f ⬝ᵥ ((subsetSum D (insert e Cᶜ) - 1)⁻¹ *ᵥ D.atom f))
      + D.weight h
        * (D.atom h ⬝ᵥ ((subsetSum D (insert e Cᶜ) - 1)⁻¹ *ᵥ D.atom h)))
        * ((1 - sixSetPivot D f f) * (1 - sixSetPivot D h h)
          - sixSetPivot D f h ^ 2)
      = D.weight f * (D.atom f ⬝ᵥ ((subsetSum D (insert e Cᶜ) - 1)⁻¹ *ᵥ D.atom f)
          * ((1 - sixSetPivot D f f) * (1 - sixSetPivot D h h)
            - sixSetPivot D f h ^ 2))
        + D.weight h * (D.atom h ⬝ᵥ ((subsetSum D (insert e Cᶜ) - 1)⁻¹ *ᵥ D.atom h)
          * ((1 - sixSetPivot D f f) * (1 - sixSetPivot D h h)
            - sixSetPivot D f h ^ 2)) := by ring
  rw [hsplit, hxf] at hmul
  have hxh' : D.atom h ⬝ᵥ ((subsetSum D (insert e Cᶜ) - 1)⁻¹ *ᵥ D.atom h)
        * ((1 - sixSetPivot D f f) * (1 - sixSetPivot D h h)
          - sixSetPivot D f h ^ 2)
      = sixSetPivot D h h * (1 - sixSetPivot D f f) + sixSetPivot D f h ^ 2 := by
    rw [← hxh]
    ring
  rw [hxh'] at hmul
  linarith [hmul, hdeficit]

end Gtz

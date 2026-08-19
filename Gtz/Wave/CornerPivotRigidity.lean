import Gtz.Wave.GhostRowBound
import Gtz.Wave.CorankTwoDeficitArm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The outside pivot block of a corank-two corner is a rank-one deflation of the
identity, and at a tie at most one selector is short

At a corank-two corner the six-set gap splits as `W = lam • u uᵀ + S_out`.  The
landed corner laws read only the DIAGONAL of the outside pivot block: every
outside pivot is capped by one (`Gtz.outside_pivot_le_one`) and the outside
pivots sum to `3 − π_u` (`Gtz.outside_pivot_sum`), with
`π_u := lam · uᵀW⁻¹u`.  This module prices the WHOLE block, and finds it
completely rigid:

  `E · (δ_{dd'} − P_{dd'}) = π_u · η_d η_{d'}` ,  `E := Σ_{d∉C} η_d²` ,

with `η_a := uᵀW⁻¹g_a` the cross reading of an atom against the gap direction
(`Gtz.outsideDefect_eq_zero`).  In words: `1 − P_DD` is `π_u` times the rank-one
projector on `η`.  Both landed laws are corollaries — the diagonal reads
`E(1 − P_dd) = π_u η_d² ≥ 0`, and its sum over the complement is the trace law.
The new content is the OFF-DIAGONAL rigidity
(`Gtz.outsidePivot_minor_vanishes`)

  `E² · [ (1 − P_dd)(1 − P_{d'd'}) − P_{dd'}² ] = 0` ,

which says every two-by-two minor of `1 − P_DD` vanishes.

## Why the proof is a `(6,3)` proof

Three facts feed it, and all three come from the polarized outside row mass
(`Gtz.outside_cross_row_mass`), which generalises `Gtz.outside_row_mass` from
one probe vector to two:

* `Σ_{k∉C} P_{ak}P_{kb} = P_{ab} − lam η_aη_b` — the cross-block law;
* `Σ_{k∉C} P_{ak}η_k = (1 − π_u)·η_a` — the gap direction is an eigenvector of
  the outside block;
* `lam · E = π_u(1 − π_u)` — the `u`-instance.

Write `M_{dd'} := E(δ_{dd'} − P_{dd'}) − π_u η_dη_{d'}`.  The three facts give
`M² = E·M` and `M` is symmetric, and the trace law gives `tr M = 0`.  Then
`Σ_{d,k} M_{dk}² = tr(M²) = E·tr M = 0`, so `M` vanishes entry by entry.  The
TRACE step is where the size enters: `tr M = E(|Cᶜ| − 3 + π_u) − π_u E`, which
vanishes only when the complement has three atoms.  Nothing here can be stated
at `(5,3)`, where the complement of a triple is a pair.

## At a tie at most one selector is short

The swap at the inside atom `x` against the ghost `y` is
`S_out − 1 + g_x g_xᵀ − g_y g_yᵀ` (`Gtz.swap_eq_sixSet_downdate`), so the swap at
`(x,y)` and the swap at `(y,x)` SUM to `2(S_out − 1)`.  A short ghost block at
the selector `e` makes the swaps at `(e,f)` and `(e,h)` positive definite, and a
short block at the selector `f` makes the swaps at `(f,e)` and `(f,h)` positive
definite.  The pair `(e,f)`, `(f,e)` then forces `S_out − 1 ≻ 0`, so the
complement triple strictly dominates and the design is not a tie
(`Gtz.not_ghostBlockShort_two_selectors`).

So at a `(6,3)` tie the corank-two corner admits AT MOST ONE short selector,
while `Gtz.NonplanarDeficitResidual` asks for at least one.  The residual is
therefore an exact-one statement, and the selector it names is unique.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The polarized outside row mass -/

/-- **The outside row mass, polarized.**  For two probe vectors the outside
readings pair to the probe pairing less `lam` times the product of the two
`u`-cross readings.  `Gtz.outside_row_mass` is the diagonal case. -/
theorem outside_cross_row_mass (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (y z : Fin 3 → ℝ) :
    ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ y))
        * (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ z))
      = y ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ z)
        - lam * ((u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ y))
          * (u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ z))) := by
  classical
  set W : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D Finset.univ - 1 with hW
  have hWsymm : Wᵀ = W := transpose_subsetSum_sub_one D Finset.univ
  have hWinvsymm : (W⁻¹)ᵀ = W⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hWsymm]
  have hunit : IsUnit W.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  set a : Fin 3 → ℝ := W⁻¹ *ᵥ y with ha
  set b : Fin 3 → ℝ := W⁻¹ *ᵥ z with hb
  have hterm : ∀ d : Fin m,
      (D.atom d ⬝ᵥ a) * (D.atom d ⬝ᵥ b) = a ⬝ᵥ (atomMatrix (D.atom d) *ᵥ b) := by
    intro d
    rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm a (D.atom d)]
    ring
  have hsum : ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ a) * (D.atom d ⬝ᵥ b)
      = a ⬝ᵥ (subsetSum D Cᶜ *ᵥ b) := by
    rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun d _ => hterm d
  have hout : subsetSum D Cᶜ = W - lam • atomMatrix u := by
    rw [hW, sixSetGap_eq_gapAtom_add_outside D C hgap]
    abel
  have hWb : W *ᵥ b = z := by
    rw [hb, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hunit, Matrix.one_mulVec]
  rw [hsum, hout, Matrix.sub_mulVec, dotProduct_sub, hWb, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, atomMatrix, vecMulVec_mulVec_eq,
    dotProduct_smul, smul_eq_mul]
  have haz : a ⬝ᵥ z = y ⬝ᵥ (W⁻¹ *ᵥ z) := by
    rw [ha, dotProduct_comm]
    exact dot_mulVec_comm hWinvsymm _ _
  have hau : a ⬝ᵥ u = u ⬝ᵥ (W⁻¹ *ᵥ y) := by
    rw [ha, dotProduct_comm]
  have hub : u ⬝ᵥ b = u ⬝ᵥ (W⁻¹ *ᵥ z) := by rw [hb]
  rw [haz, hau, hub]
  ring

/-! ## 2. The cross readings of the corner -/

/-- The cross reading of an atom against the gap direction, `η_a = uᵀW⁻¹g_a`. -/
noncomputable def gapCross (D : WeightedDesign m 3) (u : Fin 3 → ℝ) (a : Fin m) : ℝ :=
  u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom a)

/-- The self reading of the gap direction, `uᵀW⁻¹u`.  The corner pivot is
`π_u = lam` times this. -/
noncomputable def gapSelf (D : WeightedDesign m 3) (u : Fin 3 → ℝ) : ℝ :=
  u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ u)

/-- The mass of the outside cross readings, `E = Σ_{d∉C} η_d²`. -/
noncomputable def gapCrossMass (D : WeightedDesign m 3) (C : Finset (Fin m))
    (u : Fin 3 → ℝ) : ℝ :=
  ∑ k ∈ Cᶜ, gapCross D u k ^ 2

/-- The corner pivot `π_u = lam · uᵀW⁻¹u`. -/
noncomputable def cornerPivot (D : WeightedDesign m 3) (lam : ℝ) (u : Fin 3 → ℝ) : ℝ :=
  lam * gapSelf D u

/-- **The cross-block law.**  The outside pivots compose to the pivot less the
spike: `Σ_{k∉C} P_{ak}P_{kb} = P_{ab} − lam η_aη_b`. -/
theorem outside_pivot_compose (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (a b : Fin m) :
    ∑ k ∈ Cᶜ, sixSetPivot D a k * sixSetPivot D k b
      = sixSetPivot D a b - lam * (gapCross D u a * gapCross D u b) := by
  have h := outside_cross_row_mass D C hgap hPD (D.atom a) (D.atom b)
  have hsymm : ∀ k : Fin m, D.atom k ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom a)
      = sixSetPivot D a k := fun k => (sixSetPivot_comm D a k) ▸ rfl
  simp only [hsymm] at h
  simpa only [sixSetPivot, gapCross] using h

/-- **The gap direction is an eigenvector of the outside block.**
`Σ_{k∉C} P_{ak}η_k = (1 − π_u)·η_a`. -/
theorem outside_pivot_eigen (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (a : Fin m) :
    ∑ k ∈ Cᶜ, sixSetPivot D a k * gapCross D u k
      = (1 - cornerPivot D lam u) * gapCross D u a := by
  have h := outside_cross_row_mass D C hgap hPD (D.atom a) u
  have hsymm : ∀ k : Fin m, D.atom k ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom a)
      = sixSetPivot D a k := fun k => (sixSetPivot_comm D a k) ▸ rfl
  have hcross : ∀ k : Fin m, D.atom k ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ u)
      = gapCross D u k := by
    intro k
    have hWsymm : (subsetSum D Finset.univ - 1)ᵀ = subsetSum D Finset.univ - 1 :=
      transpose_subsetSum_sub_one D Finset.univ
    have hWinvsymm : ((subsetSum D Finset.univ - 1)⁻¹)ᵀ
        = (subsetSum D Finset.univ - 1)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hWsymm]
    rw [gapCross]
    exact dot_mulVec_comm hWinvsymm _ _
  simp only [hsymm, hcross] at h
  rw [h]
  simp only [gapCross, gapSelf, cornerPivot]
  ring

/-- **The mass of the cross readings.**  `lam·Σ_{d∉C} η_d² = π_u(1 − π_u)`. -/
theorem outside_gapCross_mass (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    ∑ d ∈ Cᶜ, gapCross D u d ^ 2 = gapSelf D u - lam * gapSelf D u ^ 2 := by
  have h := outside_cross_row_mass D C hgap hPD u u
  have hcross : ∀ k : Fin m, D.atom k ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ u)
      = gapCross D u k := by
    intro k
    have hWsymm : (subsetSum D Finset.univ - 1)ᵀ = subsetSum D Finset.univ - 1 :=
      transpose_subsetSum_sub_one D Finset.univ
    have hWinvsymm : ((subsetSum D Finset.univ - 1)⁻¹)ᵀ
        = (subsetSum D Finset.univ - 1)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hWsymm]
    rw [gapCross]
    exact dot_mulVec_comm hWinvsymm _ _
  simp only [hcross] at h
  rw [show ∑ d ∈ Cᶜ, gapCross D u d ^ 2
      = ∑ d ∈ Cᶜ, gapCross D u d * gapCross D u d from
    Finset.sum_congr rfl fun d _ => sq (gapCross D u d) ▸ by ring, h]
  simp only [gapSelf]
  ring

/-! ## 3. The rank-one rigidity of the outside pivot block -/

/-- **The mass law, in corner form.**  `lam·E = π_u(1 − π_u)`. -/
theorem lam_mul_gapCrossMass (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    lam * gapCrossMass D C u = cornerPivot D lam u - cornerPivot D lam u ^ 2 := by
  rw [gapCrossMass, outside_gapCross_mass D C hgap hPD, cornerPivot]
  ring

/-- The defect of the outside pivot block against its rank-one form. -/
noncomputable def outsideDefect (D : WeightedDesign m 3) (C : Finset (Fin m))
    (lam : ℝ) (u : Fin 3 → ℝ) (d d' : Fin m) : ℝ :=
  gapCrossMass D C u * ((if d = d' then (1 : ℝ) else 0) - sixSetPivot D d d')
    - cornerPivot D lam u * (gapCross D u d * gapCross D u d')

/-- The defect is symmetric. -/
theorem outsideDefect_comm (D : WeightedDesign m 3) (C : Finset (Fin m))
    (lam : ℝ) (u : Fin 3 → ℝ) (d d' : Fin m) :
    outsideDefect D C lam u d d' = outsideDefect D C lam u d' d := by
  rw [outsideDefect, outsideDefect, sixSetPivot_comm D d d']
  by_cases h : d = d'
  · subst h; ring
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

/-- **The defect composes.**  `M² = E·M` on the complement. -/
theorem outsideDefect_compose (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    {d d' : Fin m} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) :
    ∑ k ∈ Cᶜ, outsideDefect D C lam u d k * outsideDefect D C lam u k d'
      = gapCrossMass D C u * outsideDefect D C lam u d d' := by
  classical
  have hcomp := outside_pivot_compose D C hgap hPD d d'
  have heig1 := outside_pivot_eigen D C hgap hPD d
  have heig2 := outside_pivot_eigen D C hgap hPD d'
  have hlamE := lam_mul_gapCrossMass D C hgap hPD
  have hEdef : gapCrossMass D C u = ∑ k ∈ Cᶜ, gapCross D u k ^ 2 := rfl
  have hPidef : cornerPivot D lam u = lam * gapSelf D u := rfl
  -- the five basic sums over the complement
  have hd1 : ∑ k ∈ Cᶜ, (if d = k then (1:ℝ) else 0) * sixSetPivot D k d'
      = sixSetPivot D d d' := by
    simp [ite_mul, Finset.sum_ite_eq, hd]
  have hd2 : ∑ k ∈ Cᶜ, sixSetPivot D d k * (if k = d' then (1:ℝ) else 0)
      = sixSetPivot D d d' := by
    simp [mul_ite, Finset.sum_ite_eq', hd']
  have hd3 : ∑ k ∈ Cᶜ, (if d = k then (1:ℝ) else 0) * (if k = d' then (1:ℝ) else 0)
      = if d = d' then (1:ℝ) else 0 := by
    by_cases hdd : d = d'
    · subst hdd
      simp [ite_mul, Finset.sum_ite_eq, hd]
    · rw [if_neg hdd]
      simp [ite_mul, Finset.sum_ite_eq, hd, hdd]
  have hd4 : ∑ k ∈ Cᶜ, (if d = k then (1:ℝ) else 0) * gapCross D u k = gapCross D u d := by
    simp [ite_mul, Finset.sum_ite_eq, hd]
  have hd5 : ∑ k ∈ Cᶜ, gapCross D u k * (if k = d' then (1:ℝ) else 0) = gapCross D u d' := by
    simp [mul_ite, Finset.sum_ite_eq', hd']
  have hd6 : ∑ k ∈ Cᶜ, gapCross D u k * sixSetPivot D k d'
      = (1 - cornerPivot D lam u) * gapCross D u d' := by
    rw [← heig2]
    exact Finset.sum_congr rfl fun k _ => by rw [sixSetPivot_comm D k d']; ring
  have hd7 : ∑ k ∈ Cᶜ, sixSetPivot D d k * gapCross D u k
      = (1 - cornerPivot D lam u) * gapCross D u d := heig1
  have hd8 : ∑ k ∈ Cᶜ, gapCross D u k ^ 2 = gapCrossMass D C u := rfl
  -- expand the product of two defects term by term
  have hexpand : ∑ k ∈ Cᶜ, outsideDefect D C lam u d k * outsideDefect D C lam u k d'
      = gapCrossMass D C u ^ 2
          * (∑ k ∈ Cᶜ, (if d = k then (1:ℝ) else 0) * (if k = d' then (1:ℝ) else 0))
        - gapCrossMass D C u ^ 2
          * (∑ k ∈ Cᶜ, (if d = k then (1:ℝ) else 0) * sixSetPivot D k d')
        - gapCrossMass D C u ^ 2
          * (∑ k ∈ Cᶜ, sixSetPivot D d k * (if k = d' then (1:ℝ) else 0))
        + gapCrossMass D C u ^ 2 * (∑ k ∈ Cᶜ, sixSetPivot D d k * sixSetPivot D k d')
        - gapCrossMass D C u * cornerPivot D lam u * gapCross D u d'
          * (∑ k ∈ Cᶜ, (if d = k then (1:ℝ) else 0) * gapCross D u k)
        + gapCrossMass D C u * cornerPivot D lam u * gapCross D u d'
          * (∑ k ∈ Cᶜ, sixSetPivot D d k * gapCross D u k)
        - gapCrossMass D C u * cornerPivot D lam u * gapCross D u d
          * (∑ k ∈ Cᶜ, gapCross D u k * (if k = d' then (1:ℝ) else 0))
        + gapCrossMass D C u * cornerPivot D lam u * gapCross D u d
          * (∑ k ∈ Cᶜ, gapCross D u k * sixSetPivot D k d')
        + cornerPivot D lam u ^ 2 * gapCross D u d * gapCross D u d'
          * (∑ k ∈ Cᶜ, gapCross D u k ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [outsideDefect, outsideDefect]; ring
  rw [hexpand, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hcomp, outsideDefect]
  linear_combination (-(gapCrossMass D C u * gapCross D u d * gapCross D u d')) * hlamE

/-- **The trace of the defect vanishes.**  This step needs the complement to
have three atoms, so it is a `(6,3)` step. -/
theorem outsideDefect_trace (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    ∑ d ∈ Cᶜ, outsideDefect D C lam u d d = 0 := by
  classical
  have hcompl : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, hcard]
    simp
  have hpiv : ∑ d ∈ Cᶜ, sixSetPivot D d d = 3 - cornerPivot D lam u := by
    simpa only [sixSetPivot, gapSelf, cornerPivot] using outside_pivot_sum D C hgap hPD
  have hterm : ∀ d ∈ Cᶜ, outsideDefect D C lam u d d
      = gapCrossMass D C u - gapCrossMass D C u * sixSetPivot D d d
        - cornerPivot D lam u * gapCross D u d ^ 2 := by
    intro d _
    rw [outsideDefect, if_pos rfl]
    ring
  calc ∑ d ∈ Cᶜ, outsideDefect D C lam u d d
      = ∑ d ∈ Cᶜ, (gapCrossMass D C u - gapCrossMass D C u * sixSetPivot D d d
          - cornerPivot D lam u * gapCross D u d ^ 2) := Finset.sum_congr rfl hterm
    _ = ((Cᶜ : Finset (Fin 6)).card : ℝ) * gapCrossMass D C u
        - gapCrossMass D C u * (∑ d ∈ Cᶜ, sixSetPivot D d d)
        - cornerPivot D lam u * (∑ d ∈ Cᶜ, gapCross D u d ^ 2) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ = 0 := by
        rw [hcompl, hpiv, show ∑ d ∈ Cᶜ, gapCross D u d ^ 2 = gapCrossMass D C u from rfl]
        push_cast
        ring

/-- **The outside pivot block is a rank-one deflation of the identity.**  Every
entry of the defect vanishes. -/
theorem outsideDefect_eq_zero (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    {d d' : Fin 6} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) :
    outsideDefect D C lam u d d' = 0 := by
  classical
  have hrow : ∀ a ∈ Cᶜ, ∑ b ∈ Cᶜ, outsideDefect D C lam u a b ^ 2
      = gapCrossMass D C u * outsideDefect D C lam u a a := by
    intro a ha
    rw [← outsideDefect_compose D C hgap hPD ha ha]
    exact Finset.sum_congr rfl fun b _ => by
      rw [show outsideDefect D C lam u b a = outsideDefect D C lam u a b from
        outsideDefect_comm D C lam u b a]
      ring
  have hkey : ∑ a ∈ Cᶜ, ∑ b ∈ Cᶜ, outsideDefect D C lam u a b ^ 2 = 0 := by
    rw [Finset.sum_congr rfl hrow, ← Finset.mul_sum,
      outsideDefect_trace D C hcard hgap hPD, mul_zero]
  have hnn : ∀ a ∈ Cᶜ, (0:ℝ) ≤ ∑ b ∈ Cᶜ, outsideDefect D C lam u a b ^ 2 :=
    fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hrowzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hkey d hd
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg
    (fun b (_ : b ∈ Cᶜ) => sq_nonneg (outsideDefect D C lam u d b))).mp hrowzero d' hd'
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hentry

/-- **The diagonal rigidity.**  `E·(1 − P_dd) = π_u·η_d²`.  It sharpens
`Gtz.outside_pivot_le_one` from an inequality to an identity. -/
theorem outsidePivot_diag_rankOne (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    {d : Fin 6} (hd : d ∈ Cᶜ) :
    gapCrossMass D C u * (1 - sixSetPivot D d d)
      = cornerPivot D lam u * gapCross D u d ^ 2 := by
  have h := outsideDefect_eq_zero D C hcard hgap hPD hd hd
  rw [outsideDefect, if_pos rfl] at h
  linear_combination h

/-- **The off-diagonal rigidity.**  `E·P_{dd'} = −π_u·η_dη_{d'}` for distinct
outside atoms.  Nothing in the landed corner laws sees this. -/
theorem outsidePivot_offDiag_rankOne (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    {d d' : Fin 6} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (hne : d ≠ d') :
    gapCrossMass D C u * sixSetPivot D d d'
      = -(cornerPivot D lam u * (gapCross D u d * gapCross D u d')) := by
  have h := outsideDefect_eq_zero D C hcard hgap hPD hd hd'
  rw [outsideDefect, if_neg hne] at h
  linear_combination -h

/-- **Every two-by-two minor of `1 − P_DD` vanishes.**  The outside pivot block
of a corank-two corner is the identity minus a rank one. -/
theorem outsidePivot_minor_vanishes (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    {d d' : Fin 6} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (hne : d ≠ d') :
    gapCrossMass D C u ^ 2
        * ((1 - sixSetPivot D d d) * (1 - sixSetPivot D d' d')
          - sixSetPivot D d d' ^ 2) = 0 := by
  have hdiag := outsidePivot_diag_rankOne D C hcard hgap hPD hd
  have hdiag' := outsidePivot_diag_rankOne D C hcard hgap hPD hd'
  have hoff := outsidePivot_offDiag_rankOne D C hcard hgap hPD hd hd' hne
  linear_combination (gapCrossMass D C u * (1 - sixSetPivot D d' d')) * hdiag
    + (cornerPivot D lam u * gapCross D u d ^ 2) * hdiag'
    - (gapCrossMass D C u * sixSetPivot D d d'
      - cornerPivot D lam u * (gapCross D u d * gapCross D u d')) * hoff

/-- **The rank-one rigidity, with no proviso.**  `Gtz.sixSetGap_posDef` makes the
positive definiteness of the six-set gap automatic at every `(6,3)` design. -/
theorem outsidePivot_minor_vanishes' (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {d d' : Fin 6} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (hne : d ≠ d') :
    gapCrossMass D C u ^ 2
        * ((1 - sixSetPivot D d d) * (1 - sixSetPivot D d' d')
          - sixSetPivot D d d' ^ 2) = 0 :=
  outsidePivot_minor_vanishes D C hcard hgap (sixSetGap_posDef_sixThree D) hd hd' hne

/-- **The diagonal rigidity, with no proviso.** -/
theorem outsidePivot_diag_rankOne' (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) {d : Fin 6} (hd : d ∈ Cᶜ) :
    gapCrossMass D C u * (1 - sixSetPivot D d d)
      = cornerPivot D lam u * gapCross D u d ^ 2 :=
  outsidePivot_diag_rankOne D C hcard hgap (sixSetGap_posDef_sixThree D) hd

/-! ## 4. At a tie at most one selector carries a short ghost block -/

/-- **The two swaps of an ordered inside pair sum to twice the complement gap.**
The inside contributions cancel. -/
theorem swap_add_swap_eq_two_smul (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    {e f : Fin 6} (he : e ∈ C) (hf : f ∈ C) :
    ((subsetSum D (insert e Cᶜ) - 1) - Matrix.vecMulVec (D.atom f) (D.atom f))
        + ((subsetSum D (insert f Cᶜ) - 1) - Matrix.vecMulVec (D.atom e) (D.atom e))
      = (2 : ℝ) • (subsetSum D Cᶜ - 1) := by
  classical
  have hmem : ∀ {c : Fin 6}, c ∈ C → c ∉ Cᶜ := fun hc => by
    simpa using hc
  have hins : ∀ {c : Fin 6}, c ∈ C →
      subsetSum D (insert c Cᶜ) = atomMatrix (D.atom c) + subsetSum D Cᶜ := by
    intro c hc
    rw [subsetSum, Finset.sum_insert (hmem hc), subsetSum]
  rw [hins he, hins hf, show atomMatrix (D.atom e) = Matrix.vecMulVec (D.atom e) (D.atom e)
      from rfl,
    show atomMatrix (D.atom f) = Matrix.vecMulVec (D.atom f) (D.atom f) from rfl,
    two_smul]
  abel

/-- **At a tie two selectors cannot both be short.**  A short ghost block at the
inside atom `e` and a short ghost block at the inside atom `f` make the swaps at
`(e,f)` and `(f,e)` positive definite, so the complement triple would strictly
dominate. -/
theorem not_ghostBlockShort_two_selectors (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {e f h : Fin 6}
    (he : e ∈ C) (hf : f ∈ C) (hfh : f ≠ h) (heh : e ≠ h)
    (heraseE : C.erase e = {f, h}) (heraseF : C.erase f = {e, h})
    (hshortE : GhostBlockShort D f h) (hshortF : GhostBlockShort D e h) : False := by
  classical
  -- the two swaps of the ordered pair `(e,f)` sum to twice the complement gap
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hswapE := (swapPD_iff_ghostBlock D C he hfh heraseE hPD).mpr
    ⟨hshortE.1, hshortE.2.2.1⟩
  have hswapF := (swapPD_iff_ghostBlock D C hf heh heraseF hPD).mpr
    ⟨hshortF.1, hshortF.2.2.1⟩
  have hsum : ((2 : ℝ) • (subsetSum D Cᶜ - 1)).PosDef := by
    rw [← swap_add_swap_eq_two_smul D C he hf]
    exact hswapE.add hswapF
  have hhalf : (subsetSum D Cᶜ - 1).PosDef := by
    have : ((2 : ℝ)⁻¹ • ((2 : ℝ) • (subsetSum D Cᶜ - 1))).PosDef :=
      hsum.smul (by norm_num)
    rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_smul] at this
  have hcompl : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, hcard]
    simp
  exact htie.2 Cᶜ hcompl hhalf

end Gtz

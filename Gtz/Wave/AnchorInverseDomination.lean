import Gtz.Wave.OutsideTriadDeterminant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# Inverse domination: the anchor's inverse gap is capped by an explicit matrix

The anchor caps of `Gtz.Wave.OneAxisZeroAnchorCaps` bound two readings of
`B⁻¹`.  This module bounds them ALL: quadratic-form domination inverts
(`Gtz.quadForm_inv_le_of_loewner`) — if `C ⪯ A` with `C` positive definite,
every reading of `A⁻¹` sits below the same reading of `C⁻¹` — and the `Z1`
anchor dominates the explicit matrix
(`Gtz.corner_oneAxisZero_anchor_capMatrix_floor`)

  `B  ⪰  lam • u uᵀ + (1/ms) • N_out − g_x g_xᵀ`,

whose three pieces are the gap axis, the weighted outside mass paid at the
weight cap, and the erased atom.  When the cap matrix is positive definite,
every anchor reading — in particular the two inside readings `R_yy`, `R_zz`
that the tie's pair floors push UP — is capped by an explicit inverse
(`Gtz.corner_oneAxisZero_anchor_reading_cap`).  This is the missing upper
side of the anchor tension: the trace pinch forces
`(1 − t_y)R_yy` large at a heavy-inside tie, and the reading cap holds it
down by frame-and-weight data alone.

Measured: on 2·10⁵ fresh heavy-inside samples the tension inequality of
`Gtz.corner_oneAxisZero_anchor_tension` already fails at 76.5% of the cell
with the exact readings; the reading caps turn the remaining tension into a
closed-form criterion in the frame scalars, whose coverage the next round
must map before the cell can close.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Quadratic-form domination inverts -/

/-- **INVERSE DOMINATION.**  If the positive definite form `C` sits below `A`
pointwise, every reading of `A⁻¹` sits below the same reading of `C⁻¹`:
Cauchy–Schwarz in the `C⁻¹` metric at the probe `C · A⁻¹ g`. -/
theorem quadForm_inv_le_of_loewner {k : ℕ}
    {A C : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosDef) (hC : C.PosDef)
    (hAC : ∀ v : Fin k → ℝ, v ⬝ᵥ (C *ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) (g : Fin k → ℝ) :
    g ⬝ᵥ (A⁻¹ *ᵥ g) ≤ g ⬝ᵥ (C⁻¹ *ᵥ g) := by
  have hdetA : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hdetC : IsUnit C.det := isUnit_iff_ne_zero.mpr (ne_of_gt hC.det_pos)
  set w : Fin k → ℝ := A⁻¹ *ᵥ g with hw
  set t : ℝ := g ⬝ᵥ (A⁻¹ *ᵥ g) with ht
  set s : ℝ := g ⬝ᵥ (C⁻¹ *ᵥ g) with hs
  have ht0 : 0 ≤ t := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
      hA.inv.posSemidef).2 g
    rwa [star_trivial] at h
  have hs0 : 0 ≤ s := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
      hC.inv.posSemidef).2 g
    rwa [star_trivial] at h
  -- the A-energy of the probe is the reading itself
  have hAw : A *ᵥ w = g := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdetA,
      Matrix.one_mulVec]
  have hwAw : w ⬝ᵥ (A *ᵥ w) = t := by
    rw [hAw, ht, hw, dotProduct_comm]
  -- Cauchy–Schwarz in the C⁻¹ metric between g and C·w
  have hCS := psd_form_cross_sq_le hC.inv.posSemidef g (C *ᵥ w)
  have hCinvC : C⁻¹ *ᵥ (C *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul C hdetC,
      Matrix.one_mulVec]
  rw [hCinvC] at hCS
  have hgw : g ⬝ᵥ w = t := by
    rw [ht, hw]
  have hCw : (C *ᵥ w) ⬝ᵥ w = w ⬝ᵥ (C *ᵥ w) := dotProduct_comm _ _
  rw [hgw, hCw, ← hs] at hCS
  -- close: t² ≤ s · (wCw) ≤ s · t
  have hchain : t ^ 2 ≤ s * t := by
    have hwCA : w ⬝ᵥ (C *ᵥ w) ≤ t := by
      rw [← hwAw]
      exact hAC w
    have hCw0 : 0 ≤ w ⬝ᵥ (C *ᵥ w) := by
      have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
        hC.posSemidef).2 w
      rwa [star_trivial] at h
    nlinarith [hCS, hwCA, hs0]
  nlinarith [hchain, ht0, hs0]

/-! ## 2. The anchor dominates the explicit cap matrix -/

/-- **THE FULL LOEWNER FLOOR OF THE ANCHOR.**  The anchor gap dominates the
axis boost plus the ms-paid weighted outside mass minus the erased atom, read
at every direction: the frame pair pays the two inside atoms exactly, and
every outside atom pays at least its own weighted share of the cap. -/
theorem corner_oneAxisZero_anchor_capMatrix_floor (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d ≤ ms)
    (v : Fin 3 → ℝ) :
    v ⬝ᵥ ((lam • atomMatrix u
        + (1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
            D.weight d • atomMatrix (D.atom d)
        - atomMatrix (D.atom x)) *ᵥ v)
      ≤ v ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1) *ᵥ v) := by
  classical
  obtain ⟨w, hwunit, hwu, hwx, hframe⟩ :=
    corner_oneAxisZero_frame_pair D hxy hxz hyz hlam hunit hgap hax haz
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  -- the anchor quadratic form in frame coordinates
  have hquad := quadForm_subsetSum_sub_one D ((univ : Finset (Fin m)).erase x) v
  have hframe_read : (D.atom y ⬝ᵥ v) ^ 2 + (D.atom z ⬝ᵥ v) ^ 2
      = (1 + lam) * (u ⬝ᵥ v) ^ 2 + (w ⬝ᵥ v) ^ 2 := by
    have hread := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => v ⬝ᵥ (M *ᵥ v)) hframe
    simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul] at hread
    rw [show atomMatrix (D.atom y) = Matrix.vecMulVec (D.atom y) (D.atom y) from rfl,
      show atomMatrix (D.atom z) = Matrix.vecMulVec (D.atom z) (D.atom z) from rfl,
      show atomMatrix u = Matrix.vecMulVec u u from rfl,
      show atomMatrix w = Matrix.vecMulVec w w from rfl,
      quadForm_atomMatrix, quadForm_atomMatrix, quadForm_atomMatrix,
      quadForm_atomMatrix] at hread
    exact hread
  have hsum_read : ∑ a ∈ (univ : Finset (Fin m)).erase x, (D.atom a ⬝ᵥ v) ^ 2
      = (D.atom y ⬝ᵥ v) ^ 2 + (D.atom z ⬝ᵥ v) ^ 2
        + ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 := by
    have hyC : y ∉ insert z (({x, y, z} : Finset (Fin m))ᶜ) := by
      simp [hyz]
    have hzC : z ∉ (({x, y, z} : Finset (Fin m))ᶜ) := by simp
    rw [erase_eq_insert_insert_compl hxy hxz hyz, Finset.sum_insert hyC,
      Finset.sum_insert hzC]
    try ring
  have hxu : u ⬝ᵥ D.atom x = 0 := by rw [dotProduct_comm]; exact hax
  have hwx' : w ⬝ᵥ D.atom x = 0 := by rw [dotProduct_comm]; exact hwx
  have hres := read_sq_orthonormal_resolution hunit hwunit hlev hwu hxu hwx' v
  have hBform : v ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1) *ᵥ v)
      = lam * (u ⬝ᵥ v) ^ 2 - (D.atom x ⬝ᵥ v) ^ 2
        + ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 := by
    rw [hquad, hsum_read, hframe_read]
    have hvv : v ⬝ᵥ v = (u ⬝ᵥ v) ^ 2 + (w ⬝ᵥ v) ^ 2 + (D.atom x ⬝ᵥ v) ^ 2 :=
      hres.symm
    rw [hvv]
    ring
  -- the cap-matrix quadratic form
  have hcapform : v ⬝ᵥ ((lam • atomMatrix u
        + (1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
            D.weight d • atomMatrix (D.atom d)
        - atomMatrix (D.atom x)) *ᵥ v)
      = lam * (u ⬝ᵥ v) ^ 2
        + (1 / ms) * ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
            D.weight d * (D.atom d ⬝ᵥ v) ^ 2
        - (D.atom x ⬝ᵥ v) ^ 2 := by
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
      Matrix.smul_mulVec, dotProduct_smul, Matrix.smul_mulVec, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [show atomMatrix u = Matrix.vecMulVec u u from rfl,
      show atomMatrix (D.atom x) = Matrix.vecMulVec (D.atom x) (D.atom x) from rfl,
      quadForm_atomMatrix, quadForm_atomMatrix, Matrix.sum_mulVec, dotProduct_sum]
    have hterm : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        v ⬝ᵥ ((D.weight d • atomMatrix (D.atom d)) *ᵥ v)
          = D.weight d * (D.atom d ⬝ᵥ v) ^ 2 := by
      intro d _
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d) from rfl,
        quadForm_atomMatrix]
    rw [Finset.sum_congr rfl hterm]
  -- pay each outside atom by the cap
  have hpay : (1 / ms) * ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (D.atom d ⬝ᵥ v) ^ 2
      ≤ ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have h1 : D.weight d * (D.atom d ⬝ᵥ v) ^ 2 ≤ ms * (D.atom d ⬝ᵥ v) ^ 2 :=
      mul_le_mul_of_nonneg_right (hmd d hd) (sq_nonneg _)
    calc (1 / ms) * (D.weight d * (D.atom d ⬝ᵥ v) ^ 2)
        ≤ (1 / ms) * (ms * (D.atom d ⬝ᵥ v) ^ 2) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (D.atom d ⬝ᵥ v) ^ 2 := by
          field_simp
  rw [hBform, hcapform]
  linarith

/-! ## 3. Every anchor reading is capped -/

/-- **THE ANCHOR READING CAP.**  When the cap matrix is positive definite,
every reading of the anchor's inverse gap — member or not — is bounded by the
same reading of the explicit cap inverse.  The tie-side pair floors push the
inside readings up; this cap holds every one of them down with frame and
weight data alone. -/
theorem corner_oneAxisZero_anchor_reading_cap (D : WeightedDesign m 3)
    (hm : 3 ≤ m) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d ≤ ms)
    (hcap : (lam • atomMatrix u
        + (1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
            D.weight d • atomMatrix (D.atom d)
        - atomMatrix (D.atom x)).PosDef)
    (g : Fin 3 → ℝ) :
    g ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹ *ᵥ g)
      ≤ g ⬝ᵥ ((lam • atomMatrix u
          + (1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
              D.weight d • atomMatrix (D.atom d)
          - atomMatrix (D.atom x))⁻¹ *ᵥ g) := by
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  have hPD : (subsetSum D ((univ : Finset (Fin m)).erase x) - 1).PosDef :=
    complement_erase_posDef_of_leverage_le_one D hm hlev.le
  exact quadForm_inv_le_of_loewner hPD hcap
    (corner_oneAxisZero_anchor_capMatrix_floor D hxy hxz hyz hlam hunit hgap
      hax haz hms hmd) g

end Gtz

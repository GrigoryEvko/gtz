import Gtz.Wave.AnchorInverseDomination
import Gtz.Design.CapSlack
import Gtz.LinAlg.PlaneSpread

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The heavy-inside cap gap: the paid four-set is positive definite, the
# excluded readings are capped, and the cap gap empties the cell

The heavy-inside cell of the `Z1` stratum is the joint state: `Z1` proper
corner, the four-set through `z` fails, the four-set through `y` dominates.
Its tie content is three outside floors at `A_y⁻¹`
(`Gtz.corner_oneAxisZero_heavyInside_isTie_iff`), and through the ledger the
floors force the EXCLUDED pair `{x, z}` to read `A_y⁻¹` at least at one on
weighted average (`Gtz.tie_fourSet_excluded_floor`).  This module proves the
other side of that fight: in the heavy-inside cell the excluded readings are
CAPPED by explicit closed forms, tie-free, and when the caps undercut the
weighted average the cell is empty.

## The paid four-set

The engine is a strengthening of the four-set dichotomy.  The dichotomy
(`Gtz.corner_oneAxisZero_fourSet_split`) proves `A_y ≻ 0` when `A_z` fails; the
same scalar core in fact forces the PAID form positive definite
(`Gtz.corner_oneAxisZero_heavyInside_cap_posDef`):

  `C_y := (1/ms) • N_out + g_y g_yᵀ − 1 ≻ 0` ,  `N_out = Σ_{d ∈ Cᶜ} t_d G_d`,

because the failure of `A_z` pins the sign `DZ ≥ 0`, the scalar core then
forces `DY < 0`, and `−DY/(1+lam)` IS the plane Sylvester determinant of
`ms·C_y`.  The four-set dominates its own paid form pointwise
(`Gtz.corner_fourSet_capMatrix_floor`), so inverse domination
(`Gtz.quadForm_inv_le_of_loewner`) caps EVERY `A_y⁻¹` reading by the same
`C_y⁻¹` reading (`Gtz.corner_oneAxisZero_heavyInside_reading_cap`).

## The exact erased cap

The erased atom is an exact eigenvector of the paid matrix: the `x`-resolution
makes `N_out g_x = (1 − t_x) g_x`, the corner orthogonality kills the `g_y`
term, and the erased reading of the cap inverse evaluates in closed form
(`Gtz.corner_oneAxisZero_heavyInside_erased_cap`):

  `g_xᵀ C_y⁻¹ g_x = ms / (1 − t_x − ms)` .

## The cap gap empties the cell

At a `(6,3)` tie the excluded pair of the dominating four-set obeys
`t_x + t_z ≤ t_x·r_x + t_z·r_z`
(`Gtz.corner_oneAxisZero_heavyInside_excluded_floor`).  The caps bound the
same combination by `t_x·ms/(1−t_x−ms) + t_z·(g_zᵀC_y⁻¹g_z)`.  When that
closed form sits below `t_x + t_z` — the CAP GAP — the heavy-inside cell holds
no tie (`Gtz.corner_oneAxisZero_heavyInside_capGap_absurd`, with the `y`–`z`
mirror), and the tie condition of the cell sharpens losslessly to the three
floors PLUS the cap-gap refusal
(`Gtz.corner_oneAxisZero_heavyInside_isTie_iff_capGap`).

Measured on 1.6·10⁵ fresh heavy-inside samples: the paid matrix is positive
definite at 100.0% of the cell (as proved), and the cap gap fires at 79.5% —
the largest single kernel bite taken out of the cell.  Verified in 512-bit
arithmetic at all 96 exact IC violators and all 27 odds-endpoint misses of the
measured battery: the caps hold at every one.

## The determinant pins of the residual

For the remaining region the module lands the exact determinant instruments.
Three rank-one updates of a `3×3` base obey the EXCHANGE LAW
(`Gtz.det_add_atomMatrix_sub_atomMatrix_cross`)

  `det(M + ppᵀ − qqᵀ) + det(M + qqᵀ) = det(M + ppᵀ) + det M − (p×q)ᵀM(p×q)` ,

and at a `Z1` corner the cross product of the two axis-carrying inside atoms
IS the erased atom scaled by the gap
(`Gtz.corner_oneAxisZero_cross_pin`):

  `(g_y × g_z)(g_y × g_z)ᵀ = (1 + lam) • g_x g_xᵀ` .

Together they pin the `z`-excluded determinant of the cell against pure
four-set determinants and one erased reading
(`Gtz.corner_oneAxisZero_excluded_det_exchange`), the excluded-pair sum is an
exact determinant ledger (`Gtz.excluded_pair_det_ledger`), and the erased
direction always over-reads the unweighted outside mass
(`Gtz.corner_oneAxisZero_erased_overRead`).
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The quadratic form of a paid four-set -/

/-- The quadratic form of the paid four-set matrix, expanded. -/
theorem capMatrix_quadForm (D : WeightedDesign m 3) (C : Finset (Fin m))
    (e : Fin m) (ms : ℝ) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (((1 / ms) • ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d • atomMatrix (D.atom d)
        + atomMatrix (D.atom e) - 1) *ᵥ v)
      = (1 / ms) * ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d * (D.atom d ⬝ᵥ v) ^ 2
        + (D.atom e ⬝ᵥ v) ^ 2 - v ⬝ᵥ v := by
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul, Matrix.one_mulVec]
  simp only [smul_eq_mul]
  rw [show atomMatrix (D.atom e) = Matrix.vecMulVec (D.atom e) (D.atom e) from rfl,
    quadForm_atomMatrix, Matrix.sum_mulVec, dotProduct_sum]
  have hterm : ∀ d ∈ (Cᶜ : Finset (Fin m)),
      v ⬝ᵥ ((D.weight d • atomMatrix (D.atom d)) *ᵥ v)
        = D.weight d * (D.atom d ⬝ᵥ v) ^ 2 := by
    intro d _
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d) from rfl,
      quadForm_atomMatrix]
  rw [Finset.sum_congr rfl hterm]

/-- **The four-set dominates its paid form.**  Each outside atom pays at least
its own weighted share of the cap — pointwise, no corner, no tie. -/
theorem corner_fourSet_capMatrix_floor (D : WeightedDesign m 3)
    {x y z : Fin m} {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d ≤ ms)
    (v : Fin 3 → ℝ) :
    v ⬝ᵥ (((1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.weight d • atomMatrix (D.atom d)
        + atomMatrix (D.atom y) - 1) *ᵥ v)
      ≤ v ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1) *ᵥ v) := by
  classical
  have hyK : y ∉ (({x, y, z} : Finset (Fin m))ᶜ) := by simp
  have hAyform : v ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1) *ᵥ v)
      = (D.atom y ⬝ᵥ v) ^ 2
        + ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 - v ⬝ᵥ v := by
    rw [quadForm_subsetSum_sub_one, Finset.sum_insert hyK]
  rw [capMatrix_quadForm, hAyform]
  have hpay : (1 / ms) * ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (D.atom d ⬝ᵥ v) ^ 2
      ≤ ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have h1 : D.weight d * (D.atom d ⬝ᵥ v) ^ 2 ≤ ms * (D.atom d ⬝ᵥ v) ^ 2 :=
      mul_le_mul_of_nonneg_right (hmd d hd) (sq_nonneg _)
    calc (1 / ms) * (D.weight d * (D.atom d ⬝ᵥ v) ^ 2)
        ≤ (1 / ms) * (ms * (D.atom d ⬝ᵥ v) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (D.atom d ⬝ᵥ v) ^ 2 := by field_simp
  linarith

/-- Sylvester positivity of a two-by-two form: positive trailing coefficient
and positive determinant give a nonnegative form. -/
theorem sylvester_quad_nonneg {a b c : ℝ} (hc : 0 < c) (hd : 0 < a * c - b ^ 2)
    (X Y : ℝ) : 0 ≤ a * X ^ 2 + 2 * b * (X * Y) + c * Y ^ 2 := by
  have hsq : c * (a * X ^ 2 + 2 * b * (X * Y) + c * Y ^ 2)
      = (a * c - b ^ 2) * X ^ 2 + (c * Y + b * X) ^ 2 := by ring
  nlinarith [hsq, mul_nonneg hd.le (sq_nonneg X), sq_nonneg (c * Y + b * X)]

/-- Sylvester positivity, strict off the origin. -/
theorem sylvester_quad_pos {a b c : ℝ} (hc : 0 < c) (hd : 0 < a * c - b ^ 2)
    {X Y : ℝ} (hne : ¬(X = 0 ∧ Y = 0)) :
    0 < a * X ^ 2 + 2 * b * (X * Y) + c * Y ^ 2 := by
  have hsq : c * (a * X ^ 2 + 2 * b * (X * Y) + c * Y ^ 2)
      = (a * c - b ^ 2) * X ^ 2 + (c * Y + b * X) ^ 2 := by ring
  by_cases hX0 : X = 0
  · have hY0 : Y ≠ 0 := fun h => hne ⟨hX0, h⟩
    have hpos : 0 < (a * c - b ^ 2) * X ^ 2 + (c * Y + b * X) ^ 2 := by
      rw [hX0]
      have := sq_pos_of_ne_zero (mul_ne_zero (ne_of_gt hc) hY0)
      nlinarith [this]
    nlinarith [hsq, hpos, hc]
  · have hpos : 0 < (a * c - b ^ 2) * X ^ 2 + (c * Y + b * X) ^ 2 := by
      have h1 : 0 < (a * c - b ^ 2) * X ^ 2 := mul_pos hd (sq_pos_of_ne_zero hX0)
      have h2 : 0 ≤ (c * Y + b * X) ^ 2 := sq_nonneg _
      linarith
    nlinarith [hsq, hpos, hc]

/-! ## 2. The paid four-set of the heavy-inside cell is positive definite -/

/-- **THE PAID FOUR-SET OF THE HEAVY-INSIDE CELL.**  At a `Z1` proper corner
whose four-set through `z` fails, not only does the four-set through `y`
dominate — its PAID form is already positive definite.  The failure of `A_z`
pins `DZ ≥ 0` through the dichotomy branch, the scalar core then forces
`DY < 0`, and `−DY` is exactly `(1+lam)` times the plane Sylvester determinant
of the paid matrix. -/
theorem corner_oneAxisZero_heavyInside_cap_posDef (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d ≤ ms)
    (hsum : ms + D.weight y + D.weight z < 1) (hmx : ms + D.weight x < 1)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    ((1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        D.weight d • atomMatrix (D.atom d)
      + atomMatrix (D.atom y) - 1).PosDef := by
  classical
  obtain ⟨w, hwunit, hwu, hwx, hxlev, hyd, hzd, hmass, hunit2, horth⟩ :=
    corner_oneAxisZero_frame_decomp D hxy hxz hyz hlam.le hunit hgap hax haz
  set ay : ℝ := D.atom y ⬝ᵥ u with hayd
  set az : ℝ := D.atom z ⬝ᵥ u with hazd
  set cy : ℝ := D.atom y ⬝ᵥ w with hcyd
  set cz : ℝ := D.atom z ⬝ᵥ w with hczd
  set ty : ℝ := D.weight y with htyd
  set tz : ℝ := D.weight z with htzd
  set tx : ℝ := D.weight x with htxd
  have hnu : (0 : ℝ) < 1 + lam := by linarith
  -- the frame squares
  have hcy2 : (1 + lam) * cy ^ 2 = az ^ 2 := by
    linear_combination (-cy ^ 2) * hmass + az ^ 2 * hunit2
      + (ay * cy - az * cz) * horth
  have hcz2 : (1 + lam) * cz ^ 2 = ay ^ 2 := by
    linear_combination (-cz ^ 2) * hmass + ay ^ 2 * hunit2
      + (az * cz - ay * cy) * horth
  have hccc : (1 + lam) * (ay * az * (cy * cz)) = -(ay ^ 2 * az ^ 2) := by
    linear_combination ((1 + lam) * az * cz) * horth - az ^ 2 * hcz2
  -- the Parseval plane facts of the weighted outside mass
  set N : Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d • atomMatrix (D.atom d)
    with hN
  have hNpsd : N.PosSemidef := by
    rw [hN]
    exact Matrix.posSemidef_sum _ fun d _ =>
      (posSemidef_atomMatrix (D.atom d)).smul (D.weight_pos d).le
  have hNread : ∀ v : Fin 3 → ℝ, v ⬝ᵥ (N *ᵥ v)
      = v ⬝ᵥ v - tx * (D.atom x ⬝ᵥ v) ^ 2 - ty * (D.atom y ⬝ᵥ v) ^ 2
        - tz * (D.atom z ⬝ᵥ v) ^ 2 := by
    intro v
    have hquad : v ⬝ᵥ (N *ᵥ v) = ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        D.weight d * (D.atom d ⬝ᵥ v) ^ 2 := by
      rw [hN, Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d) from rfl,
        quadForm_atomMatrix]
    rw [hquad]
    have hpar := parseval_read_corner_split D hxy hxz hyz v
    rw [htxd, htyd, htzd]
    linarith [hpar]
  have hn11 : ty * cy ^ 2 + tz * cz ^ 2 ≤ 1 := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hNpsd).2 w
    rw [star_trivial, hNread w, hwunit] at h
    have hyw' : D.atom y ⬝ᵥ w = cy := rfl
    have hzw' : D.atom z ⬝ᵥ w = cz := rfl
    rw [hwx, hyw', hzw'] at h
    nlinarith [h]
  have hncross : (ty * (ay * cy) + tz * (az * cz)) ^ 2
      ≤ (1 - ty * ay ^ 2 - tz * az ^ 2) * (1 - ty * cy ^ 2 - tz * cz ^ 2) := by
    have hcs := psd_form_cross_sq_le hNpsd u w
    rw [hNread u, hNread w, hunit, hwunit] at hcs
    have hNuw : u ⬝ᵥ (N *ᵥ w) = -(ty * (ay * cy) + tz * (az * cz)) := by
      have hquad : u ⬝ᵥ (N *ᵥ w) = ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          D.weight d * ((D.atom d ⬝ᵥ u) * (D.atom d ⬝ᵥ w)) := by
        rw [hN, Matrix.sum_mulVec, dotProduct_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
          show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d)
            from rfl]
        rw [vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
          dotProduct_comm u (D.atom d)]
        ring_nf
      have hParPol : ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          D.weight d * ((D.atom d ⬝ᵥ u) * (D.atom d ⬝ᵥ w))
          = u ⬝ᵥ w - tx * ((D.atom x ⬝ᵥ u) * (D.atom x ⬝ᵥ w))
            - ty * ((D.atom y ⬝ᵥ u) * (D.atom y ⬝ᵥ w))
            - tz * ((D.atom z ⬝ᵥ u) * (D.atom z ⬝ᵥ w)) := by
        have hpolar := dotProduct_eq_sum_weight_mul_pair D u w
        rw [← Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6))
            (fun a => D.weight a * ((D.atom a ⬝ᵥ u) * (D.atom a ⬝ᵥ w))),
          sum_triple_eq hxy hxz hyz] at hpolar
        rw [htxd, htyd, htzd]
        linarith [hpolar]
      rw [hquad, hParPol, hwu, hax]
      have hyu : D.atom y ⬝ᵥ u = ay := rfl
      have hyw' : D.atom y ⬝ᵥ w = cy := rfl
      have hzu : D.atom z ⬝ᵥ u = az := rfl
      have hzw' : D.atom z ⬝ᵥ w = cz := rfl
      rw [hyu, hyw', hzu, hzw']
      ring
    rw [hNuw] at hcs
    have hxu' : D.atom x ⬝ᵥ u = 0 := hax
    have hyu : D.atom y ⬝ᵥ u = ay := rfl
    have hzu : D.atom z ⬝ᵥ u = az := rfl
    have hyw' : D.atom y ⬝ᵥ w = cy := rfl
    have hzw' : D.atom z ⬝ᵥ w = cz := rfl
    rw [hxu', hyu, hzu, hyw', hzw', hwx] at hcs
    nlinarith [hcs]
  -- the two branch scalars
  set DZ : ℝ := lam * (az ^ 2 * ms * (ms - 1 + ty - tz) + ay ^ 2 * (ty - tz)
      + (1 + lam) * tz * (1 - ty))
    - (1 + lam) * ((1 - tz) * (1 - ms - ty)) with hDZ
  set DY : ℝ := lam * (ay ^ 2 * ms * (ms - 1 + tz - ty) + az ^ 2 * (tz - ty)
      + (1 + lam) * ty * (1 - tz))
    - (1 + lam) * ((1 - ty) * (1 - ms - tz)) with hDY
  -- the failure of A_z pins DZ ≥ 0
  have hDZge : 0 ≤ DZ := by
    by_contra hcon
    have hcon' : DZ < 0 := not_le.mp hcon
    have hsylD : 0 < (1 + ms * lam - (ty + ms) * ay ^ 2 - tz * az ^ 2)
        * (1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2)
        - ((ty + ms) * (ay * cy) + tz * (az * cz)) ^ 2 := by
      have hC2 : (1 + lam) * (1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2)
          = (1 + lam) - (ty + ms) * az ^ 2 - tz * ay ^ 2 := by
        linear_combination (-(ty + ms)) * hcy2 + (-tz) * hcz2
      have hB2 : (1 + lam) * ((ty + ms) * (ay * cy) + tz * (az * cz)) ^ 2
          = (ty + ms - tz) ^ 2 * (ay ^ 2 * az ^ 2) := by
        linear_combination ((ty + ms) ^ 2 * ay ^ 2) * hcy2
          + (2 * (ty + ms) * tz) * hccc + (tz ^ 2 * az ^ 2) * hcz2
      have hbridge : (1 + lam) * ((1 + ms * lam - (ty + ms) * ay ^ 2 - tz * az ^ 2)
            * (1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2)
          - ((ty + ms) * (ay * cy) + tz * (az * cz)) ^ 2) = -DZ := by
        rw [hDZ]
        linear_combination (1 + ms * lam - (ty + ms) * ay ^ 2 - tz * az ^ 2) * hC2
          - hB2
          + (ay ^ 2 * ms * tz + ay ^ 2 * ty * tz - lam * ms + lam * ty * tz
              - lam * tz + ms * tz * az ^ 2 + ms * tz - ms + ty * tz * az ^ 2
              + ty * tz - ty - tz) * hmass
      have hDZpos : 0 < -DZ := by linarith
      nlinarith [hbridge, hDZpos, hnu]
    have hsylC : 0 < 1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2 := by
      have hcy1 : cy ^ 2 ≤ 1 := by nlinarith [sq_nonneg cz, hunit2]
      have hcz1 : cz ^ 2 ≤ 1 := by nlinarith [sq_nonneg cy, hunit2]
      have h1 : (ty + ms) * cy ^ 2 ≤ ty + ms := by
        nlinarith [sq_nonneg cy, D.weight_pos y]
      have h2 : tz * cz ^ 2 ≤ tz := by nlinarith [sq_nonneg cz, D.weight_pos z]
      linarith [hsum]
    exact hnotz (oneAxisZero_fourSet_posDef_branch D hxy hxz hyz hunit hwunit
      hwu hax hwx hxlev hyd hzd hmass hunit2 horth hms hmd hmx hsylC hsylD)
  -- the scalar core forces DY < 0
  have hDYlt : DY < 0 := by
    by_contra hcon
    have hz2 : az ^ 2 = 1 + lam - ay ^ 2 := by linarith [hmass]
    have hgez : (0 : ℝ) ≤ DZ := hDZge
    have hgey : (0 : ℝ) ≤ DY := not_lt.mp hcon
    rw [hDZ, hz2] at hgez
    rw [hDY, hz2] at hgey
    have hb0 : (0 : ℝ) ≤ ay ^ 2 := sq_nonneg ay
    have hbnu : ay ^ 2 ≤ 1 + lam := by nlinarith [sq_nonneg az, hmass]
    have hn2core : ty * (1 + lam - ay ^ 2) + tz * ay ^ 2 ≤ 1 + lam := by
      have hscaled : (1 + lam) * (ty * cy ^ 2 + tz * cz ^ 2)
          = ty * az ^ 2 + tz * ay ^ 2 := by
        linear_combination ty * hcy2 + tz * hcz2
      have hmul := mul_le_mul_of_nonneg_left hn11 hnu.le
      have hz2y : ty * az ^ 2 = ty * (1 + lam - ay ^ 2) := by rw [hz2]
      linarith [hscaled, hz2y, hmul]
    have hn3core : (ty - tz) ^ 2 * ay ^ 2 * (1 + lam - ay ^ 2)
        ≤ (1 - ty * ay ^ 2 - tz * (1 + lam - ay ^ 2))
          * ((1 + lam) - ty * (1 + lam - ay ^ 2) - tz * ay ^ 2) := by
      have hsq : (1 + lam) * (ty * (ay * cy) + tz * (az * cz)) ^ 2
          = (ty - tz) ^ 2 * (ay ^ 2 * az ^ 2) := by
        linear_combination (ty ^ 2 * ay ^ 2) * hcy2 + (2 * ty * tz) * hccc
          + (tz ^ 2 * az ^ 2) * hcz2
      have hH2v : (1 + lam) * (1 - ty * cy ^ 2 - tz * cz ^ 2)
          = (1 + lam) - ty * az ^ 2 - tz * ay ^ 2 := by
        linear_combination (-ty) * hcy2 + (-tz) * hcz2
      have hstep : (ty - tz) ^ 2 * (ay ^ 2 * az ^ 2)
          ≤ (1 - ty * ay ^ 2 - tz * az ^ 2)
            * ((1 + lam) - ty * az ^ 2 - tz * ay ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_left hncross hnu.le
        rw [hsq] at hmul
        calc (ty - tz) ^ 2 * (ay ^ 2 * az ^ 2)
            ≤ (1 + lam) * ((1 - ty * ay ^ 2 - tz * az ^ 2)
                * (1 - ty * cy ^ 2 - tz * cz ^ 2)) := hmul
          _ = (1 - ty * ay ^ 2 - tz * az ^ 2)
              * ((1 + lam) * (1 - ty * cy ^ 2 - tz * cz ^ 2)) := by ring
          _ = (1 - ty * ay ^ 2 - tz * az ^ 2)
              * ((1 + lam) - ty * az ^ 2 - tz * ay ^ 2) := by rw [hH2v]
      rw [hz2] at hstep
      nlinarith [hstep]
    exact oneAxisZero_fourSet_scalar_core ty tz ms lam (ay ^ 2)
      (by rw [htyd]; exact D.weight_pos y) (by rw [htzd]; exact D.weight_pos z)
      hms hlam hb0 hbnu hsum hn2core hn3core (by linarith [hgez])
      (by linarith [hgey])
  -- DY < 0 is the plane Sylvester determinant of the paid matrix
  have hsylD : 0 < (1 + ms * lam - (tz + ms) * az ^ 2 - ty * ay ^ 2)
      * (1 - (tz + ms) * cz ^ 2 - ty * cy ^ 2)
      - ((tz + ms) * (az * cz) + ty * (ay * cy)) ^ 2 := by
    have hC2 : (1 + lam) * (1 - (tz + ms) * cz ^ 2 - ty * cy ^ 2)
        = (1 + lam) - (tz + ms) * ay ^ 2 - ty * az ^ 2 := by
      linear_combination (-(tz + ms)) * hcz2 + (-ty) * hcy2
    have hB2 : (1 + lam) * ((tz + ms) * (az * cz) + ty * (ay * cy)) ^ 2
        = (tz + ms - ty) ^ 2 * (ay ^ 2 * az ^ 2) := by
      linear_combination ((tz + ms) ^ 2 * az ^ 2) * hcz2
        + (2 * (tz + ms) * ty) * hccc + (ty ^ 2 * ay ^ 2) * hcy2
    have hbridge : (1 + lam)
          * ((1 + ms * lam - (tz + ms) * az ^ 2 - ty * ay ^ 2)
            * (1 - (tz + ms) * cz ^ 2 - ty * cy ^ 2)
          - ((tz + ms) * (az * cz) + ty * (ay * cy)) ^ 2) = -DY := by
      rw [hDY]
      linear_combination (1 + ms * lam - (tz + ms) * az ^ 2 - ty * ay ^ 2) * hC2
        - hB2
        + (ay ^ 2 * ms * ty + ay ^ 2 * ty * tz - lam * ms + lam * ty * tz
            - lam * ty + ms * ty * az ^ 2 + ms * ty - ms + ty * tz * az ^ 2
            + ty * tz - ty - tz) * hmass
    have hDYpos : 0 < -DY := by linarith
    nlinarith [hbridge, hDYpos, hnu]
  have hsylC : 0 < 1 - (tz + ms) * cz ^ 2 - ty * cy ^ 2 := by
    have hcy1 : cy ^ 2 ≤ 1 := by nlinarith [sq_nonneg cz, hunit2]
    have hcz1 : cz ^ 2 ≤ 1 := by nlinarith [sq_nonneg cy, hunit2]
    have h1 : (tz + ms) * cz ^ 2 ≤ tz + ms := by
      nlinarith [sq_nonneg cz, D.weight_pos z]
    have h2 : ty * cy ^ 2 ≤ ty := by nlinarith [sq_nonneg cy, D.weight_pos y]
    linarith [hsum]
  -- assemble positive definiteness of the paid matrix
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun v hv => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    have hNT : Nᵀ = N := by
      rw [hN, Matrix.transpose_sum]
      exact Finset.sum_congr rfl fun d _ => by
        rw [Matrix.transpose_smul,
          transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom d)).1]
    rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_smul, hNT,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom y)).1,
      Matrix.transpose_one]
  · rw [star_trivial]
    set X : ℝ := u ⬝ᵥ v with hX
    set Yv : ℝ := w ⬝ᵥ v with hYv
    set Zr : ℝ := D.atom x ⬝ᵥ v with hZr
    have hxu : u ⬝ᵥ D.atom x = 0 := by rw [dotProduct_comm]; exact hax
    have hwx' : w ⬝ᵥ D.atom x = 0 := by rw [dotProduct_comm]; exact hwx
    have hres := read_sq_orthonormal_resolution hunit hwunit hxlev hwu hxu hwx' v
    have hyread : D.atom y ⬝ᵥ v = ay * X + cy * Yv := by
      rw [hyd, add_dotProduct, smul_dotProduct, smul_dotProduct, hX, hYv]
      simp only [smul_eq_mul]
    have hzread : D.atom z ⬝ᵥ v = az * X + cz * Yv := by
      rw [hzd, add_dotProduct, smul_dotProduct, smul_dotProduct, hX, hYv]
      simp only [smul_eq_mul]
    have hpar := parseval_read_corner_split D hxy hxz hyz v
    rw [← htxd, ← htyd, ← htzd, ← hZr, hyread, hzread] at hpar
    have hSigma : ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        D.weight d * (D.atom d ⬝ᵥ v) ^ 2
        = v ⬝ᵥ v - tx * Zr ^ 2 - ty * (ay * X + cy * Yv) ^ 2
          - tz * (az * X + cz * Yv) ^ 2 := by
      linarith [hpar]
    have hvv : v ⬝ᵥ v = X ^ 2 + Yv ^ 2 + Zr ^ 2 := hres.symm
    have hquadC := capMatrix_quadForm D ({x, y, z} : Finset (Fin 6)) y ms v
    have hscaled : ms * (v ⬝ᵥ (((1 / ms) • N + atomMatrix (D.atom y) - 1) *ᵥ v))
        = ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d * (D.atom d ⬝ᵥ v) ^ 2
          + ms * (D.atom y ⬝ᵥ v) ^ 2 - ms * (v ⬝ᵥ v) := by
      rw [hN, hquadC, mul_sub, mul_add, ← mul_assoc,
        mul_one_div_cancel (ne_of_gt hms), one_mul]
    set Ac : ℝ := 1 + ms * lam - (tz + ms) * az ^ 2 - ty * ay ^ 2 with hAc
    set Bc : ℝ := -((tz + ms) * (az * cz) + ty * (ay * cy)) with hBc
    set Cc : ℝ := 1 - (tz + ms) * cz ^ 2 - ty * cy ^ 2 with hCc
    have hmsform : ms * (v ⬝ᵥ (((1 / ms) • N + atomMatrix (D.atom y) - 1) *ᵥ v))
        = (1 - ms - tx) * Zr ^ 2
          + (Ac * X ^ 2 + 2 * Bc * (X * Yv) + Cc * Yv ^ 2) := by
      rw [hscaled, hSigma, hyread, hvv, hAc, hBc, hCc]
      linear_combination (ms * X ^ 2) * hmass + (ms * Yv ^ 2) * hunit2
        + (2 * ms * X * Yv) * horth
    have hCpos : 0 < Cc := hsylC
    have hDpos : 0 < Ac * Cc - Bc ^ 2 := by
      have hval : Ac * Cc - Bc ^ 2
          = (1 + ms * lam - (tz + ms) * az ^ 2 - ty * ay ^ 2)
              * (1 - (tz + ms) * cz ^ 2 - ty * cy ^ 2)
            - ((tz + ms) * (az * cz) + ty * (ay * cy)) ^ 2 := by
        rw [hAc, hBc, hCc]
        ring
      rw [hval]
      exact hsylD
    have hvpos : 0 < v ⬝ᵥ v := dotProduct_self_pos hv
    have hXYZ : 0 < X ^ 2 + Yv ^ 2 + Zr ^ 2 := by rw [← hvv]; exact hvpos
    have hbig : 0 < ms * (v ⬝ᵥ (((1 / ms) • N + atomMatrix (D.atom y) - 1) *ᵥ v)) := by
      rw [hmsform]
      by_cases hXY : X = 0 ∧ Yv = 0
      · have hZne : Zr ≠ 0 := by
          intro h0
          rw [hXY.1, hXY.2, h0] at hXYZ
          norm_num at hXYZ
        have hZpos : 0 < (1 - ms - tx) * Zr ^ 2 := by
          have : 0 < 1 - ms - tx := by linarith [hmx]
          exact mul_pos this (sq_pos_of_ne_zero hZne)
        have hQ := sylvester_quad_nonneg hCpos hDpos X Yv
        linarith
      · have hQ := sylvester_quad_pos hCpos hDpos hXY
        have hZnn : 0 ≤ (1 - ms - tx) * Zr ^ 2 := by
          have : 0 ≤ 1 - ms - tx := by linarith [hmx]
          exact mul_nonneg this (sq_nonneg _)
        linarith
    have hform := mul_pos (inv_pos.mpr hms) hbig
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hms), one_mul] at hform

/-! ## 3. Every heavy-inside reading is capped -/

/-- **THE HEAVY-INSIDE READING CAP.**  In the heavy-inside cell every reading
of the surviving four-set's inverse gap is bounded by the same reading of the
explicit paid inverse — the tie's floors push the outside readings up, and
this cap holds every reading down with weight and frame data alone. -/
theorem corner_oneAxisZero_heavyInside_reading_cap (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d ≤ ms)
    (hsum : ms + D.weight y + D.weight z < 1) (hmx : ms + D.weight x < 1)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (g : Fin 3 → ℝ) :
    g ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹ *ᵥ g)
      ≤ g ⬝ᵥ (((1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
            D.weight d • atomMatrix (D.atom d)
          + atomMatrix (D.atom y) - 1)⁻¹ *ᵥ g) := by
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hCy := corner_oneAxisZero_heavyInside_cap_posDef D hxy hxz hyz hlam hunit
    hgap hax haz hms hmd hsum hmx hnotz
  exact quadForm_inv_le_of_loewner hAy hCy
    (corner_fourSet_capMatrix_floor D hms hmd) g

/-! ## 4. The erased reading of the paid inverse is exact -/

/-- The weighted outside mass has the erased atom as an exact eigenvector:
the matrix form of the `x`-resolution. -/
theorem corner_oneAxisZero_outside_xEigen (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    (∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d • atomMatrix (D.atom d))
        *ᵥ D.atom x
      = (1 - D.weight x) • D.atom x := by
  have hres := corner_oneAxisZero_outside_xResolve D hxy hxz hyz hlam hunit hgap hax
  calc (∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d • atomMatrix (D.atom d))
        *ᵥ D.atom x
      = ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          (D.weight d • atomMatrix (D.atom d)) *ᵥ D.atom x := by
        rw [Matrix.sum_mulVec]
    _ = ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          (D.weight d * (D.atom d ⬝ᵥ D.atom x)) • D.atom d := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Matrix.smul_mulVec,
          show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d)
            from rfl,
          vecMulVec_mulVec_eq, smul_smul]
    _ = (1 - D.weight x) • D.atom x := hres

/-- **THE ERASED CAP IS EXACT.**  The erased atom is an eigenvector of the
paid four-set matrix, so its reading of the paid inverse evaluates in closed
form: `g_xᵀ C_y⁻¹ g_x = ms/(1 − t_x − ms)`. -/
theorem corner_oneAxisZero_heavyInside_erased_cap (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d ≤ ms)
    (hsum : ms + D.weight y + D.weight z < 1) (hmx : ms + D.weight x < 1)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    D.atom x ⬝ᵥ (((1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          D.weight d • atomMatrix (D.atom d)
        + atomMatrix (D.atom y) - 1)⁻¹ *ᵥ D.atom x)
      = ms / (1 - D.weight x - ms) := by
  classical
  set Cy : Matrix (Fin 3) (Fin 3) ℝ :=
    (1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        D.weight d • atomMatrix (D.atom d)
      + atomMatrix (D.atom y) - 1 with hCy
  have hCyPD := corner_oneAxisZero_heavyInside_cap_posDef D hxy hxz hyz hlam hunit
    hgap hax haz hms hmd hsum hmx hnotz
  rw [← hCy] at hCyPD
  have hdetC : IsUnit Cy.det := isUnit_iff_ne_zero.mpr (ne_of_gt hCyPD.det_pos)
  set κ : ℝ := (1 - D.weight x - ms) / ms with hκ
  have hκpos : 0 < κ := by
    rw [hκ]
    have : 0 < 1 - D.weight x - ms := by linarith [hmx]
    positivity
  have hyx : D.atom y ⬝ᵥ D.atom x = 0 := by
    rw [dotProduct_comm]
    exact (corner_oneAxisZero_xOrthogonal D hxy hxz hyz hlam.le hunit hgap hax).1
  have hCx : Cy *ᵥ D.atom x = κ • D.atom x := by
    rw [hCy, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      corner_oneAxisZero_outside_xEigen D hxy hxz hyz hlam.le hunit hgap hax,
      show atomMatrix (D.atom y) = Matrix.vecMulVec (D.atom y) (D.atom y) from rfl,
      vecMulVec_mulVec_eq, hyx, zero_smul, add_zero, Matrix.one_mulVec,
      smul_smul, hκ]
    rw [show (1 / ms * (1 - D.weight x)) = (1 - D.weight x) / ms by ring]
    rw [show ((1 - D.weight x - ms) / ms) = (1 - D.weight x) / ms - 1 by
      field_simp]
    rw [sub_smul, one_smul]
  have hinv : Cy⁻¹ *ᵥ D.atom x = κ⁻¹ • D.atom x := by
    have hxrec : D.atom x = Cy *ᵥ (κ⁻¹ • D.atom x) := by
      rw [Matrix.mulVec_smul, hCx, smul_smul, inv_mul_cancel₀ (ne_of_gt hκpos),
        one_smul]
    calc Cy⁻¹ *ᵥ D.atom x = Cy⁻¹ *ᵥ (Cy *ᵥ (κ⁻¹ • D.atom x)) := by rw [← hxrec]
      _ = (Cy⁻¹ * Cy) *ᵥ (κ⁻¹ • D.atom x) := by rw [Matrix.mulVec_mulVec]
      _ = κ⁻¹ • D.atom x := by
          rw [Matrix.nonsing_inv_mul Cy hdetC, Matrix.one_mulVec]
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam.le
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin 6))) hax
  rw [hinv, dotProduct_smul, smul_eq_mul, hlev, mul_one, hκ, inv_div]

/-! ## 5. The excluded floor of the heavy-inside cell -/

/-- **THE EXCLUDED PAIR OF THE HEAVY-INSIDE FOUR-SET.**  At a `(6,3)` tie the
dominating four-set through `y` forces the excluded pair `{x, z}` to read its
inverse gap at least at one on weighted average. -/
theorem corner_oneAxisZero_heavyInside_excluded_floor (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    D.weight x + D.weight z
      ≤ D.weight x
          * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom x))
        + D.weight z
          * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom z)) := by
  classical
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hF : (insert y (({x, y, z} : Finset (Fin 6))ᶜ)).card = 4 := by
    rw [Finset.card_insert_of_notMem hyK,
      card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)]
  have hcompl : ((insert y (({x, y, z} : Finset (Fin 6))ᶜ))ᶜ : Finset (Fin 6))
      = {x, z} := by
    rw [Finset.compl_insert, compl_compl]
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
  have hfloor := tie_fourSet_excluded_floor D htie _ hF hAy
  rw [hcompl] at hfloor
  have hxz' : x ∉ ({z} : Finset (Fin 6)) := by simp [hxz]
  rw [Finset.sum_insert hxz', Finset.sum_singleton,
    Finset.sum_insert hxz', Finset.sum_singleton] at hfloor
  exact hfloor

/-! ## 6. The cap gap empties the cell -/

/-- **THE CAP GAP EMPTIES THE HEAVY-INSIDE CELL.**  When the closed-form cap
combination of the excluded pair undercuts its weight total, the heavy-inside
cell of the `Z1` stratum holds no `(6,3)` tie: the tie's excluded floor and
the paid caps are contradictory. -/
theorem corner_oneAxisZero_heavyInside_capGap_absurd (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d ≤ ms)
    (hsum : ms + D.weight y + D.weight z < 1) (hmx : ms + D.weight x < 1)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hcapgap : D.weight x * (ms / (1 - D.weight x - ms))
        + D.weight z
          * (D.atom z ⬝ᵥ (((1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
                D.weight d • atomMatrix (D.atom d)
              + atomMatrix (D.atom y) - 1)⁻¹ *ᵥ D.atom z))
      < D.weight x + D.weight z) : False := by
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hfloor := corner_oneAxisZero_heavyInside_excluded_floor D htie hxy hxz hyz hAy
  have hrx := corner_oneAxisZero_heavyInside_reading_cap D hxy hxz hyz hlam hunit
    hgap hax haz hms hmd hsum hmx hnotz (D.atom x)
  rw [corner_oneAxisZero_heavyInside_erased_cap D hxy hxz hyz hlam hunit hgap hax
    haz hms hmd hsum hmx hnotz] at hrx
  have hrz := corner_oneAxisZero_heavyInside_reading_cap D hxy hxz hyz hlam hunit
    hgap hax haz hms hmd hsum hmx hnotz (D.atom z)
  have hwx := (D.weight_pos x).le
  have hwz := (D.weight_pos z).le
  nlinarith [hfloor, hrx, hrz, hcapgap,
    mul_le_mul_of_nonneg_left hrx hwx, mul_le_mul_of_nonneg_left hrz hwz]

/-- **The cap gap, `y` and `z` exchanged.**  When the four-set through `y`
fails, the same closed form at the four-set through `z` empties the mirrored
cell. -/
theorem corner_oneAxisZero_heavyInside_capGap_absurd' (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (hay : D.atom y ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d ≤ ms)
    (hsum : ms + D.weight y + D.weight z < 1) (hmx : ms + D.weight x < 1)
    (hnoty : ¬ (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hcapgap : D.weight x * (ms / (1 - D.weight x - ms))
        + D.weight y
          * (D.atom y ⬝ᵥ (((1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
                D.weight d • atomMatrix (D.atom d)
              + atomMatrix (D.atom z) - 1)⁻¹ *ᵥ D.atom y))
      < D.weight x + D.weight y) : False := by
  have hset : ({x, z, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) := by
    ext c
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  exact corner_oneAxisZero_heavyInside_capGap_absurd D htie hxz hxy (Ne.symm hyz)
    hlam hunit (by rw [hset]; exact hgap) hax hay hms
    (by rw [hset]; exact hmd) (by linarith [hsum]) hmx
    (by rw [hset]; exact hnoty) (by rw [hset]; exact hcapgap)

/-- **The heavy-inside tie condition, sharpened by the cap gap.**  In the
heavy-inside cell the tie is the three outside floors, and the floors force
the closed-form cap combination to reach the excluded weight total: the
residual content of the cell shrinks losslessly onto the cap-gap-nonnegative
region. -/
theorem corner_oneAxisZero_heavyInside_isTie_iff_capGap (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d ≤ ms)
    (hsum : ms + D.weight y + D.weight z < 1) (hmx : ms + D.weight x < 1)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    IsTie D ↔
      ((∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        1 ≤ D.atom d ⬝ᵥ
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom d))
      ∧ D.weight x + D.weight z
          ≤ D.weight x * (ms / (1 - D.weight x - ms))
            + D.weight z
              * (D.atom z ⬝ᵥ (((1 / ms) • ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
                    D.weight d • atomMatrix (D.atom d)
                  + atomMatrix (D.atom y) - 1)⁻¹ *ᵥ D.atom z))) := by
  constructor
  · intro htie
    refine ⟨(corner_oneAxisZero_heavyInside_isTie_iff D hxy hxz hyz hlam hunit
      hgap hax haz hnotz).mp htie, ?_⟩
    by_contra hcon
    exact corner_oneAxisZero_heavyInside_capGap_absurd D htie hxy hxz hyz hlam
      hunit hgap hax haz hms hmd hsum hmx hnotz (not_le.mp hcon)
  · rintro ⟨hfloors, -⟩
    exact (corner_oneAxisZero_heavyInside_isTie_iff D hxy hxz hyz hlam hunit
      hgap hax haz hnotz).mpr hfloors

/-! ## 7. The determinant exchange law of two rank-one updates -/

/-- **THE RANK-TWO DETERMINANT EXCHANGE LAW.**  For any `3×3` base, adding one
atom and subtracting another exchanges against the two single-atom updates
through one cross-product reading:

  `det(M + ppᵀ − qqᵀ) + det(M + qqᵀ) = det(M + ppᵀ) + det M − (p×q)ᵀM(p×q)`.

A polynomial identity — no hypotheses. -/
theorem det_add_atomMatrix_sub_atomMatrix_cross (M : Matrix (Fin 3) (Fin 3) ℝ)
    (p q : Fin 3 → ℝ) :
    (M + atomMatrix p - atomMatrix q).det + (M + atomMatrix q).det
      = (M + atomMatrix p).det + M.det
        - crossProduct p q ⬝ᵥ (M *ᵥ crossProduct p q) := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.sub_apply,
    atomMatrix, Matrix.vecMulVec_apply, cross_apply, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## 8. The cross pin of the `Z1` frame -/

/-- **THE CROSS PIN.**  At a `Z1` corner the cross product of the two
axis-carrying inside atoms is the erased atom scaled by the gap:

  `(g_y × g_z)(g_y × g_z)ᵀ = (1 + lam) • g_x g_xᵀ` . -/
theorem corner_oneAxisZero_cross_pin (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0) :
    atomMatrix (crossProduct (D.atom y) (D.atom z))
      = (1 + lam) • atomMatrix (D.atom x) := by
  obtain ⟨w, hwunit, hwu, hwx, hxlev, hyd, hzd, hmass, hunit2, horth⟩ :=
    corner_oneAxisZero_frame_decomp D hxy hxz hyz hlam hunit hgap hax haz
  set ay : ℝ := D.atom y ⬝ᵥ u with hayd
  set az : ℝ := D.atom z ⬝ᵥ u with hazd
  set cy : ℝ := D.atom y ⬝ᵥ w with hcyd
  set cz : ℝ := D.atom z ⬝ᵥ w with hczd
  have hnu : (0 : ℝ) < 1 + lam := by linarith
  have hcy2 : (1 + lam) * cy ^ 2 = az ^ 2 := by
    linear_combination (-cy ^ 2) * hmass + az ^ 2 * hunit2
      + (ay * cy - az * cz) * horth
  have hcz2 : (1 + lam) * cz ^ 2 = ay ^ 2 := by
    linear_combination (-cz ^ 2) * hmass + ay ^ 2 * hunit2
      + (az * cz - ay * cy) * horth
  have hccc : (1 + lam) * (ay * az * (cy * cz)) = -(ay ^ 2 * az ^ 2) := by
    linear_combination ((1 + lam) * az * cz) * horth - az ^ 2 * hcz2
  -- the cross product collapses onto the plane normal
  have h1 : crossProduct (D.atom y) (D.atom z)
      = (ay * cz - cy * az) • crossProduct u w := by
    rw [hyd, hzd]
    funext i
    fin_cases i <;>
      simp [cross_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring
  -- the plane normal carries the erased atom
  have hcu : u ⬝ᵥ crossProduct u w = 0 := dot_self_cross u w
  have hcw : w ⬝ᵥ crossProduct u w = 0 := dot_cross_self u w
  have hcc : crossProduct u w ⬝ᵥ crossProduct u w = 1 := by
    rw [cross_dot_cross, hunit, hwunit, hwu, dotProduct_comm w u, hwu]
    ring
  have hxu : u ⬝ᵥ D.atom x = 0 := by rw [dotProduct_comm]; exact hax
  have hwx' : w ⬝ᵥ D.atom x = 0 := by rw [dotProduct_comm]; exact hwx
  have hres := atomMatrix_orthonormal_resolution hunit hwunit hxlev hwu hxu hwx'
  have happly := congrArg
    (fun M : Matrix (Fin 3) (Fin 3) ℝ => M *ᵥ crossProduct u w) hres
  simp only [Matrix.add_mulVec, Matrix.one_mulVec] at happly
  rw [show atomMatrix u = Matrix.vecMulVec u u from rfl,
    show atomMatrix w = Matrix.vecMulVec w w from rfl,
    show atomMatrix (D.atom x) = Matrix.vecMulVec (D.atom x) (D.atom x) from rfl,
    vecMulVec_mulVec_eq, vecMulVec_mulVec_eq, vecMulVec_mulVec_eq,
    hcu, hcw, zero_smul, zero_smul, zero_add, zero_add] at happly
  have hcx : crossProduct u w
      = (D.atom x ⬝ᵥ crossProduct u w) • D.atom x := happly.symm
  have hsq : (D.atom x ⬝ᵥ crossProduct u w) ^ 2 = 1 := by
    have hread := read_sq_orthonormal_resolution hunit hwunit hxlev hwu hxu hwx'
      (crossProduct u w)
    rw [hcu, hcw, hcc] at hread
    nlinarith [hread]
  have hscal : (ay * cz - cy * az) ^ 2 = 1 + lam := by
    have hkey : (1 + lam) * ((ay * cz - cy * az) ^ 2) = (1 + lam) * (1 + lam) := by
      linear_combination ay ^ 2 * hcz2 + az ^ 2 * hcy2 - 2 * hccc
        + (ay ^ 2 + az ^ 2 + 1 + lam) * hmass
    exact mul_left_cancel₀ (ne_of_gt hnu) hkey
  rw [h1, atomMatrix_smul, hscal, hcx, atomMatrix_smul, hsq, one_smul]

/-! ## 9. The excluded determinant exchange of the heavy-inside cell -/

/-- **THE EXCLUDED DETERMINANT EXCHANGE.**  At a `Z1` corner the `z`-excluded
determinant of the `y` four-set exchanges against pure four-set determinants
and one erased reading of the outside gap:

  `det(A_y − g_zg_zᵀ) + det A_z = det A_y + det(S_{Cᶜ} − 1)
      − (1+lam)·g_xᵀ(S_{Cᶜ} − 1)g_x` . -/
theorem corner_oneAxisZero_excluded_det_exchange (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0) :
    (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
        - atomMatrix (D.atom z)).det
      + (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det
    = (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det
      + (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).det
      - (1 + lam)
        * (D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
            *ᵥ D.atom x)) := by
  classical
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hzK : z ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  set K : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1 with hK
  have hAy : subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
      = K + atomMatrix (D.atom y) := by
    rw [hK, subsetSum, subsetSum, Finset.sum_insert hyK]
    abel
  have hAz : subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
      = K + atomMatrix (D.atom z) := by
    rw [hK, subsetSum, subsetSum, Finset.sum_insert hzK]
    abel
  have hpin := corner_oneAxisZero_cross_pin D hxy hxz hyz hlam hunit hgap hax haz
  have hcrossread : crossProduct (D.atom y) (D.atom z)
        ⬝ᵥ (K *ᵥ crossProduct (D.atom y) (D.atom z))
      = (1 + lam) * (D.atom x ⬝ᵥ (K *ᵥ D.atom x)) := by
    calc crossProduct (D.atom y) (D.atom z)
          ⬝ᵥ (K *ᵥ crossProduct (D.atom y) (D.atom z))
        = Matrix.trace (K * atomMatrix (crossProduct (D.atom y) (D.atom z))) :=
          (trace_mul_atomMatrix K _).symm
      _ = Matrix.trace (K * ((1 + lam) • atomMatrix (D.atom x))) := by rw [hpin]
      _ = (1 + lam) * Matrix.trace (K * atomMatrix (D.atom x)) := by
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      _ = (1 + lam) * (D.atom x ⬝ᵥ (K *ᵥ D.atom x)) := by
          rw [trace_mul_atomMatrix]
  have h9 := det_add_atomMatrix_sub_atomMatrix_cross K (D.atom y) (D.atom z)
  rw [hcrossread] at h9
  rw [hAy, hAz]
  linarith [h9]

/-- **THE EXCLUDED-PAIR DETERMINANT LEDGER.**  The weighted excluded-pair
excess of any invertible base is an exact determinant combination: the matrix
determinant lemma, weighted over the pair.  With the base at the surviving
four-set this is the determinant form of the `o = 0` excluded floor. -/
theorem excluded_pair_det_ledger {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ}
    (hdet : IsUnit M.det) (p q : Fin k → ℝ) (a b : ℝ) :
    (a * (p ⬝ᵥ (M⁻¹ *ᵥ p) - 1) + b * (q ⬝ᵥ (M⁻¹ *ᵥ q) - 1)) * M.det
      = -(a * (M - atomMatrix p).det + b * (M - atomMatrix q).det) := by
  rw [det_sub_atomMatrix hdet p, det_sub_atomMatrix hdet q]
  ring

/-- **THE TIE'S DETERMINANT FLOOR.**  At a `(6,3)` tie the excluded-pair
determinants of the dominating four-set are nonpositive on weighted average:
the determinant form of the excluded floor, ready for the exchange pins. -/
theorem corner_oneAxisZero_heavyInside_tie_det_floor (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    D.weight x * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
        - atomMatrix (D.atom x)).det
      + D.weight z * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
          - atomMatrix (D.atom z)).det ≤ 0 := by
  have hdet : IsUnit (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hAy.det_pos)
  have hfloor := corner_oneAxisZero_heavyInside_excluded_floor D htie hxy hxz hyz hAy
  have hled := excluded_pair_det_ledger hdet (D.atom x) (D.atom z)
    (D.weight x) (D.weight z)
  have hS : 0 ≤ D.weight x
        * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom x) - 1)
      + D.weight z
        * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom z) - 1) := by
    nlinarith [hfloor]
  have hprod := mul_nonneg hS hAy.det_pos.le
  rw [hled] at hprod
  linarith

/-! ## 10. The erased over-read of the outside mass -/

/-- **THE ERASED OVER-READ.**  The unweighted outside mass reads the erased
direction at least at `(1 − t_x)/ms`: the over-coverage at the erased atom
itself. -/
theorem corner_oneAxisZero_erased_overRead (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    {ms : ℝ} (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d ≤ ms) :
    1 - D.weight x
      ≤ ms * (D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
          *ᵥ D.atom x)) := by
  have hcover := corner_oneAxisZero_outside_overCoverage D hxy hxz hyz hlam hunit
    hgap hax hmd (D.atom x)
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  have hread : D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
        *ᵥ D.atom x)
      = ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ D.atom x) ^ 2 := by
    rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d)
        from rfl,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm (D.atom x) (D.atom d)]
    ring
  rw [hread]
  rw [hlev] at hcover
  linarith [hcover]

/-- **The erased over-read is strict**: below the erased-and-cap weight budget
the outside mass over-reads the erased direction beyond one. -/
theorem corner_oneAxisZero_erased_overRead_strict (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    {ms : ℝ} (hms : 0 < ms) (hmx : ms + D.weight x < 1)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d ≤ ms) :
    1 < D.atom x ⬝ᵥ (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) *ᵥ D.atom x) := by
  have hfloor := corner_oneAxisZero_erased_overRead D hxy hxz hyz hlam hunit hgap
    hax hmd
  nlinarith [hfloor, hms, hmx]

end Gtz

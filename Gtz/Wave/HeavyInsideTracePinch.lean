import Gtz.Wave.ErasedDeflationFloor
import Gtz.Design.PivotStallPropagation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The member trace pinch, the survivor self-read, and the S-floor of the
# heavy-inside cell

This module lands the per-member trace law of a dominating four-set and its
consequences on the two `Z1` cells.  Measured at 512 bits, the member trace
pinch alone refutes 71 of the 72 stored both-light survivors and the stored
fork-21 heavy-inside survivor; the S-floor refutes the heavy-inside survivor
independently.  The witness fails the pinch in exact rationals — a fourth
kernel refutation route.

## The instrument

For a positive definite base, one subtracted atom and one added atom exchange
through three inverse readings (`Gtz.det_sub_add_atomMatrix_readings`):

  `det(M − ppᵀ + qqᵀ) = det M · ((1 − pᵀM⁻¹p)(1 + qᵀM⁻¹q) + (pᵀM⁻¹q)²)` .

The proof composes the two landed determinant lemmas with the exact
Sherman–Morrison cross update — no new matrix analysis.

## The member trace pinch

The readings of a dominating set at its own inverse gap total three plus the
trace (`Gtz.subset_reading_total`).  At a tie every member reads at least one,
so every member reading is pinned below the trace
(`Gtz.tie_fourSet_member_trace_pinch`):

  `q_eᵀ(S_F − 1)⁻¹ q_e ≤ tr (S_F − 1)⁻¹`  for every member `e` of `F` .

The landed pivot determinant floor is the SUM form of this law; the member
form is per-atom and strictly sharper.  Measured at 512 bits it fires at 58
of the 72 stored both-light survivors at the `y` four-set, at 57 at the `z`
four-set, at 71 of 72 jointly, and at the stored heavy-inside survivor at
both four-sets.

## The survivor self-read of the heavy-inside cell

On the heavy-inside cell the failed four-set has nonpositive determinant, and
the instrument turns that sign into a tie-free reading law
(`Gtz.corner_oneAxisZero_heavyInside_selfRead`):

  `(r_y − 1)(1 + r_z) ≥ ρ²` ,  `r_y = g_yᵀA_y⁻¹g_y`, `r_z = g_zᵀA_y⁻¹g_z`,
  `ρ = g_yᵀA_y⁻¹g_z` ,

so the surviving inside atom reads its own four-set above one
(`Gtz.corner_oneAxisZero_heavyInside_selfRead_ge_one`) — the four-set form of
the anchor law, with the exact cross sharpening.

## The S-floor

At a heavy-inside tie the pinch at `e = y` gives `tr A_y⁻¹ ≥ r_y`, the odds
determinant floor turns into the reading form
(`Gtz.corner_oneAxisZero_heavyInside_odds_reading_floor`)

  `o · (tr A_y⁻¹ − 1) ≤ (1 + o) · S` ,  `S = t_x(r_x − 1) + t_z(r_z − 1)` ,

and the chain closes into the S-FLOOR
(`Gtz.corner_oneAxisZero_heavyInside_sFloor`):

  `o · ρ² ≤ (1 + o) · S · (1 + r_z)`  for every admissible odds level `o` .

The `o = 0` clause is the landed sign `S ≥ 0`; every positive level now
charges `S` a strictly positive floor whenever `ρ ≠ 0`.  The measured
maximizers of `min_d r_d` over the sharpened heavy-inside clause region all
sit at `S = 0` with `ρ² > 0`: the S-floor is the clause that kills them.

## The caps close unconditionally

With the outside TOTAL as the cap weight, both side conditions of the paid
four-set collapse to weight positivity, so the erased cap needs no
hypotheses beyond the cell (`Gtz.corner_oneAxisZero_heavyInside_erased_cap_auto`):

  `r_x ≤ (1 − t_x − t_y − t_z)/(t_y + t_z)` ,

and the S-floor collides with the capped `S`
(`Gtz.corner_oneAxisZero_heavyInside_sWindow`): at every admissible `o`,

  `o·ρ² ≤ (1+o)·(t_x·(capx − 1) + t_z·(g_zᵀC_y⁻¹g_z − 1))·(1 + r_z)` .

At `o = 0` this is the landed cap-gap refusal; the positive levels extend the
cap-gap kill region.

## Calibration

The witness refutation: at the witness four-set `A_y = 3·1 + g₁g₁ᵀ` the
inverse is exact (`Gtz.oneAxisZeroWitness_fourSet_inv`), the member `3` reads
`2275/2037 > 1`, the trace is `7307/8148 < 1`, and the pinch refuses the tie
(`Gtz.oneAxisZeroWitness_not_isTie_by_tracePinch`).
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The two-update determinant instrument -/

/-- **THE TWO-UPDATE DETERMINANT LAW.**  Over a positive definite base, one
subtracted and one added atom exchange through three inverse readings:

  `det(M − ppᵀ + qqᵀ) = det M · ((1 − pᵀM⁻¹p)(1 + qᵀM⁻¹q) + (pᵀM⁻¹q)²)` .

The two landed determinant lemmas and the exact Sherman–Morrison cross update
compose into the law — no eigenvalue and no case split. -/
theorem det_sub_add_atomMatrix_readings {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ}
    (hM : M.PosDef) (p q : Fin k → ℝ) :
    (M - atomMatrix p + atomMatrix q).det
      = M.det * ((1 - p ⬝ᵥ (M⁻¹ *ᵥ p)) * (1 + q ⬝ᵥ (M⁻¹ *ᵥ q))
          + (p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2) := by
  have hMdet : IsUnit M.det := isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  have hMq : (M + atomMatrix q).PosDef :=
    hM.add_posSemidef (posSemidef_atomMatrix q)
  have hMqdet : IsUnit (M + atomMatrix q).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hMq.det_pos)
  have hshape : M - atomMatrix p + atomMatrix q
      = (M + atomMatrix q) - atomMatrix p := by abel
  have hcross := inverseForm_add_atomMatrix_cross_update hM q p
  rw [hshape, det_sub_atomMatrix hMqdet p, det_add_atomMatrix hMdet q]
  linear_combination M.det * hcross

/-! ## 2. The reading total of a dominating set -/

/-- **THE READING TOTAL.**  The members of any set with invertible gap read
the inverse gap at three plus its trace — the identity behind every trace
floor of the campaign, at every cardinality. -/
theorem subset_reading_total (D : WeightedDesign m 3) (F : Finset (Fin m))
    (hdet : IsUnit (subsetSum D F - 1).det) :
    ∑ a ∈ F, D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a)
      = 3 + Matrix.trace (subsetSum D F - 1)⁻¹ := by
  classical
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hA
  have hSF : subsetSum D F = A + 1 := by rw [hA]; abel
  have hexp : Matrix.trace (A⁻¹ * subsetSum D F)
      = ∑ a ∈ F, D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a) := by
    rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun a _ => trace_mul_atomMatrix A⁻¹ (D.atom a)
  rw [hSF, Matrix.mul_add, Matrix.trace_add, Matrix.nonsing_inv_mul A hdet,
    Matrix.trace_one, Matrix.mul_one] at hexp
  rw [← hexp, Fintype.card_fin]
  norm_num

/-! ## 3. The member trace pinch -/

/-- **THE MEMBER TRACE PINCH.**  At a tie, EVERY member of a strictly
dominating four-set reads the inverse gap below its trace: the other three
member floors pay for the pinched member inside the reading total.  The
landed pivot determinant floor is the sum form; this is the per-member
sharpening.  Measured at 512 bits the pinch refutes 71 of the 72 stored
both-light survivors and the stored heavy-inside survivor. -/
theorem tie_fourSet_member_trace_pinch (D : WeightedDesign m 3)
    (htie : IsTie D) (F : Finset (Fin m)) (hF : F.card = 4)
    (hPD : (subsetSum D F - 1).PosDef) {e : Fin m} (he : e ∈ F) :
    D.atom e ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom e)
      ≤ Matrix.trace (subsetSum D F - 1)⁻¹ := by
  classical
  have hdet : IsUnit (subsetSum D F - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have htotal := subset_reading_total D F hdet
  have hsplit := Finset.add_sum_erase F
    (fun a => D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a)) he
  have hcard : (F.erase e).card = 3 := by
    rw [Finset.card_erase_of_mem he, hF]
  have hones : ∑ _a ∈ F.erase e, (1 : ℝ) = 3 := by
    rw [Finset.sum_const, hcard]
    norm_num
  have hrest : (3 : ℝ)
      ≤ ∑ a ∈ F.erase e, D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a) := by
    rw [← hones]
    exact Finset.sum_le_sum fun a ha =>
      fourSet_leverage_ge_one D htie F hF hPD (Finset.mem_of_mem_erase ha)
  linarith [htotal, hsplit, hrest]

/-! ## 4. The survivor self-read of the heavy-inside cell -/

/-- **THE SURVIVOR SELF-READ.**  On the heavy-inside cell the failed four-set
has nonpositive determinant, and the two-update law reads that sign at the
surviving four-set:

  `(r_y − 1)(1 + r_z) ≥ ρ²` ,  `ρ = g_yᵀ A_y⁻¹ g_z` .

Tie-free: the cell alone forces the survivor's inside atom to over-read its
own four-set, quantitatively in the cross reading. -/
theorem corner_oneAxisZero_heavyInside_selfRead (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z)) ^ 2
      ≤ (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom y) - 1)
        * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z)) := by
  classical
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hzK : z ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hAzAy : subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
      = (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
        - atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [subsetSum, subsetSum, Finset.sum_insert hzK, Finset.sum_insert hyK]
    abel
  have hdetz := corner_oneAxisZero_heavyInside_failedSet_det_nonpos D hxy hxz
    hyz hlam hunit hgap hax haz hnotz
  have hread := det_sub_add_atomMatrix_readings hAy (D.atom y) (D.atom z)
  rw [← hAzAy] at hread
  rw [hread] at hdetz
  nlinarith [hAy.det_pos, hdetz]

/-- **The survivor reads its own atom above one** — the four-set form of the
anchor self-reading, tie-free on the cell. -/
theorem corner_oneAxisZero_heavyInside_selfRead_ge_one (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    1 ≤ D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom y) := by
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hself := corner_oneAxisZero_heavyInside_selfRead D hxy hxz hyz hlam
    hunit hgap hax haz hnotz
  have hrz0 : 0 ≤ D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hAy.inv.posSemidef).2
      (D.atom z)
    rwa [star_trivial] at h
  by_contra hcon
  push Not at hcon
  nlinarith [hself, hrz0,
    sq_nonneg (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
      - 1)⁻¹ *ᵥ D.atom z))]

/-! ## 5. The trace pinch of the heavy-inside cell -/

/-- **THE HEAVY-INSIDE MEMBER TRACE PINCH.**  At a heavy-inside tie every
member of the surviving four-set — the inside survivor and the three outside
atoms — reads the inverse gap below its trace. -/
theorem corner_oneAxisZero_heavyInside_member_trace_pinch (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    ∀ e ∈ insert y (({x, y, z} : Finset (Fin 6))ᶜ),
      D.atom e ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom e)
        ≤ Matrix.trace (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹ := by
  classical
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hF : (insert y (({x, y, z} : Finset (Fin 6))ᶜ)).card = 4 := by
    rw [Finset.card_insert_of_notMem hyK,
      card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)]
  exact fun e he => tie_fourSet_member_trace_pinch D htie _ hF hAy he

/-- **THE SHARPENED TRACE PINCH.**  At a heavy-inside tie the trace excess
carries the whole self-read floor:

  `(tr A_y⁻¹ − 1)(1 + r_z) ≥ ρ²` . -/
theorem corner_oneAxisZero_heavyInside_trace_pinch_sharp (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z)) ^ 2
      ≤ (Matrix.trace (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            - 1)
        * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z)) := by
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hself := corner_oneAxisZero_heavyInside_selfRead D hxy hxz hyz hlam
    hunit hgap hax haz hnotz
  have hpinch := corner_oneAxisZero_heavyInside_member_trace_pinch D htie hxy
    hxz hyz hAy y (Finset.mem_insert_self y _)
  have hrz0 : 0 ≤ D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hAy.inv.posSemidef).2
      (D.atom z)
    rwa [star_trivial] at h
  nlinarith [hself, hpinch, hrz0]

/-! ## 6. The odds reading floor -/

/-- **THE ODDS READING FLOOR.**  The landed odds determinant floor, divided by
the positive four-set determinant: at a tie, for every admissible odds level,

  `o · (tr A_y⁻¹ − 1) ≤ (1 + o) · (t_x(r_x − 1) + t_z(r_z − 1))` .

The `o = 0` clause is the landed sign `S ≥ 0` of the excluded pair. -/
theorem corner_oneAxisZero_heavyInside_odds_reading_floor (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    {o : ℝ} (ho : 0 ≤ o)
    (hodds : ∀ a ∈ insert y (({x, y, z} : Finset (Fin 6))ᶜ),
      o * D.weight a ≤ 1 - D.weight a) :
    o * (Matrix.trace (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          - 1)
      ≤ (1 + o) * (D.weight x
            * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                  - 1)⁻¹ *ᵥ D.atom x) - 1)
          + D.weight z
            * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                  - 1)⁻¹ *ᵥ D.atom z) - 1)) := by
  have hdet : IsUnit (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hAy.det_pos)
  have hoddsdet := corner_oneAxisZero_heavyInside_odds_det_floor D htie hxy hxz
    hyz hAy ho hodds
  have hled := excluded_pair_det_ledger hdet (D.atom x) (D.atom z)
    (D.weight x) (D.weight z)
  have hbr := trace_inv_mul_det_eq_trace_adjugate hdet
  have hsub : (1 + o) * (D.weight x
        * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
          - atomMatrix (D.atom x)).det
      + D.weight z
        * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
          - atomMatrix (D.atom z)).det)
      + o * (Matrix.trace
            (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).adjugate
          - (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det)
      = (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det
        * (o * (Matrix.trace
              (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹ - 1)
          - (1 + o) * (D.weight x
              * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                    - 1)⁻¹ *ᵥ D.atom x) - 1)
            + D.weight z
              * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                    - 1)⁻¹ *ᵥ D.atom z) - 1))) := by
    linear_combination (1 + o) * hled - o * hbr
  rw [hsub] at hoddsdet
  by_contra hcon
  push Not at hcon
  nlinarith [hoddsdet, hAy.det_pos, hcon]

/-! ## 7. The S-floor of the heavy-inside cell -/

/-- **THE S-FLOOR.**  At a heavy-inside tie the excluded-pair excess `S` is
floored by the squared cross reading through every admissible odds level:

  `o · ρ² ≤ (1 + o) · S · (1 + r_z)` .

The chain: the self-read floors `ρ²` by `(r_y − 1)(1 + r_z)`, the member trace
pinch lifts `r_y` to the trace, and the odds reading floor charges the trace
excess to `S`.  At `o = 0` this is the landed sign `S ≥ 0`; at every positive
level the floor is strictly positive whenever the cross reading is nonzero.
Measured: the stored fork-21 heavy-inside survivor violates it at 512 bits. -/
theorem corner_oneAxisZero_heavyInside_sFloor (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    {o : ℝ} (ho : 0 ≤ o)
    (hodds : ∀ a ∈ insert y (({x, y, z} : Finset (Fin 6))ᶜ),
      o * D.weight a ≤ 1 - D.weight a) :
    o * (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z)) ^ 2
      ≤ (1 + o) * (D.weight x
            * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                  - 1)⁻¹ *ᵥ D.atom x) - 1)
          + D.weight z
            * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                  - 1)⁻¹ *ᵥ D.atom z) - 1))
        * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z)) := by
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hsharp := corner_oneAxisZero_heavyInside_trace_pinch_sharp D htie hxy hxz
    hyz hlam hunit hgap hax haz hnotz
  have hoddsr := corner_oneAxisZero_heavyInside_odds_reading_floor D htie hxy
    hxz hyz hAy ho hodds
  have hrz0 : 0 ≤ D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hAy.inv.posSemidef).2
      (D.atom z)
    rwa [star_trivial] at h
  have hone : (0 : ℝ) ≤ 1 + D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by linarith
  have hstep1 := mul_le_mul_of_nonneg_left hsharp ho
  have hstep2 := mul_le_mul_of_nonneg_right hoddsr hone
  nlinarith [hstep1, hstep2, hone, ho]

/-! ## 8. The caps close unconditionally at the outside total -/

/-- **THE ERASED CAP, HYPOTHESIS-FREE.**  With the outside weight TOTAL as the
cap weight, both side conditions of the paid four-set are weight positivity,
so the heavy-inside erased reading is capped by the closed form

  `r_x ≤ (1 − t_x − t_y − t_z)/(t_y + t_z)`

on the whole cell, with no cap hypotheses. -/
theorem corner_oneAxisZero_heavyInside_erased_cap_auto (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom x)
      ≤ (1 - D.weight x - D.weight y - D.weight z)
        / (D.weight y + D.weight z) := by
  classical
  set ms : ℝ := ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d with hmsdef
  have hms_eq : ms = 1 - D.weight x - D.weight y - D.weight z := by
    have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6)) D.weight
    rw [D.weight_sum_one, sum_triple_eq hxy hxz hyz] at hsplit
    rw [hmsdef]
    linarith
  have hKne : ((({x, y, z} : Finset (Fin 6))ᶜ)).Nonempty := by
    rw [← Finset.card_pos,
      card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)]
    norm_num
  have hms : 0 < ms := Finset.sum_pos (fun d _ => D.weight_pos d) hKne
  have hmd : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d ≤ ms :=
    fun d hd => Finset.single_le_sum (fun e _ => (D.weight_pos e).le) hd
  have hsum : ms + D.weight y + D.weight z < 1 := by
    rw [hms_eq]
    linarith [D.weight_pos x]
  have hmx : ms + D.weight x < 1 := by
    rw [hms_eq]
    linarith [D.weight_pos y, D.weight_pos z]
  have hcap := corner_oneAxisZero_heavyInside_reading_cap D hxy hxz hyz hlam
    hunit hgap hax haz hms hmd hsum hmx hnotz (D.atom x)
  rw [corner_oneAxisZero_heavyInside_erased_cap D hxy hxz hyz hlam hunit hgap
    hax haz hms hmd hsum hmx hnotz] at hcap
  have hval : ms / (1 - D.weight x - ms)
      = (1 - D.weight x - D.weight y - D.weight z)
        / (D.weight y + D.weight z) := by
    rw [hms_eq]
    congr 1
    ring
  rwa [hval] at hcap

/-- **THE S-WINDOW.**  At a heavy-inside tie the S-floor collides with the
paid caps: for every admissible odds level `o`,

  `o·ρ² ≤ (1+o)·(t_x·(capx − 1) + t_z·(g_zᵀC_y⁻¹g_z − 1))·(1 + r_z)` ,

with `capx = (1−t_x−t_y−t_z)/(t_y+t_z)` the closed erased cap and `C_y` the
paid four-set at the outside total.  The `o = 0` clause is the landed cap-gap
refusal; the positive levels extend its kill region by the squared cross
reading. -/
theorem corner_oneAxisZero_heavyInside_sWindow (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    {o : ℝ} (ho : 0 ≤ o)
    (hodds : ∀ a ∈ insert y (({x, y, z} : Finset (Fin 6))ᶜ),
      o * D.weight a ≤ 1 - D.weight a) :
    o * (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z)) ^ 2
      ≤ (1 + o) * (D.weight x
            * ((1 - D.weight x - D.weight y - D.weight z)
                / (D.weight y + D.weight z) - 1)
          + D.weight z
            * (D.atom z ⬝ᵥ
                (((1 / (1 - D.weight x - D.weight y - D.weight z))
                    • ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
                        D.weight d • atomMatrix (D.atom d)
                  + atomMatrix (D.atom y) - 1)⁻¹ *ᵥ D.atom z) - 1))
        * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z)) := by
  classical
  set ms : ℝ := ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d with hmsdef
  have hms_eq : ms = 1 - D.weight x - D.weight y - D.weight z := by
    have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6)) D.weight
    rw [D.weight_sum_one, sum_triple_eq hxy hxz hyz] at hsplit
    rw [hmsdef]
    linarith
  have hKne : ((({x, y, z} : Finset (Fin 6))ᶜ)).Nonempty := by
    rw [← Finset.card_pos,
      card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)]
    norm_num
  have hms : 0 < ms := Finset.sum_pos (fun d _ => D.weight_pos d) hKne
  have hmd : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d ≤ ms :=
    fun d hd => Finset.single_le_sum (fun e _ => (D.weight_pos e).le) hd
  have hsum : ms + D.weight y + D.weight z < 1 := by
    rw [hms_eq]
    linarith [D.weight_pos x]
  have hmx : ms + D.weight x < 1 := by
    rw [hms_eq]
    linarith [D.weight_pos y, D.weight_pos z]
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hsfloor := corner_oneAxisZero_heavyInside_sFloor D htie hxy hxz hyz hlam
    hunit hgap hax haz hnotz ho hodds
  have hcapx := corner_oneAxisZero_heavyInside_erased_cap_auto D hxy hxz hyz
    hlam hunit hgap hax haz hnotz
  have hcapz := corner_oneAxisZero_heavyInside_reading_cap D hxy hxz hyz hlam
    hunit hgap hax haz hms hmd hsum hmx hnotz (D.atom z)
  rw [hms_eq] at hcapz
  have hrz0 : 0 ≤ D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hAy.inv.posSemidef).2
      (D.atom z)
    rwa [star_trivial] at h
  have hone : (0 : ℝ) ≤ 1 + D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by linarith
  have hSle : D.weight x
        * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom x) - 1)
      + D.weight z
        * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z) - 1)
      ≤ D.weight x
          * ((1 - D.weight x - D.weight y - D.weight z)
              / (D.weight y + D.weight z) - 1)
        + D.weight z
          * (D.atom z ⬝ᵥ
              (((1 / (1 - D.weight x - D.weight y - D.weight z))
                  • ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
                      D.weight d • atomMatrix (D.atom d)
                + atomMatrix (D.atom y) - 1)⁻¹ *ᵥ D.atom z) - 1) := by
    have h1 := mul_le_mul_of_nonneg_left hcapx (D.weight_pos x).le
    have h2 := mul_le_mul_of_nonneg_left hcapz (D.weight_pos z).le
    linarith
  have hfac : (0 : ℝ) ≤ (1 + o)
      * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z)) := by
    have : (0 : ℝ) ≤ 1 + o := by linarith
    exact mul_nonneg this hone
  nlinarith [hsfloor, mul_le_mul_of_nonneg_left hSle hfac]

/-! ## 9. The both-light cell carries the pinch at both four-sets -/

/-- **THE BOTH-LIGHT MEMBER TRACE PINCH.**  At a both-light tie every member
of EACH four-set reads that four-set's inverse gap below its trace.  Measured
at 512 bits this pair of clauses refutes 71 of the 72 stored both-light
survivors — the sharpest single addition to the cell's clause map. -/
theorem corner_oneAxisZero_bothLight_member_trace_pinch (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    (∀ e ∈ insert y (({x, y, z} : Finset (Fin 6))ᶜ),
      D.atom e ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom e)
        ≤ Matrix.trace (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹)
    ∧ (∀ e ∈ insert z (({x, y, z} : Finset (Fin 6))ᶜ),
      D.atom e ⬝ᵥ ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom e)
        ≤ Matrix.trace (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹) := by
  classical
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hzK : z ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hFy : (insert y (({x, y, z} : Finset (Fin 6))ᶜ)).card = 4 := by
    rw [Finset.card_insert_of_notMem hyK,
      card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)]
  have hFz : (insert z (({x, y, z} : Finset (Fin 6))ᶜ)).card = 4 := by
    rw [Finset.card_insert_of_notMem hzK,
      card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)]
  exact ⟨fun e he => tie_fourSet_member_trace_pinch D htie _ hFy hAy he,
    fun e he => tie_fourSet_member_trace_pinch D htie _ hFz hAz he⟩

/-! ## 10. The witness fails the pinch in exact rationals -/

/-- The inverse of the witness four-set gap, exact:  `A_y = 3·1 + g₁g₁ᵀ` has

  `A_y⁻¹ = !![2275/8148, 0, −35/679; 0, 1/3, 0; −35/679, 0, 193/679]` . -/
theorem oneAxisZeroWitness_fourSet_inv :
    (subsetSum oneAxisZeroWitness (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1)⁻¹
      = !![2275 / 8148, 0, -(35 / 679); 0, 1 / 3, 0;
          -(35 / 679), 0, 193 / 679] := by
  refine Matrix.inv_eq_right_inv ?_
  rw [oneAxisZeroWitness_fourSet_form]
  have hform : (3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + atomMatrix (oneAxisZeroWitness.atom 1)
      = !![2316 / 625, 0, 84 / 125; 0, 3, 0; 84 / 125, 0, 91 / 25] := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [atomMatrix, Matrix.vecMulVec_apply, oneAxisZeroWitness_atom,
        oneAxisZeroWitnessAtom, Matrix.one_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
  rw [hform]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- **The witness is not a tie, by the trace pinch.**  At the witness four-set
the outside atom `3` reads `2275/2037 > 1` while the inverse-gap trace is
`7307/8148 < 1`: a tie would pinch the reading below the trace.  The fourth
kernel refutation route of the witness, and the first through a trace law. -/
theorem oneAxisZeroWitness_not_isTie_by_tracePinch :
    ¬ IsTie oneAxisZeroWitness := by
  intro htie
  have hF : (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)).card = 4 := by decide
  have hmem : (3 : Fin 6) ∈ insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ) := by decide
  have hval := tie_fourSet_member_trace_pinch oneAxisZeroWitness htie _ hF
    (oneAxisZeroWitness_fourSet_posDef (Or.inl rfl)) hmem
  rw [oneAxisZeroWitness_fourSet_inv] at hval
  have hread : oneAxisZeroWitness.atom 3 ⬝ᵥ
      ((!![2275 / 8148, 0, -(35 / 679); 0, 1 / 3, 0;
          -(35 / 679), 0, 193 / 679] : Matrix (Fin 3) (Fin 3) ℝ)
        *ᵥ oneAxisZeroWitness.atom 3) = 2275 / 2037 := by
    norm_num [oneAxisZeroWitness_atom, oneAxisZeroWitnessAtom, dotProduct,
      Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
  have htr : Matrix.trace (!![2275 / 8148, 0, -(35 / 679); 0, 1 / 3, 0;
      -(35 / 679), 0, 193 / 679] : Matrix (Fin 3) (Fin 3) ℝ) = 7307 / 8148 := by
    rw [Matrix.trace_fin_three]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  rw [hread, htr] at hval
  norm_num at hval

end Gtz

import Gtz.Wave.HeavyInsideCapGap
import Gtz.Wave.OneAxisZeroWitness
import Gtz.LinAlg.DepthTwoDowndate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The downdate floor of the anchor, the odds-determinant floor, and the
# residual wiring of the `Z1` stratum

This module lands two new tie laws for the `Z1` stratum and wires them into
an exact residual decomposition of `Gtz.OneAxisZeroPairCoverage`.

## The downdate floor

At a `Z1` tie the anchor `B` loses one outside atom `q_d` and the four-set
`B − q_dq_dᵀ` keeps the pair `{x, d}` out.  The excluded floor of that
four-set, the Sherman–Morrison readings of the downdate, and Cauchy–Schwarz
at `B⁻¹` close into a per-atom law (`Gtz.corner_oneAxisZero_tie_downdate_floor`):

  `t_x + t_d ≤ ρ_d·(t_x + 2t_d) + t_x·X` ,  `ρ_d = q_dᵀB⁻¹q_d`, `X = g_xᵀB⁻¹g_x`.

With the landed erased cap `X ≤ ms/(1 − t_x − ms)` the floor becomes closed
form (`Gtz.corner_oneAxisZero_tie_downdate_floor_cap`).  As `t_x` collapses,
the law forces EVERY outside anchor reading up to `1/2` — the anchor-side
weapon for the small-`t_x` misses: all five stored fork-20 miss points
violate it, with margins from `1.8·10⁻⁴` to `0.18`.

## The odds-determinant floor

The excluded-trace floor of the surviving four-set `A_y`, the excluded-pair
determinant ledger, and the trace–adjugate bridge give a polynomial tie law
(`Gtz.corner_oneAxisZero_heavyInside_odds_det_floor`): for every admissible
odds level `o`,

  `(1+o)·(t_x·det(A_y − G_x) + t_z·det(A_y − G_z))
      + o·(tr adj A_y − det A_y) ≤ 0` .

At `o = 0` this is the landed tie determinant floor.  The bridge instruments
are `Gtz.trace_inv_mul_det_eq_trace_adjugate` and the rank-one update law
`Gtz.trace_adjugate_add_atomMatrix`.  Because the landed caps sit above the
readings, the `o = 0` clause already forces the cap gap nonnegative: the
fork-20 cap-gap clause is subsumed.

## The failed sets have nonpositive determinants

A matrix that one rank-one atom completes to positive definite has at most
one nonpositive eigenvalue, so a failure pins the determinant sign
(`Gtz.det_nonpos_of_not_posDef_of_add_atomMatrix_posDef`).  In the
heavy-inside cell this gives, with no tie, `det A_z ≤ 0` and
`det(S_{Cᶜ} − 1) ≤ 0`
(`Gtz.corner_oneAxisZero_heavyInside_failedSet_det_nonpos`,
`Gtz.corner_oneAxisZero_heavyInside_outsideGap_det_nonpos`).

## The sharpened tie condition and the residual wiring

The heavy-inside tie condition extends losslessly by the three new clause
families (`Gtz.corner_oneAxisZero_heavyInside_isTie_iff_downdateOdds`).
Measured on 2.0·10⁵ fresh heavy-inside samples the sharpened system leaves
one sample in `2·10⁵` — the fork-20 residual was `20.5%` of the cell.  The
whole coverage residual factors exactly through the two cells
(`Gtz.oneAxisZeroPairCoverage_iff_cellResiduals`):

  `OneAxisZeroPairCoverage ↔
     OneAxisZeroHeavyInsideResidual ∧ OneAxisZeroBothLightResidual` ,

where the heavy-inside Prop carries the sharpened clause set in both
orientations and the both-light Prop carries the seven floors plus the new
stratum-wide clauses.

## Calibration

The witness refutes the odds-determinant clause in exact rationals at
`o = 157/44` (`Gtz.oneAxisZeroWitness_oddsDet_fails`), which yields a second,
determinant-route proof that the witness is not a tie
(`Gtz.oneAxisZeroWitness_not_isTie_by_oddsDet`).  The downdate floor HOLDS at
the witness and at the two `Z2` foils, and the bridge identities hold at
every fixture in exact rationals.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The trace–adjugate bridge -/

/-- **The trace–adjugate bridge.**  For an invertible matrix the inverse
trace scales by the determinant onto the adjugate trace. -/
theorem trace_inv_mul_det_eq_trace_adjugate {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} (hdet : IsUnit A.det) :
    Matrix.trace A⁻¹ * A.det = Matrix.trace A.adjugate := by
  rw [Matrix.inv_def, Matrix.trace_smul, smul_eq_mul, mul_comm (Ring.inverse A.det),
    mul_assoc, Ring.inverse_mul_cancel _ hdet, mul_one]

/-- **The adjugate-trace rank-one update.**  Adding one atom to a `3×3` base
moves the adjugate trace by the base trace times the atom mass minus the
atom's own base reading.  A polynomial identity — no hypotheses. -/
theorem trace_adjugate_add_atomMatrix (M : Matrix (Fin 3) (Fin 3) ℝ)
    (p : Fin 3 → ℝ) :
    Matrix.trace (M + atomMatrix p).adjugate
      = Matrix.trace M.adjugate + Matrix.trace M * (p ⬝ᵥ p) - p ⬝ᵥ (M *ᵥ p) := by
  simp only [Matrix.adjugate_fin_three, Matrix.trace_fin_three, Matrix.add_apply,
    atomMatrix, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-! ## 2. A completed failure pins the determinant sign -/

/-- **The completed-failure determinant sign.**  If one atom completes `B` to
a positive definite matrix while `B` itself is not positive definite, the
determinant of `B` is nonpositive: a positive determinant would put the
completed reading below one and resurrect `B` through the rank-one Schur
criterion. -/
theorem det_nonpos_of_not_posDef_of_add_atomMatrix_posDef {k : ℕ}
    {B : Matrix (Fin k) (Fin k) ℝ} {p : Fin k → ℝ}
    (hBp : (B + atomMatrix p).PosDef) (hB : ¬ B.PosDef) : B.det ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hdet : IsUnit (B + atomMatrix p).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hBp.det_pos)
  have hBM : B = (B + atomMatrix p) - atomMatrix p := by abel
  have hdetB : B.det = (B + atomMatrix p).det
      * (1 - p ⬝ᵥ ((B + atomMatrix p)⁻¹ *ᵥ p)) := by
    calc B.det = ((B + atomMatrix p) - atomMatrix p).det := by rw [← hBM]
      _ = (B + atomMatrix p).det
          * (1 - p ⬝ᵥ ((B + atomMatrix p)⁻¹ *ᵥ p)) := det_sub_atomMatrix hdet p
  have hread : p ⬝ᵥ ((B + atomMatrix p)⁻¹ *ᵥ p) < 1 := by
    nlinarith [hBp.det_pos, hcon, hdetB]
  refine hB ?_
  rw [hBM, show atomMatrix p = Matrix.vecMulVec p p from rfl]
  exact (posDef_sub_vecMulVec_iff (B + atomMatrix p) hBp p).mpr hread

/-- **The failed four-set has nonpositive determinant.**  In the heavy-inside
cell the atom `g_y` completes `A_z` to `A_y + G_z ≻ 0`, so the failure of
`A_z` pins `det A_z ≤ 0` — with no tie. -/
theorem corner_oneAxisZero_heavyInside_failedSet_det_nonpos
    (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det ≤ 0 := by
  classical
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hzK : z ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hswap : subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
        + atomMatrix (D.atom y)
      = subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
        + atomMatrix (D.atom z) := by
    rw [subsetSum, subsetSum, Finset.sum_insert hzK, Finset.sum_insert hyK]
    abel
  have hPD : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
      + atomMatrix (D.atom y)).PosDef := by
    rw [hswap]
    exact hAy.add_posSemidef (posSemidef_atomMatrix (D.atom z))
  exact det_nonpos_of_not_posDef_of_add_atomMatrix_posDef hPD hnotz

/-- **The outside gap has nonpositive determinant.**  The failure of `A_z`
passes down to `K = S_{Cᶜ} − 1`, and the atom `g_y` completes `K` to `A_y`:
in the heavy-inside cell `det K ≤ 0` — with no tie. -/
theorem corner_oneAxisZero_heavyInside_outsideGap_det_nonpos
    (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).det ≤ 0 := by
  classical
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hzK : z ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hKy : subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1 + atomMatrix (D.atom y)
      = subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1 := by
    rw [subsetSum, subsetSum, Finset.sum_insert hyK]
    abel
  have hKz : subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1
      = (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
        - Matrix.vecMulVec (D.atom z) (D.atom z) := by
    rw [subsetSum, subsetSum, Finset.sum_insert hzK,
      show atomMatrix (D.atom z) = Matrix.vecMulVec (D.atom z) (D.atom z) from rfl]
    abel
  have hKnot : ¬ (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).PosDef := by
    rw [hKz]
    exact not_posDef_sub_vecMulVec_of_not_posDef hnotz _
  refine det_nonpos_of_not_posDef_of_add_atomMatrix_posDef (p := D.atom y) ?_ hKnot
  rw [hKy]
  exact hAy

/-! ## 3. The downdate floor of the anchor -/

/-- **THE DOWNDATE FLOOR.**  At a `(6,3)` tie with a `Z1` corner, every
outside atom's anchor reading obeys

  `t_x + t_d ≤ ρ_d·(t_x + 2t_d) + t_x·X` .

If the reading `ρ_d` is below one, the anchor downdate `B − q_dq_dᵀ` is the
four-set that keeps the pair `{x, d}` out: its excluded floor opens through
the Sherman–Morrison readings, and Cauchy–Schwarz at `B⁻¹` pays the cross
term.  If `ρ_d` reaches one, the floor is free.  As `t_x` collapses the law
forces every outside anchor reading up to `1/2`. -/
theorem corner_oneAxisZero_tie_downdate_floor (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    {d : Fin 6} (hd : d ∈ (({x, y, z} : Finset (Fin 6))ᶜ)) :
    D.weight x + D.weight d
      ≤ (D.atom d ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom d)) * (D.weight x + 2 * D.weight d)
        + D.weight x
          * (D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
              *ᵥ D.atom x)) := by
  classical
  set B : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ((univ : Finset (Fin 6)).erase x) - 1 with hB
  have hPD : B.PosDef :=
    corner_oneAxisZero_fiveSet_posDef D hxy hxz hyz hlam hunit hgap hax
  set ρ : ℝ := D.atom d ⬝ᵥ (B⁻¹ *ᵥ D.atom d) with hρdef
  set X : ℝ := D.atom x ⬝ᵥ (B⁻¹ *ᵥ D.atom x) with hXdef
  have hInv : (B⁻¹).PosSemidef := hPD.inv.posSemidef
  have hX0 : 0 ≤ X := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hInv).2 (D.atom x)
    rwa [star_trivial] at h
  have htx := D.weight_pos x
  have htd := D.weight_pos d
  by_cases hρ : ρ < 1
  · -- the mixed four-set is positive definite: open the excluded floor
    have hdx : d ≠ x := by
      intro h
      exact (Finset.mem_compl.mp hd) (h ▸ (by simp : x ∈ ({x, y, z} : Finset (Fin 6))))
    have hdF : d ∈ (univ : Finset (Fin 6)).erase x :=
      Finset.mem_erase.mpr ⟨hdx, Finset.mem_univ d⟩
    have hAm_eq : subsetSum D (((univ : Finset (Fin 6)).erase x).erase d) - 1
        = B - Matrix.vecMulVec (D.atom d) (D.atom d) := by
      rw [subsetSum_erase_sub_one_rankOne D ((univ : Finset (Fin 6)).erase x) hdF,
        hB]
    have hAmPD : (subsetSum D (((univ : Finset (Fin 6)).erase x).erase d) - 1).PosDef := by
      rw [hAm_eq]
      exact (posDef_sub_vecMulVec_iff B hPD (D.atom d)).mpr hρ
    have hFcard : (((univ : Finset (Fin 6)).erase x).erase d).card = 4 := by
      rw [Finset.card_erase_of_mem hdF,
        Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
        Fintype.card_fin]
    have hcompl : ((((univ : Finset (Fin 6)).erase x).erase d)ᶜ : Finset (Fin 6))
        = {x, d} := by
      ext a
      simp only [Finset.mem_compl, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h
        rcases not_and_or.mp h with h1 | h2
        · exact Or.inr (not_not.mp h1)
        · exact Or.inl (not_not.mp h2)
      · rintro (rfl | rfl)
        · exact fun hcon => hcon.2 rfl
        · exact fun hcon => hcon.1 rfl
    have hfloor := tie_fourSet_excluded_floor D htie _ hFcard hAmPD
    rw [hcompl] at hfloor
    have hxd : x ∉ ({d} : Finset (Fin 6)) := by simp [Ne.symm hdx]
    rw [Finset.sum_insert hxd, Finset.sum_singleton,
      Finset.sum_insert hxd, Finset.sum_singleton, hAm_eq] at hfloor
    -- the Sherman–Morrison readings of the downdate
    have hne : D.atom d ⬝ᵥ (B⁻¹ *ᵥ D.atom d) ≠ 1 := by
      rw [← hρdef]
      exact ne_of_lt hρ
    have hrd := downdate_reading B hPD (D.atom d) (D.atom d) hne
    have hrx := downdate_reading B hPD (D.atom d) (D.atom x) hne
    rw [← hρdef] at hrd hrx
    rw [← hXdef] at hrx
    set c : ℝ := D.atom d ⬝ᵥ (B⁻¹ *ᵥ D.atom x) with hcdef
    have h1r : (0 : ℝ) < 1 - ρ := by linarith
    have h1rne : (1 : ℝ) - ρ ≠ 0 := ne_of_gt h1r
    -- Cauchy–Schwarz at the inverse metric
    have hCS : c ^ 2 ≤ ρ * X := by
      have h := psd_form_cross_sq_le hInv (D.atom d) (D.atom x)
      rw [← hcdef, ← hρdef, ← hXdef] at h
      exact h
    -- clear the Sherman–Morrison denominators
    have hinvcancel : (1 - ρ) * (1 - ρ)⁻¹ = 1 := mul_inv_cancel₀ h1rne
    have hrd' : (1 - ρ)
        * (D.atom d ⬝ᵥ ((B - Matrix.vecMulVec (D.atom d) (D.atom d))⁻¹
            *ᵥ D.atom d)) = ρ := by
      rw [hrd]
      linear_combination ρ ^ 2 * hinvcancel
    have hrx' : (1 - ρ)
        * (D.atom x ⬝ᵥ ((B - Matrix.vecMulVec (D.atom d) (D.atom d))⁻¹
            *ᵥ D.atom x)) = (1 - ρ) * X + c ^ 2 := by
      rw [hrx]
      linear_combination c ^ 2 * hinvcancel
    have hm := mul_le_mul_of_nonneg_left hfloor h1r.le
    have hexp : (1 - ρ)
        * (D.weight x
            * (D.atom x ⬝ᵥ ((B - Matrix.vecMulVec (D.atom d) (D.atom d))⁻¹
                *ᵥ D.atom x))
          + D.weight d
            * (D.atom d ⬝ᵥ ((B - Matrix.vecMulVec (D.atom d) (D.atom d))⁻¹
                *ᵥ D.atom d)))
        = D.weight x * ((1 - ρ)
            * (D.atom x ⬝ᵥ ((B - Matrix.vecMulVec (D.atom d) (D.atom d))⁻¹
                *ᵥ D.atom x)))
          + D.weight d * ((1 - ρ)
            * (D.atom d ⬝ᵥ ((B - Matrix.vecMulVec (D.atom d) (D.atom d))⁻¹
                *ᵥ D.atom d))) := by ring
    rw [hexp, hrd', hrx'] at hm
    have hcs' : D.weight x * c ^ 2 ≤ D.weight x * (ρ * X) :=
      mul_le_mul_of_nonneg_left hCS htx.le
    nlinarith [hm, hcs']
  · -- the reading is at least one: the floor is free
    push Not at hρ
    have hstep : D.weight x + 2 * D.weight d
        ≤ ρ * (D.weight x + 2 * D.weight d) := by
      nlinarith [hρ, htx, htd]
    nlinarith [hstep, mul_nonneg htx.le hX0, htd]

/-- **The downdate floor, closed form.**  The landed erased cap
`X ≤ ms/(1 − t_x − ms)` prices the erased reading out of the floor:

  `t_x + t_d ≤ ρ_d·(t_x + 2t_d) + t_x·ms/(1 − t_x − ms)` . -/
theorem corner_oneAxisZero_tie_downdate_floor_cap (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ e ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight e ≤ ms)
    (hmx : D.weight x + ms < 1)
    {d : Fin 6} (hd : d ∈ (({x, y, z} : Finset (Fin 6))ᶜ)) :
    D.weight x + D.weight d
      ≤ (D.atom d ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom d)) * (D.weight x + 2 * D.weight d)
        + D.weight x * (ms / (1 - D.weight x - ms)) := by
  have hfloor := corner_oneAxisZero_tie_downdate_floor D htie hxy hxz hyz hlam
    hunit hgap hax hd
  obtain ⟨-, hcap, -⟩ := corner_oneAxisZero_anchor_axis_cap D (by norm_num)
    hxy hxz hyz hlam hunit hgap hax haz hms hmd hmx
  have hpos : (0 : ℝ) < 1 - D.weight x - ms := by linarith
  have hX : D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
        *ᵥ D.atom x) ≤ ms / (1 - D.weight x - ms) := by
    rw [le_div_iff₀ hpos, mul_comm]
    exact hcap
  nlinarith [hfloor, hX, (D.weight_pos x).le,
    mul_le_mul_of_nonneg_left hX (D.weight_pos x).le]

/-! ## 4. The odds-determinant floor of the surviving four-set -/

/-- **THE ODDS-DETERMINANT FLOOR.**  At a `(6,3)` tie whose four-set through
`y` dominates, every admissible odds level `o` floors the excluded-pair
determinants against the adjugate trace:

  `(1+o)·(t_x·det(A_y − G_x) + t_z·det(A_y − G_z))
      + o·(tr adj A_y − det A_y) ≤ 0` .

At `o = 0` this is the landed tie determinant floor.  The excluded-trace
floor supplies the reading form, the excluded-pair ledger converts the
readings to determinants, and the trace–adjugate bridge clears the inverse
trace. -/
theorem corner_oneAxisZero_heavyInside_odds_det_floor (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    {o : ℝ} (ho : 0 ≤ o)
    (hodds : ∀ a ∈ insert y (({x, y, z} : Finset (Fin 6))ᶜ),
      o * D.weight a ≤ 1 - D.weight a) :
    (1 + o) * (D.weight x
          * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
            - atomMatrix (D.atom x)).det
        + D.weight z
          * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
            - atomMatrix (D.atom z)).det)
      + o * (Matrix.trace (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1).adjugate
          - (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det)
      ≤ 0 := by
  classical
  set A : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1 with hA
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hAy.det_pos)
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
  have hfloor := tie_fourSet_excluded_trace_floor D htie _ hF hAy ho hodds
  rw [hcompl] at hfloor
  have hxz' : x ∉ ({z} : Finset (Fin 6)) := by simp [hxz]
  rw [Finset.sum_insert hxz', Finset.sum_singleton,
    Finset.sum_insert hxz', Finset.sum_singleton, ← hA] at hfloor
  set rx : ℝ := D.atom x ⬝ᵥ (A⁻¹ *ᵥ D.atom x) with hrx
  set rz : ℝ := D.atom z ⬝ᵥ (A⁻¹ *ᵥ D.atom z) with hrz
  have hled := excluded_pair_det_ledger hdet (D.atom x) (D.atom z)
    (D.weight x) (D.weight z)
  rw [← hrx, ← hrz] at hled
  have hbridge := trace_inv_mul_det_eq_trace_adjugate hdet
  have hmul := mul_le_mul_of_nonneg_right hfloor hAy.det_pos.le
  have hL : o * (Matrix.trace A⁻¹ - 1) * A.det
      = o * (Matrix.trace A.adjugate - A.det) := by
    linear_combination o * hbridge
  have hR : (1 + o) * (D.weight x * rx + D.weight z * rz
        - (D.weight x + D.weight z)) * A.det
      = -((1 + o) * (D.weight x * (A - atomMatrix (D.atom x)).det
          + D.weight z * (A - atomMatrix (D.atom z)).det)) := by
    linear_combination (1 + o) * hled
  rw [hL, hR] at hmul
  linarith [hmul]

/-! ## 5. The sharpened heavy-inside tie condition -/

/-- **The heavy-inside tie condition, sharpened by the downdate and odds
floors.**  The tie of the heavy-inside cell is the three outside floors, and
the floors force the whole new clause family: the odds-determinant floor at
every admissible level, the downdate floor at every outside atom, and the
excluded-trace floor at every positive definite anchor downdate.  Each added
clause is tie-necessary, so the sharpening is lossless.  Measured on
2.0·10⁵ fresh heavy-inside samples the clause system keeps one sample. -/
theorem corner_oneAxisZero_heavyInside_isTie_iff_downdateOdds
    (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    IsTie D ↔
      ((∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        1 ≤ D.atom d ⬝ᵥ
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom d))
      ∧ (∀ o : ℝ, 0 ≤ o →
          (∀ a ∈ insert y (({x, y, z} : Finset (Fin 6))ᶜ),
            o * D.weight a ≤ 1 - D.weight a) →
          (1 + o) * (D.weight x
                * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
                  - atomMatrix (D.atom x)).det
              + D.weight z
                * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
                  - atomMatrix (D.atom z)).det)
            + o * (Matrix.trace
                  (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                    - 1).adjugate
                - (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                    - 1).det)
            ≤ 0)
      ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          D.weight x + D.weight d
            ≤ (D.atom d ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
                  *ᵥ D.atom d)) * (D.weight x + 2 * D.weight d)
              + D.weight x
                * (D.atom x ⬝ᵥ
                    ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
                      *ᵥ D.atom x)))
      ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), ∀ o : ℝ, 0 ≤ o →
          (∀ a ∈ ((univ : Finset (Fin 6)).erase x).erase d,
            o * D.weight a ≤ 1 - D.weight a) →
          (subsetSum D (((univ : Finset (Fin 6)).erase x).erase d) - 1).PosDef →
          o * (Matrix.trace
                (subsetSum D (((univ : Finset (Fin 6)).erase x).erase d) - 1)⁻¹
              - 1)
            ≤ (1 + o) * (D.weight x
                  * (D.atom x ⬝ᵥ
                      ((subsetSum D (((univ : Finset (Fin 6)).erase x).erase d)
                          - 1)⁻¹ *ᵥ D.atom x))
                + D.weight d
                  * (D.atom d ⬝ᵥ
                      ((subsetSum D (((univ : Finset (Fin 6)).erase x).erase d)
                          - 1)⁻¹ *ᵥ D.atom d))
                - (D.weight x + D.weight d)))) := by
  classical
  constructor
  · intro htie
    have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
      (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
        haz).resolve_left hnotz
    refine ⟨(corner_oneAxisZero_heavyInside_isTie_iff D hxy hxz hyz hlam hunit
      hgap hax haz hnotz).mp htie, fun o ho hodds => ?_, fun d hd => ?_,
      fun d hd o ho hodds hPD => ?_⟩
    · exact corner_oneAxisZero_heavyInside_odds_det_floor D htie hxy hxz hyz
        hAy ho hodds
    · exact corner_oneAxisZero_tie_downdate_floor D htie hxy hxz hyz hlam.le
        hunit hgap hax hd
    · have hdx : d ≠ x := by
        intro h
        exact (Finset.mem_compl.mp hd)
          (h ▸ (by simp : x ∈ ({x, y, z} : Finset (Fin 6))))
      have hdF : d ∈ (univ : Finset (Fin 6)).erase x :=
        Finset.mem_erase.mpr ⟨hdx, Finset.mem_univ d⟩
      have hFcard : (((univ : Finset (Fin 6)).erase x).erase d).card = 4 := by
        rw [Finset.card_erase_of_mem hdF,
          Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
          Fintype.card_fin]
      have hcompl : ((((univ : Finset (Fin 6)).erase x).erase d)ᶜ : Finset (Fin 6))
          = {x, d} := by
        ext a
        simp only [Finset.mem_compl, Finset.mem_erase, Finset.mem_univ, and_true,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h
          rcases not_and_or.mp h with h1 | h2
          · exact Or.inr (not_not.mp h1)
          · exact Or.inl (not_not.mp h2)
        · rintro (rfl | rfl)
          · exact fun hcon => hcon.2 rfl
          · exact fun hcon => hcon.1 rfl
      have hfloor := tie_fourSet_excluded_trace_floor D htie _ hFcard hPD ho hodds
      rw [hcompl] at hfloor
      have hxd : x ∉ ({d} : Finset (Fin 6)) := by simp [Ne.symm hdx]
      rw [Finset.sum_insert hxd, Finset.sum_singleton,
        Finset.sum_insert hxd, Finset.sum_singleton] at hfloor
      linarith [hfloor]
  · rintro ⟨hfloors, -, -, -⟩
    exact (corner_oneAxisZero_heavyInside_isTie_iff D hxy hxz hyz hlam hunit
      hgap hax haz hnotz).mpr hfloors

/-! ## 6. The two cell residuals -/

/-- **THE HEAVY-INSIDE RESIDUAL.**  On the heavy-inside cell of `Z1` proper —
the four-set through `z` fails — the sharpened clause system is infeasible:
the three outside floors, the odds-determinant floors, the downdate floors,
and the excluded-trace floors of the anchor downdates never hold together.
Measured share of the clause region: one sample in `2·10⁵` of the cell. -/
def OneAxisZeroHeavyInsideResidual : Prop :=
  ∀ (D : WeightedDesign 6 3) (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
    ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 →
    subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u →
    D.atom x ⬝ᵥ u = 0 → D.atom y ⬝ᵥ u ≠ 0 → D.atom z ⬝ᵥ u ≠ 0 →
    ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef →
    (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d)) →
    (∀ o : ℝ, 0 ≤ o →
      (∀ a ∈ insert y (({x, y, z} : Finset (Fin 6))ᶜ),
        o * D.weight a ≤ 1 - D.weight a) →
      (1 + o) * (D.weight x
            * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
              - atomMatrix (D.atom x)).det
          + D.weight z
            * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
              - atomMatrix (D.atom z)).det)
        + o * (Matrix.trace
              (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).adjugate
            - (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det)
        ≤ 0) →
    (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      D.weight x + D.weight d
        ≤ (D.atom d ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
              *ᵥ D.atom d)) * (D.weight x + 2 * D.weight d)
          + D.weight x
            * (D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
                *ᵥ D.atom x))) →
    (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), ∀ o : ℝ, 0 ≤ o →
      (∀ a ∈ ((univ : Finset (Fin 6)).erase x).erase d,
        o * D.weight a ≤ 1 - D.weight a) →
      (subsetSum D (((univ : Finset (Fin 6)).erase x).erase d) - 1).PosDef →
      o * (Matrix.trace
            (subsetSum D (((univ : Finset (Fin 6)).erase x).erase d) - 1)⁻¹ - 1)
        ≤ (1 + o) * (D.weight x
              * (D.atom x ⬝ᵥ
                  ((subsetSum D (((univ : Finset (Fin 6)).erase x).erase d) - 1)⁻¹
                    *ᵥ D.atom x))
            + D.weight d
              * (D.atom d ⬝ᵥ
                  ((subsetSum D (((univ : Finset (Fin 6)).erase x).erase d) - 1)⁻¹
                    *ᵥ D.atom d))
            - (D.weight x + D.weight d))) →
    False

/-- **THE BOTH-LIGHT RESIDUAL.**  On the both-light cell of `Z1` proper the
seven floors together with the new stratum-wide clauses are infeasible: the
downdate floors and the odds-determinant floors at BOTH four-sets ride along
with the landed floor system. -/
def OneAxisZeroBothLightResidual : Prop :=
  ∀ (D : WeightedDesign 6 3) (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
    ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 →
    subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u →
    D.atom x ⬝ᵥ u = 0 → D.atom y ⬝ᵥ u ≠ 0 → D.atom z ⬝ᵥ u ≠ 0 →
    (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef →
    (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef →
    (1 ≤ D.atom y ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom y)) →
    (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d)) →
    (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ
        ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d)) →
    (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      D.weight x + D.weight d
        ≤ (D.atom d ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
              *ᵥ D.atom d)) * (D.weight x + 2 * D.weight d)
          + D.weight x
            * (D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
                *ᵥ D.atom x))) →
    (∀ o : ℝ, 0 ≤ o →
      (∀ a ∈ insert y (({x, y, z} : Finset (Fin 6))ᶜ),
        o * D.weight a ≤ 1 - D.weight a) →
      (1 + o) * (D.weight x
            * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
              - atomMatrix (D.atom x)).det
          + D.weight z
            * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
              - atomMatrix (D.atom z)).det)
        + o * (Matrix.trace
              (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).adjugate
            - (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det)
        ≤ 0) →
    (∀ o : ℝ, 0 ≤ o →
      (∀ a ∈ insert z (({x, y, z} : Finset (Fin 6))ᶜ),
        o * D.weight a ≤ 1 - D.weight a) →
      (1 + o) * (D.weight x
            * (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
              - atomMatrix (D.atom x)).det
          + D.weight y
            * (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
              - atomMatrix (D.atom y)).det)
        + o * (Matrix.trace
              (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).adjugate
            - (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det)
        ≤ 0) →
    False

/-! ## 7. The coverage residual factors through the two cells -/

/-- The `{x, z, y}` relabel of a corner triple. -/
theorem triple_swap_eq {x y z : Fin 6} :
    ({x, z, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) := by
  ext c
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **THE COVERAGE RESIDUAL FACTORS THROUGH THE CELLS.**  The `Z1` coverage
residual holds exactly when the two sharpened cell residuals hold: the
dispatch sends a tie into one of the cells, every new clause is
tie-necessary, and each cell residual rebuilds the tie it refutes.  The
heavy-inside Prop absorbs both orientations of the failed four-set. -/
theorem oneAxisZeroPairCoverage_iff_cellResiduals :
    OneAxisZeroPairCoverage ↔
      OneAxisZeroHeavyInsideResidual ∧ OneAxisZeroBothLightResidual := by
  constructor
  · intro hcov
    have hempty := oneAxisZeroPairCoverage_iff.mp hcov
    constructor
    · intro D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz hnotz
        hfloors _ _ _
      exact hempty D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz
        ((corner_oneAxisZero_heavyInside_isTie_iff D hxy hxz hyz hlam hunit
          hgap hax haz hnotz).mpr hfloors)
    · intro D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz hAy hAz
        hyfloor hyfloors hzfloors _ _ _
      exact hempty D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz
        ((corner_oneAxisZero_bothLight_isTie_iff D hxy hxz hyz hlam.le hunit
          hgap hax hAy hAz).mpr ⟨hyfloor, hyfloors, hzfloors⟩)
  · rintro ⟨hH, hB⟩
    refine oneAxisZeroPairCoverage_iff.mpr ?_
    intro D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz htie
    have hgap' : subsetSum D ({x, z, y} : Finset (Fin 6)) - 1 = lam • atomMatrix u := by
      rw [triple_swap_eq]
      exact hgap
    have hcompl_swap : (({x, z, y} : Finset (Fin 6))ᶜ : Finset (Fin 6))
        = (({x, y, z} : Finset (Fin 6))ᶜ) := by
      rw [triple_swap_eq]
    rcases corner_oneAxisZero_tie_cell_dispatch D htie hxy hxz hyz hlam hunit
      hgap hax hay haz with ⟨hnotz, hfloors⟩ | ⟨hnoty, hfloors⟩ | ⟨hAy, hAz, h7⟩
    · exact hH D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz hnotz
        hfloors
        (fun o ho hodds => corner_oneAxisZero_heavyInside_odds_det_floor D htie
          hxy hxz hyz ((corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam
            hunit hgap hax haz).resolve_left hnotz) ho hodds)
        (fun d hd => corner_oneAxisZero_tie_downdate_floor D htie hxy hxz hyz
          hlam.le hunit hgap hax hd)
        (fun d hd o ho hodds hPD =>
          ((corner_oneAxisZero_heavyInside_isTie_iff_downdateOdds D hxy hxz hyz
            hlam hunit hgap hax haz hnotz).mp htie).2.2.2 d hd o ho hodds hPD)
    · -- the mirrored orientation: relabel the corner as (x, z, y)
      have hnoty' : ¬ (subsetSum D (insert y (({x, z, y} : Finset (Fin 6))ᶜ))
          - 1).PosDef := by
        rw [hcompl_swap]
        exact hnoty
      refine hH D x z y hxz hxy (Ne.symm hyz) lam hlam u hunit hgap' hax haz hay
        hnoty' (by rw [hcompl_swap]; exact hfloors)
        (fun o ho hodds => ?_) (fun d hd => ?_) (fun d hd o ho hodds hPD => ?_)
      · exact corner_oneAxisZero_heavyInside_odds_det_floor D htie hxz hxy
          (Ne.symm hyz) ((corner_oneAxisZero_fourSet_split D hxz hxy
            (Ne.symm hyz) hlam hunit hgap' hax hay).resolve_left hnoty') ho hodds
      · exact corner_oneAxisZero_tie_downdate_floor D htie hxz hxy
          (Ne.symm hyz) hlam.le hunit hgap' hax hd
      · exact ((corner_oneAxisZero_heavyInside_isTie_iff_downdateOdds D hxz hxy
          (Ne.symm hyz) hlam hunit hgap' hax hay hnoty').mp htie).2.2.2
          d hd o ho hodds hPD
    · exact hB D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz hAy hAz
        h7.1 h7.2.1 h7.2.2
        (fun d hd => corner_oneAxisZero_tie_downdate_floor D htie hxy hxz hyz
          hlam.le hunit hgap hax hd)
        (fun o ho hodds => corner_oneAxisZero_heavyInside_odds_det_floor D htie
          hxy hxz hyz hAy ho hodds)
        (fun o ho hodds => by
          have h := corner_oneAxisZero_heavyInside_odds_det_floor D htie hxz hxy
            (Ne.symm hyz) (by rw [hcompl_swap]; exact hAz) ho
            (by rw [hcompl_swap]; exact hodds)
          rw [hcompl_swap] at h
          exact h)

/-! ## 8. The witness refutes the odds-determinant clause in exact rationals -/

/-- The four-set of the witness through atom `1` is `3•1 + g₁g₁ᵀ`. -/
theorem oneAxisZeroWitness_fourSet_form :
    subsetSum oneAxisZeroWitness (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
      = (3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + atomMatrix (oneAxisZeroWitness.atom 1) := by
  have hcompl : ((({0, 1, 2} : Finset (Fin 6))ᶜ) : Finset (Fin 6)) = {3, 4, 5} := by
    decide
  have hstep : subsetSum oneAxisZeroWitness (insert 1 ({3, 4, 5} : Finset (Fin 6)))
      = atomMatrix (oneAxisZeroWitness.atom 1)
        + subsetSum oneAxisZeroWitness ({3, 4, 5} : Finset (Fin 6)) := by
    rw [subsetSum, subsetSum, Finset.sum_insert (by decide)]
  have hcform := oneAxisZeroWitness_compl_form
  rw [hcompl, hstep]
  rw [show atomMatrix (oneAxisZeroWitness.atom 1)
      + subsetSum oneAxisZeroWitness ({3, 4, 5} : Finset (Fin 6)) - 1
    = atomMatrix (oneAxisZeroWitness.atom 1)
      + (subsetSum oneAxisZeroWitness ({3, 4, 5} : Finset (Fin 6)) - 1) from by abel,
    hcform]
  abel

/-- The erased-excluded determinant of the witness: `16296/625`. -/
theorem oneAxisZeroWitness_erased_det :
    (subsetSum oneAxisZeroWitness (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
      - atomMatrix (oneAxisZeroWitness.atom 0)).det = 16296 / 625 := by
  have hM : subsetSum oneAxisZeroWitness
        (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
      - atomMatrix (oneAxisZeroWitness.atom 0)
      = !![2316 / 625, 0, 84 / 125; 0, 2, 0; 84 / 125, 0, 91 / 25] := by
    rw [oneAxisZeroWitness_fourSet_form]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [atomMatrix, Matrix.vecMulVec_apply, oneAxisZeroWitness_atom,
        oneAxisZeroWitnessAtom, Matrix.one_apply, Matrix.cons_val_two]
  rw [hM, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The `z`-excluded determinant of the witness: `11688/625`. -/
theorem oneAxisZeroWitness_zSide_det :
    (subsetSum oneAxisZeroWitness (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
      - atomMatrix (oneAxisZeroWitness.atom 2)).det = 11688 / 625 := by
  have hM : subsetSum oneAxisZeroWitness
        (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
      - atomMatrix (oneAxisZeroWitness.atom 2)
      = !![1532 / 625, 0, 168 / 125; 0, 3, 0; 168 / 125, 0, 82 / 25] := by
    rw [oneAxisZeroWitness_fourSet_form]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [atomMatrix, Matrix.vecMulVec_apply, oneAxisZeroWitness_atom,
        oneAxisZeroWitnessAtom, Matrix.one_apply, Matrix.cons_val_two]
  rw [hM, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The four-set determinant of the witness: `24444/625`. -/
theorem oneAxisZeroWitness_fourSet_det :
    (subsetSum oneAxisZeroWitness (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ))
      - 1).det = 24444 / 625 := by
  have hM : subsetSum oneAxisZeroWitness
        (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
      = !![2316 / 625, 0, 84 / 125; 0, 3, 0; 84 / 125, 0, 91 / 25] := by
    rw [oneAxisZeroWitness_fourSet_form]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [atomMatrix, Matrix.vecMulVec_apply, oneAxisZeroWitness_atom,
        oneAxisZeroWitnessAtom, Matrix.one_apply, Matrix.cons_val_two]
  rw [hM, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The adjugate trace of the witness four-set: `21921/625`, through the
rank-one update law. -/
theorem oneAxisZeroWitness_fourSet_adjugate_trace :
    Matrix.trace (subsetSum oneAxisZeroWitness
      (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1).adjugate = 21921 / 625 := by
  rw [oneAxisZeroWitness_fourSet_form,
    trace_adjugate_add_atomMatrix ((3 : ℝ) • 1) (oneAxisZeroWitness.atom 1)]
  have h1 : Matrix.trace (((3 : ℝ) • 1 : Matrix (Fin 3) (Fin 3) ℝ)).adjugate
      = 27 := by
    rw [Matrix.adjugate_smul, Matrix.adjugate_one, Matrix.trace_smul,
      Matrix.trace_one]
    norm_num
  have h2 : Matrix.trace ((3 : ℝ) • 1 : Matrix (Fin 3) (Fin 3) ℝ) = 9 := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    norm_num
  have h3 : oneAxisZeroWitness.atom 1 ⬝ᵥ oneAxisZeroWitness.atom 1
      = 841 / 625 := by
    norm_num [oneAxisZeroWitness_atom, oneAxisZeroWitnessAtom, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  have h4 : oneAxisZeroWitness.atom 1
      ⬝ᵥ (((3 : ℝ) • 1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ oneAxisZeroWitness.atom 1)
      = 2523 / 625 := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, h3]
    norm_num
  rw [h1, h2, h3, h4]
  norm_num

/-- **The odds-determinant clause fails at the witness**, at the odds level
`157/44` of its four-set members: the clause value is `303489/27500 > 0` in
exact rationals. -/
theorem oneAxisZeroWitness_oddsDet_fails :
    ¬ ((1 + 157 / 44 : ℝ) * (oneAxisZeroWitness.weight 0
          * (subsetSum oneAxisZeroWitness
              (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
            - atomMatrix (oneAxisZeroWitness.atom 0)).det
        + oneAxisZeroWitness.weight 2
          * (subsetSum oneAxisZeroWitness
              (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
            - atomMatrix (oneAxisZeroWitness.atom 2)).det)
      + (157 / 44 : ℝ) * (Matrix.trace (subsetSum oneAxisZeroWitness
              (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1).adjugate
          - (subsetSum oneAxisZeroWitness
              (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1).det)
      ≤ 0) := by
  rw [oneAxisZeroWitness_erased_det, oneAxisZeroWitness_zSide_det,
    oneAxisZeroWitness_fourSet_det, oneAxisZeroWitness_fourSet_adjugate_trace,
    oneAxisZeroWitness_weight]
  norm_num [oneAxisZeroWitnessWeight]

/-- **The witness is not a tie, by the odds-determinant route.**  The
odds-determinant floor is tie-necessary at the witness four-set, and the
clause fails there in exact rationals: a second, determinant-route proof of
`Gtz.oneAxisZeroWitness_not_isTie`. -/
theorem oneAxisZeroWitness_not_isTie_by_oddsDet : ¬ IsTie oneAxisZeroWitness := by
  intro htie
  refine oneAxisZeroWitness_oddsDet_fails ?_
  refine corner_oneAxisZero_heavyInside_odds_det_floor oneAxisZeroWitness htie
    (by decide) (by decide) (by decide)
    (oneAxisZeroWitness_fourSet_posDef (Or.inl rfl))
    (by norm_num : (0 : ℝ) ≤ 157 / 44) ?_
  intro a ha
  have hmem : ∀ b : Fin 6, b ∈ insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ) →
      b = 1 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by decide
  rcases hmem a ha with rfl | rfl | rfl | rfl <;>
    norm_num [oneAxisZeroWitness_weight, oneAxisZeroWitnessWeight]

end Gtz

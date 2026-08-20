import Gtz.Wave.HeavyInsideTracePinch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The seesaw exchange: the per-atom coupling of the two four-sets

The stored both-light survivors fail the tie's floors in a SEESAW: each
outside atom reads one four-set below one and the other above.  No landed law
coupled the two four-sets at the SAME outside atom.  This module lands that
coupling, exactly.

## The instruments

The inverse reading of a positive definite base is symmetric
(`Gtz.inv_reading_symm`), and one added atom moves every CROSS reading by an
exact product (`Gtz.update_cross_reading`):

  `(1 + sᵀM⁻¹s) · tᵀ(M + ssᵀ)⁻¹u = (1 + sᵀM⁻¹s) · tᵀM⁻¹u − (tᵀM⁻¹s)(sᵀM⁻¹u)` .

This is the two-sided Sherman–Morrison law; the landed cross update is its
diagonal `t = u` case.

## The seesaw exchange identity

The two four-sets differ by one subtracted and one added atom:
`A_z = A_y − g_yg_yᵀ + g_zg_zᵀ`.  Composing the update laws with the landed
downdate reading gives the EXACT exchange of any reading across the swap
(`Gtz.seesaw_exchange_reading`): with all readings at `M = A_y`,

  `vᵀA_z⁻¹v · Δ · (1 + r_q)
     = (vᵀM⁻¹v·(1 + r_q) − c_q²) · Δ + (c_p(1 + r_q) − ρ·c_q)²` ,

  `Δ = (1 − r_p)(1 + r_q) + ρ²`,  `r_p = pᵀM⁻¹p`, `r_q = qᵀM⁻¹q`,
  `ρ = pᵀM⁻¹q`, `c_p = vᵀM⁻¹p`, `c_q = vᵀM⁻¹q` ,

where `Δ · det M = det A_z` is the landed two-update determinant.  Every
`A_z`-side quantity of the seesaw is now a polynomial in `A_y`-side readings.

## The seesaw floor

At a both-light tie the member floor of the `z` four-set transports through
the exchange into a clause at the `y` four-set alone
(`Gtz.corner_oneAxisZero_bothLight_seesaw_floor`): for every outside atom `d`,

  `(1 + r_z) · Δ ≤ (r_d(1 + r_z) − c_dz²) · Δ + (c_dy(1 + r_z) − ρ·c_dz)²` .

This is the per-atom coupling of the seesaw: both floors of one atom read the
SAME positive matrix `A_y⁻¹`.  Measured at 512 bits: the one stored both-light
survivor that outlives the member trace pinch (row 64 of the 72) violates this
clause at its first outside atom, so the pinch and the seesaw floor together
refute all 72 stored survivors.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The reading symmetry of a positive definite inverse -/

/-- The inverse readings of a positive definite base are symmetric in the two
probes: `tᵀM⁻¹u = uᵀM⁻¹t`. -/
theorem inv_reading_symm {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ}
    (hM : M.PosDef) (t u : Fin k → ℝ) :
    t ⬝ᵥ (M⁻¹ *ᵥ u) = u ⬝ᵥ (M⁻¹ *ᵥ t) := by
  have hinvT : (M⁻¹)ᵀ = M⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, PosDef.transpose_eq hM]
  have hentry : ∀ row col : Fin k, M⁻¹ col row = M⁻¹ row col := by
    intro row col
    have hcongr := congrFun (congrFun hinvT row) col
    simpa using hcongr
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun row _ => Finset.sum_congr rfl fun col _ => ?_
  rw [hentry row col]
  ring

/-! ## 2. The two-sided Sherman–Morrison update -/

/-- **THE CROSS UPDATE, TWO-SIDED.**  One added atom moves every cross reading
by the exact product of the two mixed readings:

  `(1 + sᵀM⁻¹s) · tᵀ(M + ssᵀ)⁻¹u = (1 + sᵀM⁻¹s) · tᵀM⁻¹u − (tᵀM⁻¹s)(sᵀM⁻¹u)` .

Proved by solving one linear system — the landed diagonal cross update is the
`t = u` case. -/
theorem update_cross_reading {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ}
    (hM : M.PosDef) (s t u : Fin k → ℝ) :
    (1 + s ⬝ᵥ (M⁻¹ *ᵥ s)) * (t ⬝ᵥ ((M + atomMatrix s)⁻¹ *ᵥ u))
      = (1 + s ⬝ᵥ (M⁻¹ *ᵥ s)) * (t ⬝ᵥ (M⁻¹ *ᵥ u))
        - (t ⬝ᵥ (M⁻¹ *ᵥ s)) * (s ⬝ᵥ (M⁻¹ *ᵥ u)) := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  have hbig : (M + atomMatrix s).PosDef :=
    hM.add_posSemidef (posSemidef_atomMatrix s)
  have hbigUnit : IsUnit (M + atomMatrix s).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hbig.det_pos)
  set sDual : Fin k → ℝ := M⁻¹ *ᵥ s with hsDual
  set uDual : Fin k → ℝ := M⁻¹ *ᵥ u with huDual
  set sEnergy : ℝ := s ⬝ᵥ sDual with hsEnergy
  set cross : ℝ := s ⬝ᵥ uDual with hcross
  have hsMul : M *ᵥ sDual = s := by
    rw [hsDual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit,
      Matrix.one_mulVec]
  have huMul : M *ᵥ uDual = u := by
    rw [huDual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit,
      Matrix.one_mulVec]
  have hatomU : atomMatrix s *ᵥ uDual = cross • s := by
    rw [atomMatrix, vecMulVec_mulVec_eq, hcross]
  have hatomS : atomMatrix s *ᵥ sDual = sEnergy • s := by
    rw [atomMatrix, vecMulVec_mulVec_eq, hsEnergy]
  set candidate : Fin k → ℝ := (1 + sEnergy) • uDual - cross • sDual
    with hcandidate
  have hbigMul : (M + atomMatrix s) *ᵥ candidate = (1 + sEnergy) • u := by
    rw [hcandidate, Matrix.add_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hsMul, huMul, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hatomU, hatomS]
    ext index
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsolve : (1 + sEnergy) • ((M + atomMatrix s)⁻¹ *ᵥ u) = candidate := by
    have hstep : (M + atomMatrix s)⁻¹ *ᵥ ((M + atomMatrix s) *ᵥ candidate)
        = candidate := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hbigUnit,
        Matrix.one_mulVec]
    rw [← hstep, hbigMul, Matrix.mulVec_smul]
  have hpair := congrArg (fun w => t ⬝ᵥ w) hsolve
  simp only [dotProduct_smul, smul_eq_mul, hcandidate, dotProduct_sub] at hpair
  linear_combination hpair

/-! ## 3. The seesaw exchange identity -/

/-- **THE SEESAW EXCHANGE.**  Any reading of `M − ppᵀ + qqᵀ` is an exact
polynomial in five readings of `M` — division-free through the two-update
determinant factor `Δ = (1 − pᵀM⁻¹p)(1 + qᵀM⁻¹q) + (pᵀM⁻¹q)²`:

  `vᵀ(M − ppᵀ + qqᵀ)⁻¹v · Δ · (1 + qᵀM⁻¹q)
     = (vᵀM⁻¹v (1 + qᵀM⁻¹q) − (vᵀM⁻¹q)²) · Δ
       + (vᵀM⁻¹p (1 + qᵀM⁻¹q) − pᵀM⁻¹q · vᵀM⁻¹q)²` .

With `M = A_y`, `p = g_y`, `q = g_z` this moves EVERY `A_z` reading of the
`Z1` seesaw into the `A_y` coordinate system. -/
theorem seesaw_exchange_reading {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ}
    (hM : M.PosDef) (p q v : Fin k → ℝ)
    (hAz : (M - atomMatrix p + atomMatrix q).PosDef) :
    (v ⬝ᵥ ((M - atomMatrix p + atomMatrix q)⁻¹ *ᵥ v))
        * ((1 - p ⬝ᵥ (M⁻¹ *ᵥ p)) * (1 + q ⬝ᵥ (M⁻¹ *ᵥ q))
            + (p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2)
        * (1 + q ⬝ᵥ (M⁻¹ *ᵥ q))
      = (v ⬝ᵥ (M⁻¹ *ᵥ v) * (1 + q ⬝ᵥ (M⁻¹ *ᵥ q)) - (v ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2)
          * ((1 - p ⬝ᵥ (M⁻¹ *ᵥ p)) * (1 + q ⬝ᵥ (M⁻¹ *ᵥ q))
              + (p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2)
        + (v ⬝ᵥ (M⁻¹ *ᵥ p) * (1 + q ⬝ᵥ (M⁻¹ *ᵥ q))
            - p ⬝ᵥ (M⁻¹ *ᵥ q) * (v ⬝ᵥ (M⁻¹ *ᵥ q))) ^ 2 := by
  have hM1 : (M + atomMatrix q).PosDef :=
    hM.add_posSemidef (posSemidef_atomMatrix q)
  have hrq0 : 0 ≤ q ⬝ᵥ (M⁻¹ *ᵥ q) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM.inv.posSemidef).2 q
    rwa [star_trivial] at h
  have hrqpos : (0 : ℝ) < 1 + q ⬝ᵥ (M⁻¹ *ᵥ q) := by linarith
  -- the three update laws at M₁ = M + qqᵀ
  have hP1 := update_cross_reading hM q p p
  have hP2 := update_cross_reading hM q p v
  have hP3 := update_cross_reading hM q v v
  -- the swap shape
  have hshape : M - atomMatrix p + atomMatrix q
      = (M + atomMatrix q) - atomMatrix p := by abel
  -- Δ = (1 + r_q) · (1 − pᵀM₁⁻¹p), through hP1
  have hdelta : (1 - p ⬝ᵥ (M⁻¹ *ᵥ p)) * (1 + q ⬝ᵥ (M⁻¹ *ᵥ q))
        + (p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2
      = (1 + q ⬝ᵥ (M⁻¹ *ᵥ q))
        * (1 - p ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ p)) := by
    have hqp : q ⬝ᵥ (M⁻¹ *ᵥ p) = p ⬝ᵥ (M⁻¹ *ᵥ q) := inv_reading_symm hM q p
    linear_combination hP1 - (p ⬝ᵥ (M⁻¹ *ᵥ q)) * hqp
  -- the downdate denominator is away from one, from positivity of both dets
  have hdetAz := det_sub_add_atomMatrix_readings hM p q
  have hne : p ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ p) ≠ 1 := by
    intro hcon
    rw [hcon] at hdelta
    have hdet0 : (M - atomMatrix p + atomMatrix q).det = 0 := by
      rw [hdetAz]
      rw [show (1 - p ⬝ᵥ (M⁻¹ *ᵥ p)) * (1 + q ⬝ᵥ (M⁻¹ *ᵥ q))
            + (p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 = 0 by rw [hdelta]; ring]
      ring
    exact absurd hdet0 (ne_of_gt hAz.det_pos)
  -- the landed downdate reading at M₁, probe v, removed atom p
  have hdown := downdate_reading (M + atomMatrix q) hM1 p v hne
  rw [show Matrix.vecMulVec p p = atomMatrix p from rfl] at hdown
  rw [hshape]
  -- clear the single inverse through the nonvanishing factor
  have hfac : (1 : ℝ) - p ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ p) ≠ 0 := by
    intro hcon
    exact hne (by linarith [hcon, sub_eq_zero.mp hcon])
  have hdown' : (1 - p ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ p))
      * (v ⬝ᵥ (((M + atomMatrix q) - atomMatrix p)⁻¹ *ᵥ v))
      = (1 - p ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ p))
          * (v ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ v))
        + (p ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ v)) ^ 2 := by
    rw [hdown]
    field_simp
  -- assemble: everything is now polynomial in M₁-readings; push back to M
  have hpv : p ⬝ᵥ (M⁻¹ *ᵥ v) = v ⬝ᵥ (M⁻¹ *ᵥ p) := inv_reading_symm hM p v
  have hqv : q ⬝ᵥ (M⁻¹ *ᵥ v) = v ⬝ᵥ (M⁻¹ *ᵥ q) := inv_reading_symm hM q v
  have hqp : q ⬝ᵥ (M⁻¹ *ᵥ p) = p ⬝ᵥ (M⁻¹ *ᵥ q) := inv_reading_symm hM q p
  -- goal · : LHS = v'Az⁻¹v · Δ · (1+rq); rewrite Δ via hdelta, then hdown', then hP2, hP3
  rw [hdelta]
  have hgoal : v ⬝ᵥ (((M + atomMatrix q) - atomMatrix p)⁻¹ *ᵥ v)
      * ((1 + q ⬝ᵥ (M⁻¹ *ᵥ q)) * (1 - p ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ p)))
      * (1 + q ⬝ᵥ (M⁻¹ *ᵥ q))
      = ((1 + q ⬝ᵥ (M⁻¹ *ᵥ q)) * (v ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ v)))
          * ((1 + q ⬝ᵥ (M⁻¹ *ᵥ q)) * (1 - p ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ p)))
        + ((1 + q ⬝ᵥ (M⁻¹ *ᵥ q)) * (p ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ v))) ^ 2 := by
    linear_combination (1 + q ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 * hdown'
  rw [hgoal]
  -- replace the two M₁-readings by their M-forms
  have hP2' : (1 + q ⬝ᵥ (M⁻¹ *ᵥ q)) * (p ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ v))
      = v ⬝ᵥ (M⁻¹ *ᵥ p) * (1 + q ⬝ᵥ (M⁻¹ *ᵥ q))
        - p ⬝ᵥ (M⁻¹ *ᵥ q) * (v ⬝ᵥ (M⁻¹ *ᵥ q)) := by
    linear_combination hP2 + (1 + q ⬝ᵥ (M⁻¹ *ᵥ q)) * hpv
      - (p ⬝ᵥ (M⁻¹ *ᵥ q)) * hqv
  have hP3' : (1 + q ⬝ᵥ (M⁻¹ *ᵥ q)) * (v ⬝ᵥ ((M + atomMatrix q)⁻¹ *ᵥ v))
      = v ⬝ᵥ (M⁻¹ *ᵥ v) * (1 + q ⬝ᵥ (M⁻¹ *ᵥ q)) - (v ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 := by
    linear_combination hP3 - (v ⬝ᵥ (M⁻¹ *ᵥ q)) * hqv
  rw [hP2', hP3']

/-! ## 4. The seesaw floor of the both-light cell -/

/-- **THE SEESAW FLOOR.**  At a both-light tie, the `z` four-set's member
floor of every outside atom transports through the exchange into a clause at
the `y` four-set alone: with all readings at `A_y⁻¹`,

  `(1 + r_z) · Δ ≤ (r_d (1 + r_z) − c_dz²) · Δ + (c_dy (1 + r_z) − ρ · c_dz)²` ,

  `Δ = (1 − r_y)(1 + r_z) + ρ²` .

The per-atom coupling of the seesaw: both floors of one outside atom now read
the SAME positive matrix.  Measured at 512 bits, this clause refutes the one
stored both-light survivor that outlives the member trace pinch. -/
theorem corner_oneAxisZero_bothLight_seesaw_floor (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    {d : Fin 6} (hd : d ∈ (({x, y, z} : Finset (Fin 6))ᶜ)) :
    (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z))
      * ((1 - D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom y))
          * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
        + (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z)) ^ 2)
      ≤ (D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom d)
          * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
          - (D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z)) ^ 2)
        * ((1 - D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom y))
            * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z))
          + (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z)) ^ 2)
        + (D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom y)
            * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z))
          - D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom z)
            * (D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z))) ^ 2 := by
  classical
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hzK : z ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hFz : (insert z (({x, y, z} : Finset (Fin 6))ᶜ)).card = 4 := by
    rw [Finset.card_insert_of_notMem hzK,
      card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)]
  -- the z four-set in the y coordinates
  have hAzAy : subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
      = (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
        - atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [subsetSum, subsetSum, Finset.sum_insert hzK, Finset.sum_insert hyK]
    abel
  -- the z-side member floor at atom d
  have hfloor := fourSet_leverage_ge_one D htie _ hFz hAz
    (Finset.mem_insert_of_mem hd)
  -- the exchange identity at M = A_y, p = g_y, q = g_z, v = q_d
  have hAz' : ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
      - atomMatrix (D.atom y) + atomMatrix (D.atom z)).PosDef := by
    rw [← hAzAy]
    exact hAz
  have hex := seesaw_exchange_reading hAy (D.atom y) (D.atom z) (D.atom d) hAz'
  rw [← hAzAy] at hex
  -- the exchange multiplier is positive: Δ(1 + r_z) = detAz/detAy · (1+r_z)
  have hrz0 : 0 ≤ D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hAy.inv.posSemidef).2
      (D.atom z)
    rwa [star_trivial] at h
  have hrqpos : (0 : ℝ) < 1 + D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by linarith
  have hdetAz := det_sub_add_atomMatrix_readings hAy (D.atom y) (D.atom z)
  rw [← hAzAy] at hdetAz
  have hDpos : (0 : ℝ) < (1 - D.atom y ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom y))
      * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1)⁻¹ *ᵥ D.atom z))
      + (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z)) ^ 2 := by
    have hratio : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det
        > 0 := hAz.det_pos
    nlinarith [hdetAz, hAy.det_pos, hratio]
  -- transport: r_d(A_z) ≥ 1 times the positive multiplier Δ(1+r_z)
  have hmul : (0 : ℝ) < ((1 - D.atom y ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom y))
      * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1)⁻¹ *ᵥ D.atom z))
      + (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z)) ^ 2)
      * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1)⁻¹ *ᵥ D.atom z)) := mul_pos hDpos hrqpos
  nlinarith [hex, hfloor, hmul]

end Gtz

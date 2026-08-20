import Gtz.Wave.ErasedAtomSpectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The dual-frame budget

The ambient transverse floor prices the both-light cell in the energies of
the dual frame `w_d = Mo⁻¹g_d` of the outside triple.  This module lands
the conservation laws of that frame, and collapses the floor onto five
dual scalars.

* `Gtz.trace_mul_atomMatrix` — a reading is a trace.
* `Gtz.dual_frame_energy_trace` — THE DUAL TRACE LAW: for EVERY matrix
  `B`, the total `B`-energy of the dual frame is `tr(B·Mo⁻¹)`.  One law,
  every consumer: the four-set gaps of cell B, the `Δ`-arena of cell H,
  and any future functional of the outside dual frame.
* `Gtz.dual_frame_parseval` — the dual frame resolves `Mo⁻¹`: for every
  probe `v`, `Σ_d (v·w_d)² = vᵀMo⁻¹v`.
* `Gtz.dual_reading_total` — `Σ_d g_dᵀMo⁻¹g_d = 3`, exactly.
* `Gtz.fourSet_dual_energy_total` — at a four-set gap the total dual
  energy is pure dual data: `tr(A_s·Mo⁻¹) = q_s + 3 − tr(Mo⁻¹)`.
* `Gtz.corner_bothLight_dual_trace_floor` — THE DUAL-COLLAPSED FLOOR:
  on the both-light cell,

    `σ·(σ − tcap) ≤ t_y·(q_y + 3 − tr Mo⁻¹ − Σ_d 1/r^y_d)
                    + t_z·(q_z + 3 − tr Mo⁻¹ − Σ_d 1/r^z_d)` ,

  a law in the two inside dual readings, one trace, the six floors and
  the weights.  The degeneration penalty `−tr(Mo⁻¹)` is the exact
  currency in which outside collapse must pay.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The dual trace law -/

/-- **THE DUAL TRACE LAW.**  The total `B`-energy of the outside dual frame
`w_d = Mo⁻¹g_d` is one trace, for EVERY `B`:

  `Σ_d w_dᵀBw_d = tr(B·Mo⁻¹)` .

The dual frame resolves `Mo⁻¹` as a quadratic frame, so every quadratic
total collapses. -/
theorem dual_frame_energy_trace {m : ℕ} (D : WeightedDesign m 3)
    {d4 d5 d6 : Fin m} (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hMo : (subsetSum D ({d4, d5, d6} : Finset (Fin m))).PosDef)
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ j : Fin 3,
        ((subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹
            *ᵥ D.atom (![d4, d5, d6] j)) ⬝ᵥ
          (B *ᵥ ((subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹
            *ᵥ D.atom (![d4, d5, d6] j))))
      = Matrix.trace
          (B * (subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹) := by
  classical
  set Mo : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ({d4, d5, d6} : Finset (Fin m)) with hMoDef
  have hMoSum : Mo = atomMatrix (D.atom d4) + atomMatrix (D.atom d5)
      + atomMatrix (D.atom d6) := by
    rw [hMoDef, subsetSum, Finset.sum_insert (by simp [h45, h46]),
      Finset.sum_insert (by simp [h56]), Finset.sum_singleton]
    abel
  have hdetMo : IsUnit Mo.det := isUnit_iff_ne_zero.mpr
    (ne_of_gt hMo.det_pos)
  have hsym : (Mo⁻¹)ᵀ = Mo⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, transpose_eq_of_isHermitian hMo.1]
  have hterm : ∀ g : Fin 3 → ℝ,
      (Mo⁻¹ *ᵥ g) ⬝ᵥ (B *ᵥ (Mo⁻¹ *ᵥ g))
        = Matrix.trace (B * (Mo⁻¹ * atomMatrix g * Mo⁻¹)) := by
    intro g
    have hatom : Mo⁻¹ * atomMatrix g * Mo⁻¹ = atomMatrix (Mo⁻¹ *ᵥ g) := by
      rw [← congr_atomMatrix Mo⁻¹ g, hsym]
    rw [hatom, trace_mul_atomMatrix]
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  have hsum : Mo⁻¹ * atomMatrix (D.atom d4) * Mo⁻¹
      + Mo⁻¹ * atomMatrix (D.atom d5) * Mo⁻¹
      + Mo⁻¹ * atomMatrix (D.atom d6) * Mo⁻¹ = Mo⁻¹ := by
    rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add,
      ← Matrix.mul_add, ← hMoSum, Matrix.nonsing_inv_mul Mo hdetMo,
      Matrix.one_mul]
  rw [hterm, hterm, hterm, ← Matrix.trace_add, ← Matrix.trace_add,
    ← Matrix.mul_add, ← Matrix.mul_add, hsum]

/-- **THE DUAL PARSEVAL.**  The dual frame resolves the inverse outside
sum: for every probe, `Σ_d (v·w_d)² = vᵀMo⁻¹v`. -/
theorem dual_frame_parseval {m : ℕ} (D : WeightedDesign m 3)
    {d4 d5 d6 : Fin m} (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hMo : (subsetSum D ({d4, d5, d6} : Finset (Fin m))).PosDef)
    (v : Fin 3 → ℝ) :
    (∑ j : Fin 3,
        (v ⬝ᵥ ((subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹
          *ᵥ D.atom (![d4, d5, d6] j))) ^ 2)
      = v ⬝ᵥ ((subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹ *ᵥ v) := by
  have h := dual_frame_energy_trace D h45 h46 h56 hMo (atomMatrix v)
  have hterm : ∀ j : Fin 3,
      ((subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹
          *ᵥ D.atom (![d4, d5, d6] j)) ⬝ᵥ
        (atomMatrix v *ᵥ ((subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹
          *ᵥ D.atom (![d4, d5, d6] j)))
      = (v ⬝ᵥ ((subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹
          *ᵥ D.atom (![d4, d5, d6] j))) ^ 2 := by
    intro j
    rw [show atomMatrix v *ᵥ ((subsetSum D
        ({d4, d5, d6} : Finset (Fin m)))⁻¹ *ᵥ D.atom (![d4, d5, d6] j))
        = (v ⬝ᵥ ((subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹
            *ᵥ D.atom (![d4, d5, d6] j))) • v from
      vecMulVec_mulVec_eq _ _ _, dotProduct_smul, smul_eq_mul,
      dotProduct_comm]
    ring
  rw [Finset.sum_congr rfl (fun j _ => (hterm j).symm), h,
    Matrix.trace_mul_comm, trace_mul_atomMatrix]

/-- **THE DUAL READING TOTAL**: the three self dual readings of the outside
triple total exactly three. -/
theorem dual_reading_total {m : ℕ} (D : WeightedDesign m 3)
    {d4 d5 d6 : Fin m} (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hMo : (subsetSum D ({d4, d5, d6} : Finset (Fin m))).PosDef) :
    (∑ j : Fin 3,
        D.atom (![d4, d5, d6] j) ⬝ᵥ
          ((subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹
            *ᵥ D.atom (![d4, d5, d6] j)))
      = 3 := by
  classical
  set Mo : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ({d4, d5, d6} : Finset (Fin m)) with hMoDef
  have hMoSum : Mo = atomMatrix (D.atom d4) + atomMatrix (D.atom d5)
      + atomMatrix (D.atom d6) := by
    rw [hMoDef, subsetSum, Finset.sum_insert (by simp [h45, h46]),
      Finset.sum_insert (by simp [h56]), Finset.sum_singleton]
    abel
  have hdetMo : IsUnit Mo.det := isUnit_iff_ne_zero.mpr
    (ne_of_gt hMo.det_pos)
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [← trace_mul_atomMatrix, ← trace_mul_atomMatrix,
    ← trace_mul_atomMatrix, ← Matrix.trace_add, ← Matrix.trace_add,
    ← Matrix.mul_add, ← Matrix.mul_add, ← hMoSum,
    Matrix.nonsing_inv_mul Mo hdetMo, Matrix.trace_one]
  simp

/-! ## 3. The four-set dual energy total -/

/-- **THE FOUR-SET DUAL ENERGY TOTAL.**  The trace of a four-set gap
against `Mo⁻¹` is pure dual data:

  `tr(A_s·Mo⁻¹) = q_s + 3 − tr(Mo⁻¹)` ,

with `q_s` the inside dual reading of the inserted atom. -/
theorem fourSet_dual_energy_total {m : ℕ} (D : WeightedDesign m 3)
    {s d4 d5 d6 : Fin m}
    (hs : s ∉ ({d4, d5, d6} : Finset (Fin m)))
    (hMo : (subsetSum D ({d4, d5, d6} : Finset (Fin m))).PosDef) :
    Matrix.trace
        ((subsetSum D (insert s ({d4, d5, d6} : Finset (Fin m))) - 1)
          * (subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹)
      = D.atom s ⬝ᵥ ((subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹
            *ᵥ D.atom s)
        + 3
        - Matrix.trace (subsetSum D ({d4, d5, d6} : Finset (Fin m)))⁻¹ := by
  classical
  set Mo : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ({d4, d5, d6} : Finset (Fin m)) with hMoDef
  have hdetMo : IsUnit Mo.det := isUnit_iff_ne_zero.mpr
    (ne_of_gt hMo.det_pos)
  have hsplit : subsetSum D (insert s ({d4, d5, d6} : Finset (Fin m)))
      = atomMatrix (D.atom s) + Mo := by
    rw [hMoDef, subsetSum, subsetSum, Finset.sum_insert hs]
  rw [hsplit, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul,
    Matrix.trace_sub, Matrix.trace_add,
    Matrix.mul_nonsing_inv Mo hdetMo, Matrix.trace_one]
  have hread : Matrix.trace (atomMatrix (D.atom s) * Mo⁻¹)
      = D.atom s ⬝ᵥ (Mo⁻¹ *ᵥ D.atom s) := by
    rw [Matrix.trace_mul_comm, trace_mul_atomMatrix]
  rw [hread]
  simp

/-! ## 4. The dual-collapsed floor of the both-light cell -/

/-- **THE DUAL-COLLAPSED FLOOR.**  On the both-light cell the transverse
floor collapses onto five dual scalars:

  `σ·(σ − tcap) ≤ t_y·(q_y + 3 − tr Mo⁻¹ − Σ_d 1/r^y_d)
                  + t_z·(q_z + 3 − tr Mo⁻¹ − Σ_d 1/r^z_d)` .

The two inside dual readings fight the trace penalty of outside collapse:
as the outside triple degenerates, `tr(Mo⁻¹)` blows up, and the floors and
weights must pay for it through `q_y` and `q_z`. -/
theorem corner_bothLight_dual_trace_floor (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    (hMo : (subsetSum D ({d4, d5, d6} : Finset (Fin 6))).PosDef)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hyfloor : 1 ≤ D.atom y ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom y))
    (hfY : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d))
    (hfZ : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ
        ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d))
    {tcap : ℝ} (hc4 : D.weight d4 ≤ tcap) (hc5 : D.weight d5 ≤ tcap)
    (hc6 : D.weight d6 ≤ tcap) :
    (D.weight d4 + D.weight d5 + D.weight d6)
        * (D.weight d4 + D.weight d5 + D.weight d6 - tcap)
      ≤ D.weight y
          * ((D.atom y ⬝ᵥ ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
                *ᵥ D.atom y))
              + 3
              - Matrix.trace
                  (subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
              - ∑ j : Fin 3,
                  1 / (D.atom (![d4, d5, d6] j) ⬝ᵥ
                    ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                        - 1)⁻¹ *ᵥ D.atom (![d4, d5, d6] j))))
        + D.weight z
          * ((D.atom z ⬝ᵥ ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
                *ᵥ D.atom z))
              + 3
              - Matrix.trace
                  (subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
              - ∑ j : Fin 3,
                  1 / (D.atom (![d4, d5, d6] j) ⬝ᵥ
                    ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ))
                        - 1)⁻¹ *ᵥ D.atom (![d4, d5, d6] j)))) := by
  classical
  have hmain := corner_bothLight_transverse_floor D hxy hxz hyz h45 h46 h56
    hcompl hMo hAy hAz hxunit hyfloor hfY hfZ hc4 hc5 hc6
  have hynot : y ∉ ({d4, d5, d6} : Finset (Fin 6)) := by
    rw [← hcompl]
    simp
  have hznot : z ∉ ({d4, d5, d6} : Finset (Fin 6)) := by
    rw [← hcompl]
    simp
  have hAyEq : subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
      = subsetSum D (insert y ({d4, d5, d6} : Finset (Fin 6))) - 1 := by
    rw [hcompl]
  have hAzEq : subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
      = subsetSum D (insert z ({d4, d5, d6} : Finset (Fin 6))) - 1 := by
    rw [hcompl]
  have htotY := fourSet_dual_energy_total D hynot hMo
  have htotZ := fourSet_dual_energy_total D hznot hMo
  rw [← hAyEq] at htotY
  rw [← hAzEq] at htotZ
  have htrY := dual_frame_energy_trace D h45 h46 h56 hMo
    (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
  have htrZ := dual_frame_energy_trace D h45 h46 h56 hMo
    (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, htrY, htrZ,
    htotY, htotZ] at hmain
  exact hmain

end Gtz

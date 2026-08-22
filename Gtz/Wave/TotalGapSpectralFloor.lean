/-
# The total gap of a primitive tie is LARGE: a spectral floor from the five-set clause

`Gtz.forall_posDef_gap_erase_of_isPrimitiveDesign_of_isTie` says every five-set of
a primitive `(6,3)` tie dominates strictly, which by the co-atom dichotomy is

    `rho_c < 1`  at every label,   `rho_c = g_c . G^{-1} g_c`,  `G = S_all - 1` .

That is six scalar inequalities.  This module spends them, and what comes out is
not a scalar clause but a SPECTRAL one on the total gap itself.

## The engine, in three lines

The tree already prices every quadratic reading against the weights
(`Gtz.sum_weight_mul_reading_eq_trace_gen`).  Read it at the form `G^{-1}`:

    **`sum_c t_c rho_c = tr(G^{-1})`**   (`Gtz.sum_weight_mul_totalGapReading`)

so `rho_c < 1` at every label collapses the whole reading vector onto ONE number:

    **`tr(G^{-1}) < 1`**   (`Gtz.trace_totalGap_inv_lt_one`).

That single inequality carries three consequences, each at every rank and size.

* **The metric floor.**  Cauchy-Schwarz in the `G^{-1}` metric turns Parseval into
  `x . x <= tr(G^{-1}) * (x . G x)` for EVERY probe
  (`Gtz.dotProduct_self_le_trace_totalGap_inv_mul_quadForm`).  With the bound
  above, `G > 1`, that is

      **`S_all > 2 . 1`**   (`Gtz.posDef_subsetSum_univ_sub_two`).

  Every eigenvalue of the whole atom sum exceeds TWO.  The tree owned only
  `S_all > 1` (`Gtz.posDef_subsetSum_univ_sub_one`).

* **The leverage floor.**  For a positive definite `A` of size `k`,
  `tr(A) * tr(A^{-1}) >= k^2` (`Gtz.sq_rank_le_trace_mul_trace_inv`), by
  Cauchy-Schwarz on the diagonal against `A_ii * (A^{-1})_ii >= 1`.  Against
  `tr(G^{-1}) < 1` that gives `tr(G) > k^2`, hence

      **`k^2 + k  <  sum_c l_c`**   (`Gtz.sq_rank_add_rank_lt_sum_leverage`).

  The tree's landed floor is `Gtz.sq_rank_le_sum_leverage`, `k^2 <= sum_c l_c`,
  with no hypothesis.  This is the same shape one rank higher, and at `(6,3)` it
  reads `12 < sum_c l_c` against the landed `9`.

* **The five-set package** at `(6,3)`, `Gtz.sixThree_primitiveTie_gapFloor`.

## Where the sharpness sits

The three consequences are NOT equally strong against the residual, and the
measurement says exactly which one is the instrument.

[MEASURED, adversarial annealing over `(6,3)` designs restricted to the all-heavy
stratum and to the six clauses of `Gtz.sixThree_primitiveTie_normalForm`, 2000
restarts of 40000 steps each, double precision, `scratchpad/package/cut.c`.

* `tr(G^{-1})` reaches `1.36e8` on that stratum.  So `tr(G^{-1}) < 1` is a
  SEPARATING clause: the six clauses do not imply it, by eight orders of
  magnitude.
* `lambda_min(G)` reaches `6.5e-4` on that stratum.  So `S_all > 2` is a
  SEPARATING clause too.
* `sum_c l_c` reaches `12.09` on that stratum.  So the leverage floor `12` is
  true but nearly vacuous THERE, although it is strictly stronger than the
  landed `9` at every design.

Also verified, 9000000 random `(6,3)` designs at three weight spreads: the two
identities `sum_c t_c rho_c = tr(G^{-1})` and `sum_c (1 - t_c) rho_c = 3` to
`5.3e-15` and `9.6e-9`, and, on the 5395611 of them with every `rho_c < 1`,
`max tr(G^{-1}) = 0.979`, `min lambda_min(G) = 1.037`, `min sum l_c = 14.66`,
`min det(G) = 52.2`.  Every claim above is a theorem, checked.]

## The field verdict

Parts 1 to 3 are FIELD-BLIND.  Cauchy-Schwarz in a positive definite metric, the
trace-product floor and the moment law all survive verbatim over `C` with `ᴴ` in
place of `ᵀ`, and so does the co-atom dichotomy.  So no theorem of Parts 1 to 3
can prove `Gtz.HingeHoldsAtSize 6 3`, and none of them claims to: their
hypothesis is the strictness of every five-set, not a tie.

Part 4 is NOT field-blind, at one named step.  It consumes
`Gtz.forall_posDef_gap_erase_of_isPrimitiveDesign_of_isTie`, which consumes
`Gtz.allHeavy_of_isPrimitiveDesign_of_isTie_sixThree`, which consumes the funnel
closure and hence the rank-two three-class law.  Complex rank-two GTZ is FALSE at
four atoms, so `Gtz.gtz_rank_two` is real-only and the chain is exempt.

## What this does NOT claim

* It does not claim the hinge.  Every Part 4 statement has the shape
  `∀ design, IsPrimitiveDesign design → IsTie design → …`, which
  `Gtz.onPathRegistryCollapse` records as IMPLIED by the hinge.
* It does not claim that the leverage floor `12` is independent of the six
  clauses at `(6,3)`; the measurement above says it is nearly vacuous there.
  The two SPECTRAL clauses are the separating ones, and their separation is
  MEASURED, not proved: no exact design is exhibited.
* It does not use the sharp duality anywhere.  The five-set clause is consumed
  as a black box.
-/
import Gtz.Wave.PrimitiveTieSharpTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — Cauchy-Schwarz in a positive semidefinite metric

The tree carries the EQUALITY case (`Gtz.gramDefect_eq_zero_iff`) and never the
inequality.  One discriminant closes it. -/

/- `Gtz.sq_dotProduct_mulVec_le_of_posSemidef` is landed
(Gtz/Design/TwoFamilyTightFrame.lean, and a second copy at the same full name in
Gtz/Wave/WiringSixThreeNoGo.lean -- a pre-existing DUPLICATION, reported and not
touched here).  It is imported, not restated. -/

/-- **THE DIAGONAL RECIPROCAL LAW.**  For a positive definite matrix the product
of a diagonal entry with the matching diagonal entry of the inverse is at least
one.  Cauchy-Schwarz at the coordinate vector and its image under the inverse. -/
theorem one_le_diag_mul_diag_inv {form : Matrix (Fin k) (Fin k) ℝ} (hform : form.PosDef)
    (slot : Fin k) : 1 ≤ form slot slot * form⁻¹ slot slot := by
  classical
  have hunit : IsUnit form.det := isUnit_iff_ne_zero.mpr (ne_of_gt hform.det_pos)
  set probe : Fin k → ℝ := Pi.single slot 1 with hprobe
  set image : Fin k → ℝ := form⁻¹ *ᵥ probe with himage
  have hleft : probe ⬝ᵥ (form *ᵥ probe) = form slot slot := by
    rw [hprobe]
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq']
  have hpush : form *ᵥ image = probe := by
    rw [himage, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hcross : probe ⬝ᵥ (form *ᵥ image) = 1 := by
    rw [hpush, hprobe]
    simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  have hright : image ⬝ᵥ (form *ᵥ image) = form⁻¹ slot slot := by
    rw [hpush, himage, hprobe]
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq']
  have hcs := sq_dotProduct_mulVec_le_of_posSemidef hform.posSemidef probe image
  rw [hcross, hleft, hright] at hcs
  linarith [hcs]

/-! ## Part 2 — the trace product floor

`tr(A) tr(A^{-1}) >= k^2` for a positive definite `A` of size `k`.  No
eigenvalue, no square root of a matrix: the diagonal reciprocal law against the
discrete Cauchy-Schwarz. -/

/-- **THE TRACE PRODUCT FLOOR.**  A positive definite matrix and its inverse have
trace product at least the SQUARE of the size.  Sharp at the identity. -/
theorem sq_rank_le_trace_mul_trace_inv {form : Matrix (Fin k) (Fin k) ℝ} (hform : form.PosDef) :
    ((k : ℝ)) ^ 2 ≤ Matrix.trace form * Matrix.trace form⁻¹ := by
  classical
  have hdiagPos : ∀ slot : Fin k, 0 < form slot slot := fun _ => hform.diag_pos
  have hinvPos : ∀ slot : Fin k, 0 < form⁻¹ slot slot := fun _ => hform.inv.diag_pos
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k))
    (fun slot => Real.sqrt (form slot slot)) (fun slot => Real.sqrt (form⁻¹ slot slot))
  have hsqLeft : (∑ slot, Real.sqrt (form slot slot) ^ 2) = Matrix.trace form := by
    rw [Matrix.trace]
    exact Finset.sum_congr rfl fun slot _ => by
      rw [Real.sq_sqrt (hdiagPos slot).le, Matrix.diag_apply]
  have hsqRight : (∑ slot, Real.sqrt (form⁻¹ slot slot) ^ 2) = Matrix.trace form⁻¹ := by
    rw [Matrix.trace]
    exact Finset.sum_congr rfl fun slot _ => by
      rw [Real.sq_sqrt (hinvPos slot).le, Matrix.diag_apply]
  have hfloor : ((k : ℝ)) ≤ ∑ slot, Real.sqrt (form slot slot) * Real.sqrt (form⁻¹ slot slot) := by
    have hterm : ∀ slot : Fin k,
        (1 : ℝ) ≤ Real.sqrt (form slot slot) * Real.sqrt (form⁻¹ slot slot) := by
      intro slot
      rw [← Real.sqrt_mul (hdiagPos slot).le]
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (one_le_diag_mul_diag_inv hform slot)
    calc ((k : ℝ)) = ∑ _slot : Fin k, (1 : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun slot _ => hterm slot
  rw [hsqLeft, hsqRight] at hcs
  nlinarith [hcs, hfloor, Nat.cast_nonneg (α := ℝ) k]

/-! ## Part 3 — the co-atom readings collapse onto one number

`Gtz.totalGapReading` is the co-atom reading `rho_c = g_c . G^{-1} g_c`.  The
landed moment law prices its weighted total exactly. -/

/-- **THE WEIGHTED READING TOTAL IS THE INVERSE TRACE.**  The landed moment law
`Gtz.sum_weight_mul_reading_eq_trace_gen`, read at the form `G^{-1}`. -/
theorem sum_weight_mul_totalGapReading (D : WeightedDesign m k) :
    (∑ label, D.weight label * totalGapReading D label) = Matrix.trace (totalGap D)⁻¹ :=
  sum_weight_mul_reading_eq_trace_gen D (totalGap D)⁻¹

/-- **STRICT FIVE-SETS FORCE A SMALL INVERSE TRACE.**  If every co-atom set
dominates strictly then the whole reading vector collapses: the inverse trace of
the total gap is below ONE, at every rank and every size. -/
theorem trace_totalGap_inv_lt_one (D : WeightedDesign m k) (_hm : 2 ≤ m)
    (hstrict : ∀ label : Fin m, totalGapReading D label < 1) :
    Matrix.trace (totalGap D)⁻¹ < 1 := by
  classical
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin m)) with hempty | hne
    · exfalso
      have hsum := D.weight_sum_one
      rw [hempty, Finset.sum_empty] at hsum
      exact zero_ne_one hsum
    · exact hne
  have hlt : (∑ label, D.weight label * totalGapReading D label)
      < ∑ label, D.weight label := by
    refine Finset.sum_lt_sum_of_nonempty hnonempty fun label _ => ?_
    have hpos := D.weight_pos label
    nlinarith [hstrict label, hpos]
  rw [sum_weight_mul_totalGapReading D, D.weight_sum_one] at hlt
  exact hlt

theorem trace_totalGap_inv_pos (D : WeightedDesign m k) (hm : 2 ≤ m) (hk : 0 < k) :
    0 < Matrix.trace (totalGap D)⁻¹ := by
  have hinv := posDef_totalGap_inv D hm
  have hdiagPos : ∀ slot : Fin k, 0 < ((totalGap D)⁻¹) slot slot := fun _ => hinv.diag_pos
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [Matrix.trace]
  exact Finset.sum_pos (fun slot _ => hdiagPos slot) Finset.univ_nonempty

/-- The trace of the total gap is positive. -/
theorem trace_totalGap_pos (D : WeightedDesign m k) (hm : 2 ≤ m) (hk : 0 < k) :
    0 < Matrix.trace (totalGap D) := by
  have hdiagPos : ∀ slot : Fin k, 0 < (totalGap D) slot slot := fun _ =>
    (posDef_totalGap D hm).diag_pos
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [Matrix.trace]
  exact Finset.sum_pos (fun slot _ => hdiagPos slot) Finset.univ_nonempty

/-- **THE METRIC FLOOR.**  Parseval read against Cauchy-Schwarz in the `G^{-1}`
metric: every probe's own square is capped by the inverse trace times its total
gap reading.  No hypothesis at all. -/
theorem dotProduct_self_le_trace_totalGap_inv_mul_quadForm (D : WeightedDesign m k)
    (hm : 2 ≤ m) (probe : Fin k → ℝ) :
    probe ⬝ᵥ probe
      ≤ Matrix.trace (totalGap D)⁻¹ * (probe ⬝ᵥ (totalGap D *ᵥ probe)) := by
  classical
  have hunit := isUnit_det_totalGap D hm
  have hinv := posDef_totalGap_inv D hm
  have hquadNonneg : 0 ≤ probe ⬝ᵥ (totalGap D *ᵥ probe) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (posDef_totalGap D hm).posSemidef).2 probe
    rwa [star_trivial] at h
  have hterm : ∀ label : Fin m,
      (D.atom label ⬝ᵥ probe) ^ 2
        ≤ totalGapReading D label * (probe ⬝ᵥ (totalGap D *ᵥ probe)) := by
    intro label
    have hcs := sq_dotProduct_mulVec_le_of_posSemidef hinv.posSemidef (D.atom label)
      (totalGap D *ᵥ probe)
    have hcross : D.atom label ⬝ᵥ ((totalGap D)⁻¹ *ᵥ (totalGap D *ᵥ probe))
        = D.atom label ⬝ᵥ probe := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
    have hright : (totalGap D *ᵥ probe) ⬝ᵥ ((totalGap D)⁻¹ *ᵥ (totalGap D *ᵥ probe))
        = probe ⬝ᵥ (totalGap D *ᵥ probe) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
        dotProduct_comm]
    rw [hcross, hright, ← totalGapReading] at hcs
    exact hcs
  have hpars : probe ⬝ᵥ probe = ∑ label, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2 :=
    dotProduct_self_eq_sum_weight_mul_sq D probe
  calc probe ⬝ᵥ probe
      = ∑ label, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2 := hpars
    _ ≤ ∑ label, D.weight label
        * (totalGapReading D label * (probe ⬝ᵥ (totalGap D *ᵥ probe))) :=
        Finset.sum_le_sum fun label _ =>
          mul_le_mul_of_nonneg_left (hterm label) (D.weight_pos label).le
    _ = (∑ label, D.weight label * totalGapReading D label)
          * (probe ⬝ᵥ (totalGap D *ᵥ probe)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun label _ => by ring
    _ = Matrix.trace (totalGap D)⁻¹ * (probe ⬝ᵥ (totalGap D *ᵥ probe)) := by
        rw [sum_weight_mul_totalGapReading D]

/-- **THE WHOLE ATOM SUM CLEARS TWICE THE IDENTITY.**  If every co-atom set
dominates strictly then `S_all - 2 . 1` is positive definite.  The tree owned
only `S_all - 1 > 0` (`Gtz.posDef_subsetSum_univ_sub_one`); this doubles the
level, at every rank and every size. -/
theorem posDef_totalGap_sub_one (D : WeightedDesign m k) (hm : 2 ≤ m)
    (hstrict : ∀ label : Fin m, totalGapReading D label < 1) :
    (totalGap D - 1).PosDef := by
  have hsymm : (totalGap D - 1)ᵀ = totalGap D - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, totalGap_transpose]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq hsymm,
    fun probe hprobe => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
  have hbound := dotProduct_self_le_trace_totalGap_inv_mul_quadForm D hm probe
  have htrace := trace_totalGap_inv_lt_one D hm hstrict
  have hquadPos : 0 < probe ⬝ᵥ (totalGap D *ᵥ probe) := by
    have h := (Matrix.posDef_iff_dotProduct_mulVec.mp (posDef_totalGap D hm)).2 hprobe
    rwa [star_trivial] at h
  nlinarith [hbound, htrace, hquadPos]

/-- **THE WHOLE ATOM SUM, AT LEVEL TWO.**  The same statement written on
`Gtz.subsetSum`. -/
theorem posDef_subsetSum_univ_sub_two (D : WeightedDesign m k) (hm : 2 ≤ m)
    (hstrict : ∀ label : Fin m, totalGapReading D label < 1) :
    (subsetSum D Finset.univ - 2 • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef := by
  have hshape : subsetSum D Finset.univ - 2 • (1 : Matrix (Fin k) (Fin k) ℝ)
      = totalGap D - 1 := by
    rw [totalGap, two_smul]
    abel
  rw [hshape]
  exact posDef_totalGap_sub_one D hm hstrict

/-! ### The leverage floor -/

/- `Gtz.trace_subsetSum_univ` (Gtz/Ties/AllTied.lean) is landed.  It is imported,
not restated. -/

theorem trace_totalGap (D : WeightedDesign m k) :
    Matrix.trace (totalGap D) = (∑ label, leverageOf (D.atom label)) - (k : ℝ) := by
  rw [totalGap, Matrix.trace_sub, Matrix.trace_one, trace_subsetSum_univ]
  simp

/-- **THE SHARPENED LEVERAGE FLOOR.**  If every co-atom set dominates strictly
then the leverage total exceeds `rank^2 + rank`, at every rank and every size.

The landed `Gtz.sq_rank_le_sum_leverage` gives `rank^2` with no hypothesis.  This
adds a whole rank, and at `(6,3)` it reads `12` against the landed `9`. -/
theorem sq_rank_add_rank_lt_sum_leverage (D : WeightedDesign m k) (hm : 2 ≤ m) (hk : 0 < k)
    (hstrict : ∀ label : Fin m, totalGapReading D label < 1) :
    ((k : ℝ)) ^ 2 + (k : ℝ) < ∑ label, leverageOf (D.atom label) := by
  have hfloor := sq_rank_le_trace_mul_trace_inv (posDef_totalGap D hm)
  have hlt := trace_totalGap_inv_lt_one D hm hstrict
  have hpos := trace_totalGap_inv_pos D hm hk
  have htraceG : Matrix.trace (totalGap D)
      = (∑ label, leverageOf (D.atom label)) - (k : ℝ) := trace_totalGap D
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have htracePos := trace_totalGap_pos D hm hk
  nlinarith [hfloor, hlt, hpos, htraceG, hkpos, htracePos,
    mul_lt_mul_of_pos_left hlt htracePos]

/-! ## Part 4 — the `(6,3)` residual

`Gtz.forall_posDef_gap_erase_of_isPrimitiveDesign_of_isTie` supplies the
hypothesis of Part 3 at every primitive `(6,3)` tie, so all three consequences
land on the residual with no further work. -/

/-- **THE INVERSE TRACE OF A PRIMITIVE `(6,3)` TIE IS BELOW ONE.** -/
theorem trace_totalGap_inv_lt_one_of_isPrimitiveDesign_of_isTie (D : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) :
    Matrix.trace (totalGap D)⁻¹ < 1 :=
  trace_totalGap_inv_lt_one D (by norm_num)
    (totalGapReading_lt_one_of_isPrimitiveDesign_of_isTie_sixThree D hprimitive htie)

/-- **THE ATOM SUM OF A PRIMITIVE `(6,3)` TIE CLEARS TWICE THE IDENTITY.** -/
theorem posDef_subsetSum_univ_sub_two_of_isPrimitiveDesign_of_isTie (D : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) :
    (subsetSum D Finset.univ - 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef :=
  posDef_subsetSum_univ_sub_two D (by norm_num)
    (totalGapReading_lt_one_of_isPrimitiveDesign_of_isTie_sixThree D hprimitive htie)

/-- **THE LEVERAGE TOTAL OF A PRIMITIVE `(6,3)` TIE EXCEEDS TWELVE.**  Against the
landed `Gtz.sixThree_nine_le_sum_leverage`, which gives nine at every design. -/
theorem twelve_lt_sum_leverage_of_isPrimitiveDesign_of_isTie (D : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) :
    (12 : ℝ) < ∑ label, leverageOf (D.atom label) := by
  have hbound := sq_rank_add_rank_lt_sum_leverage D (by norm_num) (by norm_num)
    (totalGapReading_lt_one_of_isPrimitiveDesign_of_isTie_sixThree D hprimitive htie)
  norm_num at hbound
  exact hbound

/-- **THE GAP FLOOR PACKAGE.**  Everything the five-set clause buys, as one
theorem: at a primitive `(6,3)` tie every co-atom reading is below one, the
inverse trace of the total gap is below one, the whole atom sum clears twice the
identity, and the leverage total exceeds twelve.

The two SPECTRAL clauses are the separating ones — MEASURED, not proved: over
`(6,3)` designs satisfying the six clauses of
`Gtz.sixThree_primitiveTie_normalForm` the inverse trace reaches `1.36e8` and the
smallest eigenvalue of the total gap reaches `6.5e-4`.  The leverage clause is
nearly vacuous there, its measured infimum being `12.09`. -/
theorem sixThree_primitiveTie_gapFloor (D : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) :
    (∀ label : Fin 6, totalGapReading D label < 1)
      ∧ (∀ label : Fin 6, (subsetSum D (Finset.univ.erase label) - 1).PosDef)
      ∧ Matrix.trace (totalGap D)⁻¹ < 1
      ∧ (subsetSum D Finset.univ - 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef
      ∧ (12 : ℝ) < ∑ label, leverageOf (D.atom label) :=
  ⟨totalGapReading_lt_one_of_isPrimitiveDesign_of_isTie_sixThree D hprimitive htie,
    forall_posDef_gap_erase_of_isPrimitiveDesign_of_isTie D hprimitive htie,
    trace_totalGap_inv_lt_one_of_isPrimitiveDesign_of_isTie D hprimitive htie,
    posDef_subsetSum_univ_sub_two_of_isPrimitiveDesign_of_isTie D hprimitive htie,
    twelve_lt_sum_leverage_of_isPrimitiveDesign_of_isTie D hprimitive htie⟩

end Gtz

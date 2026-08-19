import Gtz.Wave.OutsideFrameLaws
import Gtz.Wave.PairRefusalLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The second moment of the outside co-weights, and the refusal law it carries

The refusal ledger (`Gtz.sum_coweight_pairRefusalSlack`) weights the four refusal
slacks of a pair by the CO-WEIGHTS `1 − t_x`, and the corner ledger
(`Gtz.corner_pairRefusal_bound`) weights the three outside ones by ONE.  Those
are the only two weightings the campaign could evaluate, because the outside
atoms carry exactly two computable moments: `Σ_d g_d g_dᵀ = S_out` and
`Σ_d (1−t_d) g_d g_dᵀ = W − Σ_{e∈C}(1−t_e) g_e g_eᵀ`, the co-weighted Parseval
split.

## The third moment exists, and it is the frame law

At `(6,3)` the complement of the dominator is a BASIS, so
`Gtz.outside_weighted_adj_square` supplies the SECOND moment as well:

  `(Σ_d (1−t_d) g_d g_dᵀ)·adj(S_out)·(Σ_d (1−t_d) g_d g_dᵀ)
      = det(S_out)·Σ_d (1−t_d)² g_d g_dᵀ` .

Reading that identity at two probes through the six-set metric collapses the
left side onto the CORNER RESIDUAL of each probe — the probe less its
co-weighted reflection in the dominator's atoms — and gives the master identity
(`Gtz.outside_secondMoment_adj`)

  `det(S_out)·Σ_d (1−t_d)²·(g_d·W⁻¹y)(g_d·W⁻¹z)
      = res(y)ᵀ adj(S_out) res(z)` .

## The refusal law

Every refusal slack of an admissible pair is nonnegative at a tie
(`Gtz.pairRefusalSlack_nonneg_of_isTie`), so ANY nonnegative weighting of the
three outside slacks is nonnegative.  Taking the weights `(1−t_d)²` and
evaluating through the master identity, together with the diagonal rank-one
rigidity `Gtz.outsidePivot_diag_rankOne'` for the co-pivot term, gives a tie law
that neither landed aggregate implies
(`Gtz.corner_secondMoment_refusal`):

  `E·[a_h·R_ff + 2 P_fh·R_fh + a_f·R_hh] ≥ π_u·Δ_fh·R_uu` ,

where `R_yz := res(y)ᵀ adj(S_out) res(z)`, `E` is the outside cross mass, and
`a_f = 1 − P_ff`.

## Why the weighting matters

The campaign's brief asserted a Schur–Horn cap: that for one inside pair the
three outside refusals are equivalent to their SUM, so no pair-by-pair programme
can beat `Gtz.corner_pairRefusal_bound`.  That is false.  Schur–Horn frees the
outside frame, but the co-weighted Parseval split PINS it: the frame is the
eigenframe of one fixed matrix and its co-weights are that matrix's eigenvalues.
The ledger and this second-moment law are both pair-by-pair, and both are
strictly stronger than the unweighted sum.

## The sharpened ledger

The same observation sharpens the landed ledger at once.  Dropping only the
outside slacks from `Gtz.sum_coweight_pairRefusalSlack` leaves
(`Gtz.ghostDeficitForm_ge_coweight_slack`)

  `(1 − t_x)·slack_x ≤ ghostDeficitForm(f,h)`   for every `x ∉ {f,h}` ,

which strengthens `Gtz.ghostDeficitForm_nonneg_of_isTie` from `0 ≤` to a
positive lower bound at every one of the four slots.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The corner residual of a probe -/

/-- The CORNER RESIDUAL of a probe: the probe less its co-weighted reflection in
the atoms of the dominator. -/
noncomputable def cornerResidual (D : WeightedDesign m 3) (C : Finset (Fin m))
    (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  y - ∑ e ∈ C, ((1 - D.weight e)
    * (D.atom e ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ y))) • D.atom e

/-- **The co-weighted Parseval split.**  The outside co-weighted atom sum is the
six-set gap less the inside one. -/
theorem coweight_outside_atomSum (D : WeightedDesign m 3) (C : Finset (Fin m)) :
    ∑ d ∈ Cᶜ, (1 - D.weight d) • atomMatrix (D.atom d)
      = (subsetSum D Finset.univ - 1)
        - ∑ e ∈ C, (1 - D.weight e) • atomMatrix (D.atom e) := by
  have hall := coweight_atomSum_eq_sixSetGap D (k := 3)
  have hsplit := Finset.sum_add_sum_compl C
    (fun c => (1 - D.weight c) • atomMatrix (D.atom c))
  rw [← hall, ← hsplit]
  abel

/-- The co-weighted outside atom sum is symmetric. -/
theorem coweight_outside_transpose (D : WeightedDesign m 3) (C : Finset (Fin m)) :
    (∑ d ∈ Cᶜ, (1 - D.weight d) • atomMatrix (D.atom d))ᵀ
      = ∑ d ∈ Cᶜ, (1 - D.weight d) • atomMatrix (D.atom d) := by
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.transpose_smul,
    show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d) from rfl,
    Matrix.transpose_vecMulVec]

/-- **The outside sum reads the metric as the corner residual.** -/
theorem coweight_outside_mulVec (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (y : Fin 3 → ℝ) :
    (∑ d ∈ Cᶜ, (1 - D.weight d) • atomMatrix (D.atom d))
        *ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ y)
      = cornerResidual D C y := by
  classical
  set W : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D Finset.univ - 1 with hW
  have hu : IsUnit W.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have hWy : W *ᵥ (W⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hu, Matrix.one_mulVec]
  rw [coweight_outside_atomSum D C, Matrix.sub_mulVec, hWy, Matrix.sum_mulVec,
    cornerResidual]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Matrix.smul_mulVec,
    show atomMatrix (D.atom e) = Matrix.vecMulVec (D.atom e) (D.atom e) from rfl,
    vecMulVec_mulVec_eq, smul_smul]

/-! ## 2. The master second-moment identity -/

/-- **The second moment of the outside co-weights, read at two probes.**  The
frame law of the complement triple turns the squared co-weights into the
adjugate form of the corner residuals.  Nothing on either side is an inverse of
the outside atom sum, so the identity survives the degenerate corner where the
complement triple is coplanar (both sides then vanish). -/
theorem outside_secondMoment_adj (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcompl : (Cᶜ : Finset (Fin m)).card = 3)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (y z : Fin 3 → ℝ) :
    (subsetSum D Cᶜ).det * ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2
        * ((D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ y))
          * (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ z)))
      = cornerResidual D C y
          ⬝ᵥ ((subsetSum D Cᶜ).adjugate *ᵥ cornerResidual D C z) := by
  classical
  set W : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D Finset.univ - 1 with hW
  set Th : Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ d ∈ Cᶜ, (1 - D.weight d) • atomMatrix (D.atom d) with hTh
  set M2 : Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2 • atomMatrix (D.atom d) with hM2
  have hframe : Th * (subsetSum D Cᶜ).adjugate * Th = (subsetSum D Cᶜ).det • M2 :=
    outside_weighted_adj_square D C hcompl (fun a => 1 - D.weight a)
  have hsymm : Thᵀ = Th := coweight_outside_transpose D C
  have hres : ∀ v : Fin 3 → ℝ, Th *ᵥ (W⁻¹ *ᵥ v) = cornerResidual D C v :=
    fun v => coweight_outside_mulVec D C hPD v
  have hread := congrArg
    (fun M : Matrix (Fin 3) (Fin 3) ℝ => (W⁻¹ *ᵥ y) ⬝ᵥ (M *ᵥ (W⁻¹ *ᵥ z))) hframe
  have hleft : (W⁻¹ *ᵥ y) ⬝ᵥ ((Th * (subsetSum D Cᶜ).adjugate * Th) *ᵥ (W⁻¹ *ᵥ z))
      = cornerResidual D C y
          ⬝ᵥ ((subsetSum D Cᶜ).adjugate *ᵥ cornerResidual D C z) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dot_mulVec_comm_of_symm hsymm, hres, hres]
  have hright : (W⁻¹ *ᵥ y) ⬝ᵥ (((subsetSum D Cᶜ).det • M2) *ᵥ (W⁻¹ *ᵥ z))
      = (subsetSum D Cᶜ).det * ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2
          * ((D.atom d ⬝ᵥ (W⁻¹ *ᵥ y)) * (D.atom d ⬝ᵥ (W⁻¹ *ᵥ z))) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hM2, Matrix.sum_mulVec,
      dotProduct_sum]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.smul_mulVec,
      show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d) from rfl,
      vecMulVec_mulVec_eq, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, dotProduct_comm (W⁻¹ *ᵥ y) (D.atom d)]
    ring
  rw [hleft] at hread
  rw [hright] at hread
  exact hread.symm

/-! ## 3. The second moment in pivot form -/

/-- The second-moment cross reading of two atoms. -/
theorem outside_secondMoment_pivot (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcompl : (Cᶜ : Finset (Fin m)).card = 3)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (a b : Fin m) :
    (subsetSum D Cᶜ).det
        * ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2 * (sixSetPivot D a d * sixSetPivot D b d)
      = cornerResidual D C (D.atom a)
          ⬝ᵥ ((subsetSum D Cᶜ).adjugate *ᵥ cornerResidual D C (D.atom b)) := by
  rw [← outside_secondMoment_adj D C hcompl hPD (D.atom a) (D.atom b)]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [show D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom a)
      = sixSetPivot D a d from (sixSetPivot_comm D a d) ▸ rfl,
    show D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b)
      = sixSetPivot D b d from (sixSetPivot_comm D b d) ▸ rfl]

/-- The second-moment mass of the gap-axis cross readings. -/
theorem outside_secondMoment_gapCross (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcompl : (Cᶜ : Finset (Fin m)).card = 3)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) {u : Fin 3 → ℝ} :
    (subsetSum D Cᶜ).det * ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2 * gapCross D u d ^ 2
      = cornerResidual D C u ⬝ᵥ ((subsetSum D Cᶜ).adjugate *ᵥ cornerResidual D C u) := by
  rw [← outside_secondMoment_adj D C hcompl hPD u u]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  have hWsymm : (subsetSum D Finset.univ - 1)ᵀ = subsetSum D Finset.univ - 1 :=
    transpose_subsetSum_sub_one D Finset.univ
  have hWinv : ((subsetSum D Finset.univ - 1)⁻¹)ᵀ = (subsetSum D Finset.univ - 1)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hWsymm]
  rw [show D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ u) = gapCross D u d from
    (dot_mulVec_comm hWinv (D.atom d) u).trans rfl]
  ring

/-! ## 4. The sharpened ledger -/

/-- **The ledger, sharpened at one slot.**  Dropping the other three slacks of an
admissible pair leaves a positive lower bound on the weighted ghost deficit.  It
strengthens `Gtz.ghostDeficitForm_nonneg_of_isTie` at every slot at once. -/
theorem ghostDeficitForm_ge_coweight_slack (D : WeightedDesign 6 3) (htie : IsTie D)
    {f h x : Fin 6} (hfh : f ≠ h) (hxf : x ≠ f) (hxh : x ≠ h)
    (ha : sixSetPivot D f f < 1) (hminor : 0 < pairPivotMinor D f h) :
    (1 - D.weight x) * pairRefusalSlack D f h x ≤ ghostDeficitForm D f h := by
  classical
  rw [← sum_coweight_pairRefusalSlack D hfh]
  refine Finset.single_le_sum (f := fun c => (1 - D.weight c) * pairRefusalSlack D f h c)
    (fun c hc => ?_) ?_
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    refine mul_nonneg ?_ (pairRefusalSlack_nonneg_of_isTie D htie hfh
      (fun hcc => hc.1 hcc.symm) (fun hcc => hc.2 hcc.symm) ha hminor)
    linarith [design_weight_lt_one D (by norm_num) c]
  · simp [hxf, hxh]

/-! ## 5. The second-moment refusal law of a corner -/

/-- **The second-moment refusal law.**  At a corank-two corner of a `(6,3)` tie
the squared co-weights of the outside atoms carry a refusal inequality that
neither `Gtz.corner_pairRefusal_bound` (the unweighted sum of the three outside
slacks) nor `Gtz.pairRefusalLedger` (their co-weighted sum) implies.  The second
moment exists only because the complement triple is a basis, which happens at
`6 = 3 + 3` and at no other size. -/
theorem corner_secondMoment_refusal (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ}
    {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {f h : Fin 6} (hf : f ∈ C) (hh : h ∈ C) (hfh : f ≠ h)
    (ha : sixSetPivot D f f < 1) (hminor : 0 < pairPivotMinor D f h) :
    cornerPivot D lam u * (pairPivotMinor D f h
        * (cornerResidual D C u
            ⬝ᵥ ((subsetSum D Cᶜ).adjugate *ᵥ cornerResidual D C u)))
      ≤ gapCrossMass D C u
        * ((1 - sixSetPivot D h h)
              * (cornerResidual D C (D.atom f)
                  ⬝ᵥ ((subsetSum D Cᶜ).adjugate *ᵥ cornerResidual D C (D.atom f)))
            + 2 * (sixSetPivot D f h
              * (cornerResidual D C (D.atom f)
                  ⬝ᵥ ((subsetSum D Cᶜ).adjugate *ᵥ cornerResidual D C (D.atom h))))
            + (1 - sixSetPivot D f f)
              * (cornerResidual D C (D.atom h)
                  ⬝ᵥ ((subsetSum D Cᶜ).adjugate *ᵥ cornerResidual D C (D.atom h)))) := by
  classical
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hcompl : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, hcard]; simp
  have hpsd : (subsetSum D Cᶜ).PosSemidef := by
    rw [subsetSum]
    exact Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add)
      Matrix.PosSemidef.zero (fun d _ => posSemidef_atomMatrix (D.atom d))
  have hdet : 0 ≤ (subsetSum D Cᶜ).det := hpsd.det_nonneg
  have hE : 0 ≤ gapCrossMass D C u := Finset.sum_nonneg fun d _ => sq_nonneg _
  have hff := outside_secondMoment_pivot D C hcompl hPD f f
  have hfh2 := outside_secondMoment_pivot D C hcompl hPD f h
  have hhh := outside_secondMoment_pivot D C hcompl hPD h h
  have huu := outside_secondMoment_gapCross D C hcompl hPD (u := u)
  have hslack : 0 ≤ ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2 * pairRefusalSlack D f h d := by
    refine Finset.sum_nonneg fun d hd => ?_
    rw [Finset.mem_compl] at hd
    exact mul_nonneg (sq_nonneg _) (pairRefusalSlack_nonneg_of_isTie D htie hfh
      (fun hc => hd (hc ▸ hf)) (fun hc => hd (hc ▸ hh)) ha hminor)
  have hdiag : ∀ d ∈ (Cᶜ : Finset (Fin 6)),
      gapCrossMass D C u * (1 - sixSetPivot D d d)
        = cornerPivot D lam u * gapCross D u d ^ 2 :=
    fun d hd => outsidePivot_diag_rankOne' D C hcard hgap hd
  have hkey : gapCrossMass D C u
        * ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2 * pairRefusalSlack D f h d
      = gapCrossMass D C u * ((1 - sixSetPivot D h h)
            * ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2 * (sixSetPivot D f d * sixSetPivot D f d)
          + 2 * (sixSetPivot D f h
            * ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2 * (sixSetPivot D f d * sixSetPivot D h d))
          + (1 - sixSetPivot D f f)
            * ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2 * (sixSetPivot D h d * sixSetPivot D h d))
        - cornerPivot D lam u * (pairPivotMinor D f h
            * ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2 * gapCross D u d ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd' := hdiag d hd
    rw [pairRefusalSlack]
    linear_combination (-((1 - D.weight d) ^ 2 * pairPivotMinor D f h)) * hd'
  have hnn : 0 ≤ (subsetSum D Cᶜ).det
      * (gapCrossMass D C u
        * ∑ d ∈ Cᶜ, (1 - D.weight d) ^ 2 * pairRefusalSlack D f h d) :=
    mul_nonneg hdet (mul_nonneg hE hslack)
  rw [hkey] at hnn
  rw [← hff, ← hfh2, ← hhh, ← huu]
  nlinarith [hnn]

end Gtz

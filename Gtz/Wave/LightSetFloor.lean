import Gtz.Wave.CornerPivotRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The light set of a design, the polarized inside row law, and the crux in
cofactor form

## The light set

An atom is LIGHT when its six-set pivot sits below one, `P_cc < 1`.  The light
set is where every strictly dominating triple has to leave its complement: if
`T` dominates strictly then `S_T − 1 ≻ 0`, so `W − g_c g_cᵀ ≻ 0` for every
`c ∉ T`, hence `P_cc < 1` (`Gtz.compl_subset_lightSet_of_posDef`).

The trace law of the co-weighted projection (`Gtz.sixSet_coweight_pivot_sum`)
prices the light set from below.  With `Σ_c (1 − t_c) = m − 1` and
`Σ_c (1 − t_c)·P_cc = 3`,

  `Σ_c (1 − t_c)(1 − P_cc) = m − 4` ,

and every summand is at most `1 − t_c < 1`, while the heavy atoms contribute
nothing positive.  So `m − 4 < |L|`, that is `|L| ≥ m − 3`
(`Gtz.card_lightSet_ge`).  The count `m − 3` is exactly the size of the
complement of a triple, so the light set is always big enough to hold one
candidate and never guaranteed to hold two.  At `(6,3)` it reads `|L| ≥ 3`
(`Gtz.three_le_card_lightSet`), and when `|L| = 3` the only candidate for a
strictly dominating triple is `Lᶜ` (`Gtz.eq_compl_lightSet_of_card_three`).

The strict positivity of the weights is what makes the count work: a summand
`(1 − t_c)(1 − P_cc)` reaches one only in the dust limit `t_c → 0`.

## The polarized inside row law

`Gtz.inside_row_law` prices the co-weighted INSIDE row mass of one atom.  Its
polarized form (`Gtz.inside_cross_row_law`) prices the pairing of two rows,

  `Σ_{e∈C} (1 − t_e)·P_{ae}P_{eb} = lam·η_aη_b + Σ_{d∉C} t_d·P_{ad}P_{db}` ,

and follows from the projection identity and the cross-block law of the corner.

## The crux in cofactor form

The swap bracket is `2P_ff + P_hh − 1 − 2·det B` for the ghost block `B`
(`Gtz.swapBracket_eq_traceForm`).  Summing the two brackets with the ghost
weights turns `Gtz.GhostDeficitShort` into

  `tr B + (t_f P_ff + t_h P_hh)/(t_f + t_h) < 1 + 2·det B` ,

stated without division as `Gtz.weightedDeficit_cofactor_form`.  The short block
`Gtz.GhostBlockShort` is the same statement with the weighted mean replaced by
the maximum, so the weighted surface is exactly the block trace plus a mean
against one plus twice the block determinant.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The pivot is nonnegative, and the co-weight deficit -/

/-- Every six-set pivot is nonnegative: it is a co-weighted square sum. -/
theorem sixSetPivot_self_nonneg (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (c : Fin m) :
    0 ≤ sixSetPivot D c c := by
  classical
  have hWsymm : (subsetSum D Finset.univ - 1)ᵀ = subsetSum D Finset.univ - 1 :=
    transpose_subsetSum_sub_one D Finset.univ
  have hWinvsymm : ((subsetSum D Finset.univ - 1)⁻¹)ᵀ
      = (subsetSum D Finset.univ - 1)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hWsymm]
  have hproj := pivot_coweight_projection D hPD c c
  have hdiag : sixSetPivot D c c
      = ∑ c', (1 - D.weight c') * sixSetPivot D c c' ^ 2 := by
    rw [sixSetPivot, ← hproj]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [show D.atom c' ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c)
        = sixSetPivot D c c' from dot_mulVec_comm hWinvsymm _ _,
      show D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c')
        = sixSetPivot D c c' from rfl]
    ring
  rw [hdiag]
  exact Finset.sum_nonneg fun c' _ =>
    mul_nonneg (by linarith [design_weight_lt_one D hm c']) (sq_nonneg _)

/-- **The co-weight deficit of a design.**  `Σ_c (1 − t_c)(1 − P_cc) = m − 4`. -/
theorem coweight_pivot_deficit (D : WeightedDesign m 3)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    ∑ c, (1 - D.weight c) * (1 - sixSetPivot D c c) = (m : ℝ) - 4 := by
  classical
  have htrace : ∑ c, (1 - D.weight c) * sixSetPivot D c c = 3 := by
    simpa only [sixSetPivot] using sixSet_coweight_pivot_sum D hPD
  have hco : ∑ c, (1 - D.weight c) = (m : ℝ) - 1 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, D.weight_sum_one]
    simp
  have hsplit : ∑ c, (1 - D.weight c) * (1 - sixSetPivot D c c)
      = (∑ c, (1 - D.weight c)) - ∑ c, (1 - D.weight c) * sixSetPivot D c c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, hco, htrace]
  ring

/-! ## 2. The light set -/

open scoped Classical in
/-- The LIGHT SET of a design: the atoms whose six-set pivot is below one. -/
noncomputable def lightSet (D : WeightedDesign m 3) : Finset (Fin m) :=
  Finset.univ.filter fun c => sixSetPivot D c c < 1

open scoped Classical in
theorem mem_lightSet_iff (D : WeightedDesign m 3) (c : Fin m) :
    c ∈ lightSet D ↔ sixSetPivot D c c < 1 := by
  simp [lightSet]

/-- **The complement of a strict dominator is light.**  Removing one outside
atom from the six-set gap already leaves a positive definite matrix. -/
theorem compl_subset_lightSet_of_posDef (D : WeightedDesign m 3)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) {T : Finset (Fin m)}
    (hT : (subsetSum D T - 1).PosDef) : Tᶜ ⊆ lightSet D := by
  classical
  intro c hc
  rw [mem_lightSet_iff]
  refine (posDef_sub_vecMulVec_iff (subsetSum D Finset.univ - 1) hPD (D.atom c)).mp ?_
  have hrest : (subsetSum D Finset.univ - 1)
      - Matrix.vecMulVec (D.atom c) (D.atom c)
      = (subsetSum D T - 1) + ∑ c' ∈ Tᶜ.erase c, atomMatrix (D.atom c') := by
    have hsplit : subsetSum D T + subsetSum D Tᶜ = subsetSum D Finset.univ := by
      rw [subsetSum, subsetSum, subsetSum]
      exact Finset.sum_add_sum_compl T _
    have hout : subsetSum D Tᶜ
        = atomMatrix (D.atom c) + ∑ c' ∈ Tᶜ.erase c, atomMatrix (D.atom c') := by
      rw [subsetSum, ← Finset.add_sum_erase Tᶜ _ hc]
    rw [← hsplit, hout, show atomMatrix (D.atom c)
      = Matrix.vecMulVec (D.atom c) (D.atom c) from rfl]
    abel
  rw [hrest]
  refine hT.add_posSemidef ?_
  exact Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add)
    (Matrix.PosSemidef.zero) (fun c' _ => posSemidef_atomMatrix (D.atom c'))

/-- **The light set floor.**  `m − 4 < |L|`.  Every co-weight deficit is below
one because the weights are strictly positive, and the heavy atoms contribute
nothing positive. -/
theorem card_lightSet_gt (D : WeightedDesign m 3) (hm : 5 ≤ m)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    (m : ℝ) - 4 < (lightSet D).card := by
  classical
  have hm2 : 2 ≤ m := by omega
  have hm5 : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hdef := coweight_pivot_deficit D hPD
  have hpart := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin m))
    (fun c => sixSetPivot D c c < 1)
    (fun c => (1 - D.weight c) * (1 - sixSetPivot D c c))
  have hheavy : ∑ c ∈ Finset.univ.filter (fun c => ¬ sixSetPivot D c c < 1),
      (1 - D.weight c) * (1 - sixSetPivot D c c) ≤ 0 := by
    refine Finset.sum_nonpos fun c hc => ?_
    simp only [Finset.mem_filter, not_lt] at hc
    exact mul_nonpos_of_nonneg_of_nonpos
      (by linarith [design_weight_lt_one D hm2 c]) (by linarith [hc.2])
  have hLight : lightSet D
      = Finset.univ.filter (fun c => sixSetPivot D c c < 1) := by
    rw [lightSet]
  have hLsum : (m : ℝ) - 4
      ≤ ∑ c ∈ lightSet D, (1 - D.weight c) * (1 - sixSetPivot D c c) := by
    rw [hLight]
    linarith [hpart, hdef, hheavy]
  have hne : (lightSet D).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (lightSet D) with he | hne
    · rw [he, Finset.sum_empty] at hLsum
      linarith
    · exact hne
  have hle : ∑ c ∈ lightSet D, (1 - D.weight c) * (1 - sixSetPivot D c c)
      ≤ ∑ c ∈ lightSet D, (1 - D.weight c) := by
    refine Finset.sum_le_sum fun c _ => ?_
    have hp : 0 ≤ sixSetPivot D c c := sixSetPivot_self_nonneg D hm2 hPD c
    have hw : D.weight c < 1 := design_weight_lt_one D hm2 c
    nlinarith
  have hlt : ∑ c ∈ lightSet D, (1 - D.weight c) < ((lightSet D).card : ℝ) := by
    calc ∑ c ∈ lightSet D, (1 - D.weight c)
        < ∑ _c ∈ lightSet D, (1 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hne fun c _ => by linarith [D.weight_pos c]
      _ = ((lightSet D).card : ℝ) := by simp
  linarith

/-- **At least three atoms of a `(6,3)` design are light.** -/
theorem three_le_card_lightSet (D : WeightedDesign 6 3) :
    3 ≤ (lightSet D).card := by
  have h := card_lightSet_gt D (by norm_num) (sixSetGap_posDef_sixThree D)
  have h2 : (2 : ℝ) < ((lightSet D).card : ℝ) := by
    push_cast at h ⊢
    linarith
  have h3 : 2 < (lightSet D).card := by exact_mod_cast h2
  omega

/-- **A three-atom light set pins the only candidate.**  If exactly three atoms
are light, then the complement of the light set is the only triple that can
dominate strictly. -/
theorem eq_compl_lightSet_of_card_three (D : WeightedDesign 6 3)
    (hthree : (lightSet D).card = 3) {T : Finset (Fin 6)} (hcard : T.card = 3)
    (hT : (subsetSum D T - 1).PosDef) : T = (lightSet D)ᶜ := by
  classical
  have hsub : Tᶜ ⊆ lightSet D :=
    compl_subset_lightSet_of_posDef D (sixSetGap_posDef_sixThree D) hT
  have hcompl : Tᶜ.card = 3 := by
    rw [Finset.card_compl, hcard]
    simp
  have hcard2 : (lightSet D).card ≤ Tᶜ.card := by omega
  have heq : Tᶜ = lightSet D := Finset.eq_of_subset_of_card_le hsub hcard2
  rw [← compl_compl T, heq]

/-- **Some atom of a `(6,3)` design has pivot below two thirds.**  The
co-weight deficits sum to two over six atoms, and a pivot at two thirds or above
caps its own deficit at one third. -/
theorem exists_pivot_lt_two_thirds (D : WeightedDesign 6 3) :
    ∃ c : Fin 6, sixSetPivot D c c < 2 / 3 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hdef := coweight_pivot_deficit D (sixSetGap_posDef_sixThree D)
  have hbound : ∀ c : Fin 6,
      (1 - D.weight c) * (1 - sixSetPivot D c c) < 1 / 3 := by
    intro c
    have h1 : (0:ℝ) < 1 - D.weight c := by
      linarith [design_weight_lt_one D (by norm_num) c]
    have h2 : 1 - sixSetPivot D c c ≤ 1 / 3 := by linarith [hcon c]
    have h3 : 0 ≤ (1 - D.weight c) * (1 / 3 - (1 - sixSetPivot D c c)) :=
      mul_nonneg h1.le (by linarith)
    nlinarith [D.weight_pos c, h1, h3]
  have hlt : ∑ _c : Fin 6, (1 - D.weight _c) * (1 - sixSetPivot D _c _c)
      < ∑ _c : Fin 6, (1 / 3 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun c _ => hbound c
  rw [hdef] at hlt
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  norm_num at hlt

/-! ## 3. The polarized inside row law -/

/-- **The inside row law, polarized.**  The co-weighted inside pairing of two
pivot rows is the spike pairing plus the weighted outside pairing.
`Gtz.inside_row_law` is the diagonal case. -/
theorem inside_cross_row_law (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (a b : Fin m) :
    ∑ e ∈ C, (1 - D.weight e) * (sixSetPivot D a e * sixSetPivot D e b)
      = lam * (gapCross D u a * gapCross D u b)
        + ∑ d ∈ Cᶜ, D.weight d * (sixSetPivot D a d * sixSetPivot D d b) := by
  classical
  have hWsymm : (subsetSum D Finset.univ - 1)ᵀ = subsetSum D Finset.univ - 1 :=
    transpose_subsetSum_sub_one D Finset.univ
  have hWinvsymm : ((subsetSum D Finset.univ - 1)⁻¹)ᵀ
      = (subsetSum D Finset.univ - 1)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hWsymm]
  have hproj := pivot_coweight_projection D hPD a b
  have hrewrite : ∀ c : Fin m,
      (1 - D.weight c)
          * ((D.atom a ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c))
            * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b)))
        = (1 - D.weight c) * (sixSetPivot D a c * sixSetPivot D c b) := fun c => rfl
  simp only [hrewrite] at hproj
  rw [← Finset.sum_add_sum_compl C] at hproj
  have hcomp := outside_pivot_compose D C hgap hPD a b
  have houtsplit : ∑ d ∈ Cᶜ, (1 - D.weight d) * (sixSetPivot D a d * sixSetPivot D d b)
      = (∑ d ∈ Cᶜ, sixSetPivot D a d * sixSetPivot D d b)
        - ∑ d ∈ Cᶜ, D.weight d * (sixSetPivot D a d * sixSetPivot D d b) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [houtsplit, hcomp] at hproj
  have hab : D.atom a ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b)
      = sixSetPivot D a b := rfl
  rw [hab] at hproj
  linarith [hproj]

/-! ## 4. The crux in cofactor form -/

/-- **The weighted deficit in cofactor form.**  The weighted sum of the two swap
brackets is the block trace, plus the weight-mean of the two diagonals, against
one plus twice the block determinant. -/
theorem weightedDeficit_cofactor_form (a b c tf th : ℝ) :
    tf * ((1 - b) * (2 * a - 1) + 2 * c ^ 2)
        + th * ((1 - a) * (2 * b - 1) + 2 * c ^ 2)
      = (tf + th) * (a + b - 1 - 2 * (a * b - c ^ 2)) + (tf * a + th * b) := by
  ring

/-- **The short block in cofactor form.**  A short ghost block is the block trace
plus the LARGER diagonal against one plus twice the block determinant, in both
orders. -/
theorem ghostBlockShort_cofactor_form (a b c : ℝ) :
    ((1 - 2 * a) * (1 - b) - 2 * c ^ 2 = 1 + 2 * (a * b - c ^ 2) - (a + b) - a)
      ∧ ((1 - 2 * b) * (1 - a) - 2 * c ^ 2
          = 1 + 2 * (a * b - c ^ 2) - (a + b) - b) := by
  constructor <;> ring

/-- **The weighted deficit holds when the cofactor form is negative.** -/
theorem ghostDeficitShort_of_cofactor (D : WeightedDesign 6 3) {f h : Fin 6}
    (ha : sixSetPivot D f f < 1) (hb : sixSetPivot D h h < 1)
    (hdet : 0 < (1 - sixSetPivot D f f) * (1 - sixSetPivot D h h)
      - sixSetPivot D f h ^ 2)
    (hcof : (D.weight f + D.weight h)
        * (sixSetPivot D f f + sixSetPivot D h h - 1
          - 2 * (sixSetPivot D f f * sixSetPivot D h h - sixSetPivot D f h ^ 2))
        + (D.weight f * sixSetPivot D f f + D.weight h * sixSetPivot D h h) < 0) :
    GhostDeficitShort D f h := by
  refine ⟨ha, hb, hdet, ?_⟩
  have := weightedDeficit_cofactor_form (sixSetPivot D f f) (sixSetPivot D h h)
    (sixSetPivot D f h) (D.weight f) (D.weight h)
  linarith

end Gtz

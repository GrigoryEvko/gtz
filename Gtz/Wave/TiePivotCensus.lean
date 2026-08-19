import Gtz.Wave.PairRefusalLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The pivot census of a tie, and the light count of a corank-two corner

The pivot matrix of a `(6,3)` design carries two exact totals.  Parseval reads
the weighted diagonal as the trace of the inverse gap
(`Gtz.trace_gapInv_eq_weighted_pivot`)

  `Σ_c t_c·P_cc = tr W⁻¹` ,

and the co-weighted diagonal is the rank (`Gtz.sixSet_coweight_pivot_sum`), so
the plain diagonal totals `3 + tr W⁻¹` (`Gtz.sum_pivot_eq_three_add_trace`).
Together with `Gtz.tie_triple_pivot_sum_ge_one` these are the census of a tie:
every triple carries a unit of pivot while the whole diagonal is pinned by one
trace.

## The pair minor dichotomy

Cauchy–Schwarz on the co-weighted rows turns a nonpositive pair minor into a
full unit of pivot on that pair (`Gtz.pivot_sum_ge_one_of_pairMinor_nonpos`),
with NO tie hypothesis and no weights:

  `(1 − P_ff)(1 − P_hh) ≤ P_fh²  ⟹  1 ≤ P_ff + P_hh` .

So inside the light set every pair is either admissible — and then the refusal
ledger applies — or it already carries a unit of pivot.  This is the dichotomy
that makes the light set a finite combinatorial object.

## The light count of a corank-two corner

At a corank-two corner every outside pivot is capped by one
(`Gtz.outside_pivot_le_one`) and the outside co-pivots total the corner pivot
`π_u ≤ 1` (`Gtz.outside_pivot_sum`).  The light set of a tie carries a co-weight
deficit of two (`Gtz.two_le_sum_lightSet_coweight_deficit`), and the outside
atoms can supply at most `π_u` of it.  The inside light atoms must supply the
rest, and each supplies less than one, so

  **at least TWO inside atoms are light** (`Gtz.two_le_card_light_inside`),

and their pivots fall short (`Gtz.sum_light_inside_pivot_lt`).  When exactly two
are light the pivot law of that pair forces the corner pivot past one half
(`Gtz.half_lt_cornerPivot_of_two_light_inside`), which is a quantitative floor on
a corner scalar that no landed instrument reached.

## The outside row mass at an arbitrary gap

`Gtz.outside_cross_row_mass` was proved for a rank-one gap.  Its proof uses only
`S_{Cᶜ} = W − (S_C − 1)`, so it holds at EVERY subset
(`Gtz.outside_cross_row_mass_general`): the outside readings pair to the probe
pairing less the gap read in the `W⁻¹` metric.  At corank one the gap has rank
two and the same law prices the outside block, so the corank-one arm inherits
the whole cross-block calculus.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The outside row mass at an arbitrary gap -/

/-- **The polarized outside row mass, at an arbitrary subset.**  The outside
readings of two probes pair to the probe pairing less the gap of the subset read
in the `W⁻¹` metric.  `Gtz.outside_cross_row_mass` is the rank-one instance. -/
theorem outside_cross_row_mass_general (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (y z : Fin 3 → ℝ) :
    ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ y))
        * (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ z))
      = y ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ z)
        - ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ y)
            ⬝ᵥ ((subsetSum D C - 1) *ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ z)) := by
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
  have hsplit : subsetSum D C + subsetSum D Cᶜ = subsetSum D Finset.univ := by
    rw [subsetSum, subsetSum, subsetSum]
    exact Finset.sum_add_sum_compl C _
  have hout : subsetSum D Cᶜ = W - (subsetSum D C - 1) := by
    rw [hW, ← hsplit]; abel
  have hWb : W *ᵥ b = z := by
    rw [hb, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hunit, Matrix.one_mulVec]
  have haz : a ⬝ᵥ z = y ⬝ᵥ (W⁻¹ *ᵥ z) := by
    rw [ha, dotProduct_comm]
    exact dot_mulVec_comm hWinvsymm _ _
  rw [hsum, hout, Matrix.sub_mulVec, dotProduct_sub, hWb, haz]

/-! ## 2. The two pivot totals -/

/-- **The weighted pivot diagonal is the trace of the inverse gap.**  Parseval
collapses the weighted atom sum to the identity. -/
theorem trace_gapInv_eq_weighted_pivot (D : WeightedDesign m 3) :
    ∑ c, D.weight c * sixSetPivot D c c
      = Matrix.trace ((subsetSum D Finset.univ - 1)⁻¹) :=
  sum_weight_quadForm_eq_trace D _

/-- **The pivot diagonal totals three plus the trace.**  The co-weighted diagonal
is the rank and the weighted diagonal is the trace. -/
theorem sum_pivot_eq_three_add_trace (D : WeightedDesign m 3)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    ∑ c, sixSetPivot D c c
      = 3 + Matrix.trace ((subsetSum D Finset.univ - 1)⁻¹) := by
  have hco : ∑ c, (1 - D.weight c) * sixSetPivot D c c = 3 := by
    simpa only [sixSetPivot] using sixSet_coweight_pivot_sum D hPD
  have hw := trace_gapInv_eq_weighted_pivot D
  have hsplit : ∑ c, (1 - D.weight c) * sixSetPivot D c c
      = (∑ c, sixSetPivot D c c) - ∑ c, D.weight c * sixSetPivot D c c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, hw] at hco
  linarith

/-! ## 3. The pair minor dichotomy -/

/-- **A nonpositive pair minor costs a full unit of pivot.**  Cauchy–Schwarz on
the co-weighted rows caps the off-diagonal by the two diagonals, and the pair
minor then reads `1 ≤ P_ff + P_hh` directly.  No tie, no weights. -/
theorem pivot_sum_ge_one_of_pairMinor_nonpos (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) {f h : Fin m}
    (hminor : (1 - sixSetPivot D f f) * (1 - sixSetPivot D h h)
      ≤ sixSetPivot D f h ^ 2) :
    1 ≤ sixSetPivot D f f + sixSetPivot D h h := by
  have hcs := sixSetPivot_sq_le_mul D hm hPD f h
  nlinarith [hminor, hcs]

/-- **Inside the light set every pair is admissible or heavy in total.**  The
dichotomy that makes the light set finite combinatorics. -/
theorem light_pair_dichotomy (D : WeightedDesign 6 3) {f h : Fin 6}
    (hf : f ∈ lightSet D) (hh : h ∈ lightSet D) :
    0 < pairPivotMinor D f h ∨ 1 ≤ sixSetPivot D f f + sixSetPivot D h h := by
  rw [mem_lightSet_iff] at hf hh
  by_cases hpos : 0 < pairPivotMinor D f h
  · exact Or.inl hpos
  · refine Or.inr (pivot_sum_ge_one_of_pairMinor_nonpos D (by norm_num)
      (sixSetGap_posDef_sixThree D) ?_)
    rw [pairPivotMinor] at hpos
    linarith [not_lt.mp hpos]

/-! ## 4. The outside co-pivot budget of a corner -/

/-- **The outside co-pivots total the corner pivot.**  At a corank-two corner the
complement triple's pivots sum to `3 − π_u`, so their co-pivots sum to `π_u`. -/
theorem sum_outside_copivot (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    ∑ d ∈ Cᶜ, (1 - sixSetPivot D d d) = cornerPivot D lam u := by
  classical
  have hcompl : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, hcard]; simp
  have hsumP : ∑ d ∈ Cᶜ, sixSetPivot D d d = 3 - cornerPivot D lam u := by
    simpa only [sixSetPivot, gapSelf, cornerPivot] using outside_pivot_sum D C hgap hPD
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hsumP, hcompl]
  norm_num

/-- **The light outside atoms use at most the corner pivot.**  Every outside
co-pivot is nonnegative and the co-weights are below one. -/
theorem sum_light_outside_coweight_le (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∑ c ∈ (lightSet D).filter (fun c => c ∉ C), (1 - D.weight c) * (1 - sixSetPivot D c c)
      ≤ cornerPivot D lam u := by
  classical
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hcap : ∀ d ∈ (Cᶜ : Finset (Fin 6)), sixSetPivot D d d ≤ 1 := fun d hd =>
    outside_pivot_le_one D C hlam hgap hPD hd
  have hsub : (lightSet D).filter (fun c => c ∉ C) ⊆ (Cᶜ : Finset (Fin 6)) := by
    intro c hc
    simp only [Finset.mem_filter] at hc
    simpa using hc.2
  calc ∑ c ∈ (lightSet D).filter (fun c => c ∉ C),
        (1 - D.weight c) * (1 - sixSetPivot D c c)
      ≤ ∑ c ∈ (lightSet D).filter (fun c => c ∉ C), (1 - sixSetPivot D c c) := by
        refine Finset.sum_le_sum fun c hc => ?_
        have hc1 : sixSetPivot D c c ≤ 1 := hcap c (hsub hc)
        nlinarith [D.weight_pos c, hc1]
    _ ≤ ∑ d ∈ (Cᶜ : Finset (Fin 6)), (1 - sixSetPivot D d d) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun d hd _ => ?_
        linarith [hcap d hd]
    _ = cornerPivot D lam u := sum_outside_copivot D C hcard hgap hPD

/-! ## 5. The light count of a corank-two corner -/

/-- **The inside light atoms carry the rest of the deficit.**  The light set of a
tie owes two units of co-weight deficit and the outside can supply at most the
corner pivot. -/
theorem sum_light_inside_coweight_ge (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    2 - cornerPivot D lam u
      ≤ ∑ c ∈ (lightSet D).filter (fun c => c ∈ C),
          (1 - D.weight c) * (1 - sixSetPivot D c c) := by
  classical
  have hbase := two_le_sum_lightSet_coweight_deficit D
  have hout := sum_light_outside_coweight_le D C hcard hlam hgap
  have hsplit := Finset.sum_filter_add_sum_filter_not (lightSet D) (fun c => c ∈ C)
    (fun c => (1 - D.weight c) * (1 - sixSetPivot D c c))
  linarith

/-- **The inside light pivots fall short.**  Each light co-pivot is capped by one
and the co-weights are strictly below one. -/
theorem sum_light_inside_pivot_lt (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∑ c ∈ (lightSet D).filter (fun c => c ∈ C), sixSetPivot D c c
      < (((lightSet D).filter (fun c => c ∈ C)).card : ℝ) - 2 + cornerPivot D lam u := by
  classical
  set S := (lightSet D).filter (fun c => c ∈ C) with hS
  have hlow := sum_light_inside_coweight_ge D htie C hcard hlam hgap
  rw [← hS] at hlow
  have hne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with hemp | hne
    · rw [hemp, Finset.sum_empty] at hlow
      have hpi : cornerPivot D lam u ≤ 1 := by
        simpa only [cornerPivot, gapSelf] using
          uPivot_le_one D C hlam hgap (sixSetGap_posDef_sixThree D)
      linarith
    · exact hne
  have hstrict : ∑ c ∈ S, (1 - D.weight c) * (1 - sixSetPivot D c c)
      < ∑ c ∈ S, (1 - sixSetPivot D c c) := by
    refine Finset.sum_lt_sum_of_nonempty hne fun c hc => ?_
    have hcl : sixSetPivot D c c < 1 := by
      rw [hS, Finset.mem_filter] at hc
      exact (mem_lightSet_iff D c).mp hc.1
    nlinarith [D.weight_pos c, hcl]
  have hcount : ∑ c ∈ S, (1 - sixSetPivot D c c)
      = (S.card : ℝ) - ∑ c ∈ S, sixSetPivot D c c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

/-- **At least two inside atoms of a corank-two corner are light.**  One light
inside atom could supply less than one unit of deficit, while the corner owes at
least `2 − π_u ≥ 1`. -/
theorem two_le_card_light_inside (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    2 ≤ ((lightSet D).filter (fun c => c ∈ C)).card := by
  classical
  set S := (lightSet D).filter (fun c => c ∈ C) with hS
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hpi : cornerPivot D lam u ≤ 1 := by
    simpa only [cornerPivot, gapSelf] using uPivot_le_one D C hlam hgap hPD
  have hlt := sum_light_inside_pivot_lt D htie C hcard hlam hgap
  rw [← hS] at hlt
  have hnn : 0 ≤ ∑ c ∈ S, sixSetPivot D c c :=
    Finset.sum_nonneg fun c _ => sixSetPivot_self_nonneg D (by norm_num) hPD c
  by_contra hcon
  push_neg at hcon
  have hle : (S.card : ℝ) ≤ 1 := by
    have : S.card ≤ 1 := by omega
    exact_mod_cast this
  linarith

/-- **Two light inside atoms force the corner pivot past one half.**  Their
pivots total less than the corner pivot, while the pivot law of a tie makes the
larger of the two reach `1 − π_u`. -/
theorem half_lt_cornerPivot_of_two_light_inside (D : WeightedDesign 6 3)
    (htie : IsTie D) (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ}
    (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (htwo : ((lightSet D).filter (fun c => c ∈ C)).card = 2) :
    1 / 2 < cornerPivot D lam u := by
  classical
  set S := (lightSet D).filter (fun c => c ∈ C) with hS
  obtain ⟨e1, e2, hne, hset⟩ := Finset.card_eq_two.mp htwo
  have hlt := sum_light_inside_pivot_lt D htie C hcard hlam hgap
  rw [← hS, htwo, hset, Finset.sum_insert (by simp [hne]), Finset.sum_singleton] at hlt
  have hlaw := tie_pair_pivot_law D htie hne
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have h1 : 0 ≤ sixSetPivot D e1 e1 := sixSetPivot_self_nonneg D (by norm_num) hPD e1
  have h2 : 0 ≤ sixSetPivot D e2 e2 := sixSetPivot_self_nonneg D (by norm_num) hPD e2
  norm_num at hlt
  rcases hlaw with hlaw | hlaw <;> linarith

end Gtz

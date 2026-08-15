/-
# The complement leverage law, at the design level

`Gtz.posDef_directionChartGap_compl_iff` reads a selection's gap off the labels
the selection OMITS, but it reads it on a direction chart.  Every consumer must
first place its stratum on a chart.  The same law holds on the design itself,
with no chart, no whitening and no square root, and this module lands it.

Write `K := subsetSum D univ - 1` for the full-selection gap.  Parseval makes
`K = ∑ c, (1 - weight c) • atomMatrix (atom c)`, so `K` is positive definite for
free.  For a label set `T` put `v y := ∑ c ∈ T, y c • atom c`.

The whole law is ONE algebraic identity, true for every `y` and every probe `u`,
with no positivity and no inverse anywhere:

  `∑_{c∈T} (y c - atom c ⬝ u)² + u ⬝ (S_{Tᶜ} - 1) u`
      `= ∑_{c∈T} (y c)² - 2 ⟨v y, u⟩ + u ⬝ K u`

because `subsetSum D T + (subsetSum D Tᶜ - 1) = K`.  At the dual probe
`u = K⁻¹ (v y)`, where the variational bound `2⟨v,u⟩ - u ⬝ K u ≤ v ⬝ K⁻¹ v` is
attained, the identity becomes an exact formula for

  `designComplementForm T y := ∑_{c∈T} (y c)² - (v y) ⬝ K⁻¹ (v y)`

and both directions of the equivalence fall out of it:

  `(subsetSum D Tᶜ - 1).PosDef  ↔  designComplementForm T y > 0 for every y ≠ 0 on T`

so a selection of `k` labels is read off the `m - k` labels it omits.  At `(6,3)`
both sides are triples.

The diagonal of that form is the full-selection pivot: at a single label the
complement form reads `1 - pivot D univ c`.  The trace identity at `univ` prices
those pivots, and the last part spends that price: at most `k` labels can carry
pivot one or more, so at least `m - k` labels carry pivot below one.  At `(6,3)`
that is three labels, and a candidate triple always exists.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.TraceIdentity
import Gtz.Design.MarginTransfer
import Gtz.Reduction.DescentLadder

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### The gap is symmetric -/

/-- An atom's outer square is Hermitian. -/
theorem isHermitian_atomMatrix (g : Fin k → ℝ) : (atomMatrix g).IsHermitian := by
  show (atomMatrix g)ᴴ = atomMatrix g
  ext i j
  simp [atomMatrix, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

/-- Every gap `S_C - 1` is Hermitian. -/
theorem isHermitian_designGap (D : WeightedDesign m k) (C : Finset (Fin m)) :
    (subsetSum D C - 1).IsHermitian := by
  have hsum : (subsetSum D C).IsHermitian := by
    show (subsetSum D C)ᴴ = subsetSum D C
    rw [subsetSum, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun c _ => (isHermitian_atomMatrix (D.atom c)).eq
  exact hsum.sub Matrix.isHermitian_one

/-! ### Weights and deficiencies -/

/-- With two or more labels every weight is strictly below one. -/
theorem design_weight_lt_one (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    D.weight c < 1 := by
  have hcard : 1 < Fintype.card (Fin m) := by rw [Fintype.card_fin]; omega
  obtain ⟨d, hd⟩ := Fintype.exists_ne_of_one_lt_card hcard c
  have hother : 0 < ∑ e ∈ Finset.univ.erase c, D.weight e :=
    Finset.sum_pos (fun e _ => D.weight_pos e)
      ⟨d, Finset.mem_erase.mpr ⟨hd, Finset.mem_univ d⟩⟩
  have hsplit := Finset.add_sum_erase Finset.univ D.weight (Finset.mem_univ c)
  have hone := D.weight_sum_one
  linarith

/-- Every deficiency `1 - weight` is strictly positive. -/
theorem deficiency_pos (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    0 < 1 - D.weight c := by
  linarith [design_weight_lt_one D hm c]

/-- The deficiencies sum to the label count minus one. -/
theorem sum_deficiency (D : WeightedDesign m k) :
    ∑ c, (1 - D.weight c) = (m : ℝ) - 1 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, D.weight_sum_one, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-! ### The full-selection gap read through Parseval -/

/-- **Parseval reads the full gap as the deficiency sum.**  Subtracting the
identity from the unweighted atom sum leaves each atom scaled by the weight it
does NOT carry. -/
theorem univGap_eq_deficiencySum (D : WeightedDesign m k) :
    subsetSum D Finset.univ - 1 = ∑ c, (1 - D.weight c) • atomMatrix (D.atom c) := by
  have hsplit : ∑ c, (1 - D.weight c) • atomMatrix (D.atom c)
      = (∑ c, atomMatrix (D.atom c)) - ∑ c, D.weight c • atomMatrix (D.atom c) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [sub_smul, one_smul]
  rw [hsplit, D.isParseval, subsetSum]

/-! ### The master bracket -/

/-- The combination the label set `T` produces from a coefficient vector. -/
noncomputable def complementCombination (D : WeightedDesign m k) (T : Finset (Fin m))
    (y : Fin m → ℝ) : Fin k → ℝ :=
  ∑ c ∈ T, y c • D.atom c

theorem dotProduct_complementCombination (D : WeightedDesign m k) (T : Finset (Fin m))
    (y : Fin m → ℝ) (u : Fin k → ℝ) :
    complementCombination D T y ⬝ᵥ u = ∑ c ∈ T, y c * (D.atom c ⬝ᵥ u) := by
  rw [complementCombination, sum_dotProduct]
  exact Finset.sum_congr rfl fun c _ => by rw [smul_dotProduct, smul_eq_mul]

/-- **THE MASTER BRACKET.**  For every coefficient vector and every probe, the
residual squares over `T` plus the complement gap form equal the coefficient
energy minus twice the pairing plus the full gap form.  No positivity is used and
no inverse occurs.  The whole content is
`subsetSum D T + (subsetSum D Tᶜ - 1) = subsetSum D univ - 1`. -/
theorem complementBracket (D : WeightedDesign m k) (T : Finset (Fin m))
    (y : Fin m → ℝ) (u : Fin k → ℝ) :
    (∑ c ∈ T, (y c - D.atom c ⬝ᵥ u) ^ 2)
        + u ⬝ᵥ ((subsetSum D Tᶜ - 1) *ᵥ u)
      = (∑ c ∈ T, (y c) ^ 2)
        - 2 * (complementCombination D T y ⬝ᵥ u)
        + u ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ u) := by
  have hsplit : subsetSum D Finset.univ - 1
      = subsetSum D T + (subsetSum D Tᶜ - 1) := by
    rw [subsetSum, subsetSum, subsetSum]
    rw [← Finset.sum_add_sum_compl T (fun c => atomMatrix (D.atom c))]
    abel
  have hT : u ⬝ᵥ (subsetSum D T *ᵥ u) = ∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2 := by
    rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun c _ => atom_form_eq_sq _ _
  have hexpand : ∑ c ∈ T, (y c - D.atom c ⬝ᵥ u) ^ 2
      = (∑ c ∈ T, (y c) ^ 2) - 2 * (∑ c ∈ T, y c * (D.atom c ⬝ᵥ u))
        + ∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hexpand, dotProduct_complementCombination, hsplit, Matrix.add_mulVec,
    dotProduct_add, hT]
  ring

/-! ### The variational bound for the inverse form -/

/-- The inverse form dominates every probe reading.  This is the completed square
`0 ≤ (u - K⁻¹v) ⬝ K (u - K⁻¹v)`, with no square root. -/
theorem designInverseForm_ge_probe {K : Matrix (Fin k) (Fin k) ℝ} (hK : K.PosDef)
    (v u : Fin k → ℝ) :
    2 * (v ⬝ᵥ u) - u ⬝ᵥ (K *ᵥ u) ≤ v ⬝ᵥ (K⁻¹ *ᵥ v) := by
  have hdet : IsUnit K.det := isUnit_iff_ne_zero.mpr (ne_of_gt hK.det_pos)
  have hKsymm : Kᵀ = K := by
    have h := hK.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hcollapse : K *ᵥ (K⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv K hdet, Matrix.one_mulVec]
  have hcross : (K⁻¹ *ᵥ v) ⬝ᵥ (K *ᵥ u) = v ⬝ᵥ u := by
    have hadj := dotProduct_mulVec_transpose K (K⁻¹ *ᵥ v) u
    rw [hKsymm, hcollapse] at hadj
    exact hadj.symm
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hK.posSemidef).2 (u - K⁻¹ *ᵥ v)
  rw [star_trivial] at hform
  have hexp : (u - K⁻¹ *ᵥ v) ⬝ᵥ (K *ᵥ (u - K⁻¹ *ᵥ v))
      = u ⬝ᵥ (K *ᵥ u) - 2 * (v ⬝ᵥ u) + v ⬝ᵥ (K⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
      hcollapse, hcross]
    have hsym : u ⬝ᵥ v = v ⬝ᵥ u := dotProduct_comm _ _
    have hdual : (K⁻¹ *ᵥ v) ⬝ᵥ v = v ⬝ᵥ (K⁻¹ *ᵥ v) := dotProduct_comm _ _
    rw [hsym, hdual]
    ring
  rw [hexp] at hform
  linarith

/-- The bound is attained at the dual probe. -/
theorem designInverseForm_eq_dual {K : Matrix (Fin k) (Fin k) ℝ} (hK : K.PosDef)
    (v : Fin k → ℝ) :
    2 * (v ⬝ᵥ (K⁻¹ *ᵥ v)) - (K⁻¹ *ᵥ v) ⬝ᵥ (K *ᵥ (K⁻¹ *ᵥ v)) = v ⬝ᵥ (K⁻¹ *ᵥ v) := by
  have hdet : IsUnit K.det := isUnit_iff_ne_zero.mpr (ne_of_gt hK.det_pos)
  have hcollapse : K *ᵥ (K⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv K hdet, Matrix.one_mulVec]
  rw [hcollapse, dotProduct_comm (K⁻¹ *ᵥ v) v]
  ring

/-! ### The complement form and the law -/

/-- **The complement form.**  The coefficient energy on `T` priced against the
inverse full gap.  It reads only the labels a selection OMITS. -/
noncomputable def designComplementForm (D : WeightedDesign m k) (T : Finset (Fin m))
    (y : Fin m → ℝ) : ℝ :=
  (∑ c ∈ T, (y c) ^ 2)
    - complementCombination D T y
        ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ complementCombination D T y)

/-- **THE EXACT FORMULA.**  At the dual probe the master bracket turns the
complement form into residual squares plus the complement gap form.  This single
equation carries both directions of the law. -/
theorem designComplementForm_eq_squares_add_gap (D : WeightedDesign m k) (T : Finset (Fin m))
    (hK : (subsetSum D Finset.univ - 1).PosDef) (y : Fin m → ℝ) :
    designComplementForm D T y
      = (∑ c ∈ T, (y c - D.atom c ⬝ᵥ
            ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ complementCombination D T y)) ^ 2)
        + ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ complementCombination D T y)
            ⬝ᵥ ((subsetSum D Tᶜ - 1) *ᵥ
              ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ complementCombination D T y)) := by
  set K := subsetSum D Finset.univ - 1 with hKdef
  set v := complementCombination D T y with hvdef
  have hbracket := complementBracket D T y (K⁻¹ *ᵥ v)
  rw [← hvdef, ← hKdef] at hbracket
  have hdual := designInverseForm_eq_dual hK v
  rw [designComplementForm, ← hvdef, ← hKdef, hbracket]
  linarith

/-- **The producer.**  A positive definite complement gap makes the complement
form strictly positive at every coefficient vector nonzero on `T`. -/
theorem designComplementForm_pos_of_posDef_complementGap (D : WeightedDesign m k)
    (T : Finset (Fin m)) (hK : (subsetSum D Finset.univ - 1).PosDef)
    (hcompl : (subsetSum D Tᶜ - 1).PosDef) (y : Fin m → ℝ)
    (hy : ∃ c ∈ T, y c ≠ 0) :
    0 < designComplementForm D T y := by
  rw [designComplementForm_eq_squares_add_gap D T hK y]
  set u := (subsetSum D Finset.univ - 1)⁻¹ *ᵥ complementCombination D T y with hudef
  rcases eq_or_ne u 0 with hu | hu
  · obtain ⟨c, hcT, hcne⟩ := hy
    have hsq : 0 < ∑ d ∈ T, (y d - D.atom d ⬝ᵥ u) ^ 2 := by
      refine Finset.sum_pos' (fun d _ => sq_nonneg _) ⟨c, hcT, ?_⟩
      rw [hu, dotProduct_zero, sub_zero]
      exact pow_two_pos_of_ne_zero hcne
    have hgap : u ⬝ᵥ ((subsetSum D Tᶜ - 1) *ᵥ u) = 0 := by
      rw [hu, zero_dotProduct]
    linarith
  · have hgap : 0 < u ⬝ᵥ ((subsetSum D Tᶜ - 1) *ᵥ u) := by
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hcompl).2 hu
      simpa using h
    have hsq : 0 ≤ ∑ d ∈ T, (y d - D.atom d ⬝ᵥ u) ^ 2 :=
      Finset.sum_nonneg fun d _ => sq_nonneg _
    linarith

/-- **The converse.**  If the complement form is positive at every coefficient
vector nonzero on `T`, the complement gap is positive definite.  The witness is
the coefficient vector the probe itself reads off `T`. -/
theorem posDef_complementGap_of_designComplementForm_pos (D : WeightedDesign m k)
    (T : Finset (Fin m)) (hK : (subsetSum D Finset.univ - 1).PosDef)
    (hform : ∀ y : Fin m → ℝ, (∃ c ∈ T, y c ≠ 0) → 0 < designComplementForm D T y) :
    (subsetSum D Tᶜ - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_designGap D Tᶜ, fun u hu => ?_⟩
  simp only [star_trivial]
  set y : Fin m → ℝ := fun c => if c ∈ T then D.atom c ⬝ᵥ u else 0 with hydef
  have hyT : ∀ c ∈ T, y c = D.atom c ⬝ᵥ u := by
    intro c hc; rw [hydef]; simp [hc]
  have hbracket := complementBracket D T y u
  have hres : ∑ c ∈ T, (y c - D.atom c ⬝ᵥ u) ^ 2 = 0 :=
    Finset.sum_eq_zero fun c hc => by rw [hyT c hc, sub_self]; ring
  rw [hres, zero_add] at hbracket
  have hbound := designInverseForm_ge_probe hK (complementCombination D T y) u
  have hle : designComplementForm D T y ≤ u ⬝ᵥ ((subsetSum D Tᶜ - 1) *ᵥ u) := by
    rw [designComplementForm, hbracket]
    linarith
  by_cases hnz : ∃ c ∈ T, y c ≠ 0
  · exact lt_of_lt_of_le (hform y hnz) hle
  · push Not at hnz
    have hzeroT : subsetSum D T *ᵥ u = 0 := by
      rw [subsetSum, Matrix.sum_mulVec]
      refine Finset.sum_eq_zero fun c hc => ?_
      have hc0 : D.atom c ⬝ᵥ u = 0 := by
        have h := hnz c hc; rwa [hyT c hc] at h
      rw [atomMatrix, vecMulVec_mulVec_eq, hc0, zero_smul]
    have hsplit : subsetSum D Finset.univ - 1
        = subsetSum D T + (subsetSum D Tᶜ - 1) := by
      rw [subsetSum, subsetSum, subsetSum]
      rw [← Finset.sum_add_sum_compl T (fun c => atomMatrix (D.atom c))]
      abel
    have hfull : 0 < u ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ u) := by
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hK).2 hu
      simpa using h
    rw [hsplit, Matrix.add_mulVec, dotProduct_add, hzeroT, dotProduct_zero,
      zero_add] at hfull
    exact hfull

/-- **THE COMPLEMENT LEVERAGE LAW, AT THE DESIGN LEVEL.**  A selection's gap is
positive definite exactly when the complement form is positive at every
coefficient vector supported on the labels the selection OMITS.  Generic in the
size and the rank, with no chart, no whitening and no square root. -/
theorem posDef_complementGap_iff_designComplementForm_pos (D : WeightedDesign m k)
    (T : Finset (Fin m)) (hK : (subsetSum D Finset.univ - 1).PosDef) :
    (subsetSum D Tᶜ - 1).PosDef
      ↔ ∀ y : Fin m → ℝ, (∃ c ∈ T, y c ≠ 0) → 0 < designComplementForm D T y :=
  ⟨fun hcompl y hy => designComplementForm_pos_of_posDef_complementGap D T hK hcompl y hy,
    fun hform => posDef_complementGap_of_designComplementForm_pos D T hK hform⟩

/-! ### The diagonal of the complement form is the full-selection pivot -/

/-- At a single label the complement form reads one minus that label's
full-selection pivot. -/
theorem designComplementForm_single (D : WeightedDesign m k) (c : Fin m) :
    designComplementForm D {c} (fun d => if d = c then 1 else 0)
      = 1 - pivot D Finset.univ c := by
  have hcomb : complementCombination D {c} (fun d => if d = c then 1 else 0) = D.atom c := by
    rw [complementCombination, Finset.sum_singleton]
    simp
  rw [designComplementForm, hcomb, pivot_eq_dot]
  simp

/-! ### The pivot budget at the full selection -/

/-- **The deficiency-weighted pivot budget.**  The trace identity at the full
selection has an empty complement, so the deficiency-weighted pivots sum to the
rank exactly. -/
theorem sum_deficiency_mul_pivot_univ (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ c, (1 - D.weight c) * pivot D Finset.univ c = (k : ℝ) := by
  have hid := trace_identity D Finset.univ (posDef_fullExcess D hm)
  rwa [Finset.compl_univ, Finset.sum_empty, add_zero] at hid

/-- Every full-selection pivot is nonnegative. -/
theorem pivot_univ_nonneg (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    0 ≤ pivot D Finset.univ c := by
  rw [pivot_eq_dot]
  have hinv : ((subsetSum D Finset.univ - 1)⁻¹).PosDef := (posDef_fullExcess D hm).inv
  rcases eq_or_ne (D.atom c) 0 with h0 | h0
  · rw [h0]; simp
  · have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hinv).2 h0
    simp only [star_trivial] at h
    exact h.le

/-- **THE CANDIDATE COUNT.**  At most `k` labels can carry a full-selection pivot
of one or more.  The deficiency budget is exactly the rank, each such label
spends at least its own deficiency, and the weights sum to one, so `k + 1` such
labels would overspend. -/
theorem card_le_rank_of_forall_pivot_univ_ge_one (D : WeightedDesign m k) (hm : 2 ≤ m)
    (T : Finset (Fin m)) (hT : ∀ c ∈ T, 1 ≤ pivot D Finset.univ c)
    (hne : T ≠ Finset.univ) :
    T.card ≤ k := by
  have hbudget := sum_deficiency_mul_pivot_univ D hm
  have hTspend : ∑ c ∈ T, (1 - D.weight c)
      ≤ ∑ c ∈ T, (1 - D.weight c) * pivot D Finset.univ c := by
    refine Finset.sum_le_sum fun c hc => ?_
    nlinarith [deficiency_pos D hm c, hT c hc]
  have houtside : 0 ≤ ∑ c ∈ Tᶜ, (1 - D.weight c) * pivot D Finset.univ c :=
    Finset.sum_nonneg fun c _ =>
      mul_nonneg (deficiency_pos D hm c).le (pivot_univ_nonneg D hm c)
  have hall : ∑ c ∈ T, (1 - D.weight c) * pivot D Finset.univ c
      + ∑ c ∈ Tᶜ, (1 - D.weight c) * pivot D Finset.univ c = (k : ℝ) := by
    rw [Finset.sum_add_sum_compl T (fun c => (1 - D.weight c) * pivot D Finset.univ c)]
    exact hbudget
  have hweightT : ∑ c ∈ T, D.weight c < 1 := by
    obtain ⟨c, hc⟩ : ∃ c, c ∉ T := by
      by_contra hcon
      push Not at hcon
      exact hne (Finset.eq_univ_iff_forall.mpr hcon)
    have hsplit := Finset.sum_add_sum_compl T D.weight
    have hpos : 0 < ∑ d ∈ Tᶜ, D.weight d :=
      Finset.sum_pos (fun d _ => D.weight_pos d) ⟨c, Finset.mem_compl.mpr hc⟩
    have hone := D.weight_sum_one
    linarith
  have hcardT : ∑ c ∈ T, (1 - D.weight c) = (T.card : ℝ) - ∑ c ∈ T, D.weight c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hbound : (T.card : ℝ) < (k : ℝ) + 1 := by linarith
  have : (T.card : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-! ### The rank-three consequence -/

/-- **At `(6,3)` a candidate triple always exists.**  At most three labels carry
a full-selection pivot of one or more, so at least three labels carry pivot below
one.  Each of those is a label whose erasure from the full selection still
dominates. -/
theorem three_le_card_pivot_univ_lt_one (D : WeightedDesign 6 3) :
    3 ≤ (Finset.univ.filter fun c => pivot D Finset.univ c < 1).card := by
  classical
  set high := Finset.univ.filter fun c => ¬ pivot D Finset.univ c < 1 with hhigh
  have hhighT : ∀ c ∈ high, 1 ≤ pivot D Finset.univ c := by
    intro c hc
    rw [hhigh, Finset.mem_filter] at hc
    exact not_lt.mp hc.2
  have hne : high ≠ Finset.univ := by
    intro hcon
    have hall : ∀ c : Fin 6, 1 ≤ pivot D Finset.univ c := fun c =>
      hhighT c (by rw [hcon]; exact Finset.mem_univ c)
    have hbudget := sum_deficiency_mul_pivot_univ D (by norm_num)
    have hge : ∑ c, (1 - D.weight c) ≤ ∑ c, (1 - D.weight c) * pivot D Finset.univ c := by
      refine Finset.sum_le_sum fun c _ => ?_
      nlinarith [deficiency_pos D (by norm_num) c, hall c]
    have hsum := sum_deficiency (D := D)
    rw [hsum] at hge
    norm_num at hbudget hge
    linarith
  have hle := card_le_rank_of_forall_pivot_univ_ge_one D (by norm_num) high hhighT hne
  have hpart : (Finset.univ.filter fun c => pivot D Finset.univ c < 1).card + high.card
      = (Finset.univ : Finset (Fin 6)).card := by
    rw [hhigh]
    exact Finset.card_filter_add_card_filter_not _
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  omega

end Gtz

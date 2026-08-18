import Gtz.Wave.CorankTwoOneShared
import Gtz.Wave.CorankOneNormalForm
import Gtz.Wave.TieStratumClassification
import Gtz.Wave.ShareOneForcingConic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The planar corner is weight-rigid: equal inside weights and `lam > 2`

At a corank-two `(6,3)` tie the dominator's gap is `lam • u uᵀ`.  This module
works in the PLANAR corner: every outside atom reads zero against `u`.  The
corner cannot be stated at `(5,3)` — it needs three outside atoms — so no
diamond hazard exists here by construction.

## The rigidity mechanism

Two resolve identities meet.  The rank-one gap resolves the gap direction
through the dominator (`Gtz.resolve_of_rankOneGap`):

  `Σ_{e∈C} (g_e·u) • g_e = (1 + lam) • u` ,

and Parseval resolves the same direction through the weighted atoms; in the
planar corner the outside atoms drop out:

  `Σ_{e∈C} t_e (g_e·u) • g_e = u` .

Their difference is a vanishing combination of the three inside atoms.  The
inside atoms admit no such combination — a common orthogonal direction would
read the gap form as `-|w|² = lam (u·w)² ≥ 0` — so every coefficient is zero:

  `(g_e·u) · (1 - (1 + lam) t_e) = 0` .

An inside atom with `g_e·u = 0` joins the three outside atoms in a coplanar
quadruple, which stress-freeness forbids
(`Gtz.not_coplanar_quadruple_of_stressFree`), and stress-freeness is free at a
primitive tie (`Gtz.isStressFreeDesign_of_isPrimitiveDesign_of_isTie`).  So at
a primitive planar corank-two tie EVERY inside weight equals `1/(1 + lam)`,
the inside weight total is `3/(1 + lam)`, and positivity of the outside
weights forces

  `lam > 2` .

This replaces the complement threshold, which is SILENT in the planar corner
(`Gtz.corankTwoPlanar_complement_refused`), with a floor that is not only
positive but quantitative, and it removes the low-`lam` corner from the
planar closure entirely.

## Field and rank

The order enters through the gap-form sign (`lam ≥ 0`) and through weight
positivity — both real.  The coplanar kill consumes stress-freeness at six
atoms, which is `(6,3)`-specific; the weight rigidity itself holds at every
size and rank three.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The weighted resolve -/

/-- **Parseval resolves every direction.**  The weighted atoms reconstruct any
vector: `Σ_c t_c (g_c·u) • g_c = u`. -/
theorem weighted_resolve (D : WeightedDesign m k) (u : Fin k → ℝ) :
    ∑ c, (D.weight c * (D.atom c ⬝ᵥ u)) • D.atom c = u := by
  have h := congrArg (fun M => M *ᵥ u) D.isParseval
  simp only [Matrix.sum_mulVec, Matrix.one_mulVec] at h
  calc ∑ c, (D.weight c * (D.atom c ⬝ᵥ u)) • D.atom c
      = ∑ c, (D.weight c • atomMatrix (D.atom c)) *ᵥ u := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq, smul_smul]
    _ = u := h

/-- **The planar corner concentrates the resolve on the subset.**  When every
atom off `C` reads zero against `u`, the weighted resolve is carried by `C`
alone. -/
theorem weighted_resolve_of_planarOutside (D : WeightedDesign m k)
    (C : Finset (Fin m)) {u : Fin k → ℝ}
    (houtside : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0) :
    ∑ e ∈ C, (D.weight e * (D.atom e ⬝ᵥ u)) • D.atom e = u := by
  have h := weighted_resolve D u
  rw [← Finset.sum_add_sum_compl C] at h
  have hout : ∑ d ∈ Cᶜ, (D.weight d * (D.atom d ⬝ᵥ u)) • D.atom d = 0 :=
    Finset.sum_eq_zero fun d hd => by rw [houtside d hd, mul_zero, zero_smul]
  rw [hout, add_zero] at h
  exact h

/-! ## 2. The inside atoms are independent -/

/-- **The dominator's atoms have no common orthogonal direction.**  One would
read the gap form as `-|w|² = lam (u·w)² ≥ 0`. -/
theorem not_forall_reads_zero_of_rankOneGap (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {w : Fin 3 → ℝ} (hwne : w ≠ 0)
    (hzero : ∀ c ∈ C, D.atom c ⬝ᵥ w = 0) : False := by
  have hsumzero : ∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2 = 0 :=
    Finset.sum_eq_zero fun c hc => by rw [hzero c hc]; ring
  have hform := dominationGap_form D C w
  rw [hsumzero, zero_sub] at hform
  have hval : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w)
      = lam * ((u ⬝ᵥ w) * (w ⬝ᵥ u)) := by
    rw [hgap, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul]
  rw [hval] at hform
  have hsq : 0 ≤ lam * ((u ⬝ᵥ w) * (w ⬝ᵥ u)) := by
    rw [dotProduct_comm u w]
    exact mul_nonneg hlam (mul_self_nonneg _)
  linarith [hform, hsq, dotProduct_self_pos hwne]

/-- **A vanishing combination of the dominator's atoms has zero
coefficients.**  Dot the combination against a direction orthogonal to the
other two atoms: only the chosen coefficient survives, and a surviving
coefficient would hand the design a common orthogonal direction. -/
theorem coeff_eq_zero_of_sum_smul_eq_zero_of_rankOneGap (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (co : Fin m → ℝ) (hsum : ∑ c ∈ C, co c • D.atom c = 0)
    {e : Fin m} (hmem : e ∈ C) : co e = 0 := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, hC⟩ := Finset.card_eq_three.mp hcard
  have hxnot : x ∉ ({y, z} : Finset (Fin m)) := by simp [hxy, hxz]
  have hynot : y ∉ ({z} : Finset (Fin m)) := by simp [hyz]
  rw [hC, Finset.sum_insert hxnot, Finset.sum_insert hynot,
    Finset.sum_singleton] at hsum
  have hmem' : e = x ∨ e = y ∨ e = z := by
    have := hmem
    rw [hC] at this
    simpa using this
  have hkill : ∀ first second third : Fin m,
      co first • D.atom first
          + (co second • D.atom second + co third • D.atom third) = 0 →
        (∀ c ∈ C, c = first ∨ c = second ∨ c = third) → co first = 0 := by
    intro first second third hcombo hcover
    obtain ⟨w, hwne, hwsecond, hwthird⟩ :=
      exists_orthogonal_to_pair (D.atom second) (D.atom third)
    by_contra hco
    have hdot := congrArg (fun v => v ⬝ᵥ w) hcombo
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct,
      hwsecond, hwthird, mul_zero, add_zero] at hdot
    have hfirst : D.atom first ⬝ᵥ w = 0 := by
      rcases mul_eq_zero.mp hdot with h | h
      · exact absurd h hco
      · exact h
    refine not_forall_reads_zero_of_rankOneGap D C hlam hgap hwne ?_
    intro c hc
    rcases hcover c hc with rfl | rfl | rfl
    · exact hfirst
    · exact hwsecond
    · exact hwthird
  have hcoverxyz : ∀ c ∈ C, c = x ∨ c = y ∨ c = z := by
    intro c hc
    have := hc
    rw [hC] at this
    simpa using this
  rcases hmem' with rfl | rfl | rfl
  · exact hkill e y z hsum hcoverxyz
  · refine hkill e x z ?_ (fun c hc => by
      rcases hcoverxyz c hc with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h))
    rw [← hsum]
    abel
  · refine hkill e x y ?_ (fun c hc => by
      rcases hcoverxyz c hc with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h)
    rw [← hsum]
    abel

/-! ## 3. The weight rigidity -/

/-- **The inside weight is pinned wherever the atom reads the gap
direction.**  The two resolves force `(g_e·u)(1 - (1+lam) t_e) = 0` at each
inside atom. -/
theorem insideWeight_eq_of_rankOneGap_of_planarOutside (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (houtside : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0)
    {e : Fin m} (hmem : e ∈ C) (hread : D.atom e ⬝ᵥ u ≠ 0) :
    D.weight e = 1 / (1 + lam) := by
  have h1 := resolve_of_rankOneGap D C hunit hgap
  have h2 := weighted_resolve_of_planarOutside D C houtside
  have hsum : ∑ c ∈ C,
      ((D.atom c ⬝ᵥ u) * (1 - (1 + lam) * D.weight c)) • D.atom c = 0 := by
    have hsplit : ∀ c ∈ C,
        ((D.atom c ⬝ᵥ u) * (1 - (1 + lam) * D.weight c)) • D.atom c
          = (D.atom c ⬝ᵥ u) • D.atom c
            - (1 + lam) • ((D.weight c * (D.atom c ⬝ᵥ u)) • D.atom c) := by
      intro c _
      rw [smul_smul, ← sub_smul]
      congr 1
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
      ← Finset.smul_sum, h1, h2, sub_self]
  have hkill := coeff_eq_zero_of_sum_smul_eq_zero_of_rankOneGap D C hcard hlam
    hgap (fun c => (D.atom c ⬝ᵥ u) * (1 - (1 + lam) * D.weight c)) hsum hmem
  have hone : (0 : ℝ) < 1 + lam := by linarith
  rcases mul_eq_zero.mp hkill with h | h
  · exact absurd h hread
  · field_simp
    linarith

/-! ## 4. The coplanar kill -/

/-- **An inside atom off the gap direction is forbidden.**  It would join the
three planar outside atoms in a quadruple orthogonal to `u`, which
stress-freeness forbids, and a primitive tie is stress-free. -/
theorem uReading_ne_zero_of_planarOutside_of_primitive (D : WeightedDesign 6 3)
    (htie : IsTie D) (hprimitive : IsPrimitiveDesign D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {u : Fin 3 → ℝ} (hune : u ≠ 0)
    (houtside : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0)
    {e : Fin 6} (hmem : e ∈ C) : D.atom e ⬝ᵥ u ≠ 0 := by
  intro hzero
  have hccard : Cᶜ.card = 3 := card_compl_eq_three_of_card_eq_three C hcard
  obtain ⟨d₁, d₂, d₃, h12, h13, h23, hCc⟩ := Finset.card_eq_three.mp hccard
  have hd₁ : d₁ ∈ Cᶜ := by rw [hCc]; simp
  have hd₂ : d₂ ∈ Cᶜ := by rw [hCc]; simp
  have hd₃ : d₃ ∈ Cᶜ := by rw [hCc]; simp
  have hne : ∀ d ∈ Cᶜ, e ≠ d := by
    intro d hd heq
    rw [heq] at hmem
    exact (Finset.mem_compl.mp hd) hmem
  have hsf := isStressFreeDesign_of_isPrimitiveDesign_of_isTie D hprimitive htie
  exact not_coplanar_quadruple_of_stressFree D (fun s hs => hsf s hs) u hune
    e d₁ d₂ d₃ (hne d₁ hd₁) (hne d₂ hd₂) (hne d₃ hd₃) h12 h13 h23
    ⟨hzero, houtside d₁ hd₁, houtside d₂ hd₂, houtside d₃ hd₃⟩

/-! ## 5. The planar rigidity -/

/-- **THE PLANAR RIGIDITY.**  At a primitive `(6,3)` tie whose gap at `C` is
`lam • u uᵀ` with every outside atom planar: every inside weight equals
`1/(1 + lam)`, and `lam > 2`.  The planar-native floor replaces the silent
complement threshold, and the low-`lam` corner is empty. -/
theorem planar_insideWeights_eq_and_lam_gt_two (D : WeightedDesign 6 3)
    (htie : IsTie D) (hprimitive : IsPrimitiveDesign D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (houtside : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0) :
    (∀ e ∈ C, D.weight e = 1 / (1 + lam)) ∧ 2 < lam := by
  have hune : u ≠ 0 := by
    intro h
    rw [h] at hunit
    simp at hunit
  have hweights : ∀ e ∈ C, D.weight e = 1 / (1 + lam) := fun e hmem =>
    insideWeight_eq_of_rankOneGap_of_planarOutside D C hcard hlam hunit hgap
      houtside hmem
      (uReading_ne_zero_of_planarOutside_of_primitive D htie hprimitive C
        hcard hune houtside hmem)
  refine ⟨hweights, ?_⟩
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hsum := D.weight_sum_one
  rw [← Finset.sum_add_sum_compl C] at hsum
  have hin : ∑ e ∈ C, D.weight e = 3 * (1 / (1 + lam)) := by
    rw [Finset.sum_congr rfl hweights, Finset.sum_const, hcard]
    simp [mul_comm]
  have hccard : Cᶜ.card = 3 := card_compl_eq_three_of_card_eq_three C hcard
  have hout : 0 < ∑ d ∈ Cᶜ, D.weight d :=
    Finset.sum_pos (fun d _ => D.weight_pos d)
      (Finset.card_pos.mp (by rw [hccard]; norm_num))
  rw [hin] at hsum
  have hlt : 3 * (1 / (1 + lam)) < 1 := by linarith
  rw [mul_one_div, div_lt_one hone] at hlt
  linarith

end Gtz

import Gtz.Wave.CorankTwoPlanarRigidity
import Gtz.Wave.WeightedHalfPlane

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The non-planar corank-two corner: the exact identity layer

At a corank-two `(6,3)` tie the dominator's gap is `lam • u uᵀ`.  The planar
corner (every outside atom orthogonal to `u`) is closed
(`Gtz.corankTwoPlanar_absurd`).  This module builds the exact identity layer
of the remaining corner, where some outside atom reads `u` nontrivially.

## The inside Gram is explicit

The rank-one gap pins every inner product of the dominator's atoms
(`Gtz.insideGram_of_rankOneGap`):

  `(1+lam)·(g_e·g_f) = (1+lam)·δ_ef + lam·(g_e·u)(g_f·u)` .

The proof reads the coordinates of `S_C g_f = g_f + lam (u·g_f) u` in the
basis of inside atoms and matches them against the resolve identity; the
basis property is `Gtz.coeff_eq_zero_of_sum_smul_eq_zero_of_rankOneGap`.

## The master reading

Subtracting the gap from Parseval prices the weighted outside mass at every
pair of directions (`Gtz.outside_reading_of_rankOneGap`):

  `(1+lam)·Σ_{d∉C} t_d (q_d·y)(q_d·w)
     = lam·(y·w) − lam·(u·y)(u·w) − Σ_{e∈C} s_e (g_e·y)(g_e·w)` ,

with `s_e := (1+lam)·t_e − 1` the inside weight deviations.  Its instances
are the `u`-mass block, the cross block, and the plane isotropy with inside
corrections.  Reading it at the explicit dual basis vector
`(1+lam)·g_f − lam(g_f·u)·u` gives the unconditional inside weight cap
`s_f·(1+lam) ≤ lam(1+lam) − lam(g_f·u)²` (`Gtz.insideWeight_cap_of_rankOneGap`).

## The non-planar deficit

In the planar corner the inside weights are pinned at `s_e = 0`.  One
off-plane outside atom forces a strict deficit: `Σ_e s_e (g_e·u)² < 0`, so
some inside weight drops strictly below `1/(1+lam)`
(`Gtz.exists_inside_deficit_of_nonplanar`).  The weight rigidity of the
planar corner is broken exactly by the outside `u`-mass.

The corner needs three outside atoms, so nothing here can be stated at
`(5,3)`: there is no diamond hazard, by construction.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The inside Gram identity -/

/-- **The rank-one gap pins the inside Gram.**  For atoms of the dominator,
`(1+lam)·(g_e·g_f) = (1+lam)·δ_ef + lam·(g_e·u)(g_f·u)`. -/
theorem insideGram_of_rankOneGap (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e f : Fin m} (he : e ∈ C) (hf : f ∈ C) :
    (1 + lam) * (D.atom e ⬝ᵥ D.atom f)
      = (1 + lam) * (if e = f then 1 else 0)
        + lam * ((D.atom e ⬝ᵥ u) * (D.atom f ⬝ᵥ u)) := by
  classical
  have hres := resolve_of_rankOneGap D C hunit hgap
  have hmul : subsetSum D C *ᵥ D.atom f
      = D.atom f + (lam * (u ⬝ᵥ D.atom f)) • u := by
    rw [sub_eq_iff_eq_add.mp hgap, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq, smul_smul, add_comm]
  have hsum0 : ∑ c ∈ C, (D.atom c ⬝ᵥ D.atom f) • D.atom c
      = D.atom f + (lam * (u ⬝ᵥ D.atom f)) • u := by
    rw [← hmul, subsetSum, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun c _ => by rw [atomMatrix, vecMulVec_mulVec_eq]
  set co : Fin m → ℝ := fun c =>
    (1 + lam) * (D.atom c ⬝ᵥ D.atom f)
      - (1 + lam) * (if c = f then 1 else 0)
      - lam * ((D.atom c ⬝ᵥ u) * (D.atom f ⬝ᵥ u)) with hco
  have h1 : ∑ c ∈ C, ((1 + lam) * (D.atom c ⬝ᵥ D.atom f)) • D.atom c
      = (1 + lam) • (D.atom f + (lam * (u ⬝ᵥ D.atom f)) • u) := by
    rw [← hsum0, Finset.smul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [smul_smul]
  have h2 : ∑ c ∈ C, ((1 + lam) * (if c = f then 1 else 0)) • D.atom c
      = (1 + lam) • D.atom f := by
    rw [Finset.sum_eq_single_of_mem f hf (fun c _ hne => by simp [hne])]
    simp
  have h3 : ∑ c ∈ C, (lam * ((D.atom c ⬝ᵥ u) * (D.atom f ⬝ᵥ u))) • D.atom c
      = (lam * (D.atom f ⬝ᵥ u) * (1 + lam)) • u := by
    calc ∑ c ∈ C, (lam * ((D.atom c ⬝ᵥ u) * (D.atom f ⬝ᵥ u))) • D.atom c
        = (lam * (D.atom f ⬝ᵥ u)) • ∑ c ∈ C, (D.atom c ⬝ᵥ u) • D.atom c := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [smul_smul]
          congr 1
          ring
      _ = (lam * (D.atom f ⬝ᵥ u)) • ((1 + lam) • u) := by rw [hres]
      _ = (lam * (D.atom f ⬝ᵥ u) * (1 + lam)) • u := by rw [smul_smul]
  have hzero : ∑ c ∈ C, co c • D.atom c = 0 := by
    have hsplit : ∀ c ∈ C, co c • D.atom c
        = ((1 + lam) * (D.atom c ⬝ᵥ D.atom f)) • D.atom c
          - ((1 + lam) * (if c = f then 1 else 0)) • D.atom c
          - (lam * ((D.atom c ⬝ᵥ u) * (D.atom f ⬝ᵥ u))) • D.atom c := by
      intro c _
      rw [hco]
      simp only [sub_smul]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, h1, h2, h3, dotProduct_comm u (D.atom f)]
    module
  have hcoe := coeff_eq_zero_of_sum_smul_eq_zero_of_rankOneGap D C hcard hlam
    hgap co hzero he
  rw [hco] at hcoe
  linarith [hcoe]

/-- The inside leverage: `(1+lam)·|g_e|² = (1+lam) + lam·(g_e·u)²`. -/
theorem insideGram_self_of_rankOneGap (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e : Fin m} (he : e ∈ C) :
    (1 + lam) * (D.atom e ⬝ᵥ D.atom e)
      = (1 + lam) + lam * (D.atom e ⬝ᵥ u) ^ 2 := by
  have h := insideGram_of_rankOneGap D C hcard hlam hunit hgap he he
  norm_num at h
  linear_combination h

/-- The inside off-diagonal: for `e ≠ f` in the dominator,
`(1+lam)·(g_e·g_f) = lam·(g_e·u)(g_f·u)`. -/
theorem insideGram_offDiag_of_rankOneGap (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e f : Fin m} (he : e ∈ C) (hf : f ∈ C) (hef : e ≠ f) :
    (1 + lam) * (D.atom e ⬝ᵥ D.atom f)
      = lam * ((D.atom e ⬝ᵥ u) * (D.atom f ⬝ᵥ u)) := by
  have h := insideGram_of_rankOneGap D C hcard hlam hunit hgap he hf
  simp only [if_neg hef, mul_zero, zero_add] at h
  exact h

/-! ## 2. The master reading -/

/-- **The master reading.**  The weighted outside mass at any pair of
directions equals the plane projection of `lam` times the metric, corrected
by the inside weight deviations `s_e = (1+lam)·t_e − 1`. -/
theorem outside_reading_of_rankOneGap (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) (y w : Fin 3 → ℝ) :
    (1 + lam) * ∑ d ∈ Cᶜ, D.weight d * ((D.atom d ⬝ᵥ y) * (D.atom d ⬝ᵥ w))
      = lam * (y ⬝ᵥ w) - lam * ((u ⬝ᵥ y) * (u ⬝ᵥ w))
        - ∑ e ∈ C, ((1 + lam) * D.weight e - 1)
            * ((D.atom e ⬝ᵥ y) * (D.atom e ⬝ᵥ w)) := by
  classical
  have hmul : subsetSum D C *ᵥ w = w + (lam * (u ⬝ᵥ w)) • u := by
    rw [sub_eq_iff_eq_add.mp hgap, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq, smul_smul, add_comm]
  have hin : ∑ e ∈ C, (D.atom e ⬝ᵥ y) * (D.atom e ⬝ᵥ w)
      = y ⬝ᵥ w + lam * ((u ⬝ᵥ y) * (u ⬝ᵥ w)) := by
    have hdot := congrArg (fun v => y ⬝ᵥ v) hmul
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hdot
    have hexp : y ⬝ᵥ (subsetSum D C *ᵥ w)
        = ∑ e ∈ C, (D.atom e ⬝ᵥ y) * (D.atom e ⬝ᵥ w) := by
      rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
        dotProduct_comm y (D.atom e)]
      ring
    rw [hexp] at hdot
    rw [hdot, dotProduct_comm y u]
    ring
  have hall := dotProduct_eq_sum_weight_mul_dotProduct D y w
  rw [← Finset.sum_add_sum_compl C] at hall
  have hshape : ∀ c : Fin m,
      D.weight c * (D.atom c ⬝ᵥ y) * (D.atom c ⬝ᵥ w)
        = D.weight c * ((D.atom c ⬝ᵥ y) * (D.atom c ⬝ᵥ w)) := fun c => by ring
  simp only [hshape] at hall
  have hsub : ∑ e ∈ C, ((1 + lam) * D.weight e - 1)
        * ((D.atom e ⬝ᵥ y) * (D.atom e ⬝ᵥ w))
      = (1 + lam) * ∑ e ∈ C, D.weight e * ((D.atom e ⬝ᵥ y) * (D.atom e ⬝ᵥ w))
        - ∑ e ∈ C, (D.atom e ⬝ᵥ y) * (D.atom e ⬝ᵥ w) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [hsub, hin]
  linear_combination (-(1 + lam)) * hall

/-- The `u`-mass block: the weighted outside `u`-mass is the negative of the
inside deviation mass. -/
theorem outside_uMass_of_rankOneGap (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    (1 + lam) * ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ u) ^ 2
      = - ∑ e ∈ C, ((1 + lam) * D.weight e - 1) * (D.atom e ⬝ᵥ u) ^ 2 := by
  have h := outside_reading_of_rankOneGap D C hgap u u
  rw [hunit] at h
  have hsq : ∀ c : Fin m,
      (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ u) = (D.atom c ⬝ᵥ u) ^ 2 := fun c => by
    ring
  simp only [hsq] at h
  rw [h]
  ring

/-- The cross block: against any `w ⊥ u` the weighted outside cross sum is
the negative of the inside deviation cross sum. -/
theorem outside_cross_of_rankOneGap (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} {u w : Fin 3 → ℝ} (hw : w ⬝ᵥ u = 0)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    (1 + lam) * ∑ d ∈ Cᶜ, D.weight d * ((D.atom d ⬝ᵥ u) * (D.atom d ⬝ᵥ w))
      = - ∑ e ∈ C, ((1 + lam) * D.weight e - 1)
          * ((D.atom e ⬝ᵥ u) * (D.atom e ⬝ᵥ w)) := by
  have h := outside_reading_of_rankOneGap D C hgap u w
  have huw : u ⬝ᵥ w = 0 := by rwa [dotProduct_comm] at hw
  rw [huw] at h
  rw [h]
  ring

/-! ## 3. The resolve difference -/

/-- **The resolve difference.**  The inside deviations resolve the weighted
outside `u`-moment: the planar corner's weight rigidity generalizes to a
linear system driven by the off-plane outside atoms. -/
theorem nonplanar_resolve_difference (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∑ e ∈ C, ((D.atom e ⬝ᵥ u) * (1 - (1 + lam) * D.weight e)) • D.atom e
      = (1 + lam) • ∑ d ∈ Cᶜ, (D.weight d * (D.atom d ⬝ᵥ u)) • D.atom d := by
  have h1 := resolve_of_rankOneGap D C hunit hgap
  have h2 := weighted_resolve D u
  rw [← Finset.sum_add_sum_compl C] at h2
  have hsplit : ∀ e ∈ C,
      ((D.atom e ⬝ᵥ u) * (1 - (1 + lam) * D.weight e)) • D.atom e
        = (D.atom e ⬝ᵥ u) • D.atom e
          - (1 + lam) • ((D.weight e * (D.atom e ⬝ᵥ u)) • D.atom e) := by
    intro e _
    rw [smul_smul, ← sub_smul]
    congr 1
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.smul_sum,
    h1]
  have hC : ∑ e ∈ C, (D.weight e * (D.atom e ⬝ᵥ u)) • D.atom e
      = u - ∑ d ∈ Cᶜ, (D.weight d * (D.atom d ⬝ᵥ u)) • D.atom d :=
    eq_sub_of_add_eq h2
  rw [hC, smul_sub]
  abel

/-! ## 4. The inside weight cap -/

/-- **The inside weight cap.**  Reading the master identity at the explicit
dual basis vector `(1+lam)·g_f − lam(g_f·u)·u` prices every inside weight:
`((1+lam)·t_f − 1)·(1+lam) ≤ lam·(1+lam) − lam·(g_f·u)²`.  Unconditional at
the corner — no tie hypothesis. -/
theorem insideWeight_cap_of_rankOneGap (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {f : Fin m} (hf : f ∈ C) :
    ((1 + lam) * D.weight f - 1) * (1 + lam)
      ≤ lam * (1 + lam) - lam * (D.atom f ⬝ᵥ u) ^ 2 := by
  classical
  set hdual : Fin 3 → ℝ :=
    (1 + lam) • D.atom f - (lam * (D.atom f ⬝ᵥ u)) • u with hdualdef
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hatom : ∀ c ∈ C, D.atom c ⬝ᵥ hdual
      = (if c = f then (1 : ℝ) else 0) * (1 + lam) := by
    intro c hc
    have hgram := insideGram_of_rankOneGap D C hcard hlam hunit hgap hc hf
    rw [hdualdef, dotProduct_sub, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    linear_combination hgram
  have huread : u ⬝ᵥ hdual = D.atom f ⬝ᵥ u := by
    rw [hdualdef, dotProduct_sub, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, hunit, dotProduct_comm u (D.atom f)]
    ring
  have hself : hdual ⬝ᵥ hdual
      = (1 + lam) ^ 2 - lam * (D.atom f ⬝ᵥ u) ^ 2 := by
    have hff := insideGram_self_of_rankOneGap D C hcard hlam hunit hgap hf
    have hexp : hdual ⬝ᵥ hdual
        = (1 + lam) ^ 2 * (D.atom f ⬝ᵥ D.atom f)
          - 2 * (1 + lam) * (lam * (D.atom f ⬝ᵥ u)) * (D.atom f ⬝ᵥ u)
          + (lam * (D.atom f ⬝ᵥ u)) ^ 2 * (u ⬝ᵥ u) := by
      rw [hdualdef]
      simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, dotProduct_comm u (D.atom f)]
      ring
    rw [hexp, hunit]
    linear_combination (1 + lam) * hff
  have hread := outside_reading_of_rankOneGap D C hgap hdual hdual
  have hinC : ∑ e ∈ C, ((1 + lam) * D.weight e - 1)
        * ((D.atom e ⬝ᵥ hdual) * (D.atom e ⬝ᵥ hdual))
      = ((1 + lam) * D.weight f - 1) * (1 + lam) ^ 2 := by
    rw [Finset.sum_eq_single_of_mem f hf (fun c hc hne => by
      rw [hatom c hc, if_neg hne]
      ring)]
    rw [hatom f hf, if_pos rfl]
    ring
  have hnn : 0 ≤ ∑ d ∈ Cᶜ, D.weight d
      * ((D.atom d ⬝ᵥ hdual) * (D.atom d ⬝ᵥ hdual)) :=
    Finset.sum_nonneg fun d _ =>
      mul_nonneg (D.weight_pos d).le (mul_self_nonneg _)
  rw [hinC, hself, huread] at hread
  nlinarith [hread, hnn, hone, mul_pos hone hone]

/-! ## 5. The non-planar deficit -/

/-- **One off-plane outside atom breaks the planar weight rigidity.**  The
inside deviation mass `Σ_e s_e (g_e·u)²` is strictly negative, so some
inside weight is strictly below `1/(1+lam)`. -/
theorem exists_inside_deficit_of_nonplanar (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {d0 : Fin m} (hd0 : d0 ∈ Cᶜ) (hread : D.atom d0 ⬝ᵥ u ≠ 0) :
    ∃ e ∈ C, (1 + lam) * D.weight e < 1 := by
  classical
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have humass := outside_uMass_of_rankOneGap D C hunit hgap
  have hpos : 0 < ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ u) ^ 2 := by
    have habs : 0 < |D.atom d0 ⬝ᵥ u| := abs_pos.mpr hread
    have hsqpos : 0 < (D.atom d0 ⬝ᵥ u) ^ 2 := by
      rw [← sq_abs]
      exact pow_pos habs 2
    exact Finset.sum_pos' (fun d _ =>
      mul_nonneg (D.weight_pos d).le (sq_nonneg _))
      ⟨d0, hd0, mul_pos (D.weight_pos d0) hsqpos⟩
  by_contra hcon
  push_neg at hcon
  have hterm : ∀ e ∈ C,
      0 ≤ ((1 + lam) * D.weight e - 1) * (D.atom e ⬝ᵥ u) ^ 2 := fun e he =>
    mul_nonneg (by linarith [hcon e he]) (sq_nonneg _)
  have hsum : 0 ≤ ∑ e ∈ C, ((1 + lam) * D.weight e - 1) * (D.atom e ⬝ᵥ u) ^ 2 :=
    Finset.sum_nonneg hterm
  nlinarith [humass, hpos, hsum, hone]


/-! ## 6. The outside plane cover -/

/-- The outside weight total: `(1+lam)·Σ_{d∉C} t_d = lam − 2 − Σ_e s_e`. -/
theorem outsideWeight_total_of_rankOneGap (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) (lam : ℝ) :
    (1 + lam) * ∑ d ∈ Cᶜ, D.weight d
      = lam - 2 - ∑ e ∈ C, ((1 + lam) * D.weight e - 1) := by
  have hsum := D.weight_sum_one
  rw [← Finset.sum_add_sum_compl C] at hsum
  have hin : ∑ e ∈ C, ((1 + lam) * D.weight e - 1)
      = (1 + lam) * ∑ e ∈ C, D.weight e - 3 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hcard]
    norm_num
  rw [hin]
  linear_combination (1 + lam) * hsum

/-- **The outside plane cover.**  At the corner, the unweighted outside atoms
strictly cover the norm on the whole plane orthogonal to the gap direction:
`|w|² < Σ_{d∉C} (q_d·w)²`.  The planar corner's outside positivity
generalizes with the inside deviation corrections absorbed by the weight
identities. -/
theorem outside_plane_cover_of_rankOneGap (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) (hne : Cᶜ.Nonempty)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {w : Fin 3 → ℝ} (hw : w ⬝ᵥ u = 0) (hwne : w ≠ 0) :
    w ⬝ᵥ w < ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ w) ^ 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hone : (0 : ℝ) < 1 + lam := by linarith
  -- the isotropy instance at (w, w)
  have h1 := outside_reading_of_rankOneGap D C hgap w w
  have huw : u ⬝ᵥ w = 0 := by rwa [dotProduct_comm] at hw
  rw [huw] at h1
  have hsq : ∀ c : Fin m,
      (D.atom c ⬝ᵥ w) * (D.atom c ⬝ᵥ w) = (D.atom c ⬝ᵥ w) ^ 2 := fun c => by
    ring
  simp only [hsq, mul_zero, zero_mul, sub_zero] at h1
  -- the inside plane Parseval
  have h2 := planeMass_of_rankOneGap D C hw hgap
  -- the crude outside bound under the contradiction hypothesis
  have h3 : ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ w) ^ 2
      ≤ (∑ d ∈ Cᶜ, D.weight d) * (w ⬝ᵥ w) := by
    calc ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ w) ^ 2
        ≤ ∑ d ∈ Cᶜ, D.weight d * ∑ d' ∈ Cᶜ, (D.atom d' ⬝ᵥ w) ^ 2 := by
          refine Finset.sum_le_sum fun d hd => ?_
          refine mul_le_mul_of_nonneg_left ?_ (D.weight_pos d).le
          exact Finset.single_le_sum
            (f := fun d' => (D.atom d' ⬝ᵥ w) ^ 2)
            (fun d' _ => sq_nonneg _) hd
      _ ≤ ∑ d ∈ Cᶜ, D.weight d * (w ⬝ᵥ w) := by
          refine Finset.sum_le_sum fun d _ => ?_
          exact mul_le_mul_of_nonneg_left hcon (D.weight_pos d).le
      _ = (∑ d ∈ Cᶜ, D.weight d) * (w ⬝ᵥ w) := by rw [Finset.sum_mul]
  -- the outside weight total
  have h4 := outsideWeight_total_of_rankOneGap D C hcard lam
  -- the strict inside reading: some inside atom reads the witness
  have h5 : ∃ e0 ∈ C, (D.atom e0 ⬝ᵥ w) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact not_forall_reads_zero_of_rankOneGap D C hlam hgap hwne hall
  obtain ⟨e0, he0, hread0⟩ := h5
  -- the strict co-coefficient sum at the reading atom
  have hcoeff : 0 < ∑ f ∈ C.erase e0, (1 + lam) * D.weight f := by
    refine Finset.sum_pos (fun f _ => mul_pos hone (D.weight_pos f)) ?_
    rw [← Finset.card_pos, Finset.card_erase_of_mem he0, hcard]
    norm_num
  -- the remainder is positive: some inside atom reads with a positive co-sum
  have hR : 0 < ∑ e ∈ C, (∑ f ∈ C.erase e, (1 + lam) * D.weight f)
      * (D.atom e ⬝ᵥ w) ^ 2 := by
    refine Finset.sum_pos' (fun e _ => mul_nonneg ?_ (sq_nonneg _))
      ⟨e0, he0, ?_⟩
    · exact Finset.sum_nonneg fun f _ => (mul_pos hone (D.weight_pos f)).le
    · refine mul_pos hcoeff ?_
      positivity
  -- expand the remainder against the plane Parseval
  have hsplit : ∀ e ∈ C, ∑ f ∈ C.erase e, (1 + lam) * D.weight f
      = (∑ f ∈ C, (1 + lam) * D.weight f) - (1 + lam) * D.weight e := by
    intro e he
    rw [← Finset.add_sum_erase C _ he]
    ring
  have hRid : ∑ e ∈ C, (∑ f ∈ C.erase e, (1 + lam) * D.weight f)
        * (D.atom e ⬝ᵥ w) ^ 2
      = (∑ f ∈ C, (1 + lam) * D.weight f) * (w ⬝ᵥ w)
        - ∑ e ∈ C, ((1 + lam) * D.weight e) * (D.atom e ⬝ᵥ w) ^ 2 := by
    calc ∑ e ∈ C, (∑ f ∈ C.erase e, (1 + lam) * D.weight f)
          * (D.atom e ⬝ᵥ w) ^ 2
        = ∑ e ∈ C, ((∑ f ∈ C, (1 + lam) * D.weight f) * (D.atom e ⬝ᵥ w) ^ 2
            - ((1 + lam) * D.weight e) * (D.atom e ⬝ᵥ w) ^ 2) := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [hsplit e he]
          ring
      _ = (∑ f ∈ C, (1 + lam) * D.weight f)
            * (∑ e ∈ C, (D.atom e ⬝ᵥ w) ^ 2)
            - ∑ e ∈ C, ((1 + lam) * D.weight e) * (D.atom e ⬝ᵥ w) ^ 2 := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ f ∈ C, (1 + lam) * D.weight f) * (w ⬝ᵥ w)
            - ∑ e ∈ C, ((1 + lam) * D.weight e) * (D.atom e ⬝ᵥ w) ^ 2 := by
          rw [h2]
  rw [hRid] at hR
  -- the deviation mass identity
  have hS1 : ∑ e ∈ C, ((1 + lam) * D.weight e - 1) * (D.atom e ⬝ᵥ w) ^ 2
      = ∑ e ∈ C, ((1 + lam) * D.weight e) * (D.atom e ⬝ᵥ w) ^ 2
        - w ⬝ᵥ w := by
    calc ∑ e ∈ C, ((1 + lam) * D.weight e - 1) * (D.atom e ⬝ᵥ w) ^ 2
        = ∑ e ∈ C, (((1 + lam) * D.weight e) * (D.atom e ⬝ᵥ w) ^ 2
            - (D.atom e ⬝ᵥ w) ^ 2) :=
          Finset.sum_congr rfl fun e _ => by ring
      _ = ∑ e ∈ C, ((1 + lam) * D.weight e) * (D.atom e ⬝ᵥ w) ^ 2
            - w ⬝ᵥ w := by
          rw [Finset.sum_sub_distrib, h2]
  -- the K-ledger bridges
  have hK : ∑ e ∈ C, ((1 + lam) * D.weight e - 1)
      = (∑ f ∈ C, (1 + lam) * D.weight f) - 3 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard]
    norm_num
  have hDW : (∑ e ∈ C, ((1 + lam) * D.weight e - 1)) * (w ⬝ᵥ w)
      = (∑ f ∈ C, (1 + lam) * D.weight f) * (w ⬝ᵥ w) - 3 * (w ⬝ᵥ w) := by
    rw [hK]
    ring
  -- the chained crude bound
  have hchain : (1 + lam) * ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ w) ^ 2
      ≤ lam * (w ⬝ᵥ w) - 2 * (w ⬝ᵥ w)
        - (∑ e ∈ C, ((1 + lam) * D.weight e - 1)) * (w ⬝ᵥ w) := by
    have hmul := mul_le_mul_of_nonneg_left h3 hone.le
    calc (1 + lam) * ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ w) ^ 2
        ≤ (1 + lam) * ((∑ d ∈ Cᶜ, D.weight d) * (w ⬝ᵥ w)) := hmul
      _ = ((1 + lam) * ∑ d ∈ Cᶜ, D.weight d) * (w ⬝ᵥ w) := by ring
      _ = (lam - 2 - ∑ e ∈ C, ((1 + lam) * D.weight e - 1)) * (w ⬝ᵥ w) := by
          rw [h4]
      _ = lam * (w ⬝ᵥ w) - 2 * (w ⬝ᵥ w)
            - (∑ e ∈ C, ((1 + lam) * D.weight e - 1)) * (w ⬝ᵥ w) := by
          ring
  -- assemble: linear arithmetic over the shared sum atoms
  have hW : 0 < w ⬝ᵥ w := dotProduct_self_pos hwne
  linarith [h1, hchain, hR, hS1, hDW, hW]

end Gtz

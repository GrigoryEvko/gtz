/-
# The pair minors of the six-set pivot: the hinge as a determinant locus

`Gtz.HasParallelPair` — the conclusion of the `(6,3)` hinge — is shown to be
EXACTLY the vanishing of a `2×2` principal minor of the six-set pivot matrix
`P_{ab} = g_aᵀ W⁻¹ g_b`, `W = S_univ − 1 ≻ 0`.  The bridge is the compound
identity

  `det P[{a,b}] · det W = (g_a × g_b)ᵀ W (g_a × g_b)` ,

which turns the pair minor into a CROSS READING in the `W`-metric — the same
functional the cross ledger prices and the same marker that degenerates on
the parallel pair.  Since `W ≻ 0` at every design, the minor vanishes exactly
when the cross product does, i.e. exactly at a parallel pair (a zero atom is
parallel to everything, with ratio zero).

## What this buys the arm

The projection program reads a `(6,3)` tie as twenty spectral conditions on
the `3×3` blocks of `P`; the hinge's conclusion is now a determinant condition
on the `2×2` blocks of the SAME matrix.  The corank-one rigidity fight is
therefore internal to one PSD rank-three matrix: derive, from the twenty
block conditions and the co-weighted projection identity, that some `2×2`
principal minor vanishes.  The minor here is the minor of `P` itself.  It is
a different quantity from `Gtz.pairPivotMinor`, which is the pair minor of
`1 − P`.  At the split diamond [MEASURED,
`scratchpad/corank1/contact.jl`, 256 bits]: twelve blocks in contact, the
eight refused blocks all at `λmax = 5/4` exactly, and the single vanishing
pair minor is `{spine, copy}` — the parallel pair.
-/
import Gtz.Wave.SixSetNullColumn
import Gtz.Wave.KirchhoffSignTower
import Gtz.Wave.SixSetDowndate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-- **The `2×2` compound identity.**  For any `3×3` matrix and any two
vectors, the pair Gram determinant in the matrix metric is the cross
product's reading against the adjugate.  Lagrange's identity is the case
`M = 1`. -/
theorem det_pairGram_eq_cross_adjugate (M : Matrix (Fin 3) (Fin 3) ℝ)
    (x₁ x₂ : Fin 3 → ℝ) :
    (x₁ ⬝ᵥ (M *ᵥ x₁)) * (x₂ ⬝ᵥ (M *ᵥ x₂))
        - (x₁ ⬝ᵥ (M *ᵥ x₂)) * (x₂ ⬝ᵥ (M *ᵥ x₁))
      = crossProduct x₁ x₂ ⬝ᵥ (M.adjugate *ᵥ crossProduct x₁ x₂) := by
  simp only [Matrix.adjugate_fin_three, cross_apply, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **The pair pivot minor is a `W`-metric cross reading.**  Scaled by
`det W`, the `2×2` principal minor of the pivot matrix at `{a,b}` is the
reading of `g_a × g_b` against the six-set gap itself. -/
theorem pairPivotMinor_mul_det_eq_crossReading (D : WeightedDesign m 3)
    (hm : 2 ≤ m) (a b : Fin m) :
    ((D.atom a ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom a))
        * (D.atom b ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom b))
      - (D.atom a ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom b))
        * (D.atom b ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom a)))
        * (subsetSum D (Finset.univ : Finset (Fin m)) - 1).det
      = crossProduct (D.atom a) (D.atom b) ⬝ᵥ
          ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)
            *ᵥ crossProduct (D.atom a) (D.atom b)) := by
  set W : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (Finset.univ : Finset (Fin m)) - 1 with hW
  have hPD : W.PosDef := sixSetGap_posDef D hm
  have hdet : W.det ≠ 0 := ne_of_gt hPD.det_pos
  have hcompound := det_pairGram_eq_cross_adjugate W⁻¹ (D.atom a) (D.atom b)
  rw [adjugate_nonsing_inv_fin_three hdet] at hcompound
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hcompound
  have hscaled := congrArg (fun r => r * W.det) hcompound
  calc _ = ((W.det)⁻¹ * (crossProduct (D.atom a) (D.atom b) ⬝ᵥ
        (W *ᵥ crossProduct (D.atom a) (D.atom b)))) * W.det := hscaled
    _ = _ := by field_simp

/-- **The pair minor vanishes exactly at a parallel pair.**  `W ≻ 0` makes the
cross reading definite, so the minor is zero exactly when the cross product
is, and a vanishing cross product is proportionality (a zero atom is a ratio-
zero multiple).  The hinge's conclusion is a determinant locus of the pivot
matrix. -/
theorem pairPivotMinor_eq_zero_iff_parallel (D : WeightedDesign m 3)
    (hm : 2 ≤ m) {a b : Fin m} (_hab : a ≠ b) :
    ((D.atom a ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom a))
        * (D.atom b ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom b))
      - (D.atom a ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom b))
        * (D.atom b ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom a)) = 0)
      ↔ (∃ ratio : ℝ, D.atom b = ratio • D.atom a)
        ∨ (∃ ratio : ℝ, D.atom a = ratio • D.atom b) := by
  set W : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (Finset.univ : Finset (Fin m)) - 1 with hW
  have hPD : W.PosDef := sixSetGap_posDef D hm
  have hdet : W.det ≠ 0 := ne_of_gt hPD.det_pos
  have hbridge := pairPivotMinor_mul_det_eq_crossReading D hm a b
  constructor
  · intro hzero
    rw [← hW] at hbridge
    rw [hzero, zero_mul] at hbridge
    have hcross : crossProduct (D.atom a) (D.atom b) = 0 := by
      by_contra hne
      have := (Matrix.posDef_iff_dotProduct_mulVec.mp hPD).2 hne
      rw [star_trivial] at this
      rw [← hbridge] at this
      exact lt_irrefl 0 this
    by_cases ha : D.atom a = 0
    · exact Or.inr ⟨0, by rw [ha, zero_smul]⟩
    · exact Or.inl (eq_smul_of_crossProduct_eq_zero ha hcross)
  · intro hpar
    have hcross : crossProduct (D.atom a) (D.atom b) = 0 := by
      rcases hpar with ⟨r, hr⟩ | ⟨r, hr⟩
      · rw [hr, map_smul, cross_self, smul_zero]
      · rw [hr, map_smul, LinearMap.smul_apply, cross_self, smul_zero]
    rw [← hW, hcross, Matrix.mulVec_zero, dotProduct_zero] at hbridge
    have hfactor := hbridge
    exact (mul_eq_zero.mp hfactor).resolve_right hdet

/-- **THE HINGE AS A DETERMINANT LOCUS.**  A design has a parallel pair
exactly when some off-diagonal pair of the six-set pivot matrix has a
singular `2×2` principal minor. -/
theorem hasParallelPair_iff_exists_pairPivotMinor_eq_zero
    (D : WeightedDesign m 3) (hm : 2 ≤ m) :
    HasParallelPair D
      ↔ ∃ a b : Fin m, a ≠ b ∧
        (D.atom a ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom a))
          * (D.atom b ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom b))
        - (D.atom a ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom b))
          * (D.atom b ⬝ᵥ ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom a)) = 0 := by
  constructor
  · rintro ⟨kept, drop, ratio, hne, heq⟩
    exact ⟨kept, drop, hne,
      (pairPivotMinor_eq_zero_iff_parallel D hm hne).mpr (Or.inl ⟨ratio, heq⟩)⟩
  · rintro ⟨a, b, hab, hzero⟩
    rcases (pairPivotMinor_eq_zero_iff_parallel D hm hab).mp hzero with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨a, b, r, hab, hr⟩
    · exact ⟨b, a, r, hab.symm, hr⟩

/-! ## The pair-heavy free engine -/

/-- **A heavy pair refuses every triple avoiding it.**  If some combination of
two atoms reads the `W⁻¹` metric at least at its own coefficient norm, then no
card-3 subset avoiding both atoms dominates strictly: the witness
`ξ = W⁻¹(c₁g_a + c₂g_b)` makes the downdated form nonpositive through
Cauchy–Schwarz on the two carried readings.  This is the six-set mirror of the
null census's free half — with the PAIR spectra of the pivot matrix as the
stratifying data. -/
theorem not_posDef_compl_of_pair_reading (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (R : Finset (Fin m)) {a b : Fin m} (ha : a ∈ R) (hb : b ∈ R) (hab : a ≠ b)
    (c₁ c₂ : ℝ)
    (hyne : c₁ • D.atom a + c₂ • D.atom b ≠ 0)
    (hheavy : c₁ ^ 2 + c₂ ^ 2 ≤ (c₁ • D.atom a + c₂ • D.atom b) ⬝ᵥ
        ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹
          *ᵥ (c₁ • D.atom a + c₂ • D.atom b))) :
    ¬ (subsetSum D Rᶜ - 1).PosDef := by
  classical
  set W : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (Finset.univ : Finset (Fin m)) - 1 with hW
  have hPD : W.PosDef := sixSetGap_posDef D hm
  have hdet : IsUnit W.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  set y : Fin 3 → ℝ := c₁ • D.atom a + c₂ • D.atom b with hy
  set ξ : Fin 3 → ℝ := W⁻¹ *ᵥ y with hξ
  have hWξ : W *ᵥ ξ = y := by
    rw [hξ, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hξne : ξ ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hWξ
    exact hyne hWξ.symm
  have hcne : (0 : ℝ) < c₁ ^ 2 + c₂ ^ 2 := by
    by_contra hle
    push Not at hle
    have h₁ : c₁ ^ 2 = 0 :=
      le_antisymm (by linarith [sq_nonneg c₂]) (sq_nonneg c₁)
    have h₂ : c₂ ^ 2 = 0 :=
      le_antisymm (by linarith [sq_nonneg c₁]) (sq_nonneg c₂)
    refine hyne ?_
    rw [hy, pow_eq_zero_iff (two_ne_zero) |>.mp h₁,
      pow_eq_zero_iff (two_ne_zero) |>.mp h₂, zero_smul, zero_smul, add_zero]
  set ρ : ℝ := y ⬝ᵥ (W⁻¹ *ᵥ y) with hρ
  have hρξ : ξ ⬝ᵥ (W *ᵥ ξ) = ρ := by
    rw [hWξ, hρ, hξ]
    exact dotProduct_comm _ _
  have hρpos : 0 < ρ := by
    have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hPD).2 hξne
    rw [star_trivial, hρξ] at h
    exact h
  set ua : ℝ := D.atom a ⬝ᵥ ξ with hua
  set ub : ℝ := D.atom b ⬝ᵥ ξ with hub
  have hcombo : c₁ * ua + c₂ * ub = ρ := by
    rw [hua, hub, hρ, hξ, hy, add_dotProduct, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul]
  intro hpd
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hξne
  rw [star_trivial] at hform
  have hdowndate := tripleGap_eq_sixSet_downdate D R
  rw [hdowndate, ← hW] at hform
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum] at hform
  have hterms : ∀ r ∈ R, ξ ⬝ᵥ (atomMatrix (D.atom r) *ᵥ ξ) = (D.atom r ⬝ᵥ ξ) ^ 2 := by
    intro r _
    rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm, pow_two]
  rw [Finset.sum_congr rfl hterms] at hform
  have hsub : ua ^ 2 + ub ^ 2 ≤ ∑ r ∈ R, (D.atom r ⬝ᵥ ξ) ^ 2 := by
    have hpair : ({a, b} : Finset (Fin m)) ⊆ R := by
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr'
      · exact ha
      · rw [Finset.mem_singleton.mp hr']
        exact hb
    calc ua ^ 2 + ub ^ 2
        = ∑ r ∈ ({a, b} : Finset (Fin m)), (D.atom r ⬝ᵥ ξ) ^ 2 := by
          rw [Finset.sum_insert (by simp [hab]), Finset.sum_singleton, hua, hub]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hpair
          (fun r _ _ => sq_nonneg _)
  have hCS : ρ ^ 2 ≤ (c₁ ^ 2 + c₂ ^ 2) * (ua ^ 2 + ub ^ 2) := by
    have := sq_nonneg (c₁ * ub - c₂ * ua)
    nlinarith [hcombo]
  -- form = ρ − Σ readings² ≤ ρ − ρ²/(c²) ≤ 0
  have hreadfloor : ρ ^ 2 / (c₁ ^ 2 + c₂ ^ 2) ≤ ∑ r ∈ R, (D.atom r ⬝ᵥ ξ) ^ 2 := by
    have h1 : ρ ^ 2 / (c₁ ^ 2 + c₂ ^ 2) ≤ ua ^ 2 + ub ^ 2 := by
      rw [div_le_iff₀ hcne]
      nlinarith [hCS]
    linarith [hsub]
  have hfinal : ξ ⬝ᵥ (W *ᵥ ξ) - ∑ r ∈ R, (D.atom r ⬝ᵥ ξ) ^ 2 ≤ 0 := by
    rw [hρξ]
    have hρsq : ρ ≤ ρ ^ 2 / (c₁ ^ 2 + c₂ ^ 2) := by
      rw [le_div_iff₀ hcne]
      nlinarith [hheavy, hρpos, hρ]
    linarith [hreadfloor]
  linarith [hform, hfinal]

end Gtz

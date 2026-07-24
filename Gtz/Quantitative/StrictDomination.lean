/-
# Strict domination and the strict spectral connector

`Gtz.Quantitative.MarginContinuity` characterises WEAK domination through the smallest eigenvalue:
`1 ≤ λ_min(M) ↔ (M − I) ⪰ 0` (`one_le_lambdaMinMat_iff_posSemidef`), a one-sided `ciInf`
estimate. The STRICT analogue `1 < λ_min(M) ↔ (M − I) ≻ 0` needs one more ingredient the
non-strict version does not: the Rayleigh infimum must be ATTAINED, so that a strictly
positive quadratic form forces the infimum strictly above `1`. In finite dimensions the
unit sphere is compact, so `λ_min` is a minimum, and the strict connector follows.

`strictDominates_iff_one_lt_lambdaMinMat` specialises it to a design's subset moment
`S_C` (over `subsetSum` / `atomMatrix`), the strict twin of `dominates_iff_one_le_lambdaMinMat`;
`margin_pos_iff_exists_strictDominates` lifts it to the `sup'`-over-gates margin
`φ = Φ − 1`, positive exactly when some gate subset strictly dominates the identity.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.MarginContinuity
import Gtz.Core.Sanity

open scoped RealInnerProductSpace
open ContinuousLinearMap Matrix

namespace Gtz

/-! ### Attainment of the Rayleigh infimum (finite-dimensional min-max) -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

/-- The Rayleigh quotient of a continuous self-map attains a global minimum over the
nonzero vectors: in finite dimensions the sphere is compact, so the continuous
`reApplyInnerSelf` has a minimizer there, and scale-invariance of the Rayleigh quotient
promotes that sphere-minimizer to a global minimum. -/
theorem exists_isMinOn_rayleighQuotient (T : E →L[ℝ] E) :
    ∃ v : E, v ≠ 0 ∧ ∀ y : E, y ≠ 0 → T.rayleighQuotient v ≤ T.rayleighQuotient y := by
  obtain ⟨seed, hseed⟩ : ∃ z : E, z ≠ 0 := exists_ne 0
  have hr : (0 : ℝ) < ‖seed‖ := norm_pos_iff.mpr hseed
  have hcpt : IsCompact (Metric.sphere (0 : E) ‖seed‖) := isCompact_sphere 0 ‖seed‖
  have hseedmem : seed ∈ Metric.sphere (0 : E) ‖seed‖ := by
    rw [Metric.mem_sphere, dist_zero_right]
  have hne : (Metric.sphere (0 : E) ‖seed‖).Nonempty := ⟨seed, hseedmem⟩
  obtain ⟨minimizer, hmem, hmin⟩ :=
    hcpt.exists_isMinOn hne T.reApplyInnerSelf_continuous.continuousOn
  have hnorm : ‖minimizer‖ = ‖seed‖ := by
    rw [Metric.mem_sphere, dist_zero_right] at hmem; exact hmem
  have hvne : minimizer ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact hr.ne' hnorm.symm
  refine ⟨minimizer, hvne, fun y hy => ?_⟩
  have hynorm : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  set scale : ℝ := ‖seed‖ / ‖y‖ with hscale
  have hscalepos : 0 < scale := by rw [hscale]; positivity
  have hscalene : scale ≠ 0 := ne_of_gt hscalepos
  have hscaledmem : scale • y ∈ Metric.sphere (0 : E) ‖seed‖ := by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hscalepos, hscale]
    field_simp
  have hreLe : T.reApplyInnerSelf minimizer ≤ T.reApplyInnerSelf (scale • y) :=
    isMinOn_iff.mp hmin (scale • y) hscaledmem
  have hnormScaled : ‖scale • y‖ = ‖seed‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscalepos, hscale]; field_simp
  have eMin : T.rayleighQuotient minimizer = T.reApplyInnerSelf minimizer / ‖seed‖ ^ 2 := by
    show T.reApplyInnerSelf minimizer / ‖minimizer‖ ^ 2 = _; rw [hnorm]
  have eScaled : T.rayleighQuotient (scale • y)
      = T.reApplyInnerSelf (scale • y) / ‖seed‖ ^ 2 := by
    show T.reApplyInnerSelf (scale • y) / ‖scale • y‖ ^ 2 = _; rw [hnormScaled]
  have hstep : T.rayleighQuotient minimizer ≤ T.rayleighQuotient (scale • y) := by
    rw [eMin, eScaled]; gcongr
  rwa [T.rayleigh_smul y hscalene] at hstep

/-! ### The strict connector: `1 < λ_min(M) ↔ (M − I) ≻ 0` -/

variable {k : ℕ} [Nonempty (Fin k)]

/-- The Rayleigh infimum `lambdaMinMat M` is ATTAINED at a nonzero Euclidean vector — the
finite-dimensional infimum equals the Rayleigh quotient at a minimizer. This is precisely
what the *strict* connector needs beyond the non-strict `one_le_lambdaMinMat_iff_posSemidef`
(a pure `ciInf` estimate): it turns `∀ v ≠ 0, 0 < ⟨v, (M−I)v⟩` into a strict lower bound
`1 <` on the infimum. -/
theorem exists_lambdaMinMat_eq_rayleigh (M : Matrix (Fin k) (Fin k) ℝ) :
    ∃ v : EuclideanSpace ℝ (Fin k), v ≠ 0 ∧
      lambdaMinMat M = (Matrix.toEuclideanCLM (𝕜 := ℝ) M).rayleighQuotient v := by
  obtain ⟨v, hvne, hvmin⟩ :=
    exists_isMinOn_rayleighQuotient (Matrix.toEuclideanCLM (𝕜 := ℝ) M)
  refine ⟨v, hvne, ?_⟩
  rw [lambdaMinMat, lambdaMinCLM]
  exact le_antisymm (ciInf_le (rayleigh_bddBelow _) ⟨v, hvne⟩)
    (le_ciInf (fun z => hvmin (z : EuclideanSpace ℝ (Fin k)) z.property))

/-- **The strict connector** — the strict twin of `one_le_lambdaMinMat_iff_posSemidef`: for
symmetric `M`, the smallest eigenvalue exceeds `1` iff `M − I` is positive definite, so
`1 < λ_min(S_C)` is exactly *strict* domination `(S_C − I) ≻ 0`. Forward is a one-sided
`ciInf` estimate; backward consumes the attainment `exists_lambdaMinMat_eq_rayleigh`. -/
theorem one_lt_lambdaMinMat_iff_posDef (M : Matrix (Fin k) (Fin k) ℝ)
    (hherm : M.IsHermitian) :
    1 < lambdaMinMat M ↔ (M - 1).PosDef := by
  constructor
  · intro hlt
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨hherm.sub Matrix.isHermitian_one, fun x hx => ?_⟩
    rw [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
    have hxpos : 0 < x ⬝ᵥ x := dotProduct_self_pos hx
    have hxne : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k)) ≠ 0 := by
      rw [← norm_ne_zero_iff]
      intro hz
      have hpos2 : (0 : ℝ) < ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
        rw [euclid_norm_sq_eq_dotProduct]; exact hxpos
      rw [hz] at hpos2; norm_num at hpos2
    have hle : lambdaMinMat M
        ≤ (Matrix.toEuclideanCLM (𝕜 := ℝ) M).rayleighQuotient (WithLp.toLp 2 x) := by
      rw [lambdaMinMat, lambdaMinCLM]
      exact ciInf_le (rayleigh_bddBelow _) ⟨WithLp.toLp 2 x, hxne⟩
    rw [rayleigh_toEuclideanCLM_eq, euclid_norm_sq_eq_dotProduct] at hle
    have hltRay : 1 < (x ⬝ᵥ M *ᵥ x) / (x ⬝ᵥ x) := lt_of_lt_of_le hlt hle
    rw [lt_div_iff₀ hxpos, one_mul] at hltRay
    linarith [hltRay]
  · intro hpd
    obtain ⟨v, hvne, hEq⟩ := exists_lambdaMinMat_eq_rayleigh M
    rw [rayleigh_toEuclideanCLM_eq, euclid_norm_sq_eq_dotProduct] at hEq
    have hvpos : 0 < (v : Fin k → ℝ) ⬝ᵥ (v : Fin k → ℝ) := by
      have := pow_pos (norm_pos_iff.mpr hvne) 2
      rwa [euclid_norm_sq_eq_dotProduct] at this
    have hvcne : (v : Fin k → ℝ) ≠ 0 := by
      intro h; rw [h] at hvpos; simp only [zero_dotProduct] at hvpos
      exact lt_irrefl 0 hvpos
    have hstrict := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hvcne
    rw [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at hstrict
    rw [hEq, lt_div_iff₀ hvpos, one_mul]
    linarith [hstrict]

/-! ### Kernel corollaries: strict domination ⇔ `1 < λ_min` -/

variable {m : ℕ}

/-- **Strict domination of a design's subset** `(S_C − I) ≻ 0` is exactly
`1 < λ_min(S_C)` — the strict analogue of `dominates_iff_one_le_lambdaMinMat`, over the
real GTZ objects `subsetSum` / `atomMatrix`. -/
theorem strictDominates_iff_one_lt_lambdaMinMat (D : WeightedDesign m k)
    (C : Finset (Fin m)) :
    (subsetSum D C - 1).PosDef ↔ 1 < lambdaMinMat (subsetSum D C) :=
  (one_lt_lambdaMinMat_iff_posDef (subsetSum D C)
    (Matrix.posSemidef_sum C (fun c _ => posSemidef_atomMatrix (D.atom c))).1).symm

/-- **The margin is positive iff some gate strictly dominates.** The domination margin
`φ = Φ − 1` at a configuration is `> 0` exactly when some subset in the gate family
strictly dominates the identity, `(S_C − I) ≻ 0` — the positive companion of
`dominates_iff_one_le_lambdaMinMat` at the `sup'`-over-gates margin level, over
`subsetSumRaw` via `isHermitian_subsetSumRaw`. -/
theorem margin_pos_iff_exists_strictDominates
    (config : (Fin m → Fin k → ℝ) × (Fin m → ℝ))
    (gates : Finset (Finset (Fin m))) (hNe : gates.Nonempty) :
    0 < (gates.sup' hNe (fun C => lambdaMinMat (subsetSumRaw config C))) - 1 ↔
      ∃ C ∈ gates, (subsetSumRaw config C - 1).PosDef := by
  rw [sub_pos, Finset.lt_sup'_iff]
  refine exists_congr (fun C => and_congr_right (fun _ => ?_))
  exact (one_lt_lambdaMinMat_iff_posDef (subsetSumRaw config C)
    (isHermitian_subsetSumRaw config C))

end Gtz

/-
# Continuity of the domination margin

The smallest eigenvalue of a self-adjoint operator, taken as the Rayleigh infimum
`λ_min T = ⨅_{x≠0} ⟨x, Tx⟩/‖x‖²`, is `1`-Lipschitz in the operator norm (Weyl 1912).
Mathlib ships the Rayleigh-quotient atoms but not a packaged eigenvalue-continuity
lemma, so the bound is spelled out here, then lifted through the matrix→operator
bridge and a finite `sup'` over the gate family to the continuity of the domination
margin `φ = Φ − 1`, `Φ = max_C λ_min(S_C)`.

`λ_min` is DEFINED as the infimum, so its `1`-Lipschitz bound is a two-sided `ciInf`
estimate from `rayleighQuotient_add` + `rayleighQuotient_le_norm`; that it is the
smallest eigenvalue is a corollary, never used for the continuity. The anchors
`one_le_lambdaMinMat_iff_posSemidef` and `dominates_iff_one_le_lambdaMinMat` identify
`1 ≤ λ_min(S_C)` with `Gtz.Dominates`, so the continuous `φ` really is the domination
margin; `offTubeGap_of_margin_pos` feeds the continuity into `Gtz.offTubeGap_pos`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.CollaredCompact
import Gtz.Quantitative.CollarRate
import Gtz.Core.Sanity
open scoped RealInnerProductSpace
open ContinuousLinearMap Matrix

namespace Gtz

/-! ### `λ_min` as a Rayleigh infimum is `1`-Lipschitz -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]

instance instNonemptyNeZero : Nonempty {x : E // x ≠ 0} :=
  ⟨⟨Classical.choose (exists_ne (0 : E)), Classical.choose_spec (exists_ne (0 : E))⟩⟩

/-- The smallest Rayleigh value of a self-map `T`, the infimum of `⟨x, Tx⟩/‖x‖²`
over nonzero vectors. For self-adjoint `T` this is the smallest eigenvalue; the
continuity proof below needs no self-adjointness. -/
noncomputable def lambdaMinCLM (T : E →L[ℝ] E) : ℝ :=
  ⨅ x : {x : E // x ≠ 0}, T.rayleighQuotient (x : E)

omit [Nontrivial E] in
/-- The Rayleigh values are bounded below by `−‖T‖`, so the infimum is genuine. -/
theorem rayleigh_bddBelow (T : E →L[ℝ] E) :
    BddBelow (Set.range fun x : {x : E // x ≠ 0} => T.rayleighQuotient (x : E)) := by
  refine ⟨-‖T‖, ?_⟩
  rintro r ⟨x, rfl⟩
  linarith [(abs_le.mp (T.rayleighQuotient_le_norm (x : E))).1]

/-- The one-sided Weyl estimate: `λ_min` drops by at most `‖T − S‖` under
perturbation. Two `ciInf` steps: `λ_min T ≤ T.rq x ≤ S.rq x + ‖T − S‖`. -/
theorem lambdaMinCLM_sub_le (S T : E →L[ℝ] E) :
    lambdaMinCLM T - ‖T - S‖ ≤ lambdaMinCLM S := by
  simp only [lambdaMinCLM]
  refine le_ciInf (fun x => ?_)
  have hTle : ⨅ y : {x : E // x ≠ 0}, T.rayleighQuotient (y : E) ≤ T.rayleighQuotient (x : E) :=
    ciInf_le (rayleigh_bddBelow T) x
  have hstep : T.rayleighQuotient (x : E) ≤ S.rayleighQuotient (x : E) + ‖T - S‖ := by
    have hdecomp : T = S + (T - S) := by abel
    have hb : (T - S).rayleighQuotient (x : E) ≤ ‖T - S‖ :=
      le_trans (le_abs_self _) ((T - S).rayleighQuotient_le_norm (x : E))
    calc T.rayleighQuotient (x : E)
        = (S + (T - S)).rayleighQuotient (x : E) := by rw [← hdecomp]
      _ = S.rayleighQuotient (x : E) + (T - S).rayleighQuotient (x : E) := by
            rw [rayleighQuotient_add]
      _ ≤ S.rayleighQuotient (x : E) + ‖T - S‖ := by linarith
  linarith

/-- The two-sided Weyl bound `|λ_min S − λ_min T| ≤ ‖S − T‖`. -/
theorem abs_lambdaMinCLM_sub_le (S T : E →L[ℝ] E) :
    |lambdaMinCLM S - lambdaMinCLM T| ≤ ‖S - T‖ := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h := lambdaMinCLM_sub_le S T
    rw [norm_sub_rev T S] at h
    linarith
  · have h := lambdaMinCLM_sub_le T S
    linarith

/-- `λ_min` is `1`-Lipschitz in the operator norm (Weyl 1912). -/
theorem lipschitzWith_lambdaMinCLM : LipschitzWith 1 (lambdaMinCLM (E := E)) := by
  refine LipschitzWith.of_dist_le_mul (fun S T => ?_)
  rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
  exact abs_lambdaMinCLM_sub_le S T

/-- `λ_min` is continuous. -/
theorem continuous_lambdaMinCLM : Continuous (lambdaMinCLM (E := E)) :=
  lipschitzWith_lambdaMinCLM.continuous

/-! ### The matrix → operator bridge is continuous -/

/-- `Matrix.toEuclideanCLM` packaged as an ℝ-linear map, to invoke finite-dimensional
continuity. -/
noncomputable def toEuclideanLM (k : ℕ) :
    Matrix (Fin k) (Fin k) ℝ →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) where
  toFun := fun M => Matrix.toEuclideanCLM (𝕜 := ℝ) M
  map_add' := fun M N => by simp [map_add]
  map_smul' := fun c M => by simp [map_smul]

theorem continuous_toEuclideanCLM (k : ℕ) :
    Continuous fun M : Matrix (Fin k) (Fin k) ℝ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) M :=
  (toEuclideanLM k).continuous_of_finiteDimensional

/-! ### `λ_min` of a matrix, continuous in the matrix -/

variable {k : ℕ} [Nonempty (Fin k)]

instance instNontrivialEuclid : Nontrivial (EuclideanSpace ℝ (Fin k)) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty (Fin k))
  refine ⟨EuclideanSpace.single i (1 : ℝ), 0, fun h => ?_⟩
  have h1 : (EuclideanSpace.single i (1 : ℝ)) i = (0 : EuclideanSpace ℝ (Fin k)) i := by rw [h]
  simp at h1

/-- The smallest eigenvalue of `M`, as the Rayleigh infimum of its Euclidean
operator. -/
noncomputable def lambdaMinMat (M : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  lambdaMinCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) M)

/-- `λ_min(M)` is continuous in `M`. -/
theorem continuous_lambdaMinMat : Continuous (lambdaMinMat (k := k)) :=
  continuous_lambdaMinCLM.comp (continuous_toEuclideanCLM k)

/-! ### `λ_min` is the smallest eigenvalue, tied to `Dominates` -/

omit [Nonempty (Fin k)] in
/-- The Rayleigh quotient in dotProduct form: `⟨y, My⟩/‖y‖²`. -/
theorem rayleigh_toEuclideanCLM_eq (M : Matrix (Fin k) (Fin k) ℝ)
    (y : EuclideanSpace ℝ (Fin k)) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) M).rayleighQuotient y = (y ⬝ᵥ M *ᵥ y) / ‖y‖ ^ 2 := by
  show (Matrix.toEuclideanCLM (𝕜 := ℝ) M).reApplyInnerSelf y / ‖y‖ ^ 2
      = (y ⬝ᵥ M *ᵥ y) / ‖y‖ ^ 2
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  simp only [RCLike.re_to_real]
  rw [real_inner_comm, inner_toEuclideanCLM]

omit [Nonempty (Fin k)] in
/-- For a Euclidean vector, `‖y‖² = ⟨y, y⟩` in dotProduct form. -/
theorem euclid_norm_sq_eq_dotProduct (y : EuclideanSpace ℝ (Fin k)) :
    ‖y‖ ^ 2 = y ⬝ᵥ y := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

/-- `1 ≤ lambdaMinMat M` iff the quadratic form dominates the norm form everywhere. -/
theorem one_le_lambdaMinMat_iff_forall (M : Matrix (Fin k) (Fin k) ℝ) :
    1 ≤ lambdaMinMat M ↔ ∀ y : EuclideanSpace ℝ (Fin k), y ⬝ᵥ y ≤ y ⬝ᵥ M *ᵥ y := by
  rw [lambdaMinMat, lambdaMinCLM, le_ciInf_iff (rayleigh_bddBelow _)]
  constructor
  · intro h y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hr := h ⟨y, hy⟩
      rw [rayleigh_toEuclideanCLM_eq] at hr
      have hpos : 0 < ‖y‖ ^ 2 := by positivity
      rw [le_div_iff₀ hpos, one_mul, euclid_norm_sq_eq_dotProduct] at hr
      exact hr
  · rintro h ⟨y, hy⟩
    rw [rayleigh_toEuclideanCLM_eq]
    have hpos : 0 < ‖y‖ ^ 2 := by positivity
    rw [le_div_iff₀ hpos, one_mul, euclid_norm_sq_eq_dotProduct]
    exact h y

/-- `1 ≤ lambdaMinMat M ↔ (M − I) ⪰ 0` for symmetric `M`: `λ_min` is the smallest
eigenvalue, and `≥ 1` is weak domination. -/
theorem one_le_lambdaMinMat_iff_posSemidef (M : Matrix (Fin k) (Fin k) ℝ)
    (hherm : M.IsHermitian) :
    1 ≤ lambdaMinMat M ↔ (M - 1).PosSemidef := by
  rw [one_le_lambdaMinMat_iff_forall, Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨hherm.sub Matrix.isHermitian_one, fun x => ?_⟩
    have hy := h (WithLp.toLp 2 x)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, star_trivial]
    linarith [hy]
  · rintro ⟨_, h⟩ y
    have hx := h (y : Fin k → ℝ)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, star_trivial] at hx
    linarith [hx]

/-! ### The subset moment and the tie to `Dominates` -/

variable {m : ℕ}

/-- The unweighted subset moment `S_C = Σ_{c∈C} g_c g_cᵀ` on a raw `(atoms, weights)`
configuration (weight-free, as `Gtz.subsetSum`). -/
def subsetSumRaw (config : (Fin m → Fin k → ℝ) × (Fin m → ℝ)) (C : Finset (Fin m)) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ c ∈ C, atomMatrix (config.1 c)

omit [Nonempty (Fin k)] in
/-- Each subset moment is symmetric (a sum of PSD rank-one atoms). -/
theorem isHermitian_subsetSumRaw (config : (Fin m → Fin k → ℝ) × (Fin m → ℝ))
    (C : Finset (Fin m)) : (subsetSumRaw config C).IsHermitian :=
  (Matrix.posSemidef_sum C (fun c _ => posSemidef_atomMatrix (config.1 c))).1

/-- `1 ≤ λ_min(S_C)` is exactly `Gtz.Dominates`. So `Φ = max_C λ_min(S_C) ≥ 1`
(margin `≥ 0`) at a config iff some `k`-subset dominates. -/
theorem dominates_iff_one_le_lambdaMinMat (D : WeightedDesign m k) (C : Finset (Fin m)) :
    Dominates D C ↔ 1 ≤ lambdaMinMat (subsetSum D C) :=
  (one_le_lambdaMinMat_iff_posSemidef (subsetSum D C)
    (isHermitian_subsetSumRaw (D.atom, D.weight) C)).symm

omit [Nonempty (Fin k)] in
theorem continuous_subsetSumRaw (C : Finset (Fin m)) :
    Continuous fun config : (Fin m → Fin k → ℝ) × (Fin m → ℝ) => subsetSumRaw config C := by
  refine continuous_matrix (fun i j => ?_)
  have hentry : ∀ (c : Fin m) (a b : Fin k),
      Continuous fun config : (Fin m → Fin k → ℝ) × (Fin m → ℝ) =>
        config.1 c a * config.1 c b := fun c a b => by fun_prop
  simp only [subsetSumRaw, Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply]
  exact continuous_finsetSum _ (fun c _ => hentry c i j)

/-! ### `Φ` and the margin are continuous -/

/-- The domination margin `φ = Φ − 1`, `Φ = max_{C ∈ gates} λ_min(S_C)`, is
continuous in the configuration, over any nonempty gate family. -/
theorem continuous_dominationMargin (gates : Finset (Finset (Fin m)))
    (hNe : gates.Nonempty) :
    Continuous fun config : (Fin m → Fin k → ℝ) × (Fin m → ℝ) =>
      (gates.sup' hNe (fun C => lambdaMinMat (subsetSumRaw config C))) - 1 := by
  refine Continuous.sub ?_ continuous_const
  exact Continuous.finset_sup'_apply hNe
    (fun C _ => continuous_lambdaMinMat.comp (continuous_subsetSumRaw C))

/-- The margin is `ContinuousOn` any set — in particular the compact off-tube slice of
`Gtz.collaredSet` — supplying `Gtz.offTubeGap_pos`'s continuity hypothesis. -/
theorem continuousOn_dominationMargin (gates : Finset (Finset (Fin m)))
    (hNe : gates.Nonempty) (offTube : Set ((Fin m → Fin k → ℝ) × (Fin m → ℝ))) :
    ContinuousOn (fun config : (Fin m → Fin k → ℝ) × (Fin m → ℝ) =>
      (gates.sup' hNe (fun C => lambdaMinMat (subsetSumRaw config C))) - 1) offTube :=
  (continuous_dominationMargin gates hNe).continuousOn

/-- The continuous margin plugs into `Gtz.offTubeGap_pos`, producing the positive
off-tube gap. Only compactness (`Gtz.isCompact_collaredSet`) and pointwise off-tube
positivity remain as hypotheses. -/
theorem offTubeGap_of_margin_pos (gates : Finset (Finset (Fin m))) (hNe : gates.Nonempty)
    (offTube : Set ((Fin m → Fin k → ℝ) × (Fin m → ℝ)))
    (hCompact : IsCompact offTube) (hNeSet : offTube.Nonempty)
    (hPos : ∀ config ∈ offTube,
      0 < (gates.sup' hNe (fun C => lambdaMinMat (subsetSumRaw config C))) - 1) :
    ∃ offGap > 0, ∀ config ∈ offTube,
      offGap ≤ (gates.sup' hNe (fun C => lambdaMinMat (subsetSumRaw config C))) - 1 :=
  offTubeGap_pos hCompact hNeSet (continuousOn_dominationMargin gates hNe offTube) hPos

end Gtz

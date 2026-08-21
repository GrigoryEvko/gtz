/-
# The corank-one stratum is rigid: `(k+1, k)` ties are classified outright

At size `rank + 1` the tie stratum is not a locus to be searched.  It is an
explicit variety, and every one of its numbers is a function of the weights:

  **`Gtz.isTie_iff_leverage_law`.**  A design `D : WeightedDesign (k+1) k` with
  `2 ≤ k` is an exact tie **if and only if**

      `k * (t_c * l_c) = (k - 1) + t_c`   at EVERY atom `c`.

  Equivalently `l_c = (k - 1 + t_c) / (k * t_c)`: the leverages are a function of
  the weights alone.  The weights themselves are FREE — measured spreads reach
  `0.97` at exact ties, so nothing here forces uniformity.

Three consequences, each hypothesis-free at every rank `k ≥ 2`.

* **`Gtz.dominates_of_card_eq_of_isTie`** — at such a tie EVERY `k`-subset
  dominates, and every gap is singular.  The tie is maximally degenerate.
* **`Gtz.not_hasParallelPair_of_isTie_succ_rank`** — such a tie is
  PARALLEL-FREE.  So `Gtz.not_hingeHoldsAtSize_succ_rank'` refutes the hinge at
  `(k+1, k)` for every `k ≥ 2`, and it refutes it at the WHOLE stratum rather
  than at one witness.  The tree carried the refutation only from the explicit
  `Gtz.flatSimplexDesign`, and only for `3 ≤ rank`.
* The band's lower guard is necessary: `Skeleton.obligationSubThresholdBandHinge`
  ranges over sizes `2 * rank` and up, and `rank + 1 < 2 * rank` for `k ≥ 2`, so
  a band statement reaching one cell lower would be false at every rank at once.

## The mechanism

Write `t_c` for the weight, `l_c` for the leverage, and

    `u_c := 1 - t_c * l_c`      (`Gtz.designCoShare`, the co-share)
    `R_c := u_c / (1 - t_c)`    (`Gtz.coRatio`)
    `Sigma := sum_c t_c * R_c`  (`Gtz.coMean`, the weight-average of the ratios).

Everything turns on ONE matrix.  Let `V` be the `m x k` matrix with rows
`sqrt(t_c) * g_c` (`Gtz.designIsometry`).  Parseval says exactly `Vᵀ V = 1`, so
`V Vᵀ` is an orthogonal projection of `R^m` of trace `k` and

    `Gtz.coProjection D := 1 - V Vᵀ`

is a symmetric idempotent whose diagonal is `u_c` and whose trace is `m - k`.

At `m = k + 1` that trace is ONE, and a symmetric idempotent of trace one is an
outer square (`Gtz.exists_vecMulVec_of_symm_idem_trace_one`, proved by a trace
argument, with no eigenvalue and no rank).  So `coProjection D = z zᵀ` with
`z_c ^ 2 = u_c`, and `dep_c := sqrt(t_c) * z_c` is the linear dependency of the
`k+1` atoms, normalised by `dep_c ^ 2 = t_c * u_c` (`Gtz.exists_dependency`).

With the dependency in hand the criterion collapses to a scalar.  A `k`-subset of
`Fin (k+1)` is `univ.erase d`, its gap reads

    `v ⬝ (S - 1) v = sum_c (1 - t_c) * (g_c ⬝ v) ^ 2 - (g_d ⬝ v) ^ 2` ,

and Cauchy-Schwarz against `a_c := (if c = d then 1 else 0) - nu * dep_c`, at the
choice `nu := dep_d / ((1 - t_d) * Sigma)`, gives

  **`Gtz.dominates_erase_of_coMean_le`: `Sigma <= R_d` forces domination**, and
  **`Gtz.posDef_erase_of_coMean_lt`: `Sigma < R_d` forces STRICT domination.**

The rigidity is then one line of averaging.  `Sigma` is the `t`-weighted mean of
the `R_c`.  No strictly dominating `k`-subset forces `R_d <= Sigma` at every `d`,
and a family that never exceeds its own weighted mean is constant.  So `R_d`
equals `Sigma` everywhere, `sum_c u_c = 1` pins `Sigma = 1 / k`, and
`u_d = (1 - t_d) / k` is the leverage law.

Note what the rigidity does NOT need: only the ABSENCE of a strict dominator
(`Gtz.NoStrictSelection`), never the existence of a weak one.  The weak half comes
out as a conclusion, which is why the classification is an iff.

## Parallel-freeness

A rank-one outer square has vanishing two-by-two minors, so
`Gtz.weight_mul_sq_dotProduct_eq_coShare_mul` reads

    `t_c * t_d * (g_c ⬝ g_d) ^ 2 = u_c * u_d`

at EVERY `(k+1, k)` design — the campaign's pairing cap, saturated.  Feed the
leverage law into it and a parallel pair would need
`(1 - t_c) * (1 - t_d) = (k - 1 + t_c) * (k - 1 + t_d)`, whose left side is below
one and whose right side is above `(k-1) ^ 2 >= 1`.

[MEASURED before proving, at exact ties located by direct minimisation of the TRUE
`max` over `k`-subsets of `lambda_min`, never a smoothed surrogate: at `(3,2)`,
`(4,3)`, `(5,4)` and `(6,5)` the leverage law holds to `8.3e-14`, every `k`-subset
gap has `|lambda_min| <= 6.8e-14` and is PSD, `|R_d - Sigma| <= 5.4e-14`, and the
largest squared cosine between atoms is `0.96`, `0.23`, `0.10`, `0.06` — bounded
away from one, as parallel-freeness requires.  The pairing-cap saturation and the
general-size trace law `sum_d (1 - t_d) * f_d = k` were checked at random designs
to `6.5e-13` and `3.7e-13`.]
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.SchurRankOne
import Gtz.Design.LeverageBound
import Gtz.Design.OneLineComplementCap
import Gtz.Reduction.Deflation
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer
import Gtz.Wave.WeightedMomentDomination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. A symmetric idempotent of trace one is an outer square

The only spectral input of the file, and it is not spectral: a symmetric
idempotent equals its own Gram, so its trace is the total square mass of its
entries.  Trace zero therefore kills the matrix outright. -/

/-- The trace of a Gram is the total square mass of the entries. -/
theorem trace_transpose_mul_self {size : ℕ} (form : Matrix (Fin size) (Fin size) ℝ) :
    (formᵀ * form).trace = ∑ rowIndex, ∑ colIndex, form rowIndex colIndex ^ 2 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun rowIndex _ =>
    Finset.sum_congr rfl fun colIndex _ => (pow_two _).symm

/-- **A SYMMETRIC IDEMPOTENT OF TRACE ZERO VANISHES.** -/
theorem matrix_eq_zero_of_symm_idem_trace_zero {size : ℕ} {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : formᵀ = form) (hidem : form * form = form) (htrace : form.trace = 0) :
    form = 0 := by
  have hgram : (formᵀ * form).trace = 0 := by rw [hsymm, hidem, htrace]
  rw [trace_transpose_mul_self] at hgram
  have hnonneg : ∀ rowIndex ∈ (Finset.univ : Finset (Fin size)),
      (0 : ℝ) ≤ ∑ colIndex, form rowIndex colIndex ^ 2 :=
    fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  ext rowIndex colIndex
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hgram rowIndex (Finset.mem_univ _)
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg
    (fun colOther (_ : colOther ∈ (Finset.univ : Finset (Fin size))) =>
      sq_nonneg (form rowIndex colOther))).mp hrow colIndex (Finset.mem_univ _)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hentry

/-- **A SYMMETRIC IDEMPOTENT OF TRACE ONE IS AN OUTER SQUARE.**  The unit vector is
a normalised column, and the residue is again a symmetric idempotent, now of trace
zero.  No eigenvalue, no rank, no spectral theorem. -/
theorem exists_vecMulVec_of_symm_idem_trace_one {size : ℕ}
    {form : Matrix (Fin size) (Fin size) ℝ} (hsymm : formᵀ = form)
    (hidem : form * form = form) (htrace : form.trace = 1) :
    ∃ axis : Fin size → ℝ, axis ⬝ᵥ axis = 1 ∧ form = Matrix.vecMulVec axis axis := by
  classical
  have hswap : ∀ rowIndex colIndex : Fin size, form colIndex rowIndex = form rowIndex colIndex := by
    intro rowIndex colIndex
    have hstep := congrFun (congrFun hsymm colIndex) rowIndex
    rw [Matrix.transpose_apply] at hstep
    exact hstep.symm
  have hdiag : ∀ index : Fin size, form index index = ∑ other, form index other ^ 2 := by
    intro index
    have hentry := congrFun (congrFun hidem index) index
    rw [Matrix.mul_apply] at hentry
    rw [← hentry]
    exact Finset.sum_congr rfl fun other _ => by rw [hswap index other, pow_two]
  have hdiagNonneg : ∀ index : Fin size, 0 ≤ form index index := by
    intro index
    rw [hdiag index]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨pivot, hpivotPos⟩ : ∃ pivot : Fin size, 0 < form pivot pivot := by
    by_contra hcontra
    push_neg at hcontra
    have hzero : ∑ index, form index index = 0 :=
      le_antisymm (Finset.sum_nonpos fun index _ => hcontra index)
        (Finset.sum_nonneg fun index _ => hdiagNonneg index)
    rw [show (∑ index, form index index) = form.trace from rfl, htrace] at hzero
    norm_num at hzero
  have hscalePos : 0 < Real.sqrt (form pivot pivot) := Real.sqrt_pos.mpr hpivotPos
  have hscaleSq : Real.sqrt (form pivot pivot) * Real.sqrt (form pivot pivot)
      = form pivot pivot := Real.mul_self_sqrt hpivotPos.le
  refine ⟨fun index => form index pivot / Real.sqrt (form pivot pivot), ?_, ?_⟩
  case _ =>
    have hcolumn : ∑ index, form index pivot ^ 2 = form pivot pivot := by
      rw [hdiag pivot]
      exact Finset.sum_congr rfl fun index _ => by rw [hswap index pivot]
    rw [dotProduct]
    have hterm : ∀ index : Fin size,
        form index pivot / Real.sqrt (form pivot pivot)
          * (form index pivot / Real.sqrt (form pivot pivot))
        = form index pivot ^ 2
          / (Real.sqrt (form pivot pivot) * Real.sqrt (form pivot pivot)) := by
      intro index
      rw [pow_two]
      field_simp
    rw [Finset.sum_congr rfl fun index _ => hterm index, ← Finset.sum_div, hcolumn, hscaleSq,
      div_self hpivotPos.ne']
  case _ =>
    set axis : Fin size → ℝ := fun index => form index pivot / Real.sqrt (form pivot pivot)
      with haxis
    have haxisApply : ∀ index, axis index
        = form index pivot / Real.sqrt (form pivot pivot) := fun _ => rfl
    have hunit : axis ⬝ᵥ axis = 1 := by
      have hcolumn : ∑ index, form index pivot ^ 2 = form pivot pivot := by
        rw [hdiag pivot]
        exact Finset.sum_congr rfl fun index _ => by rw [hswap index pivot]
      rw [dotProduct]
      have hterm : ∀ index : Fin size, axis index * axis index
          = form index pivot ^ 2
            / (Real.sqrt (form pivot pivot) * Real.sqrt (form pivot pivot)) := by
        intro index
        rw [haxisApply, pow_two]
        field_simp
      rw [Finset.sum_congr rfl fun index _ => hterm index, ← Finset.sum_div, hcolumn, hscaleSq,
        div_self hpivotPos.ne']
    have hfixRow : ∀ index : Fin size, ∑ other, form index other * axis other = axis index := by
      intro index
      have hentry := congrFun (congrFun hidem index) pivot
      rw [Matrix.mul_apply] at hentry
      have hpull : ∑ other, form index other * axis other
          = (∑ other, form index other * form other pivot)
            / Real.sqrt (form pivot pivot) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun other _ => by rw [haxisApply]; ring
      rw [hpull, hentry, haxisApply]
    have houter : (Matrix.vecMulVec axis axis)ᵀ = Matrix.vecMulVec axis axis :=
      Matrix.transpose_vecMulVec axis axis
    have hleft : form * Matrix.vecMulVec axis axis = Matrix.vecMulVec axis axis := by
      ext rowIndex colIndex
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
      rw [show (∑ other, form rowIndex other * (axis other * axis colIndex))
          = (∑ other, form rowIndex other * axis other) * axis colIndex from by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun other _ => by ring, hfixRow rowIndex]
    have hright : Matrix.vecMulVec axis axis * form = Matrix.vecMulVec axis axis := by
      have hstep := congrArg Matrix.transpose hleft
      rwa [Matrix.transpose_mul, hsymm, houter] at hstep
    have hsquare : Matrix.vecMulVec axis axis * Matrix.vecMulVec axis axis
        = Matrix.vecMulVec axis axis := by
      ext rowIndex colIndex
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
      rw [show (∑ other, axis rowIndex * axis other * (axis other * axis colIndex))
          = (axis rowIndex * axis colIndex) * ∑ other, axis other * axis other from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun other _ => by ring]
      rw [show (∑ other, axis other * axis other) = axis ⬝ᵥ axis from rfl, hunit, mul_one]
    have hzero : form - Matrix.vecMulVec axis axis = 0 := by
      refine matrix_eq_zero_of_symm_idem_trace_zero ?_ ?_ ?_
      · rw [Matrix.transpose_sub, hsymm, houter]
      · simp only [Matrix.sub_mul, Matrix.mul_sub, hidem, hleft, hright, hsquare]
        abel
      · rw [Matrix.trace_sub, htrace, Matrix.trace_vecMulVec,
          show axis ⬝ᵥ axis = 1 from hunit, sub_self]
    exact (sub_eq_zero.mp hzero)

/-! ## 2. The design isometry, and the projection Parseval builds -/

/-- The `m x k` matrix whose rows are the atoms scaled by the square roots of the
weights.  Parseval says exactly that its columns are orthonormal. -/
noncomputable def designIsometry (D : WeightedDesign m k) : Matrix (Fin m) (Fin k) ℝ :=
  Matrix.of fun atomIndex coordIndex => Real.sqrt (D.weight atomIndex) * D.atom atomIndex coordIndex

theorem designIsometry_apply (D : WeightedDesign m k) (atomIndex : Fin m) (coordIndex : Fin k) :
    designIsometry D atomIndex coordIndex
      = Real.sqrt (D.weight atomIndex) * D.atom atomIndex coordIndex := rfl

theorem sqrtWeight_mul_self (D : WeightedDesign m k) (atomIndex : Fin m) :
    Real.sqrt (D.weight atomIndex) * Real.sqrt (D.weight atomIndex) = D.weight atomIndex :=
  Real.mul_self_sqrt (D.weight_pos atomIndex).le

/-- **PARSEVAL IS ORTHONORMALITY.** -/
theorem designIsometry_transpose_mul (D : WeightedDesign m k) :
    (designIsometry D)ᵀ * designIsometry D = 1 := by
  ext rowCoord colCoord
  have hparseval := congrFun (congrFun D.isParseval rowCoord) colCoord
  rw [Matrix.sum_apply] at hparseval
  rw [Matrix.mul_apply, ← hparseval]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  have hroot := sqrtWeight_mul_self D atomIndex
  simp only [Matrix.transpose_apply, designIsometry_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul]
  linear_combination (D.atom atomIndex rowCoord * D.atom atomIndex colCoord) * hroot

/-- The co-share of an atom: the deficit of its Parseval share. -/
noncomputable def designCoShare (D : WeightedDesign m k) (atomIndex : Fin m) : ℝ :=
  1 - D.weight atomIndex * leverageOf (D.atom atomIndex)

theorem designCoShare_apply (D : WeightedDesign m k) (atomIndex : Fin m) :
    designCoShare D atomIndex = 1 - D.weight atomIndex * leverageOf (D.atom atomIndex) := rfl

/-- The complementary projection of a design: a symmetric idempotent of `R^m`
whose diagonal is the co-share and whose trace is `m - k`. -/
noncomputable def coProjection (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  1 - designIsometry D * (designIsometry D)ᵀ

theorem coProjection_transpose (D : WeightedDesign m k) :
    (coProjection D)ᵀ = coProjection D := by
  rw [coProjection, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_transpose]

theorem coProjection_mul_self (D : WeightedDesign m k) :
    coProjection D * coProjection D = coProjection D := by
  have hkey : designIsometry D * (designIsometry D)ᵀ
      * (designIsometry D * (designIsometry D)ᵀ)
      = designIsometry D * (designIsometry D)ᵀ := by
    calc designIsometry D * (designIsometry D)ᵀ * (designIsometry D * (designIsometry D)ᵀ)
        = designIsometry D * ((designIsometry D)ᵀ * designIsometry D) * (designIsometry D)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = designIsometry D * (designIsometry D)ᵀ := by
          rw [designIsometry_transpose_mul, Matrix.mul_one]
  simp only [coProjection, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hkey]
  abel

/-- **THE DIAGONAL OF THE COMPLEMENTARY PROJECTION IS THE CO-SHARE.** -/
theorem coProjection_diag (D : WeightedDesign m k) (atomIndex : Fin m) :
    coProjection D atomIndex atomIndex = designCoShare D atomIndex := by
  have hrow : (designIsometry D * (designIsometry D)ᵀ) atomIndex atomIndex
      = D.weight atomIndex * leverageOf (D.atom atomIndex) := by
    rw [Matrix.mul_apply, leverageOf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun coordIndex _ => ?_
    have hroot := sqrtWeight_mul_self D atomIndex
    simp only [Matrix.transpose_apply, designIsometry_apply]
    linear_combination (D.atom atomIndex coordIndex ^ 2) * hroot
  rw [coProjection, Matrix.sub_apply, Matrix.one_apply_eq, hrow, designCoShare_apply]

/-- **THE OFF-DIAGONAL OF THE COMPLEMENTARY PROJECTION IS THE WEIGHTED PAIRING.** -/
theorem coProjection_offDiag (D : WeightedDesign m k) {leftIndex rightIndex : Fin m}
    (hdistinct : leftIndex ≠ rightIndex) :
    coProjection D leftIndex rightIndex
      = -(Real.sqrt (D.weight leftIndex) * Real.sqrt (D.weight rightIndex)
        * (D.atom leftIndex ⬝ᵥ D.atom rightIndex)) := by
  have hgram : (designIsometry D * (designIsometry D)ᵀ) leftIndex rightIndex
      = Real.sqrt (D.weight leftIndex) * Real.sqrt (D.weight rightIndex)
        * (D.atom leftIndex ⬝ᵥ D.atom rightIndex) := by
    rw [Matrix.mul_apply, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun coordIndex _ => by
      simp only [Matrix.transpose_apply, designIsometry_apply]; ring
  rw [coProjection, Matrix.sub_apply, Matrix.one_apply_ne hdistinct, hgram, zero_sub]

/-- **THE TRACE OF THE COMPLEMENTARY PROJECTION IS THE CORANK.** -/
theorem trace_coProjection (D : WeightedDesign m k) :
    (coProjection D).trace = (m : ℝ) - (k : ℝ) := by
  have hswap : (designIsometry D * (designIsometry D)ᵀ).trace
      = ((designIsometry D)ᵀ * designIsometry D).trace :=
    Matrix.trace_mul_comm _ _
  rw [coProjection, Matrix.trace_sub, hswap, designIsometry_transpose_mul, Matrix.trace_one,
    Matrix.trace_one]
  simp

/-- The complementary projection kills the isometry. -/
theorem coProjection_mul_designIsometry (D : WeightedDesign m k) :
    coProjection D * designIsometry D = 0 := by
  rw [coProjection, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    designIsometry_transpose_mul, Matrix.mul_one, sub_self]

/-- **THE CO-SHARES TOTAL THE CORANK.**  Parseval's trace, read on the diagonal. -/
theorem sum_designCoShare (D : WeightedDesign m k) :
    ∑ atomIndex, designCoShare D atomIndex = (m : ℝ) - (k : ℝ) := by
  rw [← trace_coProjection D, Matrix.trace]
  exact (Finset.sum_congr rfl fun atomIndex _ => coProjection_diag D atomIndex).symm

/-! ## 3. The dependency of a corank-one design -/

/-- The complementary projection of a corank-one design has trace one. -/
theorem trace_coProjection_succ (D : WeightedDesign (k + 1) k) :
    (coProjection D).trace = 1 := by
  rw [trace_coProjection D]
  push_cast
  ring

/-- **THE OUTER AXIS OF A CORANK-ONE DESIGN.** -/
theorem exists_coAxis (D : WeightedDesign (k + 1) k) :
    ∃ axis : Fin (k + 1) → ℝ, axis ⬝ᵥ axis = 1
      ∧ coProjection D = Matrix.vecMulVec axis axis
      ∧ ∀ atomIndex, axis atomIndex ^ 2 = designCoShare D atomIndex := by
  obtain ⟨axis, hunit, hform⟩ := exists_vecMulVec_of_symm_idem_trace_one
    (coProjection_transpose D) (coProjection_mul_self D) (trace_coProjection_succ D)
  refine ⟨axis, hunit, hform, fun atomIndex => ?_⟩
  have hdiag := coProjection_diag D atomIndex
  rw [hform, Matrix.vecMulVec_apply] at hdiag
  rw [pow_two]
  exact hdiag

/-- **THE NORMALISED DEPENDENCY.**  At `(k+1, k)` the atoms carry a linear
dependency whose squared coefficients are the weighted co-shares, and which
resolves the whole weighted Gram: `t_r * (delta_rc - t_c * p_rc) = dep_r * dep_c`. -/
theorem exists_dependency (D : WeightedDesign (k + 1) k) :
    ∃ dep : Fin (k + 1) → ℝ,
      (∀ coordIndex : Fin k, ∑ atomIndex, dep atomIndex * D.atom atomIndex coordIndex = 0)
        ∧ (∀ atomIndex, dep atomIndex ^ 2 = D.weight atomIndex * designCoShare D atomIndex)
        ∧ (∀ rowIndex colIndex : Fin (k + 1),
            D.weight rowIndex * ((if rowIndex = colIndex then (1 : ℝ) else 0)
                - D.weight colIndex * (D.atom rowIndex ⬝ᵥ D.atom colIndex))
              = dep rowIndex * dep colIndex) := by
  classical
  obtain ⟨axis, hunit, hform, haxisSq⟩ := exists_coAxis D
  have hkill : ∀ coordIndex : Fin k,
      ∑ atomIndex, axis atomIndex * designIsometry D atomIndex coordIndex = 0 := by
    intro coordIndex
    obtain ⟨pivot, hpivot⟩ : ∃ pivot : Fin (k + 1), axis pivot ≠ 0 := by
      by_contra hcontra
      push_neg at hcontra
      have hzero : axis ⬝ᵥ axis = 0 :=
        Finset.sum_eq_zero fun atomIndex _ => by rw [hcontra atomIndex, mul_zero]
      rw [hunit] at hzero
      norm_num at hzero
    have hentry := congrFun (congrFun (coProjection_mul_designIsometry D) pivot) coordIndex
    rw [Matrix.mul_apply, hform, Matrix.zero_apply] at hentry
    have hfactor : axis pivot * ∑ atomIndex, axis atomIndex
        * designIsometry D atomIndex coordIndex = 0 := by
      rw [Finset.mul_sum, ← hentry]
      exact Finset.sum_congr rfl fun atomIndex _ => by
        rw [Matrix.vecMulVec_apply]; ring
    rcases mul_eq_zero.mp hfactor with hbad | hgood
    · exact absurd hbad hpivot
    · exact hgood
  refine ⟨fun atomIndex => Real.sqrt (D.weight atomIndex) * axis atomIndex, fun coordIndex => ?_,
    fun atomIndex => ?_, fun rowIndex colIndex => ?_⟩
  · rw [← hkill coordIndex]
    exact Finset.sum_congr rfl fun atomIndex _ => by
      rw [designIsometry_apply]; ring
  · rw [mul_pow, Real.sq_sqrt (D.weight_pos atomIndex).le, haxisSq]
  · have hrootRow := sqrtWeight_mul_self D rowIndex
    have hrootCol := sqrtWeight_mul_self D colIndex
    by_cases hcase : rowIndex = colIndex
    · subst hcase
      have hdiag := haxisSq rowIndex
      rw [designCoShare_apply, leverageOf_eq_dotProduct] at hdiag
      have hone : (if rowIndex = rowIndex then (1 : ℝ) else 0) = 1 := by simp
      rw [hone]
      calc D.weight rowIndex
            * (1 - D.weight rowIndex * (D.atom rowIndex ⬝ᵥ D.atom rowIndex))
          = D.weight rowIndex * axis rowIndex ^ 2 := by rw [hdiag]
        _ = (Real.sqrt (D.weight rowIndex) * Real.sqrt (D.weight rowIndex))
              * axis rowIndex ^ 2 := by rw [hrootRow]
        _ = _ := by ring
    · have hoff := coProjection_offDiag D hcase
      rw [hform, Matrix.vecMulVec_apply] at hoff
      have hzero : (if rowIndex = colIndex then (1 : ℝ) else 0) = 0 := by simp [hcase]
      rw [hzero]
      calc D.weight rowIndex
            * (0 - D.weight colIndex * (D.atom rowIndex ⬝ᵥ D.atom colIndex))
          = (Real.sqrt (D.weight rowIndex) * Real.sqrt (D.weight colIndex))
              * (-(Real.sqrt (D.weight rowIndex) * Real.sqrt (D.weight colIndex)
                * (D.atom rowIndex ⬝ᵥ D.atom colIndex))) := by
            linear_combination (Real.sqrt (D.weight colIndex) * Real.sqrt (D.weight colIndex)
                * (D.atom rowIndex ⬝ᵥ D.atom colIndex)) * hrootRow
              + (D.weight rowIndex * (D.atom rowIndex ⬝ᵥ D.atom colIndex)) * hrootCol
        _ = (Real.sqrt (D.weight rowIndex) * Real.sqrt (D.weight colIndex))
              * (axis rowIndex * axis colIndex) := by rw [hoff]
        _ = _ := by ring

/-- **THE PAIRING CAP IS SATURATED AT CORANK ONE.**  A rank-one outer square has
vanishing two-by-two minors, and this is that statement in design currency, at
EVERY `(k+1, k)` design and with no tie hypothesis. -/
theorem weight_mul_sq_dotProduct_eq_coShare_mul (D : WeightedDesign (k + 1) k)
    {leftIndex rightIndex : Fin (k + 1)} (hdistinct : leftIndex ≠ rightIndex) :
    D.weight leftIndex * D.weight rightIndex * (D.atom leftIndex ⬝ᵥ D.atom rightIndex) ^ 2
      = designCoShare D leftIndex * designCoShare D rightIndex := by
  obtain ⟨axis, hunit, hform, haxisSq⟩ := exists_coAxis D
  have houter : coProjection D leftIndex rightIndex = axis leftIndex * axis rightIndex := by
    rw [hform, Matrix.vecMulVec_apply]
  have hoff := coProjection_offDiag D hdistinct
  have hflip : Real.sqrt (D.weight leftIndex) * Real.sqrt (D.weight rightIndex)
      * (D.atom leftIndex ⬝ᵥ D.atom rightIndex) = -(axis leftIndex * axis rightIndex) := by
    rw [← houter, hoff]
    ring
  have hsq : (Real.sqrt (D.weight leftIndex) * Real.sqrt (D.weight rightIndex)
      * (D.atom leftIndex ⬝ᵥ D.atom rightIndex)) ^ 2
      = axis leftIndex ^ 2 * axis rightIndex ^ 2 := by
    rw [hflip]; ring
  rw [haxisSq, haxisSq] at hsq
  rw [← hsq, mul_pow, mul_pow, Real.sq_sqrt (D.weight_pos leftIndex).le,
    Real.sq_sqrt (D.weight_pos rightIndex).le]

/-! ## 4. The scalar criterion -/

/-- The co-ratio of an atom: its co-share against its own outside weight. -/
noncomputable def coRatio (D : WeightedDesign m k) (atomIndex : Fin m) : ℝ :=
  designCoShare D atomIndex / (1 - D.weight atomIndex)

/-- The weight-average of the co-ratios. -/
noncomputable def coMean (D : WeightedDesign m k) : ℝ :=
  ∑ atomIndex, D.weight atomIndex * coRatio D atomIndex

theorem one_sub_weight_pos_of_size (D : WeightedDesign m k) (hsize : 2 ≤ m) (atomIndex : Fin m) :
    0 < 1 - D.weight atomIndex := by
  linarith [weight_lt_one D hsize atomIndex]

theorem designCoShare_eq_mul (D : WeightedDesign m k) (hsize : 2 ≤ m) (atomIndex : Fin m) :
    designCoShare D atomIndex = (1 - D.weight atomIndex) * coRatio D atomIndex := by
  rw [coRatio, mul_div_cancel₀ _ (one_sub_weight_pos_of_size D hsize atomIndex).ne']

theorem gap_isHermitian (D : WeightedDesign m k) (C : Finset (Fin m)) :
    (subsetSum D C - 1).IsHermitian :=
  isHermitian_of_transpose_eq (by
    rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum_transpose])

/-- Parseval as a quadratic form: the weighted square readings total the norm. -/
theorem sum_weight_mul_sq_reading_eq_normSq (D : WeightedDesign m k) (probe : Fin k → ℝ) :
    ∑ atomIndex, D.weight atomIndex * (D.atom atomIndex ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
  have hmoment := dotProduct_weightedMoment_mulVec D Finset.univ probe
  rw [weightedMoment_univ, Matrix.one_mulVec] at hmoment
  exact hmoment.symm

/-- **THE GAP OF A CO-SINGLETON, AS A SCALAR SUM.**  Erasing one label from the
universe leaves a gap whose quadratic form is the co-weighted energy of the whole
design less the square of the erased reading. -/
theorem dotProduct_erase_gap_mulVec (D : WeightedDesign m k) (eraseIndex : Fin m)
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((subsetSum D (Finset.univ.erase eraseIndex) - 1) *ᵥ probe)
      = (∑ atomIndex, (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2)
        - (D.atom eraseIndex ⬝ᵥ probe) ^ 2 := by
  classical
  have hgap := dotProduct_subsetSum_finset_mulVec D (Finset.univ.erase eraseIndex) probe
  have hparseval := sum_weight_mul_sq_reading_eq_normSq D probe
  have hsplit : ∑ atomIndex ∈ Finset.univ.erase eraseIndex, (D.atom atomIndex ⬝ᵥ probe) ^ 2
      = (∑ atomIndex, (D.atom atomIndex ⬝ᵥ probe) ^ 2)
        - (D.atom eraseIndex ⬝ᵥ probe) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ eraseIndex)]
    ring
  have hmerge : ∑ atomIndex, (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2
      = (∑ atomIndex, (D.atom atomIndex ⬝ᵥ probe) ^ 2)
        - ∑ atomIndex, D.weight atomIndex * (D.atom atomIndex ⬝ᵥ probe) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hgap, hsplit, hmerge, hparseval]
  ring

/-! ### Cauchy-Schwarz under one linear constraint

The whole criterion is this one scalar inequality.  It is stated abstractly
because nothing in it is about designs. -/

/-- **THE CONSTRAINED CAUCHY-SCHWARZ CAP.**  Under a single linear constraint
`sum a_c r_c = 0`, one coordinate of `r` is capped by the `w`-energy of `r` at the
rate the constraint dictates.  Cleared of denominators. -/
theorem sq_le_of_constrained_cauchySchwarz {size : ℕ} {outsideWeight coefficient reading :
    Fin size → ℝ} (hpos : ∀ index, 0 < outsideWeight index)
    (horth : ∑ index, coefficient index * reading index = 0) (pivot : Fin size)
    (hmass : 0 < ∑ index, coefficient index ^ 2 / outsideWeight index) :
    reading pivot ^ 2
        * (outsideWeight pivot ^ 2 * ∑ index, coefficient index ^ 2 / outsideWeight index)
      ≤ (outsideWeight pivot * (∑ index, coefficient index ^ 2 / outsideWeight index)
          - coefficient pivot ^ 2)
        * ∑ index, outsideWeight index * reading index ^ 2 := by
  classical
  set mass : ℝ := ∑ index, coefficient index ^ 2 / outsideWeight index with hmassDef
  set shift : ℝ := coefficient pivot / (outsideWeight pivot * mass) with hshift
  set functional : Fin size → ℝ :=
    fun index => (if index = pivot then (1 : ℝ) else 0) - shift * coefficient index
    with hfunctional
  have hpivotNe : outsideWeight pivot ≠ 0 := (hpos pivot).ne'
  have hmassNe : mass ≠ 0 := hmass.ne'
  have hread : ∑ index, functional index * reading index = reading pivot := by
    have hterm : ∀ index : Fin size, functional index * reading index
        = (if index = pivot then reading index else 0)
          - shift * (coefficient index * reading index) := by
      intro index
      simp only [hfunctional]
      by_cases hcase : index = pivot
      · simp [hcase]; ring
      · simp [hcase]; ring
    rw [Finset.sum_congr rfl fun index _ => hterm index, Finset.sum_sub_distrib,
      ← Finset.mul_sum, horth, mul_zero, sub_zero, Finset.sum_ite_eq' Finset.univ pivot]
    simp
  have hnormValue : ∑ index, functional index ^ 2 / outsideWeight index
      = 1 / outsideWeight pivot
        - coefficient pivot ^ 2 / (outsideWeight pivot ^ 2 * mass) := by
    have hterm : ∀ index : Fin size, functional index ^ 2 / outsideWeight index
        = (if index = pivot then
            (1 - 2 * shift * coefficient pivot) / outsideWeight pivot else 0)
          + shift ^ 2 * (coefficient index ^ 2 / outsideWeight index) := by
      intro index
      have hne := (hpos index).ne'
      simp only [hfunctional]
      by_cases hcase : index = pivot
      · subst hcase
        simp only [if_true]
        field_simp
        ring
      · simp only [hcase, if_false]
        field_simp
        ring
    rw [Finset.sum_congr rfl fun index _ => hterm index, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ pivot, ← Finset.mul_sum, ← hmassDef]
    simp only [Finset.mem_univ, if_true]
    rw [hshift]
    field_simp
    ring
  have hcauchy : reading pivot ^ 2
      ≤ (∑ index, functional index ^ 2 / outsideWeight index)
        * ∑ index, outsideWeight index * reading index ^ 2 := by
    have hsplit : ∀ index : Fin size, functional index * reading index
        = (functional index / Real.sqrt (outsideWeight index))
          * (Real.sqrt (outsideWeight index) * reading index) := by
      intro index
      have hroot : Real.sqrt (outsideWeight index) ≠ 0 :=
        (Real.sqrt_pos.mpr (hpos index)).ne'
      field_simp
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun index => functional index / Real.sqrt (outsideWeight index))
      (fun index => Real.sqrt (outsideWeight index) * reading index)
    rw [← hread, Finset.sum_congr rfl fun index _ => hsplit index]
    refine le_trans hsq (le_of_eq ?_)
    congr 1
    · exact Finset.sum_congr rfl fun index _ => by
        rw [div_pow, Real.sq_sqrt (hpos index).le]
    · exact Finset.sum_congr rfl fun index _ => by
        rw [mul_pow, Real.sq_sqrt (hpos index).le]
  rw [hnormValue] at hcauchy
  have hscalePos : 0 < outsideWeight pivot ^ 2 * mass := by positivity
  have hclear : (1 / outsideWeight pivot
        - coefficient pivot ^ 2 / (outsideWeight pivot ^ 2 * mass))
      * (outsideWeight pivot ^ 2 * mass)
      = outsideWeight pivot * mass - coefficient pivot ^ 2 := by
    field_simp
  calc reading pivot ^ 2 * (outsideWeight pivot ^ 2 * mass)
      ≤ ((1 / outsideWeight pivot
            - coefficient pivot ^ 2 / (outsideWeight pivot ^ 2 * mass))
          * ∑ index, outsideWeight index * reading index ^ 2)
        * (outsideWeight pivot ^ 2 * mass) := mul_le_mul_of_nonneg_right hcauchy hscalePos.le
    _ = (outsideWeight pivot * mass - coefficient pivot ^ 2)
        * ∑ index, outsideWeight index * reading index ^ 2 := by rw [← hclear]; ring

/-! ### The criterion at a corank-one design -/

/-- The dependency is orthogonal to every reading vector. -/
theorem sum_dep_mul_reading_eq_zero (D : WeightedDesign (k + 1) k) {dep : Fin (k + 1) → ℝ}
    (hdep : ∀ coordIndex : Fin k, ∑ atomIndex, dep atomIndex * D.atom atomIndex coordIndex = 0)
    (probe : Fin k → ℝ) :
    ∑ atomIndex, dep atomIndex * (D.atom atomIndex ⬝ᵥ probe) = 0 := by
  have hexpand : ∀ atomIndex : Fin (k + 1), dep atomIndex * (D.atom atomIndex ⬝ᵥ probe)
      = ∑ coordIndex, dep atomIndex * D.atom atomIndex coordIndex * probe coordIndex := by
    intro atomIndex
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun coordIndex _ => by ring
  rw [Finset.sum_congr rfl fun atomIndex _ => hexpand atomIndex, Finset.sum_comm]
  refine Finset.sum_eq_zero fun coordIndex _ => ?_
  rw [← Finset.sum_mul, hdep coordIndex, zero_mul]

/-- The mass the constrained Cauchy-Schwarz sees is the co-mean. -/
theorem dep_mass_eq_coMean (D : WeightedDesign (k + 1) k) (hsize : 2 ≤ k + 1)
    {dep : Fin (k + 1) → ℝ}
    (hnorm : ∀ atomIndex, dep atomIndex ^ 2 = D.weight atomIndex * designCoShare D atomIndex) :
    ∑ atomIndex, dep atomIndex ^ 2 / (1 - D.weight atomIndex) = coMean D := by
  rw [coMean]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [hnorm atomIndex, coRatio, mul_div_assoc]

/-- The co-shares are squares, hence nonnegative. -/
theorem designCoShare_nonneg (D : WeightedDesign (k + 1) k) (atomIndex : Fin (k + 1)) :
    0 ≤ designCoShare D atomIndex := by
  obtain ⟨axis, -, -, haxisSq⟩ := exists_coAxis D
  rw [← haxisSq atomIndex]
  exact sq_nonneg _

/-- The co-mean of a corank-one design is positive: the co-shares are nonnegative
and they total one. -/
theorem coMean_pos (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k) : 0 < coMean D := by
  classical
  have hsize : 2 ≤ k + 1 := by omega
  have hslack : ∀ atomIndex : Fin (k + 1), 0 < 1 - D.weight atomIndex :=
    one_sub_weight_pos_of_size D hsize
  have htotal : ∑ atomIndex, designCoShare D atomIndex = 1 := by
    rw [sum_designCoShare D]; push_cast; ring
  obtain ⟨witness, hwitness⟩ : ∃ witness : Fin (k + 1), 0 < designCoShare D witness := by
    by_contra hcontra
    push_neg at hcontra
    have hzero : ∑ atomIndex, designCoShare D atomIndex ≤ 0 :=
      Finset.sum_nonpos fun atomIndex _ => hcontra atomIndex
    rw [htotal] at hzero
    norm_num at hzero
  refine Finset.sum_pos' (fun atomIndex _ =>
    mul_nonneg (D.weight_pos atomIndex).le (div_nonneg (designCoShare_nonneg D atomIndex)
      (hslack atomIndex).le)) ⟨witness, Finset.mem_univ _, ?_⟩
  exact mul_pos (D.weight_pos witness) (div_pos hwitness (hslack witness))

/-- **THE READING CAP AT A CORANK-ONE DESIGN.**  The squared reading of one atom
against the co-weighted energy of the whole design, at the rate the co-mean sets. -/
theorem sq_reading_mul_le (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k)
    (eraseIndex : Fin (k + 1)) (probe : Fin k → ℝ) :
    (D.atom eraseIndex ⬝ᵥ probe) ^ 2 * ((1 - D.weight eraseIndex) ^ 2 * coMean D)
      ≤ ((1 - D.weight eraseIndex) * coMean D
          - D.weight eraseIndex * designCoShare D eraseIndex)
        * ∑ atomIndex, (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2 := by
  have hsize : 2 ≤ k + 1 := by omega
  obtain ⟨dep, hdep, hnorm, -⟩ := exists_dependency D
  have hmass := dep_mass_eq_coMean D hsize hnorm
  have hcap := sq_le_of_constrained_cauchySchwarz
    (outsideWeight := fun atomIndex => 1 - D.weight atomIndex) (coefficient := dep)
    (reading := fun atomIndex => D.atom atomIndex ⬝ᵥ probe)
    (one_sub_weight_pos_of_size D hsize) (sum_dep_mul_reading_eq_zero D hdep probe) eraseIndex
    (by rw [hmass]; exact coMean_pos D hrank)
  rw [hmass, hnorm eraseIndex] at hcap
  exact hcap

/-- **THE WEAK CRITERION.**  A `k`-subset of a corank-one design dominates as soon
as the erased atom's co-ratio clears the co-mean. -/
theorem dominates_erase_of_coMean_le (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k)
    (eraseIndex : Fin (k + 1)) (hclears : coMean D ≤ coRatio D eraseIndex) :
    Dominates D (Finset.univ.erase eraseIndex) := by
  have hsize : 2 ≤ k + 1 := by omega
  have hslack := one_sub_weight_pos_of_size D hsize eraseIndex
  have hmeanPos := coMean_pos D hrank
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨gap_isHermitian D _, fun probe => ?_⟩
  rw [star_trivial, dotProduct_erase_gap_mulVec D eraseIndex]
  have henergyNonneg : (0 : ℝ)
      ≤ ∑ atomIndex, (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2 :=
    Finset.sum_nonneg fun atomIndex _ =>
      mul_nonneg (one_sub_weight_pos_of_size D hsize atomIndex).le (sq_nonneg _)
  have hcap := sq_reading_mul_le D hrank eraseIndex probe
  have hshareEq := designCoShare_eq_mul D hsize eraseIndex
  have hrate : (1 - D.weight eraseIndex) * coMean D
        - D.weight eraseIndex * designCoShare D eraseIndex
      ≤ (1 - D.weight eraseIndex) ^ 2 * coMean D := by
    rw [hshareEq]
    have hprod : (0 : ℝ) ≤ (1 - D.weight eraseIndex)
        * (D.weight eraseIndex * (coRatio D eraseIndex - coMean D)) :=
      mul_nonneg hslack.le (mul_nonneg (D.weight_pos eraseIndex).le (by linarith))
    have hid : (1 - D.weight eraseIndex) ^ 2 * coMean D
        - ((1 - D.weight eraseIndex) * coMean D
          - D.weight eraseIndex * ((1 - D.weight eraseIndex) * coRatio D eraseIndex))
        = (1 - D.weight eraseIndex)
          * (D.weight eraseIndex * (coRatio D eraseIndex - coMean D)) := by ring
    linarith [hprod, hid]
  have hscalePos : 0 < (1 - D.weight eraseIndex) ^ 2 * coMean D := by positivity
  have hfinal : (D.atom eraseIndex ⬝ᵥ probe) ^ 2 * ((1 - D.weight eraseIndex) ^ 2 * coMean D)
      ≤ (∑ atomIndex, (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2)
        * ((1 - D.weight eraseIndex) ^ 2 * coMean D) := by
    refine le_trans hcap ?_
    calc ((1 - D.weight eraseIndex) * coMean D - D.weight eraseIndex * designCoShare D eraseIndex)
          * ∑ atomIndex, (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2
        ≤ ((1 - D.weight eraseIndex) ^ 2 * coMean D)
          * ∑ atomIndex, (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2 :=
          mul_le_mul_of_nonneg_right hrate henergyNonneg
      _ = _ := by ring
  linarith [le_of_mul_le_mul_right hfinal hscalePos]

/-- **THE STRICT CRITERION.**  Strict clearance forces STRICT domination. -/
theorem posDef_erase_of_coMean_lt (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k)
    (eraseIndex : Fin (k + 1)) (hclears : coMean D < coRatio D eraseIndex) :
    (subsetSum D (Finset.univ.erase eraseIndex) - 1).PosDef := by
  classical
  have hsize : 2 ≤ k + 1 := by omega
  have hslack := one_sub_weight_pos_of_size D hsize eraseIndex
  have hmeanPos := coMean_pos D hrank
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨gap_isHermitian D _, fun probe hprobe => ?_⟩
  rw [star_trivial, dotProduct_erase_gap_mulVec D eraseIndex]
  have henergyPos : (0 : ℝ)
      < ∑ atomIndex, (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2 := by
    have hparseval := sum_weight_mul_sq_reading_eq_normSq D probe
    have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos_of_ne_zero hprobe
    rw [← hparseval] at hprobePos
    obtain ⟨witness, hwitness⟩ : ∃ witness : Fin (k + 1),
        0 < D.weight witness * (D.atom witness ⬝ᵥ probe) ^ 2 := by
      by_contra hcontra
      push_neg at hcontra
      exact absurd (Finset.sum_nonpos fun atomIndex _ => hcontra atomIndex)
        (not_le.mpr hprobePos)
    have hterm : 0 < (1 - D.weight witness) * (D.atom witness ⬝ᵥ probe) ^ 2 := by
      have hsq : 0 < (D.atom witness ⬝ᵥ probe) ^ 2 := by
        nlinarith [hwitness, D.weight_pos witness, sq_nonneg (D.atom witness ⬝ᵥ probe)]
      exact mul_pos (one_sub_weight_pos_of_size D hsize witness) hsq
    exact Finset.sum_pos' (fun atomIndex _ =>
      mul_nonneg (one_sub_weight_pos_of_size D hsize atomIndex).le (sq_nonneg _))
      ⟨witness, Finset.mem_univ _, hterm⟩
  have hcap := sq_reading_mul_le D hrank eraseIndex probe
  have hshareEq := designCoShare_eq_mul D hsize eraseIndex
  have hrate : (1 - D.weight eraseIndex) * coMean D
        - D.weight eraseIndex * designCoShare D eraseIndex
      < (1 - D.weight eraseIndex) ^ 2 * coMean D := by
    rw [hshareEq]
    have hprod : (0 : ℝ) < (1 - D.weight eraseIndex)
        * (D.weight eraseIndex * (coRatio D eraseIndex - coMean D)) :=
      mul_pos hslack (mul_pos (D.weight_pos eraseIndex) (by linarith))
    have hid : (1 - D.weight eraseIndex) ^ 2 * coMean D
        - ((1 - D.weight eraseIndex) * coMean D
          - D.weight eraseIndex * ((1 - D.weight eraseIndex) * coRatio D eraseIndex))
        = (1 - D.weight eraseIndex)
          * (D.weight eraseIndex * (coRatio D eraseIndex - coMean D)) := by ring
    linarith [hprod, hid]
  have hscalePos : 0 < (1 - D.weight eraseIndex) ^ 2 * coMean D := by positivity
  have hfinal : (D.atom eraseIndex ⬝ᵥ probe) ^ 2 * ((1 - D.weight eraseIndex) ^ 2 * coMean D)
      < (∑ atomIndex, (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2)
        * ((1 - D.weight eraseIndex) ^ 2 * coMean D) := by
    refine lt_of_le_of_lt hcap ?_
    calc ((1 - D.weight eraseIndex) * coMean D - D.weight eraseIndex * designCoShare D eraseIndex)
          * ∑ atomIndex, (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2
        < ((1 - D.weight eraseIndex) ^ 2 * coMean D)
          * ∑ atomIndex, (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2 :=
          mul_lt_mul_of_pos_right hrate henergyPos
      _ = _ := by ring
  linarith [lt_of_mul_lt_mul_right hfinal hscalePos.le]

/-! ## 5. The rigidity -/

/-- No `k`-subset dominates strictly.  Strictly weaker than `Gtz.IsTie`, because it
does not ask for a weak dominator to exist. -/
def NoStrictSelection (D : WeightedDesign m k) : Prop :=
  ∀ C : Finset (Fin m), C.card = k → ¬ (subsetSum D C - 1).PosDef

theorem noStrictSelection_of_isTie (D : WeightedDesign m k) (htie : IsTie D) :
    NoStrictSelection D := htie.2

theorem card_univ_erase (eraseIndex : Fin (k + 1)) :
    (Finset.univ.erase eraseIndex).card = k := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- **THE CO-RATIOS NEVER EXCEED THEIR OWN WEIGHTED MEAN.**  The strict criterion,
contraposed. -/
theorem coRatio_le_coMean_of_noStrict (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k)
    (hno : NoStrictSelection D) (atomIndex : Fin (k + 1)) :
    coRatio D atomIndex ≤ coMean D := by
  by_contra hcontra
  push_neg at hcontra
  exact hno (Finset.univ.erase atomIndex) (card_univ_erase atomIndex)
    (posDef_erase_of_coMean_lt D hrank atomIndex hcontra)

/-- **THE CO-RATIOS ARE CONSTANT.**  A family that never exceeds its own weighted
mean is constant, and the mean is the constant. -/
theorem coRatio_eq_coMean_of_noStrict (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k)
    (hno : NoStrictSelection D) (atomIndex : Fin (k + 1)) :
    coRatio D atomIndex = coMean D := by
  classical
  refine le_antisymm (coRatio_le_coMean_of_noStrict D hrank hno atomIndex) ?_
  by_contra hcontra
  push_neg at hcontra
  have hstrict : ∑ other, D.weight other * coRatio D other
      < ∑ other, D.weight other * coMean D := by
    refine Finset.sum_lt_sum (fun other _ =>
      mul_le_mul_of_nonneg_left (coRatio_le_coMean_of_noStrict D hrank hno other)
        (D.weight_pos other).le) ⟨atomIndex, Finset.mem_univ _, ?_⟩
    exact mul_lt_mul_of_pos_left hcontra (D.weight_pos atomIndex)
  rw [← Finset.sum_mul, D.weight_sum_one, one_mul, ← coMean] at hstrict
  exact absurd hstrict (lt_irrefl _)

/-- **THE CO-MEAN IS THE RECIPROCAL OF THE RANK.** -/
theorem coMean_mul_rank (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k)
    (hno : NoStrictSelection D) : coMean D * (k : ℝ) = 1 := by
  have hsize : 2 ≤ k + 1 := by omega
  have htotal : ∑ atomIndex, designCoShare D atomIndex = 1 := by
    rw [sum_designCoShare D]; push_cast; ring
  have houtside : ∑ atomIndex : Fin (k + 1), (1 - D.weight atomIndex) = (k : ℝ) := by
    rw [Finset.sum_sub_distrib, D.weight_sum_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have hexpand : ∑ atomIndex, designCoShare D atomIndex
      = coMean D * ∑ atomIndex : Fin (k + 1), (1 - D.weight atomIndex) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [designCoShare_eq_mul D hsize atomIndex, coRatio_eq_coMean_of_noStrict D hrank hno atomIndex]
    ring
  rw [hexpand, houtside] at htotal
  exact htotal

/-- **THE LEVERAGE LAW.**  At a corank-one design with no strictly dominating
`k`-subset the leverage of every atom is a function of its own weight:

    `k * (t_c * l_c) = (k - 1) + t_c` .

No tie hypothesis, no uniformity, no genericity. -/
theorem rank_mul_share_eq_of_noStrict (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k)
    (hno : NoStrictSelection D) (atomIndex : Fin (k + 1)) :
    (k : ℝ) * (D.weight atomIndex * leverageOf (D.atom atomIndex))
      = ((k : ℝ) - 1) + D.weight atomIndex := by
  have hsize : 2 ≤ k + 1 := by omega
  have hshare := designCoShare_eq_mul D hsize atomIndex
  rw [coRatio_eq_coMean_of_noStrict D hrank hno atomIndex, designCoShare_apply] at hshare
  have hmean := coMean_mul_rank D hrank hno
  linear_combination (-(k : ℝ)) * hshare - (1 - D.weight atomIndex) * hmean

/-- **EVERY `k`-SUBSET DOMINATES.**  The corank-one tie is maximally degenerate: the
weak half of the tie is a conclusion, not a hypothesis. -/
theorem dominates_of_noStrict (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k)
    (hno : NoStrictSelection D) {C : Finset (Fin (k + 1))} (hcard : C.card = k) :
    Dominates D C := by
  obtain ⟨eraseIndex, rfl⟩ := exists_erase_of_card_eq hcard
  exact dominates_erase_of_coMean_le D hrank eraseIndex
    (le_of_eq (coRatio_eq_coMean_of_noStrict D hrank hno eraseIndex).symm)

/-- The leverage law forces every co-ratio to be `1 / k`, hence equal to the
co-mean. -/
theorem coRatio_eq_coMean_of_law (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k)
    (hlaw : ∀ atomIndex : Fin (k + 1),
      (k : ℝ) * (D.weight atomIndex * leverageOf (D.atom atomIndex))
        = ((k : ℝ) - 1) + D.weight atomIndex) (atomIndex : Fin (k + 1)) :
    coRatio D atomIndex = coMean D := by
  have hsize : 2 ≤ k + 1 := by omega
  have hcast : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hratio : ∀ other : Fin (k + 1), coRatio D other * (k : ℝ) = 1 := by
    intro other
    have hslack := one_sub_weight_pos_of_size D hsize other
    have hshare : designCoShare D other * (k : ℝ) = 1 - D.weight other := by
      rw [designCoShare_apply]
      nlinarith [hlaw other]
    rw [coRatio, div_mul_eq_mul_div, hshare, div_self hslack.ne']
  have hmean : coMean D * (k : ℝ) = 1 := by
    rw [coMean, Finset.sum_mul]
    have hterm : ∀ other : Fin (k + 1),
        D.weight other * coRatio D other * (k : ℝ) = D.weight other := by
      intro other
      linear_combination D.weight other * hratio other
    rw [Finset.sum_congr rfl fun other _ => hterm other, D.weight_sum_one]
  have hdiff : (coRatio D atomIndex - coMean D) * (k : ℝ) = 0 := by
    linear_combination hratio atomIndex - hmean
  rcases mul_eq_zero.mp hdiff with hzero | hzero
  · linarith
  · exact absurd hzero hcast.ne'

/-- **THE RESOLUTION OF A READING.**  Any coefficient vector orthogonal to the
dependency is realised as the reading vector of an explicit probe.  This is the
surjectivity that the singular direction needs, and it costs one identity. -/
theorem exists_probe_of_reading (D : WeightedDesign (k + 1) k) {dep : Fin (k + 1) → ℝ}
    (hres : ∀ rowIndex colIndex : Fin (k + 1),
      D.weight rowIndex * ((if rowIndex = colIndex then (1 : ℝ) else 0)
          - D.weight colIndex * (D.atom rowIndex ⬝ᵥ D.atom colIndex))
        = dep rowIndex * dep colIndex)
    (target : Fin (k + 1) → ℝ) (horth : ∑ atomIndex, dep atomIndex * target atomIndex = 0) :
    ∃ probe : Fin k → ℝ, ∀ rowIndex, D.atom rowIndex ⬝ᵥ probe = target rowIndex := by
  classical
  refine ⟨∑ colIndex, (D.weight colIndex * target colIndex) • D.atom colIndex, fun rowIndex => ?_⟩
  have hread : D.atom rowIndex ⬝ᵥ ∑ colIndex, (D.weight colIndex * target colIndex)
        • D.atom colIndex
      = ∑ colIndex, D.weight colIndex * target colIndex
          * (D.atom rowIndex ⬝ᵥ D.atom colIndex) := by
    rw [dotProduct_sum]
    exact Finset.sum_congr rfl fun colIndex _ => by rw [dotProduct_smul, smul_eq_mul]
  have hbalance : ∑ colIndex, D.weight rowIndex
      * ((if rowIndex = colIndex then (1 : ℝ) else 0) * target colIndex
        - D.weight colIndex * (D.atom rowIndex ⬝ᵥ D.atom colIndex) * target colIndex) = 0 := by
    have hterm : ∀ colIndex : Fin (k + 1), D.weight rowIndex
        * ((if rowIndex = colIndex then (1 : ℝ) else 0) * target colIndex
          - D.weight colIndex * (D.atom rowIndex ⬝ᵥ D.atom colIndex) * target colIndex)
        = dep rowIndex * (dep colIndex * target colIndex) := by
      intro colIndex
      have hentry := hres rowIndex colIndex
      linear_combination target colIndex * hentry
    rw [Finset.sum_congr rfl fun colIndex _ => hterm colIndex, ← Finset.mul_sum, horth, mul_zero]
  have hpick : ∑ colIndex, (if rowIndex = colIndex then (1 : ℝ) else 0) * target colIndex
      = target rowIndex := by
    have hterm : ∀ colIndex : Fin (k + 1),
        (if rowIndex = colIndex then (1 : ℝ) else 0) * target colIndex
          = if rowIndex = colIndex then target colIndex else 0 := by
      intro colIndex
      by_cases hcase : rowIndex = colIndex
      · rw [if_pos hcase, if_pos hcase, one_mul]
      · rw [if_neg hcase, if_neg hcase, zero_mul]
    rw [Finset.sum_congr rfl fun colIndex _ => hterm colIndex,
      Finset.sum_ite_eq Finset.univ rowIndex target]
    simp
  have hsplit : ∑ colIndex, D.weight rowIndex
      * ((if rowIndex = colIndex then (1 : ℝ) else 0) * target colIndex
        - D.weight colIndex * (D.atom rowIndex ⬝ᵥ D.atom colIndex) * target colIndex)
      = D.weight rowIndex * ((∑ colIndex,
            (if rowIndex = colIndex then (1 : ℝ) else 0) * target colIndex)
          - ∑ colIndex, D.weight colIndex * target colIndex
              * (D.atom rowIndex ⬝ᵥ D.atom colIndex)) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun colIndex _ => by ring
  rw [hsplit, hpick] at hbalance
  rw [hread]
  rcases mul_eq_zero.mp hbalance with hbad | hgood
  · exact absurd hbad (D.weight_pos rowIndex).ne'
  · linarith [hgood]

/-- **THE SINGULAR DIRECTION AT THE LEVERAGE LAW.**  Under the law every erased
gap has an explicit nonzero null direction, so no `k`-subset dominates strictly.
The reading vector is `dep_c / (1 - t_c)` off the erased label and `-dep_d / t_d`
at it, which is exactly the Cauchy-Schwarz extremal. -/
theorem exists_null_probe_of_law (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k)
    (hlaw : ∀ atomIndex : Fin (k + 1),
      (k : ℝ) * (D.weight atomIndex * leverageOf (D.atom atomIndex))
        = ((k : ℝ) - 1) + D.weight atomIndex) (eraseIndex : Fin (k + 1)) :
    ∃ probe : Fin k → ℝ, probe ≠ 0
      ∧ probe ⬝ᵥ ((subsetSum D (Finset.univ.erase eraseIndex) - 1) *ᵥ probe) = 0 := by
  classical
  have hsize : 2 ≤ k + 1 := by omega
  have hslack : ∀ atomIndex : Fin (k + 1), 0 < 1 - D.weight atomIndex :=
    one_sub_weight_pos_of_size D hsize
  have hmeanPos := coMean_pos D hrank
  have hequal := coRatio_eq_coMean_of_law D hrank hlaw
  obtain ⟨dep, -, hnorm, hres⟩ := exists_dependency D
  -- every co-share is the outside weight times the common co-mean
  have hshare : ∀ atomIndex : Fin (k + 1),
      designCoShare D atomIndex = (1 - D.weight atomIndex) * coMean D := by
    intro atomIndex
    rw [designCoShare_eq_mul D hsize atomIndex, hequal atomIndex]
  have hdepSq : ∀ atomIndex : Fin (k + 1),
      dep atomIndex ^ 2 = D.weight atomIndex * ((1 - D.weight atomIndex) * coMean D) := by
    intro atomIndex
    rw [hnorm atomIndex, hshare atomIndex]
  set target : Fin (k + 1) → ℝ :=
    fun atomIndex => if atomIndex = eraseIndex then -(dep atomIndex / D.weight atomIndex)
      else dep atomIndex / (1 - D.weight atomIndex) with htarget
  have htargetOff : ∀ atomIndex : Fin (k + 1), atomIndex ≠ eraseIndex →
      target atomIndex = dep atomIndex / (1 - D.weight atomIndex) := by
    intro atomIndex hne
    simp only [htarget, if_neg hne]
  have htargetAt : target eraseIndex = -(dep eraseIndex / D.weight eraseIndex) := by
    simp only [htarget, if_pos rfl]
  have hmass : ∑ atomIndex, dep atomIndex ^ 2 / (1 - D.weight atomIndex) = coMean D :=
    dep_mass_eq_coMean D hsize hnorm
  have hpeel : dep eraseIndex ^ 2 / (1 - D.weight eraseIndex)
      = D.weight eraseIndex * coMean D := by
    rw [hdepSq eraseIndex, div_eq_iff (hslack eraseIndex).ne']
    ring
  have hmassOff : ∑ atomIndex ∈ Finset.univ.erase eraseIndex,
      dep atomIndex ^ 2 / (1 - D.weight atomIndex)
      = (1 - D.weight eraseIndex) * coMean D := by
    have hsplit := Finset.add_sum_erase _
      (fun atomIndex => dep atomIndex ^ 2 / (1 - D.weight atomIndex))
      (Finset.mem_univ eraseIndex)
    rw [hmass, hpeel] at hsplit
    linear_combination hsplit
  have horth : ∑ atomIndex, dep atomIndex * target atomIndex = 0 := by
    have hsplit := Finset.add_sum_erase _
      (fun atomIndex => dep atomIndex * target atomIndex) (Finset.mem_univ eraseIndex)
    have hoffSum : ∑ atomIndex ∈ Finset.univ.erase eraseIndex, dep atomIndex * target atomIndex
        = ∑ atomIndex ∈ Finset.univ.erase eraseIndex,
          dep atomIndex ^ 2 / (1 - D.weight atomIndex) := by
      refine Finset.sum_congr rfl fun atomIndex hatom => ?_
      rw [htargetOff atomIndex (Finset.mem_erase.mp hatom).1, pow_two, mul_div_assoc]
    have hatSum : dep eraseIndex * target eraseIndex
        = -((1 - D.weight eraseIndex) * coMean D) := by
      rw [htargetAt, mul_neg, ← mul_div_assoc, ← pow_two, hdepSq eraseIndex, neg_inj,
        div_eq_iff (D.weight_pos eraseIndex).ne']
      ring
    rw [hoffSum, hmassOff, hatSum] at hsplit
    linarith [hsplit]
  obtain ⟨probe, hprobe⟩ := exists_probe_of_reading D hres target horth
  have hdepNe : dep eraseIndex ≠ 0 := by
    intro hzero
    have hval := hdepSq eraseIndex
    rw [hzero] at hval
    nlinarith [hval, mul_pos (D.weight_pos eraseIndex)
      (mul_pos (hslack eraseIndex) hmeanPos)]
  have htargetNe : target eraseIndex ≠ 0 := by
    rw [htargetAt]
    simp only [ne_eq, neg_eq_zero, div_eq_zero_iff]
    push_neg
    exact ⟨hdepNe, (D.weight_pos eraseIndex).ne'⟩
  refine ⟨probe, ?_, ?_⟩
  · intro hzero
    exact htargetNe (by rw [← hprobe eraseIndex, hzero, dotProduct_zero])
  · rw [dotProduct_erase_gap_mulVec D eraseIndex]
    have hoffTerm : ∀ atomIndex ∈ Finset.univ.erase eraseIndex,
        (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2
          = dep atomIndex ^ 2 / (1 - D.weight atomIndex) := by
      intro atomIndex hatom
      have hsne := (hslack atomIndex).ne'
      have hsqne : (1 - D.weight atomIndex) ^ 2 ≠ 0 := pow_ne_zero 2 hsne
      rw [hprobe atomIndex, htargetOff atomIndex (Finset.mem_erase.mp hatom).1]
      field_simp
    have hwne := (D.weight_pos eraseIndex).ne'
    have hpeak : (D.atom eraseIndex ⬝ᵥ probe) ^ 2
        = (1 - D.weight eraseIndex) * coMean D / D.weight eraseIndex := by
      rw [hprobe eraseIndex, htargetAt, neg_sq, div_pow, hdepSq eraseIndex,
        div_eq_div_iff (pow_ne_zero 2 hwne) hwne]
      ring
    have hatTerm : (1 - D.weight eraseIndex) * (D.atom eraseIndex ⬝ᵥ probe) ^ 2
        = (1 - D.weight eraseIndex) ^ 2 * coMean D / D.weight eraseIndex := by
      rw [hpeak]
      ring
    have hsplit := Finset.add_sum_erase _
      (fun atomIndex => (1 - D.weight atomIndex) * (D.atom atomIndex ⬝ᵥ probe) ^ 2)
      (Finset.mem_univ eraseIndex)
    rw [Finset.sum_congr rfl hoffTerm, hmassOff, hatTerm] at hsplit
    have hcombine : (1 - D.weight eraseIndex) ^ 2 * coMean D / D.weight eraseIndex
        - (1 - D.weight eraseIndex) * coMean D / D.weight eraseIndex
        = -((1 - D.weight eraseIndex) * coMean D) := by
      rw [div_sub_div_same, div_eq_iff hwne]
      ring
    rw [← hsplit, hpeak]
    linarith [hcombine]

/-- **THE CORANK-ONE TIE IS EXACTLY THE LEVERAGE LAW.**  Both directions, at every
rank `k ≥ 1`. -/
theorem isTie_iff_leverage_law (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k) :
    IsTie D ↔ ∀ atomIndex : Fin (k + 1),
      (k : ℝ) * (D.weight atomIndex * leverageOf (D.atom atomIndex))
        = ((k : ℝ) - 1) + D.weight atomIndex := by
  classical
  constructor
  · intro htie atomIndex
    exact rank_mul_share_eq_of_noStrict D hrank (noStrictSelection_of_isTie D htie) atomIndex
  · intro hlaw
    have hequal := coRatio_eq_coMean_of_law D hrank hlaw
    refine ⟨⟨Finset.univ.erase ⟨0, by omega⟩, card_univ_erase _, ?_⟩, ?_⟩
    · exact dominates_erase_of_coMean_le D hrank _ (le_of_eq (hequal _).symm)
    · intro C hcard hposDef
      obtain ⟨eraseIndex, rfl⟩ := exists_erase_of_card_eq hcard
      obtain ⟨probe, hprobeNe, hprobeZero⟩ := exists_null_probe_of_law D hrank hlaw eraseIndex
      have hstrict := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
      rw [star_trivial, hprobeZero] at hstrict
      exact absurd hstrict (lt_irrefl 0)

/-! ## 6. Parallel-freeness, and the refutation at the whole stratum -/

/-- **A CORANK-ONE TIE HAS NO PARALLEL PAIR**, at every rank `k ≥ 2`.  The pairing
cap is saturated at corank one, and the leverage law puts its two sides on opposite
sides of one. -/
theorem not_hasParallelPair_of_isTie_succ_rank (D : WeightedDesign (k + 1) k) (hrank : 2 ≤ k)
    (htie : IsTie D) : ¬ HasParallelPair D := by
  classical
  rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
  have hrankOne : 1 ≤ k := by omega
  have hsize : 2 ≤ k + 1 := by omega
  have hlaw := (isTie_iff_leverage_law D hrankOne).mp htie
  have hcast : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrank
  have hsat := weight_mul_sq_dotProduct_eq_coShare_mul D hdistinct
  have hpair : (D.atom keptLabel ⬝ᵥ D.atom dropLabel) ^ 2
      = leverageOf (D.atom keptLabel) * leverageOf (D.atom dropLabel) := by
    have hdot : D.atom keptLabel ⬝ᵥ D.atom dropLabel
        = ratio * leverageOf (D.atom keptLabel) := by
      rw [hparallel, dotProduct_smul, smul_eq_mul, leverageOf_eq_dotProduct]
    have hlev : leverageOf (D.atom dropLabel) = ratio ^ 2 * leverageOf (D.atom keptLabel) := by
      rw [hparallel, leverageOf_eq_dotProduct, leverageOf_eq_dotProduct, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [hdot, hlev]
    ring
  have hshare : ∀ atomIndex : Fin (k + 1),
      designCoShare D atomIndex * (k : ℝ) = 1 - D.weight atomIndex := by
    intro atomIndex
    rw [designCoShare_apply]
    nlinarith [hlaw atomIndex]
  have hkeptSlack := one_sub_weight_pos_of_size D hsize keptLabel
  have hdropSlack := one_sub_weight_pos_of_size D hsize dropLabel
  have hkeptPos := D.weight_pos keptLabel
  have hdropPos := D.weight_pos dropLabel
  have hclash : ((k : ℝ) - 1 + D.weight keptLabel) * ((k : ℝ) - 1 + D.weight dropLabel)
      = (1 - D.weight keptLabel) * (1 - D.weight dropLabel) := by
    have hstep : (k : ℝ) ^ 2 * (D.weight keptLabel * D.weight dropLabel
        * (D.atom keptLabel ⬝ᵥ D.atom dropLabel) ^ 2)
        = (k : ℝ) ^ 2 * (designCoShare D keptLabel * designCoShare D dropLabel) := by rw [hsat]
    have hleftEq : (k : ℝ) ^ 2 * (D.weight keptLabel * D.weight dropLabel
        * (D.atom keptLabel ⬝ᵥ D.atom dropLabel) ^ 2)
        = ((k : ℝ) * (D.weight keptLabel * leverageOf (D.atom keptLabel)))
          * ((k : ℝ) * (D.weight dropLabel * leverageOf (D.atom dropLabel))) := by
      rw [hpair]; ring
    have hrightEq : (k : ℝ) ^ 2 * (designCoShare D keptLabel * designCoShare D dropLabel)
        = (designCoShare D keptLabel * (k : ℝ)) * (designCoShare D dropLabel * (k : ℝ)) := by ring
    rw [hleftEq, hlaw keptLabel, hlaw dropLabel, hrightEq, hshare keptLabel,
      hshare dropLabel] at hstep
    exact hstep
  have hlow : (1 + D.weight keptLabel) * (1 + D.weight dropLabel)
      ≤ ((k : ℝ) - 1 + D.weight keptLabel) * ((k : ℝ) - 1 + D.weight dropLabel) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  nlinarith [hlow, hclash, hkeptPos, hdropPos]

/-- **THE HINGE IS FALSE AT `(k+1, k)` FOR EVERY RANK `k ≥ 2`, AT THE WHOLE
STRATUM.**  Not one witness: no corank-one tie whatsoever carries a parallel pair,
and the stratum is inhabited at every rank.

CONSEQUENCE FOR THE REGISTRY.  `Skeleton.obligationSubThresholdBandHinge` guards
its sizes from below by `2 * rank`.  That guard is NECESSARY at every rank, since
`rank + 1 < 2 * rank` for `rank ≥ 2`.  The tree's `Gtz.not_hingeHoldsAtSize_succ_rank`
reaches the same conclusion from the single explicit `Gtz.flatSimplexDesign`, and
only for `3 ≤ rank`. -/
theorem not_hingeHoldsAtSize_succ_rank' {rank : ℕ} (hrank : 2 ≤ rank) :
    ¬ HingeHoldsAtSize (rank + 1) rank := by
  intro hhinge
  exact not_hasParallelPair_of_isTie_succ_rank (flatSimplexDesign rank (by omega)) hrank
    (flatSimplexDesign_isTie (by omega))
    (hhinge (flatSimplexDesign rank (by omega)) (flatSimplexDesign_isTie (by omega)))

/-- **THE CLASSIFICATION.**  The corank-one tie stratum is exactly the
leverage-law locus, every one of its `k`-subsets dominates, and it is
parallel-free at every rank `k ≥ 2`. -/
theorem corankOne_tie_classification (D : WeightedDesign (k + 1) k) (hrank : 2 ≤ k) :
    IsTie D ↔ ((∀ atomIndex : Fin (k + 1),
        (k : ℝ) * (D.weight atomIndex * leverageOf (D.atom atomIndex))
          = ((k : ℝ) - 1) + D.weight atomIndex)
      ∧ (∀ C : Finset (Fin (k + 1)), C.card = k → Dominates D C)
      ∧ ¬ HasParallelPair D) := by
  have hrankOne : 1 ≤ k := by omega
  constructor
  · intro htie
    exact ⟨(isTie_iff_leverage_law D hrankOne).mp htie,
      fun C hcard => dominates_of_noStrict D hrankOne (noStrictSelection_of_isTie D htie) hcard,
      not_hasParallelPair_of_isTie_succ_rank D hrank htie⟩
  · intro hpack
    exact (isTie_iff_leverage_law D hrankOne).mpr hpack.1

end Gtz

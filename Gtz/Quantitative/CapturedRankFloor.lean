import Mathlib
import Gtz.Quantitative.ChartMultiplierSplit
import Gtz.Quantitative.PrivateAtomQuantization
import Gtz.Quantitative.ChartFloorAtomSpan
import Gtz.Quantitative.SixThreeCrux
import Gtz.Design.NearPencilTransport
import Gtz.Design.TightAntecedentMining
import Gtz.Design.LeverageBound
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The captured rank floor — both corners of the stationary assembly have rank at least two

At a chart stationarity datum the assembly `Xi` commutes with the chart `P`, so it
splits into the two captured corners `P Xi` and `(1 - P) Xi`, both positive
semidefinite congruences of `Xi`.  This file proves that AT NEGATIVE VALUE neither
corner can have range dimension at most one, from the landed bundle alone.

The two sides close by different mechanisms, and the hypotheses differ accordingly:

* **The complement corner** (`false_of_complementCaptured_range_finrank_le_one`)
  dies by a Rayleigh estimate with NO multiplier positivity and NO window
  strictness.  A rank-one complement corner factors through one unit direction
  `w` annihilated by the chart; the assembly's constant diagonal caps every
  coordinate mass `lam * w_c^2` by `1/size`, so Cauchy-Schwarz on each block's
  `rank`-atom support caps every squared overlap `lam * (u ⬝ᵥ w)^2` by
  `rank/size`, and averaging over the multipliers gives `lam^2 ≤ rank/size`.
  But the complement corner's trace is `lam = 1 - value - 1/size`, which at
  negative value strictly exceeds `(size - 1)/size`.  Whenever
  `rank * size ≤ (size - 1)^2` — at `(6,3)`: `18 ≤ 25` — the two bounds clash.
* **The primal corner** (`false_of_projectedCaptured_range_finrank_le_one`) dies
  by transporting rank one into COLLINEARITY of the projected tight directions of
  the positively weighted blocks — each is forced onto the factor line by a
  residual argument — and firing the landed closing theorem
  `false_of_projected_tightDir_collinear`, which needs the strict window
  `-1/size < value` its statement carries.

The `(6,3)` crux corollaries discharge both side conditions from the crux fields:
the strict window from `neg_inv_size_lt_value_of_isChartStationaryData` and the
geometry inequality by arithmetic.  Neither corollary needs multiplier positivity,
so both apply to EVERY stationary datum a crux produces, at every active count
and every multiplier support — including supports with vanishing multipliers,
where the positively-restricted formulations do not reach.

Downstream, with `rank(P Xi) ≥ 2` and `rank((1 - P) Xi) ≥ 2` and the two corners'
ranges intersecting trivially, every crux assembly has rank at least four; at four
active blocks this forces all four multipliers positive, the four tight directions
independent, and the spectral regime `(2,2)` with coefficient trace two.
-/

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}
variable {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
  {value : ℝ} {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## The rank-one factorization -/

/-- **Cauchy–Schwarz for the dot product**, squared form. -/
theorem dotProduct_sq_le_dotProduct_mul_dotProduct (leftVec rightVec : Fin size → ℝ) :
    (leftVec ⬝ᵥ rightVec) ^ 2 ≤ (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ leftVec rightVec
  simpa [dotProduct, pow_two] using hcs

/-- **A symmetric matrix of positive trace and range dimension at most one is its
trace times the atom matrix of a unit direction.**  The range is a genuine line
because the trace is nonzero, every image is a multiple of a spanning unit vector,
and symmetry identifies the multiple as the trace against that direction. -/
theorem exists_unit_eq_trace_smul_atomMatrix_of_symmetric_of_range_finrank_le_one
    (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form)
    (hrange : Module.finrank ℝ (LinearMap.range (Matrix.toLin' form)) ≤ 1)
    (htrace : 0 < Matrix.trace form) :
    ∃ direction : Fin size → ℝ,
      direction ⬝ᵥ direction = 1 ∧
      form = Matrix.trace form • atomMatrix direction := by
  let formRange : Submodule ℝ (Fin size → ℝ) :=
    LinearMap.range (Matrix.toLin' form)
  have hformNe : form ≠ 0 := by
    intro hzero
    rw [hzero, Matrix.trace_zero] at htrace
    exact lt_irrefl 0 htrace
  have hlinearNe : Matrix.toLin' form ≠ 0 := by
    intro hzero
    apply hformNe
    apply Matrix.toLin'.injective
    simpa using hzero
  have hrangeNe : formRange ≠ ⊥ := by
    dsimp only [formRange]
    intro hbot
    exact hlinearNe (LinearMap.range_eq_bot.mp hbot)
  have hrangeOne : Module.finrank ℝ formRange = 1 := by
    have hrangePos : 0 < Module.finrank ℝ formRange := by
      rw [Module.finrank_pos_iff]
      exact Submodule.nontrivial_iff_ne_bot.mpr hrangeNe
    change Module.finrank ℝ formRange ≤ 1 at hrange
    omega
  obtain ⟨rawDirection, hrawRange, hrawNe⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hrangeNe
  let direction := normalizedDirection rawDirection
  have hdirectionUnit : direction ⬝ᵥ direction = 1 :=
    normalizedDirection_isUnit rawDirection hrawNe
  have hdirectionNe : direction ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hdirectionUnit
    exact one_ne_zero hdirectionUnit.symm
  have hdirectionRange : direction ∈ formRange :=
    formRange.smul_mem ((Real.sqrt (rawDirection ⬝ᵥ rawDirection))⁻¹) hrawRange
  let directionInRange : formRange := ⟨direction, hdirectionRange⟩
  have hdirectionInRangeNe : directionInRange ≠ 0 := by
    intro hzero
    apply hdirectionNe
    exact congrArg Subtype.val hzero
  have hmultiple : ∀ vector : Fin size → ℝ,
      ∃ coefficient : ℝ, coefficient • direction = form *ᵥ vector := by
    intro vector
    let imageInRange : formRange :=
      ⟨form *ᵥ vector, ⟨vector, by rw [Matrix.toLin'_apply]⟩⟩
    obtain ⟨coefficient, hcoefficient⟩ :=
      exists_smul_eq_of_finrank_eq_one hrangeOne hdirectionInRangeNe imageInRange
    exact ⟨coefficient, congrArg Subtype.val hcoefficient⟩
  obtain ⟨eigenvalue, heigenvalue⟩ := hmultiple direction
  have hmulVec : ∀ vector : Fin size → ℝ,
      form *ᵥ vector = eigenvalue • (atomMatrix direction *ᵥ vector) := by
    intro vector
    obtain ⟨coefficient, hcoefficient⟩ := hmultiple vector
    have hcoefficientEq : coefficient = eigenvalue * (direction ⬝ᵥ vector) := by
      have hleft := congrArg (fun image => direction ⬝ᵥ image) hcoefficient
      rw [dotProduct_smul, smul_eq_mul, hdirectionUnit] at hleft
      have hleft' : coefficient = direction ⬝ᵥ (form *ᵥ vector) := by
        simpa using hleft
      have hsymmetry : direction ⬝ᵥ (form *ᵥ vector) = (form *ᵥ direction) ⬝ᵥ vector := by
        calc
          direction ⬝ᵥ (form *ᵥ vector) = (formᵀ *ᵥ direction) ⬝ᵥ vector :=
            (dotProduct_mulVec_transpose form direction vector).symm
          _ = (form *ᵥ direction) ⬝ᵥ vector := by rw [hsymmetric]
      rw [hsymmetry, ← heigenvalue, smul_dotProduct, smul_eq_mul] at hleft'
      exact hleft'
    rw [← hcoefficient, hcoefficientEq, atomMatrix_mulVec_eq_smul, smul_smul]
  have hformEq : form = eigenvalue • atomMatrix direction := by
    apply Matrix.ext_of_mulVec_single
    intro basisIndex
    rw [hmulVec, Matrix.smul_mulVec]
  have heigenvalueTrace : eigenvalue = Matrix.trace form := by
    have htraceEq : Matrix.trace form = eigenvalue := by
      calc
        Matrix.trace form = Matrix.trace (eigenvalue • atomMatrix direction) :=
          congrArg Matrix.trace hformEq
        _ = eigenvalue := by
          rw [Matrix.trace_smul, trace_atomMatrix, leverageOf_eq_dotProduct,
            hdirectionUnit, smul_eq_mul, mul_one]
    exact htraceEq.symm
  exact ⟨direction, hdirectionUnit,
    hformEq.trans (congrArg (fun coefficient => coefficient • atomMatrix direction)
      heigenvalueTrace)⟩

/-- An operator that fixes a nonzero multiple of an atom matrix fixes its
direction. -/
theorem mulVec_direction_eq_self_of_mul_smul_atomMatrix
    {operator : Matrix (Fin size) (Fin size) ℝ} {direction : Fin size → ℝ}
    (hdirectionUnit : direction ⬝ᵥ direction = 1) {lam : ℝ} (hlamNe : lam ≠ 0)
    (hinvariant : operator * (lam • atomMatrix direction) = lam • atomMatrix direction) :
    operator *ᵥ direction = direction := by
  have hinner : (lam • atomMatrix direction) *ᵥ direction = lam • direction := by
    rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul, hdirectionUnit, one_smul]
  have happly := congrArg
    (fun matrixForm : Matrix (Fin size) (Fin size) ℝ => matrixForm *ᵥ direction) hinvariant
  rw [← Matrix.mulVec_mulVec, hinner, Matrix.mulVec_smul] at happly
  exact smul_right_injective (Fin size → ℝ) hlamNe happly

/-! ## The complement corner: diagonal, trace, positivity -/

/-- The complement corner's diagonal never exceeds the assembly's constant
diagonal `1/size`: the primal corner's diagonal is nonnegative. -/
theorem diagonal_complementProjection_mul_multiplier_le_inv_size
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir)
        atomIndex atomIndex ≤ ((size : ℝ))⁻¹ := by
  have hentry : ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir)
        atomIndex atomIndex
      = chartMultiplierAssembly activeSet activeWeight tightDir atomIndex atomIndex
        - (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
            atomIndex atomIndex := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply]
  have hnonneg :=
    (posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata).diag_nonneg
      (i := atomIndex)
  rw [hentry, hdata.assembly_diagonal atomIndex]
  linarith

/-- The complement corner's trace: `1 - value - 1/size`. -/
theorem trace_complementProjection_mul_multiplier_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    Matrix.trace ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir)
      = 1 - value - ((size : ℝ))⁻¹ := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    trace_chartMultiplierAssembly_of_isChartStationaryData hdata,
    trace_projection_mul_multiplier_of_isChartStationaryData hdata]
  ring

/-- The complement corner is positive semidefinite — the Naimark mirror of the
primal corner's positivity. -/
theorem posSemidef_complementProjection_mul_multiplier_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir).PosSemidef := by
  have hconj : (1 - projection : Matrix (Fin size) (Fin size) ℝ)ᴴ = 1 - projection := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_one, hdata.isSymmetric]
  have hsandwich :=
    (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata).mul_mul_conjTranspose_same
      (1 - projection)
  rw [hconj] at hsandwich
  rw [complementProjection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata]
  exact hsandwich

/-! ## The support-restricted Cauchy–Schwarz bound -/

/-- A tight direction's overlap with any probe is controlled by the probe's mass
on the direction's own block: the direction is unit and supported there. -/
theorem sq_dotProduct_tightDir_le_sum_sq_on_subset
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet) (probe : Fin size → ℝ) :
    (tightDir activeLabel ⬝ᵥ probe) ^ 2
      ≤ ∑ atomIndex ∈ activeSubset activeLabel, probe atomIndex ^ 2 := by
  classical
  let restrictedProbe : Fin size → ℝ := fun atomIndex =>
    if atomIndex ∈ activeSubset activeLabel then probe atomIndex else 0
  have hdotEq : tightDir activeLabel ⬝ᵥ probe = tightDir activeLabel ⬝ᵥ restrictedProbe := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    dsimp only [restrictedProbe]
    by_cases hmemSubset : atomIndex ∈ activeSubset activeLabel
    · rw [if_pos hmemSubset]
    · rw [if_neg hmemSubset, hdata.tightDir_support activeLabel hmem atomIndex hmemSubset]
      ring
  have hrestrictedNorm : restrictedProbe ⬝ᵥ restrictedProbe
      = ∑ atomIndex ∈ activeSubset activeLabel, probe atomIndex ^ 2 := by
    have hterms : ∀ atomIndex : Fin size,
        restrictedProbe atomIndex * restrictedProbe atomIndex
          = if atomIndex ∈ activeSubset activeLabel then probe atomIndex ^ 2 else 0 := by
      intro atomIndex
      dsimp only [restrictedProbe]
      by_cases hmemSubset : atomIndex ∈ activeSubset activeLabel
      · rw [if_pos hmemSubset, if_pos hmemSubset, pow_two]
      · rw [if_neg hmemSubset, if_neg hmemSubset, mul_zero]
    simp only [dotProduct]
    calc ∑ atomIndex : Fin size, restrictedProbe atomIndex * restrictedProbe atomIndex
        = ∑ atomIndex : Fin size,
            (if atomIndex ∈ activeSubset activeLabel then probe atomIndex ^ 2 else 0) :=
          Finset.sum_congr rfl fun atomIndex _ => hterms atomIndex
      _ = ∑ atomIndex ∈ activeSubset activeLabel, probe atomIndex ^ 2 := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hcs := dotProduct_sq_le_dotProduct_mul_dotProduct (tightDir activeLabel) restrictedProbe
  rw [hdata.tightDir_unit activeLabel hmem, one_mul, hrestrictedNorm] at hcs
  rw [hdotEq]
  exact hcs

/-! ## The complement corner is never rank one -/

/-- **THE COMPLEMENT CAPTURED CORNER IS NEVER RANK ONE AT NEGATIVE VALUE**, at any
stationarity datum whose size and rank satisfy `rank * size ≤ (size - 1)^2` — no
multiplier positivity, no window strictness, no support restriction.

Rank one factors the corner through one unit direction `w` with `P w = 0` and
per-atom masses `lam * w_c^2 ≤ 1/size`; Cauchy–Schwarz on each block's support
then caps every scaled squared overlap by `rank/size`, and the multiplier average
gives `lam^2 ≤ rank/size` for the corner's trace `lam = 1 - value - 1/size`.  At
negative value `lam` strictly exceeds `(size - 1)/size`, which the geometry
hypothesis contradicts. -/
theorem false_of_complementCaptured_range_finrank_le_one
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hnegative : value < 0)
    (hgeometry : (rank : ℝ) * size ≤ ((size : ℝ) - 1) ^ 2)
    (hrange : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir))) ≤ 1) :
    False := by
  classical
  have hsizePos : (0 : ℝ) < (size : ℝ) := size_cast_pos_of_isChartStationaryData hdata
  have hsizeNe : ((size : ℝ)) ≠ 0 := ne_of_gt hsizePos
  have hinvPos : (0 : ℝ) < ((size : ℝ))⁻¹ := inv_pos.mpr hsizePos
  have hcancel : ((size : ℝ))⁻¹ * (size : ℝ) = 1 := inv_mul_cancel₀ hsizeNe
  have honeLe : (1 : ℝ) ≤ (size : ℝ) := by
    exact_mod_cast size_pos_of_isChartStationaryData hdata
  have hinvLeOne : ((size : ℝ))⁻¹ ≤ 1 := by
    calc ((size : ℝ))⁻¹ = ((size : ℝ))⁻¹ * 1 := (mul_one _).symm
      _ ≤ ((size : ℝ))⁻¹ * (size : ℝ) := by
          exact mul_le_mul_of_nonneg_left honeLe hinvPos.le
      _ = 1 := hcancel
  have htrace :
      Matrix.trace ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir)
        = 1 - value - ((size : ℝ))⁻¹ :=
    trace_complementProjection_mul_multiplier_of_isChartStationaryData hdata
  have hlamPos : (0 : ℝ) < 1 - value - ((size : ℝ))⁻¹ := by linarith
  have hlamNe : (1 - value - ((size : ℝ))⁻¹ : ℝ) ≠ 0 := ne_of_gt hlamPos
  have hpsd :=
    posSemidef_complementProjection_mul_multiplier_of_isChartStationaryData hdata
  have hsymmetric :
      ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir)ᵀ
        = (1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir := by
    have hhermitian := hpsd.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at hhermitian
  obtain ⟨direction, hdirectionUnit, hfactor⟩ :=
    exists_unit_eq_trace_smul_atomMatrix_of_symmetric_of_range_finrank_le_one
      ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir)
      hsymmetric hrange (by rw [htrace]; exact hlamPos)
  rw [htrace] at hfactor
  have hdiagCap : ∀ atomIndex : Fin size,
      (1 - value - ((size : ℝ))⁻¹) * direction atomIndex ^ 2 ≤ ((size : ℝ))⁻¹ := by
    intro atomIndex
    have hentry := congrArg
      (fun matrixForm : Matrix (Fin size) (Fin size) ℝ => matrixForm atomIndex atomIndex) hfactor
    simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul] at hentry
    have hbound := diagonal_complementProjection_mul_multiplier_le_inv_size hdata atomIndex
    rw [hentry] at hbound
    calc (1 - value - ((size : ℝ))⁻¹) * direction atomIndex ^ 2
        = (1 - value - ((size : ℝ))⁻¹) * (direction atomIndex * direction atomIndex) := by
          rw [pow_two]
      _ ≤ ((size : ℝ))⁻¹ := hbound
  have hcomplementIdempotent :
      (1 - projection) * (1 - projection) = (1 - projection : Matrix (Fin size) (Fin size) ℝ) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hdata.isIdempotent,
      sub_self, sub_zero]
  have hfixedOp : (1 - projection)
        * ((1 - value - ((size : ℝ))⁻¹) • atomMatrix direction)
      = (1 - value - ((size : ℝ))⁻¹) • atomMatrix direction := by
    rw [← hfactor, ← Matrix.mul_assoc, hcomplementIdempotent]
  have hfixed : (1 - projection) *ᵥ direction = direction :=
    mulVec_direction_eq_self_of_mul_smul_atomMatrix hdirectionUnit hlamNe hfixedOp
  have hkilled : projection *ᵥ direction = 0 := by
    have hexpand := hfixed
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hexpand
    exact sub_eq_self.mp hexpand
  have henergyCaptured : direction ⬝ᵥ
      (((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir) *ᵥ direction)
        = 1 - value - ((size : ℝ))⁻¹ := by
    rw [hfactor, Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul, hdirectionUnit, one_smul,
      dotProduct_smul, smul_eq_mul, hdirectionUnit, mul_one]
  have henergyAssembly : direction ⬝ᵥ
      (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ direction)
        = 1 - value - ((size : ℝ))⁻¹ := by
    have hsplit :
        ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir) *ᵥ direction
          = chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ direction
            - projection *ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ direction) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    have hcross : direction ⬝ᵥ
        (projection *ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ direction))
          = 0 := by
      have hswap := dotProduct_mulVec_transpose projection direction
        (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ direction)
      rw [hdata.isSymmetric, hkilled, zero_dotProduct] at hswap
      exact hswap.symm
    have hchain := henergyCaptured
    rw [hsplit, dotProduct_sub, hcross, sub_zero] at hchain
    exact hchain
  have hsum : ∑ activeLabel ∈ activeSet,
      activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ direction) ^ 2
        = 1 - value - ((size : ℝ))⁻¹ := by
    rw [← dotProduct_mulVec_chartMultiplierAssembly]
    exact henergyAssembly
  have hblockCap : ∀ activeLabel ∈ activeSet,
      (1 - value - ((size : ℝ))⁻¹) * (tightDir activeLabel ⬝ᵥ direction) ^ 2
        ≤ (rank : ℝ) * ((size : ℝ))⁻¹ := by
    intro activeLabel hmem
    have hcs := sq_dotProduct_tightDir_le_sum_sq_on_subset hdata hmem direction
    have hscaled : (1 - value - ((size : ℝ))⁻¹) * (tightDir activeLabel ⬝ᵥ direction) ^ 2
        ≤ (1 - value - ((size : ℝ))⁻¹)
          * ∑ atomIndex ∈ activeSubset activeLabel, direction atomIndex ^ 2 :=
      mul_le_mul_of_nonneg_left hcs hlamPos.le
    have hsumCap : (1 - value - ((size : ℝ))⁻¹)
          * ∑ atomIndex ∈ activeSubset activeLabel, direction atomIndex ^ 2
        ≤ (rank : ℝ) * ((size : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      calc ∑ atomIndex ∈ activeSubset activeLabel,
            (1 - value - ((size : ℝ))⁻¹) * direction atomIndex ^ 2
          ≤ ∑ _atomIndex ∈ activeSubset activeLabel, ((size : ℝ))⁻¹ :=
            Finset.sum_le_sum fun atomIndex _ => hdiagCap atomIndex
        _ = (rank : ℝ) * ((size : ℝ))⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul, hdata.activeSubset_card activeLabel hmem]
    exact hscaled.trans hsumCap
  have hsquare : (1 - value - ((size : ℝ))⁻¹) * (1 - value - ((size : ℝ))⁻¹)
      ≤ (rank : ℝ) * ((size : ℝ))⁻¹ := by
    calc (1 - value - ((size : ℝ))⁻¹) * (1 - value - ((size : ℝ))⁻¹)
        = (1 - value - ((size : ℝ))⁻¹)
          * ∑ activeLabel ∈ activeSet,
              activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ direction) ^ 2 := by
          rw [hsum]
      _ = ∑ activeLabel ∈ activeSet,
            activeWeight activeLabel
              * ((1 - value - ((size : ℝ))⁻¹) * (tightDir activeLabel ⬝ᵥ direction) ^ 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun activeLabel _ => by ring
      _ ≤ ∑ activeLabel ∈ activeSet,
            activeWeight activeLabel * ((rank : ℝ) * ((size : ℝ))⁻¹) :=
          Finset.sum_le_sum fun activeLabel hmem =>
            mul_le_mul_of_nonneg_left (hblockCap activeLabel hmem)
              (hdata.activeWeight_nonneg activeLabel hmem)
      _ = (rank : ℝ) * ((size : ℝ))⁻¹ := by
          rw [← Finset.sum_mul, hdata.activeWeight_sum_one, one_mul]
  have hscaledSquare :
      ((1 - value - ((size : ℝ))⁻¹) * (size : ℝ)) * ((1 - value - ((size : ℝ))⁻¹) * (size : ℝ))
        ≤ (rank : ℝ) * (size : ℝ) := by
    have hstep := mul_le_mul_of_nonneg_right hsquare
      (mul_pos hsizePos hsizePos).le
    calc ((1 - value - ((size : ℝ))⁻¹) * (size : ℝ))
          * ((1 - value - ((size : ℝ))⁻¹) * (size : ℝ))
        = (1 - value - ((size : ℝ))⁻¹) * (1 - value - ((size : ℝ))⁻¹)
          * ((size : ℝ) * (size : ℝ)) := by ring
      _ ≤ (rank : ℝ) * ((size : ℝ))⁻¹ * ((size : ℝ) * (size : ℝ)) := hstep
      _ = (rank : ℝ) * (((size : ℝ))⁻¹ * (size : ℝ)) * (size : ℝ) := by ring
      _ = (rank : ℝ) * (size : ℝ) := by rw [hcancel, mul_one]
  have hshift : (size : ℝ) - 1 < (1 - value - ((size : ℝ))⁻¹) * (size : ℝ) := by
    have hexpand : (1 - value - ((size : ℝ))⁻¹) * (size : ℝ)
        = (size : ℝ) - value * (size : ℝ) - 1 := by
      calc (1 - value - ((size : ℝ))⁻¹) * (size : ℝ)
          = (size : ℝ) - value * (size : ℝ) - ((size : ℝ))⁻¹ * (size : ℝ) := by ring
        _ = (size : ℝ) - value * (size : ℝ) - 1 := by rw [hcancel]
    have hvaluePart : value * (size : ℝ) < 0 := mul_neg_of_neg_of_pos hnegative hsizePos
    rw [hexpand]
    linarith
  have hsqLt : ((size : ℝ) - 1) * ((size : ℝ) - 1)
      < ((1 - value - ((size : ℝ))⁻¹) * (size : ℝ))
        * ((1 - value - ((size : ℝ))⁻¹) * (size : ℝ)) :=
    mul_self_lt_mul_self (by linarith) hshift
  have hchain : ((1 - value - ((size : ℝ))⁻¹) * (size : ℝ))
        * ((1 - value - ((size : ℝ))⁻¹) * (size : ℝ))
      ≤ ((size : ℝ) - 1) * ((size : ℝ) - 1) := by
    calc ((1 - value - ((size : ℝ))⁻¹) * (size : ℝ))
          * ((1 - value - ((size : ℝ))⁻¹) * (size : ℝ))
        ≤ (rank : ℝ) * (size : ℝ) := hscaledSquare
      _ ≤ ((size : ℝ) - 1) ^ 2 := hgeometry
      _ = ((size : ℝ) - 1) * ((size : ℝ) - 1) := by ring
  linarith

/-! ## The primal corner is never rank one -/

/-- **The primal transport**: when the primal corner is a nonzero multiple of one
atom matrix, every positively weighted projected tight direction lies on the
factor line.  The residual against the line is chart-fixed, pairs to zero with the
corner, and its assembly mass concentrates the label's own overlap, which the
positive multiplier then kills. -/
theorem projected_tightDir_eq_smul_of_projectedCaptured_eq_smul_atomMatrix
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {direction : Fin size → ℝ} (hdirectionUnit : direction ⬝ᵥ direction = 1)
    {lam : ℝ} (hlamNe : lam ≠ 0)
    (hfactor : projection * chartMultiplierAssembly activeSet activeWeight tightDir
      = lam • atomMatrix direction)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hpositive : 0 < activeWeight activeLabel) :
    projection *ᵥ tightDir activeLabel
      = (direction ⬝ᵥ (projection *ᵥ tightDir activeLabel)) • direction := by
  classical
  have hfixedOp : projection * (lam • atomMatrix direction) = lam • atomMatrix direction := by
    rw [← hfactor, ← Matrix.mul_assoc, hdata.isIdempotent]
  have hfixed : projection *ᵥ direction = direction :=
    mulVec_direction_eq_self_of_mul_smul_atomMatrix hdirectionUnit hlamNe hfixedOp
  set capturedRow := projection *ᵥ tightDir activeLabel with hcapturedRowDef
  set residual := capturedRow - (direction ⬝ᵥ capturedRow) • direction with hresidualDef
  have hresidualOrth : direction ⬝ᵥ residual = 0 := by
    rw [hresidualDef, dotProduct_sub, dotProduct_smul, smul_eq_mul, hdirectionUnit,
      mul_one, sub_self]
  have hresidualFixed : projection *ᵥ residual = residual := by
    rw [hresidualDef, Matrix.mulVec_sub, Matrix.mulVec_smul, hfixed, hcapturedRowDef,
      Matrix.mulVec_mulVec, hdata.isIdempotent]
  have hquadZero : residual ⬝ᵥ
      ((projection * chartMultiplierAssembly activeSet activeWeight tightDir) *ᵥ residual)
        = 0 := by
    rw [hfactor, Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul, hresidualOrth, zero_smul,
      smul_zero, dotProduct_zero]
  have hassemblyZero : residual ⬝ᵥ
      (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ residual) = 0 := by
    have hmove : residual ⬝ᵥ
        ((projection * chartMultiplierAssembly activeSet activeWeight tightDir) *ᵥ residual)
          = residual ⬝ᵥ
            (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ residual) := by
      rw [← Matrix.mulVec_mulVec]
      have hswap := dotProduct_mulVec_transpose projection residual
        (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ residual)
      rw [hdata.isSymmetric, hresidualFixed] at hswap
      exact hswap.symm
    rw [← hmove]
    exact hquadZero
  have hsumZero : ∑ label ∈ activeSet,
      activeWeight label * (tightDir label ⬝ᵥ residual) ^ 2 = 0 := by
    rw [← dotProduct_mulVec_chartMultiplierAssembly]
    exact hassemblyZero
  have hlabelZero : tightDir activeLabel ⬝ᵥ residual = 0 := by
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg fun label hlabel =>
      mul_nonneg (hdata.activeWeight_nonneg label hlabel) (sq_nonneg _)).mp
      hsumZero activeLabel hmem
    rcases mul_eq_zero.mp hterms with hweightZero | hsquareZero
    · exact absurd hweightZero (ne_of_gt hpositive)
    · exact (pow_eq_zero_iff two_ne_zero).mp hsquareZero
  have hresidualNorm : residual ⬝ᵥ residual = 0 := by
    have hpair : residual ⬝ᵥ capturedRow = 0 := by
      have hswap := dotProduct_mulVec_transpose projection residual (tightDir activeLabel)
      rw [hdata.isSymmetric, hresidualFixed] at hswap
      calc residual ⬝ᵥ capturedRow
          = residual ⬝ᵥ (projection *ᵥ tightDir activeLabel) := by rw [hcapturedRowDef]
        _ = residual ⬝ᵥ tightDir activeLabel := hswap.symm
        _ = tightDir activeLabel ⬝ᵥ residual := dotProduct_comm _ _
        _ = 0 := hlabelZero
    have hdirectionSide : residual ⬝ᵥ direction = 0 := by
      rw [dotProduct_comm]
      exact hresidualOrth
    calc residual ⬝ᵥ residual
        = residual ⬝ᵥ (capturedRow - (direction ⬝ᵥ capturedRow) • direction) := by
          rw [← hresidualDef]
      _ = residual ⬝ᵥ capturedRow
          - (direction ⬝ᵥ capturedRow) * (residual ⬝ᵥ direction) := by
          rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
      _ = 0 := by rw [hpair, hdirectionSide, mul_zero, sub_zero]
  have hresidualZero : residual = 0 := by
    funext atomIndex
    have hsumSquares : ∑ index : Fin size, residual index * residual index = 0 :=
      hresidualNorm
    have htermZero := (Finset.sum_eq_zero_iff_of_nonneg fun index _ =>
      mul_self_nonneg (residual index)).mp hsumSquares atomIndex (Finset.mem_univ atomIndex)
    exact mul_self_eq_zero.mp htermZero
  exact sub_eq_zero.mp (hresidualDef.symm.trans hresidualZero)

/-- **THE PRIMAL CAPTURED CORNER IS NEVER RANK ONE** strictly inside the window
`-1/size < value < 0`: rank one transports into collinearity of the positively
weighted projected tight directions, which the landed closing theorem forbids. -/
theorem false_of_projectedCaptured_range_finrank_le_one
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hnegative : value < 0) (hinterior : -((size : ℝ))⁻¹ < value)
    (hrange : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      (projection * chartMultiplierAssembly activeSet activeWeight tightDir))) ≤ 1) :
    False := by
  classical
  have htrace :
      Matrix.trace (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
        = value + ((size : ℝ))⁻¹ :=
    trace_projection_mul_multiplier_of_isChartStationaryData hdata
  have hlamPos : (0 : ℝ) < value + ((size : ℝ))⁻¹ := by linarith
  have hlamNe : (value + ((size : ℝ))⁻¹ : ℝ) ≠ 0 := ne_of_gt hlamPos
  have hpsd := posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata
  have hsymmetric :
      (projection * chartMultiplierAssembly activeSet activeWeight tightDir)ᵀ
        = projection * chartMultiplierAssembly activeSet activeWeight tightDir := by
    have hhermitian := hpsd.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at hhermitian
  obtain ⟨direction, hdirectionUnit, hfactor⟩ :=
    exists_unit_eq_trace_smul_atomMatrix_of_symmetric_of_range_finrank_le_one
      (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
      hsymmetric hrange (by rw [htrace]; exact hlamPos)
  rw [htrace] at hfactor
  have hfixed : projection *ᵥ direction = direction := by
    apply mulVec_direction_eq_self_of_mul_smul_atomMatrix hdirectionUnit hlamNe
    rw [← hfactor, ← Matrix.mul_assoc, hdata.isIdempotent]
  have hcollinear : ∀ activeLabel ∈ activeSet, 0 < activeWeight activeLabel →
      ∃ scale : ℝ, projection *ᵥ tightDir activeLabel = scale • direction := by
    intro activeLabel hmem hpositive
    exact ⟨direction ⬝ᵥ (projection *ᵥ tightDir activeLabel),
      projected_tightDir_eq_smul_of_projectedCaptured_eq_smul_atomMatrix hdata
        hdirectionUnit hlamNe hfactor hmem hpositive⟩
  exact false_of_projected_tightDir_collinear hdata hnegative hinterior direction hfixed
    hdirectionUnit hcollinear

/-! ## The `(6,3)` crux corollaries -/

/-- At a `(6,3)` crux no stationary datum has complement corner of rank at most
one — with NO multiplier positivity, so this reaches every multiplier support. -/
theorem SixThreeCrux.not_complementProjectedMultiplier_range_finrank_le_one
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir) :
    ¬ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      ((1 - (chartPointOfDesign crux.design).chart) *
        chartMultiplierAssembly activeSet activeWeight tightDir))) ≤ 1 := by
  intro hrange
  exact false_of_complementCaptured_range_finrank_le_one hdata
    crux.hasNegativeChartValue (by norm_num) hrange

/-- At a `(6,3)` crux no stationary datum has primal corner of rank at most one —
again with no multiplier positivity; the strict window comes from the argmax
field. -/
theorem SixThreeCrux.not_projectedMultiplier_range_finrank_le_one
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir) :
    ¬ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      ((chartPointOfDesign crux.design).chart *
        chartMultiplierAssembly activeSet activeWeight tightDir))) ≤ 1 := by
  intro hrange
  exact false_of_projectedCaptured_range_finrank_le_one hdata
    crux.hasNegativeChartValue
    (neg_inv_size_lt_value_of_isChartStationaryData crux.design rfl
      crux.isChartArgmaxValue hdata) hrange

end Gtz

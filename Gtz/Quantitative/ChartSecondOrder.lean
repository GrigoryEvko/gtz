/-
# Second-order data at a chart minimiser

Everything the campaign has extracted from `Gtz.SixThreeCrux.isChartMinimiser` so
far is FIRST order: stationarity, the argmax family, the multiplier bundles.  A
crux is a GLOBAL minimiser, so every feasible curve through it carries a
second-order inequality too, and this file extracts the weight-slice half of that
family.

## Why the weight slice, and why the mechanism is margin-free

`Gtz.chartDomain` is a PRODUCT: at a fixed chart the weights range over the whole
simplex, and `Gtz.chartPointGap` is AFFINE there.  So on the weight slice the
perturbed block is `M - step * D` with `M := W[C] - value * 1` positive
semidefinite and `D` the restricted diagonal of the direction.

`not_posSemidef_sub_smul_of_mulVec_ne_zero` is the whole mechanism.  If the
first-order effect vanishes (`u . D u = 0` at a tight vector `u`) but `D` MOVES the
tight vector (`D *v u <> 0`), then `M - step * D` fails to be positive semidefinite
for EVERY nonzero `step` -- both signs, every size, no smallness hypothesis.  The
block value strictly drops on both sides.  That is exact algebraic non-definiteness
rather than a Taylor estimate, so no inequality carrying slack appears anywhere in
the chain; and the index consequence is a comparison between INTEGERS.

`lambdaMinMat_sub_smul_lt_of_lt` supplies the other blocks by the Rayleigh bound
alone: an INACTIVE block sits strictly below the value already, and it stays there as
long as the step does not eat its own gap -- an explicit, finite family of strict
inequalities, not a limit.  So `chartObjective_lt_of_perturbedWeight` needs no
continuity anywhere, and `SixThreeCrux.exists_tight_annihilated_of_flatDirection` reads
the resulting contradiction back as a structural fact about a crux.

## What is here, and what is not

* THE ESCAPE, at the level of one matrix and then of a whole chart point.
* THE FLAT-DIRECTION COUNT.  Fewer active blocks than atoms leave a nonzero
  weight direction, summing to zero, flat at all of them
  (`exists_flatDirection_of_card_add_one_lt`).
* THE DERIVED SECOND-ORDER FACT AT A CRUX.  Every flat direction has an active
  block whose tight vector it ANNIHILATES -- not merely fails to move at first
  order.  This is the weight-slice second-order condition, mechanized.
* THE TIE-RIGIDITY CERTIFICATE.  `eq_zero_of_flatDirection_of_span_top`: when the
  first-order functionals span, there is no flat direction at all, so the
  second-order test is vacuous and the point is weight-slice rigid.  The check is
  a rank computation on the eigen-square rows.

NOT here, and both are recorded rather than hidden.  (1) The nine Grassmannian
directions: the projection variety contains no line, so the chart directions carry
curvature that this file never touches, and every statement below is about the
weight slice alone.  (2) An unconditional floor on the size of the argmax family.
Turning the derived fact into `5 <= |A|` needs, on top of what is here, that a real
vector space is not a finite union of proper subspaces, plus the support analysis
of the tight vectors.  The shipped floor remains
`Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily`.

THE MECHANISM IS FIELD-BLIND, and this is orientation prose, not a theorem of this
file.  Every step runs verbatim over `C` with `u u^*` in place of `u u^T`, so
nothing here can close the cell alone; it must be combined with a realness
consumer.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Quantitative.ChartDisjointBlockExclusion
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.SixThreeCrux
import Gtz.Reduction.ChartAttainment
import Gtz.Reduction.ChartAttainmentWeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The escape, at the level of one matrix -/

section OneMatrix

variable {dim : ℕ}

/-- **A POSITIVE-SEMIDEFINITE MATRIX ANNIHILATES ITS ISOTROPIC VECTORS.**  The
square-root-free argument: the quadratic form along `vec + scale * probe` is
`2 * scale * linear + scale ^ 2 * quad` with `quad` nonnegative, so a nonzero linear
coefficient is contradicted at `scale = -linear / (quad + 1)`. -/
theorem mulVec_eq_zero_of_posSemidef_of_dotProduct_zero
    {gapMatrix : Matrix (Fin dim) (Fin dim) ℝ} (hposSemidef : gapMatrix.PosSemidef)
    {vec : Fin dim → ℝ} (hisotropic : vec ⬝ᵥ (gapMatrix *ᵥ vec) = 0) :
    gapMatrix *ᵥ vec = 0 := by
  have hsymmetric : gapMatrixᵀ = gapMatrix := hposSemidef.isHermitian.eq
  have hquad : ∀ probe : Fin dim → ℝ, 0 ≤ probe ⬝ᵥ (gapMatrix *ᵥ probe) := by
    intro probe
    have hraw := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposSemidef).2 probe
    rwa [star_trivial] at hraw
  have hswap : ∀ leftVec rightVec : Fin dim → ℝ,
      leftVec ⬝ᵥ (gapMatrix *ᵥ rightVec) = rightVec ⬝ᵥ (gapMatrix *ᵥ leftVec) := by
    intro leftVec rightVec
    have htranspose := Gtz.dotProduct_mulVec_transpose gapMatrix leftVec rightVec
    rw [hsymmetric] at htranspose
    rw [← htranspose, dotProduct_comm]
  have hcross : ∀ probe : Fin dim → ℝ, probe ⬝ᵥ (gapMatrix *ᵥ vec) = 0 := by
    intro probe
    set linearPart : ℝ := probe ⬝ᵥ (gapMatrix *ᵥ vec) with hlinearPart
    set quadPart : ℝ := probe ⬝ᵥ (gapMatrix *ᵥ probe) with hquadPart
    have hquadNonneg : 0 ≤ quadPart := hquad probe
    have hdenomPos : (0 : ℝ) < quadPart + 1 := by linarith
    have hexpand : ∀ scale : ℝ,
        (vec + scale • probe) ⬝ᵥ (gapMatrix *ᵥ (vec + scale • probe))
          = 2 * scale * linearPart + scale ^ 2 * quadPart := by
      intro scale
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        dotProduct_add, smul_dotProduct, dotProduct_smul, smul_dotProduct,
        dotProduct_smul, hisotropic, hswap vec probe, hlinearPart, hquadPart]
      ring
    have hstep := hquad (vec + (-(linearPart / (quadPart + 1))) • probe)
    rw [hexpand] at hstep
    have hcollect : 2 * (-(linearPart / (quadPart + 1))) * linearPart
        + (-(linearPart / (quadPart + 1))) ^ 2 * quadPart
        = -(linearPart ^ 2 * (quadPart + 2)) / (quadPart + 1) ^ 2 := by
      field_simp
      ring
    rw [hcollect, le_div_iff₀ (by positivity)] at hstep
    nlinarith [sq_nonneg linearPart, hquadNonneg, hstep]
  exact Gtz.eq_zero_of_dotProduct_self_eq_zero (hcross (gapMatrix *ᵥ vec))

/-- **THE ESCAPE BRICK.**  `tightVec` lies in the kernel of `tightMatrix`, the
perturbation has vanishing quadratic form there -- the first-order effect along the
weight direction is zero -- but it does not fix the kernel.  Then
`tightMatrix - step * perturbation` fails to be positive semidefinite for EVERY
nonzero `step`: the block value strictly drops on BOTH sides, with no margin and no
smallness hypothesis.  Positive semidefiniteness of `tightMatrix` is not needed. -/
theorem not_posSemidef_sub_smul_of_mulVec_ne_zero
    {tightMatrix perturbation : Matrix (Fin dim) (Fin dim) ℝ} {tightVec : Fin dim → ℝ}
    (hkernel : tightMatrix *ᵥ tightVec = 0)
    (hFirstOrder : tightVec ⬝ᵥ (perturbation *ᵥ tightVec) = 0)
    (hMoves : perturbation *ᵥ tightVec ≠ 0) {step : ℝ} (hstep : step ≠ 0) :
    ¬ (tightMatrix - step • perturbation).PosSemidef := by
  intro hposSemidef
  have hisotropic :
      tightVec ⬝ᵥ ((tightMatrix - step • perturbation) *ᵥ tightVec) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, hkernel,
      hFirstOrder]
    simp
  have hzero := mulVec_eq_zero_of_posSemidef_of_dotProduct_zero hposSemidef hisotropic
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hkernel, zero_sub, neg_eq_zero,
    smul_eq_zero] at hzero
  exact hMoves (hzero.resolve_left hstep)

/-- **THE ESCAPE BRICK IN EIGENVALUE FORM.**  With `blockValue` an eigenvalue of
`block` at `tightVec`, a direction of zero first-order effect that nevertheless moves
the eigenvector strictly LOWERS the block's smallest eigenvalue, on both sides and at
every step size. -/
theorem lambdaMinMat_lt_of_mulVec_ne_zero [Nonempty (Fin dim)]
    {block perturbation : Matrix (Fin dim) (Fin dim) ℝ} {blockValue : ℝ}
    {tightVec : Fin dim → ℝ}
    (hkernel : (block - blockValue • (1 : Matrix (Fin dim) (Fin dim) ℝ)) *ᵥ tightVec = 0)
    (hFirstOrder : tightVec ⬝ᵥ (perturbation *ᵥ tightVec) = 0)
    (hMoves : perturbation *ᵥ tightVec ≠ 0) (hblockSymmetric : blockᵀ = block)
    (hperturbSymmetric : perturbationᵀ = perturbation) {step : ℝ} (hstep : step ≠ 0) :
    lambdaMinMat (block - step • perturbation) < blockValue := by
  by_contra hcontra
  have hle : blockValue ≤ lambdaMinMat (block - step • perturbation) := not_lt.mp hcontra
  have hshift : (block - step • perturbation)
      - blockValue • (1 : Matrix (Fin dim) (Fin dim) ℝ)
      = (block - blockValue • (1 : Matrix (Fin dim) (Fin dim) ℝ)) - step • perturbation := by
    abel
  have hsymmetric : (block - step • perturbation)ᵀ = block - step • perturbation := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hblockSymmetric, hperturbSymmetric]
  have hposSemidef :=
    (le_lambdaMinMat_iff_posSemidef_sub_smul_one (block - step • perturbation) hsymmetric
      blockValue).mp hle
  rw [hshift] at hposSemidef
  exact not_posSemidef_sub_smul_of_mulVec_ne_zero hkernel hFirstOrder hMoves hstep hposSemidef

/-- **THE RAYLEIGH BOUND AT A UNIT VECTOR.**  The smallest eigenvalue never exceeds
any quadratic-form value on the unit sphere. -/
theorem lambdaMinMat_le_dotProduct_of_unit [Nonempty (Fin dim)]
    (block : Matrix (Fin dim) (Fin dim) ℝ) {probe : Fin dim → ℝ} (hunit : probe ⬝ᵥ probe = 1) :
    lambdaMinMat block ≤ probe ⬝ᵥ (block *ᵥ probe) := by
  have hbound := lambdaMinMat_mul_dotProduct_self_le block probe
  rwa [hunit, mul_one] at hbound

/-- **A FLAT DIRECTION CANNOT RAISE A BLOCK.**  Zero first-order effect at the block's
own tight vector already caps the perturbed value by the unperturbed one -- Rayleigh
alone, no definiteness and no step-size bound.  This is what carries the INACTIVE
blocks through the escape. -/
theorem lambdaMinMat_sub_smul_le_of_dotProduct_zero [Nonempty (Fin dim)]
    {block perturbation : Matrix (Fin dim) (Fin dim) ℝ} {blockValue : ℝ}
    {tightVec : Fin dim → ℝ} (hunit : tightVec ⬝ᵥ tightVec = 1)
    (hEigen : block *ᵥ tightVec = blockValue • tightVec)
    (hFirstOrder : tightVec ⬝ᵥ (perturbation *ᵥ tightVec) = 0) (step : ℝ) :
    lambdaMinMat (block - step • perturbation) ≤ blockValue := by
  have hvalue : tightVec ⬝ᵥ ((block - step • perturbation) *ᵥ tightVec) = blockValue := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, hEigen,
      hFirstOrder, dotProduct_smul, hunit]
    simp
  calc lambdaMinMat (block - step • perturbation)
      ≤ tightVec ⬝ᵥ ((block - step • perturbation) *ᵥ tightVec) :=
        lambdaMinMat_le_dotProduct_of_unit _ hunit
    _ = blockValue := hvalue

/-- **THE GENERAL RAYLEIGH STEP BOUND.**  Without flatness the tight vector still caps
the perturbed value by `blockValue - step * firstOrder`, so an INACTIVE block stays
below any level it already sits under as long as the step does not eat its whole gap.
The hypothesis is exactly that condition, written out; when the direction happens to be
flat at the block it reduces to `blockValue < level`, which inactivity already gives. -/
theorem lambdaMinMat_sub_smul_lt_of_lt [Nonempty (Fin dim)]
    {block perturbation : Matrix (Fin dim) (Fin dim) ℝ} {blockValue level step : ℝ}
    {tightVec : Fin dim → ℝ} (hunit : tightVec ⬝ᵥ tightVec = 1)
    (hEigen : block *ᵥ tightVec = blockValue • tightVec)
    (hstepSmall :
      blockValue - level < step * (tightVec ⬝ᵥ (perturbation *ᵥ tightVec))) :
    lambdaMinMat (block - step • perturbation) < level := by
  have hvalue : tightVec ⬝ᵥ ((block - step • perturbation) *ᵥ tightVec)
      = blockValue - step * (tightVec ⬝ᵥ (perturbation *ᵥ tightVec)) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, hEigen,
      dotProduct_smul, hunit, smul_eq_mul, smul_eq_mul, mul_one]
  have hbound := lambdaMinMat_le_dotProduct_of_unit (block - step • perturbation) hunit
  rw [hvalue] at hbound
  linarith

end OneMatrix

/-! ## The index step, and the flat-direction count -/

open Module in
/-- **THE SPAN BOUND.**  A family whose span contains `witnessCount` linearly
independent vectors has at least that many members.  The index step: an inequality
between INTEGERS, so nothing here can carry slack. -/
theorem le_card_of_linearIndependent_mem_span {ambient count witnessCount : ℕ}
    (functional : Fin count → (Fin ambient → ℝ)) (witness : Fin witnessCount → (Fin ambient → ℝ))
    (hindependent : LinearIndependent ℝ witness)
    (hmem : ∀ label, witness label ∈ Submodule.span ℝ (Set.range functional)) :
    witnessCount ≤ count := by
  have hle : Submodule.span ℝ (Set.range witness) ≤
      Submodule.span ℝ (Set.range functional) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hmem)
  have hwitnessRank : finrank ℝ (Submodule.span ℝ (Set.range witness)) = witnessCount := by
    rw [finrank_span_eq_card hindependent, Fintype.card_fin]
  have hmono := Submodule.finrank_mono hle
  have hcount : finrank ℝ (Submodule.span ℝ (Set.range functional)) ≤ count := by
    have hcard := finrank_span_le_card (R := ℝ) (Set.range functional)
    have himage : (Finset.image functional Finset.univ).card ≤ count := by
      have hbound := Finset.card_image_le (s := (Finset.univ : Finset (Fin count)))
        (f := functional)
      simpa using hbound
    simp only [Set.toFinset_range] at hcard
    omega
  omega

/-- **TOO FEW FUNCTIONALS LEAVE A COMMON ANNIHILATOR.**  Rank-nullity in the form the
escape consumes. -/
theorem exists_ne_zero_forall_dotProduct_eq_zero_of_card_lt {ambient count : ℕ}
    (functional : Fin count → (Fin ambient → ℝ)) (hcount : count < ambient) :
    ∃ direction : Fin ambient → ℝ, direction ≠ 0
      ∧ ∀ label, functional label ⬝ᵥ direction = 0 := by
  set pairingMap : (Fin ambient → ℝ) →ₗ[ℝ] (Fin count → ℝ) :=
    { toFun := fun direction label => functional label ⬝ᵥ direction
      map_add' := fun leftDirection rightDirection => by
        funext label; simp [dotProduct_add]
      map_smul' := fun scale direction => by
        funext label; simp [dotProduct_smul] } with hpairingMap
  have hnotInjective : ¬ Function.Injective pairingMap := by
    intro hinjective
    have hbound := LinearMap.finrank_le_finrank_of_injective hinjective
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_fin, Fintype.card_fin] at hbound
    omega
  rw [← LinearMap.ker_eq_bot] at hnotInjective
  obtain ⟨direction, hmem, hnonzero⟩ := (Submodule.ne_bot_iff _).mp hnotInjective
  exact ⟨direction, hnonzero, fun label => congrFun (LinearMap.mem_ker.mp hmem) label⟩

/-- **THE FLAT-DIRECTION COUNT.**  When the number of first-order functionals falls
one short of the atom count, there is a nonzero weight direction that sums to zero --
so it stays inside the simplex -- and is flat at every one of them.  The all-ones
vector is what consumes the extra dimension. -/
theorem exists_flatDirection_of_card_add_one_lt {ambient count : ℕ}
    (functional : Fin count → (Fin ambient → ℝ)) (hcount : count + 1 < ambient) :
    ∃ direction : Fin ambient → ℝ, direction ≠ 0 ∧ (∑ atomIndex, direction atomIndex = 0)
      ∧ ∀ label, functional label ⬝ᵥ direction = 0 := by
  obtain ⟨direction, hnonzero, hflat⟩ :=
    exists_ne_zero_forall_dotProduct_eq_zero_of_card_lt
      (Fin.cons (fun _ => (1 : ℝ)) functional : Fin (count + 1) → (Fin ambient → ℝ))
      (by omega)
  refine ⟨direction, hnonzero, ?_, fun label => ?_⟩
  · have hhead := hflat 0
    rw [Fin.cons_zero] at hhead
    simpa only [dotProduct, one_mul] using hhead
  · have htail := hflat label.succ
    rwa [Fin.cons_succ] at htail

/-! ## The weight slice of the chart domain -/

section WeightSlice

variable {size rank : ℕ}

/-- Moving the weights by `step * direction` subtracts `step` times the direction's
diagonal from the chart gap.  The whole reason the weight slice is the tractable one:
the gap is AFFINE there. -/
theorem chartPointGap_perturbedWeight (chart : Matrix (Fin size) (Fin size) ℝ)
    (weight direction : Fin size → ℝ) (step : ℝ) :
    chart - Matrix.diagonal (weight + step • direction)
      = (chart - Matrix.diagonal weight) - step • Matrix.diagonal direction := by
  ext rowIndex colIndex
  rcases eq_or_ne rowIndex colIndex with rfl | hoffDiagonal
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hoffDiagonal,
      smul_eq_mul, mul_zero, sub_zero]

/-- **THE PERTURBED CHART POINT.**  Same chart, weights moved along a direction that
sums to zero and stays nonnegative -- so the point stays in the closed chart domain and
`Gtz.chartObjective` may be compared at it. -/
def perturbedWeightChartPoint (point : ChartPoint size rank) (direction : Fin size → ℝ)
    (step : ℝ) (hnonneg : ∀ atomIndex, 0 ≤ point.weight atomIndex + step * direction atomIndex)
    (hsum : ∑ atomIndex, direction atomIndex = 0) : ChartPoint size rank where
  chart := point.chart
  weight := point.weight + step • direction
  isSymmetric := point.isSymmetric
  isIdempotent := point.isIdempotent
  hasTraceRank := point.hasTraceRank
  weight_nonneg := hnonneg
  weight_sum_one := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero, point.weight_sum_one]

/-- The perturbed point's block values, written out as a perturbation of the original
block by the direction's restricted diagonal. -/
theorem chartBlockValue_perturbedWeightChartPoint [Nonempty (Fin rank)]
    (point : ChartPoint size rank) (direction : Fin size → ℝ) (step : ℝ)
    (hnonneg : ∀ atomIndex, 0 ≤ point.weight atomIndex + step * direction atomIndex)
    (hsum : ∑ atomIndex, direction atomIndex = 0)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) :
    chartBlockValue rank
        ((perturbedWeightChartPoint point direction step hnonneg hsum).chart,
          (perturbedWeightChartPoint point direction step hnonneg hsum).weight) selected
      = lambdaMinMat
          ((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
              (selected.orderEmbOfFin hcard)
            - step • (Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
              (selected.orderEmbOfFin hcard)) := by
  have hgap : chartGapRaw
      ((perturbedWeightChartPoint point direction step hnonneg hsum).chart,
        (perturbedWeightChartPoint point direction step hnonneg hsum).weight)
      = chartPointGap point - step • Matrix.diagonal direction := by
    rw [chartGapRaw_chartConfig, chartPointGap, chartPointGap]
    exact chartPointGap_perturbedWeight point.chart point.weight direction step
  rw [chartBlockValue, dif_pos hcard, hgap]
  congr 1

/-- The restricted diagonal is symmetric, so it is a legitimate perturbation for the
escape brick. -/
theorem transpose_submatrix_diagonal (direction : Fin size → ℝ)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) :
    ((Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard))ᵀ
      = (Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard) := by
  rw [Matrix.transpose_submatrix, Matrix.diagonal_transpose]

/-- **THE OBJECTIVE DROPS WHEN EVERY BLOCK DOES.**  The objective is a finite `sup'`
over the rank-subsets, so it falls below a level exactly when all of them do. -/
theorem chartObjective_lt_of_forall_chartBlockValue_lt [Nonempty (Fin rank)]
    (point : ChartPoint size rank) (level : ℝ)
    (hblocks : ∀ selected : Finset (Fin size), selected.card = rank →
      chartBlockValue rank
        ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) selected
        < level) :
    chartObjective point < level := by
  rw [chartObjective, chartObjectiveRaw, Finset.sup'_lt_iff]
  intro selected hmem
  exact hblocks selected ((mem_chartCandidates_iff size rank selected).mp hmem)

end WeightSlice

/-! ## The escape at a chart minimiser

The two suppliers meet here.  A direction FLAT at every block cannot raise any of
them; at the ACTIVE blocks, where the value is attained, moving the tight vector
makes the drop STRICT.  So if the direction moves every active tight vector the
objective strictly falls, and minimality is contradicted -- at every nonzero step
size and on both sides. -/

section Escape

variable {size rank : ℕ} [Nonempty (Fin rank)]

/-- **THE WEIGHT-SLICE ESCAPE.**  A flat direction that moves the tight vector of every
argmax block strictly lowers the chart objective.  No continuity, no step-size bound:
the active drop is exact algebraic non-definiteness and the inactive blocks are held by
Rayleigh. -/
theorem chartObjective_lt_of_perturbedWeight (point : ChartPoint size rank)
    (direction : Fin size → ℝ) {step : ℝ} (hstep : step ≠ 0)
    (hnonneg : ∀ atomIndex, 0 ≤ point.weight atomIndex + step * direction atomIndex)
    (hsum : ∑ atomIndex, direction atomIndex = 0)
    (tightVec : Finset (Fin size) → (Fin rank → ℝ))
    (hunit : ∀ selected : Finset (Fin size), selected.card = rank →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin size)) (hcard : selected.card = rank),
      (chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue rank
            ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ))
            selected • tightVec selected)
    (hflat : ∀ (selected : Finset (Fin size)) (hcard : selected.card = rank),
      selected ∈ chartArgmaxFamily point →
        tightVec selected ⬝ᵥ ((Matrix.diagonal direction).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
            *ᵥ tightVec selected) = 0)
    (hmoves : ∀ (selected : Finset (Fin size)) (hcard : selected.card = rank),
      selected ∈ chartArgmaxFamily point →
        (Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard) *ᵥ tightVec selected ≠ 0)
    (hstepSmall : ∀ (selected : Finset (Fin size)) (hcard : selected.card = rank),
      selected ∉ chartArgmaxFamily point →
        chartBlockValue rank
            ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ))
            selected - chartObjective point
          < step * (tightVec selected ⬝ᵥ ((Matrix.diagonal direction).submatrix
              (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
                *ᵥ tightVec selected))) :
    chartObjective (perturbedWeightChartPoint point direction step hnonneg hsum)
      < chartObjective point := by
  refine chartObjective_lt_of_forall_chartBlockValue_lt _ _ fun selected hcard => ?_
  rw [chartBlockValue_perturbedWeightChartPoint point direction step hnonneg hsum hcard]
  set blockValue : ℝ := chartBlockValue rank
    ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) selected
    with hblockValue
  by_cases hactive : selected ∈ chartArgmaxFamily point
  · -- ACTIVE: the value is attained here, and moving the tight vector drops it strictly.
    have hattained : blockValue ≤ chartObjective point := by
      rw [hblockValue, chartBlockValue, dif_pos hcard, chartObjective, chartObjectiveRaw]
      refine Finset.le_sup' (fun candidate => chartBlockValue rank _ candidate)
        ((mem_chartCandidates_iff size rank selected).mpr hcard) |>.trans_eq' ?_
      rw [chartBlockValue, dif_pos hcard]
    have hkernel : ((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard)
        - blockValue • (1 : Matrix (Fin rank) (Fin rank) ℝ)) *ᵥ tightVec selected = 0 := by
      rw [Matrix.sub_mulVec, hEigen selected hcard, Matrix.smul_mulVec, Matrix.one_mulVec,
        sub_self]
    have hdrop := lambdaMinMat_lt_of_mulVec_ne_zero hkernel (hflat selected hcard hactive)
      (hmoves selected hcard hactive)
      (by
        rw [Matrix.transpose_submatrix, chartPointGap_transpose])
      (transpose_submatrix_diagonal direction hcard) hstep
    exact lt_of_lt_of_le hdrop hattained
  · -- INACTIVE: the block was already strictly below, and the step does not eat its gap.
    exact lambdaMinMat_sub_smul_lt_of_lt (hunit selected hcard) (hEigen selected hcard)
      (hstepSmall selected hcard hactive)

end Escape

/-! ## Two facts about the blocks the escape moves

The escape acts on the principal blocks of `Gtz.chartStationaryGap`, so it is worth
recording in that vocabulary what the crux fields say about them.  All-heaviness is
exactly a strictly positive gap DIAGONAL, and at a crux that plus a negative value
forces the first characteristic coefficient of every shifted block to be strictly
positive -- so no block can fail definiteness through its trace. -/

/-- **ALL-HEAVINESS IS A STRICTLY POSITIVE GAP DIAGONAL.**  `L_c > 1` says exactly
`P_cc > t_c`, at every size and rank. -/
theorem pos_chartStationaryGap_diagonal_of_allHeavy {size rank : ℕ}
    (design : WeightedDesign size rank) (hallHeavy : AllHeavy design) (atomIndex : Fin size) :
    0 < chartStationaryGap (projectionOfDesign design) design.weight atomIndex atomIndex := by
  have hweight : 0 < design.weight atomIndex := design.weight_pos atomIndex
  have hleverage : 1 < leverageOf (design.atom atomIndex) := hallHeavy atomIndex
  have hdiagonal :
      chartStationaryGap (projectionOfDesign design) design.weight atomIndex atomIndex
        = design.weight atomIndex * leverageOf (design.atom atomIndex)
          - design.weight atomIndex := by
    rw [chartStationaryGap, Matrix.sub_apply, projectionOfDesign_diagonal,
      Matrix.diagonal_apply_eq]
  rw [hdiagonal]
  nlinarith [hweight, hleverage]

/-- **THE FIRST CHARACTERISTIC COEFFICIENT IS STRICTLY POSITIVE AT EVERY TRIPLE OF A
CRUX.**  The trace of the shifted block `W[C] - value * 1` is a sum of strictly
positive gap diagonals minus three times a strictly negative value, so definiteness
can only fail through the second or third coefficient -- two branches at each of the
twenty triples rather than three. -/
theorem SixThreeCrux.pos_firstCharacteristicCoefficient (crux : SixThreeCrux)
    (triple : Finset (Fin 6)) (hcard : triple.card = 3) :
    0 < (∑ atomIndex ∈ triple,
          chartStationaryGap (projectionOfDesign crux.design) crux.design.weight
            atomIndex atomIndex)
        - 3 * chartObjective (chartPointOfDesign crux.design) := by
  have hvalue : chartObjective (chartPointOfDesign crux.design) < 0 :=
    crux.hasNegativeChartValue
  have hsum : 0 < ∑ atomIndex ∈ triple,
      chartStationaryGap (projectionOfDesign crux.design) crux.design.weight
        atomIndex atomIndex := by
    refine Finset.sum_pos (fun atomIndex _ =>
      pos_chartStationaryGap_diagonal_of_allHeavy crux.design crux.isAllHeavy atomIndex) ?_
    exact Finset.card_pos.mp (by omega)
  linarith

/-! ## The derived second-order fact at a `(6,3)` crux -/

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- **THE WEIGHT-SLICE SECOND-ORDER CONDITION AT A CRUX.**  Pick a unit tight vector at
every rank-subset.  Then no feasible weight direction can be flat at every ARGMAX block
AND move every active tight vector: some argmax block has its tight vector ANNIHILATED
by the direction's restricted diagonal -- vanishing at first order is not enough, the
direction must kill the whole eigenvector.

This is the first second-order consequence of `isChartMinimiser` in the tree.  Its ACTIVE
half is margin-free: the drop it rules out is exact algebraic non-definiteness at every
step size and on both sides, not an estimate.  The inactive half is the explicit step
condition `hstepSmall`, which asks only that the step not eat an inactive block's own
strictly positive gap -- a finite family of strict inequalities, satisfied for every
small enough step, but SUPPLIED here rather than derived. -/
theorem exists_tight_annihilated_of_flatDirection (direction : Fin 6 → ℝ) {step : ℝ}
    (hstep : step ≠ 0)
    (hnonneg : ∀ atomIndex,
      0 ≤ (chartPointOfDesign crux.design).weight atomIndex + step * direction atomIndex)
    (hsum : ∑ atomIndex, direction atomIndex = 0)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hflat : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design) →
        tightVec selected ⬝ᵥ ((Matrix.diagonal direction).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
            *ᵥ tightVec selected) = 0)
    (hstepSmall : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      selected ∉ chartArgmaxFamily (chartPointOfDesign crux.design) →
        chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) : (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ))
            selected - chartObjective (chartPointOfDesign crux.design)
          < step * (tightVec selected ⬝ᵥ ((Matrix.diagonal direction).submatrix
              (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
                *ᵥ tightVec selected))) :
    ∃ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
        ∧ (Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
            (selected.orderEmbOfFin hcard) *ᵥ tightVec selected = 0 := by
  by_contra hcontra
  push Not at hcontra
  have hmoves : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design) →
        (Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard) *ᵥ tightVec selected ≠ 0 :=
    fun selected hcard hactive => hcontra selected hcard hactive
  have hdrop := chartObjective_lt_of_perturbedWeight (chartPointOfDesign crux.design)
    direction hstep hnonneg hsum tightVec hunit hEigen hflat hmoves hstepSmall
  exact absurd (crux.isChartMinimiser _) (not_le.mpr hdrop)

end SixThreeCrux

/-! ## The tie-rigidity certificate

Route C's obligation in the weight directions.  The certificate is a RANK check on
the first-order functionals: when they span, no flat direction exists at all, the
second-order test above is vacuous and the point is weight-slice rigid.  When they
fail to span the flat directions are exactly the annihilator, and
`exists_flatDirection_of_card_add_one_lt` produces one from the member count alone. -/

/-- **THE RIGIDITY CERTIFICATE.**  Spanning first-order functionals leave no flat
direction: the only direction they all annihilate is zero. -/
theorem eq_zero_of_flatDirection_of_span_top {ambient count : ℕ}
    (functional : Fin count → (Fin ambient → ℝ))
    (hspan : Submodule.span ℝ (Set.range functional) = ⊤)
    {direction : Fin ambient → ℝ} (hflat : ∀ label, functional label ⬝ᵥ direction = 0) :
    direction = 0 := by
  have hall : ∀ probe : Fin ambient → ℝ, probe ⬝ᵥ direction = 0 := by
    intro probe
    have hmem : probe ∈ Submodule.span ℝ (Set.range functional) := by
      rw [hspan]; exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
    · rintro generator ⟨label, rfl⟩
      exact hflat label
    · exact zero_dotProduct direction
    · intro leftProbe rightProbe _ _ hleft hright
      rw [add_dotProduct, hleft, hright, add_zero]
    · intro scale innerProbe _ hinner
      rw [smul_dotProduct, hinner, smul_eq_mul, mul_zero]
  exact Gtz.eq_zero_of_dotProduct_self_eq_zero (hall direction)

/-- **THE CERTIFICATE'S CONTRAPOSITIVE, IN THE FORM A CENSUS SUPPLIES IT.**  Enough
functionals to span is a necessary condition for rigidity, and the atom count is the
threshold: at or below `ambient - 2` members a flat direction always exists. -/
theorem span_ne_top_of_card_add_one_lt {ambient count : ℕ}
    (functional : Fin count → (Fin ambient → ℝ)) (hcount : count + 1 < ambient) :
    Submodule.span ℝ (Set.range functional) ≠ ⊤ := by
  intro hspan
  obtain ⟨direction, hnonzero, _, hflat⟩ :=
    exists_flatDirection_of_card_add_one_lt functional hcount
  exact hnonzero (eq_zero_of_flatDirection_of_span_top functional hspan hflat)

end Gtz

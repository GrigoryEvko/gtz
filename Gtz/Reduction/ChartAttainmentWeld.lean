/-
# The weld: the chart minimiser CARRIES the first-order system

Two layers of this repository were disjoint before this file.  `Gtz.chartObjective` --
defined and shown attained in `Gtz.Reduction.ChartAttainment` -- occurred nowhere else,
and `Gtz.HasChartDominatingSubsetAtValue` -- the minimality hypothesis every theorem of
`Gtz.Quantitative.ChartDescentFromMinimality` consumes -- occurred nowhere but that file,
where it is only ever consumed and never produced.  The objective was attained and the
descent calculus was proved, and neither could speak to the other.  This file is the
weld.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

1. **The dictionary at a general value.**  `chartBlockDominatesAtValue_of_le_chartBlockValue`
   is the general-value twin of the shipped `Gtz.zero_le_chartBlockValue_iff_chartDominates`;
   it is what lets a `Gtz.lambdaMinMat` objective speak to a layer that never mentions an
   eigenvalue.

2. **The weld itself.**  `hasChartDominatingSubsetAtValue_of_isMin`: a global minimiser of
   the chart objective over the closed chart domain satisfies, verbatim, the minimality
   hypothesis of the descent layer.

3. **The inactive side condition is free.**  `isChartInactiveStrict_chartArgmaxFamily`:
   the objective is an infimum, so a block strictly below it already exhibits a probe.  No
   attainment and no spectral theorem.  The only previously shipped inhabitant of
   `Gtz.IsChartInactiveStrict` was the single `(4,3)` witness
   `Gtz.chartTetraProjection_isChartInactiveStrict`, proved by `decide`.

4. **The spectral leg.**  `exists_isChartTightDirection_of_mem_chartArgmaxFamily`
   discharges `hexistsTight`, which `Gtz.Quantitative.ChartDescentFromMinimality`'s own
   header names as "NOT free -- producing a tight eigenvector at a block where
   `lambda_min(W[C])` EQUALS `value` is the spectral theorem, and this file does not supply
   it".  Supplied here from Mathlib's Rayleigh theory, transported along
   `Gtz.selectionInjection`.

   With it, the STRONG bundle `Gtz.IsChartStrongStationaryData`, the weak bundle
   `Gtz.IsChartStationaryData` and `Gtz.IsChartArgmaxValue` all follow from interiority
   plus minimality ALONE.

5. **Design-side attainment on the collared class**, the only design-side minimiser in the
   tree: `Gtz.Design.CollaredCompact` ships compactness but no minimiser.

## NOT PROVED here.  Two honest defects, and one warning

No cell is closed.  The design-side bundle `Gtz.IsQuadricStationaryData` is still never
derived from minimality anywhere: only the CHART-side bundle is.

The design-side minimiser of section G minimises over a WEIGHT-FLOORED comparison class,
so it is not a global minimiser over all designs and the floor may be active and
contribute spurious multipliers; and it carries no first-order data, because no
design-side descent calculus exists.

WARNING, load-bearing.  `exists_collared_allHeavy_minimiser_sevenThree` here and
`Gtz.exists_allHeavy_minimiser_sevenThree` in `Gtz.Reduction.AllHeavyMinimiser` both
produce an all-heavy `(7,3)` minimising counterexample, but they minimise DIFFERENT
objectives -- the DESIGN margin and the CHART objective respectively.
`Gtz.Reduction.CompactnessReduction` records that the two share their threshold (that is
`Gtz.dominates_iff_chartDominates`) but NOT their minimisers, because the congruence
`diagonal (sqrt t_C)` relating them rescales non-uniformly.  The two designs are not the
same design and must not be identified.

## Provenance

One scratch file of the July 2026 attainment run.  Two of its declarations were dropped as
already shipped: a support-restriction transport duplicating
`Gtz.dotProduct_self_pick_eq_of_support`, and an all-heaviness lemma carrying a redundant
weak-heaviness hypothesis, superseded by `Gtz.allHeavy_of_forall_not_dominates`.
-/
import Mathlib
import Gtz.Design.CollaredCompact
import Gtz.Quantitative.ChartDescentFromMinimality
import Gtz.Quantitative.ElementaryValueFloor
import Gtz.Quantitative.MarginContinuity
import Gtz.Reduction.AllHeavyMinimiser
import Gtz.Reduction.ChartAttainment
import Gtz.Reduction.Deflation
import Gtz.Reduction.ExchangeInvariant
import Gtz.Reduction.Reductions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The ambient/submatrix dictionary at a general value -/

/-- **The block dictionary at a general value.**  `Gtz.chartBlockValue` being at least
`value` is exactly the stationarity layer's ambient `Gtz.ChartBlockDominatesAtValue`.  This
is the general-value twin of the shipped `Gtz.zero_le_chartBlockValue_iff_chartDominates`,
and it is what lets a `Gtz.lambdaMinMat` objective speak to a layer that never mentions an
eigenvalue. -/
theorem chartBlockDominatesAtValue_of_le_chartBlockValue [Nonempty (Fin rank)]
    (point : ChartPoint size rank) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) {value : ℝ}
    (hle : value ≤ chartBlockValue rank
      ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) selected) :
    ChartBlockDominatesAtValue point.chart point.weight value selected := by
  rw [chartBlockValue_chartConfig point hcard, le_lambdaMinMat_iff_forall_dotProduct] at hle
  intro probe hsupport
  have hspread := eq_selectionInjection_mulVec_of_support selected hcard hsupport
  have hdict := dotProduct_selectionInjection_mulVec (chartPointGap point)
    (selected.orderEmbOfFin hcard)
    (fun selectedIndex => probe (selected.orderEmbOfFin hcard selectedIndex))
  rw [← hspread] at hdict
  rw [← dotProduct_self_pick_eq_of_support (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard).injective (image_orderEmbOfFin hcard) hsupport,
    show chartStationaryGap point.chart point.weight = chartPointGap point from rfl, hdict]
  exact hle _

/-- **The objective dictionary at a general value.** -/
theorem hasChartDominatingSubsetAtValue_of_le_chartObjective [Nonempty (Fin rank)]
    (point : ChartPoint size rank) {value : ℝ} (hle : value ≤ chartObjective point) :
    HasChartDominatingSubsetAtValue rank point.chart point.weight value := by
  obtain ⟨selected, hmember, hattained⟩ := Finset.exists_mem_eq_sup'
    (chartCandidates_nonempty (rank_le_size_of_chartPoint point))
    (fun candidate => chartBlockValue rank
      ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) candidate)
  have hcard : selected.card = rank := (mem_chartCandidates_iff size rank selected).mp hmember
  refine ⟨selected, hcard, chartBlockDominatesAtValue_of_le_chartBlockValue point hcard ?_⟩
  have hobjective : chartObjective point = chartBlockValue rank
      ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) selected :=
    hattained
  rw [← hobjective]
  exact hle

/-! ## The weld -/

/-- A moved configuration inside the stationarity layer's constraint set IS a point of the
closed chart domain.

This is the shipped `Gtz.chartPointOfMem` applied to a membership assembled from the five
hypotheses; the difference in interface is that the trace and the weight sum are taken
RELATIVE to a base point rather than absolutely, which is the form the descent layer's
constraint set uses.  Both projections read back definitionally: the chart field is
`movedChart` and the weight field is `movedWeight` by `rfl`. -/
def movedChartPoint (point : ChartPoint size rank)
    {movedChart : Matrix (Fin size) (Fin size) ℝ} {movedWeight : Fin size → ℝ}
    (hsymmetric : movedChartᵀ = movedChart)
    (hidempotent : movedChart * movedChart = movedChart)
    (htrace : Matrix.trace movedChart = Matrix.trace point.chart)
    (hweightPos : ∀ atomIndex, 0 < movedWeight atomIndex)
    (hweightSum : (∑ atomIndex, movedWeight atomIndex) = ∑ atomIndex, point.weight atomIndex) :
    ChartPoint size rank :=
  chartPointOfMem (config := (movedChart, movedWeight))
    ⟨fun rowIndex colIndex => congrFun (congrFun hsymmetric rowIndex) colIndex,
      fun rowIndex colIndex => by
        have hentry := congrFun (congrFun hidempotent rowIndex) colIndex
        rwa [Matrix.mul_apply] at hentry,
      by
        simpa only [Matrix.trace, Matrix.diag_apply] using htrace.trans point.hasTraceRank,
      fun atomIndex => (hweightPos atomIndex).le,
      by rw [hweightSum, point.weight_sum_one]⟩

/-- **THE WELD.**  A global minimiser of `Gtz.chartObjective` over the closed chart domain
satisfies, verbatim, the minimality hypothesis that every theorem of
`Gtz.Quantitative.ChartDescentFromMinimality` consumes.

The two sides existed and did not touch: the objective was defined and attained in
`Gtz.Reduction.ChartAttainment` and used nowhere else; the minimality hypothesis was
consumed in `Gtz.Quantitative.ChartDescentFromMinimality` and produced nowhere. -/
theorem hasChartDominatingSubsetAtValue_of_isMin [Nonempty (Fin rank)]
    (minimiser : ChartPoint size rank)
    (hmin : ∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point) :
    ∀ (movedChart : Matrix (Fin size) (Fin size) ℝ) (movedWeight : Fin size → ℝ),
      movedChartᵀ = movedChart → movedChart * movedChart = movedChart →
      Matrix.trace movedChart = Matrix.trace minimiser.chart →
      (∀ atomIndex : Fin size, 0 < movedWeight atomIndex) →
      (∑ atomIndex : Fin size, movedWeight atomIndex)
        = ∑ atomIndex : Fin size, minimiser.weight atomIndex →
      HasChartDominatingSubsetAtValue rank movedChart movedWeight
        (chartObjective minimiser) := by
  intro movedChart movedWeight hsymmetric hidempotent htrace hweightPos hweightSum
  exact hasChartDominatingSubsetAtValue_of_le_chartObjective
    (movedChartPoint minimiser hsymmetric hidempotent htrace hweightPos hweightSum)
    (hmin _)

/-! ## The inactive side condition is free at the argmax family -/

/-- Normalising a nonzero probe preserves the support and the strict Rayleigh bound.

Distinct from the shipped normalisations: `Gtz.CompactnessReduction`'s rescales to gap
value `-1` rather than to unit length, and
`Gtz.exists_pos_isChartTightDirection_smul_of_isChartTightVector` normalises a TIGHT
vector rather than a strictly-below probe. -/
theorem exists_unit_of_dotProduct_lt {form : Matrix (Fin size) (Fin size) ℝ}
    {rawProbe : Fin size → ℝ} {value : ℝ} (hpositive : 0 < rawProbe ⬝ᵥ rawProbe)
    (hstrict : rawProbe ⬝ᵥ (form *ᵥ rawProbe) < value * (rawProbe ⬝ᵥ rawProbe)) :
    ∃ probe : Fin size → ℝ, probe ⬝ᵥ probe = 1
      ∧ (∀ atomIndex : Fin size, rawProbe atomIndex = 0 → probe atomIndex = 0)
      ∧ probe ⬝ᵥ (form *ᵥ probe) < value := by
  set scale : ℝ := (Real.sqrt (rawProbe ⬝ᵥ rawProbe))⁻¹ with hscaleDef
  have hsquare : scale ^ 2 = (rawProbe ⬝ᵥ rawProbe)⁻¹ := by
    rw [hscaleDef, inv_pow, Real.sq_sqrt hpositive.le]
  refine ⟨scale • rawProbe, ?_, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← pow_two, hsquare, inv_mul_cancel₀ (ne_of_gt hpositive)]
  · intro atomIndex hzero
    simp only [Pi.smul_apply, smul_eq_mul, hzero, mul_zero]
  · rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← pow_two, hsquare, inv_mul_lt_iff₀ hpositive]
    linarith [hstrict]

/-- **A block strictly below the value exhibits a unit probe strictly below it**, in the
AMBIENT form the inactive side condition demands.  The objective is an infimum, so falling
strictly below it already exhibits a witness: no attainment and no spectral theorem. -/
theorem exists_unit_probe_lt_of_chartBlockValue_lt [Nonempty (Fin rank)]
    (point : ChartPoint size rank) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) {value : ℝ}
    (hlt : chartBlockValue rank
      ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) selected
        < value) :
    ∃ probe : Fin size → ℝ, probe ⬝ᵥ probe = 1
      ∧ (∀ atomIndex : Fin size, atomIndex ∉ selected → probe atomIndex = 0)
      ∧ probe ⬝ᵥ (chartStationaryGap point.chart point.weight *ᵥ probe) < value := by
  rw [chartBlockValue_chartConfig point hcard] at hlt
  have hfails : ¬ ∀ direction : Fin rank → ℝ,
      value * (direction ⬝ᵥ direction)
        ≤ direction ⬝ᵥ (((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
            (selected.orderEmbOfFin hcard)) *ᵥ direction) := by
    rw [← le_lambdaMinMat_iff_forall_dotProduct]
    exact not_le.mpr hlt
  obtain ⟨direction, hdirection⟩ := not_forall.mp hfails
  have hdirectionStrict : direction ⬝ᵥ (((chartPointGap point).submatrix
      (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)) *ᵥ direction)
      < value * (direction ⬝ᵥ direction) := not_le.mp hdirection
  set rawProbe : Fin size → ℝ :=
    selectionInjection (selected.orderEmbOfFin hcard) *ᵥ direction with hrawDef
  have hform : rawProbe ⬝ᵥ (chartPointGap point *ᵥ rawProbe)
      = direction ⬝ᵥ (((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)) *ᵥ direction) :=
    dotProduct_selectionInjection_mulVec (chartPointGap point) _ direction
  have hlength : rawProbe ⬝ᵥ rawProbe = direction ⬝ᵥ direction := by
    have hdict := dotProduct_selectionInjection_mulVec
      (1 : Matrix (Fin size) (Fin size) ℝ) (selected.orderEmbOfFin hcard) direction
    rwa [Matrix.submatrix_one _ (selected.orderEmbOfFin hcard).injective, Matrix.one_mulVec,
      Matrix.one_mulVec] at hdict
  have hdirectionNonzero : 0 < direction ⬝ᵥ direction := by
    rcases lt_or_ge 0 (direction ⬝ᵥ direction) with hpositive | hnonpositive
    · exact hpositive
    · have hzero : direction ⬝ᵥ direction = 0 :=
        le_antisymm hnonpositive (dotProduct_self_nonneg direction)
      have hdirectionZero : direction = 0 := by
        funext coordinate
        have hsum : ∑ index, direction index * direction index = 0 := hzero
        have hterm : direction coordinate * direction coordinate = 0 := by
          refine le_antisymm ?_ (mul_self_nonneg _)
          rw [← hsum]
          exact Finset.single_le_sum (f := fun index => direction index * direction index)
            (fun index _ => mul_self_nonneg _) (Finset.mem_univ coordinate)
        exact mul_self_eq_zero.mp hterm
      rw [hdirectionZero] at hdirectionStrict
      simp at hdirectionStrict
  have hrawPositive : 0 < rawProbe ⬝ᵥ rawProbe := by rw [hlength]; exact hdirectionNonzero
  have hrawStrict : rawProbe ⬝ᵥ (chartPointGap point *ᵥ rawProbe)
      < value * (rawProbe ⬝ᵥ rawProbe) := by rw [hform, hlength]; exact hdirectionStrict
  obtain ⟨probe, hunit, hsupportRaw, hbelow⟩ :=
    exists_unit_of_dotProduct_lt hrawPositive hrawStrict
  refine ⟨probe, hunit, fun atomIndex hnotMem => hsupportRaw atomIndex ?_, hbelow⟩
  refine selectionInjection_mulVec_eq_zero_of_notMem _ _ fun selectedIndex heq => hnotMem ?_
  have hmember : selected.orderEmbOfFin hcard selectedIndex
      ∈ Set.range (selected.orderEmbOfFin hcard) := ⟨selectedIndex, rfl⟩
  rw [Finset.range_orderEmbOfFin selected hcard] at hmember
  exact heq ▸ hmember

open scoped Classical in
/-- **The argmax family** of a chart point: the `rank`-subsets whose block value is not
below the objective.  Since the objective is the `sup'` of the block values these are
exactly the blocks attaining it.

This is a FAMILY of subsets, and is a different object from the shipped
`Gtz.IsChartArgmaxValue`, which is a per-subset probe condition. -/
noncomputable def chartArgmaxFamily [Nonempty (Fin rank)] (point : ChartPoint size rank) :
    Finset (Finset (Fin size)) :=
  (chartCandidates size rank).filter fun candidate =>
    chartObjective point ≤ chartBlockValue rank
      ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) candidate

theorem mem_chartArgmaxFamily_iff [Nonempty (Fin rank)] (point : ChartPoint size rank)
    (candidate : Finset (Fin size)) :
    candidate ∈ chartArgmaxFamily point
      ↔ candidate.card = rank ∧ chartObjective point ≤ chartBlockValue rank
          ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ))
          candidate := by
  classical
  rw [chartArgmaxFamily, Finset.mem_filter, mem_chartCandidates_iff]

/-- **NON-VACUITY.**  The argmax family is never empty: the `sup'` defining the objective
is attained at one of the candidates.  Without this the covering condition below would be
a statement about an empty family. -/
theorem chartArgmaxFamily_nonempty [Nonempty (Fin rank)] (point : ChartPoint size rank) :
    (chartArgmaxFamily point).Nonempty := by
  obtain ⟨selected, hmember, hattained⟩ := Finset.exists_mem_eq_sup'
    (chartCandidates_nonempty (rank_le_size_of_chartPoint point))
    (fun candidate => chartBlockValue rank
      ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) candidate)
  refine ⟨selected, (mem_chartArgmaxFamily_iff point selected).mpr
    ⟨(mem_chartCandidates_iff size rank selected).mp hmember, le_of_eq ?_⟩⟩
  exact hattained

/-- **THE INACTIVE SIDE CONDITION IS FREE AT THE ARGMAX FAMILY.**  Every `rank`-subset
either attains the objective -- and is then carried by the family -- or falls strictly
below it, and falling strictly below an infimum already exhibits a probe.

The only previously shipped inhabitant of `Gtz.IsChartInactiveStrict` was the single
`(4,3)` witness `Gtz.chartTetraProjection_isChartInactiveStrict`, proved by `decide`; this
is the general construction. -/
theorem isChartInactiveStrict_chartArgmaxFamily [Nonempty (Fin rank)]
    (point : ChartPoint size rank) :
    IsChartInactiveStrict rank point.chart point.weight (chartObjective point)
      (chartArgmaxFamily point) (id : Finset (Fin size) → Finset (Fin size)) := by
  intro chosenSubset hcard
  by_cases hactive : chartObjective point ≤ chartBlockValue rank
      ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) chosenSubset
  · exact Or.inl ⟨chosenSubset,
      (mem_chartArgmaxFamily_iff point chosenSubset).mpr ⟨hcard, hactive⟩, rfl⟩
  · exact Or.inr (exists_unit_probe_lt_of_chartBlockValue_lt point hcard (not_le.mp hactive))

/-! ## The first-order covering condition, from attainment alone -/

/-- **THE COVERING CONDITION AT A GLOBAL MINIMISER OF THE CHART OBJECTIVE.**  Attainment
plus the free inactive side condition compose with the shipped
`Gtz.isChartTightCovering_of_globalMinimum`.  No spectral theorem is consumed: only the
STRONG bundle asks for a tight direction at a block. -/
theorem isChartTightCovering_of_isMin [Nonempty (Fin rank)] (minimiser : ChartPoint size rank)
    (hweightPos : ∀ atomIndex : Fin size, 0 < minimiser.weight atomIndex)
    (hmin : ∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point) :
    IsChartTightCovering minimiser.chart minimiser.weight (chartObjective minimiser)
      (chartArgmaxFamily minimiser) (id : Finset (Fin size) → Finset (Fin size)) :=
  isChartTightCovering_of_globalMinimum minimiser.isSymmetric minimiser.isIdempotent
    hweightPos (isChartInactiveStrict_chartArgmaxFamily minimiser)
    (hasChartDominatingSubsetAtValue_of_isMin minimiser hmin)

/-- **THE STRONG STATIONARITY BUNDLE AT A GLOBAL MINIMISER**, with `hexistsTight` -- a unit
tight direction at every argmax block -- still a hypothesis of THIS statement.  The
spectral leg below discharges it, and
`isChartStrongStationaryData_of_isMin_of_weightPos` is the hypothesis-free form.  Kept as
the hypothesis-carrying intermediate, mirroring the shipped local/global pair. -/
theorem isChartStrongStationaryData_of_isMin [Nonempty (Fin rank)]
    (minimiser : ChartPoint size rank)
    (hweightPos : ∀ atomIndex : Fin size, 0 < minimiser.weight atomIndex)
    (hexistsTight : ∀ activeLabel ∈ chartArgmaxFamily minimiser, ∃ tightVec : Fin size → ℝ,
      IsChartTightDirection minimiser.chart minimiser.weight (chartObjective minimiser)
        (id activeLabel) tightVec)
    (hmin : ∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point) :
    IsChartStrongStationaryData rank minimiser.chart minimiser.weight
      (chartObjective minimiser) (chartArgmaxFamily minimiser)
      (id : Finset (Fin size) → Finset (Fin size)) :=
  isChartStrongStationaryData_of_globalMinimum minimiser.isSymmetric minimiser.isIdempotent
    minimiser.hasTraceRank hweightPos minimiser.weight_sum_one
    (fun activeLabel hmember => ((mem_chartArgmaxFamily_iff minimiser activeLabel).mp hmember).1)
    hexistsTight (isChartInactiveStrict_chartArgmaxFamily minimiser)
    (hasChartDominatingSubsetAtValue_of_isMin minimiser hmin)

/-! ## The spectral leg: every argmax block DOES carry a unit tight direction -/

/-- `Matrix.toEuclideanCLM` of a Hermitian matrix is self-adjoint: the transport is a
`StarAlgEquiv`, so it carries `star` across. -/
theorem isSelfAdjoint_toEuclideanCLM
    {block : Matrix (Fin rank) (Fin rank) ℝ} (hhermitian : block.IsHermitian) :
    IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) block) := by
  have hstar : star block = block := hhermitian
  show star (Matrix.toEuclideanCLM (𝕜 := ℝ) block) = Matrix.toEuclideanCLM (𝕜 := ℝ) block
  rw [← map_star, hstar]

/-- **THE LEAST EIGENVALUE OF A SYMMETRIC BLOCK IS ATTAINED BY A UNIT EIGENVECTOR.**
Mathlib's Rayleigh theory: a sphere-minimiser of the Rayleigh quotient of a self-adjoint
operator is an eigenvector for the GLOBAL infimum of the quotient, and that infimum is
`Gtz.lambdaMinMat` by definition.

Neither shipped Rayleigh lemma can be reused as stated, and the reason is recorded here so
the third copy of the compactness step is not multiplied a fourth time.
`Gtz.exists_lambdaMinMat_eq_rayleigh` produces a Rayleigh MINIMISER but not the eigenvector
EQUATION, which is what `Gtz.IsChartTightDirection` needs; and
`Gtz.exists_isMinOn_rayleighQuotient`, whose first ten lines this proof re-runs, discards
the sphere-level `IsMinOn` that must be fed to
`IsSelfAdjoint.hasEigenvector_of_isMinOn`. -/
theorem exists_unit_eigenvector_lambdaMinMat [Nonempty (Fin rank)]
    (block : Matrix (Fin rank) (Fin rank) ℝ) (hhermitian : block.IsHermitian) :
    ∃ eigenVec : Fin rank → ℝ, eigenVec ⬝ᵥ eigenVec = 1
      ∧ ∀ coordinate, (block *ᵥ eigenVec) coordinate
          = lambdaMinMat block * eigenVec coordinate := by
  obtain ⟨seed, hseedNonzero⟩ : ∃ z : EuclideanSpace ℝ (Fin rank), z ≠ 0 := exists_ne 0
  obtain ⟨minimiser, hmemberSphere, hminOn⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin rank)) ‖seed‖).exists_isMinOn
      ⟨seed, by simp⟩
      (Matrix.toEuclideanCLM (𝕜 := ℝ) block).reApplyInnerSelf_continuous.continuousOn
  have hnormEqual : ‖minimiser‖ = ‖seed‖ := by simpa using hmemberSphere
  have hminimiserNonzero : minimiser ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnormEqual
    exact hseedNonzero (norm_eq_zero.mp hnormEqual.symm)
  have hminOnOwn : IsMinOn (Matrix.toEuclideanCLM (𝕜 := ℝ) block).reApplyInnerSelf
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin rank)) ‖minimiser‖) minimiser := by
    simpa only [← hnormEqual] using hminOn
  have happly := ((isSelfAdjoint_toEuclideanCLM hhermitian).hasEigenvector_of_isMinOn
    hminimiserNonzero hminOnOwn).apply_eq_smul
  have hcoordinates : block *ᵥ (minimiser : Fin rank → ℝ)
      = lambdaMinMat block • (minimiser : Fin rank → ℝ) :=
    congrArg (fun z : EuclideanSpace ℝ (Fin rank) => (z : Fin rank → ℝ)) happly
  have hlengthPositive : 0 < (minimiser : Fin rank → ℝ) ⬝ᵥ (minimiser : Fin rank → ℝ) := by
    rw [← euclid_norm_sq_eq_dotProduct]
    exact pow_pos (norm_pos_iff.mpr hminimiserNonzero) 2
  set scale : ℝ := (Real.sqrt ((minimiser : Fin rank → ℝ)
    ⬝ᵥ (minimiser : Fin rank → ℝ)))⁻¹ with hscaleDef
  have hsquare : scale ^ 2
      = ((minimiser : Fin rank → ℝ) ⬝ᵥ (minimiser : Fin rank → ℝ))⁻¹ := by
    rw [hscaleDef, inv_pow, Real.sq_sqrt hlengthPositive.le]
  refine ⟨scale • (minimiser : Fin rank → ℝ), ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← pow_two,
      hsquare, inv_mul_cancel₀ (ne_of_gt hlengthPositive)]
  · intro coordinate
    rw [Matrix.mulVec_smul, hcoordinates]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Spreading a selected vector and reading the ambient product back at a selected
coordinate computes the submatrix's product.  No symmetry is used.

Stated in the `Gtz.selectionInjection` vocabulary, alongside the shipped family
(`Gtz.transpose_selectionInjection_mul`, `Gtz.submatrix_mul_selectionInjection`,
`Gtz.dotProduct_selectionInjection_mulVec`).  Its content also appears as the inline
`hrow` step of `Gtz.dotProduct_mulVec_submatrix_pick_eq_of_support`; the two are not
interchangeable, because that one needs a support hypothesis and this one does not -- the
spread vector is supported by construction. -/
theorem mulVec_selectionInjection_apply {selectionSize ambient : ℕ}
    (form : Matrix (Fin ambient) (Fin ambient) ℝ) (pick : Fin selectionSize → Fin ambient)
    (probe : Fin selectionSize → ℝ) (selectedIndex : Fin selectionSize) :
    (form *ᵥ (selectionInjection pick *ᵥ probe)) (pick selectedIndex)
      = (form.submatrix pick pick *ᵥ probe) selectedIndex := by
  rw [Matrix.mulVec_mulVec]
  show ∑ otherIndex, (form * selectionInjection pick) (pick selectedIndex) otherIndex
      * probe otherIndex
    = ∑ otherIndex, form (pick selectedIndex) (pick otherIndex) * probe otherIndex
  refine Finset.sum_congr rfl fun otherIndex _ => ?_
  have hentry : (form * selectionInjection pick) (pick selectedIndex) otherIndex
      = form (pick selectedIndex) (pick otherIndex) := by
    simp only [Matrix.mul_apply, selectionInjection, Matrix.of_apply]
    rw [Finset.sum_eq_single_of_mem (pick otherIndex) (Finset.mem_univ _)
      (fun other _ hother => by rw [if_neg fun heq => hother heq.symm, mul_zero]),
      if_pos rfl, mul_one]
  rw [hentry]

/-- The spread of a vector reads back its own entries at the selected coordinates. -/
theorem selectionInjection_mulVec_apply {selectionSize ambient : ℕ}
    {pick : Fin selectionSize → Fin ambient} (hinjective : Function.Injective pick)
    (probe : Fin selectionSize → ℝ) (selectedIndex : Fin selectionSize) :
    (selectionInjection pick *ᵥ probe) (pick selectedIndex) = probe selectedIndex := by
  simp only [Matrix.mulVec, dotProduct, selectionInjection, Matrix.of_apply]
  rw [Finset.sum_eq_single_of_mem selectedIndex (Finset.mem_univ _)
    (fun other _ hother => by
      rw [if_neg fun heq => hother (hinjective heq), zero_mul]),
    if_pos rfl, one_mul]

/-- **EVERY ARGMAX BLOCK CARRIES A UNIT TIGHT DIRECTION.**  This is the `hexistsTight`
field, which `Gtz.Quantitative.ChartDescentFromMinimality`'s header names as "NOT free --
producing a tight eigenvector at a block where `lambda_min(W[C])` EQUALS `value` is the
spectral theorem, and this file does not supply it".  Supplied here, from Mathlib's
Rayleigh theory transported along `Gtz.selectionInjection`. -/
theorem exists_isChartTightDirection_of_mem_chartArgmaxFamily [Nonempty (Fin rank)]
    (point : ChartPoint size rank) {selected : Finset (Fin size)}
    (hmember : selected ∈ chartArgmaxFamily point) :
    ∃ tightVec : Fin size → ℝ,
      IsChartTightDirection point.chart point.weight (chartObjective point) selected
        tightVec := by
  obtain ⟨hcard, hobjectiveLe⟩ := (mem_chartArgmaxFamily_iff point selected).mp hmember
  have hblockLe : chartBlockValue rank
      ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) selected
        ≤ chartObjective point :=
    Finset.le_sup' (f := fun candidate => chartBlockValue rank
        ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) candidate)
      ((mem_chartCandidates_iff size rank selected).mpr hcard)
  have hvalue : lambdaMinMat ((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard)) = chartObjective point := by
    rw [← chartBlockValue_chartConfig point hcard]
    exact le_antisymm hblockLe hobjectiveLe
  obtain ⟨eigenVec, hunit, hEigen⟩ := exists_unit_eigenvector_lambdaMinMat
    ((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard))
    (isHermitian_chartPointGap_submatrix point selected hcard)
  refine ⟨selectionInjection (selected.orderEmbOfFin hcard) *ᵥ eigenVec, ?_, ?_, ?_⟩
  · have hdict := dotProduct_selectionInjection_mulVec
      (1 : Matrix (Fin size) (Fin size) ℝ) (selected.orderEmbOfFin hcard) eigenVec
    rw [Matrix.submatrix_one _ (selected.orderEmbOfFin hcard).injective, Matrix.one_mulVec,
      Matrix.one_mulVec] at hdict
    rw [hdict]
    exact hunit
  · intro atomIndex hnotMember
    refine selectionInjection_mulVec_eq_zero_of_notMem _ _ fun selectedIndex heq =>
      hnotMember ?_
    have hrange : selected.orderEmbOfFin hcard selectedIndex
        ∈ Set.range (selected.orderEmbOfFin hcard) := ⟨selectedIndex, rfl⟩
    rw [Finset.range_orderEmbOfFin selected hcard] at hrange
    exact heq ▸ hrange
  · intro atomIndex hmemberSelected
    obtain ⟨selectedIndex, hselectedIndex⟩ : ∃ selectedIndex,
        selected.orderEmbOfFin hcard selectedIndex = atomIndex := by
      have hrange : atomIndex ∈ Set.range (selected.orderEmbOfFin hcard) := by
        rw [Finset.range_orderEmbOfFin selected hcard]; exact hmemberSelected
      exact hrange
    subst hselectedIndex
    rw [show chartStationaryGap point.chart point.weight = chartPointGap point from rfl,
      mulVec_selectionInjection_apply, hEigen selectedIndex, hvalue,
      selectionInjection_mulVec_apply (selected.orderEmbOfFin hcard).injective]

/-- **THE STRONG STATIONARITY BUNDLE AT A GLOBAL MINIMISER, UNCONDITIONALLY.**  With the
spectral leg above, `hexistsTight` is discharged and the whole strong first-order system
follows from interiority plus minimality alone. -/
theorem isChartStrongStationaryData_of_isMin_of_weightPos [Nonempty (Fin rank)]
    (minimiser : ChartPoint size rank)
    (hweightPos : ∀ atomIndex : Fin size, 0 < minimiser.weight atomIndex)
    (hmin : ∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point) :
    IsChartStrongStationaryData rank minimiser.chart minimiser.weight
      (chartObjective minimiser) (chartArgmaxFamily minimiser)
      (id : Finset (Fin size) → Finset (Fin size)) :=
  isChartStrongStationaryData_of_isMin minimiser hweightPos
    (fun _activeLabel hmember =>
      exists_isChartTightDirection_of_mem_chartArgmaxFamily minimiser hmember) hmin

/-- **THE WEAK BUNDLE AND ITS ADMISSIBILITY, TOGETHER, AT A GLOBAL MINIMISER.**  The two
hypotheses every exclusion in `Gtz.Quantitative.ChartStationary` and its successors
consumes, both discharged from interiority plus minimality. -/
theorem exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin [Nonempty (Fin rank)]
    (minimiser : ChartPoint size rank)
    (hweightPos : ∀ atomIndex : Fin size, 0 < minimiser.weight atomIndex)
    (hmin : ∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point) :
    (∃ (multiplier : Finset (Fin size) → ℝ)
        (selection : Finset (Fin size) → (Fin size → ℝ)),
        IsChartStationaryData rank minimiser.chart minimiser.weight (chartObjective minimiser)
          (chartArgmaxFamily minimiser) (id : Finset (Fin size) → Finset (Fin size))
          multiplier selection)
      ∧ IsChartArgmaxValue rank minimiser.chart minimiser.weight (chartObjective minimiser) :=
  exists_isChartStationaryData_and_isChartArgmaxValue_of_globalMinimum
    minimiser.isSymmetric minimiser.isIdempotent minimiser.hasTraceRank hweightPos
    minimiser.weight_sum_one
    (fun activeLabel hmember => ((mem_chartArgmaxFamily_iff minimiser activeLabel).mp hmember).1)
    (fun _activeLabel hmember =>
      exists_isChartTightDirection_of_mem_chartArgmaxFamily minimiser hmember)
    (isChartInactiveStrict_chartArgmaxFamily minimiser)
    (hasChartDominatingSubsetAtValue_of_isMin minimiser hmin)

/-! ## Entry from a failure of the target -/

/-- **THE FAILURE IS REALISED AT A FIRST-ORDER CRITICAL POINT.**  If the weighted statement
fails at `(size + 1, rank + 1)` then -- given the two rungs one size down -- there is a
chart point which minimises the chart objective globally, has strictly negative value,
admits no dominating selection, has all weights strictly positive, and satisfies the
first-order covering condition at its own (nonempty) argmax family.

The rungs are stated in WEIGHTED form and crossed to the chart with the shipped iff
`Gtz.chartGtz_iff_gtzWeighted`, so callers do not have to cross the bridge themselves.

At `(7,3)` they read `Gtz.GtzWeighted 6 3` and `Gtz.GtzWeighted 6 2`.  The second is free
(`Gtz.gtz_rank_two`); the first is the open cell, which
`Gtz.gtzWeighted_six_three_of_seven_three` derives FROM the target.  So this is conditional
on a strictly smaller cell and must not be read as unconditional.  At `(6,3)` both rungs
are the shipped `Gtz.gtzWeighted_of_le_five` and it IS unconditional. -/
theorem exists_isChartTightCovering_minimiser_of_not_gtzWeighted [Nonempty (Fin (rank + 1))]
    (hsameRank : GtzWeighted size (rank + 1)) (hdropRank : GtzWeighted size rank)
    (hfail : ¬ GtzWeighted (size + 1) (rank + 1)) :
    ∃ minimiser : ChartPoint (size + 1) (rank + 1),
      (∀ point : ChartPoint (size + 1) (rank + 1),
        chartObjective minimiser ≤ chartObjective point)
      ∧ chartObjective minimiser < 0
      ∧ (∀ selected : Finset (Fin (size + 1)), selected.card = rank + 1 →
          ¬ ChartDominates minimiser selected)
      ∧ (∀ atomIndex, 0 < minimiser.weight atomIndex)
      ∧ (chartArgmaxFamily minimiser).Nonempty
      ∧ IsChartTightCovering minimiser.chart minimiser.weight (chartObjective minimiser)
          (chartArgmaxFamily minimiser)
          (id : Finset (Fin (size + 1)) → Finset (Fin (size + 1))) := by
  obtain ⟨minimiser, hmin, hnegative, hfails, hweightPos⟩ :=
    exists_interior_minimiser_of_not_gtzWeighted
      ((chartGtz_iff_gtzWeighted size (rank + 1)).mpr hsameRank)
      ((chartGtz_iff_gtzWeighted size rank).mpr hdropRank) hfail
  exact ⟨minimiser, hmin, hnegative, hfails, hweightPos, chartArgmaxFamily_nonempty minimiser,
    isChartTightCovering_of_isMin minimiser hweightPos hmin⟩

/-- **THE UNCONDITIONAL HALF.**  No smaller rung is needed to REALISE the failure: a
failure of the weighted statement at any `(size, rank)` is realised at a global minimiser
of the chart objective, with strictly negative value, no dominating selection, and the
stationarity layer's minimality package attached at that value.

What the smaller rungs buy is exactly INTERIORITY, and interiority is what the first-order
conclusions need -- see the previous theorem.  Nothing here is conditional on an open
cell. -/
theorem exists_minimiser_hasChartDominatingSubsetAtValue_of_not_gtzWeighted
    [Nonempty (Fin rank)] (hfail : ¬ GtzWeighted size rank) :
    ∃ minimiser : ChartPoint size rank,
      (∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point)
      ∧ chartObjective minimiser < 0
      ∧ (∀ selected : Finset (Fin size), selected.card = rank →
          ¬ ChartDominates minimiser selected)
      ∧ ∀ (movedChart : Matrix (Fin size) (Fin size) ℝ) (movedWeight : Fin size → ℝ),
          movedChartᵀ = movedChart → movedChart * movedChart = movedChart →
          Matrix.trace movedChart = Matrix.trace minimiser.chart →
          (∀ atomIndex : Fin size, 0 < movedWeight atomIndex) →
          (∑ atomIndex : Fin size, movedWeight atomIndex)
            = ∑ atomIndex : Fin size, minimiser.weight atomIndex →
          HasChartDominatingSubsetAtValue rank movedChart movedWeight
            (chartObjective minimiser) := by
  obtain ⟨minimiser, hmin, hnegative, hfails⟩ :=
    exists_minimiser_of_not_chartGtz fun hchart => hfail (gtzWeighted_of_chartGtz hchart)
  exact ⟨minimiser, hmin, hnegative, hfails,
    hasChartDominatingSubsetAtValue_of_isMin minimiser hmin⟩

/-- **THE FULL FIRST-ORDER SYSTEM AT THE REALISED FAILURE.**  The previous theorem's
interior packaging, upgraded to the strong bundle by the spectral leg.  Same
conditionality: the two rungs one size down, stated in weighted form. -/
theorem exists_isChartStrongStationaryData_minimiser_of_not_gtzWeighted
    [Nonempty (Fin (rank + 1))]
    (hsameRank : GtzWeighted size (rank + 1)) (hdropRank : GtzWeighted size rank)
    (hfail : ¬ GtzWeighted (size + 1) (rank + 1)) :
    ∃ minimiser : ChartPoint (size + 1) (rank + 1),
      chartObjective minimiser < 0
      ∧ (∀ selected : Finset (Fin (size + 1)), selected.card = rank + 1 →
          ¬ ChartDominates minimiser selected)
      ∧ (∀ atomIndex, 0 < minimiser.weight atomIndex)
      ∧ (chartArgmaxFamily minimiser).Nonempty
      ∧ IsChartStrongStationaryData (rank + 1) minimiser.chart minimiser.weight
          (chartObjective minimiser) (chartArgmaxFamily minimiser)
          (id : Finset (Fin (size + 1)) → Finset (Fin (size + 1)))
      ∧ IsChartArgmaxValue (rank + 1) minimiser.chart minimiser.weight
          (chartObjective minimiser) := by
  obtain ⟨minimiser, hmin, hnegative, hfails, hweightPos⟩ :=
    exists_interior_minimiser_of_not_gtzWeighted
      ((chartGtz_iff_gtzWeighted size (rank + 1)).mpr hsameRank)
      ((chartGtz_iff_gtzWeighted size rank).mpr hdropRank) hfail
  exact ⟨minimiser, hnegative, hfails, hweightPos, chartArgmaxFamily_nonempty minimiser,
    isChartStrongStationaryData_of_isMin_of_weightPos minimiser hweightPos hmin,
    (exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin minimiser hweightPos hmin).2⟩

/-- The weld fires on the shipped `(4, 2)` witness, so nothing above is vacuous.  Sibling
of the shipped `Gtz.exists_chartObjective_isMin_fourTwo`, which guards attainment alone;
this one fires the weld. -/
theorem hasChartDominatingSubsetAtValue_of_isMin_fourTwo :
    ∃ minimiser : ChartPoint 4 2,
      ∀ (movedChart : Matrix (Fin 4) (Fin 4) ℝ) (movedWeight : Fin 4 → ℝ),
        movedChartᵀ = movedChart → movedChart * movedChart = movedChart →
        Matrix.trace movedChart = Matrix.trace minimiser.chart →
        (∀ atomIndex : Fin 4, 0 < movedWeight atomIndex) →
        (∑ atomIndex : Fin 4, movedWeight atomIndex)
          = ∑ atomIndex : Fin 4, minimiser.weight atomIndex →
        HasChartDominatingSubsetAtValue 2 movedChart movedWeight
          (chartObjective minimiser) := by
  obtain ⟨minimiser, hmin⟩ := exists_chartObjective_isMin liftFailurePoint
  exact ⟨minimiser, hasChartDominatingSubsetAtValue_of_isMin minimiser hmin⟩

/-! ## The design-side collared attainment -/

variable {m k : ℕ}

/-- The design-side objective `Phi - 1 = max_C lambda_min(S_C) - 1` on a raw
`(atoms, weights)` configuration, over the `k`-subsets.

This names an expression the tree already speaks anonymously: there is no
`def dominationMargin`, and the margin is written out inline at every site.
`designMargin hrank` is exactly the shipped `Gtz.continuous_dominationMargin`'s subject at
`gates := Gtz.chartCandidates m k`.  A name is needed because the function is handed to
`IsCompact.exists_isMinOn`; it is not a second notion of margin. -/
noncomputable def designMargin [Nonempty (Fin k)] (hrank : k ≤ m)
    (config : (Fin m → Fin k → ℝ) × (Fin m → ℝ)) : ℝ :=
  ((chartCandidates m k).sup' (chartCandidates_nonempty hrank)
    fun candidate => lambdaMinMat (subsetSumRaw config candidate)) - 1

theorem continuous_designMargin [Nonempty (Fin k)] (hrank : k ≤ m) :
    Continuous (designMargin (m := m) (k := k) hrank) :=
  continuous_dominationMargin (chartCandidates m k) (chartCandidates_nonempty hrank)

/-- The threshold dictionary on the design side.  The shipped
`Gtz.margin_pos_iff_exists_strictDominates` is the STRICT companion at the opposite sign
and does not cover this. -/
theorem designMargin_neg_of_forall_not_dominates [Nonempty (Fin k)] (hrank : k ≤ m)
    (D : WeightedDesign m k)
    (hfail : ∀ C : Finset (Fin m), C.card = k → ¬ Dominates D C) :
    designMargin hrank ((D.atom, D.weight) : (Fin m → Fin k → ℝ) × (Fin m → ℝ)) < 0 := by
  have hsup : ((chartCandidates m k).sup' (chartCandidates_nonempty hrank)
      fun candidate => lambdaMinMat (subsetSumRaw
        ((D.atom, D.weight) : (Fin m → Fin k → ℝ) × (Fin m → ℝ)) candidate)) < 1 := by
    rw [Finset.sup'_lt_iff]
    intro candidate hmember
    have hcard : candidate.card = k := (mem_chartCandidates_iff m k candidate).mp hmember
    have hnotDominates : ¬ Dominates D candidate := hfail candidate hcard
    rw [dominates_iff_one_le_lambdaMinMat] at hnotDominates
    exact not_le.mp hnotDominates
  rw [designMargin]
  linarith

theorem forall_not_dominates_of_designMargin_neg [Nonempty (Fin k)] (hrank : k ≤ m)
    (D : WeightedDesign m k)
    (hnegative : designMargin hrank
      ((D.atom, D.weight) : (Fin m → Fin k → ℝ) × (Fin m → ℝ)) < 0) :
    ∀ C : Finset (Fin m), C.card = k → ¬ Dominates D C := by
  intro candidate hcard hdominates
  rw [dominates_iff_one_le_lambdaMinMat] at hdominates
  have hmember : candidate ∈ chartCandidates m k :=
    (mem_chartCandidates_iff m k candidate).mpr hcard
  have hle : lambdaMinMat (subsetSum D candidate)
      ≤ (chartCandidates m k).sup' (chartCandidates_nonempty hrank)
        fun other => lambdaMinMat (subsetSumRaw
          ((D.atom, D.weight) : (Fin m → Fin k → ℝ) × (Fin m → ℝ)) other) :=
    Finset.le_sup' (f := fun other => lambdaMinMat (subsetSumRaw
      ((D.atom, D.weight) : (Fin m → Fin k → ℝ) × (Fin m → ℝ)) other)) hmember
  rw [designMargin] at hnegative
  linarith

/-- A member of the collared class with a positive weight floor IS a weighted design.  The
inverse of the shipped `Gtz.design_mem_collaredSet`, which ships only the forward
direction. -/
def designOfCollared {weightFloor : ℝ} (hfloor : 0 < weightFloor)
    {config : (Fin m → Fin k → ℝ) × (Fin m → ℝ)}
    (hmember : config ∈ collaredSet m k weightFloor) : WeightedDesign m k where
  atom := config.1
  weight := config.2
  weight_pos := fun c => lt_of_lt_of_le hfloor (hmember.2.2.1 c)
  weight_sum_one := hmember.2.1
  isParseval := hmember.1

/-- **DESIGN-SIDE ATTAINMENT ON THE COLLARED CLASS.**  A weakly-heavy counterexample is
succeeded by a MINIMISING weakly-heavy counterexample carrying the original's own smallest
weight as a floor.  This is the only design-side minimiser in the tree:
`Gtz.Design.CollaredCompact` ships `Gtz.isCompact_collaredSet` but no minimiser.

TWO HONEST DEFECTS, both visible in the statement.  The comparison class is only the
designs respecting that floor, so this is NOT a global minimiser over all designs -- the
floor may be active and contribute spurious multipliers.  And heaviness is WEAK, because
the strict all-heavy region is open; the `(7,3)` corollary below removes that second defect
conditionally on the cell one size down. -/
theorem exists_collared_minimiser_of_forall_not_dominates [Nonempty (Fin k)] (hrank : k ≤ m)
    (D : WeightedDesign m k) (hheavy : ∀ c, 1 ≤ leverageOf (D.atom c))
    (hfail : ∀ C : Finset (Fin m), C.card = k → ¬ Dominates D C) :
    ∃ (weightFloor : ℝ) (minimiser : WeightedDesign m k),
      0 < weightFloor
      ∧ (∀ c, weightFloor ≤ minimiser.weight c)
      ∧ (∀ c, 1 ≤ leverageOf (minimiser.atom c))
      ∧ (∀ C : Finset (Fin m), C.card = k → ¬ Dominates minimiser C)
      ∧ ∀ config ∈ collaredSet m k weightFloor,
          designMargin hrank
              ((minimiser.atom, minimiser.weight) : (Fin m → Fin k → ℝ) × (Fin m → ℝ))
            ≤ designMargin hrank config := by
  have hpositiveRank : 0 < k := Fin.pos_iff_nonempty.mpr inferInstance
  have hpositiveSize : 0 < m := lt_of_lt_of_le hpositiveRank hrank
  have hindexNonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp hpositiveSize
  set weightFloor : ℝ := Finset.univ.inf' hindexNonempty D.weight with hfloorDef
  have hfloorPositive : 0 < weightFloor := by
    rw [hfloorDef, Finset.lt_inf'_iff]
    exact fun c _ => D.weight_pos c
  have hfloorLe : ∀ c, weightFloor ≤ D.weight c :=
    fun c => Finset.inf'_le D.weight (Finset.mem_univ c)
  have hbaseMember := design_mem_collaredSet D hfloorLe hheavy
  obtain ⟨config, hmember, hminOn⟩ :=
    (isCompact_collaredSet m k hfloorPositive).exists_isMinOn
      ⟨_, hbaseMember⟩ (continuous_designMargin (m := m) (k := k) hrank).continuousOn
  refine ⟨weightFloor, designOfCollared hfloorPositive hmember, hfloorPositive,
    hmember.2.2.1, hmember.2.2.2, ?_, fun other hother => isMinOn_iff.mp hminOn other hother⟩
  refine forall_not_dominates_of_designMargin_neg hrank _ ?_
  calc designMargin hrank ((config.1, config.2) : (Fin m → Fin k → ℝ) × (Fin m → ℝ))
      ≤ designMargin hrank
          ((D.atom, D.weight) : (Fin m → Fin k → ℝ) × (Fin m → ℝ)) :=
        isMinOn_iff.mp hminOn _ hbaseMember
    _ < 0 := designMargin_neg_of_forall_not_dominates hrank D hfail

/-- **THE (7,3) ALL-HEAVY COLLARED ATTAINMENT, conditional on `Gtz.GtzWeighted 6 3`.**  If
`Gtz.GtzWeightedHeavy 7 3` fails then the failure is realised at a design that is genuinely
ALL-HEAVY and minimises the DESIGN-side objective over the collared class carrying its own
smallest weight as a floor.  The weak-to-strict step is
`Gtz.allHeavy_of_forall_not_dominates`; the weight floor is NOT removed and is the
remaining analytic defect.

WARNING.  This is NOT `Gtz.exists_allHeavy_minimiser_sevenThree`, which minimises the CHART
objective.  `Gtz.Reduction.CompactnessReduction` records that the two objectives share
their threshold but NOT their minimisers, the congruence `diagonal (sqrt t_C)` between them
being non-uniform.  The two designs are different designs. -/
theorem exists_collared_allHeavy_minimiser_sevenThree (hsixThree : GtzWeighted 6 3)
    (hfail : ¬ GtzWeightedHeavy 7 3) :
    ∃ (weightFloor : ℝ) (minimiser : WeightedDesign 7 3),
      0 < weightFloor
      ∧ (∀ c, weightFloor ≤ minimiser.weight c)
      ∧ AllHeavy minimiser
      ∧ (∀ C : Finset (Fin 7), C.card = 3 → ¬ Dominates minimiser C)
      ∧ ∀ config ∈ collaredSet 7 3 weightFloor,
          designMargin (show (3 : ℕ) ≤ 7 by norm_num)
              ((minimiser.atom, minimiser.weight) : (Fin 7 → Fin 3 → ℝ) × (Fin 7 → ℝ))
            ≤ designMargin (show (3 : ℕ) ≤ 7 by norm_num) config := by
  rw [GtzWeightedHeavy] at hfail
  push Not at hfail
  obtain ⟨base, hbaseHeavy, hbaseFails⟩ := hfail
  have hbaseNotDominates : ∀ C : Finset (Fin 7), C.card = 3 → ¬ Dominates base C :=
    fun C hcard hdominates => absurd hdominates (hbaseFails C hcard)
  obtain ⟨weightFloor, minimiser, hfloorPositive, hfloorLe, _hweakHeavy, hminimiserFails,
    hminimal⟩ :=
    exists_collared_minimiser_of_forall_not_dominates (show (3 : ℕ) ≤ 7 by norm_num) base
      (fun c => (hbaseHeavy c).le) hbaseNotDominates
  exact ⟨weightFloor, minimiser, hfloorPositive, hfloorLe,
    allHeavy_of_forall_not_dominates (m := 6) minimiser (by norm_num) hsixThree
      hminimiserFails,
    hminimiserFails, hminimal⟩

end Gtz

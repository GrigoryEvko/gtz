import Gtz.Wave.DesignConsolidationLane
import Gtz.Design.BalancedNormalForm

/-!
# The chart-to-design gauge, and the collapse of the two consolidation lanes

`Gtz.exists_design_of_chartPoint` whitens every chart point whose moment matrix
is positive definite into a `Gtz.WeightedDesign`, square-root free, carrying the
gap of every selection simultaneously.  What it does not carry is PRIMITIVITY,
and primitivity is exactly the hypothesis `Gtz.ConsolidatedStrictTripleDesign`
demands.  This file supplies the missing transfer and closes the loop.

The consequence is that the design statement is not weaker than the chart
statement.  They are EQUIVALENT, so the design lane retires all five on-path
obligations rather than three, and the design form -- one vector family and one
weight vector, with no separate mass -- becomes the canonical target.

The gauge is rank-generic.  Nothing below reads the rank three.
-/

namespace Gtz

open Finset Matrix

variable {size : ℕ}

/-! ## 1. A spanning family has a positive definite moment -/

/-- **The moment matrix is positive definite as soon as the whole family spans.**
The landed `Gtz.posDef_massMoment_of_spanningTriple` asks for three named labels
that span between them.  The consolidated statement supplies spanning of the
whole family instead, which is weaker per label and enough here. -/
theorem posDef_massMoment_of_span {rank : ℕ} (direction : Fin size → (Fin rank → ℝ))
    (mass : Fin size → ℝ) (hmassPos : ∀ label, 0 < mass label)
    (hspan : ∀ probeVec : Fin rank → ℝ,
      (∀ label, direction label ⬝ᵥ probeVec = 0) → probeVec = 0) :
    (∑ label, mass label • atomMatrix (direction label)).PosDef := by
  classical
  have hform : ∀ probeVec : Fin rank → ℝ,
      probeVec ⬝ᵥ ((∑ label, mass label • atomMatrix (direction label)) *ᵥ probeVec)
        = ∑ label, mass label * (direction label ⬝ᵥ probeVec) ^ 2 := by
    intro probeVec
    rw [Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        dotProduct_atomMatrix_mulVec_self]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq ?_,
    fun probeVec hprobeNe => ?_⟩
  · rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]
  · rw [star_trivial, hform probeVec]
    have htermNonneg : ∀ label ∈ (Finset.univ : Finset (Fin size)),
        0 ≤ mass label * (direction label ⬝ᵥ probeVec) ^ 2 :=
      fun label _ => mul_nonneg (hmassPos label).le (sq_nonneg _)
    rcases lt_or_eq_of_le (Finset.sum_nonneg htermNonneg) with hpos | hzero
    · exact hpos
    · exact absurd (hspan probeVec fun label => by
        have hproduct := (Finset.sum_eq_zero_iff_of_nonneg htermNonneg).mp hzero.symm
          label (Finset.mem_univ label)
        rcases mul_eq_zero.mp hproduct with hmassZero | hsquareZero
        · exact absurd hmassZero (hmassPos label).ne'
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsquareZero) hprobeNe

/-! ## 2. Primitivity survives the whitening -/

/-- **An invertible congruence neither creates nor destroys a parallel pair.**
The whitened atom is `whitenerᵀ *ᵥ atomFamily c`, and `mulVec` by an invertible
matrix is injective, so proportionality of two whitened atoms descends to
proportionality of the two base atoms. -/
theorem isPrimitiveDesign_whitenedFamilyDesign {m k : ℕ}
    (atomFamily : Fin m → (Fin k → ℝ)) (weightFamily : Fin m → ℝ)
    (hweightPos : ∀ c, 0 < weightFamily c) (hweightSumOne : ∑ c, weightFamily c = 1)
    {whitener : Matrix (Fin k) (Fin k) ℝ}
    (hwhiten : whitenerᵀ * (∑ c, weightFamily c • atomMatrix (atomFamily c)) * whitener = 1)
    (hunit : IsUnit whitener.det)
    (hpair : ∀ (keptLabel dropLabel : Fin m) (ratio : ℝ), keptLabel ≠ dropLabel →
      atomFamily dropLabel ≠ ratio • atomFamily keptLabel) :
    IsPrimitiveDesign (whitenedFamilyDesign atomFamily weightFamily hweightPos
      hweightSumOne whitener hwhiten) := by
  intro keptLabel dropLabel ratio hdistinct hparallel
  have htransposeUnit : IsUnit whitenerᵀ :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rwa [Matrix.det_transpose])
  refine hpair keptLabel dropLabel ratio hdistinct ?_
  refine Matrix.mulVec_injective_of_isUnit htransposeUnit ?_
  show whitenerᵀ *ᵥ atomFamily dropLabel = whitenerᵀ *ᵥ (ratio • atomFamily keptLabel)
  rw [Matrix.mulVec_smul]
  exact hparallel

/-- **The chart atom family is pair-independent when the directions are.**  Each
chart atom is a strictly positive multiple of its direction, so scaling cannot
manufacture a parallel pair. -/
theorem chartAtomFamily_pair_independent (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmassPos : ∀ label, 0 < mass label)
    (hweightPos : ∀ label, 0 < weight label)
    (hpair : DirectionsArePairIndependent direction)
    (keptLabel dropLabel : Fin size) (ratio : ℝ) (hdistinct : keptLabel ≠ dropLabel) :
    chartAtomFamily direction mass weight dropLabel
      ≠ ratio • chartAtomFamily direction mass weight keptLabel := by
  intro hparallel
  have hdropPos : 0 < Real.sqrt (mass dropLabel / weight dropLabel) :=
    Real.sqrt_pos.mpr (div_pos (hmassPos dropLabel) (hweightPos dropLabel))
  refine hpair keptLabel dropLabel
    (ratio * Real.sqrt (mass keptLabel / weight keptLabel)
      / Real.sqrt (mass dropLabel / weight dropLabel)) hdistinct ?_
  have hscaled : Real.sqrt (mass dropLabel / weight dropLabel) • direction dropLabel
      = (ratio * Real.sqrt (mass keptLabel / weight keptLabel)) • direction keptLabel := by
    rw [← smul_smul]
    exact hparallel
  funext coordinate
  have hcoordinate := congrFun hscaled coordinate
  simp only [Pi.smul_apply, smul_eq_mul] at hcoordinate ⊢
  field_simp
  linarith [hcoordinate]

/-! ## 3. The strengthened gauge map -/

/-- **EVERY chart point with pair-independent directions whitens to a PRIMITIVE
design.**  This is `Gtz.exists_design_of_chartPoint` with the one conclusion it
does not carry.  The construction is the same landed whitening: the congruence
comes from `Gtz.exists_congruence_to_one`, the gap dictionary from
`Gtz.posDef_gap_whitenedFamilyDesign_iff`, and only the primitivity clause is
new. -/
theorem exists_primitive_design_of_chartPoint (direction : Fin size → (Fin 3 → ℝ))
    (point : DirectionChartPoint size)
    (hmoment : (∑ label, point.mass label • atomMatrix (direction label)).PosDef)
    (hpair : DirectionsArePairIndependent direction) :
    ∃ design : WeightedDesign size 3, IsPrimitiveDesign design ∧
      ∀ selected : Finset (Fin size),
        ((subsetSum design selected - 1).PosDef
          ↔ (directionChartGap direction point.mass point.weight selected).PosDef) := by
  classical
  have hmassNonneg : ∀ label, 0 ≤ point.mass label := fun label => (point.mass_pos label).le
  have hframe : frameOperatorOfAtoms (chartAtomFamily direction point.mass point.weight)
      point.weight = ∑ label, point.mass label • atomMatrix (direction label) :=
    frameOperatorOfAtoms_chartAtomFamily direction point.mass point.weight hmassNonneg
      point.weight_pos
  obtain ⟨congruence, hunit, hcongruence⟩ := exists_congruence_to_one (hframe ▸ hmoment)
  have hwhiten : congruenceᵀ * (∑ label, point.weight label
      • atomMatrix (chartAtomFamily direction point.mass point.weight label))
      * congruence = 1 := hcongruence
  refine ⟨whitenedFamilyDesign (chartAtomFamily direction point.mass point.weight)
      point.weight point.weight_pos point.weight_sum_one congruence hwhiten,
    isPrimitiveDesign_whitenedFamilyDesign _ _ _ _ hwhiten hunit
      (fun keptLabel dropLabel ratio hdistinct =>
        chartAtomFamily_pair_independent direction point.mass point.weight
          point.mass_pos point.weight_pos hpair keptLabel dropLabel ratio hdistinct),
    fun selected => ?_⟩
  have hmomentEq : subsetSum (whitenedFamilyDesign
        (chartAtomFamily direction point.mass point.weight) point.weight point.weight_pos
        point.weight_sum_one congruence hwhiten) selected
      = congruenceᵀ * subsetSumOfAtoms (chartAtomFamily direction point.mass point.weight)
          selected * congruence := by
    rw [whitenedDesign_subsetSum_eq, sum_atomMatrix_conj, subsetSumOfAtoms]
  have hgap : subsetSum (whitenedFamilyDesign
        (chartAtomFamily direction point.mass point.weight) point.weight point.weight_pos
        point.weight_sum_one congruence hwhiten) selected - 1
      = congruenceᵀ * directionChartGap direction point.mass point.weight selected
          * congruence := by
    rw [hmomentEq, ← hcongruence,
      directionChartGap_eq_frameGap direction point.mass point.weight hmassNonneg
        point.weight_pos selected,
      frameOperatorOfAtoms, Matrix.mul_assoc congruenceᵀ, Matrix.mul_assoc congruenceᵀ,
      ← Matrix.mul_sub, ← Matrix.sub_mul, ← Matrix.mul_assoc]
  rw [hgap]
  exact (posDef_congr_right
    (directionChartGap_transpose direction point.mass point.weight selected) hunit).symm

/-! ## 4. The two lanes are the same lane -/

/-- **THE DESIGN STATEMENT IMPLIES THE CHART STATEMENT.**  Whiten the chart
point, apply the design statement to the primitive design that results, and pull
the strict selection back along the congruence. -/
theorem consolidatedStrictTriple_of_consolidatedStrictTripleDesign
    (hdesign : ConsolidatedStrictTripleDesign) : ConsolidatedStrictTriple := by
  intro direction hspan hpair point
  obtain ⟨design, hprimitive, htransfer⟩ :=
    exists_primitive_design_of_chartPoint direction point
      (posDef_massMoment_of_span direction point.mass point.mass_pos hspan) hpair
  obtain ⟨selected, hcard, hposDef⟩ := hdesign design hprimitive
  exact ⟨selected, hcard, (htransfer selected).mp hposDef⟩

/-- **THE TWO CONSOLIDATIONS ARE EQUIVALENT.**  The chart statement quantifies
over a strictly larger space, and the whitening shows the extra room is gauge. -/
theorem consolidatedStrictTriple_iff_consolidatedStrictTripleDesign :
    ConsolidatedStrictTriple ↔ ConsolidatedStrictTripleDesign :=
  ⟨consolidatedStrictTripleDesign_of_consolidatedStrictTriple,
    consolidatedStrictTriple_of_consolidatedStrictTripleDesign⟩

/-! ## 5. The design lane retires all five on-path obligations -/

/-- A2 follows from the DESIGN statement. -/
theorem chartTieFreeThreeLines_of_consolidatedStrictTripleDesign
    (hdesign : ConsolidatedStrictTripleDesign) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines :=
  chartTieFreeThreeLines_of_consolidatedStrictTriple
    (consolidatedStrictTriple_of_consolidatedStrictTripleDesign hdesign)

/-- A3 follows from the DESIGN statement. -/
theorem kFourKnifeBandRefined_of_consolidatedStrictTripleDesign
    (hdesign : ConsolidatedStrictTripleDesign) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_of_consolidatedStrictTriple
    (consolidatedStrictTriple_of_consolidatedStrictTripleDesign hdesign)

/-- **ALL FIVE ON-PATH OBLIGATIONS FROM ONE DESIGN-LEVEL STATEMENT.**  The three
design-level obligations were already consequences.  The two chart-level ones,
A2 and A3, now join them through the gauge. -/
theorem allFiveOnPath_of_consolidatedStrictTripleDesign
    (hdesign : ConsolidatedStrictTripleDesign) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  ⟨baseTripleTightLineFreeOffConicHeavyNeedleResidual_of_consolidatedStrictTripleDesign hdesign,
    oneLineTenthHeavyJointBlindLineSparse_of_consolidatedStrictTripleDesign hdesign,
    twoMeetingLinesTenthHeavyJointBlindTransversal_of_consolidatedStrictTripleDesign hdesign,
    chartTieFreeThreeLines_of_consolidatedStrictTripleDesign hdesign,
    kFourKnifeBandRefined_of_consolidatedStrictTripleDesign hdesign⟩

end Gtz

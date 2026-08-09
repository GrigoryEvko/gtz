import Gtz.Design.PlaneBranchNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace Gtz

open Matrix

/-- Square row frame of the unweighted base atoms. -/
def unitAxisBaseFrame (design : WeightedDesign 6 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![design.atom 0, design.atom 1, design.atom 2]

theorem unitAxisBaseFrame_det_ne_zero (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (unitAxisBaseFrame design).det ≠ 0 := by
  have hbracket : tripleBracket (design.atom 0) (design.atom 1) (design.atom 2) ≠ 0 :=
    atomBracket_ne_zero_of_lineFree design hlineFree (by decide) (by decide) (by decide)
  simpa [unitAxisBaseFrame, tripleBracket, atomBracket] using hbracket

theorem unitAxisBaseFrame_det_isUnit (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    IsUnit (unitAxisBaseFrame design).det :=
  isUnit_iff_ne_zero.mpr (unitAxisBaseFrame_det_ne_zero design hlineFree)

/-- Rational-algebraic normalizer sending the three base atoms to the coordinate
axes.  Unlike `planeBaseNormalizer`, it introduces no square roots. -/
noncomputable def unitAxisBaseNormalizer (design : WeightedDesign 6 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (unitAxisBaseFrame design)⁻¹

theorem unitAxisBaseNormalizer_det_isUnit (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    IsUnit (unitAxisBaseNormalizer design).det :=
  (unitAxisBaseFrame design).isUnit_nonsing_inv_det
    (unitAxisBaseFrame_det_isUnit design hlineFree)

/-- Each transformed base atom is the corresponding standard coordinate. -/
theorem unitAxisBaseNormalizer_baseAtom
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (baseIndex : Fin 3) :
    (unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom (baseThreeLabel baseIndex)
      = Pi.single baseIndex 1 := by
  have hinverse := Matrix.mul_nonsing_inv (unitAxisBaseFrame design)
    (unitAxisBaseFrame_det_isUnit design hlineFree)
  ext coordinate
  have hentry := congrFun (congrFun hinverse baseIndex) coordinate
  simp only [unitAxisBaseNormalizer, unitAxisBaseFrame, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
    baseThreeLabel] at hentry ⊢
  fin_cases baseIndex <;> fin_cases coordinate <;>
    simpa [Pi.single_apply, Matrix.one_apply, mul_comm] using hentry

/-- The three free atoms in the unit-axis coordinates. -/
noncomputable def unitAxisFreeAtom (design : WeightedDesign 6 3) :
    Fin 3 -> Fin 3 -> ℝ :=
  fun freeIndex => (unitAxisBaseNormalizer design)ᵀ *ᵥ
    design.atom (freeThreeLabel freeIndex)

/-- The entire transformed family has base scale one. -/
theorem unitAxisBaseNormalizer_atom_eq_axisBaseAtom
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (fun label => (unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom label)
      = axisBaseAtom (fun _ => 1) (unitAxisFreeAtom design) := by
  funext label
  fin_cases label
  · have h := unitAxisBaseNormalizer_baseAtom design hlineFree 0
    change (unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom 0 = _
    simp [baseThreeLabel] at h
    rw [h]
    ext coordinate
    fin_cases coordinate <;> simp [axisBaseAtom]
  · have h := unitAxisBaseNormalizer_baseAtom design hlineFree 1
    change (unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom 1 = _
    simp [baseThreeLabel] at h
    rw [h]
    ext coordinate
    fin_cases coordinate <;> simp [axisBaseAtom]
  · have h := unitAxisBaseNormalizer_baseAtom design hlineFree 2
    change (unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom 2 = _
    simp [baseThreeLabel] at h
    rw [h]
    ext coordinate
    fin_cases coordinate <;> simp [axisBaseAtom]
  · rfl
  · rfl
  · rfl

theorem unitAxisFreeAtom_offDiagonalGrid_det_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom) :
    (freeOffDiagonalGrid (unitAxisFreeAtom design)).det ≠ 0 := by
  have hnormalOffConic : HasNoCommonQuadric
      (fun label => (unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom label) :=
    hasNoCommonQuadric_congrAtom design.atom (unitAxisBaseNormalizer design)
      (unitAxisBaseNormalizer_det_isUnit design hlineFree) hoffConic
  rw [unitAxisBaseNormalizer_atom_eq_axisBaseAtom design hlineFree] at hnormalOffConic
  exact freeOffDiagonalGrid_det_ne_zero_of_hasNoCommonQuadric
    (fun _ => 1) (unitAxisFreeAtom design) hnormalOffConic

/-- Row frame of the three free atoms in unit-axis coordinates. -/
noncomputable def unitAxisFreeFrame (design : WeightedDesign 6 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![unitAxisFreeAtom design 0, unitAxisFreeAtom design 1,
    unitAxisFreeAtom design 2]

theorem unitAxisFreeFrame_det_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (unitAxisFreeFrame design).det ≠ 0 := by
  let P := unitAxisBaseNormalizer design
  have horiginal : tripleBracket (design.atom 3) (design.atom 4) (design.atom 5) ≠ 0 :=
    atomBracket_ne_zero_of_lineFree design hlineFree (by decide) (by decide) (by decide)
  have hPne : P.det ≠ 0 :=
    isUnit_iff_ne_zero.mp (unitAxisBaseNormalizer_det_isUnit design hlineFree)
  have htransform :
      tripleBracket (Pᵀ *ᵥ design.atom 3) (Pᵀ *ᵥ design.atom 4)
          (Pᵀ *ᵥ design.atom 5)
        = tripleBracket (design.atom 3) (design.atom 4) (design.atom 5) * P.det := by
    rw [tripleBracket, tripleBracket, ← Matrix.det_mul]
    congr 1
    ext row col
    fin_cases row <;> simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  change tripleBracket (Pᵀ *ᵥ design.atom 3) (Pᵀ *ᵥ design.atom 4)
      (Pᵀ *ᵥ design.atom 5) ≠ 0
  rw [htransform]
  exact mul_ne_zero horiginal hPne

/-- The transformed unweighted base triple sums to the identity. -/
theorem unitAxisBaseTripleSum
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)),
        atomMatrix ((unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom label)) = 1 := by
  change (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)),
    atomMatrix ((fun c => (unitAxisBaseNormalizer design)ᵀ *ᵥ
      design.atom c) label)) = 1
  rw [unitAxisBaseNormalizer_atom_eq_axisBaseAtom design hlineFree]
  simpa using axisBaseAtom_baseTripleSum (fun _ : Fin 3 => (1 : ℝ))
    (unitAxisFreeAtom design)

/-- In unit-axis coordinates the transported identity metric is `I - hhᵀ`. -/
theorem unitAxisBaseNormalizer_metric_eq_one_sub_hidden
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {hiddenRaw : Fin 3 -> ℝ}
    (hgap : subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1
      = atomMatrix hiddenRaw) :
    (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design
      = 1 - atomMatrix ((unitAxisBaseNormalizer design)ᵀ *ᵥ hiddenRaw) := by
  let P := unitAxisBaseNormalizer design
  have hcongr := congrArg (fun matrix => Pᵀ * matrix * P) hgap
  have htransformedGap :
      (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)),
          atomMatrix (Pᵀ *ᵥ design.atom label)) - Pᵀ * P
        = atomMatrix (Pᵀ *ᵥ hiddenRaw) := by
    rw [subsetSum] at hcongr
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_one] at hcongr
    simp_rw [transpose_mul_atomMatrix_mul] at hcongr
    exact hcongr
  have hbaseSum :
      (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)),
          atomMatrix (Pᵀ *ᵥ design.atom label)) = 1 := by
    exact unitAxisBaseTripleSum design hlineFree
  change Pᵀ * P = _
  rw [hbaseSum] at htransformedGap
  calc
    Pᵀ * P = 1 - (1 - Pᵀ * P) := by noncomm_ring
    _ = 1 - atomMatrix (Pᵀ *ᵥ hiddenRaw) := by rw [htransformedGap]

/-- Parseval after the unit-axis congruence, before using the rank-one gap. -/
theorem unitAxisTransformedParseval
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    design.weight 0 • atomMatrix (![1, 0, 0] : Fin 3 -> ℝ)
        + design.weight 1 • atomMatrix (![0, 1, 0] : Fin 3 -> ℝ)
        + design.weight 2 • atomMatrix (![0, 0, 1] : Fin 3 -> ℝ)
        + design.weight 3 • atomMatrix (unitAxisFreeAtom design 0)
        + design.weight 4 • atomMatrix (unitAxisFreeAtom design 1)
        + design.weight 5 • atomMatrix (unitAxisFreeAtom design 2)
      = (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design := by
  let P := unitAxisBaseNormalizer design
  have hcongr := congrArg (fun matrix => Pᵀ * matrix * P) design.isParseval
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_one] at hcongr
  simp_rw [Matrix.mul_smul, Matrix.smul_mul, transpose_mul_atomMatrix_mul] at hcongr
  rw [Fin.sum_univ_six] at hcongr
  dsimp only [P] at hcongr
  have hzero := unitAxisBaseNormalizer_baseAtom design hlineFree 0
  have hone := unitAxisBaseNormalizer_baseAtom design hlineFree 1
  have htwo := unitAxisBaseNormalizer_baseAtom design hlineFree 2
  simp [baseThreeLabel] at hzero hone htwo
  rw [hzero, hone, htwo] at hcongr
  have esingleZero : (Pi.single 0 1 : Fin 3 -> ℝ) = ![1, 0, 0] := by
    ext coordinate
    fin_cases coordinate <;> simp
  have esingleOne : (Pi.single 1 1 : Fin 3 -> ℝ) = ![0, 1, 0] := by
    ext coordinate
    fin_cases coordinate <;> simp
  have esingleTwo : (Pi.single 2 1 : Fin 3 -> ℝ) = ![0, 0, 1] := by
    ext coordinate
    fin_cases coordinate <;> simp
  rw [esingleZero, esingleOne, esingleTwo] at hcongr
  simpa [unitAxisFreeAtom, freeThreeLabel, add_assoc] using hcongr

/-- The square-root-free four-vector identity. -/
theorem unitAxisFourVectorIdentity
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {hiddenRaw : Fin 3 -> ℝ}
    (hgap : subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1
      = atomMatrix hiddenRaw) :
    let hidden := (unitAxisBaseNormalizer design)ᵀ *ᵥ hiddenRaw
    atomMatrix hidden
        + design.weight 3 • atomMatrix (unitAxisFreeAtom design 0)
        + design.weight 4 • atomMatrix (unitAxisFreeAtom design 1)
        + design.weight 5 • atomMatrix (unitAxisFreeAtom design 2)
      = Matrix.diagonal fun coordinate =>
          1 - design.weight (baseThreeLabel coordinate) := by
  dsimp only
  have hparseval := unitAxisTransformedParseval design hlineFree
  have hmetric := unitAxisBaseNormalizer_metric_eq_one_sub_hidden
    design hlineFree hgap
  rw [hmetric] at hparseval
  ext row col
  have hentry := congrFun (congrFun hparseval row) col
  fin_cases row <;> fin_cases col <;>
    simp [atomMatrix, Matrix.vecMulVec_apply, baseThreeLabel] at hentry ⊢ <;> linarith

/-- Complete square-root-free normal form of the plane branch. -/
theorem exists_planeBranch_unitAxisNormalForm
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ hidden : Fin 3 -> ℝ,
      atomMatrix hidden
          + design.weight 3 • atomMatrix (unitAxisFreeAtom design 0)
          + design.weight 4 • atomMatrix (unitAxisFreeAtom design 1)
          + design.weight 5 • atomMatrix (unitAxisFreeAtom design 2)
        = Matrix.diagonal (fun coordinate =>
            1 - design.weight (baseThreeLabel coordinate))
      ∧ (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design
          = 1 - atomMatrix hidden
      ∧ (freeOffDiagonalGrid (unitAxisFreeAtom design)).det ≠ 0
      ∧ (unitAxisFreeFrame design).det ≠ 0 := by
  obtain ⟨axis, scale, _haxisUnit, hscalePos, hgap⟩ :=
    exists_unitAxis_gapAtom_of_offConic_planeBranch design hoffConic hdominates hfree
  let hiddenRaw := Real.sqrt scale • axis
  let hidden := (unitAxisBaseNormalizer design)ᵀ *ᵥ hiddenRaw
  have hgapRaw : subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1
      = atomMatrix hiddenRaw := hgap
  refine ⟨hidden, ?_, ?_,
    unitAxisFreeAtom_offDiagonalGrid_det_ne_zero design hlineFree hoffConic,
    unitAxisFreeFrame_det_ne_zero design hlineFree⟩
  · exact unitAxisFourVectorIdentity design hlineFree hgapRaw
  · exact unitAxisBaseNormalizer_metric_eq_one_sub_hidden design hlineFree hgapRaw

/-- Every original subset test is exactly its unit-axis test. -/
theorem posDef_gap_iff_unitAxisSubsetGap
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hidden : Fin 3 -> ℝ)
    (hmetric : (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design
      = 1 - atomMatrix hidden)
    (selected : Finset (Fin 6)) :
    (subsetSum design selected - 1).PosDef ↔
      (planeAxisSubsetGap (fun _ : Fin 3 => (1 : ℝ))
        (unitAxisFreeAtom design) hidden selected).PosDef := by
  have hiff := posDef_congrAtom_sub_metric_iff design
    (unitAxisBaseNormalizer design)
    (unitAxisBaseNormalizer_det_isUnit design hlineFree) selected
  have hatom : ∀ label,
      (unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom label
        = axisBaseAtom (fun _ : Fin 3 => (1 : ℝ))
            (unitAxisFreeAtom design) label :=
    congrFun (unitAxisBaseNormalizer_atom_eq_axisBaseAtom design hlineFree)
  simp_rw [hatom] at hiff
  have hmetricAxis : (unitAxisBaseNormalizer design)ᵀ
        * unitAxisBaseNormalizer design
      = planeAxisMetric (fun _ : Fin 3 => (1 : ℝ)) hidden := by
    rw [hmetric]
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [planeAxisMetric, atomMatrix]
  rw [hmetricAxis] at hiff
  unfold planeAxisSubsetGap
  exact hiff.symm

theorem planeBranchTenCandidate_iff_unitAxisTenCandidate
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hidden : Fin 3 -> ℝ)
    (hmetric : (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design
      = 1 - atomMatrix hidden) :
    PlaneBranchTenCandidate design ↔
      AxisPlaneTenCandidate (fun _ : Fin 3 => (1 : ℝ))
        (unitAxisFreeAtom design) hidden := by
  unfold PlaneBranchTenCandidate AxisPlaneTenCandidate
  simp only [posDef_gap_iff_unitAxisSubsetGap design hlineFree hidden hmetric]

/-- The preferred finite failure witness: all base scales are literally one. -/
def UnitAxisPlaneFailureWitness (design : WeightedDesign 6 3) : Prop :=
  ∃ hidden : Fin 3 -> ℝ,
    atomMatrix hidden
        + design.weight 3 • atomMatrix (unitAxisFreeAtom design 0)
        + design.weight 4 • atomMatrix (unitAxisFreeAtom design 1)
        + design.weight 5 • atomMatrix (unitAxisFreeAtom design 2)
      = Matrix.diagonal (fun coordinate =>
          1 - design.weight (baseThreeLabel coordinate))
    ∧ (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design
        = 1 - atomMatrix hidden
    ∧ (freeOffDiagonalGrid (unitAxisFreeAtom design)).det ≠ 0
    ∧ (unitAxisFreeFrame design).det ≠ 0
    ∧ AxisPlanePolynomialFailure (fun _ : Fin 3 => (1 : ℝ))
        (unitAxisFreeAtom design) hidden

/-- Failure of the original ten candidates is exactly the unit-axis polynomial
obstruction. -/
theorem not_planeBranchTenCandidate_iff_unitAxisFailureWitness
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ¬ PlaneBranchTenCandidate design ↔ UnitAxisPlaneFailureWitness design := by
  constructor
  · intro hfailure
    obtain ⟨hidden, hframe, hmetric, hdet, hfreeDet⟩ :=
      exists_planeBranch_unitAxisNormalForm design hlineFree hoffConic hdominates hfree
    have haxisFailure : ¬ AxisPlaneTenCandidate (fun _ : Fin 3 => (1 : ℝ))
        (unitAxisFreeAtom design) hidden := by
      exact fun haxis => hfailure
        ((planeBranchTenCandidate_iff_unitAxisTenCandidate design hlineFree hidden
          hmetric).mpr haxis)
    exact ⟨hidden, hframe, hmetric, hdet, hfreeDet,
      (not_axisPlaneTenCandidate_iff_polynomialFailure
        (fun _ : Fin 3 => (1 : ℝ)) (unitAxisFreeAtom design) hidden hdet).mp
          haxisFailure⟩
  · rintro ⟨hidden, _hframe, hmetric, hdet, _hfreeDet, hfailure⟩
    have haxisFailure : ¬ AxisPlaneTenCandidate (fun _ : Fin 3 => (1 : ℝ))
        (unitAxisFreeAtom design) hidden :=
      (not_axisPlaneTenCandidate_iff_polynomialFailure
        (fun _ : Fin 3 => (1 : ℝ)) (unitAxisFreeAtom design) hidden hdet).mpr
          hfailure
    exact fun hcandidates => haxisFailure
      ((planeBranchTenCandidate_iff_unitAxisTenCandidate design hlineFree hidden
        hmetric).mp hcandidates)

end Gtz

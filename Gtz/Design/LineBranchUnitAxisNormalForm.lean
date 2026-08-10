import Gtz.Design.PlaneBranchUnitAxisNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix

/-- The transported base gap in the square-root-free unit-axis coordinates.
For the plane branch this is `atomMatrix hidden`; on the tight-line branch it
is a PSD form with a one-dimensional kernel. -/
noncomputable def unitAxisHiddenForm (design : WeightedDesign 6 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  1 - (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design

theorem unitAxisHiddenForm_transpose (design : WeightedDesign 6 3) :
    (unitAxisHiddenForm design)ᵀ = unitAxisHiddenForm design := by
  simp [unitAxisHiddenForm, Matrix.transpose_sub, Matrix.transpose_mul]

/-- The hidden form is exactly the base gap transported by congruence. -/
theorem unitAxisHiddenForm_eq_congr_baseGap
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    unitAxisHiddenForm design
      = (unitAxisBaseNormalizer design)ᵀ
          * (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1)
          * unitAxisBaseNormalizer design := by
  let P := unitAxisBaseNormalizer design
  have hbase :
      (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)),
          atomMatrix (Pᵀ *ᵥ design.atom label)) = 1 :=
    unitAxisBaseTripleSum design hlineFree
  calc
    unitAxisHiddenForm design = 1 - Pᵀ * P := rfl
    _ = (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)),
          atomMatrix (Pᵀ *ᵥ design.atom label)) - Pᵀ * P := by rw [hbase]
    _ = Pᵀ * (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) * P := by
      rw [sum_atomMatrix_conj, subsetSum]
      noncomm_ring

/-- Domination of the original base triple transports to positive
semidefiniteness of the hidden form. -/
theorem unitAxisHiddenForm_posSemidef
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6))) :
    (unitAxisHiddenForm design).PosSemidef := by
  rw [unitAxisHiddenForm_eq_congr_baseGap design hlineFree]
  exact (posSemidef_congr_right
    (transpose_gap_eq_gap design ({0, 1, 2} : Finset (Fin 6)))
    (unitAxisBaseNormalizer_det_isUnit design hlineFree)).mp hdominates

/-- Parseval in unit-axis coordinates with a general hidden form. This is the
rank-two five-vector identity missing from the tight-line branch. -/
theorem unitAxisFiveVectorIdentity
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    unitAxisHiddenForm design
        + design.weight 3 • atomMatrix (unitAxisFreeAtom design 0)
        + design.weight 4 • atomMatrix (unitAxisFreeAtom design 1)
        + design.weight 5 • atomMatrix (unitAxisFreeAtom design 2)
      = Matrix.diagonal (fun coordinate =>
          1 - design.weight (baseThreeLabel coordinate)) := by
  have hparseval := unitAxisTransformedParseval design hlineFree
  have hmetric :
      (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design
        = 1 - unitAxisHiddenForm design := by
    simp [unitAxisHiddenForm]
  rw [hmetric] at hparseval
  ext row col
  have hentry := congrFun (congrFun hparseval row) col
  fin_cases row <;> fin_cases col <;>
    simp [atomMatrix, Matrix.vecMulVec_apply, baseThreeLabel] at hentry ⊢ <;>
    linarith

theorem unitAxisBaseNormalizer_metric_eq_one_sub_hiddenForm
    (design : WeightedDesign 6 3) :
    (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design
      = 1 - unitAxisHiddenForm design := by
  simp [unitAxisHiddenForm]

/-- The load-bearing scalar normalization omitted by the bare five-vector
identity. It is exactly `sum weight = 1` after taking the trace of Parseval.
This identity holds for both tight-space branches. -/
theorem unitAxisHiddenForm_trace_normalization
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    Matrix.trace (unitAxisHiddenForm design)
        + design.weight 3 *
            ((unitAxisFreeAtom design 0 ⬝ᵥ unitAxisFreeAtom design 0) - 1)
        + design.weight 4 *
            ((unitAxisFreeAtom design 1 ⬝ᵥ unitAxisFreeAtom design 1) - 1)
        + design.weight 5 *
            ((unitAxisFreeAtom design 2 ⬝ᵥ unitAxisFreeAtom design 2) - 1)
      = 2 := by
  have hframe := unitAxisFiveVectorIdentity design hlineFree
  have hzero := congrFun (congrFun hframe 0) 0
  have hone := congrFun (congrFun hframe 1) 1
  have htwo := congrFun (congrFun hframe 2) 2
  have hweight := design.weight_sum_one
  rw [Fin.sum_univ_six] at hweight
  simp [atomMatrix, Matrix.vecMulVec_apply, baseThreeLabel] at hzero hone htwo
  simp [Matrix.trace, Matrix.diag, dotProduct, Fin.sum_univ_three]
  nlinarith

/-- The preimage of the original tight direction in unit-axis coordinates. -/
noncomputable def unitAxisTightVector (design : WeightedDesign 6 3)
    (tightDir : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (unitAxisBaseNormalizer design)⁻¹ *ᵥ tightDir

theorem unitAxisTightVector_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0) :
    unitAxisTightVector design tightDir ≠ 0 := by
  let P := unitAxisBaseNormalizer design
  have hP := unitAxisBaseNormalizer_det_isUnit design hlineFree
  intro hzero
  have hpull := congrArg (fun vector => P *ᵥ vector) hzero
  rw [unitAxisTightVector, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec, Matrix.mulVec_zero] at hpull
  exact htightNe hpull

/-- The transported tight vector lies in the hidden form's kernel. -/
theorem unitAxisHiddenForm_mulVec_tightVector_eq_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    unitAxisHiddenForm design *ᵥ unitAxisTightVector design tightDir = 0 := by
  let P := unitAxisBaseNormalizer design
  have hP := unitAxisBaseNormalizer_det_isUnit design hlineFree
  have hkernel :
      (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir = 0 :=
    (isTightDirectionOf_iff_mulVec_eq_zero design
      ({0, 1, 2} : Finset (Fin 6)) hdominates tightDir).mp htight
  rw [unitAxisHiddenForm_eq_congr_baseGap design hlineFree,
    unitAxisTightVector, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv P hP, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    hkernel, Matrix.mulVec_zero]

/-- On the tight-line branch, the hidden form's kernel is exactly the span of
the transported tight vector. This operational kernel statement is the
rank-two assertion needed by the candidate analysis. -/
theorem unitAxisHiddenForm_mulVec_eq_zero_iff
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (other : Fin 3 → ℝ) :
    unitAxisHiddenForm design *ᵥ other = 0 ↔
      ∃ ratio : ℝ, other = ratio • unitAxisTightVector design tightDir := by
  let P := unitAxisBaseNormalizer design
  have hP := unitAxisBaseNormalizer_det_isUnit design hlineFree
  have hPT : IsUnit Pᵀ.det := by
    rwa [Matrix.det_transpose]
  constructor
  · intro hother
    have hcongr := hother
    rw [unitAxisHiddenForm_eq_congr_baseGap design hlineFree,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hcongr
    have hraw :
        (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1)
          *ᵥ (P *ᵥ other) = 0 := by
      apply Matrix.mulVec_injective_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det Pᵀ).mpr hPT)
      simpa using hcongr
    have hrawTight : IsTightDirectionOf design
        ({0, 1, 2} : Finset (Fin 6)) (P *ᵥ other) :=
      (isTightDirectionOf_iff_mulVec_eq_zero design
        ({0, 1, 2} : Finset (Fin 6)) hdominates (P *ᵥ other)).mpr hraw
    obtain ⟨ratio, hspan⟩ := hline (P *ᵥ other) hrawTight
    refine ⟨ratio, ?_⟩
    apply Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det P).mpr hP)
    change P *ᵥ other = P *ᵥ (ratio • (P⁻¹ *ᵥ tightDir))
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
    exact hspan
  · rintro ⟨ratio, rfl⟩
    rw [Matrix.mulVec_smul,
      unitAxisHiddenForm_mulVec_tightVector_eq_zero design hlineFree hdominates
        htight, smul_zero]

/-- Subset gap in the unit-axis model with an arbitrary hidden form. -/
def unitAxisHiddenSubsetGap (freeAtom : Fin 3 → Fin 3 → ℝ)
    (hiddenForm : Matrix (Fin 3) (Fin 3) ℝ)
    (selected : Finset (Fin 6)) : Matrix (Fin 3) (Fin 3) ℝ :=
  (∑ label ∈ selected,
      atomMatrix (axisBaseAtom (fun _ : Fin 3 => (1 : ℝ)) freeAtom label))
    - (1 - hiddenForm)

/-- Every original strict-subset test is exactly the corresponding test in the
general hidden-form unit-axis coordinates. -/
theorem posDef_gap_iff_unitAxisHiddenSubsetGap
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (selected : Finset (Fin 6)) :
    (unitAxisHiddenSubsetGap (unitAxisFreeAtom design)
      (unitAxisHiddenForm design) selected).PosDef ↔
      (subsetSum design selected - 1).PosDef := by
  have hiff := posDef_congrAtom_sub_metric_iff design
    (unitAxisBaseNormalizer design)
    (unitAxisBaseNormalizer_det_isUnit design hlineFree) selected
  have hatom : ∀ label,
      (unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom label
        = axisBaseAtom (fun _ : Fin 3 => (1 : ℝ))
            (unitAxisFreeAtom design) label :=
    congrFun (unitAxisBaseNormalizer_atom_eq_axisBaseAtom design hlineFree)
  simp_rw [hatom] at hiff
  rw [unitAxisBaseNormalizer_metric_eq_one_sub_hiddenForm design] at hiff
  exact hiff

/-- Complete square-root-free normal form of the U(3,6) tight-line branch.
This is the rank-two counterpart of `exists_planeBranch_unitAxisNormalForm`:
the rank statement is expressed by the exact kernel-span equivalence, avoiding
any dependence on a matrix-rank API. -/
theorem tightLine_unitAxisNormalForm
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    unitAxisHiddenForm design
          + design.weight 3 • atomMatrix (unitAxisFreeAtom design 0)
          + design.weight 4 • atomMatrix (unitAxisFreeAtom design 1)
          + design.weight 5 • atomMatrix (unitAxisFreeAtom design 2)
        = Matrix.diagonal (fun coordinate =>
            1 - design.weight (baseThreeLabel coordinate))
      ∧ (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design
          = 1 - unitAxisHiddenForm design
      ∧ (unitAxisHiddenForm design).PosSemidef
      ∧ unitAxisTightVector design tightDir ≠ 0
      ∧ unitAxisHiddenForm design *ᵥ unitAxisTightVector design tightDir = 0
      ∧ (∀ other : Fin 3 → ℝ,
          unitAxisHiddenForm design *ᵥ other = 0 ↔
            ∃ ratio : ℝ,
              other = ratio • unitAxisTightVector design tightDir)
      ∧ (freeOffDiagonalGrid (unitAxisFreeAtom design)).det ≠ 0
      ∧ (unitAxisFreeFrame design).det ≠ 0
      ∧ (∀ selected : Finset (Fin 6),
          (unitAxisHiddenSubsetGap (unitAxisFreeAtom design)
              (unitAxisHiddenForm design) selected).PosDef ↔
            (subsetSum design selected - 1).PosDef) := by
  refine ⟨unitAxisFiveVectorIdentity design hlineFree,
    unitAxisBaseNormalizer_metric_eq_one_sub_hiddenForm design,
    unitAxisHiddenForm_posSemidef design hlineFree hdominates,
    unitAxisTightVector_ne_zero design hlineFree htightNe,
    unitAxisHiddenForm_mulVec_tightVector_eq_zero design hlineFree hdominates htight,
    ?_,
    unitAxisFreeAtom_offDiagonalGrid_det_ne_zero design hlineFree hoffConic,
    unitAxisFreeFrame_det_ne_zero design hlineFree,
    ?_⟩
  · intro other
    exact unitAxisHiddenForm_mulVec_eq_zero_iff design hlineFree hdominates
      htight hline other
  · intro selected
    exact posDef_gap_iff_unitAxisHiddenSubsetGap design hlineFree selected

end Gtz

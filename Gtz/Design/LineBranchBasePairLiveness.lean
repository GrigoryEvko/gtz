import Gtz.Design.LineBranchPolynomialFailure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6000000

namespace Gtz

open Matrix

/-- The determinant of subtracting one coordinate projector is the determinant
of the form minus the corresponding principal cofactor. -/
theorem det_sub_axisAtom_fin_three
    (form : Matrix (Fin 3) (Fin 3) ℝ) (axis : Fin 3) :
    (form - atomMatrix (Pi.single axis 1)).det
      = form.det - form.adjugate axis axis := by
  fin_cases axis <;>
    simp [Matrix.det_fin_three, Matrix.adjugate_fin_three, atomMatrix,
      Matrix.vecMulVec_apply] <;> ring

/-- The transported hidden form is singular because it kills the transported
nonzero tight direction. -/
theorem unitAxisHiddenForm_det_eq_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    (unitAxisHiddenForm design).det = 0 := by
  by_contra hdet
  apply unitAxisTightVector_ne_zero design hlineFree htightNe
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet
    (unitAxisHiddenForm_mulVec_tightVector_eq_zero design hlineFree hdominates htight)

/-- If a coordinate of the rank-two kernel vector is nonzero, deleting that
coordinate leaves a positive-definite principal block of the hidden form. -/
theorem unitAxisHiddenForm_submatrix_posDef_of_tightCoordinate_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (axis : Fin 3)
    (haxis : unitAxisTightVector design tightDir axis ≠ 0) :
    ((unitAxisHiddenForm design).submatrix axis.succAbove axis.succAbove).PosDef := by
  let hiddenForm := unitAxisHiddenForm design
  let kernelVec := unitAxisTightVector design tightDir
  have hhidden : hiddenForm.PosSemidef :=
    unitAxisHiddenForm_posSemidef design hlineFree hdominates
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (hhidden.isHermitian.submatrix axis.succAbove)
  intro probe hprobeNe
  have hnonneg := (hhidden.submatrix axis.succAbove).dotProduct_mulVec_nonneg probe
  apply lt_of_le_of_ne hnonneg
  intro hzeroReverse
  have hzero :
      probe ⬝ᵥ ((hiddenForm.submatrix axis.succAbove axis.succAbove) *ᵥ probe) = 0 :=
    hzeroReverse.symm
  let lifted : Fin 3 → ℝ := Fin.insertNth axis 0 probe
  have hliftedAxis : lifted axis = 0 := by
    simp [lifted]
  have hquadLifted : lifted ⬝ᵥ (hiddenForm *ᵥ lifted) = 0 := by
    rw [dotProduct_mulVec_submatrix_succAbove hiddenForm axis hliftedAxis]
    simpa [lifted] using hzero
  have hmul : hiddenForm *ᵥ lifted = 0 :=
    mulVec_eq_zero_of_posSemidef_of_dotProduct_zero hhidden hquadLifted
  obtain ⟨ratio, hratioSpan⟩ :=
    (unitAxisHiddenForm_mulVec_eq_zero_iff design hlineFree hdominates
      htight hline lifted).mp hmul
  have hratioMul : ratio * kernelVec axis = 0 := by
    have hentry := congrFun hratioSpan axis
    simpa [lifted, kernelVec, Pi.smul_apply, smul_eq_mul] using hentry.symm
  have hratio : ratio = 0 := (mul_eq_zero.mp hratioMul).resolve_right haxis
  have hliftedZero : lifted = 0 := by
    rw [hratioSpan, hratio, zero_smul]
  apply hprobeNe
  funext index
  have hentry := congrFun hliftedZero (axis.succAbove index)
  simpa [lifted] using hentry

/-- The diagonal cofactor is strictly positive at every nonzero coordinate of
the transported kernel vector. -/
theorem unitAxisHiddenForm_adjugate_diag_pos_of_tightCoordinate_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (axis : Fin 3)
    (haxis : unitAxisTightVector design tightDir axis ≠ 0) :
    0 < (unitAxisHiddenForm design).adjugate axis axis := by
  have hdet := (unitAxisHiddenForm_submatrix_posDef_of_tightCoordinate_ne_zero
    design hlineFree hdominates htight hline axis haxis).det_pos
  fin_cases axis
  all_goals
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    norm_num
    exact hdet

/-- The base-pair gap omitting a nonzero kernel coordinate has negative
determinant. This is the exact determinant half of B2R's base-pair liveness law. -/
theorem unitAxisHiddenBasePairGap_det_neg_of_tightCoordinate_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (axis : Fin 3)
    (haxis : unitAxisTightVector design tightDir axis ≠ 0) :
    (unitAxisHiddenForm design - atomMatrix (Pi.single axis 1)).det < 0 := by
  rw [det_sub_axisAtom_fin_three,
    unitAxisHiddenForm_det_eq_zero design hlineFree hdominates htightNe htight]
  have hadj := unitAxisHiddenForm_adjugate_diag_pos_of_tightCoordinate_ne_zero
    design hlineFree hdominates htight hline axis haxis
  linarith

/-- At least one of the three normalized base-pair gaps has the live-pair
signature witness: a positive-definite surviving principal block and negative
full determinant. -/
theorem exists_unitAxisHiddenBasePair_signatureWitness
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    ∃ axis : Fin 3,
      ((unitAxisHiddenForm design).submatrix axis.succAbove axis.succAbove).PosDef
        ∧ (unitAxisHiddenForm design - atomMatrix (Pi.single axis 1)).det < 0 := by
  have hkernelNe := unitAxisTightVector_ne_zero design hlineFree htightNe
  have hexists : ∃ axis : Fin 3, unitAxisTightVector design tightDir axis ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hkernelNe
    funext axis
    exact hall axis
  obtain ⟨axis, haxis⟩ := hexists
  exact ⟨axis,
    unitAxisHiddenForm_submatrix_posDef_of_tightCoordinate_ne_zero
      design hlineFree hdominates htight hline axis haxis,
    unitAxisHiddenBasePairGap_det_neg_of_tightCoordinate_ne_zero
      design hlineFree hdominates htightNe htight hline axis haxis⟩

end Gtz

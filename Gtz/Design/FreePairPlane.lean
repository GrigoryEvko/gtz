import Gtz.Reduction.ConverseBridge
import Gtz.Reduction.Reductions
import Gtz.Design.TightAxisPairBudget
import Gtz.Design.TightSwapObstructions
import Gtz.Design.UThreeSixStratumWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-- **Selected/complement Parseval decomposition.**  The unweighted gap of a
selected set, plus the complement's weighted mass, is exactly the selected
set's complementary-weight mass.  This is the square-root-free identity behind
the plane branch's hidden four-vector Parseval frame. -/
theorem dominationGap_add_weightedComplement_eq_complementaryWeightedSelected
    {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    subsetSum design selected - 1
        + ∑ label ∈ selectedᶜ,
            design.weight label • atomMatrix (design.atom label)
      = ∑ label ∈ selected,
          (1 - design.weight label) • atomMatrix (design.atom label) := by
  classical
  have hparsevalSplit :
      (∑ label ∈ selected,
          design.weight label • atomMatrix (design.atom label))
        + ∑ label ∈ selectedᶜ,
            design.weight label • atomMatrix (design.atom label)
      = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact design.isParseval
  have hselectedSplit :
      ∑ label ∈ selected,
          (1 - design.weight label) • atomMatrix (design.atom label)
        = subsetSum design selected
          - ∑ label ∈ selected,
              design.weight label • atomMatrix (design.atom label) := by
    rw [subsetSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by
      rw [sub_smul, one_smul]
  rw [hselectedSplit]
  rw [← hparsevalSplit]
  abel

/-- **Coordinate-free rank-one form of the plane branch.**  If a dominating
rank-three gap annihilates two orthonormal directions, it is exactly one
rank-one atom on their unit cross axis.  This is the converse missing from the
coordinate-specific `hasFreeTightDirection_of_gap_eq_lastAxisAtom`. -/
theorem dominationGap_eq_axisAtom_of_orthonormal_tightPair
    {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (pOne pTwo : Fin 3 -> ℝ)
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hdominates : Dominates design selected)
    (hOneTight : IsTightDirectionOf design selected pOne)
    (hTwoTight : IsTightDirectionOf design selected pTwo) :
    let axis := crossProduct pOne pTwo
    let gap := subsetSum design selected - (1 : Matrix (Fin 3) (Fin 3) ℝ)
    gap = (axis ⬝ᵥ (gap *ᵥ axis)) • atomMatrix axis := by
  dsimp only
  let axis := crossProduct pOne pTwo
  let gap := subsetSum design selected - (1 : Matrix (Fin 3) (Fin 3) ℝ)
  let scale := axis ⬝ᵥ (gap *ᵥ axis)
  let frame : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![pOne, pTwo, axis]
  have hOneKernel : gap *ᵥ pOne = 0 := by
    change (subsetSum design selected - 1) *ᵥ pOne = 0
    exact (isTightDirectionOf_iff_mulVec_eq_zero design selected hdominates pOne).mp
      hOneTight
  have hTwoKernel : gap *ᵥ pTwo = 0 := by
    change (subsetSum design selected - 1) *ᵥ pTwo = 0
    exact (isTightDirectionOf_iff_mulVec_eq_zero design selected hdominates pTwo).mp
      hTwoTight
  have hOneAxis : pOne ⬝ᵥ axis = 0 := by
    exact planarCross_probe_dot pOne pTwo
  have hTwoAxis : pTwo ⬝ᵥ axis = 0 := by
    exact planarCross_seed_dot pOne pTwo
  have hAxisOne : axis ⬝ᵥ pOne = 0 := by
    rw [dotProduct_comm]
    exact hOneAxis
  have hAxisTwo : axis ⬝ᵥ pTwo = 0 := by
    rw [dotProduct_comm]
    exact hTwoAxis
  have hAxisAxis : axis ⬝ᵥ axis = 1 := by
    change crossProduct pOne pTwo ⬝ᵥ crossProduct pOne pTwo = 1
    rw [planarCross_self_dot, hOneOne, hTwoTwo, hOneTwo]
    norm_num
  have hgapSymm : gapᵀ = gap := by
    exact transpose_gap_eq_gap design selected
  have hframeGram : frame * frameᵀ = 1 := by
    exact frameGram_eq_one hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis hTwoAxis
  have hframeGramOther : frameᵀ * frame = 1 := mul_eq_one_comm.mp hframeGram
  have hOneGapAxis : pOne ⬝ᵥ (gap *ᵥ axis) = 0 := by
    rw [symmPairing_comm hgapSymm pOne axis, hOneKernel, dotProduct_zero]
  have hTwoGapAxis : pTwo ⬝ᵥ (gap *ᵥ axis) = 0 := by
    rw [symmPairing_comm hgapSymm pTwo axis, hTwoKernel, dotProduct_zero]
  have hcongruence :
      frame * gap * frameᵀ
        = frame * (scale • atomMatrix axis) * frameᵀ := by
    ext rowIndex colIndex
    change
      (Matrix.of ![pOne, pTwo, axis] * gap * (Matrix.of ![pOne, pTwo, axis])ᵀ)
          rowIndex colIndex
        = (Matrix.of ![pOne, pTwo, axis] * (scale • atomMatrix axis)
            * (Matrix.of ![pOne, pTwo, axis])ᵀ) rowIndex colIndex
    rw [frameCongruence_entry, frameCongruence_entry]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [hOneKernel, hTwoKernel, hOneGapAxis, hTwoGapAxis, hOneAxis,
        hTwoAxis, hAxisOne, hAxisTwo, hAxisAxis, scale, Matrix.smul_mulVec, atomMatrix,
        vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul]
  change gap = scale • atomMatrix axis
  calc
    gap = (frameᵀ * frame) * gap * (frameᵀ * frame) := by
      rw [hframeGramOther, Matrix.one_mul, Matrix.mul_one]
    _ = frameᵀ * (frame * gap * frameᵀ) * frame := by
      noncomm_ring
    _ = frameᵀ * (frame * (scale • atomMatrix axis) * frameᵀ) * frame := by
      rw [hcongruence]
    _ = (frameᵀ * frame) * (scale • atomMatrix axis) * (frameᵀ * frame) := by
      noncomm_ring
    _ = scale • atomMatrix axis := by
      rw [hframeGramOther, Matrix.one_mul, Matrix.mul_one]

noncomputable def freeThreeLabel : Fin 3 -> Fin 6 := ![3, 4, 5]

theorem freeThreeLabel_injective : Function.Injective freeThreeLabel := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [freeThreeLabel] at hij ⊢

theorem freeThreeLabel_range (i : Fin 3) :
    freeThreeLabel i = 3 \/ freeThreeLabel i = 4 \/ freeThreeLabel i = 5 := by
  fin_cases i <;> simp [freeThreeLabel]

noncomputable def freeWeightSum (design : WeightedDesign 6 2) : ℝ :=
  design.weight 3 + design.weight 4 + design.weight 5

noncomputable def freePlaneAtom (design : WeightedDesign 6 2) : Fin 3 -> (Fin 2 -> ℝ) :=
  fun i => design.atom (freeThreeLabel i)

noncomputable def normalizedFreeWeight (design : WeightedDesign 6 2) : Fin 3 -> ℝ :=
  fun i => design.weight (freeThreeLabel i) / freeWeightSum design

noncomputable def freeWeightedFrame (design : WeightedDesign 6 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ i : Fin 3, design.weight (freeThreeLabel i) • atomMatrix (design.atom (freeThreeLabel i))

theorem freeWeightSum_pos (design : WeightedDesign 6 2) :
    0 < freeWeightSum design := by
  dsimp [freeWeightSum]
  nlinarith [design.weight_pos 3, design.weight_pos 4, design.weight_pos 5]

theorem normalizedFreeWeight_pos (design : WeightedDesign 6 2) (i : Fin 3) :
    0 < normalizedFreeWeight design i := by
  rw [normalizedFreeWeight]
  exact div_pos (design.weight_pos _) (freeWeightSum_pos design)

theorem normalizedFreeWeight_sum_one (design : WeightedDesign 6 2) :
    ∑ i, normalizedFreeWeight design i = 1 := by
  rw [Fin.sum_univ_three]
  simp only [normalizedFreeWeight, freeThreeLabel, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  rw [← add_mul, ← add_mul]
  exact mul_inv_cancel₀ (ne_of_gt (freeWeightSum_pos design))

theorem frameOperator_normalizedFreeWeight (design : WeightedDesign 6 2) :
    frameOperatorOfAtoms (freePlaneAtom design) (normalizedFreeWeight design)
      = (freeWeightSum design)⁻¹ • freeWeightedFrame design := by
  ext row col
  simp only [frameOperatorOfAtoms, freeWeightedFrame, Fin.sum_univ_three,
    normalizedFreeWeight, freePlaneAtom, freeThreeLabel, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    div_eq_mul_inv, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem freeWeightedFrame_sub_floor_eq (design : WeightedDesign 6 2)
    (hbase : subsetSum design ({0, 1, 2} : Finset (Fin 6)) = 1) :
    freeWeightedFrame design - freeWeightSum design • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      = (design.weight 1 + design.weight 2) • atomMatrix (design.atom 0)
        + (design.weight 0 + design.weight 2) • atomMatrix (design.atom 1)
        + (design.weight 0 + design.weight 1) • atomMatrix (design.atom 2) := by
  ext row col
  have hparseval := congrArg (fun matrix => matrix row col) design.isParseval
  have hbaseExpanded : atomMatrix (design.atom 0) + (atomMatrix (design.atom 1)
        + atomMatrix (design.atom 2)) = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    simpa [subsetSum] using hbase
  have hbaseEntry := congrArg (fun matrix => matrix row col) hbaseExpanded
  have hweight := design.weight_sum_one
  rw [Fin.sum_univ_six] at hparseval hweight
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hparseval
  simp only [Matrix.add_apply] at hbaseEntry
  simp only [freeWeightedFrame, Fin.sum_univ_three, freeThreeLabel,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, freeWeightSum, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul]
  have hfree : design.weight 3 * atomMatrix (design.atom 3) row col
        + design.weight 4 * atomMatrix (design.atom 4) row col
        + design.weight 5 * atomMatrix (design.atom 5) row col
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) row col
        - (design.weight 0 * atomMatrix (design.atom 0) row col
          + design.weight 1 * atomMatrix (design.atom 1) row col
          + design.weight 2 * atomMatrix (design.atom 2) row col) := by
    linarith [hparseval]
  have hsum : design.weight 3 + design.weight 4 + design.weight 5
      = 1 - design.weight 0 - design.weight 1 - design.weight 2 := by
    linarith [hweight]
  rw [hfree, hsum, ← hbaseEntry]
  ring

theorem freeWeightedFrame_sub_floor_posDef (design : WeightedDesign 6 2)
    (hbase : subsetSum design ({0, 1, 2} : Finset (Fin 6)) = 1) :
    (freeWeightedFrame design
      - freeWeightSum design • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
  rw [freeWeightedFrame_sub_floor_eq design hbase]
  have h0 : 0 < design.weight 1 + design.weight 2 := by
    nlinarith [design.weight_pos 1, design.weight_pos 2]
  have h1 : 0 < design.weight 0 + design.weight 2 := by
    nlinarith [design.weight_pos 0, design.weight_pos 2]
  have h2 : 0 < design.weight 0 + design.weight 1 := by
    nlinarith [design.weight_pos 0, design.weight_pos 1]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hprobe => ?_⟩
  · exact Matrix.PosSemidef.isHermitian
      (Matrix.PosSemidef.add
        (Matrix.PosSemidef.add
          ((posSemidef_atomMatrix (design.atom 0)).smul h0.le)
          ((posSemidef_atomMatrix (design.atom 1)).smul h1.le))
        ((posSemidef_atomMatrix (design.atom 2)).smul h2.le))
  · have hbaseExpanded : atomMatrix (design.atom 0) + (atomMatrix (design.atom 1)
          + atomMatrix (design.atom 2)) = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      simpa [subsetSum] using hbase
    have hbaseForm := congrArg
      (fun matrix => probe ⬝ᵥ (matrix *ᵥ probe)) hbaseExpanded
    simp only [Matrix.add_mulVec, dotProduct_add, dotProduct_atomMatrix_mulVec,
      Matrix.one_mulVec] at hbaseForm
    have hnorm : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
    have hsumPositive :
        0 < (design.weight 1 + design.weight 2) * (design.atom 0 ⬝ᵥ probe) ^ 2
          + (design.weight 0 + design.weight 2) * (design.atom 1 ⬝ᵥ probe) ^ 2
          + (design.weight 0 + design.weight 1) * (design.atom 2 ⬝ᵥ probe) ^ 2 := by
      have hsquares :
          0 < (design.atom 0 ⬝ᵥ probe) ^ 2 + (design.atom 1 ⬝ᵥ probe) ^ 2
            + (design.atom 2 ⬝ᵥ probe) ^ 2 := by
        nlinarith [hbaseForm]
      by_cases hz0 : design.atom 0 ⬝ᵥ probe = 0
      · by_cases hz1 : design.atom 1 ⬝ᵥ probe = 0
        · have hz2 : design.atom 2 ⬝ᵥ probe ≠ 0 := by
            intro hz2
            rw [hz0, hz1, hz2] at hsquares
            norm_num at hsquares
          positivity
        · positivity
      · positivity
    rw [star_trivial]
    simpa only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec] using hsumPositive

theorem normalizedFreeFrame_sub_one_posDef (design : WeightedDesign 6 2)
    (hbase : subsetSum design ({0, 1, 2} : Finset (Fin 6)) = 1) :
    ((freeWeightSum design)⁻¹ • freeWeightedFrame design
      - (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
  have hscale : 0 < (freeWeightSum design)⁻¹ := inv_pos.mpr (freeWeightSum_pos design)
  have hscaled := (freeWeightedFrame_sub_floor_posDef design hbase).smul hscale
  have hscaleCancel : (freeWeightSum design)⁻¹ * freeWeightSum design = 1 :=
    inv_mul_cancel₀ (ne_of_gt (freeWeightSum_pos design))
  have heq : (freeWeightSum design)⁻¹ •
        (freeWeightedFrame design
          - freeWeightSum design • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      = (freeWeightSum design)⁻¹ • freeWeightedFrame design - 1 := by
    rw [smul_sub, smul_smul, hscaleCancel, one_smul]
  rwa [heq] at hscaled

theorem normalizedFreeFrame_posDef (design : WeightedDesign 6 2)
    (hbase : subsetSum design ({0, 1, 2} : Finset (Fin 6)) = 1) :
    (frameOperatorOfAtoms (freePlaneAtom design) (normalizedFreeWeight design)).PosDef := by
  rw [frameOperator_normalizedFreeWeight]
  have hgap := normalizedFreeFrame_sub_one_posDef design hbase
  rw [← sub_add_cancel
    ((freeWeightSum design)⁻¹ • freeWeightedFrame design)
    (1 : Matrix (Fin 2) (Fin 2) ℝ)]
  exact Matrix.PosDef.add hgap Matrix.PosDef.one

/-- If three labels form the identity in rank two, the complementary three labels
contain a pair that strictly covers the plane. -/
theorem exists_strict_freePair_of_baseFrame (design : WeightedDesign 6 2)
    (hbase : subsetSum design ({0, 1, 2} : Finset (Fin 6)) = 1) :
    ∃ selected : Finset (Fin 3), selected.card = 2 ∧
      (subsetSumOfAtoms (freePlaneAtom design) selected
        - (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
  obtain ⟨freeDesign, hweight, hdominates⟩ :=
    exists_design_of_frame (freePlaneAtom design) (normalizedFreeWeight design)
      (normalizedFreeWeight_pos design) (normalizedFreeWeight_sum_one design)
      (normalizedFreeFrame_posDef design hbase)
  obtain ⟨selected, hcard, hselected⟩ := gtz_rank_two 3 freeDesign
  have hraw :
      (subsetSumOfAtoms (freePlaneAtom design) selected
        - frameOperatorOfAtoms (freePlaneAtom design)
            (normalizedFreeWeight design)).PosSemidef :=
    (hdominates selected).mp hselected
  have hgap :
      (frameOperatorOfAtoms (freePlaneAtom design) (normalizedFreeWeight design)
        - (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
    rw [frameOperator_normalizedFreeWeight]
    exact normalizedFreeFrame_sub_one_posDef design hbase
  refine ⟨selected, hcard, ?_⟩
  have hadd := Matrix.PosDef.add_posSemidef hgap hraw
  have heq :
      subsetSumOfAtoms (freePlaneAtom design) selected
          - (1 : Matrix (Fin 2) (Fin 2) ℝ)
        = (frameOperatorOfAtoms (freePlaneAtom design) (normalizedFreeWeight design) - 1)
          + (subsetSumOfAtoms (freePlaneAtom design) selected
            - frameOperatorOfAtoms (freePlaneAtom design) (normalizedFreeWeight design)) := by
    abel
  rw [heq]
  exact hadd

theorem exists_strict_pair_in_freeLabels_of_baseFrame (design : WeightedDesign 6 2)
    (hbase : subsetSum design ({0, 1, 2} : Finset (Fin 6)) = 1) :
    ∃ selected : Finset (Fin 6), selected.card = 2
      ∧ selected ⊆ ({3, 4, 5} : Finset (Fin 6))
      ∧ (subsetSum design selected - (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
  obtain ⟨chosen, hcard, hstrict⟩ := exists_strict_freePair_of_baseFrame design hbase
  let selected := chosen.image freeThreeLabel
  have hselectedCard : selected.card = 2 := by
    change (chosen.image freeThreeLabel).card = 2
    rw [Finset.card_image_of_injective _ freeThreeLabel_injective, hcard]
  have hselectedSubset : selected ⊆ ({3, 4, 5} : Finset (Fin 6)) := by
    intro label hlabel
    change label ∈ chosen.image freeThreeLabel at hlabel
    obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hlabel
    rcases freeThreeLabel_range index with h3 | h4 | h5
    · simp [h3]
    · simp [h4]
    · simp [h5]
  have hsum : subsetSum design selected = subsetSumOfAtoms (freePlaneAtom design) chosen := by
    change subsetSum design (chosen.image freeThreeLabel)
      = subsetSumOfAtoms (freePlaneAtom design) chosen
    rw [subsetSum, subsetSumOfAtoms,
      Finset.sum_image fun left _ right _ heq => freeThreeLabel_injective heq]
    rfl
  exact ⟨selected, hselectedCard, hselectedSubset, by rwa [hsum]⟩

theorem planarCompression_baseFrame_of_two_tightDirections
    (design : WeightedDesign 6 3) (firstDir secondDir : Fin 3 -> ℝ)
    (hfirstUnit : firstDir ⬝ᵥ firstDir = 1)
    (hsecondUnit : secondDir ⬝ᵥ secondDir = 1)
    (horthogonal : firstDir ⬝ᵥ secondDir = 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfirstTight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) firstDir)
    (hsecondTight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) secondDir) :
    subsetSum
      (planarCompressionDesign design firstDir secondDir hfirstUnit hsecondUnit horthogonal)
      ({0, 1, 2} : Finset (Fin 6)) = 1 := by
  have hfirstKernel :=
    (isTightDirectionOf_iff_mulVec_eq_zero design ({0, 1, 2} : Finset (Fin 6))
      hdominates firstDir).mp hfirstTight
  have hsecondKernel :=
    (isTightDirectionOf_iff_mulVec_eq_zero design ({0, 1, 2} : Finset (Fin 6))
      hdominates secondDir).mp hsecondTight
  have hform11 := dominationGap_form_pair design ({0, 1, 2} : Finset (Fin 6))
    firstDir firstDir
  have hform12 := dominationGap_form_pair design ({0, 1, 2} : Finset (Fin 6))
    firstDir secondDir
  have hform21 := dominationGap_form_pair design ({0, 1, 2} : Finset (Fin 6))
    secondDir firstDir
  have hform22 := dominationGap_form_pair design ({0, 1, 2} : Finset (Fin 6))
    secondDir secondDir
  rw [hfirstKernel, dotProduct_zero, hfirstUnit] at hform11
  rw [hsecondKernel, dotProduct_zero, horthogonal] at hform12
  have horthogonalReverse : secondDir ⬝ᵥ firstDir = 0 := by
    rw [dotProduct_comm]
    exact horthogonal
  rw [hfirstKernel, dotProduct_zero, horthogonalReverse] at hform21
  rw [hsecondKernel, dotProduct_zero, hsecondUnit] at hform22
  simp at hform11 hform12 hform21 hform22
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [subsetSum, planarCompressionDesign_atom, atomMatrix] <;>
    nlinarith [hform11, hform12, hform21, hform22]

theorem exists_strict_freePair_on_tightPlane
    (design : WeightedDesign 6 3) (firstDir secondDir : Fin 3 -> ℝ)
    (hfirstUnit : firstDir ⬝ᵥ firstDir = 1)
    (hsecondUnit : secondDir ⬝ᵥ secondDir = 1)
    (horthogonal : firstDir ⬝ᵥ secondDir = 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfirstTight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) firstDir)
    (hsecondTight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) secondDir) :
    ∃ selected : Finset (Fin 6), selected.card = 2
      ∧ selected ⊆ ({3, 4, 5} : Finset (Fin 6))
      ∧ (subsetSum
          (planarCompressionDesign design firstDir secondDir
            hfirstUnit hsecondUnit horthogonal) selected
          - (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
  apply exists_strict_pair_in_freeLabels_of_baseFrame
  exact planarCompression_baseFrame_of_two_tightDirections design firstDir secondDir
    hfirstUnit hsecondUnit horthogonal hdominates hfirstTight hsecondTight

theorem exists_orthonormal_tightPair_of_hasFreeTightDirection
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ firstDir secondDir : Fin 3 -> ℝ,
      firstDir ⬝ᵥ firstDir = 1
        ∧ secondDir ⬝ᵥ secondDir = 1
        ∧ firstDir ⬝ᵥ secondDir = 0
        ∧ IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) firstDir
        ∧ IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) secondDir := by
  obtain ⟨firstRaw, hfirstNe, hfirstTight, _⟩ := hfree 0
  obtain ⟨secondRaw, hsecondNe, hsecondTight, hsecondFirst⟩ := hfree firstRaw
  have hfirstPositive : 0 < leverageOf firstRaw := by
    rw [leverageOf_eq_dotProduct_self]
    exact dotProduct_self_pos hfirstNe
  have hsecondPositive : 0 < leverageOf secondRaw := by
    rw [leverageOf_eq_dotProduct_self]
    exact dotProduct_self_pos hsecondNe
  have hfirstNormalizedTight :
      IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) (unitDirection firstRaw) := by
    rw [isTightDirectionOf_iff_mulVec_eq_zero design ({0, 1, 2} : Finset (Fin 6))
      hdominates] at hfirstTight ⊢
    rw [unitDirection, Matrix.mulVec_smul, hfirstTight, smul_zero]
  have hsecondNormalizedTight :
      IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) (unitDirection secondRaw) := by
    rw [isTightDirectionOf_iff_mulVec_eq_zero design ({0, 1, 2} : Finset (Fin 6))
      hdominates] at hsecondTight ⊢
    rw [unitDirection, Matrix.mulVec_smul, hsecondTight, smul_zero]
  have hfirstSecond : firstRaw ⬝ᵥ secondRaw = 0 := by
    rw [dotProduct_comm]
    exact hsecondFirst
  refine ⟨unitDirection firstRaw, unitDirection secondRaw,
    unitDirection_dotProduct_self hfirstPositive,
    unitDirection_dotProduct_self hsecondPositive, ?_,
    hfirstNormalizedTight, hsecondNormalizedTight⟩
  rw [unitDirection_dotProduct, hfirstSecond, mul_zero]

/-- **The hidden fourth vector of the off-conic plane branch.**  The abstract
base gap is a nonzero rank-one atom on a unit axis.  Together with the three
weighted free atoms, the selected/complement Parseval decomposition above is
therefore an honest four-vector frame identity. -/
theorem exists_unitAxis_gapAtom_of_offConic_planeBranch
    (design : WeightedDesign 6 3)
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ axis : Fin 3 -> ℝ, ∃ scale : ℝ,
      axis ⬝ᵥ axis = 1 ∧ 0 < scale
        ∧ subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1
          = atomMatrix (Real.sqrt scale • axis) := by
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneTight, hTwoTight⟩ :=
    exists_orthonormal_tightPair_of_hasFreeTightDirection design hdominates hfree
  let axis := crossProduct pOne pTwo
  let gap := subsetSum design ({0, 1, 2} : Finset (Fin 6)) -
    (1 : Matrix (Fin 3) (Fin 3) ℝ)
  let scale := axis ⬝ᵥ (gap *ᵥ axis)
  have hAxisAxis : axis ⬝ᵥ axis = 1 := by
    change crossProduct pOne pTwo ⬝ᵥ crossProduct pOne pTwo = 1
    rw [planarCross_self_dot, hOneOne, hTwoTwo, hOneTwo]
    norm_num
  have hfactor : gap = scale • atomMatrix axis := by
    exact dominationGap_eq_axisAtom_of_orthonormal_tightPair design
      ({0, 1, 2} : Finset (Fin 6)) pOne pTwo hOneOne hTwoTwo hOneTwo
      hdominates hOneTight hTwoTight
  have hscaleNonneg : 0 ≤ scale := by
    have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 axis
    rw [star_trivial] at hform
    simpa [scale, gap] using hform
  have hgapNe : gap ≠ 0 := by
    exact subsetSum_sub_one_ne_zero_of_hasNoCommonQuadric design hoffConic
      (by decide) (by decide) (by decide)
  have hscaleNe : scale ≠ 0 := by
    intro hzero
    apply hgapNe
    rw [hfactor, hzero, zero_smul]
  have hscalePos : 0 < scale := lt_of_le_of_ne hscaleNonneg (Ne.symm hscaleNe)
  refine ⟨axis, scale, hAxisAxis, hscalePos, ?_⟩
  change gap = atomMatrix (Real.sqrt scale • axis)
  rw [atomMatrix_smul, Real.sq_sqrt hscalePos.le]
  exact hfactor

/-- **Explicit four-vector frame identity for the plane branch.**  The hidden
gap atom and the three weighted free atoms resolve the complementary-weighted
base frame.  This is the exact, square-root-free bridge to a `(4,3)`
corank-one selector after congruence by the positive base frame. -/
theorem exists_fourVectorFrameIdentity_of_offConic_planeBranch
    (design : WeightedDesign 6 3)
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ axis : Fin 3 -> ℝ, ∃ scale : ℝ,
      axis ⬝ᵥ axis = 1 ∧ 0 < scale ∧
        atomMatrix (Real.sqrt scale • axis)
            + (design.weight 3 • atomMatrix (design.atom 3)
              + design.weight 4 • atomMatrix (design.atom 4)
              + design.weight 5 • atomMatrix (design.atom 5))
          = (1 - design.weight 0) • atomMatrix (design.atom 0)
              + (1 - design.weight 1) • atomMatrix (design.atom 1)
              + (1 - design.weight 2) • atomMatrix (design.atom 2) := by
  obtain ⟨axis, scale, hAxisUnit, hscalePos, hgap⟩ :=
    exists_unitAxis_gapAtom_of_offConic_planeBranch design hoffConic hdominates hfree
  refine ⟨axis, scale, hAxisUnit, hscalePos, ?_⟩
  have hdecomposition :=
    dominationGap_add_weightedComplement_eq_complementaryWeightedSelected design
      ({0, 1, 2} : Finset (Fin 6))
  rw [hgap] at hdecomposition
  have hcomplement : ({0, 1, 2} : Finset (Fin 6))ᶜ = {3, 4, 5} := by decide
  rw [hcomplement, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hdecomposition
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hdecomposition
  simpa only [add_assoc] using hdecomposition

/-- Line-freeness makes the complementary-weighted base triple a positive
definite frame.  This supplies the invertible metric needed to whiten the
four-vector identity above; positivity of the three co-weights is essential. -/
theorem complementaryWeightedBaseTriple_posDef_of_lineFree
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    ((1 - design.weight 0) • atomMatrix (design.atom 0)
        + (1 - design.weight 1) • atomMatrix (design.atom 1)
        + (1 - design.weight 2) • atomMatrix (design.atom 2)).PosDef := by
  have hbracket :
      tripleBracket (design.atom 0) (design.atom 1) (design.atom 2) ≠ 0 := by
    simpa [atomBracket] using atomBracket_ne_zero_of_lineFree design hlineFree
      (by decide) (by decide) (by decide)
  have hweightedBase :
      (baseResidual design ({3, 4, 5} : Finset (Fin 6))).PosDef :=
    (posDef_baseResidual_iff_tripleBracket_ne_zero design
      ({3, 4, 5} : Finset (Fin 6)) (![0, 1, 2] : Fin 3 → Fin 6)
      (by decide) (by decide)).mpr hbracket
  have hcoweightZero : 0 < 1 - design.weight 0 := by
    linarith [weight_lt_one design (by norm_num) 0]
  have hcoweightOne : 0 < 1 - design.weight 1 := by
    linarith [weight_lt_one design (by norm_num) 1]
  have hcoweightTwo : 0 < 1 - design.weight 2 := by
    linarith [weight_lt_one design (by norm_num) 2]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hprobeNe => ?_⟩
  · exact Matrix.PosSemidef.isHermitian
      (Matrix.PosSemidef.add
        (Matrix.PosSemidef.add
          ((posSemidef_atomMatrix (design.atom 0)).smul hcoweightZero.le)
          ((posSemidef_atomMatrix (design.atom 1)).smul hcoweightOne.le))
        ((posSemidef_atomMatrix (design.atom 2)).smul hcoweightTwo.le))
  · have hweightedForm :=
      (Matrix.posDef_iff_dotProduct_mulVec.mp hweightedBase).2 hprobeNe
    rw [star_trivial, baseResidual_eq_pickSum design
      ({3, 4, 5} : Finset (Fin 6)) (![0, 1, 2] : Fin 3 → Fin 6)
      (by decide) (by decide), Fin.sum_univ_three] at hweightedForm
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at hweightedForm
    rw [star_trivial]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]
    by_cases hzero : design.atom 0 ⬝ᵥ probe = 0
    · by_cases hone : design.atom 1 ⬝ᵥ probe = 0
      · have htwo : design.atom 2 ⬝ᵥ probe ≠ 0 := by
          intro htwo
          rw [hzero, hone, htwo] at hweightedForm
          norm_num at hweightedForm
        positivity
      · positivity
    · positivity

/-- The plane branch therefore gives a genuine positive three-frame equated
to the hidden gap atom plus the three weighted free atoms. -/
theorem exists_posDef_fourVectorFrameIdentity_of_offConic_planeBranch
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ axis : Fin 3 → ℝ, ∃ scale : ℝ,
      axis ⬝ᵥ axis = 1 ∧ 0 < scale ∧
        ((1 - design.weight 0) • atomMatrix (design.atom 0)
          + (1 - design.weight 1) • atomMatrix (design.atom 1)
          + (1 - design.weight 2) • atomMatrix (design.atom 2)).PosDef ∧
        atomMatrix (Real.sqrt scale • axis)
            + (design.weight 3 • atomMatrix (design.atom 3)
              + design.weight 4 • atomMatrix (design.atom 4)
              + design.weight 5 • atomMatrix (design.atom 5))
          = (1 - design.weight 0) • atomMatrix (design.atom 0)
              + (1 - design.weight 1) • atomMatrix (design.atom 1)
              + (1 - design.weight 2) • atomMatrix (design.atom 2) := by
  obtain ⟨axis, scale, haxis, hscale, hidentity⟩ :=
    exists_fourVectorFrameIdentity_of_offConic_planeBranch design hoffConic
      hdominates hfree
  exact ⟨axis, scale, haxis, hscale,
    complementaryWeightedBaseTriple_posDef_of_lineFree design hlineFree, hidentity⟩

/-- In the plane branch, every one-slot swap of the base triple fails.  Thus a
strict triple can overlap `{0,1,2}` in at most one label: only the nine
distance-two completions and the full complement remain. -/
theorem oneSlotSwap_not_posDef_of_planeBranch
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6)))
    (swapOut swapIn : Fin 6)
    (hmemOut : swapOut ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hnotMemIn : swapIn ∉ ({0, 1, 2} : Finset (Fin 6))) :
    ¬ (subsetSum design
        (insert swapIn (({0, 1, 2} : Finset (Fin 6)).erase swapOut)) - 1).PosDef := by
  obtain ⟨tightDir, probe, htightUnit, hprobeUnit, htightProbe,
    htight, hprobeTight⟩ :=
    exists_orthonormal_tightPair_of_hasFreeTightDirection design hdominates hfree
  have hprobeFlat : probe ⬝ᵥ tightDir = 0 := by
    rw [dotProduct_comm]
    exact htightProbe
  have hprobeNe : probe ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hprobeUnit
    norm_num at hprobeUnit
  exact tightSwap_not_posDef_of_degenerateDominatorGap design
    ({0, 1, 2} : Finset (Fin 6)) swapOut swapIn tightDir probe
    hmemOut hnotMemIn hdominates htightUnit htight hprobeFlat
    hprobeNe hprobeTight

/-- The ten triples which remain after the plane branch rules out the base and
all nine one-slot swaps: nine distance-two candidates and the complement. -/
def PlaneBranchTenCandidate (design : WeightedDesign 6 3) : Prop :=
  (subsetSum design ({0, 3, 4} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({0, 3, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({0, 4, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({1, 3, 4} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({1, 3, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({1, 4, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({2, 3, 4} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({2, 3, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({2, 4, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef

/-- **Exact candidate reduction for the plane branch.**  Strict-triple
existence is equivalent to the explicit ten-candidate disjunction.  The other
ten triples are not merely omitted: the tight base kills `{0,1,2}`, and the
corank obstruction kills every candidate containing two base labels. -/
theorem exists_posDef_cardThree_iff_planeBranchTenCandidate
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    (∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef)
      ↔ PlaneBranchTenCandidate design := by
  classical
  obtain ⟨tightDir, probe, htightUnit, _hprobeUnit, _htightProbe,
    htight, _hprobeTight⟩ :=
    exists_orthonormal_tightPair_of_hasFreeTightDirection design hdominates hfree
  have htightNe : tightDir ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at htightUnit
    norm_num at htightUnit
  have hbaseNot :
      ¬ (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
    not_posDef_baseTripleGap_of_tightDirection design htightNe htight
  have honeSlot : ∀ swapOut ∈ ({0, 1, 2} : Finset (Fin 6)),
      ∀ swapIn ∉ ({0, 1, 2} : Finset (Fin 6)),
        ¬ (subsetSum design
          (insert swapIn (({0, 1, 2} : Finset (Fin 6)).erase swapOut)) - 1).PosDef :=
    fun swapOut hmem swapIn hnot =>
      oneSlotSwap_not_posDef_of_planeBranch design hdominates hfree
        swapOut swapIn hmem hnot
  constructor
  · rintro ⟨selected, hcard, hpos⟩
    have hpow : selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3 :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    rcases cardThreeFinsetsOfSix_enumeration selected hpow with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hbaseNot hpos)
    · exfalso
      have hnot := honeSlot 2 (by decide) 3 (by decide)
      rw [show insert (3 : Fin 6) (({0, 1, 2} : Finset (Fin 6)).erase 2)
        = {0, 1, 3} by decide] at hnot
      exact hnot hpos
    · exfalso
      have hnot := honeSlot 2 (by decide) 4 (by decide)
      rw [show insert (4 : Fin 6) (({0, 1, 2} : Finset (Fin 6)).erase 2)
        = {0, 1, 4} by decide] at hnot
      exact hnot hpos
    · exfalso
      have hnot := honeSlot 2 (by decide) 5 (by decide)
      rw [show insert (5 : Fin 6) (({0, 1, 2} : Finset (Fin 6)).erase 2)
        = {0, 1, 5} by decide] at hnot
      exact hnot hpos
    · exfalso
      have hnot := honeSlot 1 (by decide) 3 (by decide)
      rw [show insert (3 : Fin 6) (({0, 1, 2} : Finset (Fin 6)).erase 1)
        = {0, 2, 3} by decide] at hnot
      exact hnot hpos
    · exfalso
      have hnot := honeSlot 1 (by decide) 4 (by decide)
      rw [show insert (4 : Fin 6) (({0, 1, 2} : Finset (Fin 6)).erase 1)
        = {0, 2, 4} by decide] at hnot
      exact hnot hpos
    · exfalso
      have hnot := honeSlot 1 (by decide) 5 (by decide)
      rw [show insert (5 : Fin 6) (({0, 1, 2} : Finset (Fin 6)).erase 1)
        = {0, 2, 5} by decide] at hnot
      exact hnot hpos
    · exact Or.inl hpos
    · exact Or.inr (Or.inl hpos)
    · exact Or.inr (Or.inr (Or.inl hpos))
    · exfalso
      have hnot := honeSlot 0 (by decide) 3 (by decide)
      rw [show insert (3 : Fin 6) (({0, 1, 2} : Finset (Fin 6)).erase 0)
        = {1, 2, 3} by decide] at hnot
      exact hnot hpos
    · exfalso
      have hnot := honeSlot 0 (by decide) 4 (by decide)
      rw [show insert (4 : Fin 6) (({0, 1, 2} : Finset (Fin 6)).erase 0)
        = {1, 2, 4} by decide] at hnot
      exact hnot hpos
    · exfalso
      have hnot := honeSlot 0 (by decide) 5 (by decide)
      rw [show insert (5 : Fin 6) (({0, 1, 2} : Finset (Fin 6)).erase 0)
        = {1, 2, 5} by decide] at hnot
      exact hnot hpos
    · exact Or.inr (Or.inr (Or.inr (Or.inl hpos)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpos))))))))
  · intro hcandidates
    rcases hcandidates with h | h | h | h | h | h | h | h | h | h
    · exact ⟨{0, 3, 4}, by decide, h⟩
    · exact ⟨{0, 3, 5}, by decide, h⟩
    · exact ⟨{0, 4, 5}, by decide, h⟩
    · exact ⟨{1, 3, 4}, by decide, h⟩
    · exact ⟨{1, 3, 5}, by decide, h⟩
    · exact ⟨{1, 4, 5}, by decide, h⟩
    · exact ⟨{2, 3, 4}, by decide, h⟩
    · exact ⟨{2, 3, 5}, by decide, h⟩
    · exact ⟨{2, 4, 5}, by decide, h⟩
    · exact ⟨{3, 4, 5}, by decide, h⟩

/-- The plane branch of the U(3,6) tight-space dichotomy always supplies a
strictly dominating free pair on the whole tight plane. -/
theorem exists_strict_freePair_on_planeBranch
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ firstDir secondDir : Fin 3 -> ℝ,
      ∃ hfirstUnit : firstDir ⬝ᵥ firstDir = 1,
      ∃ hsecondUnit : secondDir ⬝ᵥ secondDir = 1,
      ∃ horthogonal : firstDir ⬝ᵥ secondDir = 0,
        IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) firstDir
          ∧ IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) secondDir
          ∧ ∃ selected : Finset (Fin 6), selected.card = 2
          ∧ selected ⊆ ({3, 4, 5} : Finset (Fin 6))
          ∧ (subsetSum
              (planarCompressionDesign design firstDir secondDir
                hfirstUnit hsecondUnit horthogonal) selected
              - (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
  obtain ⟨firstDir, secondDir, hfirstUnit, hsecondUnit, horthogonal,
    hfirstTight, hsecondTight⟩ :=
    exists_orthonormal_tightPair_of_hasFreeTightDirection design hdominates hfree
  refine ⟨firstDir, secondDir, hfirstUnit, hsecondUnit, horthogonal,
    hfirstTight, hsecondTight, ?_⟩
  exact exists_strict_freePair_on_tightPlane design firstDir secondDir hfirstUnit
    hsecondUnit horthogonal hdominates hfirstTight hsecondTight

/-- The plane branch produces the exact `pairPlaneStrict` interface consumed by
`Gtz.det_gap_nonpos_of_isTie_of_pairPlaneStrict`, with both labels in the free triple. -/
theorem exists_free_pairPlaneStrict_of_planeBranch
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ (pOne pTwo axis : Fin 3 -> ℝ) (strongLabel otherLabel : Fin 6),
      pOne ⬝ᵥ pOne = 1
        ∧ pTwo ⬝ᵥ pTwo = 1
        ∧ axis ⬝ᵥ axis = 1
        ∧ pOne ⬝ᵥ pTwo = 0
        ∧ pOne ⬝ᵥ axis = 0
        ∧ pTwo ⬝ᵥ axis = 0
        ∧ strongLabel ≠ otherLabel
        ∧ strongLabel ∈ ({3, 4, 5} : Finset (Fin 6))
        ∧ otherLabel ∈ ({3, 4, 5} : Finset (Fin 6))
        ∧ (∀ planar : Fin 3 -> ℝ, planar ⬝ᵥ axis = 0 -> planar ≠ 0 ->
          planar ⬝ᵥ planar
            < (design.atom strongLabel ⬝ᵥ planar) ^ 2
              + (design.atom otherLabel ⬝ᵥ planar) ^ 2) := by
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hfirstTight, hsecondTight⟩ :=
    exists_orthonormal_tightPair_of_hasFreeTightDirection design hdominates hfree
  obtain ⟨selected, hselectedCard, hselectedFree, hselectedPosDef⟩ :=
    exists_strict_freePair_on_tightPlane design pOne pTwo hOneOne hTwoTwo hOneTwo
      hdominates hfirstTight hsecondTight
  obtain ⟨strongLabel, otherLabel, hlabelNe, hselectedEq⟩ :=
    Finset.card_eq_two.mp hselectedCard
  let axis := crossProduct pOne pTwo
  have hOneAxis : pOne ⬝ᵥ axis = 0 := by
    exact planarCross_probe_dot pOne pTwo
  have hTwoAxis : pTwo ⬝ᵥ axis = 0 := by
    exact planarCross_seed_dot pOne pTwo
  have hAxisAxis : axis ⬝ᵥ axis = 1 := by
    change crossProduct pOne pTwo ⬝ᵥ crossProduct pOne pTwo = 1
    rw [planarCross_self_dot, hOneOne, hTwoTwo, hOneTwo]
    norm_num
  have hstrongFree : strongLabel ∈ ({3, 4, 5} : Finset (Fin 6)) := by
    apply hselectedFree
    rw [hselectedEq]
    simp
  have hotherFree : otherLabel ∈ ({3, 4, 5} : Finset (Fin 6)) := by
    apply hselectedFree
    rw [hselectedEq]
    simp
  refine ⟨pOne, pTwo, axis, strongLabel, otherLabel, hOneOne, hTwoTwo, hAxisAxis,
    hOneTwo, hOneAxis, hTwoAxis, hlabelNe, hstrongFree, hotherFree, ?_⟩
  intro planar hplanarPerp hplanarNe
  have hexpandPlanar := orthonormalFrame_expansion hOneOne hTwoTwo hAxisAxis hOneTwo
    hOneAxis hTwoAxis planar
  rw [hplanarPerp, zero_smul, add_zero] at hexpandPlanar
  let companion := planarCompressionDesign design pOne pTwo hOneOne hTwoTwo hOneTwo
  let testVec : Fin 2 -> ℝ := ![planar ⬝ᵥ pOne, planar ⬝ᵥ pTwo]
  have htestNe : testVec ≠ 0 := by
    intro hzero
    have hcoordOne : planar ⬝ᵥ pOne = 0 := by
      have hcomponent := congrFun hzero 0
      simpa [testVec] using hcomponent
    have hcoordTwo : planar ⬝ᵥ pTwo = 0 := by
      have hcomponent := congrFun hzero 1
      simpa [testVec] using hcomponent
    rw [hcoordOne, hcoordTwo, zero_smul, zero_smul, zero_add] at hexpandPlanar
    exact hplanarNe hexpandPlanar
  have hquad := quadForm_gt_of_posDef_pair companion selected hselectedPosDef testVec htestNe
  rw [hselectedEq, Finset.sum_pair hlabelNe] at hquad
  have hatomPairing : ∀ label : Fin 6,
      companion.atom label ⬝ᵥ testVec = design.atom label ⬝ᵥ planar := by
    intro label
    conv_rhs => rw [hexpandPlanar]
    change (planarCompressionDesign design pOne pTwo hOneOne hTwoTwo hOneTwo).atom label
        ⬝ᵥ testVec = _
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul,
      planarCompressionDesign_atom]
    simp only [testVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul]
    ring
  have hbilinear : planar ⬝ᵥ planar
      = (planar ⬝ᵥ pOne) * (planar ⬝ᵥ pOne)
        + (planar ⬝ᵥ pTwo) * (planar ⬝ᵥ pTwo) := by
    rw [dotProduct_eq_frameCoordinateSum hOneOne hTwoTwo hAxisAxis hOneTwo
      hOneAxis hTwoAxis planar planar, hplanarPerp]
    ring
  rw [hatomPairing, hatomPairing] at hquad
  rw [hbilinear]
  simpa [testVec, dotProduct, Fin.sum_univ_two, pow_two] using hquad

set_option linter.unusedVariables false in
/-- Under a hypothetical tie, the free pair supplied by the plane branch lands
directly in the repository's pair-determinant budget. -/
theorem exists_free_pairBudget_nonpos_of_planeBranch_tie
    (design : WeightedDesign 6 3) (htie : IsTie design)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ (pOne pTwo axis : Fin 3 -> ℝ) (strongLabel otherLabel : Fin 6),
      strongLabel ∈ ({3, 4, 5} : Finset (Fin 6))
        ∧ otherLabel ∈ ({3, 4, 5} : Finset (Fin 6))
        ∧ strongLabel ≠ otherLabel
        ∧ (∀ planar : Fin 3 -> ℝ, planar ⬝ᵥ axis = 0 -> planar ≠ 0 ->
          planar ⬝ᵥ planar
            < (design.atom strongLabel ⬝ᵥ planar) ^ 2
              + (design.atom otherLabel ⬝ᵥ planar) ^ 2)
        ∧ ∑ thirdLabel ∈ ({strongLabel, otherLabel} : Finset (Fin 6))ᶜ,
            design.weight thirdLabel
              * (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det ≤ 0 := by
  obtain ⟨pOne, pTwo, axis, strongLabel, otherLabel, hOneOne, hTwoTwo, hAxisAxis,
    hOneTwo, hOneAxis, hTwoAxis, hlabelNe, hstrongFree, hotherFree, hpairStrict⟩ :=
    exists_free_pairPlaneStrict_of_planeBranch design hdominates hfree
  refine ⟨pOne, pTwo, axis, strongLabel, otherLabel, hstrongFree, hotherFree,
    hlabelNe, hpairStrict, ?_⟩
  exact pairBudget_nonpos_of_isTie design htie hOneOne hTwoTwo hAxisAxis hOneTwo
    hOneAxis hTwoAxis hlabelNe hpairStrict

/-! ## Exact branch form of the U(3,6) frontier

The skeleton obligation quantifies a particular nonzero tight direction.  The
landed tight-space dichotomy says that its kernel is either that single line or
has the full freedom used above.  The following two propositions isolate those
branches without changing the obligation. -/

/-- A semidefinite gap whose tight space is exactly one line is strictly
positive on every nonzero vector orthogonal to that line.  This is the
coordinate-free `rank B = 2` fact needed by the tight-normal swap criteria. -/
theorem dominationGap_form_pos_of_hasTightLineAt
    {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (tightDir probe : Fin rank → ℝ)
    (hdominates : Dominates design selected) (htightNe : tightDir ≠ 0)
    (hline : HasTightLineAt design selected tightDir)
    (hprobePerp : probe ⬝ᵥ tightDir = 0) (hprobeNe : probe ≠ 0) :
    0 < probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) := by
  have hnonneg :
      0 ≤ probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) := by
    have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    simpa only [star_trivial] using hform
  apply lt_of_le_of_ne hnonneg
  intro hzeroReverse
  have hzero :
      probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) = 0 :=
    hzeroReverse.symm
  obtain ⟨ratio, hprobe⟩ := hline probe hzero
  have htightNormPos : 0 < tightDir ⬝ᵥ tightDir := dotProduct_self_pos htightNe
  have hratio : ratio = 0 := by
    rw [hprobe, smul_dotProduct, smul_eq_mul] at hprobePerp
    nlinarith
  apply hprobeNe
  rw [hprobe, hratio, zero_smul]

/-- The unresolved U(3,6) statement restricted to a one-dimensional tight
space through the supplied direction. -/
def UThreeSixTightLineBranch : Prop :=
  ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    tightDir ≠ 0 →
    IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir →
    HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - 1).PosDef

/-- The plane branch in its exact finite form: after the base and all one-slot
swaps are excluded, one of the remaining ten triples must be strict. -/
def UThreeSixPlaneTenCandidateBranch : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6)) →
    PlaneBranchTenCandidate design

/-- **Exact U(3,6) frontier split.**  The skeleton proposition is equivalent
to the conjunction of the tight-line problem and the explicit ten-candidate
plane problem.  The reverse implication spends the repository's exhaustive
tight-space dichotomy; the forward implication merely specializes the original
statement. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_iff_tightSpaceBranches :
    BaseTripleTightLineFreeOffConicWeakToStrict ↔
      UThreeSixTightLineBranch ∧ UThreeSixPlaneTenCandidateBranch := by
  constructor
  · intro hbase
    constructor
    · intro design tightDir hlineFree hoffConic hdominates htightNe htight hline
      exact hbase design tightDir hlineFree hoffConic hdominates htightNe htight
    · intro design hlineFree hoffConic hdominates hfree
      obtain ⟨freeDir, hfreeNe, hfreeTight, _⟩ := hfree 0
      apply (exists_posDef_cardThree_iff_planeBranchTenCandidate design
        hdominates hfree).mp
      exact hbase design freeDir hlineFree hoffConic hdominates hfreeNe hfreeTight
  · rintro ⟨hlineBranch, hplaneBranch⟩
    intro design tightDir hlineFree hoffConic hdominates htightNe htight
    rcases uThreeSix_baseTripleTightSpace_dichotomy design hoffConic hdominates
      htightNe htight with hline | ⟨hfree, _⟩
    · exact hlineBranch design tightDir hlineFree hoffConic hdominates htightNe
        htight hline
    · apply (exists_posDef_cardThree_iff_planeBranchTenCandidate design
        hdominates hfree).mpr
      exact hplaneBranch design hlineFree hoffConic hdominates hfree

end Gtz

import Gtz.Design.StratumEmptinessLedger
import Gtz.Design.SphereExistence
import Gtz.Design.TightLineBranchLivePairBridge
import Gtz.Reduction.TrichotomyLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! # Two-light-atom deflation

The weak light-atom transport in `Gtz.dominating_of_light_atom` loses strictness
only because the smaller theorem supplies a positive-semidefinite gap.  If the
gap in the deflated design is already positive definite, its pullback remains
positive definite even when the dropped atom has leverage exactly one: the
strict transported summand is added to the positive-semidefinite light-atom
complement.
-/

/-- A positive-definite gap in the deflated design pulls back strictly through
a light atom. -/
theorem posDef_image_of_deflated_posDef_of_light
    (D : WeightedDesign (m + 1) k) (dropLabel : Fin (m + 1))
    (whitener : Matrix (Fin k) (Fin k) ℝ)
    (hSurvivingMass : 0 < 1 - D.weight dropLabel)
    (hWhitenerUnit : IsUnit whitener.det)
    (hWhitens : whitenerᵀ
        * (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))
        * whitener = 1)
    (deflatedSubset : Finset (Fin m))
    (hDeflatedPosDef :
      (subsetSum
          (deflatedDesign D dropLabel whitener hSurvivingMass hWhitens)
          deflatedSubset - 1).PosDef)
    (hLight : leverageOf (D.atom dropLabel) ≤ 1) :
    (subsetSum D (deflatedSubset.image dropLabel.succAbove) - 1).PosDef := by
  have hEmbeddingInjective : Function.Injective dropLabel.succAbove :=
    Fin.succAbove_right_injective
  have hPivotSymmetric :
      (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))ᵀ
        = 1 - D.weight dropLabel • atomMatrix (D.atom dropLabel) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom dropLabel)).1]
  have hScaledSum :
      ∑ survivor ∈ deflatedSubset,
          atomMatrix (Real.sqrt (1 - D.weight dropLabel)
            • (whitenerᵀ *ᵥ D.atom (dropLabel.succAbove survivor)))
        = whitenerᵀ * (((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (deflatedSubset.image dropLabel.succAbove)) * whitener := by
    rw [subsetSum, Finset.sum_image fun a _ b _ hab => hEmbeddingInjective hab,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun survivor _ => by
      rw [atomMatrix_smul, Real.sq_sqrt hSurvivingMass.le,
        transpose_mul_atomMatrix_mul]
  have hShiftedSymmetric :
      ((((1 : ℝ) - D.weight dropLabel)
          • subsetSum D (deflatedSubset.image dropLabel.succAbove))
          - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel)))ᵀ
        = (((1 : ℝ) - D.weight dropLabel)
          • subsetSum D (deflatedSubset.image dropLabel.succAbove))
          - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel)) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, subsetSum_transpose,
      hPivotSymmetric]
  have hShiftedPosDef :
      ((((1 : ℝ) - D.weight dropLabel)
          • subsetSum D (deflatedSubset.image dropLabel.succAbove))
          - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))).PosDef := by
    refine (posDef_congr_right hShiftedSymmetric hWhitenerUnit).mpr ?_
    have hExpand :
        whitenerᵀ * ((((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (deflatedSubset.image dropLabel.succAbove))
            - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))) * whitener
          = (∑ survivor ∈ deflatedSubset,
              atomMatrix (Real.sqrt (1 - D.weight dropLabel)
                • (whitenerᵀ *ᵥ D.atom (dropLabel.succAbove survivor)))) - 1 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hWhitens, ← hScaledSum]
    rw [hExpand]
    exact hDeflatedPosDef
  have hLightComplement :
      ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel)).PosSemidef :=
    (posSemidef_sub_vecMulVec_iff 1 Matrix.PosDef.one (D.atom dropLabel)).mpr
      (by
        rw [inv_one, Matrix.one_mulVec, dotProduct_self_eq_sum_sq]
        exact hLight)
  have hWeightPos := D.weight_pos dropLabel
  have hFinal :
      subsetSum D (deflatedSubset.image dropLabel.succAbove) - 1
        = ((1 : ℝ) - D.weight dropLabel)⁻¹
          • (((((1 : ℝ) - D.weight dropLabel)
              • subsetSum D (deflatedSubset.image dropLabel.succAbove))
              - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel)))
            + D.weight dropLabel
              • (1 - atomMatrix (D.atom dropLabel))) := by
    have hInner :
        ((((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (deflatedSubset.image dropLabel.succAbove))
            - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel)))
            + D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))
          = ((1 : ℝ) - D.weight dropLabel)
            • (subsetSum D (deflatedSubset.image dropLabel.succAbove) - 1) := by
      module
    rw [hInner, smul_smul, inv_mul_cancel₀ hSurvivingMass.ne', one_smul]
  rw [hFinal]
  exact (hShiftedPosDef.add_posSemidef
    (hLightComplement.smul hWeightPos.le)).smul (inv_pos.mpr hSurvivingMass)

/-- After deflating one light atom, every other light atom not parallel to it
becomes strictly light.  This is the division-free Sherman--Morrison
calculation; the strictness is exactly the strict Cauchy--Schwarz slack of the
two original atoms. -/
theorem leverage_deflatedDesign_lt_one_of_two_light
    (D : WeightedDesign (m + 1) k) (dropLabel : Fin (m + 1))
    (whitener : Matrix (Fin k) (Fin k) ℝ)
    (hSurvivingMass : 0 < 1 - D.weight dropLabel)
    (hWhitens : whitenerᵀ
        * (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))
        * whitener = 1)
    (survivor : Fin m)
    (hDropLight : leverageOf (D.atom dropLabel) ≤ 1)
    (hSurvivorLight : leverageOf (D.atom (dropLabel.succAbove survivor)) ≤ 1)
    (hStrictCauchy :
      (D.atom dropLabel ⬝ᵥ D.atom (dropLabel.succAbove survivor)) ^ 2
        < leverageOf (D.atom dropLabel)
          * leverageOf (D.atom (dropLabel.succAbove survivor))) :
    leverageOf
        ((deflatedDesign D dropLabel whitener hSurvivingMass hWhitens).atom survivor)
      < 1 := by
  let pivotForm : Matrix (Fin k) (Fin k) ℝ :=
    1 - D.weight dropLabel • atomMatrix (D.atom dropLabel)
  let inverseForm : Matrix (Fin k) (Fin k) ℝ :=
    whitener * whitenerᵀ
  let dropVec : Fin k → ℝ := D.atom dropLabel
  let survivorVec : Fin k → ℝ := D.atom (dropLabel.succAbove survivor)
  let dropLeverage : ℝ := leverageOf dropVec
  let survivorLeverage : ℝ := leverageOf survivorVec
  let pairing : ℝ := dropVec ⬝ᵥ survivorVec
  let mixedReading : ℝ := dropVec ⬝ᵥ (inverseForm *ᵥ survivorVec)
  let whitenedLeverage : ℝ := survivorVec ⬝ᵥ (inverseForm *ᵥ survivorVec)
  have hInverse : pivotForm * inverseForm = 1 := by
    have hReverse : whitener * (whitenerᵀ * pivotForm) = 1 := by
      apply mul_eq_one_comm.mp
      simpa only [pivotForm, Matrix.mul_assoc] using hWhitens
    apply mul_eq_one_comm.mpr
    simpa only [inverseForm, Matrix.mul_assoc] using hReverse
  have hVector :
      inverseForm *ᵥ survivorVec
          - D.weight dropLabel •
            (mixedReading • dropVec)
        = survivorVec := by
    have hApplied := congrArg (fun matrix => matrix *ᵥ survivorVec) hInverse
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at hApplied
    simpa only [pivotForm, inverseForm, dropVec, survivorVec, mixedReading,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, atomMatrix,
      vecMulVec_mulVec_eq, smul_smul] using hApplied
  have hMixed :
      (1 - D.weight dropLabel * dropLeverage) * mixedReading = pairing := by
    have hRead := congrArg (fun vector => dropVec ⬝ᵥ vector) hVector
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at hRead
    rw [← leverageOf_eq_dotProduct] at hRead
    dsimp only [dropLeverage, pairing]
    linear_combination hRead
  have hWhitened :
      whitenedLeverage - D.weight dropLabel * pairing * mixedReading
        = survivorLeverage := by
    have hRead := congrArg (fun vector => survivorVec ⬝ᵥ vector) hVector
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at hRead
    rw [dotProduct_comm survivorVec dropVec, ← leverageOf_eq_dotProduct] at hRead
    dsimp only [whitenedLeverage, pairing, survivorLeverage]
    linear_combination hRead
  have hExact :
      (1 - D.weight dropLabel * dropLeverage) * whitenedLeverage
        = (1 - D.weight dropLabel * dropLeverage) * survivorLeverage
          + D.weight dropLabel * pairing ^ 2 := by
    linear_combination
      (1 - D.weight dropLabel * dropLeverage) * hWhitened
        + D.weight dropLabel * pairing * hMixed
  have hWeightPos := D.weight_pos dropLabel
  have hDropLight' : dropLeverage ≤ 1 := by
    simpa only [dropLeverage, dropVec] using hDropLight
  have hSurvivorLight' : survivorLeverage ≤ 1 := by
    simpa only [survivorLeverage, survivorVec] using hSurvivorLight
  have hDropNonneg : 0 ≤ dropLeverage := by
    dsimp only [dropLeverage, dropVec]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hDenomPos : 0 < 1 - D.weight dropLabel * dropLeverage := by
    have hWeightLtOne : D.weight dropLabel < 1 :=
      weight_lt_one D (by have := survivor.isLt; omega) dropLabel
    nlinarith [mul_le_mul_of_nonneg_left hDropLight' hWeightPos.le]
  have hWhitenedNonneg : 0 ≤ whitenedLeverage := by
    have hNorm :
        (whitenerᵀ *ᵥ survivorVec) ⬝ᵥ (whitenerᵀ *ᵥ survivorVec)
          = whitenedLeverage := by
      calc
        (whitenerᵀ *ᵥ survivorVec) ⬝ᵥ (whitenerᵀ *ᵥ survivorVec)
            = survivorVec ⬝ᵥ
                (whitener *ᵥ (whitenerᵀ *ᵥ survivorVec)) :=
              dotProduct_mulVec_transpose whitener survivorVec
                (whitenerᵀ *ᵥ survivorVec)
        _ = whitenedLeverage := by
              rw [Matrix.mulVec_mulVec]
    rw [← hNorm]
    exact dotProduct_self_nonneg _
  have hDenomTimesWhitenedLtOne :
      (1 - D.weight dropLabel * dropLeverage) * whitenedLeverage < 1 := by
    have hStrictWeighted :
        0 < D.weight dropLabel
          * (dropLeverage * survivorLeverage - pairing ^ 2) := by
      apply mul_pos hWeightPos
      dsimp only [dropLeverage, survivorLeverage, pairing, dropVec, survivorVec]
        at hStrictCauchy ⊢
      linarith
    nlinarith [hExact, hSurvivorLight']
  have hSurvivingMassLeDenom :
      1 - D.weight dropLabel
        ≤ 1 - D.weight dropLabel * dropLeverage := by
    nlinarith [hWeightPos, hDropLight']
  have hRaw :
      (1 - D.weight dropLabel) * whitenedLeverage < 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hSurvivingMassLeDenom hWhitenedNonneg]
  change leverageOf
      (Real.sqrt (1 - D.weight dropLabel)
        • (whitenerᵀ *ᵥ survivorVec)) < 1
  rw [leverageOf_eq_dotProduct, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul]
  have hNorm :
      (whitenerᵀ *ᵥ survivorVec) ⬝ᵥ (whitenerᵀ *ᵥ survivorVec)
        = whitenedLeverage := by
    calc
      (whitenerᵀ *ᵥ survivorVec) ⬝ᵥ (whitenerᵀ *ᵥ survivorVec)
          = survivorVec ⬝ᵥ (whitener *ᵥ (whitenerᵀ *ᵥ survivorVec)) :=
            dotProduct_mulVec_transpose whitener survivorVec
              (whitenerᵀ *ᵥ survivorVec)
      _ = whitenedLeverage := by
            rw [Matrix.mulVec_mulVec]
  rw [hNorm]
  calc
    Real.sqrt (1 - D.weight dropLabel)
          * (Real.sqrt (1 - D.weight dropLabel) * whitenedLeverage)
        = (1 - D.weight dropLabel) * whitenedLeverage := by
            rw [← mul_assoc, Real.mul_self_sqrt hSurvivingMass.le]
    _ < 1 := hRaw

/-! ## The two-for-one consequence at `(6,3)` -/

/-- Two distinct light atoms with strict Cauchy--Schwarz slack force a strict
card-three subset avoiding BOTH atoms.  Deflate the first atom weakly, observe
that the second becomes strictly light, and invoke the proved `(4,3) -> (5,3)`
strict-light rung before pulling the resulting gap back. -/
theorem exists_posDef_cardThree_avoiding_two_of_two_light_of_strictCauchy
    (D : WeightedDesign 6 3) (first second : Fin 6) (hDistinct : first ≠ second)
    (hFirstLight : leverageOf (D.atom first) ≤ 1)
    (hSecondLight : leverageOf (D.atom second) ≤ 1)
    (hStrictCauchy :
      (D.atom first ⬝ᵥ D.atom second) ^ 2
        < leverageOf (D.atom first) * leverageOf (D.atom second)) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ first ∉ selected ∧
      second ∉ selected ∧ (subsetSum D selected - 1).PosDef := by
  have hWeightPos := D.weight_pos first
  have hWeightLtOne : D.weight first < 1 := weight_lt_one D (by norm_num) first
  have hSurvivingMass : 0 < 1 - D.weight first := by linarith
  have hFirstNonneg : 0 ≤ leverageOf (D.atom first) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hShare : D.weight first * leverageOf (D.atom first) < 1 := by
    have hProductLeWeight :
        D.weight first * leverageOf (D.atom first) ≤ D.weight first := by
      nlinarith
    linarith
  have hPivotPosDef :
      ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - D.weight first • atomMatrix (D.atom first)).PosDef :=
    posDef_one_sub_smul_atomMatrix_of_share_lt_one hWeightPos hShare
  obtain ⟨whitener, hWhitenerUnit, hWhitens⟩ :=
    exists_congruence_to_one hPivotPosDef
  obtain ⟨survivor, hSurvivor⟩ := Fin.exists_succAbove_eq hDistinct.symm
  have hDeflatedSecondLight :
      leverageOf
          ((deflatedDesign D first whitener hSurvivingMass hWhitens).atom survivor)
        < 1 := by
    apply leverage_deflatedDesign_lt_one_of_two_light D first whitener
      hSurvivingMass hWhitens survivor hFirstLight
    · simpa only [hSurvivor] using hSecondLight
    · simpa only [hSurvivor] using hStrictCauchy
  obtain ⟨deflatedSubset, hCard, hAvoidsSurvivor, hDeflatedPosDef⟩ :=
    exists_posDef_of_lightAtom
      (deflatedDesign D first whitener hSurvivingMass hWhitens)
      (m := 4) (k := 3) (by norm_num)
      (gtzWeighted_of_le_five 4 3 (by norm_num) (by norm_num)) survivor
      hDeflatedSecondLight
  let selected : Finset (Fin 6) := deflatedSubset.image first.succAbove
  have hEmbeddingInjective : Function.Injective first.succAbove :=
    Fin.succAbove_right_injective
  refine ⟨selected, ?_, ?_, ?_, ?_⟩
  · dsimp only [selected]
    rw [Finset.card_image_of_injective _ hEmbeddingInjective, hCard]
  · dsimp only [selected]
    intro hMem
    obtain ⟨index, _, hIndex⟩ := Finset.mem_image.mp hMem
    exact Fin.succAbove_ne first index hIndex
  · dsimp only [selected]
    intro hMem
    obtain ⟨index, hIndexMem, hIndex⟩ := Finset.mem_image.mp hMem
    have hIndexEq : index = survivor :=
      hEmbeddingInjective (hIndex.trans hSurvivor.symm)
    exact hAvoidsSurvivor (hIndexEq ▸ hIndexMem)
  · dsimp only [selected]
    exact posDef_image_of_deflated_posDef_of_light D first whitener
      hSurvivingMass hWhitenerUnit hWhitens deflatedSubset hDeflatedPosDef hFirstLight

/-- In a simple rank-three design, distinct light atoms satisfy the strict
Cauchy--Schwarz hypothesis of the two-for-one deflation theorem. -/
theorem exists_posDef_cardThree_avoiding_two_of_two_light_of_not_hasParallelPair
    (D : WeightedDesign 6 3) (hSimple : ¬ HasParallelPair D)
    (first second : Fin 6) (hDistinct : first ≠ second)
    (hFirstLight : leverageOf (D.atom first) ≤ 1)
    (hSecondLight : leverageOf (D.atom second) ≤ 1) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ first ∉ selected ∧
      second ∉ selected ∧ (subsetSum D selected - 1).PosDef := by
  have hCross : crossProduct (D.atom first) (D.atom second) ≠ 0 :=
    crossProduct_atom_ne_zero_of_not_hasParallelPair D hSimple hDistinct
  have hStrict :=
    (crossProduct_ne_zero_iff_sq_lt_mul (D.atom first) (D.atom second)).mp hCross
  rw [← leverageOf_eq_dotProduct, ← leverageOf_eq_dotProduct] at hStrict
  exact exists_posDef_cardThree_avoiding_two_of_two_light_of_strictCauchy D
    first second hDistinct hFirstLight hSecondLight hStrict

/-- A simple `(6,3)` tie has at most one atom on the leverage-one boundary. -/
theorem leverage_eq_one_unique_of_isTie_of_not_hasParallelPair
    (D : WeightedDesign 6 3) (hTie : IsTie D) (hSimple : ¬ HasParallelPair D)
    (first second : Fin 6)
    (hFirst : leverageOf (D.atom first) = 1)
    (hSecond : leverageOf (D.atom second) = 1) : first = second := by
  by_contra hDistinct
  obtain ⟨selected, hCard, _, _, hPosDef⟩ :=
    exists_posDef_cardThree_avoiding_two_of_two_light_of_not_hasParallelPair D
      hSimple first second hDistinct hFirst.le hSecond.le
  exact hTie.2 selected hCard hPosDef

/-- The existing all-heavy/boundary dichotomy is exclusive and the boundary
label is unique on the primitive stratum. -/
theorem allHeavy_or_existsUnique_leverage_eq_one_of_isTie_of_not_hasParallelPair
    (D : WeightedDesign 6 3) (hTie : IsTie D) (hSimple : ¬ HasParallelPair D) :
    AllHeavy D ∨ ∃! label : Fin 6, leverageOf (D.atom label) = 1 := by
  rcases allHeavy_or_exists_leverage_eq_one_of_isTie_sixThree D hTie with
    hAllHeavy | ⟨label, hLabel⟩
  · exact Or.inl hAllHeavy
  · exact Or.inr ⟨label, hLabel, fun other hOther =>
      leverage_eq_one_unique_of_isTie_of_not_hasParallelPair D hTie hSimple
        other label hOther hLabel⟩

/-! ## The tight-line hinge consequence -/

/-- A card-three subset avoiding two distinct free labels is either the base
triple or a one-slot swap.  This is a closed 64-subset fact; `decide` produces a
kernel-checked proof and introduces no native-code axiom. -/
theorem cardThree_avoiding_two_free_eq_base_or_oneSlot :
    ∀ (first second : Fin 3) (selected : Finset (Fin 6)),
      first ≠ second → selected.card = 3 →
      freeThreeLabel first ∉ selected → freeThreeLabel second ∉ selected →
      selected = ({0, 1, 2} : Finset (Fin 6)) ∨
        ∃ swapOut ∈ ({0, 1, 2} : Finset (Fin 6)),
          ∃ swapIn ∉ ({0, 1, 2} : Finset (Fin 6)),
            selected = insert swapIn
              ((({0, 1, 2} : Finset (Fin 6))).erase swapOut) := by
  decide

/-- **The no-one-slot hinge, proved.**  At a simple tight-line configuration
with no strict one-slot swap, at most one of the three free atoms has leverage
at most one.

The proof is structural rather than an average: two such atoms deflate to a
strict triple avoiding both; the finite classification says that triple is the
tight base or a forbidden one-slot swap. -/
theorem atMostOne_light_free_of_tightLine_of_no_oneSlot
    (D : WeightedDesign 6 3) (hSimple : ¬ HasParallelPair D)
    {tightDir : Fin 3 → ℝ} (hTightNe : tightDir ≠ 0)
    (hTight : IsTightDirectionOf D ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hNoOneSlot : ¬ TightLineOneSlotFamily D) :
    ∀ first second : Fin 3,
      leverageOf (D.atom (freeThreeLabel first)) ≤ 1 →
      leverageOf (D.atom (freeThreeLabel second)) ≤ 1 → first = second := by
  intro first second hFirstLight hSecondLight
  by_contra hDistinct
  have hLabelDistinct : freeThreeLabel first ≠ freeThreeLabel second :=
    fun hEqual => hDistinct (freeThreeLabel_injective hEqual)
  obtain ⟨selected, hCard, hAvoidsFirst, hAvoidsSecond, hPosDef⟩ :=
    exists_posDef_cardThree_avoiding_two_of_two_light_of_not_hasParallelPair D
      hSimple (freeThreeLabel first) (freeThreeLabel second) hLabelDistinct
      hFirstLight hSecondLight
  rcases cardThree_avoiding_two_free_eq_base_or_oneSlot first second selected
      hDistinct hCard hAvoidsFirst hAvoidsSecond with hBase | hOneSlot
  · have hBaseNot :
        ¬ (subsetSum D ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
      not_posDef_baseTripleGap_of_tightDirection D hTightNe hTight
    exact hBaseNot (hBase ▸ hPosDef)
  · obtain ⟨swapOut, hSwapOut, swapIn, hSwapIn, hSelected⟩ := hOneSlot
    apply hNoOneSlot
    exact ⟨swapOut, hSwapOut, swapIn, hSwapIn, hSelected ▸ hPosDef⟩

/-- The form consumed by the `U(3,6)` line branch: its empty line-family pattern
is general position, hence forbids parallel pairs automatically. -/
theorem atMostOne_light_free_of_uThreeSix_tightLine_of_no_oneSlot
    (D : WeightedDesign 6 3)
    (hLineFree :
      HasLinePattern D (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ} (hTightNe : tightDir ≠ 0)
    (hTight : IsTightDirectionOf D ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hNoOneSlot : ¬ TightLineOneSlotFamily D) :
    ∀ first second : Fin 3,
      leverageOf (D.atom (freeThreeLabel first)) ≤ 1 →
      leverageOf (D.atom (freeThreeLabel second)) ≤ 1 → first = second := by
  have hPrimitive : IsPrimitiveDesign D :=
    isPrimitiveDesign_of_hasLinePattern (by decide) D hLineFree
  exact atMostOne_light_free_of_tightLine_of_no_oneSlot D
    ((isPrimitiveDesign_iff_not_hasParallelPair D).mp hPrimitive)
    hTightNe hTight hNoOneSlot

/-- The exact pairwise-heaviness shape consumed by
`exists_live_freePair_of_atMostOneNonheavy_of_rowAggregate_pos`. -/
theorem pairwise_free_heavy_of_uThreeSix_tightLine_of_no_oneSlot
    (D : WeightedDesign 6 3)
    (hLineFree :
      HasLinePattern D (lineFamilyPattern ([] : List (List (Fin 6)))))
    {tightDir : Fin 3 → ℝ} (hTightNe : tightDir ≠ 0)
    (hTight : IsTightDirectionOf D ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hNoOneSlot : ¬ TightLineOneSlotFamily D) :
    ∀ first second : Fin 3, first ≠ second →
      0 < gapExcessOf D (freeThreeLabel first) ∨
        0 < gapExcessOf D (freeThreeLabel second) := by
  have hAtMostOne :=
    atMostOne_light_free_of_uThreeSix_tightLine_of_no_oneSlot D hLineFree
      hTightNe hTight hNoOneSlot
  intro first second hDistinct
  by_cases hFirstLight : leverageOf (D.atom (freeThreeLabel first)) ≤ 1
  · right
    simp only [gapExcessOf]
    have hSecondHeavy : 1 < leverageOf (D.atom (freeThreeLabel second)) := by
      by_contra hSecondLight
      exact hDistinct (hAtMostOne first second hFirstLight (not_lt.mp hSecondLight))
    linarith
  · left
    simp only [gapExcessOf]
    linarith

end Gtz

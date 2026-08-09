import Gtz.Design.UThreeSixDisjunction
import Gtz.Design.TightSwapObstructions
import Gtz.Design.InsertPlaneCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- A tight weak dominator containing at least two atoms forces some atom in its
complement to be strictly heavy. -/
theorem exists_complementAtom_strictlyHeavy_of_tightDirection
    (design : WeightedDesign m k) (selected : Finset (Fin m))
    (hcard : 2 ≤ selected.card) (tightDir : Fin k → ℝ) (htightNe : tightDir ≠ 0)
    (htight : subsetSum design selected *ᵥ tightDir = tightDir) :
    ∃ outsideLabel ∈ selectedᶜ, 1 < leverageOf (design.atom outsideLabel) := by
  classical
  have hselectedNonempty : selected.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hcard
    simp at hcard
  obtain ⟨maxLabel, hmaxMem, hmax⟩ :=
    Finset.exists_max_image selected design.weight hselectedNonempty
  by_contra hnone
  push Not at hnone
  have htightForm := congrArg (fun vector : Fin k → ℝ => tightDir ⬝ᵥ vector) htight
  rw [dotProduct_subsetSum_mulVec_of_finset] at htightForm
  have hnormPos : 0 < tightDir ⬝ᵥ tightDir := dotProduct_self_pos htightNe
  have hinside :
      ∑ label ∈ selected,
          design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
        ≤ design.weight maxLabel
          * ∑ label ∈ selected, (design.atom label ⬝ᵥ tightDir) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun label hlabel =>
      mul_le_mul_of_nonneg_right (hmax label hlabel) (sq_nonneg _)
  have houtside :
      ∑ label ∈ selectedᶜ,
          design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
        ≤ (∑ label ∈ selectedᶜ, design.weight label)
          * (tightDir ⬝ᵥ tightDir) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun label hlabel => ?_
    have hcauchy :=
      atomOverlap_sq_le_leverage_mul_normSq (design.atom label) tightDir
    have hleverage := hnone label hlabel
    have hnormNonneg : 0 ≤ tightDir ⬝ᵥ tightDir := hnormPos.le
    have hreading : (design.atom label ⬝ᵥ tightDir) ^ 2
        ≤ tightDir ⬝ᵥ tightDir := by
      nlinarith [hcauchy]
    exact mul_le_mul_of_nonneg_left hreading (design.weight_pos label).le
  have hparseval :
      tightDir ⬝ᵥ tightDir
        = (∑ label ∈ selected,
            design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2)
          + ∑ label ∈ selectedᶜ,
            design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2 := by
    rw [dotProduct_self_eq_sum_weight_mul_sq design tightDir]
    exact (Finset.sum_add_sum_compl selected
      (fun label => design.weight label
        * (design.atom label ⬝ᵥ tightDir) ^ 2)).symm
  have hweightSplit :
      (∑ label ∈ selected, design.weight label)
          + ∑ label ∈ selectedᶜ, design.weight label = 1 := by
    rw [Finset.sum_add_sum_compl, design.weight_sum_one]
  have heraseNonempty : (selected.erase maxLabel).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hmaxMem]
    omega
  have heraseWeightPos :
      0 < ∑ label ∈ selected.erase maxLabel, design.weight label :=
    Finset.sum_pos (fun label _ => design.weight_pos label) heraseNonempty
  have hselectedWeightSplit :
      (∑ label ∈ selected.erase maxLabel, design.weight label)
          + design.weight maxLabel
        = ∑ label ∈ selected, design.weight label :=
    Finset.sum_erase_add selected design.weight hmaxMem
  have hselectedWeightGt :
      design.weight maxLabel < ∑ label ∈ selected, design.weight label := by
    linarith
  have hinside' :
      ∑ label ∈ selected,
          design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
        ≤ design.weight maxLabel * (tightDir ⬝ᵥ tightDir) := by
    rw [← htightForm]
    exact hinside
  have htotalUpper :
      tightDir ⬝ᵥ tightDir
        ≤ (design.weight maxLabel
            + ∑ label ∈ selectedᶜ, design.weight label)
          * (tightDir ⬝ᵥ tightDir) := by
    calc
      tightDir ⬝ᵥ tightDir =
          (∑ label ∈ selected,
              design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2)
            + ∑ label ∈ selectedᶜ,
              design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2 := hparseval
      _ ≤ design.weight maxLabel * (tightDir ⬝ᵥ tightDir)
            + (∑ label ∈ selectedᶜ, design.weight label)
              * (tightDir ⬝ᵥ tightDir) := add_le_add hinside' houtside
      _ = _ := by ring
  have hcoefficient :
      design.weight maxLabel
          + ∑ label ∈ selectedᶜ, design.weight label < 1 := by
    linarith
  nlinarith [htotalUpper]

/-- Quantitative complement heaviness. The excess above one is controlled by
the selected weight left after removing its largest member. -/
theorem exists_complementAtom_quantitativelyHeavy_of_tightDirection
    (design : WeightedDesign m k) (selected : Finset (Fin m))
    (hcard : 2 ≤ selected.card) (tightDir : Fin k → ℝ) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design selected - 1) *ᵥ tightDir) = 0) :
    ∃ maxLabel ∈ selected,
      (∀ label ∈ selected, design.weight label ≤ design.weight maxLabel) ∧
      ∃ outsideLabel ∈ selectedᶜ,
        1 - design.weight maxLabel
            ≤ leverageOf (design.atom outsideLabel)
              * (1 - ∑ label ∈ selected, design.weight label) ∧
        1 < leverageOf (design.atom outsideLabel) := by
  classical
  have hselectedNonempty : selected.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hcard
    simp at hcard
  obtain ⟨maxLabel, hmaxMem, hmax⟩ :=
    Finset.exists_max_image selected design.weight hselectedNonempty
  obtain ⟨overLabel, hoverNotMem, hoverReading⟩ :=
    exists_outsideAtom_strictly_overcovers_tightDirection design selected tightDir
      hcard htightNe htight
  have hcomplementNonempty : selectedᶜ.Nonempty :=
    ⟨overLabel, Finset.mem_compl.mpr hoverNotMem⟩
  obtain ⟨outsideLabel, houtsideMem, houtsideMax⟩ :=
    Finset.exists_max_image selectedᶜ
      (fun label => leverageOf (design.atom label)) hcomplementNonempty
  have hnormPos : 0 < tightDir ⬝ᵥ tightDir := dotProduct_self_pos htightNe
  have htightMass := tightDirection_sum_sq_eq design selected tightDir htight
  have hinside :
      ∑ label ∈ selected,
          design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
        ≤ design.weight maxLabel * (tightDir ⬝ᵥ tightDir) := by
    rw [← htightMass, Finset.mul_sum]
    exact Finset.sum_le_sum fun label hlabel =>
      mul_le_mul_of_nonneg_right (hmax label hlabel) (sq_nonneg _)
  have houtside :
      ∑ label ∈ selectedᶜ,
          design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
        ≤ leverageOf (design.atom outsideLabel)
          * (∑ label ∈ selectedᶜ, design.weight label)
          * (tightDir ⬝ᵥ tightDir) := by
    calc
      ∑ label ∈ selectedᶜ,
          design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
        ≤ ∑ label ∈ selectedᶜ,
            design.weight label
              * (leverageOf (design.atom label) * (tightDir ⬝ᵥ tightDir)) := by
          exact Finset.sum_le_sum fun label _ =>
            mul_le_mul_of_nonneg_left
              (atomOverlap_sq_le_leverage_mul_normSq (design.atom label) tightDir)
              (design.weight_pos label).le
      _ ≤ ∑ label ∈ selectedᶜ,
            design.weight label
              * (leverageOf (design.atom outsideLabel) * (tightDir ⬝ᵥ tightDir)) := by
          refine Finset.sum_le_sum fun label hlabel => ?_
          have hnormNonneg : 0 ≤ tightDir ⬝ᵥ tightDir := hnormPos.le
          have hleverage := houtsideMax label hlabel
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hleverage hnormNonneg)
            (design.weight_pos label).le
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hparseval :
      tightDir ⬝ᵥ tightDir
        = (∑ label ∈ selected,
            design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2)
          + ∑ label ∈ selectedᶜ,
            design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2 := by
    rw [dotProduct_self_eq_sum_weight_mul_sq design tightDir]
    exact (Finset.sum_add_sum_compl selected
      (fun label => design.weight label
        * (design.atom label ⬝ᵥ tightDir) ^ 2)).symm
  have hweightSplit :
      (∑ label ∈ selected, design.weight label)
          + ∑ label ∈ selectedᶜ, design.weight label = 1 := by
    rw [Finset.sum_add_sum_compl, design.weight_sum_one]
  have hscaled :
      (1 - design.weight maxLabel) * (tightDir ⬝ᵥ tightDir)
        ≤ (leverageOf (design.atom outsideLabel)
            * (∑ label ∈ selectedᶜ, design.weight label))
          * (tightDir ⬝ᵥ tightDir) := by
    nlinarith [hinside, houtside, hparseval]
  have hquantComplement :
      1 - design.weight maxLabel
        ≤ leverageOf (design.atom outsideLabel)
          * (∑ label ∈ selectedᶜ, design.weight label) :=
    by nlinarith [hscaled]
  have heraseNonempty : (selected.erase maxLabel).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hmaxMem]
    omega
  have heraseWeightPos :
      0 < ∑ label ∈ selected.erase maxLabel, design.weight label :=
    Finset.sum_pos (fun label _ => design.weight_pos label) heraseNonempty
  have hselectedWeightSplit :
      (∑ label ∈ selected.erase maxLabel, design.weight label)
          + design.weight maxLabel
        = ∑ label ∈ selected, design.weight label :=
    Finset.sum_erase_add selected design.weight hmaxMem
  have hcomplementWeightPos :
      0 < ∑ label ∈ selectedᶜ, design.weight label :=
    Finset.sum_pos (fun label _ => design.weight_pos label) hcomplementNonempty
  have houtsideHeavy : 1 < leverageOf (design.atom outsideLabel) := by
    nlinarith [hquantComplement]
  refine ⟨maxLabel, hmaxMem, hmax, outsideLabel, houtsideMem, ?_, houtsideHeavy⟩
  have hcomplementWeight :
      1 - ∑ label ∈ selected, design.weight label
        = ∑ label ∈ selectedᶜ, design.weight label := by
    linarith [hweightSplit]
  rw [hcomplementWeight]
  exact hquantComplement

/-- The collar form: the complement atom's leverage excess pays for all
selected weights except the largest one. -/
theorem exists_complementAtom_leverageExcess_of_tightDirection
    (design : WeightedDesign m k) (selected : Finset (Fin m))
    (hcard : 2 ≤ selected.card) (tightDir : Fin k → ℝ) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design selected - 1) *ᵥ tightDir) = 0) :
    ∃ maxLabel ∈ selected,
      (∀ label ∈ selected, design.weight label ≤ design.weight maxLabel) ∧
      ∃ outsideLabel ∈ selectedᶜ,
        (∑ label ∈ selected, design.weight label) - design.weight maxLabel
            ≤ (leverageOf (design.atom outsideLabel) - 1)
              * (1 - ∑ label ∈ selected, design.weight label) ∧
        1 < leverageOf (design.atom outsideLabel) := by
  obtain ⟨maxLabel, hmaxMem, hmax, outsideLabel, houtsideMem, hquant, hheavy⟩ :=
    exists_complementAtom_quantitativelyHeavy_of_tightDirection design selected
      hcard tightDir htightNe htight
  refine ⟨maxLabel, hmaxMem, hmax, outsideLabel, houtsideMem, ?_, hheavy⟩
  nlinarith [hquant]

/-- Stronger than the leverage estimate: the excess is already visible in the
tight-direction reading, before Cauchy--Schwarz. -/
theorem exists_complementAtom_readingExcess_of_tightDirection
    (design : WeightedDesign m k) (selected : Finset (Fin m))
    (hcard : 2 ≤ selected.card) (tightDir : Fin k → ℝ) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design selected - 1) *ᵥ tightDir) = 0) :
    ∃ maxLabel ∈ selected,
      (∀ label ∈ selected, design.weight label ≤ design.weight maxLabel) ∧
      ∃ outsideLabel ∈ selectedᶜ,
        ((∑ label ∈ selected, design.weight label) - design.weight maxLabel)
              * (tightDir ⬝ᵥ tightDir)
            ≤ ((design.atom outsideLabel ⬝ᵥ tightDir) ^ 2
                - tightDir ⬝ᵥ tightDir)
              * (1 - ∑ label ∈ selected, design.weight label) ∧
        tightDir ⬝ᵥ tightDir
          < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 := by
  classical
  have hselectedNonempty : selected.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hcard
    simp at hcard
  obtain ⟨maxLabel, hmaxMem, hmax⟩ :=
    Finset.exists_max_image selected design.weight hselectedNonempty
  obtain ⟨overLabel, hoverNotMem, hoverReading⟩ :=
    exists_outsideAtom_strictly_overcovers_tightDirection design selected tightDir
      hcard htightNe htight
  have hcomplementNonempty : selectedᶜ.Nonempty :=
    ⟨overLabel, Finset.mem_compl.mpr hoverNotMem⟩
  obtain ⟨outsideLabel, houtsideMem, houtsideMax⟩ :=
    Finset.exists_max_image selectedᶜ
      (fun label => (design.atom label ⬝ᵥ tightDir) ^ 2) hcomplementNonempty
  have hnormPos : 0 < tightDir ⬝ᵥ tightDir := dotProduct_self_pos htightNe
  have htightMass := tightDirection_sum_sq_eq design selected tightDir htight
  have hinside :
      ∑ label ∈ selected,
          design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
        ≤ design.weight maxLabel * (tightDir ⬝ᵥ tightDir) := by
    rw [← htightMass, Finset.mul_sum]
    exact Finset.sum_le_sum fun label hlabel =>
      mul_le_mul_of_nonneg_right (hmax label hlabel) (sq_nonneg _)
  have houtside :
      ∑ label ∈ selectedᶜ,
          design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
        ≤ (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2
          * ∑ label ∈ selectedᶜ, design.weight label := by
    calc
      ∑ label ∈ selectedᶜ,
          design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
        ≤ ∑ label ∈ selectedᶜ,
            design.weight label * (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 := by
          exact Finset.sum_le_sum fun label hlabel =>
            mul_le_mul_of_nonneg_left (houtsideMax label hlabel)
              (design.weight_pos label).le
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hparseval :
      tightDir ⬝ᵥ tightDir
        = (∑ label ∈ selected,
            design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2)
          + ∑ label ∈ selectedᶜ,
            design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2 := by
    rw [dotProduct_self_eq_sum_weight_mul_sq design tightDir]
    exact (Finset.sum_add_sum_compl selected
      (fun label => design.weight label
        * (design.atom label ⬝ᵥ tightDir) ^ 2)).symm
  have hweightSplit :
      (∑ label ∈ selected, design.weight label)
          + ∑ label ∈ selectedᶜ, design.weight label = 1 := by
    rw [Finset.sum_add_sum_compl, design.weight_sum_one]
  have hscaled :
      (1 - design.weight maxLabel) * (tightDir ⬝ᵥ tightDir)
        ≤ (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2
          * ∑ label ∈ selectedᶜ, design.weight label := by
    nlinarith [hinside, houtside, hparseval]
  have hreading : tightDir ⬝ᵥ tightDir
      < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 :=
    lt_of_lt_of_le hoverReading (houtsideMax overLabel (Finset.mem_compl.mpr hoverNotMem))
  refine ⟨maxLabel, hmaxMem, hmax, outsideLabel, houtsideMem, ?_, hreading⟩
  nlinarith [hscaled, hweightSplit]

/-- The exact base-triple specialization consumed by the open U(3,6)
obligation. -/
theorem uThreeSix_exists_complementAtom_leverageExcess
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ
      ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0) :
    ∃ maxLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      (∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.weight label ≤ design.weight maxLabel) ∧
      ∃ outsideLabel ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ,
        (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label)
              - design.weight maxLabel
            ≤ (leverageOf (design.atom outsideLabel) - 1)
              * (1 - ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label) ∧
        1 < leverageOf (design.atom outsideLabel) := by
  exact exists_complementAtom_leverageExcess_of_tightDirection design {0, 1, 2}
    (by decide) tightDir htightNe htight

/-- Named U(3,6) form, using the base/complement vocabulary already consumed by
the disjunction module. -/
theorem uThreeSix_exists_complementAtom_baseWeightRemainder_le
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ
      ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0) :
    ∃ outsideLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label)
            - baseTripleMaxWeight design
          ≤ (leverageOf (design.atom outsideLabel) - 1)
            * (1 - ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label) ∧
      1 < leverageOf (design.atom outsideLabel) := by
  obtain ⟨maxLabel, hmaxMem, hmax, outsideLabel, houtsideMem, hbound, hheavy⟩ :=
    uThreeSix_exists_complementAtom_leverageExcess design tightDir htightNe htight
  have hmaxLe : design.weight maxLabel ≤ baseTripleMaxWeight design :=
    weight_le_baseTripleMaxWeight design maxLabel hmaxMem
  have hbaseLe : baseTripleMaxWeight design ≤ design.weight maxLabel := by
    rcases exists_eq_baseTripleMaxWeight design with hzero | hone | htwo
    · rw [hzero]
      exact hmax 0 (by decide)
    · rw [hone]
      exact hmax 1 (by decide)
    · rw [htwo]
      exact hmax 2 (by decide)
  have hmaxEq : design.weight maxLabel = baseTripleMaxWeight design :=
    le_antisymm hmaxLe hbaseLe
  refine ⟨outsideLabel, ?_, ?_, hheavy⟩
  · rw [← baseTriple_compl_eq_complementTriple]
    exact houtsideMem
  · rwa [hmaxEq] at hbound

/-- Tight-reading version of the named U(3,6) collar estimate.  This is the
form that feeds directly into the corner condition of the exact tight-swap
criterion. -/
theorem uThreeSix_exists_complementAtom_baseReadingRemainder_le
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ
      ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0) :
    ∃ outsideLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      ((∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label)
              - baseTripleMaxWeight design)
            * (tightDir ⬝ᵥ tightDir)
          ≤ ((design.atom outsideLabel ⬝ᵥ tightDir) ^ 2
                - tightDir ⬝ᵥ tightDir)
              * (1 - ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label) ∧
      tightDir ⬝ᵥ tightDir
        < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 := by
  obtain ⟨maxLabel, hmaxMem, hmax, outsideLabel, houtsideMem, hbound, hoverread⟩ :=
    exists_complementAtom_readingExcess_of_tightDirection design {0, 1, 2}
      (by decide) tightDir htightNe htight
  have hmaxLe : design.weight maxLabel ≤ baseTripleMaxWeight design :=
    weight_le_baseTripleMaxWeight design maxLabel hmaxMem
  have hbaseLe : baseTripleMaxWeight design ≤ design.weight maxLabel := by
    rcases exists_eq_baseTripleMaxWeight design with hzero | hone | htwo
    · rw [hzero]
      exact hmax 0 (by decide)
    · rw [hone]
      exact hmax 1 (by decide)
    · rw [htwo]
      exact hmax 2 (by decide)
  have hmaxEq : design.weight maxLabel = baseTripleMaxWeight design :=
    le_antisymm hmaxLe hbaseLe
  refine ⟨outsideLabel, ?_, ?_, hoverread⟩
  · rw [← baseTriple_compl_eq_complementTriple]
    exact houtsideMem
  · rwa [hmaxEq] at hbound

/-- An interior floor on the three base weights gives one complement atom a
uniform tight-direction surplus over the norm. -/
theorem uThreeSix_exists_complementAtom_tightReading_gt_one_add_two_mul_weightFloor
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ
      ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0)
    (weightFloor : ℝ)
    (hfloor : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      weightFloor ≤ design.weight label) :
    ∃ outsideLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      (1 + 2 * weightFloor) * (tightDir ⬝ᵥ tightDir)
        < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 := by
  obtain ⟨outsideLabel, houtsideMem, hbound, hoverread⟩ :=
    uThreeSix_exists_complementAtom_baseReadingRemainder_le
      design tightDir htightNe htight
  have hbaseSum :
      ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label
        = design.weight 0 + design.weight 1 + design.weight 2 := by
    exact sum_over_triple design.weight (by decide) (by decide) (by decide)
  have hfloorZero := hfloor 0 (by decide)
  have hfloorOne := hfloor 1 (by decide)
  have hfloorTwo := hfloor 2 (by decide)
  have hremainder :
      2 * weightFloor
        ≤ (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label)
          - baseTripleMaxWeight design := by
    rcases exists_eq_baseTripleMaxWeight design with hzero | hone | htwo
    · rw [hbaseSum, hzero]
      linarith
    · rw [hbaseSum, hone]
      linarith
    · rw [hbaseSum, htwo]
      linarith
  have hbaseWeightPos :
      0 < ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label :=
    Finset.sum_pos (fun label _ => design.weight_pos label) (by decide)
  have hfactorLtOne :
      1 - ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label < 1 := by
    linarith
  have hexcessPos :
      0 < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2
          - tightDir ⬝ᵥ tightDir := by
    linarith
  have hproductLt :
      ((design.atom outsideLabel ⬝ᵥ tightDir) ^ 2
          - tightDir ⬝ᵥ tightDir)
          * (1 - ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label)
        < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2
          - tightDir ⬝ᵥ tightDir :=
    mul_lt_of_lt_one_right hexcessPos hfactorLtOne
  have hnormPos : 0 < tightDir ⬝ᵥ tightDir := dotProduct_self_pos htightNe
  refine ⟨outsideLabel, houtsideMem, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hremainder hnormPos.le]

/-- The same complement atom clears the tight-direction corner test for all
three one-slot swaps, with a common quantitative surplus. -/
theorem uThreeSix_exists_complementAtom_uniform_tightSwapCorner
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ
      ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0)
    (weightFloor : ℝ)
    (hfloor : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      weightFloor ≤ design.weight label) :
    ∃ outsideLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      ∀ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        (design.atom baseLabel ⬝ᵥ tightDir) ^ 2
            + 2 * weightFloor * (tightDir ⬝ᵥ tightDir)
          < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 := by
  obtain ⟨outsideLabel, houtsideMem, houtsideReading⟩ :=
    uThreeSix_exists_complementAtom_tightReading_gt_one_add_two_mul_weightFloor
      design tightDir htightNe htight weightFloor hfloor
  refine ⟨outsideLabel, houtsideMem, ?_⟩
  intro baseLabel hbaseMem
  have hbaseReading :=
    dominatorAtom_reading_le_normSq design ({0, 1, 2} : Finset (Fin 6))
      tightDir htight hbaseMem
  nlinarith

/-- The weight-collar choice is compatible with the universal `2/3` exchange
bound: the SAME incoming complement atom clears every base corner by `2 * floor`
and clears at least one base corner by more than `2/3` at a unit tight direction. -/
theorem uThreeSix_exists_commonIncoming_uniform_and_twoThirds_corner
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ
      ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0)
    (weightFloor : ℝ) (hweightFloorPos : 0 < weightFloor)
    (hfloor : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      weightFloor ≤ design.weight label) :
    ∃ outsideLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      (∀ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        (design.atom baseLabel ⬝ᵥ tightDir) ^ 2 + 2 * weightFloor
          < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2) ∧
      ∃ dropLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        (design.atom dropLabel ⬝ᵥ tightDir) ^ 2 + 2 / 3
          < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 := by
  have htightNe : tightDir ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    norm_num at hunit
  obtain ⟨outsideLabel, houtsideMem, houtsideReading⟩ :=
    uThreeSix_exists_complementAtom_tightReading_gt_one_add_two_mul_weightFloor
      design tightDir htightNe htight weightFloor hfloor
  have hcorners : ∀ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      (design.atom baseLabel ⬝ᵥ tightDir) ^ 2
          + 2 * weightFloor * (tightDir ⬝ᵥ tightDir)
        < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 := by
    intro baseLabel hbaseMem
    have hbaseReading :=
      dominatorAtom_reading_le_normSq design ({0, 1, 2} : Finset (Fin 6))
        tightDir htight hbaseMem
    nlinarith
  obtain ⟨dropLabel, hdropMem, hdropSmall⟩ :=
    exists_inside_axisMass_le design (selected := ({0, 1, 2} : Finset (Fin 6)))
      (by decide) htight
  have hcornerUnit : ∀ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      (design.atom baseLabel ⬝ᵥ tightDir) ^ 2 + 2 * weightFloor
        < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 := by
    intro baseLabel hbaseMem
    simpa [hunit] using hcorners baseLabel hbaseMem
  have houtsideOverOne :
      1 < (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 := by
    rw [hunit, mul_one] at houtsideReading
    linarith
  have hdropThird :
      (design.atom dropLabel ⬝ᵥ tightDir) ^ 2 ≤ 1 / 3 := by
    have hcard : ({0, 1, 2} : Finset (Fin 6)).card = 3 := by decide
    rw [hcard, hunit] at hdropSmall
    norm_num at hdropSmall ⊢
    linarith
  refine ⟨outsideLabel, houtsideMem, hcornerUnit, dropLabel, hdropMem, ?_⟩
  nlinarith

/-- If no strict triple exists, one complement atom simultaneously generates
three quantitative one-swap refusals.  This is the exact planar obstruction
left after the tight-direction corner conditions have been discharged. -/
theorem uThreeSix_noStrict_yields_uniform_tightSwap_refusals
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ
      ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0)
    (weightFloor : ℝ)
    (hweightFloorPos : 0 < weightFloor)
    (hfloor : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      weightFloor ≤ design.weight label)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    ∃ swapIn ∈ ({3, 4, 5} : Finset (Fin 6)),
      ∀ swapOut ∈ ({0, 1, 2} : Finset (Fin 6)),
        (design.atom swapOut ⬝ᵥ tightDir) ^ 2 + 2 * weightFloor
            < (design.atom swapIn ⬝ᵥ tightDir) ^ 2 ∧
        ∃ probe : Fin 3 → ℝ, probe ⬝ᵥ tightDir = 0 ∧ probe ≠ 0 ∧
          ((design.atom swapIn ⬝ᵥ tightDir) ^ 2
                - (design.atom swapOut ⬝ᵥ tightDir) ^ 2)
              * (probe ⬝ᵥ
                ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probe))
            ≤ ((design.atom swapIn ⬝ᵥ tightDir)
                  * (design.atom swapOut ⬝ᵥ probe)
                - (design.atom swapOut ⬝ᵥ tightDir)
                  * (design.atom swapIn ⬝ᵥ probe)) ^ 2 := by
  have htightNe : tightDir ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    norm_num at hunit
  obtain ⟨swapIn, hswapInMem, hcorners⟩ :=
    uThreeSix_exists_complementAtom_uniform_tightSwapCorner design tightDir
      htightNe htight weightFloor hfloor
  have hswapInComplement : swapIn ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ := by
    rwa [baseTriple_compl_eq_complementTriple]
  have hswapInNotMem : swapIn ∉ ({0, 1, 2} : Finset (Fin 6)) :=
    Finset.mem_compl.mp hswapInComplement
  refine ⟨swapIn, hswapInMem, ?_⟩
  intro swapOut hswapOutMem
  have hcorner := hcorners swapOut hswapOutMem
  rw [hunit, mul_one] at hcorner
  have hstrictCorner :
      (design.atom swapOut ⬝ᵥ tightDir) ^ 2
        < (design.atom swapIn ⬝ᵥ tightDir) ^ 2 := by
    linarith
  obtain ⟨probe, hprobeFlat, hprobeNe, hrefusal⟩ :=
    noStrictDominator_yields_tightSwapExcess_failure design
      ({0, 1, 2} : Finset (Fin 6)) swapOut swapIn tightDir
      (by decide) hswapOutMem hswapInNotMem hdominates hunit htight
      hstrictCorner hnoStrict
  exact ⟨hcorner, probe, hprobeFlat, hprobeNe, hrefusal⟩

/-- A hypothetical `(6,3)` tie carries BOTH gate-failure families around one
common heavy complement atom: three tight-plane swap refusals and the three
insert-plane pair refusals.  This removes every selection quantifier from the
four-atom hinge subsystem. -/
theorem uThreeSix_isTie_yields_commonHeavy_twoFamily_refusals
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ
      ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0)
    (weightFloor : ℝ) (hweightFloorPos : 0 < weightFloor)
    (hfloor : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      weightFloor ≤ design.weight label)
    (htie : IsTie design) :
    ∃ insertLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      1 < leverageOf (design.atom insertLabel) ∧
      (∀ dropLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        (design.atom dropLabel ⬝ᵥ tightDir) ^ 2 + 2 * weightFloor
            < (design.atom insertLabel ⬝ᵥ tightDir) ^ 2 ∧
        ∃ probe : Fin 3 → ℝ, probe ⬝ᵥ tightDir = 0 ∧ probe ≠ 0 ∧
          ((design.atom insertLabel ⬝ᵥ tightDir) ^ 2
                - (design.atom dropLabel ⬝ᵥ tightDir) ^ 2)
              * (probe ⬝ᵥ
                ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probe))
            ≤ ((design.atom insertLabel ⬝ᵥ tightDir)
                  * (design.atom dropLabel ⬝ᵥ probe)
                - (design.atom dropLabel ⬝ᵥ tightDir)
                  * (design.atom insertLabel ⬝ᵥ probe)) ^ 2) ∧
      (∀ keptOne ∈ ({0, 1, 2} : Finset (Fin 6)),
        ∀ keptTwo ∈ ({0, 1, 2} : Finset (Fin 6)), keptOne ≠ keptTwo →
          ∃ planar : Fin 3 → ℝ,
            design.atom insertLabel ⬝ᵥ planar = 0 ∧ planar ≠ 0 ∧
            ((leverageOf (design.atom insertLabel)) ^ 2
                  + (design.atom keptOne ⬝ᵥ design.atom insertLabel) ^ 2
                  + (design.atom keptTwo ⬝ᵥ design.atom insertLabel) ^ 2
                  - leverageOf (design.atom insertLabel))
                * ((design.atom keptOne ⬝ᵥ planar) ^ 2
                  + (design.atom keptTwo ⬝ᵥ planar) ^ 2
                  - planar ⬝ᵥ planar)
              ≤ ((design.atom keptOne ⬝ᵥ design.atom insertLabel)
                    * (design.atom keptOne ⬝ᵥ planar)
                  + (design.atom keptTwo ⬝ᵥ design.atom insertLabel)
                    * (design.atom keptTwo ⬝ᵥ planar)) ^ 2) := by
  have htightNe : tightDir ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    norm_num at hunit
  obtain ⟨insertLabel, hinsertMem, hinsertReading⟩ :=
    uThreeSix_exists_complementAtom_tightReading_gt_one_add_two_mul_weightFloor
      design tightDir htightNe htight weightFloor hfloor
  have hinsertComplement : insertLabel ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ := by
    rwa [baseTriple_compl_eq_complementTriple]
  have hinsertNotMem : insertLabel ∉ ({0, 1, 2} : Finset (Fin 6)) :=
    Finset.mem_compl.mp hinsertComplement
  have hinsertReadOne :
      1 < (design.atom insertLabel ⬝ᵥ tightDir) ^ 2 := by
    rw [hunit, mul_one] at hinsertReading
    linarith
  have hinsertHeavy : 1 < leverageOf (design.atom insertLabel) := by
    have hcs := dotProduct_sq_le_mul (design.atom insertLabel) tightDir
    rw [hunit, mul_one] at hcs
    rw [leverageOf_eq_dotProduct_self]
    linarith
  have hinsertHeavyDot :
      1 < design.atom insertLabel ⬝ᵥ design.atom insertLabel := by
    simpa [leverageOf_eq_dotProduct_self] using hinsertHeavy
  refine ⟨insertLabel, hinsertMem, hinsertHeavy, ?_, ?_⟩
  · intro dropLabel hdropMem
    have hdropReading :=
      tightDirection_memberReading_le_one design ({0, 1, 2} : Finset (Fin 6))
        tightDir hunit htight hdropMem
    have hcorner :
        (design.atom dropLabel ⬝ᵥ tightDir) ^ 2 + 2 * weightFloor
          < (design.atom insertLabel ⬝ᵥ tightDir) ^ 2 := by
      rw [hunit, mul_one] at hinsertReading
      linarith
    have hstrict :
        (design.atom dropLabel ⬝ᵥ tightDir) ^ 2
          < (design.atom insertLabel ⬝ᵥ tightDir) ^ 2 := by
      linarith
    obtain ⟨probe, hprobeFlat, hprobeNe, hrefusal⟩ :=
      noStrictDominator_yields_tightSwapExcess_failure design
        ({0, 1, 2} : Finset (Fin 6)) dropLabel insertLabel tightDir
        (by decide) hdropMem hinsertNotMem hdominates hunit htight hstrict htie.2
    exact ⟨hcorner, probe, hprobeFlat, hprobeNe, hrefusal⟩
  · intro keptOne hkeptOne keptTwo hkeptTwo hkeptNe
    have hkeptOneInsert : keptOne ≠ insertLabel := by
      intro heq
      exact hinsertNotMem (heq ▸ hkeptOne)
    have hkeptTwoInsert : keptTwo ≠ insertLabel := by
      intro heq
      exact hinsertNotMem (heq ▸ hkeptTwo)
    have hcard :
        ({keptOne, keptTwo, insertLabel} : Finset (Fin 6)).card = 3 := by
      simp [hkeptNe, hkeptOneInsert, hkeptTwoInsert]
    simpa [leverageOf_eq_dotProduct_self] using
      (exists_insertGateFailure_of_isTie design htie hkeptNe hkeptOneInsert
        hkeptTwoInsert hcard hinsertHeavyDot)

/-- A raw floor on the three base weights produces a linear leverage gap on a
complement atom. -/
theorem uThreeSix_exists_complementAtom_one_add_two_mul_weightFloor_lt_leverage
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ
      ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0)
    (weightFloor : ℝ)
    (hfloor : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      weightFloor ≤ design.weight label) :
    ∃ outsideLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      1 + 2 * weightFloor < leverageOf (design.atom outsideLabel) := by
  obtain ⟨outsideLabel, houtsideMem, hbound, hheavy⟩ :=
    uThreeSix_exists_complementAtom_baseWeightRemainder_le design tightDir htightNe htight
  have hbaseSum :
      ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label
        = design.weight 0 + design.weight 1 + design.weight 2 := by
    exact sum_over_triple design.weight (by decide) (by decide) (by decide)
  have hfloorZero := hfloor 0 (by decide)
  have hfloorOne := hfloor 1 (by decide)
  have hfloorTwo := hfloor 2 (by decide)
  have hremainder :
      2 * weightFloor
        ≤ (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label)
          - baseTripleMaxWeight design := by
    rcases exists_eq_baseTripleMaxWeight design with hzero | hone | htwo
    · rw [hbaseSum, hzero]
      linarith
    · rw [hbaseSum, hone]
      linarith
    · rw [hbaseSum, htwo]
      linarith
  have hbaseWeightPos :
      0 < ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label :=
    Finset.sum_pos (fun label _ => design.weight_pos label) (by decide)
  have hfactorLtOne :
      1 - ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label < 1 := by
    linarith
  have hproductLt :
      (leverageOf (design.atom outsideLabel) - 1)
          * (1 - ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight label)
        < leverageOf (design.atom outsideLabel) - 1 := by
    exact mul_lt_of_lt_one_right (by linarith) hfactorLtOne
  exact ⟨outsideLabel, houtsideMem, by linarith⟩

/-- If all complement leverages lie within `leverageExcess` of one, one of the
base weights has entered the corresponding dust collar. -/
theorem uThreeSix_exists_baseWeight_le_half_leverageExcess
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ
      ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0)
    (leverageExcess : ℝ)
    (hcap : ∀ outsideLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      leverageOf (design.atom outsideLabel) ≤ 1 + leverageExcess) :
    ∃ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.weight baseLabel ≤ leverageExcess / 2 := by
  by_contra hnone
  push Not at hnone
  have hfloor : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      leverageExcess / 2 ≤ design.weight label := by
    intro label hmem
    exact (hnone label hmem).le
  obtain ⟨outsideLabel, houtsideMem, houtsideLarge⟩ :=
    uThreeSix_exists_complementAtom_one_add_two_mul_weightFloor_lt_leverage
      design tightDir htightNe htight (leverageExcess / 2) hfloor
  have houtsideCap := hcap outsideLabel houtsideMem
  linarith

end Gtz

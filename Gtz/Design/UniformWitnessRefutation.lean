import Gtz.Design.PlaneMarginFloor

/-!
# The uniform witness, and what it refutes

`Gtz.PlaneMarginProducerAtLightLabel` is the one open statement of the dust leg of
the line-free off-conic cell.  `Gtz.producer_forces_heavy_label` shows the producer
forces every design of the cell to carry a label above the dust threshold.  This
file supplies the design that carries none.

The witness is a tight frame.  Its six atoms satisfy `∑ a a' = 6` times the
identity, so Parseval holds at the uniform weight one sixth, and every label sits
at one sixth exactly.  The atoms are rational with denominator five, so line
freeness and the conic condition are decided by exact arithmetic.

Two refutations follow.  The whole-design one kills the producer at every dust
threshold from one sixth up.  The light-set one is sharper: it kills the producer
whenever the labels below the threshold carry more weight than the bulk bound
permits, and it reaches thresholds far below one sixth.

The consequence for the repaired route is `Gtz.weightAwareRoute_threshold_lt_sixth`.
`Gtz.lineFreeOffConic_noTie_of_weightAware_of_producer` consumes the producer at
the threshold `collarWidth / weightScale`, so that ratio is now bounded.
-/

namespace Gtz

open Finset

/-- The six atoms of the uniform witness.  Each entry has denominator five, and
`∑ a a'` is six times the identity. -/
noncomputable def uniformWitnessAtom : Fin 6 → (Fin 3 → ℝ) :=
  ![![-3 / 5, 2 / 5, 1 / 5],
    ![-2 / 5, -1 / 5, 0],
    ![4 / 5, 1 / 5, -2 / 5],
    ![11 / 5, 0, 1 / 5],
    ![0, 12 / 5, 0],
    ![0, 0, 12 / 5]]

/-- **THE UNIFORM WITNESS.**  A weighted design at `(6,3)` all of whose weights are
one sixth.  Parseval holds because the atoms form a tight frame. -/
noncomputable def uniformWitnessDesign : WeightedDesign 6 3 where
  atom := uniformWitnessAtom
  weight := fun _ => 1 / 6
  weight_pos := by intro label; norm_num
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [uniformWitnessAtom, atomMatrix, Matrix.vecMulVec] <;> norm_num

@[simp] theorem uniformWitnessDesign_weight (label : Fin 6) :
    uniformWitnessDesign.weight label = 1 / 6 := rfl

set_option maxHeartbeats 4000000 in
/-- **THE WITNESS IS LINE FREE.**  No three of its atoms are coplanar, so it
realizes the empty line pattern, which is the line-free cell of the
stratification. -/
theorem uniformWitnessDesign_hasLinePattern :
    HasLinePattern uniformWitnessDesign (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | norm_num [lineFamilyPattern, atomBracket, tripleBracket, uniformWitnessDesign,
           uniformWitnessAtom, Matrix.det_fin_three, Matrix.cons_val_zero,
           Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **THE WITNESS IS OFF CONIC.**  The six atoms lie on no conic: the six linear
equations a symmetric form must satisfy have only the zero solution. -/
theorem uniformWitnessDesign_hasNoCommonQuadric :
    HasNoCommonQuadric uniformWitnessDesign.atom := by
  intro form hsymm hzero
  have s10 : form 1 0 = form 0 1 := by
    have := congrFun (congrFun hsymm 0) 1; simpa using this
  have s20 : form 2 0 = form 0 2 := by
    have := congrFun (congrFun hsymm 0) 2; simpa using this
  have s21 : form 2 1 = form 1 2 := by
    have := congrFun (congrFun hsymm 1) 2; simpa using this
  have h0 := hzero 0
  have h1 := hzero 1
  have h2 := hzero 2
  have h3 := hzero 3
  have h4 := hzero 4
  have h5 := hzero 5
  simp [uniformWitnessDesign, uniformWitnessAtom, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2 h3 h4 h5
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp_all <;> linarith

/-- **THE WHOLE-DESIGN REFUTATION, FIRED.**  Every weight of the witness is one
sixth, so at any dust threshold from one sixth up the producer is refuted. -/
theorem not_planeMarginProducerAtLightLabel_of_sixth_le {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio) (hsixth : 1 / 6 ≤ dustThreshold) :
    ¬ PlaneMarginProducerAtLightLabel dustThreshold marginRatio :=
  not_planeMarginProducer_of_all_weights_le hmarginPos uniformWitnessDesign
    uniformWitnessDesign_hasLinePattern uniformWitnessDesign_hasNoCommonQuadric
    (fun label => by rw [uniformWitnessDesign_weight]; exact hsixth)

/-- **THE SHARP REFUTATION.**  The bulk bound caps the total weight of the labels
below the threshold.  Any design of the cell whose light labels carry more than
that cap refutes the producer, and this reaches thresholds far below one sixth. -/
theorem not_planeMarginProducer_of_lightSum_gt {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (lightSet : Finset (Fin 6))
    (hlight : ∀ c ∈ lightSet, design.weight c ≤ dustThreshold)
    (hbig : 3 * marginRatio
      < (3 * marginRatio + 2) * (∑ c ∈ lightSet, design.weight c)) :
    ¬ PlaneMarginProducerAtLightLabel dustThreshold marginRatio := by
  intro hproducer
  have hbulk := producer_light_weight_sum_le hmarginPos hproducer design hpattern hoffConic
    lightSet hlight
  linarith

/-- **THE CAP, IN CLOSED FORM.**  Under the producer the labels below the
threshold carry less than the whole weight, at every positive margin ratio. -/
theorem producer_lightSum_lt_one {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hproducer : PlaneMarginProducerAtLightLabel dustThreshold marginRatio)
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (lightSet : Finset (Fin 6))
    (hlight : ∀ c ∈ lightSet, design.weight c ≤ dustThreshold) :
    (∑ c ∈ lightSet, design.weight c) < 1 := by
  have hbulk := producer_light_weight_sum_le hmarginPos hproducer design hpattern hoffConic
    lightSet hlight
  nlinarith [hbulk, hmarginPos]

/-- **THE ROUTE CARRIES A BOUND ON ITS OWN PARAMETERS.**
`Gtz.lineFreeOffConic_noTie_of_weightAware_of_producer` consumes the producer at
the threshold `collarWidth / weightScale`.  The witness forces that ratio strictly
below one sixth, so the repaired route cannot be run with a wide collar. -/
theorem weightAwareRoute_threshold_lt_sixth {weightScale collarWidth marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (hproducer : PlaneMarginProducerAtLightLabel (collarWidth / weightScale) marginRatio) :
    collarWidth / weightScale < 1 / 6 := by
  by_contra hle
  push Not at hle
  exact not_planeMarginProducerAtLightLabel_of_sixth_le hmarginPos hle hproducer

/-! ## How far the refutation reaches

The whole-design refutation stops exactly at one sixth, and the reason is
pigeonhole rather than geometry.  Below one sixth no design is entirely light, so
only the light-set form can reach, and its reach is capped by the number of light
labels.
-/

/-- Six weights summing to one cannot all sit below one sixth. -/
theorem exists_sixth_le_weight (design : WeightedDesign 6 3) :
    ∃ c : Fin 6, 1 / 6 ≤ design.weight c := by
  by_contra hall
  push Not at hall
  have hsum := design.weight_sum_one
  rw [Fin.sum_univ_six] at hsum
  have h0 := hall 0; have h1 := hall 1; have h2 := hall 2
  have h3 := hall 3; have h4 := hall 4; have h5 := hall 5
  linarith

/-- **THE WHOLE-DESIGN REFUTATION IS SHARP AT ONE SIXTH.**  Below one sixth no
design of any stratum is entirely light, so `Gtz.not_planeMarginProducer_of_all_weights_le`
has no instance there. -/
theorem not_all_weights_le_of_lt_sixth {dustThreshold : ℝ} (hlt : dustThreshold < 1 / 6)
    (design : WeightedDesign 6 3) :
    ¬ (∀ c : Fin 6, design.weight c ≤ dustThreshold) := by
  intro hall
  obtain ⟨c, hc⟩ := exists_sixth_le_weight design
  linarith [hall c]

/-- Below one sixth the light labels are a proper subset. -/
theorem lightSet_ne_univ_of_lt_sixth {dustThreshold : ℝ} (hlt : dustThreshold < 1 / 6)
    (design : WeightedDesign 6 3) (lightSet : Finset (Fin 6))
    (hlight : ∀ c ∈ lightSet, design.weight c ≤ dustThreshold) :
    lightSet ≠ Finset.univ := by
  intro huniv
  subst huniv
  exact not_all_weights_le_of_lt_sixth hlt design
    (fun c => hlight c (Finset.mem_univ c))

/-- The light labels carry at most their count times the threshold. -/
theorem lightSum_le_card_mul {dustThreshold : ℝ} (design : WeightedDesign 6 3)
    (lightSet : Finset (Fin 6))
    (hlight : ∀ c ∈ lightSet, design.weight c ≤ dustThreshold) :
    (∑ c ∈ lightSet, design.weight c) ≤ lightSet.card * dustThreshold := by
  calc (∑ c ∈ lightSet, design.weight c)
      ≤ ∑ _c ∈ lightSet, dustThreshold := Finset.sum_le_sum hlight
    _ = lightSet.card * dustThreshold := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **THE REACH OF THE LIGHT-SET REFUTATION.**  A refutation at a threshold and a
margin ratio needs the light count times the threshold to clear the bulk cap.  This
is the exact boundary of the two-parameter region the witness family can reach. -/
theorem lightSum_refutation_needs {dustThreshold marginRatio : ℝ}
    (hmarginPos : 0 < marginRatio)
    (design : WeightedDesign 6 3) (lightSet : Finset (Fin 6))
    (hlight : ∀ c ∈ lightSet, design.weight c ≤ dustThreshold)
    (hbig : 3 * marginRatio
      < (3 * marginRatio + 2) * (∑ c ∈ lightSet, design.weight c)) :
    3 * marginRatio < (3 * marginRatio + 2) * (lightSet.card * dustThreshold) := by
  have hcap := lightSum_le_card_mul design lightSet hlight
  nlinarith [hcap, hmarginPos]

/-- The witness is a tight frame: its unweighted atom sum is six times the
identity.  This is Parseval at the uniform weight, stated without the weight. -/
theorem uniformWitnessDesign_subsetSum_univ :
    subsetSum uniformWitnessDesign Finset.univ = (6 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [subsetSum, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [uniformWitnessDesign, uniformWitnessAtom, atomMatrix, Matrix.vecMulVec] <;> norm_num

end Gtz

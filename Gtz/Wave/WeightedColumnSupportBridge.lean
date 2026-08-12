import Gtz.Wave.Index46SupportExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! **THE WEIGHTED-COLUMN SUPPORT BRIDGE, FREED FROM ITS FAMILY.**  Under a
positive multiplier, the weighted tight column of any labelled block has
exactly the block's total tight support: the square root of the multiplier
scales the ambient selection without moving its support.  This is the language
bridge between the second-order spine's supports and the permutation-invariant
type-eight exit, for an arbitrary four-block labelling. -/

/-- The weighted column support is the total tight support, at any label with
a positive multiplier. -/
theorem fourFamilyWeightedColumnSupport_eq_totalTightSupport
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (multiplier : Finset (Fin 6) → ℝ)
    (label : Fin 4 → Finset (Fin 6)) (pick : Fin 4)
    (hcard : (label pick).card = 3)
    (hpositive : 0 < multiplier (label pick)) :
    orbitFourWeightedColumnSupport
        (fourFamilyWeightedTightColumns label multiplier
          (ambientTightSelection tightVec)) pick
      = totalTightSupport tightVec (label pick) := by
  classical
  have hroot : Real.sqrt (multiplier (label pick)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpositive)
  ext atomIndex
  rw [orbitFourWeightedColumnSupport_mem_iff,
    ← totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport tightVec hcard,
    totalEigenSquareRow_eq_ambientTightSelection_mul_self tightVec hcard]
  simp only [fourFamilyWeightedTightColumns]
  constructor
  · intro hproduct
    have hambient :
        ambientTightSelection tightVec (label pick) atomIndex ≠ 0 :=
      (mul_ne_zero_iff.mp hproduct).2
    exact mul_ne_zero hambient hambient
  · intro hsquare
    have hambient :
        ambientTightSelection tightVec (label pick) atomIndex ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hsquare
      exact hsquare rfl
    exact mul_ne_zero hroot hambient

/-- Crux form: at a card-four family every multiplier is positive, so the
bridge fires at every label of any enumeration of the family. -/
theorem SixThreeCrux.fourFamilyWeightedColumnSupport_eq_totalTightSupport
    (crux : SixThreeCrux)
    {tightVec : Finset (Fin 6) → (Fin 3 → ℝ)}
    {multiplier : Finset (Fin 6) → ℝ}
    {label : Fin 4 → Finset (Fin 6)}
    (hrange : Finset.univ.image label
      = chartArgmaxFamily (chartPointOfDesign crux.design))
    (hfamilyCard : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (pick : Fin 4) (hcard : (label pick).card = 3) :
    orbitFourWeightedColumnSupport
        (fourFamilyWeightedTightColumns label multiplier
          (ambientTightSelection tightVec)) pick
      = totalTightSupport tightVec (label pick) := by
  have hpositive := crux.activeWeight_pos_of_identity_family_card_four
    hdata hfamilyCard
  refine _root_.Gtz.fourFamilyWeightedColumnSupport_eq_totalTightSupport tightVec
    multiplier label pick hcard (hpositive (label pick) ?_)
  rw [← hrange]
  exact Finset.mem_image.mpr ⟨pick, Finset.mem_univ _, rfl⟩

end Gtz

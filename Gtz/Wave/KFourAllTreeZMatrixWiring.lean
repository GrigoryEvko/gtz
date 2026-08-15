import Gtz.Wave.KFourPolynomialBudgetCells

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# Complete the K4 Z-matrix obstruction ledger

The all-tree minor atlas has one three-minor cell for every one of the sixteen
K4 spanning trees.  `KFourZMatrixWiring` exposed the failure data for the seven
cells added last.  This module performs the same canonical-floor conversion for
the nine earlier cells: the original gauge star and band path, the other three
vertex stars, and the four pendant trees.  Failure of the full atlas therefore
produces sixteen nonnegative dual witnesses, sixteen Gershgorin bad rows, and
sixteen division-free polynomial bad-budget alternatives.
-/

namespace Gtz

open Matrix Finset

/-! ## The nine earlier dual witnesses -/

def KFourStar345DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (-(point.mass 0)) (-(point.mass 1))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 2))
    (-(point.mass 2))
    (directionChartExactFloor point 5 - (point.mass 1 + point.mass 2))

theorem kFourStar345DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourUnsignedStarCellFires point) :
    KFourStar345DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 3 4 5
    (point.mass 0 + point.mass 1) (point.mass 0 + point.mass 2)
    (point.mass 1 + point.mass 2) (-(point.mass 0)) (-(point.mass 1))
    (-(point.mass 2)) ?_ ?_ ?_ ?_
  · linarith [point.mass_pos 0]
  · linarith [point.mass_pos 1]
  · linarith [point.mass_pos 2]
  · simpa [KFourUnsignedStarCellFires] using hnot

def KFourBand134DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (-(point.mass 2 + point.mass 5)) (-(point.mass 2))
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 2 + point.mass 5))
    (-(point.mass 0 + point.mass 2))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 2))

theorem kFourBand134DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourUnsignedBandTreeCellFires point) :
    KFourBand134DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 1 3 4
    (point.mass 2 + point.mass 5) (point.mass 0 + point.mass 2 + point.mass 5)
    (point.mass 0 + point.mass 2) (-(point.mass 2 + point.mass 5))
    (-(point.mass 2)) (-(point.mass 0 + point.mass 2)) ?_ ?_ ?_ ?_
  · nlinarith [point.mass_pos 2, point.mass_pos 5]
  · linarith [point.mass_pos 2]
  · nlinarith [point.mass_pos 0, point.mass_pos 2]
  · intro hcell
    apply hnot
    rcases hcell with ⟨floorOne, floorThree, floorFour, hfloorOne, hfloorThree,
      hfloorFour, hcorner, hminorTwo, hminorDet⟩
    refine ⟨floorOne, floorThree, floorFour, hfloorOne, hfloorThree, hfloorFour,
      hcorner, ?_, ?_⟩
    · ring_nf at hminorTwo ⊢
      exact hminorTwo
    · ring_nf at hminorDet ⊢
      exact hminorDet

def KFourStar013DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 4))
    (-(point.mass 2)) (-(point.mass 4))
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (-(point.mass 5))
    (directionChartExactFloor point 3 - (point.mass 4 + point.mass 5))

theorem kFourStar013DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourUnsignedStarACellFires point) :
    KFourStar013DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 0 1 3
    (point.mass 2 + point.mass 4) (point.mass 2 + point.mass 5)
    (point.mass 4 + point.mass 5) (-(point.mass 2)) (-(point.mass 4))
    (-(point.mass 5)) ?_ ?_ ?_ ?_
  · linarith [point.mass_pos 2]
  · linarith [point.mass_pos 4]
  · linarith [point.mass_pos 5]
  · simpa [KFourUnsignedStarACellFires] using hnot

def KFourStar024DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 3))
    (-(point.mass 1)) (-(point.mass 3))
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (-(point.mass 5))
    (directionChartExactFloor point 4 - (point.mass 3 + point.mass 5))

theorem kFourStar024DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourUnsignedStarBCellFires point) :
    KFourStar024DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 0 2 4
    (point.mass 1 + point.mass 3) (point.mass 1 + point.mass 5)
    (point.mass 3 + point.mass 5) (-(point.mass 1)) (-(point.mass 3))
    (-(point.mass 5)) ?_ ?_ ?_ ?_
  · linarith [point.mass_pos 1]
  · linarith [point.mass_pos 3]
  · linarith [point.mass_pos 5]
  · simpa [KFourUnsignedStarBCellFires] using hnot

def KFourStar125DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 3))
    (-(point.mass 0)) (-(point.mass 3))
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (-(point.mass 4))
    (directionChartExactFloor point 5 - (point.mass 3 + point.mass 4))

theorem kFourStar125DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourUnsignedStarCCellFires point) :
    KFourStar125DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 1 2 5
    (point.mass 0 + point.mass 3) (point.mass 0 + point.mass 4)
    (point.mass 3 + point.mass 4) (-(point.mass 0)) (-(point.mass 3))
    (-(point.mass 4)) ?_ ?_ ?_ ?_
  · linarith [point.mass_pos 0]
  · linarith [point.mass_pos 3]
  · linarith [point.mass_pos 4]
  · simpa [KFourUnsignedStarCCellFires] using hnot

def KFourPendant023DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 4 + point.mass 5))
    (-(point.mass 1 + point.mass 5)) (-(point.mass 4 + point.mass 5))
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (-(point.mass 5))
    (directionChartExactFloor point 3 - (point.mass 4 + point.mass 5))

theorem kFourPendant023DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPendantCell023Fires point) :
    KFourPendant023DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 0 2 3
    (point.mass 1 + point.mass 4 + point.mass 5) (point.mass 1 + point.mass 5)
    (point.mass 4 + point.mass 5) (-(point.mass 1 + point.mass 5))
    (-(point.mass 4 + point.mass 5)) (-(point.mass 5)) ?_ ?_ ?_ ?_
  · nlinarith [point.mass_pos 1, point.mass_pos 5]
  · nlinarith [point.mass_pos 4, point.mass_pos 5]
  · linarith [point.mass_pos 5]
  · intro hcell
    apply hnot
    rcases hcell with ⟨floorZero, floorTwo, floorThree, hfloorZero, hfloorTwo,
      hfloorThree, hcorner, hminorTwo, hminorDet⟩
    refine ⟨floorZero, floorTwo, floorThree, hfloorZero, hfloorTwo, hfloorThree,
      hcorner, ?_, ?_⟩
    · ring_nf at hminorTwo ⊢
      exact hminorTwo
    · ring_nf at hminorDet ⊢
      exact hminorDet

def KFourPendant123DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 4 + point.mass 5))
    (-(point.mass 0 + point.mass 4)) (-(point.mass 4 + point.mass 5))
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (-(point.mass 4))
    (directionChartExactFloor point 3 - (point.mass 4 + point.mass 5))

theorem kFourPendant123DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPendantCell123Fires point) :
    KFourPendant123DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 1 2 3
    (point.mass 0 + point.mass 4 + point.mass 5) (point.mass 0 + point.mass 4)
    (point.mass 4 + point.mass 5) (-(point.mass 0 + point.mass 4))
    (-(point.mass 4 + point.mass 5)) (-(point.mass 4)) ?_ ?_ ?_ ?_
  · nlinarith [point.mass_pos 0, point.mass_pos 4]
  · nlinarith [point.mass_pos 4, point.mass_pos 5]
  · linarith [point.mass_pos 4]
  · intro hcell
    apply hnot
    rcases hcell with ⟨floorOne, floorTwo, floorThree, hfloorOne, hfloorTwo,
      hfloorThree, hcorner, hminorTwo, hminorDet⟩
    refine ⟨floorOne, floorTwo, floorThree, hfloorOne, hfloorTwo, hfloorThree,
      hcorner, ?_, ?_⟩
    · ring_nf at hminorTwo ⊢
      exact hminorTwo
    · ring_nf at hminorDet ⊢
      exact hminorDet

def KFourPendant234DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (-(point.mass 1)) (-(point.mass 1 + point.mass 5))
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (-(point.mass 0 + point.mass 1))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 1 + point.mass 5))

theorem kFourPendant234DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPendantCell234Fires point) :
    KFourPendant234DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 2 3 4
    (point.mass 1 + point.mass 5) (point.mass 0 + point.mass 1)
    (point.mass 0 + point.mass 1 + point.mass 5) (-(point.mass 1))
    (-(point.mass 1 + point.mass 5)) (-(point.mass 0 + point.mass 1)) ?_ ?_ ?_ ?_
  · linarith [point.mass_pos 1]
  · nlinarith [point.mass_pos 1, point.mass_pos 5]
  · nlinarith [point.mass_pos 0, point.mass_pos 1]
  · intro hcell
    apply hnot
    rcases hcell with ⟨floorTwo, floorThree, floorFour, hfloorTwo, hfloorThree,
      hfloorFour, hcorner, hminorTwo, hminorDet⟩
    refine ⟨floorTwo, floorThree, floorFour, hfloorTwo, hfloorThree, hfloorFour,
      hcorner, ?_, ?_⟩
    · ring_nf at hminorTwo ⊢
      exact hminorTwo
    · ring_nf at hminorDet ⊢
      exact hminorDet

def KFourPendant235DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (-(point.mass 0)) (-(point.mass 0 + point.mass 4))
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (-(point.mass 0 + point.mass 1))
    (directionChartExactFloor point 5 - (point.mass 0 + point.mass 1 + point.mass 4))

theorem kFourPendant235DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPendantCell235Fires point) :
    KFourPendant235DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 2 3 5
    (point.mass 0 + point.mass 4) (point.mass 0 + point.mass 1)
    (point.mass 0 + point.mass 1 + point.mass 4) (-(point.mass 0))
    (-(point.mass 0 + point.mass 4)) (-(point.mass 0 + point.mass 1)) ?_ ?_ ?_ ?_
  · linarith [point.mass_pos 0]
  · nlinarith [point.mass_pos 0, point.mass_pos 4]
  · nlinarith [point.mass_pos 0, point.mass_pos 1]
  · intro hcell
    apply hnot
    rcases hcell with ⟨floorTwo, floorThree, floorFive, hfloorTwo, hfloorThree,
      hfloorFive, hcorner, hminorTwo, hminorDet⟩
    refine ⟨floorTwo, floorThree, floorFive, hfloorTwo, hfloorThree, hfloorFive,
      hcorner, ?_, ?_⟩
    · ring_nf at hminorTwo ⊢
      exact hminorTwo
    · ring_nf at hminorDet ⊢
      exact hminorDet

def KFourPriorTreeDualWitnessLedger (point : DirectionChartPoint 6) : Prop :=
  KFourStar345DualWitness point ∧ KFourBand134DualWitness point ∧
    KFourStar013DualWitness point ∧ KFourStar024DualWitness point ∧
    KFourStar125DualWitness point ∧ KFourPendant023DualWitness point ∧
    KFourPendant123DualWitness point ∧ KFourPendant234DualWitness point ∧
    KFourPendant235DualWitness point

theorem kFourPriorTreeDualWitnessLedger_of_not_fullMinorAtlas
    (point : DirectionChartPoint 6) (hnot : ¬ KFourFullMinorAtlasCellFires point) :
    KFourPriorTreeDualWitnessLedger point := by
  have hcycle : ¬ KFourUnsignedCycleCellFires point :=
    fun h => hnot (Or.inl (Or.inl h))
  have htrace : ¬ KFourUnsignedTraceAtlasCellFires point :=
    fun h => hnot (Or.inl (Or.inr h))
  have hpendant : ¬ KFourPendantAtlasCellFires point :=
    fun h => hnot (Or.inr h)
  refine ⟨
    kFourStar345DualWitness_of_not_fires point (fun h => hcycle (Or.inl h)),
    kFourBand134DualWitness_of_not_fires point (fun h => hcycle (Or.inr h)),
    kFourStar013DualWitness_of_not_fires point
      (fun h => htrace (Or.inr (Or.inl h))),
    kFourStar024DualWitness_of_not_fires point
      (fun h => htrace (Or.inr (Or.inr (Or.inl h)))),
    kFourStar125DualWitness_of_not_fires point
      (fun h => htrace (Or.inr (Or.inr (Or.inr h)))),
    kFourPendant023DualWitness_of_not_fires point (fun h => hpendant (Or.inl h)),
    kFourPendant123DualWitness_of_not_fires point
      (fun h => hpendant (Or.inr (Or.inl h))),
    kFourPendant234DualWitness_of_not_fires point
      (fun h => hpendant (Or.inr (Or.inr (Or.inl h)))),
    kFourPendant235DualWitness_of_not_fires point
      (fun h => hpendant (Or.inr (Or.inr (Or.inr h))))⟩

/-! ## Gershgorin bad rows for the nine earlier trees -/

def KFourStar345BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (-(point.mass 0)) (-(point.mass 1))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 2))
    (-(point.mass 2))
    (directionChartExactFloor point 5 - (point.mass 1 + point.mass 2))

def KFourBand134BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (-(point.mass 2 + point.mass 5)) (-(point.mass 2))
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 2 + point.mass 5))
    (-(point.mass 0 + point.mass 2))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 2))

def KFourStar013BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 4))
    (-(point.mass 2)) (-(point.mass 4))
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (-(point.mass 5))
    (directionChartExactFloor point 3 - (point.mass 4 + point.mass 5))

def KFourStar024BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 3))
    (-(point.mass 1)) (-(point.mass 3))
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (-(point.mass 5))
    (directionChartExactFloor point 4 - (point.mass 3 + point.mass 5))

def KFourStar125BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 3))
    (-(point.mass 0)) (-(point.mass 3))
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (-(point.mass 4))
    (directionChartExactFloor point 5 - (point.mass 3 + point.mass 4))

def KFourPendant023BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 4 + point.mass 5))
    (-(point.mass 1 + point.mass 5)) (-(point.mass 4 + point.mass 5))
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (-(point.mass 5))
    (directionChartExactFloor point 3 - (point.mass 4 + point.mass 5))

def KFourPendant123BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 4 + point.mass 5))
    (-(point.mass 0 + point.mass 4)) (-(point.mass 4 + point.mass 5))
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (-(point.mass 4))
    (directionChartExactFloor point 3 - (point.mass 4 + point.mass 5))

def KFourPendant234BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (-(point.mass 1)) (-(point.mass 1 + point.mass 5))
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (-(point.mass 0 + point.mass 1))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 1 + point.mass 5))

def KFourPendant235BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (-(point.mass 0)) (-(point.mass 0 + point.mass 4))
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (-(point.mass 0 + point.mass 1))
    (directionChartExactFloor point 5 - (point.mass 0 + point.mass 1 + point.mass 4))

def KFourPriorTreeBadRowLedger (point : DirectionChartPoint 6) : Prop :=
  KFourStar345BadRow point ∧ KFourBand134BadRow point ∧
    KFourStar013BadRow point ∧ KFourStar024BadRow point ∧
    KFourStar125BadRow point ∧ KFourPendant023BadRow point ∧
    KFourPendant123BadRow point ∧ KFourPendant234BadRow point ∧
    KFourPendant235BadRow point

theorem kFourPriorTreeBadRowLedger_of_dualWitnessLedger
    (point : DirectionChartPoint 6) (hdual : KFourPriorTreeDualWitnessLedger point) :
    KFourPriorTreeBadRowLedger point := by
  rcases hdual with ⟨h345, h134, h013, h024, h125, h023, h123, h234, h235⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ZThreeDualWitness.badRow
      (by linarith [point.mass_pos 0]) (by linarith [point.mass_pos 1])
      (by linarith [point.mass_pos 2]) h345
  · exact ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 2, point.mass_pos 5])
      (by linarith [point.mass_pos 2])
      (by nlinarith [point.mass_pos 0, point.mass_pos 2]) h134
  · exact ZThreeDualWitness.badRow
      (by linarith [point.mass_pos 2]) (by linarith [point.mass_pos 4])
      (by linarith [point.mass_pos 5]) h013
  · exact ZThreeDualWitness.badRow
      (by linarith [point.mass_pos 1]) (by linarith [point.mass_pos 3])
      (by linarith [point.mass_pos 5]) h024
  · exact ZThreeDualWitness.badRow
      (by linarith [point.mass_pos 0]) (by linarith [point.mass_pos 3])
      (by linarith [point.mass_pos 4]) h125
  · exact ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 1, point.mass_pos 5])
      (by nlinarith [point.mass_pos 4, point.mass_pos 5])
      (by linarith [point.mass_pos 5]) h023
  · exact ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 0, point.mass_pos 4])
      (by nlinarith [point.mass_pos 4, point.mass_pos 5])
      (by linarith [point.mass_pos 4]) h123
  · exact ZThreeDualWitness.badRow
      (by linarith [point.mass_pos 1])
      (by nlinarith [point.mass_pos 1, point.mass_pos 5])
      (by nlinarith [point.mass_pos 0, point.mass_pos 1]) h234
  · exact ZThreeDualWitness.badRow
      (by linarith [point.mass_pos 0])
      (by nlinarith [point.mass_pos 0, point.mass_pos 4])
      (by nlinarith [point.mass_pos 0, point.mass_pos 1]) h235

/-! ## Division-free bad budgets for the nine earlier trees -/

def KFourStar345BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 3 * (1 - point.weight 3) ≤
      (2 * point.mass 0 + 2 * point.mass 1) * point.weight 3 ∨
    point.mass 4 * (1 - point.weight 4) ≤
      (2 * point.mass 0 + 2 * point.mass 2) * point.weight 4 ∨
    point.mass 5 * (1 - point.weight 5) ≤
      (2 * point.mass 1 + 2 * point.mass 2) * point.weight 5

def KFourBand134BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 1 * (1 - point.weight 1) ≤
      (3 * point.mass 2 + 2 * point.mass 5) * point.weight 1 ∨
    point.mass 3 * (1 - point.weight 3) ≤
      (2 * point.mass 0 + 3 * point.mass 2 + 2 * point.mass 5) * point.weight 3 ∨
    point.mass 4 * (1 - point.weight 4) ≤
      (2 * point.mass 0 + 3 * point.mass 2) * point.weight 4

def KFourStar013BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 0 * (1 - point.weight 0) ≤
      (2 * point.mass 2 + 2 * point.mass 4) * point.weight 0 ∨
    point.mass 1 * (1 - point.weight 1) ≤
      (2 * point.mass 2 + 2 * point.mass 5) * point.weight 1 ∨
    point.mass 3 * (1 - point.weight 3) ≤
      (2 * point.mass 4 + 2 * point.mass 5) * point.weight 3

def KFourStar024BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 0 * (1 - point.weight 0) ≤
      (2 * point.mass 1 + 2 * point.mass 3) * point.weight 0 ∨
    point.mass 2 * (1 - point.weight 2) ≤
      (2 * point.mass 1 + 2 * point.mass 5) * point.weight 2 ∨
    point.mass 4 * (1 - point.weight 4) ≤
      (2 * point.mass 3 + 2 * point.mass 5) * point.weight 4

def KFourStar125BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 1 * (1 - point.weight 1) ≤
      (2 * point.mass 0 + 2 * point.mass 3) * point.weight 1 ∨
    point.mass 2 * (1 - point.weight 2) ≤
      (2 * point.mass 0 + 2 * point.mass 4) * point.weight 2 ∨
    point.mass 5 * (1 - point.weight 5) ≤
      (2 * point.mass 3 + 2 * point.mass 4) * point.weight 5

def KFourPendant023BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 0 * (1 - point.weight 0) ≤
      (2 * point.mass 1 + 2 * point.mass 4 + 3 * point.mass 5) * point.weight 0 ∨
    point.mass 2 * (1 - point.weight 2) ≤
      (2 * point.mass 1 + 3 * point.mass 5) * point.weight 2 ∨
    point.mass 3 * (1 - point.weight 3) ≤
      (2 * point.mass 4 + 3 * point.mass 5) * point.weight 3

def KFourPendant123BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 1 * (1 - point.weight 1) ≤
      (2 * point.mass 0 + 3 * point.mass 4 + 2 * point.mass 5) * point.weight 1 ∨
    point.mass 2 * (1 - point.weight 2) ≤
      (2 * point.mass 0 + 3 * point.mass 4) * point.weight 2 ∨
    point.mass 3 * (1 - point.weight 3) ≤
      (3 * point.mass 4 + 2 * point.mass 5) * point.weight 3

def KFourPendant234BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 2 * (1 - point.weight 2) ≤
      (3 * point.mass 1 + 2 * point.mass 5) * point.weight 2 ∨
    point.mass 3 * (1 - point.weight 3) ≤
      (2 * point.mass 0 + 3 * point.mass 1) * point.weight 3 ∨
    point.mass 4 * (1 - point.weight 4) ≤
      (2 * point.mass 0 + 3 * point.mass 1 + 2 * point.mass 5) * point.weight 4

def KFourPendant235BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 2 * (1 - point.weight 2) ≤
      (3 * point.mass 0 + 2 * point.mass 4) * point.weight 2 ∨
    point.mass 3 * (1 - point.weight 3) ≤
      (3 * point.mass 0 + 2 * point.mass 1) * point.weight 3 ∨
    point.mass 5 * (1 - point.weight 5) ≤
      (3 * point.mass 0 + 2 * point.mass 1 + 2 * point.mass 4) * point.weight 5

theorem kFourStar345BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourStar345BadRow point) : KFourStar345BadBudget point := by
  rcases hbad with hthree | hfour | hfive
  · left; exact directionChart_budget_le_of_exactFloor_le point 3 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 4 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 5 _ (by nlinarith)

theorem kFourBand134BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourBand134BadRow point) : KFourBand134BadBudget point := by
  rcases hbad with hone | hthree | hfour
  · left; exact directionChart_budget_le_of_exactFloor_le point 1 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 3 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 4 _ (by nlinarith)

theorem kFourStar013BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourStar013BadRow point) : KFourStar013BadBudget point := by
  rcases hbad with hzero | hone | hthree
  · left; exact directionChart_budget_le_of_exactFloor_le point 0 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 1 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 3 _ (by nlinarith)

theorem kFourStar024BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourStar024BadRow point) : KFourStar024BadBudget point := by
  rcases hbad with hzero | htwo | hfour
  · left; exact directionChart_budget_le_of_exactFloor_le point 0 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 2 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 4 _ (by nlinarith)

theorem kFourStar125BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourStar125BadRow point) : KFourStar125BadBudget point := by
  rcases hbad with hone | htwo | hfive
  · left; exact directionChart_budget_le_of_exactFloor_le point 1 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 2 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 5 _ (by nlinarith)

theorem kFourPendant023BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourPendant023BadRow point) : KFourPendant023BadBudget point := by
  rcases hbad with hzero | htwo | hthree
  · left; exact directionChart_budget_le_of_exactFloor_le point 0 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 2 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 3 _ (by nlinarith)

theorem kFourPendant123BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourPendant123BadRow point) : KFourPendant123BadBudget point := by
  rcases hbad with hone | htwo | hthree
  · left; exact directionChart_budget_le_of_exactFloor_le point 1 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 2 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 3 _ (by nlinarith)

theorem kFourPendant234BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourPendant234BadRow point) : KFourPendant234BadBudget point := by
  rcases hbad with htwo | hthree | hfour
  · left; exact directionChart_budget_le_of_exactFloor_le point 2 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 3 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 4 _ (by nlinarith)

theorem kFourPendant235BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourPendant235BadRow point) : KFourPendant235BadBudget point := by
  rcases hbad with htwo | hthree | hfive
  · left; exact directionChart_budget_le_of_exactFloor_le point 2 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 3 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 5 _ (by nlinarith)

def KFourPriorTreeBadBudgetLedger (point : DirectionChartPoint 6) : Prop :=
  KFourStar345BadBudget point ∧ KFourBand134BadBudget point ∧
    KFourStar013BadBudget point ∧ KFourStar024BadBudget point ∧
    KFourStar125BadBudget point ∧ KFourPendant023BadBudget point ∧
    KFourPendant123BadBudget point ∧ KFourPendant234BadBudget point ∧
    KFourPendant235BadBudget point

theorem kFourPriorTreeBadBudgetLedger_of_badRowLedger
    (point : DirectionChartPoint 6) (hbad : KFourPriorTreeBadRowLedger point) :
    KFourPriorTreeBadBudgetLedger point := by
  rcases hbad with ⟨h345, h134, h013, h024, h125, h023, h123, h234, h235⟩
  exact ⟨kFourStar345BadBudget_of_badRow point h345,
    kFourBand134BadBudget_of_badRow point h134,
    kFourStar013BadBudget_of_badRow point h013,
    kFourStar024BadBudget_of_badRow point h024,
    kFourStar125BadBudget_of_badRow point h125,
    kFourPendant023BadBudget_of_badRow point h023,
    kFourPendant123BadBudget_of_badRow point h123,
    kFourPendant234BadBudget_of_badRow point h234,
    kFourPendant235BadBudget_of_badRow point h235⟩

/-! ## The complete sixteen-tree obstruction ledger -/

def KFourPriorTreeObstructionLedger (point : DirectionChartPoint 6) : Prop :=
  KFourPriorTreeDualWitnessLedger point ∧ KFourPriorTreeBadRowLedger point ∧
    KFourPriorTreeBadBudgetLedger point

theorem kFourPriorTreeObstructionLedger_of_not_fullMinorAtlas
    (point : DirectionChartPoint 6) (hnot : ¬ KFourFullMinorAtlasCellFires point) :
    KFourPriorTreeObstructionLedger point := by
  have hdual := kFourPriorTreeDualWitnessLedger_of_not_fullMinorAtlas point hnot
  have hbad := kFourPriorTreeBadRowLedger_of_dualWitnessLedger point hdual
  exact ⟨hdual, hbad, kFourPriorTreeBadBudgetLedger_of_badRowLedger point hbad⟩

/-- The sixteen nonnegative dual witnesses, grouped nine plus seven. -/
def KFourAllTreeDualWitnessLedger (point : DirectionChartPoint 6) : Prop :=
  KFourPriorTreeDualWitnessLedger point ∧ KFourMissingPathDualWitnessLedger point

/-- The sixteen diagonally non-dominant rows, grouped nine plus seven. -/
def KFourAllTreeBadRowLedger (point : DirectionChartPoint 6) : Prop :=
  KFourPriorTreeBadRowLedger point ∧ KFourMissingPathBadRowLedger point

/-- The sixteen three-way division-free polynomial budget alternatives,
grouped nine plus seven.  This is the finite branch interface for the next
algebraic elimination. -/
def KFourAllTreeBadBudgetLedger (point : DirectionChartPoint 6) : Prop :=
  KFourPriorTreeBadBudgetLedger point ∧ KFourMissingPathBadBudgetLedger point

/-- Failure of the sixteen-tree atlas, organized by consequence type rather
than by landing chronology. -/
def KFourAllTreeObstructionLedger (point : DirectionChartPoint 6) : Prop :=
  KFourAllTreeDualWitnessLedger point ∧ KFourAllTreeBadRowLedger point ∧
    KFourAllTreeBadBudgetLedger point

theorem kFourAllTreeObstructionLedger_of_allTreeBlind
    (point : DirectionChartPoint 6)
    (hnot : ¬ KFourAllTreeMinorAtlasCellFires point) :
    KFourAllTreeObstructionLedger point := by
  have hnotPrior : ¬ KFourFullMinorAtlasCellFires point :=
    fun hprior => hnot (Or.inl hprior)
  have hprior := kFourPriorTreeObstructionLedger_of_not_fullMinorAtlas point hnotPrior
  have hmissing := kFourMissingPathObstructionLedger_of_allTreeBlind point hnot
  exact ⟨⟨hprior.1, hmissing.1⟩, ⟨hprior.2.1, hmissing.2.1⟩,
    ⟨hprior.2.2, hmissing.2.2⟩⟩

/-! ## Spend the full ledger in A3 -/

/-- The exact K4 residual after exposing Z-matrix failure data at every one of
the sixteen spanning trees. -/
noncomputable def KFourKnifeBandRefinedAllTreeZObstructedWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem zObstructedKFourKnifeBandRefined_of_allTreeZObstructed
    (hall : KFourKnifeBandRefinedAllTreeZObstructedWeakToStrict) :
    KFourKnifeBandRefinedZObstructedWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas _hmissing hweak
  exact hall point hnotLayerA hnotExchange hnotAtlas
    (kFourAllTreeObstructionLedger_of_allTreeBlind point hnotAtlas) hweak

theorem allTreeZObstructedKFourKnifeBandRefined_of_zObstructed
    (hmissing : KFourKnifeBandRefinedZObstructedWeakToStrict) :
    KFourKnifeBandRefinedAllTreeZObstructedWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hweak
  exact hmissing point hnotLayerA hnotExchange hnotAtlas
    ⟨hledger.1.2, hledger.2.1.2, hledger.2.2.2⟩ hweak

theorem kFourKnifeBandRefinedAllTreeZObstructed_iff_zObstructed :
    KFourKnifeBandRefinedAllTreeZObstructedWeakToStrict ↔
      KFourKnifeBandRefinedZObstructedWeakToStrict :=
  ⟨zObstructedKFourKnifeBandRefined_of_allTreeZObstructed,
    allTreeZObstructedKFourKnifeBandRefined_of_zObstructed⟩

theorem kFourKnifeBandRefinedAllTreeZObstructed_iff :
    KFourKnifeBandRefinedAllTreeZObstructedWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedAllTreeZObstructed_iff_zObstructed.trans
    kFourKnifeBandRefinedZObstructed_iff

end Gtz

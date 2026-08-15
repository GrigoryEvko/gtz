import Gtz.Design.ZMatrixAlternative
import Gtz.Wave.KFourRowCertificateWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# Spend the Z-matrix alternative in the K4 residual

Every path cell is written with three auxiliary diagonal floors.  At a chart
point those floors have canonical maximal values

`mass i * (1 - weight i) / weight i`.

Consequently, failure of a cell forces failure of one leading minor of its
canonical symmetric Z-matrix.  `ZMatrixAlternative` converts that failure into
an explicit nonzero nonnegative dual vector and then into a diagonally
non-dominant row.  This module performs that conversion for all seven path
cells added by `KFourRowCertificateWiring` and exposes the resulting finite
ledger in the exact A3 residual.
-/

namespace Gtz

open Matrix Finset

/-! ## Canonical floors and the generic dual conversion -/

/-- The largest floor allowed by the chart budget at one label. -/
noncomputable def directionChartExactFloor (point : DirectionChartPoint 6)
    (label : Fin 6) : ℝ :=
  point.mass label * (1 - point.weight label) / point.weight label

theorem directionChartExactFloor_mul_weight (point : DirectionChartPoint 6)
    (label : Fin 6) :
    directionChartExactFloor point label * point.weight label =
      point.mass label * (1 - point.weight label) := by
  rw [directionChartExactFloor, div_mul_cancel₀]
  exact ne_of_gt (point.weight_pos label)

/-- Clear the positive chart weight from a canonical-floor upper bound. -/
theorem directionChart_budget_le_of_exactFloor_le
    (point : DirectionChartPoint 6) (label : Fin 6) (bound : ℝ)
    (hfloor : directionChartExactFloor point label ≤ bound) :
    point.mass label * (1 - point.weight label) ≤ bound * point.weight label := by
  rw [← directionChartExactFloor_mul_weight point label]
  exact mul_le_mul_of_nonneg_right hfloor (point.weight_pos label).le

/-- A named scalar package for the nonnegative dual vector returned by the
Z-matrix alternative. -/
def ZThreeDualWitness (a b c d e f : ℝ) : Prop :=
  ∃ yOne yTwo yThree : ℝ,
    0 ≤ yOne ∧ 0 ≤ yTwo ∧ 0 ≤ yThree ∧
    ¬ (yOne = 0 ∧ yTwo = 0 ∧ yThree = 0) ∧
    a * yOne + b * yTwo + c * yThree ≤ 0 ∧
    b * yOne + d * yTwo + e * yThree ≤ 0 ∧
    c * yOne + e * yTwo + f * yThree ≤ 0

/-- Failure of an existential floor cell gives a dual witness at the canonical
maximal floors.  This is the exact bridge from atlas blindness to the
Z-matrix alternative. -/
theorem zThreeDualWitness_of_not_floorCell
    (point : DirectionChartPoint 6) (selA selB selC : Fin 6)
    (lossA lossB lossC entryAB entryAC entryBC : ℝ)
    (hAB : entryAB ≤ 0) (hAC : entryAC ≤ 0) (hBC : entryBC ≤ 0)
    (hnot : ¬ ∃ floorA floorB floorC : ℝ,
      floorA * point.weight selA ≤ point.mass selA * (1 - point.weight selA) ∧
      floorB * point.weight selB ≤ point.mass selB * (1 - point.weight selB) ∧
      floorC * point.weight selC ≤ point.mass selC * (1 - point.weight selC) ∧
      0 < floorA - lossA ∧
      0 < (floorA - lossA) * (floorB - lossB) - entryAB ^ 2 ∧
      0 < (floorA - lossA) * (floorB - lossB) * (floorC - lossC)
        - (floorA - lossA) * entryBC ^ 2
        - entryAB ^ 2 * (floorC - lossC)
        + 2 * entryAB * entryAC * entryBC
        - entryAC ^ 2 * (floorB - lossB)) :
    ZThreeDualWitness
      (directionChartExactFloor point selA - lossA) entryAB entryAC
      (directionChartExactFloor point selB - lossB) entryBC
      (directionChartExactFloor point selC - lossC) := by
  apply zThreeDualWitness_of_not_minors hAB hAC hBC
  intro hminors
  apply hnot
  exact ⟨directionChartExactFloor point selA,
    directionChartExactFloor point selB,
    directionChartExactFloor point selC,
    (directionChartExactFloor_mul_weight point selA).le,
    (directionChartExactFloor_mul_weight point selB).le,
    (directionChartExactFloor_mul_weight point selC).le,
    hminors.1, hminors.2.1, hminors.2.2⟩

/-! ## The seven path dual witnesses -/

def KFourPath015DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 4))
    (-(point.mass 2 + point.mass 4)) (-(point.mass 4))
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 3 + point.mass 4))
    (-(point.mass 3 + point.mass 4))
    (directionChartExactFloor point 5 - (point.mass 3 + point.mass 4))

theorem kFourPath015DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell015Fires point) :
    KFourPath015DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 0 1 5
    (point.mass 2 + point.mass 4)
    (point.mass 2 + point.mass 3 + point.mass 4)
    (point.mass 3 + point.mass 4)
    (-(point.mass 2 + point.mass 4)) (-(point.mass 4))
    (-(point.mass 3 + point.mass 4)) ?_ ?_ ?_ ?_
  · nlinarith [point.mass_pos 2, point.mass_pos 4]
  · nlinarith [point.mass_pos 4]
  · nlinarith [point.mass_pos 3, point.mass_pos 4]
  · simpa only [KFourPathCell015Fires, neg_sq] using hnot

def KFourPath025DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 3))
    (-(point.mass 1 + point.mass 3)) (-(point.mass 3))
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 3 + point.mass 4))
    (-(point.mass 3 + point.mass 4))
    (directionChartExactFloor point 5 - (point.mass 3 + point.mass 4))

theorem kFourPath025DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell025Fires point) :
    KFourPath025DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 0 2 5
    (point.mass 1 + point.mass 3)
    (point.mass 1 + point.mass 3 + point.mass 4)
    (point.mass 3 + point.mass 4)
    (-(point.mass 1 + point.mass 3)) (-(point.mass 3))
    (-(point.mass 3 + point.mass 4)) ?_ ?_ ?_ ?_
  · nlinarith [point.mass_pos 1, point.mass_pos 3]
  · nlinarith [point.mass_pos 3]
  · nlinarith [point.mass_pos 3, point.mass_pos 4]
  · simpa only [KFourPathCell025Fires, neg_sq] using hnot

def KFourPath035DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 4))
    (-(point.mass 2 + point.mass 4)) (-(point.mass 2))
    (directionChartExactFloor point 3 - (point.mass 1 + point.mass 2 + point.mass 4))
    (-(point.mass 1 + point.mass 2))
    (directionChartExactFloor point 5 - (point.mass 1 + point.mass 2))

theorem kFourPath035DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell035Fires point) :
    KFourPath035DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 0 3 5
    (point.mass 2 + point.mass 4)
    (point.mass 1 + point.mass 2 + point.mass 4)
    (point.mass 1 + point.mass 2)
    (-(point.mass 2 + point.mass 4)) (-(point.mass 2))
    (-(point.mass 1 + point.mass 2)) ?_ ?_ ?_ ?_
  · nlinarith [point.mass_pos 2, point.mass_pos 4]
  · nlinarith [point.mass_pos 2]
  · nlinarith [point.mass_pos 1, point.mass_pos 2]
  · simpa only [KFourPathCell035Fires, neg_sq] using hnot

def KFourPath045DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 3))
    (-(point.mass 1 + point.mass 3)) (-(point.mass 1))
    (directionChartExactFloor point 4 - (point.mass 1 + point.mass 2 + point.mass 3))
    (-(point.mass 1 + point.mass 2))
    (directionChartExactFloor point 5 - (point.mass 1 + point.mass 2))

theorem kFourPath045DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell045Fires point) :
    KFourPath045DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 0 4 5
    (point.mass 1 + point.mass 3)
    (point.mass 1 + point.mass 2 + point.mass 3)
    (point.mass 1 + point.mass 2)
    (-(point.mass 1 + point.mass 3)) (-(point.mass 1))
    (-(point.mass 1 + point.mass 2)) ?_ ?_ ?_ ?_
  · nlinarith [point.mass_pos 1, point.mass_pos 3]
  · nlinarith [point.mass_pos 1]
  · nlinarith [point.mass_pos 1, point.mass_pos 2]
  · simpa only [KFourPathCell045Fires, neg_sq] using hnot

def KFourPath014DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 3 + point.mass 5))
    (-(point.mass 2 + point.mass 5)) (-(point.mass 3 + point.mass 5))
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (-(point.mass 5))
    (directionChartExactFloor point 4 - (point.mass 3 + point.mass 5))

theorem kFourPath014DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell014Fires point) :
    KFourPath014DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 0 1 4
    (point.mass 2 + point.mass 3 + point.mass 5)
    (point.mass 2 + point.mass 5)
    (point.mass 3 + point.mass 5)
    (-(point.mass 2 + point.mass 5)) (-(point.mass 3 + point.mass 5))
    (-(point.mass 5)) ?_ ?_ ?_ ?_
  · nlinarith [point.mass_pos 2, point.mass_pos 5]
  · nlinarith [point.mass_pos 3, point.mass_pos 5]
  · nlinarith [point.mass_pos 5]
  · simpa only [KFourPathCell014Fires, neg_sq] using hnot

def KFourPath124DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 3))
    (-(point.mass 0 + point.mass 3)) (-(point.mass 3))
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 3 + point.mass 5))
    (-(point.mass 3 + point.mass 5))
    (directionChartExactFloor point 4 - (point.mass 3 + point.mass 5))

theorem kFourPath124DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell124Fires point) :
    KFourPath124DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 1 2 4
    (point.mass 0 + point.mass 3)
    (point.mass 0 + point.mass 3 + point.mass 5)
    (point.mass 3 + point.mass 5)
    (-(point.mass 0 + point.mass 3)) (-(point.mass 3))
    (-(point.mass 3 + point.mass 5)) ?_ ?_ ?_ ?_
  · nlinarith [point.mass_pos 0, point.mass_pos 3]
  · nlinarith [point.mass_pos 3]
  · nlinarith [point.mass_pos 3, point.mass_pos 5]
  · simpa only [KFourPathCell124Fires, neg_sq] using hnot

def KFourPath145DualWitness (point : DirectionChartPoint 6) : Prop :=
  ZThreeDualWitness
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 3))
    (-(point.mass 0)) (-(point.mass 0 + point.mass 3))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 2))
    (-(point.mass 0 + point.mass 2))
    (directionChartExactFloor point 5 - (point.mass 0 + point.mass 2 + point.mass 3))

theorem kFourPath145DualWitness_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell145Fires point) :
    KFourPath145DualWitness point := by
  refine zThreeDualWitness_of_not_floorCell point 1 4 5
    (point.mass 0 + point.mass 3)
    (point.mass 0 + point.mass 2)
    (point.mass 0 + point.mass 2 + point.mass 3)
    (-(point.mass 0)) (-(point.mass 0 + point.mass 3))
    (-(point.mass 0 + point.mass 2)) ?_ ?_ ?_ ?_
  · nlinarith [point.mass_pos 0]
  · nlinarith [point.mass_pos 0, point.mass_pos 3]
  · nlinarith [point.mass_pos 0, point.mass_pos 2]
  · simpa only [KFourPathCell145Fires, neg_sq] using hnot

/-! ## Dual and Gershgorin ledgers -/

def KFourMissingPathDualWitnessLedger (point : DirectionChartPoint 6) : Prop :=
  KFourPath015DualWitness point ∧ KFourPath025DualWitness point ∧
    KFourPath035DualWitness point ∧ KFourPath045DualWitness point ∧
    KFourPath014DualWitness point ∧ KFourPath124DualWitness point ∧
    KFourPath145DualWitness point

theorem kFourMissingPathDualWitnessLedger_of_not_fires
    (point : DirectionChartPoint 6)
    (hnot : ¬ KFourMissingPathMinorAtlasCellFires point) :
    KFourMissingPathDualWitnessLedger point := by
  refine ⟨kFourPath015DualWitness_of_not_fires point (fun h => hnot (Or.inl h)),
    kFourPath025DualWitness_of_not_fires point (fun h => hnot (Or.inr (Or.inl h))),
    kFourPath035DualWitness_of_not_fires point
      (fun h => hnot (Or.inr (Or.inr (Or.inl h)))),
    kFourPath045DualWitness_of_not_fires point
      (fun h => hnot (Or.inr (Or.inr (Or.inr (Or.inl h))))),
    kFourPath014DualWitness_of_not_fires point
      (fun h => hnot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))),
    kFourPath124DualWitness_of_not_fires point
      (fun h => hnot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),
    kFourPath145DualWitness_of_not_fires point
      (fun h => hnot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))⟩

/-- A named diagonally non-dominant row alternative for a symmetric
three-by-three Z-matrix. -/
def ZThreeBadRow (a b c d e f : ℝ) : Prop :=
  a ≤ -b - c ∨ d ≤ -b - e ∨ f ≤ -c - e

theorem ZThreeDualWitness.badRow {a b c d e f : ℝ}
    (hAB : b ≤ 0) (hAC : c ≤ 0) (hBC : e ≤ 0)
    (hdual : ZThreeDualWitness a b c d e f) :
    ZThreeBadRow a b c d e f := by
  obtain ⟨yOne, yTwo, yThree, hyOne, hyTwo, hyThree, hne,
    hrowOne, hrowTwo, hrowThree⟩ := hdual
  exact zThree_gershgorin_of_dualWitness hAB hAC hBC
    hyOne hyTwo hyThree hne hrowOne hrowTwo hrowThree

def KFourPath015BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 4))
    (-(point.mass 2 + point.mass 4)) (-(point.mass 4))
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 3 + point.mass 4))
    (-(point.mass 3 + point.mass 4))
    (directionChartExactFloor point 5 - (point.mass 3 + point.mass 4))

def KFourPath025BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 3))
    (-(point.mass 1 + point.mass 3)) (-(point.mass 3))
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 3 + point.mass 4))
    (-(point.mass 3 + point.mass 4))
    (directionChartExactFloor point 5 - (point.mass 3 + point.mass 4))

def KFourPath035BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 4))
    (-(point.mass 2 + point.mass 4)) (-(point.mass 2))
    (directionChartExactFloor point 3 - (point.mass 1 + point.mass 2 + point.mass 4))
    (-(point.mass 1 + point.mass 2))
    (directionChartExactFloor point 5 - (point.mass 1 + point.mass 2))

def KFourPath045BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 3))
    (-(point.mass 1 + point.mass 3)) (-(point.mass 1))
    (directionChartExactFloor point 4 - (point.mass 1 + point.mass 2 + point.mass 3))
    (-(point.mass 1 + point.mass 2))
    (directionChartExactFloor point 5 - (point.mass 1 + point.mass 2))

def KFourPath014BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 3 + point.mass 5))
    (-(point.mass 2 + point.mass 5)) (-(point.mass 3 + point.mass 5))
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (-(point.mass 5))
    (directionChartExactFloor point 4 - (point.mass 3 + point.mass 5))

def KFourPath124BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 3))
    (-(point.mass 0 + point.mass 3)) (-(point.mass 3))
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 3 + point.mass 5))
    (-(point.mass 3 + point.mass 5))
    (directionChartExactFloor point 4 - (point.mass 3 + point.mass 5))

def KFourPath145BadRow (point : DirectionChartPoint 6) : Prop :=
  ZThreeBadRow
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 3))
    (-(point.mass 0)) (-(point.mass 0 + point.mass 3))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 2))
    (-(point.mass 0 + point.mass 2))
    (directionChartExactFloor point 5 - (point.mass 0 + point.mass 2 + point.mass 3))

def KFourMissingPathBadRowLedger (point : DirectionChartPoint 6) : Prop :=
  KFourPath015BadRow point ∧ KFourPath025BadRow point ∧
    KFourPath035BadRow point ∧ KFourPath045BadRow point ∧
    KFourPath014BadRow point ∧ KFourPath124BadRow point ∧
    KFourPath145BadRow point

theorem kFourMissingPathBadRowLedger_of_dualWitnessLedger
    (point : DirectionChartPoint 6)
    (hdual : KFourMissingPathDualWitnessLedger point) :
    KFourMissingPathBadRowLedger point := by
  rcases hdual with ⟨h015, h025, h035, h045, h014, h124, h145⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 2, point.mass_pos 4])
      (by nlinarith [point.mass_pos 4])
      (by nlinarith [point.mass_pos 3, point.mass_pos 4]) h015
  · exact ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 1, point.mass_pos 3])
      (by nlinarith [point.mass_pos 3])
      (by nlinarith [point.mass_pos 3, point.mass_pos 4]) h025
  · exact ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 2, point.mass_pos 4])
      (by nlinarith [point.mass_pos 2])
      (by nlinarith [point.mass_pos 1, point.mass_pos 2]) h035
  · exact ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 1, point.mass_pos 3])
      (by nlinarith [point.mass_pos 1])
      (by nlinarith [point.mass_pos 1, point.mass_pos 2]) h045
  · exact ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 2, point.mass_pos 5])
      (by nlinarith [point.mass_pos 3, point.mass_pos 5])
      (by nlinarith [point.mass_pos 5]) h014
  · exact ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 0, point.mass_pos 3])
      (by nlinarith [point.mass_pos 3])
      (by nlinarith [point.mass_pos 3, point.mass_pos 5]) h124
  · exact ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 0])
      (by nlinarith [point.mass_pos 0, point.mass_pos 3])
      (by nlinarith [point.mass_pos 0, point.mass_pos 2]) h145

/-! ## Clear the bad rows to polynomial budget alternatives -/

def KFourPath015BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 0 * (1 - point.weight 0) ≤
      (2 * point.mass 2 + 3 * point.mass 4) * point.weight 0 ∨
    point.mass 1 * (1 - point.weight 1) ≤
      (2 * point.mass 2 + 2 * point.mass 3 + 3 * point.mass 4) * point.weight 1 ∨
    point.mass 5 * (1 - point.weight 5) ≤
      (2 * point.mass 3 + 3 * point.mass 4) * point.weight 5

def KFourPath025BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 0 * (1 - point.weight 0) ≤
      (2 * point.mass 1 + 3 * point.mass 3) * point.weight 0 ∨
    point.mass 2 * (1 - point.weight 2) ≤
      (2 * point.mass 1 + 3 * point.mass 3 + 2 * point.mass 4) * point.weight 2 ∨
    point.mass 5 * (1 - point.weight 5) ≤
      (3 * point.mass 3 + 2 * point.mass 4) * point.weight 5

def KFourPath035BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 0 * (1 - point.weight 0) ≤
      (3 * point.mass 2 + 2 * point.mass 4) * point.weight 0 ∨
    point.mass 3 * (1 - point.weight 3) ≤
      (2 * point.mass 1 + 3 * point.mass 2 + 2 * point.mass 4) * point.weight 3 ∨
    point.mass 5 * (1 - point.weight 5) ≤
      (2 * point.mass 1 + 3 * point.mass 2) * point.weight 5

def KFourPath045BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 0 * (1 - point.weight 0) ≤
      (3 * point.mass 1 + 2 * point.mass 3) * point.weight 0 ∨
    point.mass 4 * (1 - point.weight 4) ≤
      (3 * point.mass 1 + 2 * point.mass 2 + 2 * point.mass 3) * point.weight 4 ∨
    point.mass 5 * (1 - point.weight 5) ≤
      (3 * point.mass 1 + 2 * point.mass 2) * point.weight 5

def KFourPath014BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 0 * (1 - point.weight 0) ≤
      (2 * point.mass 2 + 2 * point.mass 3 + 3 * point.mass 5) * point.weight 0 ∨
    point.mass 1 * (1 - point.weight 1) ≤
      (2 * point.mass 2 + 3 * point.mass 5) * point.weight 1 ∨
    point.mass 4 * (1 - point.weight 4) ≤
      (2 * point.mass 3 + 3 * point.mass 5) * point.weight 4

def KFourPath124BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 1 * (1 - point.weight 1) ≤
      (2 * point.mass 0 + 3 * point.mass 3) * point.weight 1 ∨
    point.mass 2 * (1 - point.weight 2) ≤
      (2 * point.mass 0 + 3 * point.mass 3 + 2 * point.mass 5) * point.weight 2 ∨
    point.mass 4 * (1 - point.weight 4) ≤
      (3 * point.mass 3 + 2 * point.mass 5) * point.weight 4

def KFourPath145BadBudget (point : DirectionChartPoint 6) : Prop :=
  point.mass 1 * (1 - point.weight 1) ≤
      (3 * point.mass 0 + 2 * point.mass 3) * point.weight 1 ∨
    point.mass 4 * (1 - point.weight 4) ≤
      (3 * point.mass 0 + 2 * point.mass 2) * point.weight 4 ∨
    point.mass 5 * (1 - point.weight 5) ≤
      (3 * point.mass 0 + 2 * point.mass 2 + 2 * point.mass 3) * point.weight 5

theorem kFourPath015BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourPath015BadRow point) : KFourPath015BadBudget point := by
  rcases hbad with hzero | hone | hfive
  · left
    exact directionChart_budget_le_of_exactFloor_le point 0 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 1 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 5 _ (by nlinarith)

theorem kFourPath025BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourPath025BadRow point) : KFourPath025BadBudget point := by
  rcases hbad with hzero | htwo | hfive
  · left
    exact directionChart_budget_le_of_exactFloor_le point 0 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 2 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 5 _ (by nlinarith)

theorem kFourPath035BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourPath035BadRow point) : KFourPath035BadBudget point := by
  rcases hbad with hzero | hthree | hfive
  · left
    exact directionChart_budget_le_of_exactFloor_le point 0 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 3 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 5 _ (by nlinarith)

theorem kFourPath045BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourPath045BadRow point) : KFourPath045BadBudget point := by
  rcases hbad with hzero | hfour | hfive
  · left
    exact directionChart_budget_le_of_exactFloor_le point 0 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 4 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 5 _ (by nlinarith)

theorem kFourPath014BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourPath014BadRow point) : KFourPath014BadBudget point := by
  rcases hbad with hzero | hone | hfour
  · left
    exact directionChart_budget_le_of_exactFloor_le point 0 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 1 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 4 _ (by nlinarith)

theorem kFourPath124BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourPath124BadRow point) : KFourPath124BadBudget point := by
  rcases hbad with hone | htwo | hfour
  · left
    exact directionChart_budget_le_of_exactFloor_le point 1 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 2 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 4 _ (by nlinarith)

theorem kFourPath145BadBudget_of_badRow (point : DirectionChartPoint 6)
    (hbad : KFourPath145BadRow point) : KFourPath145BadBudget point := by
  rcases hbad with hone | hfour | hfive
  · left
    exact directionChart_budget_le_of_exactFloor_le point 1 _ (by nlinarith)
  · right; left
    exact directionChart_budget_le_of_exactFloor_le point 4 _ (by nlinarith)
  · right; right
    exact directionChart_budget_le_of_exactFloor_le point 5 _ (by nlinarith)

def KFourMissingPathBadBudgetLedger (point : DirectionChartPoint 6) : Prop :=
  KFourPath015BadBudget point ∧ KFourPath025BadBudget point ∧
    KFourPath035BadBudget point ∧ KFourPath045BadBudget point ∧
    KFourPath014BadBudget point ∧ KFourPath124BadBudget point ∧
    KFourPath145BadBudget point

theorem kFourMissingPathBadBudgetLedger_of_badRowLedger
    (point : DirectionChartPoint 6)
    (hbad : KFourMissingPathBadRowLedger point) :
    KFourMissingPathBadBudgetLedger point := by
  rcases hbad with ⟨h015, h025, h035, h045, h014, h124, h145⟩
  exact ⟨kFourPath015BadBudget_of_badRow point h015,
    kFourPath025BadBudget_of_badRow point h025,
    kFourPath035BadBudget_of_badRow point h035,
    kFourPath045BadBudget_of_badRow point h045,
    kFourPath014BadBudget_of_badRow point h014,
    kFourPath124BadBudget_of_badRow point h124,
    kFourPath145BadBudget_of_badRow point h145⟩

def KFourMissingPathObstructionLedger (point : DirectionChartPoint 6) : Prop :=
  KFourMissingPathDualWitnessLedger point ∧ KFourMissingPathBadRowLedger point ∧
    KFourMissingPathBadBudgetLedger point

theorem kFourMissingPathObstructionLedger_of_allTreeBlind
    (point : DirectionChartPoint 6)
    (hnot : ¬ KFourAllTreeMinorAtlasCellFires point) :
    KFourMissingPathObstructionLedger point := by
  have hnotMissing : ¬ KFourMissingPathMinorAtlasCellFires point :=
    fun hmissing => hnot (Or.inr hmissing)
  have hdual := kFourMissingPathDualWitnessLedger_of_not_fires point hnotMissing
  have hbad := kFourMissingPathBadRowLedger_of_dualWitnessLedger point hdual
  exact ⟨hdual, hbad, kFourMissingPathBadBudgetLedger_of_badRowLedger point hbad⟩

/-! ## Spend the obstruction ledger in A3 -/

/-- The exact K4 residual after exposing the dual and Gershgorin consequences
of failure at all seven missing path cells. -/
noncomputable def KFourKnifeBandRefinedZObstructedWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourMissingPathObstructionLedger point →
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- The obstruction-wired residual discharges the former all-tree-blind
residual because atlas blindness manufactures the complete ledger. -/
theorem allTreeBlindKFourKnifeBandRefined_of_zObstructed
    (hz : KFourKnifeBandRefinedZObstructedWeakToStrict) :
    KFourKnifeBandRefinedAllTreeBlindWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hweak
  exact hz point hnotLayerA hnotExchange hnotAtlas
    (kFourMissingPathObstructionLedger_of_allTreeBlind point hnotAtlas) hweak

/-- Conversely, the former residual proves the obstruction-wired statement
without using the now-explicit necessary ledger. -/
theorem zObstructedKFourKnifeBandRefined_of_allTreeBlind
    (hblind : KFourKnifeBandRefinedAllTreeBlindWeakToStrict) :
    KFourKnifeBandRefinedZObstructedWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas _hledger hweak
  exact hblind point hnotLayerA hnotExchange hnotAtlas hweak

theorem kFourKnifeBandRefinedZObstructed_iff_allTreeBlind :
    KFourKnifeBandRefinedZObstructedWeakToStrict ↔
      KFourKnifeBandRefinedAllTreeBlindWeakToStrict :=
  ⟨allTreeBlindKFourKnifeBandRefined_of_zObstructed,
    zObstructedKFourKnifeBandRefined_of_allTreeBlind⟩

theorem kFourKnifeBandRefinedZObstructed_iff :
    KFourKnifeBandRefinedZObstructedWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedZObstructed_iff_allTreeBlind.trans
    kFourKnifeBandRefinedAllTreeBlind_iff

end Gtz

import Gtz.Wave.KFourZMatrixWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# Polynomial entry cells for the seven missing K4 paths

`KFourZMatrixWiring` turns failure of each missing path minor cell into a
three-way, division-free bad-budget alternative.  This file spends the
contrapositive in the direction needed by the atlas: if all three bad budgets
fail strictly, the corresponding path minor cell fires.  Thus each of the
seven existential floor certificates acquires a cheap polynomial sufficient
condition, with no auxiliary floor or determinant in its public interface.
-/

namespace Gtz

open Matrix Finset

/-! ## Failure of a path cell forces its polynomial bad budget -/

theorem kFourPath015BadBudget_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell015Fires point) : KFourPath015BadBudget point := by
  have hdual := kFourPath015DualWitness_of_not_fires point hnot
  have hrow : KFourPath015BadRow point :=
    ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 2, point.mass_pos 4])
      (by nlinarith [point.mass_pos 4])
      (by nlinarith [point.mass_pos 3, point.mass_pos 4]) hdual
  exact kFourPath015BadBudget_of_badRow point hrow

theorem kFourPath025BadBudget_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell025Fires point) : KFourPath025BadBudget point := by
  have hdual := kFourPath025DualWitness_of_not_fires point hnot
  have hrow : KFourPath025BadRow point :=
    ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 1, point.mass_pos 3])
      (by nlinarith [point.mass_pos 3])
      (by nlinarith [point.mass_pos 3, point.mass_pos 4]) hdual
  exact kFourPath025BadBudget_of_badRow point hrow

theorem kFourPath035BadBudget_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell035Fires point) : KFourPath035BadBudget point := by
  have hdual := kFourPath035DualWitness_of_not_fires point hnot
  have hrow : KFourPath035BadRow point :=
    ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 2, point.mass_pos 4])
      (by nlinarith [point.mass_pos 2])
      (by nlinarith [point.mass_pos 1, point.mass_pos 2]) hdual
  exact kFourPath035BadBudget_of_badRow point hrow

theorem kFourPath045BadBudget_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell045Fires point) : KFourPath045BadBudget point := by
  have hdual := kFourPath045DualWitness_of_not_fires point hnot
  have hrow : KFourPath045BadRow point :=
    ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 1, point.mass_pos 3])
      (by nlinarith [point.mass_pos 1])
      (by nlinarith [point.mass_pos 1, point.mass_pos 2]) hdual
  exact kFourPath045BadBudget_of_badRow point hrow

theorem kFourPath014BadBudget_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell014Fires point) : KFourPath014BadBudget point := by
  have hdual := kFourPath014DualWitness_of_not_fires point hnot
  have hrow : KFourPath014BadRow point :=
    ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 2, point.mass_pos 5])
      (by nlinarith [point.mass_pos 3, point.mass_pos 5])
      (by nlinarith [point.mass_pos 5]) hdual
  exact kFourPath014BadBudget_of_badRow point hrow

theorem kFourPath124BadBudget_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell124Fires point) : KFourPath124BadBudget point := by
  have hdual := kFourPath124DualWitness_of_not_fires point hnot
  have hrow : KFourPath124BadRow point :=
    ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 0, point.mass_pos 3])
      (by nlinarith [point.mass_pos 3])
      (by nlinarith [point.mass_pos 3, point.mass_pos 5]) hdual
  exact kFourPath124BadBudget_of_badRow point hrow

theorem kFourPath145BadBudget_of_not_fires (point : DirectionChartPoint 6)
    (hnot : ¬ KFourPathCell145Fires point) : KFourPath145BadBudget point := by
  have hdual := kFourPath145DualWitness_of_not_fires point hnot
  have hrow : KFourPath145BadRow point :=
    ZThreeDualWitness.badRow
      (by nlinarith [point.mass_pos 0])
      (by nlinarith [point.mass_pos 0, point.mass_pos 3])
      (by nlinarith [point.mass_pos 0, point.mass_pos 2]) hdual
  exact kFourPath145BadBudget_of_badRow point hrow

/-! ## Existential-free polynomial cells -/

def KFourPath015PolynomialCellFires (point : DirectionChartPoint 6) : Prop :=
  (2 * point.mass 2 + 3 * point.mass 4) * point.weight 0 <
      point.mass 0 * (1 - point.weight 0) ∧
    (2 * point.mass 2 + 2 * point.mass 3 + 3 * point.mass 4) * point.weight 1 <
      point.mass 1 * (1 - point.weight 1) ∧
    (2 * point.mass 3 + 3 * point.mass 4) * point.weight 5 <
      point.mass 5 * (1 - point.weight 5)

def KFourPath025PolynomialCellFires (point : DirectionChartPoint 6) : Prop :=
  (2 * point.mass 1 + 3 * point.mass 3) * point.weight 0 <
      point.mass 0 * (1 - point.weight 0) ∧
    (2 * point.mass 1 + 3 * point.mass 3 + 2 * point.mass 4) * point.weight 2 <
      point.mass 2 * (1 - point.weight 2) ∧
    (3 * point.mass 3 + 2 * point.mass 4) * point.weight 5 <
      point.mass 5 * (1 - point.weight 5)

def KFourPath035PolynomialCellFires (point : DirectionChartPoint 6) : Prop :=
  (3 * point.mass 2 + 2 * point.mass 4) * point.weight 0 <
      point.mass 0 * (1 - point.weight 0) ∧
    (2 * point.mass 1 + 3 * point.mass 2 + 2 * point.mass 4) * point.weight 3 <
      point.mass 3 * (1 - point.weight 3) ∧
    (2 * point.mass 1 + 3 * point.mass 2) * point.weight 5 <
      point.mass 5 * (1 - point.weight 5)

def KFourPath045PolynomialCellFires (point : DirectionChartPoint 6) : Prop :=
  (3 * point.mass 1 + 2 * point.mass 3) * point.weight 0 <
      point.mass 0 * (1 - point.weight 0) ∧
    (3 * point.mass 1 + 2 * point.mass 2 + 2 * point.mass 3) * point.weight 4 <
      point.mass 4 * (1 - point.weight 4) ∧
    (3 * point.mass 1 + 2 * point.mass 2) * point.weight 5 <
      point.mass 5 * (1 - point.weight 5)

def KFourPath014PolynomialCellFires (point : DirectionChartPoint 6) : Prop :=
  (2 * point.mass 2 + 2 * point.mass 3 + 3 * point.mass 5) * point.weight 0 <
      point.mass 0 * (1 - point.weight 0) ∧
    (2 * point.mass 2 + 3 * point.mass 5) * point.weight 1 <
      point.mass 1 * (1 - point.weight 1) ∧
    (2 * point.mass 3 + 3 * point.mass 5) * point.weight 4 <
      point.mass 4 * (1 - point.weight 4)

def KFourPath124PolynomialCellFires (point : DirectionChartPoint 6) : Prop :=
  (2 * point.mass 0 + 3 * point.mass 3) * point.weight 1 <
      point.mass 1 * (1 - point.weight 1) ∧
    (2 * point.mass 0 + 3 * point.mass 3 + 2 * point.mass 5) * point.weight 2 <
      point.mass 2 * (1 - point.weight 2) ∧
    (3 * point.mass 3 + 2 * point.mass 5) * point.weight 4 <
      point.mass 4 * (1 - point.weight 4)

def KFourPath145PolynomialCellFires (point : DirectionChartPoint 6) : Prop :=
  (3 * point.mass 0 + 2 * point.mass 3) * point.weight 1 <
      point.mass 1 * (1 - point.weight 1) ∧
    (3 * point.mass 0 + 2 * point.mass 2) * point.weight 4 <
      point.mass 4 * (1 - point.weight 4) ∧
    (3 * point.mass 0 + 2 * point.mass 2 + 2 * point.mass 3) * point.weight 5 <
      point.mass 5 * (1 - point.weight 5)

/-! ## The polynomial cells recover their path minor cells -/

theorem kFourPath015CellFires_of_polynomial (point : DirectionChartPoint 6)
    (hpoly : KFourPath015PolynomialCellFires point) :
    KFourPathCell015Fires point := by
  by_contra hnot
  have hbad := kFourPath015BadBudget_of_not_fires point hnot
  rcases hbad with hzero | hone | hfive
  · exact (not_lt_of_ge hzero) hpoly.1
  · exact (not_lt_of_ge hone) hpoly.2.1
  · exact (not_lt_of_ge hfive) hpoly.2.2

theorem kFourPath025CellFires_of_polynomial (point : DirectionChartPoint 6)
    (hpoly : KFourPath025PolynomialCellFires point) :
    KFourPathCell025Fires point := by
  by_contra hnot
  have hbad := kFourPath025BadBudget_of_not_fires point hnot
  rcases hbad with hzero | htwo | hfive
  · exact (not_lt_of_ge hzero) hpoly.1
  · exact (not_lt_of_ge htwo) hpoly.2.1
  · exact (not_lt_of_ge hfive) hpoly.2.2

theorem kFourPath035CellFires_of_polynomial (point : DirectionChartPoint 6)
    (hpoly : KFourPath035PolynomialCellFires point) :
    KFourPathCell035Fires point := by
  by_contra hnot
  have hbad := kFourPath035BadBudget_of_not_fires point hnot
  rcases hbad with hzero | hthree | hfive
  · exact (not_lt_of_ge hzero) hpoly.1
  · exact (not_lt_of_ge hthree) hpoly.2.1
  · exact (not_lt_of_ge hfive) hpoly.2.2

theorem kFourPath045CellFires_of_polynomial (point : DirectionChartPoint 6)
    (hpoly : KFourPath045PolynomialCellFires point) :
    KFourPathCell045Fires point := by
  by_contra hnot
  have hbad := kFourPath045BadBudget_of_not_fires point hnot
  rcases hbad with hzero | hfour | hfive
  · exact (not_lt_of_ge hzero) hpoly.1
  · exact (not_lt_of_ge hfour) hpoly.2.1
  · exact (not_lt_of_ge hfive) hpoly.2.2

theorem kFourPath014CellFires_of_polynomial (point : DirectionChartPoint 6)
    (hpoly : KFourPath014PolynomialCellFires point) :
    KFourPathCell014Fires point := by
  by_contra hnot
  have hbad := kFourPath014BadBudget_of_not_fires point hnot
  rcases hbad with hzero | hone | hfour
  · exact (not_lt_of_ge hzero) hpoly.1
  · exact (not_lt_of_ge hone) hpoly.2.1
  · exact (not_lt_of_ge hfour) hpoly.2.2

theorem kFourPath124CellFires_of_polynomial (point : DirectionChartPoint 6)
    (hpoly : KFourPath124PolynomialCellFires point) :
    KFourPathCell124Fires point := by
  by_contra hnot
  have hbad := kFourPath124BadBudget_of_not_fires point hnot
  rcases hbad with hone | htwo | hfour
  · exact (not_lt_of_ge hone) hpoly.1
  · exact (not_lt_of_ge htwo) hpoly.2.1
  · exact (not_lt_of_ge hfour) hpoly.2.2

theorem kFourPath145CellFires_of_polynomial (point : DirectionChartPoint 6)
    (hpoly : KFourPath145PolynomialCellFires point) :
    KFourPathCell145Fires point := by
  by_contra hnot
  have hbad := kFourPath145BadBudget_of_not_fires point hnot
  rcases hbad with hone | hfour | hfive
  · exact (not_lt_of_ge hone) hpoly.1
  · exact (not_lt_of_ge hfour) hpoly.2.1
  · exact (not_lt_of_ge hfive) hpoly.2.2

/-! ## Aggregate atlas and direct strict-tree dispatch -/

def KFourMissingPathPolynomialAtlasCellFires
    (point : DirectionChartPoint 6) : Prop :=
  KFourPath015PolynomialCellFires point ∨ KFourPath025PolynomialCellFires point ∨
    KFourPath035PolynomialCellFires point ∨ KFourPath045PolynomialCellFires point ∨
    KFourPath014PolynomialCellFires point ∨ KFourPath124PolynomialCellFires point ∨
    KFourPath145PolynomialCellFires point

theorem kFourMissingPathMinorAtlasCellFires_of_polynomialAtlas
    (point : DirectionChartPoint 6)
    (hpoly : KFourMissingPathPolynomialAtlasCellFires point) :
    KFourMissingPathMinorAtlasCellFires point := by
  rcases hpoly with h015 | h025 | h035 | h045 | h014 | h124 | h145
  · exact Or.inl (kFourPath015CellFires_of_polynomial point h015)
  · exact Or.inr (Or.inl (kFourPath025CellFires_of_polynomial point h025))
  · exact Or.inr (Or.inr (Or.inl (kFourPath035CellFires_of_polynomial point h035)))
  · exact Or.inr (Or.inr (Or.inr
      (Or.inl (kFourPath045CellFires_of_polynomial point h045))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (kFourPath014CellFires_of_polynomial point h014)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (kFourPath124CellFires_of_polynomial point h124))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (kFourPath145CellFires_of_polynomial point h145))))))

theorem kFourAllTreeMinorAtlasCellFires_of_polynomialAtlas
    (point : DirectionChartPoint 6)
    (hpoly : KFourMissingPathPolynomialAtlasCellFires point) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inr (kFourMissingPathMinorAtlasCellFires_of_polynomialAtlas point hpoly)

theorem kFourAtlas_hasStrictTree_of_polynomialAtlas
    (point : DirectionChartPoint 6)
    (hpoly : KFourMissingPathPolynomialAtlasCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef :=
  kFourAtlas_hasStrictTree_of_missingPathMinorAtlasCell point
    (kFourMissingPathMinorAtlasCellFires_of_polynomialAtlas point hpoly)

/-- Every point in the exact A3 residual fails all seven polynomial cells. -/
theorem not_polynomialAtlas_of_allTreeBlind (point : DirectionChartPoint 6)
    (hnot : ¬ KFourAllTreeMinorAtlasCellFires point) :
    ¬ KFourMissingPathPolynomialAtlasCellFires point :=
  fun hpoly => hnot (kFourAllTreeMinorAtlasCellFires_of_polynomialAtlas point hpoly)

end Gtz
